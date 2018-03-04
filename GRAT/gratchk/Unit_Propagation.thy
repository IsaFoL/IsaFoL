section \<open>Unit Propagation and RUP/RAT Checks\<close>
theory Unit_Propagation
imports SAT_Basic
begin
  text \<open>This theory formalizes the basics of unit propagation and 
    RUP/RAT redundancy checks.\<close>
  
  subsection \<open>Partial Assignments\<close>
  primrec sem_lit' :: "'a literal \<Rightarrow> ('a\<rightharpoonup>bool) \<rightharpoonup> bool" where
    "sem_lit' (Pos x) A = A x"  
  | "sem_lit' (Neg x) A = map_option Not (A x)"

  definition sem_clause' :: "'a literal set \<Rightarrow> ('a \<rightharpoonup> bool) \<rightharpoonup> bool" where
    "sem_clause' C A \<equiv> 
      if \<exists>l\<in>C. sem_lit' l A = Some True then Some True
      else if \<forall>l\<in>C. sem_lit' l A = Some False then Some False
      else None"

  definition compat_assignment :: "('a \<rightharpoonup> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" 
    where "compat_assignment A \<sigma> \<equiv> \<forall>x v. A x = Some v \<longrightarrow> \<sigma> x = v"
      
  lemma sem_neg_lit'[simp]: 
    "sem_lit' (neg_lit l) A = map_option Not (sem_lit' l A)"
    by (cases l) (auto simp: option.map_comp o_def option.map_ident)

  lemma (in -) sem_lit'_empty[simp]: "sem_lit' l Map.empty = None" 
    by (cases l) auto

  text \<open>We install a custom case distinction rule for @{typ "bool option"}, which
    has the cases \<open>undec\<close>, \<open>false\<close>, and \<open>true\<close>.
  \<close>    
  fun boolopt_cases_aux where
    "boolopt_cases_aux None = ()"
  | "boolopt_cases_aux (Some False) = ()"
  | "boolopt_cases_aux (Some True) = ()"
  
  lemmas boolopt_cases[case_names undec false true, cases type] 
    = boolopt_cases_aux.cases
  
  lemma not_Some_bool_if: "\<lbrakk> a\<noteq>Some False; a\<noteq>Some True \<rbrakk> \<Longrightarrow> a=None"
    by (cases a) auto

  text \<open>Rules to trigger case distinctions on the semantics of a clause 
    with a distinguished literal.\<close>
  lemma sem_clause_insert_eq_complete: 
    "sem_clause' (insert l C) A = (case sem_lit' l A of
      Some True \<Rightarrow> Some True
    | Some False \<Rightarrow> sem_clause' C A
    | None \<Rightarrow> (case sem_clause' C A of 
        None \<Rightarrow> None 
      | Some False \<Rightarrow> None 
      | Some True \<Rightarrow> Some True))"
    by (auto simp: sem_clause'_def split: option.split bool.split)
  
      
  lemma sem_clause_empty[simp]: "sem_clause' {} A = Some False"
    unfolding sem_clause'_def by auto
      
  lemma sem_clause'_insert_true: "sem_clause' (insert l C) A = Some True \<longleftrightarrow> 
    sem_lit' l A = Some True \<or> sem_clause' C A = Some True"
    by (auto simp: sem_clause_insert_eq_complete split: option.split bool.split)
      
  lemma sem_clause'_insert_false[simp]:
    "sem_clause' (insert l C) A = Some False 
    \<longleftrightarrow> sem_lit' l A = Some False \<and> sem_clause' C A = Some False"
    unfolding sem_clause'_def by auto
      
  lemma sem_clause'_union_false[simp]:
    "sem_clause' (C1\<union>C2) A = Some False 
    \<longleftrightarrow> sem_clause' C1 A = Some False \<and> sem_clause' C2 A = Some False"
    unfolding sem_clause'_def by auto

  lemma compat_assignment_empty[simp]: "compat_assignment Map.empty \<sigma>" 
    unfolding compat_assignment_def by simp

      
  text \<open>Assign variable such that literal becomes true\<close>
  definition "assign_lit A l \<equiv> A( var_of_lit l \<mapsto> is_pos l )"
  
  lemma assign_lit_simps[simp]:
    "assign_lit A (Pos x) = A(x\<mapsto>True)"
    "assign_lit A (Neg x) = A(x\<mapsto>False)"
    unfolding assign_lit_def by auto

  lemma assign_lit_dom[simp]: 
    "dom (assign_lit A l) = insert (var_of_lit l) (dom A)"  
    unfolding assign_lit_def by auto

  lemma sem_lit_assign[simp]: "sem_lit' l (assign_lit A l) = Some True"
    unfolding assign_lit_def by (cases l) auto

  lemma sem_lit'_none_conv: "sem_lit' l A = None \<longleftrightarrow> A (var_of_lit l) = None"
    by (cases l) auto

  lemma assign_undec_pres_dec_lit: 
    "\<lbrakk> sem_lit' l A = None; sem_lit' l' A = Some v \<rbrakk> 
    \<Longrightarrow> sem_lit' l' (assign_lit A l) = Some v"  
    unfolding assign_lit_def 
    apply (cases l)
    apply auto
    apply (cases l'; auto)
    apply (cases l'; clarsimp)
    done

  lemma assign_undec_pres_dec_clause: 
    "\<lbrakk> sem_lit' l A = None; sem_clause' C A = Some v \<rbrakk> 
    \<Longrightarrow> sem_clause' C (assign_lit A l) = Some v"  
    unfolding sem_clause'_def
    by (force split: if_split_asm simp: assign_undec_pres_dec_lit)

  lemma sem_lit'_assign_conv: "sem_lit' l' (assign_lit A l) = (
    if l'=l then Some True 
    else if l'=neg_lit l then Some False 
    else sem_lit' l' A)"  
    unfolding assign_lit_def
    by (cases l; cases l'; auto)

  text \<open>Predicates for unit clauses\<close>    
  definition "is_unit_lit A C l 
    \<equiv> l\<in>C \<and> sem_lit' l A = None \<and> (sem_clause' (C-{l}) A = Some False)"
  definition "is_unit_clause A C \<equiv> \<exists>l. is_unit_lit A C l"
  definition "the_unit_lit A C \<equiv> THE l. is_unit_lit A C l"

  abbreviation (input) "is_conflict_clause A C \<equiv> sem_clause' C A = Some False"
  abbreviation (input) "is_true_clause A C \<equiv> sem_clause' C A = Some True"
    
  lemma sem_clause'_false_conv: 
    "sem_clause' C A = Some False \<longleftrightarrow> (\<forall>l\<in>C. sem_lit' l A = Some False)"
    unfolding sem_clause'_def by auto

  lemma sem_clause'_true_conv: 
    "sem_clause' C A = Some True \<longleftrightarrow> (\<exists>l\<in>C. sem_lit' l A = Some True)"
    unfolding sem_clause'_def by auto

  lemma the_unit_lit_eq[simp]: "is_unit_lit A C l \<Longrightarrow> the_unit_lit A C = l"
    unfolding is_unit_lit_def the_unit_lit_def sem_clause'_false_conv
    by force

  lemma is_unit_lit_unique: "\<lbrakk>is_unit_lit C A l1; is_unit_lit C A l2\<rbrakk> \<Longrightarrow> l1=l2"
    using the_unit_lit_eq by blast

  lemma is_unit_clauseE:
    assumes "is_unit_clause A C"
    obtains l C' where 
      "C=insert l C'" 
      "l\<notin>C'" 
      "sem_lit' l A = None" 
      "sem_clause' C' A = Some False"
      "the_unit_lit A C = l"
    using assms
  proof -
    from assms obtain l where IUL: "is_unit_lit A C l"
      unfolding is_unit_clause_def by blast
    note [simp] = the_unit_lit_eq[OF IUL]  

    from IUL 
      have 1: "l\<in>C" "sem_lit' l A = None" "sem_clause' (C-{l}) A = Some False"
      unfolding is_unit_lit_def by blast+
    show thesis  
      apply (rule that[of l "C-{l}"])
      using 1
      by auto
  qed    

  lemma is_unit_clauseE':
    assumes "is_unit_clause A C"
    obtains l C' where 
      "C=insert l C'" 
      "l\<notin>C'" 
      "sem_lit' l A = None" 
      "sem_clause' C' A = Some False"
    by (rule is_unit_clauseE[OF assms])

  lemma sem_not_false_the_unit_lit:
    assumes "is_unit_lit A C l"
    assumes "l'\<in>C"
    assumes "sem_lit' l' A \<noteq> Some False"
    shows "l'=l"
    by (metis assms insert_Diff insert_iff 
          is_unit_lit_def sem_clause'_insert_false)

  lemma sem_none_the_unit_lit:
    assumes "is_unit_lit A C l"
    assumes "l'\<in>C"
    assumes "sem_lit' l' A = None"
    shows "l'=l"
    using sem_not_false_the_unit_lit[OF assms(1,2)] assms(3) by auto

  lemma is_unit_lit_unique_ss: 
    "\<lbrakk>C'\<subseteq>C; is_unit_lit A C' l'; is_unit_lit A C l\<rbrakk> \<Longrightarrow> l'=l"
    by (simp add: is_unit_lit_def sem_none_the_unit_lit subsetD)
      
  lemma is_unit_litI: 
    "\<lbrakk>l\<in>C; sem_clause' (C-{l}) A = Some False; sem_lit' l A = None\<rbrakk> 
    \<Longrightarrow> is_unit_lit A C l"  
    by (auto simp: is_unit_lit_def)

  lemma is_unit_clauseI: "is_unit_lit A C l \<Longrightarrow> is_unit_clause A C"  
    by (auto simp: is_unit_clause_def)

  lemma unit_other_false:
    assumes "is_unit_lit A C l"
    assumes "l'\<in>C" "l\<noteq>l'"
    shows "sem_lit' l' A = Some False"
    using assms by (auto simp: is_unit_lit_def sem_clause'_false_conv)

  lemma unit_clause_sem': "is_unit_lit A C l \<Longrightarrow> sem_clause' C A = None"
    unfolding is_unit_lit_def sem_clause'_def
    using mk_disjoint_insert by (fastforce split: if_split_asm)

  lemma unit_clause_assign_dec: 
    "is_unit_lit A C l \<Longrightarrow> sem_clause' C (assign_lit A l) = Some True"
    unfolding is_unit_lit_def sem_clause'_def
    by (force split: if_split_asm simp: sem_lit'_assign_conv)

  lemma unit_clause_sem: "is_unit_clause A C \<Longrightarrow> sem_clause' C A = None"  
    by (auto simp: is_unit_clause_def unit_clause_sem')

  lemma sem_not_unit_clause: "sem_clause' C A \<noteq> None \<Longrightarrow> \<not>is_unit_clause A C"
    by (auto simp: is_unit_clause_def unit_clause_sem')

  lemma unit_contains_no_true:
    assumes "is_unit_clause A C"
    assumes "l\<in>C"
    shows "sem_lit' l A \<noteq> Some True"
    using assms unfolding is_unit_clause_def is_unit_lit_def
    by (force simp: sem_clause'_false_conv) 

  lemma two_nfalse_not_unit:
    assumes "l1\<in>C" and "l2\<in>C" and "l1\<noteq>l2" 
    assumes "sem_lit' l1 A \<noteq> Some False" and "sem_lit' l2 A \<noteq> Some False"
    shows "\<not>is_unit_clause A C"  
    using assms
    unfolding is_unit_clause_def is_unit_lit_def
    by (auto simp: sem_clause'_false_conv)


  lemma conflict_clause_assign_indep:
    assumes "sem_clause' C (assign_lit A l) = Some False"
    assumes "neg_lit l \<notin> C"
    shows "sem_clause' C A = Some False"
    using assms
    by (auto simp: sem_clause'_def sem_lit'_assign_conv split: if_split_asm)
    
  lemma sem_lit'_assign_undec_conv: 
    "sem_lit' l' (assign_lit A l) = None 
    \<longleftrightarrow> sem_lit' l' A = None \<and> var_of_lit l \<noteq> var_of_lit l'"  
    by (cases l; cases l'; auto)

  lemma unit_clause_assign_indep:
    assumes "is_unit_clause (assign_lit A l) C" 
    assumes "neg_lit l \<notin> C"  
    shows "is_unit_clause A C"
    using assms
    unfolding is_unit_clause_def is_unit_lit_def
    by (auto 
          dest!: conflict_clause_assign_indep 
          simp: sem_lit'_assign_undec_conv)

  lemma clause_assign_false_cases[consumes 1, case_names no_lit lit]:
    assumes "sem_clause' C (assign_lit A l) = Some False"  
    obtains "neg_lit l \<notin> C" "sem_clause' C A = Some False"
          | "neg_lit l \<in> C" "sem_clause' (C-{neg_lit l}) A = Some False"
  proof (cases)        
    assume A: "neg_lit l \<in> C" 
    with assms have "sem_clause' (C-{neg_lit l}) A = Some False"  
      by (auto simp: sem_clause'_def sem_lit'_assign_conv split: if_split_asm)
    with A show ?thesis by (rule that)
  next
    assume A: "neg_lit l \<notin> C"  
    with assms have "sem_clause' C A = Some False"  
      by (auto simp: sem_clause'_def sem_lit'_assign_conv split: if_split_asm)
    with A show ?thesis by (rule that)
  qed  

  lemma clause_assign_unit_cases[consumes 1, case_names no_lit lit]:
    assumes "is_unit_clause (assign_lit A l) C"
    obtains "neg_lit l \<notin> C" "is_unit_clause A C"
          | "neg_lit l \<in> C"
  proof (cases)        
    assume "neg_lit l \<in> C" thus ?thesis by (rule that)
  next
    assume A: "neg_lit l \<notin> C"  
    from assms obtain lu C' where 
      [simp]: "C = insert lu C'" "lu\<notin>C'"
      and LUN: "sem_lit' lu (assign_lit A l) = None" 
      and SCF: "sem_clause' C' (assign_lit A l) = Some False"
      by (blast elim: is_unit_clauseE)

    from clause_assign_false_cases[OF SCF] A
    have "sem_clause' C' A = Some False" by auto
    moreover from LUN have "sem_lit' lu A = None" 
      by (simp add: sem_lit'_assign_undec_conv)
    ultimately have "is_unit_clause A C"
      by (auto simp: is_unit_clause_def is_unit_lit_def)
    with A show ?thesis by (rule that)
  qed      

  lemma sem_clause_ins_assign_not_false[simp]: 
    "sem_clause' (insert l C) (assign_lit A l) \<noteq> Some False"
    unfolding sem_clause'_def by auto

  lemma sem_clause_ins_assign_not_unit[simp]: 
    "\<not>is_unit_clause (assign_lit A l) (insert l C')"  
    apply (clarsimp simp: is_unit_clause_def is_unit_lit_def sem_lit'_assign_undec_conv sem_clause'_false_conv)
    apply force
    done

  context 
    fixes A :: "'a \<rightharpoonup> bool" and \<sigma> :: "'a \<Rightarrow> bool" 
    assumes C: "compat_assignment A \<sigma>"
  begin  
    lemma compat_lit: "sem_lit' l A = Some v \<Longrightarrow> sem_lit l \<sigma> = v"
      using C 
      by (cases l) (auto simp: compat_assignment_def)
      
    lemma compat_clause: "sem_clause' C A = Some v \<Longrightarrow> sem_clause C \<sigma> = v"  
      unfolding sem_clause_def sem_clause'_def
      by (force simp: compat_lit split: if_split_asm)
  end      

  subsubsection \<open>Models, Equivalence, and Redundancy\<close>

  definition "models' F A \<equiv> { \<sigma>. compat_assignment A \<sigma> \<and> sem_cnf F \<sigma>}"
  definition "sat' F A \<equiv> models' F A \<noteq> {}"
  definition "equiv' F A A' \<equiv> models' F A = models' F A'"

  text \<open>Alternative definition of models', which may be suited for 
    presentation in paper.\<close>
  lemma "models' F A = models F \<inter> Collect (compat_assignment A)"
    unfolding models'_def models_def by auto
  
  
  lemma equiv'_refl[simp]: "equiv' F A A" unfolding equiv'_def by simp
  lemma equiv'_sym: "equiv' F A A' \<Longrightarrow> equiv' F A' A" 
    unfolding equiv'_def by simp
  lemma equiv'_trans[trans]: "\<lbrakk> equiv' F A B; equiv' F B C \<rbrakk> \<Longrightarrow> equiv' F A C" 
    unfolding equiv'_def by simp

  lemma models_antimono: "C'\<subseteq>C \<Longrightarrow> models' C A \<subseteq> models' C' A"
    unfolding models'_def by (auto simp: sem_cnf_def)


  lemma conflict_clause_imp_no_models:
    "\<lbrakk> C\<in>F; is_conflict_clause A C \<rbrakk> \<Longrightarrow> models' F A = {}"  
    by (auto simp: models'_def sem_cnf_def dest: compat_clause)

  lemma sat'_empty_iff[simp]: "sat' F Map.empty = sat F"  
    unfolding sat'_def sat_def models'_def
    by auto

  lemma sat'_antimono: "F\<subseteq>F' \<Longrightarrow> sat' F' A \<Longrightarrow> sat' F A"  
    unfolding sat'_def using models_antimono by blast

  lemma sat'_equiv: "equiv' F A A' \<Longrightarrow> sat' F A = sat' F A'"
    unfolding equiv'_def sat'_def by blast
    
  lemma sat_iff_sat': "sat F \<longleftrightarrow> (\<exists>A. sat' F A)"
    by (metis (no_types, lifting) Collect_empty_eq models'_def models_def 
          sat'_def sat'_empty_iff sat_iff_has_models)
    

  definition "implied_clause F A C \<equiv> models' (insert C F) A = models' F A"  
  definition "redundant_clause F A C 
    \<equiv> (models' (insert C F) A = {}) \<longleftrightarrow> (models' F A = {})"
  
  lemma redundant_clause_alt: "redundant_clause F A C \<longleftrightarrow> sat' (insert C F) A = sat' F A"
    unfolding redundant_clause_def sat'_def by blast
    
  lemma redundant_clauseI[intro?]:
    assumes "\<And>\<sigma>. \<lbrakk>compat_assignment A \<sigma>; sem_cnf F \<sigma>\<rbrakk> 
              \<Longrightarrow> \<exists>\<sigma>'. compat_assignment A \<sigma>' \<and> sem_clause C \<sigma>' \<and> sem_cnf F \<sigma>'"
    shows "redundant_clause F A C"
    using assms unfolding redundant_clause_def models'_def 
    by auto
  
  lemma implied_clauseI[intro?]:
    assumes "\<And>\<sigma>. \<lbrakk>compat_assignment A \<sigma>; sem_cnf F \<sigma>\<rbrakk> \<Longrightarrow> sem_clause C \<sigma>"
    shows "implied_clause F A C"
    using assms unfolding implied_clause_def models'_def 
    by auto
  
  
  lemma implied_is_redundant: "implied_clause F A C \<Longrightarrow> redundant_clause F A C"
    unfolding implied_clause_def redundant_clause_def by blast

  lemma add_redundant_sat_iff[simp]: 
    "redundant_clause F A C \<Longrightarrow> sat' (insert C F) A = sat' F A"  
    unfolding redundant_clause_def sat'_def by auto

  lemma true_clause_implied: 
    "sem_clause' C A = Some True \<Longrightarrow> implied_clause F A C"
    unfolding implied_clause_def models'_def 
    by (auto simp: compat_clause)


  lemma equiv'_map_empty_sym: 
    "NO_MATCH Map.empty A \<Longrightarrow> equiv' F Map.empty A \<longleftrightarrow> equiv' F A Map.empty"
    using equiv'_sym by auto

  lemma tautology: "\<lbrakk>l\<in>C; neg_lit l \<in> C\<rbrakk> \<Longrightarrow> sem_clause C \<sigma>"
    by (cases "sem_lit l \<sigma>"; cases l; force simp: sem_clause_def)

  lemma implied_taut: "\<lbrakk>l\<in>C; neg_lit l \<in> C\<rbrakk> \<Longrightarrow> implied_clause F A C"
    unfolding implied_clause_def models'_def using tautology[of l C]
    by auto

  definition "is_syn_taut C \<equiv> C \<inter> neg_lit ` C \<noteq> {}"
  definition "is_blocked A C \<equiv> sem_clause' C A = Some True \<or> is_syn_taut C"
  lemma is_blocked_alt: 
    "is_blocked A C \<longleftrightarrow> sem_clause' C A = Some True \<or> C \<inter> neg_lit ` C \<noteq> {}"
    unfolding is_syn_taut_def is_blocked_def by auto
  
  lemma is_syn_taut_empty[simp]: "\<not>is_syn_taut {}" 
    by (auto simp: is_syn_taut_def)
      
  lemma is_syn_taut_conv: "is_syn_taut C \<longleftrightarrow> (\<exists>l. l\<in>C \<and> neg_lit l \<in> C)"
    unfolding is_syn_taut_def by auto
      
  lemma empty_not_blocked[simp]: "\<not>is_blocked A {}" 
    unfolding is_blocked_alt by (auto simp: sem_clause'_true_conv)
      
  lemma is_blocked_insert_iff: 
    "is_blocked A (insert l C) 
    \<longleftrightarrow> is_blocked A C \<or> sem_lit' l A = Some True \<or> neg_lit l \<in> C"
    by (auto simp: is_blocked_alt sem_clause'_true_conv)
  
  lemma is_blockedI1: "\<lbrakk>l\<in>C; sem_lit' l A = Some True\<rbrakk> \<Longrightarrow> is_blocked A C"
    by (auto simp: is_blocked_def sem_clause'_true_conv)
  
  lemma is_blockedI2: "\<lbrakk>l\<in>C; neg_lit l \<in> C\<rbrakk> \<Longrightarrow> is_blocked A C"
    by (auto simp: is_blocked_def is_syn_taut_def)
      
      
  lemma syn_taut_true[simp]: "is_syn_taut C \<Longrightarrow> sem_clause C \<sigma> = True"  
    apply (auto simp: sem_clause_def is_syn_taut_def)
    using sem_neg_lit by blast
    
      
  lemma syn_taut_imp_blocked: "is_syn_taut C \<Longrightarrow> is_blocked A C"
    unfolding is_blocked_def by auto
  
  lemma blocked_redundant: "is_blocked A C \<Longrightarrow> redundant_clause F A C"
    unfolding is_blocked_alt
    using implied_is_redundant implied_taut true_clause_implied by fastforce
    
  lemma blocked_clause_true: 
    "\<lbrakk>is_blocked A C; compat_assignment A \<sigma>\<rbrakk> \<Longrightarrow> sem_clause C \<sigma>"
  proof -
    assume a1: "compat_assignment A \<sigma>"
    assume "is_blocked A C"
    then have f2: "sem_clause' C A = Some True \<or> C \<inter> neg_lit ` C \<noteq> {}"
      by (simp add: is_blocked_alt)
    have f3: "\<forall>l L p. ((l::'a literal) \<notin> L \<or> neg_lit l \<notin> L) \<or> sem_clause L p"
      by (simp add: tautology)
    have "sem_clause' C A = Some True \<longrightarrow> sem_clause C \<sigma>"
      using a1 by (simp add: compat_clause)
    then show ?thesis
      using f3 f2 by fastforce
  qed

  subsection \<open>Unit Propagation\<close>  


  lemma unit_propagation:
    assumes "C\<in>F"
    assumes UNIT: "is_unit_lit A C l"
    shows "equiv' F A (assign_lit A l)"
    unfolding equiv'_def models'_def
  proof safe
    from UNIT have "l\<in>C" 
      and UNDEC: "sem_lit' l A = None" 
      and OTHER_FALSE': "sem_clause' (C-{l}) A = Some False"
      unfolding is_unit_lit_def by auto

    {  
      fix \<sigma>
      assume COMPAT: "compat_assignment A \<sigma>"
      have OTHER_FALSE: "sem_clause (C-{l}) \<sigma> = False" 
        using compat_clause[OF COMPAT OTHER_FALSE'] .
  
      assume "sem_cnf F \<sigma>"
      with \<open>C\<in>F\<close> \<open>l\<in>C\<close> OTHER_FALSE have "sem_lit l \<sigma>"
        unfolding sem_cnf_def sem_clause_def by auto
        
      with COMPAT show "compat_assignment (assign_lit A l) \<sigma>" 
        unfolding compat_assignment_def
        by (cases l) auto
    }
    {
      fix \<sigma>
      assume "compat_assignment (assign_lit A l) \<sigma>"
      with UNDEC show "compat_assignment A \<sigma>"
        unfolding compat_assignment_def
        apply (cases l; simp)
        apply (metis option.distinct(1))+
        done
    }
  qed  


  inductive_set prop_unit_R :: "'a cnf \<Rightarrow> (('a\<rightharpoonup>bool) \<times> ('a\<rightharpoonup>bool)) set" for F 
    where
    step: "\<lbrakk> C\<in>F; is_unit_lit A C l \<rbrakk> \<Longrightarrow> (A,assign_lit A l)\<in>prop_unit_R F"

  lemma prop_unit_R_Domain[simp]: 
    "A \<in> Domain (prop_unit_R F) \<longleftrightarrow> (\<exists>C\<in>F. is_unit_clause A C)"
    by (auto 
        elim!: prop_unit_R.cases 
        simp: is_unit_clause_def 
        dest: prop_unit_R.intros)

  lemma prop_unit_R_equiv:
    assumes "(A,A')\<in>(prop_unit_R F)\<^sup>*"  
    shows "equiv' F A A'"
    using assms
    apply induction
    apply simp
    apply (erule prop_unit_R.cases)
    using equiv'_trans unit_propagation by blast

  
  lemma wf_prop_unit_R: "finite F \<Longrightarrow> wf ((prop_unit_R F)\<inverse>)"
    apply (rule wf_subset[OF 
              wf_measure[where f="\<lambda>A. card { C\<in>F. sem_clause' C A = None }"]])
    apply safe
    apply (erule prop_unit_R.cases)
    apply simp
    apply (rule psubset_card_mono)
    subgoal by auto []
    apply safe
    subgoal
      apply (auto simp: is_unit_lit_def)
      apply (metis assign_undec_pres_dec_clause boolopt_cases_aux.cases)
      done
    subgoal for _ _ C A l
      proof -
        assume a1: "C \<in> F"
        assume a2: "is_unit_lit A C l"
        assume a3: "{C \<in> F. sem_clause' C (assign_lit A l) = None} 
                    = {C \<in> F. sem_clause' C A = None}"
        have "sem_clause' C A = None"
          using a2 by (metis unit_clause_sem')
        then show ?thesis
          using a3 a2 a1 unit_clause_assign_dec by force
      qed
    done  


subsection \<open>RUP and RAT Criteria\<close>
  text \<open> RAT-criterion to check for a redundant clause:
    Pick a \<^emph>\<open>resolution literal\<close> \<open>l\<close> from the clause, which is not assigned 
    to false, and then check that all resolvents of the clause are implied 
    clauses. 
    
    Note: We include \<open>l\<close> in the resolvents here, as drat-trim does.
    \<close>
  lemma abs_rat_criterion:
    assumes LIC: "l\<in>C"
    assumes NFALSE: "sem_lit' l A \<noteq> Some False"
    assumes CANDS: "\<forall>D\<in>F. neg_lit l \<in> D 
                  \<longrightarrow> implied_clause F A (C \<union> (D - {neg_lit l}))"  
    shows "redundant_clause F A C"
  proof (cases "is_blocked A C")
    case True thus ?thesis using blocked_redundant by blast
  next
    case NBLOCKED: False 
    show ?thesis
    proof  
      fix \<sigma>
      assume COMPAT: "compat_assignment A \<sigma>" and MODELS: "sem_cnf F \<sigma>"
      show "\<exists>\<sigma>'. compat_assignment A \<sigma>' \<and> sem_clause C \<sigma>' \<and> sem_cnf F \<sigma>'"
      proof (cases "sem_clause C \<sigma>")
        case True with COMPAT MODELS show ?thesis by blast
      next
        case False
      
        let ?\<sigma>' = "\<sigma>(var_of_lit l := is_pos l)"
        from NFALSE COMPAT have "compat_assignment A ?\<sigma>'" 
          by (cases l) (auto simp: compat_assignment_def)
        moreover from LIC have "sem_clause C ?\<sigma>'" 
          unfolding sem_clause_def by (cases l; force)
        moreover {
          fix E assume "E\<in>F" "neg_lit l \<notin> E"
          with MODELS have "sem_clause E ?\<sigma>'"
            unfolding sem_cnf_def sem_clause_def
            apply (cases l; clarsimp)
            apply (metis sem_lit.simps(1) syn_indep_lit 
                         upd_sigma_true var_of_lit.elims)
            by (metis sem_lit.simps(2) syn_indep_lit 
                      upd_sigma_false var_of_lit.elims)
        } moreover {
          fix D assume "D\<in>F" "neg_lit l \<in> D"
          with CANDS have "implied_clause F A (C \<union> (D - {neg_lit l}))" by blast
          with MODELS COMPAT have "sem_clause (C \<union> (D - {neg_lit l})) \<sigma>"
            by (metis (no_types, lifting) implied_clause_def 
                      mem_Collect_eq models'_def sem_cnf_insert)
          with False have "sem_clause (D - {neg_lit l}) \<sigma>" 
            by (auto simp: sem_clause_def)
          hence "sem_clause D ?\<sigma>'" by (simp add: sem_clause_set)
        } ultimately show ?thesis unfolding sem_cnf_def by blast
      qed
    qed
  qed

  lemma abs_rat_criterion':
    assumes RAT: "\<exists>l\<in>C. 
      sem_lit' l A \<noteq> Some False 
    \<and> (\<forall>D\<in>F. neg_lit l \<in> D \<longrightarrow> implied_clause F A (C \<union> (D-{neg_lit l})))"
    shows "redundant_clause F A C"
    using assms abs_rat_criterion by blast  

  text \<open>Assign all literals of clause to false.\<close>
  definition "and_not_C A C \<equiv> \<lambda>v. 
    if Pos v \<in> C then Some False else if Neg v \<in> C then Some True else A v"

  lemma compat_and_not_C:
    assumes "compat_assignment A \<sigma>"
    assumes "\<not>sem_clause C \<sigma>"
    shows "compat_assignment (and_not_C A C) \<sigma>"
    by (smt SAT_Basic.sem_neg_lit and_not_C_def assms(1) assms(2) 
        compat_assignment_def neg_lit.simps(2) option.inject 
        sem_clause_def sem_lit.simps(2))  
  
  lemma and_not_empty[simp]: "and_not_C A {} = A" 
    unfolding and_not_C_def by auto
  
  lemma and_not_insert_None: "sem_lit' l (and_not_C A C) = None 
    \<Longrightarrow> and_not_C A (insert l C) = assign_lit (and_not_C A C) (neg_lit l)"
    apply (cases l)
    apply (auto simp: and_not_C_def split: if_split_asm)
    done
  
  lemma and_not_insert_False: "sem_lit' l (and_not_C A C) = Some False 
    \<Longrightarrow> and_not_C A (insert l C) = and_not_C A C"
    apply (cases l)
    apply (auto simp: and_not_C_def split: if_split_asm)
    done
      
  lemma sem_lit_and_not_C_conv: "sem_lit' l (and_not_C A C) = Some v \<longleftrightarrow> (
      (l\<notin>C \<and> neg_lit l\<notin>C \<and> sem_lit' l A = Some v)
    \<or> (l\<in>C \<and> neg_lit l\<notin>C \<and> v=False)
    \<or> (l\<notin>C \<and> neg_lit l\<in>C \<and> v=True)
    \<or> (l\<in>C \<and> neg_lit l\<in>C \<and> v=(\<not>is_pos l))
    )"
    by (cases l) (auto simp: and_not_C_def)
  
  lemma sem_lit_and_not_C_None_conv: "sem_lit' l (and_not_C A C) = None \<longleftrightarrow> 
    sem_lit' l A = None \<and> l\<notin>C \<and> neg_lit l\<notin>C"
    by (cases l) (auto simp: and_not_C_def)
      
  text \<open>Check for implied clause by RUP:
    If the clause is not blocked, assign all literals of the clause to false,
    and search for an equivalent assignment (usually by unit-propagation), which 
    has a conflict.
    \<close>  
  lemma one_step_implied:
    assumes RC: "\<not>is_blocked A C \<Longrightarrow> 
      \<exists>A\<^sub>1. equiv' F (and_not_C A C) A\<^sub>1 \<and> (\<exists>E\<in>F. is_conflict_clause A\<^sub>1 E)"
    shows "implied_clause F A C"
  proof 
    fix \<sigma>
    assume COMPAT: "compat_assignment A \<sigma>"
    assume MODELS: "sem_cnf F \<sigma>"
    
    show "sem_clause (C) \<sigma>"
    proof (cases "is_blocked A C")
      case True
      thus ?thesis using blocked_clause_true COMPAT by auto
    next
      case False
      from RC[OF False] obtain A\<^sub>1 E where 
            EQ: "equiv' F (and_not_C A C) A\<^sub>1" 
        and CONFL: "E \<in> F" "sem_clause' E A\<^sub>1 = Some False"
        by auto
      show ?thesis
      proof (rule ccontr)
        assume "\<not>sem_clause C \<sigma>"
        with compat_and_not_C[OF COMPAT] 
        have "compat_assignment (and_not_C A C) \<sigma>" by auto
        with EQ have COMPAT1: "compat_assignment A\<^sub>1 \<sigma>"
          by (metis (mono_tags, lifting) MODELS equiv'_def 
                    mem_Collect_eq models'_def)
        with MODELS CONFL show False using compat_clause sem_cnf_def by blast  
      qed
    qed
  qed

  text \<open> The unit-propagation steps of @{thm one_step_implied} can also be distributed
    over between the assignments of the negated literals.
    This is an optimization used for the RAT-check, where an initial set of unit-propagations
    can be shared between all candidate checks.
    \<close>
  lemma two_step_implied:
    assumes "\<not>is_blocked A C 
      \<Longrightarrow> \<exists>A\<^sub>1. equiv' F (and_not_C A C) A\<^sub>1 \<and> (\<not>is_blocked A\<^sub>1 D 
      \<longrightarrow> (\<exists>A\<^sub>2. equiv' F (and_not_C A\<^sub>1 D) A\<^sub>2 \<and> (\<exists>E\<in>F. is_conflict_clause A\<^sub>2 E)))
      "
    shows "implied_clause F A (C\<union>D)"
  proof 
    fix \<sigma>
    assume COMPAT: "compat_assignment A \<sigma>"
    assume MODELS: "sem_cnf F \<sigma>"
    
    show "sem_clause (C\<union>D) \<sigma>"
    proof (cases "is_blocked A C")
      case True
      thus ?thesis using blocked_clause_true COMPAT by auto
    next
      case False
      from assms[OF False] obtain A\<^sub>1 where 
            EQ1: "equiv' F (and_not_C A C) A\<^sub>1" 
        and RC2: "(\<not>is_blocked A\<^sub>1 D 
          \<longrightarrow> (\<exists>A\<^sub>2. equiv' F (and_not_C A\<^sub>1 D) A\<^sub>2 
                  \<and> (\<exists>E\<in>F. is_conflict_clause A\<^sub>2 E)))"
        by auto
    
      show ?thesis
      proof (rule ccontr; clarsimp)
        assume "\<not>sem_clause C \<sigma>" "\<not>sem_clause D \<sigma>"
        with compat_and_not_C[OF COMPAT] 
        have "compat_assignment (and_not_C A C) \<sigma>" by auto
        with EQ1 have COMPAT1: "compat_assignment A\<^sub>1 \<sigma>"
          by (metis (mono_tags, lifting) MODELS equiv'_def 
                    mem_Collect_eq models'_def)
        from compat_and_not_C[OF COMPAT1] \<open>\<not> sem_clause D \<sigma>\<close> have
          1: "compat_assignment (and_not_C A\<^sub>1 D) \<sigma>" by auto
        have "\<not>is_blocked A\<^sub>1 D" 
          using COMPAT1 \<open>\<not> sem_clause D \<sigma>\<close> blocked_clause_true by auto
        with RC2 obtain A\<^sub>2 E where
              EQ2: "equiv' F (and_not_C A\<^sub>1 D) A\<^sub>2" 
          and CONFL: "E\<in>F" "is_conflict_clause A\<^sub>2 E"
          by auto
        from EQ2 1 have COMPAT2: "compat_assignment A\<^sub>2 \<sigma>"
          by (metis (mono_tags, lifting) MODELS equiv'_def 
                    mem_Collect_eq models'_def)
        with MODELS CONFL show False using compat_clause sem_cnf_def by blast  
      qed
    qed
  qed
  
  

  subsection \<open>Old \<open>assign_all_negated\<close> Formulation\<close>
  definition "assign_all_negated A C \<equiv> let UD = {l\<in>C. sem_lit' l A = None} in
    A ++ (\<lambda>l.      if Pos l\<in>UD then Some False 
              else if Neg l \<in> UD then Some True 
                 else None)"

  lemma abs_rup_criterion:
    assumes "models' F (assign_all_negated A C) = {}"
    shows "implied_clause F A C"
    using assms
    unfolding models'_def implied_clause_def
    apply (safe; simp)
  proof (rule ccontr)  
    fix \<sigma>
    assume COMPAT: "compat_assignment A \<sigma>" 
    assume S: "sem_cnf F \<sigma>"
    assume CD: "\<forall>\<sigma>. compat_assignment (assign_all_negated A C) \<sigma> 
                    \<longrightarrow> \<not> sem_cnf F \<sigma>" 
    assume NS: "\<not> sem_clause C \<sigma>"
    
    from NS have "\<forall>l\<in>C. sem_lit l \<sigma> = False" by (auto simp: sem_clause_def)
    
    with COMPAT have "compat_assignment (assign_all_negated A C) \<sigma>"
      by (clarsimp simp: compat_assignment_def assign_all_negated_def 
            split: if_split_asm) auto
    with S CD show False by blast
  qed  
      
  subsubsection \<open>Properties of \<open>assign_all_negated\<close>\<close>
  lemma sem_lit_assign_all_negated_cases[consumes 1, case_names None Neg Pos]:
    assumes "sem_lit' l (assign_all_negated A C) = Some v"
    obtains "sem_lit' l A = Some v" 
          | "sem_lit' l A = None" "neg_lit l \<in> C" "v=True"
          | "sem_lit' l A = None" "l \<in> C" "v=False"
    using assms unfolding assign_all_negated_def
    apply (cases l)
    apply (auto simp: map_add_def split: if_split_asm)
    done
    
  lemma sem_lit_assign_all_negated_none_iff:
    "sem_lit' l (assign_all_negated A C) = None 
    \<longleftrightarrow> (sem_lit' l A = None \<and> l\<notin>C \<and> neg_lit l \<notin> C)"  
    unfolding assign_all_negated_def
    apply (cases l)
    apply (auto simp: map_add_def split: if_split_asm)
    done
    
  lemma sem_lit_assign_all_negated_pres_decided:
    assumes "sem_lit' l A = Some v"
    shows "sem_lit' l (assign_all_negated A C) = Some v"
    using assms unfolding assign_all_negated_def
    apply (cases l)
    apply (fastforce simp: map_add_def split: if_split_asm)+
    done

  lemma sem_lit_assign_all_negated_assign: 
    assumes "\<forall>l\<in>C. neg_lit l\<notin>C" "l \<in> C" "sem_lit' l A = None"
    shows "sem_lit' l (assign_all_negated A C) = Some False"  
    using assms unfolding assign_all_negated_def
    apply (cases l)
    apply (auto simp: map_add_def split: if_split_asm)
    done
    
  lemma sem_lit_assign_all_negated_neqv: 
    "sem_lit' l (assign_all_negated A C) \<noteq> Some v \<Longrightarrow> sem_lit' l A \<noteq> Some v"
    by (auto simp: sem_lit_assign_all_negated_pres_decided)

  lemma aan_idem[simp]: 
    "assign_all_negated (assign_all_negated A C) C = assign_all_negated A C"
    by (auto intro!: ext simp: assign_all_negated_def map_add_def)

  lemma aan_dbl: 
    assumes "\<forall>l\<in>C\<union>C'. neg_lit l \<notin> C\<union>C'"
    shows "assign_all_negated (assign_all_negated A C) C' 
          = assign_all_negated A (C\<union>C')"  
    using assms by (force intro!: ext simp: assign_all_negated_def map_add_def)

  lemma aan_mono2: 
    "\<lbrakk>C\<subseteq>C'; \<forall>l\<in>C'. neg_lit l \<notin> C'\<rbrakk> 
     \<Longrightarrow> assign_all_negated A C \<subseteq>\<^sub>m assign_all_negated A C'"
    by (auto simp: assign_all_negated_def map_add_def map_le_def)


  lemma aan_empty[simp]: "assign_all_negated A {} = A"
    by (auto simp: assign_all_negated_def)

  lemma aan_restrict: 
    "assign_all_negated A C |` (- var_of_lit ` {l \<in> C. sem_lit' l A = None}) = A"
    apply (rule ext)
    unfolding assign_all_negated_def
    apply (clarsimp simp: map_add_def restrict_map_def; safe)
    apply simp_all
    apply force
    apply force
    subgoal for l by (cases l) auto
    subgoal for l v by (cases l) auto
    subgoal for v l by (cases l) auto
    subgoal for v l by (cases l) auto
    done

  lemma aan_insert:  
    assumes "\<forall>l'\<in>C. sem_lit' l' A \<noteq> Some True \<and> neg_lit l' \<notin> C"
    assumes "sem_lit' l A \<noteq> Some True \<and> neg_lit l \<notin> C"
    shows "assign_lit (assign_all_negated A C) (neg_lit l) 
          = assign_all_negated A (insert l C)"
    apply (rule ext)
    using assms
    apply (cases l)
    apply (auto simp: assign_all_negated_def map_add_def)
    done

  lemma aan_insert_set:  
    assumes "sem_lit' l A \<noteq> None"
    shows "assign_all_negated A (insert l C) = assign_all_negated A C"
    apply (rule ext)
    using assms
    apply (cases l)
    apply (auto simp: assign_all_negated_def map_add_def)
    done

end
