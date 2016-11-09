theory Unit_Propagation
imports SAT_Basic
begin
  subsection \<open>Partial Assignments\<close>
  primrec sem_lit' :: "'a literal \<Rightarrow> ('a\<rightharpoonup>bool) \<rightharpoonup> bool" where
    "sem_lit' (Pos x) A = A x"  
  | "sem_lit' (Neg x) A = map_option Not (A x)"

  definition "sem_clause' C A \<equiv> 
    if \<exists>l\<in>C. sem_lit' l A = Some True then Some True
    else if \<forall>l\<in>C. sem_lit' l A = Some False then Some False
    else None"

  lemma sem_neg_lit[simp]: "sem_lit' (neg_lit l) A = map_option Not (sem_lit' l A)"
    by (cases l) (auto simp: option.map_comp o_def option.map_ident)

  lemma (in -) sem_lit'_empty[simp]: "sem_lit' l Map.empty = None" by (cases l) auto

  fun boolopt_cases_aux where
    "boolopt_cases_aux None = ()"
  | "boolopt_cases_aux (Some False) = ()"
  | "boolopt_cases_aux (Some True) = ()"
  
  lemmas boolopt_cases[case_names undec false true, cases type] = boolopt_cases_aux.cases
  
  lemma sem_clause'_insert_false[simp]:
    "sem_clause' (insert l C) A = Some False \<longleftrightarrow> sem_lit' l A = Some False \<and> sem_clause' C A = Some False"
    unfolding sem_clause'_def by auto
  lemma sem_clause'_union_false[simp]:
    "sem_clause' (C1\<union>C2) A = Some False \<longleftrightarrow>  sem_clause' C1 A = Some False \<and> sem_clause' C2 A = Some False"
    unfolding sem_clause'_def by auto

  text \<open>Assign variable such that literal becomes true\<close>
  definition "assign_lit A l \<equiv> A( var_of_lit l \<mapsto> is_pos l )"
  
  lemma assign_lit_simps[simp]:
    "assign_lit A (Pos x) = A(x\<mapsto>True)"
    "assign_lit A (Neg x) = A(x\<mapsto>False)"
    unfolding assign_lit_def by auto

  lemma assign_lit_dom[simp]: "dom (assign_lit A l) = insert (var_of_lit l) (dom A)"  
    unfolding assign_lit_def by auto

  lemma sem_lit_assign[simp]: "sem_lit' l (assign_lit A l) = Some True"
    unfolding assign_lit_def by (cases l) auto

  lemma assign_undec_pres_dec_lit: 
    "\<lbrakk> sem_lit' l A = None; sem_lit' l' A = Some v \<rbrakk> \<Longrightarrow> sem_lit' l' (assign_lit A l) = Some v"  
    unfolding assign_lit_def 
    apply (cases l)
    apply auto
    apply (cases l'; auto)
    apply (cases l'; clarsimp)
    done

  lemma assign_undec_pres_dec_clause: 
    "\<lbrakk> sem_lit' l A = None; sem_clause' C A = Some v \<rbrakk> \<Longrightarrow> sem_clause' C (assign_lit A l) = Some v"  
    unfolding sem_clause'_def
    by (force split: split_if_asm simp: assign_undec_pres_dec_lit)

  lemma sem_lit'_assign_conv: "sem_lit' l' (assign_lit A l) = (
    if l'=l then Some True 
    else if l'=neg_lit l then Some False 
    else sem_lit' l' A)"  
    unfolding assign_lit_def
    by (cases l; cases l'; auto)

  definition "is_unit_lit A C l \<equiv> l\<in>C \<and> sem_lit' l A = None \<and> (sem_clause' (C-{l}) A = Some False)"
  definition "is_unit_clause A C \<equiv> \<exists>l. is_unit_lit A C l"
  definition "the_unit_lit A C \<equiv> THE l. is_unit_lit A C l"

  abbreviation (input) "is_conflict_clause A C \<equiv> sem_clause' C A = Some False"
  abbreviation (input) "is_true_clause A C \<equiv> sem_clause' C A = Some True"
    
  definition "compat_assignment A \<sigma> \<equiv> \<forall>x v. A x = Some v \<longrightarrow> \<sigma> x = v"

  lemma compat_assignment_empty[simp]: "compat_assignment Map.empty \<sigma>" 
    unfolding compat_assignment_def by simp

  lemma sem_clause'_false_conv: 
    "sem_clause' C A = Some False \<longleftrightarrow> (\<forall>l\<in>C. sem_lit' l A = Some False)"
    unfolding sem_clause'_def by auto

  lemma sem_clause'_true_conv: 
    "sem_clause' C A = Some True \<longleftrightarrow> (\<exists>l\<in>C. sem_lit' l A = Some True)"
    unfolding sem_clause'_def by auto

  lemma the_unit_lit_eq[simp]: "is_unit_lit A C l \<Longrightarrow> the_unit_lit A C = l"
    unfolding is_unit_lit_def the_unit_lit_def sem_clause'_false_conv
    by force


  lemma is_unit_clauseE:
    assumes "is_unit_clause A C"
    obtains l C' where "C=insert l C'" "l\<notin>C'" "sem_lit' l A = None" "sem_clause' C' A = Some False"
      "the_unit_lit A C = l"
    using assms
  proof -
    from assms obtain l where IUL: "is_unit_lit A C l"
      unfolding is_unit_clause_def by blast
    note [simp] = the_unit_lit_eq[OF IUL]  

    from IUL have 1: "l\<in>C" "sem_lit' l A = None" "sem_clause' (C-{l}) A = Some False"
      unfolding is_unit_lit_def by blast+
    show thesis  
      apply (rule that[of l "C-{l}"])
      using 1
      by auto
  qed    

  lemma is_unit_clauseE':
    assumes "is_unit_clause A C"
    obtains l C' where "C=insert l C'" "l\<notin>C'" "sem_lit' l A = None" "sem_clause' C' A = Some False"
    by (rule is_unit_clauseE[OF assms])

  lemma sem_not_false_the_unit_lit:
    assumes "is_unit_lit A C l"
    assumes "l'\<in>C"
    assumes "sem_lit' l' A \<noteq> Some False"
    shows "l'=l"
    by (metis assms insert_Diff insert_iff is_unit_lit_def sem_clause'_insert_false)

  lemma sem_none_the_unit_lit:
    assumes "is_unit_lit A C l"
    assumes "l'\<in>C"
    assumes "sem_lit' l' A = None"
    shows "l'=l"
    using sem_not_false_the_unit_lit[OF assms(1,2)] assms(3) by auto

  lemma is_unit_litI: "\<lbrakk>l\<in>C; sem_clause' (C-{l}) A = Some False; sem_lit' l A = None\<rbrakk> \<Longrightarrow> is_unit_lit A C l"  
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
    using mk_disjoint_insert by (fastforce split: split_if_asm)

  lemma unit_clause_assign_dec: "is_unit_lit A C l \<Longrightarrow> sem_clause' C (assign_lit A l) = Some True"
    unfolding is_unit_lit_def sem_clause'_def
    by (force split: split_if_asm simp: sem_lit'_assign_conv)

  lemma unit_clause_sem: "is_unit_clause A C \<Longrightarrow> sem_clause' C A = None"  
    by (auto simp: is_unit_clause_def unit_clause_sem')

  lemma unit_contains_no_true:
    assumes "is_unit_clause A C"
    assumes "l\<in>C"
    shows "sem_lit' l A \<noteq> Some True"
    using assms unfolding is_unit_clause_def is_unit_lit_def
    by (force simp: sem_clause'_false_conv) 

  lemma two_nfalse_not_unit:
    assumes "l1\<in>C" "l2\<in>C" "l1\<noteq>l2" "sem_lit' l1 A \<noteq> Some False" "sem_lit' l2 A \<noteq> Some False"
    shows "\<not>is_unit_clause A C"  
    using assms
    unfolding is_unit_clause_def is_unit_lit_def
    by (auto simp: sem_clause'_false_conv)


  lemma conflict_clause_assign_indep:
    assumes "sem_clause' C (assign_lit A l) = Some False"
    assumes "neg_lit l \<notin> C"
    shows "sem_clause' C A = Some False"
    using assms
    by (auto simp: sem_clause'_def sem_lit'_assign_conv split: split_if_asm)
    
  lemma sem_lit'_assign_undec_conv: 
    "sem_lit' l' (assign_lit A l) = None \<longleftrightarrow> sem_lit' l' A = None \<and> var_of_lit l \<noteq> var_of_lit l'"  
    by (cases l; cases l'; auto)

  lemma unit_clause_assign_indep:
    assumes "is_unit_clause (assign_lit A l) C" 
    assumes "neg_lit l \<notin> C"  
    shows "is_unit_clause A C"
    using assms
    unfolding is_unit_clause_def is_unit_lit_def
    by (auto dest!: conflict_clause_assign_indep simp: sem_lit'_assign_undec_conv)

  lemma clause_assign_false_cases[consumes 1, case_names no_lit lit]:
    assumes "sem_clause' C (assign_lit A l) = Some False"  
    obtains "neg_lit l \<notin> C" "sem_clause' C A = Some False"
          | "neg_lit l \<in> C" "sem_clause' (C-{neg_lit l}) A = Some False"
  proof (cases)        
    assume A: "neg_lit l \<in> C" 
    with assms have "sem_clause' (C-{neg_lit l}) A = Some False"  
      by (auto simp: sem_clause'_def sem_lit'_assign_conv split: split_if_asm)
    with A show ?thesis by (rule that)
  next
    assume A: "neg_lit l \<notin> C"  
    with assms have "sem_clause' C A = Some False"  
      by (auto simp: sem_clause'_def sem_lit'_assign_conv split: split_if_asm)
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

    from clause_assign_false_cases[OF SCF] A have "sem_clause' C' A = Some False" by auto
    moreover from LUN have "sem_lit' lu A = None" by (simp add: sem_lit'_assign_undec_conv)
    ultimately have "is_unit_clause A C"
      by (auto simp: is_unit_clause_def is_unit_lit_def)
    with A show ?thesis by (rule that)
  qed      

  lemma sem_clause_ins_assign_not_false[simp]: "sem_clause' (insert l C) (assign_lit A l) \<noteq> Some False"
    unfolding sem_clause'_def by auto

  lemma sem_clause_ins_assign_not_unit[simp]: "\<not>is_unit_clause (assign_lit A l) (insert l C')"  
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
      by (force simp: compat_lit split: split_if_asm)
  end      

  subsubsection \<open>Models, Equivalence, and Redundancy\<close>

  definition "models' F A \<equiv> { \<sigma>. compat_assignment A \<sigma> \<and> sem_cnf F \<sigma>}"
  definition "sat' F A \<equiv> models' F A \<noteq> {}"
  definition "equiv' F A A' \<equiv> models' F A = models' F A'"

  lemma equiv'_refl[simp]: "equiv' F A A" unfolding equiv'_def by simp
  lemma equiv'_sym: "equiv' F A A' \<Longrightarrow> equiv' F A' A" unfolding equiv'_def by simp
  lemma equiv'_trans[trans]: "\<lbrakk> equiv' F A B; equiv' F B C \<rbrakk> \<Longrightarrow> equiv' F A C" unfolding equiv'_def by simp

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
    

  definition "implied_clause F A C \<equiv> models' (insert C F) A = models' F A"  
  definition "redundant_clause F A C \<equiv> (models' (insert C F) A = {}) \<longleftrightarrow> (models' F A = {})"

  lemma implied_is_redundant: "implied_clause F A C \<Longrightarrow> redundant_clause F A C"
    unfolding implied_clause_def redundant_clause_def by blast

  lemma add_redundant_sat_iff[simp]: "redundant_clause F A C \<Longrightarrow> sat' (insert C F) A = sat' F A"  
    unfolding redundant_clause_def sat'_def by auto

  lemma true_clause_implied: "sem_clause' C A = Some True \<Longrightarrow> implied_clause F A C"
    unfolding implied_clause_def models'_def 
    by (auto simp: compat_clause)


  lemma equiv'_map_empty_sym: 
    "NO_MATCH Map.empty A \<Longrightarrow> equiv' F Map.empty A \<longleftrightarrow> equiv' F A Map.empty"
    using equiv'_sym by auto


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


  inductive_set prop_unit_R :: "'a cnf \<Rightarrow> (('a\<rightharpoonup>bool) \<times> ('a\<rightharpoonup>bool)) set" for F where
    step: "\<lbrakk> C\<in>F; is_unit_lit A C l \<rbrakk> \<Longrightarrow> (A,assign_lit A l)\<in>prop_unit_R F"

  lemma prop_unit_R_Domain[simp]: "A \<in> Domain (prop_unit_R F) \<longleftrightarrow> (\<exists>C\<in>F. is_unit_clause A C)"
    by (auto elim!: prop_unit_R.cases simp: is_unit_clause_def dest: prop_unit_R.intros)

  lemma prop_unit_R_equiv:
    assumes "(A,A')\<in>(prop_unit_R F)\<^sup>*"  
    shows "equiv' F A A'"
    using assms
    apply induction
    apply simp
    apply (erule prop_unit_R.cases)
    using equiv'_trans unit_propagation by blast

  
  lemma wf_prop_unit_R: "finite F \<Longrightarrow> wf ((prop_unit_R F)\<inverse>)"
    apply (rule wf_subset[OF wf_measure[where f="\<lambda>A. card { C\<in>F. sem_clause' C A = None }"]])
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
        assume a3: "{C \<in> F. sem_clause' C (assign_lit A l) = None} = {C \<in> F. sem_clause' C A = None}"
        have "sem_clause' C A = None"
          using a2 by (metis unit_clause_sem')
        then show ?thesis
          using a3 a2 a1 unit_clause_assign_dec by force
      qed
    done  


subsection \<open>RUP and RAT Criteria\<close>

  definition "assign_all_negated A C \<equiv> let UD = {l\<in>C. sem_lit' l A = None} in
    A ++ (\<lambda>l. if Pos l\<in>UD then Some False else if Neg l \<in> UD then Some True else None)"

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
    assume CD: "\<forall>\<sigma>. compat_assignment (assign_all_negated A C) \<sigma> \<longrightarrow> \<not> sem_cnf F \<sigma>" 
    assume NS: "\<not> sem_clause C \<sigma>"
    
    from NS have "\<forall>l\<in>C. sem_lit l \<sigma> = False" by (auto simp: sem_clause_def)
    
    with COMPAT have "compat_assignment (assign_all_negated A C) \<sigma>"
      by (clarsimp simp: compat_assignment_def assign_all_negated_def split: split_if_asm) auto
    with S CD show False by blast
  qed  
      
  lemma abs_rat_criterion:
    assumes RAT: "\<exists>l\<in>C. 
      sem_lit' l A \<noteq> Some False 
    \<and> (\<forall>D\<in>F. neg_lit l \<in> D \<longrightarrow> implied_clause F A ((D-{neg_lit l}) \<union> C))"
    shows "redundant_clause F A C"
    unfolding redundant_clause_def
  proof 
    assume "models' F A = {}"
    with models_antimono[of F "insert C F" A] 
    show "models' (insert C F) A = {}" by blast
  next
    from RAT obtain l where
      LIC: "l\<in>C" and
      NF: "sem_lit' l A \<noteq> Some False" and
      RES: "\<forall>D\<in>F. neg_lit l \<in> D \<longrightarrow> implied_clause F A ((D-{neg_lit l}) \<union> C)"
      by blast

    {
      fix \<sigma>
      assume A: "\<sigma> \<in> models' F A"
      have "models' (insert C F) A \<noteq> {}" 
      proof (cases "sem_clause C \<sigma>")
        case True with A show ?thesis 
          by (auto simp: models'_def)
      next
        case False 
        from A have 
          COMPAT: "compat_assignment A \<sigma>" and MODEL: "sem_cnf F \<sigma>"
          unfolding models'_def by auto

        from False \<open>l\<in>C\<close> have NOT_L: "\<not>sem_lit l \<sigma>" by (auto simp: sem_clause_def)
        with NF COMPAT have UNDEC: "sem_lit' l A = None"
          apply (cases "sem_lit' l A")
          apply (simp_all add: compat_lit[OF COMPAT])
          done

        let ?\<sigma>' = "\<sigma>(var_of_lit l := is_pos l)"  

        from UNDEC COMPAT have COMPAT': "compat_assignment A ?\<sigma>'"
          unfolding compat_assignment_def
          by (cases l) auto

        from MODEL have "sem_cnf F ?\<sigma>'"
        proof (clarsimp simp: sem_cnf_def sem_clause_def)
          fix D 
          assume "D\<in>F"
          and "\<forall>C\<in>F. \<exists>l\<in>C. sem_lit l \<sigma>"
          then obtain ll where "ll\<in>D" and LL_HOLDS: "sem_lit ll \<sigma>" by auto

          show "\<exists>l'\<in>D. sem_lit l' (\<sigma>(var_of_lit l := is_pos l))"
          proof -
            {
              assume "var_of_lit l \<noteq> var_of_lit ll"
              from syn_indep_lit[OF this] LL_HOLDS have "sem_lit ll (\<sigma>(var_of_lit l := is_pos l))"
                by auto
              with \<open>ll\<in>D\<close> have ?thesis by blast  
            } moreover {
              assume "l = ll"
              hence ?thesis using \<open>ll\<in>D\<close> by (cases ll) force+
            } moreover {
              assume LLNL: "ll = neg_lit l"
              with RES \<open>D\<in>F\<close> \<open>ll\<in>D\<close> have "implied_clause F A (D - {neg_lit l} \<union> C)" by auto
              with COMPAT MODEL have "sem_clause (D - {neg_lit l} \<union> C) \<sigma>"
                unfolding implied_clause_def models'_def by auto
              with False obtain l2 where "l2\<in>D" "l2\<noteq>neg_lit l" "sem_lit l2 \<sigma>"  
                by (auto simp: sem_clause_def)
              with LLNL NOT_L have "var_of_lit l \<noteq> var_of_lit l2"  
                by (cases l2; cases l; auto)
              from syn_indep_lit[OF this, of \<sigma>] \<open>sem_lit l2 \<sigma>\<close> 
                have "sem_lit l2 (\<sigma>(var_of_lit l := is_pos l))"
                by auto
              with \<open>l2\<in>D\<close> have ?thesis by blast  
            } ultimately show ?thesis
              by (cases l; cases ll; auto)
          qed
        qed  
        moreover have "sem_clause C ?\<sigma>'"
          using \<open>l\<in>C\<close> unfolding sem_clause_def
          by (cases l; force)
        ultimately show ?thesis using COMPAT'
          unfolding models'_def by auto
      qed    
    } moreover assume "models' (insert C F) A = {}"
    ultimately show "models' F A = {}" by blast
  qed




end
