section \<open>Unit Propagation\<close>
theory Unit_Propagation
imports 
  SAT_Basic 
  "$AFP/Refine_Imperative_HOL/IICF/IICF"
  "$AFP/Abstract-Rewriting/Abstract_Rewriting"
  "~~/src/HOL/Library/Lattice_Syntax"
begin

  subsection \<open>Miscellaneous\<close>

  (* TODO: Move to Misc *)  
  lemma nth_append_first[simp]: "i<length l \<Longrightarrow> (l@l')!i = l!i"
    by (simp add: nth_append) 


  (* TODO: Move, close to RETURN_SPEC_refine *)
  lemma RETURN_RES_refine:
    assumes "\<exists>x'. (x,x')\<in>R \<and> x'\<in>X"
    shows "RETURN x \<le> \<Down>R (RES X)"
    using assms 
    by (auto simp: pw_le_iff refine_pw_simps)
  
  (* TODO: Move: Refine_Basic/convenience*)  
  lemma refine_IdI: "m \<le> m' \<Longrightarrow> m \<le> \<Down>Id m'" by simp

  (* TODO: Move, check DUP *)
  lemma map_leI[intro?]: "\<lbrakk>\<And>x v. m1 x = Some v \<Longrightarrow> m2 x = Some v\<rbrakk> \<Longrightarrow> m1\<subseteq>\<^sub>mm2"
    unfolding map_le_def by force
  lemma map_leD: "m1\<subseteq>\<^sub>mm2 \<Longrightarrow> m1 k = Some v \<Longrightarrow> m2 k = Some v"
    unfolding map_le_def by force

  (* TODO: Move *)
  lemma card_doubleton_eq_2_iff[simp]: "card {a,b} = 2 \<longleftrightarrow> a\<noteq>b" by auto

  lemma in_set_image_conv_nth: "f x \<in> f`set l \<longleftrightarrow> (\<exists>i<length l. f (l!i) = f x)"
    by (auto simp: in_set_conv_nth) (metis image_eqI nth_mem)

  lemma set_image_eq_pointwiseI: 
    assumes "length l = length l'"
    assumes "\<And>i. i<length l \<Longrightarrow> f (l!i) = f (l'!i)"  
    shows "f`set l = f`set l'"
    using assms
    by (fastforce simp: in_set_conv_nth in_set_image_conv_nth)
    
  lemma insert_swap_set_eq: "i<length l \<Longrightarrow> insert (l!i) (set (l[i:=x])) = insert x (set l)"
    by (auto simp: in_set_conv_nth nth_list_update split: split_if_asm)


  (* TODO: Move *)  
  text \<open>Allows refine-rules to add \<open>RELATES\<close> goals if they introduce hidden relations\<close>
  lemma RELATES_pattern[refine_dref_pattern]: "RELATES R \<Longrightarrow> RELATES R" .
  lemmas [refine_hsimp] = RELATES_def 

  (* TODO: Move. And join with SELECT, and whatever we have there! *)  
  definition "OBTAIN P \<equiv> ASSERT (\<exists>x. P x) \<then> SPEC P"
  (* TODO: Move *)  
  lemma OBTAIN_nofail[refine_pw_simps]: "nofail (OBTAIN P) \<longleftrightarrow> (\<exists>x. P x)"
    unfolding OBTAIN_def
    by (auto simp: refine_pw_simps)
  lemma OBTAIN_inres[refine_pw_simps]: "inres (OBTAIN P) x \<longleftrightarrow> (\<forall>x. \<not>P x) \<or> P x"
    unfolding OBTAIN_def
    by (auto simp: refine_pw_simps)
  lemma OBTAIN_rule[refine_vcg]: "\<lbrakk> \<exists>x. P x; \<And>x. P x \<Longrightarrow> Q x  \<rbrakk> \<Longrightarrow> OBTAIN P \<le> SPEC Q"
    unfolding OBTAIN_def
    by auto
  lemma OBTAIN_refine_iff: "OBTAIN P \<le>\<Down>R (OBTAIN Q) \<longleftrightarrow> (Ex Q \<longrightarrow> Ex P \<and> Collect P \<subseteq> R\<inverse>``Collect Q)"
    unfolding OBTAIN_def by (auto simp: pw_le_iff refine_pw_simps)
  
  lemma OBTAIN_refine[refine]:
    assumes "RELATES R"
    assumes "\<And>x. Q x \<Longrightarrow> Ex P"
    assumes "\<And>x y. \<lbrakk>Q x; P y\<rbrakk> \<Longrightarrow> \<exists>x'. (y,x')\<in>R \<and> Q x'"
    shows "OBTAIN P \<le>\<Down>R (OBTAIN Q)"
    using assms unfolding OBTAIN_refine_iff 
    by blast
  
  definition "SELECT P \<equiv> if \<exists>x. P x then RES {Some x| x. P x} else RETURN None"
  lemma SELECT_rule[refine_vcg]:
    assumes "\<And>x. P x \<Longrightarrow> Q (Some x)"
    assumes "\<forall>x. \<not>P x \<Longrightarrow> Q None"
    shows "SELECT P \<le> SPEC Q"
    unfolding SELECT_def
    using assms
    by auto

  lemma SELECT_refine_iff: "(SELECT P \<le>\<Down>(\<langle>R\<rangle>option_rel) (SELECT P')) 
    \<longleftrightarrow> (  
      (Ex P' \<longrightarrow> Ex P) \<and>
      (\<forall>x. P x \<longrightarrow> (\<exists>x'. (x,x')\<in>R \<and> P' x'))
    )"  
    by (force simp: SELECT_def pw_le_iff refine_pw_simps) 

  lemma SELECT_refine[refine]:
    assumes "RELATES R"
    assumes "\<And>x'. P' x' \<Longrightarrow> \<exists>x. P x"
    assumes "\<And>x. P x \<Longrightarrow> \<exists>x'. (x,x')\<in>R \<and> P' x'"
    shows "SELECT P \<le>\<Down>(\<langle>R\<rangle>option_rel) (SELECT P')"
    unfolding SELECT_refine_iff using assms by blast


  lemma eq_or_mem_image_simp[simp]: "{f l |l. l = a \<or> l\<in>B} = insert (f a) {f l|l. l\<in>B}" by blast



  lemma WCR_SN_move_out: (* TODO: Better name for lemma! *)
    fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<oplus>" 65)
    assumes CR: "WCR R"
    assumes SN: "SN_on R {s\<^sub>2,s\<^sub>1\<oplus>s\<^sub>2}"
    assumes PD: "\<And>s\<^sub>1 s\<^sub>2 s\<^sub>2'. (s\<^sub>2,s\<^sub>2')\<in>R \<Longrightarrow> (s\<^sub>1\<oplus>s\<^sub>2, s\<^sub>1\<oplus>s\<^sub>2')\<in>R"
    shows "some_NF R (s\<^sub>1 \<oplus> some_NF R s\<^sub>2) = some_NF R (s\<^sub>1 \<oplus> s\<^sub>2)" (is "?A=?B")
  proof -
    have "(s\<^sub>2,some_NF R s\<^sub>2) \<in> R\<^sup>*"
      by (metis SN SN_on_subset2 insert_commute some_NF subset_insertI)
    hence ST1: "(s\<^sub>1\<oplus>s\<^sub>2, s\<^sub>1\<oplus>some_NF R s\<^sub>2) \<in> R\<^sup>*"  
      by (induction) (blast intro: PD rtrancl.rtrancl_into_rtrancl)+
    also have ST2: "(s\<^sub>1\<oplus>some_NF R s\<^sub>2,?A) \<in> R\<^sup>*" 
      by (meson SN SN_on_subset2 calculation some_NF steps_reflect_SN_on subset_insertI)
    finally have ST: "(s\<^sub>1\<oplus>s\<^sub>2,?A)\<in>R\<^sup>*" .
    have ANF: "?A\<in>NF R" 
      by (meson SN SN_on_subset2 ST1 some_NF steps_reflect_SN_on subset_insertI)

    have "(s\<^sub>1\<oplus>s\<^sub>2,?B)\<in>R\<^sup>*" "?B\<in>NF R"
      apply (meson SN SN_on_subset2 some_NF subset_insertI)
      by (meson SN SN_on_subset2 some_NF subset_insertI)
    with ST ANF WCR_SN_on_imp_CR_on[OF CR SN] show "?A=?B" 
      by (meson CR_onD insertCI join_NF_imp_eq)
      
  qed    
    
  



  (* TODO: Move *)              
  lemma SN_on_invar:
    assumes INV: "R``I \<subseteq> I"
    assumes SN: "SN_on (R \<inter> I\<times>UNIV) A"
    shows "SN_on R (I\<inter>A)"
  proof (rule SN_onI)
    fix f
    assume "f 0 \<in> I \<inter> A" "\<forall>i. (f i, f(Suc i)) \<in> R"
    hence "(f i, f(Suc i)) \<in> R \<inter> I\<times>UNIV" for i
      apply (induction i)
      using INV
      by auto
    with SN \<open>f 0 \<in> I \<inter> A\<close> show False 
      by (cases rule: SN_onE[consumes 1]) auto
  qed    



  lemma fin_C:
    assumes "finite (vars_of_clause C)" 
    shows "finite C"
  proof -  
    have "C \<subseteq> Pos`vars_of_clause C \<union> Neg`vars_of_clause C"
      unfolding vars_of_clause_def var_of_lit_alt[abs_def]
      by (force split: literal.splits)
    from finite_subset[OF this] assms show ?thesis by auto
  qed  

  lemma fin_C': "\<lbrakk>finite (vars_of_cnf F); C\<in>F\<rbrakk> \<Longrightarrow> finite C"
    by (metis fin_C finite_Un insert_absorb vars_of_cnf_simps(2))

  lemma fin_vars_C_conv[simp]: "finite (vars_of_clause C)\<longleftrightarrow>finite C"
    using fin_C
    by (auto simp: vars_of_clause_def)  


  definition normalize_impl where
    "normalize_impl R s \<equiv> RECT (\<lambda>D s. 
      if \<exists>s'. (s,s')\<in>R then do {
        s \<leftarrow> SPEC (\<lambda>s'. (s,s')\<in>R);
        D s
      } else RETURN s
    ) s"

  lemma SN_on_conv_SN: "NO_MATCH UNIV A \<Longrightarrow> SN_on R A \<longleftrightarrow> SN (R \<inter> R\<^sup>*``A \<times> UNIV)"
    apply rule
    apply (metis (no_types, lifting) IntE SN_onE SN_onI SN_on_Image_rtrancl mem_Sigma_iff)
    by (metis SN_on_Image_conv SN_on_invar SN_on_trancl SN_on_trancl_imp_SN_on inf_top_right rtrancl_image_unfold_right trancl_Image_unfold_right)


  lemma normalize_impl_correct:
    assumes "SN_on R {s}"
    shows "normalize_impl R s \<le> SPEC (\<lambda>s'. (s,s')\<in>R\<^sup>* \<and> s' \<in> NF R)"
    unfolding normalize_impl_def
    apply (refine_vcg RECT_rule[where pre="\<lambda>s'. (s,s')\<in>R\<^sup>* " and V="(R \<inter> R\<^sup>*``{s} \<times> UNIV)\<inverse>"])
    apply (rule SN_imp_wf; simp add: SN_on_conv_SN[symmetric]; fact)
    apply simp
    apply (rule order_trans)
    apply rprems
    apply (simp add: step_preserves_SN_on)
    apply auto []
    apply auto []
    apply auto []
    apply auto []
    done

  lemma normalize_impl_CR_correct:   
    assumes "CR_on R {s}"
    assumes "SN_on R {s}"
    shows "normalize_impl R s \<le> RETURN (some_NF R s)"    
    apply (rule order_trans[OF normalize_impl_correct[OF assms(2)]])
    apply clarsimp
    by (meson CR_onD assms(1) assms(2) join_NF_imp_eq singletonI some_NF)

  subsection \<open>Equivalence of CNFs\<close>  

  text \<open>Two CNFs are equivalent if they have the same models\<close>
  definition cnf_equiv :: "'a cnf \<Rightarrow> 'a cnf \<Rightarrow> bool" (infix "=\<^sub>c" 50) 
    where
    "cnf_equiv F F' \<equiv> \<forall>\<sigma>. sem_cnf F \<sigma> \<longleftrightarrow> sem_cnf F' \<sigma>"

  lemma cnf_equivI[intro?]: "(\<And>\<sigma>. sem_cnf F \<sigma> = sem_cnf F' \<sigma>) \<Longrightarrow> F =\<^sub>c F'"
    unfolding cnf_equiv_def by auto

  lemma cnf_equiv_refl[simp, intro!]: "F=\<^sub>cF"
    unfolding cnf_equiv_def by auto
  lemma cnf_equiv_sym[simp]: "F=\<^sub>cF' \<longleftrightarrow> F'=\<^sub>cF"  
    unfolding cnf_equiv_def by auto
  lemma cnf_equiv_trans[trans]: "F\<^sub>1 =\<^sub>c F\<^sub>2 \<Longrightarrow> F\<^sub>2 =\<^sub>c F\<^sub>3 \<Longrightarrow> F\<^sub>1 =\<^sub>c F\<^sub>3"  
    unfolding cnf_equiv_def by auto

  subsection \<open>Unit Propagation\<close>  

  lemma sem_lit_var_conv: "sem_lit l \<sigma> \<longleftrightarrow> \<sigma> (var_of_lit l) = is_pos l"
    by (cases l) auto

  lemma propagate_unit:
    assumes "{l} \<in> F" 
    shows "insert {l} (set_lit F l) =\<^sub>c F"
  proof (intro cnf_equivI iffI)  
    fix \<sigma>
    assume "sem_cnf (insert {l} (set_lit F l)) \<sigma>"
    hence "sem_lit l \<sigma>" "sem_cnf (set_lit F l) \<sigma>" by auto
    with sem_cnf_set[of F \<sigma> l] show "sem_cnf F \<sigma>"
      by (auto simp: sem_lit_var_conv)
  next
    fix \<sigma>
    assume A: "sem_cnf F \<sigma>"
    with assms have "sem_lit l \<sigma>" unfolding sem_cnf_def by auto 
    with sem_cnf_set[of F \<sigma> l] A show "sem_cnf (insert {l} (set_lit F l)) \<sigma>"
      by (auto simp: sem_lit_var_conv)
  qed    


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

  lemma unit_clause_sem: "is_unit_clause A C \<Longrightarrow> sem_clause' C A = None"  
    apply (auto simp: is_unit_clause_def is_unit_lit_def sem_clause'_def split: split_if_asm)
    apply force
    by (metis insertE insert_Diff option.distinct(1) option.inject)

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




  subsection \<open>Two Watched Literals\<close>  

  subsubsection \<open>Abstraction Level 1\<close>
  
  text \<open>Abstractly, we regard a set of clauses with a partial assignment\<close>
  record 'a twl1 =
    clauses :: "'a cnf"
    assignment :: "'a \<rightharpoonup> bool"

  paragraph \<open>Operations\<close>  

  definition "twl1_empty \<equiv> \<lparr> clauses = {}, assignment = Map.empty \<rparr>"

  definition "twl1_has_conflict S \<equiv> \<exists>C\<in>twl1.clauses S. is_conflict_clause (twl1.assignment S) C"

  definition "twl1_add C S \<equiv> do {
    let A=assignment S;
    ASSERT (\<not>is_unit_clause A C \<and> \<not>is_conflict_clause A C \<and> card C > 1 \<and> \<not>twl1_has_conflict S);
    RETURN (S\<lparr>clauses := insert C (clauses S)\<rparr>)
  }"

  definition "twl1_may_delete C S \<equiv> do {
    ASSERT (\<not>is_conflict_clause (assignment S) C);
    RES {S\<lparr>clauses := clauses S - {C}\<rparr>, S}
  }"

  definition "prop_unit1_R \<equiv> { (\<lparr> clauses=F,assignment=A \<rparr>, \<lparr> clauses=F,assignment=assign_lit A (the_unit_lit A C) \<rparr>) | F A C. 
    C\<in>F \<and> is_unit_clause A C \<and> finite (vars_of_cnf F) }"

  text \<open>
    Abstract level unit propagation specification. 
    We either reached a conflict, or a normal form of unit propagation, i.e.,
    a state where no more units are to propagate.
    \<close>  
  definition "twl1_prop_unit S \<equiv> SPEC (\<lambda>S'. 
    (S,S')\<in>prop_unit1_R\<^sup>* \<and> (S'\<in>NF prop_unit1_R 
      \<or> (\<exists>C\<in>twl1.clauses S'. is_conflict_clause (twl1.assignment S') C))
  )"

  definition "twl1_assign_aux S l \<equiv> do {
    let A = assignment S;
    ASSERT (sem_lit' l A = None);
    RETURN (S\<lparr> assignment := assign_lit A l \<rparr>)
  }"

  definition "twl1_assign S l \<equiv> do {
    S \<leftarrow> twl1_assign_aux S l;
    twl1_prop_unit S
  }"

  text \<open>Assign negated literals in \<open>L\<close>\<close>
  definition "twl1_prepare_rup S L \<equiv> do {
    ASSERT (finite L \<and> (\<forall>l. l\<in>L \<longrightarrow> neg_lit l\<notin>L));
    let A=twl1.assignment S;
    ASSERT (\<forall>l\<in>L. sem_lit' l A = None);
    let A' = (\<lambda>x. if Neg x \<in> L then Some True else if Pos x \<in> L then Some False else None);
    let S=S\<lparr>twl1.assignment := A++A'\<rparr>;
    RETURN S
  }"

  text \<open>Check whether assigning negated literals in \<open>L\<close> leads to conflict.
    Return unchanged state. Also on this abstraction level, we could simply 
    use the old state, we will actually return a different state (with the 
    same abstraction) on lower abstraction levels. Returning the unchanged 
    state here will finally allow us to use the state in a linear fashion, and 
    thus refine it to be stored on the heap.
  \<close>
  definition "twl1_rup S L \<equiv> do {
    ASSERT (\<not>twl1_has_conflict S);
    S' \<leftarrow> twl1_prepare_rup S L;
    S' \<leftarrow> twl1_prop_unit S';
    RETURN (twl1_has_conflict S',S)
  }"

  paragraph \<open>Equivalence relation on partial assignments\<close>
  definition "twl1_sats S \<equiv> { \<sigma>. compat_assignment (assignment S) \<sigma> \<and> sem_cnf (clauses S) \<sigma> }"

  definition twl1_equiv (infix "=\<^sub>1" 50) where
    "S =\<^sub>1 S' \<equiv> twl1_sats S = twl1_sats S'"

  lemma twl1_equiv_refl[simp, intro!]: "S =\<^sub>1 S" by (simp add: twl1_equiv_def)
  lemma twl1_equiv_sym: "S =\<^sub>1 S' \<Longrightarrow> S' =\<^sub>1 S" by (auto simp add: twl1_equiv_def)
  lemma twl1_equiv_trans[trans]: "\<lbrakk>S1 =\<^sub>1 S2; S2 =\<^sub>1 S3\<rbrakk> \<Longrightarrow> S1 =\<^sub>1 S3" by (auto simp add: twl1_equiv_def)
  lemma twl1_equiv_reflI: "S=S' \<Longrightarrow> S =\<^sub>1 S'" by simp

  paragraph \<open>Lemmas\<close>

  lemma SN_prop_unit1_R: "SN prop_unit1_R"
    apply (rule wf_imp_SN)
    apply (rule wf_subset)
    apply (rule wf_measure[where f="\<lambda>S. card (vars_of_cnf (clauses S) - dom (assignment S))"])
    apply (clarsimp simp: prop_unit1_R_def)
    apply (rule psubset_card_mono)
      apply simp
      apply (erule is_unit_clauseE; simp)
      subgoal for F A C l C' proof (goal_cases)
        case 1
        assume "insert l C' \<in> F"
        hence "var_of_lit l \<in> vars_of_cnf F" 
          by (clarsimp simp: vars_of_cnf_def vars_of_clause_def; blast) 
        moreover assume "sem_lit' l A = None" 
        hence "var_of_lit l \<notin> dom A"
          by (cases l) auto
        ultimately show "vars_of_cnf F - insert (var_of_lit l) (dom A) \<subset> vars_of_cnf F - dom A"
          by blast
      qed
    done

  lemma prop_unit_pres_clauses: 
    assumes "(S,S')\<in>prop_unit1_R"
    shows "twl1.clauses S' = twl1.clauses S"
    using assms unfolding prop_unit1_R_def by auto
    
  lemma prop_unit_rtrancl_pres_clauses:  
    assumes "(S,S')\<in>prop_unit1_R\<^sup>*"
    shows "twl1.clauses S' = twl1.clauses S"
    using assms apply induction
    by (auto simp add: prop_unit_pres_clauses)


  text \<open>Implementation by looping over literals\<close>
  definition "twl1_prepare_rup_impl S L \<equiv> do {
    ASSERT (finite L \<and> (\<forall>l. l\<in>L \<longrightarrow> neg_lit l\<notin>L));
    let A=twl1.assignment S;
    ASSERT (\<forall>l\<in>L. sem_lit' l A = None);

    FOREACH L (\<lambda>l S. twl1_assign_aux S (neg_lit l)) S
  }"

  lemma twl1_prepare_rup_impl_correct: "twl1_prepare_rup_impl S L \<le> twl1_prepare_rup S L"
    unfolding twl1_prepare_rup_impl_def twl1_prepare_rup_def Let_def twl1_assign_aux_def
    apply (refine_vcg le_ASSERTI ASSERT_leI FOREACH_rule[where I="\<lambda>it S'. 
        S' = S\<lparr>twl1.assignment := twl1.assignment S ++
          (\<lambda>x. if Neg x \<in> L-it then Some True else if Pos x \<in> L-it then Some False else None)\<rparr>
        "])
    apply auto []
    apply auto []
    apply auto []
    apply auto []
    subgoal for l it S'
      apply (cases l)
      apply (fastforce simp: map_add_None)+
      done

    subgoal for l it S'
      apply (cases l; cases S)
      by (auto simp: it_step_insert_iff map_add_def intro!: ext)
    subgoal by (auto cong: if_cong)  
    done




  subsubsection \<open>Abstraction Level 2\<close>


  type_synonym 'a clause2 = "'a literal \<times> 'a literal \<times> 'a literal list"

  definition "cl2_watched \<equiv> \<lambda>(w1,w2,_). {w1,w2}"
  definition "cl2_\<alpha> \<equiv> \<lambda>(w1,w2,ls). insert w1 (insert w2 (set ls))"

  lemma watched_ss_C: "cl2_watched C \<subseteq> cl2_\<alpha> C"
    unfolding cl2_watched_def cl2_\<alpha>_def by auto


  definition "l_assignment L \<equiv> \<lambda>x. if Pos x \<in> L then Some True else if Neg x \<in> L then Some False else None"

  lemma l_assign_empty[simp]: "l_assignment {} = Map.empty"
    unfolding l_assignment_def by auto


  record 'a twl2 = 
    clause_db :: "'a clause2 list"
    valid_idxs :: "nat set"
    assignment :: "'a \<rightharpoonup> bool"
    pending :: "'a literal set"
    conflict :: bool

    
  locale twl2_defs = 
    fixes S :: "'a twl2"
  begin
    abbreviation "CLdb \<equiv> clause_db S"
    abbreviation "VIs \<equiv> valid_idxs S"

    abbreviation "A \<equiv> assignment S"
    abbreviation "P \<equiv> pending S"
    abbreviation "CN \<equiv> conflict S"

    definition "CL \<equiv> {CLdb!i | i. i\<in>VIs}"
    definition "F \<equiv> cl2_\<alpha>`CL"

    lemma CL_update_approx: "\<lbrakk> C\<in>twl2_defs.CL (S\<lparr> clause_db := CLdb[i := C'] \<rparr>); i\<in>VIs; i<length CLdb \<rbrakk>
      \<Longrightarrow> C=C' \<or> C\<in>CL"
      by (auto simp: twl2_defs.CL_def twl2_defs.F_def nth_list_update)

    lemma F_update_eq: "\<lbrakk>i\<in>VIs; i<length CLdb; cl2_\<alpha> C' = cl2_\<alpha> (CLdb!i)\<rbrakk> 
      \<Longrightarrow> twl2_defs.F (S\<lparr> clause_db := CLdb[i := C'] \<rparr>) = F"
      apply (clarsimp simp: twl2_defs.CL_def twl2_defs.F_def nth_list_update; safe; (auto;fail)?)
      apply (simp)
    proof -
      fix a :: "'a literal" and aa :: "'a literal" and b :: "'a literal list" and ia :: nat
      assume a1: "ia \<in> VIs"
      assume "cl2_\<alpha> C' = cl2_\<alpha> (CLdb ! i)"
      then have "\<exists>p. cl2_\<alpha> (CLdb ! ia) = cl2_\<alpha> p \<and> (\<exists>n. (i = n \<longrightarrow> p = C' \<and> n \<in> VIs) \<and> (i \<noteq> n \<longrightarrow> p = CLdb ! n \<and> n \<in> VIs))"
        using a1 by (metis (no_types))
      then show "cl2_\<alpha> (CLdb ! ia) \<in> cl2_\<alpha> ` {p. \<exists>n. (i = n \<longrightarrow> p = C' \<and> n \<in> VIs) \<and> (i \<noteq> n \<longrightarrow> p = CLdb ! n \<and> n \<in> VIs)}"
        by blast
    qed
      



  end  

  lemma twl2_CL_update[simp]: 
    "twl2_defs.CL (S\<lparr> assignment := A' \<rparr>) = twl2_defs.CL S"
    "twl2_defs.CL (S\<lparr> pending := P' \<rparr>) = twl2_defs.CL S"
    "twl2_defs.CL (S\<lparr> conflict := CN' \<rparr>) = twl2_defs.CL S"
    unfolding twl2_defs.CL_def by simp_all

  lemma twl2_F_update[simp]: 
    "twl2_defs.F (S\<lparr> assignment := A' \<rparr>) = twl2_defs.F S"
    "twl2_defs.F (S\<lparr> pending := P' \<rparr>) = twl2_defs.F S"
    "twl2_defs.F (S\<lparr> conflict := CN' \<rparr>) = twl2_defs.F S"
    unfolding twl2_defs.F_def by simp_all



  definition "twl2_\<alpha> S \<equiv> \<lparr>
    twl1.clauses = twl2_defs.F S,
    assignment = assignment S
  \<rparr>"


  locale twl2_struct_invar = twl2_defs S 
    for S :: "'a twl2"
    +
    assumes pending_finite[simp, intro!]: "finite P"
    assumes pending_set: "l\<in>P \<Longrightarrow> sem_lit' l A = Some True"
    assumes two_watched: "C\<in>CL \<Longrightarrow> card (cl2_watched C) = 2"
    assumes vi_valid[simp, intro]: "i\<in>VIs \<Longrightarrow> i<length CLdb"
  begin

    lemma watchedE: 
      assumes "C\<in>CL"
      obtains w1 w2 where "cl2_watched C = {w1,w2}" "w1\<noteq>w2"
      using two_watched[OF assms]
      apply (cases C) 
      by (auto simp: cl2_watched_def card_Suc_eq eval_nat_numeral)

    lemma watched_ne:
      assumes "(w1,w2,ls)\<in>CL"
      shows "w1\<noteq>w2"
      using assms
      by (metis (no_types, lifting) cl2_watched_def doubleton_eq_iff insert_absorb2 prod.simps(2) watchedE)

    lemma finite_VIs[simp, intro!]: "finite VIs"
      apply (rule finite_subset[where B="{0..<length CLdb}"])
      by auto

    lemma finite_CL[simp, intro!]: "finite CL"  
      unfolding CL_def by auto

  end

  locale twl2_pending_invar = twl2_struct_invar +
    assumes conflict_imp: "CN \<Longrightarrow> \<exists>C\<in>F. is_conflict_clause A C"
    assumes conflict_covered: "\<lbrakk>C\<in>CL; is_conflict_clause A (cl2_\<alpha> C)\<rbrakk> \<Longrightarrow> cl2_watched C\<inter>neg_lit`P \<noteq> {} \<or> CN"
    assumes unit_covered: "\<lbrakk>C\<in>CL; is_unit_clause A (cl2_\<alpha> C) \<rbrakk> \<Longrightarrow> cl2_watched C\<inter>neg_lit`P \<noteq> {} \<or> CN"
    assumes watched1: "\<lbrakk> \<not>CN; (w1,w2,ls) \<in> CL; sem_lit' w1 A = Some False; sem_lit' w2 A \<noteq> Some True \<rbrakk> \<Longrightarrow> w1\<in>neg_lit`P \<or> (\<forall>l\<in>set ls. sem_lit' l A = Some False)"
    assumes watched2: "\<lbrakk> \<not>CN; (w1,w2,ls) \<in> CL; sem_lit' w1 A \<noteq> Some True; sem_lit' w2 A = Some False \<rbrakk> \<Longrightarrow> w2\<in>neg_lit`P \<or> (\<forall>l\<in>set ls. sem_lit' l A = Some False)"
  begin  
    lemma conflict_watched: 
      assumes CL: "C\<in>CL"
      assumes C: "is_conflict_clause A (cl2_\<alpha> C)"
      obtains w1 w2 where "cl2_watched C = {w1,w2}" "w1\<noteq>w2" "sem_lit' w1 A = Some False" "sem_lit' w2 A = Some False"
    proof -
      obtain w1 w2 where [simp]: "cl2_watched C = {w1, w2}" and NE: "w1\<noteq>w2" 
        using watchedE[OF CL] .
      from C watched_ss_C[of C] have "sem_lit' w1 A = Some False" "sem_lit' w2 A = Some False"
        by (auto simp: sem_clause'_false_conv)
      with NE show ?thesis
        by (rule_tac that[of w1 w2]) auto
    qed    
  end


  locale twl2_invar = twl2_struct_invar + twl2_pending_invar +
    assumes no_pending_or_conf: "P = {} \<or> CN"
  begin
    lemma conflict_iff_cn: "CN \<longleftrightarrow> (\<exists>C\<in>F. is_conflict_clause A C)"
      using conflict_imp conflict_covered
      using no_pending_or_conf
      by (auto simp: F_def)

  end  

  locale twl2_bt_base_defs = twl2_defs S + IBT: twl2_defs S\<^sub>b
    for S\<^sub>b S :: "'a twl2"
  begin  
    abbreviation "CL\<^sub>b \<equiv> IBT.CL"
    abbreviation "A\<^sub>b \<equiv> IBT.A"
  end

  locale twl2_bt_base_invar = 
    twl2_bt_base_defs S\<^sub>b S 
    + IBT: twl2_invar S\<^sub>b
    + twl2_struct_invar S 
    for S\<^sub>b S :: "'a twl2"
  +  
    assumes base_no_conf[simp]: "\<not>IBT.CN"
    assumes bt_sub: "A\<^sub>b \<subseteq>\<^sub>m A"
    assumes bt_abs_VIs[simp]: "IBT.VIs = VIs"
    assumes bt_abs_CLdb: "i\<in>VIs \<Longrightarrow> cl2_\<alpha> (IBT.CLdb!i) = cl2_\<alpha> (CLdb!i)"
    assumes bt_watched_repl: "\<lbrakk>i\<in>VIs; w\<in>cl2_watched (CLdb!i); w\<notin>cl2_watched (IBT.CLdb!i)\<rbrakk> \<Longrightarrow> sem_lit' w A\<^sub>b \<noteq> Some False"
    assumes bt_watched_keep: "\<lbrakk>i\<in>VIs; w\<in>cl2_watched (IBT.CLdb!i); w\<notin>cl2_watched (CLdb!i) \<rbrakk> \<Longrightarrow> sem_lit' w A\<^sub>b \<noteq> Some True"
  begin  

    lemma no_pending[simp]: "IBT.P={}"
      using IBT.no_pending_or_conf by simp

    lemma bt_abs_CL: "cl2_\<alpha>`CL\<^sub>b = cl2_\<alpha>`CL"  
      using bt_abs_CLdb unfolding CL_def IBT.CL_def 
      by clarsimp blast
      

    lemma no_units: "C\<in>CL\<^sub>b \<Longrightarrow> \<not>is_unit_clause A\<^sub>b (cl2_\<alpha> C)"  
      using "IBT.unit_covered" by (cases C) auto

    lemma no_conflicts: "C\<in>CL\<^sub>b \<Longrightarrow> \<not>is_conflict_clause A\<^sub>b (cl2_\<alpha> C)"  
      using "IBT.conflict_covered" by (cases C) auto

    lemma bt_sem_nd_keep: "sem_lit' l A \<noteq> Some v \<Longrightarrow> sem_lit' l A\<^sub>b \<noteq> Some v"  
      using bt_sub by (cases l) (auto dest: map_leD)

    lemma bt_sub_assign_undec: "sem_lit' l A = None \<Longrightarrow> A\<^sub>b \<subseteq>\<^sub>m assign_lit A l"  
      apply (rule map_leI)
      using bt_sub by (cases l) (auto dest: map_leD)

    lemma obtain_b_clause:
      assumes "C\<in>CL"
      obtains C\<^sub>b where "C\<^sub>b\<in>CL\<^sub>b" "cl2_\<alpha> C = cl2_\<alpha> C\<^sub>b"
      using assms bt_abs_CL
      by (metis (mono_tags, hide_lams) image_iff)


  end

  locale twl2_invar_aux = twl2_bt_base_invar + twl2_pending_invar
  begin

  end

  locale twl2_bt_invar = twl2_invar_aux + twl2_invar
  begin
    lemma backtrack_invar: "twl2_invar (S\<lparr> assignment := A\<^sub>b, pending := {}, conflict := False \<rparr>)"
      apply unfold_locales
      apply clarsimp_all

      subgoal by (rule two_watched)
      subgoal using IBT.conflict_covered by (fastforce elim!: obtain_b_clause)
      subgoal using IBT.unit_covered by (fastforce elim!: obtain_b_clause)
      (* TODO/FIXME: The next proof steps have four nearly identical cases, 
        each with a lot of analogous reasoning *)
      subgoal for w1 w2 ls l
      proof -
        assume CL: "(w1, w2, ls) \<in> CL"
        then obtain i where [simp]: "i\<in>VIs" and CLI: "CLdb!i=(w1, w2, ls)"
          by (auto simp: CL_def)

        obtain w1b w2b lsb where CLBI: "IBT.CLdb!i = (w1b,w2b,lsb)" by (cases "IBT.CLdb!i")
        
        from CLBI have CLB: "(w1b,w2b,lsb)\<in>CL\<^sub>b" 
          by (auto simp: IBT.CL_def dest: sym) 

        assume 
          WFALSE: "sem_lit' w1 A\<^sub>b = Some False" 
          and "sem_lit' w2 A\<^sub>b \<noteq> Some True" "l \<in> set ls"
        hence NO_TW: "w\<in>cl2_watched (CLdb!i) \<Longrightarrow> sem_lit' w A\<^sub>b \<noteq> Some True" for w
          by (auto simp: cl2_watched_def CLI)

        from bt_watched_repl[of i w1] WFALSE have "w1=w1b \<or> w1=w2b" by (auto simp: CLI CLBI cl2_watched_def)
        thus "sem_lit' l A\<^sub>b = Some False"
        proof (rule disjE)
          assume [simp]: "w1=w1b"
          have W2BNT: "sem_lit' w2b A\<^sub>b \<noteq> Some True" 
            using bt_watched_keep[of i w2b] NO_TW
            by (auto simp: cl2_watched_def CLI CLBI)
          with IBT.watched1[OF _ CLB _] WFALSE have LSB_FALSE: "(\<forall>l\<in>set lsb. sem_lit' l A\<^sub>b = Some False)" 
            by auto

          show ?thesis using W2BNT
          proof (cases "sem_lit' w2b A\<^sub>b"; simp?)
            assume "sem_lit' w2b A\<^sub>b = None"
            with LSB_FALSE WFALSE have "is_unit_lit A\<^sub>b (cl2_\<alpha> (w1b, w2b, lsb)) w2b"
              by (rule_tac is_unit_litI) (auto simp: cl2_\<alpha>_def sem_clause'_false_conv)
            with no_units[OF CLB] have False by (auto simp: is_unit_clause_def)  
            thus ?thesis ..
          next  
            assume "sem_lit' w2b A\<^sub>b = Some False"
            with LSB_FALSE WFALSE have "is_conflict_clause A\<^sub>b (cl2_\<alpha> (w1b, w2b, lsb))"
              by (auto simp: cl2_\<alpha>_def sem_clause'_false_conv)
            with no_conflicts[OF CLB] have False by auto  
            thus ?thesis ..
          qed
        next  
          assume [simp]: "w1=w2b"
          have W1BNT: "sem_lit' w1b A\<^sub>b \<noteq> Some True" 
            using bt_watched_keep[of i w1b] NO_TW
            by (auto simp: cl2_watched_def CLI CLBI)
          with IBT.watched2[OF _ CLB _] WFALSE have LSB_FALSE: "(\<forall>l\<in>set lsb. sem_lit' l A\<^sub>b = Some False)" 
            by auto

          show ?thesis using W1BNT
          proof (cases "sem_lit' w1b A\<^sub>b"; simp?)
            assume "sem_lit' w1b A\<^sub>b = None"
            with LSB_FALSE WFALSE have "is_unit_lit A\<^sub>b (cl2_\<alpha> (w1b, w2b, lsb)) w1b"
              by (rule_tac is_unit_litI) (auto simp: cl2_\<alpha>_def sem_clause'_false_conv)
            with no_units[OF CLB] have False by (auto simp: is_unit_clause_def)  
            thus ?thesis ..
          next  
            assume "sem_lit' w1b A\<^sub>b = Some False"
            with LSB_FALSE WFALSE have "is_conflict_clause A\<^sub>b (cl2_\<alpha> (w1b, w2b, lsb))"
              by (auto simp: cl2_\<alpha>_def sem_clause'_false_conv)
            with no_conflicts[OF CLB] have False by auto  
            thus ?thesis ..
          qed
        qed  
      qed      
      subgoal for w1 w2 ls l
      proof -
        assume CL: "(w1, w2, ls) \<in> CL"
        then obtain i where [simp]: "i\<in>VIs" and CLI: "CLdb!i=(w1, w2, ls)"
          by (auto simp: CL_def)

        obtain w1b w2b lsb where CLBI: "IBT.CLdb!i = (w1b,w2b,lsb)" by (cases "IBT.CLdb!i")
        
        from CLBI have CLB: "(w1b,w2b,lsb)\<in>CL\<^sub>b" 
          by (auto simp: IBT.CL_def dest: sym)

        assume 
          WFALSE: "sem_lit' w2 A\<^sub>b = Some False" 
          and "sem_lit' w1 A\<^sub>b \<noteq> Some True" "l \<in> set ls"
        hence NO_TW: "w\<in>cl2_watched (CLdb!i) \<Longrightarrow> sem_lit' w A\<^sub>b \<noteq> Some True" for w
          by (auto simp: cl2_watched_def CLI)
        
        from bt_watched_repl[of i w2] WFALSE have "w2=w1b \<or> w2=w2b" by (auto simp: CLI CLBI cl2_watched_def)
        thus "sem_lit' l A\<^sub>b = Some False"
        proof (rule disjE)
          assume [simp]: "w2=w1b"
          have W2BNT: "sem_lit' w2b A\<^sub>b \<noteq> Some True" 
            using bt_watched_keep[of i w2b] NO_TW
            by (auto simp: cl2_watched_def CLI CLBI)
          with IBT.watched1[OF _ CLB _] WFALSE have LSB_FALSE: "(\<forall>l\<in>set lsb. sem_lit' l A\<^sub>b = Some False)" 
            by auto

          show ?thesis using W2BNT
          proof (cases "sem_lit' w2b A\<^sub>b"; simp?)
            assume "sem_lit' w2b A\<^sub>b = None"
            with LSB_FALSE WFALSE have "is_unit_lit A\<^sub>b (cl2_\<alpha> (w1b, w2b, lsb)) w2b"
              by (rule_tac is_unit_litI) (auto simp: cl2_\<alpha>_def sem_clause'_false_conv)
            with no_units[OF CLB] have False by (auto simp: is_unit_clause_def)  
            thus ?thesis ..
          next  
            assume "sem_lit' w2b A\<^sub>b = Some False"
            with LSB_FALSE WFALSE have "is_conflict_clause A\<^sub>b (cl2_\<alpha> (w1b, w2b, lsb))"
              by (auto simp: cl2_\<alpha>_def sem_clause'_false_conv)
            with no_conflicts[OF CLB] have False by auto  
            thus ?thesis ..
          qed
        next  
          assume [simp]: "w2=w2b"
          have W1BNT: "sem_lit' w1b A\<^sub>b \<noteq> Some True" 
            using bt_watched_keep[of i w1b] NO_TW
            by (auto simp: cl2_watched_def CLI CLBI)
          with IBT.watched2[OF _ CLB _] WFALSE have LSB_FALSE: "(\<forall>l\<in>set lsb. sem_lit' l A\<^sub>b = Some False)" 
            by auto

          show ?thesis using W1BNT
          proof (cases "sem_lit' w1b A\<^sub>b"; simp?)
            assume "sem_lit' w1b A\<^sub>b = None"
            with LSB_FALSE WFALSE have "is_unit_lit A\<^sub>b (cl2_\<alpha> (w1b, w2b, lsb)) w1b"
              by (rule_tac is_unit_litI) (auto simp: cl2_\<alpha>_def sem_clause'_false_conv)
            with no_units[OF CLB] have False by (auto simp: is_unit_clause_def)  
            thus ?thesis ..
          next  
            assume "sem_lit' w1b A\<^sub>b = Some False"
            with LSB_FALSE WFALSE have "is_conflict_clause A\<^sub>b (cl2_\<alpha> (w1b, w2b, lsb))"
              by (auto simp: cl2_\<alpha>_def sem_clause'_false_conv)
            with no_conflicts[OF CLB] have False by auto  
            thus ?thesis ..
          qed
        qed  
      qed      
      done            
            

    lemma backtrack_\<alpha>: "twl2_\<alpha> (S\<lparr> assignment := A\<^sub>b, pending := {}, conflict := False \<rparr>) = twl2_\<alpha> S\<^sub>b"  
      apply (clarsimp simp: twl2_\<alpha>_def twl2_defs.F_def)
      by (metis bt_abs_CL set_map)


  end

  lemma (in twl2_invar) to_bt_invar: "\<not>conflict S \<Longrightarrow> twl2_bt_invar S S"
    apply unfold_locales by auto
  
  lemma (in twl2_bt_invar) to_invar: "twl2_invar S" by unfold_locales


  definition "twl2_rel_aux S\<^sub>b \<equiv> br twl2_\<alpha> (twl2_invar_aux S\<^sub>b)"
  definition "twl2_bt_rel S\<^sub>b \<equiv> br twl2_\<alpha> (twl2_bt_invar S\<^sub>b)"

  definition "twl2_rel \<equiv> br twl2_\<alpha> twl2_invar"

  lemma twl2_bt_rel_ss: "twl2_bt_rel S\<^sub>b \<subseteq> twl2_rel_aux S\<^sub>b"
    unfolding twl2_bt_rel_def twl2_rel_aux_def br_def
    by (auto simp: twl2_bt_invar.axioms)

  lemma twl2_to_bt_rel: "\<not>conflict S \<Longrightarrow> (S,S1)\<in>twl2_rel \<Longrightarrow> (S,S1)\<in>twl2_bt_rel S"
    using twl2_invar.to_bt_invar 
    unfolding twl2_bt_rel_def twl2_rel_def br_def by auto

  lemma twl2_rel_ss: "twl2_bt_rel S\<^sub>b \<subseteq> twl2_rel"  
    using twl2_bt_invar.to_invar 
    unfolding twl2_bt_rel_def twl2_rel_def br_def by auto
    
  lemma (in twl2_invar_aux) no_P_is_invar: "P={} \<Longrightarrow> twl2_bt_invar S\<^sub>b S"  
    apply unfold_locales ..

  lemma (in twl2_invar_aux) conf_is_invar: "CN \<Longrightarrow> twl2_bt_invar S\<^sub>b S"  
    apply unfold_locales ..


  definition "prop_unit2_R \<equiv> {(S,S'). 
      (
        (twl2_\<alpha> S,twl2_\<alpha> S')\<in>prop_unit1_R\<^sup>+ 
      \<or> (twl2_\<alpha> S' = twl2_\<alpha> S \<and> pending S' \<subset> pending S \<and> finite (pending S))
      )}"

  lemma prop_unit2_RI: 
    "(twl2_\<alpha> S,twl2_\<alpha> S')\<in>prop_unit1_R\<^sup>+ \<Longrightarrow> (S,S') \<in> prop_unit2_R"
    "\<lbrakk>twl2_\<alpha> S' = twl2_\<alpha> S; pending S' \<subset> pending S; finite (pending S)\<rbrakk> \<Longrightarrow> (S,S') \<in> prop_unit2_R"
    by (auto simp: prop_unit2_R_def)

  lemma wf_prop_unit2_R[simp, intro!]: "wf (prop_unit2_R\<inverse>)"  
  proof (rule wf_subset)
    show "prop_unit2_R\<inverse> \<subseteq> inv_image ((prop_unit1_R\<inverse>)\<^sup>+ <*lex*> finite_psubset) (\<lambda>S. (twl2_\<alpha> S, pending S))"
      (is "_ \<subseteq> ?U")
      unfolding prop_unit2_R_def twl2_\<alpha>_def
      by (auto simp: trancl_converse)

    from SN_prop_unit1_R[THEN SN_imp_SN_trancl, THEN SN_imp_wf]
    show "wf ?U" by (auto simp: trancl_converse)
  qed

  lemma prop_unit2_R_append_unit:
    assumes "(S,S')\<in>prop_unit2_R"
    assumes "(twl2_\<alpha> S',twl2_\<alpha> S'')\<in>prop_unit1_R"
    shows "(S,S'')\<in>prop_unit2_R"
    using assms
    unfolding prop_unit2_R_def
    by (auto dest: trancl_into_trancl) 



  locale twl2_prop_loop_invar_defs = twl2_defs S for it :: "nat set" and S :: "'a twl2"
  begin  
    definition "CLC \<equiv> {CLdb!i | i. i\<in>VIs \<and> i\<notin>it}"

    lemma CLC_empty: "it={} \<Longrightarrow> CLC = CL"
      unfolding CLC_def CL_def by auto

  end

  locale twl2_prop_loop_invar = I0: twl2_invar_aux S\<^sub>b S0 + twl2_prop_loop_invar_defs it S + twl2_bt_base_invar S\<^sub>b S 
    for S\<^sub>b S0 :: "'a twl2" 
    and l_rem :: "'a literal" 
    and it :: "nat set" 
    and S :: "'a twl2" +
    assumes it_valid[simp]: "i\<in>it \<Longrightarrow> i\<in>VIs"
    assumes clauses_len_eq[simp]: "length I0.CLdb = length CLdb"
    assumes valid_idx_eq[simp]: "I0.VIs = VIs"
    assumes clauses_unproc_eq[simp]: "i\<in>it \<Longrightarrow> I0.CLdb!i = CLdb!i"

    assumes new_ass_pending: "A x = I0.A x \<or> (I0.A x = None \<and> x \<in> var_of_lit`P)"
    assumes pending_mono: "I0.P - {l_rem} \<subseteq> P"

    assumes prop_steps: "(S0, S) \<in> prop_unit2_R"
    assumes conflict_imp: "CN \<Longrightarrow> \<exists>C\<in>F. is_conflict_clause A C"
    assumes conflict_covered: "\<lbrakk>C\<in>CLC; is_conflict_clause A (cl2_\<alpha> C)\<rbrakk> \<Longrightarrow> cl2_watched C\<inter>neg_lit`P \<noteq> {} \<or> CN"
    assumes unit_covered: "\<lbrakk>C\<in>CLC; is_unit_clause A (cl2_\<alpha> C) \<rbrakk> \<Longrightarrow> cl2_watched C\<inter>neg_lit`P \<noteq> {} \<or> CN"
    assumes watched1: "\<lbrakk> (w1,w2,ls) \<in> CLC; sem_lit' w1 A = Some False; sem_lit' w2 A \<noteq> Some True \<rbrakk> \<Longrightarrow> w1\<in>neg_lit`P \<or> (\<forall>l\<in>set ls. sem_lit' l A = Some False)"
    assumes watched2: "\<lbrakk> (w1,w2,ls) \<in> CLC; sem_lit' w1 A \<noteq> Some True; sem_lit' w2 A = Some False \<rbrakk> \<Longrightarrow> w2\<in>neg_lit`P \<or> (\<forall>l\<in>set ls. sem_lit' l A = Some False)"
  begin
    lemma empty_imp_invar: "it={} \<Longrightarrow> twl2_invar_aux S\<^sub>b S"
      apply unfold_locales
      using CLC_empty conflict_imp conflict_covered unit_covered watched1 watched2
      by simp_all

    lemma false_ass_pending:  
      assumes "sem_lit' l I0.A \<noteq> Some False"
      assumes "sem_lit' l A = Some False"
      shows "neg_lit l \<in> P"
      apply (cases l)
      using assms
      apply clarsimp_all
      apply (metis (no_types, lifting) assms(2) imageE new_ass_pending option.inject pending_set var_of_lit.elims)
      apply (metis (no_types, lifting) assms(2) imageE new_ass_pending option.inject pending_set var_of_lit.elims)
      done
      
    lemma ass_keep_decided:   
      "I0.A x = Some v \<Longrightarrow> A x = Some v"
      using new_ass_pending
      apply (metis option.simps(3))
      done      

    lemma ass_keep_undecided:   
      "A x = None \<Longrightarrow> I0.A x = None"
      using new_ass_pending by metis

    lemma ass_lit_keep_decided:
      assumes "sem_lit' l I0.A = Some v"
      shows "sem_lit' l A = Some v"
      using assms new_ass_pending
      by (cases l) (auto simp: ass_keep_decided)

    lemma ass_lit_keep_undecided:
      assumes "sem_lit' l A = None"
      shows "sem_lit' l I0.A = None"
      using assms new_ass_pending
      apply (cases "sem_lit' l I0.A") 
      using ass_lit_keep_decided[of l]
      by (auto)

    lemmas ass_keep = ass_keep_decided ass_keep_undecided 
      ass_lit_keep_decided ass_lit_keep_undecided

  end


  definition "twl2_empty \<equiv> \<lparr> clause_db = [], valid_idxs = {}, assignment = Map.empty, pending={}, conflict=False \<rparr>"
  lemma twl2_empty_refine: "(twl2_empty,twl1_empty) \<in> twl2_rel"
    apply (simp add: twl2_rel_def br_def twl1_empty_def twl2_empty_def twl2_\<alpha>_def twl2_defs.F_def twl2_defs.CL_def)
    apply unfold_locales
    apply (simp_all add: twl2_defs.CL_def)
    done

  definition "twl2_assign_aux S l \<equiv> 
    ASSERT (sem_lit' l (assignment S) = None \<and> l\<notin> pending S) \<then> 
    RETURN (S\<lparr>
      assignment := assign_lit (assignment S) l,
      pending := insert l (pending S)
    \<rparr>)"

  definition "twl2_watchset S l \<equiv> {i. i\<in>valid_idxs S \<and> neg_lit l \<in> cl2_watched (clause_db S!i)}"

  lemma twl2_watchset_update[simp]:
    "twl2_watchset (S\<lparr>pending := P'\<rparr>) l = twl2_watchset S l"
    "twl2_watchset (S\<lparr>assignment := A'\<rparr>) l = twl2_watchset S l"
    "twl2_watchset (S\<lparr>conflict := C'\<rparr>) l = twl2_watchset S l"
    unfolding twl2_watchset_def by simp_all

  lemma (in twl2_struct_invar) twl2_watchset_finite[simp, intro!]: "finite (twl2_watchset S l)"
    unfolding twl2_watchset_def
    by auto

  definition "twl2_propagate_step S\<^sub>b    S0 \<equiv> do {
    (* Get and remove literal from (non-empty!) pending list *)
    l \<leftarrow> OBTAIN (\<lambda>l. l\<in>pending S0);
    let S = S0\<lparr>
      pending := pending S0 - {l}
    \<rparr>; 

    (* Get watched set for -l *)
    let wlist = twl2_watchset S l;

    (* Iterate over watched list, and restore invariant *)
    FOREACHci (twl2_prop_loop_invar S\<^sub>b S0 l) wlist (\<lambda>S. \<not>conflict S) (\<lambda>i S. do {
      let A = assignment S;
      let CLdb = clause_db S;

      ASSERT (i\<in>valid_idxs S);
      ASSERT (i<length CLdb);
      let (w1,w2,ls) = CLdb!i;
      ASSERT (w1\<noteq>w2);

      if (sem_lit' w1 A = Some True \<or> sem_lit' w2 A = Some True) then
        RETURN S
      else do {
        (* Swap, to have w2 = -l*)
        let (w1,w2) = (if w1=neg_lit l then (w2,w1) else (w1,w2));

        ASSERT (w2=neg_lit l);
        ASSERT (w1\<noteq>w2);

        (* Try to obtain undecided or true literal *)
        j \<leftarrow> SELECT (\<lambda>j. j<length ls \<and> sem_lit' (ls!j) A \<noteq> Some False
              \<and> ls!j \<noteq> w1 (* TODO/FIXME: Required only if clauses may contain DUPs *)
            );
        case j of
          Some j \<Rightarrow> do {
            (* Found one: This is new watched literal *)
            ASSERT (j<length ls);
            ASSERT (w1 \<in> cl2_watched (CLdb!i));
            ASSERT (ls!j \<noteq> w1);
            ASSERT (ls!j \<noteq> w2);
            let w2 = ls!j; let ls=ls[j:=neg_lit l];
            let CLdb=CLdb[i:=(w1,w2,ls)];
            let S=S\<lparr>clause_db := CLdb\<rparr>;
            RETURN S
          }
        | None \<Rightarrow> do { 
            (* Found none: Propagate unit or mark conflict *)
            if sem_lit' w1 A \<noteq> Some False then
              twl2_assign_aux S w1
            else
              RETURN (S\<lparr> conflict := True \<rparr>)
        }
      }  
    }) S
  }"
    
  lemma CLC_pending_update[simp]: "twl2_prop_loop_invar_defs.CLC I (S\<lparr>pending := P'\<rparr>) = twl2_prop_loop_invar_defs.CLC I S"
    unfolding twl2_prop_loop_invar_defs.CLC_def by auto


  context twl2_invar_aux begin  
    lemma CLC_watchset_init_simp: 
      "twl2_prop_loop_invar_defs.CLC (twl2_watchset S l) S = {C\<in>CL. neg_lit l \<notin> cl2_watched C}"  
      unfolding twl2_prop_loop_invar_defs.CLC_def twl2_watchset_def CL_def
      by auto
      


    lemma init_watchset:
      "\<lbrakk>\<not>CN; l\<in>P\<rbrakk> \<Longrightarrow> twl2_prop_loop_invar S\<^sub>b S l (twl2_watchset S l) (S\<lparr>pending := P - {l}\<rparr>)"
      apply unfold_locales
      apply (simp_all add: CLC_watchset_init_simp pending_set)
      subgoal using two_watched by (auto) []
      subgoal using bt_sub .
      subgoal using bt_abs_CLdb .
      subgoal using bt_watched_repl .
      subgoal using bt_watched_keep .
      subgoal by (auto simp: twl2_watchset_def ) []
      subgoal by (rule prop_unit2_RI(2)) (auto simp add: twl2_\<alpha>_def twl2_defs.F_def)
      subgoal for C using conflict_covered[of C] by auto
      subgoal for C using unit_covered[of C] by auto
      subgoal for w1 w2 ls 
        apply clarsimp
        using watched1[of w1 w2 ls] 
        by (auto simp: cl2_watched_def)
      subgoal for w1 w2 ls 
        apply clarsimp
        using watched2[of w1 w2 ls] 
        by (auto simp: cl2_watched_def)
      done  
  end

  lemma (in twl2_prop_loop_invar) restore_true_watched:
    assumes VI: "i \<in> VIs"
    assumes IMEM: "i \<in> it"
    assumes [simp]: "CLdb ! i = (w1, w2, ls)"
    assumes T: "sem_lit' w1 A = Some True \<or> sem_lit' w2 A = Some True"
    shows "twl2_prop_loop_invar S\<^sub>b S0 l_rem (it - {i}) S"
  proof -
    from T have [simp]: 
      "sem_clause' (cl2_\<alpha> (w1, w2, ls)) A = Some True"
      unfolding cl2_\<alpha>_def 
      by (auto simp: sem_clause'_true_conv)
      
    from T have [simp]: 
      "\<not>is_unit_clause A (cl2_\<alpha> (w1, w2, ls))"
      unfolding cl2_\<alpha>_def 
      by (force simp: sem_clause'_false_conv is_unit_clause_def is_unit_lit_def)


    have [simp]: "twl2_prop_loop_invar_defs.CLC (it - {i}) S = insert (CLdb!i) CLC"  
      using VI IMEM unfolding twl2_prop_loop_invar_defs.CLC_def
      by (auto intro: exI[where x=i])


    show ?thesis  
      apply unfold_locales
      apply clarsimp_all
      subgoal using new_ass_pending by (auto simp: ass_keep)
      using pending_mono apply auto []
      using prop_steps apply assumption
      using conflict_imp apply assumption
      using conflict_covered apply auto []
      using unit_covered apply auto []
      using T watched1 apply (auto dest: watched1) []
      using T watched2 apply (auto dest: watched2) []
      done
  qed    


  lemma (in twl2_prop_loop_invar) ex_undec_watched: 
    assumes CLC: "(w1,w2,ls)\<in>CLC"
    assumes EX_UNDEC: "l\<in>set ls" "sem_lit' l A = None"
    assumes NCOV: "cl2_watched (w1,w2,ls) \<inter> neg_lit`P = {}"
    shows "sem_lit' w1 A = Some False \<longrightarrow> sem_lit' w2 A = Some True" (is ?G1)
      and "sem_lit' w2 A = Some False \<longrightarrow> sem_lit' w1 A = Some True" (is ?G2)
  proof safe
    assume "sem_lit' w1 A = Some False"
    from watched1[OF CLC this] NCOV EX_UNDEC show "sem_lit' w2 A = Some True"
      by (auto simp: cl2_watched_def)
  next  
    assume "sem_lit' w2 A = Some False"
    from watched2[OF CLC _ this] NCOV EX_UNDEC show "sem_lit' w1 A = Some True"
      by (auto simp: cl2_watched_def)
  qed  

  lemma twl2_propagate_step_correct[THEN order_trans, refine_vcg]:
    assumes "twl2_invar_aux S\<^sub>b S0"
    assumes PNE: "pending S0 \<noteq> {}"
    assumes NC[simp]: "\<not>conflict S0"
    shows "twl2_propagate_step S\<^sub>b   S0 \<le> SPEC (\<lambda>S. 
        twl2_invar_aux S\<^sub>b S
      \<and> (S0,S)\<in>prop_unit2_R
      )"
  proof -
    interpret I0: twl2_invar_aux S\<^sub>b S0 by fact

    (* FIXME: Hack, to recover some oddity introduced by vcg or clarsimp? !*)
    (*have SIMP1: "(\<forall>z. m = Some z \<longrightarrow> \<not> z) \<longleftrightarrow> m\<noteq>Some True" for m
      by (cases m) auto*)

    show ?thesis
      unfolding twl2_propagate_step_def Let_def
      apply refine_vcg
      apply (clarsimp_all del:notI)
    proof -
      show "\<exists>l. l \<in> I0.P" using PNE by blast

      fix l
      assume LIP: "l\<in>I0.P"

      show "twl2_prop_loop_invar S\<^sub>b S0 l (twl2_watchset S0 l) (S0\<lparr>pending := I0.P - {l}\<rparr>)"
        by (rule I0.init_watchset[OF NC LIP])

      { -- \<open>Inside for loop\<close>
        fix i it S
        assume I: "i \<in> it" "it \<subseteq> twl2_watchset S0 l" 
        and "twl2_prop_loop_invar S\<^sub>b S0 l it S"
        and [simp]: "\<not>conflict S"

        interpret twl2_prop_loop_invar S\<^sub>b S0 l it S by fact

        show [simp]: "i < length CLdb" using I by (auto simp: twl2_watchset_def)
        show [simp]: "i\<in>VIs" using I by (auto simp: twl2_watchset_def)

        fix w1 w2 ls
        assume CLI: "CLdb!i = (w1,w2,ls)"

        from clauses_unproc_eq I have "I0.CLdb!i = CLdb!i" by auto
        hence ORIG_CL: "(w1,w2,ls) \<in> I0.CL" 
          using CLI unfolding I0.CL_def by (auto dest: sym)

        show WNE: "w1\<noteq>w2" using I0.watchedE[OF ORIG_CL] 
          unfolding cl2_watched_def by force


        from CLI I have NL_IS_W: "w1=neg_lit l \<or> w2=neg_lit l"
          unfolding twl2_watchset_def 
          by (auto simp: cl2_watched_def)

        { -- \<open>Restore if a watched literal is true\<close>
          assume "sem_lit' w1 A = Some True \<or> sem_lit' w2 A = Some True"
          show "twl2_prop_loop_invar S\<^sub>b S0 l (it - {i}) S"
            by (rule restore_true_watched) fact+

        }

        assume WNT: "sem_lit' w1 A \<noteq> Some True" "sem_lit' w2 A \<noteq> Some True"

        fix w1' w2'
        assume SWAP_ASS: "(if w1 = neg_lit l then (w2, w1) else (w1, w2)) = (w1', w2')"

        show [simp]: "w2'=neg_lit l" using NL_IS_W SWAP_ASS by (auto split: split_if_asm)

        have WNE': "w1' \<noteq> neg_lit l" using SWAP_ASS WNE by (auto split: split_if_asm)
        thus "w1'\<noteq>w2'" by simp


        from WNT have WNT0: "sem_lit' w1 I0.A \<noteq> Some True" "sem_lit' w2 I0.A \<noteq> Some True"
          by (auto simp: ass_lit_keep_decided)

        have SLw2': "sem_lit' (neg_lit l) A = Some False"  
          by (auto simp add: I0.pending_set \<open>l \<in> I0.P\<close> ass_lit_keep_decided)

        show "w1'\<in>cl2_watched (w1,w2,ls)" using SWAP_ASS by (auto simp: cl2_watched_def split: split_if_asm) 

        { -- \<open>Found unwatched non-false literal\<close>
          fix j
          assume [simp]: "j<length ls"
          assume SLJ: "sem_lit' (ls!j) A \<noteq> Some False"
          assume DIST: "ls!j \<noteq> w1'"


          show "ls!j \<noteq> neg_lit l"
            using SLJ SLw2' by auto

          let ?C' = "(w1', ls ! j, ls[j := neg_lit l])"
          let ?S' = "S\<lparr>clause_db := CLdb[i := ?C']\<rparr>"

          have 1: "cl2_\<alpha> ?C' = cl2_\<alpha> (CLdb ! i)"
            apply (simp add: CLI)
            using SWAP_ASS apply simp
            apply (simp add: cl2_\<alpha>_def insert_swap_set_eq)
            apply (auto split: split_if_asm)
            done

          have [simp]: "twl2_defs.F ?S' = F"  
            by (rule F_update_eq) (auto simp: 1)

          have [simp]: "twl2_\<alpha> ?S' = twl2_\<alpha> S"
            by (simp add: twl2_\<alpha>_def)

          have CLC': "twl2_prop_loop_invar_defs.CLC (it - {i}) ?S' 
            = insert ?C' CLC"
            using I(1) 
            apply (auto simp: twl2_prop_loop_invar_defs.CLC_def nth_list_update)
            using \<open>i \<in>VIs\<close> by blast

          have [simp]: "sem_clause' (cl2_\<alpha> ?C') A \<noteq> Some False"
            using SLJ by (auto simp: cl2_\<alpha>_def)

          have W1'_ORIG_WATCHED: "w1' \<in> cl2_watched (CLdb!i)"  
            using SWAP_ASS CLI
            by (auto simp: cl2_watched_def split: split_if_asm)

          have [simp]: "\<not>is_unit_clause A (cl2_\<alpha> ?C')" if "cl2_watched ?C' \<inter> neg_lit ` P = {}" 
          proof (simp add: 1, rule notI)
            have 2: "ls ! j \<in> cl2_\<alpha> (CLdb ! i)" and 3: "w1' \<in> cl2_\<alpha> (CLdb ! i)"
              unfolding 1[symmetric] by (auto simp: cl2_\<alpha>_def)

            assume "is_unit_clause A (cl2_\<alpha> (CLdb ! i))"
            hence UNIT: "is_unit_lit A (cl2_\<alpha> (CLdb ! i)) (ls!j)"
              using sem_not_false_the_unit_lit[OF _ 2 SLJ]
              by (auto simp: is_unit_clause_def)
            hence 4: "sem_lit' w1' A = Some False"
              apply (rule unit_other_false)
              using DIST 3
              by auto

            from UNIT have LSJ_UNDEC: "sem_lit' (ls!j) A = None" by (auto simp: is_unit_lit_def)
            from LSJ_UNDEC have LSJ_UNDEC0: "sem_lit' (ls!j) I0.A = None" by (auto simp: ass_keep)

            from W1'_ORIG_WATCHED that have 6: "w1' \<notin> neg_lit ` P"
              by (auto simp: cl2_watched_def)

            show False proof (cases "sem_lit' w1' I0.A")
              case false
              have "neg_lit w1' \<notin> I0.P"
                apply (rule notI)
                using WNE' pending_mono 6 by force
              with I0.watched1[OF NC ORIG_CL] I0.watched2[OF NC ORIG_CL] LSJ_UNDEC0 WNT0 false  
              have "\<forall>l\<in>set ls. sem_lit' l I0.A = Some False"
                using SWAP_ASS by (auto split: split_if_asm)
              hence "sem_lit' (ls!j) I0.A = Some False" by auto
              hence "sem_lit' (ls!j) A = Some False" by (auto simp: ass_lit_keep_decided)
              with SLJ show False ..
            next
              case undec
              with 4 false_ass_pending[of w1'] have "neg_lit w1' \<in> P" by auto
              with 6 show False by force
            next  
              case true hence "sem_lit' w1' A = Some True" by (auto simp: ass_lit_keep_decided)
              with 4 show False by simp
            qed  
          qed  
      

          show "twl2_prop_loop_invar S\<^sub>b S0 l (it - {i}) ?S'"
            apply unfold_locales
            apply (clarsimp_all simp: CLC' pending_set)
            subgoal using two_watched DIST by (fastforce dest: CL_update_approx simp: cl2_watched_def)
            subgoal using bt_sub .
            subgoal using bt_abs_CLdb by (auto simp: nth_list_update 1)
            subgoal for ii w
              using bt_watched_repl
            proof (clarsimp simp: nth_list_update split: split_if_asm dest!: sym[of i ii])
              assume NW: "w \<notin> cl2_watched (I0.IBT.CLdb ! i)" 
              assume SLw: "sem_lit' w A\<^sub>b = Some False"
              assume W: "w \<in> cl2_watched (w1', ls ! j, ls[j := neg_lit l])"
              show False proof (cases "w=ls!j")
                case False hence "w\<in>cl2_watched (CLdb!i)"
                  using W SWAP_ASS
                  by (auto simp: CLI cl2_watched_def split: split_if_asm)
                with bt_watched_repl[OF _ this NW] SLw show False by auto
              next  
                case True hence "sem_lit' w A \<noteq> Some False"
                  using SLJ by auto
                from bt_sem_nd_keep[OF this] SLw show False by simp
              qed
            qed  
            subgoal for ii w
              using bt_watched_keep
              apply (clarsimp simp: nth_list_update split: split_if_asm dest!: sym[of i ii])
              by (metis (no_types, lifting) CLI WNT(1) WNT(2) \<open>i \<in> VIs\<close> bt_sem_nd_keep cl2_watched_def insert_iff old.prod.case)
            subgoal using new_ass_pending by (auto simp: ass_keep_decided) 
            subgoal using pending_mono by auto
            subgoal using prop_steps by (auto simp: prop_unit2_R_def)
            subgoal using conflict_covered by auto
            subgoal using unit_covered by auto
            subgoal for w1x w2x lsax lax
            proof - (* TODO/FIXME: Sledgehammer did a good job here, but the proof is unreadable *)
              assume a1: "w1x = w1' \<and> w2x = ls ! j \<and> lsax = ls[j := neg_lit l] \<or> (w1x, w2x, lsax) \<in> CLC"
              assume a2: "sem_lit' w1x A = Some False"
              assume a3: "sem_lit' w2x A \<noteq> Some True"
              assume a4: "w1x \<notin> neg_lit ` P"
              assume a5: "lax \<in> set lsax"
              have f6: "ls ! j \<in> set ls"
                by (metis (no_types) \<open>j < length ls\<close> nth_mem)
              have f7: "sem_lit' (ls ! j) I0.A \<noteq> Some False"
                using SLJ twl2_prop_loop_invar.ass_lit_keep_decided twl2_prop_loop_invar_axioms by blast
              then have f8: "\<exists>l. l \<in> set ls \<and> sem_lit' l I0.A \<noteq> Some False"
                using f6 by blast
              have f9: "sem_lit' w1x I0.A = Some False \<or> neg_lit w1x \<in> P"
                using a2 false_ass_pending by blast
              obtain ll :: "'a literal set \<Rightarrow> ('a literal \<Rightarrow> 'a literal) \<Rightarrow> 'a literal \<Rightarrow> 'a literal" where
                "\<forall>x0 x1 x2. (\<exists>v3. v3 \<in> x0 \<and> x2 = x1 v3) = (ll x0 x1 x2 \<in> x0 \<and> x2 = x1 (ll x0 x1 x2))"
                by moura
              then have f10: "\<forall>l f L. (l \<notin> f ` L \<or> ll L f l \<in> L \<and> l = f (ll L f l)) \<and> (l \<in> f ` L \<or> (\<forall>la. la \<notin> L \<or> l \<noteq> f la))"
                by (meson image_iff)
              have f11: "\<forall>l. l \<notin> P \<or> w1x \<noteq> neg_lit l"
                using a4 by blast
              have "sem_lit' w2 I0.A = Some False \<longrightarrow> w2 \<in> neg_lit ` I0.P"
                using f8 by (meson I0.watched2 NC ORIG_CL WNT0(1))
              then have "(w1x, w2x, lsax) \<in> CLC"
                using f11 f10 f9 f7 f6 a1 by (metis (no_types) I0.watched1 NC ORIG_CL SWAP_ASS WNE' WNT0(2) \<open>\<And>x. \<lbrakk>x \<in> I0.P; x \<notin> P\<rbrakk> \<Longrightarrow> x = l\<close> neg_neg_lit prod.inject)
              then show ?thesis
                using a5 a4 a3 a2 by (metis (no_types) twl2_prop_loop_invar.watched1 twl2_prop_loop_invar_axioms)
            qed  
            subgoal using SLJ watched2 by blast 
            done
        }

        { -- \<open>All other literals are false. Note: We may have ignored duplicates of \<open>w1'\<close>\<close>
          assume OTHERS_FALSE: "\<forall>j<length ls. sem_lit' (ls ! j) A = Some False \<or> ls ! j = w1'"
          
          hence L_FALSE: "\<lbrakk>ll\<in>set ls; ll\<noteq>w1'\<rbrakk> \<Longrightarrow> sem_lit' ll A = Some False" for ll
            by (auto simp: in_set_conv_nth)

          { -- \<open>\<open>w1'\<close> is undecided: Propagate unit\<close>
            assume "sem_lit' w1' A \<noteq> Some False"
            hence SLw1': "sem_lit' w1' A = None"
              using WNT SWAP_ASS by (cases "sem_lit' w1' A") (auto split: split_if_asm)
              
            hence UNIT: "is_unit_lit A (cl2_\<alpha> (w1,w2,ls)) w1'"
              using SLw2' SWAP_ASS L_FALSE
              unfolding is_unit_lit_def cl2_\<alpha>_def
              by (auto simp: sem_clause'_false_conv split: split_if_asm)

            from SLw1' pending_set[of w1'] pending_set[of "neg_lit w1'"] have 
              [simp]: "w1'\<notin>P" "neg_lit w1' \<notin> P"
              by auto
              
            let ?S' = "S\<lparr>twl2.assignment := assign_lit A w1', pending := insert w1' P\<rparr>"  
            have CLC': "twl2_prop_loop_invar_defs.CLC (it - {i}) ?S' 
              = insert (w1,w2,ls) CLC"
              using I(1) CLI
              by (auto simp: twl2_prop_loop_invar_defs.CLC_def nth_list_update dest: sym)
  
            have SEM_C': "sem_clause' (cl2_\<alpha> (w1, w2, ls)) (assign_lit A w1') = Some True"  
              using SWAP_ASS SLw1'
              by (auto simp: sem_clause'_true_conv cl2_\<alpha>_def split: split_if_asm)

            have [simp]: "finite (vars_of_cnf (cl2_\<alpha> ` CL))" 
              unfolding vars_of_cnf_def by (auto simp: cl2_\<alpha>_def)

            have PU: "(twl2_\<alpha> S,twl2_\<alpha> ?S')\<in> prop_unit1_R" 
            proof -
              have "cl2_\<alpha> (w1, w2, ls) \<in> cl2_\<alpha>`CL"  
                apply (clarsimp simp: CL_def)
                by (smt CLI \<open>i \<in> VIs\<close> image_iff mem_Collect_eq)
              moreover have "the_unit_lit A (cl2_\<alpha> (w1,w2,ls)) = w1'"  
                using UNIT by simp
              ultimately show ?thesis  
                using UNIT
                by (auto simp: prop_unit1_R_def twl2_\<alpha>_def twl2_defs.F_def is_unit_clause_def
                  intro: exI[of _ "cl2_\<alpha> (w1,w2,ls)"])
            qed

            show "twl2_assign_aux S w1' \<le> SPEC (twl2_prop_loop_invar S\<^sub>b S0 l (it - {i}))"
              unfolding twl2_assign_aux_def 
              apply refine_vcg
              apply unfold_locales
              unfolding CLC'
              apply (clarsimp_all simp: SEM_C')
              subgoal by (simp add: SLw1')
              subgoal by (auto simp: sem_lit'_assign_conv pending_set)
              subgoal using two_watched by auto
              subgoal using bt_sub_assign_undec[OF SLw1'] .
              subgoal using bt_abs_CLdb .
              subgoal using bt_watched_repl by auto
              subgoal using bt_watched_keep by auto
              subgoal for x using new_ass_pending[of x]  using SLw1'
                by (cases w1') auto
              subgoal using pending_mono by auto
              subgoal using prop_steps PU by (rule prop_unit2_R_append_unit)
              subgoal for w1x w2x lsx
              proof (erule disjE)
                assume F: "sem_clause' (cl2_\<alpha> (w1x, w2x, lsx)) (assign_lit A w1') = Some False" 
                  and NWATCHED: "neg_lit w1' \<notin> cl2_watched (w1x, w2x, lsx)"
                  and NCOV: "cl2_watched (w1x, w2x, lsx) \<inter> neg_lit ` P = {}" 
                  and CLC: "(w1x, w2x, lsx) \<in> CLC"
                
                from F show False 
                proof (cases rule: clause_assign_false_cases)  
                  case no_lit with conflict_covered CLC NCOV show False
                    by auto
                next
                  case lit
                  from lit(1) NWATCHED have NW': "neg_lit w1'\<noteq>w1x" "neg_lit w1'\<noteq>w2x" 
                    and IN_LSX: "neg_lit w1'\<in>set lsx"
                    by (auto simp: cl2_watched_def cl2_\<alpha>_def)

                  from ex_undec_watched[OF CLC IN_LSX _ NCOV] SLw1' NW' lit(2)
                  show False by (auto simp: sem_clause'_false_conv cl2_\<alpha>_def)
                qed  
              qed (simp add: SEM_C')
              subgoal for w1x w2x lsx
              proof (erule disjE)
                assume U: "is_unit_clause (assign_lit A w1') (cl2_\<alpha> (w1x, w2x, lsx))" 
                  and NWATCHED: "neg_lit w1' \<notin> cl2_watched (w1x, w2x, lsx)"
                  and NCOV: "cl2_watched (w1x, w2x, lsx) \<inter> neg_lit ` P = {}" 
                  
                {
                  assume CLC: "(w1x, w2x, lsx) \<in> CLC"
                
                  from U show False 
                  proof (cases "neg_lit w1' \<in> set lsx")
                    case False
                    with NWATCHED have "neg_lit w1' \<notin> cl2_\<alpha> (w1x, w2x, lsx)"
                      by (auto simp: cl2_\<alpha>_def cl2_watched_def)
                    from unit_clause_assign_indep[OF U] this have "is_unit_clause A (cl2_\<alpha> (w1x, w2x, lsx))" .
                    with unit_covered[OF CLC] NCOV show False by simp
                  next  
                    case True
                    with NWATCHED have NW': "neg_lit w1'\<noteq>w1x" "neg_lit w1'\<noteq>w2x" 
                      and IN_LSX: "neg_lit w1'\<in>set lsx"
                      by (auto simp: cl2_watched_def cl2_\<alpha>_def)
                    
                    from CLC have IN_CL: "(w1x, w2x, lsx) \<in> CL"  
                      unfolding CLC_def CL_def by auto
  
                    have 1: "sem_lit' w1x (assign_lit A w1') \<noteq> Some True" 
                         "sem_lit' w2x (assign_lit A w1') \<noteq> Some True"
                      using U 
                      apply -
                      by (force simp: is_unit_clause_def is_unit_lit_def cl2_\<alpha>_def sem_clause'_false_conv)+
                    hence "sem_lit' w1x A \<noteq> Some True" "sem_lit' w2x A \<noteq> Some True" using NW'
                      by (auto simp: sem_lit'_assign_conv split: split_if_asm)
  
                    with ex_undec_watched[OF CLC True _ NCOV] SLw1' have 
                      "sem_lit' w1x A = None" "sem_lit' w2x A = None"
                      apply clarsimp_all
                      using boolopt_cases_aux.cases by blast+
                    moreover from 1 have "w1x\<noteq>w1'" "w2x\<noteq>w1'" 
                      by - (rule notI; simp)+
                    ultimately have 
                      "sem_lit' w1x (assign_lit A w1') = None" 
                      "sem_lit' w2x (assign_lit A w1') = None"  
                      using NW'
                      by (auto simp: sem_lit'_assign_conv split: split_if_asm)
                    moreover have "w1x\<noteq>w2x" 
                      apply (rule watchedE[OF IN_CL]) 
                      by (auto simp: cl2_watched_def)
                    ultimately have "\<not>is_unit_clause (assign_lit A w1') (cl2_\<alpha> (w1x, w2x, lsx))"  
                      apply (auto simp: cl2_\<alpha>_def)
                      by (metis (full_types) insertI1 insert_commute is_unit_clause_def sem_none_the_unit_lit)
                    with U show False by simp
                  qed  
              next
                }
                {
                  assume [simp]: "w1x = w1 \<and> w2x = w2 \<and> lsx = ls"
                  with unit_clause_sem[OF U] SEM_C' show False by auto
                }
              qed  
              subgoal for w1x w2x lsx ll 
              proof (erule disjE; clarsimp?) 
                assume 
                  "sem_lit' w1 (assign_lit A w1') = Some False" 
                  "sem_lit' w2 (assign_lit A w1') \<noteq> Some True"
                with SWAP_ASS SLw1' have False
                  by (auto split: split_if_asm)
                thus "sem_lit' ll (assign_lit A w1') = Some False" ..
              next    
                assume "sem_lit' w2x (assign_lit A w1') \<noteq> Some True"
                hence "w2x \<noteq> w1'" and SLw2x: "sem_lit' w2x A \<noteq> Some True" using SLw1'
                  by (auto simp: sem_lit'_assign_conv split: split_if_asm)
                assume "sem_lit' w1x (assign_lit A w1') = Some False" "w1x \<noteq> neg_lit w1'"  
                hence SLw1x: "sem_lit' w1x A = Some False"
                  by (auto simp: sem_lit'_assign_conv split: split_if_asm)

                assume CLC: "(w1x, w2x, lsx) \<in> CLC" and NCOV: "w1x \<notin> neg_lit ` P"  
                assume IN_LSX: "ll \<in> set lsx"
                from watched1[OF CLC SLw1x SLw2x] NCOV IN_LSX 
                have "sem_lit' ll A = Some False" by auto
                thus "sem_lit' ll (assign_lit A w1') = Some False" 
                  using assign_undec_pres_dec_lit[OF SLw1'] by auto
              qed    
              subgoal for w1x w2x lsx ll (* TODO: The above, more explicit proof may be more stable than this sledgehammer one *)
              proof -
                assume a1: "sem_lit' w1x (assign_lit A w1') \<noteq> Some True"
                assume a2: "w1x = w1 \<and> w2x = w2 \<and> lsx = ls \<or> (w1x, w2x, lsx) \<in> CLC"
                assume a3: "w2x \<notin> neg_lit ` P"
                assume a4: "ll \<in> set lsx"
                assume a5: "w2x \<noteq> neg_lit w1'"
                assume a6: "sem_lit' w2x (assign_lit A w1') = Some False"
                then have "w2x \<noteq> w1'"
                  by force
                then show ?thesis
                  using a6 a5 a4 a3 a2 a1 by (metis (no_types) Pair_inject SLw1' SWAP_ASS assign_undec_pres_dec_lit sem_lit'_assign_conv twl2_prop_loop_invar.watched2 twl2_prop_loop_invar_axioms)
              qed
              done  

          }

          { -- \<open>\<open>w1'\<close> is decided: Conflict\<close>
            fix v
            assume "sem_lit' w1' A = Some v"
            with WNT SWAP_ASS have SLw1': "sem_lit' w1' A = Some False"
              by (auto split: split_if_asm)

              
            with L_FALSE SLw2' SWAP_ASS have CONF: "is_conflict_clause A (cl2_\<alpha> (w1,w2,ls))"  
              by (auto simp: cl2_\<alpha>_def sem_clause'_false_conv split: split_if_asm)

            let ?S'="S\<lparr>conflict := True\<rparr>"

            have CLC': "twl2_prop_loop_invar_defs.CLC (it - {i}) ?S' 
              = insert (w1,w2,ls) CLC"
              using I(1) CLI
              apply (auto simp: twl2_prop_loop_invar_defs.CLC_def nth_list_update)
              using \<open>i \<in> VIs\<close> by metis

            have CLF: "cl2_\<alpha> (w1,w2,ls) \<in> F"
              unfolding F_def CL_def 
              using \<open>i\<in>VIs\<close> CLI 
              by (auto dest: sym intro!: imageI)
              

            show "twl2_prop_loop_invar S\<^sub>b S0 l (it - {i}) ?S'"
              apply unfold_locales
              unfolding CLC'
              apply (clarsimp_all simp: pending_set)
              subgoal using two_watched by auto
              subgoal by (rule bt_sub) 
              subgoal by (rule bt_abs_CLdb)
              subgoal using bt_watched_repl by auto
              subgoal using bt_watched_keep by auto
              subgoal for x using new_ass_pending[of x] by auto 
              subgoal using pending_mono by auto
              subgoal using prop_steps by (auto simp: twl2_\<alpha>_def twl2_defs.F_def prop_unit2_R_def)
              subgoal using CONF CLF by (auto simp: twl2_defs.F_def)
              subgoal using watched1 CONF 
                by (fastforce simp: cl2_\<alpha>_def sem_clause'_false_conv)
              subgoal using watched2 CONF 
                by (fastforce simp: cl2_\<alpha>_def sem_clause'_false_conv)
              done  
          }
        }
      }  

      { -- \<open>Normal termination of for loop\<close>
        fix S
        assume "twl2_prop_loop_invar S\<^sub>b S0 l {} S" "\<not> conflict S"

        interpret twl2_prop_loop_invar S\<^sub>b S0 l "{}" S by fact

        show "twl2_invar_aux S\<^sub>b S"
          by (simp add: empty_imp_invar)

        show "(S0, S) \<in> prop_unit2_R" using prop_steps .
      }

      { -- \<open>Abrupt termination of for loop\<close>
        fix it S
        assume "twl2_prop_loop_invar S\<^sub>b S0 l it S" and [simp]: "conflict S"

        interpret twl2_prop_loop_invar S\<^sub>b S0 l it S by fact

        show "twl2_invar_aux S\<^sub>b S"
          apply unfold_locales
          apply clarsimp_all
          using conflict_imp apply auto []
          done

        show "(S0, S) \<in> prop_unit2_R"
          using prop_steps .
      }
      
    qed
  qed

  definition "twl2_propagate S\<^sub>b   S \<equiv> do {
    WHILET (\<lambda>S. pending S \<noteq> {} \<and> \<not>conflict S) (twl2_propagate_step S\<^sub>b) S
  }"

  lemma twl2_propagate_correct_aux: "twl2_invar_aux S\<^sub>b S \<Longrightarrow> twl2_propagate S\<^sub>b   S 
    \<le> SPEC (\<lambda>S'. (S,S')\<in>prop_unit2_R\<^sup>* \<and> twl2_invar_aux S\<^sub>b S' \<and> (conflict S' \<or> pending S'={}))"
    unfolding twl2_propagate_def
    apply (refine_vcg WHILET_rule[where 
        I="\<lambda>S'. (S,S')\<in>prop_unit2_R\<^sup>* \<and> twl2_invar_aux S\<^sub>b S'"
        and R="prop_unit2_R\<inverse>"
      ])
    by (auto simp: rtrancl_into_rtrancl)


  lemma prop_unit1_from_prop_unit2:
    assumes "(S, S1) \<in> prop_unit2_R\<^sup>*"
    shows "(twl2_\<alpha> S, twl2_\<alpha> S1) \<in> prop_unit1_R\<^sup>*"
    using assms
  proof (induction)
    case base thus ?case by auto
  next  
    case (step S' S'')
    note step.IH
    also from step.hyps(2) have "twl2_\<alpha> S'' = twl2_\<alpha> S' \<or> (twl2_\<alpha> S', twl2_\<alpha> S'')\<in>prop_unit1_R\<^sup>+"
      unfolding prop_unit2_R_def
      by (auto simp: twl2_\<alpha>_def)
    hence "(twl2_\<alpha> S', twl2_\<alpha> S'')\<in>prop_unit1_R\<^sup>*" by auto
    finally show ?case .
  qed  
      
  
  lemma no_pending_imp_conflict_or_pu_nf:
    assumes "twl2_invar_aux S\<^sub>b S"
    assumes "pending S = {}"
    assumes NOC: "\<forall>C\<in>twl1.clauses (twl2_\<alpha> S). \<not>is_conflict_clause (twl2.assignment S) C"
    shows "twl2_\<alpha> S \<in> NF prop_unit1_R"
  proof (rule NF_I; safe)
    interpret twl2_invar_aux S\<^sub>b S by fact

    from NOC have [simp]: "\<not>CN"
      using conflict_imp by (auto simp: twl2_\<alpha>_def)

    fix S'
    assume "(twl2_\<alpha> S, S') \<in> prop_unit1_R"
    then obtain C where "C\<in>F" and U: "is_unit_clause A C"
      by (auto simp: prop_unit1_R_def twl2_\<alpha>_def)
    then obtain Ci where CL: "Ci\<in>CL" and [simp]: "C=cl2_\<alpha> Ci" unfolding F_def by auto

    hence "cl2_watched Ci \<inter> neg_lit ` P \<noteq> {}"  
      using unit_covered[OF CL] U by auto
    hence "C\<inter>neg_lit`P \<noteq> {}" by (auto simp: cl2_watched_def cl2_\<alpha>_def) 
    with \<open>P={}\<close> show False by blast
  qed  
      
  lemma twl2_propagate_refine: "(twl2_propagate S\<^sub>b,twl1_prop_unit) \<in> twl2_rel_aux S\<^sub>b \<rightarrow> \<langle>twl2_bt_rel S\<^sub>b\<rangle>nres_rel"
    apply (intro fun_relI nres_relI)
    unfolding twl1_prop_unit_def twl2_bt_rel_def twl2_rel_aux_def br_def
    apply (refine_vcg twl2_propagate_correct_aux[THEN order_trans] SPEC_refine)
    apply (clarsimp_all)
    apply (intro conjI)
  proof -  
    fix S S' :: "'a twl2"
    assume "twl2_invar_aux S\<^sub>b S"
    assume PU: "(S, S') \<in> prop_unit2_R\<^sup>*" 
    assume INV': "twl2_invar_aux S\<^sub>b S'" 
    assume COP: "conflict S' \<or> pending S' = {}"

    interpret twl2_invar_aux S\<^sub>b S' by fact

    from COP show "twl2_bt_invar S\<^sub>b S'" by unfold_locales auto

    from prop_unit1_from_prop_unit2[OF PU] show "(twl2_\<alpha> S, twl2_\<alpha> S') \<in> prop_unit1_R\<^sup>*" .

    from COP no_pending_imp_conflict_or_pu_nf[OF INV'] show 
      "twl2_\<alpha> S' \<in> NF prop_unit1_R \<or>
        (\<exists>C\<in>twl1.clauses (twl2_\<alpha> S'). sem_clause' C (twl1.assignment (twl2_\<alpha> S')) = Some False)"
      using conflict_imp
      by (auto simp: twl2_\<alpha>_def)
  qed    
  lemmas twl2_propagate_refine_rl = twl2_propagate_refine[THEN fun_relD, THEN nres_relD]  


  definition "twl2_assign S\<^sub>b   S l \<equiv> do {
    S \<leftarrow> twl2_assign_aux S l;
    twl2_propagate S\<^sub>b   S
  }"

  lemma twl2_assign_aux_refine: "(twl2_assign_aux, twl1_assign_aux) \<in> twl2_rel_aux S\<^sub>b \<rightarrow> Id \<rightarrow> \<langle>twl2_rel_aux S\<^sub>b\<rangle>nres_rel"
    apply (intro fun_relI nres_relI)
    unfolding twl2_assign_aux_def twl1_assign_aux_def Let_def
    apply refine_vcg
    unfolding twl2_bt_rel_def twl2_rel_aux_def br_def
    apply (clarsimp_all simp: twl2_\<alpha>_def twl2_defs.F_def del: notI)
  proof -  
    fix S :: "'a twl2"
    assume "twl2_invar_aux S\<^sub>b S"
    then interpret twl2_invar_aux S\<^sub>b S .

    fix l
    assume UNDEC: "sem_lit' l A = None"
    from UNDEC have UNDEC': "sem_lit' (neg_lit l) A = None" by simp
    from UNDEC' have [simp]: "neg_lit l \<notin> P" using pending_set by fastforce
    from UNDEC show "l \<notin> P" using pending_set by fastforce

    show "twl2_invar_aux S\<^sub>b (S\<lparr> assignment := assign_lit A l, pending := insert l P \<rparr>)"
      apply unfold_locales
      apply clarsimp_all
      subgoal for l' by (auto simp: sem_lit'_assign_conv pending_set)
      subgoal using two_watched by auto
      subgoal using bt_sub_assign_undec[OF UNDEC] .
      subgoal by (rule bt_abs_CLdb)
      subgoal using bt_watched_repl by auto
      subgoal using bt_watched_keep by auto
      subgoal using conflict_imp 
        by (force simp: twl2_defs.F_def assign_undec_pres_dec_clause[OF UNDEC])
      subgoal for w1 w2 ls  
        apply (erule clause_assign_false_cases)
          subgoal using conflict_covered[of "(w1,w2,ls)"] by simp
          subgoal
            apply (frule (1) is_unit_litI[OF _ _ UNDEC', THEN is_unit_clauseI])
            using unit_covered[of "(w1,w2,ls)"]
            by simp
        done    
      subgoal for w1 w2 ls    
      proof -
        let ?A' = "assign_lit A l"
        assume CL: "(w1, w2, ls) \<in> CL" 
          and U: "is_unit_clause ?A' (cl2_\<alpha> (w1, w2, ls))"
          and NCOV: "cl2_watched (w1, w2, ls) \<inter> neg_lit ` P = {}" 
          and [simp]: "\<not> CN"
          
        from CL have WNE: "w1\<noteq>w2" by (rule watched_ne)

        show "neg_lit l \<in> cl2_watched (w1, w2, ls)"
          apply (rule ccontr)
          using U
        proof (cases rule: clause_assign_unit_cases)  
          case no_lit 
          with unit_covered[OF CL] NCOV show False by auto
        next  
          case lit
          assume "neg_lit l \<notin> cl2_watched (w1, w2, ls)"
          with lit have "neg_lit l \<in> set ls" and LNW: "neg_lit l\<noteq>w1" "neg_lit l\<noteq>w2"
            by (auto simp: cl2_\<alpha>_def cl2_watched_def)
          with UNDEC have OTHERS_NOT_FALSE: "\<not>(\<forall>l\<in>set ls. sem_lit' l A = Some False)" by fastforce
          from OTHERS_NOT_FALSE watched1[OF _ CL] NCOV have 
            "sem_lit' w1 A \<noteq> Some False \<or> sem_lit' w2 A = Some True"
            by (auto simp: cl2_watched_def)
          moreover from OTHERS_NOT_FALSE watched2[OF _ CL] NCOV have 
            "sem_lit' w2 A \<noteq> Some False \<or> sem_lit' w1 A = Some True"
            by (auto simp: cl2_watched_def)
          moreover from unit_contains_no_true[OF U] have 
            "sem_lit' w1 ?A' \<noteq> Some True"  
            "sem_lit' w2 ?A' \<noteq> Some True"  
            by (auto simp: cl2_\<alpha>_def)
          with UNDEC LNW have 
            "sem_lit' w1 A \<noteq> Some True" "sem_lit' w2 A \<noteq> Some True"  
            and WNL: "w1\<noteq>l" "w2\<noteq>l"
            by (auto simp: sem_lit'_assign_conv split: split_if_asm)
          ultimately have "sem_lit' w1 A = None " "sem_lit' w2 A = None" 
            apply -
            apply (cases "sem_lit' w1 A"; simp)
            apply (cases "sem_lit' w2 A"; simp)
            done
          with LNW WNL have "sem_lit' w1 ?A' = None " "sem_lit' w2 ?A' = None"  
            by (auto simp: sem_lit'_assign_conv)
          hence "\<not>is_unit_clause ?A' (cl2_\<alpha> (w1, w2, ls))"  
            apply (rule_tac two_nfalse_not_unit[of w1 _ w2, OF _ _ WNE])
            by (auto simp: cl2_\<alpha>_def)
          with U show False by simp
        qed
      qed
      subgoal
        using watched1 UNDEC
        by (fastforce simp: sem_lit'_assign_conv split: split_if_asm) 
      subgoal
        using watched2 UNDEC
        by (fastforce simp: sem_lit'_assign_conv split: split_if_asm) 
      done
  qed
    
  lemmas twl2_assign_aux_refine_rl' = twl2_assign_aux_refine[THEN fun_relD, THEN fun_relD, THEN nres_relD]  
    

  lemma twl2_assign_refine: "(twl2_assign S\<^sub>b, twl1_assign) \<in> twl2_bt_rel S\<^sub>b \<rightarrow> Id \<rightarrow> \<langle>twl2_bt_rel S\<^sub>b\<rangle>nres_rel"
    apply (intro fun_relI nres_relI)
    unfolding twl2_assign_def twl1_assign_def
    apply (refine_vcg twl2_assign_aux_refine_rl' twl2_propagate_refine_rl)
    using twl2_bt_rel_ss by auto

  lemmas twl2_assign_refine_rl'[refine] = twl2_assign_refine[THEN fun_relD, THEN fun_relD, THEN nres_relD]  
    
  definition "twl2_has_conflict S \<equiv> conflict S"

  lemma twl2_has_conflict_refine: "(twl2_has_conflict, twl1_has_conflict) \<in> twl2_rel \<rightarrow> bool_rel"
    apply (intro fun_relI)
    unfolding twl2_rel_def br_def
    apply clarsimp
  proof -
    fix S :: "'a twl2"  
    assume "twl2_invar  S"
    then interpret twl2_invar S .
    show "twl2_has_conflict S = twl1_has_conflict (twl2_\<alpha> S)"
      unfolding twl2_has_conflict_def twl1_has_conflict_def conflict_iff_cn
      by (auto simp: twl2_\<alpha>_def)
  qed    

  lemmas twl2_has_conflict_refine_rl = twl2_has_conflict_refine[THEN fun_relD]
  lemmas twl2_has_conflict_refine_rl_bt = twl2_has_conflict_refine_rl[OF set_mp[OF twl2_rel_ss]]

  lemma twl2_has_conflict_simp[simp]: "twl2_invar S \<Longrightarrow> twl1_has_conflict (twl2_\<alpha> S) = conflict S"
    using twl2_has_conflict_refine_rl[of S "twl2_\<alpha> S"]
    by (auto simp: twl2_has_conflict_def twl2_rel_def br_def)
    
  lemma twl2_has_conflict_simp_bt[simp]: "twl2_bt_invar S\<^sub>b S \<Longrightarrow> twl1_has_conflict (twl2_\<alpha> S) = conflict S"
    using twl2_has_conflict_refine_rl_bt[of S "twl2_\<alpha> S"]
    by (auto simp: twl2_has_conflict_def twl2_bt_rel_def br_def)


  definition "twl2_prepare_rup S L \<equiv> do {
    FOREACH L (\<lambda>l S. twl2_assign_aux S (neg_lit l)) S
  }"

  lemma twl2_prepare_rup_refine_aux:
    assumes "(S,S1)\<in>twl2_rel_aux S\<^sub>b"  
    shows "twl2_prepare_rup S L \<le>\<Down>(twl2_rel_aux S\<^sub>b) (twl1_prepare_rup S1 L)"
  proof -
    have "twl2_prepare_rup S L \<le>\<Down>(twl2_rel_aux S\<^sub>b) (twl1_prepare_rup_impl S1 L)"
      unfolding twl2_prepare_rup_def twl1_prepare_rup_impl_def
      apply (refine_rcg inj_on_id twl2_assign_aux_refine_rl')
      using assms by auto
    also note twl1_prepare_rup_impl_correct
    finally show ?thesis .
  qed  
  
  lemma twl2_prepare_rup_refine[refine]:
    assumes "(S,S1)\<in>twl2_rel"  
    assumes "\<not>conflict S"
    shows "twl2_prepare_rup S L \<le>\<Down>(twl2_rel_aux S) (twl1_prepare_rup S1 L)"
    by (meson assms contra_subsetD twl2_bt_rel_ss twl2_prepare_rup_refine_aux twl2_to_bt_rel)
      

  definition "backtrack S\<^sub>b S \<equiv> S\<lparr> assignment := assignment S\<^sub>b, pending := {}, conflict := False \<rparr>"

  lemma backtrack_refine[refine]: 
    assumes "(S,Sfoo)\<in>twl2_bt_rel S\<^sub>b"
    assumes "(S\<^sub>b, S1) \<in> twl2_rel"
    shows "(backtrack S\<^sub>b S, S1) \<in> twl2_rel"
    using assms "twl2_bt_invar.backtrack_\<alpha>" "twl2_bt_invar.backtrack_invar"
    unfolding twl2_bt_rel_def twl2_rel_def br_def backtrack_def
    by auto
    
    

  definition "twl2_rup S L \<equiv> 
    do {
      ASSERT (\<not>conflict S); 
      ASSERT (pending S = {});
      S' \<leftarrow> twl2_prepare_rup S L;
      S' \<leftarrow> twl2_propagate S   S';
      let cn = twl2_has_conflict S';
      
      let S'=backtrack S S';
      RETURN (cn,S')
    }"


  lemma twl2_rup_refine[refine]: "(S,S1)\<in>twl2_rel \<Longrightarrow> twl2_rup S L \<le>\<Down>(bool_rel \<times>\<^sub>r twl2_rel) (twl1_rup S1 L)"
    unfolding twl2_rup_def twl1_rup_def Let_def
    apply (refine_rcg twl2_propagate_refine_rl prod_relI bind_refine' twl2_has_conflict_refine_rl_bt)
    apply (clarsimp_all)
    subgoal by (simp add: twl2_rel_def br_def)
    subgoal using "twl2_invar.no_pending_or_conf" by (auto simp: twl2_rel_def br_def)
    apply assumption
    apply assumption
    done
    

  definition "twl2_add_clause_aux C S \<equiv> S\<lparr>
    clause_db := clause_db S @[C], 
    valid_idxs := insert (length (clause_db S)) (valid_idxs S)
  \<rparr>"

  definition "twl2_add_clause_aux' C S \<equiv> do {
    ASSERT (let (w1,w2,_) = C in w1\<noteq>w2);
    RETURN (twl2_add_clause_aux C S)
  }"
  
  lemma twl2_add_clause_aux_other_fields[simp]:
    "twl2.assignment (twl2_add_clause_aux C S) = twl2.assignment S"
    "twl2.pending (twl2_add_clause_aux C S) = twl2.pending S"
    "twl2.conflict (twl2_add_clause_aux C S) = twl2.conflict S"
    unfolding twl2_add_clause_aux_def by auto

  lemma (in twl2_struct_invar) 
    CL_add_clause_aux: "twl2_defs.CL (twl2_add_clause_aux C S) = insert C CL"
    unfolding twl2_defs.CL_def twl2_add_clause_aux_def
    by (auto simp: nth_append)

  definition "twl2_find_watched C S \<equiv> do {
    let A = assignment S;
    OBTAIN (\<lambda>(w1,w2,ls).                 (* Obtain watched literals *)
        cl2_\<alpha> C = cl2_\<alpha> (w1,w2,ls)
      \<and> w1\<noteq>w2  
      \<and> (sem_lit' w1 A = Some False \<longrightarrow> sem_lit' w2 A = Some True)
      \<and> (sem_lit' w2 A = Some False \<longrightarrow> sem_lit' w1 A = Some True))
  }"

  definition "twl2_add C S \<equiv> do {
    let A = assignment S;
    C \<leftarrow> twl2_find_watched C S;

    (* Add clause to database *)
    twl2_add_clause_aux' C S
  }"


  
  lemma find_watched_abs:
    assumes NO_CONFLICT: "\<not>is_conflict_clause A C"
    assumes NO_UNIT: "\<not>is_unit_clause A C"
    assumes NO_SNG: "card C > Suc 0"
    obtains w1 w2 where "w1\<in>C" "w2\<in>C" "w1\<noteq>w2" 
      "(sem_lit' w1 A = Some False \<longrightarrow> sem_lit' w2 A = Some True)"
      "(sem_lit' w2 A = Some False \<longrightarrow> sem_lit' w1 A = Some True)"
  proof -
    from NO_SNG obtain n where CC: "card C = Suc (Suc n)"
      by (metis lessE)
  
    show ?thesis  
    proof cases
      assume "\<exists>l\<in>C. sem_lit' l A = Some True"
      then obtain w1 C' where 
        [simp]: "C=insert w1 C'" "sem_lit' w1 A = Some True" 
        and W1NC': "w1\<notin>C'"
        by (auto intro: Set.set_insert)
      from CC have "card C' = Suc n" 
        apply clarsimp 
        by (metis One_nat_def Suc_less_eq card_infinite card_insert_disjoint' W1NC'
          diff_Suc_1 finite_insert less_numeral_extra(4) zero_less_Suc)
      then obtain w2 where W2C': "w2\<in>C'" by (auto simp: card_Suc_eq)
  
      have [simp]: "{Some True, x} \<noteq> {Some False, None}" for x 
        by (cases x) blast+
  
      show ?thesis 
        apply (rule that[of w1 w2]) 
        using W1NC' W2C'
        by (auto simp: card_insert_if)
  
    next    
      assume A: "\<not>(\<exists>l\<in>C. sem_lit' l A = Some True)"
      hence "sem_clause' C A \<noteq> Some True"
        by (auto simp: sem_clause'_def)
      with NO_CONFLICT obtain w1 where "w1\<in>C" and [simp]: "sem_lit' w1 A = None"
        unfolding sem_clause'_def by (fastforce split: split_if_asm) 
      then obtain C' where [simp]: "C=insert w1 C'" and W1NC': "w1\<notin>C'" 
        by (auto elim: Set.set_insert)
  
      from NO_UNIT obtain w2 where W2C': "w2\<in>C'" and "sem_lit' w2 A \<noteq> Some False"
        unfolding is_unit_clause_def is_unit_lit_def sem_clause'_def
        by (fastforce split: split_if_asm)
        
      with A have [simp]: "sem_lit' w2 A = None" 
        by clarsimp (metis (full_types) option.collapse)
  
      show ?thesis 
        apply (rule that[of w1 w2]) 
        using W1NC' W2C' A
        by (auto simp: card_insert_if sem_clause'_def)
    qed
  qed

  lemma cl2_reorder1: (* Note: May need to duplicate literals! 
    However, an effective algorithm to reorder watched literals needs not to duplicate literals! *)
    assumes "w\<in>cl2_\<alpha> (l1,l2,ls)"
    obtains lsx where "cl2_\<alpha> (w,l2,lsx) = cl2_\<alpha> (l1,l2,ls)"
    using assms
    unfolding cl2_\<alpha>_def
    apply auto
    apply (metis List.set_insert insert_commute)
    by (metis List.set_insert insert_absorb insert_commute)

  lemma cl2_reorder2: 
    assumes "w\<in>cl2_\<alpha> (l1,l2,ls)"
    obtains lsx where "cl2_\<alpha> (l1,w,lsx) = cl2_\<alpha> (l1,l2,ls)"
  proof -
    from assms have "w\<in>cl2_\<alpha> (l2,l1,ls)" by (auto simp: cl2_\<alpha>_def)
    from cl2_reorder1[OF this] obtain lsx where "cl2_\<alpha> (w,l1,lsx) = cl2_\<alpha> (l2,l1,ls)" .
    hence "cl2_\<alpha> (l1,w,lsx) = cl2_\<alpha> (l1,l2,ls)" by (auto simp: cl2_\<alpha>_def)
    thus ?thesis by (rule that)
  qed  


  lemma twl2_add_refine[refine]: "\<lbrakk>(S,S1)\<in>twl2_rel; (C,Ca)\<in>br cl2_\<alpha> (\<lambda>_. True)\<rbrakk> \<Longrightarrow> twl2_add C S \<le> \<Down>twl2_rel (twl1_add Ca S1)"
    unfolding twl2_add_def twl1_add_def twl2_find_watched_def twl2_add_clause_aux'_def
    apply refine_vcg
    apply (clarsimp_all simp: twl2_rel_def br_def)
    apply (clarsimp_all simp: twl2_\<alpha>_def twl2_defs.F_def)
    proof -
      assume "twl2_invar S"
      then interpret twl2_invar S .

      let "?WC" = "\<lambda>w1 w2. (\<exists>ls. cl2_\<alpha> C = cl2_\<alpha> (w1, w2, ls)) \<and>
               w1 \<noteq> w2 \<and>
               (sem_lit' w1 A = Some False \<longrightarrow> sem_lit' w2 A = Some True) \<and>
               (sem_lit' w2 A = Some False \<longrightarrow> sem_lit' w1 A = Some True)"

      {
        assume "\<not>is_conflict_clause A (cl2_\<alpha> C)" "\<not>is_unit_clause A (cl2_\<alpha> C)" "Suc 0 < card (cl2_\<alpha> C)"
        from find_watched_abs[OF this] obtain w1 w2 where 
          ABS_IN: "w1 \<in> cl2_\<alpha> C" "w2 \<in> cl2_\<alpha> C" 
          and NEQ: "w1 \<noteq> w2" 
          and WATCHED_COND:
            "sem_lit' w1 A = Some False \<longrightarrow> sem_lit' w2 A = Some True"
            "sem_lit' w2 A = Some False \<longrightarrow> sem_lit' w1 A = Some True"
          .
        from ABS_IN obtain ls where "cl2_\<alpha> (w1,w2,ls) = cl2_\<alpha> C"
          by (metis cl2_reorder1 cl2_reorder2 prod_cases3)
        with WATCHED_COND NEQ show "\<exists>w1 w2. ?WC w1 w2" by auto
      }

      {
        fix w1 w2 ls
        assume NEQ: "w1 \<noteq> w2" 
          and WATCHED_COND:
            "sem_lit' w1 A = Some False \<longrightarrow> sem_lit' w2 A = Some True"
            "sem_lit' w2 A = Some False \<longrightarrow> sem_lit' w1 A = Some True"
          and [simp]: "\<not>CN"   

        assume NUC: "\<not>is_conflict_clause A (cl2_\<alpha> (w1,w2,ls))" "\<not>is_unit_clause A (cl2_\<alpha> (w1,w2,ls))"

        from no_pending_or_conf have [simp]: "P={}" by auto 
        show "
          insert (cl2_\<alpha> (w1, w2, ls)) (cl2_\<alpha> ` CL) = cl2_\<alpha> ` twl2_defs.CL (twl2_add_clause_aux (w1, w2, ls) S) \<and>
          twl2_invar (twl2_add_clause_aux (w1, w2, ls) S)"
          apply (rule conjI)
          apply (simp add: CL_add_clause_aux)
          apply unfold_locales
          apply (clarsimp_all simp: CL_add_clause_aux)
          subgoal 
            apply (erule disjE)
            apply (auto simp: cl2_watched_def NEQ) []
            using two_watched by auto
          subgoal by (auto simp: twl2_add_clause_aux_def less_Suc_eq)
          subgoal using conflict_covered NUC by auto  
          subgoal using unit_covered NUC by auto  
          subgoal using watched1 WATCHED_COND by auto
          subgoal using watched2 WATCHED_COND by auto
          done
      }
    qed



    definition "twl2_delete_idx i S \<equiv> do {
      ASSERT (i\<in>valid_idxs S);
      RETURN (S\<lparr> valid_idxs := valid_idxs S - {i} \<rparr>)
    }"

    lemma twl2_delete_refine:
      assumes "(S,S1)\<in>twl2_rel"
      assumes V: "i\<in>valid_idxs S"
      shows "twl2_delete_idx i S \<le>\<Down>twl2_rel (twl1_may_delete (cl2_\<alpha> (clause_db S!i)) S1)"
      using assms(1)
      unfolding twl2_delete_idx_def twl1_may_delete_def
      apply (refine_rcg RETURN_RES_refine)
      subgoal by (simp add: V)
      subgoal
        apply (clarsimp simp: twl2_rel_def br_def twl2_\<alpha>_def)
      proof (rule conjI)
        assume "twl2_invar S"
        then interpret twl2_invar S .
        assume NCC: "sem_clause' (cl2_\<alpha> (CLdb ! i)) A \<noteq> Some False"

        have CSS: "C\<in>twl2_defs.CL (S\<lparr>valid_idxs := VIs - {i}\<rparr>) \<Longrightarrow> C\<in>CL" for C
          by (auto simp: twl2_defs.CL_def)

        have CSS': "C\<in>CL \<Longrightarrow> C\<in>twl2_defs.CL (S\<lparr>valid_idxs := VIs - {i}\<rparr>) \<or> C = CLdb!i" for C
          by (auto simp: twl2_defs.CL_def)
        hence ACSS': "C\<in>F \<Longrightarrow> C\<in>twl2_defs.F (S\<lparr>valid_idxs := VIs - {i}\<rparr>) \<or> C = cl2_\<alpha> (CLdb!i)" for C
          by (fastforce simp: twl2_defs.F_def)

        show "twl2_invar (S\<lparr>valid_idxs := VIs - {i}\<rparr>)"
          apply unfold_locales
          apply (vc_solve solve: asm_rl)
          subgoal using pending_set .
          subgoal using two_watched by (blast dest: CSS)
          subgoal using conflict_imp ACSS' NCC by auto
          subgoal using conflict_covered by (auto dest: CSS)
          subgoal using unit_covered by (auto dest: CSS)
          subgoal apply (drule CSS) using watched1 by blast
          subgoal apply (drule CSS) using watched2 by blast
          subgoal using no_pending_or_conf by simp 
          done
      qed (clarsimp simp: twl2_defs.F_def twl2_defs.CL_def; blast)
      done


  subsubsection \<open>Abstraction Level 2'\<close>    
  text \<open>We use the data structure from level 2, but remove ghost parameters, 
    and introduce some low-level operations\<close>

  definition "twl2_pop_pending S \<equiv> do {
    l \<leftarrow> OBTAIN (\<lambda>l. l\<in>pending S);
    let S = S\<lparr>pending := pending S - {l}\<rparr>;
    RETURN (l,S)
  }"

  definition "twl2_lit_true l S \<equiv> sem_lit' l (assignment S) = Some True"
  definition "twl2_lit_false l S \<equiv> sem_lit' l (assignment S) = Some False"

  definition "twl2_get_watched i S \<equiv> 
    do {
      ASSERT (i<length (clause_db S)); 
      (w1,w2,_) \<leftarrow> RETURN (clause_db S!i);
      RETURN (w1,w2)
    }"

  definition "twl2_find_new_watched i w1 S \<equiv> do {
    ASSERT ((i<length (clause_db S)));
    let (_,_,ls) = (clause_db S!i);
    SELECT (\<lambda>(l,j). j<length ls \<and> l=ls!j \<and> \<not>twl2_lit_false (ls!j) S
              \<and> ls!j \<noteq> w1 (* TODO/FIXME: Required only if clauses may contain DUPs *)
            )
  }"

  definition "twl2_commit_new_watched i j w1 w2 l S \<equiv> do {
    ASSERT (i\<in>valid_idxs S);
    ASSERT ((i<length (clause_db S)));
    let (w1',w2',ls) = (clause_db S!i);
    ASSERT (w1'\<noteq>w2');
    ASSERT ((w1,w2) = (w1',w2') \<or> (w1,w2) = (w2',w1'));
    ASSERT (j<length ls); 
    ASSERT (l = ls!j);
    ASSERT (w1\<noteq>l \<and> w2\<noteq>l);

    let ls = ls[j:=w2];
    RETURN (S\<lparr> clause_db := (clause_db S)[ i := (w1,l,ls) ] \<rparr>)
  }"
  definition "twl2_set_conflict S b \<equiv> S\<lparr>conflict := b\<rparr>"

  definition "twl2_propagate_step' S0 \<equiv> do {
    (* Get and remove literal from (non-empty!) pending list *)
    (l,S) \<leftarrow> twl2_pop_pending S0;

    (* Get watched set for -l *)
    let wlist = twl2_watchset S l;

    (* Iterate over watched list, and restore invariant *)
    FOREACHc wlist (\<lambda>S. \<not>conflict S) (\<lambda>i S. do {
      (w1,w2) \<leftarrow> twl2_get_watched i S;

      if (twl2_lit_true w1 S \<or> twl2_lit_true w2 S) then
        RETURN S
      else do {
        (* Swap, to have w2 = -l*)
        let (w1,w2) = (if w1=neg_lit l then (w2,w1) else (w1,w2));

        (* Try to obtain undecided or true literal *)
        j \<leftarrow> twl2_find_new_watched i w1 S;
        case j of
          Some (l,j) \<Rightarrow> do {
            (* Found one: This is new watched literal *)
            S \<leftarrow> twl2_commit_new_watched i j w1 w2 l S;
            RETURN S
          }
        | None \<Rightarrow> do { 
            (* Found none: Propagate unit or mark conflict *)
            if twl2_lit_false w1 S then
              RETURN (twl2_set_conflict S True)
            else
              twl2_assign_aux S w1
        }
      }  
    }) S
  }"
  
  context begin
    private lemma case_right3: 
      assumes "\<And>a b c. x=(a,b,c) \<Longrightarrow> m \<le> m' a b c"
      shows "m \<le> (case x of (a,b,c) \<Rightarrow> m' a b c)"
      using assms apply (cases x) by auto
  
    private lemma if_refine_right: 
      assumes "b \<Longrightarrow> m \<le> t"
      assumes "\<not>b \<Longrightarrow> m \<le> e"
      shows "m \<le> If b t e"
      using assms by auto
  
    private lemma SELECT_fixed:  
      assumes "\<And>x y. P (x,y) \<Longrightarrow> x = f y"
      shows "(SELECT P \<bind> g) = (SELECT (\<lambda>y. \<exists>x. P (x,y)) \<bind> (\<lambda>None \<Rightarrow> g None | Some y \<Rightarrow> g (Some (f y,y))))"
      using assms by (clarsimp simp: pw_eq_iff refine_pw_simps SELECT_def split: option.split; blast)


    (* TODO/FIXME: Quite fragile proof construction *)
    lemma twl2_propagate_step'_refine[refine]: 
      "(S,S')\<in>Id \<Longrightarrow> twl2_propagate_step' S \<le> \<Down>Id (twl2_propagate_step S\<^sub>b   S')"
      apply simp
      supply split_if[split del]
      unfolding twl2_propagate_step'_def twl2_propagate_step_def
      unfolding Let_def twl2_pop_pending_def nres_monad_laws split
      apply (rule Refine_Basic.bind_mono)
        subgoal by simp
      apply (rule refine_IdD)
      apply (rule FOREACHci_refine_rcg'[OF inj_on_id])
        subgoal by simp
        subgoal by simp
        subgoal by simp
      apply simp  
      apply (intro le_ASSERTI)
      apply (rule case_right3)
      apply (intro le_ASSERTI)
      apply (simp add: twl2_get_watched_def)
      apply (rule if_refine_right; simp add: twl2_lit_true_def)
      apply (split prod.split; intro allI impI; clarsimp split: split_if_asm)
      subgoal  
        apply (simp add: twl2_find_new_watched_def twl2_lit_true_def twl2_lit_false_def)
        apply (subst SELECT_fixed) applyS auto []
        apply (rule Refine_Basic.bind_mono) subgoal by simp
        apply (rule pw_leI)
        by (auto split: option.split split_if 
          simp: twl2_set_conflict_def twl2_commit_new_watched_def
          simp: refine_pw_simps
          ) 
      subgoal
        apply (intro le_ASSERTI)
        apply (simp add: twl2_find_new_watched_def twl2_lit_true_def twl2_lit_false_def)
        apply (subst SELECT_fixed) applyS auto []
        apply (rule Refine_Basic.bind_mono) subgoal by simp
        apply (rule pw_leI)
        by (auto split: option.split split_if 
          simp: twl2_set_conflict_def twl2_commit_new_watched_def
          simp: refine_pw_simps
          ) 
      done  
  end    

  
  definition "twl2_propagate' S \<equiv> do {
    WHILET (\<lambda>S. pending S \<noteq> {} \<and> \<not>conflict S) (twl2_propagate_step') S
  }"
    
  lemma twl2_propagate'_refine[refine]: 
    "(S,S')\<in>Id \<Longrightarrow> twl2_propagate' S \<le> \<Down>Id (twl2_propagate S\<^sub>b   S')"
    unfolding twl2_propagate'_def twl2_propagate_def
    apply refine_rcg
    by simp_all
    



  definition "twl2_assign' S l \<equiv> do {
    S \<leftarrow> twl2_assign_aux S l;
    twl2_propagate' S
  }"

  lemma twl2_assign'_refine[refine]: "\<lbrakk>(S,S')\<in>Id; (l,l')\<in>Id\<rbrakk> \<Longrightarrow> twl2_assign' S l \<le> \<Down>Id (twl2_assign S\<^sub>b  S' l')"
    unfolding twl2_assign'_def twl2_assign_def
    apply refine_rcg
    apply refine_dref_type
    by simp_all

  definition "twl2_prepare_rup' S L \<equiv> do {
    S' \<leftarrow> twl2_prepare_rup S L;
    RETURN (S,S')
  }"

  definition "twl2_rup' S L \<equiv> 
    do {
      ASSERT (\<not>conflict S); 
      ASSERT (pending S = {});
      (bt_info,S') \<leftarrow> twl2_prepare_rup' S L;
      S' \<leftarrow> twl2_propagate' S';
      let cn = twl2_has_conflict S';
      
      let S'=backtrack bt_info S';
      RETURN (cn,S')
    }"

  lemma twl2_rup'_refine[refine]: 
    "\<lbrakk> (S,S')\<in>Id; (L,L')\<in>Id \<rbrakk> \<Longrightarrow> twl2_rup' S L \<le> \<Down>Id (twl2_rup S' L')"
    unfolding twl2_rup'_def twl2_rup_def twl2_prepare_rup'_def
    using twl2_propagate'_refine[OF IdI]
    by (simp add: pw_le_iff refine_pw_simps; blast)
    


  subsubsection \<open>Abstraction Level 3\<close>    

  record 'a twl3 = 
    clause_db :: "'a clause2 list"
    watchlist :: "'a literal \<Rightarrow> nat set"
    assignment :: "'a \<rightharpoonup> bool"
    pending :: "'a literal set"
    conflict :: bool

  locale twl3_defs = 
    fixes S :: "'a twl3" 
  begin  
    abbreviation "CLdb \<equiv> clause_db S"
    abbreviation "WL \<equiv> watchlist S"
    abbreviation "A \<equiv> assignment S"
    abbreviation "P \<equiv> pending S"
    abbreviation "CN \<equiv> conflict S"

    definition "VLIs \<equiv> \<Union>range WL"

    definition "CL \<equiv> {CLdb!i | i. i\<in>VLIs}"

    lemma VLIs_update: 
      "twl3_defs.VLIs (S\<lparr> clause_db := CLdb'\<rparr>) = VLIs" 
      "twl3_defs.VLIs (S\<lparr> assignment := A'\<rparr>) = VLIs" 
      "twl3_defs.VLIs (S\<lparr> pending := P'\<rparr>) = VLIs" 
      "twl3_defs.VLIs (S\<lparr> conflict := CN'\<rparr>) = VLIs" 
      unfolding twl3_defs.VLIs_def by auto
    lemmas (in -) [simp] = twl3_defs.VLIs_update

    lemma CL_update: 
      "twl3_defs.CL (S\<lparr> assignment := A'\<rparr>) = CL" 
      "twl3_defs.CL (S\<lparr> pending := P'\<rparr>) = CL" 
      "twl3_defs.CL (S\<lparr> conflict := CN'\<rparr>) = CL" 
      unfolding twl3_defs.CL_def by auto
    lemmas (in -) [simp] = twl3_defs.CL_update

  end

  definition "twl3_\<alpha> S \<equiv> \<lparr>
    twl2.clause_db = clause_db S,
    valid_idxs = twl3_defs.VLIs S,
    assignment = assignment S,
    pending = pending S,
    conflict = conflict S
  \<rparr>"  


  lemma twl3_\<alpha>_fields[simp]: 
    "twl2.clause_db (twl3_\<alpha> S) = twl3.clause_db S"  
    "twl2.assignment (twl3_\<alpha> S) = twl3.assignment S"  
    "twl2.pending (twl3_\<alpha> S) = twl3.pending S"  
    "twl2.conflict (twl3_\<alpha> S) = twl3.conflict S"  
    "twl2.valid_idxs (twl3_\<alpha> S) = twl3_defs.VLIs S"
    unfolding twl3_\<alpha>_def twl3_defs.VLIs_def by simp_all

  locale twl3_invar = twl3_defs +
    assumes watchlist_valid_idx: "VLIs \<subseteq> {0..<length CLdb}"
    assumes finite_P[simp, intro!]: "finite P"

    assumes watchlist_watched: "i\<in>VLIs \<Longrightarrow> i \<in> WL l \<longleftrightarrow> l \<in> cl2_watched (CLdb!i)"

    assumes watched_dj: "i\<in>VLIs \<Longrightarrow> CLdb!i=(w1,w2,ls) \<Longrightarrow> w1\<noteq>w2"

  begin
    lemma WL_VLI: "i\<in>WL l \<Longrightarrow> i\<in>VLIs"
      unfolding VLIs_def by auto

    lemma watchlist_watched1: "i\<in>WL l \<Longrightarrow> l\<in>cl2_watched (CLdb!i)"
      using WL_VLI watchlist_watched by blast

    lemma VLIs_len[simp, intro]: "i\<in>VLIs \<Longrightarrow> i<length CLdb" 
      using watchlist_valid_idx by auto


  end

  definition "twl3_rel \<equiv> br twl3_\<alpha> twl3_invar"  

  definition "twl3_empty \<equiv> \<lparr> clause_db = [], watchlist=(\<lambda>_. {}), assignment=Map.empty, pending={}, conflict=False \<rparr>"
  lemma twl3_empty_refine: "(twl3_empty,twl2_empty)\<in>twl3_rel"
    unfolding twl3_rel_def br_def twl3_\<alpha>_def twl2_empty_def twl3_empty_def twl3_defs.VLIs_def
    apply clarsimp
    apply unfold_locales
    by (auto simp: twl3_defs.VLIs_def)

  definition "twl3_assign_lit S l \<equiv> do {
    let A = assignment S;
    ASSERT (sem_lit' l A = None);
    RETURN (S\<lparr> assignment := assign_lit A l \<rparr>)
  }"

  definition "twl3_insert_pending S l \<equiv> do {
    let P = pending S;
    ASSERT (l \<notin> P);
    RETURN (S\<lparr> pending := insert l P \<rparr>)
  }"

  definition "twl3_assign_aux S l \<equiv> do {
    S \<leftarrow> twl3_assign_lit S l;
    twl3_insert_pending S l
  }"

  lemma twl3_assign_aux_refine: "(twl3_assign_aux, twl2_assign_aux) \<in> twl3_rel \<rightarrow> Id \<rightarrow> \<langle>twl3_rel\<rangle>nres_rel"
    apply (intro fun_relI nres_relI)
    unfolding twl3_assign_aux_def twl2_assign_aux_def twl3_insert_pending_def twl3_assign_lit_def
    apply refine_rcg
    unfolding twl3_rel_def br_def twl3_\<alpha>_def
    apply clarsimp
    apply (auto simp: twl3_invar_def twl3_defs.VLIs_def)
    done

  definition "twl3_watchset S l \<equiv> watchlist S (neg_lit l)"
    
  lemma twl3_watchset_refine: "(twl3_watchset,twl2_watchset) \<in> twl3_rel \<rightarrow> Id \<rightarrow> Id"
    apply (intro fun_relI nres_relI)
    unfolding twl3_watchset_def twl2_watchset_def twl3_rel_def br_def twl3_\<alpha>_def twl3_defs.VLIs_def
    apply (clarsimp; safe; (auto;fail)?)
  proof -
    fix S :: "'a twl3"
    assume "twl3_invar S"
    then interpret twl3_invar S .

    {
      fix i l
      assume "i\<in>WL (neg_lit l)"
      with watchlist_watched1 show "neg_lit l\<in>cl2_watched (CLdb ! i)" .
    }

    {
      fix l i ll
      assume "i\<in>WL ll" 
      hence IV: "i\<in>VLIs" using WL_VLI by blast
      
      assume "neg_lit l\<in>cl2_watched (CLdb ! i)"
      thus "i \<in> WL (neg_lit l)" using watchlist_watched[OF IV] by simp
    }
  qed  
    
  definition "twl3_pop_pending S \<equiv> do {
    l \<leftarrow> OBTAIN (\<lambda>l. l\<in>pending S);
    let S = S\<lparr>pending := pending S - {l}\<rparr>;
    RETURN (l,S)
  }"

  definition "twl3_lit_true l S \<equiv> sem_lit' l (assignment S) = Some True"
  definition "twl3_lit_false l S \<equiv> sem_lit' l (assignment S) = Some False"

  definition "twl3_get_watched i S \<equiv> 
    do {
      ASSERT (i<length (clause_db S)); 
      (w1,w2,_) \<leftarrow> RETURN (clause_db S!i);
      RETURN (w1,w2)
    }"

  definition "twl3_find_new_watched i w1 S \<equiv> do {
    ASSERT ((i<length (clause_db S)));
    let (_,_,ls) = (clause_db S!i);
    SELECT (\<lambda>(l,j). j<length ls \<and> l=ls!j \<and> \<not>twl3_lit_false (ls!j) S
              \<and> ls!j \<noteq> w1 (* TODO/FIXME: Required only if clauses may contain DUPs *)
            )
  }"

  definition "twl3_add_watchlist l i S \<equiv> do {
    let WL = watchlist S;
    ASSERT (i<length (clause_db S));
    ASSERT (i\<notin>WL l);
    RETURN (S\<lparr>
      watchlist := WL( l := insert i (WL l) )
    \<rparr>)
  }"

  definition "twl3_rem_watchlist l i S \<equiv> do {
    let WL = watchlist S;
    ASSERT (i<length (clause_db S));
    ASSERT (i\<in>WL l);
    RETURN (S\<lparr>
      watchlist := WL( l := WL l - {i} )
    \<rparr>)
  }"

  definition "twl3_set_watched1 w1 i S \<equiv> do {
    ASSERT (i<length (clause_db S));
    let (_,w2,ls) = clause_db S ! i;
    let S = S\<lparr>
      clause_db := (clause_db S)[ i := (w1,w2,ls) ]
    \<rparr>;
    RETURN S
  }"

  definition "twl3_set_watched2 w2 i S \<equiv> do {
    ASSERT (i<length (clause_db S));
    let (w1,_,ls) = clause_db S ! i;
    let S = S\<lparr>
      clause_db := (clause_db S)[ i := (w1,w2,ls) ]
    \<rparr>;
    RETURN S
  }"

  definition "twl3_set_cl_lit l j i S \<equiv> do {
    ASSERT (i<length (clause_db S));
    let (w1,w2,ls) = clause_db S ! i;
    ASSERT (j<length ls);
    let ls = ls[j:=l];
    let S = S\<lparr>
      clause_db := (clause_db S)[ i := (w1,w2,ls) ]
    \<rparr>;
    RETURN S
  }"


  definition "twl3_commit_new_watched i j w1 w2 l S \<equiv> do {
    (*ASSERT (i\<in>twl3_defs.VLIs S);
    ASSERT ((i<length (clause_db S)));*)

    S \<leftarrow> twl3_set_watched1 w1 i S;
    S \<leftarrow> twl3_set_watched2 l i S;
    S \<leftarrow> twl3_set_cl_lit w2 j i S;

    let WL = watchlist S;
    ASSERT (w1\<noteq>l \<and> w2\<noteq>l);
    (*ASSERT (i \<in> WL w2 \<and> i \<notin> WL l);*)
    S \<leftarrow> twl3_rem_watchlist w2 i S;
    S \<leftarrow> twl3_add_watchlist l i S;

    RETURN S
  }"

  definition "twl3_set_conflict S b \<equiv> S\<lparr>conflict := b\<rparr>"
    
    
  lemma twl3_pop_pending_refine: "(twl3_pop_pending, twl2_pop_pending) \<in> twl3_rel \<rightarrow> \<langle>Id\<times>\<^sub>rtwl3_rel\<rangle>nres_rel"
    apply (intro fun_relI nres_relI)
    unfolding twl3_pop_pending_def twl2_pop_pending_def
    apply (refine_rcg prod_relI)
    apply refine_dref_type
    apply (auto simp: twl3_rel_def br_def twl3_\<alpha>_def)
    apply (auto simp: twl3_invar_def twl3_defs.VLIs_def)
    done
    
  lemma twl3_lit_true_refine: "(twl3_lit_true, twl2_lit_true) \<in> Id \<rightarrow> twl3_rel \<rightarrow> bool_rel"
    apply (intro fun_relI nres_relI)
    unfolding twl3_lit_true_def twl2_lit_true_def
    by (auto simp: twl3_rel_def br_def twl3_\<alpha>_def)
    
  lemma twl3_lit_false_refine: "(twl3_lit_false, twl2_lit_false) \<in> Id \<rightarrow> twl3_rel \<rightarrow> bool_rel"
    apply (intro fun_relI nres_relI)
    unfolding twl3_lit_false_def twl2_lit_false_def
    by (auto simp: twl3_rel_def br_def twl3_\<alpha>_def)
    
  lemma twl3_get_watched_refine: "(twl3_get_watched, twl2_get_watched) \<in> Id \<rightarrow> twl3_rel \<rightarrow> \<langle>Id\<times>\<^sub>rId\<rangle>nres_rel"  
    apply (intro fun_relI nres_relI)
    unfolding twl3_get_watched_def twl2_get_watched_def
    apply (refine_rcg prod_relI)
    apply refine_dref_type
    by (auto simp: twl3_rel_def br_def twl3_\<alpha>_def)
    
  lemma twl3_find_new_watched_refine: "(twl3_find_new_watched, twl2_find_new_watched) \<in> Id \<rightarrow> Id \<rightarrow> twl3_rel \<rightarrow> \<langle>\<langle>Id\<rangle>option_rel\<rangle>nres_rel"
    apply (intro fun_relI nres_relI)
    unfolding twl3_find_new_watched_def twl2_find_new_watched_def
    apply (refine_rcg prod_relI)
    using twl3_lit_false_refine[THEN fun_relD, THEN fun_relD]
    apply (auto simp: refine_hsimp twl3_rel_def br_def twl3_\<alpha>_def; fastforce)+
    done
    
  lemma twl3_commit_new_watched_refine: "(twl3_commit_new_watched, twl2_commit_new_watched) \<in> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> twl3_rel \<rightarrow> \<langle>twl3_rel\<rangle>nres_rel"  
    apply (intro fun_relI nres_relI)
    unfolding twl3_commit_new_watched_def twl2_commit_new_watched_def
      twl3_rem_watchlist_def twl3_add_watchlist_def
      twl3_set_watched1_def twl3_set_watched2_def twl3_set_cl_lit_def
      Let_def
    apply (refine_vcg prod_relI)
    apply (clarsimp_all del: notI simp: twl3_rel_def br_def)
    apply (simp_all only: neq_commute[of "ls!j" for ls j])
  proof -
    fix S :: "'a twl3"
    assume "twl3_invar S"
    then interpret twl3_invar S .

    fix i w1' w2' ls
    assume [simp]: "i<length CLdb" and VLI: "i\<in>VLIs" and CLI: "CLdb!i = (w1',w2',ls)"

    
    fix w1 w2
    assume WW: "w1=w1' \<and> w2=w2' \<or> w1=w2' \<and> w2=w1'" and WNE': "w1'\<noteq>w2'"
    hence "w2\<in>cl2_watched (CLdb!i)" using CLI by (auto simp: cl2_watched_def)
    thus "i \<in> WL w2" using watchlist_watched VLI by simp

    fix j 
    assume "j<length ls"
    assume WNJ: "w1 \<noteq> ls!j" "w2 \<noteq> ls!j"

    hence "ls!j \<notin> cl2_watched (CLdb!i)" using WW CLI by (auto simp: cl2_watched_def)
    
    thus "i\<notin>WL (ls!j)"
      using watchlist_watched1 by blast
      
    let ?S2' = "(twl3_\<alpha> S)\<lparr> twl2.clause_db := CLdb[i := (w1, ls!j, ls[j := w2])] \<rparr>"
    let ?S3' = "S\<lparr> 
      twl3.clause_db := CLdb[i := (w1, ls!j, ls[j := w2])],    
      watchlist := WL( w2 := WL w2 - {i}, ls!j := insert i (WL (ls!j)) )
      \<rparr>"

    have [simp]: "twl3_defs.VLIs ?S3' = VLIs" using VLI 
      by (auto simp: twl3_defs.VLIs_def split: split_if_asm; metis)


    show "?S2' = twl3_\<alpha> ?S3' \<and> twl3_invar ?S3'"  
    proof (rule conjI)
      show "?S2' = twl3_\<alpha> ?S3'" by (auto simp: twl3_\<alpha>_def)

      show "twl3_invar ?S3'"
        apply unfold_locales
        apply simp_all

        subgoal using watchlist_valid_idx .
        subgoal 
          using watchlist_watched WNE' CLI WW
          by (auto simp: cl2_watched_def nth_list_update)

        subgoal using watched_dj WNJ  
          by (auto simp: nth_list_update split: split_if_asm)

        done
    qed
  qed      

  lemma twl3_set_conflict_refine: "(twl3_set_conflict, twl2_set_conflict) \<in> twl3_rel \<rightarrow> bool_rel \<rightarrow> twl3_rel"
    apply (intro fun_relI nres_relI)
    unfolding twl3_set_conflict_def twl2_set_conflict_def
    by (auto simp: twl3_rel_def br_def twl3_\<alpha>_def twl3_invar_def)
    

  definition "twl3_delete_idx i S \<equiv> do {
    (w1,w2) \<leftarrow> twl3_get_watched i S;
    let WL = watchlist S;

    ASSERT (i\<in>WL w1);
    ASSERT (i\<in>WL w2);
    ASSERT (w1\<noteq>w2);

    S \<leftarrow> twl3_rem_watchlist w1 i S;
    S \<leftarrow> twl3_rem_watchlist w2 i S;

    RETURN S
  }"
  
  lemma twl3_delete_idx_refine: "(twl3_delete_idx,twl2_delete_idx) \<in> Id \<rightarrow> twl3_rel \<rightarrow> \<langle>twl3_rel\<rangle>nres_rel"
    apply (intro fun_relI nres_relI)
    unfolding twl3_delete_idx_def twl2_delete_idx_def twl3_get_watched_def
      twl3_rem_watchlist_def
    apply (refine_vcg)
    apply (clarsimp_all simp: twl3_rel_def br_def del: notI)
  proof -
    fix S :: "'a twl3"
    assume "twl3_invar S"
    then interpret twl3_invar S .

    fix i
    assume VLI: "i\<in>VLIs"
    thus "i<length CLdb" by simp

    fix w1 w2 ls  
    assume CLI: "CLdb!i=(w1,w2,ls)"
    
    from CLI watchlist_watched[OF VLI] show "i\<in>WL w1" "i\<in>WL w2"
      by (auto simp: cl2_watched_def)

    from CLI watched_dj[OF VLI] show "w1\<noteq>w2" by auto 

    let ?S2' = "(twl3_\<alpha> S)\<lparr>valid_idxs := VLIs - {i}\<rparr>"
    let ?S3' = "S\<lparr>
      watchlist := WL(
        w1 := WL w1 - {i},
        w2 := WL w2 - {i}
      )
    \<rparr>"
    
    interpret S': twl3_defs ?S3' .

    have [simp]: "S'.VLIs = VLIs - {i}"
      unfolding S'.VLIs_def VLIs_def
      using watchlist_watched1[of i] CLI
      by (fastforce split: split_if_asm simp: CLI cl2_watched_def)

    show "?S2' = twl3_\<alpha> ?S3' \<and> twl3_invar ?S3'"    
    proof (rule conjI)
      show "?S2' = twl3_\<alpha> ?S3'" by (auto simp: twl3_\<alpha>_def)
        
      show "twl3_invar ?S3'"
        apply unfold_locales
        apply clarsimp_all
        subgoal using watchlist_watched by auto
        subgoal using watched_dj by auto
        done
    qed
  qed      


  definition "twl3_add_clause_aux C S \<equiv> do {
    let (w1,w2,_) = C;
    let WL = watchlist S;
    let CLdb = clause_db S;
    ASSERT (w1\<noteq>w2);

    let i = length CLdb;
    let S = S\<lparr> clause_db := CLdb@[C] \<rparr>;

    ASSERT (i\<notin>WL w1);
    ASSERT (i\<notin>WL w2);

    S \<leftarrow> twl3_add_watchlist w1 i S;
    S \<leftarrow> twl3_add_watchlist w2 i S;

    RETURN S
  }"
  

  lemma twl3_add_clause_aux_refine: "(twl3_add_clause_aux, twl2_add_clause_aux') \<in> Id \<rightarrow> twl3_rel \<rightarrow> \<langle>twl3_rel\<rangle>nres_rel"
    apply (intro fun_relI nres_relI)
    unfolding twl3_add_clause_aux_def twl2_add_clause_aux'_def twl2_add_clause_aux_def
      twl3_add_watchlist_def Let_def
    apply (refine_vcg)
    apply (clarsimp_all simp: twl3_rel_def br_def del: notI)
  proof -  
    fix S :: "'a twl3"
    assume "twl3_invar S"
    then interpret twl3_invar S .
    
    fix w1 w2 :: "'a literal" and ls :: "'a literal list"
    assume WNE: "w1\<noteq>w2"

    let ?i = "length CLdb"

    from watchlist_valid_idx have [simp]: "?i\<notin>WL l" for l
      unfolding VLIs_def by fastforce+

    thus "?i\<notin>WL w1" "?i\<notin>WL w2" by assumption+


    let ?S2' = "(twl3_\<alpha> S)\<lparr>
      twl2.clause_db := CLdb @ [(w1,w2,ls)],
      valid_idxs := insert ?i VLIs\<rparr>"
    
    let ?S3' = "S\<lparr>
      clause_db := CLdb@[(w1,w2,ls)], 
      watchlist := WL(
        w1 := insert ?i (WL w1),
        w2 := insert ?i (WL w2)
      )
    \<rparr>"  
    
    interpret S': twl3_defs ?S3' .

    have [simp]: "S'.VLIs = insert ?i VLIs"
      unfolding S'.VLIs_def VLIs_def
      by (auto split: split_if_asm)

    show "?S2' = twl3_\<alpha> ?S3' \<and> twl3_invar ?S3'"
    proof (rule conjI)  
      show "?S2' = twl3_\<alpha> ?S3'" by (auto simp: twl3_\<alpha>_def)
      
      show "twl3_invar ?S3'"
        apply unfold_locales
        apply clarsimp_all
        subgoal using watchlist_valid_idx by (auto simp del: VLIs_len)
        subgoal using watchlist_watched WNE by (auto simp: cl2_watched_def)
        subgoal using watched_dj WNE by fastforce
        done
    qed
  qed    


subsubsection \<open>Abstraction Level 4\<close>

paragraph \<open>Flat Clause Database\<close>


type_synonym lit = int

definition "lit_\<alpha> i \<equiv> 
  if i>0 then Pos (nat i) else if i<0 then Neg (nat (-i)) else undefined"
definition "lit_invar i \<equiv> i\<noteq>0"

definition "clause_\<alpha> C \<equiv> case C of w1#w2#ls \<Rightarrow> (w1,w2,ls) | _ \<Rightarrow> undefined"



record twl4 =
  clause_db :: "lit list"       -- \<open>Flat clause database. Sequence of zero-terminated clauses\<close>
  watchlist :: "lit list list"  -- \<open>Watchlist for each literal, \<open>N+l\<close> indexing\<close>
    wl_used :: "nat list"         -- \<open>Numbers of used elements in watchlists\<close>
  is_true :: "bool list"        -- \<open>Assignment, \<open>N+l\<close> indexing\<close>
  trail :: "lit list"           -- \<open>Trail and pending list\<close>
    tr_pstart :: "nat"            -- \<open>Index of first pending element\<close>
    tr_used :: "nat"              -- \<open>Index of first unused element\<close>
  conflict :: "bool"            -- \<open>Conflict flag\<close>

context
  fixes N :: nat
begin





oops
xxx: Define more basic operations on level3, that match what we want to 
  have on level4! e.g.: 

  add_watchlist  pre: not in
  remove_watchlist  pre: in

  insert_pending  pre: not in
  assign_lit  pre: undecided

  add_clause


Operations on clause db:
  get_watched :: idx \<rightarrow> lit \<times> lit
  add_clause :: clause \<rightarrow> ()
    In the final implementation, we will have a preset sequence of clauses,
    and always add/skip the next clause.

  the find/commit complex is still not structured enough.
    One possibility would be:
      find :: idx \<rightarrow> (lit\<rightarrow>bool) \<rightarrow> lit \<times> lit_idx
      set :: idx \<rightarrow> lit_idx \<rightarrow> lit \<rightarrow> ()
      set_watched1/2 :: idx \<rightarrow> lit \<rightarrow> ()

      Then, lit_idx is a literal-index in the clause. 

  Types flat clause-db:
    idx :: nat, index of start of clause
    lit_idx :: nat, index into clause, behind watched literals

xxx: Introduce clause-db operations, then implement flat clause db



oops

(*
xxx: All operations there: 
  decision point:
    1. Go for implementation:
        Implement clause list and indices by flat clause DB.  
        Implement literals by integers, assignment by bool list (with offset)
        Implement pending set by list
        Implement backtracking by collecting a trail, which is later reverted.

    2. Do abstract DRAT-checker. 
      Define abstractly the notion of valid proof. 
        \<rightarrow> Concept of clause-db as list (at least, proof as list) is also there abstractly!
      Show that our checker accepts exactly the valid proofs.    
      

  term twl2_assign_aux
*)

oops
for l i it S w1 w2 ls proof -

oops xxx: restore invar if true watched


end end

