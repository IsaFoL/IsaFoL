theory First_Order_Superposition_Example
  imports
    IsaFoR_Term_Copy
    First_Order_Superposition
begin

abbreviation trivial_select :: "('f, 'v) select" where
  "trivial_select _ \<equiv> {#}"

abbreviation trivial_tiebreakers where
  "trivial_tiebreakers _ _ _ \<equiv> False"

context
  assumes ground_critical_pair_theorem:
    "\<And>(R :: ('f :: weighted) gterm rel). ground_critical_pair_theorem R"
begin

interpretation first_order_superposition_calculus 
  "trivial_select :: ('f :: weighted, 'v :: infinite) select" 
  less_kbo
  trivial_tiebreakers
  "\<lambda>_. ([], ())"
proof(unfold_locales)
  fix clause :: "('f, 'v) atom clause"

  show "trivial_select clause \<subseteq># clause"
    by simp
next
  fix clause :: "('f, 'v) atom clause" and literal

  assume "literal \<in># trivial_select clause"

  then show "is_neg literal"
    by simp
next
  show "transp less_kbo"
    using KBO.S_trans 
    unfolding transp_def less_kbo_def
    by blast
next
  show "asymp less_kbo"
    using wfP_imp_asymp wfP_less_kbo 
    by blast
next
  show "Wellfounded.wfp_on {term. term.is_ground term} less_kbo"
    using Wellfounded.wfp_on_subset[OF wfP_less_kbo subset_UNIV] .
next
  show "totalp_on {term. term.is_ground term} less_kbo"
    using less_kbo_gtotal
    unfolding totalp_on_def Term.ground_vars_term_empty
    by blast
next
  fix 
    context\<^sub>G :: "('f, 'v) context" and
    term\<^sub>G\<^sub>1 term\<^sub>G\<^sub>2 :: "('f, 'v) term" 

  assume "less_kbo term\<^sub>G\<^sub>1 term\<^sub>G\<^sub>2" 

  then show "less_kbo context\<^sub>G\<langle>term\<^sub>G\<^sub>1\<rangle> context\<^sub>G\<langle>term\<^sub>G\<^sub>2\<rangle>"
    using KBO.S_ctxt less_kbo_def by blast
next
  fix 
    term\<^sub>1 term\<^sub>2 :: "('f, 'v) term" and 
    \<gamma> :: "('f, 'v) subst"

  assume "less_kbo term\<^sub>1 term\<^sub>2"

  then show "less_kbo (term\<^sub>1 \<cdot>t \<gamma>) (term\<^sub>2 \<cdot>t \<gamma>)"
    using less_kbo_subst by blast
next
  fix
    term\<^sub>G :: "('f, 'v) term" and
    context\<^sub>G :: "('f, 'v) context"
  assume 
    "term.is_ground term\<^sub>G" 
    "context.is_ground context\<^sub>G" 
    "context\<^sub>G \<noteq> \<box>"
  
  then show "less_kbo term\<^sub>G context\<^sub>G\<langle>term\<^sub>G\<rangle>"
    by (simp add: KBO.S_supt less_kbo_def nectxt_imp_supt_ctxt)
next
  show "\<And>(R :: ('f gterm \<times> 'f gterm) set). ground_critical_pair_theorem R"
    using ground_critical_pair_theorem .
next
  show "\<And>clause\<^sub>G. wfP (\<lambda>_ _. False) \<and> transp (\<lambda>_ _. False) \<and> asymp (\<lambda>_ _. False)"
    by (simp add: asympI)
next
  show "\<And>\<tau>. \<exists>f. ([], ()) = ([], \<tau>)"
    by simp
next
  show "|UNIV :: unit set| \<le>o |UNIV|"
    unfolding UNIV_unit
    by simp
qed

end

end
