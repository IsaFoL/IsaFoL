theory LN_Lambda_Confluence
  imports
    LN_Lambda_Strong_Normalization
    LN_Lambda_Local_Confluence
    LN_Lambda_Typing_Safety
    "Abstract-Rewriting.Abstract_Rewriting"
begin

lemma SN_on_iff_wf_on:
  assumes closed: "\<And>x y. x \<in> A \<Longrightarrow> (x, y) \<in> r \<Longrightarrow> y \<in> A"
  shows "SN_on r A = wf_on A (r\<inverse>)"
  unfolding SN_on_def
  apply (subst wf_on_iff_wf)
  apply (subst wf_iff_no_infinite_down_chain)
proof (rule iffI)
  assume no_chain: "\<not> (\<exists>f. f 0 \<in> A \<and> chain r f)"
  show "\<not> (\<exists>f. \<forall>i. (f (Suc i), f i) \<in> {(x, y) \<in> r\<inverse>. x \<in> A \<and> y \<in> A})"
  proof
    assume "\<exists>f. \<forall>i. (f (Suc i), f i) \<in> {(x, y) \<in> r\<inverse>. x \<in> A \<and> y \<in> A}"
    then obtain f where steps:
      "\<And>i. (f (Suc i), f i) \<in> {(x, y) \<in> r\<inverse>. x \<in> A \<and> y \<in> A}"
      by blast
    have "f 0 \<in> A"
      using steps[of 0] by simp
    moreover have "chain r f"
      using steps by simp
    ultimately show False
      using no_chain by blast
  qed
next
  assume wf: "\<not> (\<exists>f. \<forall>i. (f (Suc i), f i) \<in> {(x, y) \<in> r\<inverse>. x \<in> A \<and> y \<in> A})"
  show "\<not> (\<exists>f. f 0 \<in> A \<and> chain r f)"
  proof
    assume "\<exists>f. f 0 \<in> A \<and> chain r f"
    then obtain f where f0: "f 0 \<in> A" and steps: "chain r f"
      by blast
    have in_A: "f i \<in> A" for i
    proof (induction i)
      case 0
      show ?case by (rule f0)
    next
      case (Suc i)
      have "(f i, f (Suc i)) \<in> r"
        using steps by simp
      then show ?case
        by (rule closed[OF Suc.IH])
    qed
    have "\<forall>i. (f (Suc i), f i) \<in> {(x, y) \<in> r\<inverse>. x \<in> A \<and> y \<in> A}"
      using steps in_A by simp
    then show False
      using wf by blast
  qed
qed


theorem beta_reduce_confluent_on_typed_terms:
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  defines "beta_reduce_rel \<equiv> {(t, t'). beta_reduce t (t' :: (_, _, '\<V>) preterm)}"
  shows "CR_on beta_reduce_rel {t. \<exists>\<C> \<F> \<tau>. has_type \<C> \<F> t \<tau>}"
proof (rule Abstract_Rewriting.WCR_SN_on_imp_CR_on)
  show "WCR beta_reduce_rel"
  proof (rule WCR_onI)
    fix a b c :: "(_, _, '\<V>) preterm"
    assume
      ab: "(a, b) \<in> beta_reduce_rel" and
      ac: "(a, c) \<in> beta_reduce_rel"
    then have red_ab: "beta_reduce a b" and red_ac: "beta_reduce a c"
      unfolding beta_reduce_rel_def
      by simp_all
    obtain v where
      bv: "beta_reduce\<^sup>*\<^sup>* b v" and cv: "beta_reduce\<^sup>*\<^sup>* c v"
      using local_confluence_beta_reduce[OF inf_vars red_ab red_ac] by blast
    have bv_set: "(b, v) \<in> beta_reduce_rel\<^sup>*"
      using bv by (simp add: beta_reduce_rel_def rtranclp_rtrancl_eq)
    have vc_set: "(v, c) \<in> (beta_reduce_rel\<inverse>)\<^sup>*"
      using cv
      by (simp add: beta_reduce_rel_def rtranclp_rtrancl_eq rtrancl_converse)
    show "(b, c) \<in> join beta_reduce_rel"
      unfolding join_def
      using bv_set vc_set by auto
  qed
next
  show "SN_on beta_reduce_rel {t. \<exists>\<C> \<F> \<tau>. has_type \<C> \<F> t \<tau>}"
  proof (rule SN_on_iff_wf_on[THEN iffD2])
    show "\<And>x y. x \<in> {t. \<exists>\<C> \<F> \<tau>. has_type \<C> \<F> t \<tau>} \<Longrightarrow> (x, y) \<in> beta_reduce_rel \<Longrightarrow>
      y \<in> {t. \<exists>\<C> \<F> \<tau>. has_type \<C> \<F> t \<tau>}"
      using LN_Lambda_Typing_Safety.preservation[OF inf_vars]
      using beta_reduce_rel_def by blast
  next
    show "wf_on {t. \<exists>\<C> \<F>. Ex (has_type \<C> \<F> t)} (beta_reduce_rel\<inverse>)"
      unfolding beta_reduce_rel_def
      using strong_normalization_of_typed_terms[OF inf_vars, unfolded conversep_iff]
      using wfp_on_wf_on_eq by fastforce
  qed
qed

end