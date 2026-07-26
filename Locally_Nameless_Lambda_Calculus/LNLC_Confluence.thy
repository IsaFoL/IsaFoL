theory LNLC_Confluence
  imports
    LNLC_Strong_Normalization
    LNLC_Local_Confluence
    LNLC_Typing_Safety
    "Abstract-Rewriting.Abstract_Rewriting"
begin

theorem beta_reduce_confluent_on_typed_terms:
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  defines "beta_reduce_rel \<equiv> {(t, t'). beta_reduce t (t' :: (_, _, '\<V>) preterm)}"
  shows "CR_on beta_reduce_rel {t. \<exists>\<C> \<tau>. has_type \<C> t \<tau>}"
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
  show "SN_on beta_reduce_rel {t. \<exists>\<C> \<tau>. has_type \<C> t \<tau>}"
  proof (rule SN_on_iff_wf_on[THEN iffD2])
    show "\<And>x y. x \<in> {t. \<exists>\<C> \<tau>. has_type \<C> t \<tau>} \<Longrightarrow> (x, y) \<in> beta_reduce_rel \<Longrightarrow>
      y \<in> {t. \<exists>\<C> \<tau>. has_type \<C> t \<tau>}"
      using LNLC_Typing_Safety.preservation[OF inf_vars]
      using beta_reduce_rel_def by blast
  next
    show "wf_on {t. \<exists>\<C> \<tau>. has_type \<C> t \<tau>} (beta_reduce_rel\<inverse>)"
      unfolding beta_reduce_rel_def
      using strong_normalization_of_typed_terms[OF inf_vars, unfolded conversep_iff]
      using wfp_on_wf_on_eq by fastforce
  qed
qed

end