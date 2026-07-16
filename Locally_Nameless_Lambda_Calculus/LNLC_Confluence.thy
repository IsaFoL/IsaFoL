theory LNLC_Confluence
  imports
    LNLC_Strong_Normalization
    LNLC_Local_Confluence
    LNLC_Typing_Safety
    "Abstract-Rewriting.Abstract_Rewriting"
begin

lemma SN_on_iff_wf_on:
  assumes closed: "\<And>x y. x \<in> A \<Longrightarrow> (x, y) \<in> r \<Longrightarrow> y \<in> A"
  shows "SN_on r A = wf_on A (r\<inverse>)"
proof -
  have "SN_on r A \<longleftrightarrow> (\<nexists>f. f 0 \<in> A \<and> (\<forall>i. (f i, f (Suc i)) \<in> r))"
    unfolding SN_on_def ..

  also have "\<dots> \<longleftrightarrow> (\<nexists>f. \<forall>i. (f (Suc i), f i) \<in> {(x, y). (x, y) \<in> r\<inverse> \<and> x \<in> A \<and> y \<in> A})"
    (is "?LHS \<longleftrightarrow> ?RHS")
  proof (rule iffI)
    assume ?LHS
    show ?RHS
    proof (rule notI)
      assume "\<exists>f. \<forall>i. (f (Suc i), f i) \<in> {(x, y) \<in> r\<inverse>. x \<in> A \<and> y \<in> A}"
      then obtain f where steps:
        "\<And>i. (f (Suc i), f i) \<in> {(x, y) \<in> r\<inverse>. x \<in> A \<and> y \<in> A}"
        by blast

      have "f 0 \<in> A"
        using steps[of 0] by simp

      moreover have "chain r f"
        using steps by simp

      ultimately show False
        using \<open>?LHS\<close> by blast
    qed
  next
    assume ?RHS
    show ?LHS
    proof (rule notI)
      assume "\<exists>f. f 0 \<in> A \<and> chain r f"
      then obtain f where "f 0 \<in> A" and "chain r f"
        by blast

      have "f i \<in> A" for i
      proof (induction i)
        case 0
        show ?case
          using \<open>f 0 \<in> A\<close> .
      next
        case (Suc i)
        have "(f i, f (Suc i)) \<in> r"
          using \<open>chain r f\<close> by simp
        then show ?case
          by (rule closed[OF Suc.IH])
      qed
      then have "\<forall>i. (f (Suc i), f i) \<in> {(x, y) \<in> r\<inverse>. x \<in> A \<and> y \<in> A}"
        using \<open>chain r f\<close> by simp
      then show False
        using \<open>?RHS\<close> by blast
    qed
  qed

  also have "\<dots> \<longleftrightarrow> wf {(x, y) \<in> r\<inverse>. x \<in> A \<and> y \<in> A}"
    unfolding wf_iff_no_infinite_down_chain ..

  also have "\<dots> \<longleftrightarrow> wf_on A (r\<inverse>)"
    using wf_on_iff_wf[of A "r\<inverse>"] ..

  finally show ?thesis .
qed

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
    show "wf_on {t. \<exists>\<C>. Ex (has_type \<C> t)} (beta_reduce_rel\<inverse>)"
      unfolding beta_reduce_rel_def
      using strong_normalization_of_typed_terms[OF inf_vars, unfolded conversep_iff]
      using wfp_on_wf_on_eq by fastforce
  qed
qed

end