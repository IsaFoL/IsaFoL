theory Full_Run
  imports
    VeriComp.Transfer_Extras
    HOL_Extra_Extra
begin

definition full_run where
  "full_run \<R> x y \<longleftrightarrow> \<R>\<^sup>*\<^sup>* x y \<and> (\<nexists>z. \<R> y z)"

lemma Uniq_full_run:
  assumes Uniq_R: "\<And>x. \<exists>\<^sub>\<le>\<^sub>1y. R x y"
  shows "\<exists>\<^sub>\<le>\<^sub>1y. full_run R x y"
  unfolding full_run_def
  using assms
  by (smt (verit, best) Uniq_I right_unique_iff rtranclp_complete_run_right_unique)

lemma ex1_full_run:
  assumes Uniq_R: "\<And>x. \<exists>\<^sub>\<le>\<^sub>1y. R x y" and wfP_R: "wfP R\<inverse>\<inverse>"
  shows "\<exists>!y. full_run R x y"
proof -
  have "\<exists>\<^sub>\<le>\<^sub>1 y. full_run R x y"
    using Uniq_full_run[of R x] Uniq_R by argo

  moreover have "\<exists>y. full_run R x y"
    using ex_terminating_rtranclp[OF wfP_R, of x, folded full_run_def] .

  ultimately show ?thesis
    using Uniq_implies_ex1 by metis
qed

lemma full_run_preserves_invariant:
  assumes
    run: "full_run R x y" and
    P_init: "P x" and
    R_preserves_P: "\<And>x y. R x y \<Longrightarrow> P x \<Longrightarrow> P y"
  shows "P y"
proof -
  from run have "R\<^sup>*\<^sup>* x y"
    unfolding full_run_def by simp
  thus "P y"
    using P_init
  proof (induction x rule: converse_rtranclp_induct)
    case base
    thus ?case
      by assumption
  next
    case (step x x')
    then show ?case
      using R_preserves_P by metis
  qed
qed

end