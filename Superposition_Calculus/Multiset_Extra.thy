theory Multiset_Extra
  imports
    "HOL-Library.Multiset"
    "HOL-Library.Multiset_Order"
begin

lemma one_step_implies_multp\<^sub>H\<^sub>O_strong:
  fixes A B J K :: "_ multiset"
  defines "J \<equiv> B - A" and "K \<equiv> A - B"
  assumes "J \<noteq> {#}" and "\<forall>k \<in># K. \<exists>x \<in># J. R k x"
  shows "multp\<^sub>H\<^sub>O R A B"
  unfolding multp\<^sub>H\<^sub>O_def
proof (intro conjI allI impI)
  show "A \<noteq> B"
    using assms by force
next
  show "\<And>y. count B y < count A y \<Longrightarrow> \<exists>x. R y x \<and> count A x < count B x"
    using assms by (metis in_diff_count)
qed
  
definition is_maximal_wrt where
  "is_maximal_wrt R x M \<longleftrightarrow> x \<in># M \<and> (\<forall>y \<in># M - {#x#}. \<not> (R x y))"

lemma is_maximal_wrt_if_is_maximal_wrt_reflclp[simp]:
  "is_maximal_wrt R\<^sup>=\<^sup>= L C \<Longrightarrow> is_maximal_wrt R L C"
  unfolding is_maximal_wrt_def by simp

lemma Uniq_is_maximal_wrt_reflclp:
  shows "totalp_on (set_mset C) R \<Longrightarrow> \<exists>\<^sub>\<le>\<^sub>1L. L \<in># C \<and> is_maximal_wrt R\<^sup>=\<^sup>= L C"
  by (rule Uniq_I) (metis insert_DiffM insert_noteq_member is_maximal_wrt_def sup2CI totalp_onD)

lemma ex_is_maximal_wrt_if_not_empty:
  assumes "transp_on (set_mset M) R" and "asymp_on (set_mset M) R" and "M \<noteq> {#}"
  shows "\<exists>x \<in># M. is_maximal_wrt R x M"
  using assms
proof (induction M rule: multiset_induct)
  case empty
  hence False
    by simp
  thus ?case ..
next
  case (add x M)
  show ?case
  proof (cases "M = {#}")
    case True
    then show ?thesis
      by (simp add: is_maximal_wrt_def)
  next
    case False
    with add.prems add.IH obtain m where "m \<in># M" and "is_maximal_wrt R m M"
      using asymp_on_subset transp_on_subset
      by (metis diff_subset_eq_self set_mset_mono union_single_eq_diff)
    then show ?thesis
      unfolding is_maximal_wrt_def
      by (smt (verit, ccfv_SIG) add.prems(1) add.prems(2) add_mset_commute add_mset_remove_trivial
          asymp_onD at_most_one_mset_mset_diff insertE insert_Diff more_than_one_mset_mset_diff
          multi_member_split transp_onD union_single_eq_member)
  qed
qed

lemma lift_is_maximal_wrt_to_is_maximal_wrt_reflclp:
  assumes "is_maximal_wrt R x M"
  shows "is_maximal_wrt R\<^sup>=\<^sup>= x M \<longleftrightarrow> x \<notin># M - {#x#}"
  using assms
  by (metis (mono_tags, lifting) is_maximal_wrt_def reflp_onD reflp_on_reflclp sup2E)

lemma
  assumes "is_maximal_wrt R x M" and "\<not> is_maximal_wrt R\<^sup>=\<^sup>= x M"
  obtains M' where "M - {#x#} = add_mset x M'"
  using assms lift_is_maximal_wrt_to_is_maximal_wrt_reflclp
  by (meson mset_add)

lemma multp_singleton_singleton[simp]: "transp R \<Longrightarrow> multp R {#x#} {#y#} \<longleftrightarrow> R x y"
  using one_step_implies_multp[of "{#y#}" "{#x#}" R "{#}", simplified]
  using multp_implies_one_step[of R "{#x#}" "{#y#}", simplified]
  by (metis (no_types, opaque_lifting) add_mset_eq_single multi_member_split union_is_single
      union_single_eq_member)

lemma multp_subset_supersetI: "transp R \<Longrightarrow> multp R A B \<Longrightarrow> C \<subseteq># A \<Longrightarrow> B \<subseteq># D \<Longrightarrow> multp R C D"
  by (metis subset_implies_multp subset_mset.antisym_conv2 transpE transp_multp)

lemma multp_double_doubleI:
  assumes "transp R" "multp R A B"
  shows "multp R (A + A) (B + B)"
  using multp_repeat_mset_repeat_msetI[OF \<open>transp R\<close> \<open>multp R A B\<close>, of 2]
  by (simp add: numeral_Bit0)

lemma multp_implies_one_step_strong:
  fixes A B I J K :: "_ multiset"
  assumes "transp R" and "asymp R" and "multp R A B"
  defines "J \<equiv> B - A" and "K \<equiv> A - B"
  shows "J \<noteq> {#}" and "\<forall>k \<in># K. \<exists>x \<in># J. R k x"
proof -
  from assms have "multp\<^sub>H\<^sub>O R A B"
    by (simp add: multp_eq_multp\<^sub>H\<^sub>O)

  thus "J \<noteq> {#}" and "\<forall>k \<in># K. \<exists>x \<in># J. R k x"
    using multp\<^sub>H\<^sub>O_implies_one_step_strong[OF \<open>multp\<^sub>H\<^sub>O R A B\<close>]
    by (simp_all add: J_def K_def)
qed

lemma multp_double_doubleD:
  assumes "transp R" and "asymp R" and "multp R (A + A) (B + B)"
  shows "multp R A B"
proof -
  from assms have
    "B + B - (A + A) \<noteq> {#}" and
    "\<forall>k\<in>#A + A - (B + B). \<exists>x\<in>#B + B - (A + A). R k x"
    using multp_implies_one_step_strong[OF assms] by simp_all

  have "multp R (A \<inter># B + (A - B)) (A \<inter># B + (B - A))"
  proof (rule one_step_implies_multp[of "B - A" "A - B" R "A \<inter># B"])
    show "B - A \<noteq> {#}"
      using \<open>B + B - (A + A) \<noteq> {#}\<close>
      by (meson Diff_eq_empty_iff_mset mset_subset_eq_mono_add)
  next
    show "\<forall>k\<in>#A - B. \<exists>j\<in>#B - A. R k j"
    proof (intro ballI)
      fix x assume "x \<in># A - B"
      hence "x \<in># A + A - (B + B)"
        by (simp add: in_diff_count)
      then obtain y where "y \<in># B + B - (A + A)" and "R x y"
        using \<open>\<forall>k\<in>#A + A - (B + B). \<exists>x\<in>#B + B - (A + A). R k x\<close> by auto
      then show "\<exists>j\<in>#B - A. R x j"
        by (auto simp add: in_diff_count)
    qed
  qed

  moreover have "A = A \<inter># B + (A - B)"
    by (simp add: inter_mset_def)

  moreover have "B = A \<inter># B + (B - A)"
    by (metis diff_intersect_right_idem subset_mset.add_diff_inverse subset_mset.inf.cobounded2)

  ultimately show ?thesis
    by argo
qed

lemma multp_double_double:
  "transp R \<Longrightarrow> asymp R \<Longrightarrow> multp R (A + A) (B + B) \<longleftrightarrow> multp R A B"
  using multp_double_doubleD multp_double_doubleI by metis

lemma multp_single_doubleI: "M \<noteq> {#} \<Longrightarrow> multp R M (M + M)"
  using one_step_implies_multp[of M "{#}" _ M, simplified] by simp

lemma mult1_implies_one_step_strong:
  assumes "trans r" and \<open>asym r\<close> and "(A, B) \<in> mult1 r"
  shows "B - A \<noteq> {#}" and "\<forall>k \<in># A - B. \<exists>j \<in># B - A. (k, j) \<in> r"
proof -
  from \<open>(A, B) \<in> mult1 r\<close> obtain b B' A' where
    B_def: "B = add_mset b B'" and
    A_def: "A = B' + A'" and
    "\<forall>a. a \<in># A' \<longrightarrow> (a, b) \<in> r"
    unfolding mult1_def by auto

  have "b \<notin># A'"
    by (meson \<open>\<forall>a. a \<in># A' \<longrightarrow> (a, b) \<in> r\<close> assms(2) asym_onD iso_tuple_UNIV_I)
  then have "b \<in># B - A"
    by (simp add: A_def B_def)
  thus "B - A \<noteq> {#}"
    by auto

  show "\<forall>k \<in># A - B. \<exists>j \<in># B - A. (k, j) \<in> r"
    by (metis A_def B_def \<open>\<forall>a. a \<in># A' \<longrightarrow> (a, b) \<in> r\<close> \<open>b \<in># B - A\<close> \<open>b \<notin># A'\<close> add_diff_cancel_left'
        add_mset_add_single diff_diff_add_mset diff_single_trivial)
qed


lemma multp_if_maximal_less:
  assumes
    "transp R" and
    "totalp_on (set_mset M1 \<union> set_mset M2) R" and
    "x1 \<in># M1" and "x2 \<in># M2" and
    "is_maximal_wrt R x1 M1" and "R x1 x2"
  shows "multp R M1 M2"
proof (rule one_step_implies_multp[of _ _ _ "{#}", simplified])
  show "M2 \<noteq> {#}"
    using \<open>x2 \<in># M2\<close> by auto
next
  show "\<forall>k\<in>#M1. \<exists>j\<in>#M2. R k j"
    using assms
    by (smt (verit, ccfv_threshold) UnI1 at_most_one_mset_mset_diff insertE insert_Diff
        is_maximal_wrt_def iso_tuple_UNIV_I more_than_one_mset_mset_diff totalp_onD transp_onD)
qed

end