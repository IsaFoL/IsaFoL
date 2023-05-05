theory Multiset_Extra
  imports
    "HOL-Library.Multiset"
    "HOL-Library.Multiset_Order"
begin

term asymp
  
definition is_maximal_wrt where
  "is_maximal_wrt R x M \<longleftrightarrow> (\<forall>y \<in># M - {#x#}. \<not> (R x y))"

lemma is_maximal_wrt_if_is_maximal_wrt_reflclp[simp]:
  "is_maximal_wrt R\<^sup>=\<^sup>= L C \<Longrightarrow> is_maximal_wrt R L C"
  unfolding is_maximal_wrt_def by simp

lemma Uniq_is_maximal_wrt_reflclp:
  shows "totalp_on (set_mset C) R \<Longrightarrow> \<exists>\<^sub>\<le>\<^sub>1L. L \<in># C \<and> is_maximal_wrt R\<^sup>=\<^sup>= L C"
  by (rule Uniq_I) (metis insert_DiffM insert_noteq_member is_maximal_wrt_def sup2CI totalp_onD)

thm Finite_Set.bex_min_element Finite_Set.bex_least_element

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

lemma multp\<^sub>H\<^sub>O_implies_one_step_strong:
  fixes A B J K :: "_ multiset"
  assumes "multp\<^sub>H\<^sub>O R A B"
  defines "J \<equiv> B - A" and "K \<equiv> A - B"
  shows "J \<noteq> {#}" and "\<forall>k \<in># K. \<exists>x \<in># J. R k x"
  using assms
  apply (metis diff_subset_eq_self inter_mset_def multp\<^sub>D\<^sub>M_def multp\<^sub>H\<^sub>O_imp_multp\<^sub>D\<^sub>M multp\<^sub>H\<^sub>O_plus_plus
      subset_mset.add_diff_inverse subset_mset.inf.cobounded2 subset_mset.le_zero_eq)
  using assms
  by (metis J_def K_def in_diff_count multp\<^sub>H\<^sub>O_def)

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

thm mult_implies_one_step

(* lemma mult_implies_one_step:
  fixes M N I J K
  assumes
    trans: "trans r" and "asym r" and
    MN: "(M, N) \<in> mult r"
  defines "I \<equiv> M \<inter># N"
  shows "\<exists>J K. N = I + J \<and> M = I + K \<and> J \<noteq> {#} \<and> (\<forall>k \<in> set_mset K. \<exists>j \<in> set_mset J. (k, j) \<in> r)"
  using MN unfolding mult_def I_def
proof (induction rule: converse_trancl_induct)
  case (base M)
  then obtain n N' M' where
    N_def: "N = add_mset n N'" and
    M_def: "M = N' + M'" and
    "\<forall>m. m \<in># M' \<longrightarrow> (m, n) \<in> r"
    unfolding mult1_def by auto

  hence "n \<notin># M'"
    by (meson \<open>asym r\<close> asymD)

  define J where
    "J = N - M"

  define K where
    "K = M - N"

  show ?case
  proof (intro exI conjI)
    show "N = M \<inter># N + J"
      unfolding J_def
      by (metis diff_intersect_right_idem subset_mset.add_diff_inverse subset_mset.inf.cobounded2)
  next
    show "M = M \<inter># N + K"
      unfolding K_def
      by (simp add: inter_mset_def)
  next
    show "J \<noteq> {#}"
      using \<open>n \<notin># M'\<close>
      by (simp add: J_def N_def M_def)
  next
    show "\<forall>k\<in>#K. \<exists>j\<in>#J. (k, j) \<in> r"
      using J_def K_def assms(2) base local.trans mult1_implies_one_step_strong(2) by blast
  qed
next
  case (step y z) note yz = this(1) and zN = this(2) and N_decomp = this(3)
  obtain J K where
    N: "N = z \<inter># N + J" "z = z \<inter># N + K" "J \<noteq> {#}" "\<forall>k\<in>#K. \<exists>j\<in>#J. (k, j) \<in> r"
    using N_decomp by blast
  obtain a M0 K' where
    z: "z = add_mset a M0" and y: "y = M0 + K'" and K: "\<forall>b. b \<in># K' \<longrightarrow> (b, a) \<in> r"
    using yz unfolding mult1_def by blast
  show ?case
  proof (cases "a \<in># K")
    case True
    moreover have "\<exists>j\<in>#J. (k, j) \<in> r" if "k \<in># K'" for k
      using K N trans True by (meson that transE)
    ultimately show ?thesis
      apply -
      apply (rule_tac x = J in exI, rule_tac x = "(K - {#a#}) + K'" in exI)
      apply (intro conjI)
      apply (use z y N in \<open>auto simp del: subset_mset.add_diff_assoc2 dest: in_diffD\<close>)
      sledgehammer
  next
    case False
    then have "a \<in># I" by (metis N(2) union_iff union_single_eq_member z)
    moreover have "M0 = I + K - {#a#}"
      using N(2) z by force
    ultimately show ?thesis
      by (rule_tac x = "add_mset a J" in exI,
          rule_tac x = "K + K'" in exI)
        (use z y N False K in \<open>auto simp: add.assoc\<close>)
  qed
qed *)

lemma mult_implies_one_step_strong:
  assumes "trans r" and \<open>asym r\<close> and "(A, B) \<in> mult r"
  shows "B - A \<noteq> {#}" and "\<forall>k \<in># A - B. \<exists>j \<in># B - A. (k, j) \<in> r"
  using \<open>(A, B) \<in> mult r\<close>
  unfolding atomize_conj mult_def
proof (induction A rule: converse_trancl_induct)
  case (base A)
  then show ?case
    using mult1_implies_one_step_strong[OF \<open>trans r\<close> \<open>asym r\<close>] by simp
next
  case (step A C)
  from step.hyps obtain c C' A' where
    C_def: "C = add_mset c C'" and
    A_def: "A = C' + A'" and
    "\<forall>a. a \<in># A' \<longrightarrow> (a, c) \<in> r"
    by (auto simp: mult1_def)

  have "c \<notin># A'"
    by (meson \<open>\<forall>a. a \<in># A' \<longrightarrow> (a, c) \<in> r\<close> assms(2) asym_onD iso_tuple_UNIV_I)

  from step.IH have "B - C \<noteq> {#}" and "\<forall>k\<in>#C - B. \<exists>j\<in>#B - C. (k, j) \<in> r"
    by simp_all

  thm mult1_implies_one_step_strong[OF \<open>trans r\<close> \<open>asym r\<close> \<open>(A, C) \<in> mult1 r\<close>]

  show ?case
  proof (cases "c \<in># C - B")
    case True
    moreover hence "\<exists>j\<in>#B - C. (k, j) \<in> r" if "k \<in># A'" for k
      by (meson \<open>\<forall>a. a \<in># A' \<longrightarrow> (a, c) \<in> r\<close> \<open>\<forall>k\<in>#C - B. \<exists>j\<in>#B - C. (k, j) \<in> r\<close> \<open>trans r\<close> that
          transD)
    ultimately show ?thesis
      unfolding A_def
      apply (intro conjI)
      
      sorry
  next
    case False
    then show ?thesis
      sorry
  qed
qed





































end