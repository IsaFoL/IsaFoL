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


lemma bex_max_element_with_property:
  assumes "finite A" and "asymp_on A R" and "transp_on A R" and "\<exists>x \<in> A. P x"
  shows "\<exists>y \<in> A. P y \<and> (\<forall>z \<in> A. R y z \<longrightarrow> \<not> P z)"
  using assms
proof (induction A rule: finite_induct)
  case empty
  hence False
    by simp
  thus ?case ..
next
  case (insert x F)

  from insert.prems have "asymp_on F R"
    using asymp_on_subset by blast

  from insert.prems have "transp_on F R"
    using transp_on_subset by blast

  show ?case
  proof (cases "\<exists>a\<in>F. P a")
    case True
    with insert.IH obtain y where "y \<in> F" and "P y" and "\<forall>z\<in>F. R y z \<longrightarrow> \<not> P z"
      using \<open>asymp_on F R\<close> \<open>transp_on F R\<close> by metis
    show ?thesis
    proof (cases "R x y")
      case True
      hence "\<not> R y x"
        using \<open>asymp_on (insert x F) R\<close>[THEN asymp_onD, of x y] \<open>y \<in> F\<close> by simp
      then show ?thesis
        using insert_iff[of _ x F]
        using \<open>y \<in> F\<close> \<open>P y\<close> \<open>\<forall>z\<in>F. R y z \<longrightarrow> \<not> P z\<close>
        apply (cases "P x")
        by metis+
    next
      case False
      then show ?thesis
        using
          \<open>asymp_on (insert x F) R\<close>[THEN asymp_onD, of x]
          \<open>transp_on (insert x F) R\<close>[THEN transp_onD, of y x]
          insert_iff[of _ x F]
        using \<open>y \<in> F\<close> \<open>P y\<close> \<open>\<forall>z\<in>F. R y z \<longrightarrow> \<not> P z\<close>
        by metis
    qed
  next
    case False
    then show ?thesis
      using \<open>\<exists>a\<in>insert x F. P a\<close>
      using \<open>asymp_on (insert x F) R\<close>[THEN asymp_onD, of x] insert_iff[of _ x F]
      by metis
  qed
qed

lemma bex_max_element':
  assumes "finite A" and "A \<noteq> {}" and "transp_on A R" and "asymp_on A R"
  shows bex_max_element: "\<exists>m \<in> A. \<forall>x \<in> A. x \<noteq> m \<longrightarrow> \<not> R m x"
proof -
  from \<open>A \<noteq> {}\<close> have "\<exists>x. x \<in> A"
    by auto
  hence "\<exists>y\<in>A. \<forall>z\<in>A. \<not> R y z"
    using bex_max_element_with_property[OF assms(1,4,3), of "\<lambda>_. True"] by simp
  thus ?thesis
    by auto
qed

lemma transp_on_multp\<^sub>H\<^sub>O:
  assumes "asymp_on A R" and "transp_on A R" and
    subset: "\<And>M. M \<in> B \<Longrightarrow> set_mset M \<subseteq> A"
  shows "transp_on B (multp\<^sub>H\<^sub>O R)"
proof (rule transp_onI)
  from assms have "asymp_on B (multp\<^sub>H\<^sub>O R)"
    using asymp_on_multp\<^sub>H\<^sub>O by metis

  fix M1 M2 M3
  assume hyps: "M1 \<in> B" "M2 \<in> B" "M3 \<in> B" "multp\<^sub>H\<^sub>O R M1 M2" "multp\<^sub>H\<^sub>O R M2 M3"

  from assms have
    [intro]: "asymp_on (set_mset M1 \<union> set_mset M2) R" "transp_on (set_mset M1 \<union> set_mset M2) R"
    using \<open>M1 \<in> B\<close> \<open>M2 \<in> B\<close>
    by (simp_all add: asymp_on_subset transp_on_subset)

  from assms have "transp_on (set_mset M1) R"
    by (meson transp_on_subset hyps(1))

  from \<open>multp\<^sub>H\<^sub>O R M1 M2\<close> have
    "M1 \<noteq> M2" and
    "\<forall>y. count M2 y < count M1 y \<longrightarrow> (\<exists>x. R y x \<and> count M1 x < count M2 x)"
    unfolding multp\<^sub>H\<^sub>O_def by simp_all

  from \<open>multp\<^sub>H\<^sub>O R M2 M3\<close> have
    "M2 \<noteq> M3" and
    "\<forall>y. count M3 y < count M2 y \<longrightarrow> (\<exists>x. R y x \<and> count M2 x < count M3 x)"
    unfolding multp\<^sub>H\<^sub>O_def by simp_all

  show "multp\<^sub>H\<^sub>O R M1 M3"
  proof (rule ccontr)
    let ?P = "\<lambda>x. count M3 x < count M1 x \<and> (\<forall>y. R x y \<longrightarrow> count M1 y \<ge> count M3 y)"

    assume "\<not> multp\<^sub>H\<^sub>O R M1 M3"
    hence "M1 = M3 \<or> (\<exists>x. ?P x)"
      unfolding multp\<^sub>H\<^sub>O_def by force
    thus False
    proof (elim disjE)
      assume "M1 = M3"
      thus False
        using \<open>asymp_on B (multp\<^sub>H\<^sub>O R)\<close>[THEN asymp_onD]
        using \<open>M2 \<in> B\<close> \<open>M3 \<in> B\<close> \<open>multp\<^sub>H\<^sub>O R M1 M2\<close> \<open>multp\<^sub>H\<^sub>O R M2 M3\<close>
        by metis
    next
      assume "\<exists>x. ?P x"
      hence "\<exists>x \<in># M1 + M2. ?P x"
        by (auto simp: count_inI)
      have "\<exists>y \<in># M1 + M2. ?P y \<and> (\<forall>z \<in># M1 + M2. R y z \<longrightarrow> \<not> ?P z)"
      proof (rule bex_max_element_with_property)
        show "\<exists>x \<in># M1 + M2. ?P x"
          using \<open>\<exists>x. ?P x\<close>
          by (auto simp: count_inI)
      qed auto
      then obtain x where
        "x \<in># M1 + M2" and
        "count M3 x < count M1 x" and
        "\<forall>y. R x y \<longrightarrow> count M1 y \<ge> count M3 y" and
        "\<forall>y \<in># M1 + M2. R x y \<longrightarrow> count M3 y < count M1 y \<longrightarrow> (\<exists>z. R y z \<and> count M1 z < count M3 z)"
        by force

      let ?Q = "\<lambda>x'. R\<^sup>=\<^sup>= x x' \<and> count M3 x' < count M2 x'"
      show False
      proof (cases "\<exists>x'. ?Q x'")
        case True
        have "\<exists>y \<in># M1 + M2. ?Q y \<and> (\<forall>z \<in># M1 + M2. R y z \<longrightarrow> \<not> ?Q z)"
        proof (rule bex_max_element_with_property)
          show "\<exists>x \<in># M1 + M2. ?Q x"
            using \<open>\<exists>x. ?Q x\<close>
            by (auto simp: count_inI)
        qed auto
        then obtain x' where
          "x' \<in># M1 + M2" and
          "R\<^sup>=\<^sup>= x x'" and
          "count M3 x' < count M2 x'" and
          maximality_x': "\<forall>z \<in># M1 + M2. R x' z \<longrightarrow> \<not> (R\<^sup>=\<^sup>= x z) \<or> count M3 z \<ge> count M2 z"
          by (auto simp: linorder_not_less)
        with \<open>multp\<^sub>H\<^sub>O R M2 M3\<close> obtain y' where
          "R x' y'" and "count M2 y' < count M3 y'"
          unfolding multp\<^sub>H\<^sub>O_def by auto
        hence "count M2 y' < count M1 y'"
          by (smt (verit) \<open>R\<^sup>=\<^sup>= x x'\<close> \<open>\<forall>y. R x y \<longrightarrow> count M3 y \<le> count M1 y\<close>
              \<open>count M3 x < count M1 x\<close> \<open>count M3 x' < count M2 x'\<close> assms(2) count_inI
              dual_order.strict_trans1 hyps(1) hyps(2) hyps(3) less_nat_zero_code subset subsetD
              sup2E transp_onD)
        with \<open>multp\<^sub>H\<^sub>O R M1 M2\<close> obtain y'' where
          "R y' y''" and "count M1 y'' < count M2 y''"
          unfolding multp\<^sub>H\<^sub>O_def by auto
        hence "count M3 y'' < count M2 y''"
          by (smt (verit, del_insts) \<open>R x' y'\<close> \<open>R\<^sup>=\<^sup>= x x'\<close> \<open>\<forall>y. R x y \<longrightarrow> count M3 y \<le> count M1 y\<close>
              \<open>count M2 y' < count M3 y'\<close> \<open>count M3 x < count M1 x\<close> \<open>count M3 x' < count M2 x'\<close>
              assms(2) count_greater_zero_iff dual_order.strict_trans1 hyps(1) hyps(2) hyps(3)
              less_nat_zero_code linorder_not_less subset subset_iff sup2E transp_onD)

        moreover have "count M2 y'' \<le> count M3 y''"
        proof -
          have "y'' \<in># M1 + M2"
            by (metis \<open>count M1 y'' < count M2 y''\<close> count_inI not_less_iff_gr_or_eq union_iff)

          moreover have "R x' y''"
            by (metis \<open>R x' y'\<close> \<open>R y' y''\<close> \<open>count M2 y' < count M1 y'\<close>
                \<open>transp_on (set_mset M1 \<union> set_mset M2) R\<close> \<open>x' \<in># M1 + M2\<close> calculation count_inI
                nat_neq_iff set_mset_union transp_onD union_iff)

          moreover have "R\<^sup>=\<^sup>= x y''"
            using \<open>R\<^sup>=\<^sup>= x x'\<close>
            by (metis (mono_tags, opaque_lifting) \<open>transp_on (set_mset M1 \<union> set_mset M2) R\<close>
                \<open>x \<in># M1 + M2\<close> \<open>x' \<in># M1 + M2\<close> calculation(1) calculation(2) set_mset_union sup2I1
                transp_onD transp_on_reflclp)

          ultimately show ?thesis
            using maximality_x'[rule_format, of y''] by metis
        qed

        ultimately show ?thesis
          by linarith
      next
        case False
        hence "\<And>x'. R\<^sup>=\<^sup>= x x' \<Longrightarrow> count M2 x' \<le> count M3 x'"
          by auto
        hence "count M2 x \<le> count M3 x"
          by simp
        hence "count M2 x < count M1 x"
          using \<open>count M3 x < count M1 x\<close> by linarith
        with \<open>multp\<^sub>H\<^sub>O R M1 M2\<close> obtain y where
          "R x y" and "count M1 y < count M2 y"
          unfolding multp\<^sub>H\<^sub>O_def by auto
        hence "count M3 y < count M2 y"
          using \<open>\<forall>y. R x y \<longrightarrow> count M3 y \<le> count M1 y\<close> dual_order.strict_trans2 by metis
        then show ?thesis
          using False \<open>R x y\<close> by auto
      qed
    qed
  qed
qed
  
definition is_maximal_wrt where
  "is_maximal_wrt R x M \<longleftrightarrow> (\<forall>y \<in># M - {#x#}. \<not> (R x y))"

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