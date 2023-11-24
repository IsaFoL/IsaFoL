theory Multiset_Extra
  imports
    "HOL-Library.Multiset"
    "HOL-Library.Multiset_Order"
    Nested_Multisets_Ordinals.Multiset_More
begin

lemma one_le_countE:
  assumes "1 \<le> count M x"
  obtains M' where "M = add_mset x M'"
  using assms by (meson count_greater_eq_one_iff multi_member_split)

lemma two_le_countE:
  assumes "2 \<le> count M x"
  obtains M' where "M = add_mset x (add_mset x M')"
  using assms
  by (metis Suc_1 Suc_eq_plus1_left Suc_leD add.right_neutral count_add_mset multi_member_split
      not_in_iff not_less_eq_eq)

lemma three_le_countE:
  assumes "3 \<le> count M x"
  obtains M' where "M = add_mset x (add_mset x (add_mset x M'))"
  using assms
  by (metis One_nat_def Suc_1 Suc_leD add_le_cancel_left count_add_mset numeral_3_eq_3 plus_1_eq_Suc
      two_le_countE)

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

lemma Uniq_antimono: "Q \<le> P \<Longrightarrow> Uniq Q \<ge> Uniq P"
  unfolding le_fun_def le_bool_def
  by (rule impI) (simp only: Uniq_I Uniq_D)

lemma Uniq_antimono': "(\<And>x. Q x \<Longrightarrow> P x) \<Longrightarrow> Uniq P \<Longrightarrow> Uniq Q"
  by (fact Uniq_antimono[unfolded le_fun_def le_bool_def, rule_format])

lemma multp_singleton_right[simp]:
  assumes "transp R"
  shows "multp R M {#x#} \<longleftrightarrow> (\<forall>y \<in># M. R y x)"
proof (rule iffI)
  show "\<forall>y \<in># M. R y x \<Longrightarrow> multp R M {#x#}"
    using one_step_implies_multp[of "{#x#}" _ R "{#}", simplified] .
next
  show "multp R M {#x#} \<Longrightarrow> \<forall>y\<in>#M. R y x"
    using multp_implies_one_step[OF \<open>transp R\<close>]
    by (smt (verit, del_insts) add_0 set_mset_add_mset_insert set_mset_empty single_is_union
        singletonD)
qed

lemma multp_singleton_left[simp]:
  assumes "transp R"
  shows "multp R {#x#} M \<longleftrightarrow> ({#x#} \<subset># M \<or> (\<exists>y \<in># M. R x y))"
proof (rule iffI)
  show "{#x#} \<subset># M \<or> (\<exists>y\<in>#M. R x y) \<Longrightarrow> multp R {#x#} M"
  proof (elim disjE bexE)
    show "{#x#} \<subset># M \<Longrightarrow> multp R {#x#} M"
      by (simp add: subset_implies_multp)
  next
    show "\<And>y. y \<in># M \<Longrightarrow> R x y \<Longrightarrow> multp R {#x#} M"
      using one_step_implies_multp[of M "{#x#}" R "{#}", simplified] by force
  qed
next
  show "multp R {#x#} M \<Longrightarrow> {#x#} \<subset># M \<or> (\<exists>y\<in>#M. R x y)"
    using multp_implies_one_step[OF \<open>transp R\<close>, of "{#x#}" M]
    by (metis (no_types, opaque_lifting) add_cancel_right_left subset_mset.gr_zeroI
        subset_mset.less_add_same_cancel2 union_commute union_is_single union_single_eq_member)
qed

lemma multp_singleton_singleton[simp]: "transp R \<Longrightarrow> multp R {#x#} {#y#} \<longleftrightarrow> R x y"
  using multp_singleton_right[of R "{#x#}" y] by simp

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

lemma multp_doubleton_doubleton[simp]:
  "transp R \<Longrightarrow> asymp R \<Longrightarrow> multp R {#x, x#} {#y, y#} \<longleftrightarrow> R x y"
  using multp_double_double[of R "{#x#}" "{#y#}", simplified] by simp

lemma multp_single_doubleI: "M \<noteq> {#} \<Longrightarrow> multp R M (M + M)"
  using one_step_implies_multp[of M "{#}" _ M, simplified] by simp

lemma mult1_implies_one_step_strong:
  assumes "trans r" and "asym r" and "(A, B) \<in> mult1 r"
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

lemma asymp_multp:
  assumes "asymp R" and "transp R"
  shows "asymp (multp R)"
  using asymp_multp\<^sub>H\<^sub>O[OF assms]
  unfolding multp_eq_multp\<^sub>H\<^sub>O[OF assms].

lemma multp_doubleton_singleton: "transp R \<Longrightarrow> multp R {# x, x #} {# y #} \<longleftrightarrow> R x y"
  by (cases "x = y") auto

lemma image_mset_remove1_mset: 
  assumes "inj f"  
  shows "remove1_mset (f a) (image_mset f X) = image_mset f (remove1_mset a X)"
  using image_mset_remove1_mset_if
  unfolding image_mset_remove1_mset_if inj_image_mem_iff[OF assms, symmetric]
  by simp

end