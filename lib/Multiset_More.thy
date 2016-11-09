(*  Title:       More about Multisets
    Author:      Mathias Fleury <mathias.fleury at mpi-inf.mpg.de>, 2015
    Author:      Jasmin Blanchette <blanchette at in.tum.de>, 2014, 2015
    Author:      Dmitriy Traytel <traytel at in.tum.de>, 2014
    Maintainer:  Mathias Fleury <mathias.fleury at mpi-inf.mpg.de>
*)

theory Multiset_More
imports "~~/src/HOL/Library/Multiset_Order"
begin

section \<open>More about Multisets\<close>

text \<open>
Isabelle's theory of finite multisets is not as developed as other areas, such as lists and sets.
The present theory introduces some missing concepts and lemmas. Some of it is expected to move to
Isabelle's library.
\<close>


subsection \<open>Basic Setup\<close>

declare
  diff_single_trivial [simp]
  in_image_mset [iff]
  image_mset.compositionality [simp]

  (*To have the same rules as the set counter-part*)
  mset_subset_eqD[dest, intro?] (*@{thm subsetD}*)

  Multiset.in_multiset_in_set[simp]
  inter_add_left1[simp]
  inter_add_left2[simp]
  inter_add_right1[simp]
  inter_add_right2[simp]

  sum_mset_sum_list[simp]


subsection \<open>Lemma about the multiset order\<close>

lemma all_lt_Max_imp_lt_multiset: "N \<noteq> {#} \<Longrightarrow> (\<forall>a \<in># M. a < Max (set_mset N)) \<Longrightarrow> M < N"
  by (meson Max_in[OF finite_set_mset] ex_gt_imp_less_multiset set_mset_eq_empty_iff)

lemma lt_imp_ex_count_lt: "M < N \<Longrightarrow> \<exists>y. count M y < count N y"
  by (meson less_eq_multiset\<^sub>H\<^sub>O less_le_not_le)

lemma subset_imp_less_multiset:
  fixes A
  assumes a_sub_b: "A \<subset># B"
  shows "A < B"
proof -
  have a_subeq_b: "A \<subseteq># B"
    using a_sub_b by (rule subset_mset.less_imp_le)
  hence "A \<le> B"
    by (rule subset_eq_imp_le_multiset)
  moreover have "A \<noteq> B"
    using a_sub_b by simp
  ultimately show "A < B"
    by (rule order_neq_le_trans[rotated 1])
qed

lemma image_mset_mono:
  assumes
    mono_f: "\<forall>x \<in> set_mset M. \<forall>y \<in> set_mset N. x < y \<longrightarrow> f x < f y" and
    less: "M < N"
  shows "image_mset f M < image_mset f N"
proof -
  obtain Y X where
    y_nemp: "Y \<noteq> {#}" and y_sub_N: "Y \<subseteq># N" and M_eq: "M = N - Y + X" and
    ex_y: "\<forall>x. x \<in># X \<longrightarrow> (\<exists>y. y \<in># Y \<and> x < y)"
    using less[unfolded less_multiset\<^sub>D\<^sub>M] by blast

  have x_sub_M: "X \<subseteq># M"
    using M_eq by simp

  let ?fY = "image_mset f Y"
  let ?fX = "image_mset f X"

  show ?thesis
    unfolding less_multiset\<^sub>D\<^sub>M
  proof (intro exI conjI)
    show "image_mset f M = image_mset f N - ?fY + ?fX"
      using M_eq[THEN arg_cong, of "image_mset f"] y_sub_N
      by (metis image_mset_Diff image_mset_union)
  next
    obtain y where y: "\<forall>x. x \<in># X \<longrightarrow> y x \<in># Y \<and> x < y x"
      using ex_y by moura

    show "\<forall>fx. fx \<in># ?fX \<longrightarrow> (\<exists>fy. fy \<in># ?fY \<and> fx < fy)"
    proof (intro allI impI)
      fix fx
      assume "fx \<in># ?fX"
      then obtain x where fx: "fx = f x" and x_in: "x \<in># X"
        by auto
      hence y_in: "y x \<in># Y" and y_gt: "x < y x"
        using y[rule_format, OF x_in] by blast+
      hence "f (y x) \<in># ?fY \<and> f x < f (y x)"
        using mono_f y_sub_N x_sub_M x_in
        by (metis image_eqI in_image_mset mset_subset_eqD)
      thus "\<exists>fy. fy \<in># ?fY \<and> fx < fy"
        unfolding fx by auto
    qed
  qed (auto simp: y_nemp y_sub_N image_mset_subseteq_mono)
qed


subsection \<open>Lemmas about intersections, unions and point-wise inclusion\<close>

lemma mset_inter_single: "x \<in># \<Sigma> \<Longrightarrow> \<Sigma> \<inter># {#x#} = {#x#}"
  by simp

lemma subset_add_mset_notin_subset_mset: \<open>A \<subseteq># add_mset b B \<Longrightarrow> b \<notin># A  \<Longrightarrow> A \<subseteq># B\<close>
  by (simp add: subset_mset.sup.absorb_iff2)

text \<open>@{thm [source] psubsetE} is the set counterpart\<close>

lemma subset_msetE [elim!]:
  "\<lbrakk>A \<subset># B; \<lbrakk>A \<subseteq># B; ~ (B\<subseteq>#A)\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  unfolding subseteq_mset_def subset_mset_def by (meson mset_subset_eqI subset_mset.eq_iff)

lemma Diff_triv_mset: "M \<inter># N = {#} \<Longrightarrow> M - N = M"
  by (metis diff_intersect_left_idem diff_zero)

lemma diff_intersect_sym_diff: "(A - B) \<inter># (B - A) = {#}"
  unfolding multiset_inter_def
proof -
  have "A - (B - (B - A)) = A - B"
    by (metis (full_types) diff_intersect_right_idem multiset_inter_def)
  then show "A - B - (A - B - (B - A)) = {#}"
    by (metis add_diff_cancel_right' cancel_ab_semigroup_add_class.diff_right_commute
      cancel_comm_monoid_add_class.diff_cancel diff_subset_eq_self diff_zero subset_mset.diff_add
      subset_mset.diff_diff_right)
qed


subsection \<open>Lemmas about size\<close>

text \<open>
This sections adds various lemmas about size. Most lemmas have a finite set equivalent.
\<close>
lemma size_mset_SucE: "size A = Suc n \<Longrightarrow> (\<And>a B. A = {#a#} + B \<Longrightarrow> size B = n \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases A) (auto simp add: ac_simps)

lemma size_Suc_Diff1: "x \<in># \<Sigma> \<Longrightarrow> Suc (size (\<Sigma> - {#x#})) = size \<Sigma>"
  using arg_cong[OF insert_DiffM, of _ _ size] by simp

lemma size_Diff_singleton: "x \<in># \<Sigma> \<Longrightarrow> size (\<Sigma> - {#x#}) = size \<Sigma> - 1"
  by (simp add: size_Suc_Diff1 [symmetric])

lemma size_Diff_singleton_if: "size (A - {#x#}) = (if x \<in># A then size A - 1 else size A)"
  by (simp add: size_Diff_singleton)

lemma size_Un_Int: "size A + size B = size (A \<union># B) + size (A \<inter># B)"
proof -
  have *: "A + B = B + (A - B + (A - (A - B)))"
    by (simp add: subset_mset.add_diff_inverse union_commute)
  have "size B + size (A - B) = size A + size (B - A)"
    unfolding size_union[symmetric] sup_subset_mset_def[symmetric]
    by (subst subset_mset.sup_commute) (rule refl)
  then show ?thesis unfolding multiset_inter_def size_union[symmetric] "*"
    by (simp add: sup_subset_mset_def del: subset_mset.add_diff_assoc)
qed

lemma size_Un_disjoint:
  assumes "A \<inter># B = {#}"
  shows "size (A \<union># B) = size A + size B"
  using assms size_Un_Int [of A B] by simp

lemma size_Diff_subset_Int:
  shows "size (\<Sigma> - \<Sigma>') = size \<Sigma> - size (\<Sigma> \<inter># \<Sigma>')"
proof -
  have *: "\<Sigma> - \<Sigma>' = \<Sigma> - \<Sigma> \<inter># \<Sigma>'" by (auto simp add: multiset_eq_iff)
  show ?thesis unfolding * using size_Diff_submset subset_mset.inf.cobounded1 by blast
qed

lemma diff_size_le_size_Diff: "size (\<Sigma>:: _ multiset) - size \<Sigma>' \<le> size (\<Sigma> - \<Sigma>')"
proof-
  have "size \<Sigma> - size \<Sigma>' \<le> size \<Sigma> - size (\<Sigma> \<inter># \<Sigma>')"
    using size_mset_mono diff_le_mono2 subset_mset.inf_le2 by metis
  also have "\<dots> = size(\<Sigma>-\<Sigma>')" by(simp add: size_Diff_subset_Int)
  finally show ?thesis .
qed

lemma size_Diff1_less: "x\<in># \<Sigma> \<Longrightarrow> size (\<Sigma> - {#x#}) < size \<Sigma>"
  by (rule Suc_less_SucD) (simp add: size_Suc_Diff1)

lemma size_Diff2_less: "x\<in># \<Sigma> \<Longrightarrow> y\<in># \<Sigma> \<Longrightarrow> size (\<Sigma> - {#x#} - {#y#}) < size \<Sigma>"
  by (metis less_imp_diff_less size_Diff1_less size_Diff_subset_Int)

lemma size_Diff1_le: "size (\<Sigma> - {#x#}) \<le> size \<Sigma>"
  by (cases "x \<in># \<Sigma>") (simp_all add: size_Diff1_less less_imp_le)

lemma size_psubset: "(\<Sigma>:: _ multiset) \<subseteq># \<Sigma>' \<Longrightarrow> size \<Sigma> < size \<Sigma>' \<Longrightarrow> \<Sigma> \<subset># \<Sigma>'"
  using less_irrefl subset_mset_def by blast


subsection \<open>Filter and Image\<close>

lemma count_image_mset_ge_count:
  "count (image_mset f A) (f b) \<ge> count A b"
  by (induction A) auto

lemma count_image_mset_inj:
  assumes \<open>inj f\<close>
  shows  \<open>count (image_mset f M) (f x) = count M x\<close>
  by (induction M) (use assms in \<open>auto simp: inj_on_def\<close>)

lemma mset_filter_compl: "mset (filter p xs) + mset (filter (Not \<circ> p) xs) = mset xs"
  by (induction xs) (auto simp: mset_filter ac_simps)

lemma comprehension_mset_False[simp]: "{# L \<in># A. False#} = {#}"
  by (auto simp: multiset_eq_iff)

text \<open>Near duplicate of @{thm [source] filter_eq_replicate_mset}: @{thm filter_eq_replicate_mset}.\<close>

lemma filter_mset_eq: "filter_mset (op = L) A = replicate_mset (count A L) L"
  by (auto simp: multiset_eq_iff)

text \<open>See @{thm [source] filter_cong} for the set version. Mark as \<open>[fundef_cong]\<close> too?\<close>

lemma filter_mset_cong:
  assumes [simp]: "M = M'" and [simp]: "\<And>a. a \<in># M \<Longrightarrow> P a = Q a"
  shows "filter_mset P M = filter_mset Q M"
proof -
  have "M - filter_mset Q M = filter_mset (\<lambda>a. \<not>Q a) M"
    by (subst multiset_partition[of _ Q]) simp
  then show ?thesis
    by (auto simp: filter_mset_eq_conv)
qed

lemma filter_mset_filter_mset: "filter_mset Q (filter_mset P M) = {#x \<in># M. P x \<and> Q x#}"
  by (auto simp: multiset_eq_iff)

lemma image_mset_const: "{#c. x \<in># M#} = replicate_mset (size M) c"
  by (induction M) auto

lemma image_mset_filter_swap: "image_mset f {# x \<in># M. P (f x)#} = {# x \<in># image_mset f M. P x#}"
  by (induction M) auto

lemma image_mset_cong2[cong]:
  "(\<And>x. x \<in># M \<Longrightarrow> f x = g x) \<Longrightarrow> M = N \<Longrightarrow> image_mset f M = image_mset g N"
  by (hypsubst, rule image_mset_cong)

lemma filter_mset_empty_conv: \<open>(filter_mset P M = {#}) = (\<forall>L\<in>#M. \<not> P L)\<close>
  by (induction M) auto

lemma multiset_filter_mono2: \<open>filter_mset P A \<subseteq># filter_mset Q A \<longleftrightarrow>
  (\<forall>a\<in>#A. P a \<longrightarrow> Q a)\<close>
  by (induction A) (auto intro: subset_mset.order.trans)

lemma image_filter_cong:
  assumes \<open>\<And>C. C \<in># M \<Longrightarrow> P C \<Longrightarrow> f C = g C\<close>
  shows
    \<open>{#f C. C \<in># {#C \<in># M. P C#}#} = {#g C|C\<in># M. P C#}\<close>
  using assms by (induction M) auto

lemma image_mset_filter_swap2: \<open>{#C \<in># {#P x. x \<in># D#}. Q C #} = {#P x. x \<in># {#C| C \<in># D. Q (P C)#}#}\<close>
  by (simp add: image_mset_filter_swap)


subsection \<open>Sums\<close>

lemma count_sum_mset_if_1_0: \<open>count M a = (\<Sum>x\<in>#M. if x = a then 1 else 0)\<close>
  by (induction M) auto


subsection \<open>Remove\<close>

lemma set_mset_minus_replicate_mset[simp]:
  "n \<ge> count A a \<Longrightarrow> set_mset (A - replicate_mset n a) = set_mset A - {a}"
  "n < count A a \<Longrightarrow> set_mset (A - replicate_mset n a) = set_mset A"
  unfolding set_mset_def by (auto split: if_split simp: not_in_iff)

abbreviation removeAll_mset :: "'a \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset" where
"removeAll_mset C M \<equiv> M - replicate_mset (count M C) C"

lemma mset_removeAll[simp, code]:
  "removeAll_mset C (mset L) = mset (removeAll C L)"
  by (induction L) (auto simp: ac_simps multiset_eq_iff split: if_split_asm)

lemma removeAll_mset_filter_mset:
  "removeAll_mset C M = filter_mset (op \<noteq> C) M"
  by (induction M) (auto simp: ac_simps multiset_eq_iff)

abbreviation remove1_mset :: "'a \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset" where
  "remove1_mset C M \<equiv> M - {#C#}"

lemma in_remove1_mset_neq:
  assumes ab: "a \<noteq> b"
  shows "a \<in># remove1_mset b C \<longleftrightarrow> a \<in># C"
proof -
  have "count {#b#} a = 0"
    using ab by simp
  then show ?thesis
    by (metis (no_types) count_diff diff_zero mem_Collect_eq set_mset_def)
qed

lemma size_mset_removeAll_mset_le_iff:
  "size (removeAll_mset x M) < size M \<longleftrightarrow> x \<in># M"
  apply (rule iffI)
    apply (force intro: count_inI)
  apply (rule mset_subset_size)
  apply (auto simp: subset_mset_def multiset_eq_iff)
  done

lemma size_remove1_mset_If: \<open>size (remove1_mset x M) = size M - (if x \<in># M then 1 else 0)\<close>
  by (auto simp: size_Diff_subset_Int mset_inter_single)

lemma size_mset_remove1_mset_le_iff:
  "size (remove1_mset x M) < size M \<longleftrightarrow> x \<in># M"
  apply (rule iffI)
    using less_irrefl apply fastforce
  apply (rule mset_subset_size)
  by (auto elim: in_countE simp: subset_mset_def multiset_eq_iff)

lemma single_remove1_mset_eq:
  "add_mset a (remove1_mset a M) = M \<longleftrightarrow> a \<in># M"
  by (cases "count M a") (auto simp: multiset_eq_iff count_eq_zero_iff count_inI)

lemma remove_1_mset_id_iff_notin:
  "remove1_mset a M = M \<longleftrightarrow> a \<notin># M"
  by (meson diff_single_trivial multi_drop_mem_not_eq)

lemma id_remove_1_mset_iff_notin:
  "M = remove1_mset a M \<longleftrightarrow> a \<notin># M"
  using remove_1_mset_id_iff_notin by metis

lemma remove1_mset_eqE:
  "remove1_mset L x1 = M \<Longrightarrow>
    (L \<in># x1 \<Longrightarrow> x1 = M + {#L#} \<Longrightarrow> P) \<Longrightarrow>
    (L \<notin># x1 \<Longrightarrow> x1 = M \<Longrightarrow> P) \<Longrightarrow>
  P"
  by (cases "L \<in># x1") auto

lemma image_filter_ne_mset[simp]:
  "image_mset f {#x \<in># M. f x \<noteq> y#} = removeAll_mset y (image_mset f M)"
  by (induction M) simp_all

lemma image_mset_remove1_mset_if:
  "image_mset f (remove1_mset a M) =
   (if a \<in># M then remove1_mset (f a) (image_mset f M) else image_mset f M)"
  by (auto simp: image_mset_Diff)

lemma filter_mset_neq: "{#x \<in># M. x \<noteq> y#} = removeAll_mset y M"
  by (metis add_diff_cancel_left' filter_eq_replicate_mset multiset_partition)

lemma filter_mset_neq_cond: "{#x \<in># M. P x \<and> x \<noteq> y#} = removeAll_mset y {# x\<in>#M. P x#}"
  by (metis add_diff_cancel_left' filter_eq_replicate_mset filter_mset_filter_mset
    multiset_partition)

lemma remove1_mset_add_mset_If:
  "remove1_mset L (add_mset L' C) = (if L = L' then C else remove1_mset L C + {#L'#})"
  by (auto simp: multiset_eq_iff)

lemma minus_remove1_mset_if:
  "A - remove1_mset b B = (if b \<in># B \<and> b \<in># A \<and> count A b \<ge> count B b then {#b#} + (A - B) else A - B)"
  by (auto simp: multiset_eq_iff count_greater_zero_iff[symmetric]
  simp del: count_greater_zero_iff)

lemma add_mset_eq_add_mset_ne:
  "a \<noteq> b \<Longrightarrow> add_mset a A = add_mset b B \<longleftrightarrow> a \<in># B \<and> b \<in># A \<and> A = add_mset b (B - {#a#})"
  by (metis (no_types, lifting) diff_single_eq_union diff_union_swap multi_self_add_other_not_self
      remove_1_mset_id_iff_notin union_single_eq_diff)

text \<open>This lemma allows to split equality like \<^term>\<open>{#K, K'#} = {#L, L'#}\<close> into
  \<^term>\<open>(K = L \<and> L = L') \<or> (K \<noteq> L \<and> K = L' \<and> K' = L)\<close>. It can lead to a explosion of the
  numbers of cases.\<close>
lemma add_mset_eq_add_mset: \<open>add_mset a M = add_mset b M' \<longleftrightarrow>
  (a = b \<and> M = M') \<or> (a \<noteq> b \<and> b \<in># M \<and> add_mset a (M - {#b#}) = M')\<close>
  by (metis add_mset_eq_add_mset_ne add_mset_remove_trivial union_single_eq_member)

(* TODO move to Multiset: could replace add_mset_remove_trivial_eq? *)
lemma add_mset_remove_trivial_iff: \<open>N = add_mset a (N - {#b#}) \<longleftrightarrow> a \<in># N \<and> a = b\<close>
  by (metis add_left_cancel add_mset_remove_trivial insert_DiffM2 single_eq_single
      size_mset_remove1_mset_le_iff union_single_eq_member)

lemma trivial_add_mset_remove_iff: \<open>add_mset a (N - {#b#}) = N \<longleftrightarrow> a \<in># N \<and> a = b\<close>
  by (subst eq_commute) (fact add_mset_remove_trivial_iff)

lemma remove1_single_empty_iff[simp]: \<open>remove1_mset L {#L'#} = {#} \<longleftrightarrow> L = L'\<close>
  using add_mset_remove_trivial_iff by fastforce


subsection \<open>Replicate\<close>

lemma replicate_mset_minus_replicate_mset_same[simp]:
  "replicate_mset m x - replicate_mset n x = replicate_mset (m - n) x"
proof (induct m arbitrary: n, simp_all)
  fix ma :: nat and na :: nat
  assume a1: "\<And>n. replicate_mset ma x - replicate_mset n x = replicate_mset (ma - n) x"
  have f2: "\<And>n a. 0 < n \<Longrightarrow> add_mset a (replicate_mset (n - Suc 0) a) = replicate_mset n a"
    by (metis (full_types) Suc_pred replicate_mset_Suc)
  have "replicate_mset (Suc ma) x = add_mset x (replicate_mset ma x)"
    by auto
  then show "add_mset x (replicate_mset ma x) - replicate_mset na x = replicate_mset (Suc ma - na) x"
    using f2 a1 by (metis (no_types) Suc_pred add_mset_diff_bothsides
      cancel_comm_monoid_add_class.diff_cancel diff_Suc_Suc diff_zero neq0_conv)
qed

lemma replicate_mset_subset_iff_lt[simp]: "replicate_mset m x \<subset># replicate_mset n x \<longleftrightarrow> m < n"
  by (induct n m rule: diff_induct) (auto intro: subset_mset.gr_zeroI)

lemma replicate_mset_subseteq_iff_le[simp]: "replicate_mset m x \<subseteq># replicate_mset n x \<longleftrightarrow> m \<le> n"
  by (induct n m rule: diff_induct) auto

lemma replicate_mset_lt_iff_lt[simp]: "replicate_mset m x < replicate_mset n x \<longleftrightarrow> m < n"
  by (induct n m rule: diff_induct) (auto intro: subset_mset.gr_zeroI gr_zeroI)

lemma replicate_mset_le_iff_le[simp]: "replicate_mset m x \<le> replicate_mset n x \<longleftrightarrow> m \<le> n"
  by (induct n m rule: diff_induct) auto

lemma replicate_mset_eq_iff[simp]:
  "replicate_mset m x = replicate_mset n y \<longleftrightarrow> m = n \<and> (m \<noteq> 0 \<longrightarrow> x = y)"
  by (cases m; cases n; simp)
    (metis in_replicate_mset insert_noteq_member size_replicate_mset union_single_eq_diff)

lemma replicate_mset_plus: "replicate_mset (a + b) C = replicate_mset a C + replicate_mset b C"
  by (induct a) (auto simp: ac_simps)

lemma mset_replicate_replicate_mset: "mset (replicate n L) = replicate_mset n L"
  by (induction n) auto

lemma set_mset_single_iff_replicate_mset:
  "set_mset U = {a} \<longleftrightarrow> (\<exists>n > 0. U = replicate_mset n a)" (is "?S \<longleftrightarrow> ?R")
proof
  assume ?S
  show ?R
  proof (rule ccontr)
    assume "\<not> ?R"
    have "\<forall>n. U \<noteq> replicate_mset n a"
      using \<open>?S\<close> \<open>\<not> ?R\<close> by (metis gr_zeroI insert_not_empty set_mset_replicate_mset_subset)
    then obtain b where "b \<in># U" and "b \<noteq> a"
      by (metis count_replicate_mset mem_Collect_eq multiset_eqI neq0_conv set_mset_def)
    then show False
      using \<open>?S\<close> by auto
  qed
qed auto

lemma ex_replicate_mset_if_all_elems_eq:
  assumes "\<forall>x \<in># M. x = y"
  shows "\<exists>n. M = replicate_mset n y"
  using assms by (metis count_replicate_mset mem_Collect_eq multiset_eqI neq0_conv set_mset_def)


subsection \<open>Multiset and set conversion\<close>

lemma count_mset_set_if: "count (mset_set A) a = (if a \<in> A \<and> finite A then 1 else 0)"
  by auto

lemma mset_set_set_mset_empty_mempty[iff]: "mset_set (set_mset D) = {#} \<longleftrightarrow> D = {#}"
  by (auto dest: arg_cong[of _ _ set_mset])

lemma count_mset_set_le_one: "count (mset_set A) x \<le> 1"
  by (simp add: count_mset_set_if)

lemma mset_set_subseteq_mset_set[iff]:
  assumes "finite A" "finite B"
  shows "mset_set A \<subseteq># mset_set B \<longleftrightarrow> A \<subseteq> B"
  by (metis assms contra_subsetD count_mset_set(1,3) count_mset_set_le_one finite_set_mset_mset_set
    less_eq_nat.simps(1) mset_subset_eqI set_mset_mono)

lemma mset_set_set_mset_subseteq[simp]: "mset_set (set_mset A) \<subseteq># A"
  by (simp add: subseteq_mset_def count_mset_set_if)

lemma mset_sorted_list_of_set[simp]: "mset (sorted_list_of_set A) = mset_set A"
  by (metis mset_sorted_list_of_multiset sorted_list_of_mset_set)

lemma mset_take_subseteq: "mset (take n xs) \<subseteq># mset xs"
  apply (induct xs arbitrary: n)
   apply simp
  by (case_tac n) simp_all


subsection \<open>Removing duplicates\<close>

definition remdups_mset :: "'v multiset \<Rightarrow> 'v multiset" where
  "remdups_mset S = mset_set (set_mset S)"

lemma set_mset_remdups_mset[simp]: \<open>set_mset (remdups_mset A) = set_mset A\<close>
  unfolding remdups_mset_def by auto

lemma count_remdups_mset_eq_1: "a \<in># remdups_mset A \<longleftrightarrow> count (remdups_mset A) a = 1"
  unfolding remdups_mset_def by (auto simp: count_eq_zero_iff intro: count_inI)

lemma remdups_mset_empty[simp]: "remdups_mset {#} = {#}"
  unfolding remdups_mset_def by auto

lemma remdups_mset_singleton[simp]: "remdups_mset {#a#} = {#a#}"
  unfolding remdups_mset_def by auto

lemma remdups_mset_eq_empty[iff]: "remdups_mset D = {#} \<longleftrightarrow> D = {#}"
  unfolding remdups_mset_def by blast

lemma remdups_mset_singleton_sum[simp]:
  "remdups_mset (add_mset a A) = (if a \<in># A then remdups_mset A else add_mset a (remdups_mset A))"
  unfolding remdups_mset_def by (simp_all add: insert_absorb)

lemma mset_remdups_remdups_mset[simp]: "mset (remdups D) = remdups_mset (mset D)"
  by (induction D) (auto simp add: ac_simps)

declare mset_remdups_remdups_mset[symmetric, code]

definition distinct_mset :: "'a multiset \<Rightarrow> bool" where
  "distinct_mset S \<longleftrightarrow> (\<forall>a. a \<in># S \<longrightarrow> count S a = 1)"

text \<open>Another characterisation of @{term distinct_mset}:\<close>
lemma distinct_mset_count_less_1: "distinct_mset S \<longleftrightarrow> (\<forall>a. count S a \<le> 1)"
  using eq_iff nat_le_linear unfolding distinct_mset_def by fastforce

lemma distinct_mset_empty[simp]: "distinct_mset {#}"
  unfolding distinct_mset_def by auto

lemma distinct_mset_singleton: "distinct_mset {#a#}"
  unfolding distinct_mset_def by auto

lemma distinct_mset_union:
  assumes dist: "distinct_mset (A + B)"
  shows "distinct_mset A"
  unfolding distinct_mset_count_less_1
proof (rule allI)
  fix a
  have \<open>count A a \<le> count (A + B) a\<close> by auto
  moreover have \<open>count (A + B) a \<le> 1\<close>
    using dist unfolding distinct_mset_count_less_1 by auto
  ultimately show \<open>count A a \<le> 1\<close>
    by simp
qed

lemma distinct_mset_minus[simp]:
  "distinct_mset A \<Longrightarrow> distinct_mset (A - B)"
  by (metis diff_subset_eq_self mset_subset_eq_exists_conv distinct_mset_union)

lemma count_remdups_mset_If: \<open>count (remdups_mset A) a = (if a \<in># A then 1 else 0)\<close>
  unfolding remdups_mset_def by auto

lemma distinct_mset_rempdups_union_mset:
  assumes "distinct_mset A" and "distinct_mset B"
  shows "A \<union># B = remdups_mset (A + B)"
  using assms nat_le_linear unfolding remdups_mset_def
  by (force simp add: multiset_eq_iff max_def count_mset_set_if distinct_mset_def not_in_iff)

lemma distinct_mset_add_mset[simp]: "distinct_mset (add_mset a L) \<longleftrightarrow> a \<notin># L \<and> distinct_mset L"
  unfolding distinct_mset_def
  apply (rule iffI)
   apply (auto split: if_split_asm; fail)[]
  by (auto simp: not_in_iff; fail)

lemma distinct_mset_size_eq_card: "distinct_mset C \<Longrightarrow> size C = card (set_mset C)"
  by (induction C) auto

lemma distinct_mset_add:
  "distinct_mset (L + L') \<longleftrightarrow> distinct_mset L \<and> distinct_mset L' \<and> L \<inter># L' = {#}" (is "?A \<longleftrightarrow> ?B")
  by (induction L arbitrary: L') auto

lemma distinct_mset_set_mset_ident[simp]: "distinct_mset M \<Longrightarrow> mset_set (set_mset M) = M"
  by (induction M) auto

lemma distinct_finite_set_mset_subseteq_iff[iff]:
  assumes dist: "distinct_mset M" and fin: "finite N"
  shows "set_mset M \<subseteq> N \<longleftrightarrow> M \<subseteq># mset_set N"
proof
  assume "set_mset M \<subseteq> N"
  then show "M \<subseteq># mset_set N"
    by (metis dist distinct_mset_set_mset_ident fin finite_subset mset_set_subseteq_mset_set)
next
  assume "M \<subseteq># mset_set N"
  then show "set_mset M \<subseteq> N"
    by (metis contra_subsetD empty_iff finite_set_mset_mset_set infinite_set_mset_mset_set
      set_mset_mono subsetI)
qed

lemma distinct_mem_diff_mset:
  assumes dist: "distinct_mset M" and mem: "x \<in> set_mset (M - N)"
  shows "x \<notin> set_mset N"
proof -
  have "count M x = 1"
    using dist mem by (meson distinct_mset_def in_diffD)
  then show ?thesis
    using mem by (metis count_greater_eq_one_iff in_diff_count not_less)
qed

lemma distinct_set_mset_eq:
  assumes
    dist_m: "distinct_mset M" and
    dist_n: "distinct_mset N" and
    set_eq: "set_mset M = set_mset N"
  shows "M = N"
proof -
  have "mset_set (set_mset M) = mset_set (set_mset N)"
    using set_eq by simp
  thus ?thesis
    using dist_m dist_n by auto
qed

lemma distinct_mset_union_mset[simp]:
  \<open>distinct_mset (D \<union># C) \<longleftrightarrow> distinct_mset D \<and> distinct_mset C\<close>
  unfolding distinct_mset_count_less_1 by force

lemma distinct_mset_inter_mset:
  assumes
    "distinct_mset D" and
    "distinct_mset C"
  shows "distinct_mset (D \<inter># C)"
  using assms unfolding distinct_mset_count_less_1
  by (meson dual_order.trans subset_mset.inf_le2 subseteq_mset_def)

lemma distinct_mset_remove1_All: "distinct_mset C \<Longrightarrow> remove1_mset L C = removeAll_mset L C"
  by (auto simp: multiset_eq_iff distinct_mset_count_less_1)

lemma distinct_mset_size_2: "distinct_mset {#a, b#} \<longleftrightarrow> a \<noteq> b"
  by auto

lemma distinct_mset_filter: "distinct_mset M \<Longrightarrow> distinct_mset {# L \<in># M. P L#}"
  by (simp add: distinct_mset_def)

lemma distinct_mset_mset_distinct[simp]: \<open>distinct_mset (mset xs) = distinct xs\<close>
  by (induction xs) auto

lemma distinct_image_mset_inj:
  \<open>inj_on f (set_mset M) \<Longrightarrow> distinct_mset (image_mset f M) \<longleftrightarrow> distinct_mset M\<close>
  by (induction M) (auto simp: inj_on_def)


section \<open>Repeat\<close>

lemma repeat_mset_compower: "repeat_mset n A = ((op + A) ^^ n) {#}"
  by (induction n) auto

lemma repeat_mset_prod: "repeat_mset (m * n) A = ((op + (repeat_mset n A)) ^^ m) {#}"
  by (induction m) (auto simp: repeat_mset_distrib)


section \<open>Cartesian Product\<close>

text \<open>Definition of the cartesian products over multisets. The construction mimics of the cartesian
  product on sets and use the same theorem names (adding only the suffix @{text "_mset"} to Sigma
  and Times). See file @{file "~~/src/HOL/Product_Type.thy"}\<close>

definition Sigma_mset :: "'a multiset \<Rightarrow> ('a \<Rightarrow> 'b multiset) \<Rightarrow> ('a \<times> 'b) multiset" where
  "Sigma_mset A B \<equiv> \<Union># {#{#(a, b). b \<in># B a#}. a \<in># A #}"

abbreviation Times_mset :: "'a multiset \<Rightarrow> 'b multiset \<Rightarrow> ('a \<times> 'b) multiset" (infixr "\<times>mset" 80) where
  "Times_mset A B \<equiv> Sigma_mset A (\<lambda>_. B)"

hide_const (open) Times_mset

text \<open>Contrary to the set version @{term \<open>SIGMA x:A. B\<close>}, we use the non-ASCII symbol \<open>\<in>#\<close>.\<close>

syntax
  "_Sigma_mset" :: "[pttrn, 'a multiset, 'b multiset] => ('a * 'b) multiset"
  ("(3SIGMAMSET _\<in>#_./ _)" [0, 0, 10] 10)
translations
  "SIGMAMSET x\<in>#A. B" == "CONST Sigma_mset A (\<lambda>x. B)"

text \<open>Link between the multiset and the set cartesian product:\<close>

lemma Times_mset_Times: "set_mset (A \<times>mset B) = set_mset A \<times> set_mset B"
  unfolding Sigma_mset_def by auto

lemma Sigma_msetI [intro!]: "\<lbrakk>a \<in># A; b \<in># B a\<rbrakk> \<Longrightarrow> (a, b) \<in># Sigma_mset A B"
  by (unfold Sigma_mset_def) auto

lemma Sigma_msetE [elim!]:
    "\<lbrakk> c\<in># Sigma_mset A B;
        \<And>x y.\<lbrakk> x\<in>#A;  y\<in>#B(x);  c=(x,y) \<rbrakk> \<Longrightarrow> P
     \<rbrakk> \<Longrightarrow> P"
  \<comment> \<open>The general elimination rule.\<close>
  by (unfold Sigma_mset_def) auto

text \<open>Elimination of @{term "(a, b) \<in># A \<times>mset B"} -- introduces no eigenvariables.\<close>

lemma Sigma_msetD1: "(a, b) \<in># Sigma_mset A B \<Longrightarrow> a \<in># A"
  by blast

lemma Sigma_msetD2: "(a, b) \<in># Sigma_mset A B \<Longrightarrow> b \<in># B a"
  by blast

lemma Sigma_msetE2:
    "\<lbrakk> (a, b) \<in># Sigma_mset A B;
        \<lbrakk> a\<in>#A;  b\<in>#B(a) \<rbrakk> \<Longrightarrow> P
     \<rbrakk> \<Longrightarrow> P"
  by blast

lemma Sigma_mset_cong:
     "\<lbrakk>A = B; \<And>x. x \<in># B \<Longrightarrow> C x = D x\<rbrakk>
      \<Longrightarrow> (SIGMAMSET x\<in>#A. C x) = (SIGMAMSET x\<in># B. D x)"
  by (metis (mono_tags, lifting) Sigma_mset_def image_mset_cong)

lemma count_sum_mset: "count (\<Union>#M) b = (\<Sum>P\<in>#M. count P b)"
  by (induction M) auto

lemma Sigma_mset_plus_distrib1[simp]: "Sigma_mset (A + B) C = Sigma_mset A C + Sigma_mset B C"
  unfolding Sigma_mset_def by auto

lemma Sigma_mset_plus_distrib2[simp]:
  "Sigma_mset A (\<lambda>i. B i + C i) = Sigma_mset A B + Sigma_mset A C"
  unfolding Sigma_mset_def by (induction A) (auto simp: multiset_eq_iff)

lemma Times_mset_single_left: "{#a#} \<times>mset B = image_mset (Pair a) B"
  unfolding Sigma_mset_def by auto

lemma Times_mset_single_right: "A \<times>mset {#b#} = image_mset (\<lambda>a. Pair a b) A"
  unfolding Sigma_mset_def by (induction A) auto

lemma Times_mset_single_single[simp]: "{#a#} \<times>mset {#b#} = {#(a, b)#}"
  unfolding Sigma_mset_def by simp

context
begin

text \<open>Technical lemma, but not important enough to be part of the exported lemmas:\<close>
lemma count_image_mset_Pair:
  "count (image_mset (Pair a) B) (x, b) = (if x = a then count B b else 0)"
  by (induction B) auto

lemma count_Sigma_mset: "count (Sigma_mset A B) (a, b) = count A a * count (B a) b"
  by (induction A) (auto simp: Sigma_mset_def count_image_mset_Pair)

lemma Sigma_mset_empty1 [simp]: "Sigma_mset {#} B = {#}"
  unfolding Sigma_mset_def by auto

lemma Sigma_mset_empty2 [simp]: "A \<times>mset {#} = {#}"
  by (auto simp: multiset_eq_iff count_Sigma_mset)

lemma Sigma_mset_mono:
  assumes "A \<subseteq># C" and "\<And>x. x\<in>#A \<Longrightarrow> B x \<subseteq># D x"
  shows "Sigma_mset A B \<subseteq># Sigma_mset C D"
proof -
  have "count A a * count (B a) b \<le> count C a * count (D a) b" for a b
    using assms unfolding subseteq_mset_def by (metis count_inI eq_iff mult_eq_0_iff mult_le_mono)
  then show ?thesis
    by (auto simp: subseteq_mset_def count_Sigma_mset)
qed

lemma mem_Sigma_mset_iff[iff]: "((a,b) \<in># Sigma_mset A B) = (a \<in># A \<and> b \<in># B a)"
  by blast

lemma mem_Times_mset_iff: "x \<in># A \<times>mset B \<longleftrightarrow> fst x \<in># A \<and> snd x \<in># B"
  by (induct x) simp

lemma Sigma_mset_empty_iff: "(SIGMAMSET i\<in>#I. X i) = {#} \<longleftrightarrow> (\<forall>i\<in>#I. X i = {#})"
  by (auto simp: Sigma_mset_def)

lemma Times_mset_subset_mset_cancel1: "x \<in># A \<Longrightarrow> (A \<times>mset B \<subseteq># A \<times>mset C) = (B \<subseteq># C)"
  by (auto simp: subseteq_mset_def count_Sigma_mset)

lemma Times_mset_subset_mset_cancel2: "x \<in># C \<Longrightarrow> (A \<times>mset C \<subseteq># B \<times>mset C) = (A \<subseteq># B)"
  by (auto simp: subseteq_mset_def count_Sigma_mset)

lemma Times_mset_eq_cancel2: "x\<in>#C \<Longrightarrow> (A \<times>mset C = B \<times>mset C) = (A = B)"
  by (auto simp: multiset_eq_iff count_Sigma_mset dest!: in_countE)

lemma split_paired_Ball_mset_Sigma_mset [simp, no_atp]:
  "(\<forall>z\<in>#Sigma_mset A B. P z) \<longleftrightarrow> (\<forall>x\<in>#A. \<forall>y\<in>#B x. P (x, y))"
  by blast

lemma split_paired_Bex_mset_Sigma_mset [simp, no_atp]:
  "(\<exists>z\<in>#Sigma_mset A B. P z) \<longleftrightarrow> (\<exists>x\<in>#A. \<exists>y\<in>#B x. P (x, y))"
  by blast

lemma sum_mset_if_eq_constant:
  "(\<Sum>x\<in>#M. if a = x then (f x) else 0) = ((op + (f a)) ^^ (count M a)) 0"
  by (induction M) (auto simp: ac_simps)

private lemma iterate_op_plus: "((op + k) ^^ m) 0 = k * m"
  by (induction m) auto

lemma untion_image_mset_Pair_distribute:
  "\<Union>#{#image_mset (Pair x) (C x). x \<in># J - I#} = \<Union>#{#image_mset (Pair x) (C x). x \<in># J#} -
    \<Union>#{#image_mset (Pair x) (C x). x \<in># I#}"
  by (auto simp: multiset_eq_iff count_sum_mset count_image_mset_Pair sum_mset_if_eq_constant
    iterate_op_plus diff_mult_distrib2)

lemma Sigma_mset_Un_distrib1: "Sigma_mset (I \<union># J) C = Sigma_mset I C \<union># Sigma_mset J C"
  by (auto simp: Sigma_mset_def sup_subset_mset_def untion_image_mset_Pair_distribute)

lemma Sigma_mset_Un_distrib2: "(SIGMAMSET i\<in>#I. A i \<union># B i) = Sigma_mset I A \<union># Sigma_mset I B"
  by (auto simp: multiset_eq_iff count_sum_mset count_image_mset_Pair sum_mset_if_eq_constant
    Sigma_mset_def diff_mult_distrib2 iterate_op_plus max_def not_in_iff)

lemma Sigma_mset_Int_distrib1: "Sigma_mset (I \<inter># J) C = Sigma_mset I C \<inter># Sigma_mset J C"
  by (auto simp: multiset_eq_iff count_sum_mset count_image_mset_Pair sum_mset_if_eq_constant
    Sigma_mset_def iterate_op_plus min_def not_in_iff)

lemma Sigma_mset_Int_distrib2: "(SIGMAMSET i\<in>#I. A i \<inter># B i) = Sigma_mset I A \<inter># Sigma_mset I B"
  by (auto simp: multiset_eq_iff count_sum_mset count_image_mset_Pair sum_mset_if_eq_constant
    Sigma_mset_def iterate_op_plus min_def not_in_iff)

lemma Sigma_mset_Diff_distrib1: "Sigma_mset (I - J) C = Sigma_mset I C - Sigma_mset J C"
  by (auto simp: multiset_eq_iff count_sum_mset count_image_mset_Pair sum_mset_if_eq_constant
    Sigma_mset_def iterate_op_plus min_def not_in_iff diff_mult_distrib2)

lemma Sigma_mset_Diff_distrib2: "(SIGMAMSET i\<in>#I. A i - B i) = Sigma_mset I A - Sigma_mset I B"
  by (auto simp: multiset_eq_iff count_sum_mset count_image_mset_Pair sum_mset_if_eq_constant
    Sigma_mset_def iterate_op_plus min_def not_in_iff diff_mult_distrib)

lemma Sigma_mset_Union: "Sigma_mset (\<Union>#X) B = (\<Union># (image_mset (\<lambda>A. Sigma_mset A B) X))"
  by (auto simp: multiset_eq_iff count_sum_mset count_image_mset_Pair sum_mset_if_eq_constant
    Sigma_mset_def iterate_op_plus min_def not_in_iff sum_mset_distrib_left)

end

lemma Times_mset_Un_distrib1: "(A \<union># B) \<times>mset C = A \<times>mset C \<union># B \<times>mset C "
  by (fact Sigma_mset_Un_distrib1)

lemma Times_mset_Int_distrib1: "(A \<inter># B) \<times>mset C = A \<times>mset C \<inter># B \<times>mset C "
  by (fact Sigma_mset_Int_distrib1)

lemma Times_mset_Diff_distrib1: "(A - B) \<times>mset C = A \<times>mset C - B \<times>mset C "
  by (fact Sigma_mset_Diff_distrib1)

lemma Times_mset_empty[simp]: "A \<times>mset B = {#} \<longleftrightarrow> A = {#} \<or> B = {#}"
  by (auto simp: Sigma_mset_empty_iff)

lemma Times_insert_left: "A \<times>mset add_mset x B = A \<times>mset B + image_mset (\<lambda>a. Pair a x) A"
  unfolding add_mset_add_single[of x B] Sigma_mset_plus_distrib2
  by (simp add: Times_mset_single_right)

lemma Times_insert_right: "add_mset a A \<times>mset B = A \<times>mset B + image_mset (Pair a) B"
  unfolding add_mset_add_single[of a A] Sigma_mset_plus_distrib1
  by (simp add: Times_mset_single_left)

lemma fst_image_mset_times_mset [simp]:
  "image_mset fst (A \<times>mset B) = (if B = {#} then {#} else repeat_mset (size B) A)"
  by (induction B) (auto simp: Times_mset_single_right ac_simps Times_insert_left)

lemma snd_image_mset_times_mset [simp]:
  "image_mset snd (A \<times>mset B) = (if A = {#} then {#} else repeat_mset (size A) B)"
  by (induction B) (auto simp add: Times_mset_single_right image_mset_const Times_insert_left)

lemma product_swap_mset:
  "image_mset prod.swap (A \<times>mset B) = B \<times>mset A"
  by (induction A) (auto simp add: Times_mset_single_left Times_mset_single_right
      Times_insert_right Times_insert_left)

context
begin

qualified definition product_mset :: "'a multiset \<Rightarrow> 'b multiset \<Rightarrow> ('a \<times> 'b) multiset" where
  [code_abbrev]: "product_mset A B = A \<times>mset B"

lemma member_product_mset: "x \<in># Multiset_More.product_mset A B \<longleftrightarrow> x \<in># A \<times>mset B"
  by (simp add: Multiset_More.product_mset_def)

end

lemma count_Sigma_mset_abs_def: "count (Sigma_mset A B) = (\<lambda>(a, b) \<Rightarrow> count A a * count (B a) b)"
  by (auto simp: fun_eq_iff count_Sigma_mset)

lemma Times_mset_image_mset1: "image_mset f A \<times>mset B = image_mset (\<lambda>(a, b). (f a, b)) (A \<times>mset B)"
  by (induct B) (auto simp: Times_insert_left)

lemma Times_mset_image_mset2: "A \<times>mset image_mset f B = image_mset (\<lambda>(a, b). (a, f b)) (A \<times>mset B)"
  by (induct A) (auto simp: Times_insert_right)

lemma sum_le_singleton: "A \<subseteq> {x} \<Longrightarrow> sum f A = (if x \<in> A then f x else 0)"
  by (auto simp: subset_singleton_iff elim: finite_subset)

lemma Times_mset_assoc:
  "(A \<times>mset B) \<times>mset C = image_mset (\<lambda>(a, b, c). ((a, b), c)) (A \<times>mset B \<times>mset C)"
  by (auto simp: multiset_eq_iff count_Sigma_mset count_image_mset vimage_def Times_mset_Times
    Int_commute count_eq_zero_iff
    intro!: trans[OF _ sym[OF sum_le_singleton[of _ "(_, _, _)"]]]
    cong: sum.cong if_cong)


subsection \<open>Transfer rules\<close>

lemma plus_multiset_transfer[transfer_rule]:
  "(rel_fun (rel_mset R) (rel_fun (rel_mset R) (rel_mset R))) (op +) (op +)"
  by (unfold rel_fun_def rel_mset_def)
    (force dest: list_all2_appendI intro: exI[of _ "_ @ _"] conjI[rotated])

lemma minus_multiset_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique R"
  shows "(rel_fun (rel_mset R) (rel_fun (rel_mset R) (rel_mset R))) (op -) (op -)"
proof (unfold rel_fun_def rel_mset_def, safe)
  fix xs ys xs' ys'
  assume [transfer_rule]: "list_all2 R xs ys" "list_all2 R xs' ys'"
  have "list_all2 R (fold remove1 xs' xs) (fold remove1 ys' ys)"
    by transfer_prover
  moreover
  have "mset (fold remove1 xs' xs) = mset xs - mset xs'"
    by (induct xs' arbitrary: xs) auto
  moreover
  have "mset (fold remove1 ys' ys) = mset ys - mset ys'"
    by (induct ys' arbitrary: ys) auto
  ultimately show "\<exists>xs'' ys''.
    mset xs'' = mset xs - mset xs' \<and> mset ys'' = mset ys - mset ys' \<and> list_all2 R xs'' ys''"
    by blast
qed

declare rel_mset_Zero[transfer_rule]

lemma count_transfer[transfer_rule]:
  assumes "bi_unique R"
  shows "(rel_fun (rel_mset R) (rel_fun R op =)) count count"
unfolding rel_fun_def rel_mset_def proof safe
  fix x y xs ys
  assume "list_all2 R xs ys" "R x y"
  then show "count (mset xs) x = count (mset ys) y"
  proof (induct xs ys rule: list.rel_induct)
    case (Cons x' xs y' ys)
    then show ?case using assms unfolding bi_unique_alt_def2
      by (auto simp: rel_fun_def)
  qed simp
qed

lemma subseteq_multiset_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique R" "right_total R"
  shows "(rel_fun (rel_mset R) (rel_fun (rel_mset R) (op =)))
    (\<lambda>M N. filter_mset (Domainp R) M \<subseteq># filter_mset (Domainp R) N) (op \<subseteq>#)"
proof -
  have count_filter_mset_less:
    "(\<forall>a. count (filter_mset (Domainp R) M) a \<le> count (filter_mset (Domainp R) N) a) \<longleftrightarrow>
     (\<forall>a \<in> {x . Domainp R x}. count M a \<le> count N a)" for M and N by auto
  show ?thesis unfolding subseteq_mset_def count_filter_mset_less
    by transfer_prover
qed

lemma sum_mset_transfer[transfer_rule]: "R 0 0 \<Longrightarrow> rel_fun R (rel_fun R R) op + op + \<Longrightarrow>
  (rel_fun (rel_mset R) R) sum_mset sum_mset"
  using sum_list_transfer[of R] unfolding rel_fun_def rel_mset_def by auto

lemma Sigma_mset_transfer[transfer_rule]:
  "(rel_fun (rel_mset R) (rel_fun (rel_fun R (rel_mset S)) (rel_mset (rel_prod R S))))
     Sigma_mset Sigma_mset"
  by (unfold Sigma_mset_def) transfer_prover

end
