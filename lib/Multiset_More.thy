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

lemma image_mset_cong2[cong]:
  "(\<And>x. x \<in># M \<Longrightarrow> f x = g x) \<Longrightarrow> M = N \<Longrightarrow> image_mset f M = image_mset g N"
  by (hypsubst, rule image_mset_cong)

(*@{thm psubsetE} is the set counter part*)
lemma subset_msetE [elim!]:
  "[|A \<subset># B; [|A \<subseteq># B; ~ (B\<subseteq>#A)|] ==> R|] ==> R"
  unfolding subseteq_mset_def subset_mset_def by (meson mset_subset_eqI subset_mset.eq_iff)


subsection \<open>Lemmas about intersections and unions\<close>

lemma mset_inter_single:
  "x \<in># \<Sigma> \<Longrightarrow> \<Sigma> #\<inter> {#x#} = {#x#}"
  "x \<notin># \<Sigma> \<Longrightarrow> \<Sigma> #\<inter> {#x#} = {#}"
    apply (simp add: mset_subset_eq_single subset_mset.inf_absorb2)
  by (simp add: multiset_inter_def)

lemma inter_mset_empty_distrib_right: \<open>A #\<inter> (B + C) = {#} \<longleftrightarrow> A #\<inter> B = {#} \<and> A #\<inter> C = {#}\<close>
  by (meson disjunct_not_in union_iff)

lemma inter_mset_empty_distrib_left: \<open>(A + B) #\<inter> C = {#} \<longleftrightarrow> A #\<inter> C = {#} \<and> B #\<inter> C = {#}\<close>
  by (meson disjunct_not_in union_iff)

lemma
  shows
    inter_mset_single_right_empty[iff]: \<open>L #\<inter> {#x#} = {#} \<longleftrightarrow> x \<notin># L\<close> and
    inter_mset_single_left_empty[iff]: \<open>{#x#} #\<inter> L = {#} \<longleftrightarrow> x \<notin># L\<close>
    by (auto simp: disjunct_not_in)

lemma sup_subset_mset_empty_iff[iff]: "A #\<union> B = {#} \<longleftrightarrow> A = {#} \<and> B = {#}"
  by (auto simp: sup_subset_mset_def)

text \<open>TODO mark as [iff]?\<close>
lemma union_mset_mempty_iff: "\<Union># M = {#} \<longleftrightarrow> (\<forall>i\<in>#M. i = {#})"
  by (induction M) auto

lemma minus_eq_empty_iff_include: "A - B = {#} \<longleftrightarrow> A \<subseteq># B"
  by (auto simp: multiset_eq_iff subseteq_mset_def)


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

lemma size_Un_Int: "size A + size B = size (A #\<union> B) + size (A #\<inter> B)"
proof -
  have *: "A + B = B + (A - B + (A - (A - B)))"
    by (simp add: subset_mset.add_diff_inverse union_commute)
  have "size B + size (A - B) = size A + size (B - A)"
    unfolding size_union[symmetric] subset_mset.sup_commute sup_subset_mset_def[symmetric]
    by blast
  then show ?thesis unfolding multiset_inter_def size_union[symmetric] "*"
    by (auto simp add: sup_subset_mset_def)
qed

lemma size_Un_disjoint:
  assumes "A #\<inter> B = {#}"
  shows "size (A #\<union> B) = size A + size B"
  using assms size_Un_Int [of A B] by simp

lemma size_Diff_subset_Int:
  shows "size (\<Sigma> - \<Sigma>') = size \<Sigma> - size (\<Sigma> #\<inter> \<Sigma>')"
proof -
  have *: "\<Sigma> - \<Sigma>' = \<Sigma> - \<Sigma> #\<inter> \<Sigma>'" by (auto simp add: multiset_eq_iff)
  show ?thesis unfolding * using size_Diff_submset subset_mset.inf.cobounded1 by blast
qed

lemma diff_size_le_size_Diff: "size (\<Sigma>:: _ multiset) - size \<Sigma>' \<le> size (\<Sigma> - \<Sigma>')"
proof-
  have "size \<Sigma> - size \<Sigma>' \<le> size \<Sigma> - size (\<Sigma> #\<inter> \<Sigma>')"
    using size_mset_mono diff_le_mono2 subset_mset.inf_le2 by blast
  also have "\<dots> = size(\<Sigma>-\<Sigma>')" by(simp add: size_Diff_subset_Int)
  finally show ?thesis .
qed

lemma size_Diff1_less: "x\<in># \<Sigma> \<Longrightarrow> size (\<Sigma> - {#x#}) < size \<Sigma>"
  by (rule Suc_less_SucD) (simp add: size_Suc_Diff1)

lemma size_Diff2_less: "x\<in># \<Sigma> \<Longrightarrow> y\<in># \<Sigma> \<Longrightarrow> size (\<Sigma> - {#x#} - {#y#}) < size \<Sigma>"
  using nonempty_has_size by (fastforce intro!: diff_Suc_less simp add: size_Diff1_less
    size_Diff_subset_Int mset_inter_single)

lemma size_Diff1_le: "size (\<Sigma> - {#x#}) \<le> size \<Sigma>"
  by (cases "x \<in># \<Sigma>") (simp_all add: size_Diff1_less less_imp_le)

lemma size_psubset: "(\<Sigma>:: _ multiset) \<le># \<Sigma>' \<Longrightarrow> size \<Sigma> < size \<Sigma>' \<Longrightarrow> \<Sigma> <# \<Sigma>'"
  using less_irrefl subset_mset_def by blast


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

lemma remove1_mset_remove1[code]:
  "remove1_mset C (mset L) = mset (remove1 C L)"
  by auto

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

lemma size_mset_remove1_mset_le_iff:
  "size (remove1_mset x M) < size M \<longleftrightarrow> x \<in># M"
  apply (rule iffI)
    using less_irrefl apply fastforce
  apply (rule mset_subset_size)
  by (auto elim: in_countE simp: subset_mset_def multiset_eq_iff)

lemma set_mset_remove1_mset[simp]:
  "set_mset (remove1_mset L (mset W)) = set (remove1 L W)"
  by (metis mset_remove1 set_mset_mset)

lemma single_remove1_mset_eq:
  "{#a#} + remove1_mset a M = M \<longleftrightarrow> a \<in># M"
  by (cases "count M a") (auto simp: multiset_eq_iff count_eq_zero_iff count_inI)

lemma remove_1_mset_id_iff_notin:
  "remove1_mset a M = M \<longleftrightarrow> a \<notin># M"
  by (meson diff_single_trivial multi_drop_mem_not_eq)


subsection \<open>Replicate\<close>

lemma replicate_mset_plus: "replicate_mset (a + b) C = replicate_mset a C + replicate_mset b C"
  by (induct a) (auto simp: ac_simps)

lemma mset_replicate_replicate_mset:
  "mset (replicate n L) = replicate_mset n L"
  by (induction n) auto

lemma set_mset_single_iff_replicate_mset:
  "set_mset U = {a} \<longleftrightarrow> (\<exists>n>0. U = replicate_mset n a)" (is "?S \<longleftrightarrow> ?R")
proof
  assume ?R
  then show ?S by auto
next
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
qed


subsection \<open>Multiset and set conversion\<close>

lemma count_mset_set_if:
  "count (mset_set A) a = (if a \<in> A \<and> finite A then 1 else 0)"
  by auto

lemma mset_set_set_mset_empty_mempty[iff]:
  "mset_set (set_mset D) = {#} \<longleftrightarrow> D = {#}"
  by (auto dest: arg_cong[of _ _ set_mset])

lemma count_mset_set_le_one: "count (mset_set A) x \<le> 1"
  by (metis count_mset_set(1) count_mset_set(2) count_mset_set(3) eq_iff le_numeral_extra(1))

lemma mset_set_subseteq_mset_set[iff]:
  assumes "finite A" "finite B"
  shows "mset_set A \<subseteq># mset_set B \<longleftrightarrow> A \<subseteq> B"
  by (metis assms contra_subsetD count_mset_set(1,3) count_mset_set_le_one finite_set_mset_mset_set
    less_eq_nat.simps(1) mset_subset_eqI set_mset_mono)

lemma mset_set_set_mset_subseteq[simp]: "mset_set (set_mset A) \<subseteq># A"
  by (metis count_mset_set(1,3) finite_set_mset less_eq_nat.simps(1) less_one
    mem_Collect_eq mset_subset_eqI not_less set_mset_def)

lemma mset_sorted_list_of_set[simp]:
  "mset (sorted_list_of_set A) = mset_set A"
  by (metis mset_sorted_list_of_multiset sorted_list_of_mset_set)

lemma mset_take_subseteq: "mset (take n xs) \<subseteq># mset xs"
  apply (induct xs arbitrary: n)
   apply simp
  by (case_tac n) simp_all


subsection \<open>Removing duplicates\<close>

definition remdups_mset :: "'v multiset \<Rightarrow> 'v multiset" where
  "remdups_mset S = mset_set (set_mset S)"

lemma remdups_mset_in[iff]: "a \<in># remdups_mset A \<longleftrightarrow> a \<in># A"
  unfolding remdups_mset_def by auto

lemma count_remdups_mset_eq_1: "a \<in># remdups_mset A \<longleftrightarrow> count (remdups_mset A) a = 1"
  unfolding remdups_mset_def by (auto simp: count_eq_zero_iff intro: count_inI)

lemma remdups_mset_empty[simp]: "remdups_mset {#} = {#}"
  unfolding remdups_mset_def by auto

lemma remdups_mset_singleton[simp]: "remdups_mset {#a#} = {#a#}"
  unfolding remdups_mset_def by auto

lemma set_mset_remdups[simp]: "set_mset (remdups_mset C) = set_mset C"
  by auto

lemma remdups_mset_eq_empty[iff]: "remdups_mset D = {#} \<longleftrightarrow> D = {#}"
  unfolding remdups_mset_def by blast

lemma remdups_mset_singleton_sum[simp]:
  "remdups_mset ({#a#} + A) = (if a \<in># A then remdups_mset A else {#a#} + remdups_mset A)"
  "remdups_mset (A + {#a#}) = (if a \<in># A then remdups_mset A else {#a#} + remdups_mset A)"
  unfolding remdups_mset_def by (simp_all add: insert_absorb)

lemma mset_remdups_remdups_mset[simp]: "mset (remdups D) = remdups_mset (mset D)"
  by (induction D) (auto simp add: ac_simps)

definition distinct_mset :: "'a multiset \<Rightarrow> bool" where
  "distinct_mset S \<longleftrightarrow> (\<forall>a. a \<in># S \<longrightarrow> count S a = 1)"

lemma distinct_mset_empty[simp]: "distinct_mset {#}"
  unfolding distinct_mset_def by auto

lemma distinct_mset_singleton[simp]: "distinct_mset {#a#}"
  unfolding distinct_mset_def by auto

definition distinct_mset_set :: "'a multiset set \<Rightarrow> bool" where
  "distinct_mset_set \<Sigma> \<longleftrightarrow> (\<forall>S \<in> \<Sigma>. distinct_mset S)"

lemma distinct_mset_set_empty[simp]: "distinct_mset_set {}"
  unfolding distinct_mset_set_def by auto

lemma distinct_mset_set_singleton[iff]: "distinct_mset_set {A} \<longleftrightarrow> distinct_mset A"
  unfolding distinct_mset_set_def by auto

lemma distinct_mset_set_insert[iff]:
  "distinct_mset_set (insert S \<Sigma>) \<longleftrightarrow> (distinct_mset S \<and> distinct_mset_set \<Sigma>)"
  unfolding distinct_mset_set_def by auto

lemma distinct_mset_set_union[iff]:
  "distinct_mset_set (\<Sigma> \<union> \<Sigma>') \<longleftrightarrow> (distinct_mset_set \<Sigma> \<and> distinct_mset_set \<Sigma>')"
  unfolding distinct_mset_set_def by auto

lemma distinct_mset_union:
  assumes dist: "distinct_mset (A + B)"
  shows "distinct_mset A"
proof -
  obtain aa :: "'a multiset \<Rightarrow> 'a" where
    f2: "\<forall>m. \<not> distinct_mset m \<or> (\<forall>a. (a::'a) \<notin># m \<or> count m a = 1)"
      "\<forall>m. aa m \<in># m \<and> count m (aa m) \<noteq> 1 \<or> distinct_mset m"
    by (metis (full_types) distinct_mset_def)
  then have "count (A + B) (aa A) = 1 \<or> distinct_mset A"
    using dist by (meson mset_subset_eqD mset_subset_eq_add_left)
  then show ?thesis
    using f2 by (metis (no_types) One_nat_def add_is_1 count_union mem_Collect_eq order_less_irrefl
      set_mset_def)
qed

lemma distinct_mset_minus[simp]:
  "distinct_mset A \<Longrightarrow> distinct_mset (A - B)"
  by (metis diff_subset_eq_self mset_subset_eq_exists_conv distinct_mset_union)

lemma in_distinct_mset_set_distinct_mset:
  "a \<in> \<Sigma> \<Longrightarrow> distinct_mset_set \<Sigma> \<Longrightarrow> distinct_mset a"
  unfolding distinct_mset_set_def by auto

lemma distinct_mset_remdups_mset[simp]: "distinct_mset (remdups_mset S)"
  using count_remdups_mset_eq_1 unfolding distinct_mset_def by metis

lemma distinct_mset_distinct[simp]: "distinct_mset (mset x) = distinct x"
  unfolding distinct_mset_def by (auto simp: distinct_count_atmost_1 not_in_iff[symmetric])

lemma distinct_mset_mset_set: "distinct_mset (mset_set A)"
  unfolding distinct_mset_def count_mset_set_if by (auto simp: not_in_iff)

lemma distinct_mset_rempdups_union_mset:
  assumes "distinct_mset A" and "distinct_mset B"
  shows "A #\<union> B = remdups_mset (A + B)"
  using assms nat_le_linear unfolding remdups_mset_def
  by (force simp add: multiset_eq_iff max_def count_mset_set_if distinct_mset_def not_in_iff)

lemma distinct_mset_set_distinct: "distinct_mset_set (mset ` set Cs) \<longleftrightarrow> (\<forall>c\<in> set Cs. distinct c)"
  unfolding distinct_mset_set_def by auto

lemma distinct_mset_add_single: "distinct_mset ({#a#} + L) \<longleftrightarrow> distinct_mset L \<and> a \<notin># L"
  unfolding distinct_mset_def
  apply (rule iffI)
    prefer 2 apply (auto simp: not_in_iff)[]
  apply standard
    apply (intro allI)
    apply (rename_tac aa, case_tac "a = aa")
    by (auto split: if_split_asm)

lemma distinct_mset_single_add: "distinct_mset (L + {#a#}) \<longleftrightarrow> distinct_mset L \<and> a \<notin># L"
  unfolding add.commute[of L "{#a#}"] distinct_mset_add_single by fast

lemma distinct_mset_size_eq_card: "distinct_mset C \<Longrightarrow> size C = card (set_mset C)"
  by (induction C) (auto simp: distinct_mset_single_add)

text \<open>Another characterisation of @{term distinct_mset}:\<close>

lemma distinct_mset_count_less_1: "distinct_mset S \<longleftrightarrow> (\<forall>a. count S a \<le> 1)"
  using eq_iff nat_le_linear unfolding distinct_mset_def by fastforce

lemma distinct_mset_add:
  "distinct_mset (L + L') \<longleftrightarrow> distinct_mset L \<and> distinct_mset L' \<and> L #\<inter> L' = {#}" (is "?A \<longleftrightarrow> ?B")
  by (induction L arbitrary: L')
   (auto simp add: ac_simps distinct_mset_single_add inter_mset_empty_distrib_right)

lemma distinct_mset_set_mset_ident[simp]: "distinct_mset M \<Longrightarrow> mset_set (set_mset M) = M"
  by (induction M) (auto simp: distinct_mset_add ac_simps)

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

lemma distinct_mset_union_mset:
  assumes
    "distinct_mset D" and
    "distinct_mset C"
  shows "distinct_mset (D #\<union> C)"
  using assms unfolding distinct_mset_count_less_1 by force

lemma distinct_mset_inter_mset:
  assumes
    "distinct_mset D" and
    "distinct_mset C"
  shows "distinct_mset (D #\<inter> C)"
  using assms unfolding distinct_mset_count_less_1
  by (meson dual_order.trans subset_mset.inf_le2 subseteq_mset_def)

lemma distinct_mset_remove1_All: "distinct_mset C \<Longrightarrow> remove1_mset L C = removeAll_mset L C"
  by (auto simp: multiset_eq_iff distinct_mset_count_less_1)

lemma distinct_mset_size_2: "distinct_mset {#a, b#} \<longleftrightarrow> a \<noteq> b"
  unfolding distinct_mset_def by auto

lemma distinct_mset_filter: "distinct_mset M \<Longrightarrow> distinct_mset {# L \<in># M. P L#}"
  by (simp add: distinct_mset_def)


subsection \<open>Filter\<close>

lemma mset_filter_compl: "mset (filter p xs) + mset (filter (Not \<circ> p) xs) = mset xs"
  apply (induct xs)
  by simp
    (metis (no_types) add_diff_cancel_left' comp_apply filter.simps(2) mset.simps(2)
       mset_compl_union)

lemma image_mset_subseteq_mono: "A \<subseteq># B \<Longrightarrow> image_mset f A \<subseteq># image_mset f B"
  by (metis image_mset_union subset_mset.le_iff_add)

lemma image_filter_ne_mset[simp]:
  "image_mset f {#x \<in># M. f x \<noteq> y#} = removeAll_mset y (image_mset f M)"
  by (induct M, auto, meson count_le_replicate_mset_subset_eq order_refl subset_mset.add_diff_assoc2)

lemma comprehension_mset_False[simp]: "{# L \<in># A. False#} = {#}"
  by (auto simp: multiset_eq_iff)

text \<open>Near duplicate of @{thm [source] filter_eq_replicate_mset}: @{thm filter_eq_replicate_mset}.\<close>

lemma filter_mset_eq: "filter_mset (op = L) A = replicate_mset (count A L) L"
  by (auto simp: multiset_eq_iff)

lemma filter_mset_union_mset: "filter_mset P (A #\<union> B) = filter_mset P A #\<union> filter_mset P B"
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

lemma image_mset_remove1_mset_if:
  "image_mset f (remove1_mset a M) =
   (if a \<in># M then remove1_mset (f a) (image_mset f M) else image_mset f M)"
  by (auto simp: image_mset_Diff)

lemma image_mset_const: "{#c. x \<in># M#} = replicate_mset (size M) c"
  by (induction M) auto

lemma image_mset_mset_mset_map: "image_mset f (mset l) = mset (map f l)"
  by (induction l) auto

lemma filter_mset_neq: "{#x \<in># M. x \<noteq> y#} = removeAll_mset y M"
  by (metis add_diff_cancel_left' filter_eq_replicate_mset multiset_partition)

lemma filter_mset_neq_cond: "{#x \<in># M. P x \<and> x \<noteq> y#} = removeAll_mset y {# x\<in>#M. P x#}"
  by (metis add_diff_cancel_left' filter_eq_replicate_mset filter_mset_filter_mset
    multiset_partition)

lemma image_mset_filter_swap: "image_mset f {# x \<in># M. P (f x)#} = {# x \<in># image_mset f M. P x#}"
  by (induction M) auto


subsection \<open>Sums\<close>

lemma msetsum_distrib[simp]:
  fixes C D :: "'a \<Rightarrow> 'b::{comm_monoid_add}"
  shows "(\<Sum>x \<in># A. C x + D x) = (\<Sum>x \<in># A. C x) + (\<Sum>x \<in># A. D x)"
  by (induction A) (auto simp: ac_simps)

lemma msetsum_union_disjoint:
  assumes "A #\<inter> B = {#}"
  shows "(\<Sum>La\<in>#A #\<union> B. f La) = (\<Sum>La\<in>#A. f La) + (\<Sum>La\<in>#B. f La)"
  by (metis assms diff_zero empty_sup image_mset_union msetsum.union multiset_inter_commute
    multiset_union_diff_commute sup_subset_mset_def zero_diff)


section \<open>Cartesian Product\<close>

text \<open>Definition of the cartesian products over multisets. The construction mimics of the cartesian
  product on sets and use the same theorem names (adding only the suffix @{text "_mset"} to Sigma
  and Times). See file @{file "~~/src/HOL/Product_Type.thy"}\<close>

definition Sigma_mset :: "'a multiset \<Rightarrow> ('a \<Rightarrow> 'b multiset) \<Rightarrow> ('a \<times> 'b) multiset" where
  "Sigma_mset A B \<equiv> \<Union># {#{#(a, b). b \<in># B a#}. a \<in># A #}"

abbreviation Times_mset :: "'a multiset \<Rightarrow> 'b multiset \<Rightarrow> ('a \<times> 'b) multiset" (infixr "\<times>mset" 80) where
  "Times_mset A B \<equiv> Sigma_mset A (\<lambda>_. B)"

hide_const (open) Times_mset

syntax
  "_Sigma_mset" :: "[pttrn, 'a multiset, 'b multiset] => ('a * 'b) multiset"  ("(3SIGMAMSET _\<in>#_./ _)" [0, 0, 10] 10)
translations (* TODO why does \<in># not work? *)
  "SIGMAMSET x\<in>#A. B" == "CONST Sigma_mset A (%x. B)"

text \<open>Link between the multiset and the set cartesian product:\<close>

lemma Times_mset_Times: "set_mset (A \<times>mset B) = set_mset A \<times> set_mset B"
  unfolding Sigma_mset_def by auto

lemma Sigma_msetI [intro!]: "[| a\<in>#A;  b\<in>#B(a) |] ==> (a,b) \<in># Sigma_mset A B"
  by (unfold Sigma_mset_def) auto

lemma Sigma_msetE [elim!]:
    "[| c\<in># Sigma_mset A B;
        \<And>x y.[| x\<in>#A;  y\<in>#B(x);  c=(x,y) |] ==> P
     |] ==> P"
  \<comment> \<open>The general elimination rule.\<close>
  by (unfold Sigma_mset_def) auto

text \<open>
  Elimination of @{term "(a, b) \<in># A \<times>mset B"} -- introduces no
  eigenvariables.
\<close>

lemma Sigma_msetD1: "(a, b) \<in># Sigma_mset A B ==> a \<in># A"
  by blast

lemma Sigma_msetD2: "(a, b) \<in># Sigma_mset A B ==> b \<in># B a"
  by blast

lemma Sigma_msetE2:
    "[| (a, b) \<in># Sigma_mset A B;
        [| a\<in>#A;  b\<in>#B(a) |] ==> P
     |] ==> P"
  by blast

lemma Sigma_mset_cong:
     "\<lbrakk>A = B; \<And>x. x \<in># B \<Longrightarrow> C x = D x\<rbrakk>
      \<Longrightarrow> (SIGMAMSET x\<in>#A. C x) = (SIGMAMSET x\<in># B. D x)"
  by (metis (mono_tags, lifting) Sigma_mset_def image_mset_cong)

lemma count_msetsum: "count (\<Union>#M) b = (\<Sum>P\<in>#M. count P b)"
  by (induction M) auto

lemma count_image_mset_Pair:
  "count (image_mset (Pair a) B) (x, b) = (if x = a then count B b else 0)"
  by (induction B) auto

lemma count_Sigma_mset: "count (Sigma_mset A B) (a, b) = count A a * count (B a) b"
  by (induction A) (auto simp: Sigma_mset_def count_image_mset_Pair)

lemma Sigma_mset_plus_distrib1[simp]: "Sigma_mset (A + B) C = Sigma_mset A C + Sigma_mset B C"
  unfolding Sigma_mset_def by auto

lemma Sigma_mset_plus_distrib2[simp]:
  "Sigma_mset A (\<lambda>i. B i + C i) = Sigma_mset A B + Sigma_mset A C"
  unfolding Sigma_mset_def by (induction A) (auto simp: multiset_eq_iff)

lemma Times_mset_single_left: "{#a#} \<times>mset B = image_mset (Pair a) B"
  unfolding Sigma_mset_def by auto

lemma Times_mset_single_right: "A \<times>mset {#b#} = image_mset (\<lambda>a. Pair a b) A"
  unfolding Sigma_mset_def by (induction A) auto

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
  by (auto simp: Sigma_mset_def union_mset_mempty_iff)

lemma Times_mset_subset_mset_cancel2: "x \<in># C \<Longrightarrow> (A \<times>mset C \<subseteq># B \<times>mset C) = (A \<subseteq># B)"
  by (auto simp: subseteq_mset_def count_Sigma_mset)

lemma Times_mset_eq_cancel2: "x\<in>#C ==> (A \<times>mset C = B \<times>mset C) = (A = B)"
  by (auto simp: multiset_eq_iff count_Sigma_mset dest!: in_countE)

lemma split_paired_Ball_mset_Sigma_mset [simp, no_atp]:
  "(\<forall>z\<in>#Sigma_mset A B. P z) \<longleftrightarrow> (\<forall>x\<in>#A. \<forall>y\<in>#B x. P (x, y))"
  by blast

lemma split_paired_Bex_mset_Sigma_mset [simp, no_atp]:
  "(\<exists>z\<in>#Sigma_mset A B. P z) \<longleftrightarrow> (\<exists>x\<in>#A. \<exists>y\<in>#B x. P (x, y))"
  by blast

lemma minus_remove1_mset_if:
  "A - remove1_mset b B = (if b \<in># B \<and> b \<in># A \<and> count A b \<ge> count B b then {#b#} + (A - B) else A - B)"
  by (auto simp: multiset_eq_iff count_greater_zero_iff[symmetric]
  simp del: count_greater_zero_iff)

lemma image_mset_replicate_mset[simp]: "image_mset f (replicate_mset n a) = replicate_mset n (f a)"
  by (induction n) auto

lemma msetsum_if_eq_constant:
  "(\<Sum>x\<in>#M. if a = x then (f x) else 0) = ((op + (f a)) ^^ (count M a)) 0"
  by (induction M) (auto simp: ac_simps)

context
begin

private lemma iterate_op_plus: "((op + k) ^^ m) 0 = k * m"
  by (induction m) auto

lemma untion_image_mset_Pair_distribute:
  "\<Union>#{#image_mset (Pair x) (C x). x \<in># J - I#} = \<Union>#{#image_mset (Pair x) (C x). x \<in># J#} -
    \<Union>#{#image_mset (Pair x) (C x). x \<in># I#}"
  by (auto simp: multiset_eq_iff count_msetsum count_image_mset_Pair msetsum_if_eq_constant
    iterate_op_plus diff_mult_distrib2)

lemma Sigma_mset_Un_distrib1: "Sigma_mset (I #\<union> J) C = Sigma_mset I C #\<union> Sigma_mset J C"
  by (auto simp: Sigma_mset_def sup_subset_mset_def untion_image_mset_Pair_distribute)

lemma Sigma_mset_Un_distrib2: "(SIGMAMSET i\<in>#I. A i #\<union> B i) = Sigma_mset I A #\<union> Sigma_mset I B"
  by (auto simp: multiset_eq_iff count_msetsum count_image_mset_Pair msetsum_if_eq_constant
    Sigma_mset_def diff_mult_distrib2 iterate_op_plus max_def not_in_iff)

lemma Sigma_mset_Int_distrib1: "Sigma_mset (I #\<inter> J) C = Sigma_mset I C #\<inter> Sigma_mset J C"
  by (auto simp: multiset_eq_iff count_msetsum count_image_mset_Pair msetsum_if_eq_constant
    Sigma_mset_def iterate_op_plus min_def not_in_iff)

lemma Sigma_mset_Int_distrib2: "(SIGMAMSET i\<in>#I. A i #\<inter> B i) = Sigma_mset I A #\<inter> Sigma_mset I B"
  by (auto simp: multiset_eq_iff count_msetsum count_image_mset_Pair msetsum_if_eq_constant
    Sigma_mset_def iterate_op_plus min_def not_in_iff)

lemma Sigma_mset_Diff_distrib1: "Sigma_mset (I - J) C = Sigma_mset I C - Sigma_mset J C"
  by (auto simp: multiset_eq_iff count_msetsum count_image_mset_Pair msetsum_if_eq_constant
    Sigma_mset_def iterate_op_plus min_def not_in_iff diff_mult_distrib2)

lemma Sigma_mset_Diff_distrib2: "(SIGMAMSET i\<in>#I. A i - B i) = Sigma_mset I A - Sigma_mset I B"
  by (auto simp: multiset_eq_iff count_msetsum count_image_mset_Pair msetsum_if_eq_constant
    Sigma_mset_def iterate_op_plus min_def not_in_iff diff_mult_distrib)

lemma msetsum_right_distrib:
  fixes f :: "'a => ('b::semiring_0)"
  shows "a * (\<Sum>b \<in># B. f b) = (\<Sum>b \<in># B. a * f b)"
  by (induction B) (auto simp: distrib_left)

lemma Sigma_mset_Union: "Sigma_mset (\<Union>#X) B = (\<Union># (image_mset (\<lambda>A. Sigma_mset A B) X))"
  by (auto simp: multiset_eq_iff count_msetsum count_image_mset_Pair msetsum_if_eq_constant
    Sigma_mset_def iterate_op_plus min_def not_in_iff msetsum_right_distrib)

end


lemma Times_mset_Un_distrib1: "(A #\<union> B) \<times>mset C = A \<times>mset C #\<union> B \<times>mset C "
  by (fact Sigma_mset_Un_distrib1)

lemma Times_mset_Int_distrib1: "(A #\<inter> B) \<times>mset C = A \<times>mset C #\<inter> B \<times>mset C "
  by (fact Sigma_mset_Int_distrib1)

lemma Times_mset_Diff_distrib1: "(A - B) \<times>mset C = A \<times>mset C - B \<times>mset C "
  by (fact Sigma_mset_Diff_distrib1)

lemma Times_mset_empty[simp]: "A \<times>mset B = {#} \<longleftrightarrow> A = {#} \<or> B = {#}"
  by (auto simp: Sigma_mset_empty_iff)

text \<open>This is not a duplicate of @{term replicate_mset}: the latter duplicates a single element, while
  the former replicates a multiset.\<close>
fun repeat_mset :: "nat \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset" where
  "repeat_mset 0 _ = {#}" |
  "repeat_mset (Suc n) A = A + repeat_mset n A"

lemma repeat_mset_compower: "repeat_mset n A = ((op + A) ^^ n) {#}"
  by (induction n) auto

lemma repeat_mset_distrib: "repeat_mset n (A + B) = repeat_mset n A + repeat_mset n B"
  by (induction n) (auto simp: ac_simps)

lemma repeat_mset_distrib_nat: "repeat_mset (m + n) A = repeat_mset m A + repeat_mset n A"
  by (induction m) (auto simp: ac_simps)

lemma repeat_mset_single[simp]: "repeat_mset n {#a#} = replicate_mset n a"
  by (induction n) (auto simp: ac_simps)

lemma repeat_mset_prod: "repeat_mset (m * n) A = ((op + (repeat_mset n A)) ^^ m) {#}"
  by (induction m) (auto simp: repeat_mset_distrib_nat)

lemma repeat_mset_empty[simp]: "repeat_mset n {#} = {#}"
  by (induction n) auto

lemma repeat_mset_empty_iff: "repeat_mset n A = {#} \<longleftrightarrow> n = 0 \<or> A = {#}"
  by (cases n) auto

lemma fst_image_mset_times_mset [simp]:
  "image_mset fst (A \<times>mset B) = (if B = {#} then {#} else repeat_mset (size B) A)"
  by (induction B) (auto simp: Times_mset_single_right ac_simps)

lemma snd_image_mset_times_mset [simp]:
  "image_mset snd (A \<times>mset B) = (if A = {#} then {#} else repeat_mset (size A) B)"
  by (induction B) (auto simp: Times_mset_single_right repeat_mset_distrib image_mset_const)

lemma product_swap_mset:
  "image_mset prod.swap (A \<times>mset B) = B \<times>mset A"
  by (induction A) (auto simp add: Times_mset_single_left Times_mset_single_right)

context
begin

qualified definition product_mset :: "'a multiset \<Rightarrow> 'b multiset \<Rightarrow> ('a \<times> 'b) multiset" where
  [code_abbrev]: "product_mset A B = A \<times>mset B"

lemma member_product_mset: "x \<in># Multiset_More.product_mset A B \<longleftrightarrow> x \<in># A \<times>mset B"
  by (simp add: Multiset_More.product_mset_def)

end

end
