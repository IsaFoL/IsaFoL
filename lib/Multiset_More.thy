(*  Title:       More about Multisets
    Author:      Jasmin Blanchette <blanchette at in.tum.de>, 2014, 2015
    Author:      Dmitriy Traytel <traytel at in.tum.de>, 2014
    Author:      Mathias Fleury <mathias.fleury at mpi-inf.mpg.de>, 2015
    Maintainer:  Jasmin Blanchette <blanchette at in.tum.de>
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
  mset_leD[dest, intro?] (*@{thm subsetD}*)

  Multiset.in_multiset_in_set[simp]

lemma image_mset_cong2[cong]:
  "(\<And>x. x \<in># M \<Longrightarrow> f x = g x) \<Longrightarrow> M = N \<Longrightarrow> image_mset f M = image_mset g N"
by (hypsubst, rule image_mset_cong)

(*@{thm psubsetE} is the set counter part*)
lemma subset_msetE [elim!]:
  "[|A \<subset># B;  [|A \<subseteq># B; ~ (B\<subseteq>#A)|] ==> R|] ==> R"
  unfolding subseteq_mset_def subset_mset_def by (meson mset_less_eqI subset_mset.eq_iff)

(* TODO check why auto needs these lemma sometimes *)
lemma ball_msetE [elim]: "\<forall>x\<in>#A. P x ==> (P x ==> Q) ==> (x \<notin># A ==> Q) ==> Q"
  by blast

lemma bex_msetI [intro]: "P x ==> x\<in>#A ==> \<exists>x\<in>#A. P x"
  \<comment> \<open>Normally the best argument order: @{prop "P x"} constrains the
    choice of @{prop "x\<in>#A"}.\<close>
  by  blast

lemma rev_bex_msetI [intro]: "x\<in>#A ==> P x ==> \<exists>x\<in>#A. P x"
  \<comment> \<open>The best argument order when there is only one @{prop "x\<in>#A"}.\<close>
  by  blast

subsection \<open>Lemmas about intersection\<close>
(* Unsure if suited as simp rules or if only slowing down stuff\<dots>*)
lemma mset_inter_single:
  "x \<in># \<Sigma> \<Longrightarrow> \<Sigma> #\<inter> {#x#} = {#x#}"
  "x \<notin># \<Sigma> \<Longrightarrow> \<Sigma> #\<inter> {#x#} = {#}"
    apply (simp add: mset_le_single subset_mset.inf_absorb2)
  by (simp add: multiset_inter_def)

subsection \<open>Lemmas about cardinality\<close>
text \<open>
This sections adds various lemmas about size. Most lemmas have a finite set equivalent.
\<close>
lemma size_Suc_Diff1:
  "x \<in># \<Sigma> \<Longrightarrow> Suc (size (\<Sigma> - {#x#})) = size \<Sigma>"
  using arg_cong[OF insert_DiffM, of _ _ size] by simp

lemma size_Diff_singleton: "x \<in># \<Sigma> \<Longrightarrow> size (\<Sigma> - {#x#}) = size \<Sigma> - 1"
  by (simp add: size_Suc_Diff1 [symmetric])

lemma size_Diff_singleton_if: "size (A - {#x#}) = (if x \<in># A then size A - 1 else size A)"
  by (simp add: size_Diff_singleton)

lemma size_Un_Int:
  "size A + size B = size (A #\<union> B) + size (A #\<inter> B)"
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

lemma diff_size_le_size_Diff:  "size (\<Sigma>:: _ multiset) - size \<Sigma>' \<le> size (\<Sigma> - \<Sigma>')"
proof-
  have "size \<Sigma> - size \<Sigma>' \<le> size \<Sigma> - size (\<Sigma> #\<inter> \<Sigma>')"
    using size_mset_mono diff_le_mono2 subset_mset.inf_le2 by blast
  also have "\<dots> = size(\<Sigma>-\<Sigma>')" using assms by(simp add: size_Diff_subset_Int)
  finally show ?thesis .
qed

lemma size_Diff1_less: "x\<in># \<Sigma> \<Longrightarrow> size (\<Sigma> - {#x#}) < size \<Sigma>"
  apply (rule Suc_less_SucD)
  by (simp add: size_Suc_Diff1)

lemma size_Diff2_less: "x\<in># \<Sigma> \<Longrightarrow> y\<in># \<Sigma> \<Longrightarrow> size (\<Sigma> - {#x#} - {#y#}) < size \<Sigma>"
  using nonempty_has_size by (fastforce intro!: diff_Suc_less simp add: size_Diff1_less
    size_Diff_subset_Int mset_inter_single)

lemma size_Diff1_le: "size (\<Sigma> - {#x#}) \<le> size \<Sigma>"
  by (cases "x \<in># \<Sigma>") (simp_all add: size_Diff1_less less_imp_le)

lemma size_psubset: "(\<Sigma>:: _ multiset) \<le># \<Sigma>' \<Longrightarrow> size \<Sigma> < size \<Sigma>' \<Longrightarrow> \<Sigma> <# \<Sigma>'"
  using less_irrefl subset_mset_def by blast


subsection \<open>Multiset Extension of Multiset Ordering\<close>

text \<open>
The \<open>op #\<subset>##\<close> and \<open>op #\<subseteq>##\<close> operators are introduced as the multiset extension of
the multiset orderings of @{term "op #\<subset>#"} and @{term "op #\<subseteq>#"}.
\<close>

definition less_mset_mset :: "('a :: order) multiset multiset \<Rightarrow> 'a multiset multiset \<Rightarrow> bool"
  (infix "#<##" 50)
where
  "M' #<## M \<longleftrightarrow> (M', M) \<in> mult {(x', x). x' #<# x}"

definition le_mset_mset :: "('a :: order) multiset multiset \<Rightarrow> 'a multiset multiset \<Rightarrow> bool"
  (infix "#<=##" 50)
where
  "M' #<=## M \<longleftrightarrow> M' #<## M \<or> M' = M"

notation less_mset_mset (infix "#\<subset>##" 50)
notation le_mset_mset (infix "#\<subseteq>##" 50)

lemmas less_mset_mset\<^sub>D\<^sub>M = order.mult\<^sub>D\<^sub>M[OF order_multiset, folded less_mset_mset_def]
lemmas less_mset_mset\<^sub>H\<^sub>O = order.mult\<^sub>H\<^sub>O[OF order_multiset, folded less_mset_mset_def]

interpretation multiset_multiset_order: order
  "le_mset_mset :: ('a :: linorder) multiset multiset \<Rightarrow> ('a :: linorder) multiset multiset \<Rightarrow> bool"
  "less_mset_mset :: ('a :: linorder) multiset multiset \<Rightarrow> ('a::linorder) multiset multiset \<Rightarrow> bool"
  unfolding less_mset_mset_def[abs_def] le_mset_mset_def[abs_def] less_multiset_def[abs_def]
  by (rule order.order_mult)+ standard

interpretation multiset_multiset_linorder: linorder
  "le_mset_mset :: ('a :: linorder) multiset multiset \<Rightarrow> ('a :: linorder) multiset multiset \<Rightarrow> bool"
  "less_mset_mset :: ('a :: linorder) multiset multiset \<Rightarrow> ('a::linorder) multiset multiset \<Rightarrow> bool"
  unfolding less_mset_mset_def[abs_def] le_mset_mset_def[abs_def]
  by (rule linorder.linorder_mult[OF linorder_multiset])

lemma wf_less_mset_mset: "wf {(\<Sigma> :: ('a :: wellorder) multiset multiset, T). \<Sigma> #\<subset>## T}"
  unfolding less_mset_mset_def by (auto intro: wf_mult wf_less_multiset)

interpretation multiset_multiset_wellorder: wellorder
  "le_mset_mset :: ('a::wellorder) multiset multiset \<Rightarrow> ('a::wellorder) multiset multiset \<Rightarrow> bool"
  "less_mset_mset :: ('a::wellorder) multiset multiset \<Rightarrow> ('a::wellorder) multiset multiset \<Rightarrow> bool"
  by unfold_locales (blast intro: wf_less_mset_mset[unfolded wf_def, rule_format])

lemma union_less_mset_mset_mono2: "B #\<subset>## D \<Longrightarrow> C + B #\<subset>## C + (D::'a::order multiset multiset)"
apply (unfold less_mset_mset_def mult_def)
apply (erule trancl_induct)
 apply (blast intro: mult1_union)
apply (blast intro: mult1_union trancl_trans)
done

lemma union_less_mset_mset_diff_plus:
  "U \<le># \<Sigma> \<Longrightarrow> T #\<subset>## U \<Longrightarrow> \<Sigma> - U + T #\<subset>## \<Sigma>"
  apply (drule subset_mset.diff_add[symmetric])
  using union_less_mset_mset_mono2[of T U "\<Sigma> - U"] by simp

lemma ex_gt_imp_less_mset_mset:
  "(\<exists>y :: 'a :: linorder multiset \<in># T. (\<forall>x. x \<in># \<Sigma> \<longrightarrow> x #\<subset># y)) \<Longrightarrow> \<Sigma> #\<subset>## T"
  using less_mset_mset\<^sub>H\<^sub>O by (metis count_greater_zero_iff count_inI less_nat_zero_code
    multiset_linorder.not_less_iff_gr_or_eq)

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
  apply (rule mset_less_size)
  apply (auto simp: subset_mset_def multiset_eq_iff)
  done

lemma size_mset_remove1_mset_le_iff:
  "size (remove1_mset x M) < size M \<longleftrightarrow> x \<in># M"
  apply (rule iffI)
    using less_irrefl apply fastforce
  apply (rule mset_less_size)
  by (auto elim: in_countE simp: subset_mset_def multiset_eq_iff)

lemma set_mset_remove1_mset[simp]:
  "set_mset (remove1_mset L (mset W)) = set (remove1 L W)"
  by (metis mset_remove1 set_mset_mset)

subsection \<open>Replicate\<close>

lemma replicate_mset_plus: "replicate_mset (a + b) C = replicate_mset a C + replicate_mset b C"
  by (induct a) (auto simp: ac_simps)

lemma mset_replicate_replicate_mset:
  "mset (replicate n L) = replicate_mset n L"
  by (induction n) auto

lemma set_mset_single_iff_replicate_mset:
  "set_mset U = {a}  \<longleftrightarrow> (\<exists>n>0. U = replicate_mset n a)" (is "?S \<longleftrightarrow> ?R")
proof
  assume ?R
  then show ?S by auto
next
  assume ?S
  show  ?R
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

lemma mset_set_set_mset_empty_mempty[iff]:
  "mset_set (set_mset D) = {#} \<longleftrightarrow> D = {#}"
  by (auto dest: arg_cong[of _ _ set_mset])

lemma size_mset_set_card:
  "finite S \<Longrightarrow> size (mset_set S) = card S"
  by (induction S rule: finite_induct) auto

lemma count_mset_set_le_one: "count (mset_set A) x \<le> 1"
  by (metis count_mset_set(1) count_mset_set(2) count_mset_set(3) eq_iff le_numeral_extra(1))

lemma mset_set_subseteq_mset_set[iff]:
  assumes "finite A" "finite B"
  shows "mset_set A \<subseteq># mset_set B \<longleftrightarrow> A \<subseteq> B"
  by (metis assms contra_subsetD count_mset_set(1,3) count_mset_set_le_one finite_set_mset_mset_set
    less_eq_nat.simps(1) mset_less_eqI set_mset_mono)

lemma mset_set_set_mset_subseteq[simp]: "mset_set (set_mset A) \<subseteq># A"
  by (metis count_mset_set(1,3) finite_set_mset less_eq_nat.simps(1) less_one
    mem_Collect_eq mset_less_eqI not_less set_mset_def)

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

lemma remdups_mset_empty[simp]:
  "remdups_mset {#} = {#}"
  unfolding remdups_mset_def by auto

lemma remdups_mset_singleton[simp]:
  "remdups_mset {#a#} = {#a#}"
  unfolding remdups_mset_def by auto

lemma set_mset_remdups[simp]: "set_mset (remdups_mset (D + C)) = set_mset (D + C) " by auto

lemma remdups_mset_eq_empty[iff]:
  "remdups_mset D = {#} \<longleftrightarrow> D = {#}"
  unfolding remdups_mset_def by blast

lemma remdups_mset_singleton_sum[simp]:
  "remdups_mset ({#a#} + A) = (if a \<in># A then remdups_mset A else {#a#} + remdups_mset A)"
  "remdups_mset (A+{#a#}) = (if a \<in># A then remdups_mset A else {#a#} + remdups_mset A)"
  unfolding remdups_mset_def by (simp_all add: insert_absorb)

lemma mset_remdups_remdups_mset[simp]:
  "mset (remdups D) = remdups_mset (mset D)"
  by (induction D) (auto simp add: ac_simps)

definition distinct_mset :: "'a multiset \<Rightarrow> bool" where
"distinct_mset S \<longleftrightarrow> (\<forall>a. a \<in># S \<longrightarrow> count S a = 1)"

lemma distinct_mset_empty[simp]: "distinct_mset {#}"
  unfolding distinct_mset_def by auto

lemma distinct_mset_singleton[simp]: "distinct_mset {#a#}"
  unfolding distinct_mset_def by auto

definition distinct_mset_set :: "'a multiset set \<Rightarrow> bool" where
"distinct_mset_set \<Sigma> \<longleftrightarrow> (\<forall>S \<in>\<Sigma>. distinct_mset S)"

lemma distinct_mset_set_empty[simp]:
  "distinct_mset_set {}"
  unfolding distinct_mset_set_def by auto

lemma distinct_mset_set_singleton[iff]:
  "distinct_mset_set {A} \<longleftrightarrow> distinct_mset A"
  unfolding distinct_mset_set_def by auto

lemma distinct_mset_set_insert[iff]:
  "distinct_mset_set (insert S \<Sigma>) \<longleftrightarrow> (distinct_mset S \<and> distinct_mset_set \<Sigma>)"
  unfolding distinct_mset_set_def by auto

lemma distinct_mset_set_union[iff]:
  "distinct_mset_set (\<Sigma> \<union> \<Sigma>') \<longleftrightarrow> (distinct_mset_set \<Sigma> \<and> distinct_mset_set \<Sigma>')"
  unfolding distinct_mset_set_def by auto

lemma distinct_mset_union:
  "distinct_mset (A + B) \<Longrightarrow> distinct_mset A"
proof -
  assume a1: "distinct_mset (A + B)"
  obtain aa :: "'a multiset \<Rightarrow> 'a" where
    f2: "(\<forall>m. \<not> distinct_mset m \<or> (\<forall>a. (a::'a) \<notin># m \<or> count m a = 1))"
      "(\<forall>m. aa m \<in># m \<and> count m (aa m) \<noteq> 1 \<or> distinct_mset m)"
    by (metis (full_types) distinct_mset_def)
  then have "count (A + B) (aa A) = 1 \<or> distinct_mset A"
    using a1 by (meson mset_leD mset_le_add_left)
  then show ?thesis
    using f2 by (metis (no_types) One_nat_def add_is_1 count_union mem_Collect_eq order_less_irrefl
      set_mset_def)
qed

lemma distinct_mset_minus[simp]:
  "distinct_mset A \<Longrightarrow> distinct_mset (A - B)"
  by (metis Multiset.diff_le_self mset_le_exists_conv distinct_mset_union)

lemma in_distinct_mset_set_distinct_mset:
  "a \<in> \<Sigma> \<Longrightarrow> distinct_mset_set \<Sigma> \<Longrightarrow> distinct_mset a"
  unfolding distinct_mset_set_def by auto

lemma distinct_mset_remdups_mset[simp]: "distinct_mset (remdups_mset S)"
  using count_remdups_mset_eq_1 unfolding distinct_mset_def by metis

lemma distinct_mset_distinct[simp]:
  "distinct_mset (mset x) = distinct x"
  unfolding distinct_mset_def by (auto simp: distinct_count_atmost_1 not_in_iff[symmetric])

lemma count_mset_set_if:
  "count (mset_set A) a = (if a \<in> A \<and> finite A then 1 else 0)"
  by auto

lemma distinct_mset_mset_set:
  "distinct_mset (mset_set A)"
  unfolding distinct_mset_def count_mset_set_if by (auto simp: not_in_iff)

lemma distinct_mset_rempdups_union_mset:
  assumes "distinct_mset A" and "distinct_mset B"
  shows "A #\<union> B = remdups_mset (A + B)"
  using assms nat_le_linear unfolding remdups_mset_def
  by (force simp add: multiset_eq_iff max_def count_mset_set_if distinct_mset_def not_in_iff)

lemma distinct_mset_set_distinct:
  "distinct_mset_set (mset ` set Cs) \<longleftrightarrow> (\<forall>c\<in> set Cs. distinct c)"
  unfolding distinct_mset_set_def by auto

lemma distinct_mset_add_single:
  "distinct_mset ({#a#} + L) \<longleftrightarrow> distinct_mset L \<and> a \<notin># L"
  unfolding distinct_mset_def
  apply (rule iffI)
    prefer 2 apply (auto simp: not_in_iff)[]
  apply standard
    apply (intro allI)
    apply (rename_tac aa, case_tac "a = aa")
    by (auto split: if_split_asm)

lemma distinct_mset_single_add:
  "distinct_mset (L + {#a#}) \<longleftrightarrow> distinct_mset L \<and> a \<notin># L"
  unfolding add.commute[of L "{#a#}"] distinct_mset_add_single by fast

lemma distinct_mset_size_eq_card:
  "distinct_mset C \<Longrightarrow> size C = card (set_mset C)"
  by (induction C) (auto simp: distinct_mset_single_add)

text \<open>Another characterisation of @{term distinct_mset}\<close>
lemma distinct_mset_count_less_1:
  "distinct_mset S \<longleftrightarrow> (\<forall>a. count S a \<le> 1)"
  using eq_iff nat_le_linear unfolding distinct_mset_def by fastforce

lemma distinct_mset_add:
  "distinct_mset (L + L') \<longleftrightarrow> distinct_mset L \<and> distinct_mset L' \<and> L #\<inter> L' = {#}" (is "?A \<longleftrightarrow> ?B")
proof (rule iffI)
  assume ?A
  have L: "distinct_mset L"
    using \<open>distinct_mset (L + L')\<close> distinct_mset_union  by blast
  moreover have L': "distinct_mset L'"
    using \<open>distinct_mset (L + L')\<close> distinct_mset_union unfolding add.commute[of L L'] by blast
  moreover have "L #\<inter> L' = {#}"
    using L L' \<open>?A\<close> unfolding multiset_inter_def multiset_eq_iff distinct_mset_count_less_1
    by (metis Nat.diff_le_self add_diff_cancel_left' count_diff count_empty diff_is_0_eq eq_iff
      le_neq_implies_less less_one)
  ultimately show ?B by fast
next
  assume ?B
  show ?A
    unfolding distinct_mset_count_less_1
    proof (intro allI)
      fix a
      have "count (L + L') a \<le> count L a + count L' a"
        by auto
      moreover have "count L a + count L' a \<le> 1"
        using \<open>?B\<close> by (metis One_nat_def add.commute add_decreasing2 count_diff diff_add_zero
          distinct_mset_count_less_1 le_SucE multiset_inter_count plus_multiset.rep_eq
          subset_mset.inf.idem)
      ultimately show "count (L + L') a \<le> 1"
        by arith
    qed
qed

lemma distinct_mset_set_mset_ident[simp]: "distinct_mset M \<Longrightarrow> mset_set (set_mset M) = M"
  apply (auto simp: multiset_eq_iff)
  apply (rename_tac x)
  apply (case_tac "count M x = 0")
   apply (simp add: not_in_iff[symmetric])
  apply (case_tac "count M x = 1")
   apply (simp add: count_inI)
  unfolding distinct_mset_count_less_1 by (meson le_neq_implies_less less_one)

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
  by (induct M, auto, meson count_le_replicate_mset_le order_refl subset_mset.add_diff_assoc2)

lemma comprehension_mset_False[simp]:
   "{# L \<in># A. False#} = {#}"
  by (auto simp: multiset_eq_iff)

text \<open>Near duplicate of @{thm filter_eq_replicate_mset}\<close>
lemma filter_mset_eq:
   "filter_mset (op = L) A = replicate_mset (count A L) L"
  by (auto simp: multiset_eq_iff)

lemma filter_mset_union_mset:
  "filter_mset P (A #\<union> B) = filter_mset P A #\<union> filter_mset P B"
  by (auto simp: multiset_eq_iff)

lemma filter_mset_mset_set:
  "finite A \<Longrightarrow> filter_mset P (mset_set A) = mset_set {a \<in> A. P a}"
  by (auto simp: multiset_eq_iff count_mset_set_if)

subsection \<open>Sums\<close>
lemma msetsum_distrib[simp]:
  fixes C D :: "'a \<Rightarrow> 'b::{comm_monoid_add}"
  shows "(\<Sum>x\<in>#A. C x + D x) = (\<Sum>x\<in>#A. C x) + (\<Sum>x\<in>#A. D x)"
  by (induction A) (auto simp: ac_simps)

lemma msetsum_union_disjoint:
  assumes "A #\<inter> B = {#}"
  shows "(\<Sum>La\<in>#A #\<union> B. f La) = (\<Sum>La\<in>#A. f La) + (\<Sum>La\<in>#B. f La)"
  by (metis assms diff_zero empty_sup image_mset_union  msetsum.union multiset_inter_commute
    multiset_union_diff_commute sup_subset_mset_def zero_diff)

subsection \<open>Order\<close>
(*TODO: remove when multiset is of sort ord again*)
instantiation multiset :: (linorder) linorder
begin

definition less_multiset :: "'a::linorder multiset \<Rightarrow> 'a multiset \<Rightarrow> bool" where
  "M' < M \<longleftrightarrow> M' #\<subset># M"

definition less_eq_multiset :: "'a multiset \<Rightarrow> 'a multiset \<Rightarrow>bool" where
   "(M'::'a multiset) \<le> M \<longleftrightarrow> M' #\<subseteq># M"

instance
  by standard (auto simp add: less_eq_multiset_def less_multiset_def multiset_order.less_le_not_le
    add.commute multiset_order.add_right_mono)
end
end
