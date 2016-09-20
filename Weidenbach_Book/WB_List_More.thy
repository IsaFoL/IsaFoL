theory WB_List_More
imports Main "../lib/Multiset_More"
begin

text \<open>Sledgehammer parameters\<close>
sledgehammer_params[debug]

section \<open>Various Lemmas\<close>
text \<open>Close to the theorem @{thm [source] nat_less_induct} (@{thm nat_less_induct}), but with a
  separation between the zero and non-zero case.\<close>
thm nat_less_induct
lemma nat_less_induct_case[case_names 0 Suc]:
  assumes
    "P 0" and
    "\<And>n. (\<forall>m < Suc n. P m) \<Longrightarrow> P (Suc n)"
  shows "P n"
  apply (induction rule: nat_less_induct)
  by (rename_tac n, case_tac n) (auto intro: assms)

text \<open>This is only proved in simple cases by auto. In assumptions, nothing happens, and
  the theorem @{thm [source] if_split_asm} can blow up goals (because of other if-expressions either
  in the context or as simplification rules).\<close>
lemma if_0_1_ge_0[simp]:
  "0 < (if P then a else (0::nat)) \<longleftrightarrow> P \<and> 0 < a"
  by auto

text \<open>Bounded function have not yet been defined in Isabelle.\<close>
definition bounded where
"bounded f \<longleftrightarrow> (\<exists>b. \<forall>n. f n \<le> b)"

abbreviation unbounded :: "('a \<Rightarrow> 'b::ord) \<Rightarrow> bool" where
"unbounded f \<equiv> \<not> bounded f"

lemma not_bounded_nat_exists_larger:
  fixes f :: "nat \<Rightarrow> nat"
  assumes unbound: "unbounded f"
  shows "\<exists>n. f n > m \<and> n > n\<^sub>0"
proof (rule ccontr)
  assume H: "\<not> ?thesis"
  have "finite {f n|n. n \<le> n\<^sub>0}"
    by auto
  have "\<And>n. f n \<le> Max ({f n|n. n \<le> n\<^sub>0} \<union> {m})"
    apply (case_tac "n \<le> n\<^sub>0")
    apply (metis (mono_tags, lifting) Max_ge Un_insert_right \<open>finite {f n |n. n \<le> n\<^sub>0}\<close>
      finite_insert insertCI mem_Collect_eq sup_bot.right_neutral)
    by (metis (no_types, lifting) H Max_less_iff Un_insert_right \<open>finite {f n |n. n \<le> n\<^sub>0}\<close>
      finite_insert insertI1 insert_not_empty leI sup_bot.right_neutral)
  then show False
    using unbound unfolding bounded_def by auto
qed

text \<open>A function is bounded iff its product with a non-zero constant is bounded. The non-zero
  condition is needed only for the reverse implication (see for example @{term "k = (0::nat)"} and
  @{term "f = (\<lambda>i. i)"} for a counter-example).\<close>
lemma bounded_const_product:
  fixes k :: nat and f :: "nat \<Rightarrow> nat"
  assumes "k > 0"
  shows "bounded f \<longleftrightarrow> bounded (\<lambda>i. k * f i)"
  unfolding bounded_def apply (rule iffI)
   using mult_le_mono2 apply blast
  by (meson assms le_less_trans less_or_eq_imp_le nat_mult_less_cancel_disj split_div_lemma)

text \<open>This lemma is not used, but here to show that property that can be expected from
  @{term bounded} holds.\<close>
lemma bounded_finite_linorder:
  fixes f :: "'a \<Rightarrow> 'a :: {finite, linorder}"
  shows "bounded f"
proof -
  have "\<And>x. f x \<le> Max {f x|x. True}"
    by (metis (mono_tags) Max_ge finite mem_Collect_eq)
  then show ?thesis
    unfolding bounded_def by blast
qed

section \<open>More List\<close>

subsection \<open>@{term upt}\<close>
text \<open>The simplification rules are not very handy, because theorem @{thm [source] upt.simps(2)}
    (i.e.\ @{thm upt.simps(2)}) leads to a case distinction, that we do not want if the condition
    is not in the context.\<close>
lemma upt_Suc_le_append: "\<not>i \<le> j \<Longrightarrow> [i..<Suc j] = []"
  by auto

lemmas upt_simps[simp] = upt_Suc_append upt_Suc_le_append

declare upt.simps(2)[simp del]

text \<open>The counterpart for this lemma when @{term "i > n-m"} is theorem @{thm [source] take_all}. It
  is close to theorem @{thm take_upt}, but seems more general.\<close>
lemma take_upt_bound_minus[simp]:
  assumes "i \<le> n - m"
  shows "take i [m..<n] = [m ..<m+i]"
  using assms by (induction i) auto

lemma append_cons_eq_upt:
  assumes "A @ B = [m..<n]"
  shows "A = [m ..<m+length A]" and "B = [m + length A..<n]"
proof -
  have "take (length A) (A @ B) = A" by auto
  moreover
    have "length A \<le> n - m" using assms linear calculation by fastforce
    then have "take (length A) [m..<n] = [m ..<m+length A]" by auto
  ultimately show "A = [m ..<m+length A]" using assms by auto
  show "B = [m + length A..<n]" using assms by (metis append_eq_conv_conj drop_upt)
qed

text \<open>The converse of theorem @{thm [source] append_cons_eq_upt} does not hold, for example if @
  {term "B:: nat list"} is empty and @{term "A :: nat list"} is @{term "[0]"}:\<close>
lemma "A @ B = [m..< n] \<longleftrightarrow> A = [m ..<m+length A] \<and> B = [m + length A..<n]"
(*
Auto Quickcheck found a counterexample:
  A = [0]
  B = []
  m = 0
  n = 0
Evaluated terms:
  A @ B = [m..<n] = False
  A = [m..<m + length A] \<and> B = [m + length A..<n] = True*)
oops

text \<open>A more restrictive version holds:\<close>
lemma "B \<noteq> [] \<Longrightarrow> A @ B = [m..< n] \<longleftrightarrow> A = [m ..<m+length A] \<and> B = [m + length A..<n]"
  (is "?P \<Longrightarrow> ?A = ?B")
proof
  assume ?A then show ?B by (auto simp add: append_cons_eq_upt)
next
  assume ?P and ?B
  then show ?A using append_eq_conv_conj by fastforce
qed

lemma append_cons_eq_upt_length_i:
  assumes "A @ i # B = [m..<n]"
  shows "A = [m ..<i]"
proof -
  have "A = [m ..< m + length A]" using assms append_cons_eq_upt by auto
  have "(A @ i # B) ! (length A) = i" by auto
  moreover have "n - m = length (A @ i # B)"
    using assms length_upt by presburger
  then have "[m..<n] ! (length A) = m + length A" by simp
  ultimately have "i = m + length A" using assms by auto
  then show ?thesis using \<open>A = [m ..< m + length A]\<close> by auto
qed

lemma append_cons_eq_upt_length:
  assumes "A @ i # B = [m..<n]"
  shows "length A = i - m"
  using assms
proof (induction A arbitrary: m)
  case Nil
  then show ?case by (metis append_Nil diff_is_0_eq list.size(3) order_refl upt_eq_Cons_conv)
next
  case (Cons a A)
  then have A: "A @ i # B = [m + 1..<n]" by (metis append_Cons upt_eq_Cons_conv)
  then have "m < i" by (metis Cons.prems append_cons_eq_upt_length_i upt_eq_Cons_conv)
  with Cons.IH[OF A] show ?case by auto
qed

lemma append_cons_eq_upt_length_i_end:
  assumes "A @ i # B = [m..<n]"
  shows "B = [Suc i ..<n]"
proof -
  have "B = [Suc m + length A..<n]" using assms append_cons_eq_upt[of "A @ [i]" B m n] by auto
  have "(A @ i # B) ! (length A) = i" by auto
  moreover have "n - m = length (A @ i # B)"
    using assms length_upt by auto
  then have "[m..<n]! (length A) = m + length A" by simp
  ultimately have "i = m + length A" using assms by auto
  then show ?thesis using \<open>B = [Suc m + length A..<n]\<close> by auto
qed

lemma Max_n_upt: "Max (insert 0 {Suc 0..<n}) = n - Suc 0"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n) note IH = this
  have i: "insert 0 {Suc 0..<Suc n} = insert 0 {Suc 0..< n} \<union> {n}" by auto
  show ?case using IH unfolding i by auto
qed

lemma upt_decomp_lt:
  assumes H: "xs @ i # ys @ j # zs = [m ..< n]"
  shows "i < j"
proof -
  have xs: "xs = [m ..< i]" and ys: "ys = [Suc i ..< j]" and zs: "zs = [Suc j ..< n]"
    using H by (auto dest: append_cons_eq_upt_length_i append_cons_eq_upt_length_i_end)
  show ?thesis
    by (metis append_cons_eq_upt_length_i_end assms lessI less_trans self_append_conv2
      upt_eq_Cons_conv upt_rec ys)
qed

text \<open>The following two lemmas are useful as simp rules for case-distinction. The case
  @{term "length l = 0"} is already simplified by default.\<close>
lemma length_list_Suc_0:
  "length W = Suc 0 \<longleftrightarrow> (\<exists>L. W = [L])"
  apply (cases W)
    apply simp
  apply (rename_tac a W', case_tac W')
  apply auto
  done

lemma length_list_2: "length S = 2 \<longleftrightarrow> (\<exists>a b. S = [a, b])"
  apply (cases S)
   apply simp
  apply (rename_tac a S')
  apply (case_tac S')
  by simp_all

lemma finite_bounded_list:
  fixes b :: nat
  shows "finite {xs. length xs < s \<and> (\<forall>i< length xs. xs ! i < b)}" (is "finite (?S s)")
proof (induction s)
  case 0
  then show ?case by auto
next
  case (Suc s) note IH = this(1)
  have H: "?S (Suc s) \<subseteq> ?S s \<union> {x # xs| x xs. x < b \<and> length xs < s \<and> (\<forall>i< length xs. xs ! i < b)}
    \<union> {[]}"
    (is "_ \<subseteq> _ \<union> ?C \<union> _")
    proof
      fix xs
      assume "xs \<in> ?S (Suc s)"
      then have B: "\<forall>i<length xs. xs ! i < b" and len: "length xs < Suc s"
        by auto
      consider
        (st) "length xs < s" |
        (s) "length xs = 0" and "s = 0" |
        (s') s' where "length xs = Suc s'"
        using len by (cases s) (auto simp add: Nat.less_Suc_eq)
      then show "xs \<in> ?S s \<union> ?C \<union> {[]}"
        proof cases
          case st
          then show ?thesis using B by auto
        next
          case s
          then show ?thesis using B by auto
        next
          case s' note len_xs = this(1)
          then obtain x xs' where xs: "xs = x # xs'" by (cases xs) auto
          then show ?thesis using len_xs B len s' unfolding xs by auto
        qed
    qed
  have "?C \<subseteq> (case_prod Cons) ` ({x. x < b} \<times> ?S s)"
    by auto
  moreover have "finite ({x. x < b} \<times> ?S s)"
    using IH by (auto simp: finite_cartesian_product_iff)
  ultimately have "finite ?C" by (simp add: finite_surj)
  then have "finite (?S s \<union> ?C \<union> {[]})"
    using IH by auto
  then show ?case using H by (auto intro: finite_subset)
qed

subsection \<open>Lexicographic Ordering\<close>
lemma lexn_Suc:
  "(x # xs, y # ys) \<in> lexn r (Suc n) \<longleftrightarrow>
  (length xs = n \<and> length ys = n) \<and> ((x, y) \<in> r \<or> (x = y \<and> (xs, ys) \<in> lexn r n))"
  by (auto simp: map_prod_def image_iff lex_prod_def)

lemma lexn_n:
  "n > 0 \<Longrightarrow> (x # xs, y # ys) \<in> lexn r n \<longleftrightarrow>
  (length xs = n-1 \<and> length ys = n-1) \<and> ((x, y) \<in> r \<or> (x = y \<and> (xs, ys) \<in> lexn r (n - 1)))"
  apply (cases n)
   apply simp
  by (auto simp: map_prod_def image_iff lex_prod_def)

text \<open>There is some subtle point in the proof here. @{term "1::nat"} is converted to
  @{term "Suc 0::nat"}, but @{term "2::nat"} is not: meaning that @{term "1::nat"} is automatically
  simplified by default using the default simplification rule @{thm [source] lexn.simps}. However,
  the latter needs additional simplification rule (see the proof of the theorem above).\<close>

lemma lexn2_conv:
  "([a, b], [c, d]) \<in> lexn r 2 \<longleftrightarrow> (a, c) \<in> r \<or> (a = c \<and> (b, d) \<in>r)"
  by (auto simp: lexn_n simp del: lexn.simps(2))

lemma lexn3_conv:
  "([a, b, c], [a', b', c']) \<in> lexn r 3 \<longleftrightarrow>
    (a, a') \<in> r \<or> (a = a' \<and> (b, b') \<in> r) \<or> (a = a' \<and> b = b' \<and> (c, c') \<in> r)"
  by (auto simp: lexn_n simp del: lexn.simps(2))

subsection \<open>Remove\<close>
subsubsection \<open>More lemmas about remove\<close>
lemma remove1_Nil:
  "remove1 (- L) W = [] \<longleftrightarrow> (W = [] \<or> W = [-L])"
  by (cases W) auto

lemma removeAll_upt:
  "removeAll k [a..<b] = (if k \<ge> a \<and> k < b then [a..<k] @ [Suc k..<b] else [a..<b])"
  by (induction b) auto

lemma remove1_upt:
  "remove1 k [a..<b] = (if k \<ge> a \<and> k < b then [a..<k] @ [Suc k..<b] else [a..<b])"
  by (subst distinct_remove1_removeAll) (auto simp: removeAll_upt)

lemma remove1_mset_single_add:
  "a \<noteq> b \<Longrightarrow> remove1_mset a ({#b#} + C) = {#b#} + remove1_mset a C"
  "remove1_mset a ({#a#} + C) = C"
  by (auto simp: multiset_eq_iff)

lemma sorted_removeAll: "sorted C \<Longrightarrow> sorted (removeAll k C)"
  by (metis map_ident removeAll_filter_not_eq sorted_filter)


subsubsection \<open>Remove under condition\<close>

text \<open>This function removes the first element such that the condition @{term f} holds. It
  generalises @{term List.remove1}.\<close>
fun remove1_cond where
"remove1_cond f [] = []" |
"remove1_cond f (C' # L) = (if f C' then L else C' # remove1_cond f L)"

lemma "remove1 x xs = remove1_cond ((op =) x) xs"
  by (induction xs) auto

lemma mset_map_mset_remove1_cond:
  "mset (map mset (remove1_cond (\<lambda>L. mset L = mset a) C)) =
    remove1_mset (mset a) (mset (map mset C))"
  by (induction C) (auto simp: ac_simps remove1_mset_single_add)

text \<open>We can also generalise @{term List.removeAll}, which is close to @{term List.filter}:\<close>
fun removeAll_cond where
"removeAll_cond f [] = []" |
"removeAll_cond f (C' # L) =
  (if f C' then removeAll_cond f L else C' # removeAll_cond f L)"

lemma "removeAll x xs = removeAll_cond ((op =) x) xs"
  by (induction xs) auto

lemma "removeAll_cond P xs = filter (\<lambda>x. \<not>P x) xs"
  by (induction xs) auto

lemma mset_map_mset_removeAll_cond:
  "mset (map mset (removeAll_cond (\<lambda>b. mset b = mset a) C))
 = removeAll_mset (mset a) (mset (map mset C))"
  by (induction C) (auto simp: ac_simps mset_subset_eqI multiset_diff_union_assoc)

lemma count_mset_count_list:
  "count (mset xs) x = count_list xs x"
  by (induction xs) auto

lemma length_removeAll_count_list:
  "length (removeAll x xs) = length xs - count_list xs x"
proof -
  have "length (removeAll x xs) = size (removeAll_mset x (mset xs))"
    by auto
  also have "\<dots> = size (mset xs) - count (mset xs) x"
    by (metis count_le_replicate_mset_subset_eq le_refl size_Diff_submset size_replicate_mset)
  also have " \<dots> = length xs - count_list xs x"
    unfolding count_mset_count_list by simp
  finally show ?thesis .
qed


subsubsection \<open>Filter\<close>

lemma distinct_filter_eq_if:
  "distinct C \<Longrightarrow> length (filter (op = L) C) = (if L \<in> set C then 1 else 0)"
  by (induction C) auto


subsection \<open>Multisets\<close>

text \<open>The definition and the correctness theorem are from the multiset theory
  @{file "~~/src/HOL/Library/Multiset.thy"}, but a name is necessary to refer to them:\<close>
abbreviation union_mset_list where
"union_mset_list xs ys \<equiv> case_prod append (fold (\<lambda>x (ys, zs). (remove1 x ys, x # zs)) xs (ys, []))"

lemma union_mset_list:
  "mset xs \<union># mset ys = mset (union_mset_list xs ys)"
proof -
  have "\<And>zs. mset (case_prod append (fold (\<lambda>x (ys, zs). (remove1 x ys, x # zs)) xs (ys, zs))) =
      (mset xs \<union># mset ys) + mset zs"
    by (induct xs arbitrary: ys) (simp_all add: multiset_eq_iff)
  then show ?thesis by simp
qed

lemma size_le_Suc_0_iff: "size M \<le> Suc 0 \<longleftrightarrow> ((\<exists>a b. M = {#a#}) \<or> M = {#})"
   using size_1_singleton_mset by (auto simp: le_Suc_eq)

lemma size_2_iff: "size M = 2 \<longleftrightarrow> (\<exists>a b. M = {#a, b#})"
  by (metis One_nat_def Suc_1 Suc_pred empty_not_add_mset nonempty_has_size size_Diff_singleton 
      size_eq_Suc_imp_eq_union size_single union_single_eq_diff union_single_eq_member)

lemma subset_eq_mset_single_iff: "x2 \<subseteq># {#L#} \<longleftrightarrow> x2 = {#} \<or> x2 = {#L#}"
  by (metis single_is_union subset_mset.add_diff_inverse subset_mset.eq_refl subset_mset.zero_le)


subsection \<open>Sorting\<close>

text \<open>@{thm insort_is_Cons} is more general.\<close>
lemma insort_is_append: "\<forall>x\<in>set xs. a \<ge> x \<Longrightarrow> sorted xs \<Longrightarrow> insort a xs = xs @ [a]"
by (induction xs) (auto simp add: insort_is_Cons sorted_Cons)

text \<open>See @{thm sorted_distinct_set_unique}.\<close>
lemma sorted_mset_unique:
  fixes xs :: "'a :: linorder list"
  shows "sorted xs \<Longrightarrow> sorted ys \<Longrightarrow> mset xs = mset ys \<Longrightarrow> xs = ys"
  using properties_for_sort by auto

lemma insort_upt: "insort k [a..<b] =
  (if k < a then k # [a..<b]
  else if k < b then [a..<k] @ k # [k ..<b]
  else [a..<b] @ [k])"
proof -
  have H: "k < Suc b \<Longrightarrow> \<not> k < a \<Longrightarrow> {a..<b} = {a..<k} \<union> {k..<b}" for a b :: nat
    by (simp add: ivl_disj_un_two(3))
  show ?thesis
  apply (induction b)
   apply simp
  apply (case_tac "\<not>k < a \<and> k < Suc b")
   apply (rule sorted_mset_unique)
      apply (auto simp add: sorted_append sorted_insort sorted_Cons ac_simps mset_set_Union
        dest!: H)[2]
    apply (auto simp: insort_is_Cons insort_is_append sorted_append mset_set_Union
      ac_simps dest: H)
  done
qed

lemma removeAll_insert_removeAll: "removeAll k (insort k xs) = removeAll k xs"
  by (simp add: filter_insort_triv removeAll_filter_not_eq)

lemma filter_sorted: "sorted xs \<Longrightarrow> sorted (filter P xs)"
  by (metis list.map_ident sorted_filter)

lemma removeAll_insort:
  "sorted xs \<Longrightarrow> k \<noteq> k' \<Longrightarrow> removeAll k' (insort k xs) = insort k (removeAll k' xs)"
  by (simp add: filter_insort removeAll_filter_not_eq)


subsection \<open>Distinct set of multisets\<close>

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

lemma in_distinct_mset_set_distinct_mset:
  "a \<in> \<Sigma> \<Longrightarrow> distinct_mset_set \<Sigma> \<Longrightarrow> distinct_mset a"
  unfolding distinct_mset_set_def by auto

lemma distinct_mset_remdups_mset[simp]: "distinct_mset (remdups_mset S)"
  using count_remdups_mset_eq_1 unfolding distinct_mset_def by metis

lemma distinct_mset_mset_set: "distinct_mset (mset_set A)"
  unfolding distinct_mset_def count_mset_set_if by (auto simp: not_in_iff)

lemma distinct_mset_set_distinct: "distinct_mset_set (mset ` set Cs) \<longleftrightarrow> (\<forall>c\<in> set Cs. distinct c)"
  unfolding distinct_mset_set_def by auto

end