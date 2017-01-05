theory WB_List_More
imports "$AFP/Nested_Multisets_Ordinals/Multiset_More"
begin

text \<open>Sledgehammer parameters\<close>
sledgehammer_params[debug]

section \<open>Various Lemmas\<close>
text \<open>Close to the theorem @{thm [source] nat_less_induct} (@{thm nat_less_induct}), but with a
  separation between the zero and non-zero case.\<close>
thm nat_less_induct
lemma nat_less_induct_case[case_names 0 Suc]:
  assumes
    \<open>P 0\<close> and
    \<open>\<And>n. (\<forall>m < Suc n. P m) \<Longrightarrow> P (Suc n)\<close>
  shows \<open>P n\<close>
  apply (induction rule: nat_less_induct)
  by (rename_tac n, case_tac n) (auto intro: assms)

text \<open>This is only proved in simple cases by auto. In assumptions, nothing happens, and
  the theorem @{thm [source] if_split_asm} can blow up goals (because of other if-expressions either
  in the context or as simplification rules).\<close>
lemma if_0_1_ge_0[simp]:
  \<open>0 < (if P then a else (0::nat)) \<longleftrightarrow> P \<and> 0 < a\<close>
  by auto

text \<open>Bounded function have not yet been defined in Isabelle.\<close>
definition bounded :: "('a \<Rightarrow> 'b::ord) \<Rightarrow> bool" where
\<open>bounded f \<longleftrightarrow> (\<exists>b. \<forall>n. f n \<le> b)\<close>

abbreviation unbounded :: \<open>('a \<Rightarrow> 'b::ord) \<Rightarrow> bool\<close> where
\<open>unbounded f \<equiv> \<not> bounded f\<close>

lemma not_bounded_nat_exists_larger:
  fixes f :: \<open>nat \<Rightarrow> nat\<close>
  assumes unbound: \<open>unbounded f\<close>
  shows \<open>\<exists>n. f n > m \<and> n > n\<^sub>0\<close>
proof (rule ccontr)
  assume H: \<open>\<not> ?thesis\<close>
  have \<open>finite {f n|n. n \<le> n\<^sub>0}\<close>
    by auto
  have \<open>\<And>n. f n \<le> Max ({f n|n. n \<le> n\<^sub>0} \<union> {m})\<close>
    apply (case_tac \<open>n \<le> n\<^sub>0\<close>)
    apply (metis (mono_tags, lifting) Max_ge Un_insert_right \<open>finite {f n |n. n \<le> n\<^sub>0}\<close>
      finite_insert insertCI mem_Collect_eq sup_bot.right_neutral)
    by (metis (no_types, lifting) H Max_less_iff Un_insert_right \<open>finite {f n |n. n \<le> n\<^sub>0}\<close>
      finite_insert insertI1 insert_not_empty leI sup_bot.right_neutral)
  then show False
    using unbound unfolding bounded_def by auto
qed

text \<open>A function is bounded iff its product with a non-zero constant is bounded. The non-zero
  condition is needed only for the reverse implication (see for example @{term \<open>k = (0::nat)\<close>} and
  @{term \<open>f = (\<lambda>i. i)\<close>} for a counter-example).\<close>
lemma bounded_const_product:
  fixes k :: nat and f :: \<open>nat \<Rightarrow> nat\<close>
  assumes \<open>k > 0\<close>
  shows \<open>bounded f \<longleftrightarrow> bounded (\<lambda>i. k * f i)\<close>
  unfolding bounded_def apply (rule iffI)
   using mult_le_mono2 apply blast
  by (meson assms le_less_trans less_or_eq_imp_le nat_mult_less_cancel_disj split_div_lemma)

text \<open>This lemma is not used, but here to show that property that can be expected from
  @{term bounded} holds.\<close>
lemma bounded_finite_linorder:
  fixes f :: \<open>'a::finite \<Rightarrow> 'b :: {linorder}\<close>
  shows \<open>bounded f\<close>
proof -
  have \<open>finite (f ` UNIV)\<close>
    by simp
  then have \<open>\<And>x. f x \<le> Max (f ` UNIV)\<close>
    by (auto intro: Max_ge)
  then show ?thesis
    unfolding bounded_def by blast
qed


section \<open>More Lists\<close>

lemma tl_drop_def: \<open>tl N = drop 1 N\<close>
  by (cases N)  auto


subsection \<open>@{term upt}\<close>

text \<open>
  The simplification rules are not very handy, because theorem @{thm [source] upt.simps(2)}
  (i.e.\ @{thm upt.simps(2)}) leads to a case distinction, that we usually do not want if the
  condition is not in the context.
\<close>
lemma upt_Suc_le_append: \<open>\<not>i \<le> j \<Longrightarrow> [i..<Suc j] = []\<close>
  by auto

lemmas upt_simps[simp] = upt_Suc_append upt_Suc_le_append

declare upt.simps(2)[simp del]

text \<open>The counterpart for this lemma when @{term \<open>i > n-m\<close>} is theorem @{thm [source] take_all}. It
  is close to theorem @{thm take_upt}, but seems more general.\<close>
lemma take_upt_bound_minus[simp]:
  assumes \<open>i \<le> n - m\<close>
  shows \<open>take i [m..<n] = [m ..<m+i]\<close>
  using assms by (induction i) auto

lemma append_cons_eq_upt:
  assumes \<open>A @ B = [m..<n]\<close>
  shows \<open>A = [m ..<m+length A]\<close> and \<open>B = [m + length A..<n]\<close>
proof -
  have \<open>take (length A) (A @ B) = A\<close> by auto
  moreover {
    have \<open>length A \<le> n - m\<close> using assms linear calculation by fastforce
    then have \<open>take (length A) [m..<n] = [m ..<m+length A]\<close> by auto }
  ultimately show \<open>A = [m ..<m+length A]\<close> using assms by auto
  show \<open>B = [m + length A..<n]\<close> using assms by (metis append_eq_conv_conj drop_upt)
qed

text \<open>The converse of theorem @{thm [source] append_cons_eq_upt} does not hold, for example if @
  {term \<open>B:: nat list\<close>} is empty and @{term \<open>A :: nat list\<close>} is @{term \<open>[0]\<close>}:\<close>
lemma \<open>A @ B = [m..< n] \<longleftrightarrow> A = [m ..<m+length A] \<and> B = [m + length A..<n]\<close>
oops

text \<open>A more restrictive version holds:\<close>
lemma \<open>B \<noteq> [] \<Longrightarrow> A @ B = [m..< n] \<longleftrightarrow> A = [m ..<m+length A] \<and> B = [m + length A..<n]\<close>
  (is \<open>?P \<Longrightarrow> ?A = ?B\<close>)
proof
  assume ?A then show ?B by (auto simp add: append_cons_eq_upt)
next
  assume ?P and ?B
  then show ?A using append_eq_conv_conj by fastforce
qed

lemma append_cons_eq_upt_length_i:
  assumes \<open>A @ i # B = [m..<n]\<close>
  shows \<open>A = [m ..<i]\<close>
proof -
  have \<open>A = [m ..< m + length A]\<close> using assms append_cons_eq_upt by auto
  have \<open>(A @ i # B) ! (length A) = i\<close> by auto
  moreover have \<open>n - m = length (A @ i # B)\<close>
    using assms length_upt by presburger
  then have \<open>[m..<n] ! (length A) = m + length A\<close> by simp
  ultimately have \<open>i = m + length A\<close> using assms by auto
  then show ?thesis using \<open>A = [m ..< m + length A]\<close> by auto
qed

lemma append_cons_eq_upt_length:
  assumes \<open>A @ i # B = [m..<n]\<close>
  shows \<open>length A = i - m\<close>
  using assms
proof (induction A arbitrary: m)
  case Nil
  then show ?case by (metis append_Nil diff_is_0_eq list.size(3) order_refl upt_eq_Cons_conv)
next
  case (Cons a A)
  then have A: \<open>A @ i # B = [m + 1..<n]\<close> by (metis append_Cons upt_eq_Cons_conv)
  then have \<open>m < i\<close> by (metis Cons.prems append_cons_eq_upt_length_i upt_eq_Cons_conv)
  with Cons.IH[OF A] show ?case by auto
qed

lemma append_cons_eq_upt_length_i_end:
  assumes \<open>A @ i # B = [m..<n]\<close>
  shows \<open>B = [Suc i ..<n]\<close>
proof -
  have \<open>B = [Suc m + length A..<n]\<close> using assms append_cons_eq_upt[of \<open>A @ [i]\<close> B m n] by auto
  have \<open>(A @ i # B) ! (length A) = i\<close> by auto
  moreover have \<open>n - m = length (A @ i # B)\<close>
    using assms length_upt by auto
  then have \<open>[m..<n]! (length A) = m + length A\<close> by simp
  ultimately have \<open>i = m + length A\<close> using assms by auto
  then show ?thesis using \<open>B = [Suc m + length A..<n]\<close> by auto
qed

lemma Max_n_upt: \<open>Max (insert 0 {Suc 0..<n}) = n - Suc 0\<close>
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n) note IH = this
  have i: \<open>insert 0 {Suc 0..<Suc n} = insert 0 {Suc 0..< n} \<union> {n}\<close> by auto
  show ?case using IH unfolding i by auto
qed

lemma upt_decomp_lt:
  assumes H: \<open>xs @ i # ys @ j # zs = [m ..< n]\<close>
  shows \<open>i < j\<close>
proof -
  have xs: \<open>xs = [m ..< i]\<close> and ys: \<open>ys = [Suc i ..< j]\<close> and zs: \<open>zs = [Suc j ..< n]\<close>
    using H by (auto dest: append_cons_eq_upt_length_i append_cons_eq_upt_length_i_end)
  show ?thesis
    by (metis append_cons_eq_upt_length_i_end assms lessI less_trans self_append_conv2
      upt_eq_Cons_conv upt_rec ys)
qed

text \<open>The following two lemmas are useful as simp rules for case-distinction. The case
  @{term \<open>length l = 0\<close>} is already simplified by default.\<close>
lemma length_list_Suc_0:
  \<open>length W = Suc 0 \<longleftrightarrow> (\<exists>L. W = [L])\<close>
  apply (cases W)
    apply simp
  apply (rename_tac a W', case_tac W')
  apply auto
  done

lemma length_list_2: \<open>length S = 2 \<longleftrightarrow> (\<exists>a b. S = [a, b])\<close>
  apply (cases S)
   apply simp
  apply (rename_tac a S')
  apply (case_tac S')
  by simp_all

lemma finite_bounded_list:
  fixes b :: nat
  shows \<open>finite {xs. length xs < s \<and> (\<forall>i< length xs. xs ! i < b)}\<close> (is \<open>finite (?S s)\<close>)
proof (induction s)
  case 0
  then show ?case by auto
next
  case (Suc s) note IH = this(1)
  have H: \<open>?S (Suc s) \<subseteq> ?S s \<union> {x # xs| x xs. x < b \<and> length xs < s \<and> (\<forall>i< length xs. xs ! i < b)}
    \<union> {[]}\<close>
    (is \<open>_ \<subseteq> _ \<union> ?C \<union> _\<close>)
    proof
      fix xs
      assume \<open>xs \<in> ?S (Suc s)\<close>
      then have B: \<open>\<forall>i<length xs. xs ! i < b\<close> and len: \<open>length xs < Suc s\<close>
        by auto
      consider
        (st) \<open>length xs < s\<close> |
        (s) \<open>length xs = 0\<close> and \<open>s = 0\<close> |
        (s') s' where \<open>length xs = Suc s'\<close>
        using len by (cases s) (auto simp add: Nat.less_Suc_eq)
      then show \<open>xs \<in> ?S s \<union> ?C \<union> {[]}\<close>
        proof cases
          case st
          then show ?thesis using B by auto
        next
          case s
          then show ?thesis using B by auto
        next
          case s' note len_xs = this(1)
          then obtain x xs' where xs: \<open>xs = x # xs'\<close> by (cases xs) auto
          then show ?thesis using len_xs B len s' unfolding xs by auto
        qed
    qed
  have \<open>?C \<subseteq> (case_prod Cons) ` ({x. x < b} \<times> ?S s)\<close>
    by auto
  moreover have \<open>finite ({x. x < b} \<times> ?S s)\<close>
    using IH by (auto simp: finite_cartesian_product_iff)
  ultimately have \<open>finite ?C\<close> by (simp add: finite_surj)
  then have \<open>finite (?S s \<union> ?C \<union> {[]})\<close>
    using IH by auto
  then show ?case using H by (auto intro: finite_subset)
qed

lemma last_in_set_dropWhile:
  assumes \<open>\<exists>L \<in> set (xs @ [x]). \<not>P L\<close>
  shows \<open>x \<in> set (dropWhile P (xs @ [x]))\<close>
  using assms by (induction xs) auto

lemma mset_drop_upto: \<open>mset (drop a N) = {#N!i. i \<in># mset_set {a..<length N}#}\<close>
proof (induction N arbitrary: a)
  case Nil
  then show ?case by simp
next
  case (Cons c N)
  have upt: \<open>{0..<Suc (length N)} = insert 0 {1..<Suc (length N)}\<close>
    by auto
  then have H: \<open>mset_set {0..<Suc (length N)} = add_mset 0 (mset_set {1..<Suc (length N)})\<close>
    unfolding upt by auto
  have mset_case_Suc: \<open>{#case x of 0 \<Rightarrow> c | Suc x \<Rightarrow> N ! x . x \<in># mset_set {Suc a..<Suc b}#} =
    {#N ! (x-1) . x \<in># mset_set {Suc a..<Suc b}#}\<close> for a b
    by (rule image_mset_cong) (auto split: nat.splits)
  have Suc_Suc: \<open>{Suc a..<Suc b} = Suc ` {a..<b}\<close> for a b
    by auto
  then have mset_set_Suc_Suc: \<open>mset_set {Suc a..<Suc b} = {#Suc n. n \<in># mset_set {a..<b}#}\<close> for a b
    unfolding Suc_Suc by (subst image_mset_mset_set[symmetric]) auto
  have *: \<open>{#N ! (x-Suc 0) . x \<in># mset_set {Suc a..<Suc b}#} = {#N ! x . x \<in># mset_set {a..<b}#}\<close>
    for a b
    by (auto simp add: mset_set_Suc_Suc)
  show ?case
    apply (cases a)
    using Cons[of 0] Cons by (auto simp: nth_Cons drop_Cons H mset_case_Suc *)
qed


subsection \<open>Lexicographic Ordering\<close>

lemma lexn_Suc:
  \<open>(x # xs, y # ys) \<in> lexn r (Suc n) \<longleftrightarrow>
  (length xs = n \<and> length ys = n) \<and> ((x, y) \<in> r \<or> (x = y \<and> (xs, ys) \<in> lexn r n))\<close>
  by (auto simp: map_prod_def image_iff lex_prod_def)

lemma lexn_n:
  \<open>n > 0 \<Longrightarrow> (x # xs, y # ys) \<in> lexn r n \<longleftrightarrow>
  (length xs = n-1 \<and> length ys = n-1) \<and> ((x, y) \<in> r \<or> (x = y \<and> (xs, ys) \<in> lexn r (n - 1)))\<close>
  apply (cases n)
   apply simp
  by (auto simp: map_prod_def image_iff lex_prod_def)

text \<open>
  There is some subtle point in the previous theorem explaining \<^emph>\<open>why\<close> it is useful. @{term \<open>1::nat\<close>}
  is converted to @{term \<open>Suc 0::nat\<close>}, but @{term \<open>2::nat\<close>} is not: meaning that @{term \<open>1::nat\<close>}
  is automatically simplified by default allowing the use of the default simplification rule
  @{thm [source] lexn.simps}. However, the latter needs additional simplification rule (see the
  proof of the theorem above).
\<close>

lemma lexn2_conv:
  \<open>([a, b], [c, d]) \<in> lexn r 2 \<longleftrightarrow> (a, c) \<in> r \<or> (a = c \<and> (b, d) \<in>r)\<close>
  by (auto simp: lexn_n simp del: lexn.simps(2))

lemma lexn3_conv:
  \<open>([a, b, c], [a', b', c']) \<in> lexn r 3 \<longleftrightarrow>
    (a, a') \<in> r \<or> (a = a' \<and> (b, b') \<in> r) \<or> (a = a' \<and> b = b' \<and> (c, c') \<in> r)\<close>
  by (auto simp: lexn_n simp del: lexn.simps(2))


subsection \<open>Remove\<close>

subsubsection \<open>More lemmas about remove\<close>

lemma remove1_Nil:
  \<open>remove1 (- L) W = [] \<longleftrightarrow> (W = [] \<or> W = [-L])\<close>
  by (cases W) auto

lemma removeAll_upt:
  \<open>removeAll k [a..<b] = (if k \<ge> a \<and> k < b then [a..<k] @ [Suc k..<b] else [a..<b])\<close>
  by (induction b) auto

lemma remove1_upt:
  \<open>remove1 k [a..<b] = (if k \<ge> a \<and> k < b then [a..<k] @ [Suc k..<b] else [a..<b])\<close>
  by (subst distinct_remove1_removeAll) (auto simp: removeAll_upt)

lemma sorted_removeAll: \<open>sorted C \<Longrightarrow> sorted (removeAll k C)\<close>
  by (metis map_ident removeAll_filter_not_eq sorted_filter)


subsubsection \<open>Remove under condition\<close>

text \<open>This function removes the first element such that the condition @{term f} holds. It
  generalises @{term List.remove1}.\<close>
fun remove1_cond where
\<open>remove1_cond f [] = []\<close> |
\<open>remove1_cond f (C' # L) = (if f C' then L else C' # remove1_cond f L)\<close>

lemma \<open>remove1 x xs = remove1_cond ((op =) x) xs\<close>
  by (induction xs) auto

lemma mset_map_mset_remove1_cond:
  \<open>mset (map mset (remove1_cond (\<lambda>L. mset L = mset a) C)) =
    remove1_mset (mset a) (mset (map mset C))\<close>
  by (induction C) auto

text \<open>We can also generalise @{term List.removeAll}, which is close to @{term List.filter}:\<close>
fun removeAll_cond :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> where
\<open>removeAll_cond f [] = []\<close> |
\<open>removeAll_cond f (C' # L) = (if f C' then removeAll_cond f L else C' # removeAll_cond f L)\<close>

lemma \<open>removeAll x xs = removeAll_cond ((op =) x) xs\<close>
  by (induction xs) auto

lemma \<open>removeAll_cond P xs = filter (\<lambda>x. \<not>P x) xs\<close>
  by (induction xs) auto

lemma mset_map_mset_removeAll_cond:
  \<open>mset (map mset (removeAll_cond (\<lambda>b. mset b = mset a) C))
    = removeAll_mset (mset a) (mset (map mset C))\<close>
  by (induction C) auto

lemma count_mset_count_list:
  \<open>count (mset xs) x = count_list xs x\<close>
  by (induction xs) auto

lemma length_removeAll_count_list:
  \<open>length (removeAll x xs) = length xs - count_list xs x\<close>
proof -
  have \<open>length (removeAll x xs) = size (removeAll_mset x (mset xs))\<close>
    by auto
  also have \<open>\<dots> = size (mset xs) - count (mset xs) x\<close>
    by (metis count_le_replicate_mset_subset_eq le_refl size_Diff_submset size_replicate_mset)
  also have \<open> \<dots> = length xs - count_list xs x\<close>
    unfolding count_mset_count_list by simp
  finally show ?thesis .
qed


subsubsection \<open>Filter\<close>

lemma distinct_filter_eq_if:
  \<open>distinct C \<Longrightarrow> length (filter (op = L) C) = (if L \<in> set C then 1 else 0)\<close>
  by (induction C) auto


subsection \<open>Multisets\<close>

text \<open>The definition and the correctness theorem are from the multiset theory
  @{file \<open>~~/src/HOL/Library/Multiset.thy\<close>}, but a name is necessary to refer to them:\<close>
definition union_mset_list where
\<open>union_mset_list xs ys \<equiv> case_prod append (fold (\<lambda>x (ys, zs). (remove1 x ys, x # zs)) xs (ys, []))\<close>

lemma union_mset_list:
  \<open>mset xs \<union># mset ys = mset (union_mset_list xs ys)\<close>
proof -
  have \<open>\<And>zs. mset (case_prod append (fold (\<lambda>x (ys, zs). (remove1 x ys, x # zs)) xs (ys, zs))) =
      (mset xs \<union># mset ys) + mset zs\<close>
    by (induct xs arbitrary: ys) (simp_all add: multiset_eq_iff)
  then show ?thesis by (simp add: union_mset_list_def)
qed

lemma size_le_Suc_0_iff: \<open>size M \<le> Suc 0 \<longleftrightarrow> ((\<exists>a b. M = {#a#}) \<or> M = {#})\<close>
   using size_1_singleton_mset by (auto simp: le_Suc_eq)

lemma size_2_iff: \<open>size M = 2 \<longleftrightarrow> (\<exists>a b. M = {#a, b#})\<close>
  by (metis One_nat_def Suc_1 Suc_pred empty_not_add_mset nonempty_has_size size_Diff_singleton
      size_eq_Suc_imp_eq_union size_single union_single_eq_diff union_single_eq_member)

lemma subset_eq_mset_single_iff: \<open>x2 \<subseteq># {#L#} \<longleftrightarrow> x2 = {#} \<or> x2 = {#L#}\<close>
  by (metis single_is_union subset_mset.add_diff_inverse subset_mset.eq_refl subset_mset.zero_le)

lemma mset_eq_size_2:
  \<open>mset xs = {#a, b#} \<longleftrightarrow> xs = [a, b] \<or> xs = [b, a]\<close>
  by (cases xs) (auto simp: add_mset_eq_add_mset Diff_eq_empty_iff_mset subset_eq_mset_single_iff)

lemma mset_set_eq_mset_set_iff:
  \<open>finite A \<Longrightarrow> finite B \<Longrightarrow> mset_set A = mset_set B \<longleftrightarrow> A = B\<close>
  using finite_set_mset_mset_set by fastforce

lemma butlast_list_update:
  \<open>w < length xs \<Longrightarrow> butlast (xs[w := last xs]) = take w xs @ butlast (last xs # drop (Suc w) xs)\<close>
  by (induction xs arbitrary: w) (auto split: nat.splits if_splits simp: upd_conv_take_nth_drop)

lemma mset_butlast_remove1_mset: \<open>xs \<noteq> [] \<Longrightarrow> mset (butlast xs) = remove1_mset (last xs) (mset xs)\<close>
  apply (subst(2) append_butlast_last_id[of xs, symmetric])
   apply assumption
  apply (simp only: mset_append)
  by auto

lemma last_list_update_to_last:
  \<open>last (xs[x := last xs]) = last xs\<close>
  by (metis last_list_update list_update.simps(1))

subsection \<open>Sorting\<close>

text \<open>@{thm insort_is_Cons} is more general.\<close>
lemma insort_is_append: \<open>\<forall>x\<in>set xs. a \<ge> x \<Longrightarrow> sorted xs \<Longrightarrow> insort a xs = xs @ [a]\<close>
by (induction xs) (auto simp add: insort_is_Cons sorted_Cons)

text \<open>See @{thm sorted_distinct_set_unique}.\<close>
lemma sorted_mset_unique:
  fixes xs :: \<open>'a :: linorder list\<close>
  shows \<open>sorted xs \<Longrightarrow> sorted ys \<Longrightarrow> mset xs = mset ys \<Longrightarrow> xs = ys\<close>
  using properties_for_sort by auto

lemma insort_upt: \<open>insort k [a..<b] =
  (if k < a then k # [a..<b]
  else if k < b then [a..<k] @ k # [k ..<b]
  else [a..<b] @ [k])\<close>
proof -
  have H: \<open>k < Suc b \<Longrightarrow> \<not> k < a \<Longrightarrow> {a..<b} = {a..<k} \<union> {k..<b}\<close> for a b :: nat
    by (simp add: ivl_disj_un_two(3))
  show ?thesis
  apply (induction b)
   apply simp
  apply (case_tac \<open>\<not>k < a \<and> k < Suc b\<close>)
   apply (rule sorted_mset_unique)
      apply ((auto simp add: sorted_append sorted_insort sorted_Cons ac_simps mset_set_Union
        dest!: H; fail)+)[2]
    apply (auto simp: insort_is_Cons insort_is_append sorted_append mset_set_Union
      ac_simps dest: H; fail)+
  done
qed

lemma removeAll_insert_removeAll: \<open>removeAll k (insort k xs) = removeAll k xs\<close>
  by (simp add: filter_insort_triv removeAll_filter_not_eq)

lemma filter_sorted: \<open>sorted xs \<Longrightarrow> sorted (filter P xs)\<close>
  by (metis list.map_ident sorted_filter)

lemma removeAll_insort:
  \<open>sorted xs \<Longrightarrow> k \<noteq> k' \<Longrightarrow> removeAll k' (insort k xs) = insort k (removeAll k' xs)\<close>
  by (simp add: filter_insort removeAll_filter_not_eq)


subsection \<open>Distinct Set of Multisets\<close>

definition distinct_mset_set :: \<open>'a multiset set \<Rightarrow> bool\<close> where
  \<open>distinct_mset_set \<Sigma> \<longleftrightarrow> (\<forall>S \<in> \<Sigma>. distinct_mset S)\<close>

lemma distinct_mset_set_empty[simp]: \<open>distinct_mset_set {}\<close>
  unfolding distinct_mset_set_def by auto

lemma distinct_mset_set_singleton[iff]: \<open>distinct_mset_set {A} \<longleftrightarrow> distinct_mset A\<close>
  unfolding distinct_mset_set_def by auto

lemma distinct_mset_set_insert[iff]:
  \<open>distinct_mset_set (insert S \<Sigma>) \<longleftrightarrow> (distinct_mset S \<and> distinct_mset_set \<Sigma>)\<close>
  unfolding distinct_mset_set_def by auto

lemma distinct_mset_set_union[iff]:
  \<open>distinct_mset_set (\<Sigma> \<union> \<Sigma>') \<longleftrightarrow> (distinct_mset_set \<Sigma> \<and> distinct_mset_set \<Sigma>')\<close>
  unfolding distinct_mset_set_def by auto

lemma in_distinct_mset_set_distinct_mset:
  \<open>a \<in> \<Sigma> \<Longrightarrow> distinct_mset_set \<Sigma> \<Longrightarrow> distinct_mset a\<close>
  unfolding distinct_mset_set_def by auto

lemma distinct_mset_remdups_mset[simp]: \<open>distinct_mset (remdups_mset S)\<close>
  using count_remdups_mset_eq_1 unfolding distinct_mset_def by metis

lemma distinct_mset_mset_set: \<open>distinct_mset (mset_set A)\<close>
  unfolding distinct_mset_def count_mset_set_if by (auto simp: not_in_iff)

lemma distinct_mset_set_distinct: \<open>distinct_mset_set (mset ` set Cs) \<longleftrightarrow> (\<forall>c\<in> set Cs. distinct c)\<close>
  unfolding distinct_mset_set_def by auto

end
