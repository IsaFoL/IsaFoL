theory WB_List_More
  imports Nested_Multisets_Ordinals.Multiset_More "HOL-Library.Finite_Map"
    "HOL-Eisbach.Eisbach"
    "HOL-Eisbach.Eisbach_Tools"
begin

text \<open>More Sledgehammer parameters\<close>
(* sledgehammer_params[debug] *)

section \<open>Various Lemmas\<close>


subsection \<open>Not-Related to Refinement or lists\<close>

text \<open>
  Unlike clarify, this does not split tuple of the form \<^term>\<open>\<exists>T. P T\<close> in the assumption.
  After calling it, as the variable are not quantified anymore, the simproc does not trigger,
  allowing to safely call auto/simp/...
\<close>
method normalize_goal =
  (match premises in
    J[thin]: \<open>\<exists>x. _\<close> \<Rightarrow> \<open>rule exE[OF J]\<close>
  \<bar> J[thin]: \<open>_ \<and> _\<close> \<Rightarrow> \<open>rule conjE[OF J]\<close>
  )

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
  by (metis Suc_leI add.right_neutral assms mult.commute mult_0_right mult_Suc_right mult_le_mono
      nat_mult_le_cancel1)

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

subsection \<open>set, nth, tl\<close>

lemma ex_geI: \<open>P n \<Longrightarrow> n \<ge> m \<Longrightarrow> \<exists>n\<ge>m. P n\<close>
  by auto

lemma Ball_atLeastLessThan_iff: \<open>(\<forall>L\<in>{a..<b}. P L) \<longleftrightarrow> (\<forall>L. L \<ge> a \<and> L < b \<longrightarrow> P L) \<close>
  unfolding set_nths by auto

lemma nth_in_set_tl: \<open>i > 0 \<Longrightarrow> i < length xs \<Longrightarrow> xs ! i \<in> set (tl xs)\<close>
  by (cases xs) auto

lemma tl_drop_def: \<open>tl N = drop 1 N\<close>
  by (cases N) auto

lemma in_set_remove1D:
  \<open>a \<in> set (remove1 x xs) \<Longrightarrow> a \<in> set xs\<close>
  by (meson notin_set_remove1)

lemma take_length_takeWhile_eq_takeWhile:
  \<open>take (length (takeWhile P xs)) xs = takeWhile P xs\<close>
  by (induction xs) auto

lemma fold_cons_replicate: \<open>fold (\<lambda>_ xs. a # xs) [0..<n] xs = replicate n a @ xs\<close>
  by (induction n) auto

lemma Collect_minus_single_Collect: \<open>{x. P x} - {a} = {x . P x \<and> x \<noteq> a}\<close>
  by auto

lemma in_set_image_subsetD: \<open> f ` A \<subseteq> B \<Longrightarrow> x \<in> A \<Longrightarrow>f x \<in> B\<close>
  by blast

text \<open>
  This lemma is not general enough to move to Isabelle, but might be interesting in other
  cases.\<close>
lemma set_Collect_Pair_to_fst_snd:
  \<open>{((a, b), (a', b')). P a b a' b'} = {(e, f). P (fst e) (snd e) (fst f) (snd f)}\<close>
  by auto

subsection \<open>Update\<close>


lemma tl_update_swap:
  \<open>i \<ge> 1 \<Longrightarrow> tl (N[i := C]) = tl N[i-1 := C]\<close>
  by (auto simp:  drop_Suc[of 0, symmetric, simplified] drop_update_swap)

lemma tl_update_0[simp]: \<open>tl (N[0 := x]) = tl N\<close>
  by (cases N) auto

declare nth_list_update[simp]
text \<open>
  This a version of @{thm nth_list_update} with a different condition (\<^term>\<open>j\<close>
  instead of \<^term>\<open>i\<close>). This is more useful in some cases.
  \<close>
lemma nth_list_update_le'[simp]:
  "j < length xs \<Longrightarrow> (xs[i:=x])!j = (if i = j then x else xs!j)"
  by (induct xs arbitrary: i j) (auto simp add: nth_Cons split: nat.split)


subsection \<open>Take and drop\<close>

lemma take_2_if:
  \<open>take 2 C = (if C = [] then [] else if length C = 1 then [hd C] else [C!0, C!1])\<close>
  by (cases C; cases \<open>tl C\<close>) auto


lemma in_set_take_conv_nth:
  \<open>x \<in> set (take n xs) \<longleftrightarrow> (\<exists>m<min n (length xs). xs ! m = x)\<close>
  by (metis in_set_conv_nth length_take min.commute min.strict_boundedE nth_take)

text \<open>Taken from \<^file>\<open>~~/src/HOL/Word/Word.thy\<close>\<close>
lemma atd_lem: \<open>take n xs = t \<Longrightarrow> drop n xs = d \<Longrightarrow> xs = t @ d\<close>
  by (auto intro: append_take_drop_id [symmetric])

lemma drop_take_drop_drop:
  \<open>j \<ge> i \<Longrightarrow> drop i xs = take (j - i) (drop i xs) @ drop j xs\<close>
  apply (induction \<open>j - i\<close> arbitrary: j i)
  subgoal by auto
  subgoal by (auto simp add: atd_lem)
  done

lemma in_set_conv_iff:
  \<open>x \<in> set (take n xs) \<longleftrightarrow> (\<exists>i < n. i < length xs \<and> xs ! i = x)\<close>
  apply (induction n)
  subgoal by auto
  subgoal for n
    apply (cases \<open>Suc n < length xs\<close>)
    subgoal by (auto simp: take_Suc_conv_app_nth less_Suc_eq dest: in_set_takeD)
    subgoal
      apply (cases \<open>n < length xs\<close>)
      subgoal
        apply (auto simp: in_set_conv_nth)
        by (rule_tac x=i in exI; auto; fail)+
      subgoal
        apply (auto simp: take_Suc_conv_app_nth dest: in_set_takeD)
        by (rule_tac x=i in exI; auto; fail)+
      done
    done
  done

lemma distinct_in_set_take_iff:
  \<open>distinct D \<Longrightarrow> b < length D \<Longrightarrow> D ! b \<in> set (take a D) \<longleftrightarrow> b < a\<close>
  apply (induction a arbitrary: b)
  subgoal by simp
  subgoal for a
    by (cases \<open>Suc a < length D\<close>)
      (auto simp: take_Suc_conv_app_nth nth_eq_iff_index_eq)
  done

lemma in_set_distinct_take_drop_iff:
  assumes
    \<open>distinct D\<close> and
    \<open>b < length D\<close>
  shows \<open>D ! b \<in> set (take (a - init) (drop init D)) \<longleftrightarrow> (init \<le> b \<and> b < a)\<close>
  using assms apply (auto 5 5 simp: distinct_in_set_take_iff in_set_conv_iff
      nth_eq_iff_index_eq dest: in_set_takeD)
  by (metis add_diff_cancel_left' diff_less_mono le_iff_add less_imp_le_nat nth_drop)


subsection \<open>Replicate\<close>

lemma list_eq_replicate_iff_nempty:
  \<open>n > 0 \<Longrightarrow> xs = replicate n x \<longleftrightarrow> n = length xs \<and> set xs = {x}\<close>
  by (metis length_replicate neq0_conv replicate_length_same set_replicate singletonD)

lemma list_eq_replicate_iff:
  \<open>xs = replicate n x \<longleftrightarrow> (n = 0 \<and> xs = []) \<or> (n = length xs \<and> set xs = {x})\<close>
  by (cases n) (auto simp: list_eq_replicate_iff_nempty simp del: replicate.simps)


subsection \<open>@{term upt}\<close>

text \<open>
  The simplification rules are not very handy, because theorem @{thm [source] upt.simps(2)}
  (i.e.\ @{thm upt.simps(2)}) leads to a case distinction, that we usually do not want if the
  condition is not already in the context.
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

lemma nths_upt_upto_Suc: \<open>aa < length xs \<Longrightarrow> nths xs {0..<Suc aa} = nths xs {0..<aa} @ [xs ! aa]\<close>
  by (simp add: atLeast0LessThan take_Suc_conv_app_nth)


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
proof -
  have H: \<open>finite {xs. set xs \<subseteq> {0..<b} \<and> length xs \<le> s}\<close>
    by (rule finite_lists_length_le[of \<open>{0..<b}\<close> \<open>s\<close>]) auto
  show ?thesis
    by (rule finite_subset[OF _ H]) (auto simp: in_set_conv_nth)
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

lemma last_list_update_to_last:
  \<open>last (xs[x := last xs]) = last xs\<close>
  by (metis last_list_update list_update.simps(1))

lemma take_map_nth_alt_def: \<open>take n xs = map ((!) xs) [0..<min n (length xs)]\<close>
proof (induction xs rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xs) note IH = this
  show ?case
  proof (cases \<open>n < length (xs @ [x])\<close>)
    case True
    then show ?thesis
      using IH by (auto simp: min_def nth_append)
  next
    case False
    have [simp]:
      \<open>map (\<lambda>a. if a < length xs then xs ! a else [x] ! (a - length xs)) [0..<length xs] =
       map (\<lambda>a. xs ! a) [0..<length xs]\<close> for xs x
     by (rule map_cong) auto
    show ?thesis
      using IH False by (auto simp: nth_append min_def)
  qed
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
  There is some subtle point in the previous theorem explaining \<^emph>\<open>why\<close> it is useful. The term
  @{term \<open>1::nat\<close>} is converted to @{term \<open>Suc 0::nat\<close>}, but @{term \<open>2::nat\<close>} is not, meaning
  that @{term \<open>1::nat\<close>} is automatically simplified by default allowing the use of the default
  simplification rule @{thm [source] lexn.simps}. However, for 2 one additional simplification rule
  is required (see the proof of the theorem above).
\<close>

lemma lexn2_conv:
  \<open>([a, b], [c, d]) \<in> lexn r 2 \<longleftrightarrow> (a, c) \<in> r \<or> (a = c \<and> (b, d) \<in>r)\<close>
  by (auto simp: lexn_n simp del: lexn.simps(2))

lemma lexn3_conv:
  \<open>([a, b, c], [a', b', c']) \<in> lexn r 3 \<longleftrightarrow>
    (a, a') \<in> r \<or> (a = a' \<and> (b, b') \<in> r) \<or> (a = a' \<and> b = b' \<and> (c, c') \<in> r)\<close>
  by (auto simp: lexn_n simp del: lexn.simps(2))

lemma prepend_same_lexn:
  assumes irrefl: \<open>irrefl R\<close>
  shows \<open>(A @ B, A @ C) \<in> lexn R n \<longleftrightarrow> (B, C) \<in> lexn R (n - length A)\<close> (is \<open>?A \<longleftrightarrow> ?B\<close>)
proof
  assume ?A
  then obtain xys x xs y ys where
    len_B: \<open>length B = n - length A\<close> and
    len_C: \<open>length C = n - length A\<close> and
    AB: \<open>A @ B = xys @ x # xs\<close> and
    AC: \<open>A @ C = xys @ y # ys\<close> and
    xy: \<open>(x, y) \<in> R\<close>
    by (auto simp: lexn_conv)
  have x_neq_y: \<open>x \<noteq> y\<close>
    using xy irrefl by (auto simp add: irrefl_def)
  then have \<open>B = drop (length A) xys @ x # xs\<close>
    using arg_cong[OF AB, of \<open>drop (length A)\<close>]
    apply (cases \<open>length A - length xys\<close>)
     apply (auto; fail)
    by (metis AB AC nth_append nth_append_length zero_less_Suc zero_less_diff)

  moreover have \<open>C = drop (length A) xys @ y # ys\<close>
    using arg_cong[OF AC, of \<open>drop (length A)\<close>] x_neq_y
    apply (cases \<open>length A - length xys\<close>)
     apply (auto; fail)
    by (metis AB AC nth_append nth_append_length zero_less_Suc zero_less_diff)
  ultimately show ?B
    using len_B[symmetric] len_C[symmetric] xy
    by (auto simp: lexn_conv)
next
  assume ?B
  then obtain xys x xs y ys where
    len_B: \<open>length B = n - length A\<close> and
    len_C: \<open>length C = n - length A\<close> and
    AB: \<open>B = xys @ x # xs\<close> and
    AC: \<open>C = xys @ y # ys\<close> and
    xy: \<open>(x, y) \<in> R\<close>
    by (auto simp: lexn_conv)
  define Axys where \<open>Axys = A @ xys\<close>

  have \<open>A @ B = Axys @ x # xs\<close>
    using AB Axys_def by auto

  moreover have \<open>A @ C = Axys @ y # ys\<close>
    using AC Axys_def by auto
  moreover have \<open>Suc (length Axys + length xs) = n\<close> and
    \<open>length ys = length xs\<close>
    using len_B len_C AB AC Axys_def by auto
  ultimately show ?A
    using len_B[symmetric] len_C[symmetric] xy
    by (auto simp: lexn_conv)
qed

lemma append_same_lexn:
  assumes irrefl: \<open>irrefl R\<close>
  shows \<open>(B @ A , C @ A) \<in> lexn R n \<longleftrightarrow> (B, C) \<in> lexn R (n - length A)\<close> (is \<open>?A \<longleftrightarrow> ?B\<close>)
proof
  assume ?A
  then obtain xys x xs y ys where
    len_B: \<open>n = length B + length A\<close> and
    len_C: \<open>n = length C + length A\<close> and
    AB: \<open>B @ A = xys @ x # xs\<close> and
    AC: \<open>C @ A = xys @ y # ys\<close> and
    xy: \<open>(x, y) \<in> R\<close>
    by (auto simp: lexn_conv)
  have x_neq_y: \<open>x \<noteq> y\<close>
    using xy irrefl by (auto simp add: irrefl_def)
  have len_C_B: \<open>length C = length B\<close>
    using len_B len_C by simp
  have len_B_xys: \<open>length B > length xys\<close>
    apply (rule ccontr)
    using arg_cong[OF AB, of \<open>take (length B)\<close>] arg_cong[OF AB, of \<open>drop (length B)\<close>]
      arg_cong[OF AC, of \<open>drop (length C)\<close>]  x_neq_y len_C_B
    by auto

  then have B: \<open>B = xys @ x # take (length B - Suc (length xys)) xs\<close>
    using arg_cong[OF AB, of \<open>take (length B)\<close>]
    by (cases \<open>length B - length xys\<close>) simp_all

  have C: \<open>C = xys @ y # take (length C - Suc (length xys)) ys\<close>
    using arg_cong[OF AC, of \<open>take (length C)\<close>] x_neq_y len_B_xys unfolding len_C_B[symmetric]
    by (cases \<open>length C - length xys\<close>)  auto
  show ?B
    using len_B[symmetric] len_C[symmetric] xy B C
    by (auto simp: lexn_conv)
next
  assume ?B
  then obtain xys x xs y ys where
    len_B: \<open>length B = n - length A\<close> and
    len_C: \<open>length C = n - length A\<close> and
    AB: \<open>B = xys @ x # xs\<close> and
    AC: \<open>C = xys @ y # ys\<close> and
    xy: \<open>(x, y) \<in> R\<close>
    by (auto simp: lexn_conv)
  define Ays Axs where \<open>Ays = ys @ A\<close> and\<open>Axs = xs @ A\<close>

  have \<open>B @ A = xys @ x # Axs\<close>
    using AB Axs_def by auto

  moreover have \<open>C @ A = xys @ y # Ays\<close>
    using AC Ays_def by auto
  moreover have \<open>Suc (length xys + length Axs) = n\<close> and
    \<open>length Ays = length Axs\<close>
    using len_B len_C AB AC Axs_def Ays_def by auto
  ultimately show ?A
    using len_B[symmetric] len_C[symmetric] xy
    by (auto simp: lexn_conv)
qed

lemma irrefl_less_than [simp]: \<open>irrefl less_than\<close>
  by (auto simp: irrefl_def)


subsection \<open>Remove\<close>

subsubsection \<open>More lemmas about remove\<close>

lemma distinct_remove1_last_butlast:
  \<open>distinct xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> remove1 (last xs) xs = butlast xs\<close>
  by (metis append_Nil2 append_butlast_last_id distinct_butlast not_distinct_conv_prefix
      remove1.simps(2) remove1_append)

lemma remove1_Nil_iff:
  \<open>remove1 x xs = [] \<longleftrightarrow> xs = [] \<or> xs = [x]\<close>
  by (cases xs) auto

lemma removeAll_upt:
  \<open>removeAll k [a..<b] = (if k \<ge> a \<and> k < b then [a..<k] @ [Suc k..<b] else [a..<b])\<close>
  by (induction b) auto

lemma remove1_upt:
  \<open>remove1 k [a..<b] = (if k \<ge> a \<and> k < b then [a..<k] @ [Suc k..<b] else [a..<b])\<close>
  by (subst distinct_remove1_removeAll) (auto simp: removeAll_upt)

lemma sorted_removeAll: \<open>sorted C \<Longrightarrow> sorted (removeAll k C)\<close>
  by (metis map_ident removeAll_filter_not_eq sorted_filter)

lemma distinct_remove1_rev: \<open>distinct xs \<Longrightarrow> remove1 x (rev xs) = rev (remove1 x xs)\<close>
  using split_list[of x xs]
  by (cases \<open>x \<in> set xs\<close>) (auto simp: remove1_append remove1_idem)


subsubsection \<open>Remove under condition\<close>

text \<open>This function removes the first element such that the condition @{term f} holds. It
  generalises @{term List.remove1}.\<close>
fun remove1_cond where
\<open>remove1_cond f [] = []\<close> |
\<open>remove1_cond f (C' # L) = (if f C' then L else C' # remove1_cond f L)\<close>

lemma \<open>remove1 x xs = remove1_cond ((=) x) xs\<close>
  by (induction xs) auto

lemma mset_map_mset_remove1_cond:
  \<open>mset (map mset (remove1_cond (\<lambda>L. mset L = mset a) C)) =
    remove1_mset (mset a) (mset (map mset C))\<close>
  by (induction C) auto

text \<open>We can also generalise @{term List.removeAll}, which is close to @{term List.filter}:\<close>
fun removeAll_cond :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> where
\<open>removeAll_cond f [] = []\<close> |
\<open>removeAll_cond f (C' # L) = (if f C' then removeAll_cond f L else C' # removeAll_cond f L)\<close>

lemma \<open>removeAll x xs = removeAll_cond ((=) x) xs\<close>
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
  \<open>distinct C \<Longrightarrow> length (filter ((=) L) C) = (if L \<in> set C then 1 else 0)\<close>
  by (induction C) auto

lemma length_filter_update_true:
  assumes \<open>i < length xs\<close> and \<open>P (xs ! i)\<close>
  shows \<open>length (filter P (xs[i := x])) = length (filter P xs) - (if P x then 0 else 1)\<close>
  apply (subst (5) append_take_drop_id[of i, symmetric])
  using assms upd_conv_take_nth_drop[of i xs x] Cons_nth_drop_Suc[of i xs, symmetric]
  unfolding filter_append length_append
  by simp

lemma length_filter_update_false:
  assumes \<open>i < length xs\<close> and \<open>\<not>P (xs ! i)\<close>
  shows \<open>length (filter P (xs[i := x])) = length (filter P xs) + (if P x then 1 else 0)\<close>
  apply (subst (5) append_take_drop_id[of i, symmetric])
  using assms upd_conv_take_nth_drop[of i xs x] Cons_nth_drop_Suc[of i xs, symmetric]
  unfolding filter_append length_append
  by simp

lemma mset_set_mset_set_minus_id_iff:
  assumes \<open>finite A\<close>
  shows \<open>mset_set A = mset_set (A - B) \<longleftrightarrow> (\<forall>b \<in> B. b \<notin> A)\<close>
proof -
 have f1: "mset_set A = mset_set (A - B) \<longleftrightarrow> A - B = A"
    using assms by (metis (no_types) finite_Diff finite_set_mset_mset_set)
  then show ?thesis
    by blast
qed

lemma mset_set_eq_mset_set_more_conds:
  \<open>finite {x. P x} \<Longrightarrow> mset_set {x. P x} = mset_set {x. Q x \<and> P x} \<longleftrightarrow> (\<forall>x. P x \<longrightarrow> Q x)\<close>
  (is \<open>?F \<Longrightarrow> ?A \<longleftrightarrow> ?B\<close>)
proof -
  assume ?F
  then have \<open>?A \<longleftrightarrow> (\<forall>x \<in> {x. P x}. x \<in> {x. Q x \<and> P x})\<close>
    by (subst mset_set_eq_iff) auto
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>x. P x \<longrightarrow> Q x)\<close>
    by blast
  finally show ?thesis .
qed

lemma count_list_filter: \<open>count_list xs x = length (filter ((=) x) xs)\<close>
  by (induction xs) auto

lemma sum_length_filter_compl': \<open>length [x\<leftarrow>xs . \<not> P x] + length (filter P xs) = length xs\<close>
  using sum_length_filter_compl[of P xs] by auto


subsection \<open>Multisets\<close>

notation image_mset (infixr "`#" 90)

lemma in_multiset_nempty: \<open>L \<in># D \<Longrightarrow> D \<noteq> {#}\<close>
  by auto

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

lemma union_mset_list_Nil[simp]: \<open>union_mset_list [] bi = bi\<close>
  by (auto simp: union_mset_list_def)

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


lemma butlast_list_update:
  \<open>w < length xs \<Longrightarrow> butlast (xs[w := last xs]) = take w xs @ butlast (last xs # drop (Suc w) xs)\<close>
  by (induction xs arbitrary: w) (auto split: nat.splits if_splits simp: upd_conv_take_nth_drop)

lemma mset_butlast_remove1_mset: \<open>xs \<noteq> [] \<Longrightarrow> mset (butlast xs) = remove1_mset (last xs) (mset xs)\<close>
  apply (subst(2) append_butlast_last_id[of xs, symmetric])
   apply assumption
  apply (simp only: mset_append)
  by auto

lemma distinct_mset_mono: \<open>D' \<subseteq># D \<Longrightarrow> distinct_mset D \<Longrightarrow> distinct_mset D'\<close>
  by (metis distinct_mset_union subset_mset.le_iff_add)

lemma subset_mset_trans_add_mset:
  \<open>D \<subseteq># D' \<Longrightarrow> D \<subseteq># add_mset L D'\<close>
  by (metis add_mset_remove_trivial diff_subset_eq_self subset_mset.dual_order.trans)

lemma remove1_mset_empty_iff: \<open>remove1_mset L N = {#} \<longleftrightarrow> N = {#L#} \<or> N = {#}\<close>
  by (cases \<open>L \<in># N\<close>; cases N) auto

lemma distinct_subseteq_iff :
  assumes dist: "distinct_mset M" and fin: "distinct_mset N"
  shows "set_mset M \<subseteq> set_mset N \<longleftrightarrow> M \<subseteq># N"
proof
  assume "set_mset M \<subseteq> set_mset N"
  then show "M \<subseteq># N"
    using dist fin by auto
next
  assume "M \<subseteq># N"
  then show "set_mset M \<subseteq> set_mset N"
    by (metis set_mset_mono)
qed

lemma in_remove1_msetI: \<open>x \<noteq> a \<Longrightarrow> x \<in># M \<Longrightarrow> x \<in># remove1_mset a M\<close>
  by (simp add: in_remove1_mset_neq)

lemma count_multi_member_split:
   \<open>count M a \<ge> n \<Longrightarrow> \<exists>M'. M = replicate_mset n a + M'\<close>
  apply (induction n arbitrary: M)
  subgoal by auto
  subgoal premises IH for n M
    using IH(1)[of \<open>remove1_mset a M\<close>] IH(2)
    apply (cases \<open>n \<le> count M a - Suc 0\<close>)
     apply (auto dest!: Suc_le_D)
    by (metis count_greater_zero_iff insert_DiffM zero_less_Suc)
  done

lemma count_image_mset_multi_member_split:
  \<open>count (image_mset f M) L \<ge> Suc 0 \<Longrightarrow>  \<exists>K. f K = L \<and> K \<in># M\<close>
  by auto

lemma count_image_mset_multi_member_split_2:
  assumes count: \<open>count (image_mset f M) L \<ge> 2\<close>
  shows \<open>\<exists>K K' M'. f K = L \<and> K \<in># M \<and> f K' = L \<and> K' \<in># remove1_mset K M \<and>
       M = {#K, K'#} + M'\<close>
proof -
  obtain K where
    K: \<open>f K = L\<close> \<open>K \<in># M\<close>
    using count_image_mset_multi_member_split[of f M L] count by fastforce
  then obtain K' where
    K': \<open>f K' = L\<close> \<open>K' \<in># remove1_mset K M\<close>
    using count_image_mset_multi_member_split[of f \<open>remove1_mset K M\<close> L] count
    by (auto dest!: multi_member_split)
  moreover have \<open>\<exists>M'. M = {#K, K'#} + M'\<close>
    using multi_member_split[of K M] multi_member_split[of K' \<open>remove1_mset K M\<close>] K K'
    by (auto dest!: multi_member_split)
  then show ?thesis
    using K K' by blast
qed

lemma minus_notin_trivial: "L \<notin># A \<Longrightarrow> A - add_mset L B = A - B"
  by (metis diff_intersect_left_idem inter_add_right1)

lemma minus_notin_trivial2: \<open>b \<notin># A \<Longrightarrow> A - add_mset e (add_mset b B) = A - add_mset e B\<close>
  by (subst add_mset_commute) (auto simp: minus_notin_trivial)

lemma diff_union_single_conv3: \<open>a \<notin># I \<Longrightarrow> remove1_mset a (I + J) = I + remove1_mset a J\<close>
  by (metis diff_union_single_conv remove_1_mset_id_iff_notin union_iff)

lemma filter_union_or_split:
  \<open>{#L \<in># C. P L \<or> Q L#} = {#L \<in># C. P L#} + {#L \<in># C. \<not>P L \<and> Q L#}\<close>
  by (induction C) auto

lemma subset_mset_minus_eq_add_mset_noteq: \<open>A \<subset># C \<Longrightarrow> A - B \<noteq> C\<close>
  by (auto simp: dest: in_diffD)

lemma minus_eq_id_forall_notin_mset:
  \<open>A - B = A \<longleftrightarrow> (\<forall>L \<in># B. L \<notin># A)\<close>
  by (induction A)
   (auto dest!: multi_member_split simp: subset_mset_minus_eq_add_mset_noteq)

lemma in_multiset_minus_notin_snd[simp]: \<open>a \<notin># B \<Longrightarrow> a \<in># A - B \<longleftrightarrow> a \<in># A\<close>
  by (metis count_greater_zero_iff count_inI in_diff_count)

lemma distinct_mset_in_diff:
  \<open>distinct_mset C \<Longrightarrow> a \<in># C - D \<longleftrightarrow> a \<in># C \<and> a \<notin># D\<close>
  by (meson distinct_mem_diff_mset in_multiset_minus_notin_snd)

lemma diff_le_mono2_mset: \<open>A \<subseteq># B \<Longrightarrow> C - B \<subseteq># C - A\<close>
  apply (auto simp: subseteq_mset_def ac_simps)
  by (simp add: diff_le_mono2)

lemma subseteq_remove1[simp]: \<open>C \<subseteq># C' \<Longrightarrow> remove1_mset L C \<subseteq># C'\<close>
  by (meson diff_subset_eq_self subset_mset.dual_order.trans)

lemma filter_mset_cong2:
  "(\<And>x. x \<in># M \<Longrightarrow> f x = g x) \<Longrightarrow> M = N \<Longrightarrow> filter_mset f M = filter_mset g N"
  by (hypsubst, rule filter_mset_cong, simp)

lemma filter_mset_cong_inner_outer:
  assumes
     M_eq: \<open>(\<And>x. x \<in># M \<Longrightarrow> f x = g x)\<close> and
     notin: \<open>(\<And>x. x \<in># N - M \<Longrightarrow> \<not>g x)\<close> and
     MN: \<open>M \<subseteq># N\<close>
  shows \<open>filter_mset f M = filter_mset g N\<close>
proof -
  define NM where \<open>NM = N - M\<close>
  have N: \<open>N = M + NM\<close>
    unfolding NM_def using MN by simp
  have \<open>filter_mset g NM = {#}\<close>
    using notin unfolding NM_def[symmetric] by (auto simp: filter_mset_empty_conv)
  moreover have \<open>filter_mset f M = filter_mset g M\<close>
    by (rule filter_mset_cong) (use M_eq in auto)
  ultimately show ?thesis
    unfolding N by simp
qed

lemma notin_filter_mset:
  \<open>K \<notin># C \<Longrightarrow> filter_mset P C = filter_mset (\<lambda>L. P L \<and> L \<noteq> K) C\<close>
  by (rule filter_mset_cong) auto

lemma distinct_mset_add_mset_filter:
  assumes \<open>distinct_mset C\<close> and \<open>L \<in># C\<close> and \<open>\<not>P L\<close>
  shows \<open>add_mset L (filter_mset P C) = filter_mset (\<lambda>x. P x \<or> x = L) C\<close>
  using assms
proof (induction C)
  case empty
  then show ?case by simp
next
  case (add x C) note dist = this(2) and LC = this(3) and P[simp] = this(4) and _ = this
  then have IH: \<open>L \<in># C \<Longrightarrow> add_mset L (filter_mset P C) = {#x \<in># C. P x \<or> x = L#}\<close> by auto
  show ?case
  proof (cases \<open>x = L\<close>)
    case [simp]: True
    have \<open>filter_mset P C = {#x \<in># C. P x \<or> x = L#}\<close>
      by (rule filter_mset_cong2) (use dist in auto)
    then show ?thesis
      by auto
  next
    case False
    then show ?thesis
      using IH LC by auto
  qed
qed

lemma set_mset_set_mset_eq_iff: \<open>set_mset A = set_mset B \<longleftrightarrow> (\<forall>a\<in>#A. a \<in># B) \<and> (\<forall>a\<in>#B. a \<in># A)\<close>
  by blast

lemma remove1_mset_union_distrib:
  \<open>remove1_mset a (M \<union># N) = remove1_mset a M \<union># remove1_mset a N\<close>
  by (auto simp: multiset_eq_iff)

(* useful for sledgehammer/proof reconstruction ?*)
lemma member_add_mset: \<open>a \<in># add_mset x xs \<longleftrightarrow> a = x \<or> a \<in># xs\<close>
  by simp

lemma sup_union_right_if:
  \<open>N \<union># add_mset x M =
     (if x \<notin># N then add_mset x (N \<union># M) else add_mset x (remove1_mset x N \<union># M))\<close>
  by (auto simp: sup_union_right2)

lemma same_mset_distinct_iff:
  \<open>mset M = mset M' \<Longrightarrow> distinct M \<longleftrightarrow> distinct M'\<close>
  by (auto simp: distinct_mset_mset_distinct[symmetric] simp del: distinct_mset_mset_distinct)

lemma inj_on_image_mset_eq_iff:
  assumes inj: \<open>inj_on f (set_mset (M + M'))\<close>
  shows \<open>image_mset f M' = image_mset f M \<longleftrightarrow> M' = M\<close> (is \<open>?A = ?B\<close>)
proof
  assume ?B
  then show ?A by auto
next
  assume ?A
  then show ?B
    using inj
  proof(induction M arbitrary: M')
    case empty
    then show ?case by auto
  next
    case (add x M) note IH = this(1) and H = this(2) and inj = this(3)

    obtain M1 x' where
      M': \<open>M' = add_mset x' M1\<close> and
      f_xx': \<open>f x' = f x\<close> and
      M1_M: \<open>image_mset f M1 = image_mset f M\<close>
      using H by (auto dest!: msed_map_invR)
    moreover have \<open>M1 = M\<close>
      apply (rule IH[OF M1_M])
      using inj by (auto simp: M')
    moreover have \<open>x = x'\<close>
      using inj f_xx' by (auto simp: M')
    ultimately show ?case by fast
  qed
qed

lemma inj_image_mset_eq_iff:
  assumes inj: \<open>inj f\<close>
  shows \<open>image_mset f M' = image_mset f M \<longleftrightarrow> M' = M\<close>
  using inj_on_image_mset_eq_iff[of f M' M] assms
  by (simp add: inj_eq multiset.inj_map)

lemma singleton_eq_image_mset_iff:  \<open>{#a#} = f `# NE' \<longleftrightarrow> (\<exists>b. NE' = {#b#} \<and> f b = a)\<close>
  by (cases NE') auto

lemma image_mset_If_eq_notin:
   \<open>C \<notin># A \<Longrightarrow> {#f (if x = C then a x else b x). x \<in># A#} = {# f(b x). x \<in># A #}\<close>
  by (induction A) auto

lemma finite_mset_set_inter:
  \<open>finite A \<Longrightarrow> finite B \<Longrightarrow> mset_set (A \<inter> B) = mset_set A \<inter># mset_set B\<close>
  apply (induction A rule: finite_induct)
  subgoal by auto
  subgoal for a A
    apply (cases \<open>a \<in> B\<close>; cases \<open>a \<in># mset_set B\<close>)
    using multi_member_split[of a \<open>mset_set B\<close>]
    by (auto simp: mset_set.insert_remove)
  done

lemma distinct_mset_inter_remdups_mset:
  assumes dist: \<open>distinct_mset A\<close>
  shows \<open>A \<inter># remdups_mset B = A \<inter># B\<close>
proof -
  have [simp]: \<open>A' \<inter># remove1_mset a (remdups_mset Aa) = A' \<inter># Aa\<close>
    if
      \<open>A' \<inter># remdups_mset Aa = A' \<inter># Aa\<close> and
      \<open>a \<notin># A'\<close> and
      \<open>a \<in># Aa\<close>
    for A' Aa :: \<open>'a multiset\<close> and a
  by (metis insert_DiffM inter_add_right1 set_mset_remdups_mset that)

  show ?thesis
    using dist
    apply (induction A)
    subgoal by auto
     subgoal for a A'
      apply (cases \<open>a \<in># B\<close>)
      using multi_member_split[of a \<open>B\<close>]  multi_member_split[of a \<open>A\<close>]
      by (auto simp: mset_set.insert_remove)
    done
qed

lemma mset_butlast_update_last[simp]:
  \<open>w < length xs \<Longrightarrow> mset (butlast (xs[w := last (xs)])) = remove1_mset (xs ! w) (mset xs)\<close>
  by (cases \<open>xs = []\<close>)
    (auto simp add: last_list_update_to_last mset_butlast_remove1_mset mset_update)

lemma in_multiset_ge_Max: \<open>a \<in># N \<Longrightarrow> a > Max (insert 0 (set_mset N)) \<Longrightarrow> False\<close>
  by (simp add: leD)

lemma distinct_mset_set_mset_remove1_mset:
  \<open>distinct_mset M \<Longrightarrow> set_mset (remove1_mset c M) = set_mset M - {c}\<close>
  by (cases \<open>c \<in># M\<close>) (auto dest!: multi_member_split simp: add_mset_eq_add_mset)


subsection \<open>Sorting\<close>

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
   apply (simp; fail)
  apply (case_tac \<open>\<not>k < a \<and> k < Suc b\<close>)
   apply (rule sorted_mset_unique)
      apply ((auto simp add: sorted_append sorted_insort ac_simps mset_set_Union
        dest!: H; fail)+)[2]
    apply (auto simp: insort_is_Cons sorted_insort_is_snoc sorted_append mset_set_Union
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

lemma distinct_mset_remdups_mset_id: \<open>distinct_mset C \<Longrightarrow> remdups_mset C = C\<close>
  by (induction C)  auto

lemma notin_add_mset_remdups_mset:
  \<open>a \<notin># A \<Longrightarrow> add_mset a (remdups_mset A) = remdups_mset (add_mset a A)\<close>
  by auto


subsection \<open>Sublists\<close>

lemma nths_single_if: \<open>nths l {n} = (if n < length l then [l!n] else [])\<close>
proof -
  have [simp]: \<open>0 < n \<Longrightarrow> {j. Suc j = n} = {n-1}\<close> for n
    by auto
  show ?thesis
    apply (induction l arbitrary: n)
    subgoal by (auto simp: nths_def)
    subgoal by (auto simp: nths_Cons)
    done
qed

lemma atLeastLessThan_Collect: \<open>{a..<b} = {j. j \<ge> a \<and> j < b}\<close>
  by auto

lemma mset_nths_subset_mset: \<open>mset (nths xs A) \<subseteq># mset xs\<close>
  apply (induction xs arbitrary: A)
  subgoal by auto
  subgoal for a xs A
    using subset_mset.add_increasing2[of \<open>add_mset _ {#}\<close> \<open>mset (nths xs {j. Suc j \<in> A})\<close>
      \<open>mset xs\<close>]
    by (auto simp: nths_Cons)
  done

lemma nths_id_iff:
  \<open>nths xs A = xs \<longleftrightarrow> {0..<length xs} \<subseteq> A \<close>
proof -
  have \<open>{j. Suc j \<in> A} =  (\<lambda>j. j-1) ` (A - {0})\<close> for A
    using DiffI by (fastforce simp: image_iff)
  have 1: \<open>{0..<b} \<subseteq> {j. Suc j \<in> A} \<longleftrightarrow> (\<forall>x. x-1 < b \<longrightarrow> x \<noteq> 0 \<longrightarrow> x \<in> A)\<close>
    for A :: \<open>nat set\<close> and b :: nat
    by auto
  have [simp]: \<open>{0..<b} \<subseteq> {j. Suc j \<in> A} \<longleftrightarrow> (\<forall>x. x-1 < b \<longrightarrow> x \<in> A)\<close>
    if \<open>0 \<in> A\<close> for A :: \<open>nat set\<close> and b :: nat
    using that unfolding 1 by auto
  have [simp]: \<open>nths xs {j. Suc j \<in> A} = a # xs \<longleftrightarrow> False\<close>
    for a :: 'a and xs :: \<open>'a list\<close> and A :: \<open>nat set\<close>
    using mset_nths_subset_mset[of xs \<open>{j. Suc j \<in> A}\<close>] by auto
  show ?thesis
    apply (induction xs arbitrary: A)
    subgoal by auto
    subgoal
      by (auto 5 5 simp: nths_Cons) fastforce
    done
qed

lemma nts_upt_length[simp]: \<open>nths xs {0..<length xs} = xs\<close>
  by (auto simp: nths_id_iff)

lemma nths_shift_lemma':
  \<open>map fst [p\<leftarrow>zip xs [i..<i + n]. snd p + b \<in> A] = map fst [p\<leftarrow>zip xs [0..<n]. snd p + b + i \<in> A]\<close>
proof (induct xs arbitrary: i n b)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have 1: \<open>map fst [p\<leftarrow>zip (a # xs) (i # [Suc i..<i + n]). snd p + b \<in> A] =
     (if i + b \<in> A then a#map fst [p\<leftarrow>zip xs [Suc i..<i + n]. snd p + b \<in> A]
     else map fst [p\<leftarrow>zip xs [Suc i..<i + n]. snd p + b \<in>A])\<close>
    by simp
  have 2: \<open>map fst [p\<leftarrow>zip (a # xs) [0..<n] . snd p + b + i \<in> A] =
     (if i + b \<in> A then a # map fst [p\<leftarrow>zip xs [1..<n]. snd p + b + i \<in> A]
      else map fst [p\<leftarrow>zip (xs) [1..<n] . snd p + b + i \<in> A])\<close>
    if \<open>n > 0\<close>
    by (subst upt_conv_Cons) (use that in \<open>auto simp: ac_simps\<close>)
  show ?case
  proof (cases n)
    case 0
    then show ?thesis by simp
  next
    case n: (Suc m)
    then have i_n_m: \<open>i + n = Suc i + m\<close>
      by auto
    have 3: \<open>map fst [p\<leftarrow>zip xs [Suc i..<i+n] . snd p + b \<in> A] =
             map fst [p\<leftarrow>zip xs [0..<m] . snd p + b + Suc i \<in> A]\<close>
      using Cons[of b \<open>Suc i\<close> m] unfolding i_n_m .
    have 4: \<open>map fst [p\<leftarrow>zip xs [1..<n] . snd p + b + i \<in> A] =
                 map fst [p\<leftarrow>zip xs [0..<m] . Suc (snd p + b + i) \<in> A]\<close>
      using Cons[of \<open>b+i\<close> 1 m] unfolding n Suc_eq_plus1_left add.commute[of 1]
      by (simp_all add: ac_simps)
    show ?thesis
      apply (subst upt_conv_Cons)
      using n apply (simp; fail)
      apply (subst 1)
      apply (subst 2)
      using n apply (simp; fail)
      apply (subst 3)
      apply (subst 3)

      apply (subst 4)
      apply (subst 4)
      by force
  qed
qed

lemma nths_Cons_upt_Suc: \<open>nths (a # xs) {0..<Suc n} = a # nths xs {0..<n}\<close>
  unfolding nths_def
  apply (subst upt_conv_Cons)
   apply simp
  using nths_shift_lemma'[of 0 \<open>{0..<Suc n}\<close> \<open>xs\<close> 1 \<open>length xs\<close>]
  by (simp_all add: ac_simps)


lemma nths_empty_iff: \<open>nths xs A = [] \<longleftrightarrow> {..<length xs} \<inter> A = {}\<close>
proof (induction xs arbitrary: A)
  case Nil
  then show ?case by auto
next
  case (Cons a xs) note IH = this(1)
  have \<open>{..<length xs} \<inter> {j. Suc j \<in> A} = {} \<Longrightarrow> (\<forall>x<length xs. x \<noteq> 0 \<longrightarrow> x \<notin> A)\<close>
    apply auto
     apply (metis IntI empty_iff gr0_implies_Suc lessI lessThan_iff less_trans mem_Collect_eq)
    done
  show ?case
  proof (cases \<open>0 \<in> A\<close>)
    case True
    then show ?thesis by (subst nths_Cons) auto
  next
    case False
    then show ?thesis
      by (subst nths_Cons) (use less_Suc_eq_0_disj IH in auto)
  qed
qed

lemma nths_upt_Suc:
  assumes \<open>i < length xs\<close>
  shows \<open>nths xs {i..<length xs} = xs!i # nths xs {Suc i..<length xs}\<close>
proof -
  have upt: \<open>{i..<k} = {j. i \<le> j \<and> j < k}\<close> for i k :: nat
    by auto
  show ?thesis
    using assms
  proof (induction xs arbitrary: i)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs i) note IH = this(1) and i_le = this(2)
    have [simp]: \<open>i - Suc 0 \<le> j \<longleftrightarrow> i \<le> Suc j\<close> if \<open>i > 0\<close> for j
      using that by auto
    show ?case
      using IH[of \<open>i-1\<close>] i_le
      by (auto simp add: nths_Cons upt)
  qed
qed

lemma nths_upt_Suc':
  assumes \<open>i < b\<close> and \<open>b <= length xs\<close>
  shows \<open>nths xs {i..<b} = xs!i # nths xs {Suc i..<b}\<close>
proof -
  have S1: \<open>{j. i \<le> Suc j \<and> j < b - Suc 0}  = {j. i \<le> Suc j \<and> Suc j < b}\<close> for i b
    by auto
  have S2: \<open>{j. i \<le> j \<and> j < b - Suc 0}  = {j. i \<le> j \<and> Suc j < b}\<close> for i b
    by auto
  have upt: \<open>{i..<k} = {j. i \<le> j \<and> j < k}\<close> for i k :: nat
    by auto
  show ?thesis
    using assms
  proof (induction xs arbitrary: i b)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs i) note IH = this(1) and i_le = this(2,3)
    have [simp]: \<open>i - Suc 0 \<le> j \<longleftrightarrow> i \<le> Suc j\<close> if \<open>i > 0\<close> for j
      using that by auto
    have \<open>i - Suc 0 < b - Suc 0 \<or> (i = 0)\<close>
      using i_le by linarith
    moreover have \<open>b - Suc 0 \<le> length xs \<or> xs = []\<close>
      using i_le by auto
    ultimately show ?case
      using IH[of \<open>i-1\<close> \<open>b-1\<close>] i_le
      apply (subst nths_Cons)
      apply (subst nths_Cons)
      by (auto simp: upt S1 S2)
  qed
qed

lemma Ball_set_nths: \<open>(\<forall>L\<in>set (nths xs A). P L) \<longleftrightarrow> (\<forall>i \<in> A \<inter> {0..<length xs}. P (xs ! i)) \<close>
  unfolding set_nths by fastforce


subsection \<open>Product Case\<close>

text \<open>The splitting of tuples is done for sizes strictly less than 8. As we want to manipulate
  tuples of size 8, here is some more setup for larger sizes.\<close>

lemma prod_cases8 [cases type]:
  obtains (fields) a b c d e f g h where "y = (a, b, c, d, e, f, g, h)"
  by (cases y, cases \<open>snd y\<close>) auto

lemma prod_induct8 [case_names fields, induct type]:
  "(\<And>a b c d e f g h. P (a, b, c, d, e, f, g, h)) \<Longrightarrow> P x"
  by (cases x) blast

lemma prod_cases9 [cases type]:
  obtains (fields) a b c d e f g h i where "y = (a, b, c, d, e, f, g, h, i)"
  by (cases y, cases \<open>snd y\<close>) auto

lemma prod_induct9 [case_names fields, induct type]:
  "(\<And>a b c d e f g h i. P (a, b, c, d, e, f, g, h, i)) \<Longrightarrow> P x"
  by (cases x) blast

lemma prod_cases10 [cases type]:
  obtains (fields) a b c d e f g h i j where "y = (a, b, c, d, e, f, g, h, i, j)"
  by (cases y, cases \<open>snd y\<close>) auto

lemma prod_induct10 [case_names fields, induct type]:
  "(\<And>a b c d e f g h i j. P (a, b, c, d, e, f, g, h, i, j)) \<Longrightarrow> P x"
  by (cases x) blast

lemma prod_cases11 [cases type]:
  obtains (fields) a b c d e f g h i j k where "y = (a, b, c, d, e, f, g, h, i, j, k)"
  by (cases y, cases \<open>snd y\<close>) auto

lemma prod_induct11 [case_names fields, induct type]:
  "(\<And>a b c d e f g h i j k. P (a, b, c, d, e, f, g, h, i, j, k)) \<Longrightarrow> P x"
  by (cases x) blast

lemma prod_cases12 [cases type]:
  obtains (fields) a b c d e f g h i j k l where "y = (a, b, c, d, e, f, g, h, i, j, k, l)"
  by (cases y, cases \<open>snd y\<close>) auto

lemma prod_induct12 [case_names fields, induct type]:
  "(\<And>a b c d e f g h i j k l. P (a, b, c, d, e, f, g, h, i, j, k, l)) \<Longrightarrow> P x"
  by (cases x) blast


subsection \<open>More about @{term list_all2} and @{term map}\<close>

text \<open>
  More properties on the relator \<^term>\<open>list_all2\<close> and \<^term>\<open>map\<close>. These theorems are
  mostly used during the refinement and especially the lifting from a deterministic relator to
  its list version.
\<close>
lemma list_all2_op_eq_map_right_iff: \<open>list_all2 (\<lambda>L. (=) (f L)) a aa \<longleftrightarrow> aa = map f a \<close>
  apply (induction a arbitrary: aa)
   apply (auto; fail)
  by (rename_tac aa, case_tac aa) (auto)

lemma list_all2_op_eq_map_right_iff': \<open>list_all2 (\<lambda>L L'. L' = f L) a aa \<longleftrightarrow> aa = map f a\<close>
  apply (induction a arbitrary: aa)
   apply (auto; fail)
  by (rename_tac aa, case_tac aa) auto

lemma list_all2_op_eq_map_left_iff: \<open>list_all2 (\<lambda>L' L. L'  = (f L)) a aa \<longleftrightarrow> a = map f aa\<close>
  apply (induction a arbitrary: aa)
   apply (auto; fail)
  by (rename_tac aa, case_tac aa) (auto)

lemma list_all2_op_eq_map_map_right_iff:
  \<open>list_all2 (list_all2 (\<lambda>L. (=) (f L))) xs' x \<longleftrightarrow> x = map (map f) xs'\<close> for x
    apply (induction xs' arbitrary: x)
     apply (auto; fail)
    apply (case_tac x)
  by (auto simp: list_all2_op_eq_map_right_iff)

lemma list_all2_op_eq_map_map_left_iff:
  \<open>list_all2 (list_all2 (\<lambda>L' L. L' = f L)) xs' x \<longleftrightarrow> xs' = map (map f) x\<close>
    apply (induction xs' arbitrary: x)
     apply (auto; fail)
    apply (rename_tac x, case_tac x)
  by (auto simp: list_all2_op_eq_map_left_iff)

lemma list_all2_conj:
  \<open>list_all2 (\<lambda>x y. P x y \<and> Q x y) xs ys \<longleftrightarrow> list_all2 P xs ys \<and> list_all2 Q xs ys\<close>
  by (auto simp: list_all2_conv_all_nth)

lemma list_all2_replicate:
  \<open>(bi, b) \<in> R' \<Longrightarrow> list_all2 (\<lambda>x x'. (x, x') \<in> R') (replicate n bi) (replicate n b)\<close>
  by (induction n) auto


section \<open>Finite maps and multisets\<close>

text \<open>Roughly the same as \<^term>\<open>ran\<close>, but with duplication (unlike sets or finite sets) and
  it works only on finite domains (unlike a function mapping).\<close>
abbreviation mset_fset :: \<open>'a fset \<Rightarrow> 'a multiset\<close> where
  \<open>mset_fset N \<equiv> mset_set (fset N)\<close>

definition fset_mset :: \<open>'a multiset \<Rightarrow> 'a fset\<close> where
  \<open>fset_mset N \<equiv> Abs_fset (set_mset N)\<close>

lemma fset_mset_mset_fset: \<open>fset_mset (mset_fset N) = N\<close>
  by (auto simp: fset.fset_inverse fset_mset_def)

lemma mset_fset_fset_mset[simp]:
  \<open>mset_fset (fset_mset N) = remdups_mset N\<close>
  by (auto simp: fset.fset_inverse fset_mset_def Abs_fset_inverse remdups_mset_def)

lemma in_mset_fset_fmember[simp]: \<open>x \<in># mset_fset N \<longleftrightarrow> x |\<in>| N\<close>
  by (auto simp: fmember.rep_eq)

lemma in_fset_mset_mset[simp]: \<open>x |\<in>| fset_mset N \<longleftrightarrow> x \<in># N\<close>
  by (auto simp: fmember.rep_eq fset_mset_def Abs_fset_inverse)

definition dom_m where
  \<open>dom_m N = mset_fset (fmdom N)\<close>

definition ran_m where
  \<open>ran_m N =  the `# fmlookup N `# dom_m N\<close>

lemma dom_m_fmdrop[simp]: \<open>dom_m (fmdrop C N) = remove1_mset C (dom_m N)\<close>
  unfolding dom_m_def
  by (cases \<open>C |\<in>| fmdom N\<close>)
    (auto simp: mset_set.remove fmember.rep_eq)

lemma dom_m_fmupd[simp]: \<open>dom_m (fmupd k C N) = add_mset k (remove1_mset k (dom_m N))\<close>
  unfolding dom_m_def
  by (cases \<open>k |\<in>| fmdom N\<close>)
    (auto simp: mset_set.remove fmember.rep_eq mset_set.insert
    mset_set.insert_remove)

lemma (in -) fmupd_same[simp]:
  \<open>x1 \<in># dom_m x1aa \<Longrightarrow>  fmupd x1 (the (fmlookup x1aa x1)) x1aa = x1aa\<close>
  by (metis fmap_ext fmupd_lookup in_dom_m_lookup_iff option.collapse)

lemma distinct_mset_dom: \<open>distinct_mset (dom_m N)\<close>
  by (simp add: distinct_mset_mset_set dom_m_def)

lemma in_dom_m_lookup_iff: \<open>C \<in># dom_m N' \<longleftrightarrow> fmlookup N' C \<noteq> None\<close>
  by (auto simp: dom_m_def fmdom.rep_eq)

lemma in_dom_in_ran_m[simp]: \<open>i \<in># dom_m N \<Longrightarrow> the (fmlookup N i) \<in># ran_m N\<close>
  by (auto simp: ran_m_def)

definition Max_dom where
  \<open>Max_dom N = Max (set_mset (add_mset 0 (dom_m N)))\<close>

text \<open>\<^term>\<open>packed\<close> is a predicate to indicate that the domain of finite mapping starts at
   \<^term>\<open>1::nat\<close> and does not contain holes. We use it in the SAT solver for the mapping from
   indexes to clauses.
\<close>
definition packed where
  \<open>packed N \<longleftrightarrow> dom_m N = mset [1..<Suc (Max_dom N)]\<close>

text \<open>Marking this rule as simp is not compatible with unfolding the definition of packed when marked as\<close>
lemma Max_dom_empty: \<open>dom_m b = {#}  \<Longrightarrow> Max_dom b = 0\<close>
  by (auto simp: Max_dom_def)

lemma ran_m_fmempty[simp]: \<open>ran_m fmempty = {#}\<close> and
    dom_m_fmempty[simp]: \<open>dom_m fmempty = {#}\<close>
  by (auto simp: ran_m_def dom_m_def)

lemma Max_dom_fmempty: \<open>Max_dom fmempty = 0\<close>
  by (auto simp: Max_dom_empty)

lemma packed_empty[simp]: \<open>packed fmempty\<close>
  by (auto simp: packed_def Max_dom_empty)

lemma packed_Max_dom_size:
  assumes p: \<open>packed N\<close>
  shows \<open>Max_dom N = size (dom_m N)\<close>
proof -
  have 1: \<open>dom_m N = mset [1..<Suc (Max_dom N)]\<close>
    using p unfolding packed_def Max_dom_def[symmetric] .
  have \<open>size (dom_m N) = size (mset [1..<Suc (Max_dom N)])\<close>
    unfolding 1 ..
  also have \<open>\<dots> = length [1..<Suc (Max_dom N)]\<close>
    unfolding size_mset ..
  also have \<open>\<dots> = Max_dom N\<close>
    unfolding length_upt by simp
  finally show ?thesis
    by simp
qed

lemma Max_dom_le:
  \<open>L \<in># dom_m N \<Longrightarrow> L \<le> Max_dom N\<close>
  by (auto simp: Max_dom_def)

lemma remove1_mset_ge_Max_some: \<open>a > Max_dom b \<Longrightarrow> remove1_mset a (dom_m b) = dom_m  b\<close>
  by (auto simp: Max_dom_def remove_1_mset_id_iff_notin
      dest!: multi_member_split)

lemma Max_dom_fmupd_irrel:
   \<open>(a :: 'a :: {zero,linorder}) > Max_dom M \<Longrightarrow> Max_dom (fmupd a C M) = max a (Max_dom M)\<close>
  by (cases \<open>dom_m M\<close>)
     (auto simp: Max_dom_def remove1_mset_ge_Max_some ac_simps)

lemma Max_dom_alt_def: \<open>Max_dom b = Max (insert 0 (set_mset (dom_m b)))\<close>
  unfolding Max_dom_def by auto

lemma Max_insert_Suc_Max_dim_dom[simp]:
   \<open>Max (insert (Suc (Max_dom b)) (set_mset (dom_m b))) = Suc (Max_dom b)\<close>
  unfolding Max_dom_alt_def
  by (cases \<open>set_mset (dom_m b) = {}\<close>) auto

lemma size_dom_m_Max_dom:
  \<open>size (dom_m N) \<le> Suc (Max_dom N)\<close>
proof -
  have \<open>dom_m N \<subseteq># mset_set {0..< Suc (Max_dom N)}\<close>
    apply (rule distinct_finite_set_mset_subseteq_iff[THEN iffD1])
    subgoal by (auto simp: distinct_mset_dom)
    subgoal by auto
    subgoal by (auto dest: Max_dom_le)
    done
  from size_mset_mono[OF this] show ?thesis by auto
qed

lemma Max_atLeastLessThan_plus: \<open>Max {(a::nat) ..< a+n} = (if n = 0 then Max {} else a+n - 1)\<close>
  apply (induction n arbitrary: a)
  subgoal by auto
  subgoal for n a
    by (cases n)
      (auto simp: image_Suc_atLeastLessThan[symmetric] mono_Max_commute[symmetric] mono_def
        atLeastLessThanSuc
        simp del: image_Suc_atLeastLessThan)
  done

lemma Max_atLeastLessThan: \<open>Max {(a::nat) ..< b} = (if b \<le> a then Max {} else b - 1)\<close>
  using Max_atLeastLessThan_plus[of a \<open>b-a\<close>]
  by auto

lemma Max_insert_Max_dom_into_packed:
   \<open>Max (insert (Max_dom bc) {Suc 0..<Max_dom bc}) = Max_dom bc\<close>
  by (cases \<open>Max_dom bc\<close>; cases \<open>Max_dom bc - 1\<close>)
    (auto simp: Max_dom_empty Max_atLeastLessThan)

lemma packed0_fmud_Suc_Max_dom: \<open>packed b \<Longrightarrow> packed (fmupd (Suc (Max_dom b)) C b)\<close>
  by (auto simp: packed_def remove1_mset_ge_Max_some Max_dom_fmupd_irrel max_def)

lemma ge_Max_dom_notin_dom_m: \<open>a > Max_dom ao \<Longrightarrow> a \<notin># dom_m ao\<close>
  by (auto simp: Max_dom_def)

lemma packed_in_dom_mI: \<open>packed bc \<Longrightarrow> j \<le> Max_dom bc \<Longrightarrow> 0 < j \<Longrightarrow> j \<in># dom_m bc\<close>
  by (auto simp: packed_def)



lemma fmrestrict_set_fmupd:
  \<open>a \<in> xs \<Longrightarrow> fmrestrict_set xs (fmupd a C N) = fmupd a C (fmrestrict_set xs N)\<close>
  \<open>a \<notin> xs \<Longrightarrow> fmrestrict_set xs (fmupd a C N) = fmrestrict_set xs N\<close>
  by (auto simp: fmfilter_alt_defs)

lemma fset_fmdom_fmrestrict_set:
  \<open>fset (fmdom (fmrestrict_set xs N)) = fset (fmdom N) \<inter> xs\<close>
  by (auto simp: fmfilter_alt_defs)

lemma dom_m_fmresctrict_set: \<open>dom_m (fmrestrict_set (set xs) N) = mset xs \<inter># dom_m N\<close>
  using fset_fmdom_fmrestrict_set[of \<open>set xs\<close> N] distinct_mset_dom[of N]
  distinct_mset_inter_remdups_mset[of \<open>mset_fset (fmdom N)\<close> \<open>mset xs\<close>]
  by (auto simp: dom_m_def fset_mset_mset_fset finite_mset_set_inter multiset_inter_commute
    remdups_mset_def)

lemma dom_m_fmresctrict_set': \<open>dom_m (fmrestrict_set xs N) = mset_set (xs \<inter> set_mset (dom_m N))\<close>
  using fset_fmdom_fmrestrict_set[of \<open>xs\<close> N] distinct_mset_dom[of N]
  by (auto simp: dom_m_def fset_mset_mset_fset finite_mset_set_inter multiset_inter_commute
    remdups_mset_def)

end
