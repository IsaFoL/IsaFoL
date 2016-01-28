theory List_More
imports Main
begin

declare upt.simps(2)[simp del] upt_Suc[simp del]

section \<open>Various\<close>
text \<open>Close to @{thm nat_less_induct}, but with a separation between zero and non-zero.\<close>
thm nat_less_induct
lemma nat_less_induct_case[case_names 0 Suc]:
  assumes
    "P 0" and
    "\<And>n. (\<forall>m < Suc n. P m) \<Longrightarrow> P (Suc n)"
  shows "P n"
  apply (induction rule: nat_less_induct)
  by (case_tac n) (auto intro: assms)


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

lemma bounded_const_product:
  fixes k :: nat and f :: "nat \<Rightarrow> nat"
  assumes "k > 0"
  shows "bounded f \<longleftrightarrow> bounded (\<lambda>i. k * f i)"
  unfolding bounded_def apply (rule iffI)
   using mult_le_mono2 apply blast
  by (meson assms le_less_trans less_or_eq_imp_le nat_mult_less_cancel_disj split_div_lemma)

section \<open>More List\<close>
text \<open>This section contains theorems that could move to Isabelle standard library.\<close>
lemma upt_Suc_le_append: "\<not>i \<le> j \<Longrightarrow> [i..<Suc j] = []"
  by (auto simp add: upt.simps(2))

lemmas upt_simps[simp] = upt_Suc_append upt_Suc_le_append
subsubsection \<open>Helper function\<close>
lemma list_length2_append_cons:
  "[c, d] = ys @ y # ys' \<longleftrightarrow> (ys = [] \<and> y = c \<and> ys' = [d]) \<or> (ys = [c] \<and> y = d \<and> ys' = [])"
  by (cases ys; cases ys') auto
lemma lexn2_conv:
  "([a, b], [c, d]) \<in> lexn r 2 \<longleftrightarrow> (a, c)\<in>r \<or> (a = c \<and> (b, d) \<in>r)"
  unfolding lexn_conv by (auto simp add: list_length2_append_cons)

text \<open>Move to List\<close>

  (* Sledgehammer one-liner: *)
lemma
  assumes "i \<le> n - m"
  shows "take i [m..<n] = [m..<m+i]"
  by (metis Nat.le_diff_conv2 add.commute assms diff_is_0_eq' linear take_upt upt_conv_Nil)

text \<open>The counterpart for this lemma when @{term "i > n-m"} is @{thm take_all}. It is close to
  @{thm take_upt}, but seems more general.\<close>
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
    hence "take (length A) [m..<n] = [m ..<m+length A]" by auto
  ultimately show "A = [m ..<m+length A]" using assms by auto
  show "B = [m + length A..<n]" using assms by (metis append_eq_conv_conj drop_upt)
qed

text \<open>The converse of @{thm append_cons_eq_upt} does not hold:\<close>
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
  assume ?A thus ?B by (auto simp add: append_cons_eq_upt)
next
  assume ?P and ?B
  thus ?A using append_eq_conv_conj by fastforce
qed

lemma append_cons_eq_upt_length_i:
  assumes "A @ i # B = [m..<n]"
  shows "A = [m ..<i]"
proof -
  have "A = [m ..< m + length A]" using assms append_cons_eq_upt by auto
  have "(A @ i # B) ! (length A) = i" by auto
  moreover have "n - m = length (A @ i # B)"
    using assms length_upt by presburger
  hence "[m..<n] ! (length A) = m + length A" by simp
  ultimately have "i = m + length A" using assms by auto
  thus ?thesis using \<open>A = [m ..< m + length A]\<close> by auto
qed

lemma append_cons_eq_upt_length:
  assumes "A @ i # B = [m..<n]"
  shows "length A = i - m"
  using assms
proof (induction A arbitrary: m)
  case Nil
  thus ?case by (metis append_Nil diff_is_0_eq list.size(3) order_refl upt_eq_Cons_conv)
next
  case (Cons a A)
  hence A: "A @ i # B = [m + 1..<n]" by (metis append_Cons upt_eq_Cons_conv)
  hence "m < i" by (metis Cons.prems append_cons_eq_upt_length_i upt_eq_Cons_conv)
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
  hence "[m..<n]! (length A) = m + length A" by simp
  ultimately have "i = m + length A" using assms by auto
  thus ?thesis using \<open>B = [Suc m + length A..<n]\<close> by auto
qed

lemma Max_n_upt: "Max (insert 0 {Suc 0..<n}) = n - Suc 0"
proof (induct n)
  case 0
  thus ?case by simp
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

end
