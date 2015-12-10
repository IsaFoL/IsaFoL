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

section \<open>More List and Well-foundness Theorems\<close>
text \<open>This section contains theorems that could move to Isabelle standard library.\<close>
subsection \<open>More Lists\<close>
declare upt_Suc_append
lemma upt_Suc_le_append: "\<not>i \<le> j \<Longrightarrow> [i..<Suc j] = []"
  by (auto simp add: upt.simps(2))

lemmas upt_simps[simp] = upt_Suc_append upt_Suc_le_append
subsubsection \<open>Helper function\<close>
lemma list_length2_append_cons:
  "[c, d] = ys @ y # ys' \<longleftrightarrow> (ys = [] \<and> y = c \<and> ys' = [d]) \<or> (ys = [c] \<and> y = d \<and> ys' = [])"
  by (cases ys; cases ys') auto
lemma lexn2_conv:
  "([a, b], [c, d]) \<in> lexn r 2
    \<longleftrightarrow> (a, c)\<in>r \<or> (a = c \<and> (b, d)\<in>r)"
  unfolding lexn_conv by (auto simp add: list_length2_append_cons)
text \<open>Move to List\<close>
text \<open>The counterpart for this lemma when @{term "i > n-m"} is @{thm take_all}.\<close>
lemma take_upt[simp]:
  assumes "i \<le> n - m"
  shows "take i [m..<n] = [m ..<m+i]"
  using assms by (induct i) simp_all

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
