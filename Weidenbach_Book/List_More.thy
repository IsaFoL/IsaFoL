theory List_More
imports Main
begin
declare upt.simps(2)[simp del] upt_Suc[simp del]
declare upt_Suc_append
lemma upt_Suc_le_append: "\<not>i \<le> j \<Longrightarrow> [i..<Suc j] = []"
  by (auto simp add: upt.simps(2))

lemmas upt_simps[simp] = upt_Suc_append upt_Suc_le_append


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
  thus ?thesis using `A = [m ..< m + length A]` by auto
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
  hence "m < i"
    by (metis Suc_eq_plus1 append_eq_conv_conj diff_is_0_eq' drop_0 le_less less_Suc_eq
      list.distinct(1) list.sel(1) local.Cons(1) not_less upt_rec)
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
  thus ?thesis using `B = [Suc m + length A..<n]` by auto
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

text \<open>MOVE missing in List.thy (see @{thm lexord_trans})\<close>
lemma lexn_trans[trans]:
  assumes trans: "trans r"
  shows "trans (lexn r n)"
    unfolding trans_def
proof (intro allI impI)
  fix as bs cs
  assume asbs: "(as, bs) \<in> lexn r n"
  and bscs: "(bs, cs) \<in> lexn r n"
  obtain abs a b as' bs' where
    n: "length as = n" and "length bs = n" and
    as: "as = abs @ a # as'" and
    bs: "bs = abs @ b # bs'" and
    abr: "(a, b) \<in> r"
    using asbs unfolding lexn_conv by blast

  obtain bcs b' c' cs' bs' where
    n': "length cs = n" and "length bs = n" and
    bs': "bs = bcs @ b' # bs'" and
    cs: "cs = bcs @ c' # cs'" and
    b'c'r: "(b', c') \<in> r"
    using bscs unfolding lexn_conv by blast
  consider (le) "length bcs < length abs"
    | (eq) "length bcs = length abs"
    | (ge) "length bcs > length abs" by linarith
  thus "(as, cs) \<in> lexn r n"
    proof cases
      let ?k = "length bcs"
      case le
      hence "as ! ?k = bs ! ?k" unfolding as bs by (simp add: nth_append)
      hence "(as ! ?k, cs ! ?k) \<in> r" using b'c'r unfolding bs' cs by auto
      moreover
        have "length bcs < length as" using le unfolding as by simp
        from id_take_nth_drop[OF this] have "as = take ?k as @ as ! ?k # drop (Suc ?k) as" .
      moreover
        have "length bcs < length cs" unfolding cs by simp
        from id_take_nth_drop[OF this] have "cs = take ?k cs @ cs ! ?k # drop (Suc ?k) cs" .
      moreover have "take ?k as = take ?k cs"
        using le arg_cong[OF bs, of "take (length bcs)"] unfolding cs as bs' by auto
      ultimately show ?thesis using n n' unfolding lexn_conv by auto
    next
      let ?k = "length abs"
      case ge
      hence "bs ! ?k = cs ! ?k" unfolding bs' cs by (simp add: nth_append)
      hence "(as ! ?k, cs ! ?k) \<in> r" using abr unfolding as bs by auto
      moreover
        have "length abs < length as" using ge unfolding as by simp
        from id_take_nth_drop[OF this] have "as = take ?k as @ as ! ?k # drop (Suc ?k) as" .
      moreover
        have "length abs < length cs" using n n' unfolding as by simp
        from id_take_nth_drop[OF this] have "cs = take ?k cs @ cs ! ?k # drop (Suc ?k) cs" .
      moreover have "take ?k as = take ?k cs"
        using ge arg_cong[OF bs', of "take (length abs)"] unfolding cs as bs by auto
      ultimately show ?thesis using n n' unfolding lexn_conv by auto
    next
      let ?k = "length abs"
      case eq
      hence [simp]: "abs = bcs" "b = b'" using bs bs' by auto
      hence "(a, c') \<in> r" using abr b'c'r trans unfolding trans_def by blast
      thus ?thesis using n n' unfolding lexn_conv as bs cs by auto
    qed
qed

lemma upt_decomp_lt:
  assumes H: "xs @ i # ys @ j # zs = [m ..< n]"
  shows "i < j"
proof -
  have xs: "xs = [m ..< i]" and ys: "ys = [Suc i ..< j]" and zs: "zs = [Suc j ..< n]"
    using H  by (auto dest: append_cons_eq_upt_length_i append_cons_eq_upt_length_i_end)
  show ?thesis by (metis append_cons_eq_upt_length_i_end assms lessI less_trans self_append_conv2 upt_eq_Cons_conv upt_rec ys)
qed

section \<open>Well-foundedness\<close>
lemma wfP_if_measure: fixes f :: "'a \<Rightarrow> nat"
shows "(\<And>x y. P x \<Longrightarrow> g x y  \<Longrightarrow> f x < f y) \<Longrightarrow> wf {(x,y). P x \<and> g x y}"
  apply(insert wf_measure[of f])
  apply(simp only: measure_def inv_image_def less_than_def less_eq)
  apply(erule wf_subset)
  apply auto
  done

lemma wf_if_measure_f:
assumes "wf r"
shows "wf {(b, a). (f b, f a) \<in> r}"
using assms
 by (metis inv_image_def wf_inv_image)

lemma wf_wf_if_measure':
assumes "wf r" and H: "(\<And>x y. P x \<Longrightarrow> g x y \<Longrightarrow> (f y, f x) \<in> r)"
shows "wf {(y,x). P x \<and> g x y}"
proof -
  have "wf {(b, a). (f b, f a) \<in> r}" using assms(1) wf_if_measure_f by auto
  hence "wf {(b, a). P a \<and> g a b \<and> (f b, f a) \<in> r}" using wf_subset[of _ "{(b, a). P a \<and> g a b \<and> (f b, f a) \<in> r}"] by auto
  moreover have "{(b, a). P a \<and> g a b \<and> (f b, f a) \<in> r} \<subseteq> {(b, a). (f b, f a) \<in> r}" by auto
  moreover have "{(b, a). P a \<and> g a b \<and> (f b, f a) \<in> r} = {(b, a). P a \<and> g a b}" using H by auto
  ultimately show ?thesis using wf_subset by simp
qed

lemma wf_lex_less: "wf (lex {(a, b). (a::nat) < b})"
proof -
  have m: "{(a, b). a < b} = measure id" by auto
  show ?thesis  apply (rule wf_lex) unfolding m by auto
qed

lemma wfP_if_measure2: fixes f :: "'a \<Rightarrow> nat"
shows "(\<And>x y. P x y \<Longrightarrow> g x y  \<Longrightarrow> f x < f y) \<Longrightarrow> wf {(x,y). P x y \<and> g x y}"
  apply(insert wf_measure[of f])
  apply(simp only: measure_def inv_image_def less_than_def less_eq)
  apply(erule wf_subset)
  apply auto
  done

lemma lexord_on_finite_set_is_wf:
  assumes 
    P_finite: "\<And>U. P U \<longrightarrow> U \<in> A" and
    finite: "finite A" and
    wf: "wf R" and
    trans: "trans R"
  shows "wf {(T, S). (P S \<and> P T) \<and> (T, S) \<in> lexord R}"
  proof (rule wfP_if_measure2)  
    fix T S
    assume P: "P S \<and> P T" and
    s_le_t: "(T, S) \<in> lexord R"
    let ?f = "\<lambda>S. {U. (U, S) \<in> lexord R \<and> P U \<and> P S}"
    have "?f T \<subseteq> ?f S"
       using s_le_t P lexord_trans trans by auto
    moreover have "T \<in> ?f S"
      using s_le_t P by auto
    moreover have "T \<notin> ?f T"
      using s_le_t by (auto simp add: lexord_irreflexive local.wf)
    ultimately have "{U. (U, T) \<in> lexord R \<and> P U \<and> P T} \<subset> {U. (U, S) \<in> lexord R \<and> P U \<and> P S}"
      by auto
    moreover have "finite {U. (U, S) \<in> lexord R \<and> P U \<and> P S}"
      using finite by (metis (no_types, lifting) P_finite finite_subset mem_Collect_eq subsetI) 
    ultimately show "card (?f T) < card (?f S)" by (simp add: psubset_card_mono)
qed


lemma wf_fst_wf_pair:
  assumes "wf {(M', M). R M' M} "
  shows "wf {((M', N'), (M, N)). R M' M}"
proof -
  have "wf ({(M', M). R M' M} <*lex*> {})"
    using assms by auto
  thus ?thesis 
    by (rule wf_subset) auto
qed

section \<open>rtranclp\<close>
text \<open>This theorem already exists as @{thm Nitpick.rtranclp_unfold} (and sledgehammer use it), but it makes more sense to duplicate it.\<close>
lemma rtranclp_unfold: "rtranclp r a b \<longleftrightarrow> (a = b \<or> tranclp r a b)"
  by (meson rtranclp.simps rtranclpD tranclp_into_rtranclp)

end
