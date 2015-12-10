theory Wf_More
imports Main

begin

section \<open>Transition\<close>
subsection \<open>Full transitions\<close>
text \<open>We define here properties to define properties after all possible transitions.\<close>
abbreviation "no_step step S \<equiv> (\<forall>S'. \<not>step S S')"

definition full :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("_\<^sup>+\<^sup>\<down>") where
"full transf = (\<lambda>S S'. tranclp transf S S' \<and> (\<forall>S''. \<not> transf S' S''))"

definition full0:: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("_\<^sup>\<down>") where
"full0 transf = (\<lambda>S S'. rtranclp transf S S' \<and> (\<forall>S''. \<not> transf S' S''))"

lemma rtranclp_fullI:
  "R\<^sup>*\<^sup>* a b \<Longrightarrow> full R b c \<Longrightarrow> full R a c"
  unfolding full_def by auto

lemma tranclp_fullI:
  "R\<^sup>+\<^sup>+ a b \<Longrightarrow> full R b c \<Longrightarrow> full R a c"
  unfolding full_def by auto

lemma rtranclp_full0I:
  "R\<^sup>*\<^sup>* a b \<Longrightarrow> full0 R b c \<Longrightarrow> full0 R a c"
  unfolding full0_def by auto
lemma tranclp_full0_fullI:
  "R\<^sup>+\<^sup>+ a b \<Longrightarrow> full0 R b c \<Longrightarrow> full R a c"
  unfolding full0_def full_def by auto

lemma full0_unfold:
  "full0 r S S' \<longleftrightarrow> ((S = S' \<and> no_step r S') \<or> full r S S')"
  unfolding full0_def full_def by (auto simp add: Nitpick.rtranclp_unfold)

subsection \<open>Well-foundedness and full transitions\<close>
lemma wf_exists_normal_form:
  assumes wf:"wf {(x, y). R y x}"
  shows "\<exists>b. R\<^sup>*\<^sup>* a b \<and> no_step R b"
proof (rule ccontr)
  assume "\<not> ?thesis"
  hence H: "\<And>b. \<not> R\<^sup>*\<^sup>* a b \<or> \<not>no_step R b"
    by blast
  def F \<equiv> "rec_nat a (\<lambda>i b. SOME c. R b c)"
  have [simp]: "F 0 = a"
    unfolding F_def by auto
  have [simp]: "\<And>i. F (Suc i) = (SOME b. R (F i) b)"
    using F_def by simp
  { fix i
    have "\<forall>j<i. R (F j) (F (Suc j))"
      proof (induction i)
        case 0
        thus ?case by auto
      next
        case (Suc i)
        hence "R\<^sup>*\<^sup>* a (F i)"
          by (induction i) auto
        hence "R (F i) (SOME b. R (F i) b)"
          using H by (simp add: someI_ex)
        hence "\<forall>j < Suc i. R (F j) (F (Suc j))"
          using H Suc by (simp add: less_Suc_eq)
        thus ?case by fast
      qed
  }
  hence "\<forall>j. R (F j) (F (Suc j))" by blast
  thus False
    using wf unfolding wfP_def wf_iff_no_infinite_down_chain by blast
qed

lemma wf_exists_normal_form_full0:
  assumes wf:"wf {(x, y). R y x}"
  shows "\<exists>b. full0 R a b"
  using wf_exists_normal_form[OF assms] unfolding full0_def by blast

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

subsection \<open>More Well-foundedness\<close>
text \<open>A little list of theorems that could be useful, but are hidden:
  \<^item> link between @{term wf} and infinite chains: @{thm wf_iff_no_infinite_down_chain},
  @{thm wf_no_infinite_down_chainE}\<close>

lemma wf_if_measure_in_wf:
  "wf R \<Longrightarrow> (\<And>a b. (a, b) \<in> S \<Longrightarrow> (\<nu> a, \<nu> b)\<in>R) \<Longrightarrow> wf S"
  by (meson wf_iff_no_infinite_down_chain)

lemma wfP_if_measure: fixes f :: "'a \<Rightarrow> nat"
shows "(\<And>x y. P x \<Longrightarrow> g x y  \<Longrightarrow> f y < f x) \<Longrightarrow> wf {(y,x). P x \<and> g x y}"
  apply(insert wf_measure[of f])
  apply(simp only: measure_def inv_image_def less_than_def less_eq)
  apply(erule wf_subset)
  apply auto
  done

lemma wf_if_measure_f:
assumes "wf r"
shows "wf {(b, a). (f b, f a) \<in> r}"
  using assms by (metis inv_image_def wf_inv_image)

lemma wf_wf_if_measure':
assumes "wf r" and H: "(\<And>x y. P x \<Longrightarrow> g x y \<Longrightarrow> (f y, f x) \<in> r)"
shows "wf {(y,x). P x \<and> g x y}"
proof -
  have "wf {(b, a). (f b, f a) \<in> r}" using assms(1) wf_if_measure_f by auto
  hence "wf {(b, a). P a \<and> g a b \<and> (f b, f a) \<in> r}"
    using wf_subset[of _ "{(b, a). P a \<and> g a b \<and> (f b, f a) \<in> r}"] by auto
  moreover have "{(b, a). P a \<and> g a b \<and> (f b, f a) \<in> r} \<subseteq> {(b, a). (f b, f a) \<in> r}" by auto
  moreover have "{(b, a). P a \<and> g a b \<and> (f b, f a) \<in> r} = {(b, a). P a \<and> g a b}" using H by auto
  ultimately show ?thesis using wf_subset by simp
qed

lemma wf_lex_less: "wf (lex {(a, b). (a::nat) < b})"
proof -
  have m: "{(a, b). a < b} = measure id" by auto
  show ?thesis apply (rule wf_lex) unfolding m by auto
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

lemma wf_snd_wf_pair:
  assumes "wf {(M', M). R M' M} "
  shows "wf {((M', N'), (M, N)). R N' N}"
proof -
  have wf: "wf {((M', N'), (M, N)). R M' M}"
    using assms wf_fst_wf_pair by auto
  hence wf: "\<And>P. (\<forall>x. (\<forall>y. (y, x) \<in> {((M', N'), M, N). R M' M} \<longrightarrow> P y) \<longrightarrow> P x) \<Longrightarrow> All P"
    unfolding wf_def by auto
  show ?thesis
    unfolding wf_def
    proof (intro allI impI)
      fix P :: "'c \<times> 'a \<Rightarrow> bool" and x :: "'c \<times> 'a"
      assume H: "\<forall>x. (\<forall>y. (y, x) \<in> {((M', N'), M, y). R N' y} \<longrightarrow> P y) \<longrightarrow> P x"
      obtain a b where x: "x = (a, b)" by (cases x)
      have P: "P x = (P \<circ> (\<lambda>(a, b). (b, a))) (b, a)"
        unfolding x by auto
      show "P x"
        using wf[of "P o (\<lambda>(a, b). (b, a))"] apply rule
          using H apply simp
        unfolding P by blast
    qed
qed

lemma wf_if_measure_f_notation2:
  assumes "wf r"
  shows "wf {(b, h a)|b a. (f b, f (h a)) \<in> r}"
  apply (rule wf_subset)
  using wf_if_measure_f[OF assms, of f] by auto

lemma wf_wf_if_measure'_notation2:
assumes "wf r" and H: "(\<And>x y. P x \<Longrightarrow> g x y \<Longrightarrow> (f y, f (h x)) \<in> r)"
shows "wf {(y,h x)| y x. P x \<and> g x y}"
proof -
  have "wf {(b, h a)|b a. (f b, f (h a)) \<in> r}" using assms(1) wf_if_measure_f_notation2 by auto
  hence "wf {(b, h a)|b a. P a \<and> g a b \<and> (f b, f (h a)) \<in> r}"
    using wf_subset[of _ "{(b, h a)| b a. P a \<and> g a b \<and> (f b, f (h a)) \<in> r}"] by auto
  moreover have "{(b, h a)|b a. P a \<and> g a b \<and> (f b, f (h a)) \<in> r}
    \<subseteq> {(b, h a)|b a. (f b, f (h a)) \<in> r}" by auto
  moreover have "{(b, h a)|b a. P a \<and> g a b \<and> (f b, f (h a)) \<in> r} = {(b, h a)|b a. P a \<and> g a b}"
    using H by auto
  ultimately show ?thesis using wf_subset by simp
qed

subsection \<open>rtranclp\<close>
text \<open>This theorem already exists as @{thm Nitpick.rtranclp_unfold} (and sledgehammer use it), but
  it makes more sense to duplicate it.\<close>
lemma rtranclp_unfold: "rtranclp r a b \<longleftrightarrow> (a = b \<or> tranclp r a b)"
  by (meson rtranclp.simps rtranclpD tranclp_into_rtranclp)

lemma tranclp_unfold_end: "tranclp r a b \<longleftrightarrow> (\<exists>a'. rtranclp r a a' \<and> r a' b)"
  by (metis rtranclp.rtrancl_refl rtranclp_into_tranclp1 tranclp.cases tranclp_into_rtranclp)

lemma tranclp_unfold_begin: "tranclp r a b \<longleftrightarrow> (\<exists>a'. r a a' \<and> rtranclp r a' b)"
  by (meson rtranclp_into_tranclp2 tranclpD)


text \<open>Analog of @{thm rtranclp_mono}\<close>
lemma tranclp_mono:
  assumes mono:"r \<le> s"
  shows "r\<^sup>+\<^sup>+ \<le> s\<^sup>+\<^sup>+"
proof
  fix x y
  assume "r\<^sup>+\<^sup>+ x y"
  then show "s\<^sup>+\<^sup>+ x y"
    using rtranclp_mono[OF mono] mono unfolding tranclp_unfold_begin by auto
qed

end