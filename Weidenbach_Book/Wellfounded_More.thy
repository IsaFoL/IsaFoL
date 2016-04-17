(* Title:       More about Relations
    Author:      Mathias Fleury <mathias.fleury at mpi-inf.mpg.de>
*)
section \<open>Transitions\<close>

text \<open>This theory contains some facts about closure, the definition of full transformations, and
  well-foundedness.\<close>

theory Wellfounded_More
imports Main

begin

subsection \<open>More theorems about Closures\<close>

text \<open>This is the equivalent of @{thm rtranclp_mono} for @{term tranclp}\<close>
lemma tranclp_mono_explicit:
  "r\<^sup>+\<^sup>+ a b \<Longrightarrow> r \<le> s \<Longrightarrow> s\<^sup>+\<^sup>+ a b"
    using rtranclp_mono by (auto dest!: tranclpD intro: rtranclp_into_tranclp2)

lemma tranclp_mono:
  assumes mono: "r \<le> s"
  shows "r\<^sup>+\<^sup>+ \<le> s\<^sup>+\<^sup>+"
    using rtranclp_mono[OF mono] mono by (auto dest!: tranclpD intro: rtranclp_into_tranclp2)

lemma tranclp_idemp_rel:
  "R\<^sup>+\<^sup>+\<^sup>+\<^sup>+ a b \<longleftrightarrow> R\<^sup>+\<^sup>+ a b"
  apply (rule iffI)
    prefer 2 apply blast
  by (induction rule: tranclp_induct) auto

text \<open>Equivalent of @{thm rtranclp_idemp}\<close>
lemma trancl_idemp: "(r\<^sup>+)\<^sup>+ = r\<^sup>+"
  by simp

lemmas tranclp_idemp[simp] = trancl_idemp[to_pred]

text \<open>This theorem already exists as @{thm Nitpick.rtranclp_unfold} (and sledgehammer uses it), but
  it makes sense to duplicate it, because it is unclear how stable the lemmas in the
  @{file "~~/src/HOL/Nitpick.thy"} theory are.\<close>
lemma rtranclp_unfold: "rtranclp r a b \<longleftrightarrow> (a = b \<or> tranclp r a b)"
  by (meson rtranclp.simps rtranclpD tranclp_into_rtranclp)

(* TODO destruction rule instead of simp rule *)
lemma tranclp_unfold_end: "tranclp r a b \<longleftrightarrow> (\<exists>a'. rtranclp r a a' \<and> r a' b)"
  by (metis rtranclp.rtrancl_refl rtranclp_into_tranclp1 tranclp.cases tranclp_into_rtranclp)

text \<open>Near duplicate of @{thm tranclpD}:\<close>
lemma tranclp_unfold_begin: "tranclp r a b \<longleftrightarrow> (\<exists>a'. r a a' \<and> rtranclp r a' b)"
  by (meson rtranclp_into_tranclp2 tranclpD)

lemma trancl_set_tranclp: "(a, b) \<in> {(b,a). P a b}\<^sup>+ \<longleftrightarrow> P\<^sup>+\<^sup>+ b a"
  apply (rule iffI)
    apply (induction rule: trancl_induct; simp)
  apply (induction rule: tranclp_induct; auto simp: trancl_into_trancl2)
  done

lemma tranclp_rtranclp_rtranclp_rel: "R\<^sup>+\<^sup>+\<^sup>*\<^sup>* a b \<longleftrightarrow> R\<^sup>*\<^sup>* a b"
  by (simp add: rtranclp_unfold)

lemma tranclp_rtranclp_rtranclp[simp]: "R\<^sup>+\<^sup>+\<^sup>*\<^sup>* = R\<^sup>*\<^sup>*"
  by (fastforce simp: rtranclp_unfold)

lemma rtranclp_exists_last_with_prop:
  assumes "R x z" and "R\<^sup>*\<^sup>* z z'" and "P x z"
  shows "\<exists>y y'. R\<^sup>*\<^sup>* x y \<and> R y y' \<and> P y y' \<and> (\<lambda>a b. R a b \<and> \<not>P a b)\<^sup>*\<^sup>* y' z'"
  using assms(2,1,3)
proof (induction)
  case base
  then show ?case by auto
next
  case (step z' z'') note z = this(2) and IH = this(3)[OF this(4-5)]
  show ?case
    apply (cases "P z' z''")
      apply (rule exI[of _ z'], rule exI[of _ z''])
      using z assms(1) step.hyps(1) step.prems(2) apply auto[1]
    using IH z rtranclp.rtrancl_into_rtrancl by fastforce
qed

lemma rtranclp_and_rtranclp_left: "(\<lambda> a b. P a b \<and> Q a b)\<^sup>*\<^sup>* S T \<Longrightarrow> P\<^sup>*\<^sup>* S T"
  by (induction rule: rtranclp_induct) auto

subsection \<open>Full Transitions\<close>
text \<open>We define here properties to define properties after all possible transitions.\<close>
abbreviation "no_step step S \<equiv> (\<forall>S'. \<not>step S S')"

definition full1 :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" (*"_\<^sup>+\<^sup>\<down>"*) where
"full1 transf = (\<lambda>S S'. tranclp transf S S' \<and> (\<forall>S''. \<not> transf S' S''))"

definition full:: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" (*"_\<^sup>\<down>"*) where
"full transf = (\<lambda>S S'. rtranclp transf S S' \<and> (\<forall>S''. \<not> transf S' S''))"

text \<open>We define output notations only for printing:\<close>
notation (output) full1 ("_\<^sup>+\<^sup>\<down>")
notation (output) full ("_\<^sup>\<down>")

lemma rtranclp_full1I:
  "R\<^sup>*\<^sup>* a b \<Longrightarrow> full1 R b c \<Longrightarrow> full1 R a c"
  unfolding full1_def by auto

lemma tranclp_full1I:
  "R\<^sup>+\<^sup>+ a b \<Longrightarrow> full1 R b c \<Longrightarrow> full1 R a c"
  unfolding full1_def by auto

lemma rtranclp_fullI:
  "R\<^sup>*\<^sup>* a b \<Longrightarrow> full R b c \<Longrightarrow> full R a c"
  unfolding full_def by auto

lemma tranclp_full_full1I:
  "R\<^sup>+\<^sup>+ a b \<Longrightarrow> full R b c \<Longrightarrow> full1 R a c"
  unfolding full_def full1_def by auto

lemma full_fullI:
  "R a b \<Longrightarrow> full R b c \<Longrightarrow> full1 R a c"
  unfolding full_def full1_def by auto

lemma full_unfold:
  "full r S S' \<longleftrightarrow> ((S = S' \<and> no_step r S') \<or> full1 r S S')"
  unfolding full_def full1_def by (auto simp add: rtranclp_unfold)

lemma full1_is_full[intro]: "full1 R S T \<Longrightarrow> full R S T"
  by (simp add: full_unfold)

lemma not_full1_rtranclp_relation: "\<not>full1 R\<^sup>*\<^sup>* a b"
  by (meson full1_def rtranclp.rtrancl_refl)

lemma not_full_rtranclp_relation: "\<not>full R\<^sup>*\<^sup>* a b"
  by (meson full_fullI not_full1_rtranclp_relation rtranclp.rtrancl_refl)

lemma full1_tranclp_relation_full:
  "full1 R\<^sup>+\<^sup>+ a b \<longleftrightarrow> full1 R a b"
  by (metis converse_tranclpE full1_def reflclp_tranclp rtranclpD rtranclp_idemp rtranclp_reflclp
    tranclp.r_into_trancl tranclp_into_rtranclp)

lemma full_tranclp_relation_full:
  "full R\<^sup>+\<^sup>+ a b \<longleftrightarrow> full R a b"
  by (metis full_unfold full1_tranclp_relation_full tranclp.r_into_trancl tranclpD)

lemma rtranclp_full1_eq_or_full1:
  "(full1 R)\<^sup>*\<^sup>* a b \<longleftrightarrow> (a = b \<or> full1 R a b)"
proof -
  have "\<forall>p a aa. \<not> p\<^sup>*\<^sup>* (a::'a) aa \<or> a = aa \<or> (\<exists>ab. p\<^sup>*\<^sup>* a ab \<and> p ab aa)"
    by (metis rtranclp.cases)
  then obtain aa :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
    f1: "\<forall>p a ab. \<not> p\<^sup>*\<^sup>* a ab \<or> a = ab \<or> p\<^sup>*\<^sup>* a (aa p a ab) \<and> p (aa p a ab) ab"
    by moura
  { assume "a \<noteq> b"
    { assume "\<not> full1 R a b \<and> a \<noteq> b"
      then have "a \<noteq> b \<and> a \<noteq> b \<and> \<not> full1 R (aa (full1 R) a b) b \<or> \<not> (full1 R)\<^sup>*\<^sup>* a b \<and> a \<noteq> b"
        using f1 by (metis (no_types) full1_def full1_tranclp_relation_full)
      then have ?thesis
        using f1 by blast }
    then have ?thesis
      by auto }
  then show ?thesis
    by fastforce
qed

lemma tranclp_full1_full1:
  "(full1 R)\<^sup>+\<^sup>+ a b \<longleftrightarrow> full1 R a b"
  by (metis full1_def rtranclp_full1_eq_or_full1 tranclp_unfold_begin)

subsection \<open>Well-Foundedness and Full Transitions\<close>
lemma wf_exists_normal_form:
  assumes wf:"wf {(x, y). R y x}"
  shows "\<exists>b. R\<^sup>*\<^sup>* a b \<and> no_step R b"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have H: "\<And>b. \<not> R\<^sup>*\<^sup>* a b \<or> \<not>no_step R b"
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
        then show ?case by auto
      next
        case (Suc i)
        then have "R\<^sup>*\<^sup>* a (F i)"
          by (induction i) auto
        then have "R (F i) (SOME b. R (F i) b)"
          using H by (simp add: someI_ex)
        then have "\<forall>j < Suc i. R (F j) (F (Suc j))"
          using H Suc by (simp add: less_Suc_eq)
        then show ?case by fast
      qed
  }
  then have "\<forall>j. R (F j) (F (Suc j))" by blast
  then show False
    using wf unfolding wfP_def wf_iff_no_infinite_down_chain by blast
qed

lemma wf_exists_normal_form_full:
  assumes wf:"wf {(x, y). R y x}"
  shows "\<exists>b. full R a b"
  using wf_exists_normal_form[OF assms] unfolding full_def by blast

subsection \<open>More Well-Foundedness\<close>
text \<open>A little list of theorems that could be useful, but are hidden:
  \<^item> link between @{term wf} and infinite chains: @{thm wf_iff_no_infinite_down_chain},
  @{thm wf_no_infinite_down_chainE}\<close>

lemma wf_if_measure_in_wf:
  "wf R \<Longrightarrow> (\<And>a b. (a, b) \<in> S \<Longrightarrow> (\<nu> a, \<nu> b)\<in>R) \<Longrightarrow> wf S"
  by (metis in_inv_image wfE_min wfI_min wf_inv_image)

lemma wfP_if_measure: fixes f :: "'a \<Rightarrow> nat"
  shows "(\<And>x y. P x \<Longrightarrow> g x y \<Longrightarrow> f y < f x) \<Longrightarrow> wf {(y,x). P x \<and> g x y}"
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
  assumes "wf r" and H: "\<And>x y. P x \<Longrightarrow> g x y \<Longrightarrow> (f y, f x) \<in> r"
  shows "wf {(y,x). P x \<and> g x y}"
proof -
  have "wf {(b, a). (f b, f a) \<in> r}" using assms(1) wf_if_measure_f by auto
  then have "wf {(b, a). P a \<and> g a b \<and> (f b, f a) \<in> r}"
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
  shows "(\<And>x y. P x y \<Longrightarrow> g x y \<Longrightarrow> f x < f y) \<Longrightarrow> wf {(x,y). P x y \<and> g x y}"
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
  then show ?thesis
    by (rule wf_subset) auto
qed

lemma wf_snd_wf_pair:
  assumes "wf {(M', M). R M' M} "
  shows "wf {((M', N'), (M, N)). R N' N}"
proof -
  have wf: "wf {((M', N'), (M, N)). R M' M}"
    using assms wf_fst_wf_pair by auto
  then have wf: "\<And>P. (\<forall>x. (\<forall>y. (y, x) \<in> {((M', N'), M, N). R M' M} \<longrightarrow> P y) \<longrightarrow> P x) \<Longrightarrow> All P"
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
  assumes "wf r" and H: "\<And>x y. P x \<Longrightarrow> g x y \<Longrightarrow> (f y, f (h x)) \<in> r"
  shows "wf {(y,h x)| y x. P x \<and> g x y}"
proof -
  have "wf {(b, h a)|b a. (f b, f (h a)) \<in> r}" using assms(1) wf_if_measure_f_notation2 by auto
  then have "wf {(b, h a)|b a. P a \<and> g a b \<and> (f b, f (h a)) \<in> r}"
    using wf_subset[of _ "{(b, h a)| b a. P a \<and> g a b \<and> (f b, f (h a)) \<in> r}"] by auto
  moreover have "{(b, h a)|b a. P a \<and> g a b \<and> (f b, f (h a)) \<in> r}
    \<subseteq> {(b, h a)|b a. (f b, f (h a)) \<in> r}" by auto
  moreover have "{(b, h a)|b a. P a \<and> g a b \<and> (f b, f (h a)) \<in> r} = {(b, h a)|b a. P a \<and> g a b}"
    using H by auto
  ultimately show ?thesis using wf_subset by simp
qed

end
