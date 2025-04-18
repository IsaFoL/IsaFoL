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

text \<open>This is the equivalent of the theorem @{thm [source] rtranclp_mono} for @{term tranclp}\<close>
lemma tranclp_mono_explicit:
  \<open>r\<^sup>+\<^sup>+ a b \<Longrightarrow> r \<le> s \<Longrightarrow> s\<^sup>+\<^sup>+ a b\<close>
  using rtranclp_mono by (auto dest!: tranclpD intro: rtranclp_into_tranclp2)

lemma tranclp_mono:
  assumes mono: \<open>r \<le> s\<close>
  shows \<open>r\<^sup>+\<^sup>+ \<le> s\<^sup>+\<^sup>+\<close>
  using rtranclp_mono[OF mono] mono by (auto dest!: tranclpD intro: rtranclp_into_tranclp2)

lemma tranclp_idemp_rel:
  \<open>R\<^sup>+\<^sup>+\<^sup>+\<^sup>+ a b \<longleftrightarrow> R\<^sup>+\<^sup>+ a b\<close>
  apply (rule iffI)
    prefer 2 apply blast
  by (induction rule: tranclp_induct) auto

text \<open>Equivalent of the theorem @{thm [source] rtranclp_idemp}\<close>
lemma trancl_idemp: \<open>(r\<^sup>+)\<^sup>+ = r\<^sup>+\<close>
  by simp

lemmas tranclp_idemp[simp] = trancl_idemp[to_pred]

text \<open>This theorem already exists as theroem @{thm [source] Nitpick.rtranclp_unfold} (and
  sledgehammer uses it), but it makes sense to duplicate it, because it is unclear how stable the
  lemmas in the @{file \<open>~~/src/HOL/Nitpick.thy\<close>} theory are.\<close>
lemma rtranclp_unfold: \<open>rtranclp r a b \<longleftrightarrow> (a = b \<or> tranclp r a b)\<close>
  by (meson rtranclp.simps rtranclpD tranclp_into_rtranclp)

(* TODO destruction rule instead of simp rule *)
lemma tranclp_unfold_end: \<open>tranclp r a b \<longleftrightarrow> (\<exists>a'. rtranclp r a a' \<and> r a' b)\<close>
  by (metis rtranclp.rtrancl_refl rtranclp_into_tranclp1 tranclp.cases tranclp_into_rtranclp)

text \<open>Near duplicate of theorem @{thm [source] tranclpD}:\<close>
lemma tranclp_unfold_begin: \<open>tranclp r a b \<longleftrightarrow> (\<exists>a'. r a a' \<and> rtranclp r a' b)\<close>
  by (meson rtranclp_into_tranclp2 tranclpD)

lemma trancl_set_tranclp: \<open>(a, b) \<in> {(b,a). P a b}\<^sup>+ \<longleftrightarrow> P\<^sup>+\<^sup>+ b a\<close>
  apply (rule iffI)
    apply (induction rule: trancl_induct; simp)
  apply (induction rule: tranclp_induct; auto simp: trancl_into_trancl2)
  done

lemma tranclp_rtranclp_rtranclp_rel: \<open>R\<^sup>+\<^sup>+\<^sup>*\<^sup>* a b \<longleftrightarrow> R\<^sup>*\<^sup>* a b\<close>
  by (simp add: rtranclp_unfold)

lemma tranclp_rtranclp_rtranclp[simp]: \<open>R\<^sup>+\<^sup>+\<^sup>*\<^sup>* = R\<^sup>*\<^sup>*\<close>
  by (fastforce simp: rtranclp_unfold)

lemma rtranclp_exists_last_with_prop:
  assumes \<open>R x z\<close> and \<open>R\<^sup>*\<^sup>* z z'\<close> and \<open>P x z\<close>
  shows \<open>\<exists>y y'. R\<^sup>*\<^sup>* x y \<and> R y y' \<and> P y y' \<and> (\<lambda>a b. R a b \<and> \<not>P a b)\<^sup>*\<^sup>* y' z'\<close>
  using assms(2,1,3)
proof induction
  case base
  then show ?case by auto
next
  case (step z' z'') note z = this(2) and IH = this(3)[OF this(4-5)]
  show ?case
    apply (cases \<open>P z' z''\<close>)
      apply (rule exI[of _ z'], rule exI[of _ z''])
      using z assms(1) step.hyps(1) step.prems(2) apply (auto; fail)[1]
    using IH z by (fastforce intro: rtranclp.rtrancl_into_rtrancl)
qed

lemma rtranclp_and_rtranclp_left: \<open>(\<lambda> a b. P a b \<and> Q a b)\<^sup>*\<^sup>* S T \<Longrightarrow> P\<^sup>*\<^sup>* S T\<close>
  by (induction rule: rtranclp_induct) auto


subsection \<open>Full Transitions\<close>

paragraph \<open>Definition\<close>

text \<open>We define here predicates to define properties after all possible transitions.\<close>

abbreviation (input) no_step :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" where
"no_step step S \<equiv> \<forall>S'. \<not>step S S'"

definition full1 :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" (*"_\<^sup>+\<^sup>\<down>"*) where
"full1 transf = (\<lambda>S S'. tranclp transf S S' \<and> no_step transf S')"

definition full:: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" (*"_\<^sup>\<down>"*) where
"full transf = (\<lambda>S S'. rtranclp transf S S' \<and> no_step transf S')"

text \<open>We define output notations only for printing (to ease reading):\<close>
notation (output) full1 ("_\<^sup>+\<^sup>\<down>")
notation (output) full ("_\<^sup>\<down>")


paragraph \<open>Some Properties\<close>

lemma rtranclp_full1I:
  \<open>R\<^sup>*\<^sup>* a b \<Longrightarrow> full1 R b c \<Longrightarrow> full1 R a c\<close>
  unfolding full1_def by auto

lemma tranclp_full1I:
  \<open>R\<^sup>+\<^sup>+ a b \<Longrightarrow> full1 R b c \<Longrightarrow> full1 R a c\<close>
  unfolding full1_def by auto

lemma rtranclp_fullI:
  \<open>R\<^sup>*\<^sup>* a b \<Longrightarrow> full R b c \<Longrightarrow> full R a c\<close>
  unfolding full_def by auto

lemma tranclp_full_full1I:
  \<open>R\<^sup>+\<^sup>+ a b \<Longrightarrow> full R b c \<Longrightarrow> full1 R a c\<close>
  unfolding full_def full1_def by auto

lemma full_fullI:
  \<open>R a b \<Longrightarrow> full R b c \<Longrightarrow> full1 R a c\<close>
  unfolding full_def full1_def by auto

lemma full_unfold:
  \<open>full r S S' \<longleftrightarrow> ((S = S' \<and> no_step r S') \<or> full1 r S S')\<close>
  unfolding full_def full1_def by (auto simp add: rtranclp_unfold)

lemma full1_is_full[intro]: \<open>full1 R S T \<Longrightarrow> full R S T\<close>
  by (simp add: full_unfold)

lemma not_full1_rtranclp_relation: "\<not>full1 R\<^sup>*\<^sup>* a b"
  by (auto simp: full1_def)

lemma not_full_rtranclp_relation: "\<not>full R\<^sup>*\<^sup>* a b"
  by (auto simp: full_def)


lemma full1_tranclp_relation_full:
  \<open>full1 R\<^sup>+\<^sup>+ a b \<longleftrightarrow> full1 R a b\<close>
  by (metis converse_tranclpE full1_def reflclp_tranclp rtranclpD rtranclp_idemp rtranclp_reflclp
    tranclp.r_into_trancl tranclp_into_rtranclp)

lemma full_tranclp_relation_full:
  \<open>full R\<^sup>+\<^sup>+ a b \<longleftrightarrow> full R a b\<close>
  by (metis full_unfold full1_tranclp_relation_full tranclp.r_into_trancl tranclpD)

lemma tranclp_full1_full1:
  \<open>(full1 R)\<^sup>+\<^sup>+ a b \<longleftrightarrow> full1 R a b\<close>
  by (metis (mono_tags) full1_def predicate2I tranclp.r_into_trancl tranclp_idemp
      tranclp_mono_explicit tranclp_unfold_end)

lemma rtranclp_full1_eq_or_full1:
  \<open>(full1 R)\<^sup>*\<^sup>* a b \<longleftrightarrow> (a = b \<or> full1 R a b)\<close>
  unfolding rtranclp_unfold tranclp_full1_full1 by simp

lemma no_step_full_iff_eq:
  \<open>no_step R S \<Longrightarrow> full R S T \<longleftrightarrow> S = T\<close>
  unfolding full_def
  by (meson rtranclp.rtrancl_refl rtranclpD tranclpD)


subsection \<open>Well-Foundedness and Full Transitions\<close>

lemma wf_exists_normal_form:
  assumes wf: \<open>wf {(x, y). R y x}\<close>
  shows \<open>\<exists>b. R\<^sup>*\<^sup>* a b \<and> no_step R b\<close>
proof (rule ccontr)
  assume \<open>\<not> ?thesis\<close>
  then have H: \<open>\<And>b. \<not> R\<^sup>*\<^sup>* a b \<or> \<not>no_step R b\<close>
    by blast
  define F where \<open>F = rec_nat a (\<lambda>i b. SOME c. R b c)\<close>
  have [simp]: \<open>F 0 = a\<close>
    unfolding F_def by auto
  have [simp]: \<open>\<And>i. F (Suc i) = (SOME b. R (F i) b)\<close>
    unfolding F_def by simp
  { fix i
    have \<open>\<forall>j<i. R (F j) (F (Suc j))\<close>
    proof (induction i)
      case 0
      then show ?case by auto
    next
      case (Suc i)
      then have \<open>R\<^sup>*\<^sup>* a (F i)\<close>
        by (induction i) auto
      then have \<open>R (F i) (SOME b. R (F i) b)\<close>
        using H by (simp add: someI_ex)
      then have \<open>\<forall>j < Suc i. R (F j) (F (Suc j))\<close>
        using H Suc by (simp add: less_Suc_eq)
      then show ?case by fast
    qed
  }
  then have \<open>\<forall>j. R (F j) (F (Suc j))\<close> by blast
  then show False
    using wf unfolding wf_iff_no_infinite_down_chain by blast
qed

lemma wf_exists_normal_form_full:
  assumes wf: \<open>wf {(x, y). R y x}\<close>
  shows \<open>\<exists>b. full R a b\<close>
  using wf_exists_normal_form[OF assms] unfolding full_def by blast


subsection \<open>More Well-Foundedness\<close>

text \<open>A little list of theorems that could be useful, but are hidden:
  \<^item> link between @{term wf} and infinite chains: theorems
  @{thm [source] wf_iff_no_infinite_down_chain} and @{thm [source] wf_no_infinite_down_chainE}.\<close>

lemma wf_if_measure_in_wf:
  \<open>wf R \<Longrightarrow> (\<And>a b. (a, b) \<in> S \<Longrightarrow> (\<nu> a, \<nu> b)\<in>R) \<Longrightarrow> wf S\<close>
  by (metis in_inv_image wfE_min wfI_min wf_inv_image)

lemma wfP_if_measure: fixes f :: \<open>'a \<Rightarrow> nat\<close>
  shows \<open>(\<And>x y. P x \<Longrightarrow> g x y \<Longrightarrow> f y < f x) \<Longrightarrow> wf {(y,x). P x \<and> g x y}\<close>
  apply (insert wf_measure[of f])
  apply (simp only: measure_def inv_image_def less_than_def less_eq)
  apply (erule wf_subset)
  apply auto
  done

lemma wf_if_measure_f:
  assumes \<open>wf r\<close>
  shows \<open>wf {(b, a). (f b, f a) \<in> r}\<close>
  using assms by (metis inv_image_def wf_inv_image)

lemma wf_wf_if_measure':
  assumes \<open>wf r\<close> and H: \<open>\<And>x y. P x \<Longrightarrow> g x y \<Longrightarrow> (f y, f x) \<in> r\<close>
  shows \<open>wf {(y,x). P x \<and> g x y}\<close>
proof -
  have \<open>wf {(b, a). (f b, f a) \<in> r}\<close> using assms(1) wf_if_measure_f by auto
  then have \<open>wf {(b, a). P a \<and> g a b \<and> (f b, f a) \<in> r}\<close>
    using wf_subset[of _ \<open>{(b, a). P a \<and> g a b \<and> (f b, f a) \<in> r}\<close>] by auto
  moreover have \<open>{(b, a). P a \<and> g a b \<and> (f b, f a) \<in> r} \<subseteq> {(b, a). (f b, f a) \<in> r}\<close> by auto
  moreover have \<open>{(b, a). P a \<and> g a b \<and> (f b, f a) \<in> r} = {(b, a). P a \<and> g a b}\<close> using H by auto
  ultimately show ?thesis using wf_subset by simp
qed

lemma wf_lex_less: \<open>wf (lex less_than)\<close>
  by (auto simp: wf_less)

lemma wfP_if_measure2: fixes f :: \<open>'a \<Rightarrow> nat\<close>
  shows \<open>(\<And>x y. P x y \<Longrightarrow> g x y \<Longrightarrow> f x < f y) \<Longrightarrow> wf {(x,y). P x y \<and> g x y}\<close>
  apply (insert wf_measure[of f])
  apply (simp only: measure_def inv_image_def less_than_def less_eq)
  apply (erule wf_subset)
  apply auto
  done

lemma lexord_on_finite_set_is_wf:
  assumes
    P_finite: \<open>\<And>U. P U \<longrightarrow> U \<in> A\<close> and
    finite: \<open>finite A\<close> and
    wf: \<open>wf R\<close> and
    trans: \<open>trans R\<close>
  shows \<open>wf {(T, S). (P S \<and> P T) \<and> (T, S) \<in> lexord R}\<close>
proof (rule wfP_if_measure2)
  fix T S
  assume P: \<open>P S \<and> P T\<close> and
  s_le_t: \<open>(T, S) \<in> lexord R\<close>
  let ?f = \<open>\<lambda>S. {U. (U, S) \<in> lexord R \<and> P U \<and> P S}\<close>
  have \<open>?f T \<subseteq> ?f S\<close>
     using s_le_t P lexord_trans trans by auto
  moreover have \<open>T \<in> ?f S\<close>
    using s_le_t P by auto
  moreover have \<open>T \<notin> ?f T\<close>
    using s_le_t by (auto simp add: lexord_irreflexive local.wf)
  ultimately have \<open>{U. (U, T) \<in> lexord R \<and> P U \<and> P T} \<subset> {U. (U, S) \<in> lexord R \<and> P U \<and> P S}\<close>
    by auto
  moreover have \<open>finite {U. (U, S) \<in> lexord R \<and> P U \<and> P S}\<close>
    using finite by (metis (no_types, lifting) P_finite finite_subset mem_Collect_eq subsetI)
  ultimately show \<open>card (?f T) < card (?f S)\<close> by (simp add: psubset_card_mono)
qed


lemma wf_fst_wf_pair:
  assumes \<open>wf {(M', M). R M' M} \<close>
  shows \<open>wf {((M', N'), (M, N)). R M' M}\<close>
proof -
  have \<open>wf ({(M', M). R M' M} <*lex*> {})\<close>
    using assms by auto
  then show ?thesis
    by (rule wf_subset) auto
qed

lemma wf_snd_wf_pair:
  assumes \<open>wf {(M', M). R M' M} \<close>
  shows \<open>wf {((M', N'), (M, N)). R N' N}\<close>
proof -
  have wf: \<open>wf {((M', N'), (M, N)). R M' M}\<close>
    using assms wf_fst_wf_pair by auto
  then have wf: \<open>\<And>P. (\<forall>x. (\<forall>y. (y, x) \<in> {((M', N'), M, N). R M' M} \<longrightarrow> P y) \<longrightarrow> P x) \<Longrightarrow> All P\<close>
    unfolding wf_def by auto
  show ?thesis
    unfolding wf_def
    proof (intro allI impI)
      fix P :: \<open>'c \<times> 'a \<Rightarrow> bool\<close> and x :: \<open>'c \<times> 'a\<close>
      assume H: \<open>\<forall>x. (\<forall>y. (y, x) \<in> {((M', N'), M, y). R N' y} \<longrightarrow> P y) \<longrightarrow> P x\<close>
      obtain a b where x: \<open>x = (a, b)\<close> by (cases x)
      have P: \<open>P x = (P \<circ> (\<lambda>(a, b). (b, a))) (b, a)\<close>
        unfolding x by auto
      show \<open>P x\<close>
        using wf[of \<open>P o (\<lambda>(a, b). (b, a))\<close>] apply rule
          using H apply simp
        unfolding P by blast
    qed
qed

lemma wf_if_measure_f_notation2:
  assumes \<open>wf r\<close>
  shows \<open>wf {(b, h a)|b a. (f b, f (h a)) \<in> r}\<close>
  apply (rule wf_subset)
  using wf_if_measure_f[OF assms, of f] by auto

lemma wf_wf_if_measure'_notation2:
  assumes \<open>wf r\<close> and H: \<open>\<And>x y. P x \<Longrightarrow> g x y \<Longrightarrow> (f y, f (h x)) \<in> r\<close>
  shows \<open>wf {(y,h x)| y x. P x \<and> g x y}\<close>
proof -
  have \<open>wf {(b, h a)|b a. (f b, f (h a)) \<in> r}\<close> using assms(1) wf_if_measure_f_notation2 by auto
  then have \<open>wf {(b, h a)|b a. P a \<and> g a b \<and> (f b, f (h a)) \<in> r}\<close>
    using wf_subset[of _ \<open>{(b, h a)| b a. P a \<and> g a b \<and> (f b, f (h a)) \<in> r}\<close>] by auto
  moreover have \<open>{(b, h a)|b a. P a \<and> g a b \<and> (f b, f (h a)) \<in> r}
    \<subseteq> {(b, h a)|b a. (f b, f (h a)) \<in> r}\<close> by auto
  moreover have \<open>{(b, h a)|b a. P a \<and> g a b \<and> (f b, f (h a)) \<in> r} = {(b, h a)|b a. P a \<and> g a b}\<close>
    using H by auto
  ultimately show ?thesis using wf_subset by simp
qed

lemma power_ex_decomp:
  assumes \<open>(R^^n) S T\<close>
  shows
    \<open>\<exists>f. f 0 = S \<and> f n = T \<and> (\<forall>i. i < n \<longrightarrow> R (f i) (f (Suc i)))\<close>
  using assms
proof (induction n arbitrary: T)
  case 0
  then show \<open>?case\<close> by auto
next
  case (Suc n) note IH = this(1) and R = this(2)
  from R obtain T' where
    ST: \<open>(R^^n) S T'\<close> and
    T'T: \<open>R T' T\<close>
    by auto
  obtain f where
    [simp]: \<open>f 0 = S\<close> and
    [simp]: \<open>f n = T'\<close> and
    H: \<open>\<And>i. i < n \<Longrightarrow> R (f i) (f (Suc i))\<close>
    using IH[OF ST] by fast
  let ?f = \<open>f(Suc n := T)\<close>
  show ?case
    by (rule exI[of _ ?f])
      (use H ST T'T in auto)
qed


text \<open>The following lemma gives a bound on the maximal number of transitions of a sequence that is well-founded
  under the lexicographic ordering \<^term>\<open>lexn\<close> on natural numbers.
\<close>
lemma lexn_number_of_transition:
  assumes
    le: \<open>\<And>i. i < n \<Longrightarrow> ((f (Suc i)), (f i)) \<in> lexn less_than m\<close> and
    upper: \<open>\<And>i j. i \<le> n \<Longrightarrow> j < m \<Longrightarrow> (f i) ! j \<in> {0..<k}\<close> and
    \<open>finite A\<close> and
    k: \<open>k > 1\<close>
  shows \<open>n < k ^ Suc m\<close>
proof -
  define r where
    \<open>r x = zip x (map (\<lambda>i. k ^ (length x -i)) [0..<length x])\<close> for x :: \<open>nat list\<close>

  define s where
    \<open>s x = foldr (\<lambda>a b. a + b) (map (\<lambda>(a, b). a * b) x) 0\<close> for x :: \<open>(nat \<times> nat) list\<close>

  have [simp]: \<open>r [] = []\<close> \<open>s [] = 0\<close>
    by (auto simp: r_def s_def)

  have upt': \<open>m > 0 \<Longrightarrow> [0..< m] = 0 # map Suc [0..< m - 1]\<close> for m
    by (auto simp: map_Suc_upt upt_conv_Cons)

  have upt'': \<open>m > 0 \<Longrightarrow> [0..< m] = [0..< m - 1] @ [m-1]\<close> for m
    by (cases m) (auto simp: )

  have Cons: \<open>r (x # xs) = (x, k^(Suc (length xs))) # (r xs)\<close> for x xs
   unfolding r_def
   apply (subst upt')
   apply (clarsimp simp add: upt'' comp_def nth_append Suc_diff_le simp flip: zip_map2)
   apply (clarsimp simp add: upt'' comp_def nth_append Suc_diff_le simp flip: zip_map2)
   done

  have [simp]: \<open>s (ab # xs) = fst ab * snd ab + s xs\<close> for ab xs
    unfolding s_def by (cases ab) auto

  have le2: \<open>(\<forall>a \<in> set b. a < k) \<Longrightarrow> (k ^ (Suc (length b))) > s ((r b))\<close> for b
    apply (induction b arbitrary: f)
    using k apply (auto simp: Cons)
    apply (rule order.strict_trans1)
    apply (rule_tac j = \<open>(k - 1) * k *k ^ length b\<close> in Nat.add_le_mono1)
    subgoal for a b
      by auto
    apply (rule order.strict_trans2)
    apply (rule_tac b = \<open>(k - 1) * k * k ^ length b\<close> and d = \<open>(k * k ^ length b)\<close> in add_le_less_mono)
    apply (auto simp: mult.assoc comm_semiring_1_class.semiring_normalization_rules(2))
    done

  have \<open>s (r (f (Suc i))) < s (r (f i))\<close> if \<open>i < n\<close> for i
  proof -
    have i_n: \<open>Suc i \<le> n\<close> \<open>i \<le> n\<close>
      using that by auto
    have length: \<open>length (f i) = m\<close>  \<open>length (f (Suc i)) = m\<close>
     using le[OF that] by (auto dest: lexn_length)
    define xs and ys where \<open>xs = f i\<close> and \<open>ys = f (Suc i)\<close>

    show ?thesis
      using le[OF that] upper[OF i_n(2)] upper[OF i_n(1)] length Cons
      unfolding xs_def[symmetric] ys_def[symmetric]
    proof (induction m arbitrary: xs ys)
      case 0 then show ?case by auto
    next
      case (Suc m) note IH = this(1) and H = this(2) and p = this(3-)
      have IH: \<open>(tl ys, tl xs) \<in> lexn less_than m \<Longrightarrow> s (r (tl ys)) < s (r (tl xs))\<close>
        apply (rule IH)
        subgoal by auto
        subgoal for i using p(1)[of \<open>Suc i\<close>] p by (cases xs; auto)
        subgoal for i using p(2)[of \<open>Suc i\<close>] p by (cases ys; auto)
        subgoal using p by (cases xs) auto
        subgoal using p by auto
        subgoal using p by auto
        done
     have \<open>s (r (tl ys)) < k ^ (Suc (length (tl ys)))\<close>
       apply (rule le2)
       unfolding all_set_conv_all_nth
       using p by (simp add: nth_tl)
     then have \<open>ab * (k * k ^ length (tl ys)) + s (r (tl ys)) <
               ab * (k * k ^ length (tl ys)) + (k * k ^ length (tl ys))\<close> for ab
       by auto
     also have \<open>\<dots> ab  \<le> (ab + 1) * (k * k ^ length (tl ys))\<close> for ab
       by auto
     finally have less: \<open>ab < ac \<Longrightarrow> ab * (k * k ^ length (tl ys)) + s (r (tl ys)) <
                                    ac * (k * k ^ length (tl ys))\<close> for ab ac
     proof -
       assume a1: "\<And>ab. ab * (k * k ^ length (tl ys)) + s (r (tl ys)) <
                   (ab + 1) * (k * k ^ length (tl ys))"
       assume "ab < ac"
       then have "\<not> ac * (k * k ^ length (tl ys)) < (ab + 1) * (k * k ^ length (tl ys))"
         by (metis (no_types) One_nat_def Suc_leI add.right_neutral add_Suc_right
            mult_less_cancel2 not_less)
       then show ?thesis
         using a1 by (meson le_less_trans not_less)
     qed

    have \<open>ab < ac \<Longrightarrow>
        ab * (k * k ^ length (tl ys)) + s (r (tl ys))
        < ac * (k * k ^ length (tl xs)) + s (r (tl xs))\<close> for ab ac
        using less[of ab ac] p by auto
    then show ?case
         apply (cases xs; cases ys)
        using IH H p(3-5) by auto
    qed
  qed
  then have \<open>i\<le>n \<Longrightarrow> s (r (f i)) + i \<le> s (r (f 0))\<close> for i
    apply (induction i)
    subgoal by auto
    subgoal premises p for i
       using p(3)[of \<open>i-1\<close>] p(1,2)
      apply auto
      by (meson Nat.le_diff_conv2 Suc_leI Suc_le_lessD add_leD2 less_diff_conv less_le_trans p(3))
    done
  from this[of n] show \<open>n < k ^ Suc m\<close>
    using le2[of \<open>f 0\<close>] upper[of 0] k
    using le[of 0] apply (cases \<open>n = 0\<close>)
    by (auto dest!: lexn_length simp: all_set_conv_all_nth eq_commute[of _ m])
qed

end
