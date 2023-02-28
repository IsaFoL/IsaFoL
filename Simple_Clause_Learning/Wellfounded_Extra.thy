theory Wellfounded_Extra
  imports
    Main
    Relation_Extra
    "Ordered_Resolution_Prover.Lazy_List_Chain"
begin

definition wf_on :: "'a set \<Rightarrow> 'a rel \<Rightarrow> bool"
  where "wf_on A r \<longleftrightarrow> (\<forall>P. (\<forall>x \<in> A. (\<forall>y \<in> A. (y, x) \<in> r \<longrightarrow> P y) \<longrightarrow> P x) \<longrightarrow> (\<forall>x \<in> A. P x))"

abbreviation wf :: "'a rel \<Rightarrow> bool" where
  "wf \<equiv> wf_on UNIV"

definition wfp_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "wfp_on A R \<longleftrightarrow> (\<forall>P. (\<forall>x \<in> A. (\<forall>y \<in> A. R y x \<longrightarrow> P y) \<longrightarrow> P x) \<longrightarrow> (\<forall>x \<in> A. P x))"

abbreviation wfp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "wfp \<equiv> wfp_on UNIV"

abbreviation (input) wfP where
  "wfP \<equiv> wfp"

lemma wf_def[no_atp]: "wf r \<longleftrightarrow> (\<forall>P. (\<forall>x. (\<forall>y. (y, x) \<in> r \<longrightarrow> P y) \<longrightarrow> P x) \<longrightarrow> (\<forall>x. P x))"
  by (simp add: wf_on_def)

lemma wfP_def[no_atp]: "wfP r \<longleftrightarrow> wf {(x, y). r x y}"
  by (simp add: wfp_on_def wf_on_def)

lemma wf_onI:
  "(\<And>P x. (\<And>y. y \<in> A \<Longrightarrow> (\<And>z. z \<in> A \<Longrightarrow> (z, y) \<in> r \<Longrightarrow> P z) \<Longrightarrow> P y) \<Longrightarrow> x \<in> A \<Longrightarrow> P x) \<Longrightarrow> wf_on A r"
  unfolding wf_on_def by metis

thm wf_onI[of UNIV, simplified]

lemma wfI: "(\<And>P x. (\<And>y. (\<And>z. (z, y) \<in> r \<Longrightarrow> P z) \<Longrightarrow> P y) \<Longrightarrow> P x) \<Longrightarrow> wf r"
  by (auto simp: wf_on_def)

lemma wf_on_induct[consumes 1, case_names less in_dom]:
  assumes
    "wf_on A r" and
    "\<And>x. x \<in> A \<Longrightarrow> (\<And>y. y \<in> A \<Longrightarrow> (y, x) \<in> r \<Longrightarrow> P y) \<Longrightarrow> P x" and
    "x \<in> A"
  shows "P x"
  using assms unfolding wf_on_def by metis

lemma "wf_on UNIV r \<longleftrightarrow> Wellfounded.wf r"
  by (simp add: wf_on_def Wellfounded.wf_def)

lemma wfp_iff_wfP: "wfp R \<longleftrightarrow> Wellfounded.wfP R"
  by (metis (no_types, opaque_lifting) UNIV_I wfPUNIVI wfP_induct_rule wfp_on_def)

lemma wfp_on_wf_on_iff[pred_set_conv]: "wfp_on A (\<lambda>x y. (x, y) \<in> r) \<longleftrightarrow> wf_on A r"
  by (simp add: wfp_on_def wf_on_def)


subsection \<open>Basic Results\<close>

text \<open>Point-free characterization of well-foundedness\<close>

lemma wf_onE_pf:
  assumes wf: "wf_on A r" and "B \<subseteq> A" and "B \<subseteq> r `` B"
  shows "B = {}"
proof -
  from wf have "x \<notin> B" if "x \<in> A" for x
  proof (induction x rule: wf_on_induct)
    case (less x)
    then show ?case
      by (metis ImageE assms(2) assms(3) in_mono)
  next
    case in_dom
    show ?case
      using that .
  qed
  with \<open>B \<subseteq> A\<close> show ?thesis
    by blast
qed

lemma wfE_pf: "wf R \<Longrightarrow> A \<subseteq> R `` A \<Longrightarrow> A = {}"
  by (auto elim!: wf_onE_pf)

lemma wf_onI_pf:
  assumes "\<And>B. B \<subseteq> A \<Longrightarrow> B \<subseteq> R `` B \<Longrightarrow> B = {}"
  shows "wf_on A R"
  unfolding wf_on_def
proof (intro allI impI ballI)
  fix P :: "'a \<Rightarrow> bool" and x :: 'a
  let ?B = "{x \<in> A. \<not> P x}"
  assume "\<forall>x\<in>A. (\<forall>y\<in>A. (y, x) \<in> R \<longrightarrow> P y) \<longrightarrow> P x"
  hence "?B \<subseteq> R `` ?B" by blast
  with assms(1)[of ?B] have "{x \<in> A. \<not> P x} = {}"
    by simp
  moreover assume "x \<in> A"
  ultimately show "P x"
    by simp
qed

lemma wfI_pf: "(\<And>A. A \<subseteq> R `` A \<Longrightarrow> A = {}) \<Longrightarrow> wf R"
  by (auto intro!: wf_onI_pf)


subsubsection \<open>Minimal-element characterization of well-foundedness\<close>

lemma minimal_if_wf_on:
  assumes wf: "wf_on A R" and "B \<subseteq> A" and "B \<noteq> {}"
  shows "\<exists>z \<in> B. \<forall>y. (y, z) \<in> R \<longrightarrow> y \<notin> B"
  using wf_onE_pf[OF wf \<open>B \<subseteq> A\<close>]
  by (metis Image_iff assms(3) subsetI)

lemma wfE_min:
  assumes wf: "wf R" and Q: "x \<in> Q"
  obtains z where "z \<in> Q" "\<And>y. (y, z) \<in> R \<Longrightarrow> y \<notin> Q"
  using Q wfE_pf[OF wf, of Q] by blast

lemma wfE_min':
  "wf R \<Longrightarrow> Q \<noteq> {} \<Longrightarrow> (\<And>z. z \<in> Q \<Longrightarrow> (\<And>y. (y, z) \<in> R \<Longrightarrow> y \<notin> Q) \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  using wfE_min[of R _ Q] by blast

lemma wf_on_if_minimal:
  assumes "\<And>B. B \<subseteq> A \<Longrightarrow> B \<noteq> {} \<Longrightarrow> \<exists>z \<in> B. \<forall>y. (y, z) \<in> R \<longrightarrow> y \<notin> B"
  shows "wf_on A R"
proof (rule wf_onI_pf)
  fix B
  show "B \<subseteq> A \<Longrightarrow> B \<subseteq> R `` B \<Longrightarrow> B = {}"
  using assms by (metis ImageE subset_eq)
qed

lemma wfI_min:
  assumes a: "\<And>x Q. x \<in> Q \<Longrightarrow> \<exists>z\<in>Q. \<forall>y. (y, z) \<in> R \<longrightarrow> y \<notin> Q"
  shows "wf R"
proof (rule wfI_pf)
  fix A
  assume b: "A \<subseteq> R `` A"
  have False if "x \<in> A" for x
    using a[OF that] b by blast
  then show "A = {}" by blast
qed

lemma wf_on_iff_minimal: "wf_on A r \<longleftrightarrow> (\<forall>B \<subseteq> A. B \<noteq> {} \<longrightarrow> (\<exists>z \<in> B. \<forall>y. (y, z) \<in> r \<longrightarrow> y \<notin> B))"
  using minimal_if_wf_on wf_on_if_minimal by metis

lemma wf_iff_minimal: "wf r \<longleftrightarrow> (\<forall>B. B \<noteq> {} \<longrightarrow> (\<exists>z \<in> B. \<forall>y. (y, z) \<in> r \<longrightarrow> y \<notin> B))"
  using wf_on_iff_minimal[of UNIV, simplified] by metis

lemma wf_eq_minimal[no_atp]: "wf r \<longleftrightarrow> (\<forall>Q x. x \<in> Q \<longrightarrow> (\<exists>z\<in>Q. \<forall>y. (y, z) \<in> r \<longrightarrow> y \<notin> Q))"
  unfolding wf_iff_minimal by auto

lemma wfp_on_iff_minimal: "wfp_on A R \<longleftrightarrow> (\<forall>B \<subseteq> A. B \<noteq> {} \<longrightarrow> (\<exists>z \<in> B. \<forall>y. R y z \<longrightarrow> y \<notin> B))"
  using wf_on_iff_minimal[of A, to_pred] by simp

lemma wfp_iff_minimal: "wfp R \<longleftrightarrow> (\<forall>B. B \<noteq> {} \<longrightarrow> (\<exists>z \<in> B. \<forall>y. R y z \<longrightarrow> y \<notin> B))"
  using wf_eq_minimal[to_pred] by auto 

lemmas wfP_eq_minimal[no_atp] = wf_eq_minimal[to_pred]


lemma ex_trans_min_element_if_wf_on:
  assumes wf: "wf_on A r" and x_in: "x \<in> A"
  shows "\<exists>y \<in> A. (y, x) \<in> r\<^sup>* \<and> \<not>(\<exists>z \<in> A. (z, y) \<in> r)"
  using wf
proof (induction x rule: wf_on_induct)
  case (less x)
  thus ?case
    by (metis rtrancl.rtrancl_into_rtrancl rtrancl.rtrancl_refl)
next
  case in_dom
  thus ?case
    using x_in by metis
qed

lemma ex_trans_min_element_if_wfp_on: "wfp_on A R \<Longrightarrow> x \<in> A \<Longrightarrow> \<exists>y\<in>A. R\<^sup>*\<^sup>* y x \<and> \<not> (\<exists>z\<in>A. R z y)"
  by (rule ex_trans_min_element_if_wf_on[to_pred])

subsection \<open>Bound Restriction and Monotonicity\<close>

lemma wf_on_subset: "wf_on A r \<Longrightarrow> B \<subseteq> A \<Longrightarrow> wf_on B r"
  unfolding wf_on_iff_minimal
  by (meson order_trans)

lemma wfp_on_subset: "wfp_on A R \<Longrightarrow> B \<subseteq> A \<Longrightarrow> wfp_on B R"
  by (rule wf_on_subset[of A _ B, to_pred])  

lemma wf_on_mono_strong:
  "wf_on A r \<Longrightarrow> (\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> (x, y) \<in> q \<Longrightarrow> (x, y) \<in> r) \<Longrightarrow> wf_on A q"
  unfolding wf_on_iff_minimal
  by (meson in_mono)

lemma wfp_on_mono_strong:
  "wfp_on A R \<Longrightarrow> (\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> Q x y \<Longrightarrow> R x y) \<Longrightarrow> wfp_on A Q"
  by (rule wf_on_mono_strong[to_pred])


text \<open>Well-foundedness of subsets\<close>

lemma wf_subset: "wf r \<Longrightarrow> p \<subseteq> r \<Longrightarrow> wf p"
  by (simp add: wf_eq_minimal) fast

lemmas wfP_subset = wf_subset [to_pred]

text \<open>Well-foundedness of the empty relation\<close>

lemma wf_empty [iff]: "wf {}"
  by (simp add: wf_def)

lemma wfP_empty [iff]: "wfP (\<lambda>x y. False)"
proof -
  have "wfP bot"
    by (fact wf_empty[to_pred bot_empty_eq2])
  then show ?thesis
    by (simp add: bot_fun_def)
qed

lemma wf_Int1: "wf r \<Longrightarrow> wf (r \<inter> r')"
  by (erule wf_subset) (rule Int_lower1)

lemma wf_Int2: "wf r \<Longrightarrow> wf (r' \<inter> r)"
  by (erule wf_subset) (rule Int_lower2)



lemma asym_on_if_wf_on:
  assumes wf: "wf_on A r"
  shows "asym_on A r"
proof (rule asym_onI)
  fix x y
  show "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> (x, y) \<in> r \<Longrightarrow> (y, x) \<notin> r"
    using minimal_if_wf_on[OF wf, of "{x,y}"] by auto
qed

lemma asymp_on_if_wfp_on: "wfp_on A R \<Longrightarrow> asymp_on A R"
  by (rule asym_on_if_wf_on[to_pred])

lemma irrefl_on_if_wf_on: "wf_on A r \<Longrightarrow> irrefl_on A r"
  using asym_on_if_wf_on irrefl_on_if_asym_on by metis

lemma irreflp_on_if_wfp_on: "wfp_on A R \<Longrightarrow> irreflp_on A R"
  by (rule irrefl_on_if_wf_on[to_pred])

definition inv_imagep_on :: "'a set \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "inv_imagep_on A R f = (\<lambda>x y. x \<in> A \<and> y \<in> A \<and> R (f x) (f y))"

lemma wfp_on_inv_imagep:
  assumes wf: "wfp_on (f ` A) R"
  shows "wfp_on A (inv_imagep R f)"
  unfolding wfp_on_iff_minimal
proof (intro allI impI)
  fix B assume "B \<subseteq> A" and "B \<noteq> {}"
  hence "\<exists>z\<in>f ` B. \<forall>y. R y z \<longrightarrow> y \<notin> f ` B"
    using wf[unfolded wfp_on_iff_minimal, rule_format, of "f ` B"] by blast
  thus "\<exists>z\<in>B. \<forall>y. inv_imagep R f y z \<longrightarrow> y \<notin> B"
    unfolding inv_imagep_def
    by (metis image_iff)
qed

lemma wfp_on_if_convertible_to_wfp:
  assumes
    wf: "wfp_on (f ` A) Q" and
    convertible: "(\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> R x y \<Longrightarrow> Q (f x) (f y))"
  shows "wfp_on A R"
  unfolding wfp_on_iff_minimal
proof (intro allI impI)
  fix B assume "B \<subseteq> A" and "B \<noteq> {}"
  moreover from wf have "wfp_on A (inv_imagep Q f)"
    by (rule wfp_on_inv_imagep)
  ultimately obtain y where "y \<in> B" and "\<And>z. Q (f z) (f y) \<Longrightarrow> z \<notin> B"
    unfolding wfp_on_iff_minimal in_inv_imagep by metis
  thus "\<exists>z \<in> B. \<forall>y. R y z \<longrightarrow> y \<notin> B"
    using \<open>B \<subseteq> A\<close> convertible by blast
qed

definition lex_prodp where
  "lex_prodp R\<^sub>A R\<^sub>B x y \<longleftrightarrow> R\<^sub>A (fst x) (fst y) \<or> fst x = fst y \<and> R\<^sub>B (snd x) (snd y)"

lemma lex_prodp_lex_prod_iff[pred_set_conv]:
  "lex_prodp R\<^sub>A R\<^sub>B x y \<longleftrightarrow> (x, y) \<in> lex_prod {(x, y). R\<^sub>A x y} {(x, y). R\<^sub>B x y}"
  unfolding lex_prodp_def lex_prod_def by auto

lemma lex_prod_lex_prodp_iff:
  "lex_prod {(x, y). R\<^sub>A x y} {(x, y). R\<^sub>B x y} = {(x, y). lex_prodp R\<^sub>A R\<^sub>B x y}"
  unfolding lex_prodp_def lex_prod_def by auto

lemma wf_on_lex_prod:
  assumes wfA: "wf_on A r\<^sub>A" and wfB: "wf_on B r\<^sub>B"
  shows "wf_on (A \<times> B) (r\<^sub>A <*lex*> r\<^sub>B)"
  unfolding wf_on_iff_minimal
proof (intro allI impI)
  fix AB assume "AB \<subseteq> A \<times> B" and "AB \<noteq> {}"
  hence "fst ` AB \<subseteq> A" and "snd ` AB \<subseteq> B"
    by auto

  from \<open>fst ` AB \<subseteq> A\<close> \<open>AB \<noteq> {}\<close> obtain a where
    a_in: "a \<in> fst ` AB" and
    a_minimal: "(\<forall>y. (y, a) \<in> r\<^sub>A \<longrightarrow> y \<notin> fst ` AB)"
    using wfA[unfolded wf_on_iff_minimal, rule_format, of "fst ` AB"]
    by auto

  from \<open>snd ` AB \<subseteq> B\<close> \<open>AB \<noteq> {}\<close> a_in obtain b where
    b_in: "b \<in> snd ` {p \<in> AB. fst p = a}" and
    b_minimal: "(\<forall>y. (y, b) \<in> r\<^sub>B \<longrightarrow> y \<notin> snd ` {p \<in> AB. fst p = a})"
    using wfB[unfolded wf_on_iff_minimal, rule_format, of "snd ` {p \<in> AB. fst p = a}"]
    by blast

  show "\<exists>z\<in>AB. \<forall>y. (y, z) \<in> r\<^sub>A <*lex*> r\<^sub>B \<longrightarrow> y \<notin> AB"
  proof (rule bexI)
    show "(a, b) \<in> AB"
      using b_in by fastforce
  next
    show "\<forall>y. (y, (a, b)) \<in> r\<^sub>A <*lex*> r\<^sub>B \<longrightarrow> y \<notin> AB"
    proof (intro allI impI)
      fix p assume "(p, (a, b)) \<in> r\<^sub>A <*lex*> r\<^sub>B"
      hence "(fst p, a) \<in> r\<^sub>A \<or> fst p = a \<and> (snd p, b) \<in> r\<^sub>B"
        unfolding lex_prod_def by auto
      then show "p \<notin> AB"
      proof (elim disjE conjE)
        assume "(fst p, a) \<in> r\<^sub>A"
        hence "fst p \<notin> fst ` AB"
          using a_minimal by simp
        thus ?thesis
          by auto
      next
        assume "fst p = a" and "(snd p, b) \<in> r\<^sub>B"
        hence "snd p \<notin> snd ` {p \<in> AB. fst p = a}"
          using b_minimal by simp
        thus "p \<notin> AB"
          using \<open>fst p = a\<close> by auto
      qed
    qed
  qed
qed

lemma wfp_on_lex_prodp: "wfp_on A R\<^sub>A \<Longrightarrow> wfp_on B R\<^sub>B \<Longrightarrow> wfp_on (A \<times> B) (lex_prodp R\<^sub>A R\<^sub>B)"
  by (rule wf_on_lex_prod[to_pred, unfolded lex_prod_lex_prodp_iff, to_pred])

corollary wfp_lex_prodp: "wfp R\<^sub>A \<Longrightarrow> wfp R\<^sub>B \<Longrightarrow> wfp (lex_prodp R\<^sub>A R\<^sub>B)"
  by (rule wfp_on_lex_prodp[of UNIV _ UNIV, unfolded UNIV_Times_UNIV])

lemma wfp_on_sup_if_convertible_to_wfp:
  includes lattice_syntax
  assumes
    wf_S: "wfp_on A S" and
    wf_Q: "wfp_on (f ` A) Q" and
    convertible_R: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> R x y \<Longrightarrow> Q (f x) (f y)" and
    convertible_S: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> S x y \<Longrightarrow> Q (f x) (f y) \<or> f x = f y"
  shows "wfp_on A (R \<squnion> S)"
proof (rule wfp_on_if_convertible_to_wfp)
  show "wfp_on ((\<lambda>x. (f x, x)) ` A) (lex_prodp Q S)"
  proof (rule wfp_on_subset)
    show "wfp_on (f ` A \<times> A) (lex_prodp Q S)"
      by (rule wfp_on_lex_prodp[OF wf_Q wf_S])
  next
    show "(\<lambda>x. (f x, x)) ` A \<subseteq> f ` A \<times> A"
      by auto
  qed
next
  fix x y
  show "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> (R \<squnion> S) x y \<Longrightarrow> lex_prodp Q S (f x, x) (f y, y)"
    using convertible_R convertible_S
    by (auto simp add: lex_prodp_def)
qed

lemma wf_on_iff_wf: "wf_on A r \<longleftrightarrow> wf {(x, y) \<in> r. x \<in> A \<and> y \<in> A}"
proof (rule iffI)
  assume wf: "wf_on A r"
  show "wf {(x, y) \<in> r. x \<in> A \<and> y \<in> A}"
    unfolding wf_def
  proof (intro allI impI ballI)
    fix P x
    assume IH: "\<forall>x. (\<forall>y. (y, x) \<in> {(x, y). (x, y) \<in> r \<and> x \<in> A \<and> y \<in> A} \<longrightarrow> P y) \<longrightarrow> P x"
    show "P x"
    proof (cases "x \<in> A")
      case True
      from wf show ?thesis
      proof (induction x rule: wf_on_induct)
        case (less x)
        then show ?case
          by (auto intro: IH[rule_format])
      next
        case in_dom
        show ?case
          using True .
      qed
    next
      case False
      then show ?thesis
        by (auto intro: IH[rule_format])
    qed
  qed
next
  assume wf: "wf {(x, y). (x, y) \<in> r \<and> x \<in> A \<and> y \<in> A}"
  show "wf_on A r"
    unfolding wf_on_def
  proof (intro allI impI ballI)
    fix P x
    assume IH: "\<forall>x\<in>A. (\<forall>y\<in>A. (y, x) \<in> r \<longrightarrow> P y) \<longrightarrow> P x" and "x \<in> A"
    show "P x"
      using wf \<open>x \<in> A\<close>
    proof (induction x rule: wf_on_induct)
      case (less y)
      hence "\<And>z. (z, y) \<in> r \<Longrightarrow> z \<in> A \<Longrightarrow> P z"
        by simp
      thus ?case
        using IH[rule_format, OF \<open>y \<in> A\<close>] by simp
    next
      case in_dom
      show ?case
        by simp
    qed
  qed
qed

lemma wfp_on_iff_wfp: "wfp_on A R \<longleftrightarrow> wfp (\<lambda>x y. R x y \<and>  x \<in> A \<and> y \<in> A)"
  by (rule wf_on_iff_wf[to_pred])

lemma chain_lnth_rtranclp:
  assumes
    chain: "Lazy_List_Chain.chain R xs" and
    len: "enat j < llength xs"
  shows "R\<^sup>*\<^sup>* (lhd xs) (lnth xs j)"
  using len
proof (induction j)
  case 0
  from chain obtain x xs' where "xs = LCons x xs'"
    by (auto elim: chain.cases)
  thus ?case
    by simp
next
  case (Suc j)
  then show ?case
    by (metis Suc_ile_eq chain chain_lnth_rel less_le_not_le rtranclp.simps)
qed

lemma chain_conj_rtranclpI:
  fixes xs :: "'a llist"
  assumes "Lazy_List_Chain.chain (\<lambda>x y. R x y) (LCons init xs)"
  shows "Lazy_List_Chain.chain (\<lambda>x y. R x y \<and> R\<^sup>*\<^sup>* init x) (LCons init xs)"
proof (intro lnth_rel_chain allI impI conjI)
  show "\<not> lnull (LCons init xs)"
    by simp
next
  fix j
  assume hyp: "enat (j + 1) < llength (LCons init xs)"

  from hyp show "R (lnth (LCons init xs) j) (lnth (LCons init xs) (j + 1))"
    using assms[THEN chain_lnth_rel, of j] by simp

  from hyp show "R\<^sup>*\<^sup>* init (lnth (LCons init xs) j)"
    using assms[THEN chain_lnth_rtranclp, of j]
    by (simp add: Suc_ile_eq)
qed

lemma rtranclp_implies_ex_lfinite_chain:
  assumes run: "R\<^sup>*\<^sup>* x\<^sub>0 x"
  shows "\<exists>xs. lfinite xs \<and> chain (\<lambda>y z. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y) (LCons x\<^sub>0 xs) \<and> llast (LCons x\<^sub>0 xs) = x"
  using run
proof (induction x rule: rtranclp_induct)
  case base
  then show ?case
    by (meson chain.chain_singleton lfinite_code(1) llast_singleton)
next
  case (step y z)
  from step.IH obtain xs where
    "lfinite xs" and "chain (\<lambda>y z. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y) (LCons x\<^sub>0 xs)" and "llast (LCons x\<^sub>0 xs) = y"
    by auto
  let ?xs = "lappend xs (LCons z LNil)"
  show ?case
  proof (intro exI conjI)
    show "lfinite ?xs"
      using \<open>lfinite xs\<close> by simp
  next
    show "chain (\<lambda>y z. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y) (LCons x\<^sub>0 ?xs)"
      using \<open>chain (\<lambda>y z. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y) (LCons x\<^sub>0 xs)\<close> \<open>llast (LCons x\<^sub>0 xs) = y\<close>
        chain.chain_singleton chain_lappend step.hyps(1) step.hyps(2)
      by fastforce
  next
    show "llast (LCons x\<^sub>0 ?xs) = z"
      by (simp add: \<open>lfinite xs\<close> llast_LCons)
  qed
qed

lemma chain_conj_rtranclpD:
  fixes xs :: "'a llist"
  assumes inf: "\<not> lfinite xs" and chain: "chain (\<lambda>y z. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y) xs"
  shows "\<exists>ys. lfinite ys \<and> chain (\<lambda>y z. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y) (lappend ys xs) \<and> lhd (lappend ys xs) = x\<^sub>0"
  using chain
proof (cases "\<lambda>y z. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y" xs rule: chain.cases)
  case (chain_singleton x)
  with inf have False
    by simp
  thus ?thesis ..
next
  case (chain_cons xs' x)
  hence "R\<^sup>*\<^sup>* x\<^sub>0 x"
    by auto
  thus ?thesis
  proof (cases R x\<^sub>0 x rule: rtranclp.cases)
    case rtrancl_refl
    then show ?thesis
      using chain local.chain_cons(1) by force
  next
    case (rtrancl_into_rtrancl x\<^sub>n)
    then obtain ys where
      lfin_ys: "lfinite ys" and
      chain_ys: "chain (\<lambda>y z. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y) (LCons x\<^sub>0 ys)" and
      llast_ys: "llast (LCons x\<^sub>0 ys) = x\<^sub>n"
      by (auto dest: rtranclp_implies_ex_lfinite_chain)
    show ?thesis
    proof (intro exI conjI)
      show "lfinite (LCons x\<^sub>0 ys)"
        using lfin_ys
        by simp
    next
      have "R (llast (LCons x\<^sub>0 ys)) (lhd xs)"
        using rtrancl_into_rtrancl(2) chain_cons(1) llast_ys
        by simp
      moreover have "R\<^sup>*\<^sup>* x\<^sub>0 (llast (LCons x\<^sub>0 ys))"
        using rtrancl_into_rtrancl(1,2)
        using lappend_code(2)[of x\<^sub>0 ys xs]
          lhd_LCons[of x\<^sub>0 "(lappend ys xs)"] local.chain_cons(1)
        using llast_ys
        by fastforce
      ultimately show "chain (\<lambda>y z. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y) (lappend (LCons x\<^sub>0 ys) xs)"
        using chain_lappend[OF chain_ys chain]
        by metis
    next
      show "lhd (lappend (LCons x\<^sub>0 ys) xs) = x\<^sub>0"
        by simp
    qed 
  qed
qed

lemma wfp_on_rtranclp_conversep_iff_no_infinite_down_chain_llist:
  fixes R x\<^sub>0
  shows "wfp_on {x. R\<^sup>*\<^sup>* x\<^sub>0 x} R\<inverse>\<inverse> \<longleftrightarrow> (\<nexists>xs. \<not> lfinite xs \<and> Lazy_List_Chain.chain R (LCons x\<^sub>0 xs))"
proof (rule iffI)
  assume "wfp_on {x. R\<^sup>*\<^sup>* x\<^sub>0 x} R\<inverse>\<inverse>"
  hence "wfp (\<lambda>z y. R\<inverse>\<inverse> z y \<and> z \<in> {x. R\<^sup>*\<^sup>* x\<^sub>0 x} \<and> y \<in> {x. R\<^sup>*\<^sup>* x\<^sub>0 x})"
    using wfp_on_iff_wfp by blast
  hence "wfp (\<lambda>z y. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y)"
    by (auto elim: wfp_on_mono_strong)
  hence "Wellfounded.wfP (\<lambda>z y. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y)"
    by (simp add: wfp_iff_wfP)
  hence "\<nexists>xs. \<not> lfinite xs \<and> Lazy_List_Chain.chain (\<lambda>y z. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y) xs"
    unfolding wfP_iff_no_infinite_down_chain_llist
    by (metis (no_types, lifting) Lazy_List_Chain.chain_mono conversepI)
  hence "\<nexists>xs. \<not> lfinite xs \<and> Lazy_List_Chain.chain (\<lambda>y z. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y) (LCons x\<^sub>0 xs)"
    by (meson lfinite_LCons)
  thus "\<nexists>xs. \<not> lfinite xs \<and> Lazy_List_Chain.chain R (LCons x\<^sub>0 xs)"
    using chain_conj_rtranclpI
    by fastforce
next
  assume "\<nexists>xs. \<not> lfinite xs \<and> Lazy_List_Chain.chain R (LCons x\<^sub>0 xs)"
  hence no_inf_chain: "\<nexists>xs. \<not> lfinite xs \<and> chain (\<lambda>y z. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y) (LCons x\<^sub>0 xs)"
    by (metis (mono_tags, lifting) Lazy_List_Chain.chain_mono)
  have "\<nexists>xs. \<not> lfinite xs \<and> chain (\<lambda>y z. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y) xs"
  proof (rule notI, elim exE conjE)
    fix xs assume "\<not> lfinite xs" and "chain (\<lambda>y z. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y) xs"
    then obtain ys where
      "lfinite ys" and "chain (\<lambda>y z. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y) (lappend ys xs)" and "lhd (lappend ys xs) = x\<^sub>0"
    by (auto dest: chain_conj_rtranclpD)
    hence "\<exists>xs. \<not> lfinite xs \<and> chain (\<lambda>y z. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y) (LCons x\<^sub>0 xs)"
    proof (intro exI conjI)
      show "\<not> lfinite (ltl (lappend ys xs))"
        using \<open>\<not> lfinite xs\<close> lfinite_lappend lfinite_ltl
        by blast
    next
      show "chain (\<lambda>y z. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y) (LCons x\<^sub>0 (ltl (lappend ys xs)))"
        using \<open>chain (\<lambda>y z. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y) (lappend ys xs)\<close> \<open>lhd (lappend ys xs) = x\<^sub>0\<close>
          chain_not_lnull lhd_LCons_ltl
        by fastforce
    qed
    with no_inf_chain show False
      by argo
  qed
  hence "Wellfounded.wfP (\<lambda>z y. R y z \<and> y \<in> {x. R\<^sup>*\<^sup>* x\<^sub>0 x})"
    unfolding wfP_iff_no_infinite_down_chain_llist
    using Lazy_List_Chain.chain_mono by fastforce
  hence "wfp (\<lambda>z y. R y z \<and> y \<in> {x. R\<^sup>*\<^sup>* x\<^sub>0 x})"
    unfolding wfp_iff_wfP by argo
  hence "wfp (\<lambda>z y. R\<inverse>\<inverse> z y \<and> z \<in> {x. R\<^sup>*\<^sup>* x\<^sub>0 x} \<and> y \<in> {x. R\<^sup>*\<^sup>* x\<^sub>0 x})"
    by (auto elim: wfp_on_mono_strong)
  thus "wfp_on {x. R\<^sup>*\<^sup>* x\<^sub>0 x} R\<inverse>\<inverse>"
    unfolding wfp_on_iff_wfp[of "{x. R\<^sup>*\<^sup>* x\<^sub>0 x}" "R\<inverse>\<inverse>"] by argo
qed


section \<open>Backward-compatibility Layer\<close>

lemma wfP_wf_eq[no_atp]: "wfP (\<lambda>x y. (x, y) \<in> r) = wf r"
  by (rule wfp_on_wf_on_iff)

lemma wfUNIVI[no_atp]: "(\<And>P x. (\<forall>x. (\<forall>y. (y, x) \<in> r \<longrightarrow> P y) \<longrightarrow> P x) \<Longrightarrow> P x) \<Longrightarrow> wf r"
  using wfI by blast

lemmas wfPUNIVI = wfUNIVI [to_pred]

text \<open>Restriction to domain \<open>A\<close> and range \<open>B\<close>.
  If \<open>r\<close> is well-founded over their intersection, then \<open>wf r\<close>.\<close>
lemma wfI':
  assumes "r \<subseteq> A \<times> B"
    and "\<And>x P. \<lbrakk>\<forall>x. (\<forall>y. (y, x) \<in> r \<longrightarrow> P y) \<longrightarrow> P x;  x \<in> A; x \<in> B\<rbrakk> \<Longrightarrow> P x"
  shows "wf r"
  using assms unfolding wf_def by blast

end