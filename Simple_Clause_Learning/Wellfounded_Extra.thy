theory Wellfounded_Extra
  imports
    Main
    Relation_Extra
begin

definition wf_on :: "'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bool"
  where "wf_on A r \<longleftrightarrow> (\<forall>P. (\<forall>x \<in> A. (\<forall>y \<in> A. (y, x) \<in> r \<longrightarrow> P y) \<longrightarrow> P x) \<longrightarrow> (\<forall>x \<in> A. P x))"

lemma wf_on_induct[consumes 1, case_names less in_dom]:
  assumes
    "wf_on A r" and
    "\<And>x. x \<in> A \<Longrightarrow> (\<And>y. y \<in> A \<Longrightarrow> (y, x) \<in> r \<Longrightarrow> P y) \<Longrightarrow> P x" and
    "x \<in> A"
  shows "P x"
  using assms unfolding wf_on_def by metis

lemma "wf_on UNIV r \<longleftrightarrow> wf r"
  by (simp add: wf_def wf_on_def)

definition wfp_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "wfp_on A R \<longleftrightarrow> (\<forall>P. (\<forall>x \<in> A. (\<forall>y \<in> A. R y x \<longrightarrow> P y) \<longrightarrow> P x) \<longrightarrow> (\<forall>x \<in> A. P x))"

abbreviation wfp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "wfp \<equiv> wfp_on UNIV"

lemma wfp_iff_wfP: "wfp R \<longleftrightarrow> wfP R"
  by (metis (no_types, opaque_lifting) UNIV_I wfPUNIVI wfP_induct_rule wfp_on_def)

lemma wfp_on_wf_on_iff[pred_set_conv]: "wfp_on A (\<lambda>x y. (x, y) \<in> r) \<longleftrightarrow> wf_on A r"
  by (simp add: wfp_on_def wf_on_def)

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

lemma minimal_if_wf_on:
  assumes wf: "wf_on A R" and "B \<subseteq> A" and "B \<noteq> {}"
  shows "\<exists>z \<in> B. \<forall>y. (y, z) \<in> R \<longrightarrow> y \<notin> B"
  using wf_onE_pf[OF wf \<open>B \<subseteq> A\<close>]
  by (metis Image_iff assms(3) subsetI)

lemma wf_on_if_minimal:
  assumes "\<And>B. B \<subseteq> A \<Longrightarrow> B \<noteq> {} \<Longrightarrow> \<exists>z \<in> B. \<forall>y. (y, z) \<in> R \<longrightarrow> y \<notin> B"
  shows "wf_on A R"
proof (rule wf_onI_pf)
  fix B
  show "B \<subseteq> A \<Longrightarrow> B \<subseteq> R `` B \<Longrightarrow> B = {}"
  using assms by (metis ImageE subset_eq)
qed

lemma wf_on_iff_minimal:
  "wf_on A r \<longleftrightarrow> (\<forall>B \<subseteq> A. B \<noteq> {} \<longrightarrow> (\<exists>z \<in> B. \<forall>y. (y, z) \<in> r \<longrightarrow> y \<notin> B))"
  using minimal_if_wf_on wf_on_if_minimal by metis

lemma wfp_on_iff_minimal:
  "wfp_on A R \<longleftrightarrow> (\<forall>B \<subseteq> A. B \<noteq> {} \<longrightarrow> (\<exists>z \<in> B. \<forall>y. R y z \<longrightarrow> y \<notin> B))"
  using wf_on_iff_minimal[of A, to_pred] by simp

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

end