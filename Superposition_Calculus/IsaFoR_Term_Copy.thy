(*  Title:       Integration of IsaFoR Terms and the Knuth-Bendix Order
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Author:      Anders Schlichtkrull <andschl at dtu.dk>, 2017
    Maintainer:  Anders Schlichtkrull <andschl at dtu.dk>
*)

section \<open>Integration of \textsf{IsaFoR} Terms and the Knuth--Bendix Order\<close>

text \<open>
This theory implements the abstract interface for atoms and substitutions using
the \textsf{IsaFoR} library.
\<close>

theory IsaFoR_Term_Copy
  imports
    First_Order_Terms.Unification
    "HOL-Cardinals.Wellorder_Extension"
    Open_Induction.Restricted_Predicates
    Knuth_Bendix_Order.KBO
begin

text \<open>
This part extends and integrates and the Knuth--Bendix order defined in
\textsf{IsaFoR}.
\<close>

record 'f weights =
  w :: "'f \<times> nat \<Rightarrow> nat"
  w0 :: nat
  pr_strict :: "'f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool"
  least :: "'f \<Rightarrow> bool"
  scf :: "'f \<times> nat \<Rightarrow> nat \<Rightarrow> nat"

class weighted =
  fixes weights :: "'a weights"
  assumes weights_adm:
    "admissible_kbo
       (w weights) (w0 weights) (pr_strict weights) ((pr_strict weights)\<^sup>=\<^sup>=) (least weights) (scf weights)"
  and pr_strict_total: "fi = gj \<or> pr_strict weights fi gj \<or> pr_strict weights gj fi"
  and pr_strict_asymp: "asymp (pr_strict weights)"
  and scf_ok: "i < n \<Longrightarrow> scf weights (f, n) i \<le> 1"

instantiation unit :: weighted begin

definition weights_unit :: "unit weights" where "weights_unit =
  \<lparr>w = Suc \<circ> snd, w0 = 1, pr_strict = \<lambda>(_, n) (_, m). n > m, least = \<lambda>_. True, scf = \<lambda>_ _. 1\<rparr>"

instance
  by (intro_classes, unfold_locales) (auto simp: weights_unit_def SN_iff_wf irreflp_def
      intro: asympI intro!: wf_subset[OF wf_inv_image[OF wf], of _ snd])
end

global_interpretation KBO:
  admissible_kbo
    "w (weights :: 'f :: weighted weights)" "w0 (weights :: 'f :: weighted weights)"
    "pr_strict weights" "((pr_strict weights)\<^sup>=\<^sup>=)" "least weights" "scf weights"
    defines weight = KBO.weight
    and kbo = KBO.kbo
  by (simp add: weights_adm)

lemma kbo_code[code]: "kbo s t =
  (let wt = weight t; ws = weight s in
  if vars_term_ms (KBO.SCF t) \<subseteq># vars_term_ms (KBO.SCF s) \<and> wt \<le> ws
  then
    (if wt < ws then (True, True)
    else
      (case s of
        Var y \<Rightarrow> (False, case t of Var x \<Rightarrow> True | Fun g ts \<Rightarrow> ts = [] \<and> least weights g)
      | Fun f ss \<Rightarrow>
          (case t of
            Var x \<Rightarrow> (True, True)
          | Fun g ts \<Rightarrow>
              if pr_strict weights (f, length ss) (g, length ts) then (True, True)
              else if (f, length ss) = (g, length ts) then lex_ext_unbounded kbo ss ts
              else (False, False))))
  else (False, False))"
  by (subst KBO.kbo.simps) (auto simp: Let_def split: term.splits)

definition "less_kbo s t = fst (kbo t s)"

lemma less_kbo_gtotal: "ground s \<Longrightarrow> ground t \<Longrightarrow> s = t \<or> less_kbo s t \<or> less_kbo t s"
  unfolding less_kbo_def using KBO.S_ground_total by (metis pr_strict_total subset_UNIV)

lemma less_kbo_subst:
  fixes \<sigma> :: "('f :: weighted, 'v) subst"
  shows "less_kbo s t \<Longrightarrow> less_kbo (s \<cdot> \<sigma>) (t \<cdot> \<sigma>)"
  unfolding less_kbo_def by (rule KBO.S_subst)

lemma wfP_less_kbo: "wfP less_kbo"
proof -
  have "SN {(x, y). fst (kbo x y)}"
    using pr_strict_asymp by (fastforce simp: asympI irreflp_def intro!: KBO.S_SN scf_ok)
  then show ?thesis
    unfolding SN_iff_wf wfP_def by (rule wf_subset) (auto simp: less_kbo_def)
qed

end
