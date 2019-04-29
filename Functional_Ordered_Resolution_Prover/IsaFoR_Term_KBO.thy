(*  Title:       A Well-Order on Terms that Extends IsaFoR's KBO
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Author:      Anders Schlichtkrull <andschl at dtu.dk>, 2017
    Maintainer:  Anders Schlichtkrull <andschl at dtu.dk>
*)

section \<open>A Well-Order on Terms that Extends IsaFoR's KBO\<close>

theory IsaFoR_Term_KBO
imports
  Functional_Ordered_Resolution_Prover.IsaFoR_Term
  Ord.KBO
begin

text \<open>
Since not all IsaFoR files we need are in the \emph{Archive of Formal Proof}, we cannot put this
theory file in the archive.
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
  by (intro_classes, unfold_locales) (auto simp: weights_unit_def SN_iff_wf asymp.simps irreflp_def
      intro!: wf_subset[OF wf_inv_image[OF wf], of _ snd])
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
    using pr_strict_asymp by (fastforce simp: asymp.simps irreflp_def intro!: KBO.S_SN scf_ok)
  then show ?thesis
    unfolding SN_iff_wf wfP_def by (rule wf_subset) (auto simp: less_kbo_def)
qed

instantiation "term" :: (weighted, type) linorder begin

definition "leq_term = (SOME leq. {(s,t). less_kbo s t} \<subseteq> leq \<and> Well_order leq \<and> Field leq = UNIV)"

lemma less_trm_extension: "{(s,t). less_kbo s t} \<subseteq> leq_term"
  unfolding leq_term_def
  by (rule someI2_ex[OF total_well_order_extension[OF wfP_less_kbo[unfolded wfP_def]]]) auto

lemma less_trm_well_order: "well_order leq_term"
  unfolding leq_term_def
  by (rule someI2_ex[OF total_well_order_extension[OF wfP_less_kbo[unfolded wfP_def]]]) auto

definition less_eq_term :: "('a :: weighted, 'b) term \<Rightarrow> _ \<Rightarrow> bool" where
  "less_eq_term = in_rel leq_term"
definition less_term :: "('a :: weighted, 'b) term \<Rightarrow> _ \<Rightarrow> bool" where
  "less_term s t = strict (\<le>) s t"

lemma leq_term_minus_Id: "leq_term - Id = {(x,y). x < y}"
  using less_trm_well_order
  unfolding well_order_on_def linear_order_on_def partial_order_on_def antisym_def less_term_def less_eq_term_def
  by auto

lemma less_term_alt: "(<) = in_rel (leq_term - Id)"
  by (simp add: in_rel_Collect_case_prod_eq leq_term_minus_Id)

instance
proof (standard, goal_cases less_less_eq refl trans antisym total)
  case (less_less_eq x y)
  then show ?case unfolding less_term_def ..
next
case (refl x)
  then show ?case using less_trm_well_order
    unfolding well_order_on_def linear_order_on_def partial_order_on_def preorder_on_def refl_on_def
      less_eq_term_def by auto
next
case (trans x y z)
  then show ?case using less_trm_well_order
    unfolding well_order_on_def linear_order_on_def partial_order_on_def preorder_on_def trans_def
      less_eq_term_def by auto
next
  case (antisym x y)
  then show ?case using less_trm_well_order
    unfolding well_order_on_def linear_order_on_def partial_order_on_def antisym_def
      less_eq_term_def by auto
next
  case (total x y)
  then show ?case using less_trm_well_order
    unfolding well_order_on_def linear_order_on_def partial_order_on_def preorder_on_def refl_on_def
      Relation.total_on_def less_eq_term_def by (cases "x = y") auto
qed

end

instantiation "term" :: (weighted, type) wellorder begin
instance
  using less_trm_well_order[unfolded well_order_on_def wf_def leq_term_minus_Id, THEN conjunct2]
  by intro_classes (atomize, auto)
end

lemma ground_less_less_kbo: "ground s \<Longrightarrow> ground t \<Longrightarrow> s < t \<Longrightarrow> less_kbo s t"
  using less_kbo_gtotal[of s t] less_trm_extension
  by (auto simp: less_term_def less_eq_term_def)

lemma less_kbo_less: "less_kbo s t \<Longrightarrow> s < t"
  using less_trm_extension
  by (auto simp: less_term_alt less_kbo_def KBO.S_irrefl)

lemma is_ground_atm_ground: "is_ground_atm t \<longleftrightarrow> ground t"
  unfolding is_ground_atm_def
  by (induct t) (fastforce simp: in_set_conv_nth list_eq_iff_nth_eq)+

end
