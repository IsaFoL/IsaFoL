(*  Title:       A Fair Ordered Resolution Prover for First-Order Clauses with Weights
    Author:      Anders Schlichtkrull <andschl at dtu.dk>, 2017
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2017
    Maintainer:  Anders Schlichtkrull <andschl at dtu.dk>
*)

section \<open>A Fair Ordered Resolution Prover for First-Order Clauses with Weights\<close>

text \<open>
TODO. Formalizes footnote.
\<close>

theory Weighted_FO_Ordered_Resolution_Prover
  imports FO_Ordered_Resolution_Prover
begin

type_synonym 'a wclause = "'a clause \<times> nat"
type_synonym 'a wstate = "'a wclause multiset \<times> 'a wclause multiset \<times> 'a wclause multiset \<times> nat"

locale weighted_FO_resolution_prover =
  FO_resolution_prover S subst_atm id_subst comp_subst renamings_apart atm_of_atms mgu less_atm
  for
    S :: "('a :: wellorder) clause \<Rightarrow> 'a clause" and
    subst_atm :: "'a \<Rightarrow> 's \<Rightarrow> 'a" and
    id_subst :: "'s" and
    comp_subst :: "'s \<Rightarrow> 's \<Rightarrow> 's" and
    renamings_apart :: "'a clause list \<Rightarrow> 's list" and
    atm_of_atms :: "'a list \<Rightarrow> 'a" and
    mgu :: "'a set set \<Rightarrow> 's option" and
    less_atm :: "'a \<Rightarrow> 'a \<Rightarrow> bool" +
  fixes
    weight :: "'a clause \<times> nat \<Rightarrow> nat"
  assumes
    weight_mono: "m < n \<Longrightarrow> weight (C, m) < weight (C, n)"
begin

(* FIXME: generalize and add to Isabelle? *)
lemma generation_le_weight: "n \<le> weight (C, n)"
  by (induct n, simp, metis weight_mono[of k "Suc k" for k] Suc_le_eq le_less le_trans)

(* FIXME: move to FO_Ordered_Resolution_Prover *)
lemma finite_ord_FO_resolution_inferences_between:
  assumes "finite CC"
  shows "finite (ord_FO_resolution_inferences_between CC D)"
  sorry

fun state_of_wstate :: "'a wstate \<Rightarrow> 'a state" where
  "state_of_wstate (N, P, Q, n) =
   (set_mset (image_mset fst N), set_mset (image_mset fst P), set_mset (image_mset fst Q))"

(* FIXME: don't use \<circ> in abbreviations -- fragile w.r.t. simplifier when applied *)
abbreviation clss_of_wstate :: "'a wstate \<Rightarrow> 'a clause set" where
  "clss_of_wstate \<equiv> clss_of_state \<circ> state_of_wstate"

abbreviation P_of_wstate :: "'a wstate \<Rightarrow> 'a clause set" where
  "P_of_wstate \<equiv> P_of_state \<circ> state_of_wstate"

abbreviation Q_of_wstate :: "'a wstate \<Rightarrow> 'a clause set" where
  "Q_of_wstate \<equiv> Q_of_state \<circ> state_of_wstate"

abbreviation grounding_of_wstate :: "'a wstate \<Rightarrow> 'a clause set" where
  "grounding_of_wstate St \<equiv> grounding_of_state (state_of_wstate St)"

abbreviation Liminf_wstate :: "'a wstate llist \<Rightarrow> 'a state" where
  "Liminf_wstate Sts \<equiv> Liminf_state (lmap state_of_wstate Sts)"

inductive weighted_RP :: "'a wstate \<Rightarrow> 'a wstate \<Rightarrow> bool" (infix "\<leadsto>\<^sub>w" 50) where
  tautology_deletion: "Neg A \<in># C \<Longrightarrow> Pos A \<in># C \<Longrightarrow> (N + {#(C, i)#}, P, Q, n) \<leadsto>\<^sub>w (N, P, Q, n)"
| forward_subsumption: "D \<in># image_mset fst (P + Q) \<Longrightarrow> subsumes D C \<Longrightarrow>
    (N + {#(C, i)#}, P, Q, n) \<leadsto>\<^sub>w (N, P, Q, n)"
| backward_subsumption_P: "D \<in># image_mset fst N \<Longrightarrow> strictly_subsumes D C \<Longrightarrow>
    (N, P + {#(C, i)#}, Q, n) \<leadsto>\<^sub>w (N, P, Q, n)"
| backward_subsumption_Q: "D \<in># image_mset fst N \<Longrightarrow> strictly_subsumes D C \<Longrightarrow>
    (N, P, Q + {#(C, i)#}, n) \<leadsto>\<^sub>w (N, P, Q, n)"
| forward_reduction: "D + {#L'#} \<in># image_mset fst (P + Q) \<Longrightarrow> - L = L' \<cdot>l \<sigma> \<Longrightarrow> D \<cdot> \<sigma> \<subseteq># C \<Longrightarrow>
    (N + {#(C + {#L#}, i)#}, P, Q, n) \<leadsto>\<^sub>w (N + {#(C, i)#}, P, Q, n)"
| backward_reduction_P: "D + {#L'#} \<in># image_mset fst N \<Longrightarrow> - L = L' \<cdot>l \<sigma> \<Longrightarrow> D \<cdot> \<sigma> \<subseteq># C \<Longrightarrow>
    (N, P + {#(C + {#L#}, i)#}, Q, n) \<leadsto>\<^sub>w (N, P + {#(C, i)#}, Q, n)"
| backward_reduction_Q: "D + {#L'#} \<in># image_mset fst N \<Longrightarrow> - L = L' \<cdot>l \<sigma> \<Longrightarrow> D \<cdot> \<sigma> \<subseteq># C \<Longrightarrow>
    (N, P, Q + {#(C + {#L#}, i)#}, n) \<leadsto>\<^sub>w (N, P + {#(C, i)#}, Q, n)"
| clause_processing: "(N + {#(C, i)#}, P, Q, n) \<leadsto>\<^sub>w (N, P + {#(C, i)#}, Q, n)"
| inference_computation: "(\<forall>(D, j) \<in># P. weight (C, i) \<le> weight (D, j)) \<Longrightarrow>
    N = mset_set ((\<lambda>D. (D, n))
      ` concls_of (ord_FO_resolution_inferences_between (set_mset (image_mset fst Q)) C)) \<Longrightarrow>
    ({#}, P + {#(C, i)#}, Q, n) \<leadsto>\<^sub>w (N, P, Q + {#(C, i)#}, Suc n)"

lemma weighted_RP_imp_RP: "St \<leadsto>\<^sub>w St' \<Longrightarrow> state_of_wstate St \<leadsto> state_of_wstate St'"
proof (induction rule: weighted_RP.induct)
  case (inference_computation P C i N n Q)
  then show ?case
    using RP.inference_computation finite_ord_FO_resolution_inferences_between
    by (auto simp: comp_def image_comp ord_FO_resolution_inferences_between_def)
qed (use RP.intros in simp_all)

lemma weighted_RP_model:
  assumes step: "St \<leadsto>\<^sub>w St'"
  shows "I \<Turnstile>s grounding_of_wstate St' \<longleftrightarrow> I \<Turnstile>s grounding_of_wstate St"
  using RP_model[OF weighted_RP_imp_RP[OF step]] by (simp only: comp_def)

lemma final_weighted_RP: "\<not> ({#}, {#}, Q, n) \<leadsto>\<^sub>w St"
  by (auto elim: weighted_RP.cases)

context
  fixes
    Sts :: "'a wstate llist"
  assumes
    deriv: "chain (op \<leadsto>\<^sub>w) Sts" and
    finite_Sts0: "finite (clss_of_wstate (lhd Sts))" and
    empty_P0: "P_of_wstate (lhd Sts) = {}" and
    empty_Q0: "Q_of_wstate (lhd Sts) = {}"
begin

lemma deriv_RP: "chain (op \<leadsto>) (lmap state_of_wstate Sts)"
  using deriv weighted_RP_imp_RP by (metis chain_lmap)

lemma finite_Sts0_RP: "finite (clss_of_state (lhd (lmap state_of_wstate Sts)))"
  using finite_Sts0 chain_length_pos[OF deriv] by auto

lemma empty_P0_RP: "P_of_state (lhd (lmap state_of_wstate Sts)) = {}"
  using empty_P0 chain_length_pos[OF deriv] by auto

lemma empty_Q0_RP: "Q_of_state (lhd (lmap state_of_wstate Sts)) = {}"
  using empty_Q0 chain_length_pos[OF deriv] by auto

abbreviation S_gQ :: "'a clause \<Rightarrow> 'a clause" where
  "S_gQ \<equiv> S_Q (lmap state_of_wstate Sts)"

interpretation sq: selection S_gQ
  unfolding S_Q_def[OF deriv_RP finite_Sts0_RP empty_P0_RP empty_Q0_RP]
  using S_M_selects_subseteq S_M_selects_neg_lits selection_axioms by unfold_locales blast

interpretation gd: ground_resolution_with_selection S_gQ
  by unfold_locales

interpretation src: standard_redundancy_criterion_reductive gd.ord_\<Gamma>
  by unfold_locales

interpretation src: standard_redundancy_criterion_counterex_reducing gd.ord_\<Gamma>
  "ground_resolution_with_selection.INTERP S_gQ"
  by unfold_locales

lemmas ord_\<Gamma>_saturated_upto_complete = src.saturated_upto_complete

theorem weighted_RP_fair: "fair_state_seq (lmap state_of_wstate Sts)"
proof (rule ccontr)
  assume "\<not> fair_state_seq (lmap state_of_wstate Sts)"
  then obtain C where
    "C \<in> Liminf_llist (lmap N_of_state (lmap state_of_wstate Sts))
       \<union> Liminf_llist (lmap P_of_state (lmap state_of_wstate Sts))"
    unfolding fair_state_seq_def Liminf_state_def by auto
  then show False
  proof
    assume "C \<in> Liminf_llist (lmap N_of_state (lmap state_of_wstate Sts))"
    then obtain i where
      "enat i < llength Sts"
      "\<And>j. i \<le> j \<and> enat j < llength Sts \<Longrightarrow> C \<in> N_of_state (state_of_wstate (lnth Sts j))"
      unfolding Liminf_llist_def by auto
    then show False
      sorry (* *)
  next
    assume "C \<in> Liminf_llist (lmap P_of_state (lmap state_of_wstate Sts))"
    then show False
      sorry
  qed
qed

corollary weighted_RP_saturated: "src.saturated_upto (Liminf_llist (lmap grounding_of_wstate Sts))"
  using RP_saturated_if_fair[OF deriv_RP finite_Sts0_RP empty_P0_RP empty_Q0_RP
      weighted_RP_fair, unfolded llist.map_comp]
  by simp

corollary weighted_RP_complete:
  assumes "\<not> satisfiable (grounding_of_wstate (lhd Sts))"
  shows "{#} \<in> Q_of_state (Liminf_wstate Sts)"
  using assms RP_complete_if_fair[OF deriv_RP finite_Sts0_RP empty_P0_RP empty_Q0_RP weighted_RP_fair,
      simplified llist.map_sel(1)[OF chain_not_lnull[OF deriv]]]
  by blast

end

end

locale weighted_FO_resolution_prover_with_size_generation_factors =
  FO_resolution_prover S subst_atm id_subst comp_subst renamings_apart atm_of_atms mgu less_atm
  for
    S :: "('a :: wellorder) clause \<Rightarrow> 'a clause" and
    subst_atm :: "'a \<Rightarrow> 's \<Rightarrow> 'a" and
    id_subst :: "'s" and
    comp_subst :: "'s \<Rightarrow> 's \<Rightarrow> 's" and
    renamings_apart :: "'a literal multiset list \<Rightarrow> 's list" and
    atm_of_atms :: "'a list \<Rightarrow> 'a" and
    mgu :: "'a set set \<Rightarrow> 's option" and
    less_atm :: "'a \<Rightarrow> 'a \<Rightarrow> bool" +
  fixes
    size_atm :: "'a \<Rightarrow> nat" and
    size_factor :: nat and
    generation_factor :: nat
  assumes
    generation_factor_pos: "generation_factor > 0"
begin

fun weight :: "'a wclause \<Rightarrow> nat" where
  "weight (C, m) = size_factor * size_multiset (size_literal size_atm) C + generation_factor * m"

lemma weight_mono: "m < n \<Longrightarrow> weight (C, m) < weight (C, n)"
  using generation_factor_pos by simp

declare weight.simps [simp del]

sublocale weighted_FO_resolution_prover _ _ _ _ _ _ _ _ weight
  by unfold_locales (rule weight_mono)

notation weighted_RP (infix "\<leadsto>\<^sub>w" 50)

end

end
