(*  Title:       A Fair Ordered Resolution Prover for First-Order Clauses
    Author:      Anders Schlichtkrull <andschl at dtu.dk>, 2017
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2017
    Maintainer:  Anders Schlichtkrull <andschl at dtu.dk>
*)

section \<open>A Fair Ordered Resolution Prover for First-Order Clauses\<close>

text \<open>
TODO. Formalizes footnote.
\<close>

theory Fair_FO_Ordered_Resolution_Prover
  imports FO_Ordered_Resolution_Prover
begin

type_synonym 'a gclause = "'a clause \<times> nat"
type_synonym 'a gstate = "'a gclause multiset \<times> 'a gclause multiset \<times> 'a gclause multiset \<times> nat"

locale fair_FO_resolution_provers =
  FO_resolution_prover S subst_atm id_subst comp_subst renamings_apart atm_of_atms mgu less_atm
  for
    S :: "('a :: wellorder) clause \<Rightarrow> _" and
    subst_atm :: "'a \<Rightarrow> 's \<Rightarrow> 'a" and
    id_subst :: "'s" and
    comp_subst :: "'s \<Rightarrow> 's \<Rightarrow> 's" and
    renamings_apart :: "'a literal multiset list \<Rightarrow> 's list" and
    atm_of_atms :: "'a list \<Rightarrow> 'a" and
    mgu :: "'a set set \<Rightarrow> 's option" and
    less_atm :: "'a \<Rightarrow> 'a \<Rightarrow> bool" +
  fixes
    weight :: "'a clause \<times> nat \<Rightarrow> nat" 
  assumes
    weight_monotone: "m < n \<Longrightarrow> weight (C, m) < weight (C, n)"
begin

lemma generation_le_weight: "n \<le> weight (C, n)"
  by (induct n, simp, metis weight_monotone[of k "Suc k" for k] Suc_le_eq le_less le_trans)

lemma finite_ord_FO_resolution_inferences_between:
  assumes "finite CC"
  shows "finite (ord_FO_resolution_inferences_between CC D)"
  sorry

fun state_of_gstate :: "'a gstate \<Rightarrow> 'a state" where
  "state_of_gstate (N, P, Q, n) =
   (set_mset (image_mset fst N), set_mset (image_mset fst P), set_mset (image_mset fst Q))"

abbreviation clss_of_gstate :: "'a gstate \<Rightarrow> 'a clause set" where 
  "clss_of_gstate \<equiv> clss_of_state \<circ> state_of_gstate"

abbreviation P_of_gstate :: "'a gstate \<Rightarrow> 'a clause set" where 
  "P_of_gstate \<equiv> P_of_state \<circ> state_of_gstate"

abbreviation Q_of_gstate :: "'a gstate \<Rightarrow> 'a clause set" where 
  "Q_of_gstate \<equiv> Q_of_state \<circ> state_of_gstate"

abbreviation grounding_of_gstate :: "'a gstate \<Rightarrow> 'a clause set" where 
  "grounding_of_gstate \<equiv> grounding_of_state \<circ> state_of_gstate"

abbreviation Liminf_gstate :: "'a gstate llist \<Rightarrow> 'a state" where
  "Liminf_gstate \<equiv> Liminf_state \<circ> lmap state_of_gstate"

inductive fair_resolution_prover :: "'a gstate \<Rightarrow> 'a gstate \<Rightarrow> bool" (infix "\<leadsto>\<^sub>f" 50)  where
  tautology_deletion: "Neg A \<in># C \<Longrightarrow> Pos A \<in># C \<Longrightarrow> (N + {#(C, i)#}, P, Q, n) \<leadsto>\<^sub>f (N, P, Q, n)"
| forward_subsumption: "(\<exists>D \<in># image_mset fst (P + Q). subsumes D C) \<Longrightarrow>
    (N + {#(C, i)#}, P, Q, n) \<leadsto>\<^sub>f (N, P, Q, n)"
| backward_subsumption_P: "(\<exists>D \<in># image_mset fst N. strictly_subsumes D C) \<Longrightarrow>
    (N, P + {#(C, i)#}, Q, n) \<leadsto>\<^sub>f (N, P, Q, n)"
| backward_subsumption_Q: "(\<exists>D \<in># image_mset fst N. strictly_subsumes D C) \<Longrightarrow>
    (N, P, Q + {#(C, i)#}, n) \<leadsto>\<^sub>f (N, P, Q, n)"
| forward_reduction: "(\<exists>D L'. D + {#L'#} \<in># image_mset fst (P + Q) \<and> - L = L' \<cdot>l \<sigma> \<and> D \<cdot> \<sigma> \<subseteq># C) \<Longrightarrow>
    (N + {#(C + {#L#}, i)#}, P, Q, n) \<leadsto>\<^sub>f (N + {#(C, i)#}, P, Q, n)"
| backward_reduction_P: "(\<exists>D L'. D + {#L'#} \<in># image_mset fst N \<and> - L = L' \<cdot>l \<sigma> \<and> D \<cdot> \<sigma> \<subseteq># C) \<Longrightarrow>
    (N, P + {#(C + {#L#}, i)#}, Q, n) \<leadsto>\<^sub>f (N, P + {#(C, i)#}, Q, n)"
| backward_reduction_Q: "(\<exists>D L'. D + {#L'#} \<in># image_mset fst N \<and> - L = L' \<cdot>l \<sigma> \<and> D \<cdot> \<sigma> \<subseteq># C) \<Longrightarrow>
    (N, P, Q + {#(C + {#L#}, i)#}, n) \<leadsto>\<^sub>f (N, P + {#(C, i)#}, Q, n)"
| clause_processing: "(N + {#(C, i)#}, P, Q, n) \<leadsto>\<^sub>f (N, P + {#(C, i)#}, Q, n)"
| inference_computation: "(\<forall>(D, j) \<in># P. weight (C, i) \<le> weight (D, j)) \<Longrightarrow>
    N = mset_set ((\<lambda>D. (D, n))
      ` concls_of (ord_FO_resolution_inferences_between (set_mset (image_mset fst Q)) C)) \<Longrightarrow>
    ({#}, P + {#(C, i)#}, Q, n) \<leadsto>\<^sub>f (N, P, Q + {#(C, i)#}, Suc n)"

lemma fair_resolution_prover_resolution_prover':
  "St \<leadsto>\<^sub>f St' \<Longrightarrow> state_of_gstate St \<leadsto> state_of_gstate St'"
proof (induction rule: fair_resolution_prover.induct)
  case (tautology_deletion A C N i P Q n)
  then show ?case
    using resolution_prover.tautology_deletion by simp
next
  case (forward_subsumption P Q C N i n)
  then show ?case 
    using resolution_prover.forward_subsumption by simp
next
  case (backward_subsumption_P N C P i Q n)
  then show ?case
    using resolution_prover.backward_subsumption_P by simp
next
  case (backward_subsumption_Q N C P Q i n)
  then show ?case 
    using resolution_prover.backward_subsumption_Q by simp
next
  case (forward_reduction P Q L \<sigma> C N i n)
  then show ?case
    using resolution_prover.forward_reduction by simp
next
  case (backward_reduction_P N L \<sigma> C P i Q n)
  then show ?case 
    using resolution_prover.backward_reduction_P by simp
next
  case (backward_reduction_Q N L \<sigma> C P Q i n)
  then show ?case
    using resolution_prover.backward_reduction_Q by simp
next
  case (clause_processing N C P Q n)
  show ?case 
    using resolution_prover.clause_processing by simp
next
  case (inference_computation P C i N n Q)
  then show ?case 
    using resolution_prover.inference_computation finite_ord_FO_resolution_inferences_between
    by (auto simp: comp_def image_comp ord_FO_resolution_inferences_between_def)
qed

lemma fair_resolution_prover_resolution_prover:
  "chain (op \<leadsto>\<^sub>f) Sts \<Longrightarrow> chain (op \<leadsto>) (lmap state_of_gstate Sts)"
  using fair_resolution_prover_resolution_prover' using chain_lmap weight_monotone by metis

context
  fixes 
    Sts :: "'a gstate llist"
  assumes
    deriv: "chain (op \<leadsto>\<^sub>f) Sts" and
    finite_Sts0: "finite (clss_of_gstate (lnth Sts 0))" and
    empty_P0: "P_of_gstate (lnth Sts 0) = {}" and
    empty_Q0: "Q_of_gstate (lnth Sts 0) = {}"
begin

lemma monotone_fairness: "fair_state_seq (lmap state_of_gstate Sts)"
proof (rule ccontr)
  assume "\<not> fair_state_seq (lmap state_of_gstate Sts)"
  then obtain C where
    "C \<in> Liminf_llist (lmap N_of_state (lmap state_of_gstate Sts))
       \<union> Liminf_llist (lmap P_of_state (lmap state_of_gstate Sts))" 
    unfolding fair_state_seq_def Liminf_state_def by auto
  then show False
  proof
    assume "C \<in> Liminf_llist (lmap N_of_state (lmap state_of_gstate Sts))"
    then obtain i where
      "enat i < llength Sts"
      "\<And>j. i \<le> j \<and> enat j < llength Sts \<Longrightarrow> C \<in> N_of_state (state_of_gstate (lnth Sts j))" 
      unfolding Liminf_llist_def by auto
    then show False
      sorry (* *)
  next
    assume "C \<in> Liminf_llist (lmap P_of_state (lmap state_of_gstate Sts))"
    then show False 
      sorry
  qed
qed

lemma monotone_completeness:
  assumes 
    selection_renaming_invariant: "(\<And>\<rho> C. is_renaming \<rho> \<Longrightarrow> S (C \<cdot> \<rho>) = S C \<cdot> \<rho>)" and
    unsat: "\<not> satisfiable (grounding_of_state (Liminf_gstate Sts))" 
  shows "{#} \<in> clss_of_state (Liminf_gstate Sts)"
proof -
  have "state_of_gstate (lnth Sts 0) = lnth (lmap state_of_gstate Sts) 0"
    using lnth_lmap[of 0 Sts state_of_gstate, unfolded enat_0] chain_length_pos[OF deriv] by auto
  then have "finite (clss_of_state (lnth (lmap state_of_gstate Sts) 0))"
    using finite_Sts0 by auto
  moreover have "P_of_state (lnth (lmap state_of_gstate Sts) 0) = {}"
    using empty_P0 chain_length_pos[OF deriv] by (auto simp: enat_0)
  moreover have "Q_of_state (lnth (lmap state_of_gstate Sts) 0) = {}"
    using empty_Q0 chain_length_pos[OF deriv] by (auto simp: enat_0)
  moreover have "chain op \<leadsto> (lmap state_of_gstate Sts)"
    using deriv fair_resolution_prover_resolution_prover by blast 
  moreover have "\<forall>\<rho> C. is_renaming \<rho> \<longrightarrow> S (C \<cdot> \<rho>) = S C \<cdot> \<rho>"
    using selection_renaming_invariant by auto
  moreover have "fair_state_seq (lmap state_of_gstate Sts)"
    using monotone_fairness by auto
  moreover have "\<not> satisfiable (grounding_of_state (Liminf_state (lmap state_of_gstate Sts)))"
    using unsat by auto
  ultimately have "{#} \<in> clss_of_state (Liminf_state (lmap state_of_gstate Sts))" 
    using fair_state_seq_complete[of "lmap state_of_gstate Sts"] by auto
  then show "{#} \<in> clss_of_state (Liminf_gstate Sts)"
    by auto
qed 

end

end

locale fair_FO_resolution_prover_with_sum_product =
  fair_FO_resolution_provers S subst_atm id_subst comp_subst renamings_apart atm_of_atms mgu
    less_atm weight
  for
    S :: "('a :: wellorder) clause \<Rightarrow> _" and (* FIXME: assumption that no selection takes place? *)
    subst_atm :: "'a \<Rightarrow> 's \<Rightarrow> 'a" and
    id_subst :: "'s" and
    comp_subst :: "'s \<Rightarrow> 's \<Rightarrow> 's" and
    renamings_apart :: "'a literal multiset list \<Rightarrow> 's list" and
    atm_of_atms :: "'a list \<Rightarrow> 'a" and
    mgu :: "'a set set \<Rightarrow> 's option" and
    less_atm :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and
    weight :: "'a clause \<times> nat \<Rightarrow> nat" +
  fixes
    size_atm :: "'a \<Rightarrow> nat" and
    generation_factor :: nat and
    size_factor :: nat
  assumes
    generation_factor_pos: "generation_factor > 0" and
    weight_def: "weight (C, m) =
      generation_factor * m + size_factor * size_multiset (size_literal size_atm) C"
begin

sublocale fair_FO_resolution_provers
  using generation_factor_pos by unfold_locales (simp add: weight_def)

end

end
