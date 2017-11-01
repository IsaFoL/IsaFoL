(*  Title:       A Concrete Simple Ordered Resolution Prover for First-Order Clauses
    Author:      Anders Schlichtkrull <andschl at dtu.dk>, 2017
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2017
    Maintainer:  Anders Schlichtkrull <andschl at dtu.dk>
*)

section \<open>A Concrete Simple Ordered Resolution Prover for First-Order Clauses\<close>

text \<open>
This material is based on Section 4.3 (``A Simple Resolution Prover for First-Order Clauses) of 
Bachmair and Ganzinger's chapter. Specifically, it formalizes the prover in Figure 5 called
The Resolution Prover RP and its related lemmas and theorems including 
4.10, 4.11 and 4.13 (completeness of the prover).
\<close>

theory Concrete_FO_Ordered_Resolution_Prover
  imports Abstract_FO_Ordered_Resolution_Prover
begin

type_synonym 'a weighted_clause = "'a clause \<times> nat"
type_synonym 'a weighted_state =
  "'a weighted_clause set \<times> 'a weighted_clause set \<times> 'a weighted_clause set \<times> nat"

locale FO_resolution_prover_with_weights =
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

fun state_of_weighted_state :: "'a weighted_state \<Rightarrow> 'a state" where
  "state_of_weighted_state (N, P, Q, n) = (fst ` N, fst ` P, fst ` Q)"

abbreviation clss_of_weighted_state :: "'a weighted_state \<Rightarrow> 'a clause set" where 
  "clss_of_weighted_state \<equiv> clss_of_state \<circ> state_of_weighted_state"

abbreviation P_of_weighted_state :: "'a weighted_state \<Rightarrow> 'a clause set" where 
  "P_of_weighted_state \<equiv> P_of_state \<circ> state_of_weighted_state"

abbreviation Q_of_weighted_state :: "'a weighted_state \<Rightarrow> 'a clause set" where 
  "Q_of_weighted_state \<equiv> Q_of_state \<circ> state_of_weighted_state"

abbreviation grounding_of_weighted_state :: "'a weighted_state \<Rightarrow> 'a clause set" where 
  "grounding_of_weighted_state \<equiv> grounding_of_state \<circ> state_of_weighted_state"

abbreviation limit_weighted_state :: "'a weighted_state llist \<Rightarrow> 'a state" where
  "limit_weighted_state \<equiv> limit_state \<circ> lmap state_of_weighted_state"

inductive resolution_prover_with_weights :: "'a weighted_state \<Rightarrow> 'a weighted_state \<Rightarrow> bool" (infix "\<leadsto>\<^sub>w" 50)  where
  tautology_deletion: "Neg A \<in># C \<Longrightarrow> Pos A \<in># C \<Longrightarrow> (N \<union> {(C, i)}, P, Q, n) \<leadsto>\<^sub>w (N, P, Q, n)"
| forward_subsumption: "(\<exists>(D, j) \<in> P \<union> Q. subsumes D C) \<Longrightarrow> (N \<union> {(C, i)}, P, Q, n) \<leadsto>\<^sub>w (N, P, Q, n)"
| backward_subsumption_P: "(\<exists>(D, j) \<in> N. strictly_subsumes D C) \<Longrightarrow> (N, P \<union> {(C, i)}, Q, n) \<leadsto>\<^sub>w (N, P, Q, n)"
| backward_subsumption_Q: "(\<exists>(D, j) \<in> N. strictly_subsumes D C) \<Longrightarrow> (N, P, Q \<union> {(C, i)}, n) \<leadsto>\<^sub>w (N, P, Q, n)"
| forward_reduction: "(\<exists>D L'. (D + {#L'#}, j) \<in> P \<union> Q \<and> - L = L' \<cdot>l \<sigma> \<and> D \<cdot> \<sigma> \<le># C) \<Longrightarrow>
    (N \<union> {(C + {#L#}, i)}, P, Q, n) \<leadsto>\<^sub>w (N \<union> {(C, i)}, P, Q, n)"
| backward_reduction_P: "(\<exists>D L'. (D + {#L'#}, j) \<in> N \<and> - L = L' \<cdot>l \<sigma> \<and> D \<cdot> \<sigma> \<le># C) \<Longrightarrow>
    (N, P \<union> {(C + {#L#}, i)}, Q, n) \<leadsto>\<^sub>w (N, P \<union> {(C, i)}, Q, n)"
| backward_reduction_Q: "(\<exists>D L'. (D + {#L'#}, j) \<in> N \<and> - L = L' \<cdot>l \<sigma> \<and> D \<cdot> \<sigma> \<le># C) \<Longrightarrow>
    (N, P, Q \<union> {(C + {#L#}, i)}, n) \<leadsto>\<^sub>w (N, P \<union> {(C, i)}, Q, n)"
| clause_processing: "(N \<union> {(C, i)}, P, Q, n) \<leadsto>\<^sub>w (N, P \<union> {(C, i)}, Q, n)"
| inference_computation:
    "(\<forall>(D, j) \<in> P. weight (C, i) \<le> weight (D, j)) \<Longrightarrow>
     N = (\<lambda>D. (D, Suc n)) ` concls_of (ord_FO_resolution_inferences_between (fst ` Q) C) \<Longrightarrow>
     ({}, P \<union> {(C, i)}, Q, n) \<leadsto>\<^sub>w (N, P, Q \<union> {(C, i)}, Suc n)"

lemma generation_no_lte_weight: "n \<le> weight (C, n)"
proof(induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case using weight_monotone[of n "Suc n" C] by auto
qed

lemma resolution_prover_with_weights_resolution_prover':
  assumes "St \<leadsto>\<^sub>w St'"
  shows "state_of_weighted_state St \<leadsto> state_of_weighted_state St'"
  using assms proof (induction rule: resolution_prover_with_weights.induct)
  case (tautology_deletion A C N i P Q n)
  then show ?case
    using resolution_prover.tautology_deletion by auto
next
  case (forward_subsumption P Q C N i n)
  then have "\<exists>D\<in>fst ` P \<union> fst ` Q. subsumes D C"
    by force
  then show ?case 
    using resolution_prover.forward_subsumption[of "fst ` P" "fst ` Q" C] by auto
next
  case (backward_subsumption_P N C P i Q n)
  then have "\<exists>D\<in>fst ` N. strictly_subsumes D C"
    by force
  then show ?case
    using resolution_prover.backward_subsumption_P[of "fst ` N" C] by auto
next
  case (backward_subsumption_Q N C P Q i n)
  then have "\<exists>D\<in>fst ` N. strictly_subsumes D C"
    by force
  then show ?case 
    using resolution_prover.backward_subsumption_Q[of "fst ` N" C] by auto
next
  case (forward_reduction j P Q L \<sigma> C N i n)
  then obtain D L' where "(D + {#L'#}, j) \<in> P \<union> Q \<and> - L = L' \<cdot>l \<sigma> \<and> D \<cdot> \<sigma> \<subseteq># C"
    by blast
  then have "D + {#L'#} \<in> fst ` P \<union> fst ` Q \<and> - L = L' \<cdot>l \<sigma> \<and> D \<cdot> \<sigma> \<subseteq># C"
    by force
  then have "\<exists>D L'. D + {#L'#} \<in> fst ` P \<union> fst ` Q \<and> - L = L' \<cdot>l \<sigma> \<and> D \<cdot> \<sigma> \<subseteq># C"
    by blast
  then show ?case 
    using resolution_prover.forward_reduction[of "fst ` P" "fst ` Q" L \<sigma> C ] by auto
next
  case (backward_reduction_P j N L \<sigma> C P i Q n)
  then obtain D L' where "(D + {#L'#}, j) \<in> N \<and> - L = L' \<cdot>l \<sigma> \<and> D \<cdot> \<sigma> \<subseteq># C"
    by blast
  then have "D + {#L'#} \<in> fst ` N \<and> - L = L' \<cdot>l \<sigma> \<and> D \<cdot> \<sigma> \<subseteq># C"
    by force
  then have "\<exists>D L'. D + {#L'#} \<in> fst ` N \<and> - L = L' \<cdot>l \<sigma> \<and> D \<cdot> \<sigma> \<subseteq># C"
    by blast
  then show ?case 
    using resolution_prover.backward_reduction_P[of "fst ` N" L \<sigma> C] by auto
next
  case (backward_reduction_Q j N L \<sigma> C P Q i n)
  then obtain D L' where "(D + {#L'#}, j) \<in> N \<and> - L = L' \<cdot>l \<sigma> \<and> D \<cdot> \<sigma> \<subseteq># C"
    by blast
  then have "D + {#L'#} \<in> fst ` N \<and> - L = L' \<cdot>l \<sigma> \<and> D \<cdot> \<sigma> \<subseteq># C" 
    by force
  then have "\<exists>D L'. D + {#L'#} \<in> fst ` N \<and> - L = L' \<cdot>l \<sigma> \<and> D \<cdot> \<sigma> \<subseteq># C"
    by blast
  then show ?case 
    using resolution_prover.backward_reduction_Q[of "fst ` N" L \<sigma> C] by auto
next
  case (clause_processing N C P Q n)
  show ?case 
    using resolution_prover.clause_processing by auto
next
  case (inference_computation P C i N n Q)
  then have "fst ` N = fst ` (\<lambda>D. (D, Suc n)) ` concls_of (ord_FO_resolution_inferences_between (fst ` Q) C)"
    by auto
  then have "fst ` N = (fst \<circ> (\<lambda>D. (D, Suc n))) ` concls_of (ord_FO_resolution_inferences_between (fst ` Q) C)"
    using image_comp by simp
  then have "fst ` N = concls_of (ord_FO_resolution_inferences_between (fst ` Q) C)"
    by auto
  then show ?case 
    using resolution_prover.inference_computation[of "fst ` N" "fst ` Q" C]
    unfolding ord_FO_resolution_inferences_between_def by auto
qed

lemma resolution_prover_with_weights_resolution_prover:
  "chain (op \<leadsto>\<^sub>w) Sts \<Longrightarrow> chain (op \<leadsto>) (lmap state_of_weighted_state Sts)"
  using resolution_prover_with_weights_resolution_prover' using chain_lmap weight_monotone by metis

context
  fixes 
    Sts :: "('a weighted_state) llist"
  assumes
    finite_Sts0: "finite (clss_of_weighted_state (lnth Sts 0))" and
    empty_P0: "P_of_weighted_state (lnth Sts 0) = {}" and
    empty_Q0: "Q_of_weighted_state (lnth Sts 0) = {}" and
    deriv: "chain (op \<leadsto>\<^sub>w) Sts" and
    non_empty_deriv: "enat 0 < llength Sts"
begin

lemma monotone_fairness: "fair_state_seq (lmap state_of_weighted_state Sts)"
proof (rule ccontr)
  assume "\<not> fair_state_seq (lmap state_of_weighted_state Sts)"
  then obtain C where "C \<in> limit_llist (lmap N_of_state (lmap state_of_weighted_state Sts)) \<union> limit_llist (lmap P_of_state (lmap state_of_weighted_state Sts))" 
    unfolding fair_state_seq_def limit_state_def by auto
  then show False
  proof
    assume "C \<in> limit_llist (lmap N_of_state (lmap state_of_weighted_state Sts))"
    then obtain i where "enat i < llength Sts" "\<And>j. i \<le> j \<and> enat j < llength Sts \<Longrightarrow> C \<in> N_of_state (state_of_weighted_state (lnth Sts j))" 
      unfolding limit_llist_def by auto
    then show False
      sorry (* *)
  next
    assume "C \<in> limit_llist (lmap P_of_state (lmap state_of_weighted_state Sts))"
    then show False 
      sorry
  qed
qed

lemma monotone_completeness:
  assumes 
    selection_renaming_invariant: "(\<And>\<rho> C. is_renaming \<rho> \<Longrightarrow> S (C \<cdot> \<rho>) = S C \<cdot> \<rho>)" and
    unsat: "\<not> satisfiable (grounding_of_state (limit_weighted_state Sts))" 
  shows "{#} \<in> clss_of_state (limit_weighted_state Sts)"
proof -
  have "state_of_weighted_state (lnth Sts 0) = lnth (lmap state_of_weighted_state Sts) 0"
    using lnth_lmap[of 0 Sts state_of_weighted_state] non_empty_deriv
    by auto
  then have "finite (clss_of_state (lnth (lmap state_of_weighted_state Sts) 0))"
    using finite_Sts0 by auto
  moreover have "P_of_state (lnth (lmap state_of_weighted_state Sts) 0) = {}"
    using empty_P0 non_empty_deriv by auto
  moreover have "Q_of_state (lnth (lmap state_of_weighted_state Sts) 0) = {}"
    using empty_Q0 non_empty_deriv by auto
  moreover have "chain op \<leadsto> (lmap state_of_weighted_state Sts)"
    using deriv resolution_prover_with_weights_resolution_prover by blast 
  moreover have "\<forall>\<rho> C. is_renaming \<rho> \<longrightarrow> S (C \<cdot> \<rho>) = S C \<cdot> \<rho>"
    using selection_renaming_invariant by auto
  moreover have "fair_state_seq (lmap state_of_weighted_state Sts)"
    using monotone_fairness by auto
  moreover have "\<not> satisfiable (grounding_of_state (limit_state (lmap state_of_weighted_state Sts)))"
    using unsat by auto
  ultimately have "{#} \<in> clss_of_state (limit_state (lmap state_of_weighted_state Sts))" 
    using fair_state_seq_complete[of "lmap state_of_weighted_state Sts"] by auto
  then show "{#} \<in> clss_of_state (limit_weighted_state Sts)"
    by auto
qed 

end

end

type_synonym 'a weighted_list_state =
  "'a weighted_clause list \<times> 'a weighted_clause list \<times> 'a weighted_clause list \<times> nat"

locale FO_resolution_prover_with_sum_product_weights =
  FO_resolution_prover_with_weights S subst_atm id_subst comp_subst renamings_apart atm_of_atms mgu
    less_atm weight
  for
    S :: "('a :: wellorder) clause \<Rightarrow> _" and
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

sublocale FO_resolution_prover_with_weights
  using generation_factor_pos by unfold_locales (simp add: weight_def)

thm monotone_fairness

thm monotone_completeness

definition is_tautology :: "'a clause \<Rightarrow> bool" where
  "is_tautology C \<longleftrightarrow> (\<exists>A \<in> atms_of C. Pos A \<in># C \<and> Neg A \<in># C)"

definition is_subsumed_by :: "'a clause list \<Rightarrow> 'a clause \<Rightarrow> bool" where
  "is_subsumed_by Ds C \<longleftrightarrow> (\<exists>D \<in> set Ds. subsumes D C)"

definition is_reducible_lit :: "'a clause list \<Rightarrow> 'a clause \<Rightarrow> 'a literal \<Rightarrow> bool" where
  "is_reducible_lit Ds C L \<longleftrightarrow>
    (\<exists>D \<in> set Ds. \<exists>L' \<in># D. \<exists>\<sigma>. - L = L' \<cdot>l \<sigma> \<and> (D - {#L'#}) \<cdot> \<sigma> \<subseteq># C - {#L#})"

definition reduce :: "'a clause list \<Rightarrow> 'a clause \<Rightarrow> 'a clause" where
  "reduce Ds C = filter_mset (is_reducible_lit Ds C) C"

definition
  find_next_clause :: "'a weighted_clause \<Rightarrow> 'a weighted_clause list \<Rightarrow> 'a weighted_clause"
where
  "find_next_clause = undefined" (* FIXME *)

partial_function (option)
  deterministic_resolution_prover :: "'a weighted_list_state \<Rightarrow> bool option"
where
  "deterministic_resolution_prover NPQn =
   (let
      (N, P, Q, n) = NPQn
    in
      (case N of
        [] \<Rightarrow> undefined (* FIXME *)
      | (C, i) # N \<Rightarrow>
        let
          C = reduce (map fst (P @ Q)) C
        in
          if is_tautology C \<or> is_subsumed_by (map fst (P @ Q)) C then
            deterministic_resolution_prover (N, P, Q, n)
          else
            if C = {#} then
              Some True
            else
              let
                P = map (apfst (reduce [C])) P;
                P = filter (is_subsumed_by [C] \<circ> fst) N;
                P = (C, i) # P;
                Q = map (apfst (reduce [C])) Q;
                Q = filter (is_subsumed_by [C] \<circ> fst) N
              in
                deterministic_resolution_prover (N, P, Q, n)))"


(*
      (case N of
        [] \<Rightarrow> Some undefined (*FIXME*)
      | Ci # N' \<Rightarrow> find_next_clause Ci N')
*)


print_theorems
term deterministic_resolution_prover

end

end
