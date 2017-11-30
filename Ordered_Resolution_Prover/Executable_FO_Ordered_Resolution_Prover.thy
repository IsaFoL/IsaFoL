(*  Title:       An Executable Simple Ordered Resolution Prover for First-Order Clauses
    Author:      Dmitriy Traytel <TODO>, 2017
    Maintainer:  Anders Schlichtkrull <andschl at dtu.dk>
*)

section \<open>An Executable Simple Ordered Resolution Prover for First-Order Clauses\<close>

text \<open>
TODO.
\<close>

theory Executable_FO_Ordered_Resolution_Prover
  imports Deterministic_FO_Ordered_Resolution_Prover IsaFoR_IsaFoR_Term
begin

global_interpretation RP: deterministic_FO_resolution_prover where
  S = "\<lambda>_. {#}" and
  subst_atm = "op \<cdot>" and
  id_subst = "Var :: _ \<Rightarrow> ('f :: {weighted, compare}, nat) term" and
  comp_subst = "op \<circ>\<^sub>s" and
  renamings_apart = renamings_apart and
  atm_of_atms = "Fun undefined" and
  mgu = mgu_sets and
  lessatm = less_kbo and
  size_atm = size and
  generation_factor = 1 and
  size_factor = 1
  defines deterministic_RP = RP.deterministic_RP
  and deterministic_RP_step = RP.deterministic_RP_step
  and is_final_dstate = RP.is_final_dstate
  and is_reducible_lit = RP.is_reducible_lit
  and is_tautology = RP.is_tautology
  and maximal_in = RP.maximal_in
  and reduce = RP.reduce
  and reduce_all = RP.reduce_all
  and reduce_all2 = RP.reduce_all2
  and resolve = RP.resolve
  and resolve_on = RP.resolve_on
  and resolve_either_way = RP.resolve_either_way
  and resolve_rename_either_way = RP.resolve_rename_either_way
  and select_min_weight_clause = RP.select_min_weight_clause
  and strictly_maximal_in = RP.strictly_maximal_in
  and strictly_subsume = RP.strictly_subsume
  and subsume = RP.subsume
  and weight = RP.weight
  and St0 = RP.St0
  and sorted_list_of_set = "linorder.sorted_list_of_set (le_of_comp compare)"
  and sort_key = "linorder.sort_key (le_of_comp compare)"
  and insort_key = "linorder.insort_key (le_of_comp compare)"
  by (unfold_locales)
    (auto simp: less_kbo_subst is_ground_atm_ground less_kbo_less intro: ground_less_less_kbo)

declare
  RP.deterministic_RP.simps[code]
  RP.deterministic_RP_step.simps[code]
  RP.is_final_dstate.simps[code]
  RP.is_tautology_def[code]
  RP.reduce.simps[code]
  RP.reduce_all_def[code]
  RP.reduce_all2.simps[code]
  RP.resolve_either_way_def[code]
  RP.resolve_rename_either_way_def[code]
  RP.select_min_weight_clause.simps[code]
  RP.weight.simps[code]
  St0_def[code]
  substitution_ops.strictly_subsumes_def[code]
  substitution_ops.subst_cls_lists_def[code]
  substitution_ops.subst_lit_def[code]
  substitution_ops.subst_cls_def[code]

lemma [code]: "is_reducible_lit = is_reducible_lit"
  by simp

lemma [code]: "substitution_ops.subsumes = substitution_ops.subsumes"
  by simp

declare
  Pairs_def[folded sorted_list_of_set_def, code]
  linorder.sorted_list_of_set_sort_remdups[OF class_linorder_compare,
    folded sorted_list_of_set_def sort_key_def, code]
  linorder.sort_key_def[OF class_linorder_compare, folded sort_key_def insort_key_def, code]
  linorder.insort_key.simps[OF class_linorder_compare, folded insort_key_def, code]

export_code St0 in SML
export_code deterministic_RP in SML module_name RP

definition prover where
  "prover N = deterministic_RP (St0 N 0)"

lemma "prover N = None \<Longrightarrow> satisfiable (RP.grounded_N0 N)"
  unfolding prover_def St0_def by (rule RP.deterministic_RP_complete)

export_code prover in SML module_name RP

value "prover ([] :: ((unit, nat) Term.term literal list \<times> nat) list)"

end
