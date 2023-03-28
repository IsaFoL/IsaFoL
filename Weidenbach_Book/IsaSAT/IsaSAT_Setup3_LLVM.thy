theory IsaSAT_Setup3_LLVM
  imports IsaSAT_Setup
    IsaSAT_Setup0_LLVM
begin

definition wasted_bytes_st_impl :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
\<open>wasted_bytes_st_impl= read_heur_wl_heur_code wasted_of_stats_impl\<close>

global_interpretation wasted_of: read_heur_param_adder0 where
  f' = \<open>RETURN o wasted_of\<close> and
  f = wasted_of_stats_impl and
  x_assn = \<open>word64_assn\<close> and
  P = \<open>(\<lambda>_. True)\<close>
  rewrites
    \<open>read_heur_wl_heur (RETURN o wasted_of) = RETURN o wasted_bytes_st\<close> and
    \<open>read_heur_wl_heur_code wasted_of_stats_impl = wasted_bytes_st_impl\<close>
  apply unfold_locales
  apply (rule heur_refine)
  subgoal by (auto simp: wasted_bytes_st_def read_all_st_def intro!: ext split: isasat_int_splits)
  subgoal by (auto simp: wasted_bytes_st_impl_def)
  done

definition get_restart_phase_imp :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>get_restart_phase_imp = read_heur_wl_heur_code current_restart_phase_impl\<close>

global_interpretation current_restart_phase: read_heur_param_adder0 where
  f' = \<open>RETURN o current_restart_phase\<close> and
  f = current_restart_phase_impl and
  x_assn = \<open>word64_assn\<close> and
  P = \<open>(\<lambda>_. True)\<close>
  rewrites
    \<open>read_heur_wl_heur (RETURN o current_restart_phase) = RETURN o get_restart_phase\<close> and
    \<open>read_heur_wl_heur_code current_restart_phase_impl = get_restart_phase_imp\<close>
  apply unfold_locales
  apply (rule heur_refine)
  subgoal by (auto simp: get_restart_phase_def read_all_st_def intro!: ext split: isasat_int_splits)
  subgoal by (auto simp: get_restart_phase_imp_def)
  done

definition next_pure_lits_schedule_st_impl :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>next_pure_lits_schedule_st_impl = read_heur_wl_heur_code next_pure_lits_schedule_info_stats_impl\<close>

global_interpretation next_pure_lits_schedule: read_heur_param_adder0 where
  f' = \<open>RETURN o next_pure_lits_schedule\<close> and
  f = next_pure_lits_schedule_info_stats_impl and
  x_assn = \<open>word64_assn\<close> and
  P = \<open>\<lambda>_. True\<close>
  rewrites
    \<open>read_heur_wl_heur (RETURN o next_pure_lits_schedule) = RETURN o next_pure_lits_schedule_st\<close> and
    \<open>read_heur_wl_heur_code next_pure_lits_schedule_info_stats_impl = next_pure_lits_schedule_st_impl\<close>
  apply unfold_locales
  apply (rule heur_refine)
  subgoal by (auto simp: next_pure_lits_schedule_st_def read_all_st_def intro!: ext split: isasat_int_splits)
  subgoal by (auto simp: next_pure_lits_schedule_st_impl_def)
  done

definition next_reduce_schedule_st_impl :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>next_reduce_schedule_st_impl = read_heur_wl_heur_code next_reduce_schedule_info_stats_impl\<close>

global_interpretation next_reduce_schedule: read_heur_param_adder0 where
  f' = \<open>RETURN o next_reduce_schedule\<close> and
  f = next_reduce_schedule_info_stats_impl and
  x_assn = \<open>word64_assn\<close> and
  P = \<open>\<lambda>_. True\<close>
  rewrites
    \<open>read_heur_wl_heur (RETURN o next_reduce_schedule) = RETURN o next_reduce_schedule_st\<close> and
    \<open>read_heur_wl_heur_code next_reduce_schedule_info_stats_impl = next_reduce_schedule_st_impl\<close>
  apply unfold_locales
  apply (rule heur_refine)
  subgoal by (auto simp: next_reduce_schedule_st_def read_all_st_def intro!: ext split: isasat_int_splits)
  subgoal by (auto simp: next_reduce_schedule_st_impl_def)
  done

lemmas [sepref_fr_rules] =
  wasted_of.refine
  current_restart_phase.refine
  next_pure_lits_schedule.refine
  next_reduce_schedule.refine

lemmas [unfolded inline_direct_return_node_case, llvm_code] =
  wasted_bytes_st_impl_def[unfolded read_all_st_code_def]
  get_restart_phase_imp_def[unfolded read_all_st_code_def]
  next_pure_lits_schedule_st_impl_def[unfolded read_all_st_code_def]
  next_reduce_schedule_st_impl_def[unfolded read_all_st_code_def]

sepref_register set_zero_wasted mop_save_phase_heur add_lbd


sepref_register isa_trail_nth isasat_trail_nth_st

sepref_def isa_trail_nth_impl
  is \<open>uncurry isa_trail_nth\<close>
  :: \<open>trail_pol_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a unat_lit_assn\<close>
  unfolding trail_pol_fast_assn_def isa_trail_nth_def
  by sepref

definition isasat_trail_nth_st_code :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>isasat_trail_nth_st_code = (\<lambda>N C. read_trail_wl_heur_code (\<lambda>M. isa_trail_nth_impl M C) N)\<close>

global_interpretation trail_nth: read_trail_param_adder where
  R = \<open>snat_rel' TYPE(64)\<close> and
  f' = \<open>\<lambda>C M. isa_trail_nth M C\<close> and
  f = \<open>\<lambda>C M. isa_trail_nth_impl M C\<close> and
  x_assn = unat_lit_assn and
  P = \<open>\<lambda>_ _. True\<close>
  rewrites
    \<open>(\<lambda>N C'. read_trail_wl_heur (\<lambda>M. isa_trail_nth M C') N) = isasat_trail_nth_st\<close> and
    \<open>(\<lambda>N C. read_trail_wl_heur_code (\<lambda>M. isa_trail_nth_impl M C) N) = isasat_trail_nth_st_code\<close>
  apply unfold_locales
  apply (subst lambda_comp_true)
  apply (rule isa_trail_nth_impl.refine)
  subgoal by (auto simp: isasat_trail_nth_st_def read_all_st_def isasat_length_trail_st_def
      intro!: ext split: isasat_int_splits)
  subgoal by (auto simp: isasat_trail_nth_st_code_def)
  done

lemma trail_nth_precond_simp: \<open>(\<lambda>M. fst M \<noteq> []) = (\<lambda>(M,_). M \<noteq> [])\<close>
  by auto
definition lit_of_hd_trail_st_heur_fast_code :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>lit_of_hd_trail_st_heur_fast_code = read_trail_wl_heur_code lit_of_last_trail_fast_code\<close>

global_interpretation last_trail: read_trail_param_adder0 where
  f' = \<open>RETURN o lit_of_last_trail_pol\<close> and
  f = \<open>lit_of_last_trail_fast_code\<close> and
  x_assn = unat_lit_assn and
  P = \<open>\<lambda>M. fst M \<noteq> []\<close>
  rewrites
    \<open>last_trail.mop = lit_of_hd_trail_st_heur\<close> and
    \<open>read_trail_wl_heur_code lit_of_last_trail_fast_code = lit_of_hd_trail_st_heur_fast_code\<close>
  apply unfold_locales
  apply (subst trail_nth_precond_simp)
  apply (rule lit_of_last_trail_fast_code.refine)
  subgoal by (auto simp: lit_of_hd_trail_st_heur_def lit_of_last_trail_pol_def read_all_st_def read_trail_param_adder0_ops.mop_def
      intro!: ext split: isasat_int_splits)
  subgoal by (auto simp: lit_of_hd_trail_st_heur_fast_code_def)
  done

definition get_the_propagation_reason_pol_st_code :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>get_the_propagation_reason_pol_st_code = (\<lambda>N C. read_trail_wl_heur_code (\<lambda>M. get_the_propagation_reason_fast_code M C) N)\<close>

global_interpretation propagation_reason: read_trail_param_adder where
  R = unat_lit_rel and
  f' = \<open>\<lambda>C M. get_the_propagation_reason_pol M C\<close> and
  f = \<open>\<lambda>C M. get_the_propagation_reason_fast_code M C\<close> and
  x_assn = \<open>snat_option_assn' TYPE(64)\<close> and
  P = \<open>\<lambda>M _. True\<close>
  rewrites
    \<open>(\<lambda>M C. read_trail_wl_heur (\<lambda>M. get_the_propagation_reason_pol M C) M)  = get_the_propagation_reason_pol_st\<close> and
    \<open>(\<lambda>N C. read_trail_wl_heur_code (\<lambda>M. get_the_propagation_reason_fast_code M C) N) = get_the_propagation_reason_pol_st_code\<close>
  apply unfold_locales
  apply (subst lambda_comp_true)
  apply (rule get_the_propagation_reason_fast_code.refine)
  subgoal by (auto simp: get_the_propagation_reason_pol_st_def lit_of_last_trail_pol_def read_all_st_def read_trail_param_adder0_ops.mop_def
      intro!: ext split: isasat_int_splits)
  subgoal by (auto simp: get_the_propagation_reason_pol_st_code_def)
  done

definition is_fully_propagated_heur_st_code :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>is_fully_propagated_heur_st_code = read_heur_wl_heur_code is_fully_propagated_heur_stats_impl\<close>

global_interpretation is_fully_proped: read_heur_param_adder0 where
  f' = \<open>RETURN o is_fully_propagated_heur\<close> and
  f = \<open>is_fully_propagated_heur_stats_impl\<close> and
  x_assn = bool1_assn and
  P = \<open>\<lambda>_. True\<close>
  rewrites
    \<open>read_heur_wl_heur (RETURN o is_fully_propagated_heur) = RETURN o is_fully_propagated_heur_st\<close> and
    \<open>read_heur_wl_heur_code is_fully_propagated_heur_stats_impl = is_fully_propagated_heur_st_code\<close>
  apply unfold_locales
  apply (rule heur_refine)
  subgoal by (auto simp: is_fully_propagated_heur_def is_fully_propagated_heur_st_def read_all_st_def
      intro!: ext split: isasat_int_splits)
  subgoal by (auto simp: is_fully_propagated_heur_st_code_def)
  done

definition heuristic_reluctant_triggered2_st_impl :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
\<open>heuristic_reluctant_triggered2_st_impl = read_heur_wl_heur_code heuristic_reluctant_triggered2_stats_impl\<close>

global_interpretation heuristic_reluctant_triggered2: read_heur_param_adder0 where
  f' = \<open>RETURN o heuristic_reluctant_triggered2\<close> and
  f = heuristic_reluctant_triggered2_stats_impl and
  x_assn = \<open>bool1_assn\<close> and
  P = \<open>(\<lambda>_. True)\<close>
  rewrites
    \<open>read_heur_wl_heur (RETURN o heuristic_reluctant_triggered2) = RETURN o heuristic_reluctant_triggered2_st\<close> and
    \<open>read_heur_wl_heur_code heuristic_reluctant_triggered2_stats_impl = heuristic_reluctant_triggered2_st_impl\<close>
  apply unfold_locales
  apply (rule heur_refine)
  subgoal by (auto simp: read_all_st_def heuristic_reluctant_triggered2_st_def heuristic_reluctant_triggered2_def intro!: ext split: isasat_int_splits)
  subgoal by (auto simp: heuristic_reluctant_triggered2_st_impl_def)
  done

lemma heuristic_reluctant_untrigger_st_alt_def:
    \<open>heuristic_reluctant_untrigger_st S =
  (let (heur, S) = extract_heur_wl_heur S;
    heur = heuristic_reluctant_untrigger heur;
    S = update_heur_wl_heur heur S in
  S)\<close>
  by (auto simp: heuristic_reluctant_untrigger_st_def state_extractors split: isasat_int_splits
    intro!: ext)

sepref_def heuristic_reluctant_untrigger_st_impl
  is \<open>RETURN o heuristic_reluctant_untrigger_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding heuristic_reluctant_untrigger_st_alt_def
  by sepref

lemmas [sepref_fr_rules] =
   trail_nth.refine[unfolded lambda_comp_true]
  last_trail.mop_refine
  is_fully_proped.refine
  propagation_reason.refine
  heuristic_reluctant_triggered2.refine

lemmas [unfolded inline_direct_return_node_case, llvm_code] =
  isasat_trail_nth_st_code_def[unfolded read_all_st_code_def]
  lit_of_hd_trail_st_heur_fast_code_def[unfolded read_all_st_code_def]
  is_fully_propagated_heur_st_code_def[unfolded read_all_st_code_def]
  get_the_propagation_reason_pol_st_code_def[unfolded read_all_st_code_def]
  heuristic_reluctant_triggered2_st_impl_def[unfolded read_all_st_code_def]



sepref_register incr_restart_stat clss_size_lcountUE clss_size_lcountUS learned_clss_count clss_size_allcount

lemma incr_restart_stat_alt_def:
  \<open>incr_restart_stat = (\<lambda>S. do{
     let (heur, S) = extract_heur_wl_heur S;
     let heur = unset_fully_propagated_heur (heuristic_reluctant_untrigger (restart_info_restart_done_heur heur));
     let S = update_heur_wl_heur heur S;
     let (stats, S) = extract_stats_wl_heur S;
     let stats = incr_restart (stats);
     let S = update_stats_wl_heur stats S;
     RETURN S
  })\<close>
  by (auto simp: incr_restart_stat_def state_extractors split: isasat_int_splits
    intro!: ext)

sepref_def incr_restart_stat_fast_code
  is \<open>incr_restart_stat\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding incr_restart_stat_alt_def
  by sepref

sepref_register incr_reduction_stat clss_size_decr_lcount
    clss_size_incr_lcountUE clss_size_incr_lcountUS

lemma incr_reduction_stat_alt_def:
    \<open>incr_reduction_stat = (\<lambda>S. do{
     let (stats, S) = extract_stats_wl_heur S;
     let stats = incr_reduction stats;
     let S = update_stats_wl_heur stats S;
     RETURN S
  })\<close>
  by (auto simp: incr_reduction_stat_def state_extractors split: isasat_int_splits
    intro!: ext)

sepref_def incr_reduction_stat_fast_code
  is \<open>incr_reduction_stat\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding incr_reduction_stat_alt_def
  by sepref

sepref_register mark_unused_st_heur
lemma mark_unused_st_heur_alt_def:
    \<open>RETURN oo mark_unused_st_heur = (\<lambda>C S\<^sub>0. do {
    let (N, S) = extract_arena_wl_heur S\<^sub>0;
    ASSERT (N = get_clauses_wl_heur S\<^sub>0);
    let N' = mark_unused N C;
    let S = update_arena_wl_heur N' S;
    RETURN S})\<close>
    by (auto simp: mark_unused_st_heur_def state_extractors Let_def intro!: ext split: isasat_int_splits)

sepref_def mark_unused_st_fast_code
  is \<open>uncurry (RETURN oo mark_unused_st_heur)\<close>
  :: \<open>[\<lambda>(C, S). arena_act_pre (get_clauses_wl_heur S) C]\<^sub>a
        sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding mark_unused_st_heur_alt_def
    arena_act_pre_mark_used[intro!]
  supply [[goals_limit = 1]]
  by sepref

sepref_def mop_mark_unused_st_heur_impl
  is \<open>uncurry mop_mark_unused_st_heur\<close>
  :: \<open> sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding mop_mark_unused_st_heur_def fold_tuple_optimizations
  by sepref


sepref_register get_the_propagation_reason_pol_st
lemma empty_US_heur_alt_def:
  \<open>empty_US_heur S =
  (let (lcount, S) = extract_lcount_wl_heur S in
  let lcount = clss_size_resetUS0 lcount in
  let S = update_lcount_wl_heur lcount S in S
  )\<close>
    by (auto simp: empty_US_heur_def state_extractors Let_def intro!: ext split: isasat_int_splits)

sepref_def empty_US_heur_code
  is \<open>RETURN o empty_US_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding empty_US_heur_alt_def
  by sepref

lemma mark_garbage_heur2_alt_def:
  \<open>mark_garbage_heur2 C = (\<lambda>S\<^sub>0. do{
    ASSERT (mark_garbage_pre (get_clauses_wl_heur S\<^sub>0, C));
    let (N, S) = extract_arena_wl_heur S\<^sub>0;
    ASSERT (N = get_clauses_wl_heur S\<^sub>0);
    let st = arena_status N C = IRRED;
    let N' = extra_information_mark_to_delete (N) C;
    let (lcount, S) = extract_lcount_wl_heur S;
    ASSERT (lcount = get_learned_count S\<^sub>0);
    ASSERT(\<not>st \<longrightarrow> clss_size_lcount lcount \<ge> 1);
    let lcount = (if st then lcount else clss_size_decr_lcount lcount);
    RETURN (update_lcount_wl_heur lcount (update_arena_wl_heur N' S))})\<close>
    by (auto simp: mark_garbage_heur2_def state_extractors Let_def intro!: ext split: isasat_int_splits)

lemma mark_garbage_preD:
  \<open>mark_garbage_pre (N, C) \<Longrightarrow> arena_is_valid_clause_vdom N C\<close>
  by (auto simp: mark_garbage_pre_def arena_is_valid_clause_idx_def arena_is_valid_clause_vdom_def)

sepref_register mark_garbage_heur2 mark_garbage_heur4

sepref_def mark_garbage_heur2_code
  is \<open>uncurry mark_garbage_heur2\<close>
  :: \<open>[\<lambda>(C, S). True]\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  supply [intro] = mark_garbage_preD
  unfolding mark_garbage_heur2_alt_def
  by sepref


lemma mark_garbage_heur4_alt_def:
  \<open>mark_garbage_heur4 C S\<^sub>0 = do{
    let (N', S) = extract_arena_wl_heur S\<^sub>0;
    ASSERT (N' = get_clauses_wl_heur S\<^sub>0);
    let st = arena_status N' C = IRRED;
    let N' = extra_information_mark_to_delete (N') C;
    let (lcount, S) = extract_lcount_wl_heur S;
    ASSERT (lcount = get_learned_count S\<^sub>0);
    ASSERT(\<not>st \<longrightarrow> clss_size_lcount lcount \<ge> 1);
    let lcount = (if st then lcount else clss_size_incr_lcountUEk (clss_size_decr_lcount lcount));
    let (stats, S) = extract_stats_wl_heur S;
    ASSERT (stats = get_stats_heur S\<^sub>0);
    let stats = (if st then decr_irred_clss stats else stats);
    let S = update_arena_wl_heur N' S;
    let S = update_lcount_wl_heur lcount S;
    let S = update_stats_wl_heur stats S;
    RETURN S
   }\<close>
    by (cases S\<^sub>0)
     (auto simp: mark_garbage_heur4_def state_extractors  Let_def intro!: ext split: isasat_int_splits)

sepref_def mark_garbage_heur4_code
  is \<open>uncurry mark_garbage_heur4\<close>
  :: \<open>[\<lambda>(C, S). mark_garbage_pre (get_clauses_wl_heur S, C) \<and> arena_is_valid_clause_vdom (get_clauses_wl_heur S) C \<and>
        learned_clss_count S \<le> unat64_max]\<^sub>a
     sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]] isasat_fast_countD[dest] learned_clss_count_def[simp]
  unfolding mark_garbage_heur4_alt_def
  by sepref

sepref_definition access_avdom_aivdom_at_impl
  is \<open>uncurry (\<lambda>N C. RETURN (get_avdom_aivdom N ! C))\<close>
  :: \<open>[uncurry (\<lambda>N C. C < length (get_avdom_aivdom N))]\<^sub>a aivdom_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> sint64_nat_assn\<close>
  unfolding avdom_aivdom_at_def[symmetric]
  by sepref

definition access_avdom_at_fast_code :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>access_avdom_at_fast_code = (\<lambda>N C. read_vdom_wl_heur_code (\<lambda>N. avdom_aivdom_at_impl N C) N)\<close>

global_interpretation avdom_aivdom_at: read_vdom_param_adder where
  R = \<open>snat_rel' TYPE(64)\<close> and
  x_assn = sint64_nat_assn and
  f' = \<open>\<lambda>C N. (RETURN oo avdom_aivdom_at) N C\<close> and
  f = \<open>\<lambda>C N. avdom_aivdom_at_impl N C\<close> and
  P = \<open>\<lambda>C N. C < length (get_avdom_aivdom N)\<close>
  rewrites
    \<open>(\<lambda>N C'. read_vdom_wl_heur (\<lambda>N. (RETURN \<circ>\<circ> avdom_aivdom_at) N C') N) = RETURN oo access_avdom_at\<close> and
    \<open>(\<lambda>N C. read_vdom_wl_heur_code (\<lambda>N. avdom_aivdom_at_impl N C) N) = access_avdom_at_fast_code\<close> and
    \<open>(\<lambda>S C. C < length (get_avdom_aivdom (get_aivdom S))) = access_avdom_at_pre\<close>
  apply unfold_locales
  apply (subst (3) uncurry_def)
  apply (rule avdom_aivdom_at_impl_refine)
  subgoal by (auto simp: access_avdom_at_def read_all_st_def avdom_aivdom_at_def split: isasat_int_splits intro!: ext)
  subgoal by (auto simp: access_avdom_at_fast_code_def)
  subgoal by (auto simp :access_avdom_at_pre_def split: isasat_int_splits intro!: ext)
  done

definition access_ivdom_at_fast_code :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>access_ivdom_at_fast_code = (\<lambda>N C. read_vdom_wl_heur_code (\<lambda>N. ivdom_aivdom_at_impl N C) N)\<close>

global_interpretation ivdom_aivdom_at: read_vdom_param_adder where
  R = \<open>snat_rel' TYPE(64)\<close> and
  x_assn = sint64_nat_assn and
  f' = \<open>\<lambda>C N. (RETURN oo ivdom_aivdom_at) N C\<close> and
  f = \<open>\<lambda>C N. ivdom_aivdom_at_impl N C\<close> and
  P = \<open>\<lambda>C N. C < length (get_ivdom_aivdom N)\<close>
  rewrites
    \<open>(\<lambda>N C'. read_vdom_wl_heur (\<lambda>N. (RETURN \<circ>\<circ> ivdom_aivdom_at) N C') N) = RETURN oo access_ivdom_at\<close> and
    \<open>(\<lambda>N C. read_vdom_wl_heur_code (\<lambda>N. ivdom_aivdom_at_impl N C) N) = access_ivdom_at_fast_code\<close> and
    \<open>(\<lambda>S C. C < length (get_ivdom_aivdom (get_aivdom S))) = access_ivdom_at_pre\<close>
  apply unfold_locales
  apply (subst (3) uncurry_def)
  apply (rule ivdom_aivdom_at_impl_refine)
  subgoal by (auto simp: access_ivdom_at_def read_all_st_def ivdom_aivdom_at_def split: isasat_int_splits intro!: ext)
  subgoal by (auto simp: access_ivdom_at_fast_code_def)
  subgoal by (auto simp :access_ivdom_at_pre_def split: isasat_int_splits intro!: ext)
  done

definition access_tvdom_at_fast_code :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>access_tvdom_at_fast_code = (\<lambda>N C. read_vdom_wl_heur_code (\<lambda>N. tvdom_aivdom_at_impl N C) N)\<close>

global_interpretation tvdom_aivdom_at: read_vdom_param_adder where
  R = \<open>snat_rel' TYPE(64)\<close> and
  x_assn = sint64_nat_assn and
  f' = \<open>\<lambda>C N. (RETURN oo tvdom_aivdom_at) N C\<close> and
  f = \<open>\<lambda>C N. tvdom_aivdom_at_impl N C\<close> and
  P = \<open>\<lambda>C N. C < length (get_tvdom_aivdom N)\<close>
  rewrites
    \<open>(\<lambda>N C'. read_vdom_wl_heur (\<lambda>N. (RETURN \<circ>\<circ> tvdom_aivdom_at) N C') N) = RETURN oo access_tvdom_at\<close> and
    \<open>(\<lambda>N C. read_vdom_wl_heur_code (\<lambda>N. tvdom_aivdom_at_impl N C) N) = access_tvdom_at_fast_code\<close> and
    \<open>(\<lambda>S C. C < length (get_tvdom_aivdom (get_aivdom S))) = access_tvdom_at_pre\<close>
  apply unfold_locales
  apply (subst (3) uncurry_def)
  apply (rule tvdom_aivdom_at_impl_refine)
  subgoal by (auto simp: access_tvdom_at_def read_all_st_def tvdom_aivdom_at_def split: isasat_int_splits intro!: ext)
  subgoal by (auto simp: access_tvdom_at_fast_code_def)
  subgoal by (auto simp :access_tvdom_at_pre_def split: isasat_int_splits intro!: ext)
  done


lemmas [sepref_fr_rules] =
  avdom_aivdom_at.refine
  ivdom_aivdom_at.refine
  tvdom_aivdom_at.refine
lemmas [unfolded inline_direct_return_node_case, llvm_code] =
  access_avdom_at_fast_code_def[unfolded read_all_st_code_def]
  access_ivdom_at_fast_code_def[unfolded read_all_st_code_def]
  access_tvdom_at_fast_code_def[unfolded read_all_st_code_def]

 
sepref_register mop_access_lit_in_clauses_heur mop_watched_by_app_heur
  get_target_opts get_opts


sepref_register print_literal_of_trail
    print_trail print_trail_st print_trail_st2

sepref_def print_literal_of_trail_code
  is print_literal_of_trail
  :: \<open>unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_literal_of_trail_def
  by sepref

sepref_def print_encoded_lit_end_code
  is print_literal_of_trail
  :: \<open>uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_literal_of_trail_def
  by sepref

sepref_def print_trail_code
  is \<open>print_trail\<close>
  :: \<open>trail_pol_fast_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_trail_def trail_pol_fast_assn_def
  apply (rewrite at \<open>print_literal_of_trail (\<hole>)\<close> unat_const_fold[where 'a=32])
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

lemmas print_trail[sepref_fr_rules] =
  print_trail_code.refine[FCOMP print_trail_print_trail2_rel]

definition print_trail_st_code :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>print_trail_st_code = read_trail_wl_heur_code print_trail_code\<close>

global_interpretation print_trail: read_trail_param_adder0 where
  f' = print_trail and
  f = print_trail_code and
  x_assn = unit_assn and
  P = \<open>\<lambda> _. True\<close>
  rewrites
    \<open>read_trail_wl_heur print_trail = print_trail_st\<close> and
    \<open>read_trail_wl_heur_code print_trail_code = print_trail_st_code\<close>
  apply unfold_locales
  apply (rule print_trail_code.refine)
  subgoal by (auto simp: print_trail_st_def read_all_st_def print_trail_def
      intro!: ext split: isasat_int_splits)
  subgoal by (auto simp: print_trail_st_code_def)
  done

lemmas [sepref_fr_rules] =
  print_trail.refine[FCOMP print_trail_st_print_trail_st2_rel]

lemmas [unfolded inline_direct_return_node_case, llvm_code] =
  print_trail_st_code_def[unfolded read_all_st_code_def]
sepref_register is_fully_propagated_heur_st


lemma [def_pat_rules]: \<open>nth_rll \<equiv> op_list_list_idx\<close>
 by (auto simp: nth_rll_def intro!: ext eq_reflection)


definition access_watchlist :: \<open>(nat \<times> nat literal \<times> bool) list list \<Rightarrow> _\<close> where
  \<open>access_watchlist N C C' = nth_rll N (nat_of_lit C) C'\<close>

sepref_def access_watchlist_impl
  is \<open>uncurry2 (RETURN ooo access_watchlist)\<close>
  :: \<open>[uncurry2 (\<lambda>S L K. nat_of_lit L < length S \<and>
          K < length (S ! nat_of_lit L))]\<^sub>a
        watchlist_fast_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> watcher_fast_assn\<close>
  unfolding access_watchlist_def
  by sepref

lemma watched_by_app_helper:
  \<open>uncurry (\<lambda>NC D. uncurry (\<lambda>N C. access_watchlist_impl N C D) NC) = uncurry2 access_watchlist_impl\<close>
  \<open>uncurry (\<lambda>NC D'. uncurry (\<lambda>N C'. (RETURN \<circ>\<circ>\<circ> access_watchlist) N C' D') NC) = uncurry2 (RETURN ooo access_watchlist)\<close>
  \<open>uncurry (\<lambda>a b. uncurry (\<lambda>a c. nat_of_lit c < length a \<and> b < length (a ! nat_of_lit c)) a)=
  uncurry2 (\<lambda>S L K. nat_of_lit L < length S \<and> K < length (S ! nat_of_lit L))\<close>
  by (auto)

definition watched_by_app_heur_fast_code :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>watched_by_app_heur_fast_code = (\<lambda>N C D. read_watchlist_wl_heur_code (\<lambda>N. access_watchlist_impl N C D) N)\<close>

global_interpretation watched_by_app: read_watchlist_param_adder_twoargs where
  R = \<open>unat_lit_rel\<close> and
  R' = \<open>snat_rel' TYPE(64)\<close> and
  f = \<open>\<lambda>C C' N. access_watchlist_impl N C C'\<close> and
  f' = \<open>\<lambda>C C' N. (RETURN ooo access_watchlist) N C C'\<close> and
  x_assn = watcher_fast_assn and
  P = \<open>(\<lambda>L K S. nat_of_lit L < length S \<and>
          K < length (S ! nat_of_lit L))\<close>
  rewrites
    \<open>(\<lambda>N C' D'. read_watchlist_wl_heur (\<lambda>N. (RETURN \<circ>\<circ>\<circ> access_watchlist) N C' D') N) = RETURN ooo watched_by_app_heur\<close> and
    \<open>(\<lambda>N C D. read_watchlist_wl_heur_code (\<lambda>N. access_watchlist_impl N C D) N) = watched_by_app_heur_fast_code\<close> and
  \<open>uncurry2 (\<lambda>S C D. nat_of_lit C < length (get_watched_wl_heur S) \<and> D < length (get_watched_wl_heur S ! nat_of_lit C)) = watched_by_app_heur_pre\<close>

  apply unfold_locales
  unfolding watched_by_app_helper
  apply (rule access_watchlist_impl.refine)
  subgoal
    by (auto intro!: ext split: tuple17.split
      simp: read_all_st_def watched_by_app_heur_def access_watchlist_def
      nth_rll_def)
  subgoal by (auto simp: watched_by_app_heur_fast_code_def)
  subgoal by (auto simp: watched_by_app_heur_pre_def)
  done

lemma mop_watched_by_app_heur_alt_def: \<open>mop_watched_by_app_heur = (\<lambda>N C' D'. watched_by_app.XX.XX.mop N (C', D'))\<close>
   by (auto simp: mop_watched_by_app_heur_def read_all_param_adder_ops.mop_def summarize_ASSERT_conv
    read_all_st_def access_watchlist_def conj_commute nth_rll_def intro!: ext intro: bind_cong split: isasat_int_splits)
definition mop_watched_by_app_heur_fast_impl :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>mop_watched_by_app_heur_fast_impl = (\<lambda>N C D. read_watchlist_wl_heur_code (case (C, D) of (C, D) \<Rightarrow> \<lambda>N. access_watchlist_impl N C D) N) \<close>
lemma split_snd_pure_arg':
  assumes \<open>(uncurry (\<lambda>N C. f C N), uncurry (\<lambda>N C'.  f' C' N))
    \<in> [\<lambda>_. True]\<^sub>a K\<^sup>k *\<^sub>a (pure (R \<times>\<^sub>f R'))\<^sup>k \<rightarrow> x_assn\<close>
  shows \<open>(uncurry2 (\<lambda>N C D. f (C,D) N), uncurry2 (\<lambda>N C' D'.  f' (C',D') N))
    \<in> [\<lambda>_. True]\<^sub>a K\<^sup>k *\<^sub>a (pure(R))\<^sup>k *\<^sub>a (pure R')\<^sup>k \<rightarrow> x_assn\<close>
  using assms unfolding hfref_def
  by (auto simp flip: prod_assn_pure_conv)

lemmas [sepref_fr_rules] =
  watched_by_app.refine
  watched_by_app.mop_refine[THEN split_snd_pure_arg', unfolded mop_watched_by_app_heur_alt_def[symmetric] mop_watched_by_app_heur_fast_impl_def[symmetric]]

lemmas [unfolded inline_direct_return_node_case, llvm_code] =
  watched_by_app_heur_fast_code_def[unfolded read_all_st_code_def]
  mop_watched_by_app_heur_fast_impl_def[unfolded read_all_st_code_def prod.case]

definition mop_is_marked_added_heur_stats_st_impl where
  \<open>mop_is_marked_added_heur_stats_st_impl =
    (\<lambda>N A. read_heur_wl_heur_code (\<lambda>S. mop_is_marked_added_heur_stats_impl S A) N)\<close>

global_interpretation is_marked_added: read_heur_param_adder where
  R = atom_rel and
  f' = \<open> \<lambda>S A. RETURN (is_marked_added_heur A S)\<close> and
  f = \<open> \<lambda>S A. mop_is_marked_added_heur_stats_impl A S\<close> and
  x_assn = \<open>bool1_assn\<close> and
  P = \<open>(\<lambda>S A. is_marked_added_heur_pre A S)\<close>
  rewrites
  \<open>(\<lambda>N A. read_heur_wl_heur_code (\<lambda>S. mop_is_marked_added_heur_stats_impl S A) N) = mop_is_marked_added_heur_stats_st_impl\<close>
  apply unfold_locales
  unfolding lambda_comp_true
  apply (unfold uncurry_def, rule is_marked_added_heur_refine[unfolded comp_def uncurry_def])
  apply (subst mop_is_marked_added_heur_stats_st_impl_def, rule refl)
  done

lemma mop_is_marked_added_heur_st_alt_def:
  \<open>is_marked_added.XX.mop = mop_is_marked_added_heur_st\<close>
  unfolding is_marked_added.XX.mop_def mop_is_marked_added_heur_st_def
    mop_is_marked_added_heur_def
  apply (intro ext, case_tac S)
  apply (auto simp: read_all_st_def intro!: ext)
  done

lemmas [sepref_fr_rules] = is_marked_added.XX.mop_refine[unfolded mop_is_marked_added_heur_st_alt_def]
lemmas [unfolded inline_direct_return_node_case, llvm_code] =
  mop_is_marked_added_heur_stats_st_impl_def[unfolded  read_all_st_code_def]

definition length_watchlist_raw where
  \<open>length_watchlist_raw S = length (get_watched_wl_heur S)\<close>

sepref_def length_watchlist_full_impl
  is \<open>RETURN o length\<close>
  :: \<open>watchlist_fast_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  unfolding op_list_list_len_def[symmetric]
  by sepref

definition length_watchlist_raw_code where
  \<open>length_watchlist_raw_code = read_watchlist_wl_heur_code (length_watchlist_full_impl)\<close>

global_interpretation watchlist_length_raw: read_watchlist_param_adder0 where
  f' = \<open>RETURN o length\<close> and
  f = \<open>length_watchlist_full_impl\<close> and
  x_assn = sint64_nat_assn and
  P = \<open>(\<lambda>_. True)\<close>
  rewrites
    \<open>read_watchlist_wl_heur (RETURN \<circ> length) = RETURN o length_watchlist_raw\<close> and
    \<open>read_watchlist_wl_heur_code (length_watchlist_full_impl) = length_watchlist_raw_code\<close>
  apply unfold_locales
  apply (rule length_watchlist_full_impl.refine)
  subgoal
     by (auto intro!: ext simp: length_watchlist_raw_def read_all_st_def length_watchlist_def
         length_ll_def
       split: isasat_int_splits)
  subgoal by (auto simp: length_watchlist_raw_code_def)
  done

lemmas [sepref_fr_rules] = watchlist_length_raw.refine
lemmas [unfolded inline_direct_return_node_case, llvm_code] =
  length_watchlist_raw_code_def[unfolded read_all_st_code_def]

definition get_restart_count_st where
  \<open>get_restart_count_st S = get_restart_count (get_stats_heur S)\<close>

definition get_restart_count_st_impl :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>get_restart_count_st_impl = read_stats_wl_heur_code get_restart_count_impl\<close>

global_interpretation restart_count: read_stats_param_adder0 where
  f' = \<open>RETURN o get_restart_count\<close> and
  f = get_restart_count_impl and
  x_assn = word_assn and
  P = \<open>\<lambda>_. True\<close>
  rewrites \<open>read_stats_wl_heur (RETURN o get_restart_count) = RETURN o get_restart_count_st\<close> and
    \<open>read_stats_wl_heur_code get_restart_count_impl = get_restart_count_st_impl\<close>
  apply unfold_locales
  apply (rule get_restart_count_impl.refine; assumption)
  subgoal by (auto simp: read_all_st_def stats_conflicts_def get_restart_count_st_def intro!: ext
    split: isasat_int_splits)
  subgoal by (auto simp: get_restart_count_st_impl_def)
  done

definition get_reductions_count_fast_code :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>get_reductions_count_fast_code = read_stats_wl_heur_code get_reduction_count_impl\<close>

(*TODO check if this is the right statistics to read!*)
global_interpretation reduction_count: read_stats_param_adder0 where
  f' = \<open>RETURN o get_reduction_count\<close> and
  f = get_reduction_count_impl and
  x_assn = word_assn and
  P = \<open>\<lambda>_. True\<close>
  rewrites \<open>read_stats_wl_heur (RETURN o get_reduction_count) = RETURN o get_reductions_count\<close> and
    \<open>read_stats_wl_heur_code get_reduction_count_impl = get_reductions_count_fast_code\<close>
  apply unfold_locales
  apply (rule get_reduction_count_impl.refine)
  subgoal by (auto simp: read_all_st_def stats_conflicts_def intro!: ext
    split: isasat_int_splits)
  subgoal by (auto simp: get_reductions_count_fast_code_def)
  done


definition get_irredundant_count_st_code :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>get_irredundant_count_st_code = read_stats_wl_heur_code get_irredundant_count_impl\<close>

global_interpretation irredandant_count: read_stats_param_adder0 where
  f' = \<open>RETURN o get_irredundant_count\<close> and
  f = get_irredundant_count_impl and
  x_assn = word_assn and
  P = \<open>\<lambda>_. True\<close>
  rewrites \<open>read_stats_wl_heur (RETURN o get_irredundant_count) = RETURN o get_irredundant_count_st\<close> and
    \<open>read_stats_wl_heur_code get_irredundant_count_impl = get_irredundant_count_st_code\<close>
  apply unfold_locales
  apply (rule get_irredundant_count_impl.refine)
  subgoal by (auto simp: read_all_st_def get_irredundant_count_st_def stats_conflicts_def intro!: ext
    split: isasat_int_splits)
  subgoal by (auto simp: get_irredundant_count_st_code_def)
  done

definition get_slow_ema_heur_full where
  \<open>get_slow_ema_heur_full S = ema_get_value (slow_ema_of S)\<close>
definition get_fast_ema_heur_full where
  \<open>get_fast_ema_heur_full S = ema_get_value (fast_ema_of S)\<close>

sepref_def get_slow_ema_heur_full_impl
  is \<open>RETURN o get_slow_ema_heur_full\<close>
  :: \<open>heuristic_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding get_slow_ema_heur_full_def
  by sepref

sepref_def get_fast_ema_heur_full_impl
  is \<open>RETURN o get_fast_ema_heur_full\<close>
  :: \<open>heuristic_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding get_fast_ema_heur_full_def
  by sepref

definition get_slow_ema_heur_st where
  \<open>get_slow_ema_heur_st S = ema_get_value (get_slow_ema_heur S)\<close>
definition get_fast_ema_heur_st where
  \<open>get_fast_ema_heur_st S = ema_get_value (get_fast_ema_heur S)\<close>

definition get_slow_ema_heur_st_impl :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>get_slow_ema_heur_st_impl = read_heur_wl_heur_code get_slow_ema_heur_full_impl\<close>

definition get_fast_ema_heur_st_impl :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>get_fast_ema_heur_st_impl = read_heur_wl_heur_code get_fast_ema_heur_full_impl\<close>

global_interpretation slow_ema: read_heur_param_adder0 where
  f' = \<open>RETURN o get_slow_ema_heur_full\<close> and
  f = get_slow_ema_heur_full_impl and
  x_assn = word_assn and
  P = \<open>\<lambda>_. True\<close>
  rewrites \<open>read_heur_wl_heur (RETURN o get_slow_ema_heur_full) = RETURN o get_slow_ema_heur_st\<close> and
    \<open>read_heur_wl_heur_code get_slow_ema_heur_full_impl = get_slow_ema_heur_st_impl\<close>
  apply unfold_locales
  apply (rule get_slow_ema_heur_full_impl.refine)
  subgoal by (auto simp: read_all_st_def stats_conflicts_def get_slow_ema_heur_st_def
      get_slow_ema_heur_full_def intro!: ext
    split: isasat_int_splits)
  subgoal by (auto simp: get_slow_ema_heur_st_impl_def)
  done

global_interpretation fast_ema: read_heur_param_adder0 where
  f' = \<open>RETURN o get_fast_ema_heur_full\<close> and
  f = get_fast_ema_heur_full_impl and
  x_assn = word_assn and
  P = \<open>\<lambda>_. True\<close>
  rewrites \<open>read_heur_wl_heur (RETURN o get_fast_ema_heur_full) = RETURN o get_fast_ema_heur_st\<close> and
    \<open>read_heur_wl_heur_code get_fast_ema_heur_full_impl = get_fast_ema_heur_st_impl\<close>
  apply unfold_locales
  apply (rule get_fast_ema_heur_full_impl.refine)
  subgoal by (auto simp: read_all_st_def stats_conflicts_def get_fast_ema_heur_st_def
      get_fast_ema_heur_full_def intro!: ext
    split: isasat_int_splits)
  subgoal by (auto simp: get_fast_ema_heur_st_impl_def)
  done

lemmas [sepref_fr_rules] = restart_count.refine reduction_count.refine fast_ema.refine slow_ema.refine
lemmas [unfolded inline_direct_return_node_case, llvm_code] =
  get_restart_count_st_impl_def[unfolded read_all_st_code_def]
  get_reductions_count_fast_code_def[unfolded read_all_st_code_def]
  get_fast_ema_heur_st_impl_def[unfolded read_all_st_code_def]
  get_slow_ema_heur_st_impl_def[unfolded read_all_st_code_def]

end
