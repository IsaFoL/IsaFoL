theory IsaSAT_Setup2_LLVM
  imports IsaSAT_Setup IsaSAT_Watch_List_LLVM IsaSAT_Lookup_Conflict_LLVM
    More_Sepref.WB_More_Refinement IsaSAT_Clauses_LLVM LBD_LLVM
    IsaSAT_Options_LLVM IsaSAT_VMTF_Setup_LLVM
    IsaSAT_Arena_Sorting_LLVM
    IsaSAT_Rephase_LLVM
    IsaSAT_EMA_LLVM
    IsaSAT_Stats_LLVM
    IsaSAT_Setup0_LLVM
begin

definition opts_restart_st_fast_code :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>opts_restart_st_fast_code = read_opts_wl_heur_code opts_rel_restart_code\<close>

global_interpretation opts_restart: read_opts_param_adder0 where
  f' = \<open>RETURN o opts_restart\<close> and
  f = opts_rel_restart_code and
  x_assn = bool1_assn and
  P = \<open>\<lambda>_. True\<close>
  rewrites \<open>read_opts_wl_heur (RETURN o opts_restart) = RETURN o opts_restart_st\<close> and
    \<open>read_opts_wl_heur_code opts_rel_restart_code = opts_restart_st_fast_code\<close>
  apply unfold_locales
  apply (rule opts_refine; assumption)
  subgoal by (auto simp: opts_restart_st_def read_opts_wl_heur_def intro!: ext
    split: isasat_int.splits)
  subgoal by (auto simp: opts_restart_st_fast_code_def)
  done

definition opts_reduction_st_fast_code :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>opts_reduction_st_fast_code = read_opts_wl_heur_code opts_rel_reduce_code\<close>

global_interpretation opts_reduce: read_opts_param_adder0 where
  f' = \<open>RETURN o opts_reduce\<close> and
  f = opts_rel_reduce_code and
  x_assn = bool1_assn and
  P = \<open>\<lambda>_. True\<close>
  rewrites \<open>read_opts_wl_heur (RETURN o opts_reduce) = RETURN o opts_reduction_st\<close> and
    \<open>read_opts_wl_heur_code opts_rel_reduce_code = opts_reduction_st_fast_code\<close>
  apply unfold_locales
  apply (rule opts_refine; assumption)
  subgoal by (auto simp: opts_reduction_st_fast_code_def read_opts_wl_heur_def opts_reduction_st_def intro!: ext
    split: isasat_int.splits)
  subgoal by (auto simp: opts_reduction_st_fast_code_def)
  done

definition opts_unbounded_mode_st_fast_code :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
   \<open>opts_unbounded_mode_st_fast_code = read_opts_wl_heur_code opts_rel_unbounded_mode_code\<close>

global_interpretation opts_unbounded_mode: read_opts_param_adder0 where
  f' = \<open>RETURN o opts_unbounded_mode\<close> and
  f = opts_rel_unbounded_mode_code and
  x_assn = bool1_assn and
  P = \<open>\<lambda>_. True\<close>
  rewrites \<open>read_opts_wl_heur (RETURN o opts_unbounded_mode) = RETURN o opts_unbounded_mode_st\<close> and
    \<open>read_opts_wl_heur_code opts_rel_unbounded_mode_code = opts_unbounded_mode_st_fast_code\<close>
  apply unfold_locales
  apply (rule opts_refine; assumption)
  subgoal by (auto simp: read_opts_wl_heur_def opts_unbounded_mode_st_def intro!: ext
    split: isasat_int.splits)
  subgoal by (auto simp: opts_unbounded_mode_st_fast_code_def)
  done

definition opts_minimum_between_restart_st_fast_code :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
   \<open>opts_minimum_between_restart_st_fast_code = read_opts_wl_heur_code opts_rel_miminum_between_restart_code\<close>

global_interpretation opts_minimum_between_restart: read_opts_param_adder0 where
  f' = \<open>RETURN o opts_minimum_between_restart\<close> and
  f = opts_rel_miminum_between_restart_code and
  x_assn = word_assn and
  P = \<open>\<lambda>_. True\<close>
  rewrites \<open>read_opts_wl_heur (RETURN o opts_minimum_between_restart) = RETURN o opts_minimum_between_restart_st\<close> and
    \<open>read_opts_wl_heur_code opts_rel_miminum_between_restart_code = opts_minimum_between_restart_st_fast_code\<close>
  apply unfold_locales
  apply (rule opts_refine; assumption)
  subgoal by (auto simp: read_opts_wl_heur_def opts_minimum_between_restart_st_def intro!: ext
    split: isasat_int.splits)
  subgoal by (auto simp: opts_minimum_between_restart_st_fast_code_def)
  done

definition opts_restart_coeff1_st_fast_code :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
   \<open>opts_restart_coeff1_st_fast_code = read_opts_wl_heur_code opts_rel_restart_coeff1_code\<close>

global_interpretation opts_restart_coeff1: read_opts_param_adder0 where
  f' = \<open>RETURN o opts_restart_coeff1\<close> and
  f = opts_rel_restart_coeff1_code and
  x_assn = word_assn and
  P = \<open>\<lambda>_. True\<close>
  rewrites \<open>read_opts_wl_heur (RETURN o opts_restart_coeff1) = RETURN o opts_restart_coeff1_st\<close> and
    \<open>read_opts_wl_heur_code opts_rel_restart_coeff1_code = opts_restart_coeff1_st_fast_code\<close>
  apply unfold_locales
  apply (rule opts_refine; assumption)
  subgoal by (auto simp: read_opts_wl_heur_def opts_minimum_between_restart_st_def opts_restart_coeff1_st_def intro!: ext
    split: isasat_int.splits)
  subgoal by (auto simp: opts_restart_coeff1_st_fast_code_def)
  done

definition opts_restart_coeff2_st_fast_code :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
   \<open>opts_restart_coeff2_st_fast_code = read_opts_wl_heur_code opts_rel_restart_coeff2_code\<close>

global_interpretation opts_restart_coeff2: read_opts_param_adder0 where
  f' = \<open>RETURN o opts_restart_coeff2\<close> and
  f = opts_rel_restart_coeff2_code and
  x_assn = \<open>snat_assn' (TYPE(64))\<close> and
  P = \<open>\<lambda>_. True\<close>
  rewrites \<open>read_opts_wl_heur (RETURN o opts_restart_coeff2) = RETURN o opts_restart_coeff2_st\<close> and
    \<open>read_opts_wl_heur_code opts_rel_restart_coeff2_code = opts_restart_coeff2_st_fast_code\<close>
  apply unfold_locales
  apply (rule opts_refine; assumption)
  subgoal by (auto simp: read_opts_wl_heur_def opts_minimum_between_restart_st_def opts_restart_coeff2_st_def intro!: ext
    split: isasat_int.splits)
  subgoal by (auto simp: opts_restart_coeff2_st_fast_code_def)
  done

definition units_since_last_GC_st_code :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
   \<open>units_since_last_GC_st_code = read_stats_wl_heur_code units_since_last_GC_stats_impl\<close>

global_interpretation units_since_last_GC: read_stats_param_adder0 where
  f' = \<open>RETURN o units_since_last_GC\<close> and
  f = units_since_last_GC_stats_impl and
  x_assn = word_assn and
  P = \<open>\<lambda>_. True\<close>
  rewrites \<open>read_stats_wl_heur (RETURN o units_since_last_GC) = RETURN o units_since_last_GC_st\<close> and
    \<open>read_stats_wl_heur_code units_since_last_GC_stats_impl = units_since_last_GC_st_code\<close>
  apply unfold_locales
  apply (rule stats_refine; assumption)
  subgoal by (auto simp: read_stats_wl_heur_def units_since_last_GC_st_def intro!: ext
    split: isasat_int.splits)
  subgoal by (auto simp: units_since_last_GC_st_code_def)
  done
thm get_GC_units_opt_def
find_theorems opts_GC_units_lim RETURN
(*opts_GC_units_lim opts_rel_GC_units_lim_code*)
lemmas [sepref_fr_rules] =
  opts_restart.refine[unfolded]
  opts_reduce.refine[unfolded]
  opts_unbounded_mode.refine
  opts_minimum_between_restart.refine
  opts_restart_coeff1.refine
  opts_restart_coeff2.refine
  units_since_last_GC.refine
  units_since_last_GC.refine

lemmas [unfolded inline_direct_return_node_case, llvm_code] =
  opts_restart_st_fast_code_def[unfolded read_opts_wl_heur_code_def]
  opts_reduction_st_fast_code_def[unfolded read_opts_wl_heur_code_def]
  opts_unbounded_mode_st_fast_code_def[unfolded read_opts_wl_heur_code_def]
  opts_minimum_between_restart_st_fast_code_def[unfolded read_opts_wl_heur_code_def]
  opts_restart_coeff1_st_fast_code_def[unfolded read_opts_wl_heur_code_def]
  opts_restart_coeff2_st_fast_code_def[unfolded read_opts_wl_heur_code_def]
  units_since_last_GC_st_code_def[unfolded read_stats_wl_heur_def]

named_theorems state_extractors \<open>Definition of all functions modifying the state\<close>
lemmas [state_extractors] =
  extract_stats_wl_heur_def
  isasat_state_ops.remove_stats_wl_heur_def
  update_stats_wl_heur_def

sepref_register reset_units_since_last_GC

lemma reset_units_since_last_GC_st_alt_def:
  \<open>reset_units_since_last_GC_st S =
  (let (stats, S) = extract_stats_wl_heur S in
  let stats = reset_units_since_last_GC stats in
  let S = update_stats_wl_heur stats S in S
  )\<close>
  by (auto simp: reset_units_since_last_GC_st_def state_extractors split: isasat_int.splits)


sepref_def reset_units_since_last_GC_st_code
  is \<open>RETURN o reset_units_since_last_GC_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>d  \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding reset_units_since_last_GC_st_alt_def
  by sepref


experiment
begin
export_llvm opts_reduction_st_fast_code opts_restart_st_fast_code opts_unbounded_mode_st_fast_code
  opts_minimum_between_restart_st_fast_code
end

sepref_def get_GC_units_opt_code
  is \<open>RETURN o get_GC_units_opt\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  supply [[goals_limit=1]]
  unfolding get_GC_units_opt_alt_def
    isasat_bounded_assn_def fold_tuple_optimizations
  by sepref

sepref_register opts_reduction_st opts_restart_st opts_restart_coeff2_st opts_restart_coeff1_st
    opts_minimum_between_restart_st opts_unbounded_mode_st get_GC_units_opt units_since_last_GC_st

sepref_register isasat_length_trail_st

sepref_def isasat_length_trail_st_code
  is \<open>RETURN o isasat_length_trail_st\<close>
  :: \<open>[isa_length_trail_pre o get_trail_wl_heur]\<^sub>a isasat_bounded_assn\<^sup>k  \<rightarrow> sint64_nat_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_length_trail_st_alt_def isasat_bounded_assn_def
  by sepref

sepref_def mop_isasat_length_trail_st_code
  is \<open>mop_isasat_length_trail_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k  \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  supply [[goals_limit=1]]
  unfolding mop_isasat_length_trail_st_alt_def isasat_bounded_assn_def
  by sepref

sepref_register get_pos_of_level_in_trail_imp_st

sepref_def get_pos_of_level_in_trail_imp_st_code
  is \<open>uncurry get_pos_of_level_in_trail_imp_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k  \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  supply [[goals_limit=1]]
  unfolding get_pos_of_level_in_trail_imp_alt_def isasat_bounded_assn_def
  apply (rewrite in \<open>_\<close> eta_expand[where f = RETURN])
  apply (rewrite in \<open>RETURN \<hole>\<close> annot_unat_snat_upcast[where 'l=64])
  by sepref

sepref_def clause_not_marked_to_delete_heur_fast_code
  is \<open>uncurry (RETURN oo clause_not_marked_to_delete_heur)\<close>
  :: \<open>[clause_not_marked_to_delete_heur_pre]\<^sub>a isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> bool1_assn\<close>
  supply [[goals_limit=1]]
  unfolding clause_not_marked_to_delete_heur_alt_def isasat_bounded_assn_def
     clause_not_marked_to_delete_heur_pre_def
  by sepref

sepref_def mop_clause_not_marked_to_delete_heur_impl
  is \<open>uncurry mop_clause_not_marked_to_delete_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding mop_clause_not_marked_to_delete_heur_alt_def
    clause_not_marked_to_delete_heur_pre_def  prod.case isasat_bounded_assn_def
  by sepref

sepref_def mop_arena_lbd_st_impl
  is \<open>uncurry mop_arena_lbd_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=1]]
  unfolding mop_arena_lbd_st_alt_def isasat_bounded_assn_def
  by sepref

sepref_def mop_arena_status_st_impl
  is \<open>uncurry mop_arena_status_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a status_impl_assn\<close>
  supply [[goals_limit=1]]
  unfolding mop_arena_status_st_alt_def isasat_bounded_assn_def
  by sepref

sepref_def mop_marked_as_used_st_impl
  is \<open>uncurry mop_marked_as_used_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a unat_assn' TYPE(2)\<close>
  supply [[goals_limit=1]]
  unfolding mop_marked_as_used_st_alt_def isasat_bounded_assn_def
  by sepref

sepref_def mop_arena_length_st_impl
  is \<open>uncurry mop_arena_length_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  supply [[goals_limit=1]]
  unfolding mop_arena_length_st_alt_def isasat_bounded_assn_def
  by sepref

sepref_register incr_wasted_st full_arena_length_st wasted_bytes_st
sepref_def incr_wasted_st_impl
  is \<open>uncurry (RETURN oo incr_wasted_st)\<close>
  :: \<open>word64_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply[[goals_limit=1]]
  unfolding incr_wasted_st_def
    isasat_bounded_assn_def fold_tuple_optimizations
  by sepref

sepref_def full_arena_length_st_impl
  is \<open>RETURN o full_arena_length_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  unfolding full_arena_length_st_def isasat_bounded_assn_def
  by sepref

sepref_register get_global_conflict_count
sepref_def get_global_conflict_count_impl
  is \<open>RETURN o get_global_conflict_count\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding get_global_conflict_count_alt_def isasat_bounded_assn_def
  by sepref

sepref_def get_count_max_lvls_heur_impl
  is \<open>RETURN o get_count_max_lvls_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding get_count_max_lvls_heur_def isasat_bounded_assn_def
  by sepref

sepref_def clss_size_resetUS0_st
  is \<open>RETURN o clss_size_resetUS0_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding fold_tuple_optimizations isasat_bounded_assn_def clss_size_resetUS0_st_alt_def
  by sepref

sepref_def length_clauses_heur_impl
  is \<open>RETURN o length_clauses_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  unfolding length_clauses_heur_alt_def isasat_bounded_assn_def
  by sepref

end
