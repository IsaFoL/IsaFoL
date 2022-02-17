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
  subgoal by (auto simp: opts_restart_st_def read_all_wl_heur_def intro!: ext
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
  subgoal by (auto simp: opts_reduction_st_fast_code_def read_all_wl_heur_def opts_reduction_st_def intro!: ext
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
  subgoal by (auto simp: read_all_wl_heur_def opts_unbounded_mode_st_def intro!: ext
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
  subgoal by (auto simp: read_all_wl_heur_def opts_minimum_between_restart_st_def intro!: ext
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
  subgoal by (auto simp: read_all_wl_heur_def opts_minimum_between_restart_st_def opts_restart_coeff1_st_def intro!: ext
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
  subgoal by (auto simp: read_all_wl_heur_def opts_minimum_between_restart_st_def opts_restart_coeff2_st_def intro!: ext
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
  subgoal by (auto simp: read_all_wl_heur_def units_since_last_GC_st_def intro!: ext
    split: isasat_int.splits)
  subgoal by (auto simp: units_since_last_GC_st_code_def)
  done

definition get_GC_units_opt_code :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>get_GC_units_opt_code = read_opts_wl_heur_code opts_rel_GC_units_lim_code\<close>

global_interpretation opts_GC_units_lim: read_opts_param_adder0 where
  f' = \<open>RETURN o opts_GC_units_lim\<close> and
  f = opts_rel_GC_units_lim_code and
  x_assn = word_assn and
  P = \<open>\<lambda>_. True\<close>
  rewrites \<open>read_opts_wl_heur (RETURN o opts_GC_units_lim) = RETURN o get_GC_units_opt\<close> and
    \<open>read_opts_wl_heur_code opts_rel_GC_units_lim_code = get_GC_units_opt_code\<close>
  apply unfold_locales
  apply (rule opts_refine)
  subgoal by (auto simp: read_all_wl_heur_def get_GC_units_opt_def intro!: ext
    split: isasat_int.splits)
  subgoal by (auto simp: get_GC_units_opt_code_def)
  done

definition get_target_opts_impl :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>get_target_opts_impl = read_opts_wl_heur_code opts_rel_target_code\<close>

global_interpretation get_target_opts: read_opts_param_adder0 where
  f' = \<open>RETURN o opts_target\<close> and
  f = opts_rel_target_code and
  x_assn = \<open>word_assn' TYPE(3)\<close> and
  P = \<open>\<lambda>_. True\<close>
  rewrites \<open>read_opts_wl_heur (RETURN o opts_target) = RETURN o get_target_opts\<close> and
    \<open>read_opts_wl_heur_code opts_rel_target_code = get_target_opts_impl\<close>
  apply unfold_locales
  apply (rule opts_refine)
  subgoal by (auto simp: get_target_opts_def read_all_wl_heur_def intro!: ext
    split: isasat_int.splits)
  subgoal by (auto simp: get_target_opts_impl_def)
  done
thm get_target_opts_def
  find_theorems opts_target RETURN
(*
sepref_def get_opts_impl
  is \<open>RETURN o get_opts\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a opts_assn\<close>
  unfolding get_opts_alt_def isasat_bounded_assn_def fold_tuple_optimizations
  by sepref
*)


definition isasat_length_trail_st_code :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>isasat_length_trail_st_code = read_trail_wl_heur_code isa_length_trail_fast_code\<close>

global_interpretation trail_length: read_trail_param_adder0 where
  f' = \<open>RETURN o isa_length_trail\<close> and
  f = isa_length_trail_fast_code and
  x_assn = sint64_nat_assn and
  P = \<open>\<lambda>_. True\<close>
  rewrites  \<open>read_trail_wl_heur (RETURN o isa_length_trail) = RETURN o isasat_length_trail_st\<close> and
    \<open>read_trail_wl_heur_code isa_length_trail_fast_code = isasat_length_trail_st_code\<close>
  apply unfold_locales
  apply (rule isa_length_trail_fast_code.refine)
  subgoal by (auto simp: isa_length_trail_def read_all_wl_heur_def isasat_length_trail_st_def
    intro!: ext split: isasat_int.splits)
  subgoal by (auto simp: isasat_length_trail_st_code_def)
  done

lemma get_pos_of_level_in_trail_imp_alt_def:
  \<open>get_pos_of_level_in_trail_imp = (\<lambda>S C. do {k \<leftarrow> get_pos_of_level_in_trail_imp S C; RETURN k})\<close>
  by auto

sepref_def get_pos_of_level_in_trail_imp_code
  is \<open>uncurry get_pos_of_level_in_trail_imp\<close>
  :: \<open>trail_pol_fast_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k  \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  supply [[goals_limit=1]]
  apply (subst get_pos_of_level_in_trail_imp_alt_def)
  apply (rewrite in \<open>_\<close> eta_expand[where f = RETURN])
  apply (rewrite in \<open>RETURN \<hole>\<close> annot_unat_snat_upcast[where 'l=64])
  by sepref

definition get_pos_of_level_in_trail_imp_st_code :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>get_pos_of_level_in_trail_imp_st_code = (\<lambda>N C. read_trail_wl_heur_code (\<lambda>c. get_pos_of_level_in_trail_imp_code c C) N)\<close>

global_interpretation pos_of_level_in_trail: read_trail_param_adder where
  R = \<open>unat_rel' TYPE(32)\<close> and
  f' = \<open>\<lambda>M c. get_pos_of_level_in_trail_imp c M\<close> and
  f = \<open>\<lambda>M c. get_pos_of_level_in_trail_imp_code c M\<close> and
  x_assn = sint64_nat_assn and
  P = \<open>\<lambda>_ _. True\<close>
  rewrites  \<open>(\<lambda>N C'. read_trail_wl_heur (\<lambda>c. get_pos_of_level_in_trail_imp c C') N) = get_pos_of_level_in_trail_imp_st\<close> and
    \<open>(\<lambda>N C. read_trail_wl_heur_code (\<lambda>c. get_pos_of_level_in_trail_imp_code c C) N) = get_pos_of_level_in_trail_imp_st_code\<close>
  apply unfold_locales
  apply (subst lambda_comp_true)+
  apply (rule get_pos_of_level_in_trail_imp_code.refine)
  subgoal by (auto simp: get_pos_of_level_in_trail_imp_st_def read_all_wl_heur_def
    intro!: ext split: isasat_int.splits)
  subgoal by (auto simp: get_pos_of_level_in_trail_imp_st_code_def)
  done

definition get_global_conflict_count_impl :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
   \<open>get_global_conflict_count_impl = read_stats_wl_heur_code stats_conflicts_stats_impl\<close>

global_interpretation stats_conflict: read_stats_param_adder0 where
  f' = \<open>RETURN o stats_conflicts\<close> and
  f = stats_conflicts_stats_impl and
  x_assn = word_assn and
  P = \<open>\<lambda>_. True\<close>
  rewrites \<open>read_stats_wl_heur (RETURN o stats_conflicts) = RETURN o get_global_conflict_count\<close> and
    \<open>read_stats_wl_heur_code stats_conflicts_stats_impl = get_global_conflict_count_impl\<close>
  apply unfold_locales
  apply (rule stats_refine; assumption)
  subgoal by (auto simp: read_all_wl_heur_def stats_conflicts_def get_global_conflict_count_def intro!: ext
    split: isasat_int.splits)
  subgoal by (auto simp: get_global_conflict_count_impl_def)
  done

lemmas [unfolded lambda_comp_true, sepref_fr_rules] =
  opts_restart.refine[unfolded]
  opts_reduce.refine[unfolded]
  opts_unbounded_mode.refine
  opts_minimum_between_restart.refine
  opts_restart_coeff1.refine
  opts_restart_coeff2.refine
  units_since_last_GC.refine
  opts_GC_units_lim.refine
  trail_length.refine
  pos_of_level_in_trail.refine
  stats_conflict.refine
  get_target_opts.refine

sepref_register opts_reduction_st opts_restart_st opts_restart_coeff2_st opts_restart_coeff1_st
    opts_minimum_between_restart_st opts_unbounded_mode_st get_GC_units_opt units_since_last_GC_st
    isasat_length_trail_st get_pos_of_level_in_trail_imp_st

lemmas [unfolded inline_direct_return_node_case, llvm_code] =
  opts_restart_st_fast_code_def[unfolded read_all_wl_heur_code_def]
  opts_reduction_st_fast_code_def[unfolded read_all_wl_heur_code_def]
  opts_unbounded_mode_st_fast_code_def[unfolded read_all_wl_heur_code_def]
  opts_minimum_between_restart_st_fast_code_def[unfolded read_all_wl_heur_code_def]
  opts_restart_coeff1_st_fast_code_def[unfolded read_all_wl_heur_code_def]
  opts_restart_coeff2_st_fast_code_def[unfolded read_all_wl_heur_code_def]
  units_since_last_GC_st_code_def[unfolded read_all_wl_heur_def]
  get_GC_units_opt_code_def[unfolded read_all_wl_heur_code_def]
  isasat_length_trail_st_code_def[unfolded read_all_wl_heur_code_def]
  get_pos_of_level_in_trail_imp_st_code_def[unfolded read_all_wl_heur_code_def]
  get_global_conflict_count_impl_def[unfolded read_all_wl_heur_code_def]
  get_target_opts_impl_def[unfolded read_all_wl_heur_code_def]

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

lemma mop_isasat_length_trail_st_alt_def:
  \<open>mop_isasat_length_trail_st S = do {
    ASSERT(isa_length_trail_pre (get_trail_wl_heur S));
    RETURN (isasat_length_trail_st S)
  }\<close>
  unfolding isasat_length_trail_st_def mop_isasat_length_trail_st_def
  by auto


sepref_def mop_isasat_length_trail_st_code
  is \<open>mop_isasat_length_trail_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k  \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  supply [[goals_limit=1]]
  unfolding mop_isasat_length_trail_st_alt_def
  by sepref


definition arena_status_st where
  \<open>arena_status_st = (\<lambda>S. arena_status (get_clauses_wl_heur S))\<close>

definition arena_status_st_impl where
  \<open>arena_status_st_impl = (\<lambda>S C'. read_arena_wl_heur_code (\<lambda>N. arena_status_impl N C') S)\<close>

global_interpretation arena_is_valid: read_arena_param_adder where
  R = \<open>snat_rel' TYPE(64)\<close> and
  f = \<open>\<lambda>C N. arena_status_impl N C\<close> and
  f' = \<open>(\<lambda>C' N.  (RETURN oo arena_status) N C')\<close> and
  x_assn = status_impl_assn and
  P = \<open>(\<lambda>C S. arena_is_valid_clause_vdom S C)\<close>
  rewrites \<open>(\<lambda>S C'. read_arena_wl_heur (\<lambda>N.  (RETURN oo arena_status) N C') S) = RETURN oo arena_status_st\<close> and
  \<open>(\<lambda>S C'. read_arena_wl_heur_code (\<lambda>N. arena_status_impl N C') S) = arena_status_st_impl\<close> and
  \<open>arena_is_valid.mop = mop_arena_status_st\<close> and
  \<open>(\<lambda>S. arena_is_valid_clause_vdom (get_clauses_wl_heur S)) = curry clause_not_marked_to_delete_heur_pre\<close>
  apply unfold_locales
  apply (rule arena_status_impl.refine)
  subgoal by (auto simp: mop_arena_status_st_def read_all_wl_heur_def arena_status_st_def
    intro!: ext split: isasat_int.splits)
  subgoal by (auto simp: arena_status_st_impl_def)
  subgoal by (auto simp: read_arena_param_adder_ops.mop_def mop_arena_status_st_def mop_arena_status_def read_all_wl_heur_def arena_status_st_def
    intro!: ext split: isasat_int.splits)
  subgoal by (auto simp: clause_not_marked_to_delete_heur_pre_def)
  done

lemmas [sepref_fr_rules] = arena_is_valid.mop_refine arena_is_valid.refine[unfolded uncurry_curry_id]

sepref_def mop_arena_status_st_impl
  is \<open>uncurry mop_arena_status_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a status_impl_assn\<close>
  supply [[goals_limit=1]]
  by sepref

definition arena_length_st_impl :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>arena_length_st_impl = (\<lambda>S C'. read_arena_wl_heur_code (\<lambda>N. arena_length_impl N C') S)\<close>

global_interpretation arena_length_clause: read_arena_param_adder where
  R = \<open>snat_rel' TYPE(64)\<close> and
  f = \<open>\<lambda>C N. arena_length_impl N C\<close> and
  f' = \<open>(\<lambda>C' N.  (RETURN oo arena_length) N C')\<close> and
  x_assn = sint64_nat_assn and
  P = \<open>(\<lambda>C S. arena_is_valid_clause_idx S C)\<close>
  rewrites \<open>(\<lambda>S C'. read_arena_wl_heur (\<lambda>N.  (RETURN oo arena_status) N C') S) = RETURN oo arena_status_st\<close> and
  \<open>(\<lambda>S C'. read_arena_wl_heur_code (\<lambda>N. arena_length_impl N C') S) = arena_length_st_impl\<close> and
  \<open>arena_length_clause.mop = mop_arena_length_st\<close>
  apply unfold_locales
  apply (rule arena_length_impl.refine)
  subgoal by (auto simp: mop_arena_status_st_def read_all_wl_heur_def arena_status_st_def
    intro!: ext split: isasat_int.splits)
  subgoal by (auto simp: arena_length_st_impl_def)
  subgoal
    by (auto simp: read_arena_param_adder_ops.mop_def mop_arena_length_st_def mop_arena_length_def read_all_wl_heur_def
      split: isasat_int.splits intro!: ext)
  done

lemmas [sepref_fr_rules] = arena_length_clause.mop_refine
lemmas [unfolded inline_direct_return_node_case, llvm_code] = arena_length_st_impl_def[unfolded read_all_wl_heur_code_def]
  arena_status_st_impl_def[unfolded read_all_wl_heur_code_def]

sepref_definition arena_full_length_impl
  is \<open>RETURN o length\<close>
  :: \<open>arena_fast_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  by sepref

definition full_arena_length_st_impl :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>full_arena_length_st_impl = read_arena_wl_heur_code  (arena_full_length_impl)\<close>

global_interpretation arena_full_length: read_arena_param_adder0 where
  f = \<open>arena_full_length_impl\<close> and
  f' = \<open>(RETURN o length)\<close> and
  x_assn = sint64_nat_assn and
  P = \<open>(\<lambda>_. True)\<close>
  rewrites \<open>read_arena_wl_heur (RETURN o length) = RETURN o full_arena_length_st\<close> and
    \<open>read_arena_wl_heur_code  (arena_full_length_impl) = full_arena_length_st_impl\<close>
  apply unfold_locales
  apply (rule arena_full_length_impl.refine)
  subgoal by (auto simp: mop_arena_status_st_def read_all_wl_heur_def full_arena_length_st_def
    intro!: ext split: isasat_int.splits)
  subgoal by (auto simp: full_arena_length_st_impl_def)
  done

lemma incr_wasted_st_alt_def:
  \<open>incr_wasted_st = (\<lambda>waste S. do{
  let (heur, S) = extract_heur_wl_heur S in
  let heur = incr_wasted waste heur in
  let S = update_heur_wl_heur heur S in S
  })\<close>
    by (auto simp: incr_wasted_st_def state_extractors intro!: ext split: isasat_int.splits)

sepref_def incr_wasted_st_impl
  is \<open>uncurry (RETURN oo incr_wasted_st)\<close>
  :: \<open>word64_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply[[goals_limit=1]]
  unfolding incr_wasted_st_alt_def
  by sepref

lemma id_clvls_assn: \<open>(Mreturn, RETURN) \<in> (uint32_nat_assn)\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare vcg

definition get_count_max_lvls_heur_impl :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>get_count_max_lvls_heur_impl = read_ccount_wl_heur_code  (Mreturn)\<close>

global_interpretation get_count_max_lvls: read_ccount_param_adder0 where
  f = \<open>Mreturn\<close> and
  f' = \<open>(RETURN)\<close> and
  x_assn = uint32_nat_assn and
  P = \<open>(\<lambda>_. True)\<close>
  rewrites \<open>read_ccount_wl_heur (RETURN) = RETURN o get_count_max_lvls_heur\<close> and
    \<open>read_ccount_wl_heur_code  (Mreturn) = get_count_max_lvls_heur_impl\<close>
  apply unfold_locales
  apply (rule id_clvls_assn)
  subgoal by (auto simp: read_all_wl_heur_def get_count_max_lvls_heur_def
    intro!: ext split: isasat_int.splits)
  subgoal by (auto simp: get_count_max_lvls_heur_impl_def)
  done


lemmas [sepref_fr_rules] = arena_full_length.refine get_count_max_lvls.refine
lemmas [unfolded inline_direct_return_node_case, llvm_code] = full_arena_length_st_impl_def[unfolded read_all_wl_heur_code_def]
  arena_full_length_impl_def
   get_count_max_lvls_heur_impl_def[unfolded read_all_wl_heur_code_def]

lemma clss_size_resetUS0_st_alt_def:
  \<open>clss_size_resetUS0_st S =
  (let (stats, S) = extract_lcount_wl_heur S in
  let stats = clss_size_resetUS0 stats in
  let S = update_lcount_wl_heur stats S in S
  )\<close>
  by (auto simp: clss_size_resetUS0_st_def state_extractors
    split: isasat_int.splits)

sepref_def clss_size_resetUS0_st
  is \<open>RETURN o clss_size_resetUS0_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding clss_size_resetUS0_st_alt_def
  by sepref

lemma length_ll[def_pat_rules]: \<open>length_ll$xs$i \<equiv> op_list_list_llen$xs$i\<close>
  by (auto simp: op_list_list_llen_def length_ll_def)

sepref_def length_watchlist_impl
   is \<open>uncurry (RETURN oo length_watchlist)\<close>
  :: \<open>[uncurry (\<lambda>S L. nat_of_lit L < length S)]\<^sub>a watchlist_fast_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> sint64_nat_assn\<close>
  unfolding length_watchlist_def
  by sepref

definition length_ll_fs_heur_fast_code :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>length_ll_fs_heur_fast_code = (\<lambda>N C. read_watchlist_wl_heur_code (\<lambda>N. length_watchlist_impl N C) N)\<close>
global_interpretation watched_by_app: read_watchlist_param_adder where
  R = \<open>unat_lit_rel\<close> and
  f = \<open>\<lambda>C N. length_watchlist_impl N C\<close> and
  f' = \<open>\<lambda>C N. (RETURN oo length_watchlist) N C\<close> and
  x_assn = sint64_nat_assn and
  P = \<open>(\<lambda>L S. nat_of_lit L < length (S))\<close>
  rewrites
    \<open>(\<lambda>N C'. read_watchlist_wl_heur (\<lambda>N. (RETURN \<circ>\<circ> length_watchlist) N C') N) = RETURN oo length_ll_fs_heur\<close> and
    \<open>(\<lambda>N C. read_watchlist_wl_heur_code (\<lambda>N. length_watchlist_impl N C) N) = length_ll_fs_heur_fast_code\<close> and
    \<open>watched_by_app.XX.mop = mop_length_watched_by_int\<close>
  apply unfold_locales
  apply (rule length_watchlist_impl.refine)
  subgoal
     by (auto intro!: ext simp: length_ll_fs_heur_def read_all_wl_heur_def  get_watched_wl_heur_def length_watchlist_def
         length_ll_def
       split: isasat_int.splits)
  subgoal by (auto simp: length_ll_fs_heur_fast_code_def)
  subgoal
    by (auto simp: mop_length_watched_by_int_def read_all_param_adder_ops.mop_def read_all_wl_heur_def
      get_watched_wl_heur_def length_watchlist_def length_ll_def split: isasat_int.splits
      intro!: ext)
  done
thm watched_by_app.XX.mop_refine
lemmas [sepref_fr_rules] = watched_by_app.refine watched_by_app.XX.mop_refine
lemmas [unfolded inline_direct_return_node_case, llvm_code] =
  length_ll_fs_heur_fast_code_def[unfolded read_all_wl_heur_code_def]


experiment
begin
export_llvm opts_reduction_st_fast_code opts_restart_st_fast_code opts_unbounded_mode_st_fast_code
  opts_minimum_between_restart_st_fast_code mop_arena_status_st_impl full_arena_length_st_impl
  get_global_conflict_count_impl get_count_max_lvls_heur_impl clss_size_resetUS0_st
end


end
