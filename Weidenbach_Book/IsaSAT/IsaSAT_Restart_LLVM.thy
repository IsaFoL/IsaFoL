theory IsaSAT_Restart_LLVM
  imports IsaSAT_Restart IsaSAT_Restart_Heuristics_LLVM IsaSAT_CDCL_LLVM
begin


sepref_register mark_to_delete_clauses_wl_D_heur

sepref_def MINIMUM_DELETION_LBD_impl
  is \<open>uncurry0 (RETURN MINIMUM_DELETION_LBD)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding MINIMUM_DELETION_LBD_def
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref


sepref_register delete_index_and_swap mop_mark_garbage_heur

sepref_def mark_to_delete_clauses_wl_D_heur_fast_impl
  is \<open>mark_to_delete_clauses_wl_D_heur\<close>
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding mark_to_delete_clauses_wl_D_heur_def
    access_vdom_at_def[symmetric] length_avdom_def[symmetric]
    get_the_propagation_reason_heur_def[symmetric]
    clause_is_learned_heur_def[symmetric]
    clause_lbd_heur_def[symmetric]
    access_length_heur_def[symmetric]
    short_circuit_conv mark_to_delete_clauses_wl_D_heur_is_Some_iff
    marked_as_used_st_def[symmetric] if_conn(4)
    fold_tuple_optimizations
    mop_arena_lbd_st_def[symmetric]
    mop_marked_as_used_st_def[symmetric]
    mop_arena_status_st_def[symmetric]
    mop_arena_length_st_def[symmetric]
  supply [[goals_limit = 1]] of_nat_snat[sepref_import_param]
    length_avdom_def[symmetric, simp] access_vdom_at_def[simp]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_register cdcl_twl_full_restart_wl_prog_heur

sepref_def cdcl_twl_full_restart_wl_prog_heur_fast_code
  is \<open>cdcl_twl_full_restart_wl_prog_heur\<close>
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding cdcl_twl_full_restart_wl_prog_heur_def
  supply [[goals_limit = 1]]
  by sepref

sepref_def cdcl_twl_restart_wl_heur_fast_code
  is \<open>cdcl_twl_restart_wl_heur\<close>
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding cdcl_twl_restart_wl_heur_def
  supply [[goals_limit = 1]]
  by sepref


sepref_def cdcl_twl_full_restart_wl_D_GC_heur_prog_fast_code
  is \<open>cdcl_twl_full_restart_wl_D_GC_heur_prog\<close>
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit = 1]]
  unfolding cdcl_twl_full_restart_wl_D_GC_heur_prog_def
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref

sepref_register restart_required_heur cdcl_twl_restart_wl_heur

sepref_def restart_prog_wl_D_heur_fast_code
  is \<open>uncurry2 (restart_prog_wl_D_heur)\<close>
  :: \<open>[\<lambda>((S, n), _). length (get_clauses_wl_heur S) \<le> sint64_max \<and> n < uint64_max]\<^sub>a
      isasat_bounded_assn\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k \<rightarrow> isasat_bounded_assn \<times>\<^sub>a uint64_nat_assn\<close>
  unfolding restart_prog_wl_D_heur_def
  supply [[goals_limit = 1]]
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

definition isasat_fast_bound where
  \<open>isasat_fast_bound = uint64_max - (uint32_max div 2 + 6)\<close>

lemma isasat_fast_bound_alt_def:
  \<open>isasat_fast_bound = 18446744071562067962\<close>
  by (auto simp: br_def isasat_fast_bound_def
     uint64_max_def uint32_max_def)


sepref_register isasat_fast
sepref_def isasat_fast_code
  is \<open>RETURN o isasat_fast\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding isasat_fast_alt_def isasat_fast_bound_def[symmetric]
  isasat_fast_bound_alt_def
  supply [[goals_limit = 1]]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_register cdcl_twl_stgy_restart_prog_bounded_wl_heur
sepref_def cdcl_twl_stgy_restart_prog_wl_heur_fast_code
  is \<open>cdcl_twl_stgy_restart_prog_bounded_wl_heur\<close>
  :: \<open>[\<lambda>S. isasat_fast S]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> bool1_assn \<times>\<^sub>a isasat_bounded_assn\<close>
  unfolding cdcl_twl_stgy_restart_prog_bounded_wl_heur_def
  supply [[goals_limit = 1]] isasat_fast_def[simp]
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref


experiment
begin
   export_llvm opts_reduction_st_fast_code
    opts_restart_st_fast_code
    get_conflict_count_since_last_restart_heur_fast_code
    get_fast_ema_heur_fast_code
    get_slow_ema_heur_fast_code
    get_learned_count_fast_code
    count_decided_st_heur_pol_fast
    upper_restart_bound_not_reached_fast_impl
    minimum_number_between_restarts_impl
    restart_required_heur_fast_code
    cdcl_twl_full_restart_wl_D_GC_heur_prog_fast_code
    cdcl_twl_restart_wl_heur_fast_code
    cdcl_twl_full_restart_wl_prog_heur_fast_code
    cdcl_twl_local_restart_wl_D_heur_fast_code


end

end
