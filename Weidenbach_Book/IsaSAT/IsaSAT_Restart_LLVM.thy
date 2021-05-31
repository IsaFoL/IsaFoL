theory IsaSAT_Restart_LLVM
imports IsaSAT_Restart IsaSAT_Restart_Heuristics_LLVM IsaSAT_Garbage_Collect_LLVM
  IsaSAT_Other_LLVM IsaSAT_Propagate_Conflict_LLVM
begin

sepref_register mark_to_delete_clauses_wl_D_heur

sepref_def MINIMUM_DELETION_LBD_impl
  is \<open>uncurry0 (RETURN MINIMUM_DELETION_LBD)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding MINIMUM_DELETION_LBD_def
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref


sepref_register delete_index_and_swap mop_mark_garbage_heur mop_mark_garbage_heur3
  mop_access_lit_in_clauses_heur


sepref_register cdcl_twl_full_restart_wl_prog_heur

sepref_def cdcl_twl_restart_wl_heur_fast_code
  is \<open>cdcl_twl_restart_wl_heur\<close>
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding cdcl_twl_restart_wl_heur_def
  supply [[goals_limit = 1]]
  by sepref

definition isasat_fast_bound where
  \<open>isasat_fast_bound = sint64_max - (uint32_max div 2 + MAX_HEADER_SIZE + 1)\<close>

lemma isasat_fast_bound_alt_def:
  \<open>isasat_fast_bound = 9223372034707292156\<close>
  \<open>uint64_max = 18446744073709551615\<close>
  by (auto simp: br_def isasat_fast_bound_def
     sint64_max_def uint32_max_def uint64_max_def)


lemma isasat_fast_alt_def: \<open>isasat_fast S = (length_clauses_heur S \<le> 9223372034707292156 \<and>
   clss_size_lcount (get_learned_count S) +
    clss_size_lcountUE (get_learned_count S) + clss_size_lcountUS (get_learned_count S) +
      clss_size_lcountU0 (get_learned_count S) < 18446744073709551615)\<close>
  by (cases S; auto simp: isasat_fast_def sint64_max_def uint32_max_def length_clauses_heur_def
    uint64_max_def learned_clss_count_def)

sepref_register isasat_fast


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
    cdcl_twl_restart_wl_heur_fast_code
    cdcl_twl_local_restart_wl_D_heur_fast_code
   get_conflict_wl_is_None_fast_code
end

end
