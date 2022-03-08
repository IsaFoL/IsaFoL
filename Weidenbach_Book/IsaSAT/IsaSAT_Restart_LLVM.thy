theory IsaSAT_Restart_LLVM
imports IsaSAT_Restart_Simp IsaSAT_Propagate_Conflict_LLVM IsaSAT_Restart_Heuristics_LLVM
begin
sepref_register update_all_phases

sepref_def update_all_phases_impl
  is \<open>update_all_phases\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding update_all_phases_def
  by sepref


sepref_register mark_to_delete_clauses_wl_D_heur


sepref_register delete_index_and_swap mop_mark_garbage_heur mop_mark_garbage_heur3
  mop_access_lit_in_clauses_heur

(*TODO deduplicate*)
lemma [def_pat_rules]: \<open>get_the_propagation_reason_heur \<equiv> get_the_propagation_reason_pol_st\<close>
proof -
  have \<open>get_the_propagation_reason_heur = get_the_propagation_reason_pol_st\<close>
    by (auto intro!: ext simp: get_the_propagation_reason_pol_st_def
      get_the_propagation_reason_heur_def)
  then show  \<open>get_the_propagation_reason_heur \<equiv> get_the_propagation_reason_pol_st\<close>
   by auto
qed 

sepref_def mark_to_delete_clauses_wl_D_heur_fast_impl
  is \<open>mark_to_delete_clauses_wl_D_heur\<close>
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding mark_to_delete_clauses_wl_D_heur_def
    access_tvdom_at_def[symmetric] length_tvdom_def[symmetric]
    get_the_propagation_reason_heur_def[symmetric]
    clause_is_learned_heur_def[symmetric]
    clause_lbd_heur_def[symmetric]
    access_length_heur_def[symmetric]
    mark_to_delete_clauses_wl_D_heur_is_Some_iff
    marked_as_used_st_def[symmetric] if_conn(4)
    fold_tuple_optimizations
    mop_arena_lbd_st_def[symmetric]
    mop_marked_as_used_st_def[symmetric]
    mop_arena_status_st_def[symmetric]
    mop_arena_length_st_def[symmetric]
  supply [[goals_limit = 1]] of_nat_snat[sepref_import_param]
      length_tvdom_def[symmetric, simp] access_tvdom_at_def[simp]
  apply (rewrite in \<open>let _ = \<hole> in _\<close> short_circuit_conv)+
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_def mark_to_delete_clauses_GC_wl_D_heur_heur_fast_impl
  is \<open>mark_to_delete_clauses_GC_wl_D_heur\<close>
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding mark_to_delete_clauses_GC_wl_D_heur_def
    access_tvdom_at_def[symmetric] length_tvdom_def[symmetric]
    get_the_propagation_reason_heur_def[symmetric]
    clause_is_learned_heur_def[symmetric]
    clause_lbd_heur_def[symmetric]
    access_length_heur_def[symmetric]
    mark_to_delete_clauses_wl_D_heur_is_Some_iff
    marked_as_used_st_def[symmetric] if_conn(4)
    fold_tuple_optimizations
    mop_arena_lbd_st_def[symmetric]
    mop_marked_as_used_st_def[symmetric]
    mop_arena_status_st_def[symmetric]
    mop_arena_length_st_def[symmetric]
  supply [[goals_limit = 1]] of_nat_snat[sepref_import_param]
      length_avdom_def[symmetric, simp] access_avdom_at_def[simp]
  apply (rewrite in \<open>let _ = \<hole> in _\<close> short_circuit_conv)+
  apply (annot_snat_const \<open>TYPE(64)\<close>)
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
      clss_size_lcountU0 (get_learned_count S)+
      clss_size_lcountUEk (get_learned_count S) < 18446744073709551615)\<close>
  by (cases S; auto simp: isasat_fast_def sint64_max_def uint32_max_def length_clauses_heur_def
    uint64_max_def learned_clss_count_def)

sepref_register isasat_fast

sepref_def isasat_fast_code
  is \<open>RETURN o isasat_fast\<close>
  :: \<open>[\<lambda>S. isasat_fast_relaxed S]\<^sub>a isasat_bounded_assn\<^sup>k \<rightarrow> bool1_assn\<close>
  unfolding isasat_fast_alt_def isasat_fast_relaxed_def
  apply (rewrite at \<open>_ < \<hole>\<close> unat_const_fold[where 'a=64])+
  unfolding all_count_learned[symmetric] clss_size_allcount_alt_def
  supply [[goals_limit = 1]]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

end
