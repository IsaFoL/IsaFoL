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

(*TODO Move*)
lemma mop_mark_garbage_heur3_alt_def:
  \<open>mop_mark_garbage_heur3 C i = (\<lambda>(M', N', D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
       vdom, avdom, lcount, opts, old_arena). do {
    ASSERT(mark_garbage_pre (get_clauses_wl_heur (M', N', D', j, W', vm, clvls, cach, lbd, outl,
       stats, heur, vdom, avdom, lcount, opts, old_arena), C) \<and> clss_size_lcount lcount \<ge> 1 \<and> i < length avdom);
    RETURN (M', extra_information_mark_to_delete N' C, D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
       vdom, delete_index_and_swap avdom i, clss_size_resetUS (clss_size_decr_lcount lcount), opts, old_arena)
   })\<close>
  unfolding mop_mark_garbage_heur3_def mark_garbage_heur3_def
  by (auto intro!: ext)

sepref_def mop_mark_garbage_heur_impl
  is \<open>uncurry2 mop_mark_garbage_heur3\<close>
  :: \<open>[\<lambda>((C, i), S). length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a
      sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding mop_mark_garbage_heur3_alt_def
    clause_not_marked_to_delete_heur_pre_def prod.case isasat_bounded_assn_def
  by sepref

sepref_def mark_to_delete_clauses_wl_D_heur_fast_impl
  is \<open>mark_to_delete_clauses_wl_D_heur\<close>
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding mark_to_delete_clauses_wl_D_heur_def
    access_vdom_at_def[symmetric] length_avdom_def[symmetric]
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
      length_avdom_def[symmetric, simp] access_vdom_at_def[simp]
  apply (rewrite in \<open>let _ = \<hole> in _\<close> short_circuit_conv)+
  apply (rewrite at \<open>_ > \<hole>\<close> unat_const_fold[where 'a=2])
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
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max \<and> learned_clss_count S \<le> uint64_max]\<^sub>a
     isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit = 1]]
  unfolding cdcl_twl_full_restart_wl_D_GC_heur_prog_def
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref

sepref_register restart_required_heur cdcl_twl_restart_wl_heur

sepref_def restart_prog_wl_D_heur_fast_code
  is \<open>uncurry4 (restart_prog_wl_D_heur)\<close>
  :: \<open>[\<lambda>((((S, _), _), n), _). isasat_fast_relaxed2 S n]\<^sub>a
      isasat_bounded_assn\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k  *\<^sub>a uint64_nat_assn\<^sup>k  *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a
        bool1_assn\<^sup>k \<rightarrow> isasat_bounded_assn \<times>\<^sub>a uint64_nat_assn \<times>\<^sub>a uint64_nat_assn \<times>\<^sub>a uint64_nat_assn\<close>
  unfolding restart_prog_wl_D_heur_def isasat_fast_relaxed_def isasat_fast_relaxed2_def
  supply [[goals_limit = 1]]
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

definition isasat_fast_bound where
  \<open>isasat_fast_bound = sint64_max - (uint32_max div 2 + 3 + 1)\<close>

lemma isasat_fast_bound_alt_def:
  \<open>isasat_fast_bound = 9223372034707292156\<close>
  \<open>uint64_max = 18446744073709551615\<close>
  by (auto simp: br_def isasat_fast_bound_def
     sint64_max_def uint32_max_def uint64_max_def)


lemma isasat_fast_alt_def: \<open>isasat_fast S = (length_clauses_heur S \<le> 9223372034707292156 \<and>
   clss_size_lcount (get_learned_count S) +
    clss_size_lcountUE (get_learned_count S) + clss_size_lcountUS (get_learned_count S) < 18446744073709551615)\<close>
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

lemma cdcl_twl_stgy_restart_prog_bounded_wl_heurI1:
  assumes
    \<open>isasat_fast a1'b\<close>
    \<open>learned_clss_count a2'e \<le> Suc (learned_clss_count a1'b)\<close>
  shows \<open>learned_clss_count a2'e \<le> uint64_max\<close>
  using assms
  by (auto simp: isasat_fast_def)

lemma cdcl_twl_stgy_restart_prog_bounded_wl_heurI2:
  \<open>isasat_fast x \<Longrightarrow> learned_clss_count x \<le> uint64_max\<close>
  by (auto simp: isasat_fast_def)


lemma cdcl_twl_stgy_restart_prog_bounded_wl_heurI3:
  assumes
    \<open>isasat_fast S\<close>
    \<open>length (get_clauses_wl_heur T) \<le> length (get_clauses_wl_heur S)\<close>
    \<open>learned_clss_count T \<le> (learned_clss_count S)\<close>
  shows \<open>isasat_fast T\<close>
  using assms
  by (auto simp: isasat_fast_def)

sepref_register cdcl_twl_stgy_restart_prog_bounded_wl_heur
sepref_def cdcl_twl_stgy_restart_prog_wl_heur_fast_code
  is \<open>cdcl_twl_stgy_restart_prog_bounded_wl_heur\<close>
  :: \<open>[\<lambda>S. isasat_fast S]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> bool1_assn \<times>\<^sub>a isasat_bounded_assn\<close>
  unfolding cdcl_twl_stgy_restart_prog_bounded_wl_heur_def
  supply [[goals_limit = 1]] isasat_fast_countD[dest]
  supply [intro] = cdcl_twl_stgy_restart_prog_bounded_wl_heurI2
  (* supply [dest] = cdcl_twl_stgy_restart_prog_bounded_wl_heurI1
   *   cdcl_twl_stgy_restart_prog_bounded_wl_heurI2 
    * supply [intro] = cdcl_twl_stgy_restart_prog_bounded_wl_heurI3 *)
  supply [sepref_bounds_simps del] = uint32_max_def sint32_max_def uint64_max_def sint64_max_def
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref


(* experiment
 * begin
 *    export_llvm opts_reduction_st_fast_code
 *     opts_restart_st_fast_code
 *     get_conflict_count_since_last_restart_heur_fast_code
 *     get_fast_ema_heur_fast_code
 *     get_slow_ema_heur_fast_code
 *     get_learned_count_fast_code
 *     count_decided_st_heur_pol_fast
 *     upper_restart_bound_not_reached_fast_impl
 *     minimum_number_between_restarts_impl
 *     restart_required_heur_fast_code
 *     cdcl_twl_full_restart_wl_D_GC_heur_prog_fast_code
 *     cdcl_twl_restart_wl_heur_fast_code
 *     cdcl_twl_full_restart_wl_prog_heur_fast_code
 *     cdcl_twl_local_restart_wl_D_heur_fast_code
 * 
 * 
 * end *)
term array_assn
end
