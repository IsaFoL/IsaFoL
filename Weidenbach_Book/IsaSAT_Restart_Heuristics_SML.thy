theory IsaSAT_Restart_Heuristics_SML
  imports IsaSAT_Restart_Heuristics IsaSAT_Setup_SML
     IsaSAT_VMTF_SML
begin

lemma clause_score_ordering_hnr[sepref_fr_rules]:
  \<open>(uncurry (return oo clause_score_ordering), uncurry (RETURN oo clause_score_ordering)) \<in>
    (uint32_nat_assn *a uint32_nat_assn)\<^sup>k *\<^sub>a (uint32_nat_assn *a uint32_nat_assn)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: clause_score_ordering_def uint32_nat_rel_def br_def
      nat_of_uint32_less_iff nat_of_uint32_le_iff)


sepref_definition get_slow_ema_heur_fast_code
  is \<open>RETURN o get_slow_ema_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  unfolding get_slow_ema_heur_alt_def isasat_bounded_assn_def
  by sepref

sepref_definition get_slow_ema_heur_slow_code
  is \<open>RETURN o get_slow_ema_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  unfolding get_slow_ema_heur_alt_def isasat_unbounded_assn_def
  by sepref

declare get_slow_ema_heur_fast_code.refine[sepref_fr_rules]
  get_slow_ema_heur_slow_code.refine[sepref_fr_rules]


sepref_definition get_fast_ema_heur_fast_code
  is \<open>RETURN o get_fast_ema_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  unfolding get_fast_ema_heur_alt_def isasat_bounded_assn_def
  by sepref

sepref_definition get_fast_ema_heur_slow_code
  is \<open>RETURN o get_fast_ema_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  unfolding get_fast_ema_heur_alt_def isasat_unbounded_assn_def
  by sepref

declare get_fast_ema_heur_slow_code.refine[sepref_fr_rules]
  get_fast_ema_heur_fast_code.refine[sepref_fr_rules]


sepref_definition get_conflict_count_since_last_restart_heur_fast_code
  is \<open>RETURN o get_conflict_count_since_last_restart_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  unfolding get_counflict_count_heur_alt_def isasat_bounded_assn_def
  by sepref

sepref_definition get_conflict_count_since_last_restart_heur_slow_code
  is \<open>RETURN o get_conflict_count_since_last_restart_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  unfolding get_counflict_count_heur_alt_def isasat_unbounded_assn_def
  by sepref

declare get_conflict_count_since_last_restart_heur_fast_code.refine[sepref_fr_rules]
  get_conflict_count_since_last_restart_heur_slow_code.refine[sepref_fr_rules]


sepref_definition get_learned_count_fast_code
  is \<open>RETURN o get_learned_count\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  unfolding get_learned_count_alt_def isasat_bounded_assn_def
  by sepref

sepref_definition get_learned_count_slow_code
  is \<open>RETURN o get_learned_count\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  unfolding get_learned_count_alt_def isasat_unbounded_assn_def
  by sepref

declare get_learned_count_fast_code.refine[sepref_fr_rules]
  get_learned_count_slow_code.refine[sepref_fr_rules]


sepref_definition find_local_restart_target_level_code
  is \<open>uncurry find_local_restart_target_level_int\<close>
  :: \<open>trail_pol_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=1]] length_rev[simp del]
  unfolding find_local_restart_target_level_int_def find_local_restart_target_level_int_inv_def
  by sepref

sepref_definition find_local_restart_target_level_fast_code
  is \<open>uncurry find_local_restart_target_level_int\<close>
  :: \<open>trail_pol_fast_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=1]] length_rev[simp del]
  unfolding find_local_restart_target_level_int_def find_local_restart_target_level_int_inv_def
    length_uint32_nat_def
  by sepref

declare find_local_restart_target_level_code.refine[sepref_fr_rules]
  find_local_restart_target_level_fast_code.refine[sepref_fr_rules]


sepref_definition incr_restart_stat_slow_code
  is \<open>incr_restart_stat\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding incr_restart_stat_def isasat_unbounded_assn_def PR_CONST_def
  by sepref

sepref_register incr_restart_stat

sepref_definition incr_restart_stat_fast_code
  is \<open>incr_restart_stat\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding incr_restart_stat_def isasat_bounded_assn_def PR_CONST_def
  by sepref

declare incr_restart_stat_slow_code.refine[sepref_fr_rules]
  incr_restart_stat_fast_code.refine[sepref_fr_rules]


sepref_definition incr_lrestart_stat_slow_code
  is \<open>incr_lrestart_stat\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding incr_lrestart_stat_def isasat_unbounded_assn_def PR_CONST_def
  by sepref

sepref_register incr_lrestart_stat

sepref_definition incr_lrestart_stat_fast_code
  is \<open>incr_lrestart_stat\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding incr_lrestart_stat_def isasat_bounded_assn_def PR_CONST_def
  by sepref

declare incr_lrestart_stat_slow_code.refine[sepref_fr_rules]
  incr_lrestart_stat_fast_code.refine[sepref_fr_rules]


sepref_definition find_local_restart_target_level_st_code
  is \<open>find_local_restart_target_level_st\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=1]] length_rev[simp del]
  unfolding find_local_restart_target_level_st_alt_def isasat_unbounded_assn_def PR_CONST_def
  by sepref

sepref_definition find_local_restart_target_level_st_fast_code
  is \<open>find_local_restart_target_level_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=1]] length_rev[simp del]
  unfolding find_local_restart_target_level_st_alt_def isasat_bounded_assn_def PR_CONST_def
  by sepref

declare find_local_restart_target_level_st_code.refine[sepref_fr_rules]
  find_local_restart_target_level_st_fast_code.refine[sepref_fr_rules]


sepref_definition empty_Q_code
  is \<open>empty_Q\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding empty_Q_def isasat_unbounded_assn_def
  by sepref

sepref_definition empty_Q_fast_code
  is \<open>empty_Q\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding empty_Q_def isasat_bounded_assn_def
  by sepref

declare empty_Q_code.refine[sepref_fr_rules]
  empty_Q_fast_code.refine[sepref_fr_rules]

sepref_register cdcl_twl_local_restart_wl_D_heur
  empty_Q find_decomp_wl_st_int


sepref_definition cdcl_twl_local_restart_wl_D_heur_code
  is \<open>cdcl_twl_local_restart_wl_D_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  unfolding cdcl_twl_local_restart_wl_D_heur_def PR_CONST_def
  supply [[goals_limit = 1]]
  by sepref

sepref_definition cdcl_twl_local_restart_wl_D_heur_fast_code
  is \<open>cdcl_twl_local_restart_wl_D_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding cdcl_twl_local_restart_wl_D_heur_def PR_CONST_def
  supply [[goals_limit = 1]]
  by sepref

declare cdcl_twl_local_restart_wl_D_heur_code.refine[sepref_fr_rules]
  cdcl_twl_local_restart_wl_D_heur_fast_code.refine[sepref_fr_rules]


lemma five_uint64[sepref_fr_rules]:
 \<open>(uncurry0 (return five_uint64), uncurry0 (RETURN five_uint64))
  \<in>  unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  by sepref_to_hoare sep_auto

definition two_uint64 :: \<open>uint64\<close> where
  \<open>two_uint64 = 2\<close>

lemma two_uint64[sepref_fr_rules]:
 \<open>(uncurry0 (return two_uint64), uncurry0 (RETURN two_uint64))
  \<in>  unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  by sepref_to_hoare sep_auto


sepref_register upper_restart_bound_not_reached
sepref_definition upper_restart_bound_not_reached_impl
  is \<open>(RETURN o upper_restart_bound_not_reached)\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding upper_restart_bound_not_reached_def PR_CONST_def isasat_unbounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

sepref_definition upper_restart_bound_not_reached_fast_impl
  is \<open>(RETURN o upper_restart_bound_not_reached)\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding upper_restart_bound_not_reached_def PR_CONST_def isasat_bounded_assn_def
  apply (rewrite at \<open>\<hole> < _\<close> nat_of_uint64_conv_def[symmetric])
  supply [[goals_limit = 1]]
  by sepref

declare upper_restart_bound_not_reached_impl.refine[sepref_fr_rules]
  upper_restart_bound_not_reached_fast_impl.refine[sepref_fr_rules]


sepref_register lower_restart_bound_not_reached
sepref_definition lower_restart_bound_not_reached_impl
  is \<open>(RETURN o lower_restart_bound_not_reached)\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding lower_restart_bound_not_reached_def PR_CONST_def isasat_unbounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

sepref_definition lower_restart_bound_not_reached_fast_impl
  is \<open>(RETURN o lower_restart_bound_not_reached)\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding lower_restart_bound_not_reached_def PR_CONST_def isasat_bounded_assn_def
  supply [[goals_limit = 1]]
  apply (rewrite at \<open>\<hole> < _\<close> nat_of_uint64_conv_def[symmetric])
  by sepref

declare lower_restart_bound_not_reached_impl.refine[sepref_fr_rules]
  lower_restart_bound_not_reached_fast_impl.refine[sepref_fr_rules]


sepref_register clause_score_extract

sepref_definition (in -) clause_score_extract_code
  is \<open>uncurry (RETURN oo clause_score_extract)\<close>
  :: \<open>[uncurry valid_sort_clause_score_pre_at]\<^sub>a
      arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint32_nat_assn *a uint32_nat_assn\<close>
  supply uint32_max_uint32_nat_assn[sepref_fr_rules]
  unfolding clause_score_extract_def insert_sort_inner_def valid_sort_clause_score_pre_at_def
  by sepref

declare clause_score_extract_code.refine[sepref_fr_rules]
(*TODO Move*)
sepref_definition isa_get_clause_LBD_code2
  is \<open>uncurry isa_get_clause_LBD\<close>
  :: \<open>(arl64_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  unfolding isa_get_clause_LBD_def fast_minus_def[symmetric]
  by sepref

lemma isa_get_clause_LBD_code[sepref_fr_rules]:
  \<open>(uncurry isa_get_clause_LBD_code2, uncurry (RETURN \<circ>\<circ> get_clause_LBD))
     \<in> [uncurry get_clause_LBD_pre]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  using isa_get_clause_LBD_code2.refine[FCOMP isa_get_clause_LBD_get_clause_LBD[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl64_assn_comp update_lbd_pre_def)
sepref_definition isa_arena_act_code2
  is \<open>uncurry isa_arena_act\<close>
  :: \<open>(arl64_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  unfolding isa_arena_act_def ACTIVITY_SHIFT_def fast_minus_def[symmetric]
  by sepref

lemma isa_arena_act_code2[sepref_fr_rules]:
  \<open>(uncurry isa_arena_act_code2, uncurry (RETURN \<circ>\<circ> arena_act))
     \<in> [uncurry arena_act_pre]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  using isa_arena_act_code2.refine[FCOMP isa_arena_act_arena_act[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl64_assn_comp update_lbd_pre_def)

(*END Move*)
find_theorems arena_act
thm isa_arena_act_code
sepref_definition (in -) clause_score_extract_fast_code
  is \<open>uncurry (RETURN oo clause_score_extract)\<close>
  :: \<open>[uncurry valid_sort_clause_score_pre_at]\<^sub>a
      arena_fast_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint32_nat_assn *a uint32_nat_assn\<close>
  supply uint32_max_uint32_nat_assn[sepref_fr_rules]
  unfolding clause_score_extract_def insert_sort_inner_def valid_sort_clause_score_pre_at_def
  by sepref

declare clause_score_extract_fast_code.refine[sepref_fr_rules]


sepref_definition (in -) partition_main_clause_code
  is \<open>uncurry3 partition_main_clause\<close>
  :: \<open>[\<lambda>(((arena, i), j), vdom). valid_sort_clause_score_pre arena vdom]\<^sub>a
      arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a vdom_assn\<^sup>d \<rightarrow> vdom_assn *a nat_assn\<close>
  supply insort_inner_clauses_by_score_invI[intro]
    partition_main_inv_def[simp]
  unfolding partition_main_clause_def partition_between_ref_def
    partition_main_def WB_More_Refinement_List.swap_def IICF_List.swap_def[symmetric]
  by sepref

sepref_definition (in -) partition_main_clause_fast_code
  is \<open>uncurry3 partition_main_clause\<close>
  :: \<open>[\<lambda>(((arena, i), j), vdom). length vdom \<le> uint64_max \<and> valid_sort_clause_score_pre arena vdom]\<^sub>a
      arena_fast_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a vdom_assn\<^sup>d \<rightarrow> vdom_assn *a uint64_nat_assn\<close>
  supply insort_inner_clauses_by_score_invI[intro] [[goals_limit=1]]
    partition_main_inv_def[simp] mset_eq_length[dest]
  unfolding partition_main_clause_def partition_between_ref_def
    partition_main_def one_uint64_nat_def[symmetric]
    WB_More_Refinement_List.swap_def IICF_List.swap_def[symmetric]
  by sepref

sepref_register partition_main_clause_code
declare partition_main_clause_code.refine[sepref_fr_rules]
   partition_main_clause_fast_code.refine[sepref_fr_rules]


sepref_definition (in -) partition_clause_code
  is \<open>uncurry3 partition_clause\<close>
  :: \<open>[\<lambda>(((arena, i), j), vdom). valid_sort_clause_score_pre arena vdom]\<^sub>a
      arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a vdom_assn\<^sup>d \<rightarrow> vdom_assn *a nat_assn\<close>
  supply insort_inner_clauses_by_score_invI[intro] valid_sort_clause_score_pre_swap[
    unfolded WB_More_Refinement_List.swap_def IICF_List.swap_def[symmetric], intro]
  unfolding partition_clause_def partition_between_ref_def
    choose_pivot3_def partition_main_clause_def[symmetric]
    WB_More_Refinement_List.swap_def IICF_List.swap_def[symmetric]
  by sepref

lemma div2_hnr[sepref_fr_rules]: \<open>(return o (\<lambda>n. n >> 1), RETURN o div2) \<in> uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: div2_def uint64_nat_rel_def br_def nat_of_uint64_shiftl nat_shiftr_div2)

sepref_definition (in -) partition_clause_fast_code
  is \<open>uncurry3 partition_clause\<close>
  :: \<open>[\<lambda>(((arena, i), j), vdom). length vdom \<le> uint64_max \<and> valid_sort_clause_score_pre arena vdom]\<^sub>a
      arena_fast_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a vdom_assn\<^sup>d \<rightarrow> vdom_assn *a uint64_nat_assn\<close>
  supply insort_inner_clauses_by_score_invI[intro] valid_sort_clause_score_pre_swap[
    unfolded WB_More_Refinement_List.swap_def IICF_List.swap_def[symmetric], intro] mset_eq_length[dest]
  unfolding partition_clause_def partition_between_ref_def div2_def[symmetric]
    choose_pivot3_def partition_main_clause_def[symmetric]
    WB_More_Refinement_List.swap_def IICF_List.swap_def[symmetric]
  by sepref


declare partition_clause_code.refine[sepref_fr_rules]
  partition_clause_fast_code.refine[sepref_fr_rules]

sepref_definition (in -) sort_clauses_by_score_code
  is \<open>uncurry quicksort_clauses_by_score\<close>
  :: \<open>[uncurry valid_sort_clause_score_pre]\<^sub>a
      arena_assn\<^sup>k *\<^sub>a vdom_assn\<^sup>d \<rightarrow> vdom_assn\<close>
  supply sort_clauses_by_score_invI[intro]
  unfolding insert_sort_def
    quicksort_clauses_by_score_def
    full_quicksort_ref_def
    quicksort_ref_def
    partition_clause_def[symmetric]
    List.null_def
  by sepref


lemma minus_uint64_safe:
   \<open>(uncurry (return oo safe_minus), uncurry (RETURN oo (-))) \<in> uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: safe_minus_def uint64_nat_rel_def br_def nat_of_uint64_le_iff nat_of_uint64_notle_minus)


sepref_definition (in -) sort_clauses_by_score_fast_code
  is \<open>uncurry quicksort_clauses_by_score\<close>
  :: \<open>[\<lambda>(arena, vdom). length vdom \<le> uint64_max \<and> valid_sort_clause_score_pre arena vdom]\<^sub>a
      arena_fast_assn\<^sup>k *\<^sub>a vdom_assn\<^sup>d \<rightarrow> vdom_assn\<close>
  supply sort_clauses_by_score_invI[intro] [[goals_limit=1]] mset_eq_length[dest] minus_uint64_safe[sepref_fr_rules]
  unfolding insert_sort_def
    quicksort_clauses_by_score_def
    full_quicksort_ref_def
    quicksort_ref_def length_uint64_nat_def[symmetric]
    partition_clause_def[symmetric] one_uint64_nat_def[symmetric]
    List.null_def zero_uint64_nat_def[symmetric]
  by sepref


sepref_register remove_deleted_clauses_from_avdom
sepref_definition remove_deleted_clauses_from_avdom_fast_code
  is \<open>uncurry isa_remove_deleted_clauses_from_avdom\<close>
  :: \<open>arena_fast_assn\<^sup>k *\<^sub>a vdom_assn\<^sup>d \<rightarrow>\<^sub>a vdom_assn\<close>
  unfolding isa_remove_deleted_clauses_from_avdom_def swap_def[symmetric]
    WB_More_Refinement_List.swap_def
  by sepref


sepref_definition remove_deleted_clauses_from_avdom_code
  is \<open>uncurry isa_remove_deleted_clauses_from_avdom\<close>
  :: \<open>arena_assn\<^sup>k *\<^sub>a vdom_assn\<^sup>d \<rightarrow>\<^sub>a vdom_assn\<close>
  unfolding isa_remove_deleted_clauses_from_avdom_def swap_def[symmetric]
    WB_More_Refinement_List.swap_def
  by sepref

declare remove_deleted_clauses_from_avdom_fast_code.refine[sepref_fr_rules]
   remove_deleted_clauses_from_avdom_code.refine[sepref_fr_rules]

sepref_definition sort_vdom_heur_code
  is \<open>sort_vdom_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply sort_clauses_by_score_invI[intro] sort_clauses_by_score_code.refine[sepref_fr_rules]
  unfolding sort_vdom_heur_def isasat_unbounded_assn_def
  by sepref

sepref_definition sort_vdom_heur_fast_code
  is \<open>sort_vdom_heur\<close>
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> uint64_max]\<^sub>aisasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply sort_clauses_by_score_invI[intro] sort_clauses_by_score_fast_code.refine[sepref_fr_rules]
    [[goals_limit=1]]
  unfolding sort_vdom_heur_def isasat_bounded_assn_def
  by sepref

declare sort_vdom_heur_code.refine[sepref_fr_rules]
 sort_vdom_heur_fast_code.refine[sepref_fr_rules]


sepref_definition opts_restart_st_code
  is \<open>RETURN o opts_restart_st\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding opts_restart_st_def isasat_unbounded_assn_def
  by sepref

sepref_definition opts_restart_st_fast_code
  is \<open>RETURN o opts_restart_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding opts_restart_st_def isasat_bounded_assn_def
  by sepref

declare opts_restart_st_code.refine[sepref_fr_rules]
  opts_restart_st_fast_code.refine[sepref_fr_rules]


sepref_definition opts_reduction_st_code
  is \<open>RETURN o opts_reduction_st\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding opts_reduction_st_def isasat_unbounded_assn_def
  by sepref

sepref_definition opts_reduction_st_fast_code
  is \<open>RETURN o opts_reduction_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding opts_reduction_st_def isasat_bounded_assn_def
  by sepref

declare opts_reduction_st_code.refine[sepref_fr_rules]
  opts_reduction_st_fast_code.refine[sepref_fr_rules]

sepref_register opts_reduction_st opts_restart_st


sepref_register max_restart_decision_lvl

lemma minimum_number_between_restarts[sepref_fr_rules]:
 \<open>(uncurry0 (return minimum_number_between_restarts), uncurry0 (RETURN minimum_number_between_restarts))
  \<in>  unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  by sepref_to_hoare sep_auto

lemma max_restart_decision_lvl_code_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return max_restart_decision_lvl_code), uncurry0 (RETURN max_restart_decision_lvl)) \<in>
    unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: br_def uint32_nat_rel_def max_restart_decision_lvl_def
    max_restart_decision_lvl_code_def)

lemma [sepref_fr_rules]:
  \<open>(uncurry0 (return GC_EVERY), uncurry0 (RETURN GC_EVERY)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  by sepref_to_hoare (sep_auto simp: GC_EVERY_def)

lemma (in -) MINIMUM_DELETION_LBD_hnr[sepref_fr_rules]:
 \<open>(uncurry0 (return 3), uncurry0 (RETURN MINIMUM_DELETION_LBD)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: MINIMUM_DELETION_LBD_def uint32_nat_rel_def br_def)


sepref_definition restart_required_heur_fast_code
  is \<open>uncurry restart_required_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply [[goals_limit=1]]
  shiftr_uint64[sepref_fr_rules]
  unfolding restart_required_heur_def
  apply (rewrite at \<open>let _ = (\<hole> > _) in _\<close> nat_of_uint64_conv_def[symmetric])
  by sepref

sepref_definition restart_required_heur_slow_code
  is \<open>uncurry restart_required_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply [[goals_limit=1]]
  shiftr_uint64[sepref_fr_rules]
  unfolding restart_required_heur_def
  by sepref

declare restart_required_heur_fast_code.refine[sepref_fr_rules]
  restart_required_heur_slow_code.refine[sepref_fr_rules]


sepref_definition get_reductions_count_fast_code
  is \<open>RETURN o get_reductions_count\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  unfolding get_reduction_count_alt_def isasat_bounded_assn_def
  by sepref

sepref_definition get_reductions_count_code
  is \<open>RETURN o get_reductions_count\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  unfolding get_reduction_count_alt_def isasat_unbounded_assn_def
  by sepref

sepref_register get_reductions_count
declare get_reductions_count_fast_code.refine[sepref_fr_rules]
declare get_reductions_count_code.refine[sepref_fr_rules]


sepref_definition GC_required_heur_fast_code
  is \<open>uncurry GC_required_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply [[goals_limit=1]]
    op_eq_uint64[sepref_fr_rules]
  unfolding GC_required_heur_def
  by sepref

sepref_definition GC_required_heur_slow_code
  is \<open>uncurry GC_required_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply [[goals_limit=1]]
    op_eq_uint64[sepref_fr_rules]
  unfolding GC_required_heur_def
  by sepref

declare GC_required_heur_fast_code.refine[sepref_fr_rules]
  GC_required_heur_slow_code.refine[sepref_fr_rules]



sepref_register isa_trail_nth

sepref_register isasat_trail_nth_st

sepref_definition isasat_trail_nth_st_code
  is \<open>uncurry isasat_trail_nth_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a unat_lit_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_trail_nth_st_alt_def isasat_bounded_assn_def
  by sepref


sepref_definition isasat_trail_nth_st_slow_code
  is \<open>uncurry isasat_trail_nth_st\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a unat_lit_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_trail_nth_st_alt_def isasat_unbounded_assn_def
  by sepref

declare isasat_trail_nth_st_code.refine[sepref_fr_rules]
  isasat_trail_nth_st_slow_code.refine[sepref_fr_rules]


sepref_register get_the_propagation_reason_pol_st

sepref_definition get_the_propagation_reason_pol_st_code
  is \<open>uncurry get_the_propagation_reason_pol_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a option_assn uint64_nat_assn\<close>
  supply [[goals_limit=1]]
  unfolding get_the_propagation_reason_pol_st_alt_def isasat_bounded_assn_def
  by sepref


sepref_definition get_the_propagation_reason_pol_st_slow_code
  is \<open>uncurry get_the_propagation_reason_pol_st\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a option_assn nat_assn\<close>
  supply [[goals_limit=1]]
  unfolding get_the_propagation_reason_pol_st_alt_def isasat_unbounded_assn_def
  by sepref

declare get_the_propagation_reason_pol_st_code.refine[sepref_fr_rules]
  get_the_propagation_reason_pol_st_slow_code.refine[sepref_fr_rules]

sepref_register isasat_replace_annot_in_trail
sepref_definition isasat_replace_annot_in_trail_code
  is \<open>uncurry2 isasat_replace_annot_in_trail\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a (uint64_nat_assn)\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_replace_annot_in_trail_def isasat_bounded_assn_def
    zero_uint64_nat_def[symmetric]
  by sepref


sepref_definition isasat_replace_annot_in_trail_slow_code
  is \<open>uncurry2 isasat_replace_annot_in_trail\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a (nat_assn)\<^sup>k *\<^sub>a isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_replace_annot_in_trail_def isasat_unbounded_assn_def
  by sepref


(*TODO Move*)
sepref_definition mark_garbage_fast_code
  is \<open>uncurry mark_garbage\<close>
  :: \<open>(arl64_assn uint32_assn)\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a arl64_assn uint32_assn\<close>
  supply STATUS_SHIFT_hnr[sepref_fr_rules]
  unfolding mark_garbage_def fast_minus_def[symmetric]
  by sepref

lemma mark_garbage_fast_hnr[sepref_fr_rules]:
  \<open>(uncurry mark_garbage_fast_code, uncurry (RETURN oo extra_information_mark_to_delete))
  \<in> [mark_garbage_pre]\<^sub>a  arena_fast_assn\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> arena_fast_assn\<close>
  using mark_garbage_fast_code.refine[FCOMP isa_mark_garbage[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl64_assn_comp update_lbd_pre_def)

context
  notes [fcomp_norm_unfold] = arl64_assn_def[symmetric] arl64_assn_comp'
  notes [intro!] = hfrefI hn_refineI[THEN hn_refine_preI]
  notes [simp] = pure_def hn_ctxt_def invalid_assn_def
begin
definition arl64_set_nat :: "'a::heap array_list64 \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a array_list64 Heap" where
  "arl64_set_nat \<equiv> \<lambda>(a,n) i x. do { a \<leftarrow> Array.upd i x a; return (a,n)}"

  lemma arl64_set_hnr_aux: "(uncurry2 arl64_set_nat,uncurry2 (RETURN ooo op_list_set)) \<in> [\<lambda>((l,i),_). i<length l]\<^sub>a (is_array_list64\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a id_assn\<^sup>k) \<rightarrow> is_array_list64"
    by (sep_auto simp: arl64_set_nat_def is_array_list64_def)
  sepref_decl_impl arl64_set_nat: arl64_set_hnr_aux .

end

sepref_definition mark_garbage_fast_code2
  is \<open>uncurry mark_garbage\<close>
  :: \<open>(arl64_assn uint32_assn)\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a arl64_assn uint32_assn\<close>
  unfolding STATUS_SHIFT_def
  unfolding mark_garbage_def fast_minus_def[symmetric]
  by sepref

lemma mark_garbage_fast_hnr2[sepref_fr_rules]:
  \<open>(uncurry mark_garbage_fast_code2, uncurry (RETURN oo extra_information_mark_to_delete))
  \<in> [mark_garbage_pre]\<^sub>a  arena_fast_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow> arena_fast_assn\<close>
  using mark_garbage_fast_code2.refine[FCOMP isa_mark_garbage[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl64_assn_comp)
(*END Move*)

sepref_register mark_garbage_heur2
sepref_definition mark_garbage_heur2_code
  is \<open>uncurry mark_garbage_heur2\<close>
  :: \<open>[\<lambda>(C, S). mark_garbage_pre (get_clauses_wl_heur S, C) \<and> arena_is_valid_clause_vdom (get_clauses_wl_heur S) C]\<^sub>a
     uint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding mark_garbage_heur2_def isasat_bounded_assn_def
    zero_uint64_nat_def[symmetric] one_uint64_nat_def[symmetric]
  by sepref

sepref_definition mark_garbage_heur2_slow_code
  is \<open>uncurry mark_garbage_heur2\<close>
  :: \<open>[\<lambda>(C, S). mark_garbage_pre (get_clauses_wl_heur S, C) \<and> arena_is_valid_clause_vdom (get_clauses_wl_heur S) C]\<^sub>a
     nat_assn\<^sup>k *\<^sub>a isasat_unbounded_assn\<^sup>d \<rightarrow> isasat_unbounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding mark_garbage_heur2_def isasat_unbounded_assn_def
    zero_uint64_nat_def[symmetric]
  by sepref

declare isasat_replace_annot_in_trail_code.refine[sepref_fr_rules]
  isasat_replace_annot_in_trail_slow_code.refine[sepref_fr_rules]
  mark_garbage_heur2_code.refine[sepref_fr_rules]
  mark_garbage_heur2_slow_code.refine[sepref_fr_rules]

sepref_register remove_one_annot_true_clause_one_imp_wl_D_heur

sepref_definition remove_one_annot_true_clause_one_imp_wl_D_heur_code
  is \<open>uncurry remove_one_annot_true_clause_one_imp_wl_D_heur\<close>
  :: \<open>uint32_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a uint32_nat_assn *a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding remove_one_annot_true_clause_one_imp_wl_D_heur_def zero_uint64_nat_def[symmetric]
    one_uint32_nat_def[symmetric]
    isasat_trail_nth_st_def[symmetric] get_the_propagation_reason_pol_st_def[symmetric]
  by sepref


sepref_definition remove_one_annot_true_clause_one_imp_wl_D_heur_slow_code
  is \<open>uncurry remove_one_annot_true_clause_one_imp_wl_D_heur\<close>
  :: \<open>uint32_nat_assn\<^sup>k *\<^sub>a isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a uint32_nat_assn *a isasat_unbounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding remove_one_annot_true_clause_one_imp_wl_D_heur_def
    isasat_trail_nth_st_def[symmetric] get_the_propagation_reason_pol_st_def[symmetric]
    one_uint32_nat_def[symmetric]
  by sepref

declare remove_one_annot_true_clause_one_imp_wl_D_heur_slow_code.refine[sepref_fr_rules]
  remove_one_annot_true_clause_one_imp_wl_D_heur_code.refine[sepref_fr_rules]

sepref_register isasat_length_trail_st

sepref_definition isasat_length_trail_st_code
  is \<open>RETURN o isasat_length_trail_st\<close>
  :: \<open>[isa_length_trail_pre o get_trail_wl_heur]\<^sub>a isasat_bounded_assn\<^sup>k  \<rightarrow> uint32_nat_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_length_trail_st_alt_def isasat_bounded_assn_def
  by sepref


sepref_definition isasat_length_trail_st_slow_code
  is \<open>RETURN o  isasat_length_trail_st\<close>
  :: \<open>[isa_length_trail_pre o get_trail_wl_heur]\<^sub>a isasat_unbounded_assn\<^sup>k  \<rightarrow> uint32_nat_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_length_trail_st_alt_def isasat_unbounded_assn_def
  by sepref

declare isasat_length_trail_st_slow_code.refine[sepref_fr_rules]
  isasat_length_trail_st_code.refine[sepref_fr_rules]


sepref_register get_pos_of_level_in_trail_imp_st

sepref_definition get_pos_of_level_in_trail_imp_st_code
  is \<open>uncurry get_pos_of_level_in_trail_imp_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k  \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=1]]
  unfolding get_pos_of_level_in_trail_imp_alt_def isasat_bounded_assn_def
  by sepref


sepref_definition get_pos_of_level_in_trail_imp_st_slow_code
  is \<open>uncurry get_pos_of_level_in_trail_imp_st\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k  \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=1]]
  unfolding get_pos_of_level_in_trail_imp_alt_def isasat_unbounded_assn_def
  by sepref

declare get_pos_of_level_in_trail_imp_st_slow_code.refine[sepref_fr_rules]
  get_pos_of_level_in_trail_imp_st_code.refine[sepref_fr_rules]

sepref_register remove_one_annot_true_clause_imp_wl_D_heur

sepref_definition remove_one_annot_true_clause_imp_wl_D_heur_code
  is \<open>remove_one_annot_true_clause_imp_wl_D_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding remove_one_annot_true_clause_imp_wl_D_heur_def zero_uint32_nat_def[symmetric]
    isasat_length_trail_st_def[symmetric] get_pos_of_level_in_trail_imp_st_def[symmetric]
  by sepref

sepref_definition remove_one_annot_true_clause_imp_wl_D_heur_slow_code
  is \<open>remove_one_annot_true_clause_imp_wl_D_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding remove_one_annot_true_clause_imp_wl_D_heur_def zero_uint32_nat_def[symmetric]
    isasat_length_trail_st_def[symmetric] get_pos_of_level_in_trail_imp_st_def[symmetric]
  by sepref

declare remove_one_annot_true_clause_imp_wl_D_heur_code.refine[sepref_fr_rules]
   remove_one_annot_true_clause_imp_wl_D_heur_slow_code.refine[sepref_fr_rules]

declare fm_mv_clause_to_new_arena_fast_code.refine[sepref_fr_rules]
sepref_definition isasat_GC_clauses_prog_copy_wl_entry_code
  is \<open>uncurry3 isasat_GC_clauses_prog_copy_wl_entry\<close>
  :: \<open>[\<lambda>(((N, _), _), _). length N \<le> uint64_max]\<^sub>a
     arena_fast_assn\<^sup>d *\<^sub>a watchlist_fast_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a
         (arena_fast_assn *a vdom_assn *a vdom_assn)\<^sup>d \<rightarrow>
     (arena_fast_assn *a (arena_fast_assn *a vdom_assn *a vdom_assn))\<close>
  supply [[goals_limit=1]] Pos_unat_lit_assn'[sepref_fr_rules] length_ll_def[simp] if_splits[split]
  unfolding isasat_GC_clauses_prog_copy_wl_entry_def nth_rll_def[symmetric]
    length_ll_def[symmetric] zero_uint64_nat_def[symmetric] one_uint64_nat_def[symmetric]
    four_uint64_nat_def[symmetric] five_uint64_nat_def[symmetric]
  apply (rewrite at \<open>let _ = length_ll _ \<hole> in _\<close> uint64_of_uint32_conv_def[symmetric])
  apply (rewrite at \<open>_ @ [\<hole>]\<close> nat_of_uint64_conv_def[symmetric])
  apply (rewrite at \<open>If _ (_ @ [\<hole>])\<close> nat_of_uint64_conv_def[symmetric])
  by sepref

sepref_definition isasat_GC_clauses_prog_copy_wl_entry_slow_code
  is \<open>uncurry3 isasat_GC_clauses_prog_copy_wl_entry\<close>
  :: \<open>arena_assn\<^sup>d *\<^sub>a watchlist_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a (arena_assn *a vdom_assn *a vdom_assn)\<^sup>d \<rightarrow>\<^sub>a
     (arena_assn *a (arena_assn *a vdom_assn *a vdom_assn))\<close>
  supply [[goals_limit=1]] Pos_unat_lit_assn'[sepref_fr_rules] length_ll_def[simp]
  unfolding isasat_GC_clauses_prog_copy_wl_entry_def nth_rll_def[symmetric]
    length_ll_def[symmetric]
  apply (rewrite at \<open>let _ = _ + (If (\<hole> < _) _ _) in _\<close> four_uint64_nat_def[symmetric])
  by sepref


sepref_register isasat_GC_clauses_prog_copy_wl_entry
declare isasat_GC_clauses_prog_copy_wl_entry_code.refine[sepref_fr_rules]
  isasat_GC_clauses_prog_copy_wl_entry_slow_code.refine[sepref_fr_rules]

lemma shorten_take_ll_0: \<open>shorten_take_ll L 0 W = W[L := []]\<close>
  by (auto simp: shorten_take_ll_def)

lemma length_shorten_take_ll[simp]: \<open>length (shorten_take_ll a j W) = length W\<close>
  by (auto simp: shorten_take_ll_def)

(*TODO remove conversion to nat*)
sepref_definition isasat_GC_clauses_prog_single_wl_code
  is \<open>uncurry3 isasat_GC_clauses_prog_single_wl\<close>
  :: \<open>[\<lambda>(((N, _), _), A). A \<le> uint32_max div 2 \<and> length N \<le> uint64_max]\<^sub>a
     arena_fast_assn\<^sup>d *\<^sub>a (arena_fast_assn *a vdom_assn *a vdom_assn)\<^sup>d *\<^sub>a watchlist_fast_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>
     (arena_fast_assn *a (arena_fast_assn *a vdom_assn *a vdom_assn) *a watchlist_fast_assn)\<close>
  supply [[goals_limit=1]] Pos_unat_lit_assn'[sepref_fr_rules]
  unfolding isasat_GC_clauses_prog_single_wl_def zero_uint64_nat_def[symmetric]
    shorten_take_ll_0[symmetric]
  apply (rewrite at \<open>let _ = shorten_take_ll \<hole> _ _ in _\<close> nat_of_uint32_conv_def[symmetric])
  apply (rewrite at \<open>let _ = shorten_take_ll \<hole> _ _ in RETURN _\<close> nat_of_uint32_conv_def[symmetric])
  by sepref


sepref_definition isasat_GC_clauses_prog_single_wl_slow_code
  is \<open>uncurry3 isasat_GC_clauses_prog_single_wl\<close>
  :: \<open>[\<lambda>(((_, _), _), A). A \<le> uint32_max div 2]\<^sub>a
     arena_assn\<^sup>d *\<^sub>a (arena_assn *a vdom_assn *a vdom_assn)\<^sup>d *\<^sub>a watchlist_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>
     (arena_assn *a (arena_assn *a vdom_assn *a vdom_assn) *a watchlist_assn)\<close>
  supply [[goals_limit=1]] Pos_unat_lit_assn'[sepref_fr_rules]
  unfolding isasat_GC_clauses_prog_single_wl_def
    shorten_take_ll_0[symmetric]
  by sepref

declare isasat_GC_clauses_prog_single_wl_code.refine[sepref_fr_rules]
   isasat_GC_clauses_prog_single_wl_slow_code.refine[sepref_fr_rules]

definition isasat_GC_clauses_prog_wl2' where
  \<open>isasat_GC_clauses_prog_wl2' ns fst' = (isasat_GC_clauses_prog_wl2 (ns, fst'))\<close>

sepref_register isasat_GC_clauses_prog_wl2
sepref_definition isasat_GC_clauses_prog_wl2_code
  is \<open>uncurry2 isasat_GC_clauses_prog_wl2'\<close>
  :: \<open>[\<lambda>((_, _), (N, _)). length N \<le> uint64_max]\<^sub>a
     (array_assn vmtf_node_assn)\<^sup>k *\<^sub>a (option_assn uint32_nat_assn)\<^sup>k *\<^sub>a 
     (arena_fast_assn *a (arena_fast_assn *a vdom_assn *a vdom_assn) *a watchlist_fast_assn)\<^sup>d \<rightarrow>
     (arena_fast_assn *a (arena_fast_assn *a vdom_assn *a vdom_assn) *a watchlist_fast_assn)\<close>
  supply [[goals_limit=1]]
  unfolding isasat_GC_clauses_prog_wl2_def isasat_GC_clauses_prog_wl2'_def
  by sepref

sepref_definition isasat_GC_clauses_prog_wl2_slow_code
  is \<open>uncurry2 isasat_GC_clauses_prog_wl2'\<close>
  :: \<open>(array_assn vmtf_node_assn)\<^sup>k *\<^sub>a (option_assn uint32_nat_assn)\<^sup>k *\<^sub>a
     (arena_assn *a (arena_assn *a vdom_assn *a vdom_assn) *a watchlist_assn)\<^sup>d \<rightarrow>\<^sub>a
     (arena_assn *a (arena_assn *a vdom_assn *a vdom_assn) *a watchlist_assn)\<close>
  supply [[goals_limit=1]]
  unfolding isasat_GC_clauses_prog_wl2_def isasat_GC_clauses_prog_wl2'_def
  by sepref

declare isasat_GC_clauses_prog_wl2_code.refine[sepref_fr_rules]
   isasat_GC_clauses_prog_wl2_slow_code.refine[sepref_fr_rules]

(*TODO Move replace*)
lemma arl64_take[sepref_fr_rules]:
  \<open>(uncurry (return oo arl64_take), uncurry (RETURN oo take)) \<in>
    [\<lambda>(n, xs). n \<le> length xs]\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a (arl64_assn R)\<^sup>d \<rightarrow> arl64_assn R\<close>
  by (sepref_to_hoare)
    (sep_auto simp: arl64_assn_def arl64_take_def is_array_list64_def hr_comp_def
      uint64_nat_rel_def br_def list_rel_def list_all2_conv_all_nth)

sepref_register isasat_GC_clauses_prog_wl isasat_GC_clauses_prog_wl2' rewatch_heur_st
sepref_definition isasat_GC_clauses_prog_wl_code
  is \<open>isasat_GC_clauses_prog_wl\<close>
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> uint64_max]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_GC_clauses_prog_wl_def isasat_bounded_assn_def
     isasat_GC_clauses_prog_wl2'_def[symmetric]
  apply (rewrite in \<open>(_, _, _, _, _, take \<hole> _)\<close> zero_uint64_nat_def[symmetric])
  by sepref

sepref_definition isasat_GC_clauses_prog_wl_slow_code
  is \<open>isasat_GC_clauses_prog_wl\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_GC_clauses_prog_wl_def isasat_unbounded_assn_def
    IICF_Array_List.arl.fold_custom_empty isasat_GC_clauses_prog_wl2'_def[symmetric]
  by sepref

(*TODO Move*)
sepref_definition isa_arena_length_fast_code2
  is \<open>uncurry isa_arena_length\<close>
  :: \<open>(arl64_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  supply arena_el_assn_alt_def[symmetric, simp] sum_uint64_assn[sepref_fr_rules]
    minus_uint64_nat_assn[sepref_fr_rules]
  unfolding isa_arena_length_def SIZE_SHIFT_def fast_minus_def
  by sepref

lemma isa_arena_length_fast_code2_refine[sepref_fr_rules]:
  \<open>(uncurry isa_arena_length_fast_code2, uncurry (RETURN \<circ>\<circ> arena_length))
  \<in> [uncurry arena_is_valid_clause_idx]\<^sub>a
    arena_fast_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  using isa_arena_length_fast_code2.refine[FCOMP isa_arena_length_arena_length[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] uncurry_def list_rel_compp
  by (simp add: arl64_assn_comp)

sepref_definition rewatch_heur_st_code
  is \<open>rewatch_heur_st\<close>
  :: \<open>[\<lambda>S. rewatch_heur_st_pre S \<and> length (get_clauses_wl_heur S) \<le> uint64_max]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]] append_el_aa_uint32_hnr'[sepref_fr_rules] append_ll_def[simp]
  unfolding isasat_GC_clauses_prog_wl_def isasat_bounded_assn_def
    rewatch_heur_st_def rewatch_heur_def Let_def two_uint64_nat_def[symmetric]
    to_watcher_fast_def[symmetric] rewatch_heur_st_pre_def
  apply (rewrite at \<open>RETURN (append_ll (append_ll _ _ (to_watcher_fast \<hole> _ _)) _ _)\<close> uint64_of_nat_conv_def[symmetric])
  apply (rewrite at \<open>RETURN (append_ll (append_ll _ _ _) _ (to_watcher_fast \<hole> _ _))\<close> uint64_of_nat_conv_def[symmetric])
  apply (rewrite at \<open>to_watcher_fast \<hole>\<close> uint64_of_nat_conv_def[symmetric])
  by sepref

sepref_definition rewatch_heur_st_slow_code
  is \<open>rewatch_heur_st\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply [[goals_limit=1]] append_el_aa_uint32_hnr'[sepref_fr_rules]
  unfolding isasat_GC_clauses_prog_wl_def isasat_unbounded_assn_def
    rewatch_heur_st_def rewatch_heur_def Let_def two_uint64_nat_def[symmetric]
  by sepref

declare isasat_GC_clauses_prog_wl_code.refine[sepref_fr_rules]
 isasat_GC_clauses_prog_wl_slow_code.refine[sepref_fr_rules]
  rewatch_heur_st_slow_code.refine[sepref_fr_rules]
  rewatch_heur_st_code.refine[sepref_fr_rules]


sepref_register isasat_GC_clauses_wl_D

sepref_definition isasat_GC_clauses_wl_D_code
  is \<open>isasat_GC_clauses_wl_D\<close>
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> uint64_max]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]] isasat_GC_clauses_wl_D_rewatch_pre[intro!]
  unfolding isasat_GC_clauses_wl_D_def
  by sepref


sepref_definition isasat_GC_clauses_wl_D_slow_code
  is \<open>isasat_GC_clauses_wl_D\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_GC_clauses_wl_D_def
  by sepref

declare isasat_GC_clauses_wl_D_code.refine[sepref_fr_rules]
   isasat_GC_clauses_wl_D_slow_code.refine[sepref_fr_rules]

end