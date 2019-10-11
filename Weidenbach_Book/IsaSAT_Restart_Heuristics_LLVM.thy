theory IsaSAT_Restart_Heuristics_LLVM
  imports IsaSAT_Restart_Heuristics IsaSAT_Setup_LLVM
     IsaSAT_VMTF_LLVM
begin


sepref_def clause_score_ordering
  is \<open>uncurry (RETURN oo clause_score_ordering)\<close>
  :: \<open>(uint32_nat_assn *a uint32_nat_assn)\<^sup>k *\<^sub>a (uint32_nat_assn *a uint32_nat_assn)\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding clause_score_ordering_def
  by sepref

sepref_def get_slow_ema_heur_fast_code
  is \<open>RETURN o get_slow_ema_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  unfolding get_slow_ema_heur_alt_def isasat_bounded_assn_def heuristic_assn_def
  by sepref

sepref_def get_fast_ema_heur_fast_code
  is \<open>RETURN o get_fast_ema_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  unfolding get_fast_ema_heur_alt_def isasat_bounded_assn_def heuristic_assn_def
  by sepref

sepref_def get_conflict_count_since_last_restart_heur_fast_code
  is \<open>RETURN o get_conflict_count_since_last_restart_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding get_counflict_count_heur_alt_def isasat_bounded_assn_def heuristic_assn_def
  by sepref

sepref_def get_learned_count_fast_code
  is \<open>RETURN o get_learned_count\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  unfolding get_learned_count_alt_def isasat_bounded_assn_def
  by sepref


sepref_def find_local_restart_target_level_fast_code
  is \<open>uncurry find_local_restart_target_level_int\<close>
  :: \<open>trail_pol_fast_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=1]] length_rev[simp del]
  unfolding find_local_restart_target_level_int_def find_local_restart_target_level_int_inv_def
    length_uint32_nat_def vmtf_remove_assn_def trail_pol_fast_assn_def
  apply (annot_unat_const "TYPE(32)")
   apply (rewrite at "stamp (\<hole>)" annot_index_of_atm)
   apply (rewrite in "(_ ! _)" annot_unat_snat_upcast[where 'l=64])
   apply (rewrite in "(_ ! \<hole>)" annot_unat_snat_upcast[where 'l=64])
   apply (rewrite in "(\<hole> < length _)" annot_unat_snat_upcast[where 'l=64])
  by sepref


sepref_register incr_restart_stat

sepref_def incr_restart_stat_fast_code
  is \<open>incr_restart_stat\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding incr_restart_stat_def isasat_bounded_assn_def PR_CONST_def
    heuristic_assn_def fold_tuple_optimizations
  by sepref

sepref_register incr_lrestart_stat

sepref_def incr_lrestart_stat_fast_code
  is \<open>incr_lrestart_stat\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding incr_lrestart_stat_def isasat_bounded_assn_def PR_CONST_def
    heuristic_assn_def fold_tuple_optimizations
  by sepref

sepref_def find_local_restart_target_level_st_fast_code
  is \<open>find_local_restart_target_level_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=1]] length_rev[simp del]
  unfolding find_local_restart_target_level_st_alt_def isasat_bounded_assn_def PR_CONST_def
    fold_tuple_optimizations
  by sepref

sepref_def empty_Q_fast_code
  is \<open>empty_Q\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding empty_Q_def isasat_bounded_assn_def fold_tuple_optimizations
    heuristic_assn_def
  by sepref


sepref_register cdcl_twl_local_restart_wl_D_heur
  empty_Q find_decomp_wl_st_int

find_theorems count_decided_st_heur name:refine
sepref_def cdcl_twl_local_restart_wl_D_heur_fast_code
  is \<open>cdcl_twl_local_restart_wl_D_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding cdcl_twl_local_restart_wl_D_heur_def PR_CONST_def
    fold_tuple_optimizations
  supply [[goals_limit = 1]]
  by sepref

sepref_register upper_restart_bound_not_reached

sepref_def upper_restart_bound_not_reached_fast_impl
  is \<open>(RETURN o upper_restart_bound_not_reached)\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding upper_restart_bound_not_reached_def PR_CONST_def isasat_bounded_assn_def
    fold_tuple_optimizations
  supply [[goals_limit = 1]]
  by sepref

sepref_register lower_restart_bound_not_reached
sepref_def lower_restart_bound_not_reached_impl
  is \<open>(RETURN o lower_restart_bound_not_reached)\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding lower_restart_bound_not_reached_def PR_CONST_def isasat_bounded_assn_def
    fold_tuple_optimizations
  supply [[goals_limit = 1]]
  by sepref


sepref_register clause_score_extract

sepref_def (in -) clause_score_extract_code
  is \<open>uncurry (RETURN oo clause_score_extract)\<close>
  :: \<open>[uncurry valid_sort_clause_score_pre_at]\<^sub>a
      arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn *a uint32_nat_assn\<close>
  supply [[goals_limit = 1]]
  unfolding clause_score_extract_def valid_sort_clause_score_pre_at_def
  apply (annot_unat_const "TYPE(32)")
  by sepref

declare clause_score_extract_code.refine[sepref_fr_rules]

sepref_def partition_main_clause_fast_code
  is \<open>uncurry3 partition_main_clause\<close>
  :: \<open>[\<lambda>(((arena, i), j), vdom). length vdom \<le> sint64_max \<and> valid_sort_clause_score_pre arena vdom]\<^sub>a
      arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a vdom_fast_assn\<^sup>d \<rightarrow> vdom_fast_assn *a sint64_nat_assn\<close>
  supply insort_inner_clauses_by_score_invI[intro] [[goals_limit=1]]
    partition_main_inv_def[simp] mset_eq_length[dest]
  unfolding partition_main_clause_def partition_between_ref_def
    partition_main_def convert_swap gen_swap
    WB_More_Refinement_List.swap_def
  apply (annot_snat_const "TYPE(64)")
  by sepref


sepref_def partition_clause_fast_code
  is \<open>uncurry3 partition_clause\<close>
  :: \<open>[\<lambda>(((arena, i), j), vdom). length vdom \<le> sint64_max \<and> valid_sort_clause_score_pre arena vdom]\<^sub>a
      arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a vdom_fast_assn\<^sup>d \<rightarrow> vdom_fast_assn *a sint64_nat_assn\<close>
  supply insort_inner_clauses_by_score_invI[intro] valid_sort_clause_score_pre_swap[
    unfolded WB_More_Refinement_List.swap_def, intro] mset_eq_length[dest]
  unfolding partition_clause_def partition_between_ref_def
    choose_pivot3_def partition_main_clause_def[symmetric]
    convert_swap gen_swap
  apply (annot_snat_const "TYPE(64)")
  by sepref


(*TODO useful?*)
lemma minus_safe:
  \<open>p - a = (if p \<ge> a then p - a else 0)\<close> for p a :: nat
  by auto

sepref_def sort_clauses_by_score_code
  is \<open>uncurry quicksort_clauses_by_score\<close>
  :: \<open>[uncurry valid_sort_clause_score_pre]\<^sub>a
      arena_fast_assn\<^sup>k *\<^sub>a vdom_fast_assn\<^sup>d \<rightarrow> vdom_fast_assn\<close>
  supply sort_clauses_by_score_invI[intro] [[goals_limit=1]]
  unfolding
    quicksort_clauses_by_score_def
    full_quicksort_ref_def
    quicksort_ref_def
    partition_clause_def[symmetric]
    List.null_def
    length_0_conv[symmetric]
  apply (rewrite in \<open>(_, \<hole>, _)\<close> minus_safe)
  apply (rewrite in \<open>If \<hole> _\<close> minus_safe)
  apply (annot_snat_const "TYPE(64)")
  by sepref


sepref_register remove_deleted_clauses_from_avdom arena_status DELETED

sepref_def remove_deleted_clauses_from_avdom_fast_code
  is \<open>uncurry isa_remove_deleted_clauses_from_avdom\<close>
  :: \<open>[\<lambda>(N, vdom). length vdom \<le> sint64_max]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a vdom_fast_assn\<^sup>d \<rightarrow> vdom_fast_assn\<close>
  supply [[goals_limit=1]]
  unfolding isa_remove_deleted_clauses_from_avdom_def
    convert_swap gen_swap if_conn(4)
  apply (annot_snat_const "TYPE(64)")
  by sepref


sepref_def sort_vdom_heur_fast_code
  is \<open>sort_vdom_heur\<close>
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>aisasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply sort_clauses_by_score_invI[intro]
    [[goals_limit=1]]
  unfolding sort_vdom_heur_def isasat_bounded_assn_def
  by sepref

sepref_def opts_restart_st_fast_code
  is \<open>RETURN o opts_restart_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding opts_restart_st_def isasat_bounded_assn_def
  by sepref


sepref_def opts_reduction_st_fast_code
  is \<open>RETURN o opts_reduction_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding opts_reduction_st_def isasat_bounded_assn_def
  by sepref

sepref_register opts_reduction_st opts_restart_st


sepref_register max_restart_decision_lvl

sepref_def minimum_number_between_restarts_impl
  is \<open>uncurry0 (RETURN minimum_number_between_restarts)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding minimum_number_between_restarts_def
  by sepref

sepref_def uint32_nat_assn_impl
  is \<open>uncurry0 (RETURN max_restart_decision_lvl)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding max_restart_decision_lvl_def
  apply (annot_unat_const "TYPE(32)")
  by sepref


sepref_def GC_EVERY_impl
  is \<open>uncurry0 (RETURN GC_EVERY)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding GC_EVERY_def
  by sepref


lemma emag_get_value_alt_def:
  \<open>ema_get_value = (\<lambda>(a, b, c, d). a)\<close>
  by auto
sepref_def ema_get_value_impl
  is \<open>RETURN o ema_get_value\<close>
  :: \<open>ema_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding emag_get_value_alt_def
  by sepref

lemma restart_required_heur_alt_def:
  \<open>restart_required_heur S n = do {
    let opt_red = opts_reduction_st S;
    let opt_res = opts_restart_st S;
    let sema = get_slow_ema_heur S;
    sema \<leftarrow> RETURN (ema_get_value sema);
    let limit = (11 * sema) >> 4;
    let fema = (get_fast_ema_heur S);
    fema \<leftarrow> RETURN (ema_get_value fema);
    let ccount = get_conflict_count_since_last_restart_heur S;
    let lcount = get_learned_count S;
    let can_res = (lcount > n);
    let min_reached = (ccount > minimum_number_between_restarts);
    let level = count_decided_st_heur S;
    let should_not_reduce = (\<not>opt_red \<or> upper_restart_bound_not_reached S);
    RETURN ((opt_res \<or> opt_red) \<and>
       (should_not_reduce \<longrightarrow> limit > fema) \<and> min_reached \<and> can_res \<and>
      level > 2 \<and> \<^cancel>\<open>This comment from Marijn Heule seems not to help:
         \<^term>\<open>level < max_restart_decision_lvl\<close>\<close>
      of_nat level > (fema >> 32))}
  \<close>
  by (auto simp: restart_required_heur_def bind_to_let_conv Let_def)

sepref_register ema_get_value get_fast_ema_heur get_slow_ema_heur
sepref_def restart_required_heur_fast_code
  is \<open>uncurry restart_required_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  supply [[goals_limit=1]]
  unfolding restart_required_heur_alt_def
  apply (rewrite in \<open>\<hole> < _\<close> unat_const_fold(3)[where 'a=32])
  apply (rewrite in \<open>(_ >> 32) < \<hole>\<close> annot_unat_unat_upcast[where 'l=64])
  apply (annot_snat_const "TYPE(64)")
  by sepref

sepref_def get_reductions_count_fast_code
  is \<open>RETURN o get_reductions_count\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding get_reduction_count_alt_def isasat_bounded_assn_def
  by sepref


sepref_register get_reductions_count


sepref_def GC_required_heur_fast_code
  is \<open>uncurry GC_required_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  supply [[goals_limit=1]]
  unfolding GC_required_heur_def GC_EVERY_def
  by sepref

sepref_register isa_trail_nth isasat_trail_nth_st

sepref_def isasat_trail_nth_st_code
  is \<open>uncurry isasat_trail_nth_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a unat_lit_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_trail_nth_st_alt_def isasat_bounded_assn_def
  by sepref



sepref_register get_the_propagation_reason_pol_st

sepref_def get_the_propagation_reason_pol_st_code
  is \<open>uncurry get_the_propagation_reason_pol_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a snat_option_assn' TYPE(64)\<close>
  supply [[goals_limit=1]]
  unfolding get_the_propagation_reason_pol_st_alt_def isasat_bounded_assn_def
  by sepref

sepref_register isasat_replace_annot_in_trail
sepref_def isasat_replace_annot_in_trail_code
  is \<open>uncurry2 isasat_replace_annot_in_trail\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a (sint64_nat_assn)\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_replace_annot_in_trail_def isasat_bounded_assn_def
    trail_pol_fast_assn_def
  apply (annot_snat_const "TYPE(64)")
  apply (rewrite at "list_update _ _ _" annot_index_of_atm)
  by sepref

sepref_register mark_garbage_heur2
sepref_def mark_garbage_heur2_code
  is \<open>uncurry mark_garbage_heur2\<close>
  :: \<open>[\<lambda>(C, S). mark_garbage_pre (get_clauses_wl_heur S, C) \<and> arena_is_valid_clause_vdom (get_clauses_wl_heur S) C]\<^sub>a
     sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding mark_garbage_heur2_def isasat_bounded_assn_def
    fold_tuple_optimizations
  apply (annot_unat_const "TYPE(64)")
  by sepref


sepref_register remove_one_annot_true_clause_one_imp_wl_D_heur
term mark_garbage_heur2
sepref_def remove_one_annot_true_clause_one_imp_wl_D_heur_code
  is \<open>uncurry remove_one_annot_true_clause_one_imp_wl_D_heur\<close>
  :: \<open>sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a sint64_nat_assn *a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding remove_one_annot_true_clause_one_imp_wl_D_heur_def
    isasat_trail_nth_st_def[symmetric] get_the_propagation_reason_pol_st_def[symmetric]
    fold_tuple_optimizations
  apply (rewrite in \<open>_ = \<hole>\<close> snat_const_fold(1)[where 'a=64])
  apply (annot_snat_const "TYPE(64)")
  by sepref

sepref_register isasat_length_trail_st

sepref_def isasat_length_trail_st_code
  is \<open>RETURN o isasat_length_trail_st\<close>
  :: \<open>[isa_length_trail_pre o get_trail_wl_heur]\<^sub>a isasat_bounded_assn\<^sup>k  \<rightarrow> sint64_nat_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_length_trail_st_alt_def isasat_bounded_assn_def
  by sepref

sepref_register get_pos_of_level_in_trail_imp_st

sepref_def get_pos_of_level_in_trail_imp_st_code
  is \<open>uncurry get_pos_of_level_in_trail_imp_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k  \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  supply [[goals_limit=1]]
  unfolding get_pos_of_level_in_trail_imp_alt_def isasat_bounded_assn_def
  apply (rewrite in "_" eta_expand[where f = RETURN])
  apply (rewrite in "RETURN \<hole>" annot_unat_snat_upcast[where 'l=64])
  by sepref

sepref_register remove_one_annot_true_clause_imp_wl_D_heur

sepref_def remove_one_annot_true_clause_imp_wl_D_heur_code
  is \<open>remove_one_annot_true_clause_imp_wl_D_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding remove_one_annot_true_clause_imp_wl_D_heur_def
    isasat_length_trail_st_def[symmetric] get_pos_of_level_in_trail_imp_st_def[symmetric]
  apply (rewrite at "(\<hole>, _)" annot_unat_snat_upcast[where 'l=64])
  apply (annot_unat_const "TYPE(32)")
  by sepref


lemma length_ll[def_pat_rules]: \<open>length_ll$xs$i \<equiv> op_list_list_llen$xs$i\<close>
  by (auto simp: length_ll_def)

lemma [def_pat_rules]: \<open>nth_rll \<equiv> op_list_list_idx\<close>
  by (auto simp: nth_rll_def[abs_def] op_list_list_idx_def intro!: ext)

sepref_register length_ll extra_information_mark_to_delete nth_rll
  LEARNED

lemma isasat_GC_clauses_prog_copy_wl_entry_alt_def:
\<open>isasat_GC_clauses_prog_copy_wl_entry = (\<lambda>N0 W A (N', vdm, avdm). do {
    ASSERT(nat_of_lit A < length W);
    ASSERT(length (W ! nat_of_lit A) \<le> length N0);
    let le = length (W ! nat_of_lit A);
    (i, N, N', vdm, avdm) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(i, N, N', vdm, avdm). i < le)
      (\<lambda>(i, N, (N', vdm, avdm)). do {
        ASSERT(i < length (W ! nat_of_lit A));
        let (C, _, _) = (W ! nat_of_lit A ! i);
        ASSERT(arena_is_valid_clause_vdom N C);
        let st = arena_status N C;
        if st \<noteq> DELETED then do {
          ASSERT(arena_is_valid_clause_idx N C);
          ASSERT(length N' + (if arena_length N C > 4 then 5 else 4) + arena_length N C \<le> length N0);
          ASSERT(length N = length N0);
          ASSERT(length vdm < length N0);
          ASSERT(length avdm < length N0);
          let D = length N' + (if arena_length N C > 4 then 5 else 4);
          N' \<leftarrow> fm_mv_clause_to_new_arena C N N';
          ASSERT(mark_garbage_pre (N, C));
	  RETURN (i+1, extra_information_mark_to_delete N C, N', vdm @ [D],
             (if st = LEARNED then avdm @ [D] else avdm))
        } else RETURN (i+1, N, (N', vdm, avdm))
      }) (0, N0, (N', vdm, avdm));
    RETURN (N, (N', vdm, avdm))
  })\<close>
proof -
  have H: \<open>(let (a, _, _) = c in f a) = (let a = fst c in f a)\<close> for a c f
    by (cases c) (auto simp: Let_def)
  show ?thesis
    unfolding isasat_GC_clauses_prog_copy_wl_entry_def H
    ..
qed

sepref_def isasat_GC_clauses_prog_copy_wl_entry_code
  is \<open>uncurry3 isasat_GC_clauses_prog_copy_wl_entry\<close>
  :: \<open>[\<lambda>(((N, _), _), _). length N \<le> sint64_max]\<^sub>a
     arena_fast_assn\<^sup>d *\<^sub>a watchlist_fast_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a
         (arena_fast_assn *a vdom_fast_assn *a vdom_fast_assn)\<^sup>d \<rightarrow>
     (arena_fast_assn *a (arena_fast_assn *a vdom_fast_assn *a vdom_fast_assn))\<close>
  supply [[goals_limit=1]] if_splits[split] length_ll_def[simp]
  unfolding isasat_GC_clauses_prog_copy_wl_entry_alt_def nth_rll_def[symmetric]
    length_ll_def[symmetric] if_conn(4)
  apply (annot_snat_const "TYPE(64)")
  by sepref

sepref_register isasat_GC_clauses_prog_copy_wl_entry

lemma shorten_taken_op_list_list_take:
  \<open>W[L := []] = op_list_list_take W L 0\<close>
  by (auto simp:)

sepref_def isasat_GC_clauses_prog_single_wl_code
  is \<open>uncurry3 isasat_GC_clauses_prog_single_wl\<close>
  :: \<open>[\<lambda>(((N, _), _), A). A \<le> uint32_max div 2 \<and> length N \<le> sint64_max]\<^sub>a
     arena_fast_assn\<^sup>d *\<^sub>a (arena_fast_assn *a vdom_fast_assn *a vdom_fast_assn)\<^sup>d *\<^sub>a watchlist_fast_assn\<^sup>d *\<^sub>a atom_assn\<^sup>k \<rightarrow>
     (arena_fast_assn *a (arena_fast_assn *a vdom_fast_assn *a vdom_fast_assn) *a watchlist_fast_assn)\<close>
  supply [[goals_limit=1]]
  unfolding isasat_GC_clauses_prog_single_wl_def
    shorten_taken_op_list_list_take
  apply (annot_snat_const "TYPE(64)")
  by sepref


definition isasat_GC_clauses_prog_wl2' where
  \<open>isasat_GC_clauses_prog_wl2' ns fst' = (isasat_GC_clauses_prog_wl2 (ns, fst'))\<close>

sepref_register isasat_GC_clauses_prog_wl2 isasat_GC_clauses_prog_single_wl
sepref_def isasat_GC_clauses_prog_wl2_code
  is \<open>uncurry2 isasat_GC_clauses_prog_wl2'\<close>
  :: \<open>[\<lambda>((_, _), (N, _)). length N \<le> sint64_max]\<^sub>a
     (array_assn vmtf_node_assn)\<^sup>k *\<^sub>a (atom.option_assn)\<^sup>k *\<^sub>a
     (arena_fast_assn *a (arena_fast_assn *a vdom_fast_assn *a vdom_fast_assn) *a watchlist_fast_assn)\<^sup>d \<rightarrow>
     (arena_fast_assn *a (arena_fast_assn *a vdom_fast_assn *a vdom_fast_assn) *a watchlist_fast_assn)\<close>
  supply [[goals_limit=1]]
  unfolding isasat_GC_clauses_prog_wl2_def isasat_GC_clauses_prog_wl2'_def prod.case
    atom.fold_option
  apply (rewrite at \<open> _ ! _\<close> annot_index_of_atm)
  by sepref


sepref_register isasat_GC_clauses_prog_wl isasat_GC_clauses_prog_wl2' rewatch_heur_st
sepref_def isasat_GC_clauses_prog_wl_code
  is \<open>isasat_GC_clauses_prog_wl\<close>
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_GC_clauses_prog_wl_def isasat_bounded_assn_def
     isasat_GC_clauses_prog_wl2'_def[symmetric] vmtf_remove_assn_def
    atom.fold_option fold_tuple_optimizations
  apply (annot_snat_const "TYPE(64)")
  by sepref

lemma rewatch_heur_st_pre_alt_def:
  \<open>rewatch_heur_st_pre S \<longleftrightarrow> (\<forall>i \<in> set (get_vdom S). i \<le> sint64_max)\<close>
  by (auto simp: rewatch_heur_st_pre_def all_set_conv_nth)

sepref_def rewatch_heur_st_code
  is \<open>rewatch_heur_st\<close>
  :: \<open>[\<lambda>S. rewatch_heur_st_pre S \<and> length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]  append_ll_def[simp]
  unfolding isasat_GC_clauses_prog_wl_def isasat_bounded_assn_def
    rewatch_heur_st_def Let_def rewatch_heur_st_pre_alt_def
  by sepref

sepref_register isasat_GC_clauses_wl_D

sepref_def isasat_GC_clauses_wl_D_code
  is \<open>isasat_GC_clauses_wl_D\<close>
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]] isasat_GC_clauses_wl_D_rewatch_pre[intro!]
  unfolding isasat_GC_clauses_wl_D_def
  by sepref

sepref_register number_clss_to_keep

sepref_register access_vdom_at

lemma [sepref_fr_rules]:
  \<open>(return o id, RETURN o unat) \<in> word64_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
proof -
  have [simp]: \<open>(\<lambda>s. \<exists>xa. (\<up>(xa = unat x) \<and>* \<up>(xa = unat x)) s) = \<up>True\<close>
    by (intro ext)
     (auto intro!: exI[of _ \<open>unat x\<close>] simp: pure_true_conv pure_part_pure_eq pred_lift_def
      simp flip: import_param_3)
  show ?thesis
    apply sepref_to_hoare
    apply (vcg)
    apply (auto simp: unat_rel_def unat.rel_def br_def pred_lift_def ENTAILS_def pure_true_conv simp flip: import_param_3 pure_part_def)
    done
qed

sepref_def number_clss_to_keep_fast_code
  is \<open>number_clss_to_keep_impl\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  supply [[goals_limit = 1]]
  unfolding number_clss_to_keep_impl_def isasat_bounded_assn_def
    fold_tuple_optimizations
  apply (rewrite at "If _ _ \<hole>" annot_unat_snat_conv)
  apply (rewrite at "If (\<hole> \<le>_)" annot_snat_unat_conv)
  by sepref

lemma number_clss_to_keep_impl_number_clss_to_keep:
  \<open>(number_clss_to_keep_impl, number_clss_to_keep) \<in> Sepref_Rules.freft Id (\<lambda>_. \<langle>nat_rel\<rangle>nres_rel)\<close>
  by (auto simp: number_clss_to_keep_impl_def number_clss_to_keep_def Let_def intro!: frefI nres_relI)

lemma number_clss_to_keep_fast_code_refine[sepref_fr_rules]:
  \<open>(number_clss_to_keep_fast_code, number_clss_to_keep) \<in> (isasat_bounded_assn)\<^sup>k \<rightarrow>\<^sub>a snat_assn\<close>
  using hfcomp[OF number_clss_to_keep_fast_code.refine
    number_clss_to_keep_impl_number_clss_to_keep, simplified]
  by auto

sepref_def access_vdom_at_fast_code
  is \<open>uncurry (RETURN oo access_vdom_at)\<close>
  :: \<open>[uncurry access_vdom_at_pre]\<^sub>a isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> sint64_nat_assn\<close>
  unfolding access_vdom_at_alt_def access_vdom_at_pre_def isasat_bounded_assn_def
  supply [[goals_limit = 1]]
  by sepref


experiment
begin
  export_llvm restart_required_heur_fast_code
    access_vdom_at_fast_code
    isasat_GC_clauses_wl_D_code
end

end
