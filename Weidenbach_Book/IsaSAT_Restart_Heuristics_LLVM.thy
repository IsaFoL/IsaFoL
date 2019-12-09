theory IsaSAT_Restart_Heuristics_LLVM
  imports IsaSAT_Restart_Heuristics IsaSAT_Setup_LLVM
     IsaSAT_VMTF_LLVM IsaSAT_Rephase_LLVM
     IsaSAT_Arena_Sorting_LLVM
begin

hide_fact (open) Sepref_Rules.frefI
no_notation Sepref_Rules.fref ("[_]\<^sub>f\<^sub>d _ \<rightarrow> _" [0,60,60] 60)
no_notation Sepref_Rules.freft ("_ \<rightarrow>\<^sub>f\<^sub>d _" [60,60] 60)
no_notation Sepref_Rules.freftnd ("_ \<rightarrow>\<^sub>f _" [60,60] 60)
no_notation Sepref_Rules.frefnd ("[_]\<^sub>f _ \<rightarrow> _" [0,60,60] 60)

sepref_def FLAG_restart_impl
  is \<open>uncurry0 (RETURN FLAG_restart)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding FLAG_restart_def
  by sepref

sepref_def FLAG_no_restart_impl
  is \<open>uncurry0 (RETURN FLAG_no_restart)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding FLAG_no_restart_def
  by sepref

sepref_def FLAG_GC_restart_impl
  is \<open>uncurry0 (RETURN FLAG_GC_restart)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding FLAG_GC_restart_def
  by sepref

lemma current_restart_phase_alt_def:
  \<open>current_restart_phase = (\<lambda>(fast_ema, slow_ema,
    (ccount, ema_lvl, restart_phase, end_of_phase), _).
    restart_phase)\<close>
  by auto

sepref_def current_restart_phase_impl
  is \<open>RETURN o current_restart_phase\<close>
  :: \<open>heuristic_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding current_restart_phase_alt_def heuristic_assn_def
  by sepref

sepref_def get_restart_phase_imp
  is \<open>(RETURN o get_restart_phase)\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding get_restart_phase_def isasat_bounded_assn_def
  by sepref

sepref_def end_of_restart_phase_impl
  is \<open>RETURN o end_of_restart_phase\<close>
  :: \<open>heuristic_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding end_of_restart_phase_def heuristic_assn_def
  by sepref

sepref_def end_of_restart_phase_st_impl
  is \<open>RETURN o end_of_restart_phase_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding end_of_restart_phase_st_def isasat_bounded_assn_def
  by sepref

sepref_def end_of_rephasing_phase_impl
  is \<open>RETURN o end_of_rephasing_phase\<close>
  :: \<open>phase_heur_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding end_of_rephasing_phase_def heuristic_assn_def
  by sepref
  
sepref_def end_of_rephasing_phase_heur_impl
  is \<open>RETURN o end_of_rephasing_phase_heur\<close>
  :: \<open>heuristic_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding end_of_rephasing_phase_heur_def heuristic_assn_def
  by sepref

sepref_def end_of_rephasing_phase_st_impl
  is \<open>RETURN o end_of_rephasing_phase_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding end_of_rephasing_phase_st_def isasat_bounded_assn_def
  by sepref

lemma incr_restart_phase_end_alt_def:
  \<open>incr_restart_phase_end = (\<lambda>(fast_ema, slow_ema,
    (ccount, ema_lvl, restart_phase, end_of_phase, length_phase), wasted).
    (fast_ema, slow_ema, (ccount, ema_lvl, restart_phase, end_of_phase + length_phase,
      (length_phase * 3) >> 1), wasted))\<close>
  by auto

sepref_def incr_restart_phase_end_impl
  is \<open>RETURN o incr_restart_phase_end\<close>
  :: \<open>heuristic_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_assn\<close>
  supply[[goals_limit=1]]
  unfolding heuristic_assn_def incr_restart_phase_end_alt_def
  apply (annot_snat_const "TYPE(64)")
  by sepref


lemma incr_restart_phase_alt_def:
  \<open>incr_restart_phase = (\<lambda>(fast_ema, slow_ema,
    (ccount, ema_lvl, restart_phase, end_of_phase), wasted).
     (fast_ema, slow_ema, (ccount, ema_lvl, restart_phase XOR 1, end_of_phase), wasted))\<close>
  by auto

sepref_def incr_restart_phase_impl
  is \<open>RETURN o incr_restart_phase\<close>
  :: \<open>heuristic_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_assn\<close>
  unfolding heuristic_assn_def incr_restart_phase_alt_def
  by sepref

sepref_register incr_restart_phase incr_restart_phase_end
  update_restart_phases update_all_phases

sepref_def update_restart_phases_impl
  is \<open>update_restart_phases\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding update_restart_phases_def isasat_bounded_assn_def
    fold_tuple_optimizations
  by sepref

sepref_def update_all_phases_impl
  is \<open>uncurry update_all_phases\<close>
  :: \<open>isasat_bounded_assn\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a
     isasat_bounded_assn \<times>\<^sub>a uint64_nat_assn\<close>
  unfolding update_all_phases_def
    fold_tuple_optimizations
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


find_theorems sort_spec

definition lbd_sort_clauses_raw :: \<open>arena \<Rightarrow> vdom \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list nres\<close> where
  \<open>lbd_sort_clauses_raw arena N = pslice_sort_spec idx_cdom clause_score_less arena N\<close>

definition lbd_sort_clauses :: \<open>arena \<Rightarrow> vdom \<Rightarrow> nat list nres\<close> where
  \<open>lbd_sort_clauses arena N = lbd_sort_clauses_raw arena N 0 (length N)\<close>

lemmas LBD_introsort[sepref_fr_rules] =
  LBD_it.introsort_param_impl_correct[unfolded lbd_sort_clauses_raw_def[symmetric] PR_CONST_def]

lemma quicksort_clauses_by_score_sort:
 \<open>(lbd_sort_clauses, sort_clauses_by_score) \<in>
   Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
   apply (intro fun_relI nres_relI)
   subgoal for arena arena' vdom vdom'
   by (auto simp: lbd_sort_clauses_def lbd_sort_clauses_raw_def sort_clauses_by_score_def
       pslice_sort_spec_def le_ASSERT_iff idx_cdom_def slice_rel_def br_def
       conc_fun_RES sort_spec_def
       eq_commute[of _ \<open>length vdom'\<close>]
     intro!: ASSERT_leI slice_sort_spec_refine_sort[THEN order_trans, of _ vdom vdom])
   done


sepref_register lbd_sort_clauses_raw
sepref_def lbd_sort_clauses_impl
  is \<open>uncurry lbd_sort_clauses\<close>
  :: \<open>arena_fast_assn\<^sup>k *\<^sub>a vdom_fast_assn\<^sup>d \<rightarrow>\<^sub>a vdom_fast_assn\<close>
  supply[[goals_limit=1]]
  unfolding lbd_sort_clauses_def
  apply (annot_snat_const "TYPE(64)")
  by sepref

lemmas [sepref_fr_rules] =
  lbd_sort_clauses_impl.refine[FCOMP quicksort_clauses_by_score_sort]

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


sepref_def get_reductions_count_fast_code
  is \<open>RETURN o get_reductions_count\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding get_reduction_count_alt_def isasat_bounded_assn_def
  by sepref


sepref_register get_reductions_count

lemma of_nat_snat:
  "(id,of_nat) \<in> snat_rel' TYPE('a::len2) \<rightarrow> word_rel"
  by (auto simp: snat_rel_def snat.rel_def in_br_conv snat_eq_unat)

sepref_def GC_required_heur_fast_code
  is \<open>uncurry GC_required_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  supply [[goals_limit=1]] of_nat_snat[sepref_import_param]
  unfolding GC_required_heur_def GC_EVERY_def
  apply (annot_snat_const "TYPE(64)")
  by sepref

sepref_register ema_get_value get_fast_ema_heur get_slow_ema_heur
sepref_def restart_required_heur_fast_code
  is \<open>uncurry restart_required_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  supply [[goals_limit=1]]
  unfolding restart_required_heur_def
  apply (rewrite in \<open>\<hole> < _\<close> unat_const_fold(3)[where 'a=32])
  apply (rewrite in \<open>(_ >> 32) < \<hole>\<close> annot_unat_unat_upcast[where 'l=64])
  apply (annot_snat_const "TYPE(64)")
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
  :: \<open>sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a sint64_nat_assn \<times>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding remove_one_annot_true_clause_one_imp_wl_D_heur_def
    isasat_trail_nth_st_def[symmetric] get_the_propagation_reason_pol_st_def[symmetric]
    fold_tuple_optimizations
  apply (rewrite in \<open>_ = \<hole>\<close> snat_const_fold(1)[where 'a=64])
  apply (annot_snat_const "TYPE(64)")
  by sepref
sepref_register mark_clauses_as_unused_wl_D_heur

sepref_def access_vdom_at_fast_code
  is \<open>uncurry (RETURN oo access_vdom_at)\<close>
  :: \<open>[uncurry access_vdom_at_pre]\<^sub>a isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> sint64_nat_assn\<close>
  unfolding access_vdom_at_alt_def access_vdom_at_pre_def isasat_bounded_assn_def
  supply [[goals_limit = 1]]
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
         (arena_fast_assn \<times>\<^sub>a vdom_fast_assn \<times>\<^sub>a vdom_fast_assn)\<^sup>d \<rightarrow>
     (arena_fast_assn \<times>\<^sub>a (arena_fast_assn \<times>\<^sub>a vdom_fast_assn \<times>\<^sub>a vdom_fast_assn))\<close>
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
     arena_fast_assn\<^sup>d *\<^sub>a (arena_fast_assn \<times>\<^sub>a vdom_fast_assn \<times>\<^sub>a vdom_fast_assn)\<^sup>d *\<^sub>a watchlist_fast_assn\<^sup>d *\<^sub>a atom_assn\<^sup>k \<rightarrow>
     (arena_fast_assn \<times>\<^sub>a (arena_fast_assn \<times>\<^sub>a vdom_fast_assn \<times>\<^sub>a vdom_fast_assn) \<times>\<^sub>a watchlist_fast_assn)\<close>
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
     (arena_fast_assn \<times>\<^sub>a (arena_fast_assn \<times>\<^sub>a vdom_fast_assn \<times>\<^sub>a vdom_fast_assn) \<times>\<^sub>a watchlist_fast_assn)\<^sup>d \<rightarrow>
     (arena_fast_assn \<times>\<^sub>a (arena_fast_assn \<times>\<^sub>a vdom_fast_assn \<times>\<^sub>a vdom_fast_assn) \<times>\<^sub>a watchlist_fast_assn)\<close>
  supply [[goals_limit=1]]
  unfolding isasat_GC_clauses_prog_wl2_def isasat_GC_clauses_prog_wl2'_def prod.case
    atom.fold_option
  apply (rewrite at \<open> _ ! _\<close> annot_index_of_atm)
  by sepref

(*TODO Move*)
sepref_def set_zero_wasted_impl
  is \<open>RETURN o set_zero_wasted\<close>
  :: \<open>heuristic_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_assn\<close>
  unfolding heuristic_assn_def set_zero_wasted_def
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
  by (auto simp: number_clss_to_keep_impl_def number_clss_to_keep_def Let_def intro!: Sepref_Rules.frefI nres_relI)

lemma number_clss_to_keep_fast_code_refine[sepref_fr_rules]:
  \<open>(number_clss_to_keep_fast_code, number_clss_to_keep) \<in> (isasat_bounded_assn)\<^sup>k \<rightarrow>\<^sub>a snat_assn\<close>
  using hfcomp[OF number_clss_to_keep_fast_code.refine
    number_clss_to_keep_impl_number_clss_to_keep, simplified]
  by auto


sepref_def mark_clauses_as_unused_wl_D_heur_fast_code
  is \<open>uncurry mark_clauses_as_unused_wl_D_heur\<close>
  :: \<open>[\<lambda>(_, S). length (get_avdom S) \<le> sint64_max]\<^sub>a
    sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]] length_avdom_def[simp]
  unfolding mark_clauses_as_unused_wl_D_heur_def
    mark_unused_st_heur_def[symmetric]
    access_vdom_at_def[symmetric] length_avdom_def[symmetric]
  apply (annot_snat_const "TYPE(64)")
  by sepref

experiment
begin
  export_llvm restart_required_heur_fast_code
    access_vdom_at_fast_code
    isasat_GC_clauses_wl_D_code
end

end
