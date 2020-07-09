theory IsaSAT_Setup_LLVM
  imports IsaSAT_Setup IsaSAT_Watch_List_LLVM IsaSAT_Lookup_Conflict_LLVM
    More_Sepref.WB_More_Refinement IsaSAT_Clauses_LLVM LBD_LLVM
    IsaSAT_Options_LLVM IsaSAT_VMTF_Setup_LLVM
    IsaSAT_Arena_Sorting_LLVM
    IsaSAT_Rephase_LLVM
    IsaSAT_EMA_LLVM
    IsaSAT_Stats_LLVM
begin


no_notation WB_More_Refinement.fref (\<open>[_]\<^sub>f _ \<rightarrow> _\<close> [0,60,60] 60)
no_notation WB_More_Refinement.freft (\<open>_ \<rightarrow>\<^sub>f _\<close> [60,60] 60)


(*TODO Move*)

paragraph \<open>Options\<close>
sepref_register mop_arena_length

(* TODO: Move *)
type_synonym arena_assn = \<open>(32 word, 64) array_list\<close>
type_synonym heur_assn = \<open>(ema \<times> ema \<times> restart_info \<times> 64 word \<times>
   phase_saver_assn \<times> 64 word \<times> phase_saver'_assn \<times> 64 word \<times> phase_saver'_assn \<times> 64 word \<times> 64 word \<times> 64 word)\<close>

type_synonym twl_st_wll_trail_fast =
  \<open>trail_pol_fast_assn \<times> arena_assn \<times> option_lookup_clause_assn \<times>
    64 word \<times> watched_wl_uint32 \<times> vmtf_remove_assn \<times>
    32 word \<times> cach_refinement_l_assn \<times> lbd_assn \<times> out_learned_assn \<times> stats \<times>
    heur_assn \<times>
    vdom_fast_assn \<times> vdom_fast_assn \<times> (64 word \<times> 64 word \<times> 64 word) \<times> opts_assn \<times> arena_assn\<close>


definition heuristic_assn :: \<open>restart_heuristics \<Rightarrow> heur_assn \<Rightarrow> assn\<close> where
  \<open>heuristic_assn = ema_assn \<times>\<^sub>a
  ema_assn \<times>\<^sub>a
  restart_info_assn \<times>\<^sub>a
  word64_assn \<times>\<^sub>a phase_heur_assn\<close>

definition isasat_bounded_assn :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wll_trail_fast \<Rightarrow> assn\<close> where
\<open>isasat_bounded_assn =
  trail_pol_fast_assn \<times>\<^sub>a arena_fast_assn \<times>\<^sub>a
  conflict_option_rel_assn \<times>\<^sub>a
  sint64_nat_assn \<times>\<^sub>a
  watchlist_fast_assn \<times>\<^sub>a
  vmtf_remove_assn \<times>\<^sub>a
  uint32_nat_assn \<times>\<^sub>a
  cach_refinement_l_assn \<times>\<^sub>a
  lbd_assn \<times>\<^sub>a
  out_learned_assn \<times>\<^sub>a
  stats_assn \<times>\<^sub>a
  heuristic_assn \<times>\<^sub>a
  vdom_fast_assn \<times>\<^sub>a
  vdom_fast_assn \<times>\<^sub>a
  lcount_assn \<times>\<^sub>a
  opts_assn \<times>\<^sub>a arena_fast_assn\<close>



subsubsection \<open>Lift Operations to State\<close>

(*TODO proper setup to test if the conflict is none*)
sepref_def get_conflict_wl_is_None_fast_code
  is \<open>RETURN o get_conflict_wl_is_None_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding get_conflict_wl_is_None_heur_alt_def isasat_bounded_assn_def length_ll_def[symmetric]
    conflict_option_rel_assn_def
  supply [[goals_limit=1]]
  by sepref


sepref_def isa_count_decided_st_fast_code
  is \<open>RETURN o isa_count_decided_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=2]]
  unfolding isa_count_decided_st_def isasat_bounded_assn_def
  by sepref

sepref_def polarity_st_heur_pol_fast
  is \<open>uncurry (mop_polarity_st_heur)\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a tri_bool_assn\<close>
  unfolding mop_polarity_st_heur_alt_def isasat_bounded_assn_def polarity_st_pre_def
    mop_polarity_st_heur_alt_def
  supply [[goals_limit = 1]]
  by sepref


subsection \<open>More theorems\<close>

lemma count_decided_st_heur_alt_def:
   \<open>count_decided_st_heur = (\<lambda>(M, _). count_decided_pol M)\<close>
  by (auto simp: count_decided_st_heur_def count_decided_pol_def)

sepref_def count_decided_st_heur_pol_fast
  is \<open>RETURN o count_decided_st_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding isasat_bounded_assn_def count_decided_st_heur_alt_def
  supply [[goals_limit = 1]]
  by sepref

sepref_def access_lit_in_clauses_heur_fast_code
  is \<open>uncurry2 (RETURN ooo access_lit_in_clauses_heur)\<close>
  :: \<open>[\<lambda>((S, i), j). access_lit_in_clauses_heur_pre ((S, i), j) \<and>
           length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a
      isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k  *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  supply [[goals_limit=1]] arena_lit_pre_le[dest]
  unfolding isasat_bounded_assn_def access_lit_in_clauses_heur_alt_def
    access_lit_in_clauses_heur_pre_def
  unfolding fold_tuple_optimizations
  by sepref

sepref_def rewatch_heur_st_fast_code
  is \<open>(rewatch_heur_st_fast)\<close>
  :: \<open>[rewatch_heur_st_fast_pre]\<^sub>a
       isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding rewatch_heur_st_def PR_CONST_def rewatch_heur_st_fast_pre_def
    isasat_bounded_assn_def rewatch_heur_st_fast_def
  unfolding fold_tuple_optimizations
  by sepref


sepref_register length_avdom

sepref_def length_avdom_fast_code
  is \<open>RETURN o length_avdom\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  unfolding length_avdom_alt_def isasat_bounded_assn_def fold_tuple_optimizations
  supply [[goals_limit = 1]]
  by sepref

sepref_register get_the_propagation_reason_heur

sepref_def get_the_propagation_reason_heur_fast_code
  is \<open>uncurry get_the_propagation_reason_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a snat_option_assn' TYPE(64)\<close>
  unfolding get_the_propagation_reason_heur_alt_def
     isasat_bounded_assn_def fold_tuple_optimizations
  supply [[goals_limit = 1]]
  by sepref


sepref_def clause_is_learned_heur_code2
  is \<open>uncurry (RETURN oo clause_is_learned_heur)\<close>
  :: \<open>[\<lambda>(S, C). arena_is_valid_clause_vdom (get_clauses_wl_heur S) C]\<^sub>a
      isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> bool1_assn\<close>
  supply [[goals_limit = 1]]
  unfolding clause_is_learned_heur_alt_def isasat_bounded_assn_def fold_tuple_optimizations
  by sepref

sepref_register clause_lbd_heur


lemma clause_lbd_heur_alt_def:
  \<open>clause_lbd_heur = (\<lambda>(M', N', D', j, W', vm, clvls, cach, lbd, outl, stats, heur, vdom,
     lcount) C.
     arena_lbd N' C)\<close>
  by (intro ext) (auto simp: clause_lbd_heur_def)

sepref_def clause_lbd_heur_code2
  is \<open>uncurry (RETURN oo clause_lbd_heur)\<close>
  :: \<open>[\<lambda>(S, C). get_clause_LBD_pre (get_clauses_wl_heur S) C]\<^sub>a
       isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  unfolding isasat_bounded_assn_def clause_lbd_heur_alt_def fold_tuple_optimizations
  supply [[goals_limit = 1]]
  by sepref



sepref_register mark_garbage_heur


sepref_def mark_garbage_heur_code2
  is \<open>uncurry2 (RETURN ooo mark_garbage_heur)\<close>
  :: \<open>[\<lambda>((C, i), S). mark_garbage_pre (get_clauses_wl_heur S, C) \<and> i < length_avdom S \<and>
         clss_size_lcount (get_learned_count S) \<ge> 1]\<^sub>a
       sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit = 1]]
  unfolding mark_garbage_heur_def isasat_bounded_assn_def delete_index_and_swap_alt_def
    length_avdom_def fold_tuple_optimizations clss_size_decr_lcount_def clss_size_lcount_def
    lcount_assn_def fold_tuple_optimizations
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_register delete_index_vdom_heur


sepref_def delete_index_vdom_heur_fast_code2
  is \<open>uncurry (RETURN oo delete_index_vdom_heur)\<close>
  :: \<open>[\<lambda>(i, S). i < length_avdom S]\<^sub>a
        sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit = 1]]
  unfolding delete_index_vdom_heur_def isasat_bounded_assn_def delete_index_and_swap_alt_def
    length_avdom_def fold_tuple_optimizations
  by sepref

sepref_register access_length_heur

sepref_def access_length_heur_fast_code2
  is \<open>uncurry (RETURN oo access_length_heur)\<close>
  :: \<open>[\<lambda>(S, C). arena_is_valid_clause_idx (get_clauses_wl_heur S) C]\<^sub>a
       isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> sint64_nat_assn\<close>
  supply [[goals_limit = 1]]
  unfolding access_length_heur_alt_def isasat_bounded_assn_def fold_tuple_optimizations
  by sepref

sepref_register marked_as_used_st

sepref_def marked_as_used_st_fast_code
  is \<open>uncurry (RETURN oo marked_as_used_st)\<close>
  :: \<open>[\<lambda>(S, C). marked_as_used_pre (get_clauses_wl_heur S) C]\<^sub>a
       isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> unat_assn' TYPE(2)\<close>
  supply [[goals_limit = 1]]
  unfolding marked_as_used_st_alt_def isasat_bounded_assn_def fold_tuple_optimizations
  by sepref


sepref_register mark_unused_st_heur
sepref_def mark_unused_st_fast_code
  is \<open>uncurry (RETURN oo mark_unused_st_heur)\<close>
  :: \<open>[\<lambda>(C, S). arena_act_pre (get_clauses_wl_heur S) C]\<^sub>a
        sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding mark_unused_st_heur_def isasat_bounded_assn_def
    arena_act_pre_mark_used[intro!] fold_tuple_optimizations
  supply [[goals_limit = 1]]
  by sepref


sepref_def get_slow_ema_heur_fast_code
  is \<open>RETURN o get_slow_ema_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  unfolding get_slow_ema_heur_alt_def isasat_bounded_assn_def heuristic_assn_def fold_tuple_optimizations
  by sepref

sepref_def get_fast_ema_heur_fast_code
  is \<open>RETURN o get_fast_ema_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  unfolding get_fast_ema_heur_alt_def isasat_bounded_assn_def heuristic_assn_def fold_tuple_optimizations
  by sepref

sepref_def get_conflict_count_since_last_restart_heur_fast_code
  is \<open>RETURN o get_conflict_count_since_last_restart_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding get_counflict_count_heur_alt_def isasat_bounded_assn_def heuristic_assn_def fold_tuple_optimizations
  by sepref

sepref_def get_learned_count_fast_code
  is \<open>RETURN o get_learned_count\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a lcount_assn\<close>
  unfolding get_learned_count_alt_def isasat_bounded_assn_def fold_tuple_optimizations
  by sepref

sepref_register clss_size_lcount get_learned_count_number


lemma get_learned_count_number_alt_def:
   \<open>RETURN o get_learned_count_number = (\<lambda>(M, N0, D, Q, W, vm, clvls, cach, lbd, outl,
       stats, _, vdom, avdom, (lcount, _), opts). RETURN (lcount))\<close>
  by (auto simp: clss_size_lcount_def intro!: ext)


sepref_def get_learned_count_number_fast_code
  is \<open>RETURN o get_learned_count_number\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  unfolding isasat_bounded_assn_def get_learned_count_number_alt_def lcount_assn_def
  by sepref

sepref_register incr_restart_stat

sepref_def learned_clss_count_fast_code
  is \<open>RETURN o learned_clss_count\<close>
  :: \<open>[\<lambda>S. learned_clss_count S \<le> uint64_max]\<^sub>a isasat_bounded_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  unfolding clss_size_allcount_alt_def learned_clss_count_def fold_tuple_optimizations
  by sepref

sepref_register clss_size_lcountUE clss_size_lcountUS learned_clss_count clss_size_allcount

sepref_def incr_restart_stat_fast_code
  is \<open>incr_restart_stat\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding incr_restart_stat_def isasat_bounded_assn_def PR_CONST_def
    heuristic_assn_def fold_tuple_optimizations
  by sepref

sepref_register incr_lrestart_stat clss_size_decr_lcount
    clss_size_incr_lcountUE clss_size_incr_lcountUS

sepref_def incr_lrestart_stat_fast_code
  is \<open>incr_lrestart_stat\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding incr_lrestart_stat_def isasat_bounded_assn_def PR_CONST_def
    heuristic_assn_def fold_tuple_optimizations
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

sepref_def opts_unbounded_mode_st_fast_code
  is \<open>RETURN o opts_unbounded_mode_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  supply [[goals_limit=1]]
  unfolding opts_unbounded_mode_st_def isasat_bounded_assn_def
  by sepref

sepref_def opts_minimum_between_restart_st_fast_code
  is \<open>RETURN o opts_minimum_between_restart_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding opts_minimum_between_restart_st_def isasat_bounded_assn_def
  by sepref

sepref_def opts_restart_coeff1_st_fast_code
  is \<open>RETURN o opts_restart_coeff1_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding opts_restart_coeff1_st_def isasat_bounded_assn_def
  by sepref

sepref_def opts_restart_coeff2_st_fast_code
  is \<open>RETURN o opts_restart_coeff2_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a snat_assn' (TYPE(64))\<close>
  unfolding opts_restart_coeff2_st_def isasat_bounded_assn_def
  by sepref

sepref_register opts_reduction_st opts_restart_st opts_restart_coeff2_st opts_restart_coeff1_st
    opts_minimum_between_restart_st opts_unbounded_mode_st

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


lemma clause_not_marked_to_delete_heur_alt_def:
  \<open>RETURN oo clause_not_marked_to_delete_heur = (\<lambda>(M, arena, D, oth) C.
      RETURN (arena_status arena C \<noteq> DELETED))\<close>
  unfolding clause_not_marked_to_delete_heur_def by (auto intro!: ext)

sepref_def clause_not_marked_to_delete_heur_fast_code
  is \<open>uncurry (RETURN oo clause_not_marked_to_delete_heur)\<close>
  :: \<open>[clause_not_marked_to_delete_heur_pre]\<^sub>a isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> bool1_assn\<close>
  supply [[goals_limit=1]]
  unfolding clause_not_marked_to_delete_heur_alt_def isasat_bounded_assn_def
     clause_not_marked_to_delete_heur_pre_def
  by sepref

lemma mop_clause_not_marked_to_delete_heur_alt_def:
  \<open>mop_clause_not_marked_to_delete_heur = (\<lambda>(M, arena, D, oth) C. do {
    ASSERT(clause_not_marked_to_delete_heur_pre ((M, arena, D, oth), C));
     RETURN (arena_status arena C \<noteq> DELETED)
   })\<close>
  unfolding clause_not_marked_to_delete_heur_def mop_clause_not_marked_to_delete_heur_def
  by (auto intro!: ext)

sepref_def mop_clause_not_marked_to_delete_heur_impl
  is \<open>uncurry mop_clause_not_marked_to_delete_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding mop_clause_not_marked_to_delete_heur_alt_def
    clause_not_marked_to_delete_heur_pre_def  prod.case isasat_bounded_assn_def
  by sepref

sepref_def delete_index_and_swap_code2
  is \<open>uncurry (RETURN oo delete_index_and_swap)\<close>
  :: \<open>[\<lambda>(xs, i). i < length xs]\<^sub>a
      vdom_fast_assn\<^sup>d *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> vdom_fast_assn\<close>
  unfolding delete_index_and_swap.simps
  by sepref

sepref_def mop_mark_garbage_heur_impl
  is \<open>uncurry2 mop_mark_garbage_heur\<close>
  :: \<open>[\<lambda>((C, i), S). length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a
      sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding mop_mark_garbage_heur_alt_def
    clause_not_marked_to_delete_heur_pre_def prod.case isasat_bounded_assn_def
    get_clauses_wl_heur.simps
  apply (rewrite in \<open>RETURN \<hole>\<close> fold_tuple_optimizations)
  by sepref

sepref_def mop_mark_unused_st_heur_impl
  is \<open>uncurry mop_mark_unused_st_heur\<close>
  :: \<open> sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding mop_mark_unused_st_heur_def fold_tuple_optimizations
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
  unfolding incr_wasted_st_def incr_wasted.simps
    isasat_bounded_assn_def heuristic_assn_def fold_tuple_optimizations
  by sepref

sepref_def full_arena_length_st_impl
  is \<open>RETURN o full_arena_length_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  unfolding full_arena_length_st_def isasat_bounded_assn_def
  by sepref


sepref_def wasted_bytes_st_impl
  is \<open>RETURN o wasted_bytes_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_bounded_assn_def
    heuristic_assn_def wasted_bytes_st_def
  by sepref

lemma set_zero_wasted_def:
  \<open>set_zero_wasted = (\<lambda>(fast_ema, slow_ema, res_info, wasted, \<phi>).
    (fast_ema, slow_ema, res_info, 0, \<phi>))\<close>
  by (auto intro!: ext)

sepref_def set_zero_wasted_impl
  is \<open>RETURN o set_zero_wasted\<close>
  :: \<open>heuristic_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_assn\<close>
  unfolding heuristic_assn_def set_zero_wasted_def
  by sepref

lemma mop_save_phase_heur_alt_def:
  \<open>mop_save_phase_heur = (\<lambda> L b (fast_ema, slow_ema, res_info, wasted, \<phi>, target, best). do {
    ASSERT(L < length \<phi>);
    RETURN (fast_ema, slow_ema, res_info, wasted, \<phi>[L := b], target,
                 best)})\<close>
  unfolding mop_save_phase_heur_def save_phase_heur_def save_phase_heur_pre_def
    heuristic_assn_def
  by (auto intro!: ext)

sepref_def mop_save_phase_heur_impl
  is \<open>uncurry2 (mop_save_phase_heur)\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a heuristic_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_assn\<close>
  supply [[goals_limit=1]]
  unfolding mop_save_phase_heur_alt_def save_phase_heur_def save_phase_heur_pre_def
    heuristic_assn_def phase_heur_assn_def
  apply annot_all_atm_idxs
  by sepref


lemma id_unat[sepref_fr_rules]:
   \<open>(return o id, RETURN o unat) \<in> word32_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  apply sepref_to_hoare
  apply vcg
  by (auto simp: ENTAILS_def unat_rel_def unat.rel_def br_def pred_lift_merge_simps
     pred_lift_def pure_true_conv)

sepref_register set_zero_wasted mop_save_phase_heur add_lbd


sepref_def add_lbd_impl
  is \<open>uncurry (RETURN oo add_lbd)\<close>
  :: \<open>word32_assn\<^sup>k *\<^sub>a stats_assn\<^sup>d \<rightarrow>\<^sub>a stats_assn\<close>
  supply [[goals_limit=1]]
  unfolding add_lbd_def
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

sepref_def empty_US_heur_code
  is \<open>RETURN o empty_US_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding empty_US_heur_def isasat_bounded_assn_def
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


experiment begin

export_llvm
  ema_update_impl
  VMTF_Node_impl
  VMTF_stamp_impl
  VMTF_get_prev_impl
  VMTF_get_next_impl
  get_conflict_wl_is_None_fast_code
  isa_count_decided_st_fast_code
  polarity_st_heur_pol_fast
  count_decided_st_heur_pol_fast
  access_lit_in_clauses_heur_fast_code
  rewatch_heur_fast_code
  rewatch_heur_st_fast_code
  set_zero_wasted_impl
  opts_restart_st_fast_code
  opts_unbounded_mode_st_fast_code

end

end

