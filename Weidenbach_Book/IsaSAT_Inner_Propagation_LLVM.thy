theory IsaSAT_Inner_Propagation_LLVM
  imports IsaSAT_Setup_LLVM
     IsaSAT_Inner_Propagation
begin

sepref_register isa_save_pos

sepref_definition isa_save_pos_fast_code
  is \<open>uncurry2 isa_save_pos\<close>
  :: \<open>sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply
    [[goals_limit=1]]
    if_splits[split]
  unfolding isa_save_pos_def PR_CONST_def isasat_bounded_assn_def
  by sepref

declare isa_save_pos_fast_code.refine[sepref_fr_rules]

lemma [def_pat_rules]: \<open>nth_rll \<equiv> op_list_list_idx\<close>
 by (auto simp: nth_rll_def intro!: ext eq_reflection)

sepref_definition watched_by_app_heur_fast_code
  is \<open>uncurry2 (RETURN ooo watched_by_app_heur)\<close>
  :: \<open>[watched_by_app_heur_pre]\<^sub>a
        isasat_bounded_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> watcher_fast_assn\<close>
  supply [[goals_limit=1]]
  unfolding watched_by_app_heur_alt_def isasat_bounded_assn_def nth_rll_def[symmetric]
   watched_by_app_heur_pre_def
  by sepref

declare watched_by_app_heur_fast_code.refine[sepref_fr_rules]


(* TODO most of the unfolding should move to the definition *)
sepref_register isa_find_unwatched_wl_st_heur isa_find_unwatched_between isa_find_unset_lit
  polarity_pol


term snat.option_assn
sepref_definition isa_find_unwatched_between_fast_code
  is \<open>uncurry4 isa_find_unset_lit\<close>
  :: \<open>[\<lambda>((((M, N), _), _), _). length N \<le> sint64_max]\<^sub>a
     trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>
       snat_option_assn' TYPE(64)\<close>
  supply [[goals_limit = 1]]
  unfolding isa_find_unset_lit_def isa_find_unwatched_between_def SET_FALSE_def[symmetric]
    PR_CONST_def
  apply (rewrite in \<open>if \<hole> then _ else _\<close>  eq_commute)
  apply (rewrite in \<open>if \<hole> then _ else _\<close>  tri_bool_eq_def[symmetric])
apply sepref_dbg_keep
apply sepref_dbg_id_init
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_id_step
apply sepref_dbg_trans_keep
apply sepref_dbg_trans_step_keep
apply sepref_dbg_side_unfold
oops
  by sepref

declare isa_find_unwatched_between_fast_code.refine[sepref_fr_rules]

declare get_saved_pos_code[sepref_fr_rules]

sepref_definition find_unwatched_wl_st_heur_fast_code
  is \<open>uncurry isa_find_unwatched_wl_st_heur\<close>
  :: \<open>[(\<lambda>(S, C). find_unwatched_wl_st_heur_pre (S, C) \<and>
            length (get_clauses_wl_heur S) \<le> uint64_max)]\<^sub>a
         isasat_bounded_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> option_assn uint64_nat_assn\<close>
  supply [[goals_limit = 1]]
    fmap_length_rll_def[simp]
    uint64_of_uint32_conv_hnr[sepref_fr_rules] isasat_fast_def[simp]
  unfolding isa_find_unwatched_wl_st_heur_def PR_CONST_def
    find_unwatched_def fmap_rll_def[symmetric] isasat_bounded_assn_def
    length_uint32_nat_def[symmetric] isa_find_unwatched_def
    case_tri_bool_If find_unwatched_wl_st_heur_pre_def
    fmap_rll_u64_def[symmetric]
    MAX_LENGTH_SHORT_CLAUSE_def[symmetric]
    two_uint64_nat_def[symmetric]
    nat_of_uint64_conv_def
  apply (subst isa_find_unset_lit_def[symmetric])+
  by sepref

declare find_unwatched_wl_st_heur_fast_code.refine[sepref_fr_rules]


sepref_register update_clause_wl_heur
sepref_definition update_clause_wl_code
  is \<open>uncurry7 update_clause_wl_heur\<close>
  :: \<open>[update_clause_wl_code_pre]\<^sub>a
     unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a bool_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k
        *\<^sub>a isasat_unbounded_assn\<^sup>d \<rightarrow> nat_assn *a nat_assn *a isasat_unbounded_assn\<close>
  supply [[goals_limit=1]] length_rll_def[simp] length_ll_def[simp]
    update_clause_wl_heur_pre_le_uint64[intro!]
  unfolding update_clause_wl_heur_def isasat_unbounded_assn_def Array_List_Array.swap_ll_def[symmetric]
    fmap_rll_def[symmetric] delete_index_and_swap_update_def[symmetric]
    delete_index_and_swap_ll_def[symmetric] fmap_swap_ll_def[symmetric]
    append_ll_def[symmetric] update_clause_wl_code_pre_def
    fmap_rll_u64_def[symmetric]
    fmap_swap_ll_u64_def[symmetric]
    fmap_swap_ll_def[symmetric]
    PR_CONST_def
  by sepref

declare update_clause_wl_code.refine[sepref_fr_rules]

sepref_definition update_clause_wl_fast_code
  is \<open>uncurry7 update_clause_wl_heur\<close>
  :: \<open>[\<lambda>(((((((L, C), b), j), w), i), f), S). update_clause_wl_code_pre (((((((L, C), b), j), w), i), f), S) \<and>
        length (get_clauses_wl_heur S) \<le> uint64_max]\<^sub>a
     unat_lit_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a bool_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a
       uint64_nat_assn\<^sup>k
        *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> uint64_nat_assn *a uint64_nat_assn *a isasat_bounded_assn\<close>
  supply [[goals_limit=1]] length_rll_def[simp] length_ll_def[simp]
    update_clause_wl_heur_pre_le_uint64[intro]
  unfolding update_clause_wl_heur_def isasat_bounded_assn_def Array_List_Array.swap_ll_def[symmetric]
    fmap_rll_def[symmetric] delete_index_and_swap_update_def[symmetric]
    delete_index_and_swap_ll_def[symmetric] fmap_swap_ll_def[symmetric]
    append_ll_def[symmetric] update_clause_wl_code_pre_def
    fmap_rll_u64_def[symmetric]
    fmap_swap_ll_u64_def[symmetric]
    fmap_swap_ll_def[symmetric]
    PR_CONST_def
    to_watcher_fast_def[symmetric]
    one_uint64_nat_def[symmetric]
  by sepref

declare update_clause_wl_fast_code.refine[sepref_fr_rules]

sepref_definition propagate_lit_wl_code
  is \<open>uncurry3 propagate_lit_wl_heur\<close>
  :: \<open>[propagate_lit_wl_heur_pre]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a isasat_unbounded_assn\<^sup>d \<rightarrow> isasat_unbounded_assn\<close>
  unfolding PR_CONST_def propagate_lit_wl_heur_def isasat_unbounded_assn_def
    cons_trail_Propagated_def[symmetric]
  supply [[goals_limit=1]]length_rll_def[simp] length_ll_def[simp]
  unfolding update_clause_wl_heur_def isasat_unbounded_assn_def
    propagate_lit_wl_heur_pre_def fmap_swap_ll_def[symmetric]
    save_phase_def
  apply (rewrite at \<open>count_decided_pol _ = \<hole>\<close> zero_uint32_nat_def[symmetric])
  by sepref

declare propagate_lit_wl_code.refine[sepref_fr_rules]

sepref_definition propagate_lit_wl_fast_code
  is \<open>uncurry3 propagate_lit_wl_heur\<close>
  :: \<open>[\<lambda>(((L, C), i), S). propagate_lit_wl_heur_pre(((L, C), i), S) \<and>
      length (get_clauses_wl_heur S) \<le> uint64_max]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding PR_CONST_def propagate_lit_wl_heur_def isasat_unbounded_assn_def
    cons_trail_Propagated_def[symmetric]
  supply [[goals_limit=1]] length_rll_def[simp] length_ll_def[simp]
  unfolding update_clause_wl_heur_def isasat_bounded_assn_def
    propagate_lit_wl_heur_pre_def fmap_swap_ll_def[symmetric]
    fmap_swap_ll_u64_def[symmetric]
    zero_uint64_nat_def[symmetric]
    one_uint64_nat_def[symmetric]
    save_phase_def
  apply (rewrite at \<open>count_decided_pol _ = \<hole>\<close> zero_uint64_nat_def)
  apply (rewrite at \<open>count_decided_pol _ = \<hole>\<close> zero_uint32_nat_def[symmetric])
  by sepref

declare propagate_lit_wl_fast_code.refine[sepref_fr_rules]


sepref_definition propagate_lit_wl_bin_code
  is \<open>uncurry3 propagate_lit_wl_bin_heur\<close>
  :: \<open>[propagate_lit_wl_heur_pre]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a isasat_unbounded_assn\<^sup>d \<rightarrow> isasat_unbounded_assn\<close>
  unfolding PR_CONST_def propagate_lit_wl_heur_def isasat_unbounded_assn_def
    cons_trail_Propagated_def[symmetric]
  supply [[goals_limit=1]]length_rll_def[simp] length_ll_def[simp]
  unfolding update_clause_wl_heur_def isasat_unbounded_assn_def
    propagate_lit_wl_heur_pre_def fmap_swap_ll_def[symmetric]
    save_phase_def propagate_lit_wl_bin_heur_def
  apply (rewrite at \<open>count_decided_pol _ = \<hole>\<close> zero_uint32_nat_def[symmetric])
  by sepref

declare propagate_lit_wl_bin_code.refine[sepref_fr_rules]

sepref_definition propagate_lit_wl_bin_fast_code
  is \<open>uncurry3 propagate_lit_wl_bin_heur\<close>
  :: \<open>[\<lambda>(((L, C), i), S). propagate_lit_wl_heur_pre(((L, C), i), S) \<and>
      length (get_clauses_wl_heur S) \<le> uint64_max]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>
      isasat_bounded_assn\<close>
  unfolding PR_CONST_def propagate_lit_wl_heur_def isasat_unbounded_assn_def
    cons_trail_Propagated_def[symmetric]
  supply [[goals_limit=1]] length_rll_def[simp] length_ll_def[simp]
  unfolding update_clause_wl_heur_def isasat_bounded_assn_def
    propagate_lit_wl_heur_pre_def fmap_swap_ll_def[symmetric]
    fmap_swap_ll_u64_def[symmetric]
    zero_uint64_nat_def[symmetric]
    one_uint64_nat_def[symmetric]
    save_phase_def propagate_lit_wl_bin_heur_def
  apply (rewrite at \<open>count_decided_pol _ = \<hole>\<close> zero_uint64_nat_def)
  apply (rewrite at \<open>count_decided_pol _ = \<hole>\<close> zero_uint32_nat_def[symmetric])
  by sepref

declare propagate_lit_wl_bin_fast_code.refine[sepref_fr_rules]


sepref_definition clause_not_marked_to_delete_heur_code
  is \<open>uncurry (RETURN oo clause_not_marked_to_delete_heur)\<close>
  :: \<open>[clause_not_marked_to_delete_heur_pre]\<^sub>a isasat_unbounded_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> bool_assn\<close>
  supply [[goals_limit=1]]
  unfolding clause_not_marked_to_delete_heur_alt_def isasat_unbounded_assn_def
     clause_not_marked_to_delete_heur_pre_def
  by sepref

declare clause_not_marked_to_delete_heur_code.refine[sepref_fr_rules]

sepref_definition clause_not_marked_to_delete_heur_fast_code
  is \<open>uncurry (RETURN oo clause_not_marked_to_delete_heur)\<close>
  :: \<open>[clause_not_marked_to_delete_heur_pre]\<^sub>a isasat_bounded_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> bool_assn\<close>
  supply [[goals_limit=1]]
  unfolding clause_not_marked_to_delete_heur_alt_def isasat_bounded_assn_def
     clause_not_marked_to_delete_heur_pre_def
  by sepref

declare clause_not_marked_to_delete_heur_fast_code.refine[sepref_fr_rules]

sepref_definition update_blit_wl_heur_code
  is \<open>uncurry6 update_blit_wl_heur\<close>
  :: \<open>
      unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a bool_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a
     nat_assn *a nat_assn *a isasat_unbounded_assn\<close>
  supply [[goals_limit=1]] length_ll_def[simp]
  unfolding update_blit_wl_heur_def isasat_unbounded_assn_def update_ll_def[symmetric]
  by sepref

declare update_blit_wl_heur_code.refine[sepref_fr_rules]

sepref_definition update_blit_wl_heur_fast_code
  is \<open>uncurry6 update_blit_wl_heur\<close>
  :: \<open>[\<lambda>((((((_, _), _), _), C), i), S). length (get_clauses_wl_heur S) \<le> uint64_max]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a bool_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a
         isasat_bounded_assn\<^sup>d \<rightarrow>
     uint64_nat_assn *a uint64_nat_assn *a isasat_bounded_assn\<close>
  supply [[goals_limit=1]] length_ll_def[simp]
  unfolding update_blit_wl_heur_def isasat_bounded_assn_def update_ll_def[symmetric]
    to_watcher_fast_def[symmetric] one_uint64_nat_def[symmetric]
  by sepref

declare update_blit_wl_heur_fast_code.refine[sepref_fr_rules]

sepref_register keep_watch_heur

sepref_definition keep_watch_heur_code
  is \<open>uncurry3 keep_watch_heur\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply [[goals_limit=1]]
    if_splits[split]
    length_rll_def[simp] length_ll_def[simp]
  supply undefined_lit_polarity_st_iff[iff]
    unit_prop_body_wl_D_find_unwatched_heur_inv_def[simp]
    update_raa_hnr[sepref_fr_rules]
  unfolding keep_watch_heur_def length_rll_def[symmetric] PR_CONST_def
  unfolding fmap_rll_def[symmetric] isasat_unbounded_assn_def
  unfolding fast_minus_def[symmetric]
    nth_rll_def[symmetric]
    SET_FALSE_def[symmetric] SET_TRUE_def[symmetric]
    update_ll_def[symmetric]
  by sepref

declare keep_watch_heur_code.refine[sepref_fr_rules]

sepref_definition keep_watch_heur_fast_code
  is \<open>uncurry3 keep_watch_heur\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply
    [[goals_limit=1]]
    if_splits[split]
    length_rll_def[simp] length_ll_def[simp]
  supply undefined_lit_polarity_st_iff[iff]
    unit_prop_body_wl_D_find_unwatched_heur_inv_def[simp]
    update_raa_hnr[sepref_fr_rules]
  unfolding keep_watch_heur_def length_rll_def[symmetric] PR_CONST_def
  unfolding fmap_rll_def[symmetric] isasat_bounded_assn_def
  unfolding fast_minus_def[symmetric]
    nth_rll_def[symmetric]
    SET_FALSE_def[symmetric] SET_TRUE_def[symmetric]
    update_ll_def[symmetric]
  by sepref

declare keep_watch_heur_fast_code.refine[sepref_fr_rules]

sepref_register isa_set_lookup_conflict_aa set_conflict_wl_heur
sepref_definition set_conflict_wl_heur_code
  is \<open>uncurry set_conflict_wl_heur\<close>
  :: \<open>[set_conflict_wl_heur_pre]\<^sub>a
    nat_assn\<^sup>k *\<^sub>a isasat_unbounded_assn\<^sup>d \<rightarrow> isasat_unbounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding set_conflict_wl_heur_def isasat_unbounded_assn_def
    set_conflict_wl_heur_pre_def PR_CONST_def
  by sepref

declare set_conflict_wl_heur_code.refine[sepref_fr_rules]

sepref_register arena_incr_act

sepref_definition set_conflict_wl_heur_fast_code
  is \<open>uncurry set_conflict_wl_heur\<close>
  :: \<open>[\<lambda>(C, S). set_conflict_wl_heur_pre (C, S) \<and>
     length (get_clauses_wl_heur S) \<le> uint64_max]\<^sub>a
    uint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding set_conflict_wl_heur_def isasat_bounded_assn_def
    set_conflict_wl_heur_pre_def PR_CONST_def
  by sepref

declare set_conflict_wl_heur_fast_code.refine[sepref_fr_rules]


text \<open>Find a less hack-like solution\<close>
setup \<open>map_theory_claset (fn ctxt => ctxt delSWrapper "split_all_tac")\<close>

sepref_register update_blit_wl_heur clause_not_marked_to_delete_heur
sepref_definition unit_propagation_inner_loop_body_wl_heur_code
  is \<open>uncurry3 unit_propagation_inner_loop_body_wl_heur\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a nat_assn *a nat_assn *a isasat_unbounded_assn\<close>
  supply
    [[goals_limit=1]]
    if_splits[split]
    length_rll_def[simp]
  supply undefined_lit_polarity_st_iff[iff]
    unit_prop_body_wl_D_find_unwatched_heur_inv_def[simp]
    unit_propagation_inner_loop_wl_loop_D_heur_inv0_def[simp]
    unit_propagation_inner_loop_wl_loop_D_inv_def[simp]
    image_image[simp]
  unfolding unit_propagation_inner_loop_body_wl_heur_def length_rll_def[symmetric] PR_CONST_def
  unfolding fmap_rll_def[symmetric]
  unfolding fast_minus_def[symmetric]
    SET_FALSE_def[symmetric] SET_TRUE_def[symmetric] tri_bool_eq_def[symmetric]
  by sepref

sepref_definition unit_propagation_inner_loop_body_wl_fast_heur_code
  is \<open>uncurry3 unit_propagation_inner_loop_body_wl_heur\<close>
  :: \<open>[\<lambda>((L, w), S). length (get_clauses_wl_heur S) \<le> uint64_max]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k  *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>
       uint64_nat_assn *a uint64_nat_assn *a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
    if_splits[split]
    length_rll_def[simp]
  supply undefined_lit_polarity_st_iff[iff]
    unit_prop_body_wl_D_find_unwatched_heur_inv_def[simp]
  unfolding unit_propagation_inner_loop_body_wl_heur_def length_rll_def[symmetric] PR_CONST_def
  unfolding fmap_rll_def[symmetric]
  unfolding fast_minus_def[symmetric]
    SET_FALSE_def[symmetric] SET_TRUE_def[symmetric] tri_bool_eq_def[symmetric]
  apply (rewrite in \<open>access_lit_in_clauses_heur _ _ \<hole>\<close> zero_uint64_nat_def[symmetric])+
  apply (rewrite in \<open>If _ \<hole> 1\<close> zero_uint64_nat_def[symmetric])
  apply (rewrite in \<open>If _ zero_uint64_nat \<hole>\<close> one_uint64_nat_def[symmetric])
  apply (rewrite in \<open>If _ \<hole> 1\<close> zero_uint64_nat_def[symmetric])
  apply (rewrite in \<open>If _ zero_uint64_nat \<hole>\<close> one_uint64_nat_def[symmetric])
  apply (rewrite in \<open>fast_minus \<hole> _\<close> one_uint64_nat_def[symmetric])
  apply (rewrite in \<open>fast_minus \<hole> _\<close> one_uint64_nat_def[symmetric])
  unfolding one_uint64_nat_def[symmetric]
  by sepref

sepref_register unit_propagation_inner_loop_body_wl_heur

declare unit_propagation_inner_loop_body_wl_heur_code.refine[sepref_fr_rules]
  unit_propagation_inner_loop_body_wl_fast_heur_code.refine[sepref_fr_rules]
declare [[show_types]]
thm unit_propagation_inner_loop_body_wl_fast_heur_code_def
end
