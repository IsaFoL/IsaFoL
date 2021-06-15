theory IsaSAT_Inner_Propagation_LLVM
  imports IsaSAT_Setup_LLVM
     IsaSAT_Inner_Propagation
begin

sepref_register isa_save_pos

sepref_def isa_save_pos_fast_code
  is \<open>uncurry2 isa_save_pos\<close>
  :: \<open>sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply
    [[goals_limit=1]]
    if_splits[split]
  unfolding isa_save_pos_def PR_CONST_def isasat_bounded_assn_def
  by sepref


lemma [def_pat_rules]: \<open>nth_rll \<equiv> op_list_list_idx\<close>
 by (auto simp: nth_rll_def intro!: ext eq_reflection)

sepref_def watched_by_app_heur_fast_code
  is \<open>uncurry2 (RETURN ooo watched_by_app_heur)\<close>
  :: \<open>[watched_by_app_heur_pre]\<^sub>a
        isasat_bounded_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> watcher_fast_assn\<close>
  supply [[goals_limit=1]]
  unfolding watched_by_app_heur_alt_def isasat_bounded_assn_def nth_rll_def[symmetric]
   watched_by_app_heur_pre_def
  by sepref


(* TODO most of the unfolding should move to the definition *)
sepref_register isa_find_unwatched_wl_st_heur isa_find_unwatched_between isa_find_unset_lit
  polarity_pol

(*TODO dup*)
sepref_register 0 1

(*lemma \<open>found = None \<longleftrightarrow> is_None (ASSN_ANNOT (snat_option_assn' TYPE(64)) found)\<close>*)

sepref_def isa_find_unwatched_between_fast_code
  is \<open>uncurry4 isa_find_unset_lit\<close>
  :: \<open>[\<lambda>((((M, N), _), _), _). length N \<le> sint64_max]\<^sub>a
     trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>
       snat_option_assn' TYPE(64)\<close>
  supply [[goals_limit = 3]]
  unfolding isa_find_unset_lit_def isa_find_unwatched_between_def SET_FALSE_def[symmetric]
    PR_CONST_def
  apply (rewrite in \<open>if \<hole> then _ else _\<close> tri_bool_eq_def[symmetric])
  apply (annot_snat_const \<open>TYPE (64)\<close>)
  by sepref

sepref_register mop_arena_pos mop_arena_lit2
sepref_def mop_arena_pos_impl
  is \<open>uncurry mop_arena_pos\<close>
  :: \<open>arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  unfolding mop_arena_pos_def
  by sepref

sepref_def swap_lits_impl is \<open>uncurry3 mop_arena_swap\<close>
  :: \<open>sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>d \<rightarrow>\<^sub>a arena_fast_assn\<close>
  unfolding mop_arena_swap_def swap_lits_pre_def
  unfolding gen_swap
  by sepref

sepref_def find_unwatched_wl_st_heur_fast_code
  is \<open>uncurry isa_find_unwatched_wl_st_heur\<close>
  :: \<open>[(\<lambda>(S, C). length (get_clauses_wl_heur S) \<le> sint64_max)]\<^sub>a
         isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> snat_option_assn' TYPE(64)\<close>
  supply [[goals_limit = 1]] isasat_fast_def[simp]
  unfolding isa_find_unwatched_wl_st_heur_def PR_CONST_def
    find_unwatched_def fmap_rll_def[symmetric] isasat_bounded_assn_def
    length_uint32_nat_def[symmetric] isa_find_unwatched_def
    case_tri_bool_If find_unwatched_wl_st_heur_pre_def
    fmap_rll_u64_def[symmetric]
  apply (subst isa_find_unset_lit_def[symmetric])
  apply (subst isa_find_unset_lit_def[symmetric])
  apply (subst isa_find_unset_lit_def[symmetric])
  apply (annot_snat_const \<open>TYPE (64)\<close>)
  unfolding fold_tuple_optimizations
  by sepref

lemma other_watched_wl_heur_alt_def:
  \<open>other_watched_wl_heur = (\<lambda>S. arena_other_watched (get_clauses_wl_heur S))\<close>
  apply (intro ext)
  unfolding other_watched_wl_heur_def
    arena_other_watched_def
    mop_access_lit_in_clauses_heur_def
  by auto argo

lemma other_watched_wl_heur_alt_def2:
  \<open>other_watched_wl_heur = (\<lambda>(_, N, _). arena_other_watched N)\<close>
  by (auto intro!: ext simp: other_watched_wl_heur_alt_def)

sepref_def other_watched_wl_heur_impl
  is \<open>uncurry3 other_watched_wl_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a
    unat_lit_assn\<close>
  supply [[goals_limit=1]]
  unfolding other_watched_wl_heur_alt_def2
    isasat_bounded_assn_def
  by sepref

sepref_register update_clause_wl_heur
setup \<open>map_theory_claset (fn ctxt => ctxt delSWrapper "split_all_tac")\<close>

lemma arena_lit_pre_le2: \<open>
       arena_lit_pre a i \<Longrightarrow> length a \<le> sint64_max \<Longrightarrow> i < max_snat 64\<close>
   using arena_lifting(7)[of a _ _] unfolding arena_lit_pre_def arena_is_valid_clause_idx_and_access_def sint64_max_def max_snat_def
  by fastforce

lemma sint64_max_le_max_snat64: \<open>a < sint64_max \<Longrightarrow> Suc a < max_snat 64\<close>
  by (auto simp: max_snat_def sint64_max_def)

sepref_def update_clause_wl_fast_code
  is \<open>uncurry7 update_clause_wl_heur\<close>
  :: \<open>[\<lambda>(((((((L, C), b), j), w), i), f), S). length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a
     unat_lit_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a
       sint64_nat_assn\<^sup>k
        *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> sint64_nat_assn \<times>\<^sub>a sint64_nat_assn \<times>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]  arena_lit_pre_le2[intro] swap_lits_pre_def[simp]
    sint64_max_le_max_snat64[intro]
  unfolding update_clause_wl_heur_def isasat_bounded_assn_def
    fmap_rll_def[symmetric] delete_index_and_swap_update_def[symmetric]
    delete_index_and_swap_ll_def[symmetric] fmap_swap_ll_def[symmetric]
    append_ll_def[symmetric] update_clause_wl_code_pre_def
    fmap_rll_u64_def[symmetric]
    fmap_swap_ll_u64_def[symmetric]
    fmap_swap_ll_def[symmetric]
    PR_CONST_def mop_arena_lit2'_def
  apply (annot_snat_const \<open>TYPE (64)\<close>)
  unfolding fold_tuple_optimizations
  by sepref
(*takes 11s*)
sepref_register mop_arena_swap

sepref_def propagate_lit_wl_fast_code
  is \<open>uncurry3 propagate_lit_wl_heur\<close>
  :: \<open>[\<lambda>(((L, C), i), S). length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding PR_CONST_def propagate_lit_wl_heur_def
  supply [[goals_limit=1]] swap_lits_pre_def[simp]
  unfolding update_clause_wl_heur_def isasat_bounded_assn_def
    propagate_lit_wl_heur_pre_def fmap_swap_ll_def[symmetric]
    fmap_swap_ll_u64_def[symmetric]
    save_phase_def
  apply (rewrite at \<open>count_decided_pol _ = \<hole>\<close> unat_const_fold[where 'a=32])
  apply (annot_snat_const \<open>TYPE (64)\<close>)
  unfolding fold_tuple_optimizations
  by sepref


sepref_def propagate_lit_wl_bin_fast_code
  is \<open>uncurry2 propagate_lit_wl_bin_heur\<close>
  :: \<open>[\<lambda>((L, C), S). length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>
      isasat_bounded_assn\<close>
  unfolding PR_CONST_def propagate_lit_wl_heur_def
  supply [[goals_limit=1]]  length_ll_def[simp]
  unfolding update_clause_wl_heur_def isasat_bounded_assn_def
    propagate_lit_wl_heur_pre_def fmap_swap_ll_def[symmetric]
    fmap_swap_ll_u64_def[symmetric]
    save_phase_def propagate_lit_wl_bin_heur_def
  apply (rewrite at \<open>count_decided_pol _ = \<hole>\<close> unat_const_fold[where 'a=32])
  unfolding fold_tuple_optimizations
  by sepref

(*TODO Move*)
lemma op_list_list_upd_alt_def: \<open>op_list_list_upd xss i j x = xss[i := (xss ! i)[j := x]]\<close>
  unfolding op_list_list_upd_def by auto

sepref_def update_blit_wl_heur_fast_code
  is \<open>uncurry6 update_blit_wl_heur\<close>
  :: \<open>[\<lambda>((((((_, _), _), _), C), i), S). length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a
      sint64_nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>
     sint64_nat_assn \<times>\<^sub>a sint64_nat_assn \<times>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]] sint64_max_le_max_snat64[intro]
  unfolding update_blit_wl_heur_def isasat_bounded_assn_def append_ll_def[symmetric]
    op_list_list_upd_alt_def[symmetric]
  apply (annot_snat_const \<open>TYPE (64)\<close>)
  by sepref


sepref_register keep_watch_heur

lemma op_list_list_take_alt_def: \<open>op_list_list_take xss i l = xss[i := take l (xss ! i)]\<close>
  unfolding op_list_list_take_def by auto

sepref_def keep_watch_heur_fast_code
  is \<open>uncurry3 keep_watch_heur\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply
    [[goals_limit=1]]
  unfolding keep_watch_heur_def PR_CONST_def
  unfolding fmap_rll_def[symmetric] isasat_bounded_assn_def
  unfolding
    op_list_list_upd_alt_def[symmetric]
    nth_rll_def[symmetric]
    SET_FALSE_def[symmetric] SET_TRUE_def[symmetric]
  by sepref


sepref_register isa_set_lookup_conflict_aa set_conflict_wl_heur

sepref_def set_conflict_wl_heur_fast_code
  is \<open>uncurry set_conflict_wl_heur\<close>
  :: \<open>[\<lambda>(C, S).
     length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a
    sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding set_conflict_wl_heur_def isasat_bounded_assn_def
    set_conflict_wl_heur_pre_def PR_CONST_def
  apply (annot_unat_const \<open>TYPE (32)\<close>)
  unfolding fold_tuple_optimizations
  by sepref



sepref_register update_blit_wl_heur clause_not_marked_to_delete_heur
lemma mop_watched_by_app_heur_alt_def:
  \<open>mop_watched_by_app_heur = (\<lambda>(M, N, D, Q, W, vmtf, \<phi>, clvls, cach, lbd, outl, stats, fema, sema) L K. do {
     ASSERT(K < length (W ! nat_of_lit L));
     ASSERT(nat_of_lit L < length (W));
     RETURN (W ! nat_of_lit L ! K)})\<close>
  by (intro ext; rename_tac S L K; case_tac S)
    (auto simp: mop_watched_by_app_heur_def)

sepref_def mop_watched_by_app_heur_code
  is \<open>uncurry2 mop_watched_by_app_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a watcher_fast_assn\<close>
  unfolding mop_watched_by_app_heur_alt_def isasat_bounded_assn_def
     nth_rll_def[symmetric]
  by sepref

lemma unit_propagation_inner_loop_wl_loop_D_heur_inv0D:
  \<open>unit_propagation_inner_loop_wl_loop_D_heur_inv0 L (j, w, S0) \<Longrightarrow>
    j \<le> length (get_clauses_wl_heur S0) - MIN_HEADER_SIZE \<and>
    w \<le> length (get_clauses_wl_heur S0) - MIN_HEADER_SIZE\<close>
  unfolding unit_propagation_inner_loop_wl_loop_D_heur_inv0_def prod.case
    unit_propagation_inner_loop_wl_loop_inv_def unit_propagation_inner_loop_l_inv_def
  apply normalize_goal+
  by (simp only: twl_st_l twl_st twl_st_wl
     \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits) linarith


sepref_def pos_of_watched_heur_impl
  is \<open>uncurry2 pos_of_watched_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  supply [[goals_limit=1]]
  unfolding pos_of_watched_heur_def
  apply (annot_snat_const \<open>TYPE (64)\<close>)
  by sepref

sepref_def unit_propagation_inner_loop_body_wl_fast_heur_code
  is \<open>uncurry3 unit_propagation_inner_loop_body_wl_heur\<close>
  :: \<open>[\<lambda>((L, w), S). length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k  *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>
       sint64_nat_assn \<times>\<^sub>a sint64_nat_assn \<times>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
    if_splits[split] sint64_max_le_max_snat64[intro] unit_propagation_inner_loop_wl_loop_D_heur_inv0D[dest!]
  unfolding unit_propagation_inner_loop_body_wl_heur_def PR_CONST_def
  unfolding fmap_rll_def[symmetric]
  unfolding option.case_eq_if is_None_alt[symmetric]
    SET_FALSE_def[symmetric] SET_TRUE_def[symmetric] tri_bool_eq_def[symmetric]
  apply (annot_snat_const \<open>TYPE (64)\<close>)
  by sepref

sepref_register unit_propagation_inner_loop_body_wl_heur

lemmas [llvm_inline] =
  other_watched_wl_heur_impl_def
  pos_of_watched_heur_impl_def
  propagate_lit_wl_heur_def
  clause_not_marked_to_delete_heur_fast_code_def
  mop_watched_by_app_heur_code_def
  keep_watch_heur_fast_code_def
  nat_of_lit_rel_impl_def


experiment begin

export_llvm
  isa_save_pos_fast_code
  watched_by_app_heur_fast_code
  isa_find_unwatched_between_fast_code
  find_unwatched_wl_st_heur_fast_code
  update_clause_wl_fast_code
  propagate_lit_wl_fast_code
  propagate_lit_wl_bin_fast_code
  status_neq_impl
  clause_not_marked_to_delete_heur_fast_code
  update_blit_wl_heur_fast_code
  keep_watch_heur_fast_code
  set_conflict_wl_heur_fast_code
  unit_propagation_inner_loop_body_wl_fast_heur_code

end

end
