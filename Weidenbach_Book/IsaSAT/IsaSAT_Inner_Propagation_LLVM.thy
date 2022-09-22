theory IsaSAT_Inner_Propagation_LLVM
  imports IsaSAT_Setup_LLVM
    IsaSAT_Inner_Propagation
    IsaSAT_VMTF_LLVM
    IsaSAT_LBD_LLVM
begin

sepref_register isa_save_pos

lemma isa_save_pos_alt_def:
  \<open>isa_save_pos C i = (\<lambda>S\<^sub>0. do {
      ASSERT(arena_is_valid_clause_idx (get_clauses_wl_heur S\<^sub>0) C);
      if arena_length (get_clauses_wl_heur S\<^sub>0) C > MAX_LENGTH_SHORT_CLAUSE then do {
        let (N, S) = extract_arena_wl_heur S\<^sub>0;
        ASSERT (N = get_clauses_wl_heur S\<^sub>0);
        ASSERT(isa_update_pos_pre ((C, i), N));
        let N = arena_update_pos C i N;
        RETURN (update_arena_wl_heur N S)
      } else RETURN S\<^sub>0
    })
  \<close>
  by (auto simp: isa_save_pos_def state_extractors
    split: isasat_int_splits intro!: ext)

sepref_def isa_save_pos_fast_code
  is \<open>uncurry2 isa_save_pos\<close>
  :: \<open>sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply
    [[goals_limit=1]]
    if_splits[split]
  unfolding isa_save_pos_alt_def PR_CONST_def access_length_heur_def[symmetric]
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

definition isa_find_unset_lit_st where
  \<open>isa_find_unset_lit_st S = isa_find_unset_lit (get_trail_wl_heur S) (get_clauses_wl_heur S)\<close>

definition isasat_find_unset_lit_st_impl :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>isasat_find_unset_lit_st_impl = (\<lambda>N C D E.
     read_all_st_code
      (\<lambda>M N _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. isa_find_unwatched_between_fast_code M N C D E) N)\<close>

global_interpretation find_unset_lit: read_trail_arena_param_adder2_threeargs where
  R = \<open>snat_rel' (TYPE(64))\<close> and
  R' = \<open>snat_rel' (TYPE(64))\<close> and
  R'' = \<open>snat_rel' (TYPE(64))\<close> and
  f = \<open>\<lambda>C C' C'' M N. isa_find_unwatched_between_fast_code M N C C' C''\<close> and
  f' = \<open>\<lambda>C C' C'' M N. isa_find_unset_lit M N C C' C''\<close> and
  x_assn = \<open>snat_option_assn' TYPE(64)\<close> and
  P = \<open>\<lambda>C C' C'' M N. length N \<le> sint64_max\<close>
  rewrites
  \<open>(\<lambda>N C D E.
  read_all_st (\<lambda>M N _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. isa_find_unset_lit M N C D E) N) = isa_find_unset_lit_st\<close> and
  \<open>(\<lambda>N C D E.
     read_all_st_code
      (\<lambda>M N _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. isa_find_unwatched_between_fast_code M N C D E) N) = isasat_find_unset_lit_st_impl\<close>
  apply (unfold_locales)
  apply (subst (9) uncurry_def)+
  apply (rule isa_find_unwatched_between_fast_code.refine)
  subgoal by (auto simp: read_all_st_def isa_find_unset_lit_st_def intro!: ext split: isasat_int_splits)
  subgoal by (auto simp: isasat_find_unset_lit_st_impl_def)
  done

lemmas [sepref_fr_rules] = find_unset_lit.refine
lemmas [unfolded inline_direct_return_node_case, llvm_code] =
  isasat_find_unset_lit_st_impl_def[unfolded read_all_st_code_def]

sepref_def swap_lits_impl is \<open>uncurry3 mop_arena_swap\<close>
  :: \<open>sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>d \<rightarrow>\<^sub>a arena_fast_assn\<close>
  unfolding mop_arena_swap_def swap_lits_pre_def
  unfolding gen_swap
  by sepref

sepref_register isa_find_unset_lit_st

sepref_def find_unwatched_wl_st_heur_fast_code
  is \<open>uncurry isa_find_unwatched_wl_st_heur\<close>
  :: \<open>[\<lambda>(S, C). length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a
         isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> snat_option_assn' TYPE(64)\<close>
  supply [[goals_limit = 1]] isasat_fast_def[simp]
  unfolding isa_find_unwatched_wl_st_heur_def PR_CONST_def
    find_unwatched_def fmap_rll_def[symmetric]
    length_uint32_nat_def[symmetric] isa_find_unwatched_def
    case_tri_bool_If find_unwatched_wl_st_heur_pre_def
    fmap_rll_u64_def[symmetric]
    mop_arena_length_st_def[symmetric]
    mop_arena_pos_st_def[symmetric]
  apply (subst isa_find_unset_lit_def[symmetric])+
  apply (subst isa_find_unset_lit_st_def[symmetric])+
  apply (annot_snat_const \<open>TYPE (64)\<close>)
  by sepref

lemma other_watched_wl_heur_alt_def:
  \<open>other_watched_wl_heur = (\<lambda>S. arena_other_watched (get_clauses_wl_heur S))\<close>
  apply (intro ext)
  unfolding other_watched_wl_heur_def
    arena_other_watched_def
    mop_access_lit_in_clauses_heur_def
  by auto argo

definition clause_not_marked_to_delete_heur_code :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _ \<Rightarrow> _\<close> where
  \<open>clause_not_marked_to_delete_heur_code S C' = read_arena_wl_heur_code (\<lambda>N. not_deleted_code N C') S\<close>
(*mop_arena_lit2 \<longleftrightarrow> mop_access_lit_in_clauses_heur*)

sepref_def other_watched_wl_heur_impl
  is \<open>uncurry3 other_watched_wl_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a
    unat_lit_assn\<close>
  supply [[goals_limit=1]]
  unfolding other_watched_wl_heur_alt_def
    arena_other_watched_def
    mop_access_lit_in_clauses_heur_def[symmetric]
  apply (annot_snat_const \<open>TYPE (64)\<close>)
  by sepref

sepref_register update_clause_wl_heur
setup \<open>map_theory_claset (fn ctxt => ctxt delSWrapper "split_all_tac")\<close>

lemma arena_lit_pre_le2: \<open>
       arena_lit_pre a i \<Longrightarrow> length a \<le> sint64_max \<Longrightarrow> i < max_snat 64\<close>
   using arena_lifting(7)[of a _ _] unfolding arena_lit_pre_def arena_is_valid_clause_idx_and_access_def sint64_max_def max_snat_def
  by fastforce

lemma sint64_max_le_max_snat64: \<open>a < sint64_max \<Longrightarrow> Suc a < max_snat 64\<close>
  by (auto simp: max_snat_def sint64_max_def)

lemma update_clause_wl_heur_alt_def:
  \<open>update_clause_wl_heur = (\<lambda>(L::nat literal) C b j w i f S\<^sub>0. do {
     let (N, S) = extract_arena_wl_heur S\<^sub>0;
     ASSERT (N = get_clauses_wl_heur S\<^sub>0);
     let (W, S) = extract_watchlist_wl_heur S;
     ASSERT (W = get_watched_wl_heur S\<^sub>0);
     K' \<leftarrow> mop_arena_lit2' (set (get_vdom S)) N C f;
     ASSERT(w < length N);
     N' \<leftarrow> mop_arena_swap C i f N;
     ASSERT(nat_of_lit K' < length W);
     ASSERT(length (W ! (nat_of_lit K')) < length N);
     let W = W[nat_of_lit K':= W ! (nat_of_lit K') @ [(C, L, b)]];
     let S = update_arena_wl_heur N' S;
     let S = update_watchlist_wl_heur W S;
     RETURN (j, w+1, S)
   })\<close>
   by (auto intro!: ext simp: state_extractors update_clause_wl_heur_def
         split: isasat_int_splits)

sepref_def update_clause_wl_fast_code
  is \<open>uncurry7 update_clause_wl_heur\<close>
  :: \<open>[\<lambda>(((((((L, C), b), j), w), i), f), S). length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a
     unat_lit_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a
       sint64_nat_assn\<^sup>k
        *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> sint64_nat_assn \<times>\<^sub>a sint64_nat_assn \<times>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]  arena_lit_pre_le2[intro] swap_lits_pre_def[simp]
    sint64_max_le_max_snat64[intro]
  unfolding update_clause_wl_heur_alt_def
    fmap_rll_def[symmetric] delete_index_and_swap_update_def[symmetric]
    delete_index_and_swap_ll_def[symmetric] fmap_swap_ll_def[symmetric]
    append_ll_def[symmetric] update_clause_wl_code_pre_def
    fmap_rll_u64_def[symmetric]
    fmap_swap_ll_u64_def[symmetric]
    fmap_swap_ll_def[symmetric]
    PR_CONST_def mop_arena_lit2'_def
  apply (annot_snat_const \<open>TYPE (64)\<close>)
  by sepref

sepref_register mop_arena_swap

definition propagate_lit_wl_heur_inner :: \<open>_\<close> where
  \<open>propagate_lit_wl_heur_inner L' C i =  (\<lambda>M N D j W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs. do {
      ASSERT(i \<le> 1);
      M \<leftarrow> cons_trail_Propagated_tr L' C M;
      N' \<leftarrow> mop_arena_swap C 0 (1 - i) N;
      let stats = incr_propagation (if count_decided_pol M = 0 then incr_uset stats else stats);
      heur \<leftarrow> mop_save_phase_heur (atm_of L') (is_pos L') heur;
      RETURN (Tuple17 M N' D j W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs)
  })\<close>

lemma propagate_lit_wl_heur_propagate_lit_wl_heur_inner:
  \<open>propagate_lit_wl_heur = (\<lambda>L' C i (S\<^sub>0::isasat).
  case_isasat_int (propagate_lit_wl_heur_inner L' C i)
   S\<^sub>0)\<close>
  by (auto intro!: ext simp: state_extractors propagate_lit_wl_heur_def read_all_st_def
    propagate_lit_wl_heur_inner_def
    split: isasat_int_splits)

sepref_def propagate_lit_wl_fast_code
  is \<open>uncurry3 propagate_lit_wl_heur\<close>
  :: \<open>[\<lambda>(((L, C), i), S). length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding PR_CONST_def propagate_lit_wl_heur_propagate_lit_wl_heur_inner
    RETURN_case_tuple16_invers comp_def propagate_lit_wl_heur_inner_def
  unfolding
    propagate_lit_wl_heur_pre_def fmap_swap_ll_def[symmetric]
    fmap_swap_ll_u64_def[symmetric]
    save_phase_def
  apply (rewrite at \<open>count_decided_pol _ = \<hole>\<close> unat_const_fold[where 'a=32])
  apply (annot_snat_const \<open>TYPE (64)\<close>)
  supply [[goals_limit=1]]
  by sepref
lemmas [llvm_inline] = Mreturn_comp_IsaSAT_int


sepref_register incr_uset incr_units_since_last_GC


lemma propagate_lit_wl_bin_heur_alt2:
  \<open>propagate_lit_wl_bin_heur = (\<lambda>L' C (S\<^sub>0::isasat).
  case_isasat_int (\<lambda>M N D j W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs. do {
      M \<leftarrow> cons_trail_Propagated_tr L' C M;
      let stats = incr_propagation (if count_decided_pol M = 0 then incr_uset (incr_units_since_last_GC stats) else stats);
      heur \<leftarrow> mop_save_phase_heur (atm_of L') (is_pos L') heur;
      RETURN (Tuple17 M N D j W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs)
  })
   S\<^sub>0)\<close>
  by (auto intro!: ext simp: state_extractors propagate_lit_wl_bin_heur_def read_all_st_def
    propagate_lit_wl_heur_inner_def
    split: isasat_int_splits)


lemma propagate_lit_wl_bin_heur_alt_def:
  \<open>propagate_lit_wl_bin_heur = (\<lambda>L' C S\<^sub>0. do {
      let (M, S) = extract_trail_wl_heur S\<^sub>0;
      ASSERT (M = get_trail_wl_heur S\<^sub>0);
      let (heur, S) = extract_heur_wl_heur S;
      ASSERT (heur = get_heur S\<^sub>0);
      let (stats, S) = extract_stats_wl_heur S;
      M \<leftarrow> cons_trail_Propagated_tr L' C M;
      let stats = incr_propagation (if count_decided_pol M = 0 then incr_uset (incr_units_since_last_GC stats) else stats);
      heur \<leftarrow> mop_save_phase_heur (atm_of L') (is_pos L') heur;
      let S = update_trail_wl_heur M S;
      let S = update_heur_wl_heur heur S;
      let S = update_stats_wl_heur stats S;
      RETURN S
  })\<close>
  by (auto intro!: ext simp: state_extractors propagate_lit_wl_bin_heur_def
      split: isasat_int_splits)

sepref_def propagate_lit_wl_bin_fast_code
  is \<open>uncurry2 propagate_lit_wl_bin_heur\<close>
  :: \<open>[\<lambda>((L, C), S). length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>
      isasat_bounded_assn\<close>
  unfolding PR_CONST_def propagate_lit_wl_bin_heur_alt2
    RETURN_case_tuple16_invers comp_def
  supply [[goals_limit=1]]  length_ll_def[simp]
  unfolding update_clause_wl_heur_def
    propagate_lit_wl_heur_pre_def fmap_swap_ll_def[symmetric]
    fmap_swap_ll_u64_def[symmetric]
    save_phase_def propagate_lit_wl_bin_heur_def
  apply (rewrite at \<open>count_decided_pol _ = \<hole>\<close> unat_const_fold[where 'a=32])
  unfolding fold_tuple_optimizations
  by sepref

lemma update_blit_wl_heur_alt_def:
  \<open>update_blit_wl_heur = (\<lambda>(L::nat literal) C b j w K S\<^sub>0. do {
     let (W, S) = extract_watchlist_wl_heur S\<^sub>0;
     ASSERT (W = get_watched_wl_heur S\<^sub>0);
     ASSERT(nat_of_lit L < length W);
     ASSERT(j < length (W ! nat_of_lit L));
     ASSERT(j < length (get_clauses_wl_heur S\<^sub>0));
     ASSERT(w < length (get_clauses_wl_heur S\<^sub>0));
     let W = W[nat_of_lit L := (W!nat_of_lit L)[j:= (C, K, b)]];
     RETURN (j+1, w+1, update_watchlist_wl_heur W S)
  })\<close>
  by (auto intro!: ext simp: state_extractors update_blit_wl_heur_def
    split: isasat_int_splits)

sepref_def update_blit_wl_heur_fast_code
  is \<open>uncurry6 update_blit_wl_heur\<close>
  :: \<open>[\<lambda>((((((_, _), _), _), C), i), S). length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a
      sint64_nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>
     sint64_nat_assn \<times>\<^sub>a sint64_nat_assn \<times>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]] sint64_max_le_max_snat64[intro]
  unfolding update_blit_wl_heur_alt_def append_ll_def[symmetric]
    op_list_list_upd_alt_def[symmetric]
  apply (annot_snat_const \<open>TYPE (64)\<close>)
  by sepref


sepref_register keep_watch_heur

lemma op_list_list_take_alt_def: \<open>op_list_list_take xss i l = xss[i := take l (xss ! i)]\<close>
  unfolding op_list_list_take_def by auto

lemma keep_watch_heur_alt_def:
  \<open>keep_watch_heur = (\<lambda>L i j S. do {
     let (W, S) = extract_watchlist_wl_heur S;
     ASSERT(nat_of_lit L < length W);
     ASSERT(i < length (W ! nat_of_lit L));
     ASSERT(j < length (W ! nat_of_lit L));
     let W =  W[nat_of_lit L := (W!(nat_of_lit L))[i := W ! (nat_of_lit L) ! j]];
     RETURN (update_watchlist_wl_heur W S)
   })\<close>
  by (auto intro!: ext simp: state_extractors keep_watch_heur_def
    split: isasat_int_splits)

sepref_def keep_watch_heur_fast_code
  is \<open>uncurry3 keep_watch_heur\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply
    [[goals_limit=1]]
  unfolding keep_watch_heur_alt_def PR_CONST_def
  unfolding fmap_rll_def[symmetric]
  unfolding
    op_list_list_upd_alt_def[symmetric]
    nth_rll_def[symmetric]
    SET_FALSE_def[symmetric] SET_TRUE_def[symmetric]
  by sepref


sepref_register unit_propagation_inner_loop_body_wl_heur

sepref_register isa_set_lookup_conflict_aa set_conflict_wl_heur mark_conflict_to_rescore

lemma mark_conflict_to_rescore_alt_def:
  \<open>mark_conflict_to_rescore C  S\<^sub>0 = do {
    let (M, S) = extract_trail_wl_heur S\<^sub>0;
    let (N, S) = extract_arena_wl_heur S;
    let (vm, S) = extract_vmtf_wl_heur S;
    n \<leftarrow> mop_arena_length N C;
    ASSERT (n \<le> length (get_clauses_wl_heur S\<^sub>0));
    (_, vm) \<leftarrow> WHILE\<^sub>T (\<lambda>(i, vm). i < n)
      (\<lambda>(i, vm). do{
       ASSERT (i < n);
       L \<leftarrow> mop_arena_lit2 N C i;
       vm \<leftarrow> isa_vmtf_mark_to_rescore_also_reasons_cl M N C (-L) vm;
      RETURN (i+1, vm)
     })
      (0, vm);
    let (lbd, S) = extract_lbd_wl_heur S;
    (N, lbd) \<leftarrow> calculate_LBD_heur_st M N lbd C;
    let S = update_trail_wl_heur M S;
    let S = update_arena_wl_heur N S;
    let S = update_vmtf_wl_heur vm S;
    let S = update_lbd_wl_heur lbd S;
    RETURN S }\<close>
  by (auto intro!: ext simp: state_extractors mark_conflict_to_rescore_def Let_def
    split: isasat_int_splits)

sepref_def mark_conflict_to_rescore_impl
  is \<open>uncurry mark_conflict_to_rescore\<close>
  :: \<open>sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding mark_conflict_to_rescore_alt_def
  apply (annot_snat_const \<open>TYPE (64)\<close>)
  by sepref

lemma set_conflict_wl_heur_alt_def:
  \<open>set_conflict_wl_heur = (\<lambda>C S\<^sub>0. do {
    S\<^sub>0 \<leftarrow> mark_conflict_to_rescore C S\<^sub>0;
    let n = 0;
    let (M, S) = extract_trail_wl_heur S\<^sub>0;
    let (N, S) = extract_arena_wl_heur S;
    let (D, S) = extract_conflict_wl_heur S;
    let (outl, S) = extract_outl_wl_heur S;
    let (stats, S) = extract_stats_wl_heur S;
    ASSERT(curry5 isa_set_lookup_conflict_aa_pre M N C D n outl);
    (D, clvls, outl) \<leftarrow> isa_set_lookup_conflict_aa M N C D n outl;
    j \<leftarrow> mop_isa_length_trail M;
    let S = update_conflict_wl_heur D S;
    let stats = incr_conflict stats;
    let S = update_stats_wl_heur stats S;
    let S = update_outl_wl_heur outl S;
    let S = update_clvls_wl_heur clvls S;
    let S = update_literals_to_update_wl_heur j S;
    let S = update_trail_wl_heur M S;
    let S = update_arena_wl_heur N S;
    RETURN S})\<close>
    by (auto intro!: ext bind_cong[OF refl] simp: state_extractors set_conflict_wl_heur_def Let_def
    split: isasat_int_splits)

sepref_def set_conflict_wl_heur_fast_code
  is \<open>uncurry set_conflict_wl_heur\<close>
  :: \<open>[\<lambda>(C, S). length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a
    sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding set_conflict_wl_heur_alt_def
    set_conflict_wl_heur_pre_def PR_CONST_def
  apply (annot_unat_const \<open>TYPE (32)\<close>)
  by sepref



sepref_register update_blit_wl_heur clause_not_marked_to_delete_heur

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

lemmas [llvm_inline] =
  other_watched_wl_heur_impl_def
  pos_of_watched_heur_impl_def
  propagate_lit_wl_heur_def
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
  update_blit_wl_heur_fast_code
  keep_watch_heur_fast_code
  set_conflict_wl_heur_fast_code
  unit_propagation_inner_loop_body_wl_fast_heur_code

end

end
