theory IsaSAT_Garbage_Collect_LLVM
  imports IsaSAT_Restart_Heuristics_Defs IsaSAT_Setup_LLVM
     IsaSAT_VMTF_State_LLVM IsaSAT_Rephase_State_LLVM
     IsaSAT_Arena_Sorting_LLVM
     IsaSAT_Show_LLVM
begin

sepref_register length_ll extra_information_mark_to_delete nth_rll
  LEARNED

lemma isasat_GC_clauses_prog_copy_wl_entry_alt_def:
\<open>isasat_GC_clauses_prog_copy_wl_entry = (\<lambda>N0 W A (N', aivdom). do {
    ASSERT(nat_of_lit A < length W);
    ASSERT(length (W ! nat_of_lit A) \<le> length N0);
    let le = length (W ! nat_of_lit A);
    (i, N, N', aivdom) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(i, N, N', aivdom). i < le)
      (\<lambda>(i, N, (N', aivdom)). do {
        ASSERT(i < length (W ! nat_of_lit A));
        let (C, _, _) = W ! nat_of_lit A ! i;
        ASSERT(arena_is_valid_clause_vdom N C);
        let st = arena_status N C;
        if st \<noteq> DELETED then do {
          ASSERT(arena_is_valid_clause_idx N C);
          ASSERT(length N' +
            (if arena_length N C > 4 then MAX_HEADER_SIZE else MIN_HEADER_SIZE) +
            arena_length N C \<le> length N0);
          ASSERT(length N = length N0);
          ASSERT(length (get_vdom_aivdom aivdom) < length N0);
          ASSERT(length (get_avdom_aivdom aivdom) < length N0);
          ASSERT(length (get_ivdom_aivdom aivdom) < length N0);
          ASSERT(length (get_tvdom_aivdom aivdom) < length N0);
          let D = length N' + (if arena_length N C > 4 then MAX_HEADER_SIZE else MIN_HEADER_SIZE);
          N' \<leftarrow> fm_mv_clause_to_new_arena C N N';
          ASSERT(mark_garbage_pre (N, C));
	  RETURN (i+1, extra_information_mark_to_delete N C, N',
             (if st = LEARNED then add_learned_clause_aivdom_strong D aivdom else add_init_clause_aivdom_strong D aivdom))
        } else RETURN (i+1, N, (N', aivdom))
      }) (0, N0, (N', aivdom));
    RETURN (N, (N', aivdom))
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
  :: \<open>[\<lambda>(((N, _), _), _). length N \<le> snat64_max]\<^sub>a
     arena_fast_assn\<^sup>d *\<^sub>a watchlist_fast_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a
         (arena_fast_assn \<times>\<^sub>a aivdom_assn)\<^sup>d \<rightarrow>
     (arena_fast_assn \<times>\<^sub>a (arena_fast_assn \<times>\<^sub>a aivdom_assn))\<close>
  supply [[goals_limit=1]] if_splits[split] length_ll_def[simp]
  unfolding isasat_GC_clauses_prog_copy_wl_entry_alt_def nth_rll_def[symmetric]
    length_ll_def[symmetric] if_conn(4)
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_register isasat_GC_clauses_prog_copy_wl_entry

lemma shorten_taken_op_list_list_take:
  \<open>W[L := []] = op_list_list_take W L 0\<close>
  by (auto simp:)

sepref_def isasat_GC_clauses_prog_single_wl_code
  is \<open>uncurry3 isasat_GC_clauses_prog_single_wl\<close>
  :: \<open>[\<lambda>(((N, _), _), A). A \<le> unat32_max div 2 \<and> length N \<le> snat64_max]\<^sub>a
     arena_fast_assn\<^sup>d *\<^sub>a (arena_fast_assn \<times>\<^sub>a aivdom_assn)\<^sup>d *\<^sub>a watchlist_fast_assn\<^sup>d *\<^sub>a atom_assn\<^sup>k \<rightarrow>
     (arena_fast_assn \<times>\<^sub>a (arena_fast_assn \<times>\<^sub>a aivdom_assn) \<times>\<^sub>a watchlist_fast_assn)\<close>
  supply [[goals_limit=1]]
  unfolding isasat_GC_clauses_prog_single_wl_def
    shorten_taken_op_list_list_take
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_register isasat_GC_clauses_prog_wl2 isasat_GC_clauses_prog_single_wl
sepref_def isasat_GC_clauses_prog_wl2_code
  is \<open>uncurry isasat_GC_clauses_prog_wl2\<close>
  :: \<open>[\<lambda>(_, (N, _)). length N \<le> snat64_max]\<^sub>a
     (heuristic_bump_assn)\<^sup>k *\<^sub>a
     (arena_fast_assn \<times>\<^sub>a (arena_fast_assn \<times>\<^sub>a aivdom_assn) \<times>\<^sub>a watchlist_fast_assn)\<^sup>d \<rightarrow>
     (arena_fast_assn \<times>\<^sub>a (arena_fast_assn \<times>\<^sub>a aivdom_assn) \<times>\<^sub>a watchlist_fast_assn)\<close>
  supply [[goals_limit=1]]
  unfolding isasat_GC_clauses_prog_wl2_def prod.case atom.fold_option
  by sepref

lemma isasat_GC_clauses_prog_wl_alt_def:
  \<open>isasat_GC_clauses_prog_wl = (\<lambda>S\<^sub>0. do {
     let (vm, S) = extract_vmtf_wl_heur S\<^sub>0;
    let (N', S) = extract_arena_wl_heur S;
    ASSERT (N' = get_clauses_wl_heur S\<^sub>0);
    let (W', S) = extract_watchlist_wl_heur S;
    let (vdom, S) = extract_vdom_wl_heur S;
    let (old_arena, S) = extract_old_arena_wl_heur S;
    ASSERT(old_arena = []);
    (N, (N', vdom), WS) \<leftarrow> isasat_GC_clauses_prog_wl2 vm
        (N', (old_arena, empty_aivdom vdom), W');
    let S = update_watchlist_wl_heur WS S;
    let S = update_arena_wl_heur N' S;
    let S = update_old_arena_wl_heur (take 0 N) S;
    let S = update_vmtf_wl_heur vm S;
    let (stats, S) = extract_stats_wl_heur S;
    let S = update_stats_wl_heur (incr_GC stats) S;
    let S = update_vdom_wl_heur vdom S;
    let (heur, S) = extract_heur_wl_heur S;
    let heur = heuristic_reluctant_untrigger (set_zero_wasted heur);
    let S = update_heur_wl_heur heur S;
    RETURN S
      })\<close>
      by (auto simp: isasat_GC_clauses_prog_wl_def state_extractors
         Let_def intro!: ext bind_cong[OF refl]
        split: isasat_int_splits)

sepref_register isasat_GC_clauses_prog_wl rewatch_heur_st
sepref_def isasat_GC_clauses_prog_wl_code
  is \<open>isasat_GC_clauses_prog_wl\<close>
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> snat64_max]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_GC_clauses_prog_wl_alt_def
    atom.fold_option
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

lemma rewatch_heur_st_pre_alt_def:
  \<open>rewatch_heur_st_pre S \<longleftrightarrow> (\<forall>i \<in> set (get_tvdom S). i \<le> snat64_max)\<close>
  by (auto simp: rewatch_heur_st_pre_def all_set_conv_nth)


definition rewatch_heur_and_reorder_vdom where
  \<open>rewatch_heur_and_reorder_vdom vdom = rewatch_heur_and_reorder (get_tvdom_aivdom vdom)\<close>

sepref_def rewatch_heur_and_reorder_code
  is \<open>uncurry2 (rewatch_heur_and_reorder_vdom)\<close>
  :: \<open>[\<lambda>((vdom, arena), W). (\<forall>x \<in> set (get_tvdom_aivdom vdom). x \<le> snat64_max) \<and> length arena \<le> snat64_max \<and>
        length (get_tvdom_aivdom vdom) \<le> snat64_max]\<^sub>a
        aivdom_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a watchlist_fast_assn\<^sup>d \<rightarrow> watchlist_fast_assn\<close>
  supply [[goals_limit=1]]
     arena_lit_pre_le_snat64_max[dest] arena_is_valid_clause_idx_le_unat64_max[dest]
  supply [simp] = append_ll_def
  supply [dest] = arena_lit_implI(1)
  unfolding rewatch_heur_and_reorder_def Let_def PR_CONST_def rewatch_heur_and_reorder_vdom_def
    rewatch_heur_vdom_def[symmetric]
  by sepref

lemma rewatch_heur_and_reorder_st_alt_def:
  \<open>rewatch_heur_and_reorder_st = (\<lambda>S\<^sub>0. do {
  let (vdom, S) = extract_vdom_wl_heur S\<^sub>0;
  ASSERT (vdom = get_aivdom S\<^sub>0);
  let (N, S) = extract_arena_wl_heur S;
  ASSERT (N = get_clauses_wl_heur S\<^sub>0);
  let (W, S) = extract_watchlist_wl_heur S;
  ASSERT(length (get_tvdom_aivdom vdom) \<le> length N);
  W \<leftarrow> rewatch_heur_and_reorder (get_tvdom_aivdom vdom) N W;
  RETURN (update_watchlist_wl_heur W (update_arena_wl_heur N (update_vdom_wl_heur vdom S)))
  })\<close>
  by (auto simp: rewatch_heur_and_reorder_st_def state_extractors split: isasat_int_splits intro!: ext)

sepref_register rewatch_heur_and_reorder rewatch_heur_and_reorder_vdom
sepref_def rewatch_heur_st_code
  is \<open>rewatch_heur_and_reorder_st\<close>
  :: \<open>[\<lambda>S. rewatch_heur_st_pre S \<and> length (get_clauses_wl_heur S) \<le> snat64_max]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]  append_ll_def[simp]
  unfolding rewatch_heur_and_reorder_st_alt_def rewatch_heur_st_pre_alt_def rewatch_heur_vdom_def[symmetric]
    rewatch_heur_and_reorder_vdom_def[symmetric]
  by sepref

sepref_register isasat_GC_clauses_wl_D

sepref_register rewatch_heur_and_reorder_st
sepref_def isasat_GC_clauses_wl_D_code
  is \<open>uncurry isasat_GC_clauses_wl_D\<close>
  :: \<open>[\<lambda>(b, S). length (get_clauses_wl_heur S) \<le> snat64_max]\<^sub>a
      bool1_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]] isasat_GC_clauses_wl_D_rewatch_pre[intro!]
  unfolding isasat_GC_clauses_wl_D_def
  by sepref

sepref_register access_avdom_at

experiment
begin
  export_llvm
    isasat_GC_clauses_wl_D_code
end

end
