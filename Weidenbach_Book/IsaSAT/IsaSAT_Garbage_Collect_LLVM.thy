theory IsaSAT_Garbage_Collect_LLVM
  imports IsaSAT_Restart_Heuristics IsaSAT_Setup_LLVM
     IsaSAT_VMTF_State_LLVM IsaSAT_Rephase_State_LLVM
     IsaSAT_Arena_Sorting_LLVM
begin

lemma length_ll[def_pat_rules]: \<open>length_ll$xs$i \<equiv> op_list_list_llen$xs$i\<close>
  by (auto simp: length_ll_def)

lemma [def_pat_rules]: \<open>nth_rll \<equiv> op_list_list_idx\<close>
  by (auto simp: nth_rll_def[abs_def] op_list_list_idx_def intro!: ext)

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
        let (C, _, _) = (W ! nat_of_lit A ! i);
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
  :: \<open>[\<lambda>(((N, _), _), _). length N \<le> sint64_max]\<^sub>a
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
  :: \<open>[\<lambda>(((N, _), _), A). A \<le> uint32_max div 2 \<and> length N \<le> sint64_max]\<^sub>a
     arena_fast_assn\<^sup>d *\<^sub>a (arena_fast_assn \<times>\<^sub>a aivdom_assn)\<^sup>d *\<^sub>a watchlist_fast_assn\<^sup>d *\<^sub>a atom_assn\<^sup>k \<rightarrow>
     (arena_fast_assn \<times>\<^sub>a (arena_fast_assn \<times>\<^sub>a aivdom_assn) \<times>\<^sub>a watchlist_fast_assn)\<close>
  supply [[goals_limit=1]]
  unfolding isasat_GC_clauses_prog_single_wl_def
    shorten_taken_op_list_list_take
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref


definition isasat_GC_clauses_prog_wl2' where
  \<open>isasat_GC_clauses_prog_wl2' ns fst' = (isasat_GC_clauses_prog_wl2 (ns, fst'))\<close>

sepref_register isasat_GC_clauses_prog_wl2 isasat_GC_clauses_prog_single_wl
sepref_def isasat_GC_clauses_prog_wl2_code
  is \<open>uncurry2 isasat_GC_clauses_prog_wl2'\<close>
  :: \<open>[\<lambda>((_, _), (N, _)). length N \<le> sint64_max]\<^sub>a
     (array_assn vmtf_node_assn)\<^sup>k *\<^sub>a (atom.option_assn)\<^sup>k *\<^sub>a
     (arena_fast_assn \<times>\<^sub>a (arena_fast_assn \<times>\<^sub>a aivdom_assn) \<times>\<^sub>a watchlist_fast_assn)\<^sup>d \<rightarrow>
     (arena_fast_assn \<times>\<^sub>a (arena_fast_assn \<times>\<^sub>a aivdom_assn) \<times>\<^sub>a watchlist_fast_assn)\<close>
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
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

lemma rewatch_heur_st_pre_alt_def:
  \<open>rewatch_heur_st_pre S \<longleftrightarrow> (\<forall>i \<in> set (get_tvdom S). i \<le> sint64_max)\<close>
  by (auto simp: rewatch_heur_st_pre_def all_set_conv_nth)

sepref_def rewatch_heur_st_code
  is \<open>rewatch_heur_st\<close>
  :: \<open>[\<lambda>S. rewatch_heur_st_pre S \<and> length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]  append_ll_def[simp]
  unfolding isasat_GC_clauses_prog_wl_def isasat_bounded_assn_def
    rewatch_heur_st_def Let_def rewatch_heur_st_pre_alt_def rewatch_heur_vdom_def[symmetric]
  by sepref

sepref_register isasat_GC_clauses_wl_D

lemma get_clauses_wl_heur_empty_US[simp]:
    \<open>get_clauses_wl_heur (empty_US_heur xc) = get_clauses_wl_heur xc\<close> and
  get_vdom_empty_US[simp]:
    \<open>get_vdom (empty_US_heur xc) = get_vdom xc\<close>
    \<open>get_avdom (empty_US_heur xc) = get_avdom xc\<close>
    \<open>get_ivdom (empty_US_heur xc) = get_ivdom xc\<close>
    \<open>get_tvdom (empty_US_heur xc) = get_tvdom xc\<close>
  by (cases xc; auto simp: empty_US_heur_def; fail)+

sepref_def isasat_GC_clauses_wl_D_code
  is \<open>isasat_GC_clauses_wl_D\<close>
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a
      isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
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