theory IsaSAT_Simplify_Clause_Units_LLVM
  imports IsaSAT_Setup_LLVM IsaSAT_Trail_LLVM
    IsaSAT_Simplify_Units_Defs
    IsaSAT_Proofs_LLVM
begin

no_notation WB_More_Refinement.fref (\<open>[_]\<^sub>f _ \<rightarrow> _\<close> [0,60,60] 60)
no_notation WB_More_Refinement.freft (\<open>_ \<rightarrow>\<^sub>f _\<close> [60,60] 60)

sepref_register 0 1

sepref_register mop_arena_update_lit


lemma isa_simplify_clause_with_unit2_alt_def:
  \<open>isa_simplify_clause_with_unit2 C M N = do {
     l \<leftarrow> mop_arena_length N C;
    ASSERT(l < length N \<and> l \<le> Suc (uint32_max div 2));
    (i, j, N::arena, is_true) \<leftarrow> WHILE\<^sub>T(\<lambda>(i, j, N::arena, b). \<not>b \<and> j < l)
    (\<lambda>(i, j, N, is_true). do {
      ASSERT(i \<le> j \<and> j < l);
      L \<leftarrow> mop_arena_lit2 N C j;
      let _ = mark_literal_for_unit_deletion L;
      val \<leftarrow> mop_polarity_pol M L;
      if val = Some True then RETURN (i, j+1, N,True)
      else if val = Some False
      then RETURN (i, j+1, N,  False)
        else do {
        N \<leftarrow> mop_arena_update_lit C i L N;
        RETURN (i+1, j+1, N, False)}
    })
      (0, 0, N, False);
   L \<leftarrow> mop_arena_lit2 N C 0;
   if is_true \<or> i \<le> 1
   then do {
     ASSERT(mark_garbage_pre (N, C));
     RETURN (False, extra_information_mark_to_delete N C, L, is_true, i)}
   else if i = j then RETURN (True, N, L, is_true, i)
   else do {
      N \<leftarrow> mop_arena_shorten C i N;
      RETURN (False, N, L, is_true, i)}
    }\<close>
  by (auto simp: mark_literal_for_unit_deletion_def isa_simplify_clause_with_unit2_def)

sepref_def isa_simplify_clause_with_unit2_code
  is \<open>uncurry2 isa_simplify_clause_with_unit2\<close>
  :: \<open>[\<lambda>((_, _), N). length (N) \<le> sint64_max]\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>d \<rightarrow>
  bool1_assn \<times>\<^sub>a arena_fast_assn \<times>\<^sub>a unat_lit_assn \<times>\<^sub>a  bool1_assn \<times>\<^sub>a uint32_nat_assn\<close>
  unfolding isa_simplify_clause_with_unit2_alt_def
    length_avdom_def[symmetric] Suc_eq_plus1[symmetric]
    mop_arena_status_st_def[symmetric] isasat_bounded_assn_def
    SET_TRUE_def[symmetric] SET_FALSE_def[symmetric]
    tri_bool_eq_def[symmetric]
  apply (rewrite at \<open>(\<hole>, _, _)\<close> unat_const_fold[where 'a=32])
  apply (rewrite at \<open>(_ \<le> \<hole>)\<close> unat_const_fold[where 'a=32])
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  apply (rewrite at \<open>mop_arena_update_lit _ \<hole>\<close> annot_unat_snat_upcast[where 'l=64])
  apply (rewrite at \<open>If (\<hole> = _)\<close> annot_unat_snat_upcast[where 'l=64])
  supply [[goals_limit=1]]
  by sepref

sepref_register cons_trail_Propagated_tr set_conflict_to_false

lemma set_conflict_to_false_alt_def:
  \<open>RETURN o set_conflict_to_false = (\<lambda>(b, n, xs). RETURN (False, 0, xs))\<close>
  unfolding set_conflict_to_false_def by auto

sepref_def set_conflict_to_false_code
  is \<open>RETURN o set_conflict_to_false\<close>
  :: \<open>conflict_option_rel_assn\<^sup>d \<rightarrow>\<^sub>a conflict_option_rel_assn\<close>
  unfolding set_conflict_to_false_alt_def conflict_option_rel_assn_def
    lookup_clause_rel_assn_def
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  supply [[goals_limit=1]]
  by sepref

lemma isa_simplify_clause_with_unit_st2_alt_def:
  \<open>isa_simplify_clause_with_unit_st2 =  (\<lambda>C S\<^sub>0. do {
  let (lcount, S) = extract_lcount_wl_heur S\<^sub>0; let (N, S) = extract_arena_wl_heur S; let (M, S) = extract_trail_wl_heur S;
  ASSERT (N = get_clauses_wl_heur S\<^sub>0 \<and> lcount = get_learned_count S\<^sub>0 \<and> M = get_trail_wl_heur S\<^sub>0);
  E \<leftarrow> mop_arena_status N C;
   ASSERT(E = LEARNED \<longrightarrow> 1 \<le> clss_size_lcount lcount);
  (unc, N, L, b, i) \<leftarrow> isa_simplify_clause_with_unit2 C M N;
  ASSERT (length N \<le> length (get_clauses_wl_heur S\<^sub>0));
   if unc then do {
     let _ = mark_clause_for_unit_as_unchanged 0;
     RETURN (update_arena_wl_heur N (update_trail_wl_heur M (update_lcount_wl_heur lcount S)))
   }
   else if b then
   let (stats, S) = extract_stats_wl_heur S in
   let _ = mark_clause_for_unit_as_unchanged 0 in
   RETURN  (update_trail_wl_heur M
     (update_arena_wl_heur N
     (update_stats_wl_heur (if E=LEARNED then stats else decr_irred_clss (stats))
     (update_lcount_wl_heur (if E = LEARNED then clss_size_decr_lcount (lcount) else lcount)
     S))))
   else if i = 1
   then do {
     M \<leftarrow> cons_trail_Propagated_tr L 0 M;
    let (stats, S) = extract_stats_wl_heur S;
    let _ = mark_clause_for_unit_as_unchanged 0;
     RETURN (update_arena_wl_heur N
     (update_trail_wl_heur M
     (update_stats_wl_heur (if E=LEARNED then incr_uset stats else incr_uset (decr_irred_clss stats))
     (update_lcount_wl_heur (if E = LEARNED then clss_size_decr_lcount (clss_size_incr_lcountUEk lcount) else lcount)
     S)))) }
   else if i = 0
   then do {
     j \<leftarrow> mop_isa_length_trail M;
     let _ = mark_clause_for_unit_as_unchanged 0;
     let (stats, S) = extract_stats_wl_heur S; let (confl, S) = extract_conflict_wl_heur S;
     RETURN (update_trail_wl_heur M
     (update_arena_wl_heur N
     (update_conflict_wl_heur (set_conflict_to_false confl)
     (update_clvls_wl_heur 0
     (update_literals_to_update_wl_heur j
     (update_stats_wl_heur (if E=LEARNED then stats else decr_irred_clss stats)
     (update_lcount_wl_heur (if E = LEARNED then clss_size_decr_lcount lcount else lcount)
     S)))))))
   }
   else do {
     let S = (update_trail_wl_heur M
     (update_lcount_wl_heur lcount
     (update_arena_wl_heur N
     S)));
     _ \<leftarrow> log_new_clause_heur S C;
     let _ = mark_clause_for_unit_as_changed 0;
     RETURN S
   }
  })\<close>
  unfolding isa_simplify_clause_with_unit_st2_def
  apply (auto simp: state_extractors Let_def split: isasat_int_splits intro!: ext bind_cong[OF refl])
  done

(*TODO Move and generalise*)
lemma [simp]:
  \<open>get_clauses_wl_heur (update_trail_wl_heur M S) = get_clauses_wl_heur S\<close>
  \<open>get_clauses_wl_heur (update_lcount_wl_heur lc S) = get_clauses_wl_heur S\<close>
  \<open>get_clauses_wl_heur (update_arena_wl_heur N S) = N\<close>
  by (cases S) (auto simp: update_a_def update_b_def update_n_def split: isasat_int_splits)

sepref_def isa_simplify_clause_with_unit_st2_code
  is \<open>uncurry isa_simplify_clause_with_unit_st2\<close>
  :: \<open>[\<lambda>(_, S). length (get_clauses_wl_heur S) \<le> sint64_max \<and> learned_clss_count S \<le> uint64_max]\<^sub>a
  sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [simp] = learned_clss_count_def
  unfolding isa_simplify_clause_with_unit_st2_alt_def
    length_avdom_def[symmetric] Suc_eq_plus1[symmetric]
    mop_arena_status_st_def[symmetric]
  apply (rewrite at \<open>(cons_trail_Propagated_tr _ \<hole>)\<close> snat_const_fold[where 'a=64])
  apply (rewrite at \<open>(mark_clause_for_unit_as_changed \<hole>)\<close> unat_const_fold[where 'a=64])
  apply (rewrite at \<open>(mark_clause_for_unit_as_unchanged \<hole>)\<close> unat_const_fold[where 'a=64])+
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  supply [[goals_limit=1]]
  by sepref

end