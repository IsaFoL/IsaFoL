theory IsaSAT_Inprocessing_LLVM
  imports IsaSAT_Setup_LLVM IsaSAT_Trail_LLVM
    IsaSAT_Restart_Inprocessing
begin

sepref_register 0 1

sepref_register mop_arena_update_lit

sepref_def isa_simplify_clause_with_unit2_code
  is \<open>uncurry2 isa_simplify_clause_with_unit2\<close>
  :: \<open>[\<lambda>((_, _), N). length (N) \<le> sint64_max]\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>d \<rightarrow>
  bool1_assn \<times>\<^sub>a arena_fast_assn \<times>\<^sub>a unat_lit_assn \<times>\<^sub>a  bool1_assn \<times>\<^sub>a uint32_nat_assn\<close>
  unfolding isa_simplify_clause_with_unit2_def
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
   if unc then RETURN (update_arena_wl_heur N (update_trail_wl_heur M (update_lcount_wl_heur lcount S)))
   else if b then
   let (stats, S) = extract_stats_wl_heur S in
   RETURN  (update_trail_wl_heur M
     (update_arena_wl_heur N
     (update_stats_wl_heur (if E=LEARNED then stats else decr_irred_clss (stats))
     (update_lcount_wl_heur (if E = LEARNED then clss_size_decr_lcount (lcount) else lcount)
     S))))
   else if i = 1
   then do {
     M \<leftarrow> cons_trail_Propagated_tr L 0 M;
    let (stats, S) = extract_stats_wl_heur S;
     RETURN (update_arena_wl_heur N
     (update_trail_wl_heur M
     (update_stats_wl_heur (if E=LEARNED then stats else decr_irred_clss stats)
     (update_lcount_wl_heur (if E = LEARNED then clss_size_decr_lcount (clss_size_incr_lcountUEk lcount) else lcount)
     S)))) }
   else if i = 0
   then do {
     j \<leftarrow> mop_isa_length_trail M;
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
   else
     RETURN (update_trail_wl_heur M
     (update_lcount_wl_heur lcount
     (update_arena_wl_heur N
     S)))
     })\<close>
     unfolding isa_simplify_clause_with_unit_st2_def
     by (auto simp: state_extractors  split: isasat_int.splits intro!: ext bind_cong[OF refl])

sepref_def isa_simplify_clause_with_unit_st2_code
  is \<open>uncurry isa_simplify_clause_with_unit_st2\<close>
  :: \<open>[\<lambda>(_, S). length (get_clauses_wl_heur S) \<le> sint64_max \<and> learned_clss_count S \<le> uint64_max]\<^sub>a
  sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [simp] = learned_clss_count_def
  unfolding isa_simplify_clause_with_unit_st2_alt_def
    length_avdom_def[symmetric] Suc_eq_plus1[symmetric]
    mop_arena_status_st_def[symmetric]
    fold_tuple_optimizations
  apply (rewrite at \<open>(cons_trail_Propagated_tr _ \<hole>)\<close> snat_const_fold[where 'a=64])
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  supply [[goals_limit=1]]
  by sepref

lemma isa_simplify_clauses_with_unit_st2_alt_def:
  \<open>isa_simplify_clauses_with_unit_st2 S =
  do {
    ASSERT(length (get_avdom S)+length (get_ivdom S) \<le> length (get_vdom S) \<and>
      length (get_vdom S) \<le> length (get_clauses_wl_heur S));
    let m = length (get_avdom S);
    let n = length (get_ivdom S);
    let mn = m+n;
    (_, T) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(i, T). i < mn \<and> get_conflict_wl_is_None_heur T)
      (\<lambda>(i,T). do {
           ASSERT((i < length (get_avdom T) \<longrightarrow> access_avdom_at_pre T i) \<and>
           (i \<ge> length (get_avdom T) \<longrightarrow> access_ivdom_at_pre T (i - length_avdom S)) \<and>
           length_avdom T = length_avdom S \<and>
           length (get_clauses_wl_heur T) = length (get_clauses_wl_heur S) \<and>
            learned_clss_count T \<le> learned_clss_count S);
          let C = (if i < m then access_avdom_at T i else access_ivdom_at T (i - m));
          E \<leftarrow> mop_arena_status (get_clauses_wl_heur T) C;
          if E \<noteq> DELETED then do {
          T \<leftarrow> isa_simplify_clause_with_unit_st2 C T;
          ASSERT(i < length (get_avdom S)+length (get_ivdom S));
          RETURN (i+1, T)
        }
        else do {ASSERT(i < length (get_avdom S)+length (get_ivdom S)); RETURN (i+1,T)}
      })
     (0, S);
    RETURN (reset_units_since_last_GC_st T)
  }\<close>
   unfolding isa_simplify_clauses_with_unit_st2_def bind_to_let_conv Let_def length_avdom_def
  by (auto cong: if_cong intro!: bind_cong[OF refl])

sepref_register length_ivdom access_ivdom_at

sepref_register isa_simplify_clauses_with_unit_st2
sepref_def isa_simplify_clauses_with_unit_st2_code
  is isa_simplify_clauses_with_unit_st2
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max \<and> learned_clss_count S \<le> uint64_max]\<^sub>a
     isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding isa_simplify_clauses_with_unit_st2_alt_def
    length_avdom_def[symmetric] Suc_eq_plus1[symmetric] length_ivdom_def[symmetric]
    mop_arena_status_st_def[symmetric]
   apply (annot_snat_const \<open>TYPE(64)\<close>)
   supply [[goals_limit=1]]
  by sepref

sepref_def isa_simplify_clauses_with_unit_st_wl2_code
  is isa_simplify_clauses_with_unit_st_wl2
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max \<and> learned_clss_count S \<le> uint64_max]\<^sub>a
     isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding isa_simplify_clauses_with_unit_st_wl2_def
  supply [[goals_limit=1]]
  by sepref


sepref_def isa_simplify_clauses_with_units_st_wl2_code
  is isa_simplify_clauses_with_units_st_wl2
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max \<and> learned_clss_count S \<le> uint64_max]\<^sub>a
     isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding isa_simplify_clauses_with_units_st_wl2_def
  supply [[goals_limit=1]]
  by sepref

experiment
begin
  export_llvm isa_simplify_clauses_with_unit_st2_code
    isa_simplify_clauses_with_unit_st_wl2_code
    isa_simplify_clauses_with_units_st_wl2_code
end

end
