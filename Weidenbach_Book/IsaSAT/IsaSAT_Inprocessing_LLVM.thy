theory IsaSAT_Inprocessing_LLVM
  imports IsaSAT_Setup_LLVM IsaSAT_Trail_LLVM
    IsaSAT_Restart_Inprocessing
begin

sepref_register 0 1

sepref_register mop_arena_update_lit
    term isa_simplify_clause_with_unit2
term mop_arena_update_lit
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

sepref_def isa_simplify_clause_with_unit_st2_code
  is \<open>uncurry isa_simplify_clause_with_unit_st2\<close>
  :: \<open>[\<lambda>(_, S). length (get_clauses_wl_heur S) \<le> sint64_max \<and> learned_clss_count S \<le> uint64_max]\<^sub>a
  sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [simp] = learned_clss_count_def
  unfolding isa_simplify_clause_with_unit_st2_def
    length_avdom_def[symmetric] Suc_eq_plus1[symmetric]
    mop_arena_status_st_def[symmetric] isasat_bounded_assn_def
    fold_tuple_optimizations
  apply (rewrite at \<open>(cons_trail_Propagated_tr _ \<hole>)\<close> snat_const_fold[where 'a=64])
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  supply [[goals_limit=1]]
  by sepref

lemma isa_simplify_clauses_with_unit_st2_alt_def:
  \<open>isa_simplify_clauses_with_unit_st2 S =
  do {
    let n = length (get_avdom S);
    (_, T) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(i, T). i < n \<and> get_conflict_wl_is_None_heur T)
      (\<lambda>(i,T). do {
         ASSERT(i < length (get_avdom T) \<and> access_vdom_at_pre T i \<and>
         length (get_clauses_wl_heur T) = length (get_clauses_wl_heur S) \<and>
         learned_clss_count T \<le> learned_clss_count S);
         let C = access_vdom_at T i;
         E \<leftarrow> mop_arena_status (get_clauses_wl_heur T) C;
         if E \<noteq> DELETED then do {
          T \<leftarrow> isa_simplify_clause_with_unit_st2 C T;
          ASSERT(i < length (get_avdom S));
          RETURN (i+1, T)
        }
        else do {ASSERT(i < length (get_avdom S)); RETURN (i+1,T)}
      })
     (0, S);
    RETURN (reset_units_since_last_GC_st T)
           }\<close>
   unfolding isa_simplify_clauses_with_unit_st2_def bind_to_let_conv Let_def
  by auto

sepref_register isa_simplify_clauses_with_unit_st2
sepref_def isa_simplify_clauses_with_unit_st2_code
  is isa_simplify_clauses_with_unit_st2
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max \<and> learned_clss_count S \<le> uint64_max]\<^sub>a
     isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding isa_simplify_clauses_with_unit_st2_alt_def
    length_avdom_def[symmetric] Suc_eq_plus1[symmetric]
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