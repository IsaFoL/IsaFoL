theory IsaSAT_Simplify_Units_LLVM
  imports
    IsaSAT_Simplify_Clause_Units_LLVM
begin


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

sepref_def isa_simplify_clauses_with_units_st_wl2_code
  is isa_simplify_clauses_with_units_st_wl2
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max \<and> learned_clss_count S \<le> uint64_max]\<^sub>a
     isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding isa_simplify_clauses_with_units_st_wl2_def
  supply [[goals_limit=1]]
  by sepref

end