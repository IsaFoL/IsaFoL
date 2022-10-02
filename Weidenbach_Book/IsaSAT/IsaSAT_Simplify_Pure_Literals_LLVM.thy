theory IsaSAT_Simplify_Pure_Literals_LLVM
  imports IsaSAT_Restart_Defs
    IsaSAT_Simplify_Pure_Literals_Defs
    IsaSAT_Setup_LLVM IsaSAT_Trail_LLVM
    IsaSAT_Proofs_LLVM
begin

no_notation WB_More_Refinement.fref (\<open>[_]\<^sub>f _ \<rightarrow> _\<close> [0,60,60] 60)
no_notation WB_More_Refinement.freft (\<open>_ \<rightarrow>\<^sub>f _\<close> [60,60] 60)

sepref_register mop_arena_status_st isa_pure_literal_count_occs_clause_wl
sepref_def isa_pure_literal_count_occs_clause_wl_code
  is \<open>uncurry3 isa_pure_literal_count_occs_clause_wl\<close>
  :: \<open>[\<lambda>(((C, S), _), _). length (get_clauses_wl_heur S) \<le> sint64_max \<and> learned_clss_count S \<le> uint64_max]\<^sub>a
    sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>k *\<^sub>a (larray_assn' TYPE(64) bool1_assn)\<^sup>d *\<^sub>a word64_assn\<^sup>d  \<rightarrow> larray_assn' TYPE(64) bool1_assn \<times>\<^sub>a word64_assn\<close>
  unfolding isa_pure_literal_count_occs_clause_wl_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_register isa_pure_literal_count_occs_wl
sepref_def isa_pure_literal_count_occs_wl_code
  is isa_pure_literal_count_occs_wl
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max \<and> learned_clss_count S \<le> uint64_max]\<^sub>a
     isasat_bounded_assn\<^sup>k \<rightarrow> bool1_assn \<times>\<^sub>a larray_assn' TYPE(64) bool1_assn\<close>
  unfolding isa_pure_literal_count_occs_wl_def nth_append Let_def
    larray_fold_custom_replicate mop_arena_status_st_def[symmetric]
    access_ivdom_at_def[symmetric] length_avdom_def[symmetric] length_ivdom_def[symmetric]
    access_avdom_at_def[symmetric] length_watchlist_raw_def[symmetric] length_append
  supply of_nat_snat[sepref_import_param]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

lemma isa_propagate_pure_bt_wl_alt_def:
    \<open>isa_propagate_pure_bt_wl = (\<lambda>L S. do {
      let (M, S) = extract_trail_wl_heur S;
      let (stats, S) = extract_stats_wl_heur S;
      ASSERT(0 \<noteq> DECISION_REASON);
      ASSERT(cons_trail_Propagated_tr_pre ((L, 0::nat), M));
      M \<leftarrow> cons_trail_Propagated_tr (L) 0 M;
      let stats = incr_units_since_last_GC (incr_uset (incr_purelit_elim stats));
      let S = update_stats_wl_heur stats S;
      let S = update_trail_wl_heur M S;
      let _ = log_unit_clause L;
      RETURN S})\<close>
  unfolding isa_propagate_pure_bt_wl_def log_unit_clause_def
  by (auto simp: empty_US_heur_def state_extractors Let_def intro!: ext split: isasat_int_splits)

sepref_register isa_propagate_pure_bt_wl cons_trail_Propagated_tr
sepref_def isa_propagate_pure_bt_wl_code
  is \<open>uncurry isa_propagate_pure_bt_wl\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding isa_propagate_pure_bt_wl_alt_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

lemma isa_pure_literal_deletion_wl_alt_def:
 \<open>isa_pure_literal_deletion_wl occs S\<^sub>0 = (do {
  ASSERT (isa_pure_literal_deletion_wl_pre S\<^sub>0);
  (_, eliminated, S) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(n, _, S). get_vmtf_heur_array S\<^sub>0 = get_vmtf_heur_array S\<^esup> (\<lambda>(n, x). n \<noteq> None)
    (\<lambda>(n, eliminated, T). do {
       ASSERT (n \<noteq> None);
       let A = the n;
       ASSERT (A < length (get_vmtf_heur_array S\<^sub>0));
       ASSERT (A \<le> uint32_max div 2);
       ASSERT (get_vmtf_heur_array S\<^sub>0 = get_vmtf_heur_array T);
       ASSERT (nat_of_lit (Pos A) < length occs);
       ASSERT (nat_of_lit (Neg A) < length occs);
       let L = (if occs ! nat_of_lit (Pos A) \<and> \<not> occs ! nat_of_lit (Neg A) then Pos A else Neg A);
       ASSERT (nat_of_lit (- L) < length occs);
       val \<leftarrow> mop_polarity_pol (get_trail_wl_heur T) L;
       if \<not> occs ! nat_of_lit (- L) \<and> val = None then do {
          S \<leftarrow> isa_propagate_pure_bt_wl L T;
          ASSERT (get_vmtf_heur_array S\<^sub>0 = get_vmtf_heur_array S);
          RETURN (get_next (get_vmtf_heur_array S ! A),eliminated + 1, S)
       }
       else RETURN (get_next (get_vmtf_heur_array T ! A),eliminated, T)
     })
    (Some (get_vmtf_heur_fst S\<^sub>0), 0, S\<^sub>0);
   mop_free occs;
  RETURN (eliminated, S)
         })\<close>
  unfolding isa_pure_literal_deletion_wl_def mop_free_def
  by auto

sepref_def isa_pure_literal_deletion_wl_code
  is \<open>uncurry isa_pure_literal_deletion_wl\<close>
  :: \<open>[\<lambda>(_, S). length (get_clauses_wl_heur S) \<le> sint64_max \<and> learned_clss_count S \<le> uint64_max]\<^sub>a
     (larray_assn' TYPE(64) bool1_assn)\<^sup>d *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> word64_assn \<times>\<^sub>a isasat_bounded_assn\<close>
  unfolding isa_pure_literal_deletion_wl_alt_def nres_monad3 nres_monad2
    get_vmtf_heur_array_nth_def[symmetric] UNSET_def[symmetric] atom.fold_option
    mop_polarity_st_heur_def[symmetric] tri_bool_eq_def[symmetric]
    get_vmtf_heur_array_nth_def[symmetric] prod.simps
  by sepref

end