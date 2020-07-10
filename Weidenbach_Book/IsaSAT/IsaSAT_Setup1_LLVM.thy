theory IsaSAT_Setup1_LLVM
  imports
    IsaSAT_Setup0_LLVM
begin


(*TODO proper setup to test if the conflict is none*)
sepref_def get_conflict_wl_is_None_fast_code
  is \<open>RETURN o get_conflict_wl_is_None_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding get_conflict_wl_is_None_heur_alt_def isasat_bounded_assn_def length_ll_def[symmetric]
    conflict_option_rel_assn_def
  supply [[goals_limit=1]]
  by sepref


sepref_def isa_count_decided_st_fast_code
  is \<open>RETURN o isa_count_decided_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=2]]
  unfolding isa_count_decided_st_def isasat_bounded_assn_def
  by sepref

sepref_def polarity_st_heur_pol_fast
  is \<open>uncurry (mop_polarity_st_heur)\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a tri_bool_assn\<close>
  unfolding mop_polarity_st_heur_alt_def isasat_bounded_assn_def polarity_st_pre_def
    mop_polarity_st_heur_alt_def
  supply [[goals_limit = 1]]
  by sepref


subsection \<open>More theorems\<close>

lemma count_decided_st_heur_alt_def:
   \<open>count_decided_st_heur = (\<lambda>(M, _). count_decided_pol M)\<close>
  by (auto simp: count_decided_st_heur_def count_decided_pol_def)

sepref_def count_decided_st_heur_pol_fast
  is \<open>RETURN o count_decided_st_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding isasat_bounded_assn_def count_decided_st_heur_alt_def
  supply [[goals_limit = 1]]
  by sepref

sepref_def access_lit_in_clauses_heur_fast_code
  is \<open>uncurry2 (RETURN ooo access_lit_in_clauses_heur)\<close>
  :: \<open>[\<lambda>((S, i), j). access_lit_in_clauses_heur_pre ((S, i), j) \<and>
           length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a
      isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k  *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  supply [[goals_limit=1]] arena_lit_pre_le[dest]
  unfolding isasat_bounded_assn_def access_lit_in_clauses_heur_alt_def
    access_lit_in_clauses_heur_pre_def
  unfolding fold_tuple_optimizations
  by sepref

sepref_def rewatch_heur_st_fast_code
  is \<open>(rewatch_heur_st_fast)\<close>
  :: \<open>[rewatch_heur_st_fast_pre]\<^sub>a
       isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding rewatch_heur_st_def PR_CONST_def rewatch_heur_st_fast_pre_def
    isasat_bounded_assn_def rewatch_heur_st_fast_def
  unfolding fold_tuple_optimizations
  by sepref


sepref_register length_avdom

sepref_def length_avdom_fast_code
  is \<open>RETURN o length_avdom\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  unfolding length_avdom_alt_def isasat_bounded_assn_def fold_tuple_optimizations
  supply [[goals_limit = 1]]
  by sepref

sepref_register get_the_propagation_reason_heur

sepref_def get_the_propagation_reason_heur_fast_code
  is \<open>uncurry get_the_propagation_reason_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a snat_option_assn' TYPE(64)\<close>
  unfolding get_the_propagation_reason_heur_alt_def
     isasat_bounded_assn_def fold_tuple_optimizations
  supply [[goals_limit = 1]]
  by sepref


sepref_def clause_is_learned_heur_code2
  is \<open>uncurry (RETURN oo clause_is_learned_heur)\<close>
  :: \<open>[\<lambda>(S, C). arena_is_valid_clause_vdom (get_clauses_wl_heur S) C]\<^sub>a
      isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> bool1_assn\<close>
  supply [[goals_limit = 1]]
  unfolding clause_is_learned_heur_alt_def isasat_bounded_assn_def fold_tuple_optimizations
  by sepref

sepref_register clause_lbd_heur


lemma clause_lbd_heur_alt_def:
  \<open>clause_lbd_heur = (\<lambda>(M', N', D', j, W', vm, clvls, cach, lbd, outl, stats, heur, vdom,
     lcount) C.
     arena_lbd N' C)\<close>
  by (intro ext) (auto simp: clause_lbd_heur_def)

sepref_def clause_lbd_heur_code2
  is \<open>uncurry (RETURN oo clause_lbd_heur)\<close>
  :: \<open>[\<lambda>(S, C). get_clause_LBD_pre (get_clauses_wl_heur S) C]\<^sub>a
       isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  unfolding isasat_bounded_assn_def clause_lbd_heur_alt_def fold_tuple_optimizations
  supply [[goals_limit = 1]]
  by sepref



sepref_register mark_garbage_heur

sepref_def mop_mark_garbage_heur_impl
  is \<open>uncurry2 mop_mark_garbage_heur\<close>
  :: \<open>[\<lambda>((C, i), S). length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a
      sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding mop_mark_garbage_heur_alt_def
    clause_not_marked_to_delete_heur_pre_def prod.case isasat_bounded_assn_def
    get_clauses_wl_heur.simps
  apply (rewrite in \<open>RETURN \<hole>\<close> fold_tuple_optimizations)
  by sepref

sepref_def mark_garbage_heur_code2
  is \<open>uncurry2 (RETURN ooo mark_garbage_heur)\<close>
  :: \<open>[\<lambda>((C, i), S). mark_garbage_pre (get_clauses_wl_heur S, C) \<and> i < length_avdom S \<and>
         clss_size_lcount (get_learned_count S) \<ge> 1]\<^sub>a
       sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit = 1]]
  unfolding mark_garbage_heur_def isasat_bounded_assn_def delete_index_and_swap_alt_def
    length_avdom_def fold_tuple_optimizations clss_size_decr_lcount_def clss_size_lcount_def
    lcount_assn_def fold_tuple_optimizations
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

lemma mop_mark_garbage_heur3_alt_def:
  \<open>mop_mark_garbage_heur3 C i = (\<lambda>(M', N', D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
       vdom, avdom, lcount, opts, old_arena). do {
    ASSERT(mark_garbage_pre (get_clauses_wl_heur (M', N', D', j, W', vm, clvls, cach, lbd, outl,
       stats, heur, vdom, avdom, lcount, opts, old_arena), C) \<and> clss_size_lcount lcount \<ge> 1 \<and> i < length avdom);
    RETURN (M', extra_information_mark_to_delete N' C, D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
       vdom, delete_index_and_swap avdom i, clss_size_resetUS (clss_size_decr_lcount lcount), opts, old_arena)
   })\<close>
  unfolding mop_mark_garbage_heur3_def mark_garbage_heur3_def
  by (auto intro!: ext)

sepref_def mop_mark_garbage_heur3_impl
  is \<open>uncurry2 mop_mark_garbage_heur3\<close>
  :: \<open>[\<lambda>((C, i), S). length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a
      sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding mop_mark_garbage_heur3_alt_def
    clause_not_marked_to_delete_heur_pre_def prod.case isasat_bounded_assn_def
  by sepref

sepref_register delete_index_vdom_heur


sepref_def delete_index_vdom_heur_fast_code2
  is \<open>uncurry (RETURN oo delete_index_vdom_heur)\<close>
  :: \<open>[\<lambda>(i, S). i < length_avdom S]\<^sub>a
        sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit = 1]]
  unfolding delete_index_vdom_heur_def isasat_bounded_assn_def delete_index_and_swap_alt_def
    length_avdom_def fold_tuple_optimizations
  by sepref

sepref_register access_length_heur

sepref_def access_length_heur_fast_code2
  is \<open>uncurry (RETURN oo access_length_heur)\<close>
  :: \<open>[\<lambda>(S, C). arena_is_valid_clause_idx (get_clauses_wl_heur S) C]\<^sub>a
       isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> sint64_nat_assn\<close>
  supply [[goals_limit = 1]]
  unfolding access_length_heur_alt_def isasat_bounded_assn_def fold_tuple_optimizations
  by sepref

sepref_register marked_as_used_st

sepref_def marked_as_used_st_fast_code
  is \<open>uncurry (RETURN oo marked_as_used_st)\<close>
  :: \<open>[\<lambda>(S, C). marked_as_used_pre (get_clauses_wl_heur S) C]\<^sub>a
       isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> unat_assn' TYPE(2)\<close>
  supply [[goals_limit = 1]]
  unfolding marked_as_used_st_alt_def isasat_bounded_assn_def fold_tuple_optimizations
  by sepref



sepref_def get_slow_ema_heur_fast_code
  is \<open>RETURN o get_slow_ema_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  unfolding get_slow_ema_heur_alt_def isasat_bounded_assn_def heuristic_assn_def fold_tuple_optimizations
  by sepref

sepref_def get_fast_ema_heur_fast_code
  is \<open>RETURN o get_fast_ema_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  unfolding get_fast_ema_heur_alt_def isasat_bounded_assn_def heuristic_assn_def fold_tuple_optimizations
  by sepref

sepref_def get_conflict_count_since_last_restart_heur_fast_code
  is \<open>RETURN o get_conflict_count_since_last_restart_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding get_counflict_count_heur_alt_def isasat_bounded_assn_def heuristic_assn_def fold_tuple_optimizations
  by sepref

sepref_def get_learned_count_fast_code
  is \<open>RETURN o get_learned_count\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a lcount_assn\<close>
  unfolding get_learned_count_alt_def isasat_bounded_assn_def fold_tuple_optimizations
  by sepref

sepref_register clss_size_lcount get_learned_count_number


lemma get_learned_count_number_alt_def:
   \<open>RETURN o get_learned_count_number = (\<lambda>(M, N0, D, Q, W, vm, clvls, cach, lbd, outl,
       stats, _, vdom, avdom, (lcount, _), opts). RETURN (lcount))\<close>
  by (auto simp: clss_size_lcount_def intro!: ext)


sepref_def get_learned_count_number_fast_code
  is \<open>RETURN o get_learned_count_number\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  unfolding isasat_bounded_assn_def get_learned_count_number_alt_def lcount_assn_def
  by sepref

sepref_def learned_clss_count_fast_code
  is \<open>RETURN o learned_clss_count\<close>
  :: \<open>[\<lambda>S. learned_clss_count S \<le> uint64_max]\<^sub>a isasat_bounded_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  unfolding clss_size_allcount_alt_def learned_clss_count_def fold_tuple_optimizations
  by sepref
end