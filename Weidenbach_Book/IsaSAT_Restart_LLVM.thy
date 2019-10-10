theory IsaSAT_Restart_LLVM
  imports IsaSAT_Restart IsaSAT_Restart_Heuristics_LLVM IsaSAT_CDCL_LLVM
begin

sepref_register length_avdom

sepref_register clause_is_learned_heur

(*TODO Move: replace other verision*)
lemma length_avdom_alt_def:
  \<open>length_avdom = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, heur, vdom, avdom, lcount). length avdom)\<close>
  by (intro ext) (auto simp: length_avdom_def)

lemma get_the_propagation_reason_heur_alt_def:
  \<open>get_the_propagation_reason_heur = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, heur, vdom, lcount) L .
    get_the_propagation_reason_pol M' L)\<close>
  by (intro ext) (auto simp: get_the_propagation_reason_heur_def)

(*END Move*)

sepref_def length_avdom_fast_code
  is \<open>RETURN o length_avdom\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  unfolding length_avdom_alt_def access_vdom_at_pre_def isasat_bounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

sepref_register get_the_propagation_reason_heur

sepref_def get_the_propagation_reason_heur_fast_code
  is \<open>uncurry get_the_propagation_reason_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a snat_option_assn' TYPE(64)\<close>
  unfolding get_the_propagation_reason_heur_alt_def access_vdom_at_pre_def
     isasat_bounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

(*TODO Move: rplace*)

lemma clause_is_learned_heur_alt_def:
  \<open>clause_is_learned_heur = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, heur,
    vdom, lcount) C . arena_status N' C = LEARNED)\<close>
  by (intro ext) (auto simp: clause_is_learned_heur_def)
(*ENED Move*)

sepref_def clause_is_learned_heur_code2
  is \<open>uncurry (RETURN oo clause_is_learned_heur)\<close>
  :: \<open>[\<lambda>(S, C). arena_is_valid_clause_vdom (get_clauses_wl_heur S) C]\<^sub>a
      isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> bool1_assn\<close>
  supply [[goals_limit = 1]]
  unfolding clause_is_learned_heur_alt_def isasat_bounded_assn_def
  by sepref

sepref_register clause_lbd_heur


lemma clause_lbd_heur_alt_def:
  \<open>clause_lbd_heur = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, heur, vdom, lcount) C.
     arena_lbd N' C)\<close>
  by (intro ext) (auto simp: clause_lbd_heur_def)

sepref_def clause_lbd_heur_code2
  is \<open>uncurry (RETURN oo clause_lbd_heur)\<close>
  :: \<open>[\<lambda>(S, C). get_clause_LBD_pre (get_clauses_wl_heur S) C]\<^sub>a
       isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  unfolding isasat_bounded_assn_def clause_lbd_heur_alt_def
  supply [[goals_limit = 1]]
  by sepref

sepref_register mark_garbage_heur


sepref_def mark_garbage_heur_code2
  is \<open>uncurry2 (RETURN ooo mark_garbage_heur)\<close>
  :: \<open>[\<lambda>((C, i), S). mark_garbage_pre (get_clauses_wl_heur S, C) \<and> i < length_avdom S \<and>
         get_learned_count S \<ge> 1]\<^sub>a
       sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit = 1]]
  unfolding mark_garbage_heur_def isasat_bounded_assn_def delete_index_and_swap_alt_def
    length_avdom_def fold_tuple_optimizations
  apply (annot_unat_const "TYPE(64)")
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
       isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> bool1_assn\<close>
  supply [[goals_limit = 1]]
  unfolding marked_as_used_st_alt_def isasat_bounded_assn_def fold_tuple_optimizations
  by sepref

lemma arena_act_pre_mark_used:
  \<open>arena_act_pre arena C \<Longrightarrow>
  arena_act_pre (mark_unused arena C) C\<close>
  unfolding arena_act_pre_def arena_is_valid_clause_idx_def
  apply clarify
  apply (rule_tac x=N in exI)
  apply (rule_tac x=vdom in exI)
  by (auto simp: arena_act_pre_def
    simp: valid_arena_mark_unused)


sepref_register mark_unused_st_heur
sepref_def mark_unused_st_fast_code
  is \<open>uncurry (RETURN oo mark_unused_st_heur)\<close>
  :: \<open>[\<lambda>(C, S). arena_act_pre (get_clauses_wl_heur S) C]\<^sub>a
        sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding mark_unused_st_heur_def isasat_bounded_assn_def
    arena_act_pre_mark_used[intro!]
  supply [[goals_limit = 1]]
  by sepref

sepref_register mark_clauses_as_unused_wl_D_heur

declare clause_not_marked_to_delete_heur_fast_code.refine[sepref_fr_rules]

sepref_def mark_clauses_as_unused_wl_D_heur_fast_code
  is \<open>uncurry mark_clauses_as_unused_wl_D_heur\<close>
  :: \<open>[\<lambda>(_, S). length (get_avdom S) \<le> sint64_max]\<^sub>a
    sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]] length_avdom_def[simp]
  unfolding mark_clauses_as_unused_wl_D_heur_def
    mark_unused_st_heur_def[symmetric]
    access_vdom_at_def[symmetric] length_avdom_def[symmetric]
  apply (annot_snat_const "TYPE(64)")
  by sepref


sepref_register mark_to_delete_clauses_wl_D_heur

sepref_def MINIMUM_DELETION_LBD_impl
  is \<open>uncurry0 (RETURN MINIMUM_DELETION_LBD)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding MINIMUM_DELETION_LBD_def
  apply (annot_unat_const "TYPE(32)")
  by sepref

lemma mop_clause_not_marked_to_delete_heur_alt_def:
  \<open>mop_clause_not_marked_to_delete_heur = (\<lambda>(M, arena, D, oth) C. do {
    ASSERT(clause_not_marked_to_delete_heur_pre ((M, arena, D, oth), C));
     RETURN (arena_status arena C \<noteq> DELETED)
   })\<close>
  unfolding clause_not_marked_to_delete_heur_def mop_clause_not_marked_to_delete_heur_def
  by (auto intro!: ext)

sepref_def mop_clause_not_marked_to_delete_heur_impl
  is \<open>uncurry mop_clause_not_marked_to_delete_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding mop_clause_not_marked_to_delete_heur_alt_def
    clause_not_marked_to_delete_heur_pre_def  prod.case isasat_bounded_assn_def
  by sepref


lemma mop_mark_garbage_heur_alt_def:
  \<open>mop_mark_garbage_heur C i = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, heur,
       vdom, avdom, lcount, opts, old_arena). do {
    ASSERT(mark_garbage_pre (get_clauses_wl_heur (M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, heur,
       vdom, avdom, lcount, opts, old_arena), C) \<and> get_learned_count (M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, heur,
       vdom, avdom, lcount, opts, old_arena) \<ge> 1 \<and> i < length avdom);
    RETURN (M', extra_information_mark_to_delete N' C, D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats,
      heur,
       vdom, delete_index_and_swap avdom i, lcount - 1, opts, old_arena)
   })\<close>
  unfolding mop_mark_garbage_heur_def mark_garbage_heur_def
  by (auto intro!: ext)

sepref_def mop_mark_garbage_heur_impj
  is \<open>uncurry2 mop_mark_garbage_heur\<close>
  :: \<open>[\<lambda>((C, i), S). length (get_clauses_wl_heur S) < sint64_max]\<^sub>a
      sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding mop_mark_garbage_heur_alt_def
    clause_not_marked_to_delete_heur_pre_def prod.case isasat_bounded_assn_def
  apply (annot_unat_const "TYPE(64)")
  apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  apply sepref_dbg_side_unfold
oops
  by sepref
(*mop_mark_garbage_heur mop_mark_unused_st_heur mop_arena_lbd 
  mop_arena_status mop_marked_as_used*)

lemma mop_mark_unused_st_heur_alt_def:
  \<open>mop_mark_unused_st_heur C = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, heur,
       vdom, avdom, lcount, opts, old_arena). do {
    ASSERT(mark_garbage_pre (get_clauses_wl_heur (M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, heur,
       vdom, avdom, lcount, opts, old_arena), C) \<and> get_learned_count (M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, heur,
       vdom, avdom, lcount, opts, old_arena) \<ge> 1);
    RETURN (M', mop_mark_unused_st_heur N' C, D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats,
      heur,
       vdom, delete_index_and_swap avdom i, lcount - 1, opts, old_arena)
   })\<close>
  unfolding mop_mark_garbage_heur_def mark_garbage_heur_def
  by (auto intro!: ext)

sepref_def mop_mark_unused_st_heur_impl
  is \<open>uncurry2 mop_mark_unused_st_heur\<close>
  :: \<open>[\<lambda>(C, S). length (get_clauses_wl_heur S) < sint64_max]\<^sub>a
      sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding mop_mark_garbage_heur_alt_def
    clause_not_marked_to_delete_heur_pre_def prod.case isasat_bounded_assn_def
  by sepref

sepref_def mark_to_delete_clauses_wl_D_heur_fast_impl
  is \<open>mark_to_delete_clauses_wl_D_heur\<close>
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding mark_to_delete_clauses_wl_D_heur_def
    access_vdom_at_def[symmetric] length_avdom_def[symmetric]
    get_the_propagation_reason_heur_def[symmetric]
    clause_is_learned_heur_def[symmetric]
    clause_lbd_heur_def[symmetric]
    access_length_heur_def[symmetric]
    short_circuit_conv mark_to_delete_clauses_wl_D_heur_is_Some_iff
    marked_as_used_st_def[symmetric] if_conn(4)
    fold_tuple_optimizations
  supply [[goals_limit = 1]]
    length_avdom_def[symmetric, simp] access_vdom_at_def[simp]
  apply (annot_snat_const "TYPE(64)")
  apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  apply sepref_dbg_side_unfold
oops
  by sepref

sepref_register cdcl_twl_full_restart_wl_prog_heur

sepref_def cdcl_twl_full_restart_wl_prog_heur_fast_code
  is \<open>cdcl_twl_full_restart_wl_prog_heur\<close>
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a  isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding cdcl_twl_full_restart_wl_prog_heur_def
  supply [[goals_limit = 1]]
  by sepref

sepref_definition cdcl_twl_restart_wl_heur_code
  is \<open>cdcl_twl_restart_wl_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  unfolding cdcl_twl_restart_wl_heur_def
  supply [[goals_limit = 1]]
  by sepref

sepref_def cdcl_twl_restart_wl_heur_fast_code
  is \<open>cdcl_twl_restart_wl_heur\<close>
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding cdcl_twl_restart_wl_heur_def
  supply [[goals_limit = 1]]
  by sepref


sepref_def cdcl_twl_full_restart_wl_D_GC_heur_prog_fast_code
  is \<open>cdcl_twl_full_restart_wl_D_GC_heur_prog\<close>
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding cdcl_twl_full_restart_wl_D_GC_heur_prog_def zero_uint32_nat_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref

sepref_register restart_required_heur cdcl_twl_restart_wl_heur

sepref_def restart_prog_wl_D_heur_fast_code
  is \<open>uncurry2 (restart_prog_wl_D_heur)\<close>
  :: \<open>[\<lambda>((S, _), _). length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a
      isasat_bounded_assn\<^sup>d *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a bool_assn\<^sup>k \<rightarrow> isasat_bounded_assn *a sint64_nat_assn\<close>
  unfolding restart_prog_wl_D_heur_def
  supply [[goals_limit = 1]]
  by sepref

definition isasat_fast_bound where
  \<open>isasat_fast_bound = uint64_max - (uint32_max div 2 + 6)\<close>

lemma isasat_fast_bound[sepref_fr_rules]:
   \<open>(uncurry0 (return 18446744071562067962), uncurry0 (RETURN isasat_fast_bound)) \<in>
   unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint64_nat_rel_def br_def isasat_fast_bound_def
     uint64_max_def uint32_max_def)

sepref_register isasat_fast
sepref_def isasat_fast_code
  is \<open>RETURN o isasat_fast\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding isasat_fast_alt_def isasat_bounded_assn_def isasat_fast_bound_def[symmetric]
  supply [[goals_limit = 1]] uint32_max_nat_hnr[sepref_fr_rules]
  by sepref

declare isasat_fast_code.refine[sepref_fr_rules]


sepref_def cdcl_twl_stgy_restart_prog_wl_heur_fast_code
  is \<open>cdcl_twl_stgy_restart_prog_early_wl_heur\<close>
  :: \<open>[\<lambda>S. isasat_fast S]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_unbounded_assn\<close>
  unfolding cdcl_twl_stgy_restart_prog_early_wl_heur_def
  supply [[goals_limit = 1]] isasat_fast_def[simp]
  by sepref

declare cdcl_twl_stgy_restart_prog_wl_heur_fast_code.refine[sepref_fr_rules]

end
