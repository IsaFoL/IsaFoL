theory IsaSAT_Setup2_LLVM
  imports IsaSAT_Setup IsaSAT_Watch_List_LLVM IsaSAT_Lookup_Conflict_LLVM
    More_Sepref.WB_More_Refinement IsaSAT_Clauses_LLVM LBD_LLVM
    IsaSAT_Options_LLVM IsaSAT_VMTF_Setup_LLVM
    IsaSAT_Arena_Sorting_LLVM
    IsaSAT_Rephase_LLVM
    IsaSAT_EMA_LLVM
    IsaSAT_Stats_LLVM
    IsaSAT_Setup0_LLVM
begin


sepref_def opts_restart_st_fast_code
  is \<open>RETURN o opts_restart_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding opts_restart_st_def isasat_bounded_assn_def
  by sepref

sepref_def opts_reduction_st_fast_code
  is \<open>RETURN o opts_reduction_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding opts_reduction_st_def isasat_bounded_assn_def
  by sepref

sepref_def opts_unbounded_mode_st_fast_code
  is \<open>RETURN o opts_unbounded_mode_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  supply [[goals_limit=1]]
  unfolding opts_unbounded_mode_st_def isasat_bounded_assn_def
  by sepref

sepref_def opts_minimum_between_restart_st_fast_code
  is \<open>RETURN o opts_minimum_between_restart_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding opts_minimum_between_restart_st_def isasat_bounded_assn_def
  by sepref

sepref_def opts_restart_coeff1_st_fast_code
  is \<open>RETURN o opts_restart_coeff1_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding opts_restart_coeff1_st_def isasat_bounded_assn_def
  by sepref

sepref_def opts_restart_coeff2_st_fast_code
  is \<open>RETURN o opts_restart_coeff2_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a snat_assn' (TYPE(64))\<close>
  unfolding opts_restart_coeff2_st_def isasat_bounded_assn_def
  by sepref

sepref_register opts_reduction_st opts_restart_st opts_restart_coeff2_st opts_restart_coeff1_st
    opts_minimum_between_restart_st opts_unbounded_mode_st

sepref_register isasat_length_trail_st

sepref_def isasat_length_trail_st_code
  is \<open>RETURN o isasat_length_trail_st\<close>
  :: \<open>[isa_length_trail_pre o get_trail_wl_heur]\<^sub>a isasat_bounded_assn\<^sup>k  \<rightarrow> sint64_nat_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_length_trail_st_alt_def isasat_bounded_assn_def
  by sepref

sepref_def mop_isasat_length_trail_st_code
  is \<open>mop_isasat_length_trail_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k  \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  supply [[goals_limit=1]]
  unfolding mop_isasat_length_trail_st_alt_def isasat_bounded_assn_def
  by sepref

sepref_register get_pos_of_level_in_trail_imp_st

sepref_def get_pos_of_level_in_trail_imp_st_code
  is \<open>uncurry get_pos_of_level_in_trail_imp_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k  \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  supply [[goals_limit=1]]
  unfolding get_pos_of_level_in_trail_imp_alt_def isasat_bounded_assn_def
  apply (rewrite in \<open>_\<close> eta_expand[where f = RETURN])
  apply (rewrite in \<open>RETURN \<hole>\<close> annot_unat_snat_upcast[where 'l=64])
  by sepref


lemma clause_not_marked_to_delete_heur_alt_def:
  \<open>RETURN oo clause_not_marked_to_delete_heur = (\<lambda>(M, arena, D, oth) C.
      RETURN (arena_status arena C \<noteq> DELETED))\<close>
  unfolding clause_not_marked_to_delete_heur_def by (auto intro!: ext)

sepref_def clause_not_marked_to_delete_heur_fast_code
  is \<open>uncurry (RETURN oo clause_not_marked_to_delete_heur)\<close>
  :: \<open>[clause_not_marked_to_delete_heur_pre]\<^sub>a isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> bool1_assn\<close>
  supply [[goals_limit=1]]
  unfolding clause_not_marked_to_delete_heur_alt_def isasat_bounded_assn_def
     clause_not_marked_to_delete_heur_pre_def
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

sepref_def mop_arena_lbd_st_impl
  is \<open>uncurry mop_arena_lbd_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=1]]
  unfolding mop_arena_lbd_st_alt_def isasat_bounded_assn_def
  by sepref

sepref_def mop_arena_status_st_impl
  is \<open>uncurry mop_arena_status_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a status_impl_assn\<close>
  supply [[goals_limit=1]]
  unfolding mop_arena_status_st_alt_def isasat_bounded_assn_def
  by sepref

sepref_def mop_marked_as_used_st_impl
  is \<open>uncurry mop_marked_as_used_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a unat_assn' TYPE(2)\<close>
  supply [[goals_limit=1]]
  unfolding mop_marked_as_used_st_alt_def isasat_bounded_assn_def
  by sepref

sepref_def mop_arena_length_st_impl
  is \<open>uncurry mop_arena_length_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  supply [[goals_limit=1]]
  unfolding mop_arena_length_st_alt_def isasat_bounded_assn_def
  by sepref

sepref_register incr_wasted_st full_arena_length_st wasted_bytes_st
sepref_def incr_wasted_st_impl
  is \<open>uncurry (RETURN oo incr_wasted_st)\<close>
  :: \<open>word64_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply[[goals_limit=1]]
  unfolding incr_wasted_st_def incr_wasted.simps
    isasat_bounded_assn_def heuristic_assn_def fold_tuple_optimizations
  by sepref

sepref_def full_arena_length_st_impl
  is \<open>RETURN o full_arena_length_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  unfolding full_arena_length_st_def isasat_bounded_assn_def
  by sepref

end