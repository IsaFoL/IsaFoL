theory IsaSAT_Decide_LLVM
  imports IsaSAT_Decide IsaSAT_VMTF_State_LLVM IsaSAT_Setup_LLVM IsaSAT_Rephase_State_LLVM
begin


sepref_def decide_lit_wl_fast_code
  is \<open>uncurry decide_lit_wl_heur\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding decide_lit_wl_heur_def isasat_bounded_assn_def
  (*supply hn_case_prod'[sepref_comb_rules del]*)
  unfolding fold_tuple_optimizations
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_constraints
  done



sepref_register find_unassigned_lit_wl_D_heur decide_lit_wl_heur

sepref_register isa_vmtf_find_next_undef

sepref_def isa_vmtf_find_next_undef_code is
  \<open>uncurry isa_vmtf_find_next_undef\<close> :: \<open>vmtf_remove_assn\<^sup>k *\<^sub>a trail_pol_fast_assn\<^sup>k \<rightarrow>\<^sub>a atom.option_assn\<close>
  unfolding isa_vmtf_find_next_undef_def vmtf_remove_assn_def
  unfolding atom.fold_option
  apply (rewrite in \<open>WHILEIT _ \<hole>\<close> short_circuit_conv)
  supply [[goals_limit = 1]]
  apply annot_all_atm_idxs
  by sepref

sepref_register update_next_search
sepref_def update_next_search_code is
  \<open>uncurry (RETURN oo update_next_search)\<close> :: \<open>atom.option_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>d \<rightarrow>\<^sub>a vmtf_remove_assn\<close>
  unfolding update_next_search_def vmtf_remove_assn_def
  by sepref

sepref_register isa_vmtf_find_next_undef_upd  mop_get_saved_phase_heur get_next_phase_st
sepref_def isa_vmtf_find_next_undef_upd_code is
  \<open>uncurry isa_vmtf_find_next_undef_upd\<close>
    :: \<open>trail_pol_fast_assn\<^sup>d *\<^sub>a vmtf_remove_assn\<^sup>d \<rightarrow>\<^sub>a (trail_pol_fast_assn \<times>\<^sub>a vmtf_remove_assn) \<times>\<^sub>a atom.option_assn\<close>
  unfolding isa_vmtf_find_next_undef_upd_def
  by sepref

sepref_register find_unassigned_lit_wl_D_heur2
sepref_def find_unassigned_lit_wl_D_heur_impl
  is \<open>find_unassigned_lit_wl_D_heur2\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn \<times>\<^sub>a atom.option_assn\<close>
  unfolding find_unassigned_lit_wl_D_heur2_def isasat_bounded_assn_def
    fold_tuple_optimizations
  by sepref

sepref_def get_next_phase_st_impl
  is \<open>uncurry2 get_next_phase_st\<close>
  :: \<open>bool1_assn\<^sup>k *\<^sub>a atom_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding get_next_phase_st_def isasat_bounded_assn_def
  by sepref

sepref_def decide_wl_or_skip_D_fast_code
  is \<open>decide_wl_or_skip_D_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a bool1_assn \<times>\<^sub>a isasat_bounded_assn\<close>
  supply[[goals_limit=1]]
  apply (rule hfref_refine_with_pre[OF decide_wl_or_skip_D_heur'_decide_wl_or_skip_D_heur, unfolded Down_id_eq])
  unfolding decide_wl_or_skip_D_heur'_def
  unfolding fold_tuple_optimizations option.case_eq_if atom.fold_option
  by sepref


experiment begin

export_llvm
  decide_lit_wl_fast_code
  isa_vmtf_find_next_undef_code
  update_next_search_code
  isa_vmtf_find_next_undef_upd_code
  decide_wl_or_skip_D_fast_code

end


end
