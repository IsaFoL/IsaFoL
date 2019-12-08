theory IsaSAT_Decide_LLVM
  imports IsaSAT_Decide IsaSAT_VMTF_LLVM IsaSAT_Setup_LLVM IsaSAT_Rephase_LLVM
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
  "uncurry isa_vmtf_find_next_undef" :: "vmtf_remove_assn\<^sup>k *\<^sub>a trail_pol_fast_assn\<^sup>k \<rightarrow>\<^sub>a atom.option_assn"
  unfolding isa_vmtf_find_next_undef_def vmtf_remove_assn_def
  unfolding atom.fold_option
  apply (rewrite in "WHILEIT _ \<hole>" short_circuit_conv)
  supply [[goals_limit = 1]]
  apply annot_all_atm_idxs
  by sepref

sepref_register update_next_search
sepref_def update_next_search_code is 
  "uncurry (RETURN oo update_next_search)" :: "atom.option_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>d \<rightarrow>\<^sub>a vmtf_remove_assn"
  unfolding update_next_search_def vmtf_remove_assn_def
  by sepref
  
sepref_register isa_vmtf_find_next_undef_upd  mop_get_saved_phase_heur
sepref_def isa_vmtf_find_next_undef_upd_code is 
  "uncurry isa_vmtf_find_next_undef_upd" 
    :: "trail_pol_fast_assn\<^sup>d *\<^sub>a vmtf_remove_assn\<^sup>d \<rightarrow>\<^sub>a (trail_pol_fast_assn *a vmtf_remove_assn) *a atom.option_assn"
  unfolding isa_vmtf_find_next_undef_upd_def
  by sepref

lemma mop_get_saved_phase_heur_alt_def:
  \<open>mop_get_saved_phase_heur = (\<lambda>L (fast_ema, slow_ema, res_info, wasted, \<phi>, target, best). do {
            ASSERT (L < length \<phi>);
            RETURN (\<phi> ! L)
          })\<close>
  unfolding mop_get_saved_phase_heur_def
    get_saved_phase_heur_pre_def get_saved_phase_heur_def
  by auto

sepref_def mop_get_saved_phase_heur_impl
  is \<open>uncurry mop_get_saved_phase_heur\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a heuristic_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding mop_get_saved_phase_heur_alt_def[abs_def] heuristic_assn_def
  apply annot_all_atm_idxs
  by sepref

sepref_def decide_wl_or_skip_D_fast_code
  is \<open>decide_wl_or_skip_D_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a bool1_assn *a isasat_bounded_assn\<close>
  supply[[goals_limit=1]]
    decide_lit_wl_fast_code.refine[unfolded isasat_bounded_assn_def, sepref_fr_rules]
    save_phase_heur_st.refine[unfolded isasat_bounded_assn_def, sepref_fr_rules]
  apply (rule hfref_refine_with_pre[OF decide_wl_or_skip_D_heur'_decide_wl_or_skip_D_heur, unfolded Down_id_eq])
  unfolding decide_wl_or_skip_D_heur'_def isasat_bounded_assn_def
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
