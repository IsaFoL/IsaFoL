theory IsaSAT_Setup_LLVM
  imports
    IsaSAT_Setup1_LLVM
    IsaSAT_Setup2_LLVM
    IsaSAT_Setup3_LLVM
    IsaSAT_Setup4_LLVM
    IsaSAT_Profile_LLVM
begin


subsubsection \<open>Lift Operations to State\<close>

sepref_def mark_added_clause_heur2_impl
  is \<open>uncurry mark_added_clause_heur2\<close>
  :: \<open>isasat_bounded_assn\<^sup>d *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding mark_added_clause_heur2_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_def maybe_mark_added_clause_heur2_impl
  is \<open>uncurry maybe_mark_added_clause_heur2\<close>
  :: \<open>isasat_bounded_assn\<^sup>d *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding maybe_mark_added_clause_heur2_def
  by sepref

experiment begin
lemma from_bool1: "from_bool True = 1"
  by auto
lemmas [llvm_pre_simp] = from_bool1
lemmas [unfolded inline_direct_return_node_case, llvm_code] =
  remove_d_code_def[unfolded isasat_state.remove_d_code_def]

export_llvm
  ema_update_impl
  VMTF_Node_impl
  VMTF_stamp_impl
  VMTF_get_prev_impl
  VMTF_get_next_impl
  get_conflict_wl_is_None_fast_code
  isa_count_decided_st_fast_code
  polarity_st_heur_pol_fast
  isa_count_decided_st_fast_code
  access_lit_in_clauses_heur_fast_code
  rewatch_heur_fast_code
  rewatch_heur_st_fast_code
  set_zero_wasted_impl
  opts_restart_st_fast_code
  opts_unbounded_mode_st_fast_code

end

end
