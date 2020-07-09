theory IsaSAT_Setup_LLVM
  imports 
    IsaSAT_Setup1_LLVM
    IsaSAT_Setup2_LLVM
    IsaSAT_Setup3_LLVM
begin


subsubsection \<open>Lift Operations to State\<close>

experiment begin

export_llvm
  ema_update_impl
  VMTF_Node_impl
  VMTF_stamp_impl
  VMTF_get_prev_impl
  VMTF_get_next_impl
  get_conflict_wl_is_None_fast_code
  isa_count_decided_st_fast_code
  polarity_st_heur_pol_fast
  count_decided_st_heur_pol_fast
  access_lit_in_clauses_heur_fast_code
  rewatch_heur_fast_code
  rewatch_heur_st_fast_code
  set_zero_wasted_impl
  opts_restart_st_fast_code
  opts_unbounded_mode_st_fast_code

end

end
