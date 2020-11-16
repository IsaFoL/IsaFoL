theory IsaSAT_CDCL_LLVM
  imports IsaSAT_CDCL IsaSAT_Propagate_Conflict_LLVM IsaSAT_Other_LLVM
begin
term mset_rel

sepref_def cdcl_twl_stgy_prog_wl_D_code
  is \<open>cdcl_twl_stgy_prog_bounded_wl_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a bool1_assn \<times>\<^sub>a isasat_bounded_assn\<close>
  unfolding cdcl_twl_stgy_prog_bounded_wl_heur_def PR_CONST_def
  supply [[goals_limit = 1]] isasat_fast_length_leD[dest]
  by sepref

declare cdcl_twl_stgy_prog_wl_D_code.refine[sepref_fr_rules]

export_llvm cdcl_twl_stgy_prog_wl_D_code file \<open>code/isasat.ll\<close>


end
