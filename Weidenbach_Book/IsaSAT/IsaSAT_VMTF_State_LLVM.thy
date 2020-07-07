theory IsaSAT_VMTF_State_LLVM
  imports IsaSAT_VMTF_LLVM IsaSAT_Setup_LLVM
begin

sepref_def find_decomp_wl_imp'_fast_code
  is \<open>uncurry find_decomp_wl_st_int\<close>
  :: \<open>uint32_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d  \<rightarrow>\<^sub>a
        isasat_bounded_assn\<close>
  unfolding find_decomp_wl_st_int_def PR_CONST_def isasat_bounded_assn_def
  supply [[goals_limit = 1]]
  unfolding fold_tuple_optimizations
  by sepref

experiment begin

export_llvm
  find_decomp_wl_imp'_fast_code

end

end