theory IsaSAT_VMTF_State_LLVM
  imports IsaSAT_VMTF_LLVM IsaSAT_Setup_LLVM
begin
lemma find_decomp_wl_st_int_alt_def:
  \<open>find_decomp_wl_st_int = (\<lambda>highest S. do{
     let (M, S) = extract_trail_wl_heur S;
     let (vm, S) = extract_vmtf_wl_heur S;
     (M', vm) \<leftarrow> isa_find_decomp_wl_imp M highest vm;
     let S = update_trail_wl_heur M' S;
     let S = update_vmtf_wl_heur vm S;
     RETURN S
  })\<close>
  by (auto simp: find_decomp_wl_st_int_def state_extractors intro!: ext split: isasat_int.splits)

sepref_def find_decomp_wl_imp'_fast_code
  is \<open>uncurry find_decomp_wl_st_int\<close>
  :: \<open>uint32_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d  \<rightarrow>\<^sub>a
        isasat_bounded_assn\<close>
  unfolding find_decomp_wl_st_int_alt_def PR_CONST_def
  supply [[goals_limit = 1]]
  by sepref

experiment begin

export_llvm
  find_decomp_wl_imp'_fast_code

end

end