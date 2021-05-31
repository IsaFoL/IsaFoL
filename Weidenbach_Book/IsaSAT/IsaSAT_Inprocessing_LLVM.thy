theory IsaSAT_Inprocessing_LLVM
  imports IsaSAT_Setup_LLVM
    IsaSAT_Restart_Inprocessing
begin

sepref_register isa_simplify_clauses_with_unit_st2
sepref_def isa_simplify_clauses_with_unit_st2_code
  is isa_simplify_clauses_with_unit_st2
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding isa_simplify_clauses_with_unit_st2_alt_def
  by sepref

experiment
begin
  export_llvm isa_simplify_clauses_with_unit_st2_code
end

end