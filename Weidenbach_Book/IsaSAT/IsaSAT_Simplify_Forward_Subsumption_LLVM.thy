theory IsaSAT_Simplify_Forward_Subsumption_LLVM
  imports
    IsaSAT_Simplify_Forward_Subsumption
    IsaSAT_Simplify_Clause_Units_LLVM
begin

no_notation WB_More_Refinement.fref (\<open>[_]\<^sub>f _ \<rightarrow> _\<close> [0,60,60] 60)
no_notation WB_More_Refinement.freft (\<open>_ \<rightarrow>\<^sub>f _\<close> [60,60] 60)

sepref_register isa_forward_subsumption_all

sepref_def isa_forward_subsumption_all
  is \<open>isa_forward_subsumption_all\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding isa_forward_subsumption_all_def
  by sepref

end