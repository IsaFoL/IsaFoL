theory IsaSAT_Inprocessing_LLVM
  imports
    IsaSAT_Restart_Inprocessing
    IsaSAT_Simplify_Units_LLVM
    IsaSAT_Simplify_Binaries_LLVM
    IsaSAT_Simplify_Forward_Subsumption_LLVM
    IsaSAT_Simplify_Pure_Literals_LLVM
begin

no_notation WB_More_Refinement.fref (\<open>[_]\<^sub>f _ \<rightarrow> _\<close> [0,60,60] 60)
no_notation WB_More_Refinement.freft (\<open>_ \<rightarrow>\<^sub>f _\<close> [60,60] 60)

sepref_register 0 1

sepref_register mop_arena_update_lit



sepref_def isa_pure_literal_elimination_round_wl_code
  is isa_pure_literal_elimination_round_wl
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max \<and> learned_clss_count S \<le> uint64_max]\<^sub>a
     isasat_bounded_assn\<^sup>d \<rightarrow> word64_assn \<times>\<^sub>a isasat_bounded_assn\<close>
  unfolding isa_pure_literal_elimination_round_wl_def
  by sepref


sepref_def isa_pure_literal_elimination_wl_code
  is isa_pure_literal_elimination_wl
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max \<and> learned_clss_count S \<le> uint64_max]\<^sub>a
     isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding isa_pure_literal_elimination_wl_def Let_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

experiment
begin
 export_llvm isa_simplify_clauses_with_unit_st2_code
    isa_simplify_clauses_with_units_st_wl2_code
    isa_deduplicate_binary_clauses_code
end

end
