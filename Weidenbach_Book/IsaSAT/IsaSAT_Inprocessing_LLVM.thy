theory IsaSAT_Inprocessing_LLVM
  imports
    IsaSAT_Restart_Inprocessing_Defs
    IsaSAT_Simplify_Units_LLVM
    IsaSAT_Simplify_Binaries_LLVM
    IsaSAT_Simplify_Forward_Subsumption_LLVM
    IsaSAT_Simplify_Pure_Literals_LLVM
begin

sepref_register 0 1

sepref_register mop_arena_update_lit isa_pure_literal_count_occs_wl
    isa_pure_literal_elimination_round_wl incr_purelit_rounds_st


sepref_def should_inprocess_st
  is \<open>RETURN o should_inprocess_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding should_inprocess_st_def
  by sepref

lemma [simp]: \<open>get_clauses_wl_heur (incr_purelit_rounds_st S) = get_clauses_wl_heur S\<close>
  \<open>learned_clss_count (incr_purelit_rounds_st S) = learned_clss_count S\<close>
  by (auto simp: incr_purelit_rounds_st_def)


sepref_def isa_pure_literal_elimination_round_wl_code
  is isa_pure_literal_elimination_round_wl
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max \<and> learned_clss_count S \<le> uint64_max]\<^sub>a
     isasat_bounded_assn\<^sup>d \<rightarrow> word64_assn \<times>\<^sub>a isasat_bounded_assn\<close>
  unfolding isa_pure_literal_elimination_round_wl_def
  by sepref

lemma schedule_next_pure_lits_st_alt_def:
  \<open>schedule_next_pure_lits_st S =
      (let (heur, S) = extract_heur_wl_heur S;
        heur = (schedule_next_pure_lits (heur))in
     update_heur_wl_heur heur S)\<close>
  by (auto simp: schedule_next_pure_lits_st_def state_extractors split: isasat_int_splits
    intro!: ext)

sepref_def schedule_next_pure_lits_st_impl
  is \<open>RETURN o schedule_next_pure_lits_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding schedule_next_pure_lits_st_alt_def
  by sepref

sepref_def isa_pure_literal_elimination_wl_code
  is isa_pure_literal_elimination_wl
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max \<and> learned_clss_count S \<le> uint64_max]\<^sub>a
     isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding isa_pure_literal_elimination_wl_def Let_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_def isa_pure_literal_eliminate_code
  is isa_pure_literal_eliminate
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max \<and> learned_clss_count S \<le> uint64_max]\<^sub>a
     isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding isa_pure_literal_eliminate_def
  by sepref

(*TODO Move*)
lemmas [llvm_code] = is_NONE_impl_def is_subsumed_impl_def is_strengthened_impl_def
  STRENGTHENED_BY_impl_def SUBSUMED_BY_impl_def NONE_impl_def subsumed_by_impl_def
  strengthened_on_lit_impl_def

lemmas [unfolded inline_direct_return_node_case, llvm_code]  =
  get_occs_list_at_impl_def[unfolded read_all_st_code_def]
(*end move*)
experiment
begin
 export_llvm isa_simplify_clauses_with_unit_st2_code
    isa_simplify_clauses_with_units_st_wl2_code
    isa_deduplicate_binary_clauses_code
    isa_forward_subsumption_all_impl
end

end
