theory IsaSAT_Other_LLVM
  imports IsaSAT_Other IsaSAT_Conflict_Analysis_LLVM IsaSAT_Backtrack_LLVM IsaSAT_Decide_LLVM
begin


sepref_register get_conflict_wl_is_None decide_wl_or_skip_D_heur skip_and_resolve_loop_wl_D_heur
  backtrack_wl_D_nlit_heur isasat_current_status count_decided_st_heur get_conflict_wl_is_None_heur

lemma cdcl_twl_o_prog_wl_D_heurI1:
  \<open>get_learned_count x = get_learned_count xc \<Longrightarrow>
       learned_clss_count x < uint64_max \<Longrightarrow> learned_clss_count xc \<le> uint64_max\<close>
  using get_learned_count_learned_clss_countD2[of xc x]
  by (auto dest: get_learned_count_learned_clss_countD2)

lemma cdcl_twl_o_prog_wl_D_heurI:
  \<open> get_learned_count x = get_learned_count xc \<Longrightarrow>
       learned_clss_count x < uint64_max \<Longrightarrow>  learned_clss_count xc < uint64_max\<close>
  using get_learned_count_learned_clss_countD2[of xc x]
  by auto

sepref_def cdcl_twl_o_prog_wl_D_fast_code
  is \<open>cdcl_twl_o_prog_wl_D_heur\<close>
  :: \<open>[isasat_fast]\<^sub>a
      isasat_bounded_assn\<^sup>d \<rightarrow> bool1_assn \<times>\<^sub>a isasat_bounded_assn\<close>
  unfolding cdcl_twl_o_prog_wl_D_heur_def PR_CONST_def
  unfolding get_conflict_wl_is_None get_conflict_wl_is_None_heur_alt_def[symmetric]
  supply [[goals_limit = 1]] isasat_fast_def[simp] cdcl_twl_o_prog_wl_D_heurI[intro]
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref

declare
  cdcl_twl_o_prog_wl_D_fast_code.refine[sepref_fr_rules]

sepref_register
  cdcl_twl_o_prog_wl_D_heur

definition length_clauses_heur where
  \<open>length_clauses_heur S = length (get_clauses_wl_heur S)\<close>

lemma length_clauses_heur_alt_def: \<open>length_clauses_heur = (\<lambda>(M, N, _). length N)\<close>
  by (auto intro!: ext simp: length_clauses_heur_def)

sepref_def length_clauses_heur_impl
  is \<open>RETURN o length_clauses_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  unfolding length_clauses_heur_alt_def isasat_bounded_assn_def
  by sepref

declare length_clauses_heur_impl.refine [sepref_fr_rules]

lemma isasat_fast_alt_def: \<open>isasat_fast S = (length_clauses_heur S \<le> 9223372034707292156 \<and>
  clss_size_lcount (get_learned_count S) < 18446744073709551615 - clss_size_lcountUE (get_learned_count S) \<and>
  clss_size_lcount (get_learned_count S) + clss_size_lcountUE (get_learned_count S) < 18446744073709551615 - clss_size_lcountUS (get_learned_count S) \<and>
   clss_size_lcount (get_learned_count S) +
    clss_size_lcountUE (get_learned_count S) + clss_size_lcountUS (get_learned_count S)  < 18446744073709551615 - clss_size_lcountU0 (get_learned_count S) \<and>
   clss_size_lcount (get_learned_count S) +
    clss_size_lcountUE (get_learned_count S) + clss_size_lcountUS (get_learned_count S) + clss_size_lcountU0 (get_learned_count S) < 18446744073709551615)\<close>
  by (cases S; auto simp: isasat_fast_def sint64_max_def uint32_max_def length_clauses_heur_def
    uint64_max_def learned_clss_count_def clss_size_lcountU0_def)

sepref_def isasat_fast_impl
  is \<open>RETURN o isasat_fast\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding isasat_fast_alt_def short_circuit_conv
  apply (rewrite at \<open>_ < \<hole>\<close> unat_const_fold[where 'a=64])+
  apply (rewrite at \<open>_ < \<hole> - _\<close> unat_const_fold[where 'a=64])+
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

end