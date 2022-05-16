theory IsaSAT_Restart_Simp_LLVM
imports  IsaSAT_Restart_Heuristics_LLVM IsaSAT_Garbage_Collect_LLVM
  IsaSAT_Other_LLVM IsaSAT_Propagate_Conflict_LLVM IsaSAT_Inprocessing_LLVM IsaSAT_Restart_LLVM
begin

sepref_register cdcl_twl_full_restart_wl_prog_heur mark_to_delete_clauses_GC_wl_D_heur

sepref_def cdcl_twl_restart_wl_heur_fast_code
  is \<open>cdcl_twl_restart_wl_heur\<close>
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding cdcl_twl_restart_wl_heur_def
  supply [[goals_limit = 1]]
  by sepref

sepref_def cdcl_twl_full_restart_wl_prog_heur_fast_code
  is \<open>cdcl_twl_full_restart_wl_prog_heur\<close>
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding cdcl_twl_full_restart_wl_prog_heur_def
  supply [[goals_limit = 1]]
  by sepref


sepref_def cdcl_twl_full_restart_wl_D_GC_heur_prog_fast_code
  is \<open>cdcl_twl_full_restart_wl_D_GC_heur_prog\<close>
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max \<and> learned_clss_count S \<le> uint64_max]\<^sub>a
     isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit = 1]]
  unfolding cdcl_twl_full_restart_wl_D_GC_heur_prog_def
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref

sepref_def cdcl_twl_full_restart_wl_D_inprocess_heur_prog_fast_code
  is \<open>cdcl_twl_full_restart_wl_D_inprocess_heur_prog\<close>
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max \<and> learned_clss_count S \<le> uint64_max]\<^sub>a
     isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit = 1]]
  unfolding cdcl_twl_full_restart_wl_D_inprocess_heur_prog_def
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref

sepref_register restart_required_heur cdcl_twl_restart_wl_heur
  cdcl_twl_full_restart_wl_D_inprocess_heur_prog

sepref_def restart_prog_wl_D_heur_fast_code
  is \<open>uncurry4 (restart_prog_wl_D_heur)\<close>
  :: \<open>[\<lambda>((((S, _), _), n), _). isasat_fast_relaxed2 S n]\<^sub>a
      isasat_bounded_assn\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k  *\<^sub>a uint64_nat_assn\<^sup>k  *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a
        bool1_assn\<^sup>k \<rightarrow> isasat_bounded_assn \<times>\<^sub>a uint64_nat_assn \<times>\<^sub>a uint64_nat_assn \<times>\<^sub>a uint64_nat_assn\<close>
  unfolding restart_prog_wl_D_heur_def isasat_fast_relaxed_def isasat_fast_relaxed2_def
  supply [[goals_limit = 1]]
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

lemma cdcl_twl_stgy_restart_prog_bounded_wl_heurI1:
  assumes
    \<open>isasat_fast a1'b\<close>
    \<open>learned_clss_count a2'e \<le> Suc (learned_clss_count a1'b)\<close>
  shows \<open>learned_clss_count a2'e \<le> uint64_max\<close>
  using assms
  by (auto simp: isasat_fast_def)

lemma cdcl_twl_stgy_restart_prog_bounded_wl_heurI2:
  \<open>isasat_fast x \<Longrightarrow> learned_clss_count x \<le> uint64_max\<close>
  by (auto simp: isasat_fast_def)


lemma cdcl_twl_stgy_restart_prog_bounded_wl_heurI3:
  assumes
    \<open>isasat_fast S\<close>
    \<open>length (get_clauses_wl_heur T) \<le> length (get_clauses_wl_heur S)\<close>
    \<open>learned_clss_count T \<le> (learned_clss_count S)\<close>
  shows \<open>isasat_fast T\<close>
  using assms
  by (auto simp: isasat_fast_def)

sepref_register cdcl_twl_stgy_restart_prog_bounded_wl_heur
sepref_def cdcl_twl_stgy_restart_prog_wl_heur_fast_code
  is \<open>cdcl_twl_stgy_restart_prog_bounded_wl_heur\<close>
  :: \<open>[\<lambda>S. isasat_fast S]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> bool1_assn \<times>\<^sub>a isasat_bounded_assn\<close>
  unfolding cdcl_twl_stgy_restart_prog_bounded_wl_heur_def
  supply [[goals_limit = 1]] isasat_fast_countD[dest]
  supply [intro] = cdcl_twl_stgy_restart_prog_bounded_wl_heurI2
  supply [sepref_bounds_simps del] = uint32_max_def sint32_max_def uint64_max_def sint64_max_def
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

experiment
begin
   export_llvm opts_reduction_st_fast_code
    opts_restart_st_fast_code
    get_conflict_count_since_last_restart_heur_fast_code
    get_fast_ema_heur_fast_code
    get_slow_ema_heur_fast_code
    get_learned_count_fast_code
    upper_restart_bound_not_reached_fast_impl
    minimum_number_between_restarts_impl
    restart_required_heur_fast_code
    cdcl_twl_full_restart_wl_D_GC_heur_prog_fast_code
    cdcl_twl_restart_wl_heur_fast_code
    cdcl_twl_full_restart_wl_prog_heur_fast_code
    cdcl_twl_local_restart_wl_D_heur_fast_code
   get_conflict_wl_is_None_fast_code
end

end
