theory IsaSAT_Rephase_State_LLVM
imports
  IsaSAT_Rephase_State IsaSAT_Rephase_LLVM IsaSAT_Show_LLVM IsaSAT_Setup_LLVM
begin
hide_const (open) NEMonad.ASSERT NEMonad.RETURN

sepref_def save_phase_heur_stats_impl
  is \<open>uncurry save_rephase_heur_stats\<close>
  :: \<open>word64_assn\<^sup>k *\<^sub>a heuristic_int_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_int_assn\<close>
  supply [[goals_limit=1]]
  unfolding save_rephase_heur_stats_def heuristic_int_assn_def
  by sepref

sepref_register save_rephase_heur_stats
sepref_def save_phase_heur_impl
  is \<open>uncurry save_rephase_heur\<close>
  :: \<open>word64_assn\<^sup>k *\<^sub>a heuristic_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_assn\<close>
  supply [[goals_limit=1]]
  unfolding save_rephase_heur_def
  by sepref

lemma save_phase_st_alt_def:
  \<open>save_phase_st = (\<lambda>S. do {
      let (heur, S) = extract_heur_wl_heur S;
      let (stats, S) = extract_stats_wl_heur S;
      let n = no_conflict_until stats;
      heur \<leftarrow> save_rephase_heur n heur;
      RETURN (update_heur_wl_heur heur (update_stats_wl_heur stats S))
   })\<close>
  by (auto simp: save_phase_st_def state_extractors split: isasat_int_splits intro!: ext)

sepref_def save_phase_heur_st
  is save_phase_st
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding save_phase_st_alt_def
  by sepref

sepref_def phase_save_rephase_impl
  is \<open>uncurry3 phase_rephase\<close>
  :: \<open>word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k *\<^sub>a phase_heur_assn\<^sup>d \<rightarrow>\<^sub>a phase_heur_assn\<close>
  unfolding phase_rephase_def copy_phase2_def[symmetric] phase_heur_assn_def
  supply of_nat_snat[sepref_import_param]
  apply (subst copy_phase2_def)
  by sepref


sepref_def rephase_heur_stats_impl
  is \<open>uncurry3 rephase_heur_stats\<close>
  :: \<open>word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k *\<^sub>a heuristic_int_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_int_assn\<close>
  unfolding rephase_heur_stats_def heuristic_int_assn_def
  by sepref

sepref_register rephase_heur_stats isasat_print_progress

sepref_def rephase_heur_impl
  is \<open>uncurry3 rephase_heur\<close>
  :: \<open>word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k *\<^sub>a heuristic_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_assn\<close>
  unfolding rephase_heur_def
  by sepref

lemma rephase_heur_st_alt_def:
  \<open>rephase_heur_st = (\<lambda>S. do {
      let lc = get_global_conflict_count S;
      let (heur, S) = extract_heur_wl_heur S;
      let (stats, S) = extract_stats_wl_heur S;
      let lrephase = stats_rephase stats;
      let stats = incr_rephase_total stats;
      let (lcount, S) = extract_lcount_wl_heur S;
      let b = current_restart_phase heur;
      heur \<leftarrow> rephase_heur lc lrephase b heur;
      let _ = isasat_print_progress (current_phase_letter (current_rephasing_phase heur))
                  b stats (lcount);
      RETURN (update_heur_wl_heur heur (update_stats_wl_heur stats (update_lcount_wl_heur lcount S)))
   })\<close>
  by (auto simp: rephase_heur_st_def state_extractors split: isasat_int_splits intro!: ext)

sepref_register rephase_heur
sepref_def rephase_heur_st_impl
  is rephase_heur_st
  ::  \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding rephase_heur_st_alt_def
  by sepref


experiment
begin

export_llvm rephase_heur_st_impl
  save_phase_heur_st

end

end