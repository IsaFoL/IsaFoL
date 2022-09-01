theory IsaSAT_Show_LLVM
  imports
    IsaSAT_Show
    IsaSAT_Setup0_LLVM
begin


sepref_register isasat_current_information print_c print_uint64

sepref_def print_c_impl
  is \<open>RETURN o print_c\<close>
  :: \<open>word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_c_def
  by sepref

sepref_def print_uint64_impl
  is \<open>RETURN o print_uint64\<close>
  :: \<open>word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_uint64_def
  by sepref

sepref_def print_open_colour_impl
  is \<open>RETURN o print_open_colour\<close>
  :: \<open>word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_open_colour_def
  by sepref


sepref_def print_close_colour_impl
  is \<open>RETURN o print_close_colour\<close>
  :: \<open>word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_close_colour_def
  by sepref

sepref_def print_char_impl
  is \<open>RETURN o print_char\<close>
  :: \<open>word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_char_def
  by sepref


sepref_def isasat_current_information_impl [llvm_code]
  is \<open>uncurry2 (RETURN ooo isasat_current_information_stats)\<close>
  :: \<open>word_assn\<^sup>k *\<^sub>a stats_int_assn\<^sup>d *\<^sub>a lcount_assn\<^sup>k \<rightarrow>\<^sub>a stats_int_assn\<close>
  unfolding isasat_current_information_stats_def
    isasat_current_information_def lcount_assn_def
  by sepref

lemma isasat_current_information_stats_isasat_current_information:
  \<open>(isasat_current_information_stats, isasat_current_information) \<in> word_rel \<rightarrow> stats_rel \<rightarrow> Id \<rightarrow> stats_rel\<close>
  by (auto simp: isasat_current_information_def code_hider_rel_def)

lemmas [sepref_fr_rules] =
  isasat_current_information_impl.refine[FCOMP isasat_current_information_stats_isasat_current_information,
  unfolded stats_assn_alt_def[symmetric]]

lemma isasat_current_status_alt_def:
\<open>isasat_current_status =
   (\<lambda>S.
  let
      (heur, S) = extract_heur_wl_heur S;
      (stats, S) = extract_stats_wl_heur S;
      (lcount, S) = extract_lcount_wl_heur S;
       curr_phase = current_restart_phase (heur);
        stats = (isasat_current_information curr_phase stats lcount)
     in RETURN (update_stats_wl_heur stats (update_heur_wl_heur heur (update_lcount_wl_heur lcount S))))\<close>
  by (auto simp: isasat_current_status_def state_extractors split: isasat_int_splits intro!: ext)

sepref_def isasat_current_status_fast_code
  is \<open>isasat_current_status\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_current_status_alt_def
  by sepref

sepref_def isasat_print_progress_impl
  is \<open>uncurry3 (RETURN oooo isasat_print_progress_stats)\<close>
  :: \<open>word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k *\<^sub>a stats_int_assn\<^sup>k *\<^sub>a lcount_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding isasat_print_progress_stats_def lcount_assn_def
  by sepref

lemma isasat_print_progress_stats_isasat_print_progress:
  \<open>(uncurry3 (RETURN oooo isasat_print_progress_stats), uncurry3 (RETURN oooo isasat_print_progress))
  \<in> word_rel \<times>\<^sub>f word_rel \<times>\<^sub>f stats_rel \<times>\<^sub>f Id \<rightarrow> \<langle>unit_rel\<rangle>nres_rel\<close>
  by (auto simp: isasat_print_progress_def code_hider_rel_def intro!: nres_relI)

lemmas [sepref_fr_rules] =
  isasat_print_progress_impl.refine[FCOMP isasat_print_progress_stats_isasat_print_progress,
  unfolded stats_assn_alt_def[symmetric]]

end