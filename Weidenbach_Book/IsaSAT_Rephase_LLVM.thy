theory IsaSAT_Rephase_LLVM
  imports IsaSAT_Rephase IsaSAT_Show_LLVM
begin

sepref_def rephase_random_impl
  is \<open>uncurry rephase_random\<close>
  :: \<open>word_assn\<^sup>k *\<^sub>a phase_saver_assn\<^sup>d \<rightarrow>\<^sub>a phase_saver_assn\<close>
  supply [[goals_limit=1]]
  unfolding rephase_random_def
    while_eq_nfoldli[symmetric]
  apply (subst while_upt_while_direct, simp)
  apply (annot_snat_const "TYPE(64)")
  by sepref

sepref_def rephase_init_impl
  is \<open>uncurry rephase_init\<close>
  :: \<open>bool1_assn\<^sup>k *\<^sub>a phase_saver_assn\<^sup>d \<rightarrow>\<^sub>a phase_saver_assn\<close>
  unfolding rephase_init_def
    while_eq_nfoldli[symmetric]
  apply (subst while_upt_while_direct, simp)
  apply (annot_snat_const "TYPE(64)")
  by sepref

sepref_def copy_phase_impl
  is \<open>uncurry copy_phase\<close>
  :: \<open>phase_saver_assn\<^sup>k *\<^sub>a phase_saver_assn\<^sup>d \<rightarrow>\<^sub>a phase_saver_assn\<close>
  unfolding copy_phase_def
    while_eq_nfoldli[symmetric]
  apply (subst while_upt_while_direct, simp)
  apply (annot_snat_const "TYPE(64)")
  by sepref



sepref_register rephase_init rephase_random copy_phase

sepref_def phase_save_phase_impl
  is \<open>uncurry phase_save_phase\<close>
  :: \<open>sint64_nat_assn\<^sup>k *\<^sub>a phase_heur_assn\<^sup>d \<rightarrow>\<^sub>a phase_heur_assn\<close>
  supply [[goals_limit=1]]
  unfolding phase_save_phase_def
  by sepref


sepref_def save_phase_heur_impl
  is \<open>uncurry save_rephase_heur\<close>
  ::  \<open>sint64_nat_assn\<^sup>k *\<^sub>a heuristic_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_assn\<close>
  supply [[goals_limit=1]]
  unfolding save_rephase_heur_def heuristic_assn_def
  by sepref


sepref_def save_phase_heur_st
  is save_phase_st
  ::  \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding save_phase_st_def isasat_bounded_assn_def
  by sepref

sepref_def phase_save_rephase_impl
  is \<open>uncurry phase_rephase\<close>
  :: \<open>word_assn\<^sup>k *\<^sub>a phase_heur_assn\<^sup>d \<rightarrow>\<^sub>a phase_heur_assn\<close>
  unfolding phase_rephase_def
  by sepref


sepref_def rephase_heur_impl
  is \<open>uncurry rephase_heur\<close>
  :: \<open>word_assn\<^sup>k *\<^sub>a heuristic_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_assn\<close>
  unfolding rephase_heur_def heuristic_assn_def
  by sepref

lemma current_rephasing_phase_alt_def:
  \<open>RETURN o current_rephasing_phase =
    (\<lambda>(fast_ema, slow_ema, res_info, wasted,
      (\<phi>, target_assigned, target, best_assigned, best, end_of_phase, curr_phase, length_phase)).
      RETURN curr_phase)\<close>
  unfolding current_rephasing_phase_def
    phase_current_rephasing_phase_def
  by (auto intro!: ext)

sepref_def current_rephasing_phase
  is \<open>RETURN o current_rephasing_phase\<close>
  :: \<open>heuristic_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding current_rephasing_phase_alt_def heuristic_assn_def
  by sepref

sepref_register rephase_heur
sepref_def rephase_heur_st_impl
  is rephase_heur_st
  ::  \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding rephase_heur_st_def isasat_bounded_assn_def
  by sepref


experiment
begin
export_llvm rephase_heur_st_impl
  save_phase_heur_st
end

end
