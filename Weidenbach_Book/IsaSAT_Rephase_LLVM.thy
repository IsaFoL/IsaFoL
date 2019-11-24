theory IsaSAT_Rephase_LLVM
  imports IsaSAT_Rephase IsaSAT_Setup_LLVM
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

sepref_def phase_save_rephase_impl
  is phase_save_rephase
  :: \<open>phase_saver_assn\<^sup>d \<rightarrow>\<^sub>a phase_saver_assn\<close>
  unfolding phase_save_rephase_def
  by sepref

end