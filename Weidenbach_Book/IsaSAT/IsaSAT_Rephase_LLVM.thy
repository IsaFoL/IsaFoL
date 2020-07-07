theory IsaSAT_Rephase_LLVM
  imports IsaSAT_Rephase IsaSAT_Literals_LLVM
begin

type_synonym phase_saver_assn = \<open>1 word larray64\<close>
abbreviation phase_saver_assn :: \<open>phase_saver \<Rightarrow> phase_saver_assn \<Rightarrow> assn\<close> where
  \<open>phase_saver_assn \<equiv> larray64_assn bool1_assn\<close>

type_synonym phase_saver'_assn = \<open>1 word ptr\<close>

abbreviation phase_saver'_assn :: \<open>phase_saver \<Rightarrow> phase_saver'_assn \<Rightarrow> assn\<close> where
  \<open>phase_saver'_assn \<equiv> array_assn bool1_assn\<close>


abbreviation phase_heur_assn where
  \<open>phase_heur_assn \<equiv> phase_saver_assn \<times>\<^sub>a sint64_nat_assn \<times>\<^sub>a phase_saver'_assn \<times>\<^sub>a sint64_nat_assn \<times>\<^sub>a
     phase_saver'_assn \<times>\<^sub>a word64_assn \<times>\<^sub>a word64_assn \<times>\<^sub>a word64_assn\<close>

sepref_def rephase_random_impl
  is \<open>uncurry rephase_random\<close>
  :: \<open>word_assn\<^sup>k *\<^sub>a phase_saver_assn\<^sup>d \<rightarrow>\<^sub>a phase_saver_assn\<close>
  supply [[goals_limit=1]]
  unfolding rephase_random_def
    while_eq_nfoldli[symmetric]
  apply (subst while_upt_while_direct, simp)
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_def rephase_init_impl
  is \<open>uncurry rephase_init\<close>
  :: \<open>bool1_assn\<^sup>k *\<^sub>a phase_saver_assn\<^sup>d \<rightarrow>\<^sub>a phase_saver_assn\<close>
  unfolding rephase_init_def
    while_eq_nfoldli[symmetric]
  apply (subst while_upt_while_direct, simp)
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_def copy_phase_impl
  is \<open>uncurry copy_phase\<close>
  :: \<open>phase_saver_assn\<^sup>k *\<^sub>a phase_saver'_assn\<^sup>d \<rightarrow>\<^sub>a phase_saver'_assn\<close>
  unfolding copy_phase_alt_def
    while_eq_nfoldli[symmetric]
  apply (subst while_upt_while_direct, simp)
  unfolding simp_thms(21) \<comment> \<open>remove \<^term>\<open>a \<and> True\<close> from condition\<close>
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

definition copy_phase2 where
  \<open>copy_phase2 = copy_phase\<close>

sepref_def copy_phase_impl2
  is \<open>uncurry copy_phase2\<close>
  :: \<open>phase_saver'_assn\<^sup>k *\<^sub>a phase_saver_assn\<^sup>d \<rightarrow>\<^sub>a phase_saver_assn\<close>
  unfolding copy_phase_def copy_phase2_def
    while_eq_nfoldli[symmetric]
  apply (subst while_upt_while_direct, simp)
  unfolding simp_thms(21) \<comment> \<open>remove \<^term>\<open>a \<and> True\<close> from condition\<close>
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref



sepref_register rephase_init rephase_random copy_phase

sepref_def phase_save_phase_impl
  is \<open>uncurry phase_save_phase\<close>
  :: \<open>sint64_nat_assn\<^sup>k *\<^sub>a phase_heur_assn\<^sup>d \<rightarrow>\<^sub>a phase_heur_assn\<close>
  supply [[goals_limit=1]]
  unfolding phase_save_phase_def
  by sepref

end

