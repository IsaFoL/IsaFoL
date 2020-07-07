theory IsaSAT_Options_LLVM
  imports IsaSAT_Options IsaSAT_Literals_LLVM
begin

type_synonym opts_assn = \<open>1 word \<times> 1 word \<times> 1 word \<times> 64 word \<times> 64 word \<times> 64 word\<close>

definition opts_rel_assn :: \<open>opts_ref \<Rightarrow> _ \<Rightarrow> assn\<close> where
  \<open>opts_rel_assn = bool1_assn \<times>\<^sub>a bool1_assn \<times>\<^sub>a bool1_assn \<times>\<^sub>a word_assn \<times>\<^sub>a word_assn \<times>\<^sub>a snat_assn' TYPE(64)\<close>

sepref_def opts_rel_restart_code
  is \<open>RETURN o opts_rel_restart\<close>
  :: \<open>opts_rel_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding opts_rel_alt_defs opts_rel_assn_def
  by sepref


sepref_def opts_rel_reduce_code
  is \<open>RETURN o opts_rel_reduce\<close>
  :: \<open>opts_rel_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding opts_rel_alt_defs opts_rel_assn_def
  by sepref

sepref_def opts_rel_unbounded_mode_code
  is \<open>RETURN o opts_rel_unbounded_mode\<close>
  :: \<open>opts_rel_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding opts_rel_alt_defs opts_rel_assn_def
  by sepref

sepref_def opts_rel_miminum_between_restart_code
  is \<open>RETURN o opts_rel_miminum_between_restart\<close>
  :: \<open>opts_rel_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding opts_rel_alt_defs opts_rel_assn_def
  by sepref

sepref_def opts_rel_restart_coeff1_code
  is \<open>RETURN o opts_rel_restart_coeff1\<close>
  :: \<open>opts_rel_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding opts_rel_alt_defs opts_rel_assn_def
  by sepref

sepref_def opts_rel_restart_coeff2_code
  is \<open>RETURN o opts_rel_restart_coeff2\<close>
  :: \<open>opts_rel_assn\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE(64)\<close>
  unfolding opts_rel_alt_defs opts_rel_assn_def
  by sepref

definition opts_assn :: \<open>opts \<Rightarrow> opts_assn \<Rightarrow> assn\<close> where
  \<open>opts_assn = hr_comp opts_rel_assn opts_rel\<close>

lemmas [sepref_fr_rules] =
  opts_rel_restart_code.refine[FCOMP opts_rel_restart, unfolded opts_assn_def[symmetric]]
  opts_rel_reduce_code.refine[FCOMP opts_rel_reduce, unfolded opts_assn_def[symmetric]]
  opts_rel_unbounded_mode_code.refine[FCOMP opts_rel_unbounded_mode, unfolded opts_assn_def[symmetric]]
  opts_rel_miminum_between_restart_code.refine[FCOMP opts_rel_miminum_between_restart, unfolded opts_assn_def[symmetric]]
  opts_rel_restart_coeff1_code.refine[FCOMP opts_rel_restart_coeff1, unfolded opts_assn_def[symmetric]]
  opts_rel_restart_coeff2_code.refine[FCOMP opts_rel_restart_coeff2, unfolded opts_assn_def[symmetric]]

sepref_register opts_restart opts_reduce opts_minimum_between_restart opts_restart_coeff1
  opts_restart_coeff2

lemma opts_assn_assn_pure[safe_constraint_rules]: \<open>CONSTRAINT is_pure opts_assn\<close>
  unfolding opts_assn_def opts_rel_assn_def
  by solve_constraint

lemmas [sepref_frame_free_rules] = mk_free_is_pure[OF opts_assn_assn_pure[unfolded CONSTRAINT_def]]

experiment begin

export_llvm
  opts_rel_restart_code
  opts_rel_reduce_code
end

end