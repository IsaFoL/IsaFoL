theory IsaSAT_Options_LLVM
  imports IsaSAT_Options IsaSAT_Literals_LLVM
begin

type_synonym opts_assn = \<open>1 word \<times> 1 word \<times> 1 word \<times> 1 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 3 word \<times> 64 word
   \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word\<close>

definition opts_rel_assn :: \<open>opts_ref \<Rightarrow> _ \<Rightarrow> assn\<close> where
  \<open>opts_rel_assn = bool1_assn \<times>\<^sub>a bool1_assn \<times>\<^sub>a bool1_assn \<times>\<^sub>a  bool1_assn \<times>\<^sub>a word_assn \<times>\<^sub>a word_assn 
   \<times>\<^sub>a snat_assn' TYPE(64) \<times>\<^sub>a word_assn' TYPE(3) \<times>\<^sub>a word64_assn \<times>\<^sub>a word64_assn \<times>\<^sub>a word64_assn \<times>\<^sub>a word_assn \<times>\<^sub>a word_assn\<close>

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

sepref_def opts_rel_target_code
  is \<open>RETURN o opts_rel_target\<close>
  :: \<open>opts_rel_assn\<^sup>k \<rightarrow>\<^sub>a word_assn' TYPE(3)\<close>
  unfolding opts_rel_alt_defs opts_rel_assn_def
  by sepref

sepref_def opts_rel_fema_code
  is \<open>RETURN o opts_rel_fema\<close>
  :: \<open>opts_rel_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding opts_rel_alt_defs opts_rel_assn_def
  by sepref

sepref_def opts_rel_sema_code
  is \<open>RETURN o opts_rel_sema\<close>
  :: \<open>opts_rel_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding opts_rel_alt_defs opts_rel_assn_def
  by sepref

sepref_def opts_rel_GC_units_lim_code
  is \<open>RETURN o opts_rel_GC_units_lim\<close>
  :: \<open>opts_rel_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding opts_rel_alt_defs opts_rel_assn_def
  by sepref

sepref_def opts_rel_subsumption_code
  is \<open>RETURN o opts_rel_subsumption\<close>
  :: \<open>opts_rel_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding opts_rel_alt_defs opts_rel_assn_def
  by sepref

sepref_def opts_rel_reduceint_code
  is \<open>RETURN o opts_rel_reduceint\<close>
  :: \<open>opts_rel_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding opts_rel_alt_defs opts_rel_assn_def
  by sepref

sepref_def opts_rel_pureelim_rounds_code
  is \<open>RETURN o opts_rel_pureelim_rounds\<close>
  :: \<open>opts_rel_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding opts_rel_alt_defs opts_rel_assn_def
  by sepref
    
definition opts_assn :: \<open>opts \<Rightarrow> opts_assn \<Rightarrow> assn\<close> where
  \<open>opts_assn = hr_comp opts_rel_assn opts_rel\<close>

lemmas opts_refine[sepref_fr_rules] =
  opts_rel_restart_code.refine[FCOMP opts_rel_restart, unfolded opts_assn_def[symmetric]]
  opts_rel_reduce_code.refine[FCOMP opts_rel_reduce, unfolded opts_assn_def[symmetric]]
  opts_rel_unbounded_mode_code.refine[FCOMP opts_rel_unbounded_mode, unfolded opts_assn_def[symmetric]]
  opts_rel_miminum_between_restart_code.refine[FCOMP opts_rel_miminum_between_restart, unfolded opts_assn_def[symmetric]]
  opts_rel_restart_coeff1_code.refine[FCOMP opts_rel_restart_coeff1, unfolded opts_assn_def[symmetric]]
  opts_rel_restart_coeff2_code.refine[FCOMP opts_rel_restart_coeff2, unfolded opts_assn_def[symmetric]]
  opts_rel_target_code.refine[FCOMP opts_rel_target, unfolded opts_assn_def[symmetric]]
  opts_rel_fema_code.refine[FCOMP opts_rel_fema, unfolded opts_assn_def[symmetric]]
  opts_rel_sema_code.refine[FCOMP opts_rel_sema, unfolded opts_assn_def[symmetric]]
  opts_rel_GC_units_lim_code.refine[FCOMP opts_GC_units_lim, unfolded opts_assn_def[symmetric]]
  opts_rel_subsumption_code.refine[FCOMP opts_subsumption,  unfolded opts_assn_def[symmetric]]
  opts_rel_reduceint_code.refine[FCOMP opts_reduceint,  unfolded opts_assn_def[symmetric]]
  opts_rel_pureelim_rounds_code.refine[FCOMP opts_pureelim_rounds,  unfolded opts_assn_def[symmetric]]

sepref_register opts_restart opts_reduce opts_minimum_between_restart opts_restart_coeff1
  opts_restart_coeff2 opts_target opts_fema opts_sema opts_subsumption

lemma opts_assn_assn_pure[safe_constraint_rules]: \<open>CONSTRAINT is_pure opts_assn\<close>
  unfolding opts_assn_def opts_rel_assn_def
  by solve_constraint

lemmas [sepref_frame_free_rules] = mk_free_is_pure[OF opts_assn_assn_pure[unfolded CONSTRAINT_def]]

definition default_opts :: opts where
  \<open>default_opts = IsaOptions True True True True 50 11 4 1 128849010 429450 15 300 3\<close>

definition default_opts2 :: opts_ref where
  \<open>default_opts2 = (True, True, True, True, 50, 11, 4, 2, 128849010, 429450, 15, 300, 3)\<close>

definition IsaOptions_rel
  :: \<open>bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow> opts_target \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow>
    64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> opts_ref\<close> where
  \<open>IsaOptions_rel a b c d e f g h i j k l m = (a, b, c, d, e, f, g, h, i, j, k, l, m)\<close>

lemma IsaOptions_rel:
  \<open>(uncurry12 (RETURN o\<^sub>1\<^sub>3 IsaOptions_rel), uncurry12 (RETURN o\<^sub>1\<^sub>3 IsaOptions)) \<in>
    bool_rel \<times>\<^sub>f bool_rel \<times>\<^sub>f  bool_rel \<times>\<^sub>fbool_rel \<times>\<^sub>f  word_rel \<times>\<^sub>f word_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f word_rel \<times>\<^sub>f word_rel \<times>\<^sub>f word_rel \<times>\<^sub>f
      word_rel  \<times>\<^sub>f word_rel \<times>\<^sub>f word_rel \<rightarrow>
   \<langle>opts_rel\<rangle>nres_rel\<close>
  by (auto intro!: frefI nres_relI simp: opts_rel_def IsaOptions_rel_def)

sepref_def IsaOptions_rel_impl
  is \<open>uncurry12 (RETURN o\<^sub>1\<^sub>3 IsaOptions_rel)\<close>
  :: \<open>bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k *\<^sub>a
     (snat_assn' (TYPE(64)))\<^sup>k  *\<^sub>a (word_assn' (TYPE(3)))\<^sup>k  *\<^sub>a word_assn\<^sup>k  *\<^sub>a word_assn\<^sup>k  *\<^sub>a word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k \<rightarrow>\<^sub>a
        opts_rel_assn\<close>
  unfolding IsaOptions_rel_def opts_rel_assn_def
  by sepref

sepref_register IsaOptions
thm     IsaOptions_rel_impl.refine[unfolded opts_assn_def[symmetric]]

lemmas [sepref_fr_rules] =
    IsaOptions_rel_impl.refine[FCOMP IsaOptions_rel, unfolded opts_assn_def[symmetric]]

lemma [sepref_import_param]:
  \<open>(0, TARGET_NEVER) \<in> word_rel\<close>
  \<open>(1, TARGET_STABLE_ONLY) \<in> word_rel\<close>
  \<open>(2, TARGET_ALWAYS) \<in> word_rel\<close>
  by (auto simp: TARGET_NEVER_def TARGET_ALWAYS_def TARGET_STABLE_ONLY_def)


experiment begin

export_llvm
  opts_rel_restart_code
  opts_rel_reduce_code
end

end
