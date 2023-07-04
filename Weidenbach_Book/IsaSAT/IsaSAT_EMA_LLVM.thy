theory IsaSAT_EMA_LLVM
  imports IsaSAT_EMA IsaSAT_Literals_LLVM
begin

abbreviation ema_rel :: \<open>(ema\<times>ema) set\<close> where
  \<open>ema_rel \<equiv> word64_rel \<times>\<^sub>r word64_rel \<times>\<^sub>r word64_rel \<times>\<^sub>r word64_rel \<times>\<^sub>r word64_rel\<close>

abbreviation ema_assn :: \<open>ema \<Rightarrow> ema \<Rightarrow> assn\<close> where
  \<open>ema_assn \<equiv> word64_assn \<times>\<^sub>a word64_assn \<times>\<^sub>a word64_assn \<times>\<^sub>a word64_assn \<times>\<^sub>a word64_assn\<close>

lemma [sepref_import_param]:
  \<open>(ema_get_value, ema_get_value) \<in> ema_rel \<rightarrow> word64_rel\<close>
  \<open>(ema_bitshifting,ema_bitshifting) \<in> word64_rel\<close>
  \<open>(ema_reinit,ema_reinit) \<in> ema_rel \<rightarrow> ema_rel\<close>
  \<open>(ema_init,ema_init) \<in> word_rel \<rightarrow> ema_rel\<close>
  by auto

sepref_register EMA_FIXPOINT_SIZE ema_bitshifting
sepref_def EMA_FIXPOINT_SIZE_impl
  is \<open>uncurry0 (RETURN EMA_FIXPOINT_SIZE)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  unfolding EMA_FIXPOINT_SIZE_def
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

lemma EMA[simp]:
  \<open>EMA_FIXPOINT_SIZE < 64\<close>
  \<open>EMA_MULT_SHIFT < 64\<close>
  \<open>EMA_FIXPOINT_SIZE - EMA_MULT_SHIFT < 64\<close>
  \<open>EMA_MULT_SHIFT \<le> EMA_FIXPOINT_SIZE\<close>
  \<open>EMA_FIXPOINT_SIZE - 32 < 64\<close>
  \<open>EMA_FIXPOINT_SIZE \<ge> 32\<close>
  by (auto simp: EMA_FIXPOINT_SIZE_def EMA_MULT_SHIFT_def)

sepref_def ema_bitshifting_impl
  is \<open>uncurry0 (RETURN ema_bitshifting)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding ema_bitshifting_def
  by sepref

lemma ema_reinit_inline[llvm_inline]:
  "ema_reinit = (\<lambda>(value, \<alpha>, \<beta>, wait, period).
    (value, \<alpha>, ema_bitshifting, 0::_ word, 0:: _ word))"
  by (auto simp: ema_bitshifting_def intro!: ext)

sepref_def EMA_MULT_SHIFT_impl
  is \<open>uncurry0 (RETURN EMA_MULT_SHIFT)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  unfolding EMA_MULT_SHIFT_def
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

lemmas [llvm_inline] = ema_init_def

sepref_def ema_update_impl is \<open>uncurry (RETURN oo ema_update)\<close>
  :: \<open>uint32_nat_assn\<^sup>k *\<^sub>a ema_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  unfolding ema_update_def Let_def[of "_ - 1"]
  apply (rewrite at \<open>let _ = of_nat \<hole> * _ in _\<close> annot_unat_unat_upcast[where 'l = 64])
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  supply [[goals_limit = 1]]
  by sepref

sepref_def ema_init_impl
  is \<open>RETURN o ema_init\<close>
  :: \<open>word64_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  unfolding ema_init_def
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

end
