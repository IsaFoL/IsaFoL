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


lemma ema_bitshifting_inline[llvm_inline]:
  \<open>ema_bitshifting = (0x100000000::_::len word)\<close> by (auto simp: ema_bitshifting_def)

lemma ema_reinit_inline[llvm_inline]:
  "ema_reinit = (\<lambda>(value, \<alpha>, \<beta>, wait, period).
    (value, \<alpha>, 0x100000000::_::len word, 0::_ word, 0:: _ word))"
  by (auto simp: ema_bitshifting_def intro!: ext)

lemmas [llvm_inline] = ema_init_def

sepref_def ema_update_impl is \<open>uncurry (RETURN oo ema_update)\<close>
  :: \<open>uint32_nat_assn\<^sup>k *\<^sub>a ema_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  unfolding ema_update_def
  apply (rewrite at \<open>let _ = of_nat \<hole> * _ in _\<close> annot_unat_unat_upcast[where 'l = 64])
  apply (rewrite at \<open>let _=_ + _; _=\<hole> in _\<close> fold_COPY)
  (* TODO: The let x=y seems to be inlined, making necessary this COPY! Is this behaviour correct? *)
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  supply [[goals_limit = 1]]
  by sepref

end