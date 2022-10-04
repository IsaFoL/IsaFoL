theory IsaSAT_Print_LLVM
  imports IsaSAT_Literals_LLVM
begin

definition print_propa :: \<open>64 word \<Rightarrow> unit\<close> where
  \<open>print_propa _ = ()\<close>

definition print_confl :: \<open>64 word \<Rightarrow> unit\<close> where
  \<open>print_confl _ = ()\<close>

definition print_dec :: \<open>64 word \<Rightarrow> unit\<close> where
  \<open>print_dec _ = ()\<close>

definition print_res :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> unit\<close> where
  \<open>print_res _ _ = ()\<close>

definition print_lres :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> unit\<close> where
  \<open>print_lres _ _ = ()\<close>

definition print_uset :: \<open>64 word \<Rightarrow> unit\<close> where
  \<open>print_uset _ = ()\<close>

definition print_gcs :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> unit\<close> where
  \<open>print_gcs _ _ = ()\<close>

definition print_binary_unit :: \<open>64 word \<Rightarrow> unit\<close> where
  \<open>print_binary_unit _ = ()\<close>

definition print_binary_red_removed :: \<open>64 word \<Rightarrow> unit\<close> where
  \<open>print_binary_red_removed _ = ()\<close>

definition print_purelit_elim :: \<open>64 word \<Rightarrow> unit\<close> where
  \<open>print_purelit_elim _ = ()\<close>

definition print_purelit_rounds :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> unit\<close> where
  \<open>print_purelit_rounds _ _ = ()\<close>

definition print_lbds :: \<open>64 word \<Rightarrow> unit\<close> where
  \<open>print_lbds _ = ()\<close>

definition print_forward_rounds :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> unit\<close> where
  \<open>print_forward_rounds _ _ = ()\<close>

definition print_forward_subsumed :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> unit\<close> where
  \<open>print_forward_subsumed _ _ = ()\<close>

definition print_forward_tried :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> unit\<close> where
  \<open>print_forward_tried _ _ = ()\<close>

definition print_forward_strengthened :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> unit\<close> where
  \<open>print_forward_strengthened _ _ = ()\<close>

sepref_def print_propa_impl
  is \<open>RETURN o print_propa\<close>
  :: \<open>word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_propa_def
  by sepref

sepref_def print_confl_impl
  is \<open>RETURN o print_confl\<close>
  :: \<open>word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_confl_def
  by sepref

sepref_def print_dec_impl
  is \<open>RETURN o print_dec\<close>
  :: \<open>word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_dec_def
  by sepref

sepref_def print_res_impl
  is \<open>uncurry (RETURN oo print_res)\<close>
  :: \<open>word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_res_def
  by sepref

sepref_def print_lres_impl
  is \<open>uncurry (RETURN oo print_lres)\<close>
  :: \<open>word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_lres_def
  by sepref

sepref_def print_uset_impl
  is \<open>RETURN o print_uset\<close>
  :: \<open>word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_uset_def
  by sepref

definition print_irred_clss :: \<open>64 word \<Rightarrow> unit\<close> where
  \<open>print_irred_clss _ = ()\<close>

sepref_def print_gc_impl
  is \<open>uncurry (RETURN oo print_gcs)\<close>
  :: \<open>word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_gcs_def
  by sepref

sepref_def print_irred_clss_impl
  is \<open>RETURN o print_irred_clss\<close>
  :: \<open>word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_irred_clss_def
  by sepref

sepref_def print_binary_unit_impl
  is \<open>RETURN o print_binary_unit\<close>
  :: \<open>word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_binary_unit_def
  by sepref

sepref_def print_purelit_rounds_impl
  is \<open>uncurry (RETURN oo print_purelit_rounds)\<close>
  :: \<open>word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_purelit_rounds_def
  by sepref

sepref_def print_purelit_elim_impl
  is \<open>RETURN o print_purelit_elim\<close>
  :: \<open>word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_purelit_elim_def
  by sepref

sepref_def print_binary_red_removed_impl
  is \<open>RETURN o print_binary_red_removed\<close>
  :: \<open>word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_binary_red_removed_def
  by sepref

sepref_def print_forward_rounds_impl
  is \<open>uncurry (RETURN oo print_forward_rounds)\<close>
  :: \<open>word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_forward_rounds_def
  by sepref

sepref_def print_forward_subsumed_impl
  is \<open>uncurry (RETURN oo print_forward_subsumed)\<close>
  :: \<open>word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_forward_subsumed_def
  by sepref

sepref_def print_forward_tried_impl
  is \<open>uncurry (RETURN oo print_forward_tried)\<close>
  :: \<open>word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_forward_tried_def
  by sepref

sepref_def print_forward_strengthened_impl
  is \<open>uncurry (RETURN oo print_forward_strengthened)\<close>
  :: \<open>word_assn\<^sup>k *\<^sub>a word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_forward_strengthened_def
  by sepref

end