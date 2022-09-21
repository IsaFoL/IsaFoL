theory IsaSAT_Setup4_LLVM
  imports
    IsaSAT_Setup
    IsaSAT_Setup0_LLVM
begin

definition length_occs where
  \<open>length_occs S = length (get_occs S)\<close>

sepref_def length_occs_raw
  is \<open>RETURN o length\<close>
  :: \<open>occs_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  unfolding op_list_list_len_def[symmetric]
  by sepref
term   op_list_list_llen

definition length_occs_impl where
  \<open>length_occs_impl = read_occs_wl_heur_code length_occs_raw\<close>

sepref_register length_occs

global_interpretation length_occs: read_occs_param_adder0 where
  f = \<open>length_occs_raw\<close> and
  f' = \<open>RETURN o length\<close> and
  x_assn = sint64_nat_assn and
  P = \<open>(\<lambda>S. True)\<close>
  rewrites \<open>read_occs_wl_heur (RETURN o length) = RETURN o length_occs\<close> and
  \<open>read_occs_wl_heur_code length_occs_raw = length_occs_impl\<close>
  apply unfold_locales
  apply (rule length_occs_raw.refine)
  subgoal
    by (auto simp: read_all_st_def length_occs_def intro!: ext
      split: isasat_int_splits)
  subgoal
    by (auto simp: length_occs_impl_def)
  done

term mop_cocc_list_length

definition length_occs_at where
  \<open>length_occs_at S i = mop_cocc_list_length (get_occs S) i\<close>

sepref_def mop_cocc_list_length_impl
  is \<open>uncurry (mop_cocc_list_length)\<close>
  :: \<open>[uncurry cocc_list_length_pre]\<^sub>a occs_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> sint64_nat_assn\<close>
  unfolding cocc_list_length_def
    cocc_list_length_pre_def fold_op_list_list_llen mop_cocc_list_length_def
  by sepref

definition length_occs_at_impl where
  \<open>length_occs_at_impl = (\<lambda>N C. read_occs_wl_heur_code (\<lambda>M. mop_cocc_list_length_impl M C) N)\<close>

sepref_register length_occs_at

global_interpretation length_occs_at: read_occs_param_adder where
  f = \<open>\<lambda>L S. mop_cocc_list_length_impl S L\<close> and
  f' = \<open>\<lambda>L S. mop_cocc_list_length S L\<close> and
  x_assn = sint64_nat_assn and
  P = \<open>\<lambda>L S. cocc_list_length_pre S L\<close> and
  R = \<open>unat_lit_rel\<close>
  rewrites \<open>(\<lambda>N C. read_occs_wl_heur_code (\<lambda>M. mop_cocc_list_length_impl M C) N) = length_occs_at_impl\<close> and
  \<open>(\<lambda>S C'. read_occs_wl_heur (\<lambda>L. mop_cocc_list_length L C') S) = length_occs_at\<close>
  apply unfold_locales
  apply (rule mop_cocc_list_length_impl.refine)
  subgoal
    by (auto simp: length_occs_at_impl_def)
  subgoal
    by (auto simp: read_all_st_def length_occs_at_def intro!: ext
      split: isasat_int_splits)
  done

lemma length_occs_at_alt_def:
    \<open>length_occs_at = length_occs_at.XX.mop\<close>
  by (auto simp: length_occs_at.XX.mop_def length_occs_at_def read_all_param_adder_ops.mop_def
    read_all_st_def summarize_ASSERT_conv
    mop_cocc_list_length_def split: tuple17.splits intro!: ext)

lemmas [sepref_fr_rules] = length_occs.refine[unfolded lambda_comp_true]
   length_occs_at.refine
   length_occs_at.XX.mop_refine[unfolded length_occs_at_alt_def[symmetric]]
lemmas [unfolded inline_direct_return_node_case, llvm_code] =
  length_occs_impl_def[unfolded read_all_st_code_def]
  length_occs_at_impl_def[unfolded read_all_st_code_def]

definition get_occs_list_at :: \<open>isasat \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat nres\<close> where
  \<open>get_occs_list_at S L i = mop_cocc_list_at (get_occs S) L i\<close>

sepref_def mop_cocc_list_at_impl
  is \<open>uncurry2 (mop_cocc_list_at)\<close>
  :: \<open>[uncurry2 cocc_list_at_pre]\<^sub>a occs_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> sint64_nat_assn\<close>
  unfolding mop_cocc_list_at_def cocc_list_at_def cocc_list_at_pre_def fold_op_list_list_idx
  by sepref

definition get_occs_list_at_impl :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> where
  \<open>get_occs_list_at_impl = (\<lambda>N C D. read_occs_wl_heur_code (\<lambda>M. mop_cocc_list_at_impl M C D) N)\<close>

global_interpretation occs_at_at: read_occs_param_adder2 where
  f = \<open>\<lambda>C D S. mop_cocc_list_at_impl S C D\<close> and
  f' = \<open>\<lambda>C D S. mop_cocc_list_at S C D\<close> and
  x_assn = sint64_nat_assn and
  P = \<open>\<lambda>C D S. cocc_list_at_pre S C D\<close> and
  R = \<open>unat_lit_rel\<close> and
  R' = \<open>snat_rel' TYPE(64)\<close>
  rewrites
    \<open>(\<lambda>N C D. read_occs_wl_heur (\<lambda>M. mop_cocc_list_at M C D) N) = get_occs_list_at\<close> and
    \<open>(\<lambda>N C D. read_occs_wl_heur_code (\<lambda>M. mop_cocc_list_at_impl M C D) N) = get_occs_list_at_impl\<close>
  apply unfold_locales
  apply (rule mop_cocc_list_at_impl.refine)
  subgoal
    by (auto simp: read_all_st_def get_occs_list_at_def intro!: ext
      split: isasat_int_splits)
  subgoal
    by (auto simp: get_occs_list_at_impl_def)
  done

lemma get_occs_list_at_alt_def: \<open>get_occs_list_at = (\<lambda>N C D. occs_at_at.XX.XX.mop N (C, D))\<close>
  by (auto simp: occs_at_at.XX.XX.mop_def get_occs_list_at_def mop_cocc_list_at_def read_all_param_adder_ops.mop_def
    read_all_st_def summarize_ASSERT_conv
    mop_cocc_list_length_def split: tuple17.splits intro!: ext)

lemmas [sepref_fr_rules] = occs_at_at.refine
  occs_at_at.mop_refine[unfolded get_occs_list_at_alt_def[symmetric]]

lemmas [unfolded inline_direct_return_node_case, llvm_code] =
  length_occs_impl_def[unfolded read_all_st_code_def]
  length_occs_at_impl_def[unfolded read_all_st_code_def]

lemma mop_arena_promote_st_alt_def:
    \<open>mop_arena_promote_st S C = do {
    let (N', S) = extract_arena_wl_heur S;
    let (lcount, S) = extract_lcount_wl_heur S;
    ASSERT(clss_size_lcount lcount \<ge> 1);
    let lcount = clss_size_decr_lcount lcount;
    N' \<leftarrow> mop_arena_set_status N' C IRRED;
    RETURN (update_arena_wl_heur N' (update_lcount_wl_heur lcount S))
  }\<close>
  by (auto simp: mop_arena_promote_st_def state_extractors split: isasat_int_splits)

sepref_def mop_arena_promote_st_impl
  is \<open>uncurry mop_arena_promote_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>d *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding mop_arena_promote_st_alt_def
  by sepref

sepref_def get_lsize_limit_stats_impl
  is \<open>RETURN o get_lsize_limit_stats\<close>
  :: \<open>isasat_stats_assn\<^sup>k \<rightarrow>\<^sub>a lbd_size_limit_assn\<close>
  unfolding stats_code_unfold
  by sepref

definition get_lsize_limit_stats_st_impl :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>get_lsize_limit_stats_st_impl = read_stats_wl_heur_code get_lsize_limit_stats_impl\<close>

global_interpretation lsize_limit: read_stats_param_adder0 where
  f' = \<open>RETURN o get_lsize_limit_stats\<close> and
  f = get_lsize_limit_stats_impl and
  x_assn = \<open>uint32_nat_assn \<times>\<^sub>a sint64_nat_assn\<close> and
  P = \<open>\<lambda>_. True\<close>
  rewrites \<open>read_stats_wl_heur (RETURN o get_lsize_limit_stats) = RETURN o get_lsize_limit_stats_st\<close> and
    \<open>read_stats_wl_heur_code get_lsize_limit_stats_impl = get_lsize_limit_stats_st_impl\<close>
  apply unfold_locales
  apply (rule get_lsize_limit_stats_impl.refine[unfolded lbd_size_limit_assn_def]; assumption)
  subgoal by (auto simp: read_all_st_def get_lsize_limit_stats_def get_lsize_limit_stats_def get_lsize_limit_stats_st_def
    intro!: ext
    split: isasat_int_splits)
  subgoal by (auto simp: get_lsize_limit_stats_st_impl_def)
  done

lemmas [sepref_fr_rules] = lsize_limit.refine

lemmas [unfolded inline_direct_return_node_case, llvm_code] =
  get_lsize_limit_stats_st_impl_def[unfolded read_all_st_code_def]


lemma set_stats_size_limit_st_alt_def:
  \<open>RETURN ooo set_stats_size_limit_st = (\<lambda>lbd sze T.
     let (stats, T) = extract_stats_wl_heur T;
         stats = set_stats_size_limit lbd sze stats
     in RETURN (update_stats_wl_heur stats T)
)\<close>
  by (auto simp: set_stats_size_limit_st_def state_extractors split: isasat_int_splits intro!: ext)

sepref_register \<open>LSize_Stats :: nat \<Rightarrow> nat \<Rightarrow> _\<close>
  IsaSAT_Stats_LLVM.update_f set_stats_size_limit_st

lemma set_stats_size_limit_alt_def:
  \<open>RETURN ooo set_stats_size_limit = (\<lambda>lbd size' stats. RETURN (set_lsize_limit_stats (LSize_Stats lbd size') stats))\<close>
  unfolding set_stats_size_limit_def LSize_Stats_def
  by (auto intro!: ext)

sepref_def set_stats_size_limit_impl
  is \<open>uncurry2 (RETURN ooo set_stats_size_limit)\<close>
  :: \<open>uint32_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_stats_assn\<^sup>d \<rightarrow>\<^sub>a isasat_stats_assn\<close>
  unfolding set_stats_size_limit_alt_def stats_code_unfold
  by sepref

sepref_def set_stats_size_limit_st_impl
  is \<open>uncurry2 (RETURN ooo set_stats_size_limit_st)\<close>
  :: \<open>uint32_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding set_stats_size_limit_st_alt_def
  by sepref

end
