theory IsaSAT_Arena_Sorting_LLVM
  imports IsaSAT_Sorting_LLVM
begin
definition idx_cdom :: \<open>arena \<Rightarrow> nat set\<close> where
 \<open>idx_cdom arena \<equiv> {i. valid_sort_clause_score_pre_at arena i}\<close>

definition mop_clause_score_less where
  \<open>mop_clause_score_less arena i j = do {
    ASSERT(valid_sort_clause_score_pre_at arena i);
    ASSERT(valid_sort_clause_score_pre_at arena j);
    RETURN (clause_score_ordering (clause_score_extract arena i) (clause_score_extract arena j))
  }\<close>

sepref_register clause_score_extract

sepref_def (in -) clause_score_extract_code
  is \<open>uncurry (RETURN oo clause_score_extract)\<close>
  :: \<open>[uncurry valid_sort_clause_score_pre_at]\<^sub>a
      arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn \<times>\<^sub>a sint64_nat_assn\<close>
  supply [[goals_limit = 1]]
  unfolding clause_score_extract_def valid_sort_clause_score_pre_at_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_def (in -) clause_score_ordering_code
  is \<open>uncurry (RETURN oo clause_score_ordering)\<close>
  :: \<open>(uint32_nat_assn \<times>\<^sub>a sint64_nat_assn)\<^sup>k *\<^sub>a (uint32_nat_assn \<times>\<^sub>a sint64_nat_assn)\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  supply [[goals_limit = 1]]
  unfolding clause_score_ordering_def
  by sepref

sepref_register mop_clause_score_less clause_score_less clause_score_ordering
sepref_def mop_clause_score_less_impl
  is \<open>uncurry2 mop_clause_score_less\<close>
  :: \<open>arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding mop_clause_score_less_def
  by sepref


interpretation LBD: weak_ordering_on_lt where
  C = \<open>idx_cdom vs\<close> and
  less = \<open>clause_score_less vs\<close>
  by unfold_locales
   (auto simp: clause_score_less_def clause_score_extract_def
      clause_score_ordering_def split: if_splits)

interpretation LBD: parameterized_weak_ordering idx_cdom clause_score_less
    mop_clause_score_less
  by unfold_locales
   (auto simp: mop_clause_score_less_def
     idx_cdom_def clause_score_less_def)

global_interpretation LBD: parameterized_sort_impl_context
  \<open>woarray_assn snat_assn\<close> \<open>eoarray_assn snat_assn\<close> snat_assn
  return return
  eo_extract_impl
  array_upd
  idx_cdom clause_score_less mop_clause_score_less mop_clause_score_less_impl
  \<open>arena_fast_assn\<close>
  defines
          LBD_is_guarded_insert_impl = LBD.is_guarded_param_insert_impl
      and LBD_is_unguarded_insert_impl = LBD.is_unguarded_param_insert_impl
      and LBD_unguarded_insertion_sort_impl = LBD.unguarded_insertion_sort_param_impl
      and LBD_guarded_insertion_sort_impl = LBD.guarded_insertion_sort_param_impl
      and LBD_final_insertion_sort_impl = LBD.final_insertion_sort_param_impl
      (*and LBD_mop_lchild_impl  = LBD.mop_lchild_impl
      and LBD_mop_rchild_impl  = LBD.mop_rchild_impl
      and LBD_has_rchild_impl  = LBD.has_rchild_impl
      and LBD_has_lchild_impl  = LBD.has_lchild_impl *)

      and LBD_pcmpo_idxs_impl  = LBD.pcmpo_idxs_impl
      and LBD_pcmpo_v_idx_impl  = LBD.pcmpo_v_idx_impl
      and LBD_pcmpo_idx_v_impl  = LBD.pcmpo_idx_v_impl
      and LBD_pcmp_idxs_impl  = LBD.pcmp_idxs_impl

      and LBD_mop_geth_impl    = LBD.mop_geth_impl
      and LBD_mop_seth_impl    = LBD.mop_seth_impl
      and LBD_sift_down_impl   = LBD.sift_down_impl
      and LBD_heapify_btu_impl = LBD.heapify_btu_impl
      and LBD_heapsort_impl    = LBD.heapsort_param_impl
      and LBD_qsp_next_l_impl       = LBD.qsp_next_l_impl
      and LBD_qsp_next_h_impl       = LBD.qsp_next_h_impl
      and LBD_qs_partition_impl     = LBD.qs_partition_impl
(*      and LBD_qs_partitionXXX_impl     = LBD.qs_partitionXXX_impl *)
      and LBD_partition_pivot_impl  = LBD.partition_pivot_impl
      and LBD_introsort_aux_impl = LBD.introsort_aux_param_impl
      and LBD_introsort_impl        = LBD.introsort_param_impl
      and LBD_move_median_to_first_impl = LBD.move_median_to_first_param_impl

  apply unfold_locales
  apply (rule eo_hnr_dep)+
  unfolding GEN_ALGO_def refines_param_relp_def (* TODO: thm gen_refines_param_relpI *)
  by (rule mop_clause_score_less_impl.refine)


global_interpretation
  LBD_it: pure_eo_adapter sint64_nat_assn vdom_fast_assn arl_nth arl_upd
  defines LBD_it_eo_extract_impl = LBD_it.eo_extract_impl
  apply (rule al_pure_eo)
  by simp



global_interpretation LBD_it: parameterized_sort_impl_context
  vdom_fast_assn \<open>LBD_it.eo_assn\<close> sint64_nat_assn
  return return
  LBD_it_eo_extract_impl
  arl_upd
  idx_cdom clause_score_less mop_clause_score_less mop_clause_score_less_impl
  \<open>arena_fast_assn\<close>
  defines
          LBD_it_is_guarded_insert_impl = LBD_it.is_guarded_param_insert_impl
      and LBD_it_is_unguarded_insert_impl = LBD_it.is_unguarded_param_insert_impl
      and LBD_it_unguarded_insertion_sort_impl = LBD_it.unguarded_insertion_sort_param_impl
      and LBD_it_guarded_insertion_sort_impl = LBD_it.guarded_insertion_sort_param_impl
      and LBD_it_final_insertion_sort_impl = LBD_it.final_insertion_sort_param_impl
      (*and LBD_it_mop_lchild_impl  = LBD_it.mop_lchild_impl
      and LBD_it_mop_rchild_impl  = LBD_it.mop_rchild_impl
      and LBD_it_has_rchild_impl  = LBD_it.has_rchild_impl
      and LBD_it_has_lchild_impl  = LBD_it.has_lchild_impl *)

      and LBD_it_pcmpo_idxs_impl  = LBD_it.pcmpo_idxs_impl
      and LBD_it_pcmpo_v_idx_impl  = LBD_it.pcmpo_v_idx_impl
      and LBD_it_pcmpo_idx_v_impl  = LBD_it.pcmpo_idx_v_impl
      and LBD_it_pcmp_idxs_impl  = LBD_it.pcmp_idxs_impl

      and LBD_it_mop_geth_impl    = LBD_it.mop_geth_impl
      and LBD_it_mop_seth_impl    = LBD_it.mop_seth_impl
      and LBD_it_sift_down_impl   = LBD_it.sift_down_impl
      and LBD_it_heapify_btu_impl = LBD_it.heapify_btu_impl
      and LBD_it_heapsort_impl    = LBD_it.heapsort_param_impl
      and LBD_it_qsp_next_l_impl       = LBD_it.qsp_next_l_impl
      and LBD_it_qsp_next_h_impl       = LBD_it.qsp_next_h_impl
      and LBD_it_qs_partition_impl     = LBD_it.qs_partition_impl
(*      and LBD_it_qs_partitionXXX_impl     = LBD_it.qs_partitionXXX_impl *)
      and LBD_it_partition_pivot_impl  = LBD_it.partition_pivot_impl
      and LBD_it_introsort_aux_impl = LBD_it.introsort_aux_param_impl
      and LBD_it_introsort_impl        = LBD_it.introsort_param_impl
      and LBD_it_move_median_to_first_impl = LBD_it.move_median_to_first_param_impl

  apply unfold_locales
  unfolding GEN_ALGO_def refines_param_relp_def (* TODO: thm gen_refines_param_relpI *)
  apply (rule mop_clause_score_less_impl.refine)
  done



lemmas [llvm_inline] = LBD_it.eo_extract_impl_def[THEN meta_fun_cong, THEN meta_fun_cong]

print_named_simpset llvm_inline
export_llvm
  \<open>LBD_heapsort_impl :: _ \<Rightarrow> _ \<Rightarrow> _\<close>
  \<open>LBD_introsort_impl :: _ \<Rightarrow> _ \<Rightarrow> _\<close>


end