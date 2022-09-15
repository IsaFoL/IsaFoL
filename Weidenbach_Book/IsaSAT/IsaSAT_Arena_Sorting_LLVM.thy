theory IsaSAT_Arena_Sorting_LLVM
  imports IsaSAT_Sorting_LLVM IsaSAT_Arena_LLVM
begin

type_synonym vdom_fast_assn = \<open>64 word array_list64\<close>
abbreviation vdom_fast_assn :: \<open>vdom \<Rightarrow> vdom_fast_assn \<Rightarrow> assn\<close> where
  \<open>vdom_fast_assn \<equiv> arl64_assn sint64_nat_assn\<close>

sepref_def delete_index_and_swap_code2
  is \<open>uncurry (RETURN oo delete_index_and_swap)\<close>
  :: \<open>[\<lambda>(xs, i). i < length xs]\<^sub>a
      vdom_fast_assn\<^sup>d *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> vdom_fast_assn\<close>
  unfolding delete_index_and_swap.simps
  by sepref

definition idx_cdom :: \<open>arena \<Rightarrow> nat set\<close> where
 \<open>idx_cdom arena \<equiv> {i. valid_sort_clause_score_pre_at arena i}\<close>

sepref_register clause_score_extract arena_status arena_lbd uint32_max DELETED

lemma valid_sort_clause_score_pre_at_alt_def:
  \<open>valid_sort_clause_score_pre_at arena C \<longleftrightarrow>
    (\<exists>i vdom. C = vdom ! i \<and> arena_is_valid_clause_vdom arena (vdom!i) \<and>
          (arena_status arena (vdom!i) \<noteq> DELETED \<longrightarrow>
            ((get_clause_LBD_pre arena (vdom!i) \<and> arena_act_pre arena (vdom!i)) \<and>
            arena_is_valid_clause_idx arena C))
          \<and> i < length vdom)\<close>
  unfolding valid_sort_clause_score_pre_at_def arena_is_valid_clause_idx_def
     arena_act_pre_def arena_is_valid_clause_idx_def by auto

sepref_def (in -) clause_score_extract_code
  is \<open>uncurry (RETURN oo clause_score_extract)\<close>
  :: \<open>[uncurry valid_sort_clause_score_pre_at]\<^sub>a
      arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn \<times>\<^sub>a sint64_nat_assn \<times>\<^sub>a sint64_nat_assn\<close>
  supply [[goals_limit = 1]]
  unfolding clause_score_extract_def valid_sort_clause_score_pre_at_alt_def uint64_max_def[simplified]
  by sepref

sepref_def (in -) clause_score_ordering_code
  is \<open>uncurry (RETURN oo clause_score_ordering)\<close>
  :: \<open>(uint32_nat_assn \<times>\<^sub>a sint64_nat_assn \<times>\<^sub>a sint64_nat_assn)\<^sup>k *\<^sub>a (uint32_nat_assn \<times>\<^sub>a sint64_nat_assn \<times>\<^sub>a sint64_nat_assn)\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
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
  Mreturn Mreturn
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
  Mreturn Mreturn
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


definition idx_clause_cdom :: \<open>arena \<Rightarrow> nat set\<close> where
 \<open>idx_clause_cdom arena \<equiv> {i. arena_is_valid_clause_idx arena i}\<close>

sepref_def (in -) arena_length_code
  is \<open>uncurry (RETURN oo arena_length)\<close>
  :: \<open>[uncurry arena_is_valid_clause_idx]\<^sub>a
      arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> sint64_nat_assn\<close>
  supply [[goals_limit = 1]]
  unfolding clause_score_extract_def valid_sort_clause_score_pre_at_alt_def uint64_max_def[simplified]
  by sepref

sepref_def (in -) clause_size_ordering_code
  is \<open>uncurry (RETURN oo (\<le>))\<close>
  :: \<open>(sint64_nat_assn)\<^sup>k *\<^sub>a (sint64_nat_assn)\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  supply [[goals_limit = 1]]
  unfolding clause_score_ordering_def
  by sepref

definition clause_size_less where
  \<open>clause_size_less arena i j = (arena_length arena i < arena_length arena j)\<close>

definition mop_clause_size_less where
  \<open>mop_clause_size_less arena i j = do {
    ASSERT(arena_is_valid_clause_idx arena i);
    ASSERT(arena_is_valid_clause_idx arena j);
    RETURN (clause_size_less arena i j)
  }\<close>

sepref_def mop_clause_size_less_impl
  is \<open>uncurry2 mop_clause_size_less\<close>
  :: \<open>arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding mop_clause_size_less_def clause_size_less_def
  by sepref


interpretation Size_Ordering: weak_ordering_on_lt where
  C = \<open>idx_clause_cdom vs\<close> and
  less = \<open>clause_size_less vs\<close>
  by unfold_locales
   (auto simp: clause_size_less_def clause_score_extract_def
      clause_score_ordering_def split: if_splits)

interpretation Size_Ordering: parameterized_weak_ordering idx_clause_cdom clause_size_less
    mop_clause_size_less
  by unfold_locales
   (auto simp: mop_clause_size_less_def
     idx_clause_cdom_def clause_size_less_def)

global_interpretation Size_Ordering: parameterized_sort_impl_context
  \<open>woarray_assn snat_assn\<close> \<open>eoarray_assn snat_assn\<close> snat_assn
  Mreturn Mreturn
  eo_extract_impl
  array_upd
  idx_clause_cdom clause_size_less mop_clause_size_less mop_clause_size_less_impl
  \<open>arena_fast_assn\<close>
  defines
          Size_Ordering_is_guarded_insert_impl = Size_Ordering.is_guarded_param_insert_impl
      and Size_Ordering_is_unguarded_insert_impl = Size_Ordering.is_unguarded_param_insert_impl
      and Size_Ordering_unguarded_insertion_sort_impl = Size_Ordering.unguarded_insertion_sort_param_impl
      and Size_Ordering_guarded_insertion_sort_impl = Size_Ordering.guarded_insertion_sort_param_impl
      and Size_Ordering_final_insertion_sort_impl = Size_Ordering.final_insertion_sort_param_impl
      (*and Size_Ordering_mop_lchild_impl  = Size_Ordering.mop_lchild_impl
      and Size_Ordering_mop_rchild_impl  = Size_Ordering.mop_rchild_impl
      and Size_Ordering_has_rchild_impl  = Size_Ordering.has_rchild_impl
      and Size_Ordering_has_lchild_impl  = Size_Ordering.has_lchild_impl *)

      and Size_Ordering_pcmpo_idxs_impl  = Size_Ordering.pcmpo_idxs_impl
      and Size_Ordering_pcmpo_v_idx_impl  = Size_Ordering.pcmpo_v_idx_impl
      and Size_Ordering_pcmpo_idx_v_impl  = Size_Ordering.pcmpo_idx_v_impl
      and Size_Ordering_pcmp_idxs_impl  = Size_Ordering.pcmp_idxs_impl

      and Size_Ordering_mop_geth_impl    = Size_Ordering.mop_geth_impl
      and Size_Ordering_mop_seth_impl    = Size_Ordering.mop_seth_impl
      and Size_Ordering_sift_down_impl   = Size_Ordering.sift_down_impl
      and Size_Ordering_heapify_btu_impl = Size_Ordering.heapify_btu_impl
      and Size_Ordering_heapsort_impl    = Size_Ordering.heapsort_param_impl
      and Size_Ordering_qsp_next_l_impl       = Size_Ordering.qsp_next_l_impl
      and Size_Ordering_qsp_next_h_impl       = Size_Ordering.qsp_next_h_impl
      and Size_Ordering_qs_partition_impl     = Size_Ordering.qs_partition_impl
(*      and Size_Ordering_qs_partitionXXX_impl     = Size_Ordering.qs_partitionXXX_impl *)
      and Size_Ordering_partition_pivot_impl  = Size_Ordering.partition_pivot_impl
      and Size_Ordering_introsort_aux_impl = Size_Ordering.introsort_aux_param_impl
      and Size_Ordering_introsort_impl        = Size_Ordering.introsort_param_impl
      and Size_Ordering_move_median_to_first_impl = Size_Ordering.move_median_to_first_param_impl

  apply unfold_locales
  unfolding GEN_ALGO_def refines_param_relp_def (* TODO: thm gen_refines_param_relpI *)
  by (rule mop_clause_size_less_impl.refine)

global_interpretation Size_Ordering_it: parameterized_sort_impl_context
  vdom_fast_assn \<open>LBD_it.eo_assn\<close> sint64_nat_assn
  Mreturn Mreturn
  LBD_it_eo_extract_impl
  arl_upd
  idx_clause_cdom clause_size_less mop_clause_size_less mop_clause_size_less_impl
  \<open>arena_fast_assn\<close>
  defines
          Size_Ordering_it_is_guarded_insert_impl = Size_Ordering_it.is_guarded_param_insert_impl
      and Size_Ordering_it_is_unguarded_insert_impl = Size_Ordering_it.is_unguarded_param_insert_impl
      and Size_Ordering_it_unguarded_insertion_sort_impl = Size_Ordering_it.unguarded_insertion_sort_param_impl
      and Size_Ordering_it_guarded_insertion_sort_impl = Size_Ordering_it.guarded_insertion_sort_param_impl
      and Size_Ordering_it_final_insertion_sort_impl = Size_Ordering_it.final_insertion_sort_param_impl
      (*and Size_Ordering_it_mop_lchild_impl  = Size_Ordering_it.mop_lchild_impl
      and Size_Ordering_it_mop_rchild_impl  = Size_Ordering_it.mop_rchild_impl
      and Size_Ordering_it_has_rchild_impl  = Size_Ordering_it.has_rchild_impl
      and Size_Ordering_it_has_lchild_impl  = Size_Ordering_it.has_lchild_impl *)

      and Size_Ordering_it_pcmpo_idxs_impl  = Size_Ordering_it.pcmpo_idxs_impl
      and Size_Ordering_it_pcmpo_v_idx_impl  = Size_Ordering_it.pcmpo_v_idx_impl
      and Size_Ordering_it_pcmpo_idx_v_impl  = Size_Ordering_it.pcmpo_idx_v_impl
      and Size_Ordering_it_pcmp_idxs_impl  = Size_Ordering_it.pcmp_idxs_impl

      and Size_Ordering_it_mop_geth_impl    = Size_Ordering_it.mop_geth_impl
      and Size_Ordering_it_mop_seth_impl    = Size_Ordering_it.mop_seth_impl
      and Size_Ordering_it_sift_down_impl   = Size_Ordering_it.sift_down_impl
      and Size_Ordering_it_heapify_btu_impl = Size_Ordering_it.heapify_btu_impl
      and Size_Ordering_it_heapsort_impl    = Size_Ordering_it.heapsort_param_impl
      and Size_Ordering_it_qsp_next_l_impl       = Size_Ordering_it.qsp_next_l_impl
      and Size_Ordering_it_qsp_next_h_impl       = Size_Ordering_it.qsp_next_h_impl
      and Size_Ordering_it_qs_partition_impl     = Size_Ordering_it.qs_partition_impl
(*      and Size_Ordering_it_qs_partitionXXX_impl     = Size_Ordering_it.qs_partitionXXX_impl *)
      and Size_Ordering_it_partition_pivot_impl  = Size_Ordering_it.partition_pivot_impl
      and Size_Ordering_it_introsort_aux_impl = Size_Ordering_it.introsort_aux_param_impl
      and Size_Ordering_it_introsort_impl        = Size_Ordering_it.introsort_param_impl
      and Size_Ordering_it_move_median_to_first_impl = Size_Ordering_it.move_median_to_first_param_impl

  apply unfold_locales
  unfolding GEN_ALGO_def refines_param_relp_def (* TODO: thm gen_refines_param_relpI *)
  apply (rule mop_clause_size_less_impl.refine)
  done



lemmas [llvm_inline] = LBD_it.eo_extract_impl_def[THEN meta_fun_cong, THEN meta_fun_cong]

export_llvm
  \<open>LBD_heapsort_impl :: _ \<Rightarrow> _ \<Rightarrow> _\<close>
  \<open>LBD_introsort_impl :: _ \<Rightarrow> _ \<Rightarrow> _\<close>
  \<open>Size_Ordering_heapsort_impl :: _ \<Rightarrow> _ \<Rightarrow> _\<close>
  \<open>Size_Ordering_introsort_impl :: _ \<Rightarrow> _ \<Rightarrow> _\<close>


type_synonym virtual_vdom_fast_assn = \<open>64 word\<close>
definition virtual_vdom_fast_assn :: \<open>vdom \<Rightarrow> virtual_vdom_fast_assn \<Rightarrow> _\<close> where
  \<open>virtual_vdom_fast_assn = hr_comp sint64_nat_assn {(a,b). a= 0}\<close>

definition qqq where \<open>qqq xs _ = Mreturn xs\<close>
lemmas [llvm_inline] = qqq_def

lemma [unfolded qqq_def, sepref_fr_rules]:
  \<open>(uncurry (qqq), uncurry (RETURN oo op_list_append))
  \<in> virtual_vdom_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a virtual_vdom_fast_assn\<close>
proof -
  have [iff]: \<open>x = snat u \<and> snat_invar u \<and> x = 0 \<longleftrightarrow> x = 0 \<and> u= 0\<close> for x u
    by (auto intro: snat_invar_0)
     (auto simp add: snat_eq_unat_aux2 unat_arith_simps(3))

  have [simp]: "\<And>ns u. virtual_vdom_fast_assn (ns::nat list) (u) = \<up>(u=0)"
    by (auto simp add: Sepref_Basic.pure_def virtual_vdom_fast_assn_def hr_comp_def snat_rel_def
      snat.rel_def br_def
      simp flip: import_param_3
      simp del: import_param_3)
     (auto simp: import_param_3 exists_eq_star_conv)

  have [simp]: \<open>(\<exists>x. (\<up>True \<and>* \<up>(x = a @ [b])) s) = \<box> s\<close> for a b s
    by (auto simp: Exists_eq_simp, simp_all add: pure_true_conv) 
  show ?thesis
    unfolding qqq_def
    apply sepref_to_hoare
    by (vcg)
qed


definition empty_virtual_vdom :: \<open>nat list\<close> where
  \<open>empty_virtual_vdom = []\<close>

sepref_register empty_virtual_vdom
lemma [sepref_fr_rules]:
  \<open>(uncurry0 (Mreturn 0), uncurry0 (RETURN empty_virtual_vdom))
  \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a virtual_vdom_fast_assn\<close>
proof -
  have [iff]: \<open>x = snat u \<and> snat_invar u \<and> x = 0 \<longleftrightarrow> x = 0 \<and> u= 0\<close> for x u
    by (auto intro: snat_invar_0)
     (auto simp add: snat_eq_unat_aux2 unat_arith_simps(3))

  have [simp]: "\<And>ns u. virtual_vdom_fast_assn (ns::nat list) (u) = \<up>(u=0)"
    by (auto simp add: Sepref_Basic.pure_def virtual_vdom_fast_assn_def hr_comp_def snat_rel_def
      snat.rel_def br_def
      simp flip: import_param_3
      simp del: import_param_3)
     (auto simp: import_param_3 exists_eq_star_conv)

  have [simp]: \<open>(\<exists>x. (\<up>True \<and>* \<up>(x = a @ [b])) s) = \<box> s\<close> for a b s
    by (auto simp: Exists_eq_simp, simp_all add: pure_true_conv) 
  show ?thesis
    unfolding qqq_def
    apply sepref_to_hoare
    by (vcg)
qed

schematic_goal mk_free_ghost_assn[sepref_frame_free_rules]: \<open>MK_FREE virtual_vdom_fast_assn ?fr\<close>
  unfolding virtual_vdom_fast_assn_def
  by synthesize_free

experiment
begin
definition \<open>test0 \<equiv> (\<lambda> xs C. RETURN (xs @ [C]))\<close>
sepref_def test
  is \<open>uncurry test0\<close>
  :: \<open>virtual_vdom_fast_assn\<^sup>k  *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a virtual_vdom_fast_assn\<close>
  supply [[goals_limit=1]]
  unfolding test0_def
  by sepref

    export_llvm test
 end
end
