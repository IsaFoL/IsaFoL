theory IsaSAT_Restart_Reduce_LLVM
  imports IsaSAT_Restart_Reduce IsaSAT_Setup_LLVM IsaSAT_VMTF_State_LLVM
begin

hide_fact (open) Sepref_Rules.frefI
no_notation Sepref_Rules.fref (\<open>[_]\<^sub>f\<^sub>d _ \<rightarrow> _\<close> [0,60,60] 60)
no_notation Sepref_Rules.freft (\<open>_ \<rightarrow>\<^sub>f\<^sub>d _\<close> [60,60] 60)
no_notation Sepref_Rules.freftnd (\<open>_ \<rightarrow>\<^sub>f _\<close> [60,60] 60)
no_notation Sepref_Rules.frefnd (\<open>[_]\<^sub>f _ \<rightarrow> _\<close> [0,60,60] 60)

sepref_def find_local_restart_target_level_fast_code
  is \<open>uncurry find_local_restart_target_level_int\<close>
  :: \<open>trail_pol_fast_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=1]] length_rev[simp del]
  unfolding find_local_restart_target_level_int_def find_local_restart_target_level_int_inv_def
    length_uint32_nat_def vmtf_remove_assn_def trail_pol_fast_assn_def
  apply (annot_unat_const \<open>TYPE(32)\<close>)
   apply (rewrite at \<open>stamp (\<hole>)\<close> annot_index_of_atm)
   apply (rewrite in \<open>(_ ! _)\<close> annot_unat_snat_upcast[where 'l=64])
   apply (rewrite in \<open>(_ ! \<hole>)\<close> annot_unat_snat_upcast[where 'l=64])
   apply (rewrite in \<open>(\<hole> < length _)\<close> annot_unat_snat_upcast[where 'l=64])
  by sepref


sepref_def find_local_restart_target_level_st_fast_code
  is \<open>find_local_restart_target_level_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=1]] length_rev[simp del]
  unfolding find_local_restart_target_level_st_alt_def isasat_bounded_assn_def PR_CONST_def
    fold_tuple_optimizations
  by sepref

sepref_def empty_Q_fast_code
  is \<open>empty_Q\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding empty_Q_def isasat_bounded_assn_def fold_tuple_optimizations
  by sepref

sepref_register cdcl_twl_local_restart_wl_D_heur
    empty_Q find_decomp_wl_st_int

sepref_def cdcl_twl_local_restart_wl_D_heur_fast_code
  is \<open>cdcl_twl_local_restart_wl_D_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding cdcl_twl_local_restart_wl_D_heur_def PR_CONST_def
    fold_tuple_optimizations
  supply [[goals_limit = 1]]
  by sepref

definition lbd_sort_clauses_raw :: \<open>arena \<Rightarrow> vdom \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list nres\<close> where
  \<open>lbd_sort_clauses_raw arena N = pslice_sort_spec idx_cdom clause_score_less arena N\<close>

definition lbd_sort_clauses :: \<open>arena \<Rightarrow> vdom \<Rightarrow> nat list nres\<close> where
  \<open>lbd_sort_clauses arena N = lbd_sort_clauses_raw arena N 0 (length N)\<close>

lemmas LBD_introsort[sepref_fr_rules] =
  LBD_it.introsort_param_impl_correct[unfolded lbd_sort_clauses_raw_def[symmetric] PR_CONST_def]

lemma quicksort_clauses_by_score_sort:
 \<open>(lbd_sort_clauses, sort_clauses_by_score) \<in>
   Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
   apply (intro fun_relI nres_relI)
   subgoal for arena arena' vdom vdom'
   by (auto simp: lbd_sort_clauses_def lbd_sort_clauses_raw_def sort_clauses_by_score_def
       pslice_sort_spec_def le_ASSERT_iff idx_cdom_def slice_rel_def br_def
       conc_fun_RES sort_spec_def
       eq_commute[of _ \<open>length vdom'\<close>]
     intro!: ASSERT_leI slice_sort_spec_refine_sort[THEN order_trans, of _ vdom vdom])
   done


sepref_register lbd_sort_clauses_raw
sepref_def lbd_sort_clauses_impl
  is \<open>uncurry lbd_sort_clauses\<close>
  :: \<open>arena_fast_assn\<^sup>k *\<^sub>a vdom_fast_assn\<^sup>d \<rightarrow>\<^sub>a vdom_fast_assn\<close>
  supply[[goals_limit=1]]
  unfolding lbd_sort_clauses_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

lemmas [sepref_fr_rules] =
  lbd_sort_clauses_impl.refine[FCOMP quicksort_clauses_by_score_sort]

sepref_register remove_deleted_clauses_from_avdom arena_status DELETED

sepref_def remove_deleted_clauses_from_avdom_fast_code
  is \<open>uncurry isa_remove_deleted_clauses_from_avdom\<close>
  :: \<open>[\<lambda>(N, vdom). length vdom \<le> sint64_max]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a vdom_fast_assn\<^sup>d \<rightarrow> vdom_fast_assn\<close>
  supply [[goals_limit=1]]
  unfolding isa_remove_deleted_clauses_from_avdom_def
    convert_swap gen_swap if_conn(4)
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_def isa_isa_remove_deleted_clauses_from_avdom_impl
  is \<open>uncurry isa_isa_remove_deleted_clauses_from_avdom\<close>
  :: \<open>[\<lambda>(arena, vdom). length (get_avdom_aivdom vdom) \<le> length arena]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a aivdom_assn\<^sup>d \<rightarrow> aivdom_assn\<close>
  unfolding isa_isa_remove_deleted_clauses_from_avdom_def
  by sepref

sepref_def sort_clauses_by_score_aivdom_impl
  is \<open>uncurry sort_clauses_by_score_aivdom\<close>
  :: \<open>[\<lambda>(arena, vdom). length (get_avdom_aivdom vdom) \<le> length arena]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a aivdom_assn\<^sup>d \<rightarrow> aivdom_assn\<close>
  unfolding sort_clauses_by_score_aivdom_def
  by sepref

sepref_def sort_vdom_heur_fast_code
  is \<open>sort_vdom_heur\<close>
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>aisasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply sort_clauses_by_score_invI[intro]
    [[goals_limit=1]]
  unfolding sort_vdom_heur_def isasat_bounded_assn_def
  by sepref


experiment
begin
  export_llvm sort_vdom_heur_fast_code remove_deleted_clauses_from_avdom_fast_code
end

end