theory IsaSAT_LBD_LLVM
  imports IsaSAT_LBD IsaSAT_Setup0_LLVM
begin

sepref_register mark_lbd_from_clause_heur get_level_pol mark_lbd_from_list_heur
  mark_lbd_from_conflict mop_arena_status

sepref_def mark_lbd_from_clause_heur_impl
  is \<open>uncurry3 mark_lbd_from_clause_heur\<close>
  :: \<open>trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a lbd_assn\<^sup>d \<rightarrow>\<^sub>a lbd_assn\<close>
  unfolding mark_lbd_from_clause_heur_def nfoldli_upt_by_while
  apply (rewrite at \<open>_ = \<hole>\<close> unat_const_fold[where 'a=32])
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_def calculate_LBD_heur_st_impl
  is \<open>uncurry3 calculate_LBD_heur_st\<close>
  :: \<open>trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>d *\<^sub>a lbd_assn\<^sup>d *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a
     arena_fast_assn \<times>\<^sub>a lbd_assn\<close>
  supply [[goals_limit=1]]
  unfolding calculate_LBD_heur_st_def isasat_bounded_assn_def
    fold_tuple_optimizations
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref

sepref_def mark_lbd_from_list_heur_impl
  is \<open>uncurry2 mark_lbd_from_list_heur\<close>
  :: \<open>trail_pol_fast_assn\<^sup>k *\<^sub>a out_learned_assn\<^sup>k *\<^sub>a lbd_assn\<^sup>d \<rightarrow>\<^sub>a lbd_assn\<close>
  supply [[goals_limit=1]]
  unfolding mark_lbd_from_list_heur_def nfoldli_upt_by_while
  apply (rewrite at \<open>_ = \<hole>\<close> unat_const_fold[where 'a=32])
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref


lemma mark_lbd_from_conflict_alt_def:
  \<open>mark_lbd_from_conflict = (\<lambda>S. do{
     let (M, S) = extract_trail_wl_heur S;
     let (outl, S) = extract_outl_wl_heur S;
     let (lbd, S) = extract_lbd_wl_heur S;
     lbd \<leftarrow> mark_lbd_from_list_heur M outl lbd;
     RETURN (update_lbd_wl_heur lbd (update_trail_wl_heur M (update_outl_wl_heur outl S)))
    })\<close>
  by (auto simp: state_extractors mark_lbd_from_conflict_def split: isasat_int_splits)

sepref_def mark_lbd_from_conflict_impl
  is \<open>mark_lbd_from_conflict\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding mark_lbd_from_conflict_alt_def
  by sepref

lemma update_lbd_pre_arena_act_preD:
  \<open>update_lbd_pre ((a, ba), b) \<Longrightarrow>
  arena_act_pre (update_lbd a ba b) a\<close>
  unfolding update_lbd_pre_def arena_act_pre_def prod.simps
  by (auto simp: arena_is_valid_clause_idx_def intro!: valid_arena_update_lbd)

sepref_register update_lbd_and_mark_used
sepref_def update_lbd_and_mark_used_impl
  is \<open>uncurry2 (RETURN ooo update_lbd_and_mark_used)\<close>
    :: \<open>[update_lbd_pre]\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>d  \<rightarrow> arena_fast_assn\<close>
  unfolding update_lbd_and_mark_used_def LBD_SHIFT_def
  supply [dest] = update_lbd_pre_arena_act_preD
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref

sepref_def update_lbd_shrunk_clause_impl
  is \<open>uncurry update_lbd_shrunk_clause\<close>
  :: \<open>sint64_nat_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>d \<rightarrow>\<^sub>a arena_fast_assn\<close>
  unfolding update_lbd_shrunk_clause_def
  apply (rewrite  at \<open>If (\<hole> \<le> _)\<close> annot_unat_snat_upcast[where 'l=64])
  apply (rewrite at \<open>If (_ \<le> (_ - \<hole>))\<close> snat_const_fold[where 'a=64])
  apply (rewrite at \<open>If (_ \<le> _) _ (\<hole> - _)\<close> annot_snat_unat_conv)
  apply (rewrite  at \<open>If (_ \<le> _) _ (\<hole> - _)\<close> annot_unat_unat_downcast[where 'l=32])
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref

end