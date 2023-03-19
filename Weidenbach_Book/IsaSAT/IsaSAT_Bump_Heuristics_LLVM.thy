theory IsaSAT_Bump_Heuristics_LLVM
  imports IsaSAT_Bump_Heuristics
    IsaSAT_VMTF_LLVM
    Tuple4_LLVM
    IsaSAT_Bump_Heuristics_State_LLVM
begin


(*TODO remove isa_vmtf_unset = vmtf_unset *)
lemma isa_bump_unset_alt_def:
  \<open>RETURN oo isa_bump_unset = (\<lambda>L vm. case vm of Tuple4 (hstable) (focused) foc a \<Rightarrow>
  RETURN (Tuple4 (if \<not>foc then isa_vmtf_unset L hstable else hstable)
    (if foc then isa_vmtf_unset L focused else focused)
  foc a))\<close>
  unfolding isa_bump_unset_def isa_vmtf_unset_def vmtf_unset_def[symmetric]
  by (auto intro!: ext split: bump_heuristics_splits)


sepref_register vmtf_unset case_tuple4
sepref_def isa_bump_unset_impl
  is \<open>uncurry (RETURN oo isa_bump_unset)\<close>
  :: \<open>[uncurry isa_bump_unset_pre]\<^sub>a atom_assn\<^sup>k *\<^sub>a heuristic_bump_assn\<^sup>d \<rightarrow> heuristic_bump_assn\<close>
  unfolding isa_bump_unset_alt_def isa_bump_unset_pre_def
  by sepref

sepref_def isa_find_decomp_wl_imp_impl
  is \<open>uncurry2 isa_find_decomp_wl_imp\<close>
  :: \<open>trail_pol_fast_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a heuristic_bump_assn\<^sup>d \<rightarrow>\<^sub>a
  trail_pol_fast_assn \<times>\<^sub>a heuristic_bump_assn\<close>
  unfolding isa_find_decomp_wl_imp_def get_maximum_level_remove_def[symmetric] PR_CONST_def
    trail_pol_conv_to_no_CS_def
  supply trail_conv_to_no_CS_def[simp] lit_of_hd_trail_def[simp]
  supply [[goals_limit=1]] literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset[simp]
  supply vmtf_unset_pre_def[simp]
  apply (rewrite at \<open>let _ = _ - \<hole> in _\<close> annot_unat_snat_upcast[where 'l=64])
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_register isa_bump_mark_to_rescore isa_find_decomp_wl_imp
sepref_def isa_bump_mark_to_rescore_code
  is \<open>uncurry (isa_bump_mark_to_rescore)\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a heuristic_bump_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_bump_assn\<close>
  supply [[goals_limit=1]] option.splits[split] vmtf_def[simp] in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff[simp]
    neq_NilE[elim!] literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset[simp]
  unfolding isa_vmtf_mark_to_rescore_pre_def isa_vmtf_mark_to_rescore_def
    isa_bump_mark_to_rescore_def
  by sepref


sepref_def isa_bump_mark_to_rescore_clause_fast_code
  is \<open>uncurry2 (isa_bump_mark_to_rescore_clause)\<close>
  :: \<open>[\<lambda>((N, _), _). length N \<le> snat64_max]\<^sub>a
       arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a heuristic_bump_assn\<^sup>d \<rightarrow> heuristic_bump_assn\<close>
  supply [[goals_limit=1]] arena_is_valid_clause_idx_le_unat64_max[intro]
  unfolding isa_bump_mark_to_rescore_clause_def PR_CONST_def
  unfolding while_eq_nfoldli[symmetric]
  apply (subst while_upt_while_direct, simp)
  unfolding nres_monad3
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref


sepref_def isa_bump_rescore_fast_code
  is \<open>uncurry2 isa_bump_rescore\<close>
  :: \<open>clause_ll_assn\<^sup>k *\<^sub>a trail_pol_fast_assn\<^sup>k *\<^sub>a heuristic_bump_assn\<^sup>d \<rightarrow>\<^sub>a
       heuristic_bump_assn\<close>
  unfolding isa_bump_rescore_def[abs_def] PR_CONST_def isa_bump_rescore_body_def
  supply [[goals_limit = 1]] fold_is_None[simp]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_def vmtf_mark_to_rescore_also_reasons_fast_code
  is \<open>uncurry4 (isa_vmtf_mark_to_rescore_also_reasons)\<close>
  :: \<open>[\<lambda>((((_, N), _), _), _). length N \<le> snat64_max]\<^sub>a
      trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a out_learned_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a heuristic_bump_assn\<^sup>d \<rightarrow>
      heuristic_bump_assn\<close>
  supply image_image[simp] uminus_\<A>\<^sub>i\<^sub>n_iff[iff] in_diffD[dest] option.splits[split]
    in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n[simp]
  supply [[goals_limit=1]]
  unfolding isa_vmtf_mark_to_rescore_also_reasons_def PR_CONST_def
  unfolding while_eq_nfoldli[symmetric]
  apply (subst while_upt_while_direct, simp)
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  unfolding  nres_monad3 case_option_split
  by sepref

sepref_register isa_vmtf_bump_to_rescore_also_reasons_cl isa_vmtf_mark_to_rescore_also_reasons
  isa_bump_heur_flush
  
sepref_def isa_vmtf_bump_to_rescore_also_reasons_cl_impl
  is \<open>uncurry4 (isa_vmtf_bump_to_rescore_also_reasons_cl)\<close>
  :: \<open>[\<lambda>((((_, N), _), _), _). length N \<le> snat64_max]\<^sub>a
  trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a heuristic_bump_assn\<^sup>d \<rightarrow>
  heuristic_bump_assn\<close>
  supply image_image[simp] uminus_\<A>\<^sub>i\<^sub>n_iff[iff] in_diffD[dest] option.splits[split]
    in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n[simp]
  supply [[goals_limit=1]]
  supply [dest] = isa_vmtf_bump_to_rescore_also_reasons_clD
  unfolding isa_vmtf_bump_to_rescore_also_reasons_cl_def PR_CONST_def
  unfolding while_eq_nfoldli[symmetric]
  apply (subst while_upt_while_direct, simp)
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  unfolding nres_monad3 case_option_split
  by sepref

sepref_def isa_bump_heur_flush_impl
  is \<open>uncurry isa_bump_heur_flush\<close>
  :: \<open>trail_pol_fast_assn\<^sup>k *\<^sub>a heuristic_bump_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_bump_assn\<close>
  unfolding isa_bump_heur_flush_def
 by sepref


sepref_def isa_vmtf_heur_fst_code
  is \<open>isa_vmtf_heur_fst\<close>
  :: \<open>heuristic_bump_assn\<^sup>k \<rightarrow>\<^sub>a atom_assn\<close>
  unfolding isa_vmtf_heur_fst_def
  by sepref

definition isa_vmtf_heur_array_nth where
  \<open>isa_vmtf_heur_array_nth x = vmtf_heur_array_nth (bump_get_heuristics x)\<close>

lemma isa_vmtf_heur_array_nth_alt_def:
  \<open>isa_vmtf_heur_array_nth x i = (case x of Bump_Heuristics hstable focused foc _ \<Rightarrow>
     (if foc then vmtf_heur_array_nth focused i else vmtf_heur_array_nth hstable i))\<close>
  by (cases x) (auto simp: bump_get_heuristics_def isa_vmtf_heur_array_nth_def)

sepref_register is_focused_heuristics vmtf_heur_array_nth
sepref_def isa_vmtf_heur_array_nth_code
  is \<open>uncurry isa_vmtf_heur_array_nth\<close>
  :: \<open>[\<lambda>(vm, i). i < length (fst (bump_get_heuristics vm))]\<^sub>a heuristic_bump_assn\<^sup>k *\<^sub>a atom_assn\<^sup>k \<rightarrow> vmtf_node_assn\<close>
  supply if_splits[split]
  unfolding isa_vmtf_heur_array_nth_alt_def bump_get_heuristics_def
  by sepref


definition vmtf_array_fst :: \<open>vmtf \<Rightarrow> nat\<close> where
  \<open>vmtf_array_fst = (\<lambda>(a, b, c, d, e). c)\<close>


lemma bumped_vmtf_array_fst_alt_def: \<open>bumped_vmtf_array_fst x = (case x of Bump_Heuristics a b c d \<Rightarrow>
  (if c then vmtf_array_fst b else vmtf_array_fst a))\<close>
  by (cases x) (auto simp: vmtf_array_fst_def current_vmtf_array_nxt_score_def
    bump_get_heuristics_def bumped_vmtf_array_fst_def)

sepref_def vmtf_array_fst_code
  is \<open>RETURN o vmtf_array_fst\<close>
  :: \<open>vmtf_assn\<^sup>k \<rightarrow>\<^sub>a atom_assn\<close>
  unfolding vmtf_assn_def vmtf_array_fst_def
  by sepref

sepref_def bumped_vmtf_array_fst_code
  is \<open>RETURN o bumped_vmtf_array_fst\<close>
  :: \<open>heuristic_bump_assn\<^sup>k \<rightarrow>\<^sub>a atom_assn\<close>
  unfolding bumped_vmtf_array_fst_alt_def
  by sepref


sepref_register access_focused_vmtf_array

definition access_vmtf_array :: \<open>vmtf \<Rightarrow> nat \<Rightarrow> _ nres\<close> where
  \<open>access_vmtf_array = (\<lambda>(a, b, c, d, f) i. do {
  ASSERT (i < length a);
  RETURN (a ! i)})\<close>

lemma access_focused_vmtf_array_alt_def:
  \<open>access_focused_vmtf_array x i = (case x of Bump_Heuristics a b c d \<Rightarrow> do {
   if c then access_vmtf_array b i else access_vmtf_array a i
  })\<close>
  by (cases x) (auto simp: access_focused_vmtf_array_def access_vmtf_array_def
    bump_get_heuristics_def)


sepref_def access_vmtf_array_code
  is \<open>uncurry access_vmtf_array\<close>
  :: \<open>vmtf_assn\<^sup>k *\<^sub>a atom_assn\<^sup>k \<rightarrow>\<^sub>a vmtf_node_assn\<close>
  unfolding access_vmtf_array_def vmtf_assn_def
  apply (rewrite at \<open>RETURN \<hole>\<close> annot_index_of_atm)
  by sepref

sepref_register access_vmtf_array 
sepref_def access_focused_vmtf_array_code
  is \<open>uncurry access_focused_vmtf_array\<close>
  :: \<open>heuristic_bump_assn\<^sup>k *\<^sub>a atom_assn\<^sup>k \<rightarrow>\<^sub>a vmtf_node_assn\<close>
  unfolding access_focused_vmtf_array_alt_def
  by sepref

experiment begin

export_llvm
  isa_vmtf_bump_to_rescore_also_reasons_cl_impl
  vmtf_mark_to_rescore_also_reasons_fast_code
  isa_bump_rescore_fast_code
  isa_bump_mark_to_rescore_clause_fast_code
  isa_bump_heur_flush_impl
  isa_vmtf_heur_array_nth_code

end

end