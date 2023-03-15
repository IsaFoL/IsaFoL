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
  :: \<open>[\<lambda>((N, _), _). length N \<le> sint64_max]\<^sub>a
       arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a heuristic_bump_assn\<^sup>d \<rightarrow> heuristic_bump_assn\<close>
  supply [[goals_limit=1]] arena_is_valid_clause_idx_le_uint64_max[intro]
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
  :: \<open>[\<lambda>((((_, N), _), _), _). length N \<le> sint64_max]\<^sub>a
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

sepref_def isa_vmtf_bump_to_rescore_also_reasons_cl_impl
  is \<open>uncurry4 (isa_vmtf_bump_to_rescore_also_reasons_cl)\<close>
  :: \<open>[\<lambda>((((_, N), _), _), _). length N \<le> sint64_max]\<^sub>a
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

experiment begin

export_llvm
  isa_vmtf_bump_to_rescore_also_reasons_cl_impl
  vmtf_mark_to_rescore_also_reasons_fast_code
  isa_bump_rescore_fast_code
  isa_bump_mark_to_rescore_clause_fast_code
  isa_bump_heur_flush_impl

end

end