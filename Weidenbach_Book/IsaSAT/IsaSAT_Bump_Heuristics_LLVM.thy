theory IsaSAT_Bump_Heuristics_LLVM
  imports IsaSAT_Bump_Heuristics
    IsaSAT_VMTF_LLVM
    Tuple4_LLVM
    IsaSAT_Bump_Heuristics_State_LLVM
    IsaSAT_ACIDS_LLVM
begin

sepref_register isa_acids_flush_int isa_acids_find_next_undef
  acids_push_literal isa_acids_incr_score

sepref_def isa_acids_incr_score_code
  is \<open>RETURN o isa_acids_incr_score\<close>
  :: \<open>acids_assn2\<^sup>d \<rightarrow>\<^sub>a acids_assn2\<close>
  unfolding isa_acids_incr_score_def acids_assn2_def
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

lemma isa_acids_flush_int_alt_def:
\<open>isa_acids_flush_int  = (\<lambda>M vm (to_remove, h). do {
    ASSERT(length to_remove \<le> unat32_max);
    let n = length to_remove;
    (_, vm, h) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i, vm', h). i \<le> n\<^esup>
      (\<lambda>(i, vm, h). i < n)
      (\<lambda>(i, vm, h). do {
         ASSERT(i < length to_remove);
         let L = to_remove!i;
         vm \<leftarrow> acids_push_literal L vm;
	 ASSERT(atoms_hash_del_pre L h);
         RETURN (i+1, vm, atoms_hash_del L h)})
      (0, vm, h);
    RETURN (vm, (emptied_list to_remove, h))
  })\<close>
  unfolding isa_acids_flush_int_def Let_def
  by auto

sepref_def acids_flush_int
  is \<open>uncurry2 isa_acids_flush_int\<close>
  :: \<open>trail_pol_fast_assn\<^sup>k *\<^sub>a acids_assn2\<^sup>d *\<^sub>a distinct_atoms_assn\<^sup>d  \<rightarrow>\<^sub>a acids_assn2 \<times>\<^sub>a distinct_atoms_assn \<close>
  unfolding isa_acids_flush_int_alt_def emptied_list_alt_def
  apply (rewrite at \<open>WHILEIT _ (\<lambda>(_, _, _)._ < \<hole>)\<close> annot_snat_unat_conv)
  apply (rewrite at \<open>_ ! \<hole>\<close> annot_unat_snat_conv)
  apply (rewrite at \<open>take \<hole> _\<close> snat_const_fold[where 'a=64])
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

definition acids0_mset_empty where
  \<open>acids0_mset_empty = (\<lambda>(_, b, _). b= {#})\<close>

definition hp_acids_empty where
  \<open>hp_acids_empty =  (\<lambda>(_, _, _, _, _, h). h = None)\<close>

lemma hp_acids_empty:
  \<open>(RETURN o hp_acids_empty, RETURN o acids0_mset_empty) \<in> 
   (((\<langle>\<langle>nat_rel\<rangle>option_rel, \<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel)) O
   acids_encoded_hmrel) \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
proof -
  have [intro!]: \<open>Me \<in># {#} \<Longrightarrow> False\<close>for Me
    by auto
  have 1: \<open>(({#}, (\<lambda>_. None, \<lambda>_. None, \<lambda>_. None, \<lambda>_. None, \<lambda>_. None), None), empty_acids0) \<in> acids_encoded_hmrel\<close>
    by (auto simp: acids_encoded_hmrel_def bottom_acids0_def pairing_heaps_rel_def map_fun_rel_def
      ACIDS.hmrel_def encoded_hp_prop_list_conc_def encoded_hp_prop_def empty_outside_def empty_acids0_def
      intro!: relcompI)
  have H: \<open>mset_nodes ya \<noteq> {#}\<close> for ya
    by (cases ya) auto
  show ?thesis
    unfolding uncurry0_def
    by (intro frefI nres_relI)
     (auto simp add: acids_encoded_hmrel_def acids0_mset_empty_def encoded_hp_prop_def ACIDS.hmrel_def encoded_hp_prop_list_conc_def hp_acids_empty_def pairing_heaps_rel_def H
      split: option.splits)
qed


definition acids_mset_empty :: \<open>_\<close> where
  \<open>acids_mset_empty x = (acids_mset x = {#})\<close>

lemma acids_mset_empty_alt_def:
   \<open>acids_mset_empty = (\<lambda>(a, b). acids0_mset_empty a)\<close>
  by (auto intro!: ext simp: acids_mset_empty_def acids0_mset_empty_def
    acids_mset_def)



sepref_def hp_acids_empty_code
  is \<open>RETURN o  hp_acids_empty\<close>
  :: \<open>hp_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding hp_assn_def hp_acids_empty_def atom.fold_option
  by sepref

lemmas [fcomp_norm_unfold] = acids_assn_def[symmetric]

lemmas [sepref_fr_rules] = hp_acids_empty_code.refine[FCOMP hp_acids_empty,
  unfolded hr_comp_assoc[symmetric] acids_assn_def[symmetric] acids_assn2_def[symmetric]]

sepref_def acids_mset_empty_code
  is \<open>RETURN o acids_mset_empty\<close>
  :: \<open>acids_assn2\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding acids_mset_empty_alt_def acids_assn2_def
  by sepref  

sepref_def acids_find_next_undef_impl
  is \<open>uncurry isa_acids_find_next_undef\<close>
  :: \<open>acids_assn2\<^sup>d *\<^sub>a trail_pol_fast_assn\<^sup>k \<rightarrow>\<^sub>a atom.option_assn \<times>\<^sub>a acids_assn2\<close>
  unfolding isa_acids_find_next_undef_def
    atom.fold_option acids_mset_empty_def[symmetric]
  by sepref


(*TODO remove isa_vmtf_unset = vmtf_unset *)
lemma isa_bump_unset_alt_def:
  \<open>isa_bump_unset L vm = (case vm of Tuple4 (hstable) (focused) foc a \<Rightarrow> do {
  hstable \<leftarrow> (if \<not>foc then acids_tl L hstable else RETURN hstable);
  let focused = (if foc then isa_vmtf_unset L focused else focused);
  RETURN (Tuple4 hstable focused foc a)
  })\<close>
  unfolding isa_bump_unset_def isa_vmtf_unset_def vmtf_unset_def[symmetric]
  by (auto intro!: ext split: bump_heuristics_splits)


sepref_register vmtf_unset case_tuple4
sepref_def isa_bump_unset_impl
  is \<open>uncurry (isa_bump_unset)\<close>
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
     (vmtf_heur_array_nth focused i))\<close>
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
  (vmtf_array_fst b))\<close>
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
   access_vmtf_array b i
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

sepref_def vmtf_mark_to_rescore_also_reasons_cl_maybe_fast_code
  is \<open>uncurry5 (isa_vmtf_bump_to_rescore_also_reasons_cl_maybe)\<close>
  :: \<open>[\<lambda>(((((_,_), N), _), _), _). length N \<le> snat64_max]\<^sub>a
   bool1_assn\<^sup>k *\<^sub>a trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a heuristic_bump_assn\<^sup>d \<rightarrow>
  heuristic_bump_assn\<close>
  supply image_image[simp] uminus_\<A>\<^sub>i\<^sub>n_iff[iff] in_diffD[dest] option.splits[split]
    in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n[simp]
  supply [[goals_limit=1]]
  unfolding isa_vmtf_bump_to_rescore_also_reasons_cl_maybe_def PR_CONST_def
  by sepref

experiment begin

export_llvm
  isa_vmtf_bump_to_rescore_also_reasons_cl_impl
  vmtf_mark_to_rescore_also_reasons_fast_code
  isa_bump_rescore_fast_code
  isa_bump_mark_to_rescore_clause_fast_code
  isa_bump_heur_flush_impl
  isa_vmtf_heur_array_nth_code
  vmtf_mark_to_rescore_also_reasons_cl_maybe_fast_code

end

end