theory Pairing_Heaps_Impl_LLVM
  imports Pairing_Heap_LLVM.Pairing_Heaps_Impl IsaSAT_Literals_LLVM
begin

type_synonym hp_assn = \<open>32 word ptr \<times> 32 word ptr \<times> 32 word ptr \<times> 32 word ptr \<times> (64 word \<times> 64 word ptr) \<times> 32 word\<close>

definition hp_assn :: \<open>_ \<Rightarrow> hp_assn \<Rightarrow> assn\<close> where
  \<open>hp_assn \<equiv> (IICF_Array.array_assn atom.option_assn \<times>\<^sub>a
    IICF_Array.array_assn atom.option_assn \<times>\<^sub>a
    IICF_Array.array_assn atom.option_assn \<times>\<^sub>a
    IICF_Array.array_assn atom.option_assn \<times>\<^sub>a
    larray64_assn uint64_nat_assn \<times>\<^sub>a atom.option_assn)\<close>

sepref_def mop_hp_read_prev_imp_code
  is \<open>uncurry mop_hp_read_prev_imp\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a hp_assn\<^sup>k \<rightarrow>\<^sub>a atom.option_assn\<close>
  unfolding mop_hp_read_prev_imp_def hp_assn_def
  apply (rewrite at \<open>_! \<hole>\<close> value_of_atm_def[symmetric])
  apply (rewrite in \<open>_ ! \<hole>\<close> annot_unat_snat_upcast[where 'l=\<open>64\<close>])
  by sepref

sepref_def mop_hp_read_nxt_imp_code
  is \<open>uncurry mop_hp_read_nxt_imp\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a hp_assn\<^sup>k \<rightarrow>\<^sub>a atom.option_assn\<close>
  unfolding mop_hp_read_nxt_imp_def hp_assn_def
  apply (rewrite at \<open>_! \<hole>\<close> value_of_atm_def[symmetric])
  apply (rewrite in \<open>_ ! \<hole>\<close> annot_unat_snat_upcast[where 'l=\<open>64\<close>])
  by sepref

sepref_def mop_hp_read_parent_imp_code
  is \<open>uncurry mop_hp_read_parent_imp\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a hp_assn\<^sup>k \<rightarrow>\<^sub>a atom.option_assn\<close>
  unfolding mop_hp_read_parent_imp_def hp_assn_def
  apply (rewrite at \<open>_! \<hole>\<close> value_of_atm_def[symmetric])
  apply (rewrite in \<open>_ ! \<hole>\<close> annot_unat_snat_upcast[where 'l=\<open>64\<close>])
  by sepref

sepref_def mop_hp_read_child_imp_code
  is \<open>uncurry mop_hp_read_child_imp\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a hp_assn\<^sup>k \<rightarrow>\<^sub>a atom.option_assn\<close>
  unfolding mop_hp_read_child_imp_def hp_assn_def
  apply (rewrite at \<open>_! \<hole>\<close> value_of_atm_def[symmetric])
  apply (rewrite in \<open>_ ! \<hole>\<close> annot_unat_snat_upcast[where 'l=\<open>64\<close>])
  by sepref

sepref_def mop_hp_read_score_imp_code
  is \<open>uncurry mop_hp_read_score_imp\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a hp_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  unfolding mop_hp_read_score_imp_def hp_assn_def
  apply (rewrite at \<open>_! \<hole>\<close> value_of_atm_def[symmetric])
  apply (rewrite in \<open>_ ! \<hole>\<close> annot_unat_snat_upcast[where 'l=\<open>64\<close>])
  by sepref

lemma source_node_impl_alt_def:
  \<open>source_node_impl = (\<lambda>(prevs, nxts, parents, children, scores,i). i)\<close>
  by (auto intro!: ext)

sepref_def source_node_impl_code
  is \<open>(RETURN o source_node_impl)\<close>
  :: \<open>hp_assn\<^sup>k \<rightarrow>\<^sub>a atom.option_assn\<close>
  unfolding source_node_impl_alt_def hp_assn_def
  by sepref

lemma update_source_node_impl_alt_def:
  \<open>update_source_node_impl = (\<lambda>i (prevs, nxts, parents, children, scores,_). (prevs, nxts, parents, children, scores, i))\<close>
  by (auto intro!: ext)

sepref_def update_source_node_impl_code
  is \<open>uncurry (RETURN oo update_source_node_impl)\<close>
  :: \<open>atom.option_assn\<^sup>k *\<^sub>a hp_assn\<^sup>d \<rightarrow>\<^sub>a hp_assn\<close>
  unfolding update_source_node_impl_alt_def hp_assn_def
  by sepref

sepref_def mop_hp_update_prev'_imp_code
  is \<open>uncurry2 mop_hp_update_prev'_imp\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a atom.option_assn\<^sup>k *\<^sub>a hp_assn\<^sup>d \<rightarrow>\<^sub>a hp_assn\<close>
  unfolding mop_hp_update_prev'_imp_def hp_assn_def
  apply (rewrite at \<open>_[\<hole>:=_]\<close> value_of_atm_def[symmetric])
  apply (rewrite in \<open>_ [\<hole>:=_]\<close> annot_unat_snat_upcast[where 'l=\<open>64\<close>])
  by sepref

sepref_def mop_hp_update_child'_imp_code
  is \<open>uncurry2 mop_hp_update_child'_imp\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a atom.option_assn\<^sup>k *\<^sub>a hp_assn\<^sup>d \<rightarrow>\<^sub>a hp_assn\<close>
  unfolding mop_hp_update_child'_imp_def hp_assn_def
  apply (rewrite at \<open>_[\<hole>:=_]\<close> value_of_atm_def[symmetric])
  apply (rewrite in \<open>_ [\<hole>:=_]\<close> annot_unat_snat_upcast[where 'l=\<open>64\<close>])
  by sepref

sepref_def mop_hp_update_nxt'_imp_code
  is \<open>uncurry2 mop_hp_update_nxt'_imp\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a atom.option_assn\<^sup>k *\<^sub>a hp_assn\<^sup>d \<rightarrow>\<^sub>a hp_assn\<close>
  unfolding mop_hp_update_nxt'_imp_def hp_assn_def
  apply (rewrite at \<open>_[\<hole>:=_]\<close> value_of_atm_def[symmetric])
  apply (rewrite in \<open>_ [\<hole>:=_]\<close> annot_unat_snat_upcast[where 'l=\<open>64\<close>])
  by sepref

sepref_def mop_hp_update_parent'_imp_code
  is \<open>uncurry2 mop_hp_update_parent'_imp\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a atom.option_assn\<^sup>k *\<^sub>a hp_assn\<^sup>d \<rightarrow>\<^sub>a hp_assn\<close>
  unfolding mop_hp_update_parent'_imp_def hp_assn_def
  apply (rewrite at \<open>_[\<hole>:=_]\<close> value_of_atm_def[symmetric])
  apply (rewrite in \<open>_ [\<hole>:=_]\<close> annot_unat_snat_upcast[where 'l=\<open>64\<close>])
  by sepref

sepref_def mop_hp_set_all_imp_code
  is \<open>uncurry6 mop_hp_set_all_imp\<close>
  ::  \<open>atom_assn\<^sup>k *\<^sub>a atom.option_assn\<^sup>k *\<^sub>a atom.option_assn\<^sup>k *\<^sub>a atom.option_assn\<^sup>k *\<^sub>a atom.option_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a hp_assn\<^sup>d \<rightarrow>\<^sub>a hp_assn\<close>
  unfolding mop_hp_set_all_imp_def hp_assn_def
  apply (rewrite at \<open>_[\<hole>:=_]\<close> value_of_atm_def[symmetric])
  apply (rewrite in \<open>_ [\<hole>:=_]\<close> annot_unat_snat_upcast[where 'l=\<open>64\<close>])
  apply (rewrite at \<open>(_, _[\<hole>:=_], _)\<close> value_of_atm_def[symmetric])
  apply (rewrite in \<open>(_, _ [\<hole>:=_],_)\<close> annot_unat_snat_upcast[where 'l=\<open>64\<close>])
  apply (rewrite at \<open>(_, _, _[\<hole>:=_], _)\<close> value_of_atm_def[symmetric])
  apply (rewrite in \<open>(_, _, _ [\<hole>:=_],_)\<close> annot_unat_snat_upcast[where 'l=\<open>64\<close>])
  apply (rewrite at \<open>(_, _, _, _[\<hole>:=_], _)\<close> value_of_atm_def[symmetric])
  apply (rewrite in \<open>(_, _, _, _ [\<hole>:=_],_)\<close> annot_unat_snat_upcast[where 'l=\<open>64\<close>])
  apply (rewrite at \<open>(_, _, _, _, _[\<hole>:=_], _)\<close> value_of_atm_def[symmetric])
  apply (rewrite in \<open>(_, _, _, _, _ [\<hole>:=_],_)\<close> annot_unat_snat_upcast[where 'l=\<open>64\<close>])
  by sepref

sepref_register mop_hp_set_all_imp
  mop_hp_update_parent'_imp mop_hp_update_nxt'_imp mop_hp_update_child'_imp mop_hp_update_prev'_imp
  mop_hp_read_score_imp mop_hp_read_nxt_imp mop_hp_read_prev_imp mop_hp_read_parent_imp mop_hp_read_child_imp
  maybe_mop_hp_update_prev'_imp maybe_mop_hp_update_nxt'_imp maybe_mop_hp_update_child'_imp maybe_mop_hp_update_parent'_imp


sepref_def mop_hp_insert_impl_code
  is \<open>uncurry2 mop_hp_insert_impl\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a hp_assn\<^sup>d \<rightarrow>\<^sub>a hp_assn\<close>
  unfolding mop_hp_insert_impl_def
    atom.fold_option
  by sepref

sepref_def maybe_mop_hp_update_prev'_imp_code
  is \<open>uncurry2 maybe_mop_hp_update_prev'_imp\<close>
  :: \<open>atom.option_assn\<^sup>k *\<^sub>a atom.option_assn\<^sup>k *\<^sub>a hp_assn\<^sup>d \<rightarrow>\<^sub>a hp_assn\<close>
  unfolding maybe_mop_hp_update_prev'_imp_def
    atom.fold_option
  by sepref

sepref_def maybe_mop_hp_update_nxt'_imp_code
  is \<open>uncurry2 maybe_mop_hp_update_nxt'_imp\<close>
  :: \<open>atom.option_assn\<^sup>k *\<^sub>a atom.option_assn\<^sup>k *\<^sub>a hp_assn\<^sup>d \<rightarrow>\<^sub>a hp_assn\<close>
  unfolding maybe_mop_hp_update_nxt'_imp_def
    atom.fold_option
  by sepref

sepref_def maybe_mop_hp_update_child'_imp_code
  is \<open>uncurry2 maybe_mop_hp_update_child'_imp\<close>
  :: \<open>atom.option_assn\<^sup>k *\<^sub>a atom.option_assn\<^sup>k *\<^sub>a hp_assn\<^sup>d \<rightarrow>\<^sub>a hp_assn\<close>
  unfolding maybe_mop_hp_update_child'_imp_def
    atom.fold_option
  by sepref

sepref_def maybe_mop_hp_update_parent'_imp_code
  is \<open>uncurry2 maybe_mop_hp_update_parent'_imp\<close>
  :: \<open>atom.option_assn\<^sup>k *\<^sub>a atom.option_assn\<^sup>k *\<^sub>a hp_assn\<^sup>d \<rightarrow>\<^sub>a hp_assn\<close>
  unfolding maybe_mop_hp_update_parent'_imp_def
    atom.fold_option
  by sepref

sepref_def mop_hp_link_imp_impl
  is \<open>uncurry2 mop_hp_link_imp\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a atom_assn\<^sup>k *\<^sub>a hp_assn\<^sup>d \<rightarrow>\<^sub>a hp_assn \<times>\<^sub>a atom_assn\<close>
  unfolding mop_hp_link_imp_def
    atom.fold_option
  by sepref

sepref_register mop_hp_link_imp mop_vsids_pass\<^sub>1_imp  mop_vsids_pass\<^sub>2_imp mop_merge_pairs_imp
  mop_vsids_pop_min_impl mop_unroot_hp_tree

sepref_def mop_vsids_pass\<^sub>1_imp_code
  is \<open>uncurry mop_vsids_pass\<^sub>1_imp\<close>
  :: \<open>hp_assn\<^sup>d *\<^sub>a atom_assn\<^sup>k \<rightarrow>\<^sub>a hp_assn \<times>\<^sub>a atom_assn\<close>
  unfolding mop_vsids_pass\<^sub>1_imp_def
    atom.fold_option
  by sepref

sepref_def mop_vsids_pass\<^sub>2_imp_code
  is \<open>uncurry mop_vsids_pass\<^sub>2_imp\<close>
  :: \<open>hp_assn\<^sup>d *\<^sub>a atom_assn\<^sup>k \<rightarrow>\<^sub>a hp_assn\<close>
  unfolding mop_vsids_pass\<^sub>2_imp_def
    atom.fold_option
  by sepref

sepref_def mop_merge_pairs_imp_code
  is \<open>uncurry mop_merge_pairs_imp\<close>
  :: \<open>hp_assn\<^sup>d *\<^sub>a atom_assn\<^sup>k \<rightarrow>\<^sub>a hp_assn\<close>
  unfolding mop_merge_pairs_imp_def
  by sepref

sepref_def mop_vsids_pop_min_impl_code
  is mop_vsids_pop_min_impl
  :: \<open>hp_assn\<^sup>d \<rightarrow>\<^sub>a atom.option_assn \<times>\<^sub>a hp_assn\<close>
  unfolding mop_vsids_pop_min_impl_def
    atom.fold_option
  by sepref


definition mop_source_node_impl where
  "mop_source_node_impl = RETURN o source_node_impl"
sepref_register mop_source_node_impl

sepref_def mop_source_node_impl_code
  is mop_source_node_impl
  :: \<open>hp_assn\<^sup>k \<rightarrow>\<^sub>a atom.option_assn\<close>
  unfolding mop_source_node_impl_def
  by sepref

sepref_register
  "source_node_impl :: (nat,nat)pairing_heaps_imp \<Rightarrow> _"

hide_const (open) NEMonad.ASSERT NEMonad.RETURN NEMonad.SPEC
lemma mop_unroot_hp_tree_alt_def:
  \<open>mop_unroot_hp_tree arr h = do {
    a \<leftarrow> mop_source_node_impl arr;
    nnext \<leftarrow> mop_hp_read_nxt_imp h arr;
    parent \<leftarrow> mop_hp_read_parent_imp h arr;
    prev \<leftarrow> mop_hp_read_prev_imp h arr;
    if prev = None \<and> parent = None \<and> \<not>(a \<noteq> None \<and> the a = h) then RETURN (update_source_node_impl None arr)
    else if a \<noteq> None \<and> the a = h then RETURN (update_source_node_impl None arr)
    else do {
      ASSERT (a \<noteq> None);
      let a' = the a;
      arr \<leftarrow>  maybe_mop_hp_update_child'_imp parent nnext arr;
      arr \<leftarrow>  maybe_mop_hp_update_nxt'_imp prev nnext arr;
      arr \<leftarrow>  maybe_mop_hp_update_prev'_imp nnext prev arr;
      arr \<leftarrow>  maybe_mop_hp_update_parent'_imp nnext parent arr;

      arr \<leftarrow>  mop_hp_update_nxt'_imp h None arr;
      arr \<leftarrow>  mop_hp_update_prev'_imp h None arr;
      arr \<leftarrow>  mop_hp_update_parent'_imp h None arr;

      arr \<leftarrow>  mop_hp_update_nxt'_imp h (Some a') arr;
      arr \<leftarrow>  mop_hp_update_prev'_imp a' (Some h) arr;
      RETURN (update_source_node_impl None arr)
    }
}\<close>
   unfolding mop_unroot_hp_tree_def mop_source_node_impl_def
   by (cases \<open>source_node_impl arr\<close>)
    (auto intro!: bind_cong[OF refl] simp: Let_def)

sepref_def mop_unroot_hp_tree_code
  is \<open>uncurry (mop_unroot_hp_tree :: (nat,nat)pairing_heaps_imp \<Rightarrow> _)\<close>
  :: \<open>hp_assn\<^sup>d *\<^sub>a atom_assn\<^sup>k \<rightarrow>\<^sub>a hp_assn\<close>
  unfolding mop_unroot_hp_tree_alt_def
    atom.fold_option short_circuit_conv
  by sepref

sepref_def mop_hp_update_score_imp_code
  is \<open>uncurry2 mop_hp_update_score_imp\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a hp_assn\<^sup>d \<rightarrow>\<^sub>a hp_assn\<close>
  unfolding mop_hp_update_score_imp_def hp_assn_def
  apply (rewrite at \<open>_[\<hole>:=_]\<close> value_of_atm_def[symmetric])
  apply (rewrite in \<open>_ [\<hole>:=_]\<close> annot_unat_snat_upcast[where 'l=\<open>64\<close>])
  by sepref


lemma Some_eq_not_None_sepref_id_work_around: \<open>Some h = a \<longleftrightarrow> (a \<noteq> None \<and> h = the a)\<close>
  by (cases a) auto

sepref_def mop_rescale_and_reroot_code
  is \<open>uncurry2 mop_rescale_and_reroot\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a hp_assn\<^sup>d \<rightarrow>\<^sub>a hp_assn\<close>
  unfolding mop_rescale_and_reroot_def Some_eq_not_None_sepref_id_work_around
  unfolding atom.fold_option short_circuit_conv
  by sepref

sepref_def mop_hp_is_in_code
  is \<open>uncurry mop_hp_is_in\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a hp_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding mop_hp_is_in_def Some_eq_not_None_sepref_id_work_around
  unfolding atom.fold_option short_circuit_conv
  by sepref

sepref_def mop_vsids_pop_min2_impl_code
  is mop_vsids_pop_min2_impl
  :: \<open>hp_assn\<^sup>d \<rightarrow>\<^sub>a atom_assn \<times>\<^sub>a hp_assn\<close>
  unfolding mop_vsids_pop_min2_impl_def
  unfolding atom.fold_option
  by sepref

lemma mop_hp_insert_impl_spec2:
  \<open>(uncurry2 mop_hp_insert_impl, uncurry2 hp_insert) \<in>
    nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f \<langle>\<langle>nat_rel\<rangle>option_rel,\<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel \<rightarrow>\<^sub>f
    \<langle>\<langle>\<langle>nat_rel\<rangle>option_rel,\<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto intro!: mop_hp_insert_impl_spec[THEN order_trans])

lemma mop_rescale_and_reroot_spec2:
   \<open>(uncurry2 mop_rescale_and_reroot, uncurry2 rescale_and_reroot) \<in>
    nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f  \<langle>\<langle>nat_rel\<rangle>option_rel,\<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel \<rightarrow>\<^sub>f
    \<langle>\<langle>\<langle>nat_rel\<rangle>option_rel,\<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto intro!: mop_rescale_and_reroot_spec[THEN order_trans])

lemma rescale_and_reroot_mop_prio_change_weight2:
  \<open>(uncurry2 rescale_and_reroot, uncurry2 (PR_CONST ACIDS.mop_prio_change_weight)) \<in>
  nat_rel \<times>\<^sub>f  nat_rel \<times>\<^sub>f acids_encoded_hmrel \<rightarrow>\<^sub>f \<langle>acids_encoded_hmrel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
   (auto intro!: rescale_and_reroot_mop_prio_change_weight[THEN order_trans])

lemma mop_hp_is_in_spec2:
  \<open>(uncurry mop_hp_is_in, uncurry hp_is_in) \<in> nat_rel \<times>\<^sub>f \<langle>\<langle>nat_rel\<rangle>option_rel, \<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
   (auto intro!: mop_hp_is_in_spec[THEN order_trans])

lemma vsids_pop_min2_mop_prio_pop_min2:
  \<open>(vsids_pop_min2, PR_CONST ACIDS.mop_prio_pop_min) \<in> acids_encoded_hmrel \<rightarrow>\<^sub>f \<langle>nat_rel \<times>\<^sub>r acids_encoded_hmrel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
   (auto intro!: vsids_pop_min2_mop_prio_pop_min[THEN order_trans])

lemma mop_vsids_pop_min2_impl2:
  shows \<open>(mop_vsids_pop_min2_impl, vsids_pop_min2) \<in>
    \<langle>\<langle>nat_rel\<rangle>option_rel,\<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel \<rightarrow>\<^sub>f
    \<langle>nat_rel \<times>\<^sub>r \<langle>\<langle>nat_rel\<rangle>option_rel,\<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
   (auto intro!: mop_vsids_pop_min2_impl[THEN order_trans])

lemma mop_hp_read_score_imp_mop_hp_read_score2:
  \<open>(uncurry mop_hp_read_score_imp, uncurry mop_hp_read_score) \<in>
  Id \<times>\<^sub>f \<langle>\<langle>nat_rel\<rangle>option_rel,\<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel \<rightarrow>\<^sub>f \<langle>nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
   (auto intro!: mop_hp_read_score_imp_mop_hp_read_score[THEN order_trans])

definition mop_imp_needs_rescaling 
  :: \<open>('a,'b)pairing_heaps_imp \<Rightarrow> nat \<Rightarrow> bool nres\<close> where
  \<open>mop_imp_needs_rescaling = (\<lambda>_ m. 
   RETURN (m > 1152921504606846976))\<close>

sepref_def mop_imp_needs_rescaling_code
  is \<open>uncurry mop_imp_needs_rescaling\<close>
  :: \<open>(hp_assn)\<^sup>k  *\<^sub>a  uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding mop_imp_needs_rescaling_def
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

lemma mop_imp_needs_rescaling_mop_hp_needs_rescaling:
  \<open>(uncurry Pairing_Heaps_Impl_LLVM.mop_imp_needs_rescaling,
   uncurry Pairing_Heaps_Impl.mop_imp_needs_rescaling) \<in> Id \<times>\<^sub>f Id \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel \<close>
  unfolding mop_imp_needs_rescaling_def Pairing_Heaps_Impl.mop_hp_needs_rescaling_def
   Pairing_Heaps_Impl.mop_imp_needs_rescaling_def
  by (auto intro!: nres_relI frefI)


definition mop_hp_needs_rescaling2 :: \<open>(nat multiset \<times> (nat,'c) hp_fun \<times> nat option) \<Rightarrow> nat  \<Rightarrow> bool nres\<close> where
  \<open>mop_hp_needs_rescaling2 = (\<lambda>(\<V>, (prevs, nxts, childs, parents, scores), h) m. SPEC (\<lambda>_. True))\<close>

lemma mop_imp_needs_rescaling_mop_hp_needs_rescaling2:
  \<open>(uncurry Pairing_Heaps_Impl_LLVM.mop_imp_needs_rescaling, uncurry mop_hp_needs_rescaling2)
    \<in> \<langle>\<langle>nat_rel\<rangle>option_rel,\<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel \<times>\<^sub>f nat_rel  \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
  unfolding mop_imp_needs_rescaling_def Pairing_Heaps_Impl.mop_hp_needs_rescaling_def
   mop_hp_needs_rescaling2_def
  by (auto intro!: nres_relI frefI)

lemmas [sepref_fr_rules] =
  mop_imp_needs_rescaling_code.refine[FCOMP mop_imp_needs_rescaling_mop_hp_needs_rescaling2, unfolded hp_assn_def]

sepref_register Pairing_Heaps_Impl.mop_imp_needs_rescaling

sepref_def mop_imp_decreases_weights_pure_rescale_code
  is \<open>uncurry mop_imp_decreases_weights_only\<close>
  :: \<open>uint64_nat_assn\<^sup>k *\<^sub>a (hp_assn)\<^sup>d \<rightarrow>\<^sub>a hp_assn\<close>
  supply [[goals_limit=1]]
  supply [sepref_fr_rules] = mop_imp_needs_rescaling_code.refine[FCOMP mop_imp_needs_rescaling_mop_hp_needs_rescaling]
  unfolding mop_imp_decreases_weights_only_def mop_hp_needs_rescaling_def[symmetric]
    hp_assn_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

thm  mop_imp_needs_rescaling_code.refine[FCOMP mop_imp_needs_rescaling_mop_hp_needs_rescaling]

sepref_def mop_imp_decrease_weights_code
  is \<open>uncurry mop_imp_decreases_weights\<close>
  :: \<open>uint64_nat_assn\<^sup>k *\<^sub>a (hp_assn)\<^sup>d \<rightarrow>\<^sub>a hp_assn\<close>
  supply [[goals_limit=1]]
  supply [sepref_fr_rules] = mop_imp_needs_rescaling_code.refine[FCOMP mop_imp_needs_rescaling_mop_hp_needs_rescaling]
  unfolding mop_imp_decreases_weights_def mop_hp_needs_rescaling_def[symmetric]
  by sepref


definition acids_assn :: \<open>_\<close> where
  \<open>acids_assn = hr_comp (hr_comp hp_assn (\<langle>\<langle>nat_rel\<rangle>option_rel, \<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel))
              acids_encoded_hmrel\<close>

lemmas [fcomp_norm_unfold] = acids_assn_def[symmetric]

sepref_register ACIDS.mop_prio_change_weight ACIDS.mop_prio_insert
  ACIDS.mop_prio_pop_min ACIDS.mop_prio_is_in

lemma mop_prio_change_all_weights_alt_def:
  "ACIDS.mop_prio_change_all_weights \<equiv>  (\<lambda>(\<A>, b, w). RES {(\<A>, b,w) |w. True})"
  unfolding ACIDS.mop_prio_change_all_weights_def bind_RES_RETURN_eq
  by auto


lemma hp_node_hp_rescale[simp]:
  \<open>hp_node v (hp_rescale_weight a xx) =  map_option (hp_rescale_weight a) (hp_node v xx)\<close>
  apply (induction v xx rule: hp_node.induct)
  subgoal
    by (auto split: option.splits simp: hp_node.simps simp del: hp_node_children_simps2 dest: distinct_mset_union)
  subgoal
    by (auto split: option.splits simp: hp_node.simps simp del: hp_node_children_simps2 dest: distinct_mset_union)
  done

lemma [simp]: \<open>map_option node (hp_next x (hp_rescale_weight x1 y)) = map_option node (hp_next x y)\<close>
  apply (induction x y rule: hp_next.induct)
  subgoal
    apply (auto simp: hp_next.simps simp del: )
    by (metis (no_types, lifting) ext hp.exhaust_sel hp.sel(1) hp_next_children_simps(1,2,3) hp_rescale_weight.simps option.map(2) option.map_disc_iff)
  subgoal by auto
  subgoal by auto
  done

lemma node_hp_rescale_weight[simp]: \<open>node (hp_rescale_weight x1 b) = node b\<close>
  by (cases b) auto

lemma [simp]: \<open>map_option node (hp_prev x (hp_rescale_weight x1 y)) = map_option node (hp_prev x y)\<close>
  apply (induction x y rule: hp_prev.induct)
  subgoal
    by (auto simp: hp_prev.simps hp_prev_children.simps split: option.splits simp del: )
  subgoal by auto
  subgoal by auto
  done

lemma hp_child_hp_rescale_None_iff[simp]: \<open>hp_child a (hp_rescale_weight x1 x) = None \<longleftrightarrow>  hp_child a x = None\<close>
  apply (induction x) 
  subgoal for x xs children
    apply (cases children)
     apply (auto simp: hp_child.simps hp_child_children_def
        List.map_filter_def option_hd_def filter_empty_conv split: option.splits)+
    by fastforce
  done

lemma [simp]: \<open>map_option node (hp_child x (hp_rescale_weight x1 y)) = map_option node (hp_child x y)\<close>
  apply (induction x y rule: hp_child.induct)
  subgoal
    by (auto simp: hp_child.simps split: option.splits simp del: )
  subgoal by (auto simp: hp_child.simps split: option.splits)
  done
  
lemma hp_parent_hp_rescale_None_iff[simp]: \<open>hp_parent a (hp_rescale_weight x1 x) = None \<longleftrightarrow>  hp_parent a x = None\<close>
  apply (induction x) 
  subgoal for x xs children
    apply (cases children)
    by (auto simp: hp_parent.simps hp_child_children_def
        List.map_filter_def option_hd_def filter_empty_conv split: option.splits)+
  done

lemma ex_hp_parent_hp_rescale_weight[iff]: \<open>(\<exists>y. hp_parent n (hp_rescale_weight x1 x) = Some y) \<longleftrightarrow> (\<exists>y. hp_parent n (x) = Some y)\<close>
  by (metis hp_parent_hp_rescale_None_iff not_None_eq2)

lemma [simp]: \<open>map_option node (hp_parent x (hp_rescale_weight x1 y)) = map_option node (hp_parent x y)\<close>
  apply (induction x y rule: hp_parent.induct)
  subgoal for n a sc x children
    apply (cases \<open> (filter (\<lambda>x. \<exists>y. hp_parent n x = Some y) children)\<close>)
    apply (auto simp: hp_parent.simps filter_empty_conv filter_map comp_def)
    apply force
    by (metis (no_types, lifting) filter_eq_ConsD hp_parent_hp_rescale_None_iff in_list_in_setD option.map_sel)
  subgoal by (auto simp: hp_parent.simps)
  done

lemma [simp]: \<open>map_option score (map_option (hp_rescale_weight x1) (hp_node x y)) = map_option (\<lambda>x. x div x1) (hp_score x y)\<close>
  apply (induction x y rule: hp_node.induct)
  subgoal by (auto simp:  split: option.splits)
  subgoal by (auto simp: )
  done

lemma score_hp_rescale_weights_hp_node: \<open> v \<in># mset_nodes ya \<Longrightarrow>
       score (the (map_option (hp_rescale_weight x1) (hp_node v ya))) =
      (\<lambda>x. x div x1) ((the (hp_score v ya)))\<close>
  by (metis hp.exhaust_sel hp.sel(2) hp_node_None_notin2 hp_rescale_weight.simps option.map_sel)

(*hp_child, hp_parent, hp_score*)


lemma encoded_hp_prop_list_conc_rescale_weights:
  \<open> encoded_hp_prop_list_conc (ck, (cl, cm, cn, co, cp), cq) (cr, Some y) \<Longrightarrow>
       encoded_hp_prop_list_conc
        (ck, (cl, cm, cn, co, \<lambda>x. map_option (\<lambda>x. x div x1) (cp x)), cq)
        (cr, Some (hp_rescale_weight x1 y))\<close>
  by (auto simp: encoded_hp_prop_list_conc_def encoded_hp_prop_def)

lemma mop_hp_decreases_weights_mop_prio_change_all_weights:
  \<open>(uncurry (mop_hp_decreases_weights), uncurry (ACIDS.mop_prio_change_all_weights')) \<in> [\<lambda>(a, _). a > 0]\<^sub>f
  nat_rel \<times>\<^sub>f acids_encoded_hmrel  \<rightarrow> \<langle>acids_encoded_hmrel\<rangle>nres_rel\<close>
  unfolding  mop_hp_decreases_weights_def mop_prio_change_all_weights_alt_def
     mop_hp_needs_rescaling_def uncurry_def ACIDS.mop_prio_change_all_weights'_def
     mop_hp_decreases_weights_only_def
  apply (intro frefI nres_relI)
  apply refine_vcg
  apply (auto simp: mop_hp_decreases_weights_def ACIDS.mop_prio_change_all_weights_def
     mop_hp_needs_rescaling_def acids_encoded_hmrel_def intro!: RETURN_SPEC_refine)
  apply (rule_tac x= \<open>\<lambda>x. dp x div x1\<close> in exI)
  apply (rule_tac b= \<open>(dl, map_option (hp_rescale_weight x1) dm)\<close> in relcomp.relcompI)
   apply (auto simp: mop_hp_decreases_weights_def ACIDS.mop_prio_change_all_weights_def ACIDS.hmrel_def
     mop_hp_needs_rescaling_def acids_encoded_hmrel_def score_hp_rescale_weights_hp_node
     intro!: RETURN_SPEC_refine
     intro: encoded_hp_prop_list_conc_rescale_weights ACIDS.invar_hp_rescale_weight)
    apply (auto simp: encoded_hp_prop_list_conc_def encoded_hp_prop_def simp add: option.map_sel)
  done


lemmas [sepref_fr_rules] =
  mop_hp_insert_impl_code.refine[FCOMP mop_hp_insert_impl_spec2, FCOMP hp_insert_spec_mop_prio_insert2]
  mop_rescale_and_reroot_code.refine[FCOMP mop_rescale_and_reroot_spec2, FCOMP rescale_and_reroot_mop_prio_change_weight2]
  mop_hp_is_in_code.refine[FCOMP mop_hp_is_in_spec2, FCOMP hp_is_in_mop_prio_is_in2]
  mop_vsids_pop_min2_impl_code.refine[FCOMP mop_vsids_pop_min2_impl2, FCOMP vsids_pop_min2_mop_prio_pop_min2]
  mop_hp_read_score_imp_code.refine[FCOMP mop_hp_read_score_imp_mop_hp_read_score2, FCOMP mop_hp_read_score_mop_prio_old_weight2]



lemma mop_imp_decreases_weights_mop_hp_decreases_weights2:
    \<open>(uncurry mop_imp_decreases_weights, uncurry (mop_hp_decreases_weights)) \<in>
     [\<lambda>_. True]\<^sub>f nat_rel \<times>\<^sub>f (\<langle>\<langle>nat_rel\<rangle>option_rel, \<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel) \<rightarrow>
     \<langle>\<langle>\<langle>nat_rel\<rangle>option_rel, \<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel\<rangle>nres_rel\<close>
  unfolding uncurry_def
  apply (intro nres_relI frefI)
  subgoal for x y
  apply (erule prod_relE)
    apply hypsubst
    unfolding split
    apply (rule mop_imp_decreases_weights_mop_hp_decreases_weights)
      apply auto
    done
  done


lemmas [sepref_fr_rules] =
  mop_imp_decrease_weights_code.refine[FCOMP mop_imp_decreases_weights_mop_hp_decreases_weights2,
    FCOMP mop_hp_decreases_weights_mop_prio_change_all_weights,
    unfolded acids_assn_def[symmetric]]

end
