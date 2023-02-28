theory Pairing_Heaps_Impl_LLVM
  imports Pairing_Heaps_Impl IsaSAT_Literals_LLVM
begin

type_synonym hp_assn = \<open>32 word ptr \<times> 32 word ptr \<times> 32 word ptr \<times> 32 word ptr \<times> 32 word ptr \<times> 32 word\<close>

definition hp_assn :: \<open>_ \<Rightarrow> hp_assn \<Rightarrow> assn\<close> where
  \<open>hp_assn \<equiv> (IICF_Array.array_assn atom.option_assn \<times>\<^sub>a
    IICF_Array.array_assn atom.option_assn \<times>\<^sub>a
    IICF_Array.array_assn atom.option_assn \<times>\<^sub>a
    IICF_Array.array_assn atom.option_assn \<times>\<^sub>a
    IICF_Array.array_assn uint32_nat_assn \<times>\<^sub>a atom.option_assn)\<close>

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
  :: \<open>atom_assn\<^sup>k *\<^sub>a hp_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
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
  ::  \<open>atom_assn\<^sup>k *\<^sub>a atom.option_assn\<^sup>k *\<^sub>a atom.option_assn\<^sup>k *\<^sub>a atom.option_assn\<^sup>k *\<^sub>a atom.option_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a hp_assn\<^sup>d \<rightarrow>\<^sub>a hp_assn\<close>
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


sepref_def mop_hp_insert_impl
  is \<open>uncurry2 mop_hp_insert_impl\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a hp_assn\<^sup>d \<rightarrow>\<^sub>a hp_assn\<close>
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
  :: \<open>atom_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a hp_assn\<^sup>d \<rightarrow>\<^sub>a hp_assn\<close>
  unfolding mop_hp_update_score_imp_def hp_assn_def
  apply (rewrite at \<open>_[\<hole>:=_]\<close> value_of_atm_def[symmetric])
  apply (rewrite in \<open>_ [\<hole>:=_]\<close> annot_unat_snat_upcast[where 'l=\<open>64\<close>])
  by sepref


lemma Some_eq_not_None_sepref_id_work_around: \<open>Some h = a \<longleftrightarrow> (a \<noteq> None \<and> h = the a)\<close>
  by (cases a) auto

sepref_def mop_rescale_and_reroot_code
  is \<open>uncurry2 mop_rescale_and_reroot\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a hp_assn\<^sup>d \<rightarrow>\<^sub>a hp_assn\<close>
  unfolding mop_rescale_and_reroot_def Some_eq_not_None_sepref_id_work_around
  unfolding atom.fold_option short_circuit_conv
  by sepref

end
