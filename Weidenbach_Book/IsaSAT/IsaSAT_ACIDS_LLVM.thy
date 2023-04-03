theory IsaSAT_ACIDS_LLVM
  imports IsaSAT_Literals_LLVM
    IsaSAT_ACIDS
    Pairing_Heaps_Impl_LLVM
    IsaSAT_Trail_LLVM
begin

definition acids_assn2 where
  \<open>acids_assn2 = acids_assn \<times>\<^sub>a uint64_nat_assn\<close>

sepref_register ACIDS.mop_prio_insert_unchanged ACIDS.mop_prio_insert_raw_unchanged
sepref_def mop_prio_insert_raw_unchanged_impl
  is \<open>uncurry ACIDS.mop_prio_insert_raw_unchanged\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a acids_assn\<^sup>d \<rightarrow>\<^sub>a acids_assn\<close>
  unfolding ACIDS.mop_prio_insert_raw_unchanged_def
  by sepref

sepref_def mop_prio_insert_unchanged_impl
  is \<open>uncurry ACIDS.mop_prio_insert_unchanged\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a acids_assn\<^sup>d \<rightarrow>\<^sub>a acids_assn\<close>
  unfolding ACIDS.mop_prio_insert_unchanged_def
  by sepref

sepref_def acids_tl_impl
  is \<open>uncurry acids_tl\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a acids_assn2\<^sup>d \<rightarrow>\<^sub>a acids_assn2\<close>
  unfolding acids_assn2_def acids_tl_def max_def
  by sepref

sepref_def acids_pop_min_impl
  is acids_pop_min
  :: \<open>acids_assn2\<^sup>d \<rightarrow>\<^sub>a atom_assn \<times>\<^sub>a acids_assn2\<close>
  unfolding acids_pop_min_def acids_assn2_def
  by sepref

term ACIDS.mop_prio_insert_maybe

sepref_register ACIDS.mop_prio_insert_maybe
sepref_def mop_prio_insert_maybe_impl
  is \<open>uncurry2 (PR_CONST ACIDS.mop_prio_insert_maybe)\<close>
  ::  \<open>atom_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a acids_assn\<^sup>d \<rightarrow>\<^sub>a acids_assn\<close>
  unfolding ACIDS.mop_prio_insert_maybe_def PR_CONST_def
  by sepref

sepref_def acids_push_literal_impl
  is \<open>uncurry acids_push_literal\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a acids_assn2\<^sup>d \<rightarrow>\<^sub>a acids_assn2\<close>
  unfolding acids_push_literal_def acids_assn2_def
    min_def
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

definition bottom_acids0 :: \<open>_\<close> where
  \<open>bottom_acids0 = ((replicate 0 None, replicate 0 None, replicate 0 None, replicate 0 None, replicate 0 0, None))\<close>

definition bottom_acids :: \<open>_\<close> where
  \<open>bottom_acids = (bottom_acids0, None)\<close>

sepref_def bottom_acids0_impl
  is \<open>uncurry0 (RETURN bottom_acids0)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a hp_assn\<close>
  unfolding bottom_acids0_def
  apply (rewrite at \<open>(_, _, _, _, replicate 0 \<hole> , _)\<close>
    unat_const_fold[where 'a=64])
  unfolding hp_assn_def atom.fold_option array_fold_custom_replicate
    al_fold_custom_empty[where 'l=64]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

definition empty_acids0 where
  \<open>empty_acids0 = ({#}, {#}, \<lambda>_::nat. 0::nat)\<close>


definition empty_acids where
  \<open>empty_acids = (empty_acids0, 0)\<close>

lemma bottom_acids0:
  \<open>(uncurry0 (RETURN bottom_acids0), uncurry0 (RETURN empty_acids0)) \<in> 
   unit_rel \<rightarrow>\<^sub>f \<langle>((\<langle>\<langle>nat_rel\<rangle>option_rel, \<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel)) O
   acids_encoded_hmrel\<rangle>nres_rel\<close>
proof -
  have [intro!]: \<open>Me \<in># {#} \<Longrightarrow> False\<close>for Me
    by auto
  have 1: \<open>(({#}, (\<lambda>_. None, \<lambda>_. None, \<lambda>_. None, \<lambda>_. None, \<lambda>_. None), None), empty_acids0) \<in> acids_encoded_hmrel\<close>
    by (auto simp: acids_encoded_hmrel_def bottom_acids0_def pairing_heaps_rel_def map_fun_rel_def
      ACIDS.hmrel_def encoded_hp_prop_list_conc_def encoded_hp_prop_def empty_outside_def empty_acids0_def
      intro!: relcompI)

  show ?thesis
    unfolding uncurry0_def
    apply (intro frefI nres_relI)
    apply (auto intro!:  relcompI[OF _ 1])
    by(auto simp: acids_encoded_hmrel_def bottom_acids0_def pairing_heaps_rel_def map_fun_rel_def
      ACIDS.hmrel_def encoded_hp_prop_list_conc_def encoded_hp_prop_def empty_outside_def)
qed

lemmas [sepref_fr_rules] =
  bottom_acids0_impl.refine[FCOMP bottom_acids0, unfolded hr_comp_assoc[symmetric] acids_assn_def[symmetric]]

sepref_def empty_acids_code
  is \<open>uncurry0 (RETURN empty_acids)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a acids_assn2\<close>
  unfolding empty_acids_def acids_assn2_def
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

schematic_goal free_acids_assn[sepref_frame_free_rules]: \<open>MK_FREE acids_assn ?a\<close>
  unfolding acids_assn_def hp_assn_def
  by synthesize_free


schematic_goal free_acids_assn2[sepref_frame_free_rules]: \<open>MK_FREE acids_assn2 ?a\<close>
  unfolding acids_assn2_def
  by synthesize_free

sepref_def free_acids
  is \<open>mop_free\<close>
  :: \<open>acids_assn2\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

lemma free_acids_assn2': \<open>MK_FREE acids_assn2 free_acids\<close>
  unfolding free_acids_def
  by (rule back_subst[of \<open>MK_FREE acids_assn2\<close>, OF free_acids_assn2])
    (auto intro!: ext)

end
