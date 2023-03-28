theory IsaSAT_Mark_LLVM
  imports IsaSAT_Mark
    IsaSAT_Literals_LLVM
begin

type_synonym mark = \<open>bool option\<close>

definition mark_rel_aux :: \<open>(int \<times> mark) set\<close> where
  \<open>mark_rel_aux = {(0, None), (1, Some True), (-1, Some False)}\<close>

definition mark_rel :: \<open>(3 word \<times> bool option) set\<close> where
  \<open>mark_rel = sint_rel' TYPE(3) O mark_rel_aux\<close>

abbreviation mark_assn :: \<open>mark \<Rightarrow> 3 word \<Rightarrow> assn\<close> where
  \<open>mark_assn \<equiv> pure mark_rel\<close>

definition marked_struct_rel :: \<open>(_ \<times> lookup_clause_rel) set\<close> where
  \<open>marked_struct_rel = Id \<times>\<^sub>r \<langle>mark_rel_aux\<rangle>list_rel\<close>

type_synonym mark_assn = \<open>32 word \<times> 3 word ptr\<close>
definition marked_struct_assn :: \<open>lookup_clause_rel \<Rightarrow> mark_assn \<Rightarrow> assn\<close> where
  \<open>marked_struct_assn = uint32_nat_assn \<times>\<^sub>a array_assn (pure mark_rel)\<close>

definition Mark :: \<open>bool \<Rightarrow> bool option\<close> where [simp]: \<open>Mark = Some\<close>
definition NoMark :: \<open>bool option\<close> where [simp]: \<open>NoMark = None\<close>

lemmas mark_defs = Mark_def[symmetric] NoMark_def[symmetric]

lemmas [fcomp_norm_unfold] = mark_rel_aux_def[symmetric] mark_rel_def[symmetric]

sepref_def Mark_impl [llvm_inline]
  is [] \<open>RETURN o (\<lambda>b. if b then 1 else -1)\<close> :: \<open>bool1_assn\<^sup>k \<rightarrow>\<^sub>a sint_assn' TYPE(3)\<close>
  apply (annot_sint_const \<open>TYPE(3)\<close>)
  by sepref

sepref_def NoMark_impl [llvm_inline]
  is [] \<open>uncurry0 (RETURN 0)\<close> :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a sint_assn' TYPE(3)\<close>
  apply (annot_sint_const \<open>TYPE(3)\<close>)
  by sepref

sepref_register Mark NoMark

lemma Mark_rel_aux: \<open>(\<lambda>b. if b then 1 :: int else -1, Mark) \<in> bool_rel \<rightarrow> mark_rel_aux\<close>
  by (auto intro: frefI split: if_splits simp: mark_rel_aux_def)

lemmas [sepref_fr_rules] =
  Mark_impl.refine[FCOMP Mark_rel_aux]

lemma NoMark_rel_aux: \<open>(0, NoMark) \<in> mark_rel_aux\<close>
  by (auto intro: frefI split: if_splits simp: mark_rel_aux_def)

lemmas [sepref_fr_rules] =
  NoMark_impl.refine[FCOMP NoMark_rel_aux]

lemma mark_rel_aux_eq:  \<open>((=), (=)) \<in> mark_rel_aux \<rightarrow> mark_rel_aux \<rightarrow> bool_rel\<close>
  by (auto intro!: frefI simp: mark_rel_aux_def)

sepref_def mark_eq_impl is
  \<open>uncurry (RETURN oo (=))\<close> :: \<open>(sint_assn' TYPE(3))\<^sup>d *\<^sub>a (sint_assn' TYPE(3))\<^sup>d \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding mark_rel_aux_def
  by sepref

lemmas [sepref_fr_rules] = mark_eq_impl.refine[FCOMP mark_rel_aux_eq]

sepref_register \<open>(=) :: mark \<Rightarrow> _ \<Rightarrow> _\<close> lit_is_in_lookup delete_from_lookup_conflict unmark_clause
  add_to_lookup_conflict pre_simplify_clause_lookup

sepref_def lit_is_in_lookup_impl
  is \<open>uncurry lit_is_in_lookup\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a marked_struct_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding lit_is_in_lookup_def mark_defs marked_struct_assn_def
    array_fold_custom_replicate
  apply (annot_all_atm_idxs)
  by sepref

sepref_def delete_from_lookup_conflict_impl
  is \<open>uncurry delete_from_lookup_conflict\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a marked_struct_assn\<^sup>d \<rightarrow>\<^sub>a marked_struct_assn\<close>
  unfolding delete_from_lookup_conflict_def mark_defs marked_struct_assn_def
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  apply (annot_all_atm_idxs)
  by sepref
abbreviation clause_ll_assn where
  \<open>clause_ll_assn \<equiv> al_assn' TYPE(64) unat_lit_assn\<close>

sepref_def unmark_clause_impl
  is \<open>uncurry unmark_clause\<close>
  :: \<open>clause_ll_assn\<^sup>k *\<^sub>a marked_struct_assn\<^sup>d \<rightarrow>\<^sub>a marked_struct_assn\<close>
  unfolding unmark_clause_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_def add_to_lookup_conflict
  is \<open>uncurry (RETURN oo add_to_lookup_conflict)\<close>
  :: \<open>[\<lambda>(L, n, D). atm_of L < length D \<and> n < unat32_max]\<^sub>a
    unat_lit_assn\<^sup>k *\<^sub>a marked_struct_assn\<^sup>d \<rightarrow> marked_struct_assn\<close>
  unfolding mark_defs marked_struct_assn_def add_to_lookup_conflict_def NOTIN_def ISIN_def
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  apply (annot_all_atm_idxs)
  by sepref

sepref_def pre_simplify_clause_lookup_impl
  is \<open>uncurry2 pre_simplify_clause_lookup\<close>
  :: \<open>clause_ll_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>d *\<^sub>a marked_struct_assn\<^sup>d \<rightarrow>\<^sub>a bool1_assn \<times>\<^sub>a clause_ll_assn \<times>\<^sub>a marked_struct_assn\<close>
  unfolding pre_simplify_clause_lookup_def
  supply [[goals_limit=1]]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

end