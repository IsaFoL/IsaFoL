theory LBD_LLVM
  imports LBD IsaSAT_Literals_LLVM
begin

type_synonym 'a larray64 = \<open>('a,64) larray\<close>
type_synonym lbd_assn = \<open>(32 word) larray64 \<times> 32 word \<times> 32 word\<close>

(*TODO use 32*)
abbreviation lbd_int_assn :: \<open>lbd_ref \<Rightarrow> lbd_assn \<Rightarrow> assn\<close> where
  \<open>lbd_int_assn \<equiv> larray64_assn uint32_nat_assn \<times>\<^sub>a uint32_nat_assn \<times>\<^sub>a uint32_nat_assn\<close>

definition lbd_assn :: \<open>lbd \<Rightarrow> lbd_assn \<Rightarrow> assn\<close> where
  \<open>lbd_assn \<equiv> hr_comp lbd_int_assn lbd_ref\<close>


paragraph \<open>Testing if a level is marked\<close>

sepref_def level_in_lbd_code
  is [] \<open>uncurry (RETURN oo level_in_lbd_ref)\<close>
  :: \<open>uint32_nat_assn\<^sup>k *\<^sub>a lbd_int_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  supply [[goals_limit=1]]
  unfolding level_in_lbd_ref_def short_circuit_conv length_uint32_nat_def
  apply (rewrite in \<open>\<hole> < _\<close> annot_unat_snat_upcast[where 'l=\<open>64\<close>])
  apply (rewrite in \<open>_ ! \<hole>\<close> annot_unat_snat_upcast[where 'l=\<open>64\<close>])
  by sepref


lemma level_in_lbd_hnr[sepref_fr_rules]:
  \<open>(uncurry level_in_lbd_code, uncurry (RETURN \<circ>\<circ> level_in_lbd)) \<in> uint32_nat_assn\<^sup>k *\<^sub>a
     lbd_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  supply lbd_ref_def[simp] unat32_max_def[simp]
  using level_in_lbd_code.refine[FCOMP level_in_lbd_ref_level_in_lbd]
  unfolding lbd_assn_def[symmetric]
  by simp

sepref_def lbd_empty_loop_code
  is \<open>lbd_empty_loop_ref\<close>
  :: \<open>lbd_int_assn\<^sup>d  \<rightarrow>\<^sub>a lbd_int_assn\<close>
  unfolding lbd_empty_loop_ref_def
  supply [[goals_limit=1]]
  apply (rewrite at \<open>_ + \<hole>\<close> snat_const_fold[where 'a=64])+
  apply (rewrite at \<open>(_, \<hole>)\<close> snat_const_fold[where 'a=64])
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref

sepref_def lbd_empty_cheap_code
  is \<open>lbd_empty_cheap_ref\<close>
  :: \<open>[\<lambda>(_, stamp, _). stamp < unat32_max]\<^sub>a lbd_int_assn\<^sup>d  \<rightarrow> lbd_int_assn\<close>
  unfolding lbd_empty_cheap_ref_def
  supply [[goals_limit=1]]
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref

lemma unat32_max_alt_def: "unat32_max = 4294967295"
  by (auto simp: unat32_max_def)
sepref_register lbd_empty_cheap_ref lbd_empty_loop_ref

sepref_def lbd_empty_code
  is \<open>lbd_empty_ref\<close>
  :: \<open>lbd_int_assn\<^sup>d  \<rightarrow>\<^sub>a lbd_int_assn\<close>
  unfolding lbd_empty_ref_def unat32_max_alt_def
  supply [[goals_limit=1]]
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref

lemma lbd_empty_hnr[sepref_fr_rules]:
  \<open>(lbd_empty_code, lbd_empty) \<in> lbd_assn\<^sup>d \<rightarrow>\<^sub>a lbd_assn\<close>
  using lbd_empty_code.refine[FCOMP lbd_empty_ref_lbd_empty]
  unfolding lbd_assn_def .

sepref_def empty_lbd_code
  is [] \<open>uncurry0 (RETURN empty_lbd_ref)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a lbd_int_assn\<close>
  supply [[goals_limit=1]]
  unfolding empty_lbd_ref_def larray_fold_custom_replicate
  apply (rewrite at \<open>op_larray_custom_replicate \<hole> _\<close> snat_const_fold[where 'a=64])
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref

lemma empty_lbd_ref_empty_lbd:
  \<open>(uncurry0 (RETURN empty_lbd_ref), uncurry0 (RETURN empty_lbd)) \<in> unit_rel \<rightarrow>\<^sub>f \<langle>lbd_ref\<rangle>nres_rel\<close>
  using empty_lbd_ref_empty_lbd unfolding uncurry0_def .

lemma empty_lbd_hnr[sepref_fr_rules]:
  \<open>(Sepref_Misc.uncurry0 empty_lbd_code, Sepref_Misc.uncurry0 (RETURN empty_lbd)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a lbd_assn\<close>
using empty_lbd_code.refine[FCOMP empty_lbd_ref_empty_lbd]
  unfolding lbd_assn_def .

sepref_def get_LBD_code
  is [] \<open>get_LBD_ref\<close>
  :: \<open>lbd_int_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding get_LBD_ref_def
  by sepref

lemma get_LBD_hnr[sepref_fr_rules]:
  \<open>(get_LBD_code, get_LBD) \<in> lbd_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  using get_LBD_code.refine[FCOMP get_LBD_ref_get_LBD,
     unfolded lbd_assn_def[symmetric]] .


paragraph \<open>Marking more levels\<close>

lemmas list_grow_alt = list_grow_def[unfolded op_list_grow_init'_def[symmetric]]

sepref_def lbd_write_code
  is [] \<open>uncurry lbd_ref_write\<close>
  :: \<open> [\<lambda>(lbd, i). i \<le> Suc (unat32_max div 2)]\<^sub>a
     lbd_int_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> lbd_int_assn\<close>
  supply [[goals_limit=1]]
  unfolding lbd_ref_write_def length_uint32_nat_def list_grow_alt max_def
    op_list_grow_init'_alt
  apply (rewrite at \<open>_ + \<hole>\<close> unat_const_fold[where 'a=32])
  apply (rewrite at \<open>_ + \<hole>\<close> unat_const_fold[where 'a=32])
  apply (rewrite in \<open>If (\<hole> < _)\<close> annot_unat_snat_upcast[where 'l=64])
  apply (rewrite in \<open>If (_ ! \<hole> = _)\<close> annot_unat_snat_upcast[where 'l=64])
  apply (rewrite in \<open>_[ \<hole> := _]\<close> annot_unat_snat_upcast[where 'l=64])
  apply (rewrite in \<open>op_list_grow_init _ \<hole> _\<close> annot_unat_snat_upcast[where 'l=64])
  apply (rewrite  at \<open>( _[ \<hole> := _], _, _ + _)\<close> annot_unat_snat_upcast[where 'l=64])
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref

lemma lbd_write_hnr_[sepref_fr_rules]:
  \<open>(uncurry lbd_write_code, uncurry (RETURN \<circ>\<circ> lbd_write))
    \<in> [\<lambda>(lbd, i). i \<le> Suc (unat32_max div 2)]\<^sub>a
      lbd_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> lbd_assn\<close>
  using lbd_write_code.refine[FCOMP lbd_ref_write_lbd_write]
  unfolding lbd_assn_def .

schematic_goal mk_free_lbd_assn[sepref_frame_free_rules]: \<open>MK_FREE lbd_assn ?fr\<close>
  unfolding lbd_assn_def
  by synthesize_free

experiment begin

export_llvm
  level_in_lbd_code
  lbd_empty_code
  empty_lbd_code
  get_LBD_code
  lbd_write_code

end

end
