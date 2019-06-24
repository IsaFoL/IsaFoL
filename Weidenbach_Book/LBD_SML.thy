theory LBD_SML
  imports LBD Watched_Literals.WB_Word_Assn IsaSAT_Literals_SML
begin

abbreviation lbd_int_assn :: \<open>lbd_ref \<Rightarrow> lbd_assn \<Rightarrow> assn\<close> where
  \<open>lbd_int_assn \<equiv> array_assn bool_assn *a uint32_nat_assn *a uint32_nat_assn\<close>

definition lbd_assn :: \<open>lbd \<Rightarrow> lbd_assn \<Rightarrow> assn\<close> where
  \<open>lbd_assn \<equiv> hr_comp lbd_int_assn lbd_ref\<close>


paragraph \<open>Testing if a level is marked\<close>

sepref_definition level_in_lbd_code
  is \<open>uncurry (RETURN oo level_in_lbd_ref)\<close>
  :: \<open>[\<lambda>(n, (lbd, m)). length lbd \<le> uint32_max]\<^sub>a
       uint32_nat_assn\<^sup>k *\<^sub>a lbd_int_assn\<^sup>k \<rightarrow> bool_assn\<close>
  unfolding level_in_lbd_ref_def short_circuit_conv
  by sepref


lemma level_in_lbd_hnr[sepref_fr_rules]:
  \<open>(uncurry level_in_lbd_code, uncurry (RETURN \<circ>\<circ> level_in_lbd)) \<in> uint32_nat_assn\<^sup>k *\<^sub>a
     lbd_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply lbd_ref_def[simp] uint32_max_def[simp]
  using level_in_lbd_code.refine[FCOMP level_in_lbd_ref_level_in_lbd[unfolded convert_fref]]
  unfolding lbd_assn_def .


paragraph \<open>Marking more levels\<close>

lemma list_grow_array_hnr[sepref_fr_rules]:
  assumes \<open>CONSTRAINT is_pure R\<close>
  shows
    \<open>(uncurry2 (\<lambda>xs u. array_grow xs (nat_of_uint32 u)),
        uncurry2 (RETURN ooo list_grow)) \<in>
    [\<lambda>((xs, n), x). n \<ge> length xs]\<^sub>a (array_assn R)\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>d *\<^sub>a R\<^sup>k \<rightarrow>
       array_assn R\<close>
proof -
  obtain R' where [simp]:
    \<open>R = pure R'\<close>
    \<open>the_pure R = R'\<close>
    using assms by (metis CONSTRAINT_D pure_the_pure)
  have [simp]: \<open>pure R' b bi = \<up>( (bi, b) \<in> R')\<close> for b bi
    by (auto simp: pure_def)
  show ?thesis
    by sepref_to_hoare
       (sep_auto simp: list_grow_def array_assn_def is_array_def
          hr_comp_def list_rel_pres_length list_rel_def list_all2_replicate
         uint32_nat_rel_def br_def
        intro!: list_all2_appendI)
qed

sepref_definition lbd_write_code
  is \<open>uncurry lbd_ref_write\<close>
  :: \<open>lbd_int_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a lbd_int_assn\<close>
  unfolding lbd_ref_write_def
  by sepref

lemma lbd_write_hnr_[sepref_fr_rules]:
  \<open>(uncurry lbd_write_code, uncurry (RETURN \<circ>\<circ> lbd_write))
    \<in> [\<lambda>(lbd, i). i \<le> Suc (uint32_max div 2)]\<^sub>a
      lbd_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> lbd_assn\<close>
  using lbd_write_code.refine[FCOMP lbd_ref_write_lbd_write[unfolded convert_fref]]
  unfolding lbd_assn_def .

sepref_definition lbd_empty_code
  is \<open>lbd_empty_ref\<close>
  :: \<open>lbd_int_assn\<^sup>d  \<rightarrow>\<^sub>a lbd_int_assn\<close>
  unfolding lbd_empty_ref_def
  by sepref

lemma lbd_empty_hnr[sepref_fr_rules]:
  \<open>(lbd_empty_code, lbd_empty) \<in> lbd_assn\<^sup>d \<rightarrow>\<^sub>a lbd_assn\<close>
  using lbd_empty_code.refine[FCOMP lbd_empty_ref_lbd_empty[unfolded convert_fref]]
  unfolding lbd_assn_def .

sepref_definition empty_lbd_code
  is \<open>uncurry0 (RETURN empty_lbd_ref)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a lbd_int_assn\<close>
  unfolding empty_lbd_ref_def array_fold_custom_replicate
  by sepref

lemma empty_lbd_hnr[sepref_fr_rules]:
  \<open>(Sepref_Misc.uncurry0 empty_lbd_code, Sepref_Misc.uncurry0 (RETURN empty_lbd)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a lbd_assn\<close>
  using empty_lbd_code.refine[FCOMP empty_lbd_ref_empty_lbd[unfolded convert_fref uncurry0_def[symmetric]]]
  unfolding lbd_assn_def .

sepref_definition get_LBD_code
  is \<open>get_LBD_ref\<close>
  :: \<open>lbd_int_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding get_LBD_ref_def
  by sepref

lemma get_LBD_hnr[sepref_fr_rules]:
  \<open>(get_LBD_code, get_LBD) \<in> lbd_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  using get_LBD_code.refine[FCOMP get_LBD_ref_get_LBD[unfolded convert_fref],
     unfolded lbd_assn_def[symmetric]] .

end
