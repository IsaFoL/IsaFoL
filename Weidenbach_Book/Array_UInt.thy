theory Array_UInt
  imports Array_List_Array WB_Word_Assn
begin

lemma nth_aa_uint_hnr[sepref_fr_rules]:
  assumes p: \<open>is_pure R\<close>
  shows
    \<open>(uncurry2 (\<lambda>xs i. nth_aa xs (nat_of_uint32 i)), uncurry2 (RETURN \<circ>\<circ>\<circ> nth_ll)) \<in>
       [\<lambda>((l,i),j). i < length l \<and> j < length_ll l i]\<^sub>a
       (arrayO_assn (arl_assn R))\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> R\<close>
  supply nth_aa_hnr[to_hnr, sep_heap_rules]
  using assms
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def)

lemma nth_raa_uint_hnr[sepref_fr_rules]:
  assumes p: \<open>is_pure R\<close>
  shows
    \<open>(uncurry2 (\<lambda>xs i. nth_raa xs (nat_of_uint32 i)), uncurry2 (RETURN \<circ>\<circ>\<circ> nth_rll)) \<in>
       [\<lambda>((l,i),j). i < length l \<and> j < length_rll l i]\<^sub>a
       (arlO_assn (array_assn R))\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> R\<close>
  supply nth_aa_hnr[to_hnr, sep_heap_rules]
  using assms
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def)

end