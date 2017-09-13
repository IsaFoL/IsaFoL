theory Array_UInt
  imports Array_List_Array WB_Word_Assn
begin


definition nth_aa_u where
  \<open>nth_aa_u x L L' =  nth_aa x (nat_of_uint32 L) L'\<close>

lemma nth_aa_uint_hnr[sepref_fr_rules]:
  assumes \<open>CONSTRAINT is_pure R\<close>
  shows
    \<open>(uncurry2 nth_aa_u, uncurry2 (RETURN ooo nth_rll)) \<in>
       [\<lambda>((x, L), L'). L < length x \<and> L' < length (x ! L)]\<^sub>a
       (arrayO_assn (arl_assn R))\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> R\<close>
  unfolding nth_aa_u_def
  by sepref_to_hoare
    (use assms in \<open>sep_auto simp: uint32_nat_rel_def br_def length_ll_def nth_ll_def
     nth_rll_def\<close>)

definition nth_raa_u where
  \<open>nth_raa_u x L =  nth_raa x (nat_of_uint32 L)\<close>

lemma nth_raa_uint_hnr[sepref_fr_rules]:
  assumes p: \<open>is_pure R\<close>
  shows
    \<open>(uncurry2 nth_raa_u, uncurry2 (RETURN \<circ>\<circ>\<circ> nth_rll)) \<in>
       [\<lambda>((l,i),j). i < length l \<and> j < length_rll l i]\<^sub>a
       (arlO_assn (array_assn R))\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> R\<close>
  unfolding nth_raa_u_def
  supply nth_aa_hnr[to_hnr, sep_heap_rules]
  using assms
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def)

lemma array_replicate_custom_hnr_u[sepref_fr_rules]:
  \<open>CONSTRAINT is_pure A \<Longrightarrow>
   (uncurry (\<lambda>n. Array.new (nat_of_uint32 n)), uncurry (RETURN \<circ>\<circ> op_array_replicate)) \<in>
     uint32_nat_assn\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a array_assn A\<close>
  using array_replicate_custom_hnr[of A]
  unfolding hfref_def
  by (sep_auto simp: uint32_nat_assn_nat_assn_nat_of_uint32)

end