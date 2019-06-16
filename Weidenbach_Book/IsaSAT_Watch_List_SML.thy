theory IsaSAT_Watch_List_SML
  imports IsaSAT_Watch_List IsaSAT_Literals_SML
begin

type_synonym watched_wl = \<open>((nat \<times> uint64) array_list) array\<close>
type_synonym watched_wl_uint32 = \<open>((uint64 \<times> uint64) array_list) array\<close>

abbreviation watcher_enc_assn where
  \<open>watcher_enc_assn \<equiv> pure watcher_enc\<close>

abbreviation watcher_assn where
  \<open>watcher_assn \<equiv> nat_assn *a watcher_enc_assn\<close>

abbreviation watcher_fast_assn where
  \<open>watcher_fast_assn \<equiv> uint64_nat_assn *a watcher_enc_assn\<close>

lemma is_marked_binary_code_hnr:
  \<open>(return o is_marked_binary_code, RETURN o is_marked_binary) \<in> watcher_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare
    (sep_auto dest: watcher_enc_extract_bool watcher_enc_extract_bool_True)

lemma
  pair_nat_ann_lit_assn_Decided_Some:
    \<open>pair_nat_ann_lit_assn (Decided x1) (aba, Some x2) = false\<close> and
  pair_nat_ann_lit_assn_Propagated_None:
    \<open>pair_nat_ann_lit_assn (Propagated x21 x22) (aba, None) = false\<close>
  by (auto simp: nat_ann_lit_rel_def pure_def)

lemma blit_of_code_hnr:
  \<open>(return o blit_of_code, RETURN o blit_of) \<in> watcher_assn\<^sup>k \<rightarrow>\<^sub>a unat_lit_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: watcher_enc_extract_blit)

lemma watcher_of_code_hnr[sepref_fr_rules]:
  \<open>(return o watcher_of_code, RETURN o watcher_of) \<in>
    watcher_assn\<^sup>k \<rightarrow>\<^sub>a (nat_assn *a unat_lit_assn *a bool_assn)\<close>
  by sepref_to_hoare
    (sep_auto dest: watcher_enc_extract_bool watcher_enc_extract_bool_True watcher_enc_extract_blit
      simp: watcher_of_code_def)

lemma watcher_of_fast_code_hnr[sepref_fr_rules]:
  \<open>(return o watcher_of_fast_code, RETURN o watcher_of) \<in>
    watcher_fast_assn\<^sup>k \<rightarrow>\<^sub>a (uint64_nat_assn *a unat_lit_assn *a bool_assn)\<close>
  by sepref_to_hoare
    (sep_auto dest: watcher_enc_extract_bool watcher_enc_extract_bool_True watcher_enc_extract_blit
      simp: watcher_of_fast_code_def)

lemma to_watcher_code_hnr[sepref_fr_rules]:
  \<open>(uncurry2 (return ooo to_watcher_code), uncurry2 (RETURN ooo to_watcher)) \<in>
    nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a bool_assn\<^sup>k \<rightarrow>\<^sub>a watcher_assn\<close>
  by sepref_to_hoare
    (sep_auto dest: watcher_enc_extract_bool watcher_enc_extract_bool_True watcher_enc_extract_blit
      simp: to_watcher_code_def watcher_enc_def OR_132_is_sum nat_of_uint64_uint64_of_uint32
       nat_of_uint32_le_uint32_max)

lemma to_watcher_fast_code_hnr[sepref_fr_rules]:
  \<open>(uncurry2 (return ooo to_watcher_fast_code), uncurry2 (RETURN ooo to_watcher_fast)) \<in>
    uint64_nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a bool_assn\<^sup>k \<rightarrow>\<^sub>a watcher_fast_assn\<close>
  by sepref_to_hoare
    (sep_auto dest: watcher_enc_extract_bool watcher_enc_extract_bool_True watcher_enc_extract_blit
      simp: to_watcher_fast_code_def watcher_enc_def OR_132_is_sum nat_of_uint64_uint64_of_uint32
       nat_of_uint32_le_uint32_max)

end