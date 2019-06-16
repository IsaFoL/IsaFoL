theory IsaSAT_Show_SML
  imports
    IsaSAT_Show
    IsaSAT_Setup_SML
begin


definition isasat_information_banner_code :: \<open>_ \<Rightarrow> unit Heap\<close> where
\<open>isasat_information_banner_code _ =
    return (println_string (String.implode (show isasat_banner_content)))\<close>

sepref_register isasat_information_banner
lemma isasat_information_banner_hnr[sepref_fr_rules]:
   \<open>(isasat_information_banner_code, isasat_information_banner) \<in>
   R\<^sup>k \<rightarrow>\<^sub>a id_assn\<close>
  by sepref_to_hoare (sep_auto simp: isasat_information_banner_code_def isasat_information_banner_def)

sepref_register print_current_information


lemma print_current_information_hnr[sepref_fr_rules]:
   \<open>(uncurry (return oo isasat_current_information), uncurry (RETURN oo print_current_information)) \<in>
   stats_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a stats_assn\<close>
  by sepref_to_hoare (sep_auto simp: isasat_current_information_def print_current_information_def
    zero_some_stats_def)

lemma print_current_information_fast_hnr[sepref_fr_rules]:
   \<open>(uncurry (return oo isasat_current_information), uncurry (RETURN oo print_current_information)) \<in>
   stats_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a stats_assn\<close>
  by sepref_to_hoare (sep_auto simp: isasat_current_information_def print_current_information_def
    zero_some_stats_def)


sepref_definition isasat_current_status_code
  is \<open>isasat_current_status\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_unbounded_assn_def isasat_current_status_def
  by sepref

declare isasat_current_status_code.refine[sepref_fr_rules]

sepref_definition isasat_current_status_fast_code
  is \<open>isasat_current_status\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_bounded_assn_def isasat_current_status_def
  by sepref

declare isasat_current_status_fast_code.refine[sepref_fr_rules]

end