theory IsaSAT_All_LLVM
  imports IsaSAT_LLVM IsaSAT
begin

definition model_assn where
  \<open>model_assn = hr_comp model_stat_assn model_stat_rel\<close>

definition model_bounded_assn where
  \<open>model_bounded_assn =
   hr_comp (bool1_assn \<times>\<^sub>a model_stat_assn\<^sub>0)
   {((b, m), (b', m')). b=b' \<and> (\<not>b \<longrightarrow> (m,m') \<in> model_stat_rel)}\<close>

definition clauses_l_assn where
  \<open>clauses_l_assn = hr_comp (IICF_Array_of_Array_List.aal_assn unat_lit_assn)
    (list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel)\<close>

theorem IsaSAT_full_correctness:
  \<open>(uncurry IsaSAT_code, uncurry (\<lambda>_. model_if_satisfiable_bounded))
     \<in> [\<lambda>(_, a). (\<forall>C\<in>#a. \<forall>L\<in>#C. nat_of_lit L \<le> uint32_max)]\<^sub>a opts_assn\<^sup>d *\<^sub>a clauses_l_assn\<^sup>d \<rightarrow>
      model_bounded_assn\<close>
  using IsaSAT_code.refine[FCOMP IsaSAT_bounded_heur_model_if_sat']
  unfolding model_bounded_assn_def clauses_l_assn_def
  by auto

end