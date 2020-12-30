theory EPAC_Steps_Refine
  imports EPAC_Checker
begin


lemma is_CL_import[sepref_fr_rules]:
  assumes \<open>CONSTRAINT is_pure K\<close>  \<open>CONSTRAINT is_pure V\<close> \<open>CONSTRAINT is_pure R\<close>
  shows
    \<open>(return o pac_res, RETURN o pac_res) \<in> [\<lambda>x. is_Extension x \<or> is_CL x]\<^sub>a
       (pac_step_rel_assn K V R)\<^sup>k \<rightarrow> V\<close>
    \<open>(return o pac_src1, RETURN o pac_src1) \<in> [\<lambda>x. is_Del x]\<^sub>a (pac_step_rel_assn K V R)\<^sup>k \<rightarrow> K\<close>
    \<open>(return o new_id, RETURN o new_id) \<in> [\<lambda>x. is_Extension x \<or> is_CL x]\<^sub>a (pac_step_rel_assn K V R)\<^sup>k \<rightarrow> K\<close>
    \<open>(return o is_CL, RETURN o is_CL) \<in>  (pac_step_rel_assn K V R)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
    \<open>(return o is_Del, RETURN o is_Del) \<in> (pac_step_rel_assn K V R)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
    \<open>(return o new_var, RETURN o new_var) \<in> [\<lambda>x. is_Extension x]\<^sub>a (pac_step_rel_assn K V R)\<^sup>k \<rightarrow> R\<close>
    \<open>(return o is_Extension, RETURN o is_Extension) \<in> (pac_step_rel_assn K V R)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  using assms
  by (sepref_to_hoare; sep_auto simp: pac_step_rel_assn_alt_def is_pure_conv ent_true_drop pure_app_eq
    split: pac_step.splits; fail)+


lemma is_CL_import2[sepref_fr_rules]:
  assumes \<open>CONSTRAINT is_pure K\<close>  \<open>CONSTRAINT is_pure V\<close>
  shows
    \<open>(return o pac_srcs, RETURN o pac_srcs) \<in> [\<lambda>x. is_CL x]\<^sub>a (pac_step_rel_assn K V R)\<^sup>k \<rightarrow>  list_assn (V \<times>\<^sub>a K)\<close>
  using assms
  by (sepref_to_hoare; sep_auto simp: pac_step_rel_assn_alt_def is_pure_conv ent_true_drop pure_app_eq
    assms[simplified] list_assn_pure_conv
    split: pac_step.splits)

lemma is_Mult_lastI:
  \<open>\<not> is_CL b \<Longrightarrow> \<not>is_Extension b \<Longrightarrow> is_Del b\<close>
  by (cases b) auto

end
