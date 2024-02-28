theory First_Order_Superposition_Example
  imports 
    IsaFoR_Term_Copy
              
    First_Order_Superposition
begin

definition select_example  :: "('f, ('v :: infinite)) atom clause \<Rightarrow> ('f, 'v) atom clause" where
  "select_example _ \<equiv> {#}"
                                    
interpretation first_order_superposition_calculus 
  "select_example ::  ('f :: weighted, ('v :: infinite)) atom clause \<Rightarrow> ('f, 'v) atom clause" 
  less_kbo
proof(unfold_locales)
  show "\<And>clause. select_example clause \<subseteq># clause"
    unfolding select_example_def
    by simp
next
  show "\<And>clause literal. literal \<in># select_example clause \<Longrightarrow> is_neg literal"
    unfolding select_example_def
    by simp
next
  show "\<And>clause \<rho>. Term.is_renaming \<rho> \<Longrightarrow> select_example (clause \<cdot> \<rho>) = select_example clause \<cdot> \<rho>"
    unfolding select_example_def
    by simp
next
  show "transp less_kbo"
    by (metis (mono_tags, opaque_lifting) KBO.S_trans less_kbo_def transpI)
next
  show "asymp less_kbo"
    using wfP_imp_asymp wfP_less_kbo by blast
next
  show "wfp_on less_kbo {term. is_ground_term term}"
    by (meson subset_UNIV wfP_less_kbo wfp_on_UNIV wfp_on_subset)
next
  show "totalp_on {term. is_ground_term term} less_kbo"
    by (metis (mono_tags, lifting) CollectD Term.ground_vars_term_empty less_kbo_gtotal totalp_on_def)
next
  show "\<And>context term\<^sub>1 term\<^sub>2. \<lbrakk>less_kbo term\<^sub>1 term\<^sub>2; is_ground_term term\<^sub>1; is_ground_term term\<^sub>2; is_ground_context context\<rbrakk> \<Longrightarrow> less_kbo context\<langle>term\<^sub>1\<rangle> context\<langle>term\<^sub>2\<rangle>"
    using KBO.S_ctxt less_kbo_def by blast
next
  show "\<And>term\<^sub>1 term\<^sub>2 \<theta>. \<lbrakk>is_ground_term (subst_atm_abbrev term\<^sub>1 \<theta>); is_ground_term (subst_atm_abbrev term\<^sub>2 \<theta>); less_kbo term\<^sub>1 term\<^sub>2\<rbrakk> \<Longrightarrow> less_kbo (subst_atm_abbrev term\<^sub>1 \<theta>) (subst_atm_abbrev term\<^sub>2 \<theta>)"
    using less_kbo_subst by blast
next
  show "\<And>term\<^sub>G context\<^sub>G. \<lbrakk>is_ground_term term\<^sub>G; is_ground_context context\<^sub>G; context\<^sub>G \<noteq> \<box>\<rbrakk> \<Longrightarrow> less_kbo term\<^sub>G context\<^sub>G\<langle>term\<^sub>G\<rangle>"
    by (simp add: KBO.S_supt less_kbo_def nectxt_imp_supt_ctxt)
next
  show "infinite (UNIV :: 'v set)"
    by (simp add: infinite_UNIV)
next
  (* TODO: *)
  show "\<And>R. ground_critical_pair_theorem R"
    sorry
qed

end
