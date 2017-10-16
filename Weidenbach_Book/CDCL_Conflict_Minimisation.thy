theory CDCL_Conflict_Minimisation
  imports CDCL.CDCL_W_Abstract_State "../lib/Explorer"
begin

declare cdcl\<^sub>W_restart_mset_state[simp]

context
  fixes M :: \<open>('v, 'v clause) ann_lits\<close> and N U :: \<open>'v clauses\<close> and
    D :: \<open>'v clause\<close>
  assumes invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M, N, U, Some D)\<close>
begin

inductive resolution_chain :: \<open>'v clause \<Rightarrow> 'v clause \<Rightarrow> bool\<close> where
  \<open>Propagated (-L) C \<in> set M \<Longrightarrow> resolution_chain (add_mset L E) (remdups_mset (E + (C - {#-L#})))\<close>

lemma resolution_chain_resolve:
  assumes \<open>resolution_chain C E\<close> and  \<open>set_mset N \<union> set_mset U \<Turnstile>p C\<close>
  shows \<open>set_mset N \<union> set_mset U \<Turnstile>p E\<close>
  using assms
proof (induction)
  case (1 L C) note in_trail = this(1) and entailed = this(2)
  have \<open>a @ Propagated L mark # b = trail (M, N, U, Some D) \<longrightarrow>
       b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close> for L mark a b
    using invs
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    by fast
  then have [simp]: \<open>-L \<in># C\<close>
    by (metis in_trail split_list trail.simps)
  
  have \<open>set (get_all_mark_of_propagated (trail (M, N, U, Some D)))
    \<subseteq> set_mset (cdcl\<^sub>W_restart_mset.clauses (M, N, U, Some D))\<close>
    using invs
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
    by fast
  then have \<open>C \<in># N + U\<close>
    using in_trail cdcl\<^sub>W_restart_mset.in_get_all_mark_of_propagated_in_trail[of C M]
    by (auto simp: clauses_def)
  then have NU_C: \<open>N + U \<Turnstile>pm add_mset (- L) (remove1_mset (-L) C)\<close>
    by auto
  show ?case
    unfolding true_clss_cls_remdups_mset
    apply (rule true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or[of _ \<open>-L\<close>])
    using  entailed NU_C by simp_all
qed

lemma rtranclp_resolution_chain_resolve:
  assumes \<open>resolution_chain\<^sup>*\<^sup>* C E\<close> and  \<open>N + U \<Turnstile>pm C\<close>
  shows \<open>N + U \<Turnstile>pm E\<close>
  using assms by (induction) (auto dest!: resolution_chain_resolve)

inductive conflict_minimization :: \<open>'v clause \<Rightarrow> 'v clause \<Rightarrow> bool\<close> where
  \<open>resolution_chain C D \<Longrightarrow> D \<subseteq># C \<Longrightarrow> conflict_minimization C D\<close>


end

end