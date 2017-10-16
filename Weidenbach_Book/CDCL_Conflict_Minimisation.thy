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

inductive can_remove_lit :: \<open>'v literal \<Rightarrow> bool\<close>  where
(* lit_in_conflict:
  \<open>L \<in># D \<Longrightarrow> L \<noteq> L\<^sub>0 \<Longrightarrow> can_remove_lit L\<^sub>0 L\<close> |
lit_entailed:
  \<open>N + U \<Turnstile>pm {#L#} \<Longrightarrow> can_remove_lit L\<^sub>0 L\<close> | *)
recursively_entailed:
  \<open>Propagated (-L) C \<in> set M \<Longrightarrow> (\<forall>K \<in># C - {#-L#}. can_remove_lit K) \<Longrightarrow> can_remove_lit L\<close>

lemma
  assumes \<open>can_remove_lit L\<close> and \<open>distinct_mset C\<close>
  shows \<open>resolution_chain\<^sup>*\<^sup>* C (remdups_mset (C - {#L#}))\<close>
  using assms
proof (induction)
  case (recursively_entailed L E) note in_trail = this(1) and IH = this(2) and dist = this(3)
  show ?case
  proof (cases \<open>L \<in># C\<close>)
    case False
    then show ?thesis
      using dist by (auto simp: distinct_mset_remdups_mset_id)
  next
    case LC: True
    obtain C' where C: \<open>C = add_mset L C'\<close>
      using multi_member_split[OF LC] by auto
    then have C': \<open>C' = remove1_mset L C\<close>
      using LC by auto
    define E' where E': \<open>E' = remove1_mset (-L) E\<close>
    have IH': \<open>\<forall>K\<in>#remove1_mset (-L) E. can_remove_lit K \<and>
       (resolution_chain\<^sup>*\<^sup>* C (remdups_mset (remove1_mset K C)))\<close>
      using IH dist by blast
    have \<open>resolution_chain C (remdups_mset (C' + remove1_mset (-L) E))\<close>
      using resolution_chain.intros[OF in_trail, of C'] unfolding C .
    then show ?thesis
      using IH' dist unfolding E'[symmetric] dist unfolding C
    proof (induction E')
      case empty
      then show ?case by auto
    next
      case (add x E')
      then have 
         \<open>resolution_chain (add_mset L C') (remdups_mset (C' + E')) \<Longrightarrow>
          resolution_chain\<^sup>*\<^sup>* (add_mset L C') (remdups_mset C')\<close> and
         \<open>resolution_chain (add_mset L C') (remdups_mset (add_mset x (C' + E')))\<close> and
         \<open>can_remove_lit x\<close> and
         H: \<open>resolution_chain\<^sup>*\<^sup>* (add_mset L C') (remdups_mset (remove1_mset x (add_mset L C')))\<close> and
         \<open>\<forall>K\<in>#E'.
              can_remove_lit K \<and>
              resolution_chain\<^sup>*\<^sup>* (add_mset L C')
               (remdups_mset (remove1_mset K (add_mset L C')))\<close> and
         [simp]: \<open>L \<notin># C'\<close>
         \<open>distinct_mset C'\<close>
        by (simp_all del: remdups_mset_singleton_sum)

      have \<open>resolution_chain\<^sup>*\<^sup>* (remdups_mset (add_mset x (C' + E'))) (remdups_mset (C' + E'))\<close>
        if \<open>x \<in># C' + E'\<close>
        using that by auto
      have \<open>resolution_chain\<^sup>*\<^sup>* (remdups_mset (add_mset x (C' + E'))) (remdups_mset (C' + E'))\<close>
        if \<open>x \<notin># C' + E'\<close>
        using H that
        apply (induction arbitrary: E' rule: rtranclp_induct)
        subgoal by auto
        subgoal by auto
        using resolution_chain.intros[of x \<open>remdups_mset (C' + E')\<close>]
        apply (auto simp add:)
        sorry
      show ?case
        using H
        apply simp
        sorry
    qed
  qed
qed
end

end