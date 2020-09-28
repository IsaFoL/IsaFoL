theory Watched_Literals_Transition_System_Inprocessing
  imports Watched_Literals_Transition_System
begin
text \<open>
  The subsumption is very similar to the PCDCL case.
\<close>
inductive cdcl_twl_subsumed :: \<open>'v twl_st \<Rightarrow> 'v twl_st \<Rightarrow> bool\<close> where
subsumed_II:
  \<open>cdcl_twl_subsumed (M, N + {#C, C'#}, U, D, NE, UE, NS, US, {#}, Q)
     (M, add_mset C N, U, D, NE, UE, add_mset (clause C') NS, US, {#}, Q)\<close>
  if \<open>clause C \<subseteq># clause C'\<close> |
subsumed_RR:
  \<open>cdcl_twl_subsumed (M, N, U + {#C, C'#}, D, NE, UE, NS, US, {#}, Q)
     (M, N, add_mset C U, D, NE, UE, NS, add_mset (clause C') US, {#}, Q)\<close>
  if \<open>clause C \<subseteq># clause C'\<close> |
subsumed_IR:
  \<open>cdcl_twl_subsumed (M, add_mset C N, add_mset C' U, D, NE, UE, NS, US, {#}, Q)
     (M, add_mset C N, U, D, NE, UE, NS, add_mset (clause C') US, {#}, Q)\<close>
  if \<open>clause C \<subseteq># clause C'\<close>

lemma cdcl_twl_subsumed_cdcl_subsumed:
  \<open>cdcl_twl_subsumed S T \<Longrightarrow> cdcl_subsumed (pstate\<^sub>W_of S) (pstate\<^sub>W_of T)\<close>
  apply (induction rule: cdcl_twl_subsumed.induct)
  subgoal by (auto simp: cdcl_subsumed.simps)
  subgoal by (auto simp: cdcl_subsumed.simps)
  subgoal by (auto simp: cdcl_subsumed.simps)
  done

text \<open>
  The lifting from \<^term>\<open>cdcl_subresolution\<close> is a lot more complicated due to the handling of
  unit and nonunit clauses. Basically, we have to split every rule in two. Hence we don't have a
  one-to-one mapping anymore, but need to use \<^term>\<open>cdcl_flush_unit\<close> or rule of that kind.

  We don't support (yet) generation of the empty clause. This is very tricky because we entirely
  leave the CDCL calculus.
\<close>
inductive cdcl_twl_subresolution :: \<open>'v twl_st \<Rightarrow> 'v twl_st \<Rightarrow> bool\<close> where
twl_subresolution_II_nonunit:
  \<open>cdcl_twl_subresolution (M, N + {#C, C'#}, U, None, NE, UE, NS, US, {#}, Q)
    (M, N + {#C, E#}, U, None, NE, UE, add_mset (clause C') NS, US, {#}, Q)\<close>
 if
   \<open>clause C = add_mset L D\<close>
   \<open>clause C' = add_mset (-L) D'\<close>
   \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>  \<open>\<not>tautology (D + D')\<close>
   \<open>clause E = remdups_mset D'\<close>  \<open>size E \<ge> 2\<close> \<open>struct_wf_twl_cls E\<close> \<open>\<forall>L \<in># clause E. undefined_lit M L\<close>|
twl_subresolution_II_unit:
  \<open>cdcl_twl_subresolution (M, N + {#C, C'#}, U, None, NE, UE, NS, US, {#}, Q)
    (Propagated K {#K#} # M, N + {#C#}, U, None, add_mset {#K#} NE, UE,
        add_mset (clause C') NS, US, {#}, add_mset (-K) Q)\<close>
 if
   \<open>clause C = add_mset L D\<close>
   \<open>clause C' = add_mset (-L) D'\<close>
   \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>  \<open>\<not>tautology (D + D')\<close>
   \<open>remdups_mset D' = {#K#}\<close> \<open>undefined_lit M K\<close>|

twl_subresolution_LL_nonunit:
  \<open>cdcl_twl_subresolution (M, N, U + {#C, C'#}, None, NE, UE, NS, US, {#}, Q)
    (M, N, U + {#C, E#}, None, NE, UE, NS, add_mset (clause C') US, {#}, Q)\<close>
 if
   \<open>clause C = add_mset L D\<close>
   \<open>clause C' = add_mset (-L) D'\<close>
   \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>
   \<open>clause E = remdups_mset D'\<close> \<open>\<not>tautology (D + D')\<close> \<open>size E \<ge> 2\<close>  \<open>\<forall>L \<in># clause E. undefined_lit M L\<close>|
twl_subresolution_LL_unit:
  \<open>cdcl_twl_subresolution (M, N, U + {#C, C'#}, None, NE, UE, NS, US, {#}, Q)
    (Propagated K {#K#} # M, N, U + {#C#}, None, NE, add_mset {#K#} UE, NS,
       add_mset (clause C') US, {#}, add_mset (-K) Q)\<close>
 if
   \<open>clause C = add_mset L D\<close>
   \<open>clause C' = add_mset (-L) D'\<close>
   \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>
   \<open>remdups_mset D' = {#K#}\<close> \<open>\<not>tautology (D + D')\<close> \<open>undefined_lit M K\<close>|

twl_subresolution_LI_nonunit:
  \<open>cdcl_twl_subresolution (M, N + {#C#}, U + {#C'#}, None, NE, UE, NS, US, {#}, Q)
    (M, N + {#C#}, U + {#E#}, None, NE, UE, NS, add_mset (clause C') US, {#}, Q)\<close>
 if
   \<open>clause C = add_mset L D\<close>
   \<open>clause C' = add_mset (-L) D'\<close>
   \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>
   \<open>clause E = remdups_mset D'\<close>  \<open>\<not>tautology (D + D')\<close> \<open>size E \<ge> 2\<close>\<open>\<forall>L \<in># clause E. undefined_lit M L\<close>|
twl_subresolution_LI_unit:
  \<open>cdcl_twl_subresolution (M, N + {#C#}, U + {#C'#}, None, NE, UE, NS, US, {#}, Q)
    (Propagated K {#K#} # M, N + {#C#}, U, None, NE, add_mset {#K#} UE, NS,
      add_mset (clause C') US, {#}, add_mset (-K) Q)\<close>
 if
   \<open>clause C = add_mset L D\<close>
   \<open>clause C' = add_mset (-L) D'\<close>
   \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>
   \<open>remdups_mset D' = {#K#}\<close>  \<open>\<not>tautology (D + D')\<close> \<open>undefined_lit M K\<close>|

twl_subresolution_IL_nonunit:
  \<open>cdcl_twl_subresolution (M, N + {#C'#}, U + {#C#}, None, NE, UE, NS, US, {#}, Q)
    (M, N + {#E#}, U + {#C#}, None, NE, UE, add_mset (clause C') NS, add_mset (clause E) US, {#}, Q)\<close>
 if
   \<open>clause C = add_mset L D\<close>
   \<open>clause C' = add_mset (-L) D'\<close>
   \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>
   \<open>clause E = remdups_mset D'\<close>  \<open>\<not>tautology (D + D')\<close> \<open>size E \<ge> 2\<close> \<open>\<forall>L \<in># clause E. undefined_lit M L\<close> |
twl_subresolution_IL_unit:
  \<open>cdcl_twl_subresolution (M, N + {#C'#}, U + {#C#}, None, NE, UE, NS, US, {#}, Q)
    (Propagated K {#K#} # M, N, U + {#C#}, None, add_mset {#K#} NE, UE,
       add_mset (clause C') NS, add_mset {#K#} US, {#}, add_mset (-K) Q)\<close>
 if
   \<open>clause C = add_mset L D\<close>
   \<open>clause C' = add_mset (-L) D'\<close>
   \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>
   \<open>remdups_mset D' = {#K#}\<close>  \<open>\<not>tautology (D + D')\<close> \<open>undefined_lit M K\<close>

lemma past_invs_count_decided0: \<open>count_decided (get_trail S) = 0 \<Longrightarrow> past_invs S\<close>
  by (cases S) (auto simp: past_invs.simps)

lemma cdcl_twl_subresolution_past_invs: \<open>cdcl_twl_subresolution S T \<Longrightarrow> past_invs T\<close>
  by (induction rule: cdcl_twl_subresolution.induct)
    (auto simp: past_invs_count_decided0)

lemma twl_lazy_update_subresII: \<open>count_decided M = 0 \<Longrightarrow> struct_wf_twl_cls C \<Longrightarrow>
  \<not> twl_is_an_exception (C) (Q) {#} \<Longrightarrow> - K \<notin># watched C \<Longrightarrow>
  twl_lazy_update (M) C \<Longrightarrow>
  twl_lazy_update (Propagated K {#K#} # M) C\<close>
  using count_decided_ge_get_level[of M]
  by (cases C)
   (fastforce simp: get_level_cons_if has_blit_def uminus_lit_swap twl_is_an_exception_def
    dest!: multi_member_split
    elim!: size_mset_SucE)

lemma watched_literals_false_of_max_level_prop_lvl0: \<open>count_decided M = 0 \<Longrightarrow> watched_literals_false_of_max_level (Propagated K {#K#} # M) C\<close>
  using count_decided_ge_get_level[of M]
  by (cases C)
   (fastforce simp: get_level_cons_if has_blit_def uminus_lit_swap twl_is_an_exception_def
    dest!: multi_member_split
    elim!: size_mset_SucE)

lemma watched_literals_false_of_max_level_lvl0: \<open>count_decided M = 0 \<Longrightarrow> watched_literals_false_of_max_level (M) C\<close>
  using count_decided_ge_get_level[of M]
  by (cases C)
   (fastforce simp: get_level_cons_if has_blit_def uminus_lit_swap twl_is_an_exception_def
    dest!: multi_member_split
    elim!: size_mset_SucE)

lemma twl_lazy_update_undefined: \<open>\<forall>L \<in># clause E. undefined_lit M L \<Longrightarrow> twl_lazy_update M E\<close>
  by (cases E)
   (auto simp: has_blit_def Decided_Propagated_in_iff_in_lits_of_l
    dest!: multi_member_split)

lemma struct_wf_twl_cls_remdupsI: \<open>clause E = remdups_mset D' \<Longrightarrow> 2 \<le> size E \<Longrightarrow>  struct_wf_twl_cls E\<close>
  by (cases E) auto

lemma cdcl_twl_subresolution_twl_st_inv:
  \<open>cdcl_twl_subresolution S T \<Longrightarrow> twl_st_inv S \<Longrightarrow> twl_st_inv T\<close>
  by (induction rule: cdcl_twl_subresolution.induct)
    (auto simp: twl_st_inv.simps twl_lazy_update_undefined watched_literals_false_of_max_level_lvl0
    twl_lazy_update_subresII twl_is_an_exception_add_mset_to_queue
    watched_literals_false_of_max_level_prop_lvl0
    intro: struct_wf_twl_cls_remdupsI)

lemma cdcl_twl_subresolution_valid_enqueued:
  \<open>cdcl_twl_subresolution S T \<Longrightarrow> valid_enqueued S \<Longrightarrow> valid_enqueued T\<close>
  by (induction rule: cdcl_twl_subresolution.induct)
    (auto simp: get_level_cons_if)

lemma cdcl_twl_subresolution_decompE:
  assumes
    \<open>cdcl_twl_subresolution S T\<close> and \<open>Multiset.Ball (get_clauses S) (distinct_mset o clause)\<close> and
    subres: \<open>cdcl_subresolution (pstate\<^sub>W_of S) (pstate\<^sub>W_of T)  \<Longrightarrow> thesis\<close> and
    unit: \<open>\<And>S' T'. cdcl_subresolution (pstate\<^sub>W_of S) S' \<Longrightarrow>
     cdcl_propagate S' (T') \<Longrightarrow> cdcl_flush_unit (T') (pstate\<^sub>W_of T)  \<Longrightarrow> thesis\<close>
  shows thesis
    using assms(1,2,3)
  apply (cases rule: cdcl_twl_subresolution.cases)
  subgoal for C L D C' D' M E N U NE UE NS US Q
    apply (rule subres)
    using cdcl_subresolution.intros(1)[of M D D' \<open>clauses N\<close> L \<open>clauses U\<close> None NE UE NS US]
    by auto
  subgoal for C L D C' D' M E N U NE UE NS US Q
    apply (rule unit[of \<open>(M, clauses N + {#clause C, D'#}, clauses U, None, NE, UE,
      add_mset (clause C') NS, US)\<close>
      \<open>(Propagated E D' # M, clauses N + {#clause C, D'#}, clauses U, None, NE, UE, add_mset (clause C') NS, US)\<close>])
    subgoal
      by (auto simp: cdcl_subresolution.simps distinct_mset_remdups_mset_id)
    subgoal
      by (auto simp: cdcl_propagate.simps distinct_mset_remdups_mset_id)
    subgoal
      by (auto simp: cdcl_flush_unit.simps distinct_mset_remdups_mset_id)
    done
    supply[[goals_limit=1]]
    subgoal for C L D C' D' M E N U NE UE NS US Q
      apply (rule subres)
      using cdcl_subresolution.intros(2)[of M D D' \<open>clauses N\<close> \<open>clauses U\<close> L None NE UE NS US]
      by auto
    subgoal for C L D C' D' M E N U NE UE NS US Q
      apply (rule unit[of \<open>(M, clauses N, clauses U + {#clause C, D'#}, None, NE, UE,
        NS, add_mset (clause C') US)\<close>
        \<open>(Propagated E D' # M, clauses N, clauses U + {#clause C, D'#}, None, NE, UE, NS, add_mset (clause C') US)\<close>])
      subgoal
        apply (auto simp: cdcl_subresolution.simps distinct_mset_remdups_mset_id)
        apply (rule_tac x=D in exI)
        apply (rule_tac x=D' in exI)
        apply auto
        done
      subgoal
        by (auto simp: cdcl_propagate.simps distinct_mset_remdups_mset_id)
      subgoal
        by (auto simp: cdcl_flush_unit.simps distinct_mset_remdups_mset_id)
      done
    subgoal for C L D C' D' M E N U NE UE NS US Q
      apply (rule subres)
      using cdcl_subresolution.intros(3)[of M D D' \<open>clauses N\<close> L \<open>clauses U\<close> None NE UE NS US]
      by auto
    subgoal for C L D C' D' M E N U NE UE NS US Q
      apply (rule unit[of \<open>(M, clauses N + {#clause C#}, clauses U + {#D'#}, None, NE, UE,
        NS, add_mset (clause C') US)\<close>
        \<open>(Propagated E D' # M, clauses N + {#clause C#}, clauses U + {#D'#}, None, NE, UE, NS, add_mset (clause C') US)\<close>])
      subgoal
        apply (auto simp: cdcl_subresolution.simps distinct_mset_remdups_mset_id)
        apply (drule_tac x=D in spec)
        apply (drule_tac x=D' in spec)
        apply auto
        done
      subgoal
        by (auto simp: cdcl_propagate.simps distinct_mset_remdups_mset_id)
      subgoal
        by (auto simp: cdcl_flush_unit.simps distinct_mset_remdups_mset_id)
      done
    subgoal for C L D C' D' M E N U NE UE NS US Q
      apply (rule subres)
      using cdcl_subresolution.intros(4)[of M D' D \<open>clauses N\<close> \<open>-L\<close> \<open>clauses U\<close> None NE UE NS US]
      by (auto simp: ac_simps)
    subgoal for C L D C' D' M K N U NE UE NS US Q
      apply (rule unit[of \<open>(M, clauses N + {#D'#}, clauses U + {#clause C#}, None, NE, UE,
        add_mset (clause C') NS, add_mset D' US)\<close>
        \<open>(Propagated K D' # M, clauses N + {#D'#}, clauses U + {#clause C#}, None, NE, UE,
          add_mset (clause C') NS, add_mset D' US)\<close>])
      subgoal
        apply (auto simp: cdcl_subresolution.simps distinct_mset_remdups_mset_id)
        apply (rule_tac x=D' in exI)
        apply (rule_tac x=D in exI)
        apply (rule_tac x= \<open>clauses N\<close> in exI)
        apply (rule_tac x= \<open>-L\<close> in exI)
        apply auto
        done
      subgoal
        by (auto simp: cdcl_propagate.simps distinct_mset_remdups_mset_id)
      subgoal
        by (auto simp: cdcl_flush_unit.simps distinct_mset_remdups_mset_id)
      done
    done

lemma cdcl_twl_subresolution_pcdcl_all_struct_invs:
  \<open>cdcl_twl_subresolution S T \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S) \<Longrightarrow>
  pcdcl_all_struct_invs (pstate\<^sub>W_of S) \<Longrightarrow> pcdcl_all_struct_invs (pstate\<^sub>W_of T)\<close>
  apply (elim cdcl_twl_subresolution_decompE)
  subgoal
    by (cases S)
     (auto simp: pcdcl_all_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
         cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
      dest!: multi_member_split)
  subgoal
    by (drule cdcl_subresolution)
      (simp_all add: rtranclp_pcdcl_all_struct_invs)
  subgoal
    apply (drule pcdcl.intros pcdcl_core.intros)+
    apply (drule cdcl_subresolution)
    apply (auto intro: rtranclp_pcdcl_all_struct_invs)
    using rtranclp_pcdcl_all_struct_invs by blast
  done

lemma cdcl_twl_subresolution_smaller_propa:
  \<open>cdcl_twl_subresolution S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.no_smaller_propa (state\<^sub>W_of T)\<close>
  apply (induction rule: cdcl_twl_subresolution.induct)
  apply (auto simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def)
  apply (case_tac M'; auto; fail)+
  done
lemma cdcl_twl_subresolution_twl_st_exception_inv:
  \<open>cdcl_twl_subresolution S T \<Longrightarrow> no_dup (get_trail S) \<Longrightarrow>
  twl_st_exception_inv S \<Longrightarrow> twl_st_exception_inv T\<close>
  apply (induction rule: cdcl_twl_subresolution.induct)
  subgoal
    unfolding twl_st_exception_inv.simps
    apply (intro ballI)
    apply (rename_tac x; case_tac x)
    apply (auto simp: twl_exception_inv.simps)
    apply (metis Un_iff clause.simps twl_clause.sel(1) twl_clause.sel(2))
    by (metis Un_iff clause.simps twl_clause.sel(1) twl_clause.sel(2))
  subgoal
    unfolding twl_st_exception_inv.simps
    apply (intro ballI)
    apply (rename_tac x; case_tac x)
    apply (auto simp: twl_exception_inv.simps)
    apply (metis Un_iff clause.simps no_has_blit_propagate twl_clause.sel(1) twl_clause.sel(2))+
    done
  subgoal
    unfolding twl_st_exception_inv.simps
    apply (intro ballI)
    apply (rename_tac x; case_tac x)
    apply (auto simp: twl_exception_inv.simps)
    apply (metis Un_iff clause.simps twl_clause.sel(1) twl_clause.sel(2))
    by (metis Un_iff clause.simps twl_clause.sel(1) twl_clause.sel(2))
  subgoal
    unfolding twl_st_exception_inv.simps
    apply (intro ballI)
    apply (rename_tac x; case_tac x)
    apply (auto simp: twl_exception_inv.simps)
    apply (metis Un_iff clause.simps no_has_blit_propagate twl_clause.sel(1) twl_clause.sel(2))+
    done
  subgoal
    unfolding twl_st_exception_inv.simps
    apply (intro ballI)
    apply (rename_tac x; case_tac x)
    apply (auto simp: twl_exception_inv.simps)
    apply (metis Un_iff clause.simps twl_clause.sel(1) twl_clause.sel(2))
    by (metis Un_iff clause.simps twl_clause.sel(1) twl_clause.sel(2))
  subgoal
    unfolding twl_st_exception_inv.simps
    apply (intro ballI)
    apply (rename_tac x; case_tac x)
    apply (auto simp: twl_exception_inv.simps)
    apply (metis Un_iff clause.simps no_has_blit_propagate twl_clause.sel(1) twl_clause.sel(2))+
    done
  subgoal
    unfolding twl_st_exception_inv.simps
    apply (intro ballI)
    apply (rename_tac x; case_tac x)
    apply (auto simp: twl_exception_inv.simps)
    apply (metis Un_iff clause.simps twl_clause.sel(1) twl_clause.sel(2))
    by (metis Un_iff clause.simps twl_clause.sel(1) twl_clause.sel(2))
  subgoal
    unfolding twl_st_exception_inv.simps
    apply (intro ballI)
    apply (rename_tac x; case_tac x)
    apply (auto simp: twl_exception_inv.simps)
    apply (metis Un_iff clause.simps no_has_blit_propagate twl_clause.sel(1) twl_clause.sel(2))+
    done
  done


lemma cdcl_twl_subresolution_dup_enqueued:
  \<open>cdcl_twl_subresolution S T \<Longrightarrow> no_duplicate_queued S \<Longrightarrow> no_duplicate_queued T\<close>
  by (induction rule: cdcl_twl_subresolution.induct) auto

lemma cdcl_twl_subresolution_distinct_enqueued:
  \<open>cdcl_twl_subresolution S T \<Longrightarrow> distinct_queued S \<Longrightarrow> no_duplicate_queued S \<Longrightarrow> distinct_queued T\<close>
  apply (induction rule: cdcl_twl_subresolution.induct)
  unfolding distinct_queued.simps
  by (auto dest:  mset_le_add_mset simp: undefined_notin)

lemma Cons_entails_CNotE:
  assumes \<open>K # M \<Turnstile>as CNot Ca\<close> \<open>distinct_mset Ca\<close> and
    1: \<open>M \<Turnstile>as CNot Ca \<Longrightarrow> -lit_of K \<notin># Ca \<Longrightarrow> thesis\<close> and
    2: \<open>M \<Turnstile>as CNot (remove1_mset (-lit_of K) Ca) \<Longrightarrow> -lit_of K \<in># Ca \<Longrightarrow> thesis\<close>
  shows thesis
  using assms(1,2)
  apply (cases \<open>-lit_of K \<in># Ca\<close>)
  subgoal
    by (rule 2)
     (auto dest!: multi_member_split
      simp: true_annots_true_cls_def_iff_negation_in_model uminus_lit_swap
      add_mset_eq_add_mset)
  subgoal
    by (rule 1)
     (auto dest!: multi_member_split
      simp: true_annots_true_cls_def_iff_negation_in_model uminus_lit_swap
      add_mset_eq_add_mset)
  done

lemma cdcl_twl_subresolution_confl_cands_enqueued:
  \<open>cdcl_twl_subresolution S T \<Longrightarrow> no_dup (get_trail S) \<Longrightarrow> confl_cands_enqueued S \<Longrightarrow>
  propa_cands_enqueued S \<Longrightarrow>
  Multiset.Ball (get_clauses S) (distinct_mset o clause) \<Longrightarrow>
  confl_cands_enqueued T\<close>
  supply [simp] = distinct_mset_remdups_mset_id
  apply (induction rule: cdcl_twl_subresolution.induct)
  subgoal for C L D C' D' M E N U NE UE NS US Q
    by (case_tac E)
      (auto dest!: multi_member_split dest: true_annots_CNot_definedD)
  subgoal for C L D C' D' M K N U NE UE NS US Q
    unfolding confl_cands_enqueued.simps
    apply (intro ballI impI conjI)
    apply (clarsimp dest!: simp: all_conj_distrib elim!: Cons_entails_CNotE)
    apply (elim disjE)
    apply (elim Cons_entails_CNotE)
    apply (solves auto)[]
    apply simp
    apply blast+
    apply auto[]
    apply (elim Cons_entails_CNotE)
    apply auto[]
    apply simp
    apply blast+
    apply simp
    apply blast+
    apply (elim Cons_entails_CNotE)
    apply auto[]
    apply simp
    apply blast+
    apply simp
    apply blast+
    done
  subgoal for C L D C' D' M E N U NE UE NS US Q
    by (case_tac E)
      (auto dest!: multi_member_split dest: true_annots_CNot_definedD)
  subgoal for C L D C' D' M K N U NE UE NS US Q
    unfolding confl_cands_enqueued.simps
    apply (intro ballI impI conjI)
    apply (clarsimp dest!: simp: all_conj_distrib elim!: Cons_entails_CNotE)
    apply (elim disjE)
    apply (elim Cons_entails_CNotE)
    apply (solves auto)[]
    apply simp
    apply blast+
    apply auto[]
    apply (elim Cons_entails_CNotE)
    apply auto[]
    apply simp
    apply blast+
    apply simp
    apply blast+
    apply (elim Cons_entails_CNotE)
    apply auto[]
    apply simp
    apply blast+
    apply simp
    apply blast+
    done
  subgoal for C L D C' D' M E N U NE UE NS US Q
    by (case_tac E)
      (auto dest!: multi_member_split dest: true_annots_CNot_definedD)
  subgoal for C L D C' D' M K N U NE UE NS US Q
    unfolding confl_cands_enqueued.simps
    apply (intro ballI impI conjI)
    apply (clarsimp dest!: simp: all_conj_distrib elim!: Cons_entails_CNotE)
    apply (elim disjE)
    apply (elim Cons_entails_CNotE)
    apply (solves auto)[]
    apply simp
    apply blast+
    apply auto[]
    apply (elim Cons_entails_CNotE)
    apply auto[]
    apply simp
    apply blast+
    apply simp
    apply blast+
    apply (elim Cons_entails_CNotE)
    apply auto[]
    apply simp
    apply blast+
    apply simp
    apply blast+
    done
  subgoal for C L D C' D' M E N U NE UE NS US Q
    by (case_tac E)
      (auto dest!: multi_member_split dest: true_annots_CNot_definedD)
  subgoal for C L D C' D' M K N U NE UE NS US Q
    unfolding confl_cands_enqueued.simps
    apply (intro ballI impI conjI)
    apply (clarsimp dest!: simp: all_conj_distrib elim!: Cons_entails_CNotE)
    apply (elim disjE)
    apply (elim Cons_entails_CNotE)
    apply (solves auto)[]
    apply simp
    apply blast+
    apply auto[]
    apply (elim Cons_entails_CNotE)
    apply auto[]
    apply simp
    apply blast+
    apply simp
    apply blast+
    apply (elim Cons_entails_CNotE)
    apply auto[]
    apply simp
    apply blast+
    apply simp
    apply blast+
    done
  done

(* lemma cdcl_twl_subresolution_propa_cands_enqueued:
 *   \<open>cdcl_twl_subresolution S T \<Longrightarrow> propa_cands_enqueued S \<Longrightarrow> propa_cands_enqueued T\<close>
 *   by (induction rule: cdcl_twl_subresolution.induct) auto *)

lemma \<open>cdcl_twl_subresolution S T \<Longrightarrow> twl_struct_invs S \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S) \<Longrightarrow>
  twl_struct_invs T\<close>
  using cdcl_twl_subresolution_twl_st_inv[of S T]
    cdcl_twl_subresolution_valid_enqueued[of S T]
    cdcl_twl_subresolution_pcdcl_all_struct_invs[of S T]
    cdcl_twl_subresolution_smaller_propa[of S T]
    cdcl_twl_subresolution_twl_st_exception_inv[of S T]
    cdcl_twl_subresolution_dup_enqueued[of S T]
    cdcl_twl_subresolution_distinct_enqueued[of S T]
    cdcl_twl_subresolution_confl_cands_enqueued[of S T]
    (* cdcl_twl_subresolution_propa_cands_enqueued[of S T] *)
    cdcl_twl_subresolution_confl_cands_enqueued[of S T]
  unfolding twl_struct_invs_def
  apply clarsimp
    oops

end