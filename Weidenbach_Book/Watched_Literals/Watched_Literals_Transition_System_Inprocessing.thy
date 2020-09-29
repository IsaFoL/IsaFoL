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

lemma propa_confl_cands_enqueued_simps[simp]:
  \<open>propa_confl_cands_enqueued
  (M, N, U, None, add_mset E NE, UE, NS, US, {#}, Q) \<longleftrightarrow>
  propa_confl_cands_enqueued
     (M, N, U, None, NE, UE, NS, US, {#},Q)\<close>
  \<open>propa_confl_cands_enqueued
  (M, N, U, None, NE, add_mset E UE, NS, US, {#}, Q) \<longleftrightarrow>
  propa_confl_cands_enqueued
     (M, N, U, None, NE, UE, NS, US, {#},Q)\<close>
  \<open>propa_confl_cands_enqueued
  (M, N, U, None, NE, UE, add_mset (C') NS, US, {#}, Q) \<longleftrightarrow>
  propa_confl_cands_enqueued
     (M, N, U, None, NE, UE, NS, US, {#}, Q)\<close>
  \<open>propa_confl_cands_enqueued
  (M, N, U, None, NE, UE, NS, add_mset (C') US, {#}, Q) \<longleftrightarrow>
  propa_confl_cands_enqueued
     (M, N, U, None, NE, UE, NS, US, {#}, Q)\<close>
  apply (auto)
  done

lemma propa_confl_cands_enqueuedD:
  \<open>propa_confl_cands_enqueued (M, add_mset C N, U, None, NE, UE, NS, US, {#}, Q) \<Longrightarrow>
  propa_confl_cands_enqueued (M, N, U, None, NE, UE, NS, US, {#}, Q)\<close>
  \<open>propa_confl_cands_enqueued (M, N, add_mset C U, None, NE, UE, NS, US, {#}, Q) \<Longrightarrow>
  propa_confl_cands_enqueued (M, N, U, None, NE, UE, NS, US, {#}, Q)\<close>
  by auto

lemma add_mset_diff_add_mset_If:
  "(add_mset L' C) - add_mset L C'= (if L = L' then C - C' else remove1_mset L C + {#L'#} - C')"
  by (auto simp: multiset_eq_iff)

lemma propa_confl_cands_enqueued_propagate:
  assumes
    \<open>Multiset.Ball (N+U) (struct_wf_twl_cls)\<close> and
    prev: \<open>propa_confl_cands_enqueued (M, N, U, None, NE, UE, NS, US, {#}, Q)\<close> and
    excep: \<open>twl_st_exception_inv (M, N, U, None, NE, UE, NS, US, {#}, Q)\<close> and
    \<open>count_decided M = 0\<close> and
    nd: \<open>no_dup (Propagated L C # M)\<close>
  shows \<open>propa_confl_cands_enqueued (Propagated L C # M, N, U, None, NE, UE, NS, US, {#}, add_mset (-L) Q)\<close>
  unfolding propa_confl_cands_enqueued.simps
proof (intro ballI impI)
  fix Ca La
  assume NU: \<open>Ca\<in>#N + U\<close> and La_Ca: \<open>La \<in># clause Ca\<close> and
    ent: \<open>Propagated L C # M \<Turnstile>as CNot (remove1_mset La (clause Ca))\<close> and
    not_true: \<open>La \<notin> lits_of_l (Propagated L C # M)\<close>
  have [simp]: \<open>get_level M L = 0\<close> for L
    using count_decided_ge_get_level[of M] assms
      by auto
  have dist2: \<open>distinct_mset (clause Ca)\<close> and watched: \<open>size (watched Ca) = 2\<close>
    using assms(1) NU by (cases Ca; auto dest!: multi_member_split)+
  then have dist: \<open>distinct_mset (remove1_mset La (clause Ca))\<close>
    by auto
  show \<open>(\<exists>L'. L' \<in># watched Ca \<and> L' \<in># add_mset (- L) Q) \<or> (\<exists>L. (L, Ca) \<in># {#})\<close>
  proof (rule Cons_entails_CNotE[OF ent dist])
    assume \<open>M \<Turnstile>as CNot (remove1_mset La (clause Ca))\<close> and
      \<open>- lit_of (Propagated L C) \<notin># remove1_mset La (clause Ca)\<close>
    then have \<open>\<exists>L'. L' \<in># watched Ca \<and> L' \<in># Q\<close>
      using prev NU not_true La_Ca
      by (auto simp: dest!: multi_member_split)
    then show ?thesis
      by auto
  next
    assume neg: \<open>M \<Turnstile>as CNot (remove1_mset (- lit_of (Propagated L C)) (remove1_mset La (clause Ca)))\<close> and
      inL: \<open>- lit_of (Propagated L C) \<in># remove1_mset La (clause Ca)\<close>
    with in_diffD[OF this(2)] have [simp]: \<open>L \<noteq> -La\<close> \<open>L \<noteq> La\<close>
      using dist2 not_true by (auto dest!: multi_member_split)

    have \<open>twl_exception_inv (M, N, U, None, NE, UE, NS, US, {#}, Q) Ca\<close>
      using excep NU by auto
    then show \<open>(\<exists>L'. L' \<in># watched Ca \<and> L' \<in># add_mset (- L) Q) \<or> (\<exists>L. (L, Ca) \<in># {#})\<close>
      apply -
      apply (rule ccontr)
      using neg watched not_true nd inL
      apply (cases Ca)
      apply (auto elim!: Cons_entails_CNotE dest!: multi_member_split[of _ N] multi_member_split[of \<open>-L\<close>]
        simp: distinct_mset_remove1_All uminus_lit_swap removeAll_notin has_blit_def add_mset_diff_add_mset_If
        twl_exception_inv.simps size_2_iff all_conj_distrib remove1_mset_add_mset_If)
      apply (auto split: if_splits simp: remove1_mset_add_mset_If Decided_Propagated_in_iff_in_lits_of_l
        dest: no_dup_consistentD uminus_lits_of_l_definedD
        dest!: multi_member_split; fail)+
      done
  qed
qed

lemma propa_confl_cands_enqueued_learn:
  assumes
    prev: \<open>propa_confl_cands_enqueued (M, N, U, None, NE, UE, NS, US, {#}, Q)\<close> and
    \<open>\<forall>L \<in># clause C. undefined_lit M L\<close> \<open>struct_wf_twl_cls C\<close> \<open>no_dup M\<close>
  shows \<open>propa_confl_cands_enqueued (M, add_mset C N, U, None, NE, UE, NS, US, {#}, Q)\<close>
    \<open>propa_confl_cands_enqueued (M, N, add_mset C U, None, NE, UE, NS, US, {#}, Q)\<close>
  using assms
  apply (cases C; force simp: size_2_iff Decided_Propagated_in_iff_in_lits_of_l)+
  done

lemma twl_exception_inv_skip_clause:
  \<open>twl_exception_inv (M, add_mset C' (N), U, None, NE, UE, NS, US, {#}, Q) C \<Longrightarrow>
  twl_exception_inv (M, N, U, None, NE, UE, NS, US, {#}, Q) C\<close>
  \<open>twl_exception_inv (M, N, add_mset C' U, None, NE, UE, NS, US, {#}, Q) C \<Longrightarrow>
  twl_exception_inv (M, N, U, None, NE, UE, NS, US, {#}, Q) C\<close>
  by (cases C) (auto simp: twl_exception_inv.simps)

lemma cdcl_twl_subresolution_propa_confl_cands_enqueued:
  assumes
    \<open>cdcl_twl_subresolution S T\<close>
    \<open>Multiset.Ball (get_clauses S) (struct_wf_twl_cls)\<close> and
    prev: \<open>propa_confl_cands_enqueued S\<close> and
    excep: \<open>twl_st_exception_inv S\<close> and
    nd: \<open>no_dup (get_trail S)\<close>
  shows \<open>propa_confl_cands_enqueued T\<close>
  using assms
    apply (induction rule: cdcl_twl_subresolution.induct)
  subgoal for C L D C' D' M E N U NE UE NS US Q
    by (auto simp del: propa_confl_cands_enqueued.simps
      simp: add_mset_commute[of C _]
      intro!: propa_confl_cands_enqueued_learn(1)[where C=E]
      dest: propa_confl_cands_enqueuedD)
  subgoal for C L D C' D' M K N U NE UE NS US Q
    apply (auto simp del: propa_confl_cands_enqueued.simps
      simp: add_mset_commute[of C _] twl_exception_inv_skip_clause[where C'=C' and N=\<open>add_mset C N\<close>]
      intro: propa_confl_cands_enqueued_learn(1)[where C=C' and N=\<open>add_mset C N\<close>]
      intro!: propa_confl_cands_enqueued_propagate
      dest: propa_confl_cands_enqueuedD
      dest!: multi_member_split[of _ N] multi_member_split[of _ U])
    done
  subgoal for C L D C' D' M E N U NE UE NS US Q
    by (auto simp del: propa_confl_cands_enqueued.simps
      simp: add_mset_commute[of C _]
      intro!: propa_confl_cands_enqueued_learn(2)[where C=E] struct_wf_twl_cls_remdupsI
      dest: propa_confl_cands_enqueuedD)
  subgoal for C L D C' D' M K N U NE UE NS US Q
    apply (auto simp del: propa_confl_cands_enqueued.simps
      simp: add_mset_commute[of C _] twl_exception_inv_skip_clause[where C'=C' and N=\<open>add_mset C N\<close>]
      intro: propa_confl_cands_enqueued_learn(1)[where C=C' and N=\<open>add_mset C N\<close>]
      intro!: propa_confl_cands_enqueued_propagate
      dest: propa_confl_cands_enqueuedD
      dest!: multi_member_split[of _ N] multi_member_split[of _ U])
    apply (simp_all add: twl_exception_inv.simps(1))
    done
  subgoal for C L D C' D' M E N U NE UE NS US Q
    by (auto simp del: propa_confl_cands_enqueued.simps
      simp: add_mset_commute[of C _]
      intro!: propa_confl_cands_enqueued_learn(2)[where C=E] struct_wf_twl_cls_remdupsI
      dest: propa_confl_cands_enqueuedD)
  subgoal for C L D C' D' M K N U NE UE NS US Q
    apply (auto simp del: propa_confl_cands_enqueued.simps
      simp: add_mset_commute[of C _] twl_exception_inv_skip_clause[where C'=C' and N=\<open>add_mset C N\<close>]
      intro: propa_confl_cands_enqueued_learn(1)[where C=C' and N=\<open>add_mset C N\<close>]
      intro!: propa_confl_cands_enqueued_propagate
      dest: propa_confl_cands_enqueuedD
      dest!: multi_member_split[of _ N] multi_member_split[of _ U])
    done
  subgoal for C L D C' D' M E N U NE UE NS US Q
    by (auto simp del: propa_confl_cands_enqueued.simps
      simp: add_mset_commute[of C _]
      intro!: propa_confl_cands_enqueued_learn(1)[where C=E] struct_wf_twl_cls_remdupsI
      dest: propa_confl_cands_enqueuedD)
  subgoal for C L D C' D' M K N U NE UE NS US Q
    apply (auto simp del: propa_confl_cands_enqueued.simps
      simp: add_mset_commute[of C _] twl_exception_inv_skip_clause[where C'=C' and N=\<open>add_mset C N\<close>]
      intro: propa_confl_cands_enqueued_learn(1)[where C=C' and N=\<open>add_mset C N\<close>]
      intro!: propa_confl_cands_enqueued_propagate
      dest: propa_confl_cands_enqueuedD
      dest!: multi_member_split[of _ N] multi_member_split[of _ U])
    apply (simp_all add: twl_exception_inv.simps(1))
    done
  done
(* oops
 *     apply (smt member_add_mset multi_member_split set_mset_union
 *       twl_exception_inv_skip_clause union_mset_add_mset_left)
 * 
 * oops
 * 
 * 
 * lemma cdcl_twl_subresolution_confl_cands_enqueued:
 *   \<open>cdcl_twl_subresolution S T \<Longrightarrow> no_dup (get_trail S) \<Longrightarrow> confl_cands_enqueued S \<Longrightarrow>
 *   propa_cands_enqueued S \<Longrightarrow>
 *   Multiset.Ball (get_clauses S) (distinct_mset o clause) \<Longrightarrow>
 *   confl_cands_enqueued T\<close>
 *   supply [simp] = distinct_mset_remdups_mset_id
 *   apply (induction rule: cdcl_twl_subresolution.induct)
 *   subgoal for C L D C' D' M E N U NE UE NS US Q
 *     by (case_tac E)
 *       (auto dest!: multi_member_split dest: true_annots_CNot_definedD)
 *   subgoal for C L D C' D' M K N U NE UE NS US Q
 *     unfolding confl_cands_enqueued.simps
 *     apply (intro ballI impI conjI)
 *     apply (clarsimp dest!: simp: all_conj_distrib elim!: Cons_entails_CNotE)
 *     apply (elim disjE)
 *     apply (elim Cons_entails_CNotE)
 *     apply (solves auto)[]
 *     apply simp
 *     apply blast+
 *     apply auto[]
 *     apply (elim Cons_entails_CNotE)
 *     apply auto[]
 *     apply simp
 *     apply blast+
 *     apply simp
 *     apply blast+
 *     apply (elim Cons_entails_CNotE)
 *     apply auto[]
 *     apply simp
 *     apply blast+
 *     apply simp
 *     apply blast+
 *     done
 *   subgoal for C L D C' D' M E N U NE UE NS US Q
 *     by (case_tac E)
 *       (auto dest!: multi_member_split dest: true_annots_CNot_definedD)
 *   subgoal for C L D C' D' M K N U NE UE NS US Q
 *     unfolding confl_cands_enqueued.simps
 *     apply (intro ballI impI conjI)
 *     apply (clarsimp dest!: simp: all_conj_distrib elim!: Cons_entails_CNotE)
 *     apply (elim disjE)
 *     apply (elim Cons_entails_CNotE)
 *     apply (solves auto)[]
 *     apply simp
 *     apply blast+
 *     apply auto[]
 *     apply (elim Cons_entails_CNotE)
 *     apply auto[]
 *     apply simp
 *     apply blast+
 *     apply simp
 *     apply blast+
 *     apply (elim Cons_entails_CNotE)
 *     apply auto[]
 *     apply simp
 *     apply blast+
 *     apply simp
 *     apply blast+
 *     done
 *   subgoal for C L D C' D' M E N U NE UE NS US Q
 *     by (case_tac E)
 *       (auto dest!: multi_member_split dest: true_annots_CNot_definedD)
 *   subgoal for C L D C' D' M K N U NE UE NS US Q
 *     unfolding confl_cands_enqueued.simps
 *     apply (intro ballI impI conjI)
 *     apply (clarsimp dest!: simp: all_conj_distrib elim!: Cons_entails_CNotE)
 *     apply (elim disjE)
 *     apply (elim Cons_entails_CNotE)
 *     apply (solves auto)[]
 *     apply simp
 *     apply blast+
 *     apply auto[]
 *     apply (elim Cons_entails_CNotE)
 *     apply auto[]
 *     apply simp
 *     apply blast+
 *     apply simp
 *     apply blast+
 *     apply (elim Cons_entails_CNotE)
 *     apply auto[]
 *     apply simp
 *     apply blast+
 *     apply simp
 *     apply blast+
 *     done
 *   subgoal for C L D C' D' M E N U NE UE NS US Q
 *     by (case_tac E)
 *       (auto dest!: multi_member_split dest: true_annots_CNot_definedD)
 *   subgoal for C L D C' D' M K N U NE UE NS US Q
 *     unfolding confl_cands_enqueued.simps
 *     apply (intro ballI impI conjI)
 *     apply (clarsimp dest!: simp: all_conj_distrib elim!: Cons_entails_CNotE)
 *     apply (elim disjE)
 *     apply (elim Cons_entails_CNotE)
 *     apply (solves auto)[]
 *     apply simp
 *     apply blast+
 *     apply auto[]
 *     apply (elim Cons_entails_CNotE)
 *     apply auto[]
 *     apply simp
 *     apply blast+
 *     apply simp
 *     apply blast+
 *     apply (elim Cons_entails_CNotE)
 *     apply auto[]
 *     apply simp
 *     apply blast+
 *     apply simp
 *     apply blast+
 *     done
 *   done *)

(* lemma cdcl_twl_subresolution_propa_cands_enqueued:
 *   \<open>cdcl_twl_subresolution S T \<Longrightarrow> propa_cands_enqueued S \<Longrightarrow> propa_cands_enqueued T\<close>
 *   by (induction rule: cdcl_twl_subresolution.induct) auto *)

lemma cdcl_twl_subresolution_conflict:
  \<open>cdcl_twl_subresolution S T \<Longrightarrow> get_conflict T = None\<close>
  by (induction rule: cdcl_twl_subresolution.induct) auto

lemma clause_alt_def:
  \<open>clause C =  watched C +  unwatched C\<close>
  by (cases C) auto

lemma cdcl_twl_subresolution_clauses_to_update_inv:
  \<open>cdcl_twl_subresolution S T \<Longrightarrow> no_dup (get_trail S) \<Longrightarrow>
  clauses_to_update_inv S \<Longrightarrow> clauses_to_update_inv T\<close>
  apply (induction rule: cdcl_twl_subresolution.induct)
  subgoal
    by (auto simp: all_conj_distrib clauses_to_update_prop.simps filter_mset_empty_conv
      eq_commute[of _ \<open>remdups_mset _\<close>] clause_alt_def Decided_Propagated_in_iff_in_lits_of_l
      dest!: multi_member_split[of \<open>_ :: _ literal\<close>])
  subgoal
    by (auto simp: all_conj_distrib clauses_to_update_prop.simps filter_mset_empty_conv
      eq_commute[of _ \<open>remdups_mset _\<close>] clause_alt_def Decided_Propagated_in_iff_in_lits_of_l
      add_mset_eq_add_mset dest: no_has_blit_propagate
      dest!: multi_member_split[of \<open>_ :: _ literal\<close>])
  subgoal
    by (auto simp: all_conj_distrib clauses_to_update_prop.simps filter_mset_empty_conv
      eq_commute[of _ \<open>remdups_mset _\<close>] clause_alt_def Decided_Propagated_in_iff_in_lits_of_l
      dest!: multi_member_split[of \<open>_ :: _ literal\<close>])
  subgoal
    by (auto simp: all_conj_distrib clauses_to_update_prop.simps filter_mset_empty_conv
      eq_commute[of _ \<open>remdups_mset _\<close>] clause_alt_def Decided_Propagated_in_iff_in_lits_of_l
      add_mset_eq_add_mset dest: no_has_blit_propagate
      dest!: multi_member_split[of \<open>_ :: _ literal\<close>])
  subgoal
    by (auto simp: all_conj_distrib clauses_to_update_prop.simps filter_mset_empty_conv
      eq_commute[of _ \<open>remdups_mset _\<close>] clause_alt_def Decided_Propagated_in_iff_in_lits_of_l
      dest!: multi_member_split[of \<open>_ :: _ literal\<close>])
  subgoal
    by (auto simp: all_conj_distrib clauses_to_update_prop.simps filter_mset_empty_conv
      eq_commute[of _ \<open>remdups_mset _\<close>] clause_alt_def Decided_Propagated_in_iff_in_lits_of_l
      add_mset_eq_add_mset dest: no_has_blit_propagate
      dest!: multi_member_split[of \<open>_ :: _ literal\<close>])
  subgoal
    by (auto simp: all_conj_distrib clauses_to_update_prop.simps filter_mset_empty_conv
      eq_commute[of _ \<open>remdups_mset _\<close>] clause_alt_def Decided_Propagated_in_iff_in_lits_of_l
      dest!: multi_member_split[of \<open>_ :: _ literal\<close>])
  subgoal
    by (auto simp: all_conj_distrib clauses_to_update_prop.simps filter_mset_empty_conv
      eq_commute[of _ \<open>remdups_mset _\<close>] clause_alt_def Decided_Propagated_in_iff_in_lits_of_l
      add_mset_eq_add_mset dest: no_has_blit_propagate
      dest!: multi_member_split[of \<open>_ :: _ literal\<close>])
  done

lemma cdcl_twl_subresolution_twl_struct_invs:
  assumes \<open>cdcl_twl_subresolution S T\<close>
    \<open>twl_struct_invs S\<close>
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S)\<close>
  shows \<open>twl_struct_invs T\<close>
proof -
  have \<open>Multiset.Ball (get_clauses S) struct_wf_twl_cls\<close> \<open>no_dup (get_trail S)\<close>
    using assms(2) unfolding  twl_struct_invs_def pcdcl_all_struct_invs_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (cases S;  auto simp: twl_st_simps)+
  moreover have \<open>pcdcl_all_struct_invs (pstate\<^sub>W_of T)\<close> \<open>twl_st_inv T\<close>
    using assms cdcl_twl_subresolution_pcdcl_all_struct_invs[of S T]
      cdcl_twl_subresolution_twl_st_inv[of S T]
    unfolding twl_struct_invs_def
    by auto
  then have \<open>Multiset.Ball (get_clauses T) struct_wf_twl_cls\<close> \<open>no_dup (get_trail T)\<close>
    unfolding  twl_struct_invs_def pcdcl_all_struct_invs_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (cases T;  auto simp: twl_st_simps; fail)+
  ultimately show ?thesis
    using cdcl_twl_subresolution_twl_st_inv[of S T]
      cdcl_twl_subresolution_valid_enqueued[of S T]
      cdcl_twl_subresolution_pcdcl_all_struct_invs[of S T]
      cdcl_twl_subresolution_smaller_propa[of S T]
      cdcl_twl_subresolution_twl_st_exception_inv[of S T]
      cdcl_twl_subresolution_dup_enqueued[of S T]
      cdcl_twl_subresolution_distinct_enqueued[of S T]
      (* cdcl_twl_subresolution_confl_cands_enqueued[of S T] *)
      cdcl_twl_subresolution_propa_confl_cands_enqueued[of S T]
      (* cdcl_twl_subresolution_propa_cands_enqueued[of S T] *)
      cdcl_twl_subresolution_propa_confl_cands_enqueued[of S T]
      propa_confl_cands_enqueued_propa_confl_enqueued[of S]
      propa_confl_cands_enqueued_propa_confl_enqueued[of T]
      cdcl_twl_subresolution_conflict[of S T]
      cdcl_twl_subresolution_twl_st_exception_inv[of S T]
      cdcl_twl_subresolution_clauses_to_update_inv[of S T]
      cdcl_twl_subresolution_past_invs[of S T] assms
    unfolding twl_struct_invs_def
    by clarsimp
qed

end