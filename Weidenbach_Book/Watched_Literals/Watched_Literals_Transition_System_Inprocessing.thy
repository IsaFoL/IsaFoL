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
  \<open>cdcl_twl_subresolution (M, N + {#C, C'#}, U, DD, NE, UE, NS, US, {#}, Q)
    (M, N + {#C, E#}, U, DD, NE, UE, add_mset (clause C') NS, US, {#}, Q)\<close>
 if
   \<open>clause C = add_mset L D\<close>
   \<open>clause C' = add_mset (-L) D'\<close>
   \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>  \<open>\<not>tautology (D + D')\<close>
   \<open>clause E = remdups_mset D'\<close>  \<open>size E \<ge> 2\<close> \<open>struct_wf_twl_cls E\<close> \<open>\<forall>L \<in># clause E. undefined_lit M L\<close>|
twl_subresolution_II_unit:
  \<open>cdcl_twl_subresolution (M, N + {#C, C'#}, U, DD, NE, UE, NS, US, {#}, Q)
    (Propagated K {#K#} # M, N + {#C#}, U, DD, add_mset {#K#} NE, UE,
        add_mset (clause C') NS, US, {#}, add_mset (-K) Q)\<close>
 if
   \<open>clause C = add_mset L D\<close>
   \<open>clause C' = add_mset (-L) D'\<close>
   \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>  \<open>\<not>tautology (D + D')\<close>
   \<open>remdups_mset D' = {#K#}\<close> \<open>undefined_lit M K\<close>|

twl_subresolution_LL_nonunit:
  \<open>cdcl_twl_subresolution (M, N, U + {#C, C'#}, DD, NE, UE, NS, US, {#}, Q)
    (M, N, U + {#C, E#}, DD, NE, UE, NS, add_mset (clause C') US, {#}, Q)\<close>
 if
   \<open>clause C = add_mset L D\<close>
   \<open>clause C' = add_mset (-L) D'\<close>
   \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>
   \<open>clause E = remdups_mset D'\<close> \<open>\<not>tautology (D + D')\<close> \<open>size E \<ge> 2\<close>  \<open>\<forall>L \<in># clause E. undefined_lit M L\<close>|
twl_subresolution_LL_unit:
  \<open>cdcl_twl_subresolution (M, N, U + {#C, C'#}, DD, NE, UE, NS, US, {#}, Q)
    (Propagated K {#K#} # M, N, U + {#C#}, DD, NE, add_mset {#K#} UE, NS,
       add_mset (clause C') US, {#}, add_mset (-K) Q)\<close>
 if
   \<open>clause C = add_mset L D\<close>
   \<open>clause C' = add_mset (-L) D'\<close>
   \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>
   \<open>remdups_mset D' = {#K#}\<close> \<open>\<not>tautology (D + D')\<close> \<open>undefined_lit M K\<close>|

twl_subresolution_LI_nonunit:
  \<open>cdcl_twl_subresolution (M, N + {#C#}, U + {#C'#}, DD, NE, UE, NS, US, {#}, Q)
    (M, N + {#C#}, U + {#E#}, DD, NE, UE, NS, add_mset (clause C') US, {#}, Q)\<close>
 if
   \<open>clause C = add_mset L D\<close>
   \<open>clause C' = add_mset (-L) D'\<close>
   \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>
   \<open>clause E = remdups_mset D'\<close>  \<open>\<not>tautology (D + D')\<close> \<open>size E \<ge> 2\<close>\<open>\<forall>L \<in># clause E. undefined_lit M L\<close>|
twl_subresolution_LI_unit:
  \<open>cdcl_twl_subresolution (M, N + {#C#}, U + {#C'#}, DD, NE, UE, NS, US, {#}, Q)
    (Propagated K {#K#} # M, N + {#C#}, U, DD, NE, add_mset {#K#} UE, NS,
      add_mset (clause C') US, {#}, add_mset (-K) Q)\<close>
 if
   \<open>clause C = add_mset L D\<close>
   \<open>clause C' = add_mset (-L) D'\<close>
   \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>
   \<open>remdups_mset D' = {#K#}\<close>  \<open>\<not>tautology (D + D')\<close> \<open>undefined_lit M K\<close>|

twl_subresolution_IL_nonunit:
  \<open>cdcl_twl_subresolution (M, N + {#C'#}, U + {#C#}, DD, NE, UE, NS, US, {#}, Q)
    (M, N + {#E#}, U + {#C#}, DD, NE, UE, add_mset (clause C') NS, add_mset (clause E) US, {#}, Q)\<close>
 if
   \<open>clause C = add_mset L D\<close>
   \<open>clause C' = add_mset (-L) D'\<close>
   \<open>count_decided M = 0\<close> \<open>D \<subseteq># D'\<close>
   \<open>clause E = remdups_mset D'\<close>  \<open>\<not>tautology (D + D')\<close> \<open>size E \<ge> 2\<close> \<open>\<forall>L \<in># clause E. undefined_lit M L\<close> |
twl_subresolution_IL_unit:
  \<open>cdcl_twl_subresolution (M, N + {#C'#}, U + {#C#}, DD, NE, UE, NS, US, {#}, Q)
    (Propagated K {#K#} # M, N, U + {#C#}, DD, add_mset {#K#} NE, UE,
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

lemma
  assumes
    \<open>cdcl_twl_subresolution S T\<close> and \<open>Multiset.Ball (get_clauses S) (distinct_mset o clause)\<close> and
    \<open>get_conflict S = None\<close> and
    subres: \<open>cdcl_subresolution (pstate\<^sub>W_of S) (pstate\<^sub>W_of T)  \<Longrightarrow> thesis\<close> and
    unit: \<open>\<And>S' T'. cdcl_subresolution (pstate\<^sub>W_of S) S' \<Longrightarrow> 
     cdcl_propagate S' (T') \<Longrightarrow> cdcl_flush_unit (T') (pstate\<^sub>W_of T)  \<Longrightarrow> thesis\<close>
  shows thesis
    using assms(1,2,3)
  apply (cases rule: cdcl_twl_subresolution.cases)
  subgoal for C L D C' D' M E N U DD NE UE NS US Q
    apply (rule subres)
    using cdcl_subresolution.intros(1)[of M D D' \<open>clauses N\<close> L \<open>clauses U\<close> DD NE UE NS US]
    by auto
  subgoal for C L D C' D' M E N U DD NE UE NS US Q
    apply (rule unit[of \<open>(M, clauses N + {#clause C, D'#}, clauses U, DD, NE, UE,
      add_mset (clause C') NS, US)\<close>
      \<open>(Propagated E D' # M, clauses N + {#clause C, D'#}, clauses U, DD, NE, UE, add_mset (clause C') NS, US)\<close>])
    subgoal
      by (auto simp: cdcl_subresolution.simps distinct_mset_remdups_mset_id)
    subgoal
      by (auto simp: cdcl_propagate.simps distinct_mset_remdups_mset_id)
    subgoal
      by (auto simp: cdcl_flush_unit.simps distinct_mset_remdups_mset_id)
    done
    supply[[goals_limit=1]]
    subgoal for C L D C' D' M E N U DD NE UE NS US Q
      apply (rule subres)
      using cdcl_subresolution.intros(2)[of M D D' \<open>clauses N\<close> \<open>clauses U\<close> L DD NE UE NS US]
      by auto
    subgoal for C L D C' D' M E N U DD NE UE NS US Q
      apply (rule unit[of \<open>(M, clauses N, clauses U + {#clause C, D'#}, DD, NE, UE,
        NS, add_mset (clause C') US)\<close>
        \<open>(Propagated E D' # M, clauses N, clauses U + {#clause C, D'#}, DD, NE, UE, NS, add_mset (clause C') US)\<close>])
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
    subgoal for C L D C' D' M E N U DD NE UE NS US Q
      apply (rule subres)
      using cdcl_subresolution.intros(3)[of M D D' \<open>clauses N\<close> L \<open>clauses U\<close> DD NE UE NS US]
      by auto
    subgoal for C L D C' D' M E N U DD NE UE NS US Q
      apply (rule unit[of \<open>(M, clauses N + {#clause C#}, clauses U + {#D'#}, DD, NE, UE,
        NS, add_mset (clause C') US)\<close>
        \<open>(Propagated E D' # M, clauses N + {#clause C#}, clauses U + {#D'#}, DD, NE, UE, NS, add_mset (clause C') US)\<close>])
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
    subgoal for C L D C' D' M E N U DD NE UE NS US Q
      apply (rule subres)
      using cdcl_subresolution.intros(4)[of M D' D \<open>clauses N\<close> \<open>-L\<close> \<open>clauses U\<close> DD NE UE NS US]
      by (auto simp: ac_simps)
    subgoal for C L D C' D' M K N U DD NE UE NS US Q
      apply (rule unit[of \<open>(M, clauses N + {#D'#}, clauses U + {#clause C#}, DD, NE, UE,
        add_mset (clause C') NS, add_mset D' US)\<close>
        \<open>(Propagated K D' # M, clauses N + {#D'#}, clauses U + {#clause C#}, DD, NE, UE,
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

end