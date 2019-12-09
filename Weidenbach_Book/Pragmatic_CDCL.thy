theory Pragmatic_CDCL
  imports CDCL.CDCL_W_Restart CDCL.CDCL_W_Abstract_State
begin


chapter \<open>Pragmatic CDCL\<close>

text \<open>

The idea of this calculus is to sit between the nice and abstract
CDCL calculus and the first step towards the implementation,
TWL. Therefore, the calculus will contain a few things that cannot
be easily expressed in CDCL, but are important in a SAT solver:

  \<^enum> To make it possible to express subsumption, we split our clauses
  in two parts: the subsumed clauses and the non-subsumed clauses. The
  CDCL calculus sees both of them together, but we only need the
  latter.

  \<^enum> We also have components for special clauses that contains a
  literal set at level 0. We need that component anyway for clauses of
  length 1 when expressing two watched literals.

  \<^enum> Adding clauses: if an init clause is subsumed by a learned
  clauses, it is better to add that clauses to the set of init clauses
  (Armin Biere calls these clauses irredundant).


  The second idea was already included in the formalization of TWL
because of (i) clauses of length one do not have two literals to
watch; (ii) moving them away makes garbage collecting easier, because
no reason at level 0 on the trail is included in the set of clauses.

We also started to implement the ideas one and three, but we realised
while thinking about restarts that separate rules are needed to avoid
a lot of copy-and-paste. It was also not clear how to add subsumption
detection on the fly without restart (like done right after a
backtrack in CaDiCaL or in SPASS).


Termination still comes from the CDCL calculus: We do not want to
apply the other rules exhaustively.

\<close>
type_synonym 'v prag_st =
  \<open>('v, 'v clause) ann_lits \<times> 'v clauses \<times> 'v clauses \<times>
    'v clause option \<times> 'v clauses \<times> 'v clauses \<times> 'v clauses \<times> 'v clauses\<close>


fun state\<^sub>W_of :: \<open>'v prag_st \<Rightarrow> 'v cdcl\<^sub>W_restart_mset\<close> where
\<open>state\<^sub>W_of (M, N, U, C, NE, UE, NS, US) =
  (M, N + NE + NS, U + UE + US,  C)\<close>

section \<open>Conversion\<close>


fun pget_trail :: \<open>'v prag_st \<Rightarrow> ('v, 'v clause) ann_lit list\<close> where
  \<open>pget_trail (M, _, _, _, _, _, _, _) = M\<close>

fun set_conflict :: \<open>'v clause \<Rightarrow> 'v prag_st \<Rightarrow> 'v prag_st\<close> where
  \<open>set_conflict D (M, N, U, _, NE, UE, NS, US) =
     (M, N, U, Some D, NE, UE, NS, US)\<close>

fun pget_conflict :: \<open>'v prag_st \<Rightarrow> 'v clause option\<close> where
  \<open>pget_conflict (M, N, U, D, NE, UE, WS, Q) = D\<close>

fun pget_clauses :: \<open>'v prag_st \<Rightarrow> 'v clauses\<close> where
  \<open>pget_clauses (M, N, U, D, NE, UE, NS, US) = N + U\<close>

fun punit_clss :: \<open>'v prag_st \<Rightarrow> 'v clauses\<close> where
  \<open>punit_clss (M, N, U, D, NE, UE, NS, US) = NE + UE\<close>

fun punit_init_clauses :: \<open>'v prag_st \<Rightarrow> 'v clauses\<close> where
  \<open>punit_init_clauses (M, N, U, D, NE, UE, NS, US) = NE\<close>

fun psubsumed_learned_clss :: \<open>'v prag_st \<Rightarrow> 'v clause multiset\<close> where
  \<open>psubsumed_learned_clss (M, N, U, D, NE, UE, NS, US) = US\<close>

fun psubsumed_init_clauses :: \<open>'v prag_st \<Rightarrow> 'v clauses\<close> where
  \<open>psubsumed_init_clauses (M, N, U, D, NE, UE, NS, US) = NS\<close>

fun pget_all_init_clss :: \<open>'v prag_st \<Rightarrow> 'v clause multiset\<close> where
  \<open>pget_all_init_clss (M, N, U, D, NE, UE, NS, US) = N + NE + NS\<close>

fun pget_learned_clss :: \<open>'v prag_st \<Rightarrow> 'v clauses\<close> where
  \<open>pget_learned_clss (M, N, U, D, NE, UE, NS, US) = U\<close>

fun psubsumed_learned_clauses :: \<open>'v prag_st \<Rightarrow> 'v clauses\<close> where
  \<open>psubsumed_learned_clauses (M, N, U, D, NE, UE, NS, US) = US\<close>

fun psubsumed_clauses :: \<open>'v prag_st \<Rightarrow> 'v clauses\<close> where
  \<open>psubsumed_clauses (M, N, U, D, NE, UE, NS, US) = NS + US\<close>

fun pget_init_learned_clss :: \<open>'v prag_st \<Rightarrow> 'v clauses\<close> where
  \<open>pget_init_learned_clss (_, N, U, _, _, UE, NS, US) = UE\<close>

fun pget_all_learned_clss :: \<open>'v prag_st \<Rightarrow> 'v clauses\<close> where
  \<open>pget_all_learned_clss (_, N, U, _, _, UE, NS, US) = U + UE + US\<close>

fun pget_all_clss :: \<open>'v prag_st \<Rightarrow> 'v clause multiset\<close> where
  \<open>pget_all_clss (M, N, U, D, NE, UE, NS, US) =
     N + NE + NS + U + UE + US\<close>


section \<open>The old rules\<close>

inductive cdcl_propagate :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
propagate:
  \<open>cdcl_propagate (M, N, U, None, NE, UE, NS, US)
    (Propagated L' (D) # M, N, U, None, NE, UE, NS, US)\<close>
  if
  \<open>L' \<in># D\<close> and \<open>M \<Turnstile>as CNot (remove1_mset L' D)\<close> and
  \<open>undefined_lit M L'\<close> \<open>D \<in># N + U\<close>

inductive cdcl_conflict :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
conflict:
  \<open>cdcl_conflict (M, N, U, None, NE, UE, NS, US)
    (M, N, U, Some D, NE, UE, NS, US)\<close>
  if
  \<open>M \<Turnstile>as CNot D\<close> and
  \<open>D \<in># N + U + NE + UE + NS + US\<close>

inductive cdcl_decide :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
decide:
  \<open>cdcl_decide (M, N, U, None, NE, UE, NS, US)
    (Decided L' # M, N, U, None, NE, UE, NS, US)\<close>
  if
  \<open>undefined_lit M L'\<close> and
  \<open>atm_of L' \<in> atms_of_mm (N + NE + NS)\<close>

inductive cdcl_skip :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
skip:
  \<open>cdcl_skip (Propagated L' C # M, N, U, Some D, NE, UE, NS, US)
    (M, N, U, Some D, NE, UE, NS, US)\<close>
  if
  \<open>-L' \<notin># D\<close> and
  \<open>D \<noteq> {#}\<close>


inductive cdcl_resolve :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
resolve:
  \<open>cdcl_resolve (Propagated L' C # M, N, U, Some D, NE, UE, NS, US)
    (M, N, U, Some (cdcl\<^sub>W_restart_mset.resolve_cls L' D C), NE, UE, NS, US)\<close>
  if
  \<open>-L' \<in># D\<close> and
  \<open>get_maximum_level (Propagated L' C # M) (remove1_mset (-L') D) = count_decided M\<close> and
  \<open>L' \<in># C\<close>


inductive cdcl_backtrack :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
  \<open>cdcl_backtrack (M, N, U, Some (add_mset L D), NE, UE, NS, US)
  (Propagated L (add_mset L D') # M1, N, add_mset (add_mset L D') U, None, NE, UE, NS, US)\<close>
  if
    \<open>L \<in># D\<close> and
    \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition M)\<close> and
    \<open>get_level M L = count_decided M\<close> and
    \<open>get_level M L = get_maximum_level M (add_mset L D')\<close> and
    \<open>get_maximum_level M D' \<equiv> i\<close> and
    \<open>get_level M K = i + 1\<close> and
    \<open>D' \<subseteq># D\<close> and
    \<open>N + U + NE + UE + NS + US \<Turnstile>pm add_mset L D'\<close>

text \<open>
  Restart are already slightly restricted: we cannot remove literals
  set at level 0.
\<close>
inductive cdcl_restart :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
cdcl_restart:
  \<open>cdcl_restart (M, N, U, None, NE, UE, NS, US)
    (M', N, U, None, NE, UE, NS, US)\<close>
  if \<open>(M2, Decided K # M1) \<in> set (get_all_ann_decomposition M)\<close>

inductive cdcl_forget :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
cdcl_forget:
  \<open>cdcl_forget (M, N, add_mset C U, None, NE, UE, NS, US)
    (M', N, U, None, NE, UE, NS, US)\<close>
  if \<open>Propagated L C \<notin> set M\<close> |
cdcl_forget_subsumed:
  \<open>cdcl_forget (M, N, U, None, NE, UE, NS, add_mset C US)
    (M', N, U, None, NE, UE, NS, US)\<close>


section \<open>The new rules\<close>

text \<open>Now the more interesting part\<close>
inductive cdcl_subsumed :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
subsumed_II:
  \<open>cdcl_subsumed (M, N + {#C,C'#}, U, D, NE, UE, NS, US)
    (M, add_mset C N, U, D, NE, UE, add_mset C' NS, US)\<close>
  if \<open>C \<subseteq># C'\<close> |
subsumed_LL:
  \<open>cdcl_subsumed (M, N, U + {#C,C'#}, D, NE, UE, NS, US)
    (M, N, add_mset C U, D, NE, UE, NS, add_mset C' US)\<close>
  if \<open>C \<subseteq># C'\<close> |
subsumed_IL:
  \<open>cdcl_subsumed (M, add_mset C N, add_mset C' U, D, NE, UE, NS, US)
    (M, add_mset C N, U, D, NE, UE, NS, add_mset C' US)\<close>
  if \<open>C \<subseteq># C'\<close>

lemma state\<^sub>W_of_cdcl_subsumed:
  \<open>cdcl_subsumed S T \<Longrightarrow> state\<^sub>W_of S = state\<^sub>W_of T\<close>
  by (induction rule: cdcl_subsumed.induct)
     auto

text \<open>Resolution requires to restart (or a very careful thinking where
the clause can be used, so for now, we require level 0)\<close>


inductive cdcl_resolution :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
resolution_II:
  \<open>cdcl_resolution (M, N + {#add_mset L C, add_mset (-L) C'#}, U, D, NE, UE, NS, US)
    (M, N + {#add_mset L C, add_mset (-L) C', remdups_mset (C + C')#}, U, D, NE, UE, NS, US)\<close>
 if  \<open>count_decided M = 0\<close> |
resolution_LL:
  \<open>cdcl_resolution (M, N, U + {#add_mset L C, add_mset (-L) C'#}, D, NE, UE, NS, US)
    (M, N, U + {#add_mset L C, add_mset (-L) C', remdups_mset (C + C')#}, D, NE, UE, NS, US)\<close>
 if  \<open>count_decided M = 0\<close> |
resolution_IL:
  \<open>cdcl_resolution (M, N + {#add_mset L C'#}, U + {#add_mset (-L) C'#}, D, NE, UE, NS, US)
    (M, N + {#add_mset L C'#}, U + {#add_mset (-L) C', remdups_mset (C + C')#}, D, NE, UE, NS, US)\<close>
 if  \<open>count_decided M = 0\<close>

lemma cdcl_resolution_still_entailed:
  \<open>cdcl_resolution S T \<Longrightarrow> consistent_interp I \<Longrightarrow> I \<Turnstile>m pget_all_init_clss S \<Longrightarrow> I \<Turnstile>m pget_all_init_clss T\<close>
  apply (induction rule: cdcl_resolution.induct)
  subgoal for M N L C C' U D NE UE NS US
    by (auto simp: consistent_interp_def)
 subgoal
   by auto
 subgoal
   by auto
  done

text \<open>Tautologies are not necessarily entailed by the clause set. Therefore, we
 do not learn tautologies.
 \<close>
inductive cdcl_learn_clause :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
learn_clause:
  \<open>cdcl_learn_clause (M, N, U, D, NE, UE, NS, US)
    (M, add_mset C N, U, D, NE, UE, NS, US)\<close>
  if \<open>atms_of C \<subseteq> atms_of_mm (N + NE + US)\<close> and
    \<open>N +NE + NS \<Turnstile>pm C\<close> and
    \<open>\<not>tautology C\<close>
    \<open>count_decided M = 0\<close>

lemma cdcl_learn_clause_still_entailed:
  \<open>cdcl_learn_clause S T \<Longrightarrow> consistent_interp I \<Longrightarrow> total_over_m I (set_mset (pget_all_init_clss T)) \<Longrightarrow>
    I \<Turnstile>m pget_all_init_clss S \<Longrightarrow> I \<Turnstile>m pget_all_init_clss T\<close>
  apply (induction rule: cdcl_learn_clause.induct)
  subgoal for C N NE US NS M U D UE
    using true_clss_cls_true_clss_true_cls[of \<open>set_mset (N+NE+NS)\<close> C I]
    by (auto simp: intro: true_clss_cls_true_clss_true_cls)
  done


text \<open>

Subsumption-Resolution rules are the composition of resolution,
subsumption, learning of a clause, and potentially forget.

\<close>


section \<open>Relation to CDCL\<close>

lemma cdcl_decide_is_decide:
  \<open>cdcl_decide S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.decide (state\<^sub>W_of S) (state\<^sub>W_of T)\<close>
  apply (cases rule: cdcl_decide.cases, assumption)
  apply (rule_tac L=L' in cdcl\<^sub>W_restart_mset.decide.intros)
  by (auto intro!: cdcl\<^sub>W_restart_mset.decide.intros
    simp: cdcl\<^sub>W_restart_mset_state)

lemma cdcl_skip_is_skip:
  \<open>cdcl_skip S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of S) (state\<^sub>W_of T)\<close>
  apply (cases rule: cdcl_skip.cases, assumption)
  apply (rule_tac L=L' and C'=C and E=D and M=M in cdcl\<^sub>W_restart_mset.skip.intros)
  by (auto intro!: cdcl\<^sub>W_restart_mset.skip.intros
    simp: cdcl\<^sub>W_restart_mset_state)

lemma cdcl_resolve_is_resolve:
  \<open>cdcl_resolve S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of S) (state\<^sub>W_of T)\<close>
  apply (cases rule: cdcl_resolve.cases, assumption)
  apply (rule_tac L=L' and E=C in cdcl\<^sub>W_restart_mset.resolve.intros)
  by (auto intro!: cdcl\<^sub>W_restart_mset.resolve.intros
    simp: cdcl\<^sub>W_restart_mset_state)

lemma cdcl_conflict_is_conflict:
  \<open>cdcl_conflict S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.conflict (state\<^sub>W_of S) (state\<^sub>W_of T)\<close>
  apply (cases rule: cdcl_conflict.cases, assumption)
  apply (rule_tac D=D in cdcl\<^sub>W_restart_mset.conflict.intros)
  by (auto simp: clauses_def cdcl\<^sub>W_restart_mset_state)

lemma cdcl_backtrack_is_backtrack:
  \<open>cdcl_backtrack S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.backtrack (state\<^sub>W_of S) (state\<^sub>W_of T)\<close>
  apply (cases rule: cdcl_backtrack.cases, assumption)
  apply (rule_tac L=L and D'=D' and D=D and K=K in
    cdcl\<^sub>W_restart_mset.backtrack.intros)
  by (auto
    simp: clauses_def ac_simps cdcl\<^sub>W_restart_mset_state
      cdcl\<^sub>W_restart_mset_reduce_trail_to)

end