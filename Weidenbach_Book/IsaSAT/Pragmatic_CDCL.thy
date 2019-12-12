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


The idea is to have CDCL as the core part of the calculus and other
rules that are optional.
\<close>
type_synonym 'v prag_st =
  \<open>('v, 'v clause) ann_lits \<times> 'v clauses \<times> 'v clauses \<times>
    'v clause option \<times> 'v clauses \<times> 'v clauses \<times> 'v clauses \<times> 'v clauses\<close>


fun state\<^sub>W_of :: \<open>'v prag_st \<Rightarrow> 'v cdcl\<^sub>W_restart_mset\<close> where
\<open>state\<^sub>W_of (M, N, U, C, NE, UE, NS, US) =
  (M, N + NE + NS, U + UE + US,  C)\<close>

declare cdcl\<^sub>W_restart_mset_state[simp]

named_theorems ptwl "Theorems to simplify the state"


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

fun pget_init_clauses :: \<open>'v prag_st \<Rightarrow> 'v clauses\<close> where
  \<open>pget_init_clauses (M, N, U, D, NE, UE, NS, US) = N\<close>

fun punit_clss :: \<open>'v prag_st \<Rightarrow> 'v clauses\<close> where
  \<open>punit_clss (M, N, U, D, NE, UE, NS, US) = NE + UE\<close>

fun punit_init_clauses :: \<open>'v prag_st \<Rightarrow> 'v clauses\<close> where
  \<open>punit_init_clauses (M, N, U, D, NE, UE, NS, US) = NE\<close>

fun punit_clauses :: \<open>'v prag_st \<Rightarrow> 'v clauses\<close> where
  \<open>punit_clauses (M, N, U, D, NE, UE, NS, US) = NE + UE\<close>

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


lemma [ptwl]:
  \<open>trail (state\<^sub>W_of S) = pget_trail S\<close>
  by (solves \<open>cases S; auto\<close>)

declare ptwl[simp]


section \<open>The old rules\<close>

inductive cdcl_propagate :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
propagate:
  \<open>cdcl_propagate (M, N, U, None, NE, UE, NS, US)
    (Propagated L' D # M, N, U, None, NE, UE, NS, US)\<close>
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

inductive pcdcl_core :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
  \<open>cdcl_conflict S T \<Longrightarrow> pcdcl_core S T\<close> |
  \<open>cdcl_propagate S T \<Longrightarrow> pcdcl_core S T\<close> |
  \<open>cdcl_decide S T \<Longrightarrow> pcdcl_core S T\<close> |
  \<open>cdcl_skip S T \<Longrightarrow> pcdcl_core S T\<close> |
  \<open>cdcl_resolve S T \<Longrightarrow> pcdcl_core S T\<close> |
  \<open>cdcl_backtrack S T \<Longrightarrow> pcdcl_core S T\<close>

inductive pcdcl_core_stgy :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
  \<open>cdcl_conflict S T \<Longrightarrow> pcdcl_core_stgy S T\<close> |
  \<open>cdcl_propagate S T \<Longrightarrow> pcdcl_core_stgy S T\<close> |
  \<open>no_step cdcl_conflict S \<Longrightarrow> no_step cdcl_propagate S \<Longrightarrow> cdcl_decide S T \<Longrightarrow> pcdcl_core_stgy S T\<close> |
  \<open>cdcl_skip S T \<Longrightarrow> pcdcl_core_stgy S T\<close> |
  \<open>cdcl_resolve S T \<Longrightarrow> pcdcl_core_stgy S T\<close> |
  \<open>cdcl_backtrack S T \<Longrightarrow> pcdcl_core_stgy S T\<close>


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

text \<open>

Resolution requires to restart (or a very careful thinking where
the clause can be used, so for now, we require level 0). The names 'I'
and 'L' refers to 'irredundant' and 'learnt'.

\<close>


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

text \<open>
  Tautologies are always entailed by the clause set, but not necessarily entailed by a non-total
  model of the clauses. Therefore, we do not learn tautologies.

  E.g.: \<^term>\<open>(A \<or> B) \<and> (A \<or> C)\<close> entails the clause \<^term>\<open>(\<not>B \<or> B)\<close>, but the model containing only the
  literal \<^term>\<open>A\<close> does not entail the latter.

  This function has nothing to with CDCL's learn: any clause can be learned by this function,
  including the empty clause.
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
  \<open>cdcl_learn_clause S T \<Longrightarrow> consistent_interp I \<Longrightarrow>
    I \<Turnstile>m pget_all_init_clss S \<Longrightarrow> I \<Turnstile>m pget_all_init_clss T\<close>
  apply (induction rule: cdcl_learn_clause.induct)
  subgoal for C N NE US NS M U D UE
    using true_clss_cls_true_clss_true_cls[of \<open>set_mset (N+NE+NS)\<close> C I]
    by auto
  done


inductive pcdcl :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
  \<open>pcdcl_core S T \<Longrightarrow> pcdcl S T\<close> |
  \<open>cdcl_learn_clause S T \<Longrightarrow> pcdcl S T\<close> |
  \<open>cdcl_resolution S T \<Longrightarrow> pcdcl S T\<close> |
  \<open>cdcl_subsumed S T \<Longrightarrow> pcdcl S T\<close>

text \<open>

Subsumption-Resolution rules are the composition of resolution,
subsumption, learning of a clause, and potentially forget.

\<close>

section \<open>Invariants\<close>

text \<open>

To avoid adding a new component, we store tautologies in the subsumed
components, even though we could also store them separately. Finally,
we really want to get rid of tautologies from the clause set. They
require special cases in the arena module.

\<close>
definition psubsumed_invs :: \<open>'v prag_st \<Rightarrow> bool\<close> where
\<open>psubsumed_invs S \<longleftrightarrow>
  (\<forall>C\<in>#psubsumed_init_clauses S. tautology C \<or>
    (\<exists>C'\<in>#pget_init_clauses S+punit_init_clauses S. C' \<subseteq># C)) \<and>
  (\<forall>C\<in>#psubsumed_learned_clauses S. tautology C \<or>
    (\<exists>C'\<in>#pget_clauses S+punit_clauses S. C' \<subseteq># C))\<close>

text \<open>
In the TWL version, we also had \<^term>\<open>(\<forall>C \<in># NE + UE.
      (\<exists>L. L \<in># C \<and> (D = None \<or> count_decided M > 0 \<longrightarrow> get_level M L = 0 \<and> L \<in> lits_of_l M)))\<close>
as definition. This make is possible to express the conflict analysis at level 0.
However, it makes the code easier to not do this analysis, because we already know
that we will derive the empty clause (but do not know what the trail will be).

We could simplify the invariant to
 \<^term>\<open>(\<forall>C \<in># NE + UE.
      (\<exists>L. L \<in># C \<and> (get_level M L = 0 \<and> L \<in> lits_of_l M)))\<close>
at the price of an uglier correctness theorem.


Final remark, we could simplify the invariant in another way: We could have \<^term>\<open>D={#L#}\<close>.
This, however, requires that we either remove all literals set at level 0, including in
\<^emph>\<open>reasons\<close>, which we would rather avoid, or add the new clause \<^term>\<open>{#L#}\<close> each time we
propagate a clause at level 0 and change the reason to this new clause. In either cases,
we could use the subsumed components to store the clauses.
\<close>
fun entailed_clss_inv :: \<open>'v prag_st \<Rightarrow> bool\<close> where
  \<open>entailed_clss_inv (M, N, U, D, NE, UE, NS, US) \<longleftrightarrow>
    (\<forall>C \<in># NE + UE.
      (\<exists>L. L \<in># C \<and> (D = None \<or> count_decided M > 0 \<longrightarrow> get_level M L = 0 \<and> L \<in> lits_of_l M)))\<close>

lemmas entailed_clss_inv_def = entailed_clss_inv.simps

lemmas [simp del] = entailed_clss_inv.simps


section \<open>Relation to CDCL\<close>

lemma cdcl_decide_is_decide:
  \<open>cdcl_decide S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.decide (state\<^sub>W_of S) (state\<^sub>W_of T)\<close>
  apply (cases rule: cdcl_decide.cases, assumption)
  apply (rule_tac L=L' in cdcl\<^sub>W_restart_mset.decide.intros)
  by auto

lemma decide_is_cdcl_decide:
  \<open>cdcl\<^sub>W_restart_mset.decide (state\<^sub>W_of S) T \<Longrightarrow> Ex(cdcl_decide S)\<close>
  apply (cases S, hypsubst)
  apply (cases rule: cdcl\<^sub>W_restart_mset.decide.cases, assumption)
  apply (rule exI[of _ \<open>(_, _, _, None, _, _, _, _)\<close>])
  by (auto intro!: cdcl_decide.intros)

lemma cdcl_skip_is_skip:
  \<open>cdcl_skip S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of S) (state\<^sub>W_of T)\<close>
  apply (cases rule: cdcl_skip.cases, assumption)
  apply (rule_tac L=L' and C'=C and E=D and M=M in cdcl\<^sub>W_restart_mset.skip.intros)
  by auto

lemma skip_is_cdcl_skip:
  \<open>cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of S) T \<Longrightarrow> Ex(cdcl_skip S)\<close>
  apply (cases rule: cdcl\<^sub>W_restart_mset.skip.cases, assumption)
  apply (cases S)
  apply (auto simp: cdcl_skip.simps)
  done

lemma cdcl_resolve_is_resolve:
  \<open>cdcl_resolve S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of S) (state\<^sub>W_of T)\<close>
  apply (cases rule: cdcl_resolve.cases, assumption)
  apply (rule_tac L=L' and E=C in cdcl\<^sub>W_restart_mset.resolve.intros)
  by auto

lemma resolve_is_cdcl_resolve:
  \<open>cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of S) T \<Longrightarrow> Ex(cdcl_resolve S)\<close>
  apply (cases rule: cdcl\<^sub>W_restart_mset.resolve.cases, assumption)
  apply (cases S; cases \<open>pget_trail S\<close>)
  apply (auto simp: cdcl_resolve.simps)
  done

lemma cdcl_backtrack_is_backtrack:
  \<open>cdcl_backtrack S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.backtrack (state\<^sub>W_of S) (state\<^sub>W_of T)\<close>
  apply (cases rule: cdcl_backtrack.cases, assumption)
  apply (rule_tac L=L and D'=D' and D=D and K=K in
    cdcl\<^sub>W_restart_mset.backtrack.intros)
  by (auto simp: clauses_def ac_simps
      cdcl\<^sub>W_restart_mset_reduce_trail_to)


lemma backtrack_is_cdcl_backtrack:
  \<open>cdcl\<^sub>W_restart_mset.backtrack (state\<^sub>W_of S) T \<Longrightarrow> Ex(cdcl_backtrack S)\<close>
  apply (cases rule: cdcl\<^sub>W_restart_mset.backtrack.cases, assumption)
  apply (cases S; cases T)
  apply (simp add: cdcl_backtrack.simps clauses_def add_mset_eq_add_mset
        cdcl\<^sub>W_restart_mset_reduce_trail_to conj_disj_distribR ex_disj_distrib
      split: cong: if_cong)
  apply (rule disjI1)
  apply (rule_tac x=K in exI)
  apply auto
  apply (rule_tac x=D' in exI)
  apply (auto simp: Un_commute Un_assoc)
  apply (rule back_subst[of \<open>\<lambda>a. a \<Turnstile>p _\<close>])
  apply assumption
  apply auto
  done

lemma cdcl_conflict_is_conflict:
  \<open>cdcl_conflict S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.conflict (state\<^sub>W_of S) (state\<^sub>W_of T)\<close>
  apply (cases rule: cdcl_conflict.cases, assumption)
  apply (rule_tac D=D in cdcl\<^sub>W_restart_mset.conflict.intros)
  by (auto simp: clauses_def)


lemma conflict_is_cdcl_conflictD:
  assumes
    confl: \<open>cdcl\<^sub>W_restart_mset.conflict (state\<^sub>W_of S) T\<close> and
    sub: \<open>psubsumed_invs S\<close> and
    ent: \<open>entailed_clss_inv S\<close> and
    invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S)\<close>
  shows \<open>Ex (cdcl_conflict S)\<close>
proof -
  obtain C where
    C: \<open>C \<in># cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of S)\<close> and
    confl: \<open>trail (state\<^sub>W_of S) \<Turnstile>as CNot C\<close> and
    conf: \<open>conflicting (state\<^sub>W_of S) = None\<close> and
    \<open>T \<sim>m update_conflicting (Some C) (state\<^sub>W_of S)\<close>
    using cdcl\<^sub>W_restart_mset.conflictE[OF confl]
    by metis
  have n_d: \<open>no_dup (pget_trail S)\<close>
    using invs unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
      by simp
  then have \<open>C \<notin># punit_clauses S\<close>
    using ent confl conf
    by (cases S)
     (auto 4 3 simp: entailed_clss_inv_def cdcl\<^sub>W_restart_mset_state
      dest!: multi_member_split dest: no_dup_consistentD)

  moreover have \<open>C \<in># psubsumed_clauses S \<Longrightarrow> \<exists>C' \<in># pget_clauses S. trail (state\<^sub>W_of S) \<Turnstile>as CNot C'\<close>
    using sub confl conf n_d ent
      consistent_CNot_not_tautology[of \<open>lits_of_l (pget_trail S)\<close> C, OF distinct_consistent_interp]
    apply (cases S)
    apply (auto simp: psubsumed_invs_def true_annots_true_cls entailed_clss_inv_def
        insert_subset_eq_iff
      dest: distinct_consistent_interp mset_subset_eqD no_dup_consistentD
      dest!: multi_member_split)
    apply (auto simp add: mset_subset_eqD
        true_clss_def_iff_negation_in_model tautology_decomp' insert_subset_eq_iff
      dest: no_dup_consistentD)
     done
  ultimately show ?thesis
    using C confl conf
    by (cases S)
     (auto simp: cdcl_conflict.simps clauses_def)
qed

lemma cdcl_propagate_is_propagate:
  \<open>cdcl_propagate S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.propagate (state\<^sub>W_of S) (state\<^sub>W_of T)\<close>
  apply (cases rule: cdcl_propagate.cases, assumption)
  apply (rule_tac L=L' and E=D in cdcl\<^sub>W_restart_mset.propagate.intros)
  by (auto simp: clauses_def)

lemma propagate_is_cdcl_propagateD:
  assumes
    confl: \<open>cdcl\<^sub>W_restart_mset.propagate (state\<^sub>W_of S) T\<close> and
    sub: \<open>psubsumed_invs S\<close> and
    ent: \<open>entailed_clss_inv S\<close> and
    invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S)\<close>
  shows \<open>Ex (cdcl_propagate S) \<or> Ex(cdcl_conflict S)\<close>
proof -
  obtain L C where
    C: \<open>C \<in># cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of S)\<close> and
    conf: \<open>conflicting (state\<^sub>W_of S) = None\<close> and
    confl:  \<open>trail (state\<^sub>W_of S) \<Turnstile>as CNot (remove1_mset L C)\<close> and
    LC: \<open>L \<in># C\<close> and
   undef:  \<open>undefined_lit (trail (state\<^sub>W_of S)) L\<close> and
    \<open>T \<sim>m cons_trail (Propagated L C) (state\<^sub>W_of S)\<close>
    using cdcl\<^sub>W_restart_mset.propagateE[OF confl]
    by metis
  have n_d: \<open>no_dup (pget_trail S)\<close>
    using invs unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
      by simp
  then have \<open>C \<notin># punit_clauses S\<close>
    using ent confl conf LC undef
    by (cases S)
      (auto 4 3 simp: entailed_clss_inv_def cdcl\<^sub>W_restart_mset_state
      dest!: multi_member_split dest: no_dup_consistentD in_lits_of_l_defined_litD)

  have tauto: \<open>\<not> tautology (remove1_mset L C)\<close>
    using confl conf n_d ent
      consistent_CNot_not_tautology[of \<open>lits_of_l (pget_trail S)\<close> \<open>remove1_mset L C\<close>,
        OF distinct_consistent_interp]
    by (cases S)
     (auto simp: true_annots_true_cls entailed_clss_inv_def
        insert_subset_eq_iff
      dest: distinct_consistent_interp mset_subset_eqD no_dup_consistentD
      dest!: multi_member_split)
   have \<open>(\<exists>C' \<in># pget_clauses S. trail (state\<^sub>W_of S) \<Turnstile>as CNot C') \<or>
     (\<exists>C' \<in># pget_clauses S. L \<in># C' \<and> trail (state\<^sub>W_of S) \<Turnstile>as CNot (remove1_mset L C'))\<close>
    if C: \<open>C \<in># psubsumed_clauses S\<close>
  proof -
    have \<open>\<not>tautology C\<close>
      using confl undef tauto
      apply (auto simp: tautology_decomp' add_mset_eq_add_mset remove1_mset_add_mset_If
        dest!: multi_member_split dest: in_lits_of_l_defined_litD split: )
        apply (case_tac \<open>L = -La\<close>)
        apply (auto dest: in_lits_of_l_defined_litD)[]
        apply simp
        apply (subst (asm) remove1_mset_add_mset_If)
        apply (case_tac \<open>L = La\<close>)
        apply (auto dest: in_lits_of_l_defined_litD)[]
        apply (auto dest: in_lits_of_l_defined_litD)[]
        done
    then consider
       C' where \<open>C' \<subseteq># C\<close> \<open>C' \<in># pget_clauses S\<close> |
       C' where \<open>C' \<subseteq># C\<close> \<open>C' \<in># punit_clauses S\<close>
      using sub C
      by (cases S)
       (auto simp: psubsumed_invs_def
        dest!: multi_member_split)
    then show ?thesis
    proof cases
      case 2
      then show ?thesis
        using ent confl undef conf n_d
       apply (cases S)
       apply (cases \<open>L  \<in># C'\<close>)
       apply (auto simp: psubsumed_invs_def true_annots_true_cls entailed_clss_inv_def
           insert_subset_eq_iff remove1_mset_add_mset_If
         dest: distinct_consistent_interp mset_subset_eqD no_dup_consistentD
         dest!: multi_member_split)
       apply (auto simp add: mset_subset_eqD add_mset_eq_add_mset subset_mset.le_iff_add
           true_clss_def_iff_negation_in_model tautology_decomp' insert_subset_eq_iff
         dest: no_dup_consistentD in_lits_of_l_defined_litD dest!: multi_member_split[of _ C]
         split: if_splits)
       done
    next
      case 1
      then show ?thesis
        using tauto confl undef conf n_d
        apply (cases S)
       apply (cases \<open>L  \<in># C'\<close>)
        apply (auto simp: psubsumed_invs_def true_annots_true_cls entailed_clss_inv_def
            insert_subset_eq_iff
          dest: distinct_consistent_interp mset_subset_eqD no_dup_consistentD
          dest!: multi_member_split)
        apply (auto simp add: mset_subset_eqD add_mset_eq_add_mset
            true_clss_def_iff_negation_in_model tautology_decomp' insert_subset_eq_iff
          dest: no_dup_consistentD dest!: multi_member_split[of _ C] intro!: bexI[of _ C'])
        by (metis (no_types, hide_lams) in_multiset_minus_notin_snd insert_DiffM member_add_mset
          mset_subset_eqD multi_self_add_other_not_self zero_diff)+
     qed
  qed
  then show ?thesis
    using C confl conf  \<open>C \<notin># punit_clauses S\<close> undef LC
    by (cases S)
      (auto simp: cdcl_propagate.simps clauses_def cdcl_conflict.simps intro!: exI[of _ L]
        intro: exI[of _ C])
qed


lemma pcdcl_core_is_cdcl:
  \<open>pcdcl_core S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W (state\<^sub>W_of S) (state\<^sub>W_of T)\<close>
  by (induction rule: pcdcl_core.induct)
   (blast intro: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W.intros cdcl_conflict_is_conflict
      cdcl_propagate_is_propagate cdcl_propagate_is_propagate cdcl_decide_is_decide
      cdcl_propagate_is_propagate cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o.intros cdcl_skip_is_skip
      cdcl_resolve_is_resolve cdcl_backtrack_is_backtrack
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_bj.intros)+

lemma pcdcl_core_stgy_is_cdcl_stgy:
  assumes
    confl: \<open>pcdcl_core_stgy S T\<close> and
    sub: \<open>psubsumed_invs S\<close> and
    ent: \<open>entailed_clss_inv S\<close> and
    invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (state\<^sub>W_of S) (state\<^sub>W_of T)\<close>
  using assms
  by (induction rule: pcdcl_core_stgy.induct)
   ((blast intro: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.intros cdcl_conflict_is_conflict
      cdcl_propagate_is_propagate cdcl_decide_is_decide cdcl_skip_is_skip cdcl_backtrack_is_backtrack
      cdcl_resolve_is_resolve cdcl\<^sub>W_restart_mset.resolve
      cdcl_skip_is_skip cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_bj_cdcl\<^sub>W_stgy
    dest: conflict_is_cdcl_conflictD propagate_is_cdcl_propagateD)+)[6]



lemma no_step_pcdcl_core_stgy_is_cdcl_stgy:
  assumes
    confl: \<open>no_step pcdcl_core_stgy S\<close> and
    sub: \<open>psubsumed_invs S\<close> and
    ent: \<open>entailed_clss_inv S\<close> and
    invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S)\<close>
  shows \<open>no_step cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (state\<^sub>W_of S)\<close>
  using assms apply -
  apply (rule ccontr)
  unfolding not_all not_not
  apply normalize_goal+
  apply (cases rule: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.cases, assumption)
  using conflict_is_cdcl_conflictD pcdcl_core_stgy.intros(1) apply blast
  using pcdcl_core_stgy.intros(1) pcdcl_core_stgy.intros(2) propagate_is_cdcl_propagateD apply blast
  apply (cases rule: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o.cases, assumption)
  using cdcl_conflict_is_conflict cdcl_propagate_is_propagate decide_is_cdcl_decide pcdcl_core_stgy.intros(3) apply blast
  apply (cases rule: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_bj.cases, assumption)
  apply (blast dest: resolve_is_cdcl_resolve backtrack_is_cdcl_backtrack pcdcl_core_stgy.intros
    skip_is_cdcl_skip)+
  done


lemma cdcl_resolution_psubsumed_invs:
  \<open>cdcl_resolution S T \<Longrightarrow> psubsumed_invs S \<Longrightarrow> psubsumed_invs T\<close>
  by (cases rule:cdcl_resolution.cases, assumption)
    (auto simp: psubsumed_invs_def)

lemma cdcl_resolution_entailed_clss_inv:
  \<open>cdcl_resolution S T \<Longrightarrow> entailed_clss_inv S \<Longrightarrow> entailed_clss_inv T\<close>
  by (cases rule:cdcl_resolution.cases, assumption)
    (auto simp: entailed_clss_inv_def)

lemma cdcl_subsumed_psubsumed_invs:
  \<open>cdcl_subsumed S T \<Longrightarrow> psubsumed_invs S \<Longrightarrow> psubsumed_invs T\<close>
  by (cases rule:cdcl_subsumed.cases, assumption)
    (auto simp: psubsumed_invs_def)

lemma cdcl_subsumed_entailed_clss_inv:
  \<open>cdcl_subsumed S T \<Longrightarrow> entailed_clss_inv S \<Longrightarrow> entailed_clss_inv T\<close>
  by (cases rule:cdcl_subsumed.cases, assumption)
    (auto simp: entailed_clss_inv_def)

lemma cdcl_learn_clause_psubsumed_invs:
  \<open>cdcl_learn_clause S T \<Longrightarrow> psubsumed_invs S \<Longrightarrow> psubsumed_invs T\<close>
  by (cases rule:cdcl_learn_clause.cases, assumption)
    (auto simp: psubsumed_invs_def)

lemma cdcl_learn_clause_entailed_clss_inv:
  \<open>cdcl_learn_clause S T \<Longrightarrow> entailed_clss_inv S \<Longrightarrow> entailed_clss_inv T\<close>
  by (cases rule:cdcl_learn_clause.cases, assumption)
    (auto simp: entailed_clss_inv_def)

end