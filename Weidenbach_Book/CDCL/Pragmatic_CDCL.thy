theory Pragmatic_CDCL
  imports CDCL.CDCL_W_Restart CDCL.CDCL_W_Abstract_State
begin

(*TODO Move*)
lemma get_all_mark_of_propagated_alt_def:
   \<open>set (get_all_mark_of_propagated M) = {C. \<exists>L. Propagated L C \<in> set M}\<close>
  by (induction M rule: ann_lit_list_induct) auto

chapter \<open>Pragmatic CDCL\<close>

text \<open>

The idea of this calculus is to sit between the nice and abstract CDCL
calculus and the first step towards the implementation, TWL. Pragmatic
is not used to mean incomplete as Jasmin Blanchette for his
superposition, but to mean that it is closer to the idead behind SAT
implementation. Therefore, the calculus will contain a few things that
cannot be expressed in CDCL, but are important in a SAT solver:

  \<^enum> To make it possible to express subsumption, we split our clauses
  in two parts: the subsumed clauses and the non-subsumed clauses. The
  CDCL calculus sees both of them together, but we only need the
  latter.

  \<^enum> We also have components for special clauses that contains a
  literal set at level 0. We need that component anyway for clauses of
  length 1 when expressing two watched literals.

  \<^enum> Adding clauses: if an init clause is subsumed by a learned
  clauses, it is better to add that clauses to the set of init clauses
  Armin Biere calls the non-subsumed initial clauses ``irredundant'',
  because they cannot be removed anymore.


The ``CDCL'' operates on the non-subsumed clauses and we show that
this is enough to coonnect it to a CDCL that operates on all clauses.
The drawback of this approach is that we cannot remove literals, even
if they do not appear anymore in the non-subsumed clauses. However, as
these atoms will never appear in a conflict clause, they will very
soon be at the end of the decision heuristic and, therefore, will not
interfere nor slow down the solving process too much (they still
occupy some memory locations, hence a small impact).


The second idea was already included in the formalization of TWL
because of (i) clauses of length one do not have two literals to
watch; (ii) moving them away makes garbage collecting easier, because
no reason at level 0 on the trail is included in the set of clauses.

We also started to implement the ideas one and three, but we realised
while thinking about restarts that separate rules are needed to avoid
a lot of copy-and-paste. It was also not clear how to add subsumption
detection on the fly without restart (like done right after a
backtrack in CaDiCaL or in SPASS). In the end, we decided to go for a
separate calculus that incorporates all theses rules: The idea is to
have CDCL as the core part of the calculus and other rules that are
optional.


Termination still comes from the CDCL calculus: We do not want to
apply the other rules exhaustively.

Non-satisfiability-preserving clause additions are possible if all
models after adding a clause are also models from the set of clauses
before adding that clause.

The calculus as expressed here does not deal with global
transformations, like renumbering of variables or symmetry
breaking. It only supports clause addition.

There are still a few things that are missing in this calculus and
require further thinking:

  \<^enum> Non-satisfiability-preserving clause elimination (blocked clause
  elimination, covered clauses). These transformations requires to
  reconstruct the model, and it also not clear how to find these
  clauses efficiently. Reconstruction is not that easy to express, and
  it is not so clear how to implement it in the SAT solver.

  \<^enum> Variable Elimination. Here reconstruction is also required. This
  technique is however extremely powerful and likely a must for every
  SAT solver.


For the calculus we have three layers:
  \<^enum> the core corresponds to the application to most CDCL rules. Correctness and completeness come
    from this level. The rules are applied until completion.
  \<^enum> the terminating core (tcore) additionally includes rule that makes it possible to handle clauses of
    length 1. Termination comes from this level. The rules are optional.
  \<^enum> the full calculus also includes rule to do inprocessing (and restarts). The rules are optional
    too.

In order to keep the core small, if backtrack learns a unit clause, we use one step from the tcore.
At this level of the presentation, the special case of the unit clause does not matter. However,
it is important for the calculus with watched literals, since these clauses cannot be watched.


TODO:
  \<^item> model reconstruction
\<close>
type_synonym 'v prag_st =
  \<open>('v, 'v clause) ann_lits \<times> 'v clauses \<times> 'v clauses \<times>
    'v clause option \<times> 'v clauses \<times> 'v clauses \<times> 'v clauses \<times> 'v clauses\<close>


fun state_of :: \<open>'v prag_st \<Rightarrow> 'v cdcl\<^sub>W_restart_mset\<close> where
\<open>state_of (M, N, U, C, NE, UE, NS, US) =
  (M, N + NE + NS, U + UE + US, C)\<close>

declare cdcl\<^sub>W_restart_mset_state[simp]

named_theorems ptwl \<open>Theorems to simplify the state\<close>


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
  \<open>trail (state_of S) = pget_trail S\<close>
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
  \<open>D \<in># N + U\<close>

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

inductive pcdcl_core :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> for S T :: \<open>'v prag_st\<close> where
  \<open>cdcl_conflict S T \<Longrightarrow> pcdcl_core S T\<close> |
  \<open>cdcl_propagate S T \<Longrightarrow> pcdcl_core S T\<close> |
  \<open>cdcl_decide S T \<Longrightarrow> pcdcl_core S T\<close> |
  \<open>cdcl_skip S T \<Longrightarrow> pcdcl_core S T\<close> |
  \<open>cdcl_resolve S T \<Longrightarrow> pcdcl_core S T\<close> |
  \<open>cdcl_backtrack S T \<Longrightarrow> pcdcl_core S T\<close>

inductive pcdcl_core_stgy :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> for S T :: \<open>'v prag_st\<close> where
  \<open>cdcl_conflict S T \<Longrightarrow> pcdcl_core_stgy S T\<close> |
  \<open>cdcl_propagate S T \<Longrightarrow> pcdcl_core_stgy S T\<close> |
  \<open>no_step cdcl_conflict S \<Longrightarrow> no_step cdcl_propagate S \<Longrightarrow> cdcl_decide S T \<Longrightarrow> pcdcl_core_stgy S T\<close> |
  \<open>cdcl_skip S T \<Longrightarrow> pcdcl_core_stgy S T\<close> |
  \<open>cdcl_resolve S T \<Longrightarrow> pcdcl_core_stgy S T\<close> |
  \<open>cdcl_backtrack S T \<Longrightarrow> pcdcl_core_stgy S T\<close>


section \<open>The new rules\<close>

text \<open>Now the different part\<close>
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

lemma state_of_cdcl_subsumed:
  \<open>cdcl_subsumed S T \<Longrightarrow> state_of S = state_of T\<close>
  by (induction rule: cdcl_subsumed.induct)
     auto

text \<open>

Resolution requires to restart (or a very careful thinking where
the clause can be used, so for now, we require level 0). The names 'I'
and 'L' refers to 'irredundant' and 'learnt'.


We need the assumption \<^term>\<open>\<not>tautology (C + C')\<close> because learned clauses cannot
be tautologies.
\<close>


inductive cdcl_resolution :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
resolution_II:
  \<open>cdcl_resolution (M, N + {#add_mset L C, add_mset (-L) C'#}, U, D, NE, UE, NS, US)
    (M, N + {#add_mset L C, add_mset (-L) C', remdups_mset (C + C')#}, U, D, NE, UE, NS, US)\<close>
 if  \<open>count_decided M = 0\<close> |
resolution_LL:
  \<open>cdcl_resolution (M, N, U + {#add_mset L C, add_mset (-L) C'#}, D, NE, UE, NS, US)
    (M, N, U + {#add_mset L C, add_mset (-L) C', remdups_mset (C + C')#}, D, NE, UE, NS, US)\<close>
 if  \<open>count_decided M = 0\<close> and \<open>\<not>tautology (C + C')\<close> |
resolution_IL:
  \<open>cdcl_resolution (M, N + {#add_mset L C#}, U + {#add_mset (-L) C'#}, D, NE, UE, NS, US)
    (M, N + {#add_mset L C#}, U + {#add_mset (-L) C', remdups_mset (C + C')#}, D, NE, UE, NS, US)\<close>
 if  \<open>count_decided M = 0\<close> and \<open>\<not>tautology (C + C')\<close>

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
    \<open>\<not>tautology C\<close> and
    \<open>count_decided M = 0\<close> and
    \<open>distinct_mset C\<close>

lemma cdcl_learn_clause_still_entailed:
  \<open>cdcl_learn_clause S T \<Longrightarrow> consistent_interp I \<Longrightarrow>
    I \<Turnstile>m pget_all_init_clss S \<Longrightarrow> I \<Turnstile>m pget_all_init_clss T\<close>
  apply (induction rule: cdcl_learn_clause.induct)
  subgoal for C N NE US NS M U D UE
    using true_clss_cls_true_clss_true_cls[of \<open>set_mset (N+NE+NS)\<close> C I]
    by auto
  done

inductive cdcl_flush_unit :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
learn_unit_clause_R:
  \<open>cdcl_flush_unit (M, add_mset {#L#} N, U, D, NE, UE, NS, US)
    (M, N, U, D, add_mset {#L#} NE, UE, NS, US)\<close>
  if \<open>get_level M L = 0\<close> \<open>L \<in> lits_of_l M\<close> |
learn_unit_clause_I:
  \<open>cdcl_flush_unit (M, N, add_mset {#L#} U, D, NE, UE, NS, US)
    (M, N, U, D, NE, add_mset {#L#} UE, NS, US)\<close>
  if \<open>get_level M L = 0\<close> \<open>L \<in> lits_of_l M\<close>

inductive pcdcl :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
  \<open>pcdcl_core S T \<Longrightarrow> pcdcl S T\<close> |
  \<open>cdcl_learn_clause S T \<Longrightarrow> pcdcl S T\<close> |
  \<open>cdcl_resolution S T \<Longrightarrow> pcdcl S T\<close> |
  \<open>cdcl_subsumed S T \<Longrightarrow> pcdcl S T\<close> |
  \<open>cdcl_flush_unit S T \<Longrightarrow> pcdcl S T\<close>

inductive pcdcl_stgy :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> for S T :: \<open>'v prag_st\<close> where
  \<open>pcdcl_core_stgy S T \<Longrightarrow> pcdcl_stgy S T\<close> |
  \<open>cdcl_learn_clause S T \<Longrightarrow> pcdcl_stgy S T\<close> |
  \<open>cdcl_resolution S T \<Longrightarrow> pcdcl_stgy S T\<close> |
  \<open>cdcl_subsumed S T \<Longrightarrow> pcdcl_stgy S T\<close>|
  \<open>cdcl_flush_unit S T \<Longrightarrow> pcdcl_stgy S T\<close>

lemma pcdcl_core_stgy_pcdcl: \<open>pcdcl_core_stgy S T \<Longrightarrow> pcdcl_core S T\<close>
  by (auto simp: pcdcl_core.simps pcdcl_core_stgy.simps)

lemma pcdcl_stgy_pcdcl: \<open>pcdcl_stgy S T \<Longrightarrow> pcdcl S T\<close>
  by (auto simp: pcdcl.simps pcdcl_stgy.simps pcdcl_core_stgy_pcdcl)

lemma rtranclp_pcdcl_stgy_pcdcl: \<open>pcdcl_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> pcdcl\<^sup>*\<^sup>* S T\<close>
  by (induction rule: rtranclp_induct) (auto dest!: pcdcl_stgy_pcdcl)


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
      (\<exists>L. L \<in># C \<and> ((D = None \<or> count_decided M > 0) \<longrightarrow> (get_level M L = 0 \<and> L \<in> lits_of_l M))))\<close>

lemmas entailed_clss_inv_def = entailed_clss_inv.simps

lemmas [simp del] = entailed_clss_inv.simps


section \<open>Relation to CDCL\<close>

lemma cdcl_decide_is_decide:
  \<open>cdcl_decide S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.decide (state_of S) (state_of T)\<close>
  apply (cases rule: cdcl_decide.cases, assumption)
  apply (rule_tac L=L' in cdcl\<^sub>W_restart_mset.decide.intros)
  by auto

lemma decide_is_cdcl_decide:
  \<open>cdcl\<^sub>W_restart_mset.decide (state_of S) T \<Longrightarrow> Ex(cdcl_decide S)\<close>
  apply (cases S, hypsubst)
  apply (cases rule: cdcl\<^sub>W_restart_mset.decide.cases, assumption)
  apply (rule exI[of _ \<open>(_, _, _, None, _, _, _, _)\<close>])
  by (auto intro!: cdcl_decide.intros)

lemma cdcl_skip_is_skip:
  \<open>cdcl_skip S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.skip (state_of S) (state_of T)\<close>
  apply (cases rule: cdcl_skip.cases, assumption)
  apply (rule_tac L=L' and C'=C and E=D and M=M in cdcl\<^sub>W_restart_mset.skip.intros)
  by auto

lemma skip_is_cdcl_skip:
  \<open>cdcl\<^sub>W_restart_mset.skip (state_of S) T \<Longrightarrow> Ex(cdcl_skip S)\<close>
  apply (cases rule: cdcl\<^sub>W_restart_mset.skip.cases, assumption)
  apply (cases S)
  apply (auto simp: cdcl_skip.simps)
  done

lemma cdcl_resolve_is_resolve:
  \<open>cdcl_resolve S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.resolve (state_of S) (state_of T)\<close>
  apply (cases rule: cdcl_resolve.cases, assumption)
  apply (rule_tac L=L' and E=C in cdcl\<^sub>W_restart_mset.resolve.intros)
  by auto

lemma resolve_is_cdcl_resolve:
  \<open>cdcl\<^sub>W_restart_mset.resolve (state_of S) T \<Longrightarrow> Ex(cdcl_resolve S)\<close>
  apply (cases rule: cdcl\<^sub>W_restart_mset.resolve.cases, assumption)
  apply (cases S; cases \<open>pget_trail S\<close>)
  apply (auto simp: cdcl_resolve.simps)
  done

lemma cdcl_backtrack_is_backtrack:
  \<open>cdcl_backtrack S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.backtrack (state_of S) (state_of T)\<close>
  apply (cases rule: cdcl_backtrack.cases, assumption)
  apply (rule_tac L=L and D'=D' and D=D and K=K in
    cdcl\<^sub>W_restart_mset.backtrack.intros)
  by (auto simp: clauses_def ac_simps
      cdcl\<^sub>W_restart_mset_reduce_trail_to)


lemma backtrack_is_cdcl_backtrack:
  \<open>cdcl\<^sub>W_restart_mset.backtrack (state_of S) T \<Longrightarrow> Ex(cdcl_backtrack S)\<close>
  apply (cases rule: cdcl\<^sub>W_restart_mset.backtrack.cases, assumption)
  apply (cases S; cases T)
  apply (simp add: cdcl_backtrack.simps clauses_def add_mset_eq_add_mset
        cdcl\<^sub>W_restart_mset_reduce_trail_to conj_disj_distribR ex_disj_distrib
      cong: if_cong)
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
  \<open>cdcl_conflict S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.conflict (state_of S) (state_of T)\<close>
  apply (cases rule: cdcl_conflict.cases, assumption)
  apply (rule_tac D=D in cdcl\<^sub>W_restart_mset.conflict.intros)
  by (auto simp: clauses_def)


lemma conflict_is_cdcl_conflictD:
  assumes
    confl: \<open>cdcl\<^sub>W_restart_mset.conflict (state_of S) T\<close> and
    sub: \<open>psubsumed_invs S\<close> and
    ent: \<open>entailed_clss_inv S\<close> and
    invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of S)\<close>
  shows \<open>Ex (cdcl_conflict S)\<close>
proof -
  obtain C where
    C: \<open>C \<in># cdcl\<^sub>W_restart_mset.clauses (state_of S)\<close> and
    confl: \<open>trail (state_of S) \<Turnstile>as CNot C\<close> and
    conf: \<open>conflicting (state_of S) = None\<close> and
    \<open>T \<sim>m update_conflicting (Some C) (state_of S)\<close>
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

  moreover have \<open>C \<in># psubsumed_clauses S \<Longrightarrow> \<exists>C' \<in># pget_clauses S. trail (state_of S) \<Turnstile>as CNot C'\<close>
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
  \<open>cdcl_propagate S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.propagate (state_of S) (state_of T)\<close>
  apply (cases rule: cdcl_propagate.cases, assumption)
  apply (rule_tac L=L' and E=D in cdcl\<^sub>W_restart_mset.propagate.intros)
  by (auto simp: clauses_def)

lemma propagate_is_cdcl_propagateD:
  assumes
    confl: \<open>cdcl\<^sub>W_restart_mset.propagate (state_of S) T\<close> and
    sub: \<open>psubsumed_invs S\<close> and
    ent: \<open>entailed_clss_inv S\<close> and
    invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of S)\<close>
  shows \<open>Ex (cdcl_propagate S) \<or> Ex(cdcl_conflict S)\<close>
proof -
  obtain L C where
    C: \<open>C \<in># cdcl\<^sub>W_restart_mset.clauses (state_of S)\<close> and
    conf: \<open>conflicting (state_of S) = None\<close> and
    confl:  \<open>trail (state_of S) \<Turnstile>as CNot (remove1_mset L C)\<close> and
    LC: \<open>L \<in># C\<close> and
   undef:  \<open>undefined_lit (trail (state_of S)) L\<close> and
    \<open>T \<sim>m cons_trail (Propagated L C) (state_of S)\<close>
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
   have \<open>(\<exists>C' \<in># pget_clauses S. trail (state_of S) \<Turnstile>as CNot C') \<or>
     (\<exists>C' \<in># pget_clauses S. L \<in># C' \<and> trail (state_of S) \<Turnstile>as CNot (remove1_mset L C'))\<close>
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
  \<open>pcdcl_core S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W (state_of S) (state_of T)\<close>
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
    invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (state_of S) (state_of T)\<close>
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
    invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of S)\<close>
  shows \<open>no_step cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (state_of S)\<close>
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

lemma cdcl_learn_clause_all_struct_inv:
  assumes
    \<open>cdcl_learn_clause S T\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of S)\<close>
  shows
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of T)\<close>
  using assms
  by (induction rule: cdcl_learn_clause.induct)
    (auto 8 3 simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        cdcl\<^sub>W_restart_mset.no_strange_atm_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
        cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
        cdcl\<^sub>W_restart_mset.clauses_def
        cdcl\<^sub>W_restart_mset.reasons_in_clauses_def
      intro: all_decomposition_implies_mono)

lemma cdcl_subsumed_all_struct_inv:
  assumes
    \<open>cdcl_subsumed S T\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of S)\<close>
  shows
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of T)\<close>
  using assms
  apply (induction rule: cdcl_subsumed.induct)
  subgoal for C C'
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
          cdcl\<^sub>W_restart_mset.no_strange_atm_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
          cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
          cdcl\<^sub>W_restart_mset.clauses_def
          cdcl\<^sub>W_restart_mset.reasons_in_clauses_def
          insert_commute[of C C']
        intro: all_decomposition_implies_mono)
  subgoal for C C'
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
          cdcl\<^sub>W_restart_mset.no_strange_atm_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
          cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
          cdcl\<^sub>W_restart_mset.clauses_def
          cdcl\<^sub>W_restart_mset.reasons_in_clauses_def
          insert_commute[of C C']
        intro: all_decomposition_implies_mono)
  subgoal for C C'
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
          cdcl\<^sub>W_restart_mset.no_strange_atm_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
          cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
          cdcl\<^sub>W_restart_mset.clauses_def
          cdcl\<^sub>W_restart_mset.reasons_in_clauses_def
          insert_commute[of C C']
        intro: all_decomposition_implies_mono)
   done


lemma all_decomposition_implies_monoI:
  \<open>all_decomposition_implies N M \<Longrightarrow> N \<subseteq> N' \<Longrightarrow> all_decomposition_implies N' M\<close>
  by (metis all_decomposition_implies_union le_iff_sup)

lemma cdcl_resolution_all_struct_inv:
  assumes
    \<open>cdcl_resolution S T\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of S)\<close>
  shows
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of T)\<close>
  using assms
  apply (induction rule: cdcl_resolution.induct)
  subgoal for M N L C C' U D NE UE NS US
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
          cdcl\<^sub>W_restart_mset.no_strange_atm_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
          cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
          cdcl\<^sub>W_restart_mset.clauses_def
          cdcl\<^sub>W_restart_mset.reasons_in_clauses_def
          insert_commute[of _ \<open>remdups_mset (C + C')\<close>]
        intro: all_decomposition_implies_monoI)
  subgoal for M C C' N U L D NE UE NS US
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
          cdcl\<^sub>W_restart_mset.no_strange_atm_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
          cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
          cdcl\<^sub>W_restart_mset.clauses_def
          cdcl\<^sub>W_restart_mset.reasons_in_clauses_def
          insert_commute[of _ \<open>remdups_mset (C + C')\<close>]
        intro: all_decomposition_implies_monoI)
  subgoal for M C C' N L U D NE UE NS US
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
          cdcl\<^sub>W_restart_mset.no_strange_atm_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
          cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
          cdcl\<^sub>W_restart_mset.clauses_def
          cdcl\<^sub>W_restart_mset.reasons_in_clauses_def
          insert_commute[of _ \<open>remdups_mset (C + C')\<close>]
        intro: all_decomposition_implies_monoI)
  done

lemma cdcl_flush_unit_unchanged:
  \<open>cdcl_flush_unit S T \<Longrightarrow> state_of S = state_of T\<close>
  by (auto simp: cdcl_flush_unit.simps)

lemma pcdcl_all_struct_inv:
  \<open>pcdcl S T \<Longrightarrow>
   cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of S) \<Longrightarrow>
   cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of T)\<close>
  by (induction rule: pcdcl.induct)
    (blast intro: cdcl_resolution_all_struct_inv cdcl_subsumed_all_struct_inv
      cdcl_learn_clause_all_struct_inv cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_inv
    dest!: pcdcl_core_is_cdcl subst[OF cdcl_flush_unit_unchanged]
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_cdcl\<^sub>W_restart)+

definition pcdcl_all_struct_invs :: \<open>_\<close> where
\<open>pcdcl_all_struct_invs S \<longleftrightarrow>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of S) \<and>
  entailed_clss_inv S \<and>
  psubsumed_invs S\<close>

lemma entailed_clss_inv_Propagated:
  assumes \<open>entailed_clss_inv (M, N, U, None, NE, UE, NS, US)\<close> and
    undef: \<open>undefined_lit M L'\<close>
  shows \<open>entailed_clss_inv (Propagated L' D # M, N, U, None, NE, UE, NS, US)\<close>
  unfolding entailed_clss_inv_def
proof (intro conjI impI ballI)
  fix C
  assume \<open>C \<in># NE + UE\<close>
  then obtain L where
    LC: \<open>L \<in># C\<close> and
    dec: \<open>get_level M L = 0 \<and> L \<in> lits_of_l M\<close>
    using assms
    by (auto simp: entailed_clss_inv_def
        get_level_cons_if atm_of_eq_atm_of
      dest!: multi_member_split[of C]
      split: if_splits)
  show \<open>\<exists>L. L \<in># C \<and>
            (None = None \<or> 0 < count_decided (Propagated L' D # M) \<longrightarrow>
             get_level (Propagated L' D # M) L = 0 \<and> L \<in> lits_of_l (Propagated L' D # M))\<close>
    apply (rule exI[of _ L])
    apply (cases \<open>count_decided M = 0\<close>)
    using count_decided_ge_get_level[of M]
    using LC dec undef
    by (auto simp: entailed_clss_inv_def
        get_level_cons_if atm_of_eq_atm_of
      split: if_splits dest: in_lits_of_l_defined_litD)
qed


lemma entailed_clss_inv_skip:
  assumes  \<open>entailed_clss_inv (Propagated L' D'' # M, N, U, Some D, NE, UE, NS, US)\<close>
  shows  \<open>entailed_clss_inv (M, N, U, Some D', NE, UE, NS, US)\<close>
  using assms
  unfolding entailed_clss_inv_def
  by (auto 7 3 simp:
        get_level_cons_if atm_of_eq_atm_of
        dest!: multi_member_split[of _ NE]  multi_member_split[of _ UE]
        dest: multi_member_split
      split: if_splits)

lemma entailed_clss_inv_ConflictD: \<open>entailed_clss_inv (M, N, U, None, NE, UE, NS, US) \<Longrightarrow>
  entailed_clss_inv (M, N, U, Some D, NE, UE, NS, US)\<close>
  by (auto simp: entailed_clss_inv_def)

lemma entailed_clss_inv_Decided:
  assumes \<open>entailed_clss_inv (M, N, U, None, NE, UE, NS, US)\<close> and
    undef: \<open>undefined_lit M L'\<close>
  shows \<open>entailed_clss_inv (Decided L' # M, N, U, None, NE, UE, NS, US)\<close>
  using assms
  unfolding entailed_clss_inv_def
  by (auto 7 3 simp: entailed_clss_inv_def
        get_level_cons_if atm_of_eq_atm_of
      split: if_splits dest: in_lits_of_l_defined_litD
      dest!: multi_member_split[of _ \<open>NE\<close>] multi_member_split[of _ \<open>UE\<close>])

lemma get_all_ann_decomposition_lvl0_still:  \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<Longrightarrow> L \<in> lits_of_l M \<Longrightarrow> get_level M L = 0 \<Longrightarrow>
      L \<in> lits_of_l M1 \<and> get_level M1 L = 0\<close>
  by (auto dest!: get_all_ann_decomposition_exists_prepend simp: get_level_append_if get_level_cons_if
      split: if_splits dest: in_lits_of_l_defined_litD)

lemma cdcl_backtrack_entailed_clss_inv: \<open>cdcl_backtrack S T \<Longrightarrow> entailed_clss_inv S \<Longrightarrow> entailed_clss_inv T\<close> for S T :: \<open>'v prag_st\<close>
  apply (induction rule: cdcl_backtrack.induct)
  subgoal for K M1 M2 M L D' i D N U NE UE NS US
    unfolding entailed_clss_inv_def
    apply (clarsimp simp only: Set.ball_simps set_mset_add_mset_insert dest!: multi_member_split)
    apply (rename_tac C A La Aa, rule_tac x=La in exI)
    using get_all_ann_decomposition_lvl0_still[of K M1 M2 M]
    by (auto simp: cdcl_backtrack.simps entailed_clss_inv_def
        get_level_cons_if atm_of_eq_atm_of
      split: if_splits dest: in_lits_of_l_defined_litD)
  done

lemma pcdcl_core_entails_clss_inv:
  \<open>pcdcl_core S T \<Longrightarrow> entailed_clss_inv S \<Longrightarrow> entailed_clss_inv T\<close>
  by (induction rule: pcdcl_core.induct)
    (auto simp: cdcl_conflict.simps
    cdcl_propagate.simps cdcl_decide.simps
    cdcl_skip.simps cdcl_resolve.simps
    get_level_cons_if atm_of_eq_atm_of
    entailed_clss_inv_Propagated
    entailed_clss_inv_ConflictD
    entailed_clss_inv_Decided
    intro: entailed_clss_inv_skip cdcl_backtrack_entailed_clss_inv
    split: if_splits)

lemma cdcl_flush_unit_invs:
  \<open>cdcl_flush_unit S T \<Longrightarrow> psubsumed_invs S \<Longrightarrow> psubsumed_invs T\<close>
  \<open>cdcl_flush_unit S T \<Longrightarrow> entailed_clss_inv S \<Longrightarrow> entailed_clss_inv T\<close>
  \<open>cdcl_flush_unit S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state_of S) \<Longrightarrow>
     cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state_of T)\<close>
  by (auto simp: cdcl_flush_unit.simps psubsumed_invs_def entailed_clss_inv_def
    dest!: multi_member_split dest: cdcl_flush_unit_unchanged)


lemma pcdcl_entails_clss_inv:
  \<open>pcdcl S T \<Longrightarrow> entailed_clss_inv S \<Longrightarrow> entailed_clss_inv T\<close>
  by (induction rule: pcdcl.induct)
   (simp_all add: pcdcl_core_entails_clss_inv cdcl_learn_clause_entailed_clss_inv
    cdcl_resolution_entailed_clss_inv cdcl_subsumed_entailed_clss_inv
   cdcl_flush_unit_invs)

lemma rtranclp_pcdcl_entails_clss_inv:
  \<open>pcdcl\<^sup>*\<^sup>* S T \<Longrightarrow> entailed_clss_inv S \<Longrightarrow> entailed_clss_inv T\<close>
  by (induction rule: rtranclp_induct)
    (simp_all add: pcdcl_entails_clss_inv)


lemma pcdcl_core_psubsumed_invs:
  \<open>pcdcl_core S T \<Longrightarrow> psubsumed_invs S \<Longrightarrow> psubsumed_invs T\<close>
  by (induction rule: pcdcl_core.induct)
    (auto simp: cdcl_conflict.simps cdcl_backtrack.simps
    cdcl_propagate.simps cdcl_decide.simps
    cdcl_skip.simps cdcl_resolve.simps
    get_level_cons_if atm_of_eq_atm_of
    psubsumed_invs_def)

lemma pcdcl_psubsumed_invs:
  \<open>pcdcl S T \<Longrightarrow> psubsumed_invs S \<Longrightarrow> psubsumed_invs T\<close>
  by (induction rule: pcdcl.induct)
    (simp_all add: pcdcl_core_psubsumed_invs cdcl_learn_clause_psubsumed_invs
    cdcl_resolution_psubsumed_invs cdcl_subsumed_psubsumed_invs cdcl_flush_unit_invs)

lemma rtranclp_pcdcl_psubsumed_invs:
  \<open>pcdcl\<^sup>*\<^sup>* S T \<Longrightarrow> psubsumed_invs S \<Longrightarrow> psubsumed_invs T\<close>
  by (induction rule: rtranclp_induct)
    (simp_all add: pcdcl_psubsumed_invs)

lemma rtranclp_pcdcl_core_stgy_pcdcl: \<open>pcdcl_core_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> pcdcl\<^sup>*\<^sup>* S T\<close>
  apply (induction rule: rtranclp_induct)
  apply (simp add: pcdcl_core_stgy_pcdcl)
  by (metis (no_types, hide_lams) converse_rtranclp_into_rtranclp pcdcl.intros(1)
    pcdcl_core_stgy_pcdcl r_into_rtranclp rtranclp_idemp)

lemma rtranclp_pcdcl_core_stgy_is_cdcl_stgy:
  assumes
    confl: \<open>pcdcl_core_stgy\<^sup>*\<^sup>* S T\<close> and
    sub: \<open>psubsumed_invs S\<close> and
    ent: \<open>entailed_clss_inv S\<close> and
    invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (state_of S) (state_of T)\<close>
  using assms apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for T U
    using rtranclp_pcdcl_psubsumed_invs[of S T] rtranclp_pcdcl_core_stgy_pcdcl[of S T]
      rtranclp_pcdcl_entails_clss_inv[of S T] pcdcl_core_stgy_is_cdcl_stgy[of T U]
    by (auto simp add: cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv)
  done

lemma pcdcl_all_struct_invs:
  \<open>pcdcl S T \<Longrightarrow>
   pcdcl_all_struct_invs S \<Longrightarrow>
   pcdcl_all_struct_invs T\<close>
   unfolding pcdcl_all_struct_invs_def
  by (intro conjI)
   (simp_all add: pcdcl_all_struct_inv pcdcl_entails_clss_inv
    pcdcl_psubsumed_invs)

lemma rtranclp_pcdcl_all_struct_invs:
  \<open>pcdcl\<^sup>*\<^sup>* S T \<Longrightarrow> pcdcl_all_struct_invs S \<Longrightarrow> pcdcl_all_struct_invs T\<close>
  by (induction rule: rtranclp_induct)
    (auto simp: pcdcl_all_struct_invs)

lemma cdcl_resolution_entailed_by_init:
  assumes \<open>cdcl_resolution S T\<close> and
    \<open>pcdcl_all_struct_invs S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of T)\<close>
  using assms
  apply (induction rule: cdcl_resolution.induct)
  apply (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def)
  apply (metis (full_types) insert_commute true_clss_clss_insert_l)
  apply (metis (full_types) insert_commute true_clss_clss_insert_l)
  apply (metis (full_types) insert_commute true_clss_clss_insert_l)
  apply (metis add.commute true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or)
  by (metis Partial_Herbrand_Interpretation.uminus_lit_swap member_add_mset set_mset_add_mset_insert
    set_mset_union true_clss_cls_in true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or)

lemma cdcl_subsumed_entailed_by_init:
  assumes \<open>cdcl_subsumed S T\<close> and
    \<open>pcdcl_all_struct_invs S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of T)\<close>
  using assms
  by (induction rule: cdcl_subsumed.induct)
    (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def insert_commute)

lemma cdcl_learn_clause_entailed_by_init:
  assumes \<open>cdcl_learn_clause S T\<close> and
    \<open>pcdcl_all_struct_invs S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of T)\<close>
  using assms
  by (induction rule: cdcl_learn_clause.induct)
    (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def insert_commute)


lemma pcdcl_entailed_by_init:
  assumes \<open>pcdcl S T\<close> and
    \<open>pcdcl_all_struct_invs S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of T)\<close>
  using assms
  apply (induction rule: pcdcl.induct)
  apply (simp_all add: cdcl_learn_clause_entailed_by_init cdcl_subsumed_entailed_by_init
    cdcl_resolution_entailed_by_init cdcl_flush_unit_unchanged)
  by (meson cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_cdcl\<^sub>W_restart
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed pcdcl_all_struct_invs_def pcdcl_core_is_cdcl)



lemma pcdcl_core_stgy_stgy_invs:
  assumes
    confl: \<open>pcdcl_core_stgy S T\<close> and
    sub: \<open>psubsumed_invs S\<close> and
    ent: \<open>entailed_clss_inv S\<close> and
    invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of S)\<close> and
     \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state_of S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state_of T)\<close>
  using assms
  by (meson cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_cdcl\<^sub>W_stgy_invariant pcdcl_core_stgy_is_cdcl_stgy)


lemma cdcl_subsumed_stgy_stgy_invs:
  assumes
    confl: \<open>cdcl_subsumed S T\<close> and
    sub: \<open>psubsumed_invs S\<close> and
    ent: \<open>entailed_clss_inv S\<close> and
    invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of S)\<close> and
     \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state_of S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state_of T)\<close>
  using assms
  by (induction rule: cdcl_subsumed.induct)
    (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
    cdcl\<^sub>W_restart_mset.no_smaller_confl_def cdcl\<^sub>W_restart_mset.clauses_def)

lemma cdcl_resolution_stgy_stgy_invs:
  assumes
    confl: \<open>cdcl_resolution S T\<close> and
    sub: \<open>psubsumed_invs S\<close> and
    ent: \<open>entailed_clss_inv S\<close> and
    invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of S)\<close> and
     \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state_of S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state_of T)\<close>
  using assms
  by (induction rule: cdcl_resolution.induct)
    (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
    cdcl\<^sub>W_restart_mset.no_smaller_confl_def cdcl\<^sub>W_restart_mset.clauses_def)


lemma cdcl_learn_clause_stgy_stgy_invs:
  assumes
    confl: \<open>cdcl_learn_clause S T\<close> and
    sub: \<open>psubsumed_invs S\<close> and
    ent: \<open>entailed_clss_inv S\<close> and
    invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of S)\<close> and
     \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state_of S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state_of T)\<close>
  using assms
  by (induction rule: cdcl_learn_clause.induct)
    (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
    cdcl\<^sub>W_restart_mset.no_smaller_confl_def cdcl\<^sub>W_restart_mset.clauses_def)


lemma pcdcl_stgy_stgy_invs:
  assumes
    confl: \<open>pcdcl_stgy S T\<close> and
    sub: \<open>psubsumed_invs S\<close> and
    ent: \<open>entailed_clss_inv S\<close> and
    invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of S)\<close> and
     \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state_of S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state_of T)\<close>
  using assms
  apply (induction rule: pcdcl_stgy.induct)
  subgoal using pcdcl_core_stgy_stgy_invs by blast
  subgoal using cdcl_learn_clause_stgy_stgy_invs by blast
  subgoal using cdcl_resolution_stgy_stgy_invs by blast
  subgoal using cdcl_subsumed_stgy_stgy_invs by blast
  subgoal by (simp add: cdcl_flush_unit_unchanged)
  done


section \<open>Higher-level rules\<close>

subsection \<open>Subsumption resolution\<close>
text \<open>

Subsumption-Resolution rules are the composition of resolution,
subsumption, learning of a clause, and potentially forget. However,
we have decided to not model the forget, because we would like to map
the calculus to a version without restarts.

\<close>

inductive cdcl_subresolution :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
subresolution_II:
  \<open>cdcl_subresolution (M, N + {#add_mset L C, add_mset (-L) C'#}, U, D, NE, UE, NS, US)
    (M, N + {#add_mset L C, remdups_mset C'#}, U, D, NE, UE, add_mset (add_mset (-L) C') NS, US)\<close>
 if  \<open>count_decided M = 0\<close> \<open>C \<subseteq># C'\<close>|
subresolution_LL:
  \<open>cdcl_subresolution (M, N, U + {#add_mset L C, add_mset (-L) C'#}, D, NE, UE, NS, US)
    (M, N, U + {#add_mset L C, remdups_mset (C')#}, D, NE, UE, NS, add_mset (add_mset (-L) C') US)\<close>
 if  \<open>count_decided M = 0\<close> and \<open>\<not>tautology (C + C')\<close> and  \<open>C \<subseteq># C'\<close>|
subresolution_LI:
  \<open>cdcl_subresolution (M, N + {#add_mset L C#}, U + {#add_mset (-L) C'#}, D, NE, UE, NS, US)
    (M, N + {#add_mset L C#}, U + {#remdups_mset (C')#}, D, NE, UE, NS,
      add_mset (add_mset (-L) C') US)\<close>
 if  \<open>count_decided M = 0\<close> and \<open>\<not>tautology (C + C')\<close> and  \<open>C \<subseteq># C'\<close>|
subresolution_IL:
  \<open>cdcl_subresolution (M, N + {#add_mset L C#}, U + {#add_mset (-L) C'#}, D, NE, UE, NS, US)
    (M, N + {#remdups_mset C#}, U + {#add_mset (-L) C', remdups_mset C#}, D, NE, UE,
      add_mset (add_mset L C) NS,  US)\<close>
 if  \<open>count_decided M = 0\<close> and \<open>\<not>tautology (C + C')\<close> and  \<open>C' \<subseteq># C\<close>


lemma cdcl_subresolution:
  assumes \<open>cdcl_subresolution S T\<close> and
    \<open>pcdcl_all_struct_invs S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of S)\<close>
  shows \<open>pcdcl\<^sup>*\<^sup>* S T\<close>
  using assms
proof  (induction rule: cdcl_subresolution.induct)
  case (subresolution_II M C C' N L U D NE UE NS US)
  then show ?case
    apply -
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule pcdcl.intros(3))
    apply (rule cdcl_resolution.resolution_II, assumption)
    apply (rule r_into_rtranclp)
    apply (rule pcdcl.intros(4))
    using cdcl_subsumed.intros(1)[of \<open>remdups_mset (C + C')\<close> \<open>add_mset (- L) C'\<close> M
      \<open>N + {#add_mset L C#}\<close> U D NE UE NS US]
    apply (auto simp add: dest!: remdups_mset_sum_subset(1)
      simp: remdups_mset_subset_add_mset add_mset_commute)
    done
next
  case (subresolution_LL M C C' N U L D NE UE NS US)
  then show ?case apply -
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule pcdcl.intros(3))
    apply (rule cdcl_resolution.resolution_LL, assumption, assumption)
    apply (rule r_into_rtranclp)
    apply (rule pcdcl.intros(4))
    using cdcl_subsumed.intros(2)[of \<open>remdups_mset (C + C')\<close> \<open>add_mset (- L) C'\<close> M N
      \<open>U + {#add_mset L C#}\<close> D NE UE NS US]
    apply (auto dest!: remdups_mset_sum_subset(1)
      simp: remdups_mset_subset_add_mset add_mset_commute)
    done
next
  case (subresolution_LI M C C' N L U D NE UE NS US)
  then show ?case apply -
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule pcdcl.intros(3))
    apply (rule cdcl_resolution.resolution_IL, assumption, assumption)
    apply (rule r_into_rtranclp)
    apply (rule pcdcl.intros(4))
    using cdcl_subsumed.intros(2)[of \<open>remdups_mset (C + C')\<close> \<open>add_mset (- L) C'\<close> M
      \<open>N  + {#add_mset L C#}\<close> \<open>U\<close> D NE UE NS US]
    apply (auto simp add: dest!: remdups_mset_sum_subset(1)
      simp: remdups_mset_subset_add_mset add_mset_commute)
    done
next
  case (subresolution_IL M C C' N L U D NE UE NS US)
  have 1: \<open>cdcl_resolution
     (M, N + {#add_mset L C#}, U + {#add_mset (- L) C'#}, D, NE, UE, NS, US)
     (M, N + {#add_mset L C#},
        U + {#add_mset (- L) C', remdups_mset (C + C')#}, D, NE, UE, NS, US)\<close>
      (is \<open>cdcl_resolution ?A ?B\<close>)
      using subresolution_IL apply -
      by (rule cdcl_resolution.resolution_IL, assumption, assumption)
  have \<open>pcdcl_all_struct_invs ?B\<close>
    using 1 pcdcl.intros(3) pcdcl_all_struct_invs subresolution_IL.prems by blast
  moreover have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of ?B)\<close>
    using cdcl_resolution_entailed_by_init[OF 1] subresolution_IL by blast
  ultimately have 2: \<open>cdcl_learn_clause
     (M, add_mset (add_mset L C) N,
      U + {#add_mset (- L) C', remdups_mset (C + C')#}, D, NE, UE, NS, US)
      (M, add_mset (remdups_mset (C + C')) (add_mset (add_mset L C) N),
      U + {#add_mset (- L) C', remdups_mset (C + C')#}, D, NE, UE, NS, US)\<close>
    apply -
    apply (rule cdcl_learn_clause.intros[of \<open>remdups_mset (C+C')\<close>])
    using subresolution_IL(1-3)
    apply (auto simp: pcdcl_all_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
       cdcl\<^sub>W_restart_mset.clauses_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def)
    by (meson in_mono lits_subseteq_imp_atms_subseteq set_mset_mono)
  show ?case using subresolution_IL apply -
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule pcdcl.intros(3)[OF 1])
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule pcdcl.intros(2))
    apply (subst add_mset_add_single[symmetric])
    apply (rule 2)
    apply (rule r_into_rtranclp)
    apply (rule pcdcl.intros(4))
    using cdcl_subsumed.intros(1)[of \<open>remdups_mset (C)\<close> \<open>add_mset L C\<close> M \<open>N\<close>
      \<open>add_mset (remdups_mset (C)) (add_mset (add_mset (- L) C') U)\<close> D NE UE NS US]
    apply (auto simp add: dest!: remdups_mset_sum_subset(2)
      simp: remdups_mset_subset_add_mset add_mset_commute)[]
    done
qed

section \<open>Variable elimination\<close>

text \<open>This is a very first attempt to definit Variable elimination in a very general way. However,
it is not clear how to handle tautologies (because the variable is not elimination in this case).\<close>
definition elim_var :: \<open>'v \<Rightarrow> 'v clauses \<Rightarrow> 'v clauses\<close> where
\<open>elim_var L N =
   {#C \<in># N. L \<notin> atms_of C#} +
   (\<lambda>(C, D). removeAll_mset (Pos L) (removeAll_mset (Neg L) (C + D))) `#
     ((filter_mset (\<lambda>C. Pos L \<in># C) N) \<times># (filter_mset (\<lambda>C. Neg L \<in># C) N))\<close>

lemma
  \<open>L \<notin> atms_of_mm (elim_var L N)\<close>
  unfolding elim_var_def
  apply (auto simp: atms_of_ms_def atms_of_def add_mset_eq_add_mset
      eq_commute[of \<open>_ - _\<close> \<open>add_mset _ _\<close>] in_diff_count
    dest!: multi_member_split)
  apply (auto dest!: union_single_eq_member
     simp: in_diff_count split: if_splits)
     using literal.exhaust_sel apply blast+
   done

 
section \<open>Bactrack for unit clause\<close>

text \<open>This is the specific case where we learn a new unit clause and directly add it to the right
 place.\<close>
inductive cdcl_backtrack_unit :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
  \<open>cdcl_backtrack_unit (M, N, U, Some (add_mset L D), NE, UE, NS, US)
  (Propagated L {#L#} # M1, N, U, None, NE, add_mset {#L#} UE, NS, US)\<close>
  if
    \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition M)\<close> and
    \<open>get_level M L = count_decided M\<close> and
    \<open>get_level M L = get_maximum_level M {#L#}\<close> and
    \<open>get_level M K = 1\<close> and
    \<open>N + U + NE + UE + NS + US \<Turnstile>pm {#L#}\<close>

lemma cdcl_backtrack_unit_is_backtrack:
  assumes \<open>cdcl_backtrack_unit S U\<close>
  obtains T where
    \<open>cdcl_backtrack S T\<close> and
    \<open>cdcl_flush_unit T U\<close>
  using assms
proof (induction rule: cdcl_backtrack_unit.induct)
  case (1 K M1 M2 M L N U NE UE NS US D) note H =this(1-5) and that = this(6)
  let ?T = \<open>(Propagated L (add_mset L {#}) # M1, N, add_mset (add_mset L {#}) U, None, NE, UE, NS, US)\<close>
  have \<open>cdcl_backtrack (M, N, U, Some (add_mset L D), NE, UE, NS, US) ?T\<close>
    apply (rule cdcl_backtrack.intros[of K M1 M2 _ _ _ 0])
    using H by auto
  moreover have \<open>cdcl_flush_unit ?T (Propagated L {#L#} # M1, N, U, None, NE, add_mset {#L#} UE, NS, US)\<close>
    by (rule cdcl_flush_unit.intros(2))
      (use H in \<open>auto dest!: get_all_ann_decomposition_exists_prepend simp: get_level_append_if
       split: if_splits\<close>)
  ultimately show ?case using that by blast
qed

lemma cdcl_backtrack_unit_pcdcl_all_struct_invs:
   \<open>cdcl_backtrack_unit S T \<Longrightarrow> pcdcl_all_struct_invs S \<Longrightarrow> pcdcl_all_struct_invs T\<close>
  by (auto elim!: cdcl_backtrack_unit_is_backtrack intro: pcdcl_all_struct_invs
    dest!: pcdcl.intros(1) pcdcl.intros(5)  pcdcl_core.intros(6))

lemma cdcl_backtrack_unit_is_CDCL_backtrack:
  \<open>cdcl_backtrack_unit S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.backtrack (state_of S) (state_of T)\<close>
  unfolding cdcl_backtrack_unit.simps
  apply clarify
  apply (rule cdcl\<^sub>W_restart_mset.backtrack.intros[of _ \<open>lit_of (hd (pget_trail T))\<close>
     \<open>the (pget_conflict S) - {#lit_of (hd (pget_trail T))#}\<close>
     _ _ _ \<open>mark_of (hd (pget_trail T)) - {#lit_of (hd (pget_trail T))#}\<close>])
  by (auto simp: clauses_def ac_simps cdcl\<^sub>W_restart_mset_reduce_trail_to)


section \<open>Termination\<close>

text \<open>

  We here define the terminating fragment of our pragmatic CDCL. Basically, there is a design
  decision to take here. Either we decide to move \<^term>\<open>cdcl_backtrack_unit\<close> into the \<^term>\<open>pcdcl_core\<close>
  or we decide to define a larger terminating fragment. The first option is easier (even if we need
  a larger core), but we want to be able to add subsumption test after backtrack and this requires
  an extension of the core anyway.

\<close>

inductive pcdcl_tcore :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> for S T :: \<open>'v prag_st\<close> where
  \<open>pcdcl_core S T \<Longrightarrow> pcdcl_tcore S T\<close> |
  \<open>cdcl_subsumed S T \<Longrightarrow> pcdcl_tcore S T\<close> |
  \<open>cdcl_flush_unit S T \<Longrightarrow> pcdcl_tcore S T\<close> |
  \<open>cdcl_backtrack_unit S T \<Longrightarrow> pcdcl_tcore S T\<close>

inductive pcdcl_tcore_stgy :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> for S T :: \<open>'v prag_st\<close> where
  \<open>pcdcl_core_stgy S T \<Longrightarrow> pcdcl_tcore_stgy S T\<close> |
  \<open>cdcl_subsumed S T \<Longrightarrow> pcdcl_tcore_stgy S T\<close>|
  \<open>cdcl_flush_unit S T \<Longrightarrow> pcdcl_tcore_stgy S T\<close> |
  \<open>cdcl_backtrack_unit S T \<Longrightarrow> pcdcl_tcore_stgy S T\<close>

lemma pcdcl_tcore_stgy_pcdcl_tcoreD: \<open>pcdcl_tcore_stgy S T \<Longrightarrow> pcdcl_tcore S T\<close>
  using pcdcl_core_stgy_pcdcl pcdcl_tcore.simps pcdcl_tcore_stgy.simps by blast

lemma rtranclp_pcdcl_tcore_stgy_pcdcl_tcoreD:
   \<open>pcdcl_tcore_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> pcdcl_tcore\<^sup>*\<^sup>* S T\<close>
  by (induction rule: rtranclp_induct) (auto dest: pcdcl_tcore_stgy_pcdcl_tcoreD)


definition pcdcl_core_measure :: \<open>_\<close> where
  \<open>pcdcl_core_measure = {(T, S). cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of S) \<and>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W (state_of S) (state_of T)} \<union>
    {(T, S). state_of S = state_of T \<and> size (pget_clauses S) > size (pget_clauses T)}\<close>

lemma wf_pcdcl_core_measure:
  \<open>wf pcdcl_core_measure\<close>
  unfolding pcdcl_core_measure_def
proof (rule wf_union_compatible)
  let ?CDCL = \<open>{(T, S). cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of S) \<and>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W (state_of S) (state_of T)}\<close>
  let ?P = \<open>{(T, S). state_of S = state_of T \<and> size (pget_clauses S) > size (pget_clauses T)}\<close>
  show \<open>wf ?CDCL\<close>
    using wf_if_measure_f[OF cdcl\<^sub>W_restart_mset.wf_cdcl\<^sub>W, of state_of]
    by auto
  show \<open>wf ?P\<close>
    by (rule wf_subset[of \<open>{(T, S). size (pget_clauses S) > size (pget_clauses T)}\<close>])
      (use wf_if_measure_f[of less_than \<open>size o pget_clauses\<close>] in auto)
  show \<open>?CDCL O ?P \<subseteq> ?CDCL\<close>
    by auto
qed


lemma pcdcl_tcore_in_pcdcl_core_measure:
  \<open>{(T, S). pcdcl_all_struct_invs S \<and> pcdcl_tcore S T} \<subseteq> pcdcl_core_measure\<close>
proof -
  have \<open>pcdcl_tcore S T \<Longrightarrow> pcdcl_all_struct_invs S \<Longrightarrow> (T, S) \<in> pcdcl_core_measure\<close> for S T
    apply (induction rule: pcdcl_tcore.induct)
    subgoal by (auto simp: pcdcl_core_measure_def pcdcl_all_struct_invs_def pcdcl_core_is_cdcl)
    subgoal by (auto simp: pcdcl_core_measure_def cdcl_subsumed.simps)
    subgoal by (auto simp: pcdcl_core_measure_def cdcl_flush_unit.simps)
    subgoal by (auto dest!: cdcl_backtrack_unit_is_CDCL_backtrack simp: pcdcl_all_struct_invs_def
       pcdcl_core_measure_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_bj_cdcl\<^sub>W_stgy cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_bj.simps
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_cdcl\<^sub>W)
    done
  then show \<open>?thesis\<close>
    by force
qed

lemmas wf_pcdcl_tcore = wf_subset[OF wf_pcdcl_core_measure pcdcl_tcore_in_pcdcl_core_measure]

lemma pcdcl_tcore_pcdcl: \<open>pcdcl_tcore S T \<Longrightarrow> pcdcl\<^sup>*\<^sup>* S T\<close>
  by (induction rule: pcdcl_tcore.induct)
   (fastforce dest: pcdcl.intros dest!: pcdcl_core.intros elim!: cdcl_backtrack_unit_is_backtrack)+

lemma pcdcl_tcore_pcdcl_all_struct_invs:
  \<open>pcdcl_tcore S T \<Longrightarrow> pcdcl_all_struct_invs S \<Longrightarrow> pcdcl_all_struct_invs T\<close>
  using cdcl_backtrack_unit_pcdcl_all_struct_invs pcdcl.intros(1) pcdcl.intros(4) pcdcl.intros(5)
    pcdcl_all_struct_invs pcdcl_tcore.simps by blast

lemma pcdcl_core_stgy_no_smaller_propa:
   \<open>pcdcl_core_stgy S T \<Longrightarrow> pcdcl_all_struct_invs S \<Longrightarrow> cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of S) \<Longrightarrow>
   cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of T)\<close>
  using pcdcl_core_stgy_is_cdcl_stgy[of S T] unfolding pcdcl_all_struct_invs_def
  by (auto dest: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_no_smaller_propa)

lemma pcdcl_stgy_no_smaller_propa:
   \<open>pcdcl_stgy S T \<Longrightarrow> pcdcl_all_struct_invs S \<Longrightarrow> cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of S) \<Longrightarrow>
   cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of T)\<close>
  apply (induction rule: pcdcl_stgy.induct)
  subgoal by (auto dest!: pcdcl_core_stgy_no_smaller_propa)
  subgoal
    by (auto simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def cdcl_learn_clause.simps)
  subgoal
    by (auto simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def cdcl_resolution.simps)
  subgoal
    by (auto simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def cdcl_subsumed.simps clauses_def)
  subgoal
    by (auto simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def cdcl_flush_unit.simps)
  done

lemma rtranclp_pcdcl_stgy_no_smaller_propa:
   \<open>pcdcl_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> pcdcl_all_struct_invs S \<Longrightarrow> cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of S) \<Longrightarrow>
   cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of T)\<close>
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for T U
    using rtranclp_pcdcl_all_struct_invs[of S T] rtranclp_pcdcl_stgy_pcdcl[of S T]
      pcdcl_stgy_no_smaller_propa[of T U] by auto
  done

lemma pcdcl_tcore_stgy_pcdcl_stgy: \<open>pcdcl_tcore_stgy S T \<Longrightarrow> pcdcl_stgy\<^sup>+\<^sup>+ S T\<close>
  apply (auto simp: pcdcl_tcore_stgy.simps pcdcl_stgy.simps)
  by (metis cdcl_backtrack_unit_is_backtrack pcdcl_core_stgy.intros(6) pcdcl_stgy.intros(1) pcdcl_stgy.intros(5) tranclp.simps)


lemma pcdcl_tcore_stgy_no_smaller_propa:
   \<open>pcdcl_tcore_stgy S T \<Longrightarrow> pcdcl_all_struct_invs S \<Longrightarrow> cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of S) \<Longrightarrow>
   cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of T)\<close>
  using pcdcl_tcore_stgy_pcdcl_stgy[of S T] rtranclp_pcdcl_stgy_no_smaller_propa[of S T]
  by (auto simp: tranclp_into_rtranclp)

lemma pcdcl_stgy_stgy_invariant:
  \<open>pcdcl_stgy S T \<Longrightarrow> pcdcl_all_struct_invs S \<Longrightarrow> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state_of S) \<Longrightarrow>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state_of T)\<close>
  using pcdcl_all_struct_invs_def pcdcl_stgy_stgy_invs by blast

lemma rtranclp_pcdcl_stgy_stgy_invariant:
  \<open>pcdcl_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> pcdcl_all_struct_invs S \<Longrightarrow> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state_of S) \<Longrightarrow>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state_of T)\<close>
  apply (induction rule: rtranclp_induct)
  apply auto[]
  by (metis (no_types, lifting) pcdcl_stgy_stgy_invariant rtranclp_pcdcl_all_struct_invs
     rtranclp_pcdcl_stgy_pcdcl)

lemma pcdcl_tcore_nocp_pcdcl_tcore_stgy:
   \<open>pcdcl_tcore S T \<Longrightarrow> no_step cdcl_propagate S \<Longrightarrow> no_step cdcl_conflict S \<Longrightarrow> pcdcl_tcore_stgy S T\<close>
  by (auto simp: pcdcl_tcore.simps pcdcl_tcore_stgy.simps pcdcl_core_stgy.simps pcdcl_core.simps)


lemma pcdcl_tcore_stgy_pcdcl_stgy': \<open>pcdcl_tcore_stgy S T \<Longrightarrow> pcdcl_stgy\<^sup>*\<^sup>* S T\<close>
  by (auto simp: pcdcl_stgy.simps pcdcl_tcore_stgy.simps 
      pcdcl_tcore_stgy.simps pcdcl_tcore_stgy_pcdcl_stgy rtranclp_unfold)

lemma rtranclp_pcdcl_tcore_stgy_pcdcl_stgy': \<open>pcdcl_tcore_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> pcdcl_stgy\<^sup>*\<^sup>* S T\<close>
  by (induction rule: rtranclp_induct) (auto dest!: pcdcl_tcore_stgy_pcdcl_stgy')


lemma pcdcl_core_stgy_conflict_non_zero_unless_level_0:
  \<open>pcdcl_core_stgy S T \<Longrightarrow> pcdcl_all_struct_invs S \<Longrightarrow>
      cdcl\<^sub>W_restart_mset.no_false_clause (state_of S) \<Longrightarrow>
      cdcl\<^sub>W_restart_mset.conflict_non_zero_unless_level_0 (state_of S) \<Longrightarrow> 
      cdcl\<^sub>W_restart_mset.conflict_non_zero_unless_level_0 (state_of T)\<close>
  using pcdcl_core_stgy_is_cdcl_stgy[of S T]
  using cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart_conflict_non_zero_unless_level_0[of \<open>state_of S\<close> \<open>state_of T\<close>]
  by (auto simp: pcdcl_all_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_cdcl\<^sub>W_restart)

lemma pcdcl_stgy_conflict_non_zero_unless_level_0:
  \<open>pcdcl_stgy S T \<Longrightarrow> pcdcl_all_struct_invs S \<Longrightarrow>
      cdcl\<^sub>W_restart_mset.no_false_clause (state_of S) \<Longrightarrow>
      cdcl\<^sub>W_restart_mset.conflict_non_zero_unless_level_0 (state_of S) \<Longrightarrow> 
      cdcl\<^sub>W_restart_mset.conflict_non_zero_unless_level_0 (state_of T)\<close>
  apply (induction rule: pcdcl_stgy.induct)
  subgoal using pcdcl_core_stgy_conflict_non_zero_unless_level_0[of S T] by fast
  subgoal
    by (auto simp: cdcl_learn_clause.simps cdcl\<^sub>W_restart_mset.conflict_non_zero_unless_level_0_def)
  subgoal
    by (auto simp: cdcl_resolution.simps cdcl\<^sub>W_restart_mset.conflict_non_zero_unless_level_0_def)
  subgoal
    by (auto simp: cdcl_subsumed.simps cdcl\<^sub>W_restart_mset.conflict_non_zero_unless_level_0_def)
  subgoal
    by (auto simp: cdcl_flush_unit.simps cdcl\<^sub>W_restart_mset.conflict_non_zero_unless_level_0_def)
  done


section \<open>Restarts\<close>

inductive pcdcl_restart :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
restart_trail:
   \<open>pcdcl_restart (M, N, U, None, NE, UE, NS, US)
        (M', N', U', None, NE + NE', UE + UE', NS, {#})\<close>
  if
    \<open>(Decided K # M', M2) \<in> set (get_all_ann_decomposition M)\<close> and
    \<open>U' + UE' \<subseteq># U\<close> and
    \<open>N = N' + NE'\<close> and
    \<open>\<forall>E\<in>#NE'+UE'. \<exists>L\<in>#E. L \<in> lits_of_l M' \<and> get_level M' L = 0\<close>
    \<open>\<forall>L E. Propagated L E \<in> set M' \<longrightarrow> E \<in># (N + U') + NE + UE + UE'\<close> |
restart_clauses:
   \<open>pcdcl_restart (M, N, U, None, NE, UE, NS, US)
      (M, N', U', None, NE + NE', UE + UE', NS, US')\<close>
  if
    \<open>U' + UE' \<subseteq># U\<close> and
    \<open>N = N' + NE'\<close> and
    \<open>\<forall>E\<in>#NE'+UE'. \<exists>L\<in>#E. L \<in> lits_of_l M \<and> get_level M L = 0\<close>
    \<open>\<forall>L E. Propagated L E \<in> set M \<longrightarrow> E \<in># (N + U') + NE + UE + UE'\<close>
    \<open>US' = {#}\<close>


inductive pcdcl_restart_only :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
restart_trail:
   \<open>pcdcl_restart_only (M, N, U, None, NE, UE, NS, US)
        (M', N, U, None, NE, UE, NS, US)\<close>
  if
    \<open>(Decided K # M', M2) \<in> set (get_all_ann_decomposition M) \<or> M = M'\<close>


(*TODO Taken from Misc*)
lemma mset_le_incr_right1: "a\<subseteq>#(b::'a multiset) \<Longrightarrow> a\<subseteq>#b+c" using mset_subset_eq_mono_add[of a b "{#}" c, simplified] .

lemma pcdcl_restart_cdcl\<^sub>W_stgy:
  fixes S V :: \<open>'v prag_st\<close>
  assumes
    \<open>pcdcl_restart S V\<close> and
    \<open>pcdcl_all_struct_invs S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state_of S)\<close> and
    \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of S)\<close>
  shows
    \<open>\<exists>T. cdcl\<^sub>W_restart_mset.restart (state_of S) T \<and> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* T (state_of V) \<and>
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart\<^sup>*\<^sup>* (state_of S) (state_of V)\<close>
  using assms
proof (induction rule: pcdcl_restart.induct)
  case (restart_trail K M' M2 M U' UE' U N N' NE' NE UE NS US)
  note decomp = this(1) and learned = this(2) and N = this(3) and
    has_true = this(4) and kept = this(5) and inv = this(6) and stgy_invs = this(7) and
    smaller_propa = this(8)
  let ?S = \<open>(M, N, U, None, NE, UE, NS, US)\<close>
  let ?T = \<open>([], N + NE + NS,  U' + UE + UE', None)\<close>
  let ?V = \<open>(M', N, U', None, NE, UE + UE', NS, {#})\<close>
  have restart: \<open>cdcl\<^sub>W_restart_mset.restart (state_of ?S) ?T\<close>
    using learned
    by (auto simp: cdcl\<^sub>W_restart_mset.restart.simps state_def clauses_def cdcl\<^sub>W_restart_mset_state
        intro: mset_le_incr_right1)
  have struct_invs:
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of ?S)\<close>
    using inv unfolding  pcdcl_all_struct_invs_def by auto

  have drop_M_M': \<open>drop (length M - length M') M = M'\<close>
    using decomp by (auto)
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ?T
      (drop (length M - length M') M, N + NE + NS,
        U' + UE + UE', None)\<close> for n
    apply (rule after_fast_restart_replay[of M \<open>N + NE + NS\<close>
          \<open>U+UE+US\<close> _
          \<open>U' + UE + UE'\<close>])
    subgoal using struct_invs by simp
    subgoal using stgy_invs by simp
    subgoal using smaller_propa by simp
    subgoal using kept unfolding drop_M_M' by (auto simp add: ac_simps)
    subgoal using learned by (auto intro: mset_le_incr_right1)
    done
  then have st: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ?T (state_of ?V)\<close>
    unfolding drop_M_M' by (simp add: ac_simps)
  moreover have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart\<^sup>*\<^sup>* (state_of ?S) (state_of ?V)\<close>
    using restart st
    by (auto dest!: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_rf.intros cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart.intros
          cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart)
  ultimately show ?case
    using restart unfolding N state_of.simps image_mset_union add.assoc state_of.simps
      add.commute[of \<open>NE'\<close>]
    by fast
next
  case (restart_clauses U' UE' U N N' NE' M NE UE US' NS US)
  note learned = this(1) and N = this(2) and has_true = this(3) and kept = this(4) and
    US = this(5) and inv = this(6) and stgy_invs = this(7) and  smaller_propa = this(8)
  let ?S = \<open>(M, N, U, None, NE, UE, NS, US) :: 'v prag_st\<close>
  let ?T = \<open>([], N + NE + NS, U' + UE + UE' + US', None)\<close>
  let ?V = \<open>(M, N, U', None, NE, UE + UE', NS, US') :: 'v prag_st\<close>
  have restart: \<open>cdcl\<^sub>W_restart_mset.restart (state_of ?S) ?T\<close>
    using learned US
    by (auto simp: cdcl\<^sub>W_restart_mset.restart.simps state_def clauses_def cdcl\<^sub>W_restart_mset_state
        intro: mset_le_incr_right1
        split: if_splits)

  have struct_invs:
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of ?S)\<close>
    using inv unfolding pcdcl_all_struct_invs_def by auto

  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ?T
      (drop (length M - length M) M, N + NE+NS,
        U' + UE+ UE'+US', None)\<close> for n
    apply (rule after_fast_restart_replay[of M \<open>N + NE+NS\<close>
           \<open>U+UE+US\<close> _
          \<open>U' + UE + UE'+US'\<close>])
    subgoal using struct_invs by simp
    subgoal using stgy_invs by simp
    subgoal using smaller_propa by simp
    subgoal using kept by (auto simp add: ac_simps)
    subgoal using learned US
      by (auto
        intro: mset_le_incr_right1
        split: if_splits)
    done
  then have st: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ?T (state_of ?V)\<close>
    by (simp add: ac_simps)
  moreover have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart\<^sup>*\<^sup>* (state_of ?S) (state_of ?V)\<close>
    using restart st
    by (auto dest!: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_rf.intros cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart.intros
          cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart)
  ultimately show ?case
    using restart unfolding N state_of.simps image_mset_union add.assoc add.commute[of \<open>NE'\<close>]
    by fast
qed

lemma pcdcl_restart_cdcl\<^sub>W:
  assumes
    \<open>pcdcl_restart S V\<close> and
    \<open>pcdcl_all_struct_invs S\<close>
  shows
    \<open>\<exists>T. cdcl\<^sub>W_restart_mset.restart (state_of S) T \<and> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W\<^sup>*\<^sup>* T (state_of V)\<close>
  using assms
proof (induction rule: pcdcl_restart.induct)
  case (restart_trail K M' M2 M U' UE' U N N' NE' NE UE NS US)
  note decomp = this(1) and learned = this(2) and N = this(3) and
    has_true = this(4) and kept = this(5) and inv = this(6)
  let ?S = \<open>(M, N, U, None, NE, UE, NS, US)\<close>
  let ?T = \<open>([], N + NE + NS, U' + UE + UE', None)\<close>
  let ?V = \<open>(M', N, U', None, NE, UE + UE', NS, {#})\<close>
  have restart: \<open>cdcl\<^sub>W_restart_mset.restart (state_of ?S) ?T\<close>
    using learned
    by (auto simp: cdcl\<^sub>W_restart_mset.restart.simps state_def clauses_def cdcl\<^sub>W_restart_mset_state
        intro: mset_le_incr_right1)
  have struct_invs:
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of ?S)\<close> 
    using inv unfolding pcdcl_all_struct_invs_def by auto
  have drop_M_M': \<open>drop (length M - length M') M = M'\<close>
    using decomp by (auto)
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W\<^sup>*\<^sup>* ?T
      (drop (length M - length M') M,  N + NE + NS,
          U' + UE+ UE', None)\<close> for n
    apply (rule after_fast_restart_replay_no_stgy[of M
      \<open>N + NE + NS\<close> \<open>U+UE+US\<close> _
          \<open>U' + UE + UE'\<close>])
    subgoal using struct_invs by simp
    subgoal using kept unfolding drop_M_M' by (auto simp add: ac_simps)
    subgoal using learned
      by (auto
        intro: mset_le_incr_right1)
    done
  then have st: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W\<^sup>*\<^sup>* ?T (state_of ?V)\<close>
    unfolding drop_M_M' by (simp add: ac_simps)
  then show ?case
    using restart by (auto simp: ac_simps N)
next
  case (restart_clauses U' UE' U N N' NE' M NE UE US' NS US)
  note learned = this(1) and N = this(2) and has_true = this(3) and kept = this(4) and
    US = this(5) and inv = this(6)
  let ?S = \<open>(M, N, U, None, NE, UE,NS, US)\<close>
  let ?T = \<open>([], N + NE + NS, U' + UE + UE' + US', None)\<close>
  let ?V = \<open>(M, N, U', None, NE, UE + UE', NS, US')\<close>
  have restart: \<open>cdcl\<^sub>W_restart_mset.restart (state_of ?S) ?T\<close>
    using learned US
    by (auto simp: cdcl\<^sub>W_restart_mset.restart.simps state_def clauses_def cdcl\<^sub>W_restart_mset_state
        intro: mset_le_incr_right1 split: if_splits)
  have struct_invs:
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of ?S)\<close> 
    using inv unfolding pcdcl_all_struct_invs_def by fast+
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W\<^sup>*\<^sup>* ?T
      (drop (length M - length M) M, N + NE + NS,
          U' + UE+ UE' + US', None)\<close> for n
    apply (rule after_fast_restart_replay_no_stgy[of M
          \<open>N + NE + NS\<close> \<open>U+ UE + US\<close> _
          \<open>U' + UE+ UE' + US'\<close>])
    subgoal using struct_invs by simp
    subgoal using kept by (auto simp add: ac_simps)
    subgoal
     using learned US by (auto
        intro: mset_le_incr_right1 split: if_splits)
    done
  then have st: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W\<^sup>*\<^sup>* ?T (state_of ?V)\<close>
    by (simp add: ac_simps)
  then show ?case
    using restart by (auto simp: ac_simps N)
qed

lemma pcdcl_restart_pcdcl_all_struct_invs:
  fixes S V :: \<open>'v prag_st\<close>
  assumes
    \<open>pcdcl_restart S V\<close> and
    \<open>pcdcl_all_struct_invs S\<close>
  shows 
    \<open>pcdcl_all_struct_invs V\<close>
  using assms pcdcl_restart_cdcl\<^sub>W[OF assms(1,2)] apply -
  apply normalize_goal+
  subgoal for T
    using cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_all_struct_inv_inv[of \<open>state_of S\<close> \<open>state_of V\<close>]
        cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_cdcl\<^sub>W_restart[of T \<open>state_of V\<close>]
        cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_cdcl\<^sub>W_restart
       converse_rtranclp_into_rtranclp[of cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart \<open>state_of S\<close> T \<open>state_of V\<close>] apply -
    apply (cases rule: pcdcl_restart.cases, assumption)
    subgoal
      using get_all_ann_decomposition_lvl0_still[of _ _ _ \<open>pget_trail S\<close>]
      apply (auto simp: pcdcl_all_struct_invs_def dest!: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_rf.restart
        cdcl\<^sub>W_restart_mset.rf)
      by (auto 7 3 simp: entailed_clss_inv_def psubsumed_invs_def dest!: multi_member_split)
    subgoal
      apply (auto simp: pcdcl_all_struct_invs_def dest!: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_rf.restart
        cdcl\<^sub>W_restart_mset.rf)
      by (auto 7 3 simp: entailed_clss_inv_def psubsumed_invs_def dest!: multi_member_split)
    done
  done

lemma pcdcl_restart_only_cdcl\<^sub>W_stgy:
  fixes S V :: \<open>'v prag_st\<close>
  assumes
    \<open>pcdcl_restart_only S V\<close> and
    \<open>pcdcl_all_struct_invs S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state_of S)\<close> and
    \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of S)\<close>
  shows
    \<open>\<exists>T. cdcl\<^sub>W_restart_mset.restart (state_of S) T \<and> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* T (state_of V) \<and>
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart\<^sup>*\<^sup>* (state_of S) (state_of V)\<close>
  using assms
proof (induction rule: pcdcl_restart_only.induct)
  case (restart_trail K M' M2 M N U NE UE NS US)
  note decomp = this(1) and inv = this(2) and stgy_invs = this(3) and
    smaller_propa = this(4)
  let ?S = \<open>(M, N, U, None, NE, UE, NS, US)\<close>
  let ?T = \<open>([], N + NE + NS,  U + UE + US, None)\<close>
  let ?V = \<open>(M', N, U, None, NE, UE, NS, US)\<close>
  have restart: \<open>cdcl\<^sub>W_restart_mset.restart (state_of ?S) ?T\<close>
    by (auto simp: cdcl\<^sub>W_restart_mset.restart.simps state_def clauses_def cdcl\<^sub>W_restart_mset_state
        intro: mset_le_incr_right1)
  have reas: \<open>cdcl\<^sub>W_restart_mset.reasons_in_clauses (state_of ?S)\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def pcdcl_all_struct_invs_def
      by auto
  have struct_invs:
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of ?S)\<close>
    using inv unfolding  pcdcl_all_struct_invs_def by auto

  have drop_M_M': \<open>drop (length M - length M') M = M'\<close>
    using decomp by (auto)
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ?T
      (drop (length M - length M') M, N + NE + NS, U + UE + US, None)\<close> for n
    apply (rule after_fast_restart_replay[of M \<open>N + NE + NS\<close>
          \<open>U+UE+US\<close> _
          \<open>U+UE+US\<close>])
    subgoal using struct_invs by simp
    subgoal using stgy_invs by simp
    subgoal using smaller_propa by simp
    subgoal using reas unfolding cdcl\<^sub>W_restart_mset.reasons_in_clauses_def
      by (auto simp: clauses_def get_all_mark_of_propagated_alt_def dest!: in_set_dropD)
    subgoal by auto
    done
  then have st: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ?T (state_of ?V)\<close>
    unfolding drop_M_M' by (simp add: ac_simps)
  moreover have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart\<^sup>*\<^sup>* (state_of ?S) (state_of ?V)\<close>
    using restart st
    by (auto dest!: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_rf.intros cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart.intros
          cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart)
  ultimately show ?case
    using restart unfolding state_of.simps image_mset_union add.assoc state_of.simps
      add.commute[of \<open>NE'\<close>]
    by fast
qed

lemma pcdcl_restart_only_cdcl\<^sub>W:
  assumes
    \<open>pcdcl_restart_only S V\<close> and
    \<open>pcdcl_all_struct_invs S\<close>
  shows
    \<open>\<exists>T. cdcl\<^sub>W_restart_mset.restart (state_of S) T \<and> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W\<^sup>*\<^sup>* T (state_of V)\<close>
  using assms
proof (induction rule: pcdcl_restart_only.induct)
  case (restart_trail K M' M2 M N U NE UE NS US)
  note decomp = this(1) and inv = this(2)
  let ?S = \<open>(M, N, U, None, NE, UE, NS, US)\<close>
  let ?T = \<open>([], N + NE + NS, U + UE + US, None)\<close>
  let ?V = \<open>(M', N, U, None, NE, UE + US, NS, {#})\<close>
  have restart: \<open>cdcl\<^sub>W_restart_mset.restart (state_of ?S) ?T\<close>
    by (auto simp: cdcl\<^sub>W_restart_mset.restart.simps state_def clauses_def cdcl\<^sub>W_restart_mset_state
        intro: mset_le_incr_right1)
  have struct_invs:
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of ?S)\<close> 
    using inv unfolding pcdcl_all_struct_invs_def by auto
  then have reas: \<open>cdcl\<^sub>W_restart_mset.reasons_in_clauses (state_of ?S)\<close>
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
      by auto
  have drop_M_M': \<open>drop (length M - length M') M = M'\<close>
    using decomp by (auto)
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W\<^sup>*\<^sup>* ?T
      (drop (length M - length M') M,  N + NE + NS,
          U + UE+ US, None)\<close> for n
    apply (rule after_fast_restart_replay_no_stgy[of M
      \<open>N + NE + NS\<close> \<open>U+UE+US\<close> _
          \<open>U + UE + US\<close>])
    subgoal using struct_invs by simp
    subgoal using reas unfolding cdcl\<^sub>W_restart_mset.reasons_in_clauses_def
      by (auto simp: clauses_def get_all_mark_of_propagated_alt_def dest!: in_set_dropD)
    subgoal by (auto intro: mset_le_incr_right1)
    done
  then have st: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W\<^sup>*\<^sup>* ?T (state_of ?V)\<close>
    unfolding drop_M_M' by (simp add: ac_simps)
  then show ?case
    using restart by (auto simp: ac_simps)
qed

lemma pcdcl_restart_only_pcdcl_all_struct_invs:
  fixes S V :: \<open>'v prag_st\<close>
  assumes
    \<open>pcdcl_restart_only S V\<close> and
    \<open>pcdcl_all_struct_invs S\<close>
  shows 
    \<open>pcdcl_all_struct_invs V\<close>
  using assms pcdcl_restart_only_cdcl\<^sub>W[OF assms] apply -
  apply normalize_goal+
  subgoal for T
    using cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_all_struct_inv_inv[of \<open>state_of S\<close> \<open>state_of V\<close>]
      cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_cdcl\<^sub>W_restart[of T \<open>state_of V\<close>]
      cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_cdcl\<^sub>W_restart
      converse_rtranclp_into_rtranclp[of cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart \<open>state_of S\<close> T \<open>state_of V\<close>] apply -
    apply (cases rule: pcdcl_restart_only.cases, assumption)
    subgoal
      using get_all_ann_decomposition_lvl0_still[of _ _ _ \<open>pget_trail S\<close>]
      apply (auto simp: pcdcl_all_struct_invs_def dest!: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_rf.restart
        cdcl\<^sub>W_restart_mset.rf)
      by (auto 7 3 simp: entailed_clss_inv_def psubsumed_invs_def dest!: multi_member_split)
    done
  done


text \<open>
TODO: rename to \<^term>\<open>full\<^sub>t\<close> or something along that line.
\<close>
definition full2 :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"full2 transf transf2 = (\<lambda>S S'. rtranclp transf S S' \<and> no_step transf2 S')"

definition pcdcl_final_state :: \<open>'v prag_st \<Rightarrow> bool\<close> where
  \<open>pcdcl_final_state S \<longleftrightarrow> no_step pcdcl_core S \<or>
     (count_decided (pget_trail S) = 0 \<and> pget_conflict S \<noteq> None)\<close>

context twl_restart_ops
begin
text \<open>
  The following definition diverges from our previous attempt... mostly because we barely used it
  anyway. The problem was that we need to stop in final states which was not covered in the previous
  form.

  The main issue is the termination of the calculus. Between two restarts we
  allow very abstract inprocessing that makes it possible to add clauses.
  However, this means that we can add the same clause over and over and that
  have reached the bound (or subsume these clauses).



work-arounds:
   - assume the clause set is distinct. You don't want that, although that probably works if
     the reduction is done in the normal order.
   - restricts rule to SR only. No clear way to extend it to vivification
   - bound the number of clauses you can learn. Still not obvious how to get termination from that.
     Reasonable in practice (take \<^term>\<open>(2::nat) ^ 128\<close> is sufficient), but you still have to make sure
     that adding teh clause one fater one does not break proof.
   - count only the new clause

      TODO: add a forget rule in \<^term>\<open>pcdcl_stgy\<close> instead of having it in restart.

      TODO: add a boolean if we have reached a final state
 \<close>

inductive pcdcl_stgy_restart :: \<open>'v prag_st \<times> nat \<times> bool \<Rightarrow> 'v prag_st \<times> nat \<times> bool \<Rightarrow> bool\<close> where
restart_step:
  \<open>pcdcl_stgy_restart (S, n, True) (V, Suc n, True)\<close>
  if
    \<open>pcdcl_tcore_stgy\<^sup>+\<^sup>+ S T\<close> and
    \<open>size (pget_all_learned_clss T) > f n + size (pget_all_learned_clss S)\<close> and
    \<open>pcdcl_restart T U\<close> and
    \<open>pcdcl_stgy\<^sup>*\<^sup>* U V\<close> and
    \<open>pget_conflict S = None\<close> |
restart_noGC_step:
  \<open>pcdcl_stgy_restart (S, n, True) (U, n, True)\<close>
  if
    \<open>pcdcl_tcore_stgy\<^sup>+\<^sup>+ S T\<close> and
    \<open>size (pget_all_learned_clss T) > size (pget_all_learned_clss S)\<close> and
    \<open>pcdcl_restart_only T U\<close> and
    \<open>pget_conflict S = None\<close> |
restart_full:
 \<open>pcdcl_stgy_restart (S, n, True) (T, n, False)\<close>
 if
    \<open>pcdcl_tcore_stgy\<^sup>+\<^sup>+ S T\<close> and
    \<open>pcdcl_final_state T\<close>

lemma (in -) pcdcl_tcore_conflict_final_state_still:
  assumes
    \<open>pcdcl_tcore S T\<close> and
    \<open>count_decided (pget_trail S) = 0 \<and> pget_conflict S \<noteq> None\<close>
    shows \<open>count_decided (pget_trail T) = 0 \<and> pget_conflict T \<noteq> None \<and>
       pget_all_learned_clss S = pget_all_learned_clss T\<close>
  using assms
  by (auto simp: pcdcl_tcore.simps pcdcl_core.simps cdcl_conflict.simps cdcl_propagate.simps
    cdcl_decide.simps cdcl_skip.simps cdcl_resolve.simps cdcl_backtrack.simps cdcl_subsumed.simps
    cdcl_backtrack_unit.simps cdcl_flush_unit.simps)


lemma (in -) rtranclp_pcdcl_tcore_conflict_final_state_still:
  assumes
    \<open>pcdcl_tcore\<^sup>*\<^sup>* S T\<close> and
    \<open>count_decided (pget_trail S) = 0 \<and> pget_conflict S \<noteq> None\<close>
  shows
    \<open>count_decided (pget_trail T) = 0 \<and> pget_conflict T \<noteq> None \<and>
    pget_all_learned_clss S = pget_all_learned_clss T\<close>
  using assms
  by (induction rule: rtranclp_induct) (auto simp: pcdcl_tcore_conflict_final_state_still)

end

lemma pcdcl_tcore_no_core_no_learned:
  assumes \<open>pcdcl_tcore S T\<close> and
    \<open>no_step pcdcl_core S\<close>
  shows \<open>pget_all_learned_clss S = pget_all_learned_clss T\<close>
  using assms
  by (cases T)
    (auto simp: pcdcl_tcore.simps cdcl_subsumed.simps cdcl_flush_unit.simps pcdcl_core.simps
      dest: pcdcl_core.intros(6) elim!:  cdcl_backtrack_unit_is_backtrack[of S])

lemma (in -) pcdcl_tcore_no_step_final_state_still:
  assumes
    \<open>pcdcl_tcore S T\<close> and
    \<open>no_step pcdcl_core S\<close>
  shows \<open>no_step pcdcl_core T\<close>
proof -
  have \<open>cdcl_subsumed S T \<or> cdcl_backtrack_unit S T \<or> cdcl_flush_unit S T\<close>
    using assms unfolding pcdcl_tcore.simps by fast
  then have dist: \<open>cdcl_subsumed S T \<or> cdcl_flush_unit S T\<close>
    using assms(2) cdcl_backtrack_unit_is_backtrack pcdcl_core.intros(6) by blast
  then have \<open>\<exists>U. cdcl_resolve T U \<Longrightarrow> \<exists>T. cdcl_resolve S T\<close>
    by (metis cdcl_flush_unit_unchanged cdcl_resolve_is_resolve resolve_is_cdcl_resolve
      state_of_cdcl_subsumed)
  moreover have \<open>\<exists>U. cdcl_skip T U \<Longrightarrow> \<exists>T. cdcl_skip S T\<close>
    using dist
    by (metis cdcl_flush_unit_unchanged cdcl_skip_is_skip skip_is_cdcl_skip
      state_of_cdcl_subsumed)
   moreover have \<open>\<exists>U. cdcl_backtrack T U \<Longrightarrow> \<exists>T. cdcl_backtrack S T\<close>
    using dist
    by (metis backtrack_is_cdcl_backtrack cdcl_backtrack_is_backtrack cdcl_flush_unit_unchanged
      state_of_cdcl_subsumed)
   moreover have \<open>\<exists>U. cdcl_conflict T U \<Longrightarrow> \<exists>T. cdcl_conflict S T\<close>
    using dist
    by (cases S)
     (auto simp: pcdcl_tcore.simps pcdcl_core.simps cdcl_conflict.simps cdcl_propagate.simps
        cdcl_decide.simps cdcl_skip.simps cdcl_resolve.simps cdcl_backtrack.simps cdcl_subsumed.simps
        cdcl_backtrack_unit.simps cdcl_flush_unit.simps)
   moreover have \<open>\<exists>U. cdcl_propagate T U \<Longrightarrow> \<exists>T. cdcl_propagate S T\<close>
    using dist
    by (cases S)
      (auto 5 3 simp: pcdcl_tcore.simps pcdcl_core.simps cdcl_conflict.simps cdcl_propagate.simps
        cdcl_decide.simps cdcl_skip.simps cdcl_resolve.simps cdcl_backtrack.simps cdcl_subsumed.simps
        cdcl_backtrack_unit.simps cdcl_flush_unit.simps)
   moreover have \<open>\<exists>U. cdcl_decide T U \<Longrightarrow> \<exists>T. cdcl_decide S T\<close>
    using dist
    by (cases S)
      (auto simp: pcdcl_tcore.simps pcdcl_core.simps cdcl_conflict.simps cdcl_propagate.simps
        cdcl_decide.simps cdcl_skip.simps cdcl_resolve.simps cdcl_backtrack.simps cdcl_subsumed.simps
        cdcl_backtrack_unit.simps cdcl_flush_unit.simps)
   ultimately have \<open>pcdcl_core T S' \<Longrightarrow> False\<close> for S'
     using assms(2) unfolding pcdcl_core.simps
     by (elim disjE) metis+
   then show ?thesis
     by blast
qed

lemma (in -) rtranclp_pcdcl_tcore_no_step_final_state_still:
  assumes
    \<open>pcdcl_tcore\<^sup>*\<^sup>* S T\<close> and
    \<open>no_step pcdcl_core S\<close>
  shows \<open>no_step pcdcl_core T\<close>
  using assms by (induction rule: rtranclp_induct) (blast dest!: pcdcl_tcore_no_step_final_state_still)+

lemma rtranclp_pcdcl_tcore_no_core_no_learned:
  assumes \<open>pcdcl_tcore\<^sup>*\<^sup>* S T\<close> and
    \<open>no_step pcdcl_core S\<close>
  shows \<open>pget_all_learned_clss S = pget_all_learned_clss T\<close>
  using assms rtranclp_pcdcl_tcore_no_step_final_state_still[OF assms]
  by (induction rule: rtranclp_induct)
    (simp_all add: pcdcl_tcore_no_core_no_learned rtranclp_pcdcl_tcore_no_step_final_state_still)


lemma no_step_pcdcl_core_stgy_pcdcl_coreD:
   \<open>no_step pcdcl_core_stgy S \<Longrightarrow> no_step pcdcl_core S\<close>
  using pcdcl_core.simps pcdcl_core_stgy.simps by blast

lemma rtranclp_pcdcl_tcore_stgy_no_core_no_learned:
  assumes \<open>pcdcl_tcore_stgy\<^sup>*\<^sup>* S T\<close> and
    \<open>no_step pcdcl_core S\<close>
  shows \<open>pget_all_learned_clss S = pget_all_learned_clss T\<close>
  using rtranclp_pcdcl_tcore_stgy_pcdcl_tcoreD[OF assms(1)] assms(2)
  by (blast intro: rtranclp_pcdcl_tcore_no_core_no_learned)

thm wf_union_compatible

inductive pcdcl_stgy_only_restart for S where
 restart_noGC_step:
  \<open>pcdcl_stgy_only_restart (S) (U)\<close>
  if
    \<open>pcdcl_tcore_stgy\<^sup>+\<^sup>+ S T\<close> and
    \<open>size (pget_all_learned_clss T) > size (pget_all_learned_clss S)\<close> and
    \<open>pcdcl_restart_only T U\<close> and
    \<open>pget_conflict S = None\<close>

lemma pcdcl_tcore_stgy_step_or_unchanged:
   \<open>pcdcl_tcore_stgy S T \<Longrightarrow> pcdcl_core_stgy\<^sup>*\<^sup>* S T \<or> state_of S = state_of T \<or>
   (\<exists>T'. cdcl_backtrack S T' \<and> state_of T' = state_of T)\<close>
  apply (induction rule: pcdcl_tcore_stgy.induct)
  apply (auto simp: state_of_cdcl_subsumed cdcl_flush_unit_unchanged)[3]
  using cdcl_backtrack_unit_is_backtrack cdcl_flush_unit_unchanged by blast

lemma pcdcl_tcore_stgy_cdcl\<^sub>W_stgy:
   \<open>pcdcl_tcore_stgy S T \<Longrightarrow> pcdcl_all_struct_invs S \<Longrightarrow>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (state_of S) (state_of T)\<close>
  using rtranclp_pcdcl_core_stgy_is_cdcl_stgy[of S T]
  apply (auto dest!: pcdcl_tcore_stgy_step_or_unchanged simp: pcdcl_all_struct_invs_def)
  by (metis pcdcl_core_stgy.intros(6) pcdcl_core_stgy_is_cdcl_stgy r_into_rtranclp
    state_of.simps)

lemma rtranclp_pcdcl_tcore_stgy_cdcl\<^sub>W_stgy:
   \<open>pcdcl_tcore_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> pcdcl_all_struct_invs S \<Longrightarrow>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (state_of S) (state_of T)\<close>
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for T U
    by (smt pcdcl_tcore_pcdcl_all_struct_invs pcdcl_tcore_stgy_cdcl\<^sub>W_stgy
      pcdcl_tcore_stgy_pcdcl_tcoreD rtranclp.rtrancl_into_rtrancl rtranclp_induct)
  done

lemma [simp]: \<open>learned_clss (state_of S) = pget_all_learned_clss S\<close>
  by (cases S) auto

lemma
  pcdcl_tcore_stgy_init_learned:
    \<open>pcdcl_tcore_stgy S T \<Longrightarrow> pget_init_learned_clss S \<subseteq># pget_init_learned_clss T\<close> and
  pcdcl_tcore_stgy_psubsumed_learned_clauses:
    \<open>pcdcl_tcore_stgy S T \<Longrightarrow> psubsumed_learned_clauses S \<subseteq># psubsumed_learned_clauses T\<close>
  by (auto simp: pcdcl_tcore_stgy.simps pcdcl_core_stgy.simps cdcl_conflict.simps
    cdcl_propagate.simps cdcl_decide.simps cdcl_backtrack_unit.simps cdcl_skip.simps
    cdcl_resolve.simps cdcl_backtrack.simps cdcl_subsumed.simps cdcl_flush_unit.simps)

lemma
  rtranclp_pcdcl_tcore_stgy_init_learned:
    \<open>pcdcl_tcore_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> pget_init_learned_clss S \<subseteq># pget_init_learned_clss T\<close> and
  rtranclp_pcdcl_tcore_stgy_psubsumed_learned_clauses:
    \<open>pcdcl_tcore_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> psubsumed_learned_clauses S \<subseteq># psubsumed_learned_clauses T\<close>
  by (induction rule: rtranclp_induct)
    (auto dest: pcdcl_tcore_stgy_init_learned pcdcl_tcore_stgy_psubsumed_learned_clauses)

lemma
  pcdcl_stgy_only_restart_init_learned:
    \<open>pcdcl_stgy_only_restart S T \<Longrightarrow> pget_init_learned_clss S \<subseteq># pget_init_learned_clss T\<close> and
  pcdcl_stgy_only_restart_psubsumed_learned_clauses:
    \<open>pcdcl_stgy_only_restart S T \<Longrightarrow> psubsumed_learned_clauses S \<subseteq># psubsumed_learned_clauses T\<close>
  by (auto simp: pcdcl_stgy_only_restart.simps pcdcl_restart_only.simps
    dest!: tranclp_into_rtranclp dest: rtranclp_pcdcl_tcore_stgy_init_learned
    rtranclp_pcdcl_tcore_stgy_psubsumed_learned_clauses)


lemma cdcl_twl_stgy_restart_new:
  assumes
    \<open>pcdcl_stgy_only_restart S U\<close> and
    invs: \<open>pcdcl_all_struct_invs S\<close> and
    propa: \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of S)\<close> and
    dist: \<open>distinct_mset (pget_learned_clss S - A)\<close>
 shows \<open>distinct_mset (pget_learned_clss U - A)\<close>
  using assms(1)
proof cases
  case (restart_noGC_step T) note st = this(1) and res = this(3)
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (state_of S) (state_of T)\<close>
    using rtranclp_pcdcl_tcore_stgy_cdcl\<^sub>W_stgy[of S T] invs st
    unfolding pcdcl_all_struct_invs_def
    by (auto dest!: tranclp_into_rtranclp)

 then have dist: \<open>distinct_mset (learned_clss (state_of T) - (A + pget_init_learned_clss S + psubsumed_learned_clauses S))\<close>
   apply (rule cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_distinct_mset_clauses_new_abs)
   subgoal using invs unfolding pcdcl_all_struct_invs_def by fast
   subgoal using propa unfolding pcdcl_all_struct_invs_def by fast
   subgoal using dist by (cases S) simp
   done
 have [simp]: \<open>pget_all_learned_clss U = pget_all_learned_clss T\<close>
   by (use res in \<open>auto simp: pcdcl_restart_only.simps\<close>)
 have \<open>distinct_mset (learned_clss (state_of U) - (A + pget_init_learned_clss U + psubsumed_learned_clauses U))\<close>
   apply (rule distinct_mset_mono[OF _ dist])
   by (simp add: assms(1) diff_le_mono2_mset pcdcl_stgy_only_restart_init_learned
     pcdcl_stgy_only_restart_psubsumed_learned_clauses subset_mset.add_mono)
 then show \<open>?thesis\<close>
   using res by (auto simp add: pcdcl_restart_only.simps)
qed


lemma pcdcl_stgy_only_restart_all_struct_invs:
  \<open>pcdcl_stgy_only_restart S T \<Longrightarrow> pcdcl_all_struct_invs S \<Longrightarrow> pcdcl_all_struct_invs T\<close>
  using pcdcl_restart_only_pcdcl_all_struct_invs[of S]
  apply (auto simp: pcdcl_stgy_only_restart.simps dest!: tranclp_into_rtranclp)
  by (metis pcdcl_restart_only_pcdcl_all_struct_invs rtranclp_pcdcl_all_struct_invs
    rtranclp_pcdcl_stgy_pcdcl rtranclp_pcdcl_tcore_stgy_pcdcl_stgy')


lemma rtranclp_pcdcl_stgy_only_restart_all_struct_invs:
  \<open>pcdcl_stgy_only_restart\<^sup>*\<^sup>* S T \<Longrightarrow> pcdcl_all_struct_invs S \<Longrightarrow>
  pcdcl_all_struct_invs T\<close>
  by (induction rule: rtranclp_induct) (auto dest!: pcdcl_stgy_only_restart_all_struct_invs)

lemma pcdcl_stgy_only_restart_no_smaller_propa:
  \<open>pcdcl_stgy_only_restart S T \<Longrightarrow> pcdcl_all_struct_invs S \<Longrightarrow> cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of S) \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of T)\<close>
  using pcdcl_restart_only_pcdcl_all_struct_invs[of S]
  apply (auto simp: pcdcl_stgy_only_restart.simps dest!: tranclp_into_rtranclp)
sledgehammer
  by (metis pcdcl_restart_only_pcdcl_all_struct_invs rtranclp_pcdcl_all_struct_invs
    rtranclp_pcdcl_stgy_pcdcl rtranclp_pcdcl_tcore_stgy_pcdcl_stgy')


lemma rtranclp_pcdcl_stgy_only_restart_no_smaller_propa:
  \<open>pcdcl_stgy_only_restart\<^sup>*\<^sup>* S T \<Longrightarrow> pcdcl_all_struct_invs S \<Longrightarrow> cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of S) \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of T)\<close>
  by (induction rule: rtranclp_induct)
    (auto dest: pcdcl_stgy_only_restart_all_struct_invs pcdcl_stgy_only_restart_no_smaller_propa)
term \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of T)\<close>
lemma rtranclp_cdcl_twl_stgy_restart_new_abs:
  assumes
    \<open>pcdcl_stgy_only_restart\<^sup>*\<^sup>* S T\<close> and
    invs: \<open>pcdcl_all_struct_invs S\<close> and
    propa: \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of S)\<close> and
    dist: \<open>distinct_mset (pget_learned_clss S - A)\<close>
  shows \<open>distinct_mset (pget_learned_clss T - A)\<close>
  using assms apply (induction)
  subgoal by auto
  subgoal for T U
    using cdcl_twl_stgy_restart_new[of T U A] rtranclp_pcdcl_stgy_only_restart_all_struct_invs[of S T]
      apply auto
      sledgehammer
    by (auto intro: cdcl_twl_stgy_restart_new rtranclp_cdcl_twl_stgy_restart_twl_struct_invs)
  done

lemma
  \<open>pcdcl_stgy_only_restart S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (state_of S) (state_of T)\<close>
  apply (induction rule: pcdcl_stgy_only_restart.induct)
  oops

lemma
  \<open>wf {(T, S :: 'v prag_st). pcdcl_all_struct_invs S \<and> pcdcl_stgy_only_restart S T}\<close>
proof (rule ccontr)
  assume \<open>\<not> ?thesis\<close>
  then obtain g :: \<open>nat \<Rightarrow> 'v prag_st\<close> where
    g: \<open>\<And>i. pcdcl_stgy_only_restart (g i) (g (Suc i))\<close> and
    inv: \<open>\<And>i. pcdcl_all_struct_invs (g i)\<close>
    unfolding wf_iff_no_infinite_down_chain by fast
  have \<open>size (pget_learned_clss (g (Suc i))) > size (pget_learned_clss (g i))\<close> for i
    using g[of i] apply (auto simp: pcdcl_stgy_only_restart.simps pcdcl_restart_only.simps)
  have W_g_h: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (state_of (g i)) (state_of (g (Suc i)))\<close> for i
    
    by (rule rtranclp_pcdcl_stgy_cdcl\<^sub>W_stgy[OF pcdcl]) (rule inv)
  have tranclp_g: \<open>pcdcl_stgy_restart\<^sup>*\<^sup>* (g 0) (g i)\<close> for i
    apply (induction i)
    subgoal by auto
    subgoal for i using g[of i] by auto
    done

  have dist_all_g:
    \<open>distinct_mset (pget_all_learned_clss (fst (g i)) - pget_all_learned_clss (fst (g 0)))\<close>
    for i
    apply (rule rtranclp_pcdcl_stgy_restart_new_abs[OF tranclp_g])
    subgoal using inv .
    subgoal by simp
    done
oops


context twl_restart
begin

theorem wf_cdcl_twl_stgy_restart:
  \<open>wf {(T, S :: 'v prag_st \<times> nat \<times> bool). pcdcl_all_struct_invs (fst S) \<and> pcdcl_stgy_restart S T}\<close>
proof (rule ccontr)
  assume \<open>\<not> ?thesis\<close>
  then obtain g :: \<open>nat \<Rightarrow> 'v prag_st \<times> nat \<times> bool\<close> where
    g: \<open>\<And>i. pcdcl_stgy_restart (g i) (g (Suc i))\<close> and
    inv: \<open>\<And>i. pcdcl_all_struct_invs (fst (g i))\<close>
    unfolding wf_iff_no_infinite_down_chain by fast

  have [simp]: \<open>NO_MATCH True c \<Longrightarrow> g i = (a, b, c) \<longleftrightarrow> g i = (a, b, True) \<and> c = True\<close> for i a b c
    using g[of i]
    by (auto simp: pcdcl_stgy_restart.simps)

  have H: False if \<open>pcdcl_final_state (fst (g i))\<close> for i
    using g[of i] that rtranclp_pcdcl_tcore_conflict_final_state_still[of \<open>fst (g i)\<close>]
    unfolding pcdcl_stgy_restart.simps pcdcl_final_state_def
    apply (elim disjE)
    subgoal
        apply normalize_goal+
        apply (simp add: tranclp_into_rtranclp)
       apply (drule tranclp_into_rtranclp)
       apply (drule rtranclp_pcdcl_tcore_stgy_no_core_no_learned)
          apply simp
          apply simp
       done
    subgoal
        apply normalize_goal+
        apply (simp add: tranclp_into_rtranclp)
        done
    subgoal
        apply normalize_goal+
        apply (simp add: tranclp_into_rtranclp)
       apply (drule tranclp_into_rtranclp)
       apply (drule rtranclp_pcdcl_tcore_stgy_no_core_no_learned)
          apply simp
          apply simp
       done
    subgoal
        apply normalize_goal+
        apply (elim disjE)
       apply (drule tranclp_into_rtranclp)
       apply (drule rtranclp_pcdcl_tcore_stgy_no_core_no_learned)
          apply (simp )
          apply simp
          apply simp
       done
    subgoal
        apply normalize_goal+
        apply (simp add: tranclp_into_rtranclp)
        done
    subgoal
        apply normalize_goal+
        apply (elim disjE)
       apply (drule tranclp_into_rtranclp)
    apply force
    apply force
      done
    done

  let ?snd = \<open>\<lambda>i. fst (snd i)\<close>
  have snd_g: \<open>?snd (g i) = i + ?snd (g 0)\<close> for i
    apply (induction i)
    subgoal by auto
    subgoal for i
      using g[of \<open>i\<close>] by (auto simp: pcdcl_stgy_restart.simps tranclp_unfold_begin
        pcdcl_final_state_def)

    done
  then have snd_g_0: \<open>\<And>i. i > 0 \<Longrightarrow> ?snd (g i) = i + ?snd (g 0)\<close>
    by blast
  have unbounded_f_g: \<open>unbounded (\<lambda>i. f (?snd (g i)))\<close>
    using f unfolding bounded_def by (metis add.commute f less_or_eq_imp_le snd_g
        not_bounded_nat_exists_larger not_le le_iff_add)

  have ex: \<open>(\<forall>i. \<exists>h h' :: 'v prag_st. P h h' (g i) (g (i+1))) \<Longrightarrow>
      (\<exists>h h' :: nat \<Rightarrow> 'v prag_st. \<forall>i. P (h i) (h' i) (g i) (g (i+1)))\<close> for P
    apply (rule exI[of _ \<open>\<lambda>i. SOME h. \<exists>h'. P h h' (g i) (g (i+1))\<close>])
    apply (rule exI[of _ \<open>\<lambda>i. SOME h'. P (SOME h. \<exists>h'. P h h' (g i) (g (i+1))) h' (g i) (g (i+1))\<close>])
    by (smt verit_sko_ex')
  let ?P = \<open>\<lambda>hi h'i gi gi1. pcdcl_tcore_stgy\<^sup>+\<^sup>+ (fst (gi)) (hi) \<and>
         (size (pget_all_learned_clss (hi)) > f (?snd (gi)) \<or>
          size (pget_all_learned_clss (hi)) > size (pget_all_learned_clss (fst (gi)))) \<and>
         pcdcl_restart (hi) (h'i) \<and>
         pcdcl_stgy\<^sup>*\<^sup>* (h'i) (fst (gi1))\<close>
  have \<open>\<exists>h h'. pcdcl_tcore_stgy\<^sup>+\<^sup>+ (fst (g i)) (h) \<and>
         (size (pget_all_learned_clss h) > f (?snd (g i)) \<or>
          size (pget_all_learned_clss h) > size (pget_all_learned_clss (fst (g i)))) \<and>
         pcdcl_restart h h' \<and>
         pcdcl_stgy\<^sup>*\<^sup>* h' (fst (g (i+1)))\<close>
    for i
    using g[of i] H[of \<open>Suc i\<close>]
    unfolding pcdcl_stgy_restart.simps full1_def Suc_eq_plus1[symmetric]
    apply (elim disjE)
    apply normalize_goal+
    apply force
    apply normalize_goal+
    apply (metis fst_conv)
    apply normalize_goal+
    apply (metis fst_conv)
    done
  then have \<open>\<forall>i. \<exists>h h'. ?P (h i) (h' i) (g i) (g (i+1))\<close>
     by meson
  from ex[of ?P]
  have ex: \<open>\<exists>h h' :: nat \<Rightarrow> 'v prag_st. \<forall>i :: nat. (pcdcl_tcore_stgy\<^sup>+\<^sup>+ (fst (g i)) (h i) \<and>
         (size (pget_all_learned_clss (h i)) > f (?snd (g i)) \<or>
          size (pget_all_learned_clss (h i)) > size (pget_all_learned_clss (fst (g i)))) \<and>
         pcdcl_restart (h i) (h' i) \<and>
         pcdcl_stgy\<^sup>*\<^sup>* (h' i) (fst (g (i+1))))\<close>
    using \<open>\<forall>i. \<exists>h h'. ?P (h i) (h' i) (g i) (g (i+1))\<close> by blast
  then obtain h h' where
    pcdcl: \<open>pcdcl_tcore_stgy\<^sup>+\<^sup>+ (fst (g i)) (h i)\<close> and
    \<open>size (pget_all_learned_clss (h i)) > f (?snd (g i)) \<or>
          size (pget_all_learned_clss (h i)) > size (pget_all_learned_clss (fst (g i)))\<close> and
    \<open>pcdcl_restart (h i) (h' i)\<close>
    \<open>pcdcl_stgy\<^sup>*\<^sup>* (h' i) (fst (g (i+1)))\<close> for i
    by blast
  obtain k where
    f_g_k: \<open>f (?snd (g k)) >
       card (simple_clss (atms_of_mm (init_clss (state_of (h 0))))) +
           size (pget_all_learned_clss (fst (g 0)))\<close>
    using not_bounded_nat_exists_larger[OF unbounded_f_g] by blast
  have pcdcl: \<open>pcdcl_tcore_stgy\<^sup>*\<^sup>* (fst (g i)) (h i)\<close> for i
    using pcdcl[of i] by auto

(*TODO: proof

Idea: we do not care about adding clauses N since we count only clauses in U!

*)
  have W_g_h: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (state_of (fst (g i))) (state_of (h i))\<close> for i
    
    by (rule rtranclp_pcdcl_stgy_cdcl\<^sub>W_stgy[OF pcdcl]) (rule inv)
  have tranclp_g: \<open>pcdcl_stgy_restart\<^sup>*\<^sup>* (g 0) (g i)\<close> for i
    apply (induction i)
    subgoal by auto
    subgoal for i using g[of i] by auto
    done

  have dist_all_g:
    \<open>distinct_mset (pget_all_learned_clss (fst (g i)) - pget_all_learned_clss (fst (g 0)))\<close>
    for i
    apply (rule rtranclp_pcdcl_stgy_restart_new_abs[OF tranclp_g])
    subgoal using inv .
    subgoal by simp
    done

  have dist_h: \<open>distinct_mset (get_all_learned_clss (h i) - get_all_learned_clss (fst (g 0)))\<close>
    (is \<open>distinct_mset (?U i)\<close>)
    for i
    unfolding learned_clss_get_all_learned_clss[symmetric]
    apply (rule cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_distinct_mset_clauses_new_abs[OF W_g_h])
    subgoal using inv[of i] unfolding pcdcl_all_struct_invs_def by fast
    subgoal using inv[of i] unfolding pcdcl_all_struct_invs_def by fast
    subgoal using dist_all_g[of i] distinct_mset_minus
      unfolding learned_clss_get_all_learned_clss by auto
    done
  have dist_diff: \<open>distinct_mset (c + (Ca + C) - ai) \<Longrightarrow>
       distinct_mset (c - ai)\<close> for c Ca C ai
    by (metis add_diff_cancel_right' cancel_ab_semigroup_add_class.diff_right_commute
        distinct_mset_minus)

  have \<open>get_all_learned_clss (fst (g (Suc i))) \<subseteq># get_all_learned_clss (h i)\<close> for i
    using res[of i] by (auto simp: pcdcl_restart.simps
        dest!: image_mset_subseteq_mono[of _ _ clause]
        intro: mset_le_incr_right1
        split: if_splits)

  have h_g: \<open>init_clss (state\<^sub>W_of (h i)) = init_clss (state\<^sub>W_of (fst (g i)))\<close> for i
    using cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_no_more_init_clss[OF W_g_h[of i]] ..

  have h_g_Suc: \<open>init_clss (state\<^sub>W_of (h i)) = init_clss (state\<^sub>W_of (fst (g (Suc i))))\<close> for i
    using res[of i] by (auto simp: pcdcl_restart.simps init_clss.simps)
  have init_g_0: \<open>init_clss (state\<^sub>W_of (fst (g i))) = init_clss (state\<^sub>W_of (fst (g 0)))\<close> for i
    apply (induction i)
    subgoal ..
    subgoal for j
      using h_g[of j] h_g_Suc[of j] by simp
    done
  then have K: \<open>init_clss (state\<^sub>W_of (h i)) = init_clss (state\<^sub>W_of (fst (g 0)))\<close> for i
    using h_g[of i] by simp

  have incl: \<open>set_mset (get_all_learned_clss (h i)) \<subseteq>
         simple_clss (atms_of_mm (init_clss (state\<^sub>W_of (h i))))\<close> for i
    unfolding learned_clss_get_all_learned_clss[symmetric]
    apply (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_new_learned_in_all_simple_clss[of \<open>state\<^sub>W_of (fst (g i))\<close>])
    subgoal by (rule rtranclp_pcdcl_stgy_cdcl\<^sub>W_stgy[OF pcdcl]) (rule inv)
    subgoal using inv[of i]  unfolding pcdcl_all_struct_invs_def by fast
    done
  have incl: \<open>set_mset (get_all_learned_clss (h i)) \<subseteq>
         simple_clss (atms_of_mm (init_clss (state\<^sub>W_of (h i))))\<close>  (is \<open>set_mset (?V i) \<subseteq> _\<close>) for i
    using incl[of i] by (cases \<open>h i\<close>) (auto dest: in_diffD)

  have incl_init: \<open>set_mset (?U i) \<subseteq> simple_clss (atms_of_mm (init_clss (state\<^sub>W_of (h i))))\<close> for i
    using incl[of i] by (auto dest: in_diffD)
  have size_U_atms: \<open>size (?U i) \<le> card (simple_clss (atms_of_mm (init_clss (state\<^sub>W_of (h i)))))\<close> for i
    apply (subst distinct_mset_size_eq_card[OF dist_h])
    apply (rule card_mono[OF _ incl_init])
    by (auto simp: simple_clss_finite)
  have S:
    \<open>size (?V i) - size (get_all_learned_clss (fst (g 0))) \<le>
      card (simple_clss (atms_of_mm (init_clss (state\<^sub>W_of (h i)))))\<close> for i
    apply (rule order.trans)
     apply (rule diff_size_le_size_Diff)
    apply (rule size_U_atms)
    done
  have S:
    \<open>size (?V i) \<le>
      card (simple_clss (atms_of_mm (init_clss (state\<^sub>W_of (h i))))) +
       size (get_all_learned_clss (fst (g 0)))\<close> for i
    using S[of i] by auto

  have H: \<open>card (simple_clss (atms_of_mm (init_clss (state\<^sub>W_of (h k))))) +
         size (get_all_learned_clss (fst (g 0))) > f (k + snd (g 0))\<close> for k
    using S[of k] size_h_g[of k] unfolding snd_g[symmetric]
    by force

  show False
    using H[of k] f_g_k unfolding snd_g[symmetric]
    unfolding K
    by linarith
qed

end

end