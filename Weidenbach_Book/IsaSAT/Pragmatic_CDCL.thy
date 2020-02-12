theory Pragmatic_CDCL
  imports CDCL.CDCL_W_Restart CDCL.CDCL_W_Abstract_State
begin


(*TODO Move*)
lemma remdups_mset_sum_subset:  \<open>C \<subseteq># C' \<Longrightarrow> remdups_mset (C + C') = remdups_mset C'\<close>
   \<open>C \<subseteq># C' \<Longrightarrow> remdups_mset (C' + C) = remdups_mset C'\<close>
  apply (metis remdups_mset_def set_mset_mono set_mset_union sup.absorb_iff2)
  by (metis add.commute le_iff_sup remdups_mset_def set_mset_mono set_mset_union)

lemma remdups_mset_subset_add_mset: \<open>remdups_mset C' \<subseteq># add_mset L C'\<close>
  by (meson distinct_mset_remdups_mset distinct_mset_subset_iff_remdups subset_mset.order_refl
    subset_mset_trans_add_mset)
(*END Move*)


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


TODO:
  \<^item> deriving unit clauses
  \<^item> model reconstruction
\<close>
type_synonym 'v prag_st =
  \<open>('v, 'v clause) ann_lits \<times> 'v clauses \<times> 'v clauses \<times>
    'v clause option \<times> 'v clauses \<times> 'v clauses \<times> 'v clauses \<times> 'v clauses\<close>


fun state\<^sub>W_of :: \<open>'v prag_st \<Rightarrow> 'v cdcl\<^sub>W_restart_mset\<close> where
\<open>state\<^sub>W_of (M, N, U, C, NE, UE, NS, US) =
  (M, N + NE + NS, U + UE + US, C)\<close>

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

lemma state\<^sub>W_of_cdcl_subsumed:
  \<open>cdcl_subsumed S T \<Longrightarrow> state\<^sub>W_of S = state\<^sub>W_of T\<close>
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

lemma cdcl_learn_clause_all_struct_inv:
  assumes
    \<open>cdcl_learn_clause S T\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S)\<close>
  shows
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of T)\<close>
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
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S)\<close>
  shows
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of T)\<close>
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
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S)\<close>
  shows
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of T)\<close>
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
  \<open>cdcl_flush_unit S T \<Longrightarrow> state\<^sub>W_of S = state\<^sub>W_of T\<close>
  by (auto simp: cdcl_flush_unit.simps)

lemma pcdcl_all_struct_inv:
  \<open>pcdcl S T \<Longrightarrow>
   cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S) \<Longrightarrow>
   cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of T)\<close>
  by (induction rule: pcdcl.induct)
    (blast intro: cdcl_resolution_all_struct_inv cdcl_subsumed_all_struct_inv
      cdcl_learn_clause_all_struct_inv cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_inv
    dest!: pcdcl_core_is_cdcl subst[OF cdcl_flush_unit_unchanged]
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_cdcl\<^sub>W_restart)+

definition pcdcl_all_struct_invs :: \<open>_\<close> where
\<open>pcdcl_all_struct_invs S \<longleftrightarrow>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S) \<and>
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
  \<open>cdcl_flush_unit S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state\<^sub>W_of S) \<Longrightarrow>
     cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state\<^sub>W_of T)\<close>
  by (auto simp: cdcl_flush_unit.simps psubsumed_invs_def entailed_clss_inv_def
    dest!: multi_member_split dest: cdcl_flush_unit_unchanged)


lemma pcdcl_entails_clss_inv:
  \<open>pcdcl S T \<Longrightarrow> entailed_clss_inv S \<Longrightarrow> entailed_clss_inv T\<close>
  by (induction rule: pcdcl.induct)
   (simp_all add: pcdcl_core_entails_clss_inv cdcl_learn_clause_entailed_clss_inv
    cdcl_resolution_entailed_clss_inv cdcl_subsumed_entailed_clss_inv
   cdcl_flush_unit_invs)


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

lemma pcdcl_all_struct_invs:
  \<open>pcdcl S T \<Longrightarrow>
   pcdcl_all_struct_invs S \<Longrightarrow>
   pcdcl_all_struct_invs T\<close>
   unfolding pcdcl_all_struct_invs_def
  by (intro conjI)
   (simp_all add: pcdcl_all_struct_inv pcdcl_entails_clss_inv
    pcdcl_psubsumed_invs)


lemma cdcl_resolution_entailed_by_init:
  assumes \<open>cdcl_resolution S T\<close> and
    \<open>pcdcl_all_struct_invs S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of T)\<close>
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
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of T)\<close>
  using assms
  by (induction rule: cdcl_subsumed.induct)
    (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def insert_commute)

lemma cdcl_learn_clause_entailed_by_init:
  assumes \<open>cdcl_learn_clause S T\<close> and
    \<open>pcdcl_all_struct_invs S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of T)\<close>
  using assms
  by (induction rule: cdcl_learn_clause.induct)
    (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def insert_commute)


lemma pcdcl_entailed_by_init:
  assumes \<open>pcdcl S T\<close> and
    \<open>pcdcl_all_struct_invs S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of T)\<close>
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
    invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S)\<close> and
     \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state\<^sub>W_of S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state\<^sub>W_of T)\<close>
  using assms
  by (meson cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_cdcl\<^sub>W_stgy_invariant pcdcl_core_stgy_is_cdcl_stgy)


lemma cdcl_subsumed_stgy_stgy_invs:
  assumes
    confl: \<open>cdcl_subsumed S T\<close> and
    sub: \<open>psubsumed_invs S\<close> and
    ent: \<open>entailed_clss_inv S\<close> and
    invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S)\<close> and
     \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state\<^sub>W_of S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state\<^sub>W_of T)\<close>
  using assms
  by (induction rule: cdcl_subsumed.induct)
    (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
    cdcl\<^sub>W_restart_mset.no_smaller_confl_def cdcl\<^sub>W_restart_mset.clauses_def)

lemma cdcl_resolution_stgy_stgy_invs:
  assumes
    confl: \<open>cdcl_resolution S T\<close> and
    sub: \<open>psubsumed_invs S\<close> and
    ent: \<open>entailed_clss_inv S\<close> and
    invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S)\<close> and
     \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state\<^sub>W_of S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state\<^sub>W_of T)\<close>
  using assms
  by (induction rule: cdcl_resolution.induct)
    (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
    cdcl\<^sub>W_restart_mset.no_smaller_confl_def cdcl\<^sub>W_restart_mset.clauses_def)


lemma cdcl_learn_clause_stgy_stgy_invs:
  assumes
    confl: \<open>cdcl_learn_clause S T\<close> and
    sub: \<open>psubsumed_invs S\<close> and
    ent: \<open>entailed_clss_inv S\<close> and
    invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S)\<close> and
     \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state\<^sub>W_of S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state\<^sub>W_of T)\<close>
  using assms
  by (induction rule: cdcl_learn_clause.induct)
    (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
    cdcl\<^sub>W_restart_mset.no_smaller_confl_def cdcl\<^sub>W_restart_mset.clauses_def)


lemma pcdcl_stgy_stgy_invs:
  assumes
    confl: \<open>pcdcl_stgy S T\<close> and
    sub: \<open>psubsumed_invs S\<close> and
    ent: \<open>entailed_clss_inv S\<close> and
    invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S)\<close> and
     \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state\<^sub>W_of S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state\<^sub>W_of T)\<close>
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
    (M, N + {#add_mset L C#}, U + {#remdups_mset (C')#}, D, NE, UE, NS, add_mset (add_mset (-L) C')  US)\<close>
 if  \<open>count_decided M = 0\<close> and \<open>\<not>tautology (C + C')\<close> and  \<open>C \<subseteq># C'\<close>|
subresolution_IL:
  \<open>cdcl_subresolution (M, N + {#add_mset L C#}, U + {#add_mset (-L) C'#}, D, NE, UE, NS, US)
    (M, N + {#remdups_mset (C)#}, U + {#add_mset (-L) C',remdups_mset (C)#}, D, NE, UE,
      add_mset (add_mset (L) C) NS,  US)\<close>
 if  \<open>count_decided M = 0\<close> and \<open>\<not>tautology (C + C')\<close> and  \<open>C' \<subseteq># C\<close>


lemma cdcl_subresolution:
  assumes \<open>cdcl_subresolution S T\<close> and
    \<open>pcdcl_all_struct_invs S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S)\<close>
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
    using "1" pcdcl.intros(3) pcdcl_all_struct_invs subresolution_IL.prems by blast
  moreover have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of ?B)\<close>
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

end