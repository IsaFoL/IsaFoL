theory Pragmatic_CDCL
  imports CDCL.CDCL_W_Restart CDCL.CDCL_W_Abstract_State Model_Reconstruction.Inprocessing_Rules
begin

(*TODO Move*)
lemma get_all_mark_of_propagated_alt_def:
   \<open>set (get_all_mark_of_propagated M) = {C. \<exists>L. Propagated L C \<in> set M}\<close>
  by (induction M rule: ann_lit_list_induct) auto

chapter \<open>Pragmatic CDCL\<close>

text \<open>Pragmatic CDCL is a calculus that connects our nice abstract CDCL and attempts to have what we
need to run it in IsaSAT.
\<close>
section \<open>Background\<close>

text \<open>

The idea of this calculus is to sit between the nice and abstract CDCL
calculus and the first step towards the more concrete TWL version. Pragmatic
is not used to mean incomplete as Jasmin Blanchette for his
HO superposition, but to mean that it is closer to the idead behind SAT
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
  clauses, it is better to add that clauses to the set of initial clauses.
  Armin Biere calls the non-subsumed initial clauses ``irredundant'',
  because they cannot be removed anymore.

  \<^enum> Variable elimination with model reconstruction at the end to find a model.
\<close>

paragraph \<open>Initial Inprocesing Version (CADE'27).\<close>
text \<open>
The ``CDCL'' operates on the non-subsumed clauses and we show that
this is enough to connect it to a CDCL that operates on all clauses.
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


To avoid adding a new component, we stored tautologies in the subsumed
components, even though we could also store them separately. Finally,
we really want to get rid of tautologies from the clause set. They
require special cases in the arena module.

\<close>


paragraph \<open>Second Version.\<close>
text \<open>

We tried various ways around model reconstruction to make it work and initially thought that it was
orthogonal to our CDCL calculus\<dots> but then we realised that it breaks invariant used by subsumption
before: We cannot park the clause in a separate component (as the subsuming clause can be deleted
later by the reconstruction calculus, we cannot assume anymore that subsumed clauses are really
subsumed by a real clause).

On the one hand, this requires changing the calculus. On the other hand, our calculus was kind of
weird in the first place anyway. So we decided to make explicit what is implicit in our calculus:
the set of valid literals. In Kissat and CaDiCaL, this set also exists implicitly (with a similar
function) and it is only the compact functions that renames variables that gets rid of eliminated
variables.

We decided against a set and went for a (finite) multiset to avoid adding an extra information about
finiteness in our invariants. To link it to our CDCL calculus, we just add this as a tautology (on
all literals) to the initial set of clauses. This however has one interesting consequence: we cannot
eliminate variables if we have only one. And there is another special case: our big tautology can
be empty if the problem is empty.

The extra set has also some further advantages: it gives a better solution to our tautology problem
(instead of keeping them stored separately, we can just delete them).


To simplify our code we considered removing the components that store the subsumed clauses. This has
one drawback however: we cannot run subsumption during CDCL anymore (which would be possible
otherwise because for our abstract CDCL our state does not change, we could only lose some
propagation power) and have to wait for the next inprocessing phase. This is useful in CaDiCaL to
subsume recently learned clauses. However, we never implemented it and did not even include it
in our core calculus so far, so we simplified the state instead (in the long-term hope that it
makes proofs easier, avoid some commutativity). Interestingly, we never proved the natural
termination that is compatible with subsumption.
\<close>


paragraph \<open>Overall.\<close>
text \<open>

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
\<close>

section \<open>Formalization\<close>

type_synonym 'v prag_st =
  \<open>('v, 'v clause) ann_lits \<times> 'v clauses \<times> 'v clauses \<times>
   'v clause option \<times> 'v clauses \<times> 'v clauses \<times> 'v clauses \<times> 'v clauses \<times>
   'v multiset\<close>

definition make_big_tautology :: \<open>'v multiset \<Rightarrow> 'v clauses\<close> where
  \<open>make_big_tautology \<A> = (if \<A> = {#} then {#} else {#poss (remdups_mset \<A>) + negs (remdups_mset \<A>)#})\<close>

lemma total_over_m_implies_make_big_tautology:
  \<open>total_over_m I (set_mset (make_big_tautology \<A>))  \<Longrightarrow> I \<Turnstile>m make_big_tautology \<A>\<close>
  apply (cases \<A>)
  apply (auto simp: true_cls_def make_big_tautology_def total_over_set_def)
  by (meson UnCI image_eqI)


lemma make_big_tautology_true_clss_cls_iff[simp]:
  \<open>(set_mset (make_big_tautology \<A>) \<union> A) \<Turnstile>p C' \<longleftrightarrow> (A) \<Turnstile>p C'\<close>
  by (smt (verit, ccfv_threshold) Un_commute sup_bot.right_neutral total_over_m_implies_make_big_tautology
    true_cls_mset_true_clss_iff(2) true_clss_clss_def true_clss_clss_generalise_true_clss_clss
    true_clss_clss_insert true_clss_cs_mono_l)
  
lemma make_big_tautology_true_clss_cls_iff_mset: \<open>make_big_tautology \<A> + N \<Turnstile>pm C \<longleftrightarrow> N \<Turnstile>pm C\<close>
  by (auto simp: )

lemma make_big_tautology_true_clss_clss_iff[simp]: \<open>make_big_tautology \<A> + N \<Turnstile>psm C \<longleftrightarrow> N \<Turnstile>psm C\<close>
  by (metis add.commute set_mset_union sup_bot.right_neutral total_over_m_implies_make_big_tautology
    total_over_m_union true_cls_mset_true_clss_iff(2) true_clss_clss_def
    true_clss_clss_generalise_true_clss_clss true_clss_clss_union_l)

lemma make_big_tautology_true_clss_cls_insert_iff[simp]:
  \<open>insert (C) (set_mset (make_big_tautology \<A>) \<union> A) \<Turnstile>p C' \<longleftrightarrow> insert (C) (A) \<Turnstile>p C'\<close>
  by (metis Un_insert_right make_big_tautology_true_clss_cls_iff)

fun state_of :: \<open>'v prag_st \<Rightarrow> 'v cdcl\<^sub>W_restart_mset\<close> where
\<open>state_of (M, N, U, C, NE, UE, N0, U0, \<A>) =
  (M, make_big_tautology \<A> + N + NE + N0, U + UE + U0, C)\<close>

declare cdcl\<^sub>W_restart_mset_state[simp]

named_theorems ptwl \<open>Theorems to simplify the state\<close>


section \<open>Conversion\<close>

fun pget_trail :: \<open>'v prag_st \<Rightarrow> ('v, 'v clause) ann_lit list\<close> where
  \<open>pget_trail (M, _, _, _, _, _, _, _) = M\<close>

fun set_conflict :: \<open>'v clause \<Rightarrow> 'v prag_st \<Rightarrow> 'v prag_st\<close> where
  \<open>set_conflict D (M, N, U, _, NE, UE, X) =
     (M, N, U, Some D, NE, UE, X)\<close>

fun pget_conflict :: \<open>'v prag_st \<Rightarrow> 'v clause option\<close> where
  \<open>pget_conflict (M, N, U, D, NE, UE, WS, Q) = D\<close>

fun pget_clauses :: \<open>'v prag_st \<Rightarrow> 'v clauses\<close> where
  \<open>pget_clauses (M, N, U, D, NE, UE, N0, U0, \<A>) = N + U\<close>

fun pget_init_clauses :: \<open>'v prag_st \<Rightarrow> 'v clauses\<close> where
  \<open>pget_init_clauses (M, N, U, D, NE, UE, N0, U0, \<A>) = N\<close>

fun punit_clss :: \<open>'v prag_st \<Rightarrow> 'v clauses\<close> where
  \<open>punit_clss (M, N, U, D, NE, UE, N0, U0, \<A>) = NE + UE\<close>

fun punit_init_clauses :: \<open>'v prag_st \<Rightarrow> 'v clauses\<close> where
  \<open>punit_init_clauses (M, N, U, D, NE, UE, N0, U0, \<A>) = NE\<close>

fun punit_clauses :: \<open>'v prag_st \<Rightarrow> 'v clauses\<close> where
  \<open>punit_clauses (M, N, U, D, NE, UE, N0, U0, \<A>) = NE + UE\<close>

fun pclauses0 :: \<open>'v prag_st \<Rightarrow> 'v clauses\<close> where
  \<open>pclauses0 (M, N, U, D, NE, UE, N0, U0, \<A>) = N0 + U0\<close>

fun pinit_clauses0 :: \<open>'v prag_st \<Rightarrow> 'v clauses\<close> where
  \<open>pinit_clauses0 (M, N, U, D, NE, UE, N0, U0, \<A>) = N0\<close>

fun plearned_clauses0 :: \<open>'v prag_st \<Rightarrow> 'v clauses\<close> where
  \<open>plearned_clauses0 (M, N, U, D, NE, UE, N0, U0, \<A>) = U0\<close>

fun pget_all_init_clss :: \<open>'v prag_st \<Rightarrow> 'v clause multiset\<close> where
  \<open>pget_all_init_clss (M, N, U, D, NE, UE, N0, U0, \<A>) = make_big_tautology \<A> + N + NE + N0\<close>

fun pget_all_init_clss_strict :: \<open>'v prag_st \<Rightarrow> 'v clause multiset\<close> where
  \<open>pget_all_init_clss_strict (M, N, U, D, NE, UE, N0, U0, \<A>) = N + NE + N0\<close>

fun pget_support_set :: \<open>'v prag_st \<Rightarrow> 'v multiset\<close> where
  \<open>pget_support_set (M, N, U, D, NE, UE, N0, U0, \<A>) = \<A>\<close>

fun pget_learned_clss :: \<open>'v prag_st \<Rightarrow> 'v clauses\<close> where
  \<open>pget_learned_clss (M, N, U, D, NE, UE, N0, U0, \<A>) = U\<close>

fun pget_init_learned_clss :: \<open>'v prag_st \<Rightarrow> 'v clauses\<close> where
  \<open>pget_init_learned_clss (_, N, U, _, _, UE, N0, U0, \<A>) = UE\<close>

fun pget_all_learned_clss :: \<open>'v prag_st \<Rightarrow> 'v clauses\<close> where
  \<open>pget_all_learned_clss (M, N, U, D, NE, UE, N0, U0, \<A>) = U + UE + U0\<close>

fun pget_all_clss :: \<open>'v prag_st \<Rightarrow> 'v clause multiset\<close> where
  \<open>pget_all_clss (M, N, U, D, NE, UE, N0, U0, \<A>) =
     make_big_tautology \<A> + N + NE + N0 + U + UE + U0\<close>

lemma [ptwl]:
  \<open>trail (state_of S) = pget_trail S\<close>
  by (solves \<open>cases S; auto\<close>)

declare ptwl[simp]


section \<open>The old rules\<close>

inductive cdcl_propagate :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
propagate:
  \<open>cdcl_propagate (M, N, U, None, NE, UE, N0, U0, \<A>)
    (Propagated L' D # M, N, U, None, NE, UE,N0, U0, \<A>)\<close>
  if
  \<open>L' \<in># D\<close> and \<open>M \<Turnstile>as CNot (remove1_mset L' D)\<close> and
  \<open>undefined_lit M L'\<close> \<open>D \<in># N + U\<close>

inductive cdcl_conflict :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
conflict:
  \<open>cdcl_conflict (M, N, U, None, NE, UE, N0, U0, \<A>)
    (M, N, U, Some D, NE, UE, N0, U0, \<A>)\<close>
  if
  \<open>M \<Turnstile>as CNot D\<close> and
  \<open>D \<in># N + U\<close>

inductive cdcl_decide :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
decide:
  \<open>cdcl_decide (M, N, U, None, NE, UE, N0, U0, \<A>)
    (Decided L' # M, N, U, None, NE, UE, N0, U0, \<A>)\<close>
  if
  \<open>undefined_lit M L'\<close> and
  \<open>atm_of L' \<in> atms_of_mm (make_big_tautology \<A> + N + NE + N0)\<close>

inductive cdcl_skip :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
skip:
  \<open>cdcl_skip (Propagated L' C # M, N, U, Some D, NE, UE, N0, U0, \<A>)
    (M, N, U, Some D, NE, UE, N0, U0, \<A>)\<close>
  if
  \<open>-L' \<notin># D\<close> and
  \<open>D \<noteq> {#}\<close>


inductive cdcl_resolve :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
resolve:
  \<open>cdcl_resolve (Propagated L' C # M, N, U, Some D, NE, UE, N0, U0)
    (M, N, U, Some (cdcl\<^sub>W_restart_mset.resolve_cls L' D C), NE, UE, N0, U0)\<close>
  if
  \<open>-L' \<in># D\<close> and
  \<open>get_maximum_level (Propagated L' C # M) (remove1_mset (-L') D) = count_decided M\<close> and
  \<open>L' \<in># C\<close>


inductive cdcl_backtrack :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
  \<open>cdcl_backtrack (M, N, U, Some (add_mset L D), NE, UE, N0, U0, \<A>)
  (Propagated L (add_mset L D') # M1, N, add_mset (add_mset L D') U, None, NE, UE, N0, U0, \<A>)\<close>
  if
    \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition M)\<close> and
    \<open>get_level M L = count_decided M\<close> and
    \<open>get_level M L = get_maximum_level M (add_mset L D')\<close> and
    \<open>get_maximum_level M D' \<equiv> i\<close> and
    \<open>get_level M K = i + 1\<close> and
    \<open>D' \<subseteq># D\<close> and
    \<open>make_big_tautology \<A> + N + U + NE + UE + N0 + U0 \<Turnstile>pm add_mset L D'\<close>

text \<open>
  Restart are already slightly restricted: we cannot remove literals
  set at level 0.
\<close>
inductive cdcl_restart :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
cdcl_restart:
  \<open>cdcl_restart (M, N, U, None, NE, UE, N0, U0)
    (M', N, U, None, NE, UE, N0, U0)\<close>
  if \<open>(M2, Decided K # M1) \<in> set (get_all_ann_decomposition M)\<close>

inductive cdcl_forget :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
cdcl_forget:
  \<open>cdcl_forget (M, N, add_mset C U, None, NE, UE, N0, U0, \<A>)
    (M', N, U, None, NE, UE, N0, U0, \<A>)\<close>
  if \<open>Propagated L C \<notin> set M\<close>

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
  \<open>cdcl_subsumed (M, N + {#C,C'#}, U, D, NE, UE, N0, U0, \<A>)
    (M, add_mset C N, U, D, NE, UE, N0, U0, \<A>)\<close>
  if \<open>C \<subseteq># C'\<close> and \<open>C' \<notin> set (get_all_mark_of_propagated M)\<close> |
subsumed_LL:
  \<open>cdcl_subsumed (M, N, U + {#C,C'#}, D, NE, UE, N0, U0, \<A>)
    (M, N, add_mset C U, D, NE, UE, N0, U0, \<A>)\<close>
  if \<open>C \<subseteq># C'\<close> and \<open>C' \<notin> set (get_all_mark_of_propagated M)\<close> |
subsumed_IL:
  \<open>cdcl_subsumed (M, add_mset C N, add_mset C' U, D, NE, UE, N0, U0, \<A>)
    (M, add_mset C N, U, D, NE, UE, N0, U0, \<A>)\<close>
  if \<open>C \<subseteq># C'\<close> and \<open>C' \<notin> set (get_all_mark_of_propagated M)\<close> 

text \<open>

Resolution requires to restart (or a very careful thinking where
the clause can be used, so for now, we require level 0). The names 'I'
and 'L' refers to 'irredundant' and 'learnt'.


We need the assumption \<^term>\<open>\<not>tautology (C + C')\<close> because learned clauses cannot
be tautologies.
\<close>


inductive cdcl_resolution :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
resolution_II:
  \<open>cdcl_resolution (M, N + {#add_mset L C, add_mset (-L) C'#}, U, D, NE, UE, N0, U0, \<A>)
    (M, N + {#add_mset L C, add_mset (-L) C', remdups_mset (C + C')#}, U, D, NE, UE, N0, U0, \<A>)\<close>
 if  \<open>count_decided M = 0\<close> |
resolution_LL:
  \<open>cdcl_resolution (M, N, U + {#add_mset L C, add_mset (-L) C'#}, D, NE, UE, N0, U0, \<A>)
    (M, N, U + {#add_mset L C, add_mset (-L) C', remdups_mset (C + C')#}, D, NE, UE, N0, U0, \<A>)\<close>
 if  \<open>count_decided M = 0\<close> and \<open>\<not>tautology (C + C')\<close> |
resolution_IL:
  \<open>cdcl_resolution (M, N + {#add_mset L C#}, U + {#add_mset (-L) C'#}, D, NE, UE, N0, U0, \<A>)
    (M, N + {#add_mset L C#}, U + {#add_mset (-L) C', remdups_mset (C + C')#}, D, NE, UE, N0, U0, \<A>)\<close>
 if  \<open>count_decided M = 0\<close> and \<open>\<not>tautology (C + C')\<close>

lemma cdcl_resolution_still_entailed:
  \<open>cdcl_resolution S T \<Longrightarrow> consistent_interp I \<Longrightarrow> I \<Turnstile>m pget_all_init_clss S \<Longrightarrow> I \<Turnstile>m pget_all_init_clss T\<close>
  apply (induction rule: cdcl_resolution.induct)
  subgoal for M N L C C' U D NE UE N0 U0 \<A>
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
  literal \<^term>\<open>A\<close> does not entail the latter. This is also why this predicate is different from
  the previous one: in \<^term>\<open>cdcl_resolution\<close> we can learn a tautology because we do not destroy models.
  This is not the case in this predicate.

  This function has nothing to with CDCL's learn: any clause can be learned by this function,
  including the empty clause.

TODO: for clauses in U, drop entailement and level test!
 \<close>
inductive cdcl_learn_clause :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
learn_clause:
  \<open>cdcl_learn_clause (M, N, U, D, NE, UE, N0, U0, \<A>)
    (M, add_mset C N, U, D, NE, UE, N0, U0, \<A>)\<close>
  if \<open>atms_of C \<subseteq> atms_of_mm (make_big_tautology \<A> +N + NE + N0)\<close> and
    \<open>make_big_tautology \<A> + N +NE + N0 \<Turnstile>pm C\<close> and
    \<open>\<not>tautology C\<close> and
    \<open>count_decided M = 0\<close> and
    \<open>distinct_mset C\<close> |
learn_clause_R:
  \<open>cdcl_learn_clause (M, N, U, D, NE, UE, N0, U0, \<A>)
    (M, N, add_mset C U, D, NE, UE, N0, U0, \<A>)\<close>
  if \<open>atms_of C \<subseteq> atms_of_mm (make_big_tautology \<A> + N + NE + N0)\<close> and
    \<open>make_big_tautology \<A> + N +NE + N0 \<Turnstile>pm C\<close> and
    \<open>\<not>tautology C\<close> and
    \<open>count_decided M = 0\<close> and
    \<open>distinct_mset C\<close> |
promote_clause:
  \<open>cdcl_learn_clause (M, N, add_mset C U, D, NE, UE, N0, U0, \<A>)
    (M, add_mset C N, U, D, NE, UE, N0, U0, \<A>)\<close>
  if \<open>\<not>tautology C\<close>

lemma cdcl_learn_clause_still_entailed:
  \<open>cdcl_learn_clause S T \<Longrightarrow> consistent_interp I \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of S) \<Longrightarrow>
  I \<Turnstile>m pget_all_init_clss S \<Longrightarrow> I \<Turnstile>m pget_all_init_clss T\<close>
  apply (induction rule: cdcl_learn_clause.induct)
  subgoal for C \<A> N NE N0 M U D UE U0
    using true_clss_cls_true_clss_true_cls[of \<open>set_mset (make_big_tautology \<A> + N+NE+N0)\<close> C I]
    by auto
  subgoal for C \<A> N NE  N0 M U D UE U0
    by auto
  subgoal
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
      dest: true_clss_cls_true_clss_true_cls)
  done

text \<open>Detection and removal of pure literals.\<close>

inductive cdcl_pure_literal_remove :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
cdcl_pure_literal_remove:
  \<open>cdcl_pure_literal_remove (M, N, U, None, NE, UE, N0, U0, \<A>)
    (Propagated L {#L#} # M, N, U, None, add_mset {#L#} NE, UE, N0, U0, \<A>)\<close>
  if \<open>-L \<notin> \<Union>(set_mset ` (set_mset N))\<close>
     \<open>atm_of L \<in> atms_of_mm (make_big_tautology \<A> +N+NE+N0)\<close>
    \<open>undefined_lit M L\<close>
    \<open>count_decided M = 0\<close>

lemma pure_literal_can_be_removed:
  assumes
    \<open>-L \<notin> \<Union>(set_mset ` (set_mset N))\<close> and
    \<open>I \<Turnstile>m N\<close>
  shows \<open>insert L (I - {-L}) \<Turnstile>m N\<close>
  using assms
  by (induction N) (auto simp: true_cls_def)

text \<open>
  Inprocessing version of propagate and conflict.

The rules are very liberal to be used as freely as possible. They are similar to their CDCL
counterpart, but do not cover exactly the same use-cases.

\<close>
inductive cdcl_inp_propagate :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
propagate:
  \<open>cdcl_inp_propagate (M, N, U, None, NE, UE, N0, U0, \<A>)
    (Propagated L' D # M, N, U, None, NE, UE, N0, U0, \<A>)\<close>
  if
  \<open>L' \<in># D\<close> and \<open>M \<Turnstile>as CNot (remove1_mset L' D)\<close> and
  \<open>undefined_lit M L'\<close> \<open>D \<in># N + U + NE + UE\<close> and
  \<open>count_decided M = 0\<close>

inductive cdcl_inp_conflict :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
conflict:
  \<open>cdcl_inp_conflict (M, N, U, None, NE, UE, N0, U0, \<A>)
    (M, N, U, Some {#}, NE, UE, N0, U0, \<A>)\<close>
  if
    \<open>make_big_tautology \<A> + N + NE + N0 \<Turnstile>pm {#}\<close> and
    \<open>count_decided M = 0\<close>

inductive cdcl_flush_unit :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
learn_unit_clause_R:
  \<open>cdcl_flush_unit (M, add_mset {#L#} N, U, D, NE, UE, N0, U0, \<A>)
    (M, N, U, D, add_mset {#L#} NE, UE, N0, U0, \<A>)\<close>
  if \<open>get_level M L = 0\<close> \<open>L \<in> lits_of_l M\<close> |
learn_unit_clause_I:
  \<open>cdcl_flush_unit (M, N, add_mset {#L#} U, D, NE, UE, N0, U0, \<A>)
    (M, N, U, D, NE, add_mset {#L#} UE, N0, U0, \<A>)\<close>
  if \<open>get_level M L = 0\<close> \<open>L \<in> lits_of_l M\<close>

inductive cdcl_unitres_true :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
  \<open>cdcl_unitres_true (M, add_mset (add_mset L C) N, U, D, NE, UE, N0, U0, \<A>)
    (M, N, U, D, add_mset (add_mset L C) NE, UE, N0, U0, \<A>)\<close>
  if \<open>get_level M L = 0\<close> \<open>L \<in> lits_of_l M\<close> |
  \<open>cdcl_unitres_true (M, N, add_mset (add_mset L C) U, D, NE, UE, N0, U0, \<A>)
    (M, N, U, D, NE, add_mset (add_mset L C) UE, N0, U0, \<A>)\<close>
  if \<open>get_level M L = 0\<close> \<open>L \<in> lits_of_l M\<close>

text \<open>Even if we don't generated tautologies in the learnt clauses, we still keep the possibility
 to remove them later\<close>
inductive cdcl_promote_false :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
  \<open>cdcl_promote_false (M, add_mset {#} N, U, D, NE, UE, N0, U0, \<A>)
    (M, N, U, Some {#}, NE, UE, add_mset {#} N0, U0, \<A>)\<close> |
  \<open>cdcl_promote_false (M, N, add_mset {#} U, D, NE, UE, N0, U0, \<A>)
    (M, N, U, Some {#}, NE, UE, N0, add_mset {#} U0, \<A>)\<close>

inductive pcdcl :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
  \<open>pcdcl_core S T \<Longrightarrow> pcdcl S T\<close> |
  \<open>cdcl_learn_clause S T \<Longrightarrow> pcdcl S T\<close> |
  \<open>cdcl_resolution S T \<Longrightarrow> pcdcl S T\<close> |
  \<open>cdcl_subsumed S T \<Longrightarrow> pcdcl S T\<close> |
  \<open>cdcl_flush_unit S T \<Longrightarrow> pcdcl S T\<close> |
  \<open>cdcl_inp_propagate S T \<Longrightarrow> pcdcl S T\<close> |
  \<open>cdcl_inp_conflict S T \<Longrightarrow> pcdcl S T\<close> |
  \<open>cdcl_unitres_true S T \<Longrightarrow> pcdcl S T\<close> |
  \<open>cdcl_promote_false S T \<Longrightarrow> pcdcl S T\<close>

inductive pcdcl_stgy :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> for S T :: \<open>'v prag_st\<close> where
  \<open>pcdcl_core_stgy S T \<Longrightarrow> pcdcl_stgy S T\<close> |
  \<open>cdcl_learn_clause S T \<Longrightarrow> pcdcl_stgy S T\<close> |
  \<open>cdcl_resolution S T \<Longrightarrow> pcdcl_stgy S T\<close> |
  \<open>cdcl_subsumed S T \<Longrightarrow> pcdcl_stgy S T\<close>|
  \<open>cdcl_flush_unit S T \<Longrightarrow> pcdcl_stgy S T\<close> |
  \<open>cdcl_inp_propagate S T \<Longrightarrow> pcdcl_stgy S T\<close> |
  \<open>cdcl_inp_conflict S T \<Longrightarrow> pcdcl_stgy S T\<close> |
  \<open>cdcl_unitres_true S T \<Longrightarrow> pcdcl_stgy S T\<close>

lemma pcdcl_core_stgy_pcdcl: \<open>pcdcl_core_stgy S T \<Longrightarrow> pcdcl_core S T\<close>
  by (auto simp: pcdcl_core.simps pcdcl_core_stgy.simps)

lemma pcdcl_stgy_pcdcl: \<open>pcdcl_stgy S T \<Longrightarrow> pcdcl S T\<close>
  by (auto simp: pcdcl.simps pcdcl_stgy.simps pcdcl_core_stgy_pcdcl)

lemma rtranclp_pcdcl_stgy_pcdcl: \<open>pcdcl_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> pcdcl\<^sup>*\<^sup>* S T\<close>
  by (induction rule: rtranclp_induct) (auto dest!: pcdcl_stgy_pcdcl)


section \<open>Model Reconstruction\<close>

fun to_mr_state :: \<open>'v prag_st \<times> 'v stackWit \<Rightarrow> 'v clauses \<times> 'v clauses \<times> 'v stackWit \<times> 'v set\<close> where
  \<open>to_mr_state ((M, N, U, D, NE, UE, N0, U0, \<A>), S) = (make_big_tautology \<A> + N + NE + N0, U + UE + U0, S, atms_of_mm (N + NE + N0 + U + UE + U0) \<union> atms_of_ms (wit_clause ` set S) \<union> set_mset \<A>)\<close>

(*
lemma
  assumes \<open>pcdcl V W\<close>
  shows \<open>inp_mr\<^sup>*\<^sup>* (to_mr_state (V, S)) (to_mr_state (W, S))\<close>
  using assms
  apply (cases rule: pcdcl.cases)
  subgoal
    sorry
    subgoal
      apply (cases rule: cdcl_learn_clause.cases, assumption)
      using inp_mr.intros(1)[of \<open>pget_all_init_clss W\<close> _ \<open>pget_all_learned_clss V\<close> S \<open>{}\<close>]
      apply auto
        oops
    apply (auto simp: pcdcl.simps cdcl_learn_clause.simps c dcl_resolution.simps
      cdcl_subsumed.simps cdcl_flush_unit.simps cdcl_inp_propagate.simps cdcl_inp_conflict.simps
      cdcl_unitres_true.simps cdcl_promote_false.simps rules.simps
      dest: multi_member_split)
      sledgehammer
  oops
*)
section \<open>Invariants\<close>

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
  \<open>entailed_clss_inv (M, N, U, D, NE, UE, N0, U0, \<A>) \<longleftrightarrow>
    (\<forall>C \<in># NE + UE.
     (\<exists>L. L \<in># C \<and> ((D = None \<or> count_decided M > 0) \<longrightarrow> (get_level M L = 0 \<and> L \<in> lits_of_l M))))\<close>

lemmas entailed_clss_inv_def = entailed_clss_inv.simps

lemmas [simp del] = entailed_clss_inv.simps

fun clauses0_inv :: \<open>'v prag_st \<Rightarrow> bool\<close> where
  \<open>clauses0_inv  (M, N, U, D, NE, UE, N0, U0, \<A>) \<longleftrightarrow> (\<forall>C \<in># N0 + U0. C = {#}) \<and>
     ({#} \<in># N0 + U0 \<longrightarrow> D = Some {#})\<close>

lemma clauses0_inv_def:
  \<open>clauses0_inv  (M, N, U, D, NE, UE, N0, U0, \<A>) \<longleftrightarrow> (\<forall>C \<in># N0 + U0. C = {#}) \<and>
     (N0 + U0 \<noteq> {#} \<longrightarrow> D = Some {#})\<close>
  by (auto dest!: multi_member_split)

lemmas [simp del] = clauses0_inv.simps


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

lemma in_make_big_tautology_not_conflict: \<open>no_dup A \<Longrightarrow> C \<in># make_big_tautology \<A> \<Longrightarrow> \<not>A \<Turnstile>as CNot C\<close>
  apply (cases \<A>)
  apply (auto simp: make_big_tautology_def CNot_def true_annots_def split: if_splits)
  apply (metis imageI no_dup_consistentD true_annot_singleton uminus_Neg)
  by (metis in_lit_of_true_annot no_dup_consistentD uminus_Neg)

lemma make_big_tautology_not_singleton: \<open>poss (remdups_mset \<A>) + negs (remdups_mset \<A>) \<noteq> {#L#}\<close>
  by (metis image_mset_is_empty_iff multi_self_add_other_not_self union_is_single)
  
lemma tautology_make_big_tautology_iff: \<open>tautology (poss (remdups_mset \<A>) + negs (remdups_mset \<A>)) \<longleftrightarrow> \<A> \<noteq> {#}\<close>
  by (cases \<open>remdups_mset \<A>\<close>) auto

lemma in_make_big_tautology_tautology_propagation_iff:
  assumes \<open>C \<in># make_big_tautology \<A>\<close>
  shows \<open>\<not>tautology (remove1_mset L C) \<longleftrightarrow> (set_mset \<A> = {atm_of L} \<and> C = {#-L, L#})\<close>
proof -
  have [simp]: \<open>atm_of L \<notin># \<A> \<Longrightarrow> remove1_mset L (poss (remdups_mset \<A>) + negs (remdups_mset \<A>)) = poss (remdups_mset \<A>) + negs (remdups_mset \<A>)\<close>
    by (metis add_diff_cancel_left' atm_iff_pos_or_neg_lit atms_of_negs atms_of_poss diff_single_trivial in_multiset_minus_notin_snd literal.exhaust_sel set_mset_remdups_mset)
  have \<A>_nempty[simp]: \<open>\<A> \<noteq> {#}\<close> and
    C: \<open>C = poss (remdups_mset \<A>) + negs (remdups_mset \<A>)\<close>
    using assms by (auto simp: make_big_tautology_def split: if_splits)
  show ?thesis
  proof -
    consider
      (LinA) \<open>atm_of L \<in># \<A>\<close> |
      (LnotinA) \<open>atm_of L \<notin># \<A>\<close>
      by blast
    then show ?thesis
    proof cases
      case LinA
      have H: \<open>tautology (remove1_mset L C)\<close> (is ?A) and
        \<open>set_mset \<A> \<noteq> {atm_of L}\<close> (is ?B) if L': \<open>L' \<in># \<A>\<close>  \<open>atm_of L \<noteq> L'\<close> for L'
      proof -
        obtain A' where A': \<open>remdups_mset \<A> = {#atm_of L, L'#} + A'\<close>
          by (metis L'(1) L'(2) LinA add_mset_add_single in_remove1_msetI insert_DiffM
            multi_member_split set_mset_remdups_mset union_commute union_mset_add_mset_right)
        then show ?A
          using assms that by (cases L) (auto simp: make_big_tautology_def tautology_add_mset split: if_splits)
        show ?B
          using A' L' by auto
      qed
      have [dest]: \<open>remdups_mset \<A> = {#x1#} \<Longrightarrow> x1 \<in># \<A>\<close> for x1
        by (metis multi_member_last set_mset_remdups_mset)
      consider
        (single) \<open>remdups_mset \<A> = {#atm_of L#}\<close> |
        (morethanone) L' where \<open>L' \<in># \<A>\<close>  \<open>atm_of L \<noteq> L'\<close>
        apply (cases \<open>\<exists>L'. L' \<in># \<A> \<and> atm_of L \<noteq> L'\<close>)
         apply blast
        by (metis LinA all_not_in_conv insertCI mk_disjoint_insert remdups_mset_def remdups_mset_singleton set_mset_single)
      then show ?thesis
        by (cases) (cases \<open>L\<close>, use C H in auto)
      next
        case LnotinA
        then show ?thesis
          using assms
          by (auto simp: make_big_tautology_def CNot_def true_annots_def
            tautology_make_big_tautology_iff split: if_splits)
      qed
    qed
qed

lemma conflict_is_cdcl_conflictD:
  assumes
    confl: \<open>cdcl\<^sub>W_restart_mset.conflict (state_of S) T\<close> and
    ent: \<open>entailed_clss_inv S\<close> and
    invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of S)\<close> and
    clss0: \<open>clauses0_inv S\<close>
  shows \<open>Ex (cdcl_conflict S)\<close>
proof -
  obtain C where
    C: \<open>C \<in># cdcl\<^sub>W_restart_mset.clauses (state_of S)\<close> and
    confl: \<open>trail (state_of S) \<Turnstile>as CNot C\<close> and
    conf: \<open>conflicting (state_of S) = None\<close> and
    \<open>T \<sim>m update_conflicting (Some C) (state_of S)\<close>
    using cdcl\<^sub>W_restart_mset.conflictE[OF confl]
    by metis

  have p0: \<open>pclauses0 S = {#}\<close>
    using clss0 conf
    by (cases S; auto 4 3 simp: entailed_clss_inv_def cdcl\<^sub>W_restart_mset_state clauses0_inv_def
        true_annots_true_cls
      dest!: multi_member_split dest: no_dup_consistentD)
  have n_d: \<open>no_dup (pget_trail S)\<close>
    using invs unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
      by simp
  then have \<open>C \<notin># punit_clauses S\<close> \<open>C \<notin># pclauses0 S\<close>
    using ent confl conf clss0
      consistent_CNot_not_tautology[of \<open>lits_of_l (pget_trail S)\<close> C] distinct_consistent_interp[OF n_d]
    by (cases S; auto 4 3 simp: entailed_clss_inv_def cdcl\<^sub>W_restart_mset_state clauses0_inv_def
        true_annots_true_cls
      dest!: multi_member_split dest: no_dup_consistentD; fail)+
  then show ?thesis
    using C confl conf n_d
    by (cases S)
     (auto simp: cdcl_conflict.simps clauses_def in_make_big_tautology_not_conflict)
qed

lemma cdcl_propagate_is_propagate:
  \<open>cdcl_propagate S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.propagate (state_of S) (state_of T)\<close>
  apply (cases rule: cdcl_propagate.cases, assumption)
  apply (rule_tac L=L' and E=D in cdcl\<^sub>W_restart_mset.propagate.intros)
  by (auto simp: clauses_def)

lemma propagate_is_cdcl_propagateD:
  assumes
    confl: \<open>cdcl\<^sub>W_restart_mset.propagate (state_of S) T\<close> and
    ent: \<open>entailed_clss_inv S\<close> and
    invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of S)\<close> and
    clss0: \<open>clauses0_inv S\<close>
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
  then have \<open>C \<notin># punit_clauses S\<close> \<open>C \<notin># pclauses0 S\<close>
    using ent confl conf LC undef clss0
      consistent_CNot_not_tautology[of \<open>lits_of_l (pget_trail S)\<close> \<open>remove1_mset L C\<close>]
      distinct_consistent_interp[OF n_d]
    by (cases S;
      auto 4 3 simp: entailed_clss_inv_def cdcl\<^sub>W_restart_mset_state clauses0_inv_def true_annots_true_cls
      tautology_add_mset
      dest!: multi_member_split dest: no_dup_consistentD in_lits_of_l_defined_litD; fail)+

  have p0: \<open>pclauses0 S = {#}\<close>
    using clss0 conf
    by (cases S; auto 4 3 simp: entailed_clss_inv_def cdcl\<^sub>W_restart_mset_state clauses0_inv_def
        true_annots_true_cls
      dest!: multi_member_split dest: no_dup_consistentD)
  have tauto: \<open>\<not> tautology (remove1_mset L C)\<close>
    using confl conf n_d ent
      consistent_CNot_not_tautology[of \<open>lits_of_l (pget_trail S)\<close> \<open>remove1_mset L C\<close>,
        OF distinct_consistent_interp]
    by (cases S)
     (auto simp: true_annots_true_cls entailed_clss_inv_def
        insert_subset_eq_iff
      dest: distinct_consistent_interp mset_subset_eqD no_dup_consistentD
      dest!: multi_member_split)
  moreover have \<open>-L \<notin># C\<close>
    using LC tauto by (metis Decided_Propagated_in_iff_in_lits_of_l confl in_CNot_implies_uminus(2) in_remove1_mset_neq uminus_not_id uminus_of_uminus_id undef)
  ultimately show ?thesis
    using C confl conf  \<open>C \<notin># punit_clauses S\<close> \<open>C \<notin># pclauses0 S\<close> undef LC
    by (cases S)
      (auto simp: cdcl_propagate.simps clauses_def cdcl_conflict.simps in_make_big_tautology_tautology_propagation_iff intro!: exI[of _ L]
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

lemma rtranclp_pcdcl_core_is_cdcl:
  \<open>pcdcl_core\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W\<^sup>*\<^sup>* (state_of S) (state_of T)\<close>
  by (induction rule: rtranclp_induct) (auto dest: pcdcl_core_is_cdcl)

lemma pcdcl_core_stgy_is_cdcl_stgy:
  assumes
    confl: \<open>pcdcl_core_stgy S T\<close> and
    ent: \<open>entailed_clss_inv S\<close> and
    invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of S)\<close> and
    clss0: \<open>clauses0_inv S\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (state_of S) (state_of T)\<close>
  using assms
  by (induction rule: pcdcl_core_stgy.induct)
   ((blast intro: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.intros cdcl_conflict_is_conflict
      cdcl_propagate_is_propagate cdcl_decide_is_decide cdcl_skip_is_skip cdcl_backtrack_is_backtrack
      cdcl_resolve_is_resolve cdcl\<^sub>W_restart_mset.resolve
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_bj_cdcl\<^sub>W_stgy
    dest: conflict_is_cdcl_conflictD propagate_is_cdcl_propagateD)+)[6]

lemma no_step_pcdcl_core_stgy_is_cdcl_stgy:
  assumes
    confl: \<open>no_step pcdcl_core_stgy S\<close> and
    ent: \<open>entailed_clss_inv S\<close> and
    clss0: \<open>clauses0_inv S\<close> and
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

lemma cdcl_resolution_entailed_clss_inv:
  \<open>cdcl_resolution S T \<Longrightarrow> entailed_clss_inv S \<Longrightarrow> entailed_clss_inv T\<close>
  by (cases rule:cdcl_resolution.cases, assumption)
    (auto simp: entailed_clss_inv_def)


lemma cdcl_pure_literal_remove_entailed_clss_inv:
  \<open>cdcl_pure_literal_remove S T \<Longrightarrow> entailed_clss_inv S \<Longrightarrow> entailed_clss_inv T\<close>
  by (cases rule:cdcl_pure_literal_remove.cases, assumption)
   (auto simp: entailed_clss_inv_def get_level_cons_if)

lemma cdcl_subsumed_entailed_clss_inv:
  \<open>cdcl_subsumed S T \<Longrightarrow> entailed_clss_inv S \<Longrightarrow> entailed_clss_inv T\<close>
  by (cases rule:cdcl_subsumed.cases, assumption)
    (auto simp: entailed_clss_inv_def)

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

(*TODO Move*)
lemma consistent_interp_poss[simp]:
  \<open>consistent_interp (Pos ` A)\<close> and
  consistent_interp_negs[simp]:
  \<open>consistent_interp (Neg ` A)\<close>
  by (auto simp: consistent_interp_def)

lemma all_decomposition_implies_remove_subsumed:
  assumes \<open>C \<subseteq># C'\<close>
  shows \<open>all_decomposition_implies (insert C' (insert C N)) M = all_decomposition_implies (insert C N) M\<close>
    (is \<open>?A = ?B\<close>)
proof -
  have ?B if ?A
    unfolding all_decomposition_implies_def
  proof (intro ballI impI)
    fix x
    assume XM: \<open>x \<in> set M\<close>
    obtain Ls seen where x: \<open>x = (Ls, seen)\<close> by (cases x)
    then have \<open>unmark_l Ls \<union> insert C' (insert C N) \<Turnstile>ps unmark_l seen\<close>
      using XM that by (auto simp: all_decomposition_implies_def)
    have \<open>unmark_l Ls \<union> insert C N \<Turnstile>ps unmark_l seen\<close>
      unfolding true_clss_clss_def
    proof (intro allI impI)
      fix I
      assume I: \<open>total_over_m I (unmark_l Ls \<union> insert C N \<union> unmark_l seen)\<close>
        \<open>consistent_interp I\<close>
        \<open>I \<Turnstile>s unmark_l Ls \<union> insert C N\<close>

      let ?I = \<open>I \<union> Pos ` {l. Pos l \<notin> I \<and> Neg l \<notin> I \<and> l \<in> atms_of C'}\<close>
      have
        \<open>total_over_m ?I (unmark_l Ls \<union> insert C' (insert C N) \<union> unmark_l seen)\<close>
        \<open>consistent_interp ?I\<close>
        \<open>?I \<Turnstile>s unmark_l Ls \<union> insert C' (insert C N)\<close>
        using I apply (auto simp: total_over_set_def total_over_m_def atms_of_def
          intro!: consistent_interp_disjoint)
        by (meson assms true_cls.entail_union true_cls_mono_leD)
      then have \<open>?I \<Turnstile>s unmark_l seen\<close>
        by (smt (verit, best) \<open>unmark_l Ls \<union> insert C' (insert C N) \<Turnstile>ps unmark_l seen\<close> true_clss_clss_def)
      then show \<open>I \<Turnstile>s unmark_l seen\<close>
        by (metis (no_types, lifting) I(1) Un_commute total_not_CNot
          \<open>consistent_interp ?I\<close> consistent_CNot_not mk_disjoint_insert sup_bot.right_neutral
          total_over_m_insert total_over_m_union true_clss_def true_clss_union_increase')
    qed
    then show \<open>case x of (Ls, seen) \<Rightarrow> unmark_l Ls \<union> insert C N \<Turnstile>ps unmark_l seen\<close>
      unfolding x by auto
  qed
  then show ?thesis
    by (auto simp: all_decomposition_implies_def)
qed

lemma true_cls_p_remove_subsumed:
  assumes \<open>C \<subseteq># C'\<close>
  shows \<open>(insert C' (insert C N)) \<Turnstile>p T \<longleftrightarrow> insert C N \<Turnstile>p T\<close>
    (is \<open>?A = ?B\<close>)
    by (smt (verit, best) assms true_cls_cls_insert_l true_cls_mono_leD true_clss_cls_def
      true_clss_cls_insert_l true_clss_cls_tautology_iff true_clss_cls_true_clss_true_cls
      true_clss_insert true_prop_true_clause)


definition proper_support_set :: \<open>'v prag_st \<Rightarrow> bool\<close> where
  \<open>proper_support_set S \<longleftrightarrow> atms_of_mm (pget_all_init_clss S) = set_mset (pget_support_set S)\<close>

lemma atms_of_mm_make_big_tautology[simp]: \<open>atms_of_mm (make_big_tautology \<A>) = set_mset \<A>\<close>
  by (auto simp: make_big_tautology_def)

lemma proper_support_set_alt_def:
  \<open>proper_support_set S \<longleftrightarrow> atms_of_mm (pget_all_init_clss_strict S) \<subseteq> set_mset (pget_support_set S)\<close>
  by (cases S) (auto simp: proper_support_set_def)

lemma cdcl_subsumed_all_struct_inv:
  assumes
    \<open>cdcl_subsumed S T\<close> and
    \<open>proper_support_set S\<close>
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of S)\<close>
  shows
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of T)\<close>
  using assms
proof (induction rule: cdcl_subsumed.induct)
  case (subsumed_II C C' M N U D NE UE N0 U0 \<A>)
  then have [simp]:
    \<open>atms_of C' \<union> set_mset \<A> = set_mset \<A>\<close>
    \<open>(atms_of C \<union> set_mset \<A>) = set_mset \<A>\<close>
    \<open>(set_mset \<A> \<union> atms_of_mm N \<union> atms_of_mm NE \<union> atms_of_mm N0) = set_mset \<A>\<close>
    by (auto simp: proper_support_set_def
      intro: all_decomposition_implies_mono)
  show ?case
    using subsumed_II
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
          cdcl\<^sub>W_restart_mset.no_strange_atm_def proper_support_set_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
          cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
          cdcl\<^sub>W_restart_mset.clauses_def true_cls_p_remove_subsumed
          cdcl\<^sub>W_restart_mset.reasons_in_clauses_def
          insert_commute[of C C'] all_decomposition_implies_remove_subsumed
      intro: all_decomposition_implies_mono)
next
  case (subsumed_LL C C' M N U D NE UE N0 U0 \<A>)
  then have [simp]:
    \<open>(set_mset \<A> \<union> atms_of_mm N \<union> atms_of_mm NE \<union> atms_of_mm N0) = set_mset \<A>\<close>
    by (auto simp: proper_support_set_def
      intro: all_decomposition_implies_mono)
  show ?case
    using subsumed_LL
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
          cdcl\<^sub>W_restart_mset.no_strange_atm_def proper_support_set_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
          cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
          cdcl\<^sub>W_restart_mset.clauses_def true_cls_p_remove_subsumed
          cdcl\<^sub>W_restart_mset.reasons_in_clauses_def
          insert_commute[of C C'] all_decomposition_implies_remove_subsumed
      intro: all_decomposition_implies_mono)
next
  case (subsumed_IL C C' M N U D NE UE N0 U0 \<A>)
  then have [simp]:
    \<open>(atms_of C \<union> set_mset \<A>) = set_mset \<A>\<close>
    \<open>(set_mset \<A> \<union> atms_of_mm N \<union> atms_of_mm NE \<union> atms_of_mm N0) = set_mset \<A>\<close>
    by (auto simp: proper_support_set_def
      intro: all_decomposition_implies_mono)
  show ?case
    using subsumed_IL
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
          cdcl\<^sub>W_restart_mset.no_strange_atm_def proper_support_set_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
          cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
          cdcl\<^sub>W_restart_mset.clauses_def true_cls_p_remove_subsumed
          cdcl\<^sub>W_restart_mset.reasons_in_clauses_def
          insert_commute[of C C'] all_decomposition_implies_remove_subsumed
      intro: all_decomposition_implies_mono)
qed


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
  subgoal for M N L C C' U D NE UE
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

lemma cdcl_pure_literal_remove_all_struct_inv:
  assumes
    \<open>cdcl_pure_literal_remove S T\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of S)\<close>
  shows
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of T)\<close>
  using assms
proof (induction rule: cdcl_pure_literal_remove.induct)
  case (cdcl_pure_literal_remove L N \<A> NE N0 M U UE U0) note IH = this(1-4) and all = this(5)
  let ?S = \<open>state_of (M, N, U, None, NE, UE, N0, U0, \<A>)\<close>
  let ?T = \<open>state_of (Propagated L {#L#} # M, N, U, None, add_mset {#L#} NE, UE, N0, U0, \<A>)\<close>
  have 1: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm ?S\<close> and
    2: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv ?S\<close> and
    3: \<open>(\<forall>s\<in>#learned_clss ?S. \<not> tautology s)\<close> and
    4: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state ?S\<close> and
    5: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting ?S\<close> and
    6: \<open>all_decomposition_implies_m (cdcl\<^sub>W_restart_mset.clauses ?S) (get_all_ann_decomposition (trail ?S))\<close> and
    7: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause ?S\<close>
    using all unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  have 1: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm ?T\<close>
    using 1 by (auto simp: cdcl\<^sub>W_restart_mset.no_strange_atm_def)
  moreover have 2: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv ?T\<close>
    using 2 IH by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def)
  moreover have 3: \<open>(\<forall>s\<in>#learned_clss ?T. \<not> tautology s)\<close>
    using 3 by auto
  moreover have 4: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state ?T\<close>
    using 4 by (auto simp: cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def)
  moreover have 5: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting ?T\<close>
    using 5 unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    by (auto simp add: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
      Cons_eq_append_conv eq_commute[of "_ @ _" "_ # _"])
  moreover {
    have \<open>all_decomposition_implies_m (cdcl\<^sub>W_restart_mset.clauses ?T) (get_all_ann_decomposition (trail ?S))\<close>
      by (rule  all_decomposition_implies_monoI[OF 6, of \<open>set_mset (cdcl\<^sub>W_restart_mset.clauses ?T)\<close>])
        (auto simp: clauses_def)
    then have 6:
      \<open>all_decomposition_implies_m (cdcl\<^sub>W_restart_mset.clauses ?T) (get_all_ann_decomposition (trail ?T))\<close>
      apply -
      by (use IH in \<open>auto intro: simp: no_decision_get_all_ann_decomposition clauses_def count_decided_0_iff\<close>)
  }
  moreover have 7: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause ?T\<close>
    using 7 by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
      cdcl\<^sub>W_restart_mset.reasons_in_clauses_def clauses_def)
  ultimately show ?case unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast
qed

lemma cdcl_flush_unit_unchanged:
  \<open>cdcl_flush_unit S T \<Longrightarrow> state_of S = state_of T\<close>
  by (auto simp: cdcl_flush_unit.simps)

lemma cdcl_inp_conflict_all_struct_inv:
  \<open>cdcl_inp_conflict S T \<Longrightarrow>
   cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of S) \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of T)\<close>
  by (auto 4 4 simp: cdcl_inp_conflict.simps
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
          cdcl\<^sub>W_restart_mset.no_strange_atm_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
          cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
          cdcl\<^sub>W_restart_mset.clauses_def
    cdcl\<^sub>W_restart_mset.reasons_in_clauses_def)

lemma cdcl_inp_propagate_is_propagate: \<open>cdcl_inp_propagate S T \<Longrightarrow>
    cdcl\<^sub>W_restart_mset.propagate (state_of S) (state_of T)\<close>
  by (force simp: cdcl_inp_propagate.simps cdcl\<^sub>W_restart_mset.propagate.simps
    clauses_def)

lemma cdcl_inp_propagate_all_struct_inv:
  \<open>cdcl_inp_propagate S T \<Longrightarrow>
   cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of S) \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of T)\<close>
  using cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.propagate'
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv
  by (blast dest!: cdcl_inp_propagate_is_propagate)

lemma cdcl_unitres_true_same:
  \<open>cdcl_unitres_true S T \<Longrightarrow> state_of S = state_of T\<close>
  by (induction rule: cdcl_unitres_true.induct) auto

lemma cdcl_promote_false_all_struct_inv:
  \<open>cdcl_promote_false S T \<Longrightarrow>
   cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of S) \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of T)\<close>
  by (auto 4 4 simp: cdcl_promote_false.simps cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
          cdcl\<^sub>W_restart_mset.no_strange_atm_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
          cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
          cdcl\<^sub>W_restart_mset.reasons_in_clauses_def
          cdcl\<^sub>W_restart_mset.clauses_def)

lemma pcdcl_all_struct_inv:
  \<open>pcdcl S T \<Longrightarrow> proper_support_set S \<Longrightarrow>
   cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of S) \<Longrightarrow>
   cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of T)\<close>
  by (induction rule: pcdcl.induct)
   (blast intro: cdcl_resolution_all_struct_inv cdcl_subsumed_all_struct_inv
    cdcl_learn_clause_all_struct_inv cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_inv
    cdcl_inp_conflict_all_struct_inv cdcl_inp_propagate_all_struct_inv
    cdcl_pure_literal_remove_all_struct_inv
    dest!:
    cdcl_unitres_true_same[THEN arg_cong[of _ _ cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv], THEN iffD1]
    cdcl_promote_false_all_struct_inv
    pcdcl_core_is_cdcl subst[OF cdcl_flush_unit_unchanged]
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_cdcl\<^sub>W_restart)+

lemma cdcl_unitres_true_entailed_clss_inv:
  \<open>cdcl_unitres_true S T \<Longrightarrow> entailed_clss_inv S \<Longrightarrow> entailed_clss_inv T\<close>
  by (induction rule: cdcl_unitres_true.induct) (auto simp: entailed_clss_inv_def)

definition pcdcl_all_struct_invs :: \<open>_\<close> where
\<open>pcdcl_all_struct_invs S \<longleftrightarrow>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of S) \<and>
  entailed_clss_inv S \<and>
  clauses0_inv S \<and>
  proper_support_set S\<close>

lemma entailed_clss_inv_Propagated:
  assumes \<open>entailed_clss_inv (M, N, U, None, NE, UE, NS, US, \<A>)\<close> and
    undef: \<open>undefined_lit M L'\<close>
  shows \<open>entailed_clss_inv (Propagated L' D # M, N, U, None, NE, UE, NS, US, \<A>)\<close>
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
  assumes \<open>entailed_clss_inv (Propagated L' D'' # M, N, U, Some D, NE, UE, NS, US, \<A>)\<close>
  shows \<open>entailed_clss_inv (M, N, U, Some D', NE, UE, NS, US, \<A>)\<close>
  using assms
  unfolding entailed_clss_inv_def
  by (auto 7 3 simp:
        get_level_cons_if atm_of_eq_atm_of
        dest!: multi_member_split[of _ NE]  multi_member_split[of _ UE]
        dest: multi_member_split
      split: if_splits)

lemma entailed_clss_inv_ConflictD: \<open>entailed_clss_inv (M, N, U, None, NE, UE, NS, US, \<A>) \<Longrightarrow>
  entailed_clss_inv (M, N, U, Some D, NE, UE, NS, US, \<A>)\<close>
  by (auto simp: entailed_clss_inv_def)

lemma entailed_clss_inv_Decided:
  assumes \<open>entailed_clss_inv (M, N, U, None, NE, UE, NS, US, \<A>)\<close> and
    undef: \<open>undefined_lit M L'\<close>
  shows \<open>entailed_clss_inv (Decided L' # M, N, U, None, NE, UE, NS, US, \<A>)\<close>
  using assms
  unfolding entailed_clss_inv_def
  by (auto 7 3 simp: entailed_clss_inv_def
        get_level_cons_if atm_of_eq_atm_of
      split: if_splits dest: in_lits_of_l_defined_litD
      dest!: multi_member_split[of _ \<open>NE\<close>] multi_member_split[of _ \<open>UE\<close>])

lemma get_all_ann_decomposition_lvl0_still:
  \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<Longrightarrow> L \<in> lits_of_l M \<Longrightarrow>
  get_level M L = 0 \<Longrightarrow> L \<in> lits_of_l M1 \<and> get_level M1 L = 0\<close>
  by (auto dest!: get_all_ann_decomposition_exists_prepend simp: get_level_append_if get_level_cons_if
      split: if_splits dest: in_lits_of_l_defined_litD)

lemma cdcl_backtrack_entailed_clss_inv:
  \<open>cdcl_backtrack S T \<Longrightarrow> entailed_clss_inv S \<Longrightarrow> entailed_clss_inv T\<close> for S T :: \<open>'v prag_st\<close>
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

lemma pcdcl_core_clauses0_inv:
  \<open>pcdcl_core S T \<Longrightarrow> clauses0_inv S \<Longrightarrow> clauses0_inv T\<close>
  by (auto simp: clauses0_inv_def pcdcl_core.simps cdcl_conflict.simps
    cdcl_propagate.simps cdcl_decide.simps cdcl_backtrack.simps
    cdcl_skip.simps cdcl_resolve.simps)

lemma cdcl_flush_unit_invs:
  \<open>cdcl_flush_unit S T \<Longrightarrow> entailed_clss_inv S \<Longrightarrow> entailed_clss_inv T\<close>
  \<open>cdcl_flush_unit S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state_of S) \<Longrightarrow>
     cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state_of T)\<close>
  \<open>cdcl_flush_unit S T \<Longrightarrow> clauses0_inv S \<Longrightarrow> clauses0_inv T\<close>
  by (auto simp: cdcl_flush_unit.simps entailed_clss_inv_def clauses0_inv_def
    dest!: multi_member_split dest: cdcl_flush_unit_unchanged)

lemma cdcl_inp_propagate_invs:
  \<open>cdcl_inp_propagate S T \<Longrightarrow> entailed_clss_inv S \<Longrightarrow> entailed_clss_inv T\<close>
  \<open>cdcl_inp_propagate S T \<Longrightarrow> clauses0_inv S \<Longrightarrow> clauses0_inv T\<close>
  using count_decided_ge_get_level[of \<open>pget_trail S\<close>]
  by (auto 5 5 simp: cdcl_inp_propagate.simps entailed_clss_inv_def clauses0_inv_def
    get_level_cons_if)

lemma cdcl_inp_conflict_invs:
  \<open>cdcl_inp_conflict S T \<Longrightarrow> entailed_clss_inv S \<Longrightarrow> entailed_clss_inv T\<close>
  \<open>cdcl_inp_conflict S T \<Longrightarrow> clauses0_inv S \<Longrightarrow> clauses0_inv T\<close>
  using count_decided_ge_get_level[of \<open>pget_trail S\<close>]
  by (auto 5 5 simp: cdcl_inp_conflict.simps entailed_clss_inv_def
    get_level_cons_if clauses0_inv_def)

lemma cdcl_promote_false_invs:
  \<open>cdcl_promote_false S T \<Longrightarrow> entailed_clss_inv S \<Longrightarrow> entailed_clss_inv T\<close>
  \<open>cdcl_promote_false S T \<Longrightarrow> clauses0_inv S \<Longrightarrow> clauses0_inv T\<close>
  using count_decided_ge_get_level[of \<open>pget_trail S\<close>]
  by (auto 4 4 simp: cdcl_promote_false.simps entailed_clss_inv_def
    get_level_cons_if clauses0_inv_def dest!: multi_member_split)

lemma pcdcl_entails_clss_inv:
  \<open>pcdcl S T \<Longrightarrow> entailed_clss_inv S \<Longrightarrow> entailed_clss_inv T\<close>
  by (induction rule: pcdcl.induct)
   (simp_all add: pcdcl_core_entails_clss_inv cdcl_learn_clause_entailed_clss_inv
    cdcl_resolution_entailed_clss_inv cdcl_subsumed_entailed_clss_inv
    cdcl_pure_literal_remove_entailed_clss_inv
    cdcl_flush_unit_invs cdcl_inp_propagate_invs cdcl_inp_conflict_invs
    cdcl_unitres_true_entailed_clss_inv cdcl_promote_false_invs)

lemma rtranclp_pcdcl_entails_clss_inv:
  \<open>pcdcl\<^sup>*\<^sup>* S T \<Longrightarrow> entailed_clss_inv S \<Longrightarrow> entailed_clss_inv T\<close>
  by (induction rule: rtranclp_induct)
    (simp_all add: pcdcl_entails_clss_inv)

lemma pcdcl_clauses0_inv:
  \<open>pcdcl S T \<Longrightarrow> clauses0_inv S \<Longrightarrow> clauses0_inv T\<close>
  by (induction rule: pcdcl.induct)
    (auto simp add: cdcl_flush_unit_invs cdcl_pure_literal_remove.simps
    cdcl_inp_propagate_invs cdcl_inp_conflict_invs pcdcl_core_clauses0_inv
    cdcl_learn_clause.simps clauses0_inv_def cdcl_resolution.simps cdcl_subsumed.simps
    cdcl_unitres_true.simps cdcl_promote_false.simps)

lemma rtranclp_pcdcl_clauses0_inv:
  \<open>pcdcl\<^sup>*\<^sup>* S T \<Longrightarrow> clauses0_inv S \<Longrightarrow> clauses0_inv T\<close>
  by (induction rule: rtranclp_induct)
    (simp_all add: pcdcl_clauses0_inv)

lemma rtranclp_pcdcl_core_stgy_pcdcl: \<open>pcdcl_core_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> pcdcl\<^sup>*\<^sup>* S T\<close>
  apply (induction rule: rtranclp_induct)
  apply (simp add: pcdcl_core_stgy_pcdcl)
  by (metis (no_types, opaque_lifting) converse_rtranclp_into_rtranclp pcdcl.intros(1)
    pcdcl_core_stgy_pcdcl r_into_rtranclp rtranclp_idemp)

lemma rtranclp_pcdcl_core_stgy_is_cdcl_stgy:
  assumes
    confl: \<open>pcdcl_core_stgy\<^sup>*\<^sup>* S T\<close> and
    ent: \<open>entailed_clss_inv S\<close> and
    invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of S)\<close> and
    \<open>clauses0_inv S\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (state_of S) (state_of T)\<close>
  using assms apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for T U
    using rtranclp_pcdcl_core_stgy_pcdcl[of S T]
      rtranclp_pcdcl_entails_clss_inv[of S T] pcdcl_core_stgy_is_cdcl_stgy[of T U]
      rtranclp_pcdcl_clauses0_inv[of S T]
    by (auto simp add: cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv)
  done

lemma pcdcl_proper_support_set_and_unchanged:
  assumes \<open>pcdcl S T\<close>  and \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of S)\<close> and  \<open>proper_support_set S\<close>
  shows \<open>proper_support_set T \<and> set_mset (pget_support_set S) = set_mset (pget_support_set T)\<close>
proof -
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of T)\<close>
    using assms(1) assms(2) assms(3) pcdcl_all_struct_inv by blast
  have \<open>atms_of_mm (pget_all_learned_clss S) \<subseteq> atms_of_mm (pget_all_init_clss S)\<close>
    using assms(2) unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.no_strange_atm_def
    by (cases S; auto)
  then show ?thesis
    using assms(1,3)
    by (auto simp: pcdcl.simps pcdcl_core.simps proper_support_set_def
      cdcl_conflict.simps cdcl_propagate.simps cdcl_decide.simps cdcl_skip.simps cdcl_resolve.simps
      cdcl_backtrack.simps cdcl_learn_clause.simps cdcl_resolution.simps cdcl_subsumed.simps
      cdcl_flush_unit.simps cdcl_inp_propagate.simps cdcl_inp_conflict.simps cdcl_unitres_true.simps
      cdcl_promote_false.simps eq_commute[of \<open>_ \<union> _\<close> \<open>set_mset _\<close>])
qed

 
lemma rtranclp_pcdcl_proper_support_set_and_unchanged:
  assumes \<open>pcdcl\<^sup>*\<^sup>* S T\<close>  and \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of S)\<close> and  \<open>proper_support_set S\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of T) \<and> proper_support_set T \<and> set_mset (pget_support_set S) = set_mset (pget_support_set T)\<close>
  using assms apply (induction rule: rtranclp_induct)
  subgoal by simp
  subgoal for T U
    using pcdcl_proper_support_set_and_unchanged[of T U] pcdcl_all_struct_inv[of T U] by simp
  done

lemma pcdcl_all_struct_invs:
  \<open>pcdcl S T \<Longrightarrow> pcdcl_all_struct_invs S \<Longrightarrow> pcdcl_all_struct_invs T\<close>
  using pcdcl_proper_support_set_and_unchanged[of S T]
  unfolding pcdcl_all_struct_invs_def
  by (intro conjI)
   (simp_all add: pcdcl_all_struct_inv pcdcl_entails_clss_inv
      pcdcl_clauses0_inv)

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

lemma cdcl_pure_literal_remove_entailed_by_init:
  assumes \<open>cdcl_pure_literal_remove S T\<close> and
    \<open>pcdcl_all_struct_invs S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of T)\<close>
  using assms
  by (induction rule: cdcl_pure_literal_remove.induct)
   (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def)

lemma true_clss_ps_remove_subsumed:
  assumes \<open>C \<subseteq># C'\<close>
  shows \<open>(insert C' (insert C N)) \<Turnstile>ps T \<longleftrightarrow> insert C N \<Turnstile>ps T\<close>
  by (smt (verit, best) assms sup_bot_left true_cls_p_remove_subsumed
    true_clss_clss_generalise_true_clss_clss true_clss_clss_insert union_trus_clss_clss)

lemma cdcl_subsumed_entailed_by_init:
  assumes \<open>cdcl_subsumed S T\<close> and
    \<open>pcdcl_all_struct_invs S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of T)\<close>
  using assms
  apply (induction rule: cdcl_subsumed.induct)
  apply (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def insert_commute
    true_clss_ps_remove_subsumed insert_commute)
  apply (metis insert_commute true_clss_clss_insert_l true_clss_ps_remove_subsumed)
  apply (metis insert_commute true_clss_clss_insert_l true_clss_ps_remove_subsumed)
  apply (metis insert_commute true_clss_clss_insert_l true_clss_ps_remove_subsumed)
  done

lemma cdcl_learn_clause_entailed_by_init:
  assumes \<open>cdcl_learn_clause S T\<close> and
    \<open>pcdcl_all_struct_invs S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of T)\<close>
  using assms
  by (induction rule: cdcl_learn_clause.induct)
    (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def insert_commute)

lemma cdcl_inp_propagate_entailed_by_init:
  assumes \<open>cdcl_inp_propagate S T\<close> and
    \<open>pcdcl_all_struct_invs S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of T)\<close>
  using assms
  by (induction rule: cdcl_inp_propagate.induct)
    (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def insert_commute)

lemma cdcl_inp_conflict_entailed_by_init:
  assumes \<open>cdcl_inp_conflict S T\<close> and
    \<open>pcdcl_all_struct_invs S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of T)\<close>
  using assms
  by (induction rule: cdcl_inp_conflict.induct)
    (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def insert_commute)

lemma cdcl_promote_false_entailed_by_init:
  assumes \<open>cdcl_promote_false S T\<close> and
    \<open>pcdcl_all_struct_invs S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of T)\<close>
  using assms
  by (induction rule: cdcl_promote_false.induct)
    (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def insert_commute)

lemma pcdcl_entailed_by_init:
  assumes \<open>pcdcl S T\<close> and
    \<open>pcdcl_all_struct_invs S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of T)\<close>
  using assms
  apply (induction rule: pcdcl.induct)
    apply (meson cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_cdcl\<^sub>W_restart
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed pcdcl_all_struct_invs_def pcdcl_core_is_cdcl)
  by (simp_all add: cdcl_learn_clause_entailed_by_init cdcl_subsumed_entailed_by_init
    cdcl_resolution_entailed_by_init cdcl_flush_unit_unchanged cdcl_pure_literal_remove_entailed_by_init
    cdcl_inp_conflict_entailed_by_init cdcl_inp_propagate_entailed_by_init
    cdcl_unitres_true_same cdcl_promote_false_entailed_by_init)

lemma rtranclp_pcdcl_entailed_by_init:
  assumes \<open>pcdcl\<^sup>*\<^sup>* S T\<close> and
    \<open>pcdcl_all_struct_invs S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of T)\<close>
  using assms
  by (induction rule: rtranclp_induct)
   (use pcdcl_entailed_by_init rtranclp_pcdcl_all_struct_invs in blast)+


lemma pcdcl_core_stgy_stgy_invs:
  assumes
    confl: \<open>pcdcl_core_stgy S T\<close> and
    ent: \<open>entailed_clss_inv S\<close> and
    invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of S)\<close> and
     \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state_of S)\<close> and
    clss0: \<open>clauses0_inv S\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state_of T)\<close>
  using assms
  by (meson cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_cdcl\<^sub>W_stgy_invariant pcdcl_core_stgy_is_cdcl_stgy)


lemma cdcl_subsumed_stgy_stgy_invs:
  assumes
    confl: \<open>cdcl_subsumed S T\<close> and
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
    ent: \<open>entailed_clss_inv S\<close> and
    invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of S)\<close> and
     \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state_of S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state_of T)\<close>
  using assms
  by (induction rule: cdcl_resolution.induct)
    (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
    cdcl\<^sub>W_restart_mset.no_smaller_confl_def cdcl\<^sub>W_restart_mset.clauses_def)

lemma cdcl_pure_literal_remove_stgy_stgy_invs:
  assumes
    confl: \<open>cdcl_pure_literal_remove S T\<close> and
    ent: \<open>entailed_clss_inv S\<close> and
    invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of S)\<close> and
     \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state_of S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state_of T)\<close>
  using assms
  by (induction rule: cdcl_pure_literal_remove.induct)
    (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def get_level_cons_if Cons_eq_append_conv
    cdcl\<^sub>W_restart_mset.no_smaller_confl_def cdcl\<^sub>W_restart_mset.clauses_def)

lemma cdcl_learn_clause_stgy_stgy_invs:
  assumes
    confl: \<open>cdcl_learn_clause S T\<close> and
    ent: \<open>entailed_clss_inv S\<close> and
    invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of S)\<close> and
     \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state_of S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state_of T)\<close>
  using assms
  by (induction rule: cdcl_learn_clause.induct)
    (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
    cdcl\<^sub>W_restart_mset.no_smaller_confl_def cdcl\<^sub>W_restart_mset.clauses_def)

lemma cdcl_inp_conflict_stgy_stgy_invs:
  assumes
    confl: \<open>cdcl_inp_conflict S T\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state_of T)\<close>
  using assms
 by (induction rule: cdcl_inp_conflict.induct)
   (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
    cdcl\<^sub>W_restart_mset.no_smaller_confl_def cdcl\<^sub>W_restart_mset.clauses_def)

lemma pcdcl_stgy_stgy_invs:
  assumes
    confl: \<open>pcdcl_stgy S T\<close> and
    ent: \<open>entailed_clss_inv S\<close> and
    invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state_of S)\<close> and
     \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state_of S)\<close> and
    clss0: \<open>clauses0_inv S\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state_of T)\<close>
  using assms
  apply (induction rule: pcdcl_stgy.induct)
  subgoal using pcdcl_core_stgy_stgy_invs by blast
  subgoal using cdcl_learn_clause_stgy_stgy_invs by blast
  subgoal using cdcl_resolution_stgy_stgy_invs by blast
  subgoal using cdcl_subsumed_stgy_stgy_invs by blast
  subgoal by (simp add: cdcl_flush_unit_unchanged)
  subgoal
    using cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.propagate' cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_cdcl\<^sub>W_stgy_invariant
      cdcl_inp_propagate_is_propagate by blast
  subgoal
    by (simp add: cdcl_inp_conflict_stgy_stgy_invs)
  subgoal by (simp add: cdcl_unitres_true_same)
  done


section \<open>Higher-level rules\<close>

subsection \<open>Simplify unit clauses\<close>

text \<open>
Initially, I wanted to remove the literals one at a time, but this has two disadvantages:
  \<^item> more subsumed clauses are generated.
  \<^item> it makes it possible to remove all literals making it much easier to express that the clause
  is correctly watched in the next refinement step. Undefined literals are correctly watched. Mixed
  situation are strange (we could watch two false clauses during the simplification only).

As we only make the rule strictly more powerful and that the proof is not different, I changed the
rule instead of doing any other solution.

The change to explicitly remove subsumed clauses requires some more \<^term>\<open>C' \<notin> set (get_all_mark_of_propagated M)\<close>, 
because we do not want to delete reasons from the trail. However, practically, as we work on level 0
those clauses have already been moved to the entailed clauses anyway. Therefore, there is no real
restriction going on here.
\<close>
inductive cdcl_unitres :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
cdcl_unitresI:
  \<open>cdcl_unitres (M, N + {#C+C'#}, U, None, NE, UE, N0, U0, \<A>)
    (M, N + {#C#}, U, None, NE, UE, N0, U0, \<A>)\<close>
  if \<open>count_decided M = 0\<close> and \<open>add_mset (C+C') (make_big_tautology \<A> + N + NE + N0) \<Turnstile>psm mset_set (CNot C')\<close>
    \<open>\<not>tautology C\<close> \<open>distinct_mset C\<close> \<open>C+C' \<notin> set (get_all_mark_of_propagated M)\<close>|
cdcl_unitresI_unit:
  \<open>cdcl_unitres (M, N + {#C+C'#}, U, None, NE, UE, N0, U0, \<A>)
    (Propagated K C # M, N, U, None, NE + {#C#}, UE, N0, U0, \<A>)\<close>
  if \<open>count_decided M = 0\<close> and \<open>add_mset (C+C') (make_big_tautology \<A> + N + NE + N0) \<Turnstile>psm mset_set (CNot C')\<close>
    \<open>\<not>tautology C\<close> \<open>distinct_mset C\<close> \<open>C = {#K#}\<close> \<open>undefined_lit M K\<close> |
cdcl_unitresR:
  \<open>cdcl_unitres (M, N, U + {#C+C'#}, None, NE, UE, N0, U0, \<A>)
    (M, N, U + {#C#}, None, NE, UE, N0, U0, \<A>)\<close>
  if \<open>count_decided M = 0\<close> and \<open>(make_big_tautology \<A> + N + NE + N0) \<Turnstile>psm mset_set (CNot C')\<close>  \<open>\<not>tautology C\<close>
    \<open>distinct_mset C\<close> \<open>atms_of C \<subseteq> atms_of_mm (make_big_tautology \<A> + N+NE+N0)\<close>  \<open>C+C' \<notin> set (get_all_mark_of_propagated M)\<close> |
cdcl_unitresR_unit:
  \<open>cdcl_unitres (M, N, U + {#C+C'#}, None, NE, UE, N0, U0, \<A>)
    (Propagated K C # M, N, U, None, NE, UE + {#C#}, N0, U0, \<A>)\<close>
  if \<open>count_decided M = 0\<close> and \<open>(make_big_tautology \<A> + N + NE + N0) \<Turnstile>psm mset_set (CNot C')\<close>  \<open>\<not>tautology C\<close>
    \<open>distinct_mset C\<close> \<open>atms_of C \<subseteq> atms_of_mm (make_big_tautology \<A> + N+NE+N0)\<close> \<open>C = {#K#}\<close> \<open>undefined_lit M K\<close> |
cdcl_unitresR_empty:
  \<open>cdcl_unitres (M, N, U + {#C'#}, None, NE, UE, N0, U0, \<A>)
    (M, N, U, Some {#}, NE, UE, N0, add_mset {#} U0, \<A>)\<close>
  if \<open>count_decided M = 0\<close> and \<open>(make_big_tautology \<A> + N + NE + N0) \<Turnstile>psm mset_set (CNot C')\<close>
    \<open>C' \<notin> set (get_all_mark_of_propagated M)\<close> |
cdcl_unitresI_empty:
  \<open>cdcl_unitres (M, N + {#C'#}, U, None, NE, UE, N0, U0, \<A>)
    (M, N, U, Some {#}, NE, UE, add_mset {#} N0, U0, \<A>)\<close>
  if \<open>count_decided M = 0\<close> and \<open>(add_mset C' (make_big_tautology \<A> + N + NE + N0)) \<Turnstile>psm mset_set (CNot C')\<close>
    \<open>C' \<notin> set (get_all_mark_of_propagated M)\<close>

lemma true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or_generalise':
  \<open>N \<Turnstile>ps CNot C' \<Longrightarrow> N \<Turnstile>p C + C' \<Longrightarrow> C'' \<subseteq># C' \<Longrightarrow> N \<Turnstile>p (C + (C' - C''))\<close>
  apply (induction C'')
  subgoal by auto
  subgoal for x C''
    using true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or[of \<open>N\<close>
      \<open>x\<close> \<open>{#}\<close> \<open>C + (C' - add_mset x C'')\<close>]
    apply (auto dest!: mset_subset_eq_insertD dest!: multi_member_split)
    by (smt Multiset.diff_right_commute add_mset_remove_trivial add_mset_remove_trivial_eq diff_single_trivial)
  done

lemmas true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or_generalise =
  true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or_generalise'[of N C' C C' for C C' N, simplified]

lemma true_clss_cls_insert_itself:
  \<open>insert (C + C') (set_mset N \<union> set_mset NE \<union> set_mset NS \<union> set_mset N0) \<Turnstile>p C + C'\<close>
  by auto

lemmas make_big_tautology_true_clss_cls_insert_iff3[simp] =
  make_big_tautology_true_clss_cls_insert_iff[of _ _ \<open>N \<union> NE \<union> N0\<close> for N NE N0, unfolded Un_assoc[symmetric]]

lemma cdcl_unitres_learn_subsumeE:
  assumes
    \<open>cdcl_unitres S X\<close>
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of S)\<close> and
    \<open>pcdcl_all_struct_invs S\<close>
  obtains T U V W where \<open>cdcl_learn_clause S T\<close> \<open>cdcl_subsumed T U\<close>
    \<open>cdcl_propagate\<^sup>*\<^sup>* U V\<close>
    \<open>cdcl_flush_unit\<^sup>*\<^sup>* V W\<close>
    \<open>cdcl_promote_false\<^sup>*\<^sup>* W X\<close>
  using assms
proof (cases rule: cdcl_unitres.cases)
  case (cdcl_unitresI M C C' \<A> N NE N0 U UE U0)
  then show ?thesis
    using assms(2) apply -
    by (rule that[of \<open>(M, N + {#C+C', C#}, U, None, NE, UE, N0, U0, \<A>)\<close> X X])
      (auto simp: cdcl_learn_clause.simps cdcl_subsumed.simps make_big_tautology_true_clss_cls_insert_iff
      intro: true_clss_cls_insert_itself
      dest!: true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or_generalise
      intro: exI[of _ C])
next
  case (cdcl_unitresI_unit M C C' \<A> N NE N0 K U UE U0)
  have H: \<open>insert (add_mset K C') (set_mset N \<union> set_mset NE \<union> set_mset N0) \<Turnstile>p {#K#} + C'\<close>
    by auto
  have \<open>add_mset K C' \<notin> set (get_all_mark_of_propagated M)\<close>
  proof (rule ccontr)
    assume \<open>\<not> ?thesis\<close>
    moreover have \<open>\<forall>L mark a b. a @ Propagated L mark # b = M \<longrightarrow> b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close>
      using assms(3) cdcl_unitresI_unit
      by (auto simp: pcdcl_all_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def)
    ultimately show False
      using cdcl_unitresI_unit unfolding cdcl\<^sub>W_restart_mset.in_get_all_mark_of_propagated_in_trail
      apply (auto simp: pcdcl_all_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def dest!: split_list)
      by (metis add_cancel_left_left diff_union_swap multi_member_this true_annots_CNot_definedD union_mset_add_mset_left)
  qed
  then show ?thesis
    using cdcl_unitresI_unit apply -
    by (rule that[of \<open>(M, N + {#C+C', C#}, U, None, NE, UE, N0, U0, \<A>)\<close>
      \<open>(M, add_mset C N, U, None, NE, UE, N0, U0, \<A>)\<close>
      \<open>(Propagated K C # M, add_mset C N, U, None, NE, UE, N0, U0, \<A>)\<close>
      X])
      (auto simp: cdcl_learn_clause.simps cdcl_subsumed.simps cdcl_flush_unit.simps
      cdcl_propagate.simps intro: H exI[of _ \<open>{#K#}\<close>]
      dest!: true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or_generalise
      intro!: r_into_rtranclp)
next
  case (cdcl_unitresR M \<A> N NE N0 C' C U UE U0)
  have \<open>(make_big_tautology \<A>) + N + NE + N0 \<Turnstile>pm C+C'\<close>
    using assms(2) cdcl_unitresR
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def)
  then have \<open>(make_big_tautology \<A>) + N + NE + N0 \<Turnstile>pm C\<close>
    using cdcl_unitresR(4) true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or_generalise
    by (metis finite_CNot finite_set_mset_mset_set)

  then show ?thesis
    using cdcl_unitresR apply -
      by (rule that[of \<open>(M, N, U + {#C+C', C#}, None, NE, UE, N0, U0, \<A>)\<close> X X X])
       (auto simp: cdcl_learn_clause.simps cdcl_subsumed.simps
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
        intro: exI[of _ C])
next
  case (cdcl_unitresR_unit M \<A> N NE N0 C' C K U UE U0)
  moreover have [intro]: \<open>set_mset (make_big_tautology \<A>) \<union> set_mset N \<union> set_mset NE \<union> set_mset N0 \<Turnstile>p
    {#K#} + C'\<close>
    using assms(2) cdcl_unitresR_unit
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def)
  moreover have \<open>add_mset K C' \<notin> set (get_all_mark_of_propagated M)\<close>
  proof (rule ccontr)
    assume \<open>\<not> ?thesis\<close>
    moreover have \<open>\<forall>L mark a b. a @ Propagated L mark # b = M \<longrightarrow> b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close>
      using assms(3) cdcl_unitresR_unit
      by (auto simp: pcdcl_all_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def)
    ultimately show False
      using cdcl_unitresR_unit unfolding cdcl\<^sub>W_restart_mset.in_get_all_mark_of_propagated_in_trail
      apply (auto simp: pcdcl_all_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def dest!: split_list)
      by (metis add_cancel_left_left diff_union_swap multi_member_this true_annots_CNot_definedD union_mset_add_mset_left)+
  qed
  ultimately show ?thesis apply -
    by (rule that[of \<open>(M, N, U + {#C+C', C#}, None, NE, UE, N0, U0, \<A>)\<close>
      \<open>(M, N, add_mset C U, None, NE, UE, N0, U0, \<A>)\<close>
      \<open>(Propagated K C # M, N, add_mset C U, None, NE, UE, N0, U0, \<A>)\<close>
      X])
     (auto simp: cdcl_learn_clause.simps cdcl_subsumed.simps cdcl_flush_unit.simps
      cdcl_propagate.simps cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
      dest!: true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or_generalise
      intro: r_into_rtranclp exI[of _ \<open>{#K#}\<close>])
next
  case (cdcl_unitresR_empty M \<A> N NE N0 C' U UE U0)
  have [intro]: \<open>(make_big_tautology \<A>) + N + NE + N0 \<Turnstile>pm {#} + C'\<close>
    \<open>set_mset (make_big_tautology \<A>) \<union> set_mset N \<union> set_mset NE \<union> set_mset N0 \<Turnstile>p {#} + C'\<close>
    using assms(2) cdcl_unitresR_empty
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def)
  then have \<open>(make_big_tautology \<A>) + N + NE + N0 \<Turnstile>pm {#}\<close>
    using cdcl_unitresR_empty true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or_generalise[of \<open>set_mset (make_big_tautology \<A> + N + NE + N0)\<close> C' \<open>{#}\<close>]
    by auto
  then show ?thesis
    using cdcl_unitresR_empty apply -
    by (rule that[of \<open>(M, N, U + {#C', {#}#}, None, NE, UE, N0, U0, \<A>)\<close>
      \<open>(M, N, add_mset {#} U, None, NE, UE, N0, U0, \<A>)\<close>
      \<open>(M, N, add_mset {#} U, None, NE, UE, N0, U0, \<A>)\<close>
      \<open>(M, N, add_mset {#} U, None, NE, UE, N0, U0, \<A>)\<close>])
     (auto simp: cdcl_learn_clause.simps cdcl_subsumed.simps cdcl_flush_unit.simps
      cdcl_propagate.simps cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
      cdcl_promote_false.simps
        dest!: true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or_generalise
        intro!: r_into_rtranclp intro: exI[of _ C'] exI[of _ \<open>{#}\<close>])
next
  case (cdcl_unitresI_empty M C' \<A> N NE N0 U UE U0)
  then show ?thesis
    apply -
      using true_clss_clss_contradiction_true_clss_cls_false[of C'
        \<open>insert C' (set_mset N \<union> set_mset NE \<union> set_mset N0)\<close>] apply -
      by (rule that[of \<open>(M, N + {#C', {#}#}, U, None, NE, UE, N0, U0, \<A>)\<close>
           \<open>(M, add_mset {#} N, U, None, NE, UE, N0, U0, \<A>)\<close>
           \<open>(M, add_mset {#} N, U, None, NE, UE, N0, U0, \<A>)\<close>
          \<open>(M, add_mset {#} N, U, None, NE, UE,  N0, U0, \<A>)\<close>])
        (auto simp: cdcl_learn_clause.simps cdcl_subsumed.simps
        cdcl_propagate.simps cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
        cdcl_promote_false.simps
        dest: true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or_generalise
        intro!: r_into_rtranclp intro: exI[of _ \<open>{#}\<close>])
qed

lemma cdcl_unitres_learn_subsume:
  assumes \<open>cdcl_unitres S U\<close> \<open>pcdcl_all_struct_invs S\<close>
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state_of S)\<close>
  shows \<open>pcdcl\<^sup>*\<^sup>* S U\<close>
proof -
  have [dest!]: \<open>cdcl_propagate\<^sup>*\<^sup>* S T \<Longrightarrow> pcdcl\<^sup>*\<^sup>* S T\<close> for S T
    by (rule mono_rtranclp[rule_format, of cdcl_propagate pcdcl]) (*Who is the idiot who wrote the theorem that way?*)
     (auto dest: pcdcl.intros pcdcl_core.intros)
  have [dest!]: \<open>cdcl_flush_unit\<^sup>*\<^sup>* S T \<Longrightarrow> pcdcl\<^sup>*\<^sup>* S T\<close> for S T
    by (rule mono_rtranclp[rule_format, of cdcl_flush_unit pcdcl])
     (auto dest: pcdcl.intros pcdcl_core.intros)
  have [dest!]: \<open>cdcl_promote_false\<^sup>*\<^sup>* S T \<Longrightarrow> pcdcl\<^sup>*\<^sup>* S T\<close> for S T
    by (rule mono_rtranclp[rule_format, of cdcl_promote_false pcdcl])
     (auto dest: pcdcl.intros pcdcl_core.intros)
  show ?thesis
    by (rule cdcl_unitres_learn_subsumeE[OF assms(1,3)]) (use assms in \<open>auto dest!: pcdcl.intros pcdcl_core.intros\<close>)
qed

lemma get_all_ann_decomposition_count_decided0:
  \<open>count_decided M = 0 \<Longrightarrow> get_all_ann_decomposition M = [([], M)]\<close>
  by (induction M rule: ann_lit_list_induct)  auto

text \<open>The following two lemmas gives the nicer introduction rule that are what anyone expects
from removing false literals.\<close>
lemma cdcl_unitresI1:
  assumes
    invs: \<open>pcdcl_all_struct_invs (M, N, U + {#C+C'#}, None, NE, UE, N0, U0, \<A>)\<close> and
    L: \<open>\<forall>L. L \<in># C' \<longrightarrow> -L \<in> lits_of_l M\<close> and
    [simp]: \<open>count_decided M = 0\<close> and
    \<open>\<not> tautology C\<close> and
    ent_init: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init
    (state_of (M, N, U + {#C+C'#}, None, NE, UE, N0, U0, \<A>))\<close> and
    notin: \<open>C + C' \<notin> set (get_all_mark_of_propagated M)\<close>
  shows \<open>cdcl_unitres (M, N, U + {#C+C'#}, None, NE, UE, N0, U0, \<A>)
    (M, N, U + {#C#}, None, NE, UE, N0, U0, \<A>)\<close> (is \<open>cdcl_unitres ?S ?T\<close>)
proof
  show \<open>count_decided M = 0\<close> and \<open>\<not> tautology C\<close>
    by (rule assms)+
  have ent: \<open>all_decomposition_implies_m (cdcl\<^sub>W_restart_mset.clauses (state_of ?S))
      (get_all_ann_decomposition (trail (state_of ?S)))\<close> and
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state_of ?S)\<close> and
    alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state_of ?S)\<close>
    using invs
    unfolding pcdcl_all_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  have [iff]: \<open>insert (C+C')
        (set_mset (make_big_tautology \<A>) \<union> set_mset N \<union> set_mset NE \<union> set_mset N0 \<union>
    (set_mset U \<union> set_mset UE \<union> set_mset U0)) \<Turnstile>p NC \<longleftrightarrow>
    set_mset (make_big_tautology \<A>) \<union> set_mset N \<union> set_mset NE \<union> set_mset N0 \<Turnstile>p NC\<close> for NC
    using true_clss_clss_generalise_true_clss_clss[of \<open>(set_mset N \<union> set_mset NE \<union> set_mset N0)\<close>
      \<open>insert (C+C') (set_mset U \<union> set_mset UE \<union> set_mset U0)\<close>
      \<open>{NC}\<close>
       \<open>(set_mset N \<union> set_mset NE \<union> set_mset N0)\<close>] ent_init
    apply (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def)
    by (metis Un_assoc make_big_tautology_true_clss_cls_iff make_big_tautology_true_clss_cls_insert_iff3 make_big_tautology_true_clss_clss_iff set_mset_union)


  have \<open>make_big_tautology \<A> + N + NE + N0 \<Turnstile>psm mset_set (CNot (C''))\<close> if \<open>C'' \<subseteq># C'\<close> for C''
    using ent L ent_init that
    by (induction C'')
     (auto simp: clauses_def all_decomposition_implies_def lits_of_def uminus_lit_swap
      eq_commute[of \<open>lit_of _\<close>] cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
      all_conj_distrib
      get_all_ann_decomposition_count_decided0 dest!: split_list mset_subset_eq_insertD)

  from this[of C'] show \<open>make_big_tautology \<A> + N + NE + N0 \<Turnstile>psm mset_set (CNot C')\<close> by auto
  show \<open>distinct_mset C\<close>
    using dist by (auto simp: cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def dest: distinct_mset_union)
  show \<open>atms_of C \<subseteq> atms_of_mm (make_big_tautology \<A> + N + NE + N0)\<close>
    using alien
    by (auto simp: cdcl\<^sub>W_restart_mset.no_strange_atm_def)
  show \<open>C + C' \<notin> set (get_all_mark_of_propagated M)\<close>
    by (rule notin)
qed

lemma cdcl_unitresI1_unit:
  fixes K :: \<open>'v literal\<close>
  defines \<open>C \<equiv> {#K#}\<close>
  assumes
    invs: \<open>pcdcl_all_struct_invs (M, N, U + {#C+C'#}, None, NE, UE, N0, U0, \<A>)\<close> and
    L: \<open>\<forall>L. L \<in># C' \<longrightarrow> -L \<in> lits_of_l M\<close> and
    [simp]: \<open>count_decided M = 0\<close> and
    \<open>\<not> tautology C\<close> and
    undef: \<open>undefined_lit M K\<close> and
    ent_init: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init
       (state_of (M, N, U + {#C+C'#}, None, NE, UE, N0, U0, \<A>))\<close>
  shows \<open>cdcl_unitres (M, N, U + {#C+C'#}, None, NE, UE, N0, U0, \<A>)
    (Propagated K C # M, N, U, None, NE, UE + {#C#}, N0, U0, \<A>)\<close> (is \<open>cdcl_unitres ?S ?T\<close>)
proof
  show \<open>count_decided M = 0\<close> and \<open>\<not> tautology C\<close>
    by (rule assms)+
  have ent: \<open>all_decomposition_implies_m (cdcl\<^sub>W_restart_mset.clauses (state_of ?S))
      (get_all_ann_decomposition (trail (state_of ?S)))\<close> and
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state_of ?S)\<close> and
    alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state_of ?S)\<close>
    using invs
    unfolding pcdcl_all_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  have [iff]: \<open>insert (C+C')
        (set_mset (make_big_tautology \<A>) \<union> set_mset N \<union> set_mset NE \<union> set_mset N0 \<union>
    (set_mset U \<union> set_mset UE \<union> set_mset U0)) \<Turnstile>p NC \<longleftrightarrow>
    set_mset (make_big_tautology \<A>) \<union> set_mset N \<union> set_mset NE \<union> set_mset N0 \<Turnstile>p NC\<close> for NC
    using true_clss_clss_generalise_true_clss_clss[of \<open>(set_mset N \<union> set_mset NE \<union> set_mset N0)\<close>
      \<open>insert (C+C') (set_mset U \<union> set_mset UE \<union> set_mset U0)\<close>
      \<open>{NC}\<close>
       \<open>(set_mset N \<union> set_mset NE \<union> set_mset N0)\<close>] ent_init
    apply (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def)
    by (metis Un_assoc make_big_tautology_true_clss_cls_iff make_big_tautology_true_clss_cls_insert_iff3 make_big_tautology_true_clss_clss_iff set_mset_union)

  have \<open>make_big_tautology \<A> + N + NE + N0 \<Turnstile>psm mset_set (CNot (C''))\<close> if \<open>C'' \<subseteq># C'\<close> for C''
    using ent L ent_init that
    by (induction C'')
      (auto simp: clauses_def all_decomposition_implies_def lits_of_def uminus_lit_swap
      eq_commute[of \<open>lit_of _\<close>] cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
      all_conj_distrib
      get_all_ann_decomposition_count_decided0 dest!: split_list mset_subset_eq_insertD)
  from this[of C'] show \<open>make_big_tautology \<A> + N + NE + N0 \<Turnstile>psm mset_set (CNot C')\<close> by auto
  show \<open>distinct_mset C\<close>
    using dist by (auto simp: cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def dest: distinct_mset_union)
  show \<open>atms_of C \<subseteq> atms_of_mm (make_big_tautology \<A> + N + NE + N0)\<close>
    using alien
    by (auto simp: cdcl\<^sub>W_restart_mset.no_strange_atm_def)
  show \<open>C = {#K#}\<close>
    unfolding C_def by auto
  show \<open>undefined_lit M K\<close>
    using undef by auto
qed

lemma cdcl_unitresI2:
  assumes
    invs: \<open>pcdcl_all_struct_invs (M, N + {#C+C'#}, U, None, NE, UE, N0, U0, \<A>)\<close> and
    L: \<open>\<forall>L. L \<in># C' \<longrightarrow> -L \<in> lits_of_l M\<close> and
    [simp]: \<open>count_decided M = 0\<close> and
    \<open>\<not> tautology C\<close> and
    ent_init: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init
    (state_of (M, N + {#C+C'#}, U, None, NE, UE, N0, U0, \<A>))\<close> and
    notin: \<open>C + C' \<notin> set (get_all_mark_of_propagated M)\<close>
  shows \<open>cdcl_unitres (M, N + {#C+C'#}, U, None, NE, UE, N0, U0, \<A>)
    (M, N + {#C#}, U, None, NE, UE, N0, U0, \<A>)\<close> (is \<open>cdcl_unitres ?S ?T\<close>)
proof
  show \<open>count_decided M = 0\<close> and \<open>\<not> tautology C\<close>
    by (rule assms)+
  have ent: \<open>all_decomposition_implies_m (cdcl\<^sub>W_restart_mset.clauses (state_of ?S))
      (get_all_ann_decomposition (trail (state_of ?S)))\<close> and
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state_of ?S)\<close> and
    alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state_of ?S)\<close>
    using invs
    unfolding pcdcl_all_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  have [iff]: \<open>insert (C+C')
        (set_mset (make_big_tautology \<A>) \<union> set_mset N \<union> set_mset NE \<union> set_mset N0 \<union>
    (set_mset (make_big_tautology \<A>) \<union> set_mset U \<union> set_mset UE \<union> set_mset U0)) \<Turnstile>p NC \<longleftrightarrow>
    insert (C+C') (set_mset N \<union> set_mset NE \<union> set_mset N0) \<Turnstile>p NC\<close> for NC
    using true_clss_clss_generalise_true_clss_clss[of \<open>insert (C+C') (set_mset (make_big_tautology \<A>) \<union> set_mset N \<union> set_mset NE \<union> set_mset N0)\<close>
      \<open>(set_mset (make_big_tautology \<A>) \<union> set_mset U \<union> set_mset UE \<union> set_mset U0)\<close>
      \<open>{NC}\<close>
       \<open>insert (C+C') (set_mset (make_big_tautology \<A>) \<union> set_mset N \<union> set_mset NE \<union> set_mset N0)\<close>] ent_init
    apply (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
      dest: true_clss_cs_mono_l)
    apply (meson Un_iff all_in_true_clss_clss insertCI)
      by (meson inf_sup_ord(3) insert_mono make_big_tautology_true_clss_cls_insert_iff3 true_clss_cls_subsetI)
  have \<open>add_mset (C+C') (make_big_tautology \<A> +N + NE + N0) \<Turnstile>psm mset_set (CNot C'')\<close> if \<open>C'' \<subseteq># C'\<close> for C''
    using that
    apply (induction C'')
      using ent L ent_init
    apply (auto simp: clauses_def all_decomposition_implies_def lits_of_def uminus_lit_swap
      eq_commute[of _ \<open>lit_of _\<close>] cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
      get_all_ann_decomposition_count_decided0 dest!: split_list mset_subset_eq_insertD)
by (smt (verit, ccfv_threshold) L Un_left_commute \<open>\<And>NC. (insert (C + C') (set_mset (make_big_tautology \<A>) \<union> set_mset N \<union> set_mset NE \<union> set_mset N0 \<union> (set_mset (make_big_tautology \<A>) \<union> set_mset U \<union> set_mset UE \<union> set_mset U0)) \<Turnstile>p NC) = (insert (C + C') (set_mset N \<union> set_mset NE \<union> set_mset N0) \<Turnstile>p NC)\<close> in_unmark_l_in_lits_of_l_iff make_big_tautology_true_clss_cls_insert_iff3 true_clss_clss_in_imp_true_clss_cls)

  from this[of C'] show \<open>add_mset (C+C') (make_big_tautology \<A> +N + NE + N0) \<Turnstile>psm mset_set (CNot C')\<close>
   by auto
  show \<open>distinct_mset C\<close>
    using dist by (auto simp: cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def dest: distinct_mset_union)
qed (rule notin)

lemma cdcl_unitresI2_unit:
  fixes K :: \<open>'v literal\<close>
  defines \<open>C \<equiv> {#K#}\<close>
  assumes
    invs: \<open>pcdcl_all_struct_invs (M, N + {#C+C'#}, U, None, NE, UE, N0, U0, \<A>)\<close> and
    L: \<open>\<forall>L. L \<in># C' \<longrightarrow> -L \<in> lits_of_l M\<close> and
    [simp]: \<open>count_decided M = 0\<close> and
    \<open>\<not> tautology C\<close> and
    undef: \<open>undefined_lit M K\<close> and
    ent_init: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init
       (state_of (M, N + {#C+C'#}, U, None, NE, UE, N0, U0, \<A>))\<close>
  shows \<open>cdcl_unitres (M, N + {#C+C'#}, U, None, NE, UE, N0, U0, \<A>)
    (Propagated K C # M, N, U, None, NE + {#C#}, UE, N0, U0, \<A>)\<close> (is \<open>cdcl_unitres ?S ?T\<close>)
proof
  show \<open>count_decided M = 0\<close> and \<open>\<not> tautology C\<close> and \<open>undefined_lit M K\<close>
    by (rule assms)+
  show \<open>C = {#K#}\<close>
    unfolding C_def ..
  have ent: \<open>all_decomposition_implies_m (cdcl\<^sub>W_restart_mset.clauses (state_of ?S))
      (get_all_ann_decomposition (trail (state_of ?S)))\<close> and
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state_of ?S)\<close> and
    alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state_of ?S)\<close>
    using invs
    unfolding pcdcl_all_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  have [iff]: \<open>insert (C+C')
        (set_mset (make_big_tautology \<A>) \<union> set_mset N \<union> set_mset NE \<union> set_mset N0 \<union>
    (set_mset U \<union> set_mset UE \<union> set_mset U0)) \<Turnstile>p NC \<longleftrightarrow>
    insert (C+C') (set_mset (make_big_tautology \<A>) \<union> set_mset N \<union> set_mset NE \<union> set_mset N0) \<Turnstile>p NC\<close> for NC
    using true_clss_clss_generalise_true_clss_clss[of \<open>insert (C+C') (set_mset (make_big_tautology \<A>) \<union> set_mset N \<union> set_mset NE \<union> set_mset N0)\<close>
      \<open>(set_mset U \<union> set_mset UE \<union> set_mset U0)\<close>
      \<open>{NC}\<close>
       \<open>insert (C+C') (set_mset (make_big_tautology \<A>) \<union> set_mset N \<union> set_mset NE \<union> set_mset N0)\<close>] ent_init
    apply (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
      dest: true_clss_cs_mono_l)
    by (metis (no_types, opaque_lifting) Un_assoc Un_insert_left make_big_tautology_true_clss_cls_insert_iff sup_ge1 true_clss_cls_subsetI)

  have \<open>add_mset (C+C') (make_big_tautology \<A> + N + NE + N0) \<Turnstile>psm mset_set (CNot C'')\<close> if \<open>C'' \<subseteq># C'\<close> for C''
    using that
    apply (induction C'')
      using ent L ent_init
    by (auto simp: clauses_def all_decomposition_implies_def lits_of_def uminus_lit_swap
      eq_commute[of _ \<open>lit_of _\<close>] cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
      get_all_ann_decomposition_count_decided0 dest!: split_list mset_subset_eq_insertD)

  from this[of C'] show \<open>add_mset (C+C') (make_big_tautology \<A> + N + NE + N0) \<Turnstile>psm mset_set (CNot C')\<close>
   by auto
  show \<open>distinct_mset C\<close>
    using dist by (auto simp: cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def dest: distinct_mset_union)
qed


subsection \<open>Subsumption resolution\<close>
text \<open>

Subsumption-Resolution rules are the composition of resolution,
subsumption, learning of a clause, and potentially forget. However,
we have decided to not model the forget, because we would like to map
the calculus to a version without restarts.

\<close>

inductive cdcl_subresolution :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
subresolution_II:
  \<open>cdcl_subresolution (M, N + {#add_mset L C, add_mset (-L) C'#}, U, D, NE, UE, N0, U0, \<A>)
    (M, N + {#add_mset L C, remdups_mset C'#}, U, D, NE, UE, N0, U0, \<A>)\<close>
 if  \<open>count_decided M = 0\<close> \<open>C \<subseteq># C'\<close> \<open>add_mset (- L) C' \<notin> set (get_all_mark_of_propagated M)\<close> |
subresolution_LL:
  \<open>cdcl_subresolution (M, N, U + {#add_mset L C, add_mset (-L) C'#}, D, NE, UE, N0, U0, \<A>)
    (M, N, U + {#add_mset L C, remdups_mset (C')#}, D, NE, UE, N0, U0, \<A>)\<close>
 if  \<open>count_decided M = 0\<close> and \<open>\<not>tautology (C + C')\<close> and  \<open>C \<subseteq># C'\<close> \<open>add_mset (- L) C' \<notin> set (get_all_mark_of_propagated M)\<close>|
subresolution_LI:
  \<open>cdcl_subresolution (M, N + {#add_mset L C#}, U + {#add_mset (-L) C'#}, D, NE, UE, N0, U0, \<A>)
    (M, N + {#add_mset L C#}, U + {#remdups_mset (C')#}, D, NE, UE, N0, U0, \<A>)\<close>
 if  \<open>count_decided M = 0\<close> and \<open>\<not>tautology (C + C')\<close> and  \<open>C \<subseteq># C'\<close> \<open>add_mset (- L) C' \<notin> set (get_all_mark_of_propagated M)\<close>|
subresolution_IL:
  \<open>cdcl_subresolution (M, N + {#add_mset L C#}, U + {#add_mset (-L) C'#}, D, NE, UE, N0, U0, \<A>)
    (M, N + {#remdups_mset C#}, U + {#add_mset (-L) C'#}, D, NE, UE,
     N0, U0, \<A>)\<close>
 if  \<open>count_decided M = 0\<close> and \<open>\<not>tautology (C + C')\<close> and  \<open>C' \<subseteq># C\<close>  \<open>add_mset (L) C \<notin> set (get_all_mark_of_propagated M)\<close>


lemma cdcl_subresolution:
  assumes \<open>cdcl_subresolution S T\<close>
  shows \<open>pcdcl\<^sup>*\<^sup>* S T\<close>
  using assms
proof  (induction rule: cdcl_subresolution.induct)
  case (subresolution_II M C C' L N U D NE UE N0 U0 \<A>)
  then show ?case
    apply -
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule pcdcl.intros(3))
    apply (rule cdcl_resolution.resolution_II, assumption)
    apply (rule r_into_rtranclp)
    apply (rule pcdcl.intros(4))
    using cdcl_subsumed.intros(1)[of \<open>remdups_mset (C + C')\<close> \<open>add_mset (- L) C'\<close> M
      \<open>N + {#add_mset L C#}\<close> U D NE UE N0 U0 \<A>]
    apply (auto simp add: dest!: remdups_mset_sum_subset(1)
      simp: remdups_mset_subset_add_mset add_mset_commute)
    done
next
  case (subresolution_LL M C C' L N U D NE UE N0 U0 \<A>)
  then show ?case apply -
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule pcdcl.intros(3))
    apply (rule cdcl_resolution.resolution_LL, assumption, assumption)
    apply (rule r_into_rtranclp)
    apply (rule pcdcl.intros(4))
    using cdcl_subsumed.intros(2)[of \<open>remdups_mset (C + C')\<close> \<open>add_mset (- L) C'\<close> M N
      \<open>U + {#add_mset L C#}\<close> D NE UE N0 U0 \<A>]
    apply (auto dest!: remdups_mset_sum_subset(1)
      simp: remdups_mset_subset_add_mset add_mset_commute)
    done
next
  case (subresolution_LI M C C' L N U D NE UE N0 U0 \<A>)
  then show ?case apply -
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule pcdcl.intros(3))
    apply (rule cdcl_resolution.resolution_IL, assumption, assumption)
    apply (rule r_into_rtranclp)
    apply (rule pcdcl.intros(4))
    using cdcl_subsumed.intros(2)[of \<open>remdups_mset (C + C')\<close> \<open>add_mset (- L) C'\<close> M
      \<open>N  + {#add_mset L C#}\<close> \<open>U\<close> D NE UE N0 U0 \<A>]
    apply (auto simp add: dest!: remdups_mset_sum_subset(1)
      simp: remdups_mset_subset_add_mset add_mset_commute)
    done
next
  case (subresolution_IL M C C' L N U D NE UE N0 U0 \<A>)
  then have [simp]: \<open>remdups_mset (C + C') = remdups_mset C\<close> and
    tauto: \<open>\<not> tautology (remdups_mset (C + C'))\<close>
    using remdups_mset_sum_subset(2) by auto
  have [simp]: \<open>remdups_mset C \<subseteq># add_mset L C\<close>
    by (simp add: remdups_mset_subset_add_mset)
  have 1: \<open>cdcl_resolution
     (M, N + {#add_mset L C#}, U + {#add_mset (- L) C'#}, D, NE, UE, N0, U0, \<A>)
     (M, N + {#add_mset L C#},
        U + {#add_mset (- L) C', remdups_mset (C + C')#}, D, NE, UE, N0, U0, \<A>)\<close>
      (is \<open>cdcl_resolution ?A ?B\<close>)
      using subresolution_IL apply -
      by (rule cdcl_resolution.resolution_IL, assumption, assumption)
  have \<open>cdcl_learn_clause
     (M, add_mset (add_mset L C) N,
      add_mset (remdups_mset (C + C')) (U + {#add_mset (- L) C'#}), D, NE, UE, N0, U0, \<A>)
      (M, add_mset (remdups_mset (C + C')) (add_mset (add_mset L C) N),
      U + {#add_mset (- L) C'#}, D, NE, UE, N0, U0, \<A>)\<close> (is \<open>cdcl_learn_clause _ ?C\<close>)
    by (rule cdcl_learn_clause.intros(3)[of \<open>remdups_mset (C+C')\<close>, OF tauto])
  then have 2: \<open>cdcl_learn_clause ?B ?C\<close>
    by (auto simp: add_mset_commute)
  have 3: \<open>cdcl_subsumed ?C
     (M, N + {#remdups_mset C#}, U + {#add_mset (- L) C'#}, D, NE, UE, N0, U0, \<A>)\<close>
    using subsumed_II[of _ _ M N _ D NE UE N0 U0 \<A>] subresolution_IL(4)
    by (auto simp: add_mset_commute dest!: )
  show ?case using subresolution_IL apply -
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule pcdcl.intros(3)[OF 1])
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule pcdcl.intros(2))
    apply (rule 2)
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule pcdcl.intros(4))
    apply (rule 3)
    by auto
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
  \<open>cdcl_backtrack_unit (M, N, U, Some (add_mset L D), NE, UE, N0, U0, \<A>)
  (Propagated L {#L#} # M1, N, U, None, NE, add_mset {#L#} UE, N0, U0, \<A>)\<close>
  if
    \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition M)\<close> and
    \<open>get_level M L = count_decided M\<close> and
    \<open>get_level M L = get_maximum_level M {#L#}\<close> and
    \<open>get_level M K = 1\<close> and
    \<open>make_big_tautology \<A> + N + U + NE + UE + N0 + U0 \<Turnstile>pm {#L#}\<close>

lemma cdcl_backtrack_unit_is_backtrack:
  assumes \<open>cdcl_backtrack_unit S U\<close>
  obtains T where
    \<open>cdcl_backtrack S T\<close> and
    \<open>cdcl_flush_unit T U\<close>
  using assms
proof (induction rule: cdcl_backtrack_unit.induct)
  case (1 K M1 M2 M L \<A> N U NE UE N0 U0 D) note H =this(1-5) and that = this(6)
  let ?T = \<open>(Propagated L (add_mset L {#}) # M1, N, add_mset (add_mset L {#}) U, None, NE, UE, N0, U0, \<A>)\<close>
  have \<open>cdcl_backtrack (M, N, U, Some (add_mset L D), NE, UE, N0, U0, \<A>) ?T\<close>
    apply (rule cdcl_backtrack.intros[of K M1 M2 _ _ _ 0])
    using H by auto
  moreover have \<open>cdcl_flush_unit ?T (Propagated L {#L#} # M1, N, U, None, NE, add_mset {#L#} UE, N0, U0, \<A>)\<close>
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


section \<open>Subsume and promote\<close>

inductive cdcl_subsumed_RI :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
cdcl_subsumed_RI:
  \<open>cdcl_subsumed_RI (M, add_mset C' N, add_mset C U, D, NE, UE, N0, U0, \<A>)
     (M, add_mset C N, U, D, NE, UE, N0, U0, \<A>)\<close>
  if \<open>C \<subseteq># C'\<close> \<open>\<not>tautology C\<close> \<open>distinct_mset C\<close> \<open>C' \<notin> set (get_all_mark_of_propagated M)\<close>

lemma cdcl_subsumed_RID:
  assumes
    \<open>cdcl_subsumed_RI S W\<close>
  obtains T where
    \<open>cdcl_learn_clause S T\<close> and
    \<open>cdcl_subsumed T W\<close>
  using assms(1)
proof (cases rule: cdcl_subsumed_RI.cases)
  case (cdcl_subsumed_RI C C' M N U D NE UE N0 U0 \<A>)
  let ?T = \<open>(M, add_mset C (add_mset C' N), U, D, NE, UE, N0, U0, \<A>)\<close>
  show ?thesis
    apply (rule that[of ?T])
    subgoal
      using cdcl_subsumed_RI by (auto simp: cdcl_learn_clause.simps
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def mset_subset_eq_exists_conv)
    subgoal
      using cdcl_subsumed_RI by (auto simp: cdcl_subsumed.simps intro: exI[of _ C])
    done
qed

lemma cdcl_subsumed_RI_pcdcl:
  assumes
    \<open>cdcl_subsumed_RI S W\<close>
  shows
    \<open>pcdcl\<^sup>*\<^sup>* S W\<close>
  by (rule cdcl_subsumed_RID[OF assms])
    (metis pcdcl.intros(2,4) rtranclp.rtrancl_refl tranclp_into_rtranclp tranclp_unfold_end)


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
  \<open>cdcl_flush_unit S T \<Longrightarrow> pcdcl_tcore S T\<close> |
  \<open>cdcl_backtrack_unit S T \<Longrightarrow> pcdcl_tcore S T\<close>

inductive pcdcl_tcore_stgy :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> for S T :: \<open>'v prag_st\<close> where
  \<open>pcdcl_core_stgy S T \<Longrightarrow> pcdcl_tcore_stgy S T\<close> |
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
    subgoal by (auto simp: pcdcl_core_measure_def cdcl_flush_unit.simps)
    subgoal by (auto dest!: cdcl_backtrack_unit_is_CDCL_backtrack simp: pcdcl_all_struct_invs_def
       pcdcl_core_measure_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_bj_cdcl\<^sub>W_stgy cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_bj.simps
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_cdcl\<^sub>W)
    done
  then show \<open>?thesis\<close>
    by force
qed

lemmas wf_pcdcl_tcore = wf_subset[OF wf_pcdcl_core_measure pcdcl_tcore_in_pcdcl_core_measure]

lemma wf_pcdcl_tcore_stgy: \<open>wf {(T, S). pcdcl_all_struct_invs S \<and> pcdcl_tcore_stgy S T}\<close>
  by (rule wf_subset[OF wf_pcdcl_tcore])
    (auto simp add: pcdcl_tcore_stgy_pcdcl_tcoreD)

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
    by (auto simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def cdcl_learn_clause.simps
      clauses_def)
  subgoal
    by (auto simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def cdcl_resolution.simps)
  subgoal
    by (auto simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def cdcl_subsumed.simps clauses_def)
  subgoal
    by (auto simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def cdcl_flush_unit.simps)
  subgoal
    apply (auto simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def cdcl_inp_propagate.simps)
    apply (case_tac M'; auto)+
    done
  subgoal
    by (auto simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def cdcl_inp_conflict.simps)
  subgoal by (auto simp: cdcl_unitres_true_same)
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

lemma rtranclp_pcdcl_tcore_stgy_no_smaller_propa:
   \<open>pcdcl_tcore_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> pcdcl_all_struct_invs S \<Longrightarrow> cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of S) \<Longrightarrow>
   cdcl\<^sub>W_restart_mset.no_smaller_propa (state_of T)\<close>
  by (metis (no_types, opaque_lifting) mono_rtranclp pcdcl_tcore_stgy_pcdcl_stgy rtranclp_idemp
    rtranclp_pcdcl_stgy_no_smaller_propa tranclp_into_rtranclp)

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
  subgoal
    by (auto simp: cdcl_inp_propagate.simps cdcl\<^sub>W_restart_mset.conflict_non_zero_unless_level_0_def)
  subgoal
    by (auto simp: cdcl_inp_conflict.simps cdcl\<^sub>W_restart_mset.conflict_non_zero_unless_level_0_def)
  subgoal by (auto simp: cdcl_unitres_true_same)
  done

text \<open>
  TODO: rename to \<^term>\<open>full\<^sub>t\<close> or something along that line.
  \<close>
definition full2 :: \<open>('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool\<close> where
  \<open>full2 transf transf2 = (\<lambda>S S'. rtranclp transf S S' \<and> no_step transf2 S')\<close>

end