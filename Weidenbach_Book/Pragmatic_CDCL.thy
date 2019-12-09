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
  \<open>M \<Turnstile>as CNot D\<close>

inductive cdcl_decide :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
decide:
  \<open>cdcl_decide (M, N, U, None, NE, UE, NS, US)
    (Decided L' # M, N, U, None, NE, UE, NS, US)\<close>
  if
  \<open>undefined_lit M L'\<close>

inductive cdcl_skip :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
skip:
  \<open>cdcl_skip (Propagated L' C # M, N, U, Some D, NE, UE, NS, US)
    (Propagated L' C # M, N, U, Some D, NE, UE, NS, US)\<close>
  if
  \<open>-L' \<notin># D\<close>


inductive cdcl_resolve :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
resolve:
  \<open>cdcl_resolve (Propagated L' C # M, N, U, Some D, NE, UE, NS, US)
    (M, N, U, Some (cdcl\<^sub>W_restart_mset.resolve_cls L D C), NE, UE, NS, US)\<close>
  if
  \<open>-L' \<in># D\<close> and
  \<open>get_maximum_level M (remove1_mset (-L') D) = count_decided M\<close>


inductive cdcl_backtrack :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
  \<open>cdcl_backtrack (M, N, U, Some D, NE, UE, NS, US)
  (Propagated L D' # M1, N, add_mset D' U, None, NE, UE, NS, US)\<close>
  if
    \<open>L \<in># D\<close> and
    \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition M)\<close> and
    \<open>get_level M L = count_decided M\<close> and
    \<open>get_level M L = get_maximum_level M D'\<close> and
    \<open>get_maximum_level M (D' - {#L#}) \<equiv> i\<close> and
    \<open>get_level M K = i + 1\<close>
    \<open>D' = {#L#}\<close> and
    \<open>D' \<subseteq># D\<close> and
    \<open>N + U + NE + UE + NS + US \<Turnstile>pm D'\<close>


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


inductive cdcl_learn_clause :: \<open>'v prag_st \<Rightarrow> 'v prag_st \<Rightarrow> bool\<close> where
learn_clause:
  \<open>cdcl_learn_clause (M, N, U, D, NE, UE, NS, US)
    (M, add_mset C N, U, D, NE, UE, NS, US)\<close>
  if \<open>atms_of C \<subseteq> atms_of_mm (N + NE + US)\<close> and
    \<open>N +NE + NS \<Turnstile>pm C\<close> and
    \<open>count_decided M = 0\<close>


text \<open>

Subsumption-Resolution rules are the composition of resolution,
subsumption, learning of a clause, and potentially forget.

\<close>


end