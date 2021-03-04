theory Watched_Literals_Transition_System
  imports More_Sepref.WB_More_Refinement CDCL.CDCL_W_Abstract_State
    CDCL.CDCL_W_Restart  CDCL.Pragmatic_CDCL
begin

chapter \<open>Two-Watched Literals\<close>

section \<open>Rule-based system\<close>

text \<open>
  We define the calculus and map it to the pragmatic CDCL in order to inherit termination and
  correctness.


   We initially inherited directly from CDCL, but this had two issues:

   \<^item> First, there are inprocessing techniques we could not express (like subsumption-resolution, see
    the comments on PCDCL)...

   \<^item> ... however, we tried to (had to) still express some of them (mostly about handling unit
     literals), leading to more complicated proofs. Additionally all of it was an afterthought (like
     the idea that clauses containing a true literal can be removed) and was never properly
     implemented (in that case, because there was no solution for clauses containing a false
     literal).

  To overcome the issue, we decided to inherite not from CDCL, but from a different calculus devised
  exactly to express a more realistic calculus for SAT solvers.
\<close>


subsection \<open>Types and Transitions System\<close>

subsubsection \<open>Types and accessing functions\<close>

datatype 'v twl_clause =
  TWL_Clause (watched: 'v) (unwatched: 'v)

fun clause :: \<open>'a twl_clause \<Rightarrow> 'a :: {plus}\<close> where
  \<open>clause (TWL_Clause W UW) = W + UW\<close>

abbreviation clauses :: \<open>'a :: {plus} twl_clause multiset \<Rightarrow> 'a multiset\<close> where
  \<open>clauses C \<equiv> clause `# C\<close>

type_synonym 'v twl_cls = \<open>'v clause twl_clause\<close>
type_synonym 'v twl_clss = \<open>'v twl_cls multiset\<close>
type_synonym 'v clauses_to_update = \<open>('v literal \<times> 'v twl_cls) multiset\<close>
type_synonym 'v lit_queue = \<open>'v literal multiset\<close>
type_synonym 'v twl_st =
  \<open>('v, 'v clause) ann_lits \<times> 'v twl_clss \<times> 'v twl_clss \<times>
    'v clause option \<times> 'v clauses \<times> 'v clauses \<times> 'v clauses \<times> 'v clauses \<times> 'v clauses \<times> 'v clauses \<times>
    'v clauses_to_update \<times> 'v lit_queue\<close>

fun get_trail :: \<open>'v twl_st \<Rightarrow> ('v, 'v clause) ann_lit list\<close> where
  \<open>get_trail (M, _, _, _, _, _, _, _) = M\<close>

fun clauses_to_update :: \<open>'v twl_st \<Rightarrow> ('v literal \<times> 'v twl_cls) multiset\<close> where
  \<open>clauses_to_update (_, _, _, _, _, _, _, _, _, _, WS, _) = WS\<close>

fun set_clauses_to_update :: \<open>('v literal \<times> 'v twl_cls) multiset \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st\<close> where
  \<open>set_clauses_to_update WS (M, N, U, D, NE, UE, NS, US, N0, U0, _, Q) =
     (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q)\<close>

fun literals_to_update :: \<open>'v twl_st \<Rightarrow> 'v lit_queue\<close> where
  \<open>literals_to_update (_, _, _, _, _, _, _, _, _, _, _, Q) = Q\<close>

fun set_literals_to_update :: \<open>'v lit_queue \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st\<close> where
  \<open>set_literals_to_update Q (M, N, U, D, NE, UE, NS, US, N0, U0, WS, _) =
    (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q)\<close>

fun set_conflict :: \<open>'v clause \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st\<close> where
  \<open>set_conflict D (M, N, U, _, NE, UE, NS, US, WS, N0, U0, Q) =
     (M, N, U, Some D, NE, UE, NS, US, WS, N0, U0, Q)\<close>

fun get_conflict :: \<open>'v twl_st \<Rightarrow> 'v clause option\<close> where
  \<open>get_conflict (M, N, U, D, NE, UE, N0, U0, WS, Q) = D\<close>

fun get_clauses :: \<open>'v twl_st \<Rightarrow> 'v twl_clss\<close> where
  \<open>get_clauses (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q) = N + U\<close>

fun unit_clss :: \<open>'v twl_st \<Rightarrow> 'v clause multiset\<close> where
  \<open>unit_clss (M, N, U, D, NE, UE, NS, US, WS, Q) = NE + UE\<close>

fun unit_init_clauses :: \<open>'v twl_st \<Rightarrow> 'v clauses\<close> where
  \<open>unit_init_clauses (M, N, U, D, NE, UE, NS, US, WS, Q) = NE\<close>

fun subsumed_learned_clss :: \<open>'v twl_st \<Rightarrow> 'v clause multiset\<close> where
  \<open>subsumed_learned_clss (M, N, U, D, NE, UE, NS, US, WS, Q) = US\<close>

fun subsumed_init_clauses :: \<open>'v twl_st \<Rightarrow> 'v clauses\<close> where
  \<open>subsumed_init_clauses (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q) = NS\<close>

fun get_all_init_clss :: \<open>'v twl_st \<Rightarrow> 'v clause multiset\<close> where
  \<open>get_all_init_clss (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q) = clause `# N + NE + NS + N0\<close>

fun get_learned_clss :: \<open>'v twl_st \<Rightarrow> 'v twl_clss\<close> where
  \<open>get_learned_clss (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q) = U\<close>

fun subsumed_learned_clauses :: \<open>'v twl_st \<Rightarrow> 'v clauses\<close> where
  \<open>subsumed_learned_clauses (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q) = US\<close>

fun subsumed_clauses :: \<open>'v twl_st \<Rightarrow> 'v clauses\<close> where
  \<open>subsumed_clauses (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q) = NS + US\<close>

fun get_init_learned_clss :: \<open>'v twl_st \<Rightarrow> 'v clauses\<close> where
  \<open>get_init_learned_clss (_, N, U, _, _, UE, NS, US, _) = UE\<close>

fun get_all_learned_clss :: \<open>'v twl_st \<Rightarrow> 'v clauses\<close> where
  \<open>get_all_learned_clss (_, N, U, _, _, UE, NS, US, N0, U0, _) = clause `# U + UE + US + U0\<close>

fun get_all_clss :: \<open>'v twl_st \<Rightarrow> 'v clause multiset\<close> where
  \<open>get_all_clss (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q) =
     clause `# N + NE + NS + N0 + clause `# U + UE + US + U0\<close>

fun get_init_clauses0 :: \<open>'v twl_st \<Rightarrow> 'v clauses\<close> where
  \<open>get_init_clauses0 (_, N, U, _, _, UE, NS, US, N0, U0,_, _) = N0\<close>

fun get_learned_clauses0 :: \<open>'v twl_st \<Rightarrow> 'v clauses\<close> where
  \<open>get_learned_clauses0 (_, N, U, _, _, UE, NS, US, N0, U0,_, _) = U0\<close>

fun get_all_clauses0 :: \<open>'v twl_st \<Rightarrow> 'v clauses\<close> where
  \<open>get_all_clauses0 (_, N, U, _, _, UE, NS, US, N0, U0, _, _) = N0 + U0\<close>

fun update_clause where
\<open>update_clause (TWL_Clause W UW) L L' =
  TWL_Clause (add_mset L' (remove1_mset L W)) (add_mset L (remove1_mset L' UW))\<close>

text \<open>
  When updating clause, we do it non-deterministically: in case of duplicate clause in the two
  sets, one of the two can be updated (and it does not matter), contrary to an if-condition.
  In later refinement, we know where the clause comes from and update it.
\<close>
inductive update_clauses ::
  \<open>'a multiset twl_clause multiset \<times> 'a multiset twl_clause multiset \<Rightarrow>
  'a multiset twl_clause \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow>
  'a multiset twl_clause multiset \<times> 'a multiset twl_clause multiset \<Rightarrow> bool\<close> where
  \<open>D \<in># N \<Longrightarrow> update_clauses (N, U) D L L' (add_mset (update_clause D L L') (remove1_mset D N), U)\<close>
| \<open>D \<in># U \<Longrightarrow> update_clauses (N, U) D L L' (N, add_mset (update_clause D L L') (remove1_mset D U))\<close>

inductive_cases update_clausesE: \<open>update_clauses (N, U) D L L' (N', U')\<close>



subsubsection \<open>The Transition System\<close>

text \<open>We ensure that there are always \<^emph>\<open>2\<close> watched literals and that there are different. All
  clauses containing a single literal are put in \<^term>\<open>NE\<close> or \<^term>\<open>UE\<close>.\<close>

inductive cdcl_twl_cp :: \<open>'v twl_st \<Rightarrow> 'v twl_st \<Rightarrow> bool\<close> where
pop:
  \<open>cdcl_twl_cp (M, N, U, None, NE, UE, NS, US, N0, U0, {#}, add_mset L Q)
    (M, N, U, None, NE, UE, NS, US, N0, U0, {#(L, C)|C \<in># N + U. L \<in># watched C#}, Q)\<close> |
propagate:
  \<open>cdcl_twl_cp (M, N, U, None, NE, UE, NS, US, N0, U0, add_mset (L, D) WS, Q)
    (Propagated L' (clause D) # M, N, U, None, NE, UE, NS, US, N0, U0, WS, add_mset (-L') Q)\<close>
  if
    \<open>watched D = {#L, L'#}\<close> and \<open>undefined_lit M L'\<close> and \<open>\<forall>L \<in># unwatched D. -L \<in> lits_of_l M\<close> |
conflict:
  \<open>cdcl_twl_cp (M, N, U, None, NE, UE, NS, US, N0, U0, add_mset (L, D) WS, Q)
    (M, N, U, Some (clause D), NE, UE, NS, US, N0, U0, {#}, {#})\<close>
  if \<open>watched D = {#L, L'#}\<close> and \<open>-L' \<in> lits_of_l M\<close> and \<open>\<forall>L \<in># unwatched D. -L \<in> lits_of_l M\<close> |
delete_from_working:
  \<open>cdcl_twl_cp (M, N, U, None, NE, UE, NS, US, N0, U0, add_mset (L, D) WS, Q)
    (M, N, U, None, NE, UE, NS, US, N0, U0, WS, Q)\<close>
  if \<open>L' \<in># clause D\<close> and \<open>L' \<in> lits_of_l M\<close> |
update_clause:
  \<open>cdcl_twl_cp (M, N, U, None, NE, UE, NS, US, N0, U0, add_mset (L, D) WS, Q)
    (M, N', U', None, NE, UE, NS, US, N0, U0, WS, Q)\<close>
  if \<open>watched D = {#L, L'#}\<close> and \<open>-L \<in> lits_of_l M\<close> and \<open>L' \<notin> lits_of_l M\<close> and
    \<open>K \<in># unwatched D\<close> and \<open>undefined_lit M K \<or> K \<in> lits_of_l M\<close> and
    \<open>update_clauses (N, U) D L K (N', U')\<close>
    \<comment> \<open>The condition \<^term>\<open>-L \<in> lits_of_l M\<close> is already implied by \<^term>\<open>valid\<close> invariant.\<close>

inductive_cases cdcl_twl_cpE: \<open>cdcl_twl_cp S T\<close>


text \<open>We do not care about the \<^term>\<open>literals_to_update\<close> literals.\<close>
inductive cdcl_twl_o :: \<open>'v twl_st \<Rightarrow> 'v twl_st \<Rightarrow> bool\<close> where
  decide:
  \<open>cdcl_twl_o (M, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#})
     (Decided L # M, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#-L#})\<close>
  if \<open>undefined_lit M L\<close> and \<open>atm_of L \<in> atms_of_mm (clause `# N + NE + NS + N0)\<close>
| skip:
  \<open>cdcl_twl_o (Propagated L C' # M, N, U, Some D, NE, UE, NS, US, N0, U0, {#}, {#})
  (M, N, U, Some D, NE, UE, NS, US, N0, U0, {#}, {#})\<close>
  if \<open>-L \<notin># D\<close> and \<open>D \<noteq> {#}\<close>
| resolve:
  \<open>cdcl_twl_o (Propagated L C # M, N, U, Some D, NE, UE, NS, US, N0, U0, {#}, {#})
  (M, N, U, Some (cdcl\<^sub>W_restart_mset.resolve_cls L D C), NE, UE, NS, US, N0, U0, {#}, {#})\<close>
  if \<open>-L \<in># D\<close> and
    \<open>get_maximum_level (Propagated L C # M) (remove1_mset (-L) D) = count_decided M\<close>
| backtrack_unit_clause:
  \<open>cdcl_twl_o (M, N, U, Some D, NE, UE, NS, US, N0, U0, {#}, {#})
  (Propagated L {#L#} # M1, N, U, None, NE, add_mset {#L#} UE, NS, US, N0, U0, {#}, {#-L#})\<close>
  if
    \<open>L \<in># D\<close> and
    \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition M)\<close> and
    \<open>get_level M L = count_decided M\<close> and
    \<open>get_level M L = get_maximum_level M D'\<close> and
    \<open>get_maximum_level M (D' - {#L#}) \<equiv> i\<close> and
    \<open>get_level M K = i + 1\<close>
    \<open>D' = {#L#}\<close> and
    \<open>D' \<subseteq># D\<close> and
    \<open>clause `# (N + U) + NE + UE + NS + US + N0 + U0 \<Turnstile>pm D'\<close>
| backtrack_nonunit_clause:
  \<open>cdcl_twl_o (M, N, U, Some D, NE, UE, NS, US, N0, U0, {#}, {#})
     (Propagated L D' # M1, N, add_mset (TWL_Clause {#L, L'#} (D' - {#L, L'#})) U, None, NE, UE,
       NS, US, N0, U0, {#}, {#-L#})\<close>
  if
    \<open>L \<in># D\<close> and
    \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition M)\<close> and
    \<open>get_level M L = count_decided M\<close> and
    \<open>get_level M L = get_maximum_level M D'\<close> and
    \<open>get_maximum_level M (D' - {#L#}) \<equiv> i\<close> and
    \<open>get_level M K = i + 1\<close>
    \<open>D' \<noteq> {#L#}\<close> and
    \<open>D' \<subseteq># D\<close> and
    \<open>clause `# (N + U) + NE + UE + NS + US + N0 + U0 \<Turnstile>pm D'\<close> and
    \<open>L \<in># D'\<close>
    \<open>L' \<in># D'\<close> and \<comment> \<open>\<^term>\<open>L'\<close> is the new watched literal\<close>
    \<open>get_level M L' = i\<close>

inductive_cases cdcl_twl_oE: \<open>cdcl_twl_o S T\<close>

inductive cdcl_twl_stgy :: \<open>'v twl_st \<Rightarrow> 'v twl_st \<Rightarrow> bool\<close> for S :: \<open>'v twl_st\<close> where
cp: \<open>cdcl_twl_cp S S' \<Longrightarrow> cdcl_twl_stgy S S'\<close> |
other': \<open>cdcl_twl_o S S' \<Longrightarrow> cdcl_twl_stgy S S'\<close>

inductive_cases cdcl_twl_stgyE: \<open>cdcl_twl_stgy S T\<close>


subsection \<open>Definition of the Two-watched Literals Invariants\<close>

subsubsection \<open>Definitions\<close>

text \<open>The structural invariants states that there are at most two watched elements, that the watched
  literals are distinct, and that there are 2 watched literals if there are at least than two
  different literals in the full clauses.\<close>
primrec struct_wf_twl_cls :: \<open>'v multiset twl_clause \<Rightarrow> bool\<close> where
\<open>struct_wf_twl_cls (TWL_Clause W UW) \<longleftrightarrow>
   size W = 2 \<and> distinct_mset (W + UW)\<close>

fun pstate\<^sub>W_of :: \<open>'v twl_st \<Rightarrow> 'v prag_st\<close> where
\<open>pstate\<^sub>W_of (M, N, U, C, NE, UE, NS, US, N0, U0, Q) =
  (M, clause `# N, clause `# U, C, NE, UE, NS, US, N0, U0)\<close>

named_theorems twl_st \<open>Conversions simp rules\<close>

lemma [twl_st,simp]: \<open>pget_trail (pstate\<^sub>W_of S') = get_trail S'\<close>
  by (cases S') (auto simp: trail.simps)

lemma [twl_st,simp]: \<open>pget_conflict (pstate\<^sub>W_of S') = get_conflict S'\<close>
  by (cases S') (auto simp: conflicting.simps)

lemma [twl_st,simp]: \<open>cdcl\<^sub>W_restart_mset.clauses (state_of (pstate\<^sub>W_of S')) = get_all_clss S'\<close>
  by (cases S') (auto simp: clauses_def)

text \<open>TODO: could also be an abbreviation.\<close>
definition state\<^sub>W_of :: \<open>'v twl_st \<Rightarrow> 'v cdcl\<^sub>W_restart_mset\<close> where
  \<open>state\<^sub>W_of S = state_of (pstate\<^sub>W_of S)\<close>


lemma subsumed_clauses_simps[twl_st,simp]:
  \<open>subsumed_init_clauses (set_clauses_to_update K S) = subsumed_init_clauses S\<close>
  \<open>subsumed_learned_clauses (set_clauses_to_update K S) = subsumed_learned_clauses S\<close>
  \<open>subsumed_clauses (set_clauses_to_update K S) = subsumed_clauses S\<close>
  by (cases S; auto; fail)+

lemma [twl_st,simp]:
  \<open>trail (state_of (pstate\<^sub>W_of S)) = get_trail S\<close>
  \<open>trail (state\<^sub>W_of S) = get_trail S\<close>
  \<open>conflicting (state_of (pstate\<^sub>W_of S)) = get_conflict S\<close>
  \<open>conflicting (state\<^sub>W_of S) = get_conflict S\<close>
  \<open>conflicting (state_of T) = pget_conflict T\<close>
  by (cases S; cases T; auto simp: state\<^sub>W_of_def; fail)+

text \<open>
  The invariant on the clauses is the following:
  \<^item> the structure is correct (the watched part is of length exactly two).
  \<^item> if we do not have to update the clause, then the invariant holds.
\<close>
definition twl_is_an_exception :: \<open>'a multiset twl_clause \<Rightarrow> 'a multiset \<Rightarrow>
     ('b \<times> 'a multiset twl_clause) multiset \<Rightarrow> bool\<close>
where
\<open>twl_is_an_exception C Q WS \<longleftrightarrow>
   (\<exists>L. L \<in># Q \<and> L \<in># watched C) \<or> (\<exists>L. (L, C) \<in># WS)\<close>

definition is_blit :: \<open>('a, 'b) ann_lits \<Rightarrow> 'a clause \<Rightarrow> 'a literal \<Rightarrow> bool\<close>where
  [simp]: \<open>is_blit M D L \<longleftrightarrow> (L \<in># D \<and> L \<in> lits_of_l M)\<close>

definition has_blit :: \<open>('a, 'b) ann_lits \<Rightarrow> 'a clause \<Rightarrow> 'a literal \<Rightarrow> bool\<close>where
  \<open>has_blit M D L' \<longleftrightarrow> (\<exists>L. is_blit M D L \<and> get_level M L \<le> get_level M L')\<close>

text \<open>This invariant state that watched literals are set at the end and are not swapped with an
  unwatched literal later.\<close>
fun twl_lazy_update :: \<open>('a, 'b) ann_lits \<Rightarrow> 'a twl_cls \<Rightarrow> bool\<close> where
\<open>twl_lazy_update M (TWL_Clause W UW) \<longleftrightarrow>
  (\<forall>L. L \<in># W \<longrightarrow> -L \<in> lits_of_l M \<longrightarrow> \<not>has_blit M (W+UW) L \<longrightarrow>
    (\<forall>K \<in># UW. get_level M L \<ge> get_level M K \<and> -K \<in> lits_of_l M))\<close>

text \<open>
  If one watched literals has been assigned to false (\<^term>\<open>-L \<in> lits_of_l M\<close>) and the clause
  has not yet been updated (\<^term>\<open>L' \<notin> lits_of_l M\<close>: it should be removed either by
  updating \<open>L\<close>, propagating \<open>L'\<close>, or marking the conflict), then the literals \<^term>\<open>L\<close> is of
  maximal level.
\<close>
fun watched_literals_false_of_max_level :: \<open>('a, 'b) ann_lits \<Rightarrow> 'a twl_cls \<Rightarrow> bool\<close> where
\<open>watched_literals_false_of_max_level M (TWL_Clause W UW) \<longleftrightarrow>
  (\<forall>L. L \<in># W \<longrightarrow> -L \<in> lits_of_l M \<longrightarrow> \<not>has_blit M (W+UW) L \<longrightarrow>
    get_level M L = count_decided M)\<close>

text \<open>
  This invariants talks about the enqueued literals:
  \<^item> the working stack contains a single literal;
  \<^item> the working stack and the \<^term>\<open>literals_to_update\<close> literals are false with respect to the
   trail and there are no duplicates;
  \<^item> and the latter condition holds even when \<^term>\<open>WS = {#}\<close>.\<close>
fun no_duplicate_queued :: \<open>'v twl_st \<Rightarrow> bool\<close> where
\<open>no_duplicate_queued (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q) \<longleftrightarrow>
  (\<forall>C C'. C \<in># WS \<longrightarrow> C' \<in># WS \<longrightarrow> fst C = fst C') \<and>
  (\<forall>C. C \<in># WS \<longrightarrow> add_mset (fst C) Q \<subseteq># uminus `# lit_of `# mset M) \<and>
  Q \<subseteq># uminus `# lit_of `# mset M\<close>

lemma no_duplicate_queued_alt_def:
   \<open>no_duplicate_queued S =
    ((\<forall>C C'. C \<in># clauses_to_update S \<longrightarrow> C' \<in># clauses_to_update S \<longrightarrow> fst C = fst C') \<and>
     (\<forall>C. C \<in># clauses_to_update S \<longrightarrow>
       add_mset (fst C) (literals_to_update S) \<subseteq># uminus `# lit_of `# mset (get_trail S)) \<and>
     literals_to_update S \<subseteq># uminus `# lit_of `# mset (get_trail S))\<close>
  by (cases S) auto

fun distinct_queued :: \<open>'v twl_st \<Rightarrow> bool\<close> where
\<open>distinct_queued (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q) \<longleftrightarrow>
  distinct_mset Q \<and>
  (\<forall>L C. count WS (L, C) \<le> count (N + U) C)\<close>

text \<open>
  These are the conditions to indicate that the 2-WL invariant does not hold and is not
  \<^term>\<open>literals_to_update\<close>.
\<close>
fun clauses_to_update_prop where
  \<open>clauses_to_update_prop Q M (L, C) \<longleftrightarrow>
      (L \<in># watched C \<and> -L \<in> lits_of_l M \<and> L \<notin># Q \<and> \<not>has_blit M (clause C) L)\<close>
declare clauses_to_update_prop.simps[simp del]

text \<open>
  This invariants talks about the enqueued literals:
  \<^item> all clauses that should be updated are in \<^term>\<open>WS\<close> and are repeated often enough in it.
  \<^item> if \<^term>\<open>WS = {#}\<close>, then there are no clauses to updated that is not enqueued;
  \<^item> all clauses to updated are either in \<^term>\<open>WS\<close> or \<^term>\<open>Q\<close>.

  The first two conditions are written that way to please Isabelle.\<close>

fun clauses_to_update_inv :: \<open>'v twl_st \<Rightarrow> bool\<close> where
  \<open>clauses_to_update_inv (M, N, U, None, NE, UE, NS, US, N0, U0, WS, Q) \<longleftrightarrow>
     (\<forall>L C. ((L, C) \<in># WS \<longrightarrow> {#(L, C)| C \<in># N + U. clauses_to_update_prop Q M (L, C)#} \<subseteq># WS)) \<and>
     (\<forall>L. WS = {#} \<longrightarrow> {#(L, C)| C \<in># N + U. clauses_to_update_prop Q M (L, C)#} = {#}) \<and>
     (\<forall>L C. C \<in># N + U \<longrightarrow> L \<in># watched C \<longrightarrow> -L \<in> lits_of_l M \<longrightarrow> \<not>has_blit M (clause C) L \<longrightarrow>
       (L, C) \<notin># WS \<longrightarrow> L \<in># Q)\<close>
| \<open>clauses_to_update_inv (M, N, U, D, NE, UE, NS, US, WS, Q) \<longleftrightarrow> True\<close>

text \<open>
  This is the invariant of the 2WL structure: if one watched literal is false, then all unwatched
  are false.
\<close>
fun twl_exception_inv :: \<open>'v twl_st \<Rightarrow>  'v twl_cls \<Rightarrow> bool\<close> where
  \<open>twl_exception_inv (M, N, U, None, NE, UE, NS, US, N0, U0, WS, Q) C \<longleftrightarrow>
    (\<forall>L. L \<in># watched C \<longrightarrow> -L \<in> lits_of_l M \<longrightarrow> \<not>has_blit M (clause C) L \<longrightarrow>
      L \<notin># Q \<longrightarrow> (L, C) \<notin># WS \<longrightarrow>
      (\<forall>K \<in># unwatched C. -K \<in> lits_of_l M))\<close>
| \<open>twl_exception_inv (M, N, U, D, NE, UE, NS, US, WS, Q) C \<longleftrightarrow> True\<close>

declare twl_exception_inv.simps[simp del]

fun twl_st_exception_inv :: \<open>'v twl_st \<Rightarrow> bool\<close> where
\<open>twl_st_exception_inv (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q) \<longleftrightarrow>
  (\<forall>C \<in># N + U. twl_exception_inv (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q) C)\<close>


text \<open>Candidats for propagation (i.e., the clause where only one literals is non
  assigned) are enqueued.\<close>
fun propa_cands_enqueued :: \<open>'v twl_st \<Rightarrow> bool\<close> where
  \<open>propa_cands_enqueued (M, N, U, None, NE, UE, NS, US, N0, U0, WS, Q) \<longleftrightarrow>
    (\<forall>L C. C \<in># N+U \<longrightarrow> L \<in># clause C \<longrightarrow> M \<Turnstile>as CNot (remove1_mset L (clause C)) \<longrightarrow>
      undefined_lit M L \<longrightarrow>
      (\<exists>L'. L' \<in># watched C \<and> L' \<in># Q) \<or> (\<exists>L. (L, C) \<in># WS))\<close>
  | \<open>propa_cands_enqueued (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q) \<longleftrightarrow> True\<close>

fun confl_cands_enqueued :: \<open>'v twl_st \<Rightarrow> bool\<close> where
  \<open>confl_cands_enqueued (M, N, U, None, NE, UE, NS, US, N0, U0, WS, Q) \<longleftrightarrow>
     (\<forall>C \<in># N + U. M \<Turnstile>as CNot (clause C) \<longrightarrow>
       (\<exists>L'. L' \<in># watched C \<and> L' \<in># Q) \<or> (\<exists>L. (L, C) \<in># WS))\<close>
| \<open>confl_cands_enqueued (M, N, U, Some _, NE, UE, NS, US, N0, U0, WS, Q) \<longleftrightarrow>
     True\<close>

fun propa_confl_cands_enqueued :: \<open>'v twl_st \<Rightarrow> bool\<close> where
  \<open>propa_confl_cands_enqueued (M, N, U, None, NE, UE, NS, US, N0, U0, WS, Q) \<longleftrightarrow>
     (\<forall>C \<in># N + U. \<forall>L \<in># clause C. M \<Turnstile>as CNot (clause C - {#L#}) \<longrightarrow> L \<notin> lits_of_l M \<longrightarrow>
       (\<exists>L'. L' \<in># watched C \<and> L' \<in># Q) \<or> (\<exists>L. (L, C) \<in># WS))\<close>
| \<open>propa_confl_cands_enqueued (M, N, U, Some _, NE, UE, NS, US, N0, U0, WS, Q) \<longleftrightarrow>
     True\<close>

lemma propa_confl_cands_enqueued_propa_confl_enqueued:
  assumes \<open>\<forall>C \<in># get_clauses S. struct_wf_twl_cls C\<close> and \<open>no_dup (get_trail S)\<close>
  shows \<open>propa_confl_cands_enqueued S \<longleftrightarrow> propa_cands_enqueued S \<and> confl_cands_enqueued S\<close>
  using assms
  apply (cases S; cases \<open>get_conflict S\<close>)
  apply (auto dest!: multi_member_split simp: Decided_Propagated_in_iff_in_lits_of_l no_dup_consistentD)
  apply (case_tac C; case_tac \<open>watched C\<close>)
  apply (clarsimp_all simp: imp_conjR all_conj_distrib no_dup_consistentD)
  apply (case_tac C; case_tac \<open>watched C\<close>)
  apply (clarsimp_all simp: imp_conjR all_conj_distrib no_dup_consistentD)
  done

text \<open>This invariant talk about the decomposition of the trail and the invariants that holds in
  these states.\<close>
fun past_invs :: \<open>'v twl_st \<Rightarrow> bool\<close> where
  \<open>past_invs (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q) \<longleftrightarrow>
    (\<forall>M1 M2 K. M = M2 @ Decided K # M1 \<longrightarrow> (
      (\<forall>C \<in># N + U. twl_lazy_update M1 C \<and>
        watched_literals_false_of_max_level M1 C \<and>
        twl_exception_inv (M1, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#}) C) \<and>
      confl_cands_enqueued (M1, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#}) \<and>
      propa_cands_enqueued (M1, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#}) \<and>
      clauses_to_update_inv (M1, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#})))\<close>
declare past_invs.simps[simp del]

fun twl_st_inv :: \<open>'v twl_st \<Rightarrow> bool\<close> where
\<open>twl_st_inv (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q) \<longleftrightarrow>
  (\<forall>C \<in># N + U. struct_wf_twl_cls C) \<and>
  (\<forall>C \<in># N + U. D = None \<longrightarrow> \<not>twl_is_an_exception C Q WS \<longrightarrow> (twl_lazy_update M C)) \<and>
  (\<forall>C \<in># N + U. D = None \<longrightarrow> watched_literals_false_of_max_level M C)\<close>

lemma twl_st_inv_alt_def:
  \<open>twl_st_inv S \<longleftrightarrow>
  (\<forall>C \<in># get_clauses S. struct_wf_twl_cls C) \<and>
  (\<forall>C \<in># get_clauses S. get_conflict S = None \<longrightarrow>
     \<not>twl_is_an_exception C (literals_to_update S) (clauses_to_update S) \<longrightarrow>
     (twl_lazy_update (get_trail S) C)) \<and>
  (\<forall>C \<in># get_clauses S. get_conflict S = None \<longrightarrow>
     watched_literals_false_of_max_level (get_trail S) C)\<close>
  by (cases S) (auto simp: twl_st_inv.simps)

text \<open>
  \<^term>\<open>literals_to_update\<close> literals are of maximum level and their negation is in the trail.
\<close>
fun valid_enqueued :: \<open>'v twl_st \<Rightarrow> bool\<close> where
\<open>valid_enqueued (M, N, U, C, NE, UE, NS, US, N0, U0, WS, Q) \<longleftrightarrow>
  (\<forall>(L, C) \<in># WS. L \<in># watched C \<and> C \<in># N + U \<and> -L \<in> lits_of_l M \<and>
     get_level M L = count_decided M) \<and>
  (\<forall>L \<in># Q. -L \<in> lits_of_l M \<and> get_level M L = count_decided M)\<close>

text \<open>Putting invariants together:\<close>
definition twl_struct_invs :: \<open>'v twl_st \<Rightarrow> bool\<close> where
  \<open>twl_struct_invs S \<longleftrightarrow>
    (twl_st_inv S \<and>
    valid_enqueued S \<and>
    pcdcl_all_struct_invs (pstate\<^sub>W_of S) \<and>
    cdcl\<^sub>W_restart_mset.no_smaller_propa (state\<^sub>W_of S) \<and>
    twl_st_exception_inv S \<and>
    no_duplicate_queued S \<and>
    distinct_queued S \<and>
    confl_cands_enqueued S \<and>
    propa_cands_enqueued S \<and>
    (get_conflict S \<noteq> None \<longrightarrow> clauses_to_update S = {#} \<and> literals_to_update S = {#}) \<and>
    clauses_to_update_inv S \<and>
    past_invs S)
  \<close>

definition twl_stgy_invs :: \<open>'v twl_st \<Rightarrow> bool\<close> where
  \<open>twl_stgy_invs S \<longleftrightarrow>
     cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state\<^sub>W_of S) \<and>
     cdcl\<^sub>W_restart_mset.conflict_non_zero_unless_level_0 (state\<^sub>W_of S)\<close>


subsubsection \<open>Initial properties\<close>

lemma twl_is_an_exception_add_mset_to_queue: \<open>twl_is_an_exception C (add_mset L Q) WS \<longleftrightarrow>
  (twl_is_an_exception C Q WS \<or> (L \<in># watched C))\<close>
  unfolding twl_is_an_exception_def by auto

lemma twl_is_an_exception_add_mset_to_clauses_to_update:
  \<open>twl_is_an_exception C Q (add_mset (L, D) WS) \<longleftrightarrow> (twl_is_an_exception C Q WS \<or> C = D)\<close>
  unfolding twl_is_an_exception_def by auto

lemma twl_is_an_exception_empty[simp]: \<open>\<not>twl_is_an_exception C {#} {#}\<close>
  unfolding twl_is_an_exception_def by auto

lemma twl_inv_empty_trail:
  shows
    \<open>watched_literals_false_of_max_level [] C\<close> and
    \<open>twl_lazy_update [] C\<close>
  by (solves \<open>cases C; auto\<close>)+

lemma clauses_to_update_inv_cases[case_names WS_nempty WS_empty Q]:
  assumes
    \<open>\<And>L C. (L, C) \<in># WS \<Longrightarrow> {#(L, C)| C \<in># N + U. clauses_to_update_prop Q M (L, C)#} \<subseteq># WS\<close> and
    \<open>\<And>L. WS = {#} \<Longrightarrow> {#(L, C)| C \<in># N + U. clauses_to_update_prop Q M (L, C)#} = {#}\<close> and
    \<open>\<And>L C. C \<in># N + U \<Longrightarrow> L \<in># watched C \<Longrightarrow> -L \<in> lits_of_l M \<Longrightarrow> \<not>has_blit M (clause C) L \<Longrightarrow>
       (L, C) \<notin># WS \<Longrightarrow> L \<in># Q\<close>
  shows
    \<open>clauses_to_update_inv (M, N, U, None, NE, UE, NS, US, N0, U0, WS, Q)\<close>
  using assms unfolding clauses_to_update_inv.simps by blast

lemma
  assumes \<open>\<And>C. C \<in># N + U \<Longrightarrow> struct_wf_twl_cls C\<close>
  shows
    twl_st_inv_empty_trail: \<open>twl_st_inv ([], N, U, C, NE, UE, NS, US, N0, U0, WS, Q)\<close>
  by (auto simp: assms twl_inv_empty_trail)

lemma
  shows
    no_duplicate_queued_no_queued: \<open>no_duplicate_queued (M, N, U, D, NE, UE, NS, US, N0, U0, {#}, {#})\<close> and
    no_distinct_queued_no_queued: \<open>distinct_queued ([], N, U, D, NE, UE, NS, US, N0, U0, {#}, {#})\<close>
  by auto

lemma twl_st_inv_add_mset_clauses_to_update:
  assumes \<open>D \<in># N + U\<close>
  shows \<open>twl_st_inv (M, N, U, None, NE, UE, NS, US, N0, U0, WS, Q)
  \<longleftrightarrow> twl_st_inv (M, N, U, None, NE, UE, NS, US, N0, U0, add_mset (L, D) WS, Q) \<and>
    (\<not> twl_is_an_exception D Q WS \<longrightarrow>twl_lazy_update M D)\<close>
  using assms by (auto simp: twl_is_an_exception_add_mset_to_clauses_to_update)

lemma twl_st_simps:
\<open>twl_st_inv (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q) \<longleftrightarrow>
  (\<forall>C \<in># N + U. struct_wf_twl_cls C \<and>
    (D = None \<longrightarrow> (\<not>twl_is_an_exception C Q WS \<longrightarrow> twl_lazy_update M C) \<and>
    watched_literals_false_of_max_level M C))\<close>
  unfolding twl_st_inv.simps by fast

lemma propa_cands_enqueued_unit_clause:
  \<open>propa_cands_enqueued (M, N, U, C, add_mset L NE, UE, NS, US, N0, U0, WS, Q) \<longleftrightarrow>
    propa_cands_enqueued (M, N, U, C, {#}, {#}, NS, US, N0, U0, WS, Q)\<close>
  \<open>propa_cands_enqueued (M, N, U, C, NE, add_mset L UE, NS, US, N0, U0, WS, Q) \<longleftrightarrow>
    propa_cands_enqueued (M, N, U, C, {#}, {#}, NS, US, N0, U0, WS, Q)\<close>
  by (cases C; auto)+

lemma past_invs_enqueud: \<open>past_invs (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q) \<longleftrightarrow>
  past_invs (M, N, U, D, NE, UE, NS, US, N0, U0, {#}, {#})\<close>
  unfolding past_invs.simps by simp

lemma confl_cands_enqueued_unit_clause:
  \<open>confl_cands_enqueued (M, N, U, C, add_mset L NE, UE, NS, US, N0, U0, WS, Q) \<longleftrightarrow>
    confl_cands_enqueued (M, N, U, C, {#}, {#}, NS, US, N0, U0, WS, Q)\<close>
  \<open>confl_cands_enqueued (M, N, U, C, NE, add_mset L UE, NS, US, N0, U0, WS, Q) \<longleftrightarrow>
    confl_cands_enqueued (M, N, U, C, {#}, {#}, NS, US, N0, U0, WS, Q)\<close>
  by (cases C; auto)+

lemma twl_inv_decomp:
  assumes
    lazy: \<open>twl_lazy_update M C\<close> and
    decomp: \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition M)\<close> and
    n_d: \<open>no_dup M\<close>
  shows
    \<open>twl_lazy_update M1 C\<close>
proof -
  obtain W UW where C: \<open>C = TWL_Clause W UW\<close> by (cases C)
  obtain M3 where M: \<open>M = M3 @ M2 @ Decided K # M1\<close>
    using decomp by blast
  define M' where M': \<open>M' = M3 @ M2 @ [Decided K]\<close>
  have MM': \<open>M = M' @ M1\<close>
    by (auto simp: M M')
  have lev_M_M1: \<open>get_level M L = get_level M1 L\<close> if \<open>L \<in> lits_of_l M1\<close> for L
  proof -
    have LM: \<open>L \<in> lits_of_l M\<close>
      using that unfolding M by auto
    have \<open>undefined_lit M' L\<close>
      by (rule no_dup_append_in_atm_notin)
        (use that n_d in \<open>auto simp: M M' defined_lit_map\<close>)
    then show lev_L_M1: \<open>get_level M L = get_level M1 L\<close>
      using that n_d by (auto simp: M image_Un M')
  qed

  show \<open>twl_lazy_update M1 C\<close>
    unfolding C twl_lazy_update.simps
  proof (intro allI impI)
    fix L
    assume
      W: \<open>L \<in># W\<close> and
      uL: \<open>- L \<in> lits_of_l M1\<close> and
      L': \<open>\<not>has_blit M1 (W+UW) L\<close>

    then have lev_L_M1: \<open>get_level M L = get_level M1 L\<close>
      using uL n_d lev_M_M1[of \<open>-L\<close>] by auto

    have L'M: \<open>\<not>has_blit M (W+UW) L\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then obtain L' where
        b: \<open>is_blit M (W+UW) L'\<close> and
        lev_L'_L: \<open>get_level M L' \<le> get_level M L\<close>unfolding has_blit_def by auto
      then have L'M': \<open>L' \<in> lits_of_l M'\<close>
        using L' MM' W lev_L_M1 lev_M_M1 unfolding has_blit_def by auto
      moreover {
        have \<open>atm_of L' \<in> atm_of ` lits_of_l M'\<close>
          using L'M' by (simp add: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set)
        moreover have \<open>Decided K \<in>set (dropWhile (\<lambda>S. atm_of (lit_of S) \<noteq> atm_of K') M')\<close>
          if \<open>K' \<in> lits_of_l M'\<close> for K'
          unfolding M' append_assoc[symmetric] by (rule last_in_set_dropWhile)
            (use that in \<open>auto simp: lits_of_def M' MM'\<close>)
        ultimately have \<open>get_level M L' > count_decided M1\<close>
          unfolding MM' by (force simp: filter_empty_conv get_level_def count_decided_def
              lits_of_def) }
      ultimately show False
        using lev_M_M1[of \<open>-L\<close>] uL count_decided_ge_get_level[of M1 \<open>-L\<close>] lev_L'_L by auto
    qed

    show \<open>\<forall>K\<in>#UW. get_level M1 K \<le> get_level M1 L \<and> -K \<in> lits_of_l M1\<close>
    proof clarify
      fix K''
      assume \<open>K'' \<in># UW\<close>
      then have
        lev_K'_L: \<open>get_level M K'' \<le> get_level M L\<close> and
        uK'_M: \<open>-K'' \<in> lits_of_l M\<close>
        using lazy W uL L'M unfolding C MM' by auto
      then have uK'_M1: \<open>- K'' \<in> lits_of_l M1\<close>
        using uK'_M unfolding  M apply (auto simp: get_level_append_if
            split: if_splits)
        using M' MM' n_d uL count_decided_ge_get_level[of M1 L]
        by (auto dest: defined_lit_no_dupD in_lits_of_l_defined_litD
            simp: get_level_cons_if atm_of_eq_atm_of
            split: if_splits)
      have \<open>get_level M K'' = get_level M1 K''\<close>
      proof (rule ccontr, cases \<open>defined_lit M' K''\<close>)
        case False
        moreover assume \<open>get_level M K'' \<noteq> get_level M1 K''\<close>
        ultimately show False unfolding MM' by auto
      next
        case True
        assume K'': \<open>get_level M K'' \<noteq> get_level M1 K''\<close>
        have \<open>get_level M' K'' = 0\<close>
        proof -
          have a1: \<open>get_level M' K'' + count_decided M1 \<le> get_level M1 L\<close>
            using lev_K'_L unfolding lev_L_M1 unfolding MM' get_level_skip_end[OF True] .
          then have \<open>count_decided M1 \<le> get_level M1 L\<close>
            by linarith
          then have \<open>get_level M1 L = count_decided M1\<close>
            using count_decided_ge_get_level le_antisym by blast
          then show ?thesis
            using a1 by linarith
        qed
        moreover have \<open>Decided K \<in> set (dropWhile (\<lambda>S. atm_of (lit_of S) \<noteq> atm_of K'') M')\<close>
          unfolding M' append_assoc[symmetric] by (rule last_in_set_dropWhile)
            (use True in \<open>auto simp: lits_of_def M' MM' defined_lit_map\<close>)
        ultimately show False
          by (auto simp: M' filter_empty_conv get_level_def)
      qed
      then show \<open>get_level M1 K'' \<le> get_level M1 L \<and> -K'' \<in> lits_of_l M1\<close>
        using lev_M_M1[OF uL] lev_K'_L uK'_M uK'_M1 by auto
    qed
  qed
qed

declare twl_st_inv.simps[simp del]

lemma has_blit_Cons[simp]:
  assumes blit: \<open>has_blit M C L\<close> and n_d: \<open>no_dup (K # M)\<close>
  shows \<open>has_blit (K # M) C L\<close>
proof -
  obtain L' where
    \<open>is_blit M C L'\<close> and
    \<open>get_level M L' \<le> get_level M L\<close>
    using blit unfolding has_blit_def by auto
  then have
    \<open>is_blit (K # M) C L'\<close> and
    \<open>get_level (K # M) L' \<le> get_level (K # M) L\<close>
    using n_d by (auto simp add: has_blit_def get_level_cons_if atm_of_eq_atm_of
      dest: in_lits_of_l_defined_litD)
  then show ?thesis
    unfolding has_blit_def by blast
qed


lemma is_blit_Cons:
  \<open>is_blit (K # M) C L \<longleftrightarrow> (L = lit_of K \<and> lit_of K \<in># C) \<or> is_blit M C L\<close>
  by (auto simp: has_blit_def)

lemma no_has_blit_propagate:
  \<open>\<not>has_blit (Propagated L D # M) (W + UW) La \<Longrightarrow>
    undefined_lit M L \<Longrightarrow> no_dup M \<Longrightarrow> \<not>has_blit M (W + UW) La\<close>
  apply (auto simp: has_blit_def get_level_cons_if
    dest: in_lits_of_l_defined_litD
     split:  cong: if_cong)
  apply (smt atm_lit_of_set_lits_of_l count_decided_ge_get_level defined_lit_map image_eqI)
  by (smt atm_lit_of_set_lits_of_l count_decided_ge_get_level defined_lit_map image_eqI)

lemma no_has_blit_propagate':
  \<open>\<not>has_blit (Propagated L D # M) (clause C) La \<Longrightarrow>
    undefined_lit M L \<Longrightarrow> no_dup M \<Longrightarrow> \<not>has_blit M (clause C) La\<close>
  using no_has_blit_propagate[of L D M \<open>watched C\<close> \<open>unwatched C\<close>]
  by (cases C) auto


lemma no_has_blit_decide:
  \<open>\<not>has_blit (Decided L # M) (W + UW) La \<Longrightarrow>
    undefined_lit M L \<Longrightarrow> no_dup M \<Longrightarrow> \<not>has_blit M (W + UW) La\<close>
  apply (auto simp: has_blit_def get_level_cons_if
    dest: in_lits_of_l_defined_litD
     split:  cong: if_cong)
  apply (smt count_decided_ge_get_level defined_lit_map in_lits_of_l_defined_litD le_SucI)
  apply (smt count_decided_ge_get_level defined_lit_map in_lits_of_l_defined_litD le_SucI)
  done

lemma no_has_blit_decide':
  \<open>\<not>has_blit (Decided L # M) (clause C) La \<Longrightarrow>
    undefined_lit M L \<Longrightarrow> no_dup M \<Longrightarrow> \<not>has_blit M (clause C) La\<close>
  using no_has_blit_decide[of L M \<open>watched C\<close> \<open>unwatched C\<close>]
  by (cases C) auto

lemma twl_lazy_update_Propagated:
  assumes
    W: \<open>L \<in># W\<close> and n_d: \<open>no_dup (Propagated L D # M)\<close> and
    lazy: \<open>twl_lazy_update M (TWL_Clause W UW)\<close>
  shows
    \<open>twl_lazy_update (Propagated L D # M) (TWL_Clause W UW)\<close>
  unfolding twl_lazy_update.simps
proof (intro conjI impI allI)
  fix La
  assume
    La: \<open>La \<in># W\<close> and
    uL_M: \<open>- La \<in> lits_of_l (Propagated L D # M)\<close> and
    b: \<open>\<not> has_blit (Propagated L D # M) (W + UW) La\<close>
  have b': \<open>\<not>has_blit M (W + UW) La\<close>
    apply (rule no_has_blit_propagate[OF b])
    using assms by auto

  have \<open>- La \<in> lits_of_l M \<longrightarrow> (\<forall>K\<in>#UW. get_level M K \<le> get_level M La \<and> - K \<in> lits_of_l M)\<close>
    using lazy assms b' uL_M La unfolding twl_lazy_update.simps
    by blast
  then consider
     \<open>\<forall>K\<in>#UW. get_level M K \<le> get_level M La \<and> -K \<in> lits_of_l M\<close> and \<open>La \<noteq> -L\<close> |
     \<open>La = -L\<close>
    using b' uL_M La
    by (simp only: list.set(2) lits_of_insert insert_iff uminus_lit_swap)
      fastforce
  then show \<open>\<forall>K\<in>#UW. get_level (Propagated L D # M) K \<le> get_level (Propagated L D # M) La \<and>
             -K \<in> lits_of_l (Propagated L D # M)\<close>
  proof cases
    case 1
    have [simp]: \<open>has_blit (Propagated L D # M) (W + UW) L\<close> if \<open>L \<in># W+UW\<close>
      using that unfolding has_blit_def apply -
      by (rule exI[of _ L]) (auto simp: get_level_cons_if atm_of_eq_atm_of)
    show ?thesis
      using n_d b 1 b' uL_M
      by (auto simp: get_level_cons_if atm_of_eq_atm_of
          count_decided_ge_get_level Decided_Propagated_in_iff_in_lits_of_l
          dest!: multi_member_split)
  next
    case 2
    have [simp]: \<open>has_blit (Propagated L D # M) (W + UW) (-L)\<close>
      using 2 La W unfolding has_blit_def apply -
      by (rule exI[of _ L])
        (auto simp: get_level_cons_if atm_of_eq_atm_of)
    show ?thesis
      using 2 b count_decided_ge_get_level[of \<open>Propagated L D # M\<close>]
      by (auto simp: uminus_lit_swap split: if_splits)
  qed
qed

lemma pair_in_image_Pair:
  \<open>(La, C) \<in> Pair L ` D \<longleftrightarrow> La = L \<and> C \<in> D\<close>
  by auto

lemma image_Pair_subset_mset:
  \<open>Pair L `# A \<subseteq># Pair L `# B \<longleftrightarrow> A \<subseteq># B\<close>
proof -
  have [simp]: \<open>remove1_mset (L, x) (Pair L `# B) = Pair L `# (remove1_mset x B)\<close> for x :: 'b and B
  proof -
    have \<open>(L, x) \<in># Pair L `# B \<longrightarrow> x \<in># B\<close>
      by force
    then show ?thesis
      by (metis (no_types) diff_single_trivial image_mset_remove1_mset_if)
  qed
  show ?thesis
    by (induction A arbitrary: B)  (auto simp: insert_subset_eq_iff)
qed

lemma count_image_mset_Pair2:
  \<open>count {#(L, x). L \<in># M x#} (L, C) = (if x = C then count (M x) L else 0)\<close>
proof -
  have \<open>count (M C) L = count {#L. L\<in>#M C#} L\<close>
    by simp
  also have \<open>\<dots> = count ((\<lambda>L. Pair L C) `# {#L. L\<in>#M C#}) ((\<lambda>L. Pair L C) L)\<close>
    by (subst (2) count_image_mset_inj) (simp_all add: inj_on_def)
  finally have C: \<open>count {#(L, C). L \<in># {#L. L \<in># M C#}#} (L, C) = count (M C) L\<close> ..

  show ?thesis
  apply (cases \<open>x \<noteq> C\<close>)
   apply (auto simp: not_in_iff[symmetric] count_image_mset; fail)[]
  using C by simp
qed

lemma lit_of_inj_on_no_dup: \<open>no_dup M \<Longrightarrow> inj_on (\<lambda>x. - lit_of x) (set M)\<close>
  by (induction M) (auto simp: no_dup_def)

lemma
  assumes
    cdcl: \<open>cdcl_twl_cp S T\<close> and
    twl: \<open>twl_st_inv S\<close> and
    twl_excep: \<open>twl_st_exception_inv S\<close> and
    valid: \<open>valid_enqueued S\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S)\<close> and
    no_dup: \<open>no_duplicate_queued S\<close> and
    dist_q: \<open>distinct_queued S\<close> and
    ws: \<open>clauses_to_update_inv S\<close>
  shows twl_cp_twl_st_exception_inv: \<open>twl_st_exception_inv T\<close> and
    twl_cp_clauses_to_update: \<open>clauses_to_update_inv T\<close>
  using cdcl twl twl_excep valid inv no_dup ws
proof (induction rule: cdcl_twl_cp.induct)
  case (pop M N U NE UE N0 U0 L Q)
  case 1 note _ = this(2)
  then show ?case unfolding twl_st_inv.simps twl_is_an_exception_def
    by (fastforce simp add: pair_in_image_Pair image_constant_conv uminus_lit_swap
        twl_exception_inv.simps)
  case 2 note twl = this(1) and ws = this(6)
  have struct: \<open>struct_wf_twl_cls C\<close> if \<open>C \<in># N + U\<close> for C
    using twl that by (simp add: twl_st_inv.simps)
  have H: \<open>count (watched C) L \<le> 1\<close> if \<open>C \<in># N + U\<close> for C L
    using struct[OF that] by (cases C) (auto simp add: twl_st_inv.simps size_2_iff)
  have sum_le_count: \<open>(\<Sum>x\<in>#N+U. count {#(L, x). L \<in># watched x#} (a, b)) \<le> count (N+U) b\<close>
    for a b
    apply (subst (2) count_sum_mset_if_1_0)
    apply (rule sum_mset_mono)
    using H apply (auto simp: count_image_mset_Pair2)
    done
  define NU where NU[symmetric]: \<open>NU = N + U\<close>
  show ?case
    using ws by (fastforce simp add: pair_in_image_Pair multiset_filter_mono2 image_Pair_subset_mset
        clauses_to_update_prop.simps NU filter_mset_empty_conv)
next
  case (propagate D L L' M N U NE UE NS US N0 U0 WS Q) note watched = this(1) and undef = this(2) and
    unw = this(3)

  case 1
  note twl = this(1) and twl_excep = this(2) and valid = this(3) and inv = this(4) and
    no_dup = this(5) and ws = this(6)
  have [simp]: \<open>- L' \<notin> lits_of_l M\<close>
    using Decided_Propagated_in_iff_in_lits_of_l propagate.hyps(2) by blast
  have D_N_U: \<open>D \<in># N + U\<close> and lev_L: \<open>get_level M L = count_decided M\<close>
    using valid by auto
  then have wf_D: \<open>struct_wf_twl_cls D\<close>
    using twl by (simp add: twl_st_inv.simps)
  have \<open>\<forall>s\<in>#clause `# U. \<not> tautology s\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def by (simp_all add: cdcl\<^sub>W_restart_mset_state
        state\<^sub>W_of_def)
  have n_d: \<open>no_dup M\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: trail.simps state\<^sub>W_of_def)
  have [simp]: \<open>L \<noteq> L'\<close>
    using wf_D watched by (cases D) auto
  have [simp]: \<open>- L \<in> lits_of_l M\<close>
    using valid by auto
  then have [simp]: \<open>L \<notin> lits_of_l M\<close>
    using n_d no_dup_consistentD by blast
  obtain NU where NU: \<open>N + U = add_mset D NU\<close>
    by (metis D_N_U insert_DiffM)
  have [simp]: \<open>has_blit (Propagated L' (add_mset L (add_mset L' x2)) # M)
              (add_mset L (add_mset L' x2)) L\<close> for x2
    unfolding has_blit_def
    by (rule exI[of _ L'])
      (use lev_L in \<open>auto simp: get_level_cons_if\<close>)
  have HH: \<open>\<not>clauses_to_update_prop (add_mset (-L') Q) (Propagated L' (clause D) # M) (L, D)\<close>
    using watched unfolding clauses_to_update_prop.simps by (cases D) (auto simp: watched)
  have \<open>add_mset L Q \<subseteq># {#- lit_of x. x \<in># mset M#}\<close>
    using no_dup by (auto)
  moreover have \<open>distinct_mset {#- lit_of x. x \<in># mset M#}\<close>
    by (subst distinct_image_mset_inj)
      (use n_d in \<open>auto simp: lit_of_inj_on_no_dup distinct_map no_dup_def\<close>)
  ultimately have [simp]: \<open>L \<notin># Q\<close>
    by (metis distinct_mset_add_mset distinct_mset_union subset_mset.le_iff_add)
  have \<open>\<not>has_blit M (clause D) L\<close>
    using watched undef unw n_d by (cases D)
     (auto simp: has_blit_def Decided_Propagated_in_iff_in_lits_of_l dest: no_dup_consistentD)
  then have w_q_p_D: \<open>clauses_to_update_prop Q M (L, D)\<close>
    by (auto simp: clauses_to_update_prop.simps watched)
  have \<open>Pair L `# {#C \<in># add_mset D NU. clauses_to_update_prop Q M (L, C)#} \<subseteq># add_mset (L, D) WS\<close>
    using ws no_dup unfolding clauses_to_update_inv.simps NU
    by (auto simp: all_conj_distrib)
  then have IH: \<open>Pair L `# {#C \<in># NU. clauses_to_update_prop Q M (L, C)#} \<subseteq># WS\<close>
    using w_q_p_D by auto
  have IH_Q: \<open>\<forall>La C. C \<in># add_mset D NU \<longrightarrow> La \<in># watched C \<longrightarrow> - La \<in> lits_of_l M \<longrightarrow>
    \<not> has_blit M (clause C) La \<longrightarrow> (La, C) \<notin># add_mset (L, D) WS \<longrightarrow> La \<in># Q\<close>
    using ws no_dup unfolding clauses_to_update_inv.simps NU
    by (auto simp: all_conj_distrib)

  show ?case
    unfolding Ball_def twl_st_exception_inv.simps twl_exception_inv.simps
  proof (intro allI conjI impI)
    fix C J K
    assume C: \<open>C \<in># N + U\<close> and
      watched_C: \<open>J \<in># watched C\<close> and
      J: \<open>- J \<in> lits_of_l (Propagated L' (clause D) # M)\<close> and
      J': \<open>\<not> has_blit (Propagated L' (clause D) # M) (clause C) J\<close> and
      J_notin: \<open>J \<notin># add_mset (- L') Q\<close> and
      C_WS: \<open>(J, C) \<notin># WS\<close> and
      \<open>K \<in># unwatched C\<close>
    moreover have \<open>\<not> has_blit M (clause C) J\<close>
      using no_has_blit_propagate'[OF J'] n_d undef by fast
    ultimately have \<open>- K \<in> lits_of_l (Propagated L' (clause D) # M)\<close> if \<open>C \<noteq> D\<close>
      using twl_excep that by (auto simp add: uminus_lit_swap twl_exception_inv.simps)

    moreover have CD: False if \<open>C = D\<close>
      using J J' watched_C watched that J_notin
      by (cases D)  (auto simp: add_mset_eq_add_mset)
    ultimately show \<open>- K \<in> lits_of_l (Propagated L' (clause D) # M)\<close>
      by blast
  qed
  case 2
  show ?case
  proof (induction rule: clauses_to_update_inv_cases)
    case (WS_nempty L'' C)
    then have [simp]: \<open>L'' = L\<close>
      using ws no_dup unfolding clauses_to_update_inv.simps NU by (auto simp: all_conj_distrib)

    have *: \<open>Pair L `# {#C \<in># NU. clauses_to_update_prop Q M (L, C)#} \<supseteq>#
      Pair L `# {#C \<in># NU.
        clauses_to_update_prop (add_mset (- L') Q) (Propagated L' (clause D) # M) (L'', C)#}\<close>
      using undef n_d
      unfolding image_Pair_subset_mset multiset_filter_mono2 clauses_to_update_prop.simps
      by (auto dest!: no_has_blit_propagate')
    show ?case
      using subset_mset.dual_order.trans[OF IH *]  HH
      unfolding NU \<open>L'' = L\<close>
      by simp
  next
    case (WS_empty K)
    then show ?case
      using IH IH_Q watched undef n_d unfolding NU
      by (cases D) (auto simp: filter_mset_empty_conv
          clauses_to_update_prop.simps watched add_mset_eq_add_mset
          dest!: no_has_blit_propagate')
  next
    case (Q LC' C)
    then show ?case
       using watched "1.prems"(6) HH Q.hyps HH IH_Q undef n_d
       apply (cases D)
       apply (cases C)
       apply (auto simp: add_mset_eq_add_mset NU)
       by (metis HH Q.IH(2) Q.IH(3) Q.hyps clauses_to_update_prop.simps insert_iff
           no_has_blit_propagate' set_mset_add_mset_insert)
  qed
next
  case (conflict D L L' M N U NE UE N0 U0 WS Q)
  case 1
  note twl = this(5)
  show ?case by (auto simp: twl_st_inv.simps twl_exception_inv.simps)

  case 2
  show ?case
    by (auto simp: twl_st_inv.simps twl_exception_inv.simps)
next
  case (delete_from_working L' D M N U NE UE NS US N0 U0 L WS Q) note watched = this(1) and L' = this(2)

  case 1 note twl = this(1) and twl_excep = this(2) and valid = this(3) and inv = this(4) and
    no_dup = this(5) and ws = this(6)
  have n_d: \<open>no_dup M\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: trail.simps state\<^sub>W_of_def)
  have D_N_U: \<open>D \<in># N + U\<close>
    using valid by auto
  then have wf_D: \<open>struct_wf_twl_cls D\<close>
    using twl by (simp add: twl_st_inv.simps)
  obtain NU where NU: \<open>N + U = add_mset D NU\<close>
    by (metis D_N_U insert_DiffM)
  have D_N_U: \<open>D \<in># N + U\<close> and lev_L: \<open>get_level M L = count_decided M\<close>
    using valid by auto
  have [simp]: \<open>has_blit M (clause D) L\<close>
    unfolding has_blit_def
    by (rule exI[of _ L'])
       (use watched L' lev_L in \<open>auto simp: count_decided_ge_get_level\<close>)
  have [simp]: \<open>\<not>clauses_to_update_prop Q M (L, D)\<close>
    using L' by (auto simp: clauses_to_update_prop.simps watched)
  have IH_WS: \<open>Pair L `# {#C \<in># N + U. clauses_to_update_prop Q M (L, C)#} \<subseteq># add_mset (L, D) WS\<close>
    using ws by (auto simp del: filter_union_mset simp: NU)
  then have IH_WS_NU: \<open>Pair L `# {#C \<in># NU. clauses_to_update_prop Q M (L, C)#} \<subseteq>#
     add_mset (L, D) WS\<close>
    using ws by (auto simp del: filter_union_mset simp: NU)

  have IH_WS': \<open>Pair L `# {#C \<in># N + U. clauses_to_update_prop Q M (L, C)#} \<subseteq># WS\<close>
    by (rule subset_add_mset_notin_subset_mset[OF IH_WS]) auto
  have IH_Q: \<open>\<forall>La C. C \<in># add_mset D NU \<longrightarrow> La \<in># watched C \<longrightarrow> - La \<in> lits_of_l M \<longrightarrow>
    \<not>has_blit M (clause C) La \<longrightarrow> (La, C) \<notin># add_mset (L, D) WS \<longrightarrow> La \<in># Q\<close>
    using ws no_dup unfolding clauses_to_update_inv.simps NU
    by (auto simp: all_conj_distrib)

  show ?case
    unfolding Ball_def twl_st_exception_inv.simps twl_exception_inv.simps
  proof (intro allI conjI impI)
    fix C J K
    assume C: \<open>C \<in># N + U\<close> and
      watched_C: \<open>J \<in># watched C\<close> and
      J: \<open>- J \<in> lits_of_l M\<close> and
      J': \<open>\<not>has_blit M (clause C) J\<close> and
      J_notin: \<open>J \<notin># Q\<close> and
      C_WS: \<open>(J, C) \<notin># WS\<close> and
      \<open>K \<in># unwatched C\<close>
    then have \<open>- K \<in> lits_of_l M\<close> if \<open>C \<noteq> D\<close>
      using twl_excep that by (simp add: uminus_lit_swap twl_exception_inv.simps)

    moreover {
      from n_d have False if \<open> - L' \<in> lits_of_l M\<close> \<open>L' \<in> lits_of_l M\<close>
        using that consistent_interp_def distinct_consistent_interp by blast
      then have CD: False if \<open>C = D\<close>
        using J J' watched_C watched L' C_WS IH_Q J_notin \<open>\<not> clauses_to_update_prop Q M (L, D)\<close> that
        apply (auto simp: add_mset_eq_add_mset)
        by (metis C_WS J_notin \<open>\<not> clauses_to_update_prop Q M (L, D)\<close>
            clauses_to_update_prop.simps that)
      }
    ultimately show \<open>- K \<in> lits_of_l M\<close>
      by blast
  qed

  case 2
  show ?case
  proof (induction rule: clauses_to_update_inv_cases)
    case (WS_nempty K C) note KC = this
    have LK: \<open>L = K\<close>
      using no_dup KC by auto
    from subset_add_mset_notin_subset_mset[OF IH_WS]
    have 1: \<open>Pair K `# {#C \<in># N + U. clauses_to_update_prop Q M (L, C)#} \<subseteq># WS\<close>
      using L' LK \<open>has_blit M (clause D) L\<close>
      by (auto simp del: filter_union_mset simp: pair_in_image_Pair watched add_mset_eq_add_mset
          all_conj_distrib clauses_to_update_prop.simps)
    show ?case
      by (metis (no_types, lifting) 1 LK)
  next
    case (WS_empty K) note [simp] = this(1)
    have [simp]: \<open>\<not>clauses_to_update_prop Q M (K, D)\<close>
      using IH_Q WS_empty.IH watched  \<open>has_blit M (clause D) L\<close>
      using IH_WS' IH_Q watched by (auto simp: add_mset_eq_add_mset NU filter_mset_empty_conv
          all_conj_distrib clauses_to_update_prop.simps)
    show ?case
      using IH_WS' IH_Q watched by (auto simp: add_mset_eq_add_mset NU filter_mset_empty_conv
          all_conj_distrib clauses_to_update_prop.simps)
  next
    case (Q K C)
    then show ?case
      using \<open>\<not> clauses_to_update_prop Q M (L, D)\<close> ws
      unfolding clauses_to_update_inv.simps(1) clauses_to_update_prop.simps member_add_mset
       is_blit_def
      by blast
  qed
next
  case (update_clause D L L' M K N U N' U' NE UE NS US N0 U0 WS Q) note watched = this(1) and uL = this(2)
    and L' = this(3) and K = this(4) and undef = this(5) and N'U' = this(6)

  case 1 note twl = this(1) and twl_excep = this(2) and valid = this(3) and inv = this(4) and
    no_dup = this(5) and ws = this(6)
  obtain WD UWD where D: \<open>D = TWL_Clause WD UWD\<close> by (cases D)
  have L: \<open>L \<in># watched D\<close> and D_N_U: \<open>D \<in># N + U\<close> and lev_L: \<open>get_level M L = count_decided M\<close>
    using valid by auto
  then have struct_D: \<open>struct_wf_twl_cls D\<close>
    using twl by (auto simp: twl_st_inv.simps)
  have L'_UWD: \<open>L \<notin># remove1_mset L' UWD\<close> if \<open>L \<in># WD\<close> for L
  proof (rule ccontr)
    assume \<open>\<not> ?thesis\<close>
    then have \<open>count UWD L \<ge> 1\<close>
      by (auto simp del: count_greater_zero_iff simp: count_greater_zero_iff[symmetric]
          split: if_splits)
    then have \<open>count (clause D) L \<ge> 2\<close>
      using D that by (auto simp del: count_greater_zero_iff simp: count_greater_zero_iff[symmetric]
          split: if_splits)
    moreover have \<open>distinct_mset (clause D)\<close>
      using struct_D D by (auto simp: distinct_mset_union)
    ultimately show False
      unfolding distinct_mset_count_less_1 by (metis Suc_1 not_less_eq_eq)
  qed
  have L'_L'_UWD: \<open>K \<notin># remove1_mset K UWD\<close>
  proof (rule ccontr)
    assume \<open>\<not> ?thesis\<close>
    then have \<open>count UWD K \<ge> 2\<close>
      by (auto simp del: count_greater_zero_iff simp: count_greater_zero_iff[symmetric]
          split: if_splits)
    then have \<open>count (clause D) K \<ge> 2\<close>
      using D L' by (auto simp del: count_greater_zero_iff simp: count_greater_zero_iff[symmetric]
          split: if_splits)
    moreover have \<open>distinct_mset (clause D)\<close>
      using struct_D D by (auto simp: distinct_mset_union)
    ultimately show False
      unfolding distinct_mset_count_less_1 by (metis Suc_1 not_less_eq_eq)
  qed
  have \<open>watched_literals_false_of_max_level M D\<close>
    using D_N_U twl by (auto simp: twl_st_inv.simps)
  let ?D = \<open>update_clause D L K\<close>
  have *: \<open>C \<in># N + U\<close> if \<open>C \<noteq> ?D\<close> and C: \<open>C \<in># N' + U'\<close> for C
    using C N'U' that by (auto elim!: update_clausesE dest: in_diffD)
  have n_d: \<open>no_dup M\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp: trail.simps state\<^sub>W_of_def)
  then have uK_M: \<open>- K \<notin> lits_of_l M\<close>
    using undef Decided_Propagated_in_iff_in_lits_of_l consistent_interp_def
      distinct_consistent_interp by blast
  have add_remove_WD: \<open>add_mset K (remove1_mset L WD) \<noteq> WD\<close>
    using uK_M uL by (auto simp: add_mset_remove_trivial_iff trivial_add_mset_remove_iff)
  obtain NU where NU: \<open>N + U = add_mset D NU\<close>
    by (metis D_N_U insert_DiffM)
  have L_M: \<open>L \<notin> lits_of_l M\<close>
    using n_d uL by (fastforce dest!: distinct_consistent_interp
        simp: consistent_interp_def lits_of_def uminus_lit_swap)
  have w_max_D: \<open>watched_literals_false_of_max_level M D\<close>
    using D_N_U twl by (auto simp: twl_st_inv.simps)
  have lev_L': \<open>get_level M L' = count_decided M\<close>
    if \<open>- L' \<in> lits_of_l M\<close> \<open>\<not>has_blit M (clause D) L'\<close>
    using L_M w_max_D D watched L' uL that by auto
  have D_ne_D: \<open>D \<noteq> update_clause D L K\<close>
    using D add_remove_WD by auto
  have N'U': \<open>N' + U' = add_mset ?D (remove1_mset D (N + U))\<close>
    using N'U' D_N_U by (auto elim!: update_clausesE)
  define NU where \<open>NU = remove1_mset D (N + U)\<close>
  then have NU: \<open>N + U = add_mset D NU\<close>
    using D_N_U by auto
  have watched_D: \<open>watched ?D = {#K, L'#}\<close>
    using D add_remove_WD watched by auto
  have n_d: \<open>no_dup M\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: trail.simps state\<^sub>W_of_def)
  have D_N_U: \<open>D \<in># N + U\<close> and lev_L: \<open>get_level M L = count_decided M\<close>
    using valid by auto
  have \<open>has_blit (Propagated L' C # M)
              (add_mset L (add_mset L' x2)) L\<close> for C x2
    unfolding has_blit_def
    by (rule exI[of _ L'])
      (use lev_L in \<open>auto simp: count_decided_ge_get_level get_level_cons_if\<close>)
  then have HH: \<open>\<not>clauses_to_update_prop (add_mset (-L') Q) (Propagated L' (clause D) # M) (L, D)\<close>
    using watched unfolding clauses_to_update_prop.simps by (cases D) (auto simp: watched)
  have \<open>add_mset L Q \<subseteq># {#- lit_of x. x \<in># mset M#}\<close>
    using no_dup by (auto)
  moreover have \<open>distinct_mset {#- lit_of x. x \<in># mset M#}\<close>
    by (subst distinct_image_mset_inj)
      (use n_d in \<open>auto simp: lit_of_inj_on_no_dup distinct_map no_dup_def\<close>)
  ultimately have LQ: \<open>L \<notin># Q\<close>
    by (metis distinct_mset_add_mset distinct_mset_union subset_mset.le_iff_add)
  have w_q_p_D: \<open>\<not>has_blit M (clause D) L \<Longrightarrow> clauses_to_update_prop Q M (L, D)\<close>
    using watched uL L' by (cases D) (auto simp: LQ clauses_to_update_prop.simps)
  have \<open>Pair L `# {#C \<in># add_mset D NU. clauses_to_update_prop Q M (L, C)#} \<subseteq># add_mset (L, D) WS\<close>
    using ws no_dup unfolding clauses_to_update_inv.simps NU
    by (auto simp: all_conj_distrib)
  then have IH: \<open>\<not>has_blit M (clause D) L \<Longrightarrow> Pair L `# {#C \<in># NU. clauses_to_update_prop Q M (L, C)#} \<subseteq># WS\<close>
    using w_q_p_D by auto
  have IH_Q: \<open>\<And>La C. C \<in># add_mset D NU \<Longrightarrow> La \<in># watched C \<Longrightarrow> - La \<in> lits_of_l M \<Longrightarrow>
    \<not>has_blit M (clause C) La \<Longrightarrow> (La, C) \<notin># add_mset (L, D) WS \<Longrightarrow> La \<in># Q\<close>
    using ws no_dup unfolding clauses_to_update_inv.simps NU
    by (auto simp: all_conj_distrib)
  have blit_clss_to_upd: \<open>has_blit M (clause D) L \<Longrightarrow> \<not> clauses_to_update_prop Q M (L, D)\<close>
    by (auto simp: clauses_to_update_prop.simps)
  have
    \<open>Pair L `# {#C \<in># N + U. clauses_to_update_prop Q M (L, C)#} \<subseteq># add_mset (L, D) WS\<close>
    using ws by (auto simp del: filter_union_mset)
  moreover have \<open>has_blit M (clause D) L \<Longrightarrow>
      (L, D) \<notin># Pair L `# {#C \<in># NU. clauses_to_update_prop Q M (L, C)#}\<close>
    by (auto simp: clauses_to_update_prop.simps)
  ultimately have Q_M_L_WS:
    \<open>Pair L `# {#C \<in># NU. clauses_to_update_prop Q M (L, C)#} \<subseteq># WS\<close>
    by (auto simp del: filter_union_mset simp: NU w_q_p_D blit_clss_to_upd
      intro: subset_add_mset_notin_subset_mset split: if_splits)
  have L_ne_L': \<open>L \<noteq> L'\<close>
    using struct_D D watched by auto
  have clss_upd_D[simp]: \<open>clause ?D = clause D\<close>
    using D K watched by auto
  show ?case
    unfolding Ball_def twl_st_exception_inv.simps twl_exception_inv.simps
  proof (intro allI conjI impI)
    fix C J K''
    assume C: \<open>C \<in># N' + U'\<close> and
      watched_C: \<open>J\<in># watched C\<close> and
      J: \<open>- J \<in> lits_of_l M\<close> and
      J': \<open>\<not>has_blit M (clause C) J\<close> and
      J_notin: \<open>J \<notin># Q\<close> and
      C_WS: \<open>(J, C) \<notin># WS\<close> and
      K'': \<open>K'' \<in># unwatched C\<close>
    then have \<open>- K'' \<in> lits_of_l M\<close> if \<open>C \<noteq> D\<close> \<open>C \<noteq> ?D\<close>
      using twl_excep that *[OF _ C]  N'U' by (simp add: uminus_lit_swap twl_exception_inv.simps)
    moreover have \<open>- K'' \<in> lits_of_l M\<close> if CD: \<open>C = D\<close>
    proof (rule ccontr)
      assume uK''_M: \<open>- K'' \<notin> lits_of_l M\<close>
      have \<open>Pair L `# {#C \<in># N + U. clauses_to_update_prop Q M (L, C)#} \<subseteq># add_mset (L, D) WS\<close>
        using ws by (auto simp: all_conj_distrib
            simp del: filter_union_mset)
      show False
      proof cases
        assume [simp]: \<open>J = L\<close>
        have w_q_p_L: \<open>clauses_to_update_prop Q M (L, C)\<close>
          unfolding clauses_to_update_prop.simps watched_C J J' K'' uK''_M
          apply (auto simp add: add_mset_eq_add_mset conj_disj_distribR ex_disj_distrib)
          using watched watched_C CD J J' J_notin K'' uK''_M uL L' L_M
          by (auto simp: clauses_to_update_prop.simps add_mset_eq_add_mset)
        then have \<open>Pair L `# {#C \<in># NU. clauses_to_update_prop Q M (L, C)#} \<subseteq># WS\<close>
          using ws by (auto simp: all_conj_distrib NU CD simp del: filter_union_mset)
        moreover have \<open>(L, C) \<in># Pair L `# {#C \<in># NU. clauses_to_update_prop Q M (L, C)#}\<close>
          using C w_q_p_L D_ne_D by (auto simp: pair_in_image_Pair N'U' NU CD)
        ultimately have \<open>(L, C) \<in># WS\<close>
          by blast
        then show \<open>False\<close>
          using C_WS by simp
      next
        assume \<open>J \<noteq> L\<close>
        then have \<open>clauses_to_update_prop Q M (L, C)\<close>
          unfolding clauses_to_update_prop.simps watched_C J J' K'' uK''_M
          apply (auto simp add: add_mset_eq_add_mset conj_disj_distribR ex_disj_distrib)
          using watched watched_C CD J J' J_notin K'' uK''_M uL L' L_M
             apply (auto simp: clauses_to_update_prop.simps add_mset_eq_add_mset)
          using C_WS D_N_U clauses_to_update_prop.simps ws by auto
        then show \<open>False\<close>
          using C_WS D_N_U J J' J_notin \<open>J \<noteq> L\<close> that watched_C ws by auto
      qed
    qed
    moreover {
      assume CD: \<open>C = ?D\<close>
      have JL[simp]: \<open>J = L'\<close>
        using CD J J' watched_C watched L' D uK_M undef
        by (auto simp: add_mset_eq_add_mset)
      have \<open>K'' \<noteq> K\<close>
        using K'' uK_M uL D L'_L'_UWD unfolding CD
        by (cases D) auto
      have K''_unwatched_L: \<open>K'' \<in>#  remove1_mset K (unwatched D) \<or> K'' = L\<close>
        using K'' unfolding CD by (cases D) auto
      have \<open>clause C = clause D\<close>
        using D K watched unfolding CD by auto
      then have blit: \<open>\<not> has_blit M (clause D) L'\<close>
        using J' unfolding CD by simp
      have False if \<open>- L' \<in> lits_of_l M\<close> \<open>L' \<in> lits_of_l M\<close>
        using n_d that consistent_interp_def distinct_consistent_interp by blast
      have H: \<open>\<And>x La xa. x \<in># N + U \<Longrightarrow>
            La \<in># watched x \<Longrightarrow> - La \<in> lits_of_l M \<Longrightarrow>
            \<not>has_blit M (clause x) La \<Longrightarrow> La \<notin># Q \<Longrightarrow> (La, x) \<notin># add_mset (L, D) WS \<Longrightarrow>
            xa \<in># unwatched x \<Longrightarrow> - xa \<in> lits_of_l M\<close>
        using twl_excep[unfolded twl_st_exception_inv.simps Ball_def twl_exception_inv.simps]
        unfolding has_blit_def is_blit_def
        by blast
      have LL': \<open>L \<noteq> L'\<close>
        using struct_D watched by (cases D) auto
      have L'D_WS: \<open>(L', D) \<notin># WS\<close>
        using no_dup LL' by (auto dest: multi_member_split)
      have \<open>xa \<in># unwatched D \<Longrightarrow> - xa \<in> lits_of_l M\<close>
        if \<open>- L' \<in> lits_of_l M\<close> and \<open>L' \<notin># Q\<close> and \<open>\<not> has_blit M (clause D) L'\<close> for xa
        by (rule H[of D L'])
          (use D_N_U watched LL' that L'D_WS K'' that in \<open>auto simp: add_mset_eq_add_mset L_M\<close>)
      consider
        (unwatched_unqueued) \<open>K'' \<in># remove1_mset K (unwatched D)\<close> |
        (KL) \<open>K'' = L\<close>
        using K''_unwatched_L by blast
      then have \<open>- K'' \<in> lits_of_l M\<close>
      proof cases
        case KL
        then show ?thesis
          using uL by simp
      next
        case unwatched_unqueued
        moreover have \<open>L' \<notin># Q\<close>
          using JL J_notin by blast
        ultimately show ?thesis
          using blit H[of D L'] D_N_U watched LL' L'D_WS K'' J J'
          by (auto simp: add_mset_eq_add_mset L_M dest: in_diffD)
      qed
      }
    ultimately show \<open>- K'' \<in> lits_of_l M\<close>
      by blast
  qed

  case 2
  show ?case
  proof (induction rule: clauses_to_update_inv_cases)
    case (WS_nempty K'' C) note KC = this(1)
    have LK: \<open>L = K''\<close>
      using no_dup KC by auto
    have [simp]: \<open>\<not>clauses_to_update_prop Q M (K'', update_clause D K'' K)\<close>
      using watched uK_M struct_D
      by (cases D) (auto simp: clauses_to_update_prop.simps add_mset_eq_add_mset LK)
    have 1: \<open>Pair L `#  {#C \<in># N' + U'. clauses_to_update_prop Q M (L, C)#} \<subseteq>#
      Pair L `#  {#C \<in># NU. clauses_to_update_prop Q M (L, C)#}\<close>
      unfolding image_Pair_subset_mset LK
      using LK N'U' by (auto simp del: filter_union_mset simp: pair_in_image_Pair watched NU
          add_mset_eq_add_mset all_conj_distrib)
    then show \<open>Pair K'' `#  {#C \<in># N' + U'. clauses_to_update_prop Q M (K'', C)#} \<subseteq># WS\<close>
      using Q_M_L_WS unfolding LK by auto
  next
    case (WS_empty K'')
    then show ?case
      using IH IH_Q uL uK_M L_M watched L_ne_L' unfolding N'U' NU
      by (force simp: filter_mset_empty_conv clauses_to_update_prop.simps
          add_mset_eq_add_mset watched_D all_conj_distrib)
  next
    case (Q K' C) note C = this(1) and uK'_M = this(2) and uK''_M = this(3) and KC_WS = this(4)
      and watched_C = this(5)
    have ?case if CD: \<open>C \<noteq> D\<close> \<open>C \<noteq> ?D\<close>
      using IH_Q[of C K'] CD watched uK_M L'  L_ne_L' L_M uK'_M uK''_M
        Q unfolding N'U' NU
      by auto
    moreover have ?case if CD: \<open>C = D\<close>
    proof -
      consider
        (KL)   \<open>K' = L\<close> |
        (K'L') \<open>K' = L'\<close>
        using watched watched_C CD by (auto simp: add_mset_eq_add_mset)
      then show ?thesis
      proof cases
        case KL note [simp] = this
        have \<open>(L, C) \<in># Pair L `# {#C \<in># NU. clauses_to_update_prop Q M (L, C)#}\<close>
          using CD C w_q_p_D uK''_M unfolding NU N'U' by (auto simp: pair_in_image_Pair D_ne_D)
        then have \<open>(L, C) \<in># WS\<close>
          using Q_M_L_WS by blast
        then have False using KC_WS unfolding CD by simp
        then show ?thesis by fast
      next
        case K'L' note [simp] = this
        show ?thesis
          by (rule IH_Q[of C]) (use CD watched_C uK'_M uK''_M KC_WS L_ne_L' in auto)
      qed
    qed
    moreover {
      have \<open>(L', D) \<notin># WS\<close>
        using no_dup L_ne_L' by (auto simp: all_conj_distrib)
      then have ?case if CD: \<open>C = ?D\<close>
        using IH_Q[of D L] IH_Q[of D L']  CD watched watched_D watched_C watched uK_M L'
          L_ne_L' L_M uK'_M uK''_M D_ne_D C unfolding NU N'U'
        by (auto simp: add_mset_eq_add_mset all_conj_distrib imp_conjR)
    }
    ultimately show ?case
      by blast
  qed
qed

declare  state\<^sub>W_of_def[simp]

lemma twl_cp_twl_inv:
  assumes
    cdcl: \<open>cdcl_twl_cp S T\<close> and
    twl: \<open>twl_st_inv S\<close> and
    valid: \<open>valid_enqueued S\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S)\<close> and
    twl_excep: \<open>twl_st_exception_inv S\<close> and
    no_dup: \<open>no_duplicate_queued S\<close> and
    wq: \<open>clauses_to_update_inv S\<close>
  shows \<open>twl_st_inv T\<close>
  using cdcl twl valid inv twl_excep no_dup wq
proof (induction rule: cdcl_twl_cp.induct)
  case (pop M N U NE UE NS US L Q) note inv = this(1)
  then show ?case unfolding twl_st_inv.simps twl_is_an_exception_def
    by (fastforce simp add: pair_in_image_Pair)
next
  case (propagate D L L' M N U NE UE NS US N0 U0 WS Q) note watched = this(1) and undef = this(2) and
   unw = this(3) and twl = this(4) and valid = this(5) and inv = this(6) and exception = this(7)
  have uL'_M[simp]: \<open>- L' \<notin> lits_of_l M\<close>
    using Decided_Propagated_in_iff_in_lits_of_l propagate.hyps(2) by blast
  have D_N_U: \<open>D \<in># N + U\<close> and lev_L: \<open>get_level M L = count_decided M\<close>
    using valid by auto
  then have wf_D: \<open>struct_wf_twl_cls D\<close>
    using twl by (auto simp add: twl_st_inv.simps)
  have [simp]: \<open>- L \<in> lits_of_l M\<close>
    using valid by auto
  have n_d: \<open>no_dup M\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: trail.simps)
  show ?case unfolding twl_st_simps Ball_def
  proof (intro allI conjI impI)
    fix C
    assume C: \<open>C \<in># N + U\<close>
    show \<open>struct_wf_twl_cls C\<close>
      using twl C by (auto simp: twl_st_inv.simps)[]
    have watched_max: \<open>watched_literals_false_of_max_level M C\<close>
      using twl C by (auto simp: twl_st_inv.simps)
    then show \<open>watched_literals_false_of_max_level (Propagated L' (clause D) # M) C\<close>
      using undef n_d
      by (cases C) (auto simp: get_level_cons_if dest!: no_has_blit_propagate')

    assume excep: \<open>\<not>twl_is_an_exception C (add_mset (- L') Q) WS\<close>
    have excep_C: \<open>\<not> twl_is_an_exception C Q (add_mset (L, D) WS)\<close> if \<open>C \<noteq> D\<close>
      using excep that by (auto simp add: twl_is_an_exception_def)
    then have \<open>twl_lazy_update M C\<close> if \<open>C \<noteq> D\<close>
      using twl C D_N_U that by (cases \<open>C = D\<close>) (auto simp add: twl_st_inv.simps)
    then show \<open>twl_lazy_update (Propagated L' (clause D) # M) C\<close>
      using twl C excep uL'_M twl undef n_d uL'_M unw watched_max
      apply (cases C)
      apply (auto simp: get_level_cons_if count_decided_ge_get_level
          twl_is_an_exception_add_mset_to_queue atm_of_eq_atm_of
          dest!: no_has_blit_propagate' no_has_blit_propagate)
      apply (metis twl_clause.sel(2) uL'_M unw)
      apply (metis twl_clause.sel(2) uL'_M unw)
      apply (metis twl_clause.sel(2) uL'_M unw)
      apply (metis twl_clause.sel(2) uL'_M unw)
      done
  qed
next
  case (conflict D L L' M N U NE UE NS US N0 U0 WS Q) note twl = this(4)
  then show ?case
    by (auto simp: twl_st_inv.simps)
next
  case (delete_from_working L' D M N U NE UE NS US N0 U0 L WS Q) note watched = this(1) and L' = this(2) and
  twl = this(3) and valid = this(4) and inv = this(5) and tauto = this(6)
  show ?case unfolding twl_st_simps Ball_def
  proof (intro allI conjI impI)
    fix C
    assume C: \<open>C \<in># N + U\<close>
    show \<open>struct_wf_twl_cls C\<close>
      using twl C by (auto simp: twl_st_inv.simps)[]
    show \<open>watched_literals_false_of_max_level M C\<close>
      using twl C by (auto simp: twl_st_inv.simps)

    assume excep: \<open>\<not>twl_is_an_exception C Q WS\<close>
    have \<open>get_level M L = count_decided M\<close> and L: \<open>-L \<in> lits_of_l M\<close> and D: \<open>D \<in># N + U\<close>
      using valid by auto
    have \<open>watched_literals_false_of_max_level M D\<close>
      using twl D by (auto simp: twl_st_inv.simps)
    have \<open>no_dup M\<close>
      using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (simp add: trail.simps)
    then have [simp]: \<open>- L' \<notin> lits_of_l M\<close>
      using L' consistent_interp_def distinct_consistent_interp by blast
    have \<open>\<not> twl_is_an_exception C Q (add_mset (L, D) WS)\<close> if \<open>C \<noteq> D\<close>
      using excep that by (auto simp add: twl_is_an_exception_def)
    have twl_D: \<open>twl_lazy_update M D\<close>
      using twl C excep twl watched L' \<open>watched_literals_false_of_max_level M D\<close>
      by (cases D)
        (auto simp: get_level_cons_if count_decided_ge_get_level has_blit_def
          twl_is_an_exception_add_mset_to_queue atm_of_eq_atm_of count_decided_ge_get_level
          dest!: no_has_blit_propagate' no_has_blit_propagate)
    have twl_C: \<open>twl_lazy_update M C\<close> if \<open>C \<noteq> D\<close>
      using twl C excep that by (auto simp add: twl_st_inv.simps
          twl_is_an_exception_add_mset_to_clauses_to_update)

    show \<open>twl_lazy_update M C\<close>
      using twl_C twl_D by blast
  qed
next
  case (update_clause D L L' M K N U N' U' NE UE NS US N0 U0 WS Q) note watched = this(1) and uL = this(2)
    and L' = this(3) and K = this(4) and undef = this(5) and N'U' = this(6) and twl = this(7) and
    valid = this(8) and inv = this(9) and twl_excep = this(10) and
    no_dup = this(11) and wq = this(12)
  obtain WD UWD where D: \<open>D = TWL_Clause WD UWD\<close> by (cases D)
  have L: \<open>L \<in># watched D\<close> and D_N_U: \<open>D \<in># N + U\<close> and lev_L: \<open>get_level M L = count_decided M\<close>
    using valid by auto
  then have struct_D: \<open>struct_wf_twl_cls D\<close>
    using twl by (auto simp: twl_st_inv.simps)
  have L'_UWD: \<open>L \<notin># remove1_mset L' UWD\<close> if \<open>L \<in># WD\<close> for L
  proof (rule ccontr)
    assume \<open>\<not> ?thesis\<close>
    then have \<open>count UWD L \<ge> 1\<close>
      by (auto simp del: count_greater_zero_iff simp: count_greater_zero_iff[symmetric]
          split: if_splits)
    then have \<open>count (clause D) L \<ge> 2\<close>
      using D that by (auto simp del: count_greater_zero_iff simp: count_greater_zero_iff[symmetric]
          split: if_splits)
    moreover have \<open>distinct_mset (clause D)\<close>
      using struct_D D by (auto simp: distinct_mset_union)
    ultimately show False
      unfolding distinct_mset_count_less_1 by (metis Suc_1 not_less_eq_eq)
  qed
  have L'_L'_UWD: \<open>K \<notin># remove1_mset K UWD\<close>
  proof (rule ccontr)
    assume \<open>\<not> ?thesis\<close>
    then have \<open>count UWD K \<ge> 2\<close>
      by (auto simp del: count_greater_zero_iff simp: count_greater_zero_iff[symmetric]
          split: if_splits)
    then have \<open>count (clause D) K \<ge> 2\<close>
      using D L' by (auto simp del: count_greater_zero_iff simp: count_greater_zero_iff[symmetric]
          split: if_splits)
    moreover have \<open>distinct_mset (clause D)\<close>
      using struct_D D by (auto simp: distinct_mset_union)
    ultimately show False
      unfolding distinct_mset_count_less_1 by (metis Suc_1 not_less_eq_eq)
  qed
  have \<open>watched_literals_false_of_max_level M D\<close>
    using D_N_U twl by (auto simp: twl_st_inv.simps)
  let ?D = \<open>update_clause D L K\<close>
  have *: \<open>C \<in># N + U\<close> if \<open>C \<noteq> ?D\<close> and C: \<open>C \<in># N' + U'\<close> for C
    using C N'U' that by (auto elim!: update_clausesE dest: in_diffD)
  have n_d: \<open>no_dup M\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: trail.simps)
  then have uK_M: \<open>- K \<notin> lits_of_l M\<close>
    using undef Decided_Propagated_in_iff_in_lits_of_l consistent_interp_def
      distinct_consistent_interp by blast
  have add_remove_WD: \<open>add_mset K (remove1_mset L WD) \<noteq> WD\<close>
    using uK_M uL by (auto simp: add_mset_remove_trivial_iff trivial_add_mset_remove_iff)
  have cls_D_D: \<open>clause ?D = clause D\<close>
    by (cases D) (use watched K in auto)

  have L_M: \<open>L \<notin> lits_of_l M\<close>
    using n_d uL by (fastforce dest!: distinct_consistent_interp
        simp: consistent_interp_def lits_of_def uminus_lit_swap)
  have w_max_D: \<open>watched_literals_false_of_max_level M D\<close>
    using D_N_U twl by (auto simp: twl_st_inv.simps)


  show ?case unfolding twl_st_simps Ball_def
  proof (intro allI conjI impI)
    fix C
    assume C: \<open>C \<in># N' + U'\<close>
    moreover have \<open>L \<noteq> L'\<close>
      using struct_D watched by (auto simp: D dest: multi_member_split)
    ultimately have struct_D': \<open>struct_wf_twl_cls ?D\<close>
      using L K struct_D watched by (auto simp: D L'_UWD L'_L'_UWD dest: in_diffD)

    have struct_C: \<open>struct_wf_twl_cls C\<close> if \<open>C \<noteq> ?D\<close>
      using twl C that N'U' by (fastforce simp: twl_st_inv.simps elim!: update_clausesE
          split: if_splits dest: in_diffD)
    show \<open>struct_wf_twl_cls C\<close>
      using struct_D' struct_C by blast

     have H: \<open>\<And>C. C \<in># N+U \<Longrightarrow> \<not> twl_is_an_exception C Q WS \<Longrightarrow> C \<noteq> D \<Longrightarrow>
       twl_lazy_update M C\<close>
      using twl
      by (auto simp add: twl_st_inv.simps twl_is_an_exception_add_mset_to_clauses_to_update)
    have \<open>watched_literals_false_of_max_level M C\<close> if \<open>C \<noteq> ?D\<close>
      using twl C that N'U' by (fastforce simp: twl_st_inv.simps elim!: update_clausesE
          dest: in_diffD)
    moreover have \<open>watched_literals_false_of_max_level M ?D\<close>
      using w_max_D D watched L' uK_M distinct_consistent_interp[OF n_d] uL K
      apply (cases D)
      apply (simp_all add: add_mset_eq_add_mset consistent_interp_def)
      by (metis add_mset_eq_add_mset)
    ultimately show \<open>watched_literals_false_of_max_level M C\<close>
      by blast

    assume excep: \<open>\<not>twl_is_an_exception C Q WS\<close>
    have \<open>get_level M L = count_decided M\<close> and L: \<open>-L \<in> lits_of_l M\<close> and D_N_U: \<open>D \<in># N + U\<close>
      using valid by auto

    have excep_WS: \<open>\<not> twl_is_an_exception C Q WS\<close>
      using excep C by (force simp: twl_is_an_exception_def)
    have excep_inv_D: \<open>twl_exception_inv (M, N, U, None, NE, UE, NS, US, N0, U0, add_mset (L, D) WS, Q) D\<close>
      using twl_excep D_N_U unfolding twl_st_exception_inv.simps
      by blast
    then have \<open>\<not> has_blit M (clause D) L \<Longrightarrow>
         L \<notin># Q \<Longrightarrow> (L, D) \<notin># add_mset (L, D) WS \<Longrightarrow> (\<forall>K\<in>#unwatched D. - K \<in> lits_of_l M)\<close>
      using watched L
      unfolding twl_exception_inv.simps
      apply auto
      done
    have NU_WS: \<open>Pair L `# {#C \<in># N+U. clauses_to_update_prop Q M (L, C)#} \<subseteq># add_mset (L, D) WS\<close>
      using wq by auto
    have \<open>distinct_mset {#- lit_of x. x \<in># mset M#}\<close>
      by (subst distinct_image_mset_inj)
        (use n_d in \<open>auto simp: lit_of_inj_on_no_dup distinct_map no_dup_def\<close>)
    moreover have \<open>add_mset L Q \<subseteq># {#- lit_of x. x \<in># mset M#}\<close>
      using no_dup by auto
    ultimately have LQ[simp]: \<open>L \<notin># Q\<close>
      by (metis distinct_mset_add_mset distinct_mset_union subset_mset.le_iff_add)

    have \<open>twl_lazy_update M C\<close> if CD: \<open>C = D\<close>
      unfolding twl_lazy_update.simps CD D
    proof (intro conjI impI allI)
      fix K'
      assume \<open>K' \<in># WD\<close> \<open>- K' \<in> lits_of_l M\<close>\<open>\<not> has_blit M (WD + UWD) K'\<close>
      have C_D': \<open>C \<noteq> update_clause D L K\<close>
        using D add_remove_WD that by auto

      have H: \<open>\<not> has_blit M (add_mset L (add_mset L' UWD)) L' \<Longrightarrow>
         has_blit M (add_mset L (add_mset L' UWD)) L \<Longrightarrow> False\<close>
        using  \<open>- K' \<in> lits_of_l M\<close> \<open>K' \<in># WD\<close> \<open>\<not> has_blit M (WD + UWD) K'\<close>
          lev_L w_max_D
        using L_M by (auto simp: has_blit_def D)
      obtain NU where NU: \<open>N+U = add_mset D NU\<close>
        using multi_member_split[OF D_N_U] by auto
      have \<open>C \<in># remove1_mset D (N + U)\<close>
        using C C_D' N'U' unfolding NU
        apply (auto simp: update_clauses.simps NU[symmetric])
        using C by auto
      then obtain NU' where \<open>N+U = add_mset C (add_mset D NU')\<close>
        using NU multi_member_split by force
      moreover have \<open>clauses_to_update_prop Q M (L, D)\<close>
        using watched uL \<open>\<not> has_blit M (WD + UWD) K'\<close> \<open>K' \<in># WD\<close> LQ
        by (auto simp: clauses_to_update_prop.simps D dest: H)
      ultimately have \<open>(L, D) \<in># WS\<close>
        using NU_WS by (auto simp: CD split: if_splits)
      then have False
        using excep unfolding CD
        by (auto simp: twl_is_an_exception_def)
      then show \<open>\<forall>K\<in>#UWD. get_level M K \<le> get_level M K' \<and> - K \<in> lits_of_l M\<close>
        by fast
    qed

    moreover have \<open>twl_lazy_update M C\<close> if \<open>C \<noteq> ?D\<close> \<open>C \<noteq> D\<close>
      using H[of C] that excep_WS * C
      by (auto simp add: twl_st_inv.simps)[]
    moreover {
      have D': \<open>?D = TWL_Clause {#K, L'#} (add_mset L (remove1_mset K UWD))\<close> and
        mset_D': \<open>{#K, L'#} + add_mset L (remove1_mset K UWD) = clause D\<close>
        using D watched cls_D_D by auto
      have lev_L': \<open>get_level M L' = count_decided M\<close> if \<open>- L' \<in> lits_of_l M \<close> and
        \<open>\<not> has_blit M (clause D) L'\<close>
        using L_M w_max_D D watched L' uL that
        by simp
      have \<open>\<forall>C. C \<in># WS \<longrightarrow> fst C = L\<close>
        using no_dup
        using watched uL L' undef D (* excep wq *)
        by (auto simp del: set_mset_union simp: )
      then have \<open>(L', TWL_Clause {#L, L'#} UWD) \<notin># WS\<close>
        using wq multi_member_split[OF D_N_U] struct_D
        using watched uL L' undef D (* excep wq *)
        by auto
      then have \<open>- L' \<in> lits_of_l M \<Longrightarrow> \<not> has_blit M (add_mset L (add_mset L' UWD)) L' \<Longrightarrow>
              L' \<in># Q \<close>
        using wq multi_member_split[OF D_N_U] struct_D
        using watched uL L' undef D (* excep wq *)
        by (auto simp del: set_mset_union simp: )
      then have
          H: \<open>- L' \<in> lits_of_l M \<Longrightarrow> \<not> has_blit M (add_mset L (add_mset L' UWD)) L' \<Longrightarrow>
             False\<close> if \<open>C = ?D\<close>
        using excep multi_member_split[OF D_N_U] struct_D
        using watched uL L' undef D (*  wq *) that
        by (auto simp del: set_mset_union simp: twl_is_an_exception_def)

      have in_remove1_mset: \<open>K' \<in># remove1_mset K UWD \<longleftrightarrow> K' \<noteq> K \<and> K' \<in># UWD\<close> for K'
        using struct_D L'_L'_UWD by (auto simp: D in_remove1_mset_neq dest: in_diffD)
      have \<open>twl_lazy_update M ?D\<close> if \<open>C = ?D\<close>
        using watched uL L' undef D w_max_D H
        unfolding twl_lazy_update.simps D' mset_D' that
        by (auto simp: uK_M D add_mset_eq_add_mset lev_L count_decided_ge_get_level
            in_remove1_mset twl_is_an_exception_def)
      }
    ultimately show \<open>twl_lazy_update M C\<close>
      by blast
  qed
qed

lemma twl_cp_no_duplicate_queued:
  assumes
    cdcl: \<open>cdcl_twl_cp S T\<close> and
    no_dup: \<open>no_duplicate_queued S\<close>
  shows \<open>no_duplicate_queued T\<close>
  using cdcl no_dup
proof (induction rule: cdcl_twl_cp.induct)
  case (pop M N U NE UE NS US N0 U0 L Q)
  then show ?case
    by (auto simp: image_Un image_image subset_mset.less_imp_le
        dest: mset_subset_eq_insertD)
qed auto

lemma distinct_mset_Pair: \<open>distinct_mset (Pair L `# C) \<longleftrightarrow> distinct_mset C\<close>
  by (induction C) auto

lemma distinct_image_mset_clause:
  \<open>distinct_mset (clause `# C) \<Longrightarrow> distinct_mset C\<close>
  by (induction C) auto

lemma twl_cp_distinct_queued:
  assumes
    cdcl: \<open>cdcl_twl_cp S T\<close> and
    twl: \<open>twl_st_inv S\<close> and
    valid: \<open>valid_enqueued S\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S)\<close> and
    no_dup: \<open>no_duplicate_queued S\<close> and
    dist: \<open>distinct_queued S\<close>
  shows \<open>distinct_queued T\<close>
  using cdcl twl valid inv no_dup dist
proof (induction rule: cdcl_twl_cp.induct)
  case (pop M N U NE UE NS US N0 U0 L Q) note c_dist = this(4) and dist = this(5)
  show ?case
    using dist by (auto simp: distinct_mset_Pair count_image_mset_Pair simp del: image_mset_union)
next
  case (propagate D L L' M N U NE UE NS US N0 U0 WS Q) note watched = this(1) and undef = this(2) and
    twl = this(4) and valid = this(5)  and inv = this(6) and no_dup = this(7)
    and dist = this(8)
  have \<open>L' \<notin> lits_of_l M\<close>
    using Decided_Propagated_in_iff_in_lits_of_l propagate.hyps(2) by auto
  then have \<open>-L' \<notin># Q\<close>
    using no_dup by (fastforce simp: lits_of_def dest!: mset_subset_eqD)
  then show ?case
    using dist by (auto simp: all_conj_distrib split: if_splits dest!: Suc_leD)
next
  case (conflict D L L' M N U NE UE N0 U0 WS Q) note dist = this(8)
  then show ?case
    by auto
next
  case (delete_from_working D L L' M N U NE UE NS US N0 U0 WS Q) note dist = this(7)
  show ?case using dist by (auto simp: all_conj_distrib split: if_splits dest!: Suc_leD)
next
  case (update_clause D L L' M K N U N' U' NE UE NS US N0 U0 WS Q) note watched = this(1) and uL = this(2) and
    L' = this(3) and K = this(4) and undef = this(5) and N'U' = this(6) and twl = this(7) and
    valid = this(8) and inv = this(9) and no_dup = this(10) and dist = this(11)

  show ?case
    unfolding distinct_queued.simps
  proof (intro conjI allI)
    show \<open>distinct_mset Q\<close>
      using dist N'U' by (auto simp: all_conj_distrib split: if_splits intro: le_SucI)

    fix K'' C
    have LD: \<open>Suc (count WS (L, D)) \<le> count N D + count U D\<close>
      using dist N'U' by (auto split: if_splits)
    have LC: \<open>count WS (La, Ca) \<le> count N Ca + count U Ca\<close>
      if \<open>(La , Ca) \<noteq> (L, D)\<close> for Ca La
      using dist N'U' by (force simp: all_conj_distrib split: if_splits intro: le_SucI)
    show \<open>count WS (K'', C) \<le> count (N' + U') C\<close>
    proof (cases \<open>K'' \<noteq> L\<close>)
      case True
      then have \<open>count WS (K'', C) = 0\<close>
      using no_dup by auto
      then show ?thesis by arith
    next
      case False
      then show ?thesis
        apply (cases \<open>C = D\<close>)
        using LD N'U' apply (auto simp: all_conj_distrib elim!: update_clausesE intro: le_SucI;
            fail)
        using LC[of L C] N'U' by (auto simp: all_conj_distrib elim!: update_clausesE intro: le_SucI)
    qed
  qed
qed

lemma twl_cp_valid:
  assumes
    cdcl: \<open>cdcl_twl_cp S T\<close> and
    twl: \<open>twl_st_inv S\<close> and
    valid: \<open>valid_enqueued S\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S)\<close> and
    no_dup: \<open>no_duplicate_queued S\<close> and
    dist: \<open>distinct_queued S\<close>
  shows \<open>valid_enqueued T\<close>
  using cdcl twl valid inv no_dup dist
proof (induction rule: cdcl_twl_cp.induct)
  case (pop M N U NE UE NS US N0 U0 L Q) note valid = this(2)
  then show ?case
    by (auto simp del: filter_union_mset)
next
  case (propagate D L L' M N U NE UE NS US N0 U0 WS Q) note watched = this(1) and twl = this(4) and
    valid = this(5) and inv = this(6) and no_taut = this(7)
  show ?case
    using valid by (auto dest: mset_subset_eq_insertD simp: get_level_cons_if)
next
  case (conflict D L L' M N U NE UE NS US N0 U0 WS Q) note valid = this(5)
  then show ?case
    by auto
next
  case (delete_from_working D L L' M N U NE UE NS US N0 U0 WS Q) note watched = this(1) and L' = this(2) and
  twl = this(3) and valid = this(4) and inv = this(5)
  show ?case unfolding twl_st_simps Ball_def
    using valid by (auto dest: mset_subset_eq_insertD)
next
  case (update_clause D L L' M K N U N' U' NE UE NS US N0 U0 WS Q) note watched = this(1) and uL = this(2) and
    L' = this(3) and K = this(4) and undef = this(5) and N'U' = this(6) and twl = this(7) and
    valid = this(8) and inv = this(9) and no_dup = this(10) and dist = this(11)
  show ?case
    unfolding valid_enqueued.simps Ball_def
  proof (intro allI impI conjI)
    fix L :: \<open>'a literal\<close>
    assume L:  \<open>L \<in># Q\<close>
    then show \<open>-L \<in> lits_of_l M\<close>
      using valid by auto
    show \<open>get_level M L = count_decided M\<close>
      using L valid by auto
  next
    fix KC :: \<open>'a literal \<times> 'a twl_cls\<close>
    assume LC_WS: \<open>KC \<in># WS\<close>
    obtain K'' C where LC: \<open>KC = (K'', C)\<close> by (cases KC)
    have \<open>K'' \<in># watched C\<close>
      using LC_WS valid LC by auto
    have C_ne_D: \<open>case KC of (L, C) \<Rightarrow> L \<in># watched C \<and> C \<in># N' + U' \<and> - L \<in> lits_of_l M \<and>
        get_level M L = count_decided M\<close> if \<open>C \<noteq> D\<close>
      by (cases \<open>C = D\<close>)
        (use valid LC LC_WS N'U' that in \<open>auto simp: in_remove1_mset_neq elim!: update_clausesE\<close>)
    have K''_L: \<open>K'' = L\<close>
      using no_dup LC_WS LC by auto
    have \<open>Suc (count WS (L, D)) \<le> count N D + count U D\<close>
      using dist by (auto simp: all_conj_distrib split: if_splits)
    then have D_DN_U: \<open>D \<in># remove1_mset D (N+U)\<close> if [simp]: \<open>C = D\<close>
      using LC_WS unfolding count_greater_zero_iff[symmetric]
      by (auto simp del: count_greater_zero_iff simp: LC K''_L)
    have D_D_N: \<open>D \<in># remove1_mset D N\<close> if \<open>D \<in># N\<close> and \<open>D \<notin># U\<close> and [simp]: \<open>C = D\<close>
    proof -
      have \<open>D \<in># remove1_mset D (U + N)\<close>
        using D_DN_U by (simp add: union_commute)
      then have \<open>D \<in># U + remove1_mset D N\<close>
        using that(1) by (metis (no_types) add_mset_remove_trivial insert_DiffM
            union_mset_add_mset_right)
      then show \<open>D \<in># remove1_mset D N\<close>
        using that(2) by (meson union_iff)
    qed
    have D_D_U: \<open>D \<in># remove1_mset D U\<close> if \<open>D \<in># U\<close> and \<open>D \<notin># N\<close> and [simp]: \<open>C = D\<close>
    proof -
      have \<open>D \<in># remove1_mset D (U + N)\<close>
        using D_DN_U by (simp add: union_commute)
      then have \<open>D \<in># N + remove1_mset D U\<close>
        using D_DN_U that(1) by fastforce
      then show \<open>D \<in># remove1_mset D U\<close>
        using that(2) by (meson union_iff)
    qed
    have CD: \<open>case KC of (L, C) \<Rightarrow> L \<in># watched C \<and> C \<in># N' + U' \<and> - L \<in> lits_of_l M \<and>
        get_level M L = count_decided M\<close> if \<open>C = D\<close>
      by (use valid LC_WS N'U' in \<open>auto simp: LC D_D_N that in_remove1_mset_neq
          dest!: D_D_U elim!: update_clausesE\<close>)
    show \<open>case KC of (L, C) \<Rightarrow> L \<in># watched C \<and> C \<in># N' + U' \<and> - L \<in> lits_of_l M \<and>
        get_level M L = count_decided M\<close>
      using CD C_ne_D by blast
  qed
qed


lemma twl_cp_propa_cands_enqueued:
  assumes
    cdcl: \<open>cdcl_twl_cp S T\<close> and
    twl: \<open>twl_st_inv S\<close> and
    valid: \<open>valid_enqueued S\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S)\<close> and
    twl_excep: \<open>twl_st_exception_inv S\<close> and
    no_dup: \<open>no_duplicate_queued S\<close> and
    cands: \<open>propa_cands_enqueued S\<close> and
    ws: \<open>clauses_to_update_inv S\<close>
  shows \<open>propa_cands_enqueued T\<close>
  using cdcl twl valid inv twl_excep no_dup cands ws
proof (induction rule: cdcl_twl_cp.induct)
  case (pop M N U NE UE NS US N0 U0 L Q) note inv = this(1) and valid = this(2) and cands = this(6)
  show ?case unfolding propa_cands_enqueued.simps
  proof (intro allI conjI impI)
    fix C K
    assume C: \<open>C \<in># N + U\<close> and
      \<open>K \<in># clause C\<close> and
      \<open>M \<Turnstile>as CNot (remove1_mset K (clause C))\<close> and
      \<open>undefined_lit M K\<close>
    then have \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># add_mset L Q)\<close>
      using cands by auto
    then show
      \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># Q) \<or>
        (\<exists>La. (La, C) \<in># Pair L `# {#C \<in># N + U. L \<in># watched C#})\<close>
      using C by auto
  qed
next
  case (propagate D L L' M N U NE UE NS US N0 U0 WS Q) note watched = this(1) and undef = this(2) and
    false = this(3) and
    twl = this(4) and valid = this(5) and inv = this(6) and excep = this(7)
    and no_dup = this(8) and cands = this(9) and to_upd = this(10)
  have uL'_M: \<open>- L' \<notin> lits_of_l M\<close>
    using Decided_Propagated_in_iff_in_lits_of_l propagate.hyps(2) by blast
  have D_N_U: \<open>D \<in># N + U\<close>
    using valid by auto
  then have wf_D: \<open>struct_wf_twl_cls D\<close>
    using twl by (simp add: twl_st_inv.simps)
  show ?case unfolding propa_cands_enqueued.simps
  proof (intro allI conjI impI)
    fix C K
    assume C: \<open>C \<in># N + U\<close> and
      K: \<open>K \<in># clause C\<close> and
      L'_M_C: \<open>Propagated L' (clause D) # M \<Turnstile>as CNot (remove1_mset K (clause C))\<close> and
      undef_K: \<open>undefined_lit (Propagated L' (clause D) # M) K\<close>
    then have wf_C: \<open>struct_wf_twl_cls C\<close>
      using twl by (simp add: twl_st_inv.simps)
    have undef_K_M: \<open>undefined_lit M K\<close>
      using undef_K by (simp add: Decided_Propagated_in_iff_in_lits_of_l)
    consider
      (no_L') \<open>M \<Turnstile>as CNot (remove1_mset K (clause C))\<close> |
      (L') \<open>-L' \<in># remove1_mset K (clause C)\<close>
      using L'_M_C \<open>- L' \<notin> lits_of_l M\<close>
      by (metis insertE list.simps(15) lit_of.simps(2) lits_of_insert
          true_annots_CNot_lit_of_notin_skip true_annots_true_cls_def_iff_negation_in_model)
    then show \<open>(\<exists>L'a. L'a \<in># watched C \<and> L'a \<in># add_mset (- L') Q) \<or> (\<exists>L. (L, C) \<in># WS)\<close>
    proof cases
      case no_L'
      then have \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in>#  Q) \<or> (\<exists>La. (La, C) \<in># add_mset (L, D) WS)\<close>
        using cands C K undef_K_M by auto
      moreover {
        have \<open>K = L'\<close> if \<open>C = D\<close>
          by (metis \<open>- L' \<notin> lits_of_l M\<close> add_mset_add_single clause.simps in_CNot_implies_uminus(2)
              in_remove1_mset_neq multi_member_this no_L' that twl_clause.exhaust twl_clause.sel(1)
              union_iff watched)
        then have False if \<open>C = D\<close>
          using undef_K by (simp add: Decided_Propagated_in_iff_in_lits_of_l that)
      }
      ultimately show ?thesis by auto
    next
      case L'
      have ?thesis if \<open>L' \<in># watched C\<close>
      proof -
        have \<open>K = L'\<close>
          using that L'_M_C \<open>- L' \<notin> lits_of_l M\<close> L' undef
          by (metis clause.simps in_CNot_implies_uminus(2) in_lits_of_l_defined_litD
              in_remove1_mset_neq insert_iff list.simps(15) lits_of_insert
              twl_clause.exhaust_sel uminus_not_id' uminus_of_uminus_id union_iff)
        then have False
          using Decided_Propagated_in_iff_in_lits_of_l undef_K by force
        then show ?thesis
          by fastforce
      qed

      moreover have ?thesis if L'_C: \<open>L' \<notin># watched C\<close>
      proof (rule ccontr, clarsimp)
        assume
          Q: \<open>\<forall>L'a. L'a \<in># watched C \<longrightarrow> L'a \<noteq> - L' \<and> L'a \<notin># Q\<close> and
          WS: \<open>\<forall>L. (L, C) \<notin># WS\<close>
        then have \<open>\<not> twl_is_an_exception C (add_mset (- L') Q) WS\<close>
          by (auto simp: twl_is_an_exception_def)
        moreover have
          \<open>twl_st_inv (Propagated L' (clause D) # M, N, U, None, NE, UE, NS, US, N0, U0, WS,
             add_mset (- L') Q)\<close>
          using twl_cp_twl_inv[OF _ twl valid inv excep no_dup to_upd]
          cdcl_twl_cp.propagate[OF propagate(1-3)] by fast
        ultimately have \<open>twl_lazy_update (Propagated L' (clause D) # M) C\<close>
          using C by (auto simp: twl_st_inv.simps)

        have CD: \<open>C \<noteq> D\<close>
          using that watched by auto
        have struct: \<open>struct_wf_twl_cls C\<close>
          using twl C by (simp add: twl_st_inv.simps)
        obtain a b W UW where
          C_W_UW: \<open>C = TWL_Clause W UW\<close> and
          W: \<open>W = {#a, b#}\<close>
          using struct by (cases C, auto simp: size_2_iff)
        have ua_or_ub: \<open>-a \<in> lits_of_l M \<or> -b \<in> lits_of_l M\<close>
          using L'_M_C C_W_UW W \<open>\<forall>L'a. L'a \<in># watched C \<longrightarrow> L'a \<noteq> - L' \<and> L'a \<notin># Q\<close>
          apply (cases \<open>K = a\<close>) by fastforce+

        have \<open>no_dup M\<close>
          using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (simp add: trail.simps)
        then have [dest]: False if \<open>a \<in> lits_of_l M\<close> and \<open>-a \<in> lits_of_l M\<close> for a
          using consistent_interp_def distinct_consistent_interp that(1) that(2) by blast
        have uab: \<open>a \<notin> lits_of_l M\<close> if \<open>-b \<in> lits_of_l M\<close>
          using L'_M_C C_W_UW W that undef_K_M uL'_M
          by (cases \<open>K = a\<close>) (fastforce simp: Decided_Propagated_in_iff_in_lits_of_l
              simp del: uL'_M)+
        have uba: \<open>b \<notin> lits_of_l M\<close> if \<open>-a \<in> lits_of_l M\<close>
          using L'_M_C C_W_UW W that undef_K_M uL'_M
          by (cases \<open>K = b\<close>) (fastforce simp: Decided_Propagated_in_iff_in_lits_of_l
              add_mset_commute[of a b])+
        have [simp]: \<open>-a \<noteq> L'\<close> \<open>-b \<noteq> L'\<close>
          using Q W C_W_UW by fastforce+
        have H': \<open>\<forall>La L'. watched C = {#La, L'#} \<longrightarrow> - La \<in> lits_of_l M \<longrightarrow>
           \<not>has_blit M (clause C) La \<longrightarrow> L' \<notin> lits_of_l M \<longrightarrow>
          (\<forall>K\<in>#unwatched C. - K \<in> lits_of_l M)\<close>
          using excep C CD Q W WS uab uba by (auto simp: twl_exception_inv.simps simp del: set_mset_union
              dest: multi_member_split)
        moreover have \<open>watched C = {#La, L''#} \<longrightarrow>- La \<in> lits_of_l M \<longrightarrow> \<not>has_blit M (clause C) La\<close> for La L''
          using in_CNot_implies_uminus[OF _ L'_M_C]  wf_C L' uL'_M undef_K_M undef uab uba
          unfolding C_W_UW has_blit_def apply -
          apply (cases \<open>La = K\<close>)
           apply (auto simp: has_blit_def Decided_Propagated_in_iff_in_lits_of_l W
              add_mset_eq_add_mset in_remove1_mset_neq)
          apply (metis \<open>\<And>a. \<lbrakk>a \<in> lits_of_l M; - a \<in> lits_of_l M\<rbrakk> \<Longrightarrow> False\<close> add_mset_remove_trivial
              defined_lit_uminus in_lits_of_l_defined_litD in_remove1_mset_neq undef)
          apply (metis \<open>\<And>a. \<lbrakk>a \<in> lits_of_l M; - a \<in> lits_of_l M\<rbrakk> \<Longrightarrow> False\<close> add_mset_remove_trivial
              defined_lit_uminus in_lits_of_l_defined_litD in_remove1_mset_neq undef)
          done
        ultimately have \<open>\<forall>K\<in>#unwatched C. - K \<in> lits_of_l M\<close>
          using uab uba W C_W_UW ua_or_ub wf_C unfolding C_W_UW
          by (auto simp: add_mset_eq_add_mset )
        then show False
          by (metis Decided_Propagated_in_iff_in_lits_of_l L' uminus_lit_swap
              Q clause.simps in_diffD propagate.hyps(2) twl_clause.collapse union_iff)
      qed

      ultimately show ?thesis by fast
    qed
  qed
next
  case (conflict D L L' M N U NE UE NS US N0 U0 WS Q) note cands = this(10)
  then show ?case
    by auto
next
  case (delete_from_working L' D M N U NE UE NS US N0 U0 L WS Q) note watched = this(1) and L' = this(2)
    and twl = this(3) and valid = this(4) and inv = this(5) and cands = this(8) and ws = this(9)
  have n_d: \<open>no_dup M\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (simp add: trail.simps)
  show ?case unfolding propa_cands_enqueued.simps
  proof (intro allI conjI impI)
    fix C K
    assume C: \<open>C \<in># N + U\<close> and
      K: \<open>K \<in># clause C\<close> and
      L'_M_C: \<open>M \<Turnstile>as CNot (remove1_mset K (clause C))\<close> and
      undef_K: \<open>undefined_lit M K\<close>
    then have \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># Q) \<or> (\<exists>La. La = L \<and> C = D \<or> (La, C) \<in># WS)\<close>
      using cands by auto
    moreover have False if [simp]: \<open>C = D\<close>
      using L' L'_M_C undef_K watched
      using Decided_Propagated_in_iff_in_lits_of_l consistent_interp_def distinct_consistent_interp
        local.K n_d K
      by (cases D)
        (auto 5 5 simp: true_annots_true_cls_def_iff_negation_in_model add_mset_eq_add_mset
          dest: in_lits_of_l_defined_litD no_dup_consistentD dest!: multi_member_split)
    ultimately show \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># Q) \<or> (\<exists>L. (L, C) \<in># WS)\<close>
      by auto
  qed
next
  case (update_clause D L L' M K N U N' U' NE UE NS US N0 U0 WS Q) note watched = this(1) and uL = this(2)
    and L' = this(3) and K = this(4) and undef = this(5) and N'U' = this(6) and twl = this(7) and
    valid = this(8) and inv = this(9) and twl_excep = this(10) and no_dup = this(11) and
    cands = this(12) and ws = this(13)
  obtain WD UWD where D: \<open>D = TWL_Clause WD UWD\<close> by (cases D)
  have L: \<open>L \<in># watched D\<close> and D_N_U: \<open>D \<in># N + U\<close> and lev_L: \<open>get_level M L = count_decided M\<close>
    using valid by auto
  then have struct_D: \<open>struct_wf_twl_cls D\<close>
    using twl by (auto simp: twl_st_inv.simps)
  have L'_UWD: \<open>L \<notin># remove1_mset L' UWD\<close> if \<open>L \<in># WD\<close> for L
  proof (rule ccontr)
    assume \<open>\<not> ?thesis\<close>
    then have \<open>count UWD L \<ge> 1\<close>
      by (auto simp del: count_greater_zero_iff simp: count_greater_zero_iff[symmetric]
          split: if_splits)
    then have \<open>count (clause D) L \<ge> 2\<close>
      using D that by (auto simp del: count_greater_zero_iff simp: count_greater_zero_iff[symmetric]
          split: if_splits)
    moreover have \<open>distinct_mset (clause D)\<close>
      using struct_D D by (auto simp: distinct_mset_union)
    ultimately show False
      unfolding distinct_mset_count_less_1 by (metis Suc_1 not_less_eq_eq)
  qed
  have L'_L'_UWD: \<open>K \<notin># remove1_mset K UWD\<close>
  proof (rule ccontr)
    assume \<open>\<not> ?thesis\<close>
    then have \<open>count UWD K \<ge> 2\<close>
      by (auto simp del: count_greater_zero_iff simp: count_greater_zero_iff[symmetric]
          split: if_splits)
    then have \<open>count (clause D) K \<ge> 2\<close>
      using D L' by (auto simp del: count_greater_zero_iff simp: count_greater_zero_iff[symmetric]
          split: if_splits)
    moreover have \<open>distinct_mset (clause D)\<close>
      using struct_D D by (auto simp: distinct_mset_union)
    ultimately show False
      unfolding distinct_mset_count_less_1 by (metis Suc_1 not_less_eq_eq)
  qed
  have \<open>watched_literals_false_of_max_level M D\<close>
    using D_N_U twl by (auto simp: twl_st_inv.simps)
  let ?D = \<open>update_clause D L K\<close>
  have *: \<open>C \<in># N + U\<close> if \<open>C \<noteq> ?D\<close> and C: \<open>C \<in># N' + U'\<close> for C
    using C N'U' that by (auto elim!: update_clausesE dest: in_diffD)
  have n_d: \<open>no_dup M\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: trail.simps)
  then have uK_M: \<open>- K \<notin> lits_of_l M\<close>
    using undef Decided_Propagated_in_iff_in_lits_of_l consistent_interp_def
      distinct_consistent_interp by blast
  have add_remove_WD: \<open>add_mset K (remove1_mset L WD) \<noteq> WD\<close>
    using uK_M uL by (auto simp: add_mset_remove_trivial_iff trivial_add_mset_remove_iff)
  have D_N_U: \<open>D \<in># N + U\<close>
    using N'U' D uK_M uL D_N_U by (auto simp: add_mset_remove_trivial_iff split: if_splits)
  have D_ne_D: \<open>D \<noteq> update_clause D L K\<close>
    using D add_remove_WD by auto

  have L_M: \<open>L \<notin> lits_of_l M\<close>
    using n_d uL by (fastforce dest!: distinct_consistent_interp
        simp: consistent_interp_def lits_of_def uminus_lit_swap)
  have w_max_D: \<open>watched_literals_false_of_max_level M D\<close>
    using D_N_U twl by (auto simp: twl_st_inv.simps)

  have clause_D: \<open>clause ?D = clause D\<close>
    using D K watched by auto
  show ?case unfolding propa_cands_enqueued.simps
  proof (intro allI conjI impI)
    fix C K2
    assume C: \<open>C \<in># N' + U'\<close> and
      K: \<open>K2 \<in># clause C\<close> and
      L'_M_C: \<open>M \<Turnstile>as CNot (remove1_mset K2 (clause C))\<close> and
      undef_K: \<open>undefined_lit M K2\<close>
    then have \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># Q) \<or> (\<exists>La. (La, C) \<in># WS)\<close> if \<open>C \<noteq> ?D\<close> \<open>C \<noteq> D\<close>
      using cands *[OF that(1) C] that(2) by auto
    moreover have \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># Q) \<or> (\<exists>L. (L, C) \<in># WS)\<close> if [simp]: \<open>C = ?D\<close>
    proof (rule ccontr)
      have \<open>K \<notin> lits_of_l M\<close>
        by (metis D Decided_Propagated_in_iff_in_lits_of_l L'_M_C add_diff_cancel_left'
            clause.simps clause_D in_diffD in_remove1_mset_neq that
            true_annots_true_cls_def_iff_negation_in_model twl_clause.sel(2) uK_M undef_K
            update_clause.hyps(4))
      moreover have \<open>\<forall>L\<in>#remove1_mset K2 (clause ?D). defined_lit M L\<close>
        using L'_M_C unfolding true_annots_true_cls_def_iff_negation_in_model
        by (auto simp: clause_D Decided_Propagated_in_iff_in_lits_of_l)
      ultimately have [simp]: \<open>K2 = K\<close>
        using undef undef_K K unfolding that clause_D
        by (metis D clause.simps in_remove1_mset_neq twl_clause.sel(2) union_iff
            update_clause.hyps(4))

      have uL'_M: \<open>- L' \<in> lits_of_l M\<close>
        using D watched L'_M_C by auto
      have [simp]: \<open>L \<noteq> L'\<close> \<open>L' \<noteq> L\<close>
        using struct_D D watched by auto

      assume \<open>\<not> ((\<exists>L'. L' \<in># watched C \<and> L' \<in># Q) \<or> (\<exists>L. (L, C) \<in># WS))\<close>
      then have [simp]: \<open>L' \<notin># Q\<close> and L'_C_WS: \<open>(L', C) \<notin># WS\<close>
        using watched D by auto
      have \<open>C \<in># add_mset (L, TWL_Clause WD UWD) WS \<longrightarrow>
        C' \<in># add_mset (L, TWL_Clause WD UWD) WS \<longrightarrow>
        fst C = fst C'\<close> for C C'
        using no_dup unfolding D no_duplicate_queued.simps
        by blast
      from this[of \<open>(L, TWL_Clause WD UWD)\<close> \<open>(L', TWL_Clause {#L, L'#} UWD)\<close>]
      have notin: \<open>False\<close> if \<open>(L', TWL_Clause {#L, L'#} UWD) \<in># WS\<close>
        using struct_D watched that unfolding D
        by auto
      have \<open>?D \<noteq> D\<close>
        using C D watched L K uK_M uL by auto
      then have excep: \<open>twl_exception_inv (M, N, U, None, NE, UE, NS, US, N0, U0, add_mset (L, D) WS, Q) D\<close>
        using twl_excep *[of D] D_N_U by (auto simp: twl_st_inv.simps)
      moreover have \<open>D = TWL_Clause {#L, L'#} UWD \<Longrightarrow>
          WD = {#L, L'#} \<Longrightarrow>
          \<forall>L\<in>#remove1_mset K UWD.
             - L \<in> lits_of_l M \<Longrightarrow>
          \<not>has_blit M (add_mset L (add_mset L' UWD)) L'\<close>
        using uL uL'_M n_d \<open>K \<notin> lits_of_l M\<close>  unfolding has_blit_def
        apply (auto dest:no_dup_consistentD simp: in_remove1_mset_neq Ball_def)
        by (metis in_remove1_mset_neq no_dup_consistentD)
      ultimately have \<open>\<forall>K \<in># unwatched D. -K \<in> lits_of_l M\<close>
        using D watched L'_M_C L'_C_WS
        by (auto simp: add_mset_eq_add_mset uL'_M L_M uL twl_exception_inv.simps
            true_annots_true_cls_def_iff_negation_in_model dest: in_diffD notin)
      then show False
        using uK_M update_clause.hyps(4) by blast
    qed
    moreover have \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># Q) \<or> (\<exists>L. (L, C) \<in># WS)\<close> if [simp]: \<open>C = D\<close>
      unfolding that
    proof -
      have n_d: \<open>no_dup M\<close>
        using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: trail.simps)
      obtain NU where NU: \<open>N + U = add_mset D NU\<close>
        by (metis D_N_U insert_DiffM)
      have N'U': \<open>N' + U' = add_mset ?D (remove1_mset D (N + U))\<close>
        using N'U' D_N_U by (auto elim!: update_clausesE)

      have \<open>add_mset L Q \<subseteq># {#- lit_of x. x \<in># mset M#}\<close>
        using no_dup by (auto)
      moreover have \<open>distinct_mset {#- lit_of x. x \<in># mset M#}\<close>
        by (subst distinct_image_mset_inj)
          (use n_d in \<open>auto simp: lit_of_inj_on_no_dup distinct_map no_dup_def\<close>)
      ultimately have [simp]: \<open>L \<notin># Q\<close>
        by (metis distinct_mset_add_mset distinct_mset_union subset_mset.le_iff_add)
      have \<open>has_blit M (clause D) L \<Longrightarrow> False\<close> (* CVC4 is amazing! *)
        by (smt K L'_M_C has_blit_def in_lits_of_l_defined_litD insert_DiffM insert_iff
            is_blit_def n_d no_dup_consistentD set_mset_add_mset_insert that
            true_annots_true_cls_def_iff_negation_in_model undef_K)
      then have w_q_p_D: \<open>clauses_to_update_prop Q M (L, D)\<close>
        by (auto simp: clauses_to_update_prop.simps watched)
           (use uL undef L' in \<open>auto simp: Decided_Propagated_in_iff_in_lits_of_l\<close>)
      have \<open>Pair L `# {#C \<in># add_mset D NU. clauses_to_update_prop Q M (L, C)#} \<subseteq>#
          add_mset (L, D) WS\<close>
        using ws no_dup unfolding clauses_to_update_inv.simps NU
        by (auto simp: all_conj_distrib)
      then have IH: \<open>Pair L `# {#C \<in># NU. clauses_to_update_prop Q M (L, C)#} \<subseteq># WS\<close>
        using w_q_p_D by auto
      moreover have \<open>(L, D) \<in># Pair L `# {#C \<in># NU. clauses_to_update_prop Q M (L, C)#}\<close>
        using C D_ne_D w_q_p_D unfolding NU N'U' by (auto simp: pair_in_image_Pair)
      ultimately show \<open>(\<exists>L'. L' \<in># watched D \<and> L' \<in># Q) \<or> (\<exists>L. (L, D) \<in># WS)\<close>
        by blast
    qed
    ultimately show \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># Q) \<or> (\<exists>L. (L, C) \<in># WS)\<close>
      by auto
  qed
qed


lemma twl_cp_confl_cands_enqueued:
  assumes
    cdcl: \<open>cdcl_twl_cp S T\<close> and
    twl: \<open>twl_st_inv S\<close> and
    valid: \<open>valid_enqueued S\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S)\<close> and
    excep: \<open>twl_st_exception_inv S\<close> and
    no_dup: \<open>no_duplicate_queued S\<close> and
    cands: \<open>confl_cands_enqueued S\<close> and
    ws: \<open>clauses_to_update_inv S\<close>
  shows
    \<open>confl_cands_enqueued T\<close>
  using cdcl
proof (induction rule: cdcl_twl_cp.cases)
  case (pop M N U NE UE NS US N0 U0 L Q) note S = this(1) and T = this(2)
  show ?case unfolding confl_cands_enqueued.simps Ball_def S T
  proof (intro allI conjI impI)
    fix C K
    assume C: \<open>C \<in># N + U\<close> and
      \<open>M \<Turnstile>as CNot (clause C)\<close>
    then have \<open>(\<exists>L'. L' \<in># watched C \<and> L'  \<in># add_mset L Q)\<close>
      using cands S by auto
    then show
      \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># Q) \<or>
        (\<exists>La. (La, C) \<in># Pair L `# {#C \<in># N + U. L \<in># watched C#})\<close>
      using C by auto
  qed
next
  case (propagate D L L' M N U NE UE NS US N0 U0 WS Q) note S = this(1) and T = this(2) and watched = this(3)
    and undef = this(4)
  have uL'_M: \<open>- L' \<notin> lits_of_l M\<close>
    using Decided_Propagated_in_iff_in_lits_of_l undef by blast
  have D_N_U: \<open>D \<in># N + U\<close>
    using valid S by auto
  then have wf_D: \<open>struct_wf_twl_cls D\<close>
    using twl by (simp add: twl_st_inv.simps S)
  show ?case unfolding confl_cands_enqueued.simps Ball_def S T
  proof (intro allI conjI impI)
    fix C K
    assume C: \<open>C \<in># N + U\<close> and
      L'_M_C: \<open>Propagated L' (clause D) # M \<Turnstile>as CNot (clause C)\<close>
    consider
        (no_L') \<open>M \<Turnstile>as CNot (clause C)\<close>
      | (L') \<open>-L' \<in># clause C\<close>
      using L'_M_C \<open>- L' \<notin> lits_of_l M\<close>
      by (metis insertE list.simps(15) lit_of.simps(2) lits_of_insert
          true_annots_CNot_lit_of_notin_skip true_annots_true_cls_def_iff_negation_in_model)
    then show \<open>(\<exists>L'a. L'a \<in># watched C \<and> L'a \<in># add_mset (- L') Q) \<or> (\<exists>L. (L, C) \<in># WS)\<close>
    proof cases
      case no_L'
      then have \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># Q) \<or> (\<exists>La. (La, C) \<in># add_mset (L, D) WS)\<close>
        using cands C by (auto simp: S)
      moreover {
        have \<open>C \<noteq> D\<close>
          by (metis \<open>- L' \<notin> lits_of_l M\<close> add_mset_add_single clause.simps in_CNot_implies_uminus(2)
              multi_member_this no_L' twl_clause.exhaust twl_clause.sel(1)
              union_iff watched)
      }
      ultimately show ?thesis by auto
    next
      case L'
      have L'_C: \<open>L' \<notin># watched C\<close>
        using L'_M_C \<open>- L' \<notin> lits_of_l M\<close>
        by (metis (no_types, hide_lams) Decided_Propagated_in_iff_in_lits_of_l L' clause.simps
            in_CNot_implies_uminus(2) insertE list.simps(15) lits_of_insert twl_clause.exhaust_sel
            uminus_not_id' uminus_of_uminus_id undef union_iff)
      moreover have ?thesis
      proof (rule ccontr, clarsimp)
        assume
          Q: \<open>\<forall>L'a. L'a \<in># watched C \<longrightarrow> L'a \<noteq> - L' \<and> L'a \<notin># Q\<close> and
          WS: \<open>\<forall>L. (L, C) \<notin># WS\<close>
        then have \<open>\<not> twl_is_an_exception C (add_mset (- L') Q) WS\<close>
          by (auto simp: twl_is_an_exception_def)
        moreover have
          \<open>twl_st_inv (Propagated L' (clause D) # M, N, U, None, NE, UE, NS, US, N0, U0, WS,
             add_mset (- L') Q)\<close>
          using twl_cp_twl_inv[OF _ twl valid inv excep no_dup ws] cdcl unfolding S T by fast
        ultimately have \<open>twl_lazy_update (Propagated L' (clause D) # M) C\<close>
          using C by (auto simp: twl_st_inv.simps)

        have struct: \<open>struct_wf_twl_cls C\<close>
          using twl C by (simp add: twl_st_inv.simps S)
        have CD: \<open>C \<noteq> D\<close>
          using L'_C watched by auto
        have struct: \<open>struct_wf_twl_cls C\<close>
          using twl C by (simp add: twl_st_inv.simps S)
        obtain a b W UW where
          C_W_UW: \<open>C = TWL_Clause W UW\<close> and
          W: \<open>W = {#a, b#}\<close>
          using struct by (cases C) (auto simp: size_2_iff)
        have ua_ub: \<open>-a \<in> lits_of_l M \<or> -b \<in> lits_of_l M\<close>
          using L'_M_C C_W_UW W \<open>\<forall>L'a. L'a \<in># watched C \<longrightarrow> L'a \<noteq> - L' \<and> L'a \<notin># Q\<close>
          by (cases \<open>K = a\<close>) fastforce+

        have \<open>no_dup M\<close>
          using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (simp add: trail.simps S)
        then have [dest]: False if \<open>a \<in> lits_of_l M\<close> and \<open>-a \<in> lits_of_l M\<close> for a
          using consistent_interp_def distinct_consistent_interp that(1) that(2) by blast
        have uab: \<open>a \<notin> lits_of_l M\<close> if \<open>-b \<in> lits_of_l M\<close>
          using L'_M_C C_W_UW W that uL'_M by (cases \<open>K = a\<close>) auto
        have uba: \<open>b \<notin> lits_of_l M\<close> if \<open>-a \<in> lits_of_l M\<close>
          using L'_M_C C_W_UW W that uL'_M by (cases \<open>K = b\<close>) auto
        have [simp]: \<open>-a \<noteq> L'\<close> \<open>-b \<noteq> L'\<close>
          using \<open>\<forall>L'a. L'a \<in># watched C \<longrightarrow> L'a \<noteq> - L' \<and> L'a \<notin># Q\<close> W C_W_UW
          by fastforce+
        have H': \<open>\<forall>La L'. watched C = {#La, L'#} \<longrightarrow> - La \<in> lits_of_l M \<longrightarrow> L' \<notin> lits_of_l M \<longrightarrow>
          \<not> has_blit M (clause C) La \<longrightarrow>(\<forall>K\<in>#unwatched C. - K \<in> lits_of_l M)\<close>
          using excep C CD Q W WS uab uba
          by (auto simp: twl_exception_inv.simps S dest: multi_member_split)
        moreover have \<open>\<not> has_blit M (clause C) a\<close> \<open>\<not> has_blit M (clause C) b\<close>
          using multi_member_split[OF C]
          using watched L' undef L'_M_C
          unfolding has_blit_def
          by (metis (no_types, lifting) Clausal_Logic.uminus_lit_swap
              \<open>\<And>a. \<lbrakk>a \<in> lits_of_l M; - a \<in> lits_of_l M\<rbrakk> \<Longrightarrow> False\<close> in_CNot_implies_uminus(2)
              in_lits_of_l_defined_litD insert_iff is_blit_def list.set(2) lits_of_insert uL'_M)+
        ultimately have \<open>\<forall>K\<in>#unwatched C. - K \<in> lits_of_l M\<close>
          using uab uba W C_W_UW ua_ub struct
          by (auto simp: add_mset_eq_add_mset)
        then show False
          by (metis Decided_Propagated_in_iff_in_lits_of_l L' uminus_lit_swap
              Q clause.simps undef twl_clause.collapse union_iff)
      qed
      ultimately show ?thesis by fast
    qed
  qed
next
  case (conflict D L L' M N U NE UE NS US N0 U0 WS Q)
  then show ?case
    by auto
next
  case (delete_from_working L' D M N U NE UE NS US N0 U0 L WS Q) note S = this(1) and T = this(2) and
    watched = this(3) and L' = this(4)
  have n_d: \<open>no_dup M\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (simp add: trail.simps S)
  show ?case unfolding confl_cands_enqueued.simps Ball_def S T
  proof (intro allI conjI impI)
    fix C
    assume C: \<open>C \<in># N + U\<close> and
      L'_M_C: \<open>M \<Turnstile>as CNot (clause C)\<close>
    then have \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># Q) \<or> (\<exists>La. La = L \<and> C = D \<or> (La, C) \<in># WS)\<close>
      using cands S by auto
    moreover have False if [simp]: \<open>C = D\<close>
      using L'_M_C watched L' n_d by (cases D) (auto dest!: distinct_consistent_interp
          simp: consistent_interp_def dest!: multi_member_split)
    ultimately show \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># Q) \<or> (\<exists>L. (L, C) \<in># WS)\<close>
      by auto
  qed
next
  case (update_clause D L L' M K N U N' U' NE UE NS US N0 U0 WS Q) note S = this(1) and T = this(2) and
    watched = this(3) and uL = this(4) and L' = this(5) and K = this(6) and undef = this(7) and
    N'U' = this(8)
  obtain WD UWD where D: \<open>D = TWL_Clause WD UWD\<close> by (cases D)
  have L: \<open>L \<in># watched D\<close> and D_N_U: \<open>D \<in># N + U\<close> and lev_L: \<open>get_level M L = count_decided M\<close>
    using valid S by auto
  then have struct_D: \<open>struct_wf_twl_cls D\<close>
    using twl by (auto simp: twl_st_inv.simps S)
  have L'_UWD: \<open>L \<notin># remove1_mset L' UWD\<close> if \<open>L \<in># WD\<close> for L
  proof (rule ccontr)
    assume \<open>\<not> ?thesis\<close>
    then have \<open>count UWD L \<ge> 1\<close>
      by (auto simp del: count_greater_zero_iff simp: count_greater_zero_iff[symmetric]
          split: if_splits)
    then have \<open>count (clause D) L \<ge> 2\<close>
      using D that by (auto simp del: count_greater_zero_iff simp: count_greater_zero_iff[symmetric]
          split: if_splits)
    moreover have \<open>distinct_mset (clause D)\<close>
      using struct_D D by (auto simp: distinct_mset_union)
    ultimately show False
      unfolding distinct_mset_count_less_1 by (metis Suc_1 not_less_eq_eq)
  qed
  have L'_L'_UWD: \<open>K \<notin># remove1_mset K UWD\<close>
  proof (rule ccontr)
    assume \<open>\<not> ?thesis\<close>
    then have \<open>count UWD K \<ge> 2\<close>
      by (auto simp del: count_greater_zero_iff simp: count_greater_zero_iff[symmetric]
          split: if_splits)
    then have \<open>count (clause D) K \<ge> 2\<close>
      using D L' by (auto simp del: count_greater_zero_iff simp: count_greater_zero_iff[symmetric]
          split: if_splits)
    moreover have \<open>distinct_mset (clause D)\<close>
      using struct_D D by (auto simp: distinct_mset_union)
    ultimately show False
      unfolding distinct_mset_count_less_1 by (metis Suc_1 not_less_eq_eq)
  qed
  have \<open>watched_literals_false_of_max_level M D\<close>
    using D_N_U twl by (auto simp: twl_st_inv.simps S)
  let ?D = \<open>update_clause D L K\<close>
  have *: \<open>C \<in># N + U\<close> if \<open>C \<noteq> ?D\<close> and C: \<open>C \<in># N' + U'\<close> for C
    using C N'U' that by (auto elim!: update_clausesE dest: in_diffD)
  have n_d: \<open>no_dup M\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: trail.simps S)
  then have uK_M: \<open>- K \<notin> lits_of_l M\<close>
    using undef Decided_Propagated_in_iff_in_lits_of_l consistent_interp_def
      distinct_consistent_interp by blast
  have add_remove_WD: \<open>add_mset K (remove1_mset L WD) \<noteq> WD\<close>
    using uK_M uL by (auto simp: add_mset_remove_trivial_iff trivial_add_mset_remove_iff)
  have D_N_U: \<open>D \<in># N + U\<close>
    using N'U' D uK_M uL D_N_U by (auto simp: add_mset_remove_trivial_iff split: if_splits)

  have D_ne_D: \<open>D \<noteq> update_clause D L K\<close>
    using D add_remove_WD by auto

  have L_M: \<open>L \<notin> lits_of_l M\<close>
    using n_d uL by (fastforce dest!: distinct_consistent_interp
        simp: consistent_interp_def lits_of_def uminus_lit_swap)
  have w_max_D: \<open>watched_literals_false_of_max_level M D\<close>
    using D_N_U twl by (auto simp: twl_st_inv.simps S)

  have clause_D: \<open>clause ?D = clause D\<close>
    using D K watched by auto

  show ?case unfolding confl_cands_enqueued.simps Ball_def S T
  proof (intro allI conjI impI)
    fix C
    assume C: \<open>C \<in># N' + U'\<close> and
      L'_M_C: \<open>M \<Turnstile>as CNot (clause C)\<close>
    then have \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># Q) \<or> (\<exists>La. (La, C) \<in># WS)\<close> if \<open>C \<noteq> ?D\<close> \<open>C \<noteq> D\<close>
      using cands *[OF that(1) C] that(2) S by auto
    moreover have \<open>C \<noteq> ?D\<close>
      by (metis D L'_M_C add_diff_cancel_left'  clause.simps clause_D in_diffD
          true_annots_true_cls_def_iff_negation_in_model twl_clause.sel(2) uK_M K)
    moreover have \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># Q) \<or> (\<exists>La. (La, C) \<in># WS)\<close> if [simp]: \<open>C = D\<close>
      unfolding that
    proof -
      obtain NU where NU: \<open>N + U = add_mset D NU\<close>
        by (metis D_N_U insert_DiffM)
      have N'U': \<open>N' + U' = add_mset ?D (remove1_mset D (N + U))\<close>
        using N'U' D_N_U by (auto elim!: update_clausesE)

      have \<open>add_mset L Q \<subseteq># {#- lit_of x. x \<in># mset M#}\<close>
        using no_dup by (auto simp: S)
      moreover have \<open>distinct_mset {#- lit_of x. x \<in># mset M#}\<close>
        by (subst distinct_image_mset_inj)
          (use n_d in \<open>auto simp: lit_of_inj_on_no_dup distinct_map no_dup_def\<close>)
      ultimately have [simp]: \<open>L \<notin># Q\<close>
        by (metis distinct_mset_add_mset distinct_mset_union subset_mset.le_iff_add)

      have \<open>has_blit M (clause D) L \<Longrightarrow> False\<close> (* CVC4 is amazing! *)
        by (smt K L'_M_C has_blit_def in_lits_of_l_defined_litD insert_DiffM insert_iff
            is_blit_def n_d no_dup_consistentD set_mset_add_mset_insert that
            true_annots_true_cls_def_iff_negation_in_model)
      then have w_q_p_D: \<open>clauses_to_update_prop Q M (L, D)\<close>
        by (auto simp: clauses_to_update_prop.simps watched)
           (use uL undef L' in \<open>auto simp: Decided_Propagated_in_iff_in_lits_of_l\<close>)
      have \<open>Pair L `# {#C \<in># add_mset D NU. clauses_to_update_prop Q M (L, C)#} \<subseteq>#
          add_mset (L, D) WS\<close>
        using ws no_dup unfolding clauses_to_update_inv.simps NU S
        by (auto simp: all_conj_distrib)
      then have IH: \<open>Pair L `# {#C \<in># NU. clauses_to_update_prop Q M (L, C)#} \<subseteq># WS\<close>
        using w_q_p_D by auto
      moreover have \<open>(L, D) \<in># Pair L `# {#C \<in># NU. clauses_to_update_prop Q M (L, C)#}\<close>
        using C D_ne_D w_q_p_D unfolding NU N'U' by (auto simp: pair_in_image_Pair)
      ultimately show \<open>(\<exists>L'. L' \<in># watched D \<and> L' \<in># Q) \<or> (\<exists>L. (L, D) \<in># WS)\<close>
        by blast
    qed
    ultimately show \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># Q) \<or> (\<exists>L. (L, C) \<in># WS)\<close>
      by auto
  qed
qed

lemma twl_cp_past_invs:
  assumes
    cdcl: \<open>cdcl_twl_cp S T\<close> and
    twl: \<open>twl_st_inv S\<close> and
    valid: \<open>valid_enqueued S\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S)\<close> and
    twl_excep: \<open>twl_st_exception_inv S\<close> and
    no_dup: \<open>no_duplicate_queued S\<close> and
    past_invs: \<open>past_invs S\<close>
  shows \<open>past_invs T\<close>
  using cdcl twl valid inv twl_excep no_dup past_invs
proof (induction rule: cdcl_twl_cp.induct)
  case (pop M N U NE UE NS US N0 U0 L Q) note past_invs = this(6)
  then show ?case
    by (subst past_invs_enqueud, subst (asm) past_invs_enqueud)
next
  case (propagate D L L' M N U NE UE NS US N0 U0 WS Q) note watched = this(1) and twl = this(4) and
    valid = this(5) and inv = this(6) and past_invs = this(9)
  have [simp]: \<open>- L' \<notin> lits_of_l M\<close>
    using Decided_Propagated_in_iff_in_lits_of_l propagate.hyps(2) by blast
  have D_N_U: \<open>D \<in># N + U\<close>
    using valid by auto
  then have wf_D: \<open>struct_wf_twl_cls D\<close>
    using twl by (simp add: twl_st_inv.simps)
  show ?case unfolding past_invs.simps Ball_def
  proof (intro allI conjI impI)
    fix C
    assume C: \<open>C \<in># N + U\<close>

    fix M1 M2 :: \<open>('a, 'a clause) ann_lits\<close> and K
    assume \<open>Propagated L' (clause D) # M = M2 @ Decided K # M1\<close>
    then have M: \<open>M = tl M2 @ Decided K # M1\<close>
      by (meson cdcl\<^sub>W_restart_mset.propagated_cons_eq_append_decide_cons)
    then show
      \<open>twl_lazy_update M1 C\<close> and
      \<open>watched_literals_false_of_max_level M1 C\<close> and
      \<open>twl_exception_inv (M1, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#}) C\<close>
      using C past_invs by (auto simp add: past_invs.simps)
  next
    fix M1 M2 :: \<open>('a, 'a clause) ann_lits\<close> and K
    assume \<open>Propagated L' (clause D) # M = M2 @ Decided K # M1\<close>
    then have M: \<open>M = tl M2 @ Decided K # M1\<close>
      by (meson cdcl\<^sub>W_restart_mset.propagated_cons_eq_append_decide_cons)
    then show \<open>confl_cands_enqueued (M1, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#})\<close> and
      \<open>propa_cands_enqueued (M1, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#})\<close> and
      \<open>clauses_to_update_inv (M1, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#})\<close>
      using past_invs by (auto simp add: past_invs.simps)
  qed
next
  case (conflict D L L' M N U NE UE NS US N0 U0 WS Q) note twl = this(9)
  then show ?case
    by (auto simp: past_invs.simps)
next
  case (delete_from_working L' D M N U NE UE NS US N0 U0 L WS Q) note watched = this(1) and L' = this(2) and
  twl = this(3) and valid = this(4) and inv = this(5) and past_invs = this(8)
  show ?case unfolding past_invs.simps Ball_def
  proof (intro allI conjI impI)
    fix C
    assume C: \<open>C \<in># N + U\<close>

    fix M1 M2 :: \<open>('a, 'a clause) ann_lits\<close> and K
    assume \<open>M = M2 @ Decided K # M1\<close>
    then show \<open>twl_lazy_update M1 C\<close> and
      \<open>watched_literals_false_of_max_level M1 C\<close> and
      \<open>twl_exception_inv (M1, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#}) C\<close>
      using C past_invs by (auto simp add: past_invs.simps)
  next
    fix M1 M2 :: \<open>('a, 'a clause) ann_lits\<close> and K
    assume \<open>M = M2 @ Decided K # M1\<close>
    then show \<open>confl_cands_enqueued (M1, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#})\<close> and
      \<open>propa_cands_enqueued (M1, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#})\<close> and
      \<open>clauses_to_update_inv (M1, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#})\<close>
      using past_invs by (auto simp add: past_invs.simps)
  qed
next
  case (update_clause D L L' M K N U N' U' NE UE NS US N0 U0 WS Q) note watched = this(1) and uL = this(2)
    and L' = this(3) and K = this(4) and undef = this(5) and N'U' = this(6) and twl = this(7) and
    valid = this(8) and inv = this(9) and twl_excep = this(10) and no_dup = this(11) and
    past_invs = this(12)
  obtain WD UWD where D: \<open>D = TWL_Clause WD UWD\<close> by (cases D)
  have L: \<open>L \<in># watched D\<close> and D_N_U: \<open>D \<in># N + U\<close> and lev_L: \<open>get_level M L = count_decided M\<close>
    using valid by auto
  then have struct_D: \<open>struct_wf_twl_cls D\<close>
    using twl by (auto simp: twl_st_inv.simps)
  have L'_UWD: \<open>L \<notin># remove1_mset L' UWD\<close> if \<open>L \<in># WD\<close> for L
  proof (rule ccontr)
    assume \<open>\<not> ?thesis\<close>
    then have \<open>count UWD L \<ge> 1\<close>
      by (auto simp del: count_greater_zero_iff simp: count_greater_zero_iff[symmetric]
          split: if_splits)
    then have \<open>count (clause D) L \<ge> 2\<close>
      using D that by (auto simp del: count_greater_zero_iff simp: count_greater_zero_iff[symmetric]
          split: if_splits)
    moreover have \<open>distinct_mset (clause D)\<close>
      using struct_D D by (auto simp: distinct_mset_union)
    ultimately show False
      unfolding distinct_mset_count_less_1 by (metis Suc_1 not_less_eq_eq)
  qed
  have L'_L'_UWD: \<open>K \<notin># remove1_mset K UWD\<close>
  proof (rule ccontr)
    assume \<open>\<not> ?thesis\<close>
    then have \<open>count UWD K \<ge> 2\<close>
      by (auto simp del: count_greater_zero_iff simp: count_greater_zero_iff[symmetric]
          split: if_splits)
    then have \<open>count (clause D) K \<ge> 2\<close>
      using D L' by (auto simp del: count_greater_zero_iff simp: count_greater_zero_iff[symmetric]
          split: if_splits)
    moreover have \<open>distinct_mset (clause D)\<close>
      using struct_D D by (auto simp: distinct_mset_union)
    ultimately show False
      unfolding distinct_mset_count_less_1 by (metis Suc_1 not_less_eq_eq)
  qed
  have \<open>watched_literals_false_of_max_level M D\<close>
    using D_N_U twl by (auto simp: twl_st_inv.simps)
  let ?D = \<open>update_clause D L K\<close>
  have *: \<open>C \<in># N + U\<close> if \<open>C \<noteq> ?D\<close> and C: \<open>C \<in># N' + U'\<close> for C
    using C N'U' that by (auto elim!: update_clausesE dest: in_diffD)
  have n_d: \<open>no_dup M\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: trail.simps)
  then have uK_M: \<open>- K \<notin> lits_of_l M\<close>
    using undef Decided_Propagated_in_iff_in_lits_of_l consistent_interp_def
      distinct_consistent_interp by blast
  have add_remove_WD: \<open>add_mset K (remove1_mset L WD) \<noteq> WD\<close>
    using uK_M uL by (auto simp: add_mset_remove_trivial_iff trivial_add_mset_remove_iff)
  have cls_D_D: \<open>clause ?D = clause D\<close>
    by (cases D) (use watched K in auto)

  have L_M: \<open>L \<notin> lits_of_l M\<close>
    using n_d uL by (fastforce dest!: distinct_consistent_interp
        simp: consistent_interp_def lits_of_def uminus_lit_swap)
  have w_max_D: \<open>watched_literals_false_of_max_level M D\<close>
    using D_N_U twl by (auto simp: twl_st_inv.simps)

  show ?case unfolding past_invs.simps Ball_def
  proof (intro allI conjI impI)
    fix C
    assume C: \<open>C \<in># N' + U'\<close>

    fix M1 M2 :: \<open>('a, 'a clause) ann_lits\<close> and K'
    assume M: \<open>M = M2 @ Decided K' # M1\<close>

    have lev_L_M1: \<open>get_level M1 L = 0\<close>
      using lev_L n_d unfolding M
      apply (auto simp: get_level_append_if get_level_cons_if
          atm_of_notin_get_level_eq_0 split: if_splits dest: defined_lit_no_dupD)
      using atm_of_notin_get_level_eq_0 defined_lit_no_dupD(1) apply blast
      apply (simp add: defined_lit_map)
      by (metis Suc_count_decided_gt_get_level add_Suc_right not_add_less2)

    have \<open>twl_lazy_update M1 D\<close>
      using past_invs D_N_U unfolding past_invs.simps M twl_lazy_update.simps C
      by fast
    then have
      lazy_L': \<open>- L' \<in> lits_of_l M1 \<Longrightarrow> \<not> has_blit M1 (add_mset L (add_mset L' UWD)) L' \<Longrightarrow>
            (\<forall>K\<in>#UWD. get_level M1 K \<le> get_level M1 L' \<and> - K \<in> lits_of_l M1)\<close>
      using watched unfolding D twl_lazy_update.simps
      by (simp_all add: all_conj_distrib)
    have excep_inv: \<open>twl_exception_inv (M1, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#}) C\<close> if \<open>C \<noteq> ?D\<close>
      using * C past_invs that M by (auto simp add: past_invs.simps)
    then have \<open>twl_exception_inv (M1, N', U', None, NE, UE, NS, US, N0, U0, {#}, {#}) C\<close> if \<open>C \<noteq> ?D\<close>
      using N'U' that by (auto simp add: twl_st_inv.simps twl_exception_inv.simps)
    moreover have \<open>twl_lazy_update M1 C\<close> \<open>watched_literals_false_of_max_level M1 C\<close>
      if \<open>C \<noteq> ?D\<close>
      using * C twl past_invs M N'U' that
      by (auto simp add: past_invs.simps twl_exception_inv.simps)
    moreover {
      have \<open>twl_lazy_update M1 ?D\<close>
        using D watched uK_M K lazy_L'
          by (auto simp add: M add_mset_eq_add_mset twl_exception_inv.simps lev_L_M1
              all_conj_distrib add_mset_commute dest!: multi_member_split[of K])
    }
    moreover have \<open>watched_literals_false_of_max_level M1 ?D\<close>
      using D watched uK_M K lazy_L'
      by (auto simp add: M add_mset_eq_add_mset twl_exception_inv.simps lev_L_M1
          all_conj_distrib add_mset_commute dest!: multi_member_split[of K])
    moreover have \<open>twl_exception_inv (M1, N', U', None, NE, UE, NS, US, N0, U0, {#}, {#}) ?D\<close>
       using D watched uK_M K lazy_L'
       by (auto simp add: M add_mset_eq_add_mset twl_exception_inv.simps lev_L_M1
           all_conj_distrib add_mset_commute dest!: multi_member_split[of K])
    ultimately show \<open>twl_lazy_update M1 C\<close> \<open>watched_literals_false_of_max_level M1 C\<close>
      \<open>twl_exception_inv (M1, N', U', None, NE, UE, NS, US, N0, U0, {#}, {#}) C\<close>
      by blast+
  next
    have [dest!]: \<open>C \<in># N' \<Longrightarrow> C \<in># N \<or> C = ?D\<close> \<open>C \<in># U' \<Longrightarrow> C \<in># U \<or> C = ?D\<close> for C
      using N'U' by (auto elim!: update_clausesE dest: in_diffD)
    fix M1 M2 :: \<open>('a, 'a clause) ann_lits\<close> and K'
    assume M: \<open>M = M2 @ Decided K' # M1\<close>
    then have \<open>confl_cands_enqueued (M1, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#})\<close> and
      \<open>propa_cands_enqueued (M1, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#})\<close> and
      w_q: \<open>clauses_to_update_inv (M1, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#})\<close>
      using past_invs by (auto simp add: past_invs.simps)
    moreover have \<open>\<not>M1 \<Turnstile>as CNot (clause ?D)\<close>
      using K uK_M unfolding true_annots_true_cls_def_iff_negation_in_model cls_D_D M
      by (cases D) auto
    moreover {
      have lev_L_M: \<open>get_level M L = count_decided M\<close> and uL_M: \<open>-L \<in> lits_of_l M\<close>
        using valid by auto
      have \<open>-L \<notin> lits_of_l M1\<close>
      proof (rule ccontr)
        assume \<open>\<not> ?thesis\<close>
        then have \<open>undefined_lit (M2 @ [Decided K']) L\<close>
          using uL_M n_d unfolding M
          by (auto simp: lits_of_def uminus_lit_swap no_dup_def defined_lit_map
              dest: mk_disjoint_insert)
        then show False
          using lev_L_M count_decided_ge_get_level[of M1 L]
          by (auto simp: lits_of_def uminus_lit_swap M)
      qed
      then have \<open>\<not>M1 \<Turnstile>as CNot (remove1_mset K'' (clause ?D))\<close> for K''
        using K uK_M watched D unfolding M by (cases \<open>K'' = L\<close>) auto }
    ultimately show \<open>confl_cands_enqueued (M1, N', U', None, NE, UE, NS, US, N0, U0, {#}, {#})\<close> and
      \<open>propa_cands_enqueued (M1, N', U', None, NE, UE, NS, US, N0, U0, {#}, {#})\<close>
      by (auto simp add: twl_st_inv.simps split: if_splits)
    obtain NU where NU: \<open>N + U = add_mset D NU\<close>
      by (metis D_N_U insert_DiffM)
    then have NU_remove: \<open>NU = remove1_mset D (N + U)\<close>
      by auto
    have \<open>N' + U' = add_mset ?D (remove1_mset D (N + U))\<close>
      using N'U' D_N_U by (auto elim!: update_clausesE)
    then have N'U': \<open>N'+U' = add_mset ?D NU\<close>
      unfolding NU_remove .
    have watched_D: \<open>watched ?D = {#K, L'#}\<close>
      using D add_remove_WD watched by auto

    have \<open>twl_lazy_update M1 D\<close>
      using past_invs D_N_U unfolding past_invs.simps M twl_lazy_update.simps
      by fast
    then have
      lazy_L': \<open>- L' \<in> lits_of_l M1 \<Longrightarrow> \<not> has_blit M1 (add_mset L (add_mset L' UWD)) L' \<Longrightarrow>
            (\<forall>K\<in>#UWD. get_level M1 K \<le> get_level M1 L' \<and> - K \<in> lits_of_l M1)\<close>
      using watched unfolding D twl_lazy_update.simps
      by (simp_all add: all_conj_distrib)
    have uL'_M1: \<open>has_blit M1 (clause (update_clause D L K)) L'\<close> if \<open>- L' \<in> lits_of_l M1\<close>
    proof -
      show ?thesis
        using K uK_M lazy_L' that D watched unfolding cls_D_D
        by (force simp: M dest!: multi_member_split[of K UWD])
    qed
    show \<open>clauses_to_update_inv (M1, N', U', None, NE, UE, NS, US, N0, U0, {#}, {#})\<close>
    proof (induction rule: clauses_to_update_inv_cases)
      case (WS_nempty L C)
      then show ?case by simp
    next
      case (WS_empty K'')
      have uK_M1: \<open>- K \<notin> lits_of_l M1\<close>
        using uK_M unfolding M by auto
      have \<open>\<not>clauses_to_update_prop {#} M1 (K'', ?D)\<close>
        using uK_M1 uL'_M1 by (auto simp: clauses_to_update_prop.simps watched_D
            add_mset_eq_add_mset)
      then show ?case
        using w_q unfolding clauses_to_update_inv.simps N'U' NU
        by (auto split: if_splits simp: all_conj_distrib watched_D add_mset_eq_add_mset)
    next
      case (Q J C)
      moreover have \<open>- K \<notin> lits_of_l M1\<close>
        using uK_M unfolding M by auto
      moreover have \<open>clauses_to_update_prop {#} M1 (L', D)\<close> if \<open>- L' \<in> lits_of_l M1\<close>
        using watched that uL'_M1 Q.hyps calculation(1,2,3,6) cls_D_D
          insert_DiffM w_q watched_D by auto
      ultimately show ?case
        using w_q watched_D unfolding clauses_to_update_inv.simps N'U' NU
        by (fastforce split: if_splits simp: all_conj_distrib add_mset_eq_add_mset)
    qed
  qed
qed


subsection \<open>Invariants and the Transition System\<close>

subsubsection \<open>Conflict and propagate\<close>

fun literals_to_update_measure :: \<open>'v twl_st \<Rightarrow> nat list\<close> where
  \<open>literals_to_update_measure S = [size (literals_to_update S), size (clauses_to_update S)]\<close>

lemma twl_cp_propagate_or_conflict:
  assumes
    cdcl: \<open>cdcl_twl_cp S T\<close> and
    twl: \<open>twl_st_inv S\<close> and
    valid: \<open>valid_enqueued S\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S)\<close>
  shows
    \<open>cdcl_propagate (pstate\<^sub>W_of S) (pstate\<^sub>W_of T) \<or>
    cdcl_conflict (pstate\<^sub>W_of S) (pstate\<^sub>W_of T) \<or>
    (pstate\<^sub>W_of S = pstate\<^sub>W_of T \<and> (literals_to_update_measure T, literals_to_update_measure S) \<in>
       lexn less_than 2)\<close>
  using cdcl twl valid inv
proof (induction rule: cdcl_twl_cp.induct)
  case (pop M N U N0 U0 L Q)
  then show ?case by (simp add: lexn2_conv)
next
  case (propagate D L L' M N U NE UE NS US N0 U0 WS Q) note watched = this(1) and undef = this(2) and
    no_upd = this(3) and twl = this(4) and valid = this(5) and inv = this(6)
  let ?S = \<open>pstate\<^sub>W_of (M, N, U, None, NE, UE, NS, US, N0, U0, add_mset (L, D) WS, Q)\<close>
  let ?T = \<open>pstate\<^sub>W_of (Propagated L' (clause D) # M, N, U, None, NE, UE, NS, US, N0, U0, WS,
    add_mset (- L') Q)\<close>
  have \<open>\<forall>s\<in>#clause `# U. \<not> tautology s\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def by (simp_all add: cdcl\<^sub>W_restart_mset_state)
  have D_N_U: \<open>D \<in># N + U\<close>
    using valid by auto
  have \<open>cdcl_propagate ?S ?T\<close>
    unfolding pstate\<^sub>W_of.simps
    apply (rule cdcl_propagate.intros[of L' \<open>clause D\<close>])
      using watched apply (cases D, simp add: clauses_def; fail)
     using no_upd watched valid apply (cases D;
         simp add: trail.simps true_annots_true_cls_def_iff_negation_in_model; fail)
     using undef apply (simp add: trail.simps)
     apply (use \<open>D \<in># N+U\<close> in \<open>auto simp add: clauses_def state\<^sub>W_of_def\<close>; fail)
     done
  then show ?case by blast
next
  case (conflict D L L' M N U NE UE NS US N0 U0 WS Q) note watched = this(1) and defined = this(2)
    and no_upd = this(3) and twl = this(3) and valid = this(5) and inv = this(6)
  let ?S = \<open>pstate\<^sub>W_of (M, N, U, None, NE, UE, NS, US, N0, U0, add_mset (L, D) WS, Q)\<close>
  let ?T = \<open>pstate\<^sub>W_of (M, N, U, Some (clause D), NE, UE, NS, US, N0, U0, {#}, {#})\<close>
  have D_N_U: \<open>D \<in># N + U\<close>
    using valid by auto
  have \<open>distinct_mset (clause D)\<close>
    using inv valid \<open>D \<in># N + U\<close> unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def distinct_mset_set_def
    by (auto simp: cdcl\<^sub>W_restart_mset_state)
  then have \<open>L \<noteq> L'\<close>
    using watched by (cases D) simp
  have \<open>M \<Turnstile>as CNot (unwatched D)\<close>
    using no_upd by (auto simp: true_annots_true_cls_def_iff_negation_in_model)
  have \<open>cdcl_conflict ?S ?T\<close>
    unfolding pstate\<^sub>W_of.simps
    apply (rule cdcl_conflict.intros[of _ \<open>clause D\<close>])
    using watched defined valid \<open>M \<Turnstile>as CNot (unwatched D)\<close>
    apply (cases D; auto simp add: clauses_def
         trail.simps twl_st_inv.simps; fail)
    apply (use \<open>D \<in># N+U\<close> in \<open>auto simp add: clauses_def state\<^sub>W_of_def\<close>; fail)
    done
  then show ?case by fast
next
  case (delete_from_working D L L' M N U NE UE NS US N0 U0 WS Q)
  then show ?case by (simp add: lexn2_conv)
next
  case (update_clause D L L' M K N U N' U' NE UE NS US N0 U0 WS Q) note unwatched = this(4) and
    valid = this(8)
  have \<open>D \<in># N + U\<close>
    using valid by auto
  have [simp]: \<open>clause (update_clause D L K) = clause D\<close>
    using valid unwatched by (cases D) (auto simp: diff_union_swap2[symmetric]
        simp del: diff_union_swap2)
  have \<open>pstate\<^sub>W_of (M, N, U, None, NE, UE, NS, US, N0, U0, add_mset (L, D) WS, Q) =
    pstate\<^sub>W_of (M, N', U', None, NE, UE, NS, US, N0, U0, WS, Q)\<close>
    \<open>(literals_to_update_measure (M, N', U', None, NE, UE, NS, US, N0, U0, WS, Q),
       literals_to_update_measure (M, N, U, None, NE, UE, NS, US, N0, U0, add_mset (L, D) WS, Q))
     \<in> lexn less_than 2\<close>
    using update_clause \<open>D \<in># N + U\<close> by (cases \<open>D \<in># N\<close>)
      (fastforce simp: image_mset_remove1_mset_if elim!: update_clausesE
        simp add: lexn2_conv)+
  then show ?case by fast
qed

lemma cdcl_twl_o_cdcl\<^sub>W_o:
  assumes
    cdcl: \<open>cdcl_twl_o S T\<close> and
    twl: \<open>twl_st_inv S\<close> and
    valid: \<open>valid_enqueued S\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S)\<close>
  shows \<open>pcdcl_tcore (pstate\<^sub>W_of S) (pstate\<^sub>W_of T)\<close>
  using cdcl twl valid inv
proof (induction rule: cdcl_twl_o.induct)
  case (decide M L N NE NS N0 U UE US U0) note undef = this(1) and atm = this(2)
  have \<open>cdcl_decide (pstate\<^sub>W_of (M, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#}))
    (pstate\<^sub>W_of (Decided L # M, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#-L#}))\<close>
    unfolding pstate\<^sub>W_of.simps
    apply (rule cdcl_decide.intros)
      using undef apply (simp add: trail.simps; fail)
     using atm apply (simp add: cdcl\<^sub>W_restart_mset_state; fail)
     done
  then show ?case
    by (blast dest: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o.intros pcdcl_core.intros pcdcl_tcore.intros)
next
  case (skip L D C' M N U NE UE N0 U0 NS US) note LD = this(1) and D = this(2)
  show ?case
    apply (rule pcdcl_tcore.intros(1), rule pcdcl_core.intros(4))
    unfolding pstate\<^sub>W_of.simps
    apply (rule cdcl_skip.intros)
      using LD apply (simp; fail)
     using D apply (simp; fail)
    done
next
  case (resolve L D C M N U NE UE NS US N0 U0) note LD = this(1) and lev = this(2) and inv = this(5)
  have \<open>\<forall>La mark a b. a @ Propagated La mark # b = Propagated L C # M \<longrightarrow>
      b \<Turnstile>as CNot (remove1_mset La mark) \<and> La \<in># mark\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
     cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    by (auto simp: trail.simps)
  then have LC: \<open>L \<in># C\<close>
    by blast
  show ?case
    apply (rule pcdcl_tcore.intros(1), rule pcdcl_core.intros(5))
    unfolding pstate\<^sub>W_of.simps
    apply (rule cdcl_resolve.intros)
     using LD apply (simp; fail)
     using lev apply (simp add: cdcl\<^sub>W_restart_mset_state; fail)
     using LC apply (simp add: trail.simps; fail)
     done
next
  case (backtrack_unit_clause L D K M1 M2 M D' i N U NE UE NS US N0 U0) note L_D = this(1) and
     decomp = this(2) and lev_L = this(3) and max_D'_L = this(4) and lev_D = this(5) and
     lev_K = this(6) and D'_D = this(8) and NU_D' = this(9) and inv = this(12) and
     D'[simp] = this(7)
  have D: \<open>D = add_mset L (remove1_mset L D)\<close>
    using L_D by auto
  show ?case
    apply (rule pcdcl_tcore.intros(4))
    unfolding pstate\<^sub>W_of.simps
    apply (subst D)
    apply (rule cdcl_backtrack_unit.intros)
    using backtrack_unit_clause by auto
next
  case (backtrack_nonunit_clause L D K M1 M2 M D' i N U NE UE NS US N0 U0 L') note LD = this(1) and
    decomp = this(2) and lev_L = this(3) and max_lev = this(4) and i = this(5) and lev_K = this(6)
    and D'_D = this(8) and NU_D' = this(9) and L_D' = this(10) and L' = this(11-12) and
    inv = this(15)
  let ?S = \<open>state\<^sub>W_of (M, N, U, Some D, NE, UE, NS, US, N0, U0, {#}, {#})\<close>
  let ?T = \<open>state\<^sub>W_of (Propagated L D # M1, N, U, None, NE, add_mset {#L#} UE, NS, US, N0, U0, {#}, {#L#})\<close>
  have n_d: \<open>no_dup M\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (simp add: cdcl\<^sub>W_restart_mset_state)
  have \<open>undefined_lit M1 L\<close>
    apply (rule cdcl\<^sub>W_restart_mset.backtrack_lit_skiped[of ?S _ K _ M2 i])
    subgoal
      using lev_L inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
      by (simp add: cdcl\<^sub>W_restart_mset_state; fail)
    subgoal using decomp by (simp add: trail.simps; fail)
    subgoal using lev_L inv
      unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
      by (simp add: cdcl\<^sub>W_restart_mset_state; fail)
   subgoal using lev_K by (simp add: trail.simps; fail)
   done
  obtain M3 where M3: \<open>M = M3 @ M2 @ Decided K # M1\<close>
    using decomp by (blast dest!: get_all_ann_decomposition_exists_prepend)

  have \<open>undefined_lit (M3 @ M2) K\<close>
    using n_d unfolding M3 by (auto simp: lits_of_def)
  then have count_M1: \<open>count_decided M1 = i\<close>
    using lev_K unfolding M3 by (auto simp: image_Un)
  have \<open>L \<noteq> L'\<close>
    using L' lev_L lev_K count_decided_ge_get_level[of M K] L' by auto
  then have D: \<open>add_mset L (add_mset L' (D' - {#L, L'#})) = D'\<close>
    using L' L_D'
    by (metis add_mset_diff_bothsides diff_single_eq_union insert_noteq_member mset_add)
  then have D4: \<open>({#L, L'#} + (D' - {#L, L'#})) = add_mset L (add_mset L' (D' - {#L, L'#}))\<close>
    by auto
  have D': \<open>remove1_mset L D' = add_mset L' (D' - {#L, L'#})\<close>
    by (subst D[symmetric]) auto
  have D'': \<open>D = add_mset L (remove1_mset L D)\<close>
    using L_D' D'_D by auto
  show ?case
    apply (subst D[symmetric])
    apply (subst D'')
    apply (rule pcdcl_tcore.intros(1), rule pcdcl_core.intros(6))
    unfolding pstate\<^sub>W_of.simps image_mset_add_mset clause.simps D4
    apply (rule cdcl_backtrack.intros[of K M1 M2 _ _ _ i])
    subgoal using decomp by (simp add: trail.simps)
    subgoal using lev_L by (simp add: cdcl\<^sub>W_restart_mset_state; fail)
    subgoal using max_lev L_D' by (simp add: cdcl\<^sub>W_restart_mset_state get_maximum_level_add_mset D)
    subgoal using i by (simp add: cdcl\<^sub>W_restart_mset_state D')
    subgoal using lev_K i unfolding D' by (simp add: trail.simps)
    subgoal using D'_D by (metis D' mset_le_subtract)
    subgoal using NU_D' L_D' by (simp add: mset_le_subtract clauses_def ac_simps D)
    done
qed

lemma cdcl_twl_cp_cdcl\<^sub>W_stgy:
  \<open>cdcl_twl_cp S T \<Longrightarrow> twl_struct_invs S \<Longrightarrow>
  pcdcl_tcore_stgy (pstate\<^sub>W_of S) (pstate\<^sub>W_of T) \<or>
  (state\<^sub>W_of S = state\<^sub>W_of T \<and> state\<^sub>W_of S = state\<^sub>W_of T \<and> (literals_to_update_measure T, literals_to_update_measure S)
   \<in> lexn less_than 2)\<close>
  by (auto dest!: twl_cp_propagate_or_conflict
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.conflict'
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.propagate'
      intro: pcdcl_core.intros pcdcl_core_stgy.intros pcdcl_tcore_stgy.intros
      simp: twl_struct_invs_def pcdcl_all_struct_invs_def)

lemma cdcl_twl_cp_conflict:
  \<open>cdcl_twl_cp S T \<Longrightarrow> get_conflict T \<noteq> None \<longrightarrow>
     clauses_to_update T = {#} \<and> literals_to_update T = {#}\<close>
  by (induction rule: cdcl_twl_cp.induct) auto

lemma cdcl_twl_cp_twl_struct_invs:
  \<open>cdcl_twl_cp S T \<Longrightarrow> twl_struct_invs S \<Longrightarrow> twl_struct_invs T\<close>
  supply [simp] = pcdcl_all_struct_invs_def
  apply (subst twl_struct_invs_def)
  apply (intro conjI)
  subgoal by (rule twl_cp_twl_inv; auto simp add: twl_struct_invs_def twl_cp_twl_inv)
  subgoal by (simp add: twl_cp_valid twl_struct_invs_def)
  subgoal by (metis pcdcl_all_struct_invs_def pcdcl_core.intros(1) pcdcl_core.intros(2)
      pcdcl_tcore.simps pcdcl_tcore_pcdcl_all_struct_invs state\<^sub>W_of_def twl_cp_propagate_or_conflict
      twl_struct_invs_def)
  subgoal
    by (metis pcdcl_all_struct_invs_def pcdcl_core_stgy.intros(1) pcdcl_core_stgy.intros(2)
      pcdcl_core_stgy_no_smaller_propa state\<^sub>W_of_def twl_cp_propagate_or_conflict twl_struct_invs_def)
  subgoal by (rule twl_cp_twl_st_exception_inv; auto simp add: twl_struct_invs_def; fail)
  subgoal by (use twl_struct_invs_def twl_cp_no_duplicate_queued in blast)
  subgoal by (rule twl_cp_distinct_queued; auto simp add: twl_struct_invs_def)
  subgoal by (rule twl_cp_confl_cands_enqueued; auto simp add: twl_struct_invs_def; fail)
  subgoal by (rule twl_cp_propa_cands_enqueued; auto simp add: twl_struct_invs_def; fail)
  subgoal by (simp add: cdcl_twl_cp_conflict; fail)
  subgoal by (simp add: twl_struct_invs_def twl_cp_clauses_to_update; fail)
  subgoal by (simp add: twl_cp_past_invs twl_struct_invs_def; fail)
  done

(* lemma twl_struct_invs_no_false_clause:
 *   assumes \<open>twl_struct_invs S\<close>
 *   shows \<open>cdcl\<^sub>W_restart_mset.no_false_clause (state\<^sub>W_of S)\<close>
 * proof -
 *   obtain M N U D NE UE NS US N0 U0 WS Q where
 *     S: \<open>S = (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q)\<close>
 *     by (cases S) auto
 *   have wf: \<open>\<And>C. C \<in># N + U \<Longrightarrow> struct_wf_twl_cls C\<close> and entailed: \<open>entailed_clss_inv (pstate\<^sub>W_of S)\<close> and
 *     subs: \<open>psubsumed_invs (pstate\<^sub>W_of S)\<close> and
 *     clss0: \<open>clauses0_inv (pstate\<^sub>W_of S)\<close>
 *     using assms unfolding twl_struct_invs_def twl_st_inv.simps S pcdcl_all_struct_invs_def by fast+
 *   have NUE: \<open>{#} \<notin># NE + UE\<close>
 *     using entailed unfolding S entailed_clss_inv.simps
 *     by (auto simp del: set_mset_union simp: entailed_clss_inv.simps)
 *   moreover have H: \<open>clause C = {#} \<Longrightarrow> C \<in># N + U \<Longrightarrow> False\<close> for C
 *     using wf[of C] by (cases C) (auto simp del: set_mset_union)
 *   moreover have H': \<open>C \<in># N0 + U0 \<Longrightarrow> D = Some {#}\<close> for C
 *     using clss0 by (auto simp: S clauses0_inv_def)
 *   moreover have \<open>C \<in># NS + US \<Longrightarrow> C \<noteq> {#} \<or> D = Some {#}\<close> for C
 *     using H H' NUE subs by (auto simp: S psubsumed_invs_def dest!: multi_member_split) auto
 *   ultimately show ?thesis
 *     apply (auto simp: S clauses_def cdcl\<^sub>W_restart_mset.no_false_clause_def
 *       dest: multi_member_split)
 * thm  cdcl\<^sub>W_restart_mset.no_false_clause_def
 * qed *)

lemma (in conflict_driven_clause_learning\<^sub>W) cdcl\<^sub>W_restart_conflict_non_zero_unless_level_0:
  assumes
    \<open>cdcl\<^sub>W_restart S T\<close>
    \<open>cdcl\<^sub>W_stgy_invariant S\<close> and
    \<open>conflict_non_zero_unless_level_0 S\<close>
  shows \<open>conflict_non_zero_unless_level_0 T\<close>
proof -
  have [dest]: \<open>local.backtrack_lvl S = 0 \<Longrightarrow> count_decided (tl (trail S)) = 0\<close>
    by (cases \<open>trail S\<close>)
      (auto  split: if_splits simp del: state_simp)
  have \<open>{#} \<in># clauses S \<Longrightarrow> count_decided (trail S) = 0\<close>
    using assms(2)
    by (fastforce simp: cdcl\<^sub>W_stgy_invariant_def no_smaller_confl_def count_decided_0_iff is_decided_def
      dest!: multi_member_split split_list)
  with assms show ?thesis
    by (induction rule: cdcl\<^sub>W_restart_all_induct)
     (auto simp add: conflict_non_zero_unless_level_0_def state_prop
      no_false_clause_def propagate.simps remove1_mset_empty_iff
      conflict.simps cdcl\<^sub>W_o.simps
      decide.simps resolve.simps
      backtrack.simps cdcl\<^sub>W_bj.simps
      skip.simps)
qed

lemma cdcl_twl_cp_twl_stgy_invs:
  \<open>cdcl_twl_cp S T \<Longrightarrow> twl_struct_invs S \<Longrightarrow> twl_stgy_invs S \<Longrightarrow> twl_stgy_invs T\<close>
  using pcdcl_stgy_stgy_invariant[of \<open>pstate\<^sub>W_of S\<close> \<open>pstate\<^sub>W_of S\<close>]
  unfolding twl_stgy_invs_def
  apply (intro conjI impI)
  apply (metis cdcl_twl_cp_cdcl\<^sub>W_stgy pcdcl_tcore_stgy_pcdcl_stgy' rtranclp_pcdcl_stgy_stgy_invariant state\<^sub>W_of_def twl_struct_invs_def)
  by (metis cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart_conflict_non_zero_unless_level_0
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_cdcl\<^sub>W_restart pcdcl_all_struct_invs_def pcdcl_core_stgy.simps
    pcdcl_core_stgy_is_cdcl_stgy state\<^sub>W_of_def twl_cp_propagate_or_conflict twl_struct_invs_def)

subsubsection \<open>The other rules\<close>

lemma
  assumes
    cdcl: \<open>cdcl_twl_o S T\<close> and
    twl: \<open>twl_struct_invs S\<close>
  shows
    cdcl_twl_o_twl_st_inv: \<open>twl_st_inv T\<close> and
    cdcl_twl_o_past_invs: \<open>past_invs T\<close>
  using cdcl twl
proof (induction rule: cdcl_twl_o.induct)
  case (decide M K N NE NS N0 U UE US U0) note undef = this(1) and atm = this(2)

  case 1 note invs = this(1)
  let ?S = \<open>(M, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#})\<close>
  have inv: \<open>twl_st_inv ?S\<close> and excep: \<open>twl_st_exception_inv ?S\<close> and past: \<open>past_invs ?S\<close> and
    w_q: \<open>clauses_to_update_inv ?S\<close>
    using invs unfolding twl_struct_invs_def by blast+
  have n_d: \<open>no_dup M\<close>
    using invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def pcdcl_all_struct_invs_def
   by (simp add: cdcl\<^sub>W_restart_mset_state state\<^sub>W_of_def)
  have n_d': \<open>no_dup (Decided K # M)\<close>
    using defined_lit_map n_d undef by auto
  have propa_cands: \<open>propa_cands_enqueued ?S\<close> and
    confl_cands: \<open>confl_cands_enqueued ?S\<close>
    using invs unfolding twl_struct_invs_def by blast+

  show ?case
    unfolding twl_st_inv.simps Ball_def
  proof (intro conjI allI impI)
    fix C :: \<open>'a twl_cls\<close>
    assume C: \<open>C \<in># N + U\<close>
    show struct: \<open>struct_wf_twl_cls C\<close>
      using inv C by (auto simp: twl_st_inv.simps)

    have watched: \<open>watched_literals_false_of_max_level M C\<close> and
      lazy: \<open>twl_lazy_update M C\<close>
      using C inv by (auto simp: twl_st_inv.simps)

    obtain W UW where C_W: \<open>C = TWL_Clause W UW\<close>
      by (cases C)

    have H: False if
      W: \<open>L \<in># W\<close> and
      uL: \<open>- L \<in> lits_of_l (Decided K # M)\<close> and
      L': \<open>\<not>has_blit (Decided K # M) (W + UW) L\<close> and
      False: \<open>-L \<noteq> K\<close> for L
    proof -
      have H: \<open>- L \<in> lits_of_l M \<Longrightarrow> \<not> has_blit M (W + UW) L \<Longrightarrow> get_level M L = count_decided M \<close>
        using watched W unfolding C_W
        by auto
      obtain L' where W': \<open>W = {#L, L'#}\<close>
        using struct W size_2_iff[of W] unfolding C_W
        by (auto simp: add_mset_eq_single add_mset_eq_add_mset dest!: multi_member_split)
      have no_has_blit: \<open>\<not>has_blit M (W + UW) L\<close>
        using no_has_blit_decide'[of K M C] L' n_d C_W W undef by auto
      then have \<open>\<forall>K \<in># UW. -K \<in> lits_of_l M\<close>
        using uL L' False excep C W C_W L' W n_d undef
        by (auto simp: twl_exception_inv.simps all_conj_distrib
            dest!: multi_member_split[of _ N])
      then have M_CNot_C: \<open>M \<Turnstile>as CNot (remove1_mset L' (clause C))\<close>
        using uL False W' unfolding true_annots_true_cls_def_iff_negation_in_model
        by (auto simp: C_W W)
      moreover have L'_C: \<open>L' \<in># clause C\<close>
        unfolding C_W W' by auto
      ultimately have \<open>defined_lit M L'\<close>
        using propa_cands C by auto

      then have \<open>-L' \<in> lits_of_l M\<close>
        using L' W' False uL C_W L'_C H no_has_blit (* TODO Proof *)
        apply (auto simp: Decided_Propagated_in_iff_in_lits_of_l)
        by (metis C_W L'_C no_has_blit clause.simps
            count_decided_ge_get_level has_blit_def is_blit_def)
      then have \<open>M \<Turnstile>as CNot (clause C)\<close>
        using M_CNot_C W' unfolding true_annots_true_cls_def_iff_negation_in_model
        by (auto simp: C_W)
      then show False
        using confl_cands C by auto
    qed

    show \<open>watched_literals_false_of_max_level (Decided K # M) C\<close>
      unfolding C_W watched_literals_false_of_max_level.simps
    proof (intro allI impI)
      fix L
      assume
        W: \<open>L \<in># W\<close> and
        uL: \<open>- L \<in> lits_of_l (Decided K # M)\<close> and
        L': \<open>\<not>has_blit (Decided K # M) (W + UW) L\<close>
      then have \<open>-L = K\<close>
        using H[OF W uL L'] by fast
      then show \<open>get_level (Decided K # M) L = count_decided (Decided K # M)\<close>
        by auto
    qed

    {
      assume exception: \<open>\<not> twl_is_an_exception C {#-K#} {#}\<close>
      have \<open>twl_lazy_update M C\<close>
        using C inv by (auto simp: twl_st_inv.simps)
      have lev_le_Suc: \<open>get_level M Ka \<le> Suc (count_decided M)\<close> for Ka
        using count_decided_ge_get_level le_Suc_eq by blast
      show \<open>twl_lazy_update (Decided K # M) C\<close>
        unfolding C_W twl_lazy_update.simps Ball_def
      proof (intro allI impI)
        fix L K' :: \<open>'a literal\<close>
        assume
          W: \<open>L \<in># W\<close> and
          uL: \<open>- L \<in> lits_of_l (Decided K # M)\<close> and
          L': \<open>\<not>has_blit (Decided K # M) (W + UW) L\<close> and
          K': \<open>K' \<in># UW\<close>
        then have \<open>-L = K\<close>
          using H[OF W uL L'] by fast
        then have False
          using exception W
          by (auto simp: C_W twl_is_an_exception_def)
        then show \<open>get_level (Decided K # M) K' \<le> get_level (Decided K # M) L \<and>
             -K'  \<in> lits_of_l (Decided K # M)\<close>
          by fast
      qed
    }
  qed

  case 2
  show ?case
    unfolding past_invs.simps Ball_def
  proof (intro allI impI conjI)
    fix M1 M2 K' C
    assume \<open>Decided K # M = M2 @ Decided K' # M1\<close> and C: \<open>C \<in># N + U\<close>
    then have M: \<open>M = tl M2 @ Decided K' # M1 \<or> M = M1\<close>
      by (cases M2) auto
    have IH: \<open>\<forall>M1 M2 K. M = M2 @ Decided K # M1 \<longrightarrow>
        twl_lazy_update M1 C \<and> watched_literals_false_of_max_level M1 C \<and>
        twl_exception_inv (M1, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#}) C\<close>
      using past C unfolding past_invs.simps by blast

    have \<open>twl_lazy_update M C\<close>
      using inv C unfolding twl_st_inv.simps by auto
    then show \<open>twl_lazy_update M1 C\<close>
      using IH M by blast

    have \<open>watched_literals_false_of_max_level M C\<close>
      using inv C unfolding twl_st_inv.simps by auto
    then show \<open>watched_literals_false_of_max_level M1 C\<close>
      using IH M by blast

    have \<open>twl_exception_inv (M, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#}) C\<close>
      using excep inv C unfolding twl_st_inv.simps by auto
    then show \<open>twl_exception_inv (M1, N, U, None, NE, UE, NS, US,N0, U0,  {#}, {#}) C\<close>
      using IH M by blast
  next
    fix M1 M2 :: \<open>('a, 'a clause) ann_lits\<close> and K'
    assume \<open>Decided K # M = M2 @ Decided K' # M1\<close>
    then have M: \<open>M = tl M2 @ Decided K' # M1 \<or> M = M1\<close>
      by (cases M2) auto
    then show \<open>confl_cands_enqueued (M1, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#})\<close> and
      \<open>propa_cands_enqueued (M1, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#})\<close> and
      \<open>clauses_to_update_inv (M1, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#})\<close>
      using confl_cands past propa_cands w_q unfolding past_invs.simps by blast+
  qed

next
  case (skip L D C' M N U NE UE NS US)
  case 1
  then show ?case
    by (auto simp: twl_st_inv.simps twl_struct_invs_def)
  case 2
  then show ?case
    by (auto simp: past_invs.simps twl_struct_invs_def)
next
  case (resolve L D C M N U NE UE NS US)
  case 1
  then show ?case
    by (auto simp: twl_st_inv.simps twl_struct_invs_def)
  case 2
  then show ?case
    by (auto simp: past_invs.simps twl_struct_invs_def)
next
  case (backtrack_unit_clause K' D K M1 M2 M D' i N U NE UE NS US N0 U0) note decomp = this(2) and
    lev = this(3-5)

  case 1 note invs = this(1)
  let ?S = \<open>(M, N, U, Some D, NE, UE, NS, US, N0, U0, {#}, {#})\<close>
  let ?T = \<open>(Propagated K' {#K'#} # M1, N, U, None, NE, add_mset {#K'#} UE, NS, US, N0, U0, {#}, {#- K'#})\<close>
  let ?M1 = \<open>Propagated K' {#K'#} # M1\<close>
  have bt_twl: \<open>cdcl_twl_o ?S ?T\<close>
    using cdcl_twl_o.backtrack_unit_clause[OF backtrack_unit_clause.hyps] .
  then have \<open>pcdcl_tcore (pstate\<^sub>W_of ?S)  (pstate\<^sub>W_of ?T)\<close>
    by (rule cdcl_twl_o_cdcl\<^sub>W_o) (use invs in \<open>simp_all add: twl_struct_invs_def pcdcl_all_struct_invs_def\<close>)
  from pcdcl_tcore_pcdcl_all_struct_invs[OF this]
  have struct_inv_T: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of ?T)\<close>
    using invs unfolding twl_struct_invs_def pcdcl_all_struct_invs_def by auto
  have inv: \<open>twl_st_inv ?S\<close> and w_q: \<open>clauses_to_update_inv ?S\<close> and past: \<open>past_invs ?S\<close>
    using invs unfolding twl_struct_invs_def by blast+
  have n_d: \<open>no_dup M\<close>
    using invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def pcdcl_all_struct_invs_def
    by (simp add: cdcl\<^sub>W_restart_mset_state)
  have n_d': \<open>no_dup ?M1\<close>
    using struct_inv_T unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (simp add: trail.simps)

  have propa_cands: \<open>propa_cands_enqueued ?S\<close> and
    confl_cands: \<open>confl_cands_enqueued ?S\<close>
    using invs unfolding twl_struct_invs_def by blast+

  have excep: \<open>twl_st_exception_inv ?S\<close>
    using invs unfolding twl_struct_invs_def by fast

  obtain M3 where M: \<open>M = M3 @ M2 @ Decided K # M1\<close>
    using decomp by blast
  define M2' where \<open>M2' = M3 @ M2\<close>
  have M': \<open>M = M2' @ Decided K # M1\<close>
    unfolding M M2'_def by simp

  have propa_cands_M1:
    \<open>propa_cands_enqueued (M1, N, U, None, NE, add_mset {#K'#} UE, NS, US, N0, U0, {#}, {#- K'#})\<close>
    unfolding propa_cands_enqueued.simps
  proof (intro allI impI)
    fix L C
    assume
      C: \<open>C \<in># N + U\<close> and
      L: \<open>L \<in># clause C\<close> and
      M1_CNot: \<open>M1 \<Turnstile>as CNot (remove1_mset L (clause C))\<close> and
      undef: \<open>undefined_lit M1 L\<close>
    define D where \<open>D = remove1_mset L (clause C)\<close>
    have \<open>add_mset L D \<in># clause `# (N + U)\<close> and \<open>M1 \<Turnstile>as CNot D\<close>
      using C L M1_CNot unfolding D_def by auto
    moreover have \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state\<^sub>W_of ?S)\<close>
      using invs unfolding twl_struct_invs_def by blast
    ultimately have False
      using undef M'
      by (auto 7 7 simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def trail.simps clauses_def)
    then show \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># {#- K'#}) \<or> (\<exists>L. (L, C) \<in># {#})\<close>
      by fast
  qed

  have excep_M1: \<open>twl_st_exception_inv (M1, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#})\<close>
    using past unfolding past_invs.simps M' by auto

  show ?case
    unfolding twl_st_inv.simps Ball_def
  proof (intro conjI allI impI)
    fix C :: \<open>'a twl_cls\<close>
    assume C: \<open>C \<in># N + U\<close>
    show struct: \<open>struct_wf_twl_cls C\<close>
      using inv C by (auto simp: twl_st_inv.simps)

    obtain CW CUW where C_W: \<open>C = TWL_Clause CW CUW\<close>
        by (cases C)

    {
      assume exception: \<open>\<not> twl_is_an_exception C {#-K'#} {#}\<close>
      have
        lazy: \<open>twl_lazy_update M1 C\<close> and
        watched_max: \<open>watched_literals_false_of_max_level M1 C\<close>
        using C past M by (auto simp: past_invs.simps)
      have lev_le_Suc: \<open>get_level M Ka \<le> Suc (count_decided M)\<close> for Ka
        using count_decided_ge_get_level le_Suc_eq by blast
      have Lev_M1: \<open>get_level (?M1) K \<le> count_decided M1\<close> for K
        by (auto simp: count_decided_ge_get_level get_level_cons_if)

      show \<open>twl_lazy_update ?M1 C\<close>
      proof -
        show ?thesis (* TODO Proof *)
          using (* lazy *) Lev_M1
          using twl C exception twl n_d' (* unw *) watched_max
          unfolding C_W
          apply (auto simp: (* get_level_cons_if *) count_decided_ge_get_level
              twl_is_an_exception_add_mset_to_queue atm_of_eq_atm_of
              dest!: no_has_blit_propagate' no_has_blit_propagate)
             apply (metis count_decided_ge_get_level get_level_skip_beginning get_level_take_beginning)
          using lazy unfolding C_W twl_lazy_update.simps apply blast
           apply (metis count_decided_ge_get_level get_level_skip_beginning get_level_take_beginning)
          using lazy unfolding C_W twl_lazy_update.simps apply blast
          done
      qed

    }

    have \<open>watched_literals_false_of_max_level M1 C\<close>
      using past C unfolding M' past_invs.simps by blast
    then show \<open>watched_literals_false_of_max_level ?M1 C\<close>
      using has_blit_Cons n_d'
      by (auto simp: C_W get_level_cons_if)
  qed
  case 2
  show ?case
    unfolding past_invs.simps Ball_def
  proof (intro allI impI conjI)
    fix M1'' M2'' K'' C
    assume \<open>?M1 = M2'' @ Decided K'' # M1''\<close> and C: \<open>C \<in># N + U\<close>
    then have M1: \<open>M1 = tl M2'' @ Decided K'' # M1''\<close>
      by (cases M2'') auto
    have \<open>twl_lazy_update M1'' C\<close>\<open>watched_literals_false_of_max_level M1'' C\<close>
      using past C unfolding past_invs.simps M M1 twl_exception_inv.simps by auto
    moreover {
      have \<open>twl_exception_inv (M1'', N, U, None, NE, UE, NS, US, N0, U0, {#}, {#}) C\<close>
        using past C unfolding past_invs.simps M M1 by auto
      then have \<open>twl_exception_inv (M1'', N, U, None, NE, add_mset {#K'#} UE, NS, US, N0, U0, {#}, {#}) C\<close>
      using C unfolding twl_exception_inv.simps by auto }
    ultimately show \<open>twl_lazy_update M1'' C\<close>\<open>watched_literals_false_of_max_level M1'' C\<close>
      \<open>twl_exception_inv (M1'', N, U, None, NE, add_mset {#K'#} UE, NS, US, N0, U0, {#}, {#}) C\<close>
      by fast+
  next
    fix M1'' M2'' K''
    assume \<open>?M1 = M2'' @ Decided K'' # M1''\<close>
    then have M1: \<open>M1 = tl M2'' @ Decided K'' # M1''\<close>
      by (cases M2'') auto
    then show
      \<open>confl_cands_enqueued (M1'', N, U, None, NE, add_mset {#K'#} UE, NS, US, N0, U0, {#}, {#})\<close> and
      \<open>propa_cands_enqueued (M1'', N, U, None, NE, add_mset {#K'#} UE, NS, US, N0, U0, {#}, {#})\<close> and
      \<open>clauses_to_update_inv (M1'', N, U, None, NE, add_mset {#K'#} UE, NS, US, N0, U0, {#}, {#})\<close>
      using past by (auto simp add: past_invs.simps M)
  qed
next
  case (backtrack_nonunit_clause K' D K M1 M2 M D' i N U NE UE NS US N0 U0 K'') note K'_D = this(1) and
    decomp = this(2) and lev_K' = this(3) and i = this(5) and lev_K = this(6) and K'_D' = this(10)
    and K'' = this(11) and lev_K'' = this(12)
  case 1 note invs = this(1)
  let ?S = \<open>(M, N, U, Some D, NE, UE, NS, US, N0, U0, {#}, {#})\<close>
  let ?M1 = \<open>Propagated K' D' # M1\<close>
  let ?T = \<open>(?M1, N, add_mset (TWL_Clause {#K', K''#} (D' - {#K', K''#})) U, None, NE, UE, NS, US,
   N0, U0, {#}, {#- K'#})\<close>
  let ?D = \<open>TWL_Clause {#K', K''#} (D' - {#K', K''#})\<close>
  have bt_twl: \<open>cdcl_twl_o ?S ?T\<close>
    using cdcl_twl_o.backtrack_nonunit_clause[OF backtrack_nonunit_clause.hyps] .
  then have \<open>pcdcl_tcore (pstate\<^sub>W_of ?S) (pstate\<^sub>W_of ?T)\<close>
    by (rule cdcl_twl_o_cdcl\<^sub>W_o) (use invs in \<open>simp_all add: twl_struct_invs_def
      pcdcl_all_struct_invs_def\<close>)
  from pcdcl_tcore_pcdcl_all_struct_invs[OF this]
  have struct_inv_T: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of ?T)\<close>
    using invs unfolding twl_struct_invs_def pcdcl_all_struct_invs_def by auto
  have inv: \<open>twl_st_inv ?S\<close> and
    w_q: \<open>clauses_to_update_inv ?S\<close> and
    past: \<open>past_invs ?S\<close>
    using invs unfolding twl_struct_invs_def by blast+
  have n_d: \<open>no_dup M\<close>
    using invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def pcdcl_all_struct_invs_def
   by (simp add: cdcl\<^sub>W_restart_mset_state)
  have n_d': \<open>no_dup ?M1\<close>
    using struct_inv_T unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (simp add: trail.simps)

  have propa_cands: \<open>propa_cands_enqueued ?S\<close> and
    confl_cands: \<open>confl_cands_enqueued ?S\<close>
    using invs unfolding twl_struct_invs_def by blast+
  obtain M3 where M: \<open>M = M3 @ M2 @ Decided K # M1\<close>
    using decomp by blast
  define M2' where \<open>M2' = M3 @ M2\<close>
  have M': \<open>M = M2' @ Decided K # M1\<close>
    unfolding M M2'_def by simp
  have struct_inv_S: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of ?S)\<close>
    using invs unfolding twl_struct_invs_def pcdcl_all_struct_invs_def by auto
  then have \<open>distinct_mset D\<close>
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
    by (auto simp: conflicting.simps)

  have \<open>undefined_lit (M3 @ M2) K\<close>
    using n_d unfolding M by auto
  then have count_M1: \<open>count_decided M1 = i\<close>
    using lev_K unfolding M by (auto simp: image_Un)
  then have K''_ne_K: \<open>K' \<noteq> K''\<close>
    using lev_K lev_K' lev_K'' count_decided_ge_get_level[of M K''] unfolding M by auto
  then have D:
    \<open>add_mset K' (add_mset K'' (D' - {#K', K''#})) = D'\<close>
    \<open>add_mset K'' (add_mset K' (D' - {#K', K''#})) = D'\<close>
    using K'' K'_D' multi_member_split by fastforce+
  have propa_cands_M1: \<open>propa_cands_enqueued (M1, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#- K''#})\<close>
    unfolding propa_cands_enqueued.simps
  proof (intro allI impI)
    fix L C
    assume
      C: \<open>C \<in># N + U\<close> and
      L: \<open>L \<in># clause C\<close> and
      M1_CNot: \<open>M1 \<Turnstile>as CNot (remove1_mset L (clause C))\<close> and
      undef: \<open>undefined_lit M1 L\<close>
    define D where \<open>D = remove1_mset L (clause C)\<close>
    have \<open>add_mset L D \<in># clause `# (N + U)\<close> and \<open>M1 \<Turnstile>as CNot D\<close>
      using C L M1_CNot unfolding D_def by auto
    moreover have \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state\<^sub>W_of ?S)\<close>
      using invs unfolding twl_struct_invs_def by blast
    ultimately have False
      using undef M'
      by (auto 7 7 simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def trail.simps clauses_def)
    then show \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># {#- K''#}) \<or> (\<exists>L. (L, C) \<in># {#})\<close>
      by fast
  qed
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of ?T)\<close>
    using struct_inv_T unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def twl_struct_invs_def
    by (auto simp: conflicting.simps)
  then have M1_CNot_D: \<open>M1 \<Turnstile>as CNot (remove1_mset K' D')\<close>
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    by (auto simp: conflicting.simps trail.simps)
  then have uK''_M1: \<open>-K'' \<in> lits_of_l M1\<close>
    using K'' K''_ne_K unfolding true_annots_true_cls_def_iff_negation_in_model
    by (metis in_remove1_mset_neq)
  then have \<open>undefined_lit (M3 @ M2 @ Decided K # []) K''\<close>
    using n_d M by (auto simp: atm_of_eq_atm_of dest: in_lits_of_l_defined_litD defined_lit_no_dupD)
  then have lev_M1_K'': \<open>get_level M1 K'' = count_decided M1\<close>
    using lev_K'' count_M1 unfolding M by (auto simp: image_Un)

  have excep_M1: \<open>twl_st_exception_inv (M1, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#})\<close>
    using past unfolding past_invs.simps M' by auto

  show ?case
    unfolding twl_st_inv.simps Ball_def
  proof (intro conjI allI impI)
    fix C :: \<open>'a twl_cls\<close>
    assume C: \<open>C \<in># N + add_mset ?D U\<close>
    have \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of ?T)\<close>
      using struct_inv_T unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by blast
    then have \<open>distinct_mset D'\<close>
      unfolding cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
      by (auto simp: cdcl\<^sub>W_restart_mset_state)
    then show struct: \<open>struct_wf_twl_cls C\<close>
      using inv C by (auto simp: twl_st_inv.simps D)

    obtain CW CUW where C_W: \<open>C = TWL_Clause CW CUW\<close>
      by (cases C)
    have
      lazy: \<open>twl_lazy_update M1 C\<close> and
      watched_max: \<open>watched_literals_false_of_max_level M1 C\<close> if \<open>C \<noteq> ?D\<close>
      using C past M' that by (auto simp: past_invs.simps)
    from M1_CNot_D have in_D_M1: \<open>L \<in># remove1_mset K' D' \<Longrightarrow> - L \<in> lits_of_l M1\<close> for L
      by (auto simp: true_annots_true_cls_def_iff_negation_in_model)
    then have in_K_D_M1: \<open>L \<in># D' - {#K', K''#} \<Longrightarrow> - L \<in> lits_of_l M1\<close> for L
      by (metis K'_D' add_mset_diff_bothsides add_mset_remove_trivial in_diffD mset_add)
    have \<open>- K' \<notin> lits_of_l M1\<close>
      using n_d' by (simp add: Decided_Propagated_in_iff_in_lits_of_l)
    have def_K'': \<open>defined_lit M1 K''\<close>
      using n_d' uK''_M1
      using Decided_Propagated_in_iff_in_lits_of_l uK''_M1 by blast
    have
      lazy_D: \<open>twl_lazy_update ?M1 C\<close> if \<open>C = ?D\<close>
      using that n_d' uK''_M1 def_K''  \<open>- K' \<notin> lits_of_l M1\<close> in_K_D_M1 lev_M1_K''
      by (auto simp: add_mset_eq_add_mset count_decided_ge_get_level get_level_cons_if
          atm_of_eq_atm_of)
    have
      watched_max_D: \<open>watched_literals_false_of_max_level ?M1 C\<close> if \<open>C = ?D\<close>
      using that in_D_M1 by (auto simp add: add_mset_eq_add_mset lev_M1_K'' get_level_cons_if
          dest: in_K_D_M1)

    {
      assume excep: \<open>\<not> twl_is_an_exception C {#-K'#} {#}\<close>

      have lev_le_Suc: \<open>get_level M Ka \<le> Suc (count_decided M)\<close> for Ka
        using count_decided_ge_get_level le_Suc_eq by blast
      have Lev_M1: \<open>get_level (?M1) K \<le> count_decided M1\<close> for K
        by (auto simp: count_decided_ge_get_level get_level_cons_if)

      have \<open>twl_lazy_update ?M1 C\<close> if \<open>C \<noteq> ?D\<close>
      proof -
        have 1: \<open>get_level (Propagated K' D' # M1) K \<le> get_level (Propagated K' D' # M1) L\<close>
          if
            \<open>\<forall>L. L \<in># CW \<longrightarrow> - L \<in> lits_of_l M1 \<longrightarrow> \<not> has_blit M1 (CW + CUW) L \<longrightarrow>
                get_level M1 L = count_decided M1\<close> and
            \<open>L \<in># CW\<close> and
            \<open>- L \<in> lits_of_l M1\<close> and
            \<open>K \<in># CUW\<close> and
            \<open>\<not> has_blit M1 (CW + CUW) L\<close>
          for L :: \<open>'a literal\<close> and K :: \<open>'a literal\<close>
          using that Lev_M1
          by (metis count_decided_ge_get_level get_level_skip_beginning get_level_take_beginning)
        have 2: False
          if
            \<open>L \<in># CW\<close> and
            \<open>TWL_Clause CW CUW \<in># N\<close> and
            \<open>CW \<noteq> {#K', K''#}\<close> and
            \<open>- L \<in> lits_of_l M1\<close> and
            \<open>K \<in># CUW\<close> and
            \<open>- K \<notin> lits_of_l M1\<close> and
            \<open>\<not> has_blit M1 (CW + CUW) L\<close>
          for L :: \<open>'a literal\<close> and K :: \<open>'a literal\<close>
          using lazy that unfolding C_W twl_lazy_update.simps by blast

        show ?thesis (* TODO Proof *)
          using Lev_M1 C_W that
          using twl C excep twl n_d' (* unw *) watched_max 1
          unfolding C_W
          apply (auto simp: (* get_level_cons_if *) count_decided_ge_get_level
              twl_is_an_exception_add_mset_to_queue atm_of_eq_atm_of that
              dest!: no_has_blit_propagate' no_has_blit_propagate dest: 2)
          using lazy unfolding C_W twl_lazy_update.simps apply blast
          using lazy unfolding C_W twl_lazy_update.simps apply blast
          using lazy unfolding C_W twl_lazy_update.simps apply blast
          done
      qed
      then show \<open>twl_lazy_update ?M1 C\<close>
        using lazy_D by blast
    }

    have \<open>watched_literals_false_of_max_level M1 C\<close> if \<open>C \<noteq> ?D\<close>
      using past C that unfolding M past_invs.simps by auto
    then have \<open>watched_literals_false_of_max_level ?M1 C\<close> if \<open>C \<noteq> ?D\<close>
      using has_blit_Cons n_d' C_W that by (auto simp: get_level_cons_if)
    then show \<open>watched_literals_false_of_max_level ?M1 C\<close>
      using watched_max_D by blast
  qed

  case 2
  show ?case
    unfolding past_invs.simps Ball_def
  proof (intro allI impI conjI)
    fix M1'' M2'' K''' C
    assume M1: \<open>?M1 = M2'' @ Decided K''' # M1''\<close> and C: \<open>C \<in># N + add_mset ?D U\<close>
    then have M1: \<open>M1 = tl M2'' @ Decided K''' # M1''\<close>
      by (cases M2'') auto
    have \<open>twl_lazy_update M1'' C\<close>\<open>watched_literals_false_of_max_level M1'' C\<close>
      if \<open>C \<noteq> ?D\<close>
      using past C that unfolding past_invs.simps M M1 twl_exception_inv.simps by auto
    moreover {
      have \<open>twl_exception_inv (M1'', N, U, None, NE, UE, NS, US, N0, U0, {#}, {#}) C\<close> if \<open>C \<noteq> ?D\<close>
        using past C unfolding past_invs.simps M M1 by (auto simp: that)
      then have \<open>twl_exception_inv (M1'', N, add_mset ?D U, None, NE, UE, NS, US, N0, U0, {#}, {#}) C\<close>
      if \<open>C \<noteq> ?D\<close>
      using C unfolding twl_exception_inv.simps by (auto simp: that) }
    moreover {
      have n_d_M1: \<open>no_dup ?M1\<close>
        using struct_inv_T unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (simp add: cdcl\<^sub>W_restart_mset_state)
      then have \<open>undefined_lit M1'' K'\<close>
        unfolding M1 by auto
      moreover {
        have \<open>- K'' \<notin> lits_of_l M1''\<close>
        proof (rule ccontr)
          assume \<open>\<not> - K'' \<notin> lits_of_l M1''\<close>
          then have \<open>undefined_lit (tl M2'' @ Decided K''' # []) K''\<close>
            (* TODO tune proof *)
            using n_d_M1 unfolding M1 by (auto simp: atm_lit_of_set_lits_of_l
                atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
                defined_lit_map atm_of_eq_atm_of image_Un
                dest: no_dup_uminus_append_in_atm_notin)
          then show False
            using lev_M1_K''  count_decided_ge_get_level[of M1'' K''] unfolding M1
            by (auto simp: image_Un Int_Un_distrib)
        qed }
      ultimately have \<open>twl_lazy_update M1'' ?D\<close> and
         \<open>watched_literals_false_of_max_level M1'' ?D\<close> and
         \<open>twl_exception_inv (M1'', N, add_mset (TWL_Clause {#K', K''#} (D' - {#K', K''#})) U, None,
           NE, UE, NS, US, N0, U0, {#}, {#}) ?D\<close>
        by (auto simp: add_mset_eq_add_mset twl_exception_inv.simps get_level_cons_if
            Decided_Propagated_in_iff_in_lits_of_l) }
    ultimately show \<open>twl_lazy_update M1'' C\<close>
      \<open>watched_literals_false_of_max_level M1'' C\<close>
      \<open>twl_exception_inv (M1'', N, add_mset (TWL_Clause {#K', K''#} (D' - {#K', K''#})) U, None,
         NE, UE, NS, US, N0, U0, {#}, {#}) C\<close>
      by blast+
  next
    fix M1'' M2'' K'''
    assume M1: \<open>?M1 = M2'' @ Decided K''' # M1''\<close>
    then have M1: \<open>M1 = tl M2'' @ Decided K''' # M1''\<close>
      by (cases M2'') auto
    then have confl_cands: \<open>confl_cands_enqueued (M1'', N, U, None, NE, UE, NS, US, N0, U0, {#}, {#})\<close> and
      propa_cands: \<open>propa_cands_enqueued (M1'', N, U, None, NE, UE, NS, US, N0, U0, {#}, {#})\<close> and
      w_q: \<open>clauses_to_update_inv (M1'', N, U, None, NE, UE, NS, US, N0, U0, {#}, {#})\<close>
      using past by (auto simp add: M M1 past_invs.simps simp del: propa_cands_enqueued.simps
          confl_cands_enqueued.simps)
    have uK''_M1'': \<open>- K'' \<notin> lits_of_l M1''\<close>
    proof (rule ccontr)
      assume K''_M1'': \<open>\<not> ?thesis\<close>
      have \<open>undefined_lit (tl M2'' @ Decided K''' # []) (-K'')\<close>
        apply (rule no_dup_append_in_atm_notin)
         prefer 2 using K''_M1'' apply (simp; fail)
        by (use n_d in \<open>auto simp: M M1 no_dup_def; fail\<close>)[]
      then show False
        using lev_M1_K'' count_decided_ge_get_level[of M1'' K''] unfolding M M1
        by (auto simp: image_Un)
    qed
    have uK'_M1'': \<open>- K' \<notin> lits_of_l M1''\<close>
    proof (rule ccontr)
      assume K'_M1'': \<open>\<not> ?thesis\<close>
      have \<open>undefined_lit (M3 @ M2 @ Decided K # tl M2'' @ Decided K''' # []) (-K')\<close>
        apply (rule no_dup_append_in_atm_notin)
         prefer 2 using K'_M1'' apply (simp; fail)
        by (use n_d in \<open>auto simp: M M1; fail\<close>)[]
      then show False
        using lev_K' count_decided_ge_get_level[of M1'' K'] unfolding M M1
        by (auto simp: image_Un)
    qed

    have [simp]: \<open>\<not>clauses_to_update_prop {#} M1'' (L, ?D)\<close> for L
      using uK'_M1'' uK''_M1'' by (auto simp: clauses_to_update_prop.simps add_mset_eq_add_mset)
    show \<open>confl_cands_enqueued (M1'', N, add_mset ?D U, None, NE, UE, NS, US, N0, U0, {#}, {#})\<close> and
      \<open>propa_cands_enqueued (M1'', N, add_mset ?D U, None, NE, UE, NS, US, N0, U0, {#}, {#})\<close> and
      \<open>clauses_to_update_inv (M1'', N, add_mset ?D U, None, NE, UE, NS, US, N0, U0, {#}, {#})\<close>
      using confl_cands propa_cands w_q uK'_M1'' uK''_M1''
      by (fastforce simp add: twl_st_inv.simps add_mset_eq_add_mset)+
  qed
qed

lemma
  assumes
    cdcl: \<open>cdcl_twl_o S T\<close>
  shows
    cdcl_twl_o_valid: \<open>valid_enqueued T\<close> and
    cdcl_twl_o_conflict_None_queue:
      \<open>get_conflict T \<noteq> None \<Longrightarrow> clauses_to_update T = {#} \<and> literals_to_update T = {#}\<close> and
      cdcl_twl_o_no_duplicate_queued: \<open>no_duplicate_queued T\<close> and
      cdcl_twl_o_distinct_queued: \<open>distinct_queued T\<close>
  using cdcl by (induction rule: cdcl_twl_o.induct) auto

lemma cdcl_twl_o_twl_st_exception_inv:
  assumes
    cdcl: \<open>cdcl_twl_o S T\<close> and
    twl: \<open>twl_struct_invs S\<close>
  shows
    \<open>twl_st_exception_inv T\<close>
  using cdcl twl
proof (induction rule: cdcl_twl_o.induct)
  case (decide M L N NE NS N0 U UE US U0) note undef = this(1) and in_atms = this(2) and twl = this(3)
  then have excep: \<open>twl_st_exception_inv (M, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#})\<close>
    unfolding twl_struct_invs_def
    by (auto simp: twl_exception_inv.simps)
  let ?S =  \<open>(M, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#})\<close>
  have struct_inv_T: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of ?S)\<close>
    using cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_inv cdcl\<^sub>W_restart_mset.other twl
    unfolding twl_struct_invs_def pcdcl_all_struct_invs_def by auto
  have n_d: \<open>no_dup M\<close>
    using twl unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def pcdcl_all_struct_invs_def
    by (simp add: cdcl\<^sub>W_restart_mset_state)
  show ?case
    using decide.hyps n_d excep
    unfolding twl_struct_invs_def
    by (auto simp: twl_exception_inv.simps dest!: no_has_blit_decide')
next
  case (skip L D C' M N U NE UE NS US)
  then show ?case
    unfolding twl_struct_invs_def by (auto simp: twl_exception_inv.simps)
next
  case (resolve L D C M N U NE UE NS US)
  then show ?case
    unfolding twl_struct_invs_def by (auto simp: twl_exception_inv.simps)
next
  case (backtrack_unit_clause L D K M1 M2 M D' i N U NE UE NS US N0 U0) note decomp = this(2) and
    invs = this(10)
  let ?S = \<open>(M, N, U, Some D, NE, UE, NS, US, N0, U0, {#}, {#})\<close>
  let ?S' = \<open>state\<^sub>W_of S\<close>
  let ?T = \<open>(M1, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#})\<close>
  let ?T' = \<open>state\<^sub>W_of T\<close>
  let ?U = \<open>(Propagated L {#L#} # M1, N, U, None, NE, add_mset {#L#} UE, NS, US, N0, U0, {#}, {#- L#})\<close>
  let ?U' = \<open>state\<^sub>W_of ?U\<close>
  have \<open>twl_st_inv ?S\<close> and past: \<open>past_invs ?S\<close> and valid: \<open>valid_enqueued ?S\<close>
    using invs decomp unfolding twl_struct_invs_def by fast+
  then have excep: \<open>twl_exception_inv ?T C\<close> if \<open>C \<in># N + U\<close> for C
    using decomp that unfolding past_invs.simps by auto
  have struct_inv_T: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of ?S)\<close>
    using invs unfolding twl_struct_invs_def pcdcl_all_struct_invs_def by auto
  have n_d: \<open>no_dup M\<close>
    using invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def pcdcl_all_struct_invs_def
    by (simp add: cdcl\<^sub>W_restart_mset_state pcdcl_all_struct_invs_def)
  then have n_d: \<open>no_dup M1\<close>
    using decomp by (auto dest: no_dup_appendD)


  have struct_inv_U: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of ?U)\<close>
    using cdcl_twl_o_cdcl\<^sub>W_o[OF cdcl_twl_o.backtrack_unit_clause[OF backtrack_unit_clause.hyps]
       \<open>twl_st_inv ?S\<close> valid struct_inv_T] invs
     pcdcl_tcore_pcdcl_all_struct_invs[of \<open>pstate\<^sub>W_of ?S\<close> \<open>pstate\<^sub>W_of ?U\<close>]
      struct_inv_T unfolding pcdcl_all_struct_invs_def twl_struct_invs_def by auto
  then have undef: \<open>undefined_lit M1 L\<close>
    unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (simp add: cdcl\<^sub>W_restart_mset_state)

  show ?case
    using n_d excep undef
    unfolding twl_struct_invs_def
    by (auto simp: twl_exception_inv.simps dest!: no_has_blit_propagate')
next
  case (backtrack_nonunit_clause L D K M1 M2 M D' i N U NE UE NS US N0 U0 L') note decomp = this(2) and
    lev_K = this(6) and lev_L' = this(12) and invs = this(13)
  let ?S = \<open>(M, N, U, Some D, NE, UE, NS, US, N0, U0, {#}, {#})\<close>
  let ?D = \<open>TWL_Clause {#L, L'#} (D' - {#L, L'#})\<close>
  let ?T = \<open>(M1, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#})\<close>
  let ?U = \<open>(Propagated L D' # M1, N, add_mset ?D U, None, NE, UE, NS, US, N0, U0, {#}, {#- L#})\<close>
  have \<open>twl_st_inv ?S\<close> and past: \<open>past_invs ?S\<close> and valid: \<open>valid_enqueued ?S\<close>
    using invs decomp unfolding twl_struct_invs_def by fast+
  then have excep: \<open>twl_exception_inv ?T C\<close> if \<open>C \<in># N + U\<close> for C
    using decomp that unfolding past_invs.simps by auto
  have struct_inv_T: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of ?S)\<close>
    using invs unfolding twl_struct_invs_def pcdcl_all_struct_invs_def  by auto
  have n_d_M: \<open>no_dup M\<close>
    using invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def pcdcl_all_struct_invs_def
    by (simp add: cdcl\<^sub>W_restart_mset_state)
  then have n_d: \<open>no_dup M1\<close>
    using decomp by (auto dest: no_dup_appendD)

  have struct_inv_U: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of ?U)\<close>
    using cdcl_twl_o_cdcl\<^sub>W_o[OF cdcl_twl_o.backtrack_nonunit_clause[OF backtrack_nonunit_clause.hyps]
       \<open>twl_st_inv ?S\<close> valid struct_inv_T] invs
     pcdcl_tcore_pcdcl_all_struct_invs[of \<open>pstate\<^sub>W_of ?S\<close> \<open>pstate\<^sub>W_of ?U\<close>]
      struct_inv_T unfolding pcdcl_all_struct_invs_def twl_struct_invs_def by auto
  then have undef: \<open>undefined_lit M1 L\<close>
    unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (simp add: cdcl\<^sub>W_restart_mset_state)

  have n_d: \<open>no_dup (Propagated L D' # M1)\<close>
    using struct_inv_U unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by (simp add: trail.simps)
  have \<open>i = count_decided M1\<close>
    using decomp lev_K n_d_M by (auto dest!: get_all_ann_decomposition_exists_prepend
        simp: get_level_append_if get_level_cons_if
        split: if_splits)
  then have lev_L'_M1: \<open>get_level (Propagated L D' # M1) L' = count_decided M1\<close>
    using decomp lev_L' n_d_M by (auto dest!: get_all_ann_decomposition_exists_prepend
        simp: get_level_append_if get_level_cons_if
        split: if_splits)
  have \<open>- L \<notin> lits_of_l M1\<close>
    using n_d by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)
  moreover have \<open>has_blit (Propagated L D' # M1) (add_mset L (add_mset L' (D' - {#L, L'#}))) L'\<close>
    unfolding has_blit_def
    apply (rule exI[of _ L])
    using lev_L' lev_L'_M1
    by auto
  ultimately show ?case
    using n_d excep undef
    unfolding twl_struct_invs_def
    by (auto simp: twl_exception_inv.simps dest!: no_has_blit_propagate')
qed

(* TODO refactor: the two backtrack ?cases are copy-paste from each other.*)
lemma
  assumes
    cdcl: \<open>cdcl_twl_o S T\<close> and
    twl: \<open>twl_struct_invs S\<close>
  shows
    cdcl_twl_o_confl_cands_enqueued: \<open>confl_cands_enqueued T\<close> and
    cdcl_twl_o_propa_cands_enqueued: \<open>propa_cands_enqueued T\<close> and
    twl_o_clauses_to_update: \<open>clauses_to_update_inv T\<close>
  using cdcl twl
proof (induction rule: cdcl_twl_o.induct)
  case (decide M L N NE NS N0 U UE US U0)
  let ?S = \<open>(M, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#})\<close>
  let ?T = \<open>(Decided L # M, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#-L#})\<close>
  case 1
  then have confl_cand: \<open>confl_cands_enqueued ?S\<close> and
    twl_st_inv: \<open>twl_st_inv ?S\<close> and
    excep: \<open>twl_st_exception_inv ?S\<close> and
    propa_cands: \<open>propa_cands_enqueued ?S\<close> and
    confl_cands: \<open>confl_cands_enqueued ?S\<close> and
    w_q: \<open>clauses_to_update_inv ?S\<close>
    unfolding twl_struct_invs_def by fast+

  have \<open>pcdcl_tcore (pstate\<^sub>W_of ?S) (pstate\<^sub>W_of ?T)\<close>
    by (rule cdcl_twl_o_cdcl\<^sub>W_o) (use cdcl_twl_o.decide[OF decide.hyps] 1 in
        \<open>simp_all add: twl_struct_invs_def pcdcl_all_struct_invs_def\<close>)
  from pcdcl_tcore_pcdcl_all_struct_invs[OF this]
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of ?T)\<close>
    using 1 unfolding pcdcl_all_struct_invs_def twl_struct_invs_def by auto
  then have n_d: \<open>no_dup (Decided L # M)\<close>
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp: trail.simps)
  show ?case
    unfolding confl_cands_enqueued.simps Ball_def
  proof (intro allI impI)
    fix C
    assume
      C: \<open>C \<in># N + U\<close> and
      LM_C: \<open>Decided L # M \<Turnstile>as CNot (clause C)\<close>

    have struct_C: \<open>struct_wf_twl_cls C\<close>
      using twl_st_inv C unfolding twl_st_inv.simps by blast
    then have dist_C: \<open>distinct_mset (clause C)\<close>
      by (cases C) auto
    obtain W UW K K' where
      C_W: \<open>C = TWL_Clause W UW\<close> and
      W: \<open>W = {#K, K'#}\<close>
      using struct_C by (cases C) (auto simp: size_2_iff)

    have \<open>\<not>M \<Turnstile>as CNot (clause C)\<close>
      using confl_cand C by auto
    then have uL_C: \<open>-L \<in># clause C\<close> and neg_C: \<open>\<forall>K \<in># clause C. -K \<in> lits_of_l (Decided L # M)\<close>
      using LM_C unfolding true_annots_true_cls_def_iff_negation_in_model by auto
    have \<open>twl_exception_inv (M, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#}) C\<close>
      using excep C by auto
    then have H:  \<open>L \<in># watched (TWL_Clause {#K, K'#} UW) \<longrightarrow>
              - L \<in> lits_of_l M \<longrightarrow> \<not> has_blit M (clause (TWL_Clause {#K, K'#} UW)) L \<longrightarrow>
      L \<notin># {#} \<longrightarrow>
      (L, TWL_Clause {#K, K'#} UW) \<notin># {#} \<longrightarrow>
      (\<forall>K\<in>#unwatched (TWL_Clause {#K, K'#} UW).
          - K \<in> lits_of_l M)\<close> for L
      unfolding twl_exception_inv.simps C_W W by blast
    have excep: \<open>L \<in># watched (TWL_Clause {#K, K'#} UW) \<longrightarrow>
              - L \<in> lits_of_l M \<longrightarrow> \<not> has_blit M (clause (TWL_Clause {#K, K'#} UW)) L \<longrightarrow>
           (\<forall>K\<in>#unwatched (TWL_Clause {#K, K'#} UW). - K \<in> lits_of_l M)\<close> for L
      using H[of L] by simp
    have \<open>-L \<in># watched C\<close>
    proof (rule ccontr)
      assume uL_W: \<open>-L \<notin># watched C\<close>
      then have uL_UW: \<open>-L \<in># UW\<close>
        using uL_C unfolding C_W by auto
      have \<open>K \<noteq> -L \<or> K' \<noteq> -L\<close>
        using dist_C C_W W by auto
      moreover have \<open>K \<notin> lits_of_l M\<close> and \<open>K' \<notin> lits_of_l M\<close> and L_M: \<open>L \<notin> lits_of_l M\<close>
        using neg_C uL_W n_d unfolding C_W W by (auto simp: lits_of_def uminus_lit_swap
            no_dup_cannot_not_lit_and_uminus Decided_Propagated_in_iff_in_lits_of_l)
      ultimately have disj: \<open>(-K \<in> lits_of_l M \<and> K' \<notin> lits_of_l M) \<or>
         (-K' \<in> lits_of_l M \<and> K \<notin> lits_of_l M)\<close>
        using neg_C by (auto simp: C_W W)
      have \<open>\<not>has_blit M (clause C) K\<close>
        using \<open>K \<notin> lits_of_l M\<close>  \<open>K' \<notin> lits_of_l M\<close>
        using uL_C neg_C n_d unfolding has_blit_def by (auto dest!: multi_member_split
            dest!: no_dup_consistentD
            dest!: in_lits_of_l_defined_litD[of \<open>-L\<close>] simp: add_mset_eq_add_mset)
      moreover have \<open>\<not>has_blit M (clause C) K'\<close>
        using \<open>K' \<notin> lits_of_l M\<close> \<open> K \<notin> lits_of_l M\<close>
        using uL_C neg_C n_d unfolding has_blit_def by (auto dest!: multi_member_split
            dest!: no_dup_consistentD
            dest!: in_lits_of_l_defined_litD[of \<open>-L\<close>] simp: add_mset_eq_add_mset)
      ultimately have \<open>\<forall>K \<in># unwatched C. -K \<in> lits_of_l M\<close>
        apply -
        apply (rule disjE[OF disj])
        subgoal
          using excep[of K]
          unfolding C_W twl_clause.sel member_add_mset W
          by auto
        subgoal
          using excep[of K']
          unfolding C_W twl_clause.sel member_add_mset W
          by auto
        done
      then show False
        using uL_W uL_C L_M unfolding C_W W by auto
    qed
    then show \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># {#- L#}) \<or> (\<exists>L. (L, C) \<in># {#})\<close>
      by auto
  qed

  case 2
  show ?case
    unfolding propa_cands_enqueued.simps Ball_def
  proof (intro allI impI)
    fix FK C
    assume
      C: \<open>C \<in># N + U\<close> and
      K: \<open>FK \<in># clause C\<close> and
      LM_C: \<open>Decided L # M \<Turnstile>as CNot (remove1_mset FK (clause C))\<close> and
      undef: \<open>undefined_lit (Decided L # M) FK\<close>
    have undef_M_K: \<open>undefined_lit M FK\<close>
      using undef by (auto simp: defined_lit_map)
    then have \<open>\<not> M \<Turnstile>as CNot (remove1_mset FK (clause C))\<close>
      using propa_cands C K undef by auto
    then have \<open>-L \<in># clause C\<close> and
      neg_C: \<open>\<forall>K \<in># remove1_mset FK (clause C). -K \<in> lits_of_l (Decided L # M)\<close>
      using LM_C undef_M_K by (force simp: true_annots_true_cls_def_iff_negation_in_model
          dest: in_diffD)+

    have struct_C: \<open>struct_wf_twl_cls C\<close>
      using twl_st_inv C unfolding twl_st_inv.simps by blast
    then have dist_C: \<open>distinct_mset (clause C)\<close>
      by (cases C) auto

    have \<open>-L \<in># watched C\<close>
    proof (rule ccontr)
      assume uL_W: \<open>-L \<notin># watched C\<close>
      then obtain W UW K K' where
        C_W: \<open>C = TWL_Clause W UW\<close> and
        W: \<open>W = {#K, K'#}\<close> and
        uK_M: \<open>-K \<in> lits_of_l M\<close>
        using struct_C neg_C by (cases C) (auto simp: size_2_iff remove1_mset_add_mset_If
          add_mset_commute split: if_splits)
      have FK_F: \<open>FK \<noteq> K\<close>
        using Decided_Propagated_in_iff_in_lits_of_l uK_M undef_M_K by blast
      have L_M: \<open>undefined_lit M L\<close>
        using neg_C uL_W n_d unfolding C_W W by auto
      then have \<open>K \<noteq> -L\<close>
        using uK_M by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)
      moreover have \<open>K \<notin> lits_of_l M\<close>
        using neg_C uL_W n_d uK_M by (auto simp: lits_of_def uminus_lit_swap
            no_dup_cannot_not_lit_and_uminus)
      ultimately have \<open>K' \<notin> lits_of_l M\<close>
        apply (cases \<open>K' = FK\<close>)
        using Decided_Propagated_in_iff_in_lits_of_l undef_M_K apply blast
        using neg_C C_W W FK_F n_d uL_W by (auto simp add: remove1_mset_add_mset_If uminus_lit_swap
            lits_of_def no_dup_cannot_not_lit_and_uminus)
      moreover have \<open>twl_exception_inv (M, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#}) C\<close>
        using excep C by auto

      moreover have \<open>\<not>has_blit M (clause C) K\<close>
        using \<open>K \<notin> lits_of_l M\<close>  \<open>K' \<notin> lits_of_l M\<close>
        using K in_lits_of_l_defined_litD neg_C undef_M_K n_d unfolding has_blit_def
        by (force dest!: multi_member_split
            dest!: no_dup_consistentD
            dest!: in_lits_of_l_defined_litD[of \<open>-L\<close>] simp: add_mset_eq_add_mset)
      moreover have \<open>\<not>has_blit M (clause C) K'\<close>
        using \<open>K' \<notin> lits_of_l M\<close> \<open> K \<notin> lits_of_l M\<close>  K in_lits_of_l_defined_litD neg_C undef_M_K
        using n_d unfolding has_blit_def by (force dest!: multi_member_split
            dest!: no_dup_consistentD
            dest!: in_lits_of_l_defined_litD[of \<open>-L\<close>] simp: add_mset_eq_add_mset)
      ultimately have \<open>\<forall>K \<in># unwatched C. -K \<in> lits_of_l M\<close>
        using uK_M
        by (auto simp: twl_exception_inv.simps C_W W add_mset_eq_add_mset all_conj_distrib)
      then show False
        using C_W L_M(1) \<open>- L \<in># clause C\<close> uL_W
        by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)
    qed
    then show \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># {#- L#}) \<or> (\<exists>L. (L, C) \<in># {#})\<close>
      by auto
  qed

  case 3
  show ?case
  proof (induction rule: clauses_to_update_inv_cases)
    case (WS_nempty L C)
    then show ?case by simp
  next
    case (WS_empty K)
    then show ?case
      using w_q n_d unfolding clauses_to_update_prop.simps
      by (auto simp add: filter_mset_empty_conv
          dest!: no_has_blit_decide')
  next
    case (Q K C)
    then show ?case
      using w_q n_d by (auto dest!: no_has_blit_decide')
  qed
next
  case (skip L D C' M N U NE UE NS US)
  case 1 then show ?case by auto
  case 2 then show ?case by auto
  case 3 then show ?case by auto
next
  case (resolve L D C M N U NE UE NS US)
  case 1 then show ?case by auto
  case 2 then show ?case by auto
  case 3 then show ?case by auto
next
  case (backtrack_unit_clause L D K M1 M2 M D' i N U NE UE NS US N0 U0) note decomp = this(2)
  let ?S = \<open>(M, N, U, Some D, NE, UE, NS, US, N0, U0, {#}, {#})\<close>
  let ?U = \<open>(Propagated L {#L#} # M1, N, U, None, NE, add_mset {#L#} UE, NS, US, N0, U0, {#}, {#- L#})\<close>
  obtain M3 where
    M: \<open>M = M3 @ M2 @ Decided K # M1\<close>
    using decomp by blast

  case 1
  then have twl_st_inv: \<open>twl_st_inv ?S\<close> and
    struct_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of ?S)\<close> and
    excep: \<open>twl_st_exception_inv ?S\<close> and
    past: \<open>past_invs ?S\<close>
    using decomp unfolding twl_struct_invs_def pcdcl_all_struct_invs_def by auto
  then have
    confl_cands: \<open>confl_cands_enqueued (M1, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#})\<close> and
    propa_cands: \<open>propa_cands_enqueued (M1, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#})\<close>and
    w_q: \<open>clauses_to_update_inv (M1, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#})\<close>
    using decomp unfolding past_invs.simps by (auto simp del: clauses_to_update_inv.simps)

  have n_d: \<open>no_dup M\<close>
    using struct_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
     cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: trail.simps)
  have \<open>pcdcl_tcore (pstate\<^sub>W_of ?S) (pstate\<^sub>W_of ?U)\<close>
    using cdcl_twl_o_cdcl\<^sub>W_o[OF cdcl_twl_o.backtrack_unit_clause[OF backtrack_unit_clause.hyps]]
      1 unfolding twl_struct_invs_def pcdcl_all_struct_invs_def by auto
  from pcdcl_tcore_pcdcl_all_struct_invs[OF this]
  have struct_inv_T: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of ?U)\<close>
    using 1 unfolding twl_struct_invs_def pcdcl_all_struct_invs_def by auto
  then have n_d_L_M1: \<open>no_dup (Propagated L {#L#} # M1)\<close>
    using struct_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
     cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: trail.simps)
  then have uL_M1: \<open>undefined_lit M1 L\<close>
    by (simp_all add: atm_lit_of_set_lits_of_l atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set)


  have excep_M1: \<open>\<forall>C \<in># N + U. twl_exception_inv (M1, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#}) C\<close>
    using past unfolding past_invs.simps M by auto

  show ?case
    unfolding confl_cands_enqueued.simps Ball_def
  proof (intro allI impI)
    fix C
    assume
      C: \<open>C \<in># N + U\<close> and
      LM_C: \<open>Propagated L {#L#} # M1 \<Turnstile>as CNot (clause C)\<close>

    have struct_C: \<open>struct_wf_twl_cls C\<close>
      using twl_st_inv C unfolding twl_st_inv.simps by auto
    then have dist_C: \<open>distinct_mset (clause C)\<close>
      by (cases C) auto

    obtain W UW K K' where
      C_W: \<open>C = TWL_Clause W UW\<close> and
      W: \<open>W = {#K, K'#}\<close>
      using struct_C by (cases C) (auto simp: size_2_iff)

    have \<open>\<not>M1 \<Turnstile>as CNot (clause C)\<close>
      using confl_cands C by auto
    then have uL_C: \<open>-L \<in># clause C\<close> and neg_C: \<open>\<forall>K \<in># clause C. -K \<in> lits_of_l (Decided L # M1)\<close>
      using LM_C unfolding true_annots_true_cls_def_iff_negation_in_model by auto
    have K_L: \<open>K \<noteq> L\<close> and K'_L: \<open>K' \<noteq> L\<close>
       apply (metis C_W LM_C W add_diff_cancel_right' clause.simps consistent_interp_def
          distinct_consistent_interp in_CNot_implies_uminus(2) in_diffD n_d_L_M1 uL_C
          union_single_eq_member)
      using C_W LM_C W uL_M1 by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)
    have \<open>-L \<in># watched C\<close>
    proof (rule ccontr)
      assume uL_W: \<open>-L \<notin># watched C\<close>
      have \<open>K \<noteq> -L \<or> K' \<noteq> -L\<close>
        using dist_C C_W W by auto
      moreover have \<open>K \<notin> lits_of_l M1\<close> and \<open>K' \<notin> lits_of_l M1\<close> and L_M: \<open>L \<notin> lits_of_l M1\<close>
      proof -
        have f2: \<open>consistent_interp (lits_of_l M1)\<close>
          using distinct_consistent_interp n_d_L_M1 by auto
        have undef_L: \<open>undefined_lit M1 L\<close>
          using atm_lit_of_set_lits_of_l n_d_L_M1 by force
        then show \<open>K \<notin> lits_of_l M1\<close>
          using f2 neg_C unfolding C_W W by (metis (no_types) C_W W add_diff_cancel_right'
              atm_of_eq_atm_of clause.simps
              consistent_interp_def in_diffD insertE list.simps(15) lits_of_insert uL_C
              union_single_eq_member Decided_Propagated_in_iff_in_lits_of_l)
        show \<open>K' \<notin> lits_of_l M1\<close>
          using consistent_interp_def distinct_consistent_interp n_d_L_M1
          using neg_C uL_W n_d unfolding C_W W by auto
        show \<open>L \<notin> lits_of_l M1\<close>
          using undef_L by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)
      qed
      ultimately have \<open>(-K \<in> lits_of_l M1 \<and> K' \<notin> lits_of_l M1) \<or>
          (-K' \<in> lits_of_l M1 \<and> K \<notin> lits_of_l M1)\<close>
        using neg_C by (auto simp: C_W W)
      moreover have \<open>twl_exception_inv (M1, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#}) C\<close>
        using excep_M1 C by auto
      have \<open>\<not>has_blit M1 (clause C) K\<close>
        using \<open>K \<notin> lits_of_l M1\<close>  \<open>K' \<notin> lits_of_l M1\<close> \<open>L \<notin> lits_of_l M1\<close> uL_M1
          n_d_L_M1 no_dup_cons
        using uL_C neg_C n_d unfolding has_blit_def apply (auto dest!: multi_member_split
            dest!: no_dup_consistentD[OF n_d_L_M1]
            dest!: in_lits_of_l_defined_litD[of \<open>-L\<close>] simp: add_mset_eq_add_mset)
        using n_d_L_M1 no_dup_cons no_dup_consistentD by blast
      moreover have \<open>\<not>has_blit M1 (clause C) K'\<close>
        using \<open>K' \<notin> lits_of_l M1\<close> \<open> K \<notin> lits_of_l M1\<close> \<open>L \<notin> lits_of_l M1\<close> uL_M1
          n_d_L_M1 no_dup_cons no_dup_consistentD
        using uL_C neg_C n_d unfolding has_blit_def apply (auto 10 10 dest!: multi_member_split
            dest!: in_lits_of_l_defined_litD[of \<open>-L\<close>] simp: add_mset_eq_add_mset)
        using n_d_L_M1 no_dup_cons no_dup_consistentD by auto
      ultimately have \<open>\<forall>K \<in># unwatched C. -K \<in> lits_of_l M1\<close>
        using C twl_clause.sel(1) union_single_eq_member w_q
        by (fastforce simp: twl_exception_inv.simps C_W W add_mset_eq_add_mset all_conj_distrib L_M)
      then show False
        using uL_W uL_C L_M K_L uL_M1 unfolding C_W W by auto
    qed
    then show \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># {#- L#}) \<or> (\<exists>L. (L, C) \<in># {#})\<close>
      by auto
  qed
  case 2
  then show ?case
    unfolding propa_cands_enqueued.simps Ball_def
  proof (intro allI impI)
    fix FK C
    assume
      C: \<open>C \<in># N + U\<close> and
      K: \<open>FK \<in># clause C\<close> and
      LM_C: \<open>Propagated L {#L#} # M1 \<Turnstile>as CNot (remove1_mset FK (clause C))\<close> and
      undef: \<open>undefined_lit (Propagated L {#L#} # M1) FK\<close>
    have undef_M_K: \<open>undefined_lit (Propagated L D # M1) FK\<close>
      using undef by (auto simp: defined_lit_map)
    then have \<open>\<not> M1 \<Turnstile>as CNot (remove1_mset FK (clause C))\<close>
      using propa_cands C K undef by (auto simp: defined_lit_map)
    then have uL_C: \<open>-L \<in># clause C\<close> and
      neg_C: \<open>\<forall>K \<in># remove1_mset FK (clause C). -K \<in> lits_of_l (Propagated L D # M1)\<close>
      using LM_C undef_M_K by (force simp: true_annots_true_cls_def_iff_negation_in_model
          dest: in_diffD)+

    have struct_C: \<open>struct_wf_twl_cls C\<close>
      using twl_st_inv C unfolding twl_st_inv.simps by blast
    then have dist_C: \<open>distinct_mset (clause C)\<close>
      by (cases C) auto

    moreover have \<open>-L \<in># watched C\<close>
    proof (rule ccontr)
      assume uL_W: \<open>-L \<notin># watched C\<close>
      then obtain W UW K K' where
        C_W: \<open>C = TWL_Clause W UW\<close> and
        W: \<open>W = {#K, K'#}\<close> and
        uK_M: \<open>-K \<in> lits_of_l M1\<close>
        using struct_C neg_C by (cases C) (auto simp: size_2_iff remove1_mset_add_mset_If
            add_mset_commute split: if_splits)
      have \<open>K \<notin> lits_of_l M1\<close> and L_M: \<open>L \<notin> lits_of_l M1\<close>
      proof -
        have f2: \<open>consistent_interp (lits_of_l M1)\<close>
          using distinct_consistent_interp n_d_L_M1 by auto
        have undef_L: \<open>undefined_lit M1 L\<close>
          using atm_lit_of_set_lits_of_l n_d_L_M1 by force
        then show \<open>K \<notin> lits_of_l M1\<close>
          using f2 neg_C unfolding C_W W
          using n_d_L_M1 no_dup_cons no_dup_consistentD uK_M by blast
        show \<open>L \<notin> lits_of_l M1\<close>
          using undef_L by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)
      qed
      have FK_F: \<open>FK \<noteq> K\<close>
        using uK_M undef_M_K unfolding Decided_Propagated_in_iff_in_lits_of_l by auto
      have \<open>K \<noteq> -L\<close>
        using uK_M uL_M1 by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)
      moreover have \<open>K \<notin> lits_of_l M1\<close>
        using neg_C uL_W n_d uK_M n_d_L_M1 by (auto simp: lits_of_def uminus_lit_swap
            no_dup_cannot_not_lit_and_uminus dest: no_dup_cannot_not_lit_and_uminus)
      ultimately have \<open>K' \<notin> lits_of_l M1\<close>
        apply (cases \<open>K' = FK\<close>)
        using undef_M_K apply (force simp: Decided_Propagated_in_iff_in_lits_of_l)
        using neg_C C_W W FK_F n_d uL_W n_d_L_M1 by (auto simp add: remove1_mset_add_mset_If
            uminus_lit_swap lits_of_def no_dup_cannot_not_lit_and_uminus
            dest: no_dup_cannot_not_lit_and_uminus)
      moreover have \<open>twl_exception_inv (M1, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#}) C\<close>
        using excep_M1 C by auto
      moreover have \<open>\<not>has_blit M1 (clause C) K\<close>
        using \<open>K \<notin> lits_of_l M1\<close>  \<open>K' \<notin> lits_of_l M1\<close> \<open>L \<notin> lits_of_l M1\<close> uL_M1
          n_d_L_M1 no_dup_cons K undef
        using uL_C neg_C n_d unfolding has_blit_def apply (auto dest!: multi_member_split
            dest!: no_dup_consistentD[OF n_d_L_M1]
            dest!: in_lits_of_l_defined_litD[of \<open>-L\<close>] simp: add_mset_eq_add_mset)
        by (smt add_mset_commute add_mset_eq_add_mset defined_lit_uminus in_lits_of_l_defined_litD
            insert_DiffM no_dup_consistentD set_subset_Cons true_annot_mono true_annot_singleton)+
      moreover have \<open>\<not>has_blit M1 (clause C) K'\<close>
        using \<open>K' \<notin> lits_of_l M1\<close> \<open> K \<notin> lits_of_l M1\<close> \<open>L \<notin> lits_of_l M1\<close> uL_M1
          n_d_L_M1 no_dup_cons no_dup_consistentD K undef
        using uL_C neg_C n_d unfolding has_blit_def apply (auto 10 10 dest!: multi_member_split
            dest!: in_lits_of_l_defined_litD[of \<open>-L\<close>] simp: add_mset_eq_add_mset)
        by (smt add_mset_commute add_mset_eq_add_mset defined_lit_uminus in_lits_of_l_defined_litD
            insert_DiffM no_dup_consistentD set_subset_Cons true_annot_mono true_annot_singleton)+
      ultimately have \<open>\<forall>K \<in># unwatched C. -K \<in> lits_of_l M1\<close>
        using uK_M
        by (auto simp: twl_exception_inv.simps C_W W add_mset_eq_add_mset all_conj_distrib)
      then show False
        using C_W uL_M1 \<open>- L \<in># clause C\<close> uL_W
        by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)
    qed
    then show \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># {#- L#}) \<or> (\<exists>L. (L, C) \<in># {#})\<close>
      by auto
  qed

  case 3
  have
    2: \<open>\<And>L. Pair L `# {#C \<in># N + U. clauses_to_update_prop {#} M1 (L, C)#} = {#}\<close> and
    3: \<open>\<And>L C. C \<in># N + U \<Longrightarrow> L \<in># watched C \<Longrightarrow> - L \<in> lits_of_l M1 \<Longrightarrow>
      \<not> has_blit M1 (clause C) L \<Longrightarrow> (L, C) \<notin># {#} \<Longrightarrow> L \<in># {#}\<close>
    using w_q unfolding clauses_to_update_inv.simps by auto


  show ?case
  proof (induction rule: clauses_to_update_inv_cases)
    case (WS_nempty L C)
    then show ?case by simp
  next
    case (WS_empty K)
    then show ?case
      using 2[of K]  n_d_L_M1
      apply (simp only: filter_mset_empty_conv Ball_def image_mset_is_empty_iff)
      by (auto simp add: clauses_to_update_prop.simps)
  next
    case (Q K C)
    then show ?case
      using 3[of C K] has_blit_Cons n_d_L_M1 by (fastforce simp add: clauses_to_update_prop.simps)
  qed
next
  case (backtrack_nonunit_clause L D K M1 M2 M D' i N U NE UE NS US N0 U0 L') note LD = this(1) and
    decomp = this(2) and lev_L = this(3) and lev_max_L = this(4) and i = this(5) and lev_K = this(6)
    and LD' = this(11) and lev_L' = this(12)
  let ?S = \<open>(M, N, U, Some D, NE, UE, NS, US, N0, U0, {#}, {#})\<close>
  let ?D = \<open>TWL_Clause {#L, L'#} (D' - {#L, L'#})\<close>
  let ?U = \<open>(Propagated L D' # M1, N, add_mset ?D U, None, NE,
    UE, NS, US, N0, U0, {#}, {#- L#})\<close>
  obtain M3 where
    M: \<open>M = M3 @ M2 @ Decided K # M1\<close>
    using decomp by blast

  case 1
  then have twl_st_inv: \<open>twl_st_inv ?S\<close> and
    struct_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of ?S)\<close> and
    excep: \<open>twl_st_exception_inv ?S\<close> and
    past: \<open>past_invs ?S\<close>
    using decomp unfolding twl_struct_invs_def pcdcl_all_struct_invs_def by auto
  then have
    confl_cands: \<open>confl_cands_enqueued (M1, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#})\<close> and
    propa_cands: \<open>propa_cands_enqueued (M1, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#})\<close> and
    w_q: \<open>clauses_to_update_inv (M1, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#})\<close>
    using decomp unfolding past_invs.simps by auto

  have n_d: \<open>no_dup M\<close>
    using struct_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
     cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: trail.simps)

  have \<open>undefined_lit (M3 @ M2 @ M1) K\<close>
    by (rule no_dup_append_in_atm_notin[of _ \<open>[Decided K]\<close>])
      (use n_d M in \<open>auto simp: no_dup_def\<close>)
  then have L_uL': \<open>L \<noteq> - L'\<close>
    using lev_L lev_L' lev_K unfolding M by (auto simp: image_Un)

  have \<open>pcdcl_tcore (pstate\<^sub>W_of ?S) (pstate\<^sub>W_of ?U)\<close>
    using cdcl_twl_o_cdcl\<^sub>W_o[OF cdcl_twl_o.backtrack_nonunit_clause[OF backtrack_nonunit_clause.hyps]]
      1 unfolding twl_struct_invs_def pcdcl_all_struct_invs_def by auto
  from pcdcl_tcore_pcdcl_all_struct_invs[OF this]
  have struct_inv_T: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of ?U)\<close>
    using 1 unfolding twl_struct_invs_def pcdcl_all_struct_invs_def by auto
  then have n_d_L_M1: \<open>no_dup (Propagated L D' # M1)\<close>
    using struct_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
     cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: trail.simps)
  then have uL_M1: \<open>undefined_lit M1 L\<close>
    by simp

  have M1_CNot_L_D: \<open>M1 \<Turnstile>as CNot (remove1_mset L D')\<close>
    using struct_inv_T unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
     cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def by (auto simp: trail.simps)

  have L_M1: \<open>- L \<notin> lits_of_l M1\<close> \<open>L \<notin> lits_of_l M1\<close>
    using n_d n_d_L_M1 uL_M1 by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)

  have excep_M1: \<open>\<forall>C \<in># N + U. twl_exception_inv (M1, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#}) C\<close>
    using past unfolding past_invs.simps M by auto
  show ?case
    unfolding confl_cands_enqueued.simps Ball_def
  proof (intro allI impI)
    fix C
    assume
      C: \<open>C \<in># N + add_mset ?D U\<close> and
      LM_C: \<open>Propagated L D' # M1 \<Turnstile>as CNot (clause C)\<close>
    have \<open>twl_st_inv ?U\<close>
      using cdcl_twl_o.backtrack_nonunit_clause[OF backtrack_nonunit_clause.hyps] "1.prems"
        cdcl_twl_o_twl_st_inv by blast
    then have \<open>struct_wf_twl_cls ?D\<close>
      unfolding twl_st_inv.simps by auto

    show \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># {#- L#}) \<or> (\<exists>L. (L, C) \<in># {#})\<close>
    proof (cases \<open>C = ?D\<close>)
      case True
      then have False
        using LM_C L_uL' uL_M1 by (auto simp: true_annots_true_cls_def_iff_negation_in_model
            Decided_Propagated_in_iff_in_lits_of_l)
      then show ?thesis by fast
    next
      case False
      have struct_C: \<open>struct_wf_twl_cls C\<close>
        using twl_st_inv C False unfolding twl_st_inv.simps by auto
      then have dist_C: \<open>distinct_mset (clause C)\<close>
        by (cases C) auto

      have C: \<open>C \<in># N + U\<close>
        using C False by auto
      obtain W UW K K' where
        C_W: \<open>C = TWL_Clause W UW\<close> and
        W: \<open>W = {#K, K'#}\<close>
        using struct_C by (cases C) (auto simp: size_2_iff)

      have \<open>\<not>M1 \<Turnstile>as CNot (clause C)\<close>
        using confl_cands C by auto
      then have uL_C: \<open>-L \<in># clause C\<close> and neg_C: \<open>\<forall>K \<in># clause C. -K \<in> lits_of_l (Decided L # M1)\<close>
        using LM_C unfolding true_annots_true_cls_def_iff_negation_in_model by auto
      have K_L: \<open>K \<noteq> L\<close> and K'_L: \<open>K' \<noteq> L\<close>
         apply (metis C_W LM_C W add_diff_cancel_right' clause.simps consistent_interp_def
            distinct_consistent_interp in_CNot_implies_uminus(2) in_diffD n_d_L_M1 uL_C
            union_single_eq_member)
        using C_W LM_C W uL_M1 by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)
      have \<open>-L \<in># watched C\<close>
      proof (rule ccontr)
        assume uL_W: \<open>-L \<notin># watched C\<close>
        have \<open>K \<noteq> -L \<or> K' \<noteq> -L\<close>
          using dist_C C_W W by auto
        moreover have \<open>K \<notin> lits_of_l M1\<close> and \<open>K' \<notin> lits_of_l M1\<close> and L_M: \<open>L \<notin> lits_of_l M1\<close>
        proof -
          have f2: \<open>consistent_interp (lits_of_l M1)\<close>
            using distinct_consistent_interp n_d_L_M1 by auto
          have undef_L: \<open>undefined_lit M1 L\<close>
            using atm_lit_of_set_lits_of_l n_d_L_M1 by force
          then show \<open>K \<notin> lits_of_l M1\<close>
            using f2 neg_C unfolding C_W W by (metis (no_types) C_W W add_diff_cancel_right'
                atm_of_eq_atm_of clause.simps consistent_interp_def in_diffD insertE list.simps(15)
                lits_of_insert uL_C union_single_eq_member Decided_Propagated_in_iff_in_lits_of_l)
          show \<open>K' \<notin> lits_of_l M1\<close>
            using consistent_interp_def distinct_consistent_interp n_d_L_M1
            using neg_C uL_W n_d unfolding C_W W by auto
          show \<open>L \<notin> lits_of_l M1\<close>
            using undef_L by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)
        qed
        ultimately have \<open>(-K \<in> lits_of_l M1 \<and> K' \<notin> lits_of_l M1) \<or>
            (-K' \<in> lits_of_l M1 \<and> K \<notin> lits_of_l M1)\<close>
          using neg_C by (auto simp: C_W W)
        moreover have \<open>\<not>has_blit M1 (clause C) K\<close>
          using \<open>K \<notin> lits_of_l M1\<close>  \<open>K' \<notin> lits_of_l M1\<close> \<open>L \<notin> lits_of_l M1\<close> uL_M1
            n_d_L_M1 no_dup_cons
          using uL_C neg_C n_d unfolding has_blit_def apply (auto dest!: multi_member_split
              dest!: no_dup_consistentD[OF n_d_L_M1]
              dest!: in_lits_of_l_defined_litD[of \<open>-L\<close>] simp: add_mset_eq_add_mset)
          using n_d_L_M1 no_dup_cons no_dup_consistentD by blast
        moreover have \<open>\<not>has_blit M1 (clause C) K'\<close>
          using \<open>K' \<notin> lits_of_l M1\<close> \<open> K \<notin> lits_of_l M1\<close> \<open>L \<notin> lits_of_l M1\<close> uL_M1
            n_d_L_M1 no_dup_cons no_dup_consistentD
          using uL_C neg_C n_d unfolding has_blit_def apply (auto 10 10 dest!: multi_member_split
              dest!: in_lits_of_l_defined_litD[of \<open>-L\<close>] simp: add_mset_eq_add_mset)
          using n_d_L_M1 no_dup_cons no_dup_consistentD by auto
        moreover have \<open>twl_exception_inv (M1, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#}) C\<close>
          using excep_M1 C by auto
        ultimately have \<open>\<forall>K \<in># unwatched C. -K \<in> lits_of_l M1\<close>
          using C twl_clause.sel(1) union_single_eq_member w_q
          by (fastforce simp: twl_exception_inv.simps C_W W add_mset_eq_add_mset all_conj_distrib
              L_M)
        then show False
          using uL_W uL_C L_M K_L uL_M1 unfolding C_W W by auto
      qed
      then show \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># {#- L#}) \<or> (\<exists>L. (L, C) \<in># {#})\<close>
        by auto
    qed
  qed

  case 2
  then show ?case
    unfolding propa_cands_enqueued.simps Ball_def
  proof (intro allI impI)
    fix FK C
    assume
      C: \<open>C \<in># N + add_mset ?D U\<close> and
      K: \<open>FK \<in># clause C\<close> and
      LM_C: \<open>Propagated L D' # M1 \<Turnstile>as CNot (remove1_mset FK (clause C))\<close> and
      undef: \<open>undefined_lit (Propagated L D' # M1) FK\<close>
    show \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># {#- L#}) \<or> (\<exists>L. (L, C) \<in># {#})\<close>
    proof (cases \<open>C = ?D\<close>)
      case False
      then have C: \<open>C \<in># N + U\<close>
        using C by auto
      have undef_M_K: \<open>undefined_lit (Propagated L D # M1) FK\<close>
        using undef by (auto simp: defined_lit_map)
      then have \<open>\<not> M1 \<Turnstile>as CNot (remove1_mset FK (clause C))\<close>
        using propa_cands C K undef by (auto simp: defined_lit_map)
      then have \<open>-L \<in># clause C\<close> and
        neg_C: \<open>\<forall>K \<in># remove1_mset FK (clause C). -K \<in> lits_of_l (Propagated L D # M1)\<close>
        using LM_C undef_M_K by (force simp: true_annots_true_cls_def_iff_negation_in_model
            dest: in_diffD)+

      have struct_C: \<open>struct_wf_twl_cls C\<close>
        using twl_st_inv C unfolding twl_st_inv.simps by blast
      then have dist_C: \<open>distinct_mset (clause C)\<close>
        by (cases C) auto

      have \<open>-L \<in># watched C\<close>
      proof (rule ccontr)
        assume uL_W: \<open>-L \<notin># watched C\<close>
        then obtain W UW K K' where
          C_W: \<open>C = TWL_Clause W UW\<close> and
          W: \<open>W = {#K, K'#}\<close> and
          uK_M: \<open>-K \<in> lits_of_l M1\<close>
          using struct_C neg_C by (cases C) (auto simp: size_2_iff remove1_mset_add_mset_If
              add_mset_commute split: if_splits)
        have FK_F: \<open>FK \<noteq> K\<close>
          using uK_M undef_M_K unfolding Decided_Propagated_in_iff_in_lits_of_l by auto
        have \<open>K \<noteq> -L\<close>
          using uK_M uL_M1 by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)
        moreover have \<open>K \<notin> lits_of_l M1\<close>
          using neg_C uL_W n_d uK_M n_d_L_M1 by (auto simp: lits_of_def uminus_lit_swap
              no_dup_cannot_not_lit_and_uminus dest: no_dup_cannot_not_lit_and_uminus)
        ultimately have \<open>K' \<notin> lits_of_l M1\<close>
          apply (cases \<open>K' = FK\<close>)
          using undef_M_K apply (force simp: Decided_Propagated_in_iff_in_lits_of_l)
          using neg_C C_W W FK_F n_d uL_W n_d_L_M1 by (auto simp add: remove1_mset_add_mset_If
              uminus_lit_swap lits_of_def no_dup_cannot_not_lit_and_uminus
              dest: no_dup_cannot_not_lit_and_uminus)
        moreover have \<open>twl_exception_inv (M1, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#}) C\<close>
          using excep_M1 C by auto
        moreover have \<open>\<not>has_blit M1 (clause C) K\<close>
          using \<open>K \<notin> lits_of_l M1\<close>  \<open>K' \<notin> lits_of_l M1\<close> uL_M1
            n_d_L_M1 no_dup_cons
          using n_d_L_M1 no_dup_cons no_dup_consistentD
          using K in_lits_of_l_defined_litD undef
          using neg_C n_d unfolding has_blit_def by (fastforce dest!: multi_member_split
              dest!: no_dup_consistentD[OF n_d_L_M1]
              dest!: in_lits_of_l_defined_litD[of \<open>-L\<close>] simp: add_mset_eq_add_mset)
        moreover have \<open>\<not>has_blit M1 (clause C) K'\<close>
          using \<open>K' \<notin> lits_of_l M1\<close> \<open> K \<notin> lits_of_l M1\<close> uL_M1
            n_d_L_M1 no_dup_cons no_dup_consistentD
          using n_d_L_M1 no_dup_cons no_dup_consistentD
          using K in_lits_of_l_defined_litD undef
          using neg_C n_d unfolding has_blit_def by (fastforce dest!: multi_member_split
              dest!: in_lits_of_l_defined_litD[of \<open>-L\<close>] simp: add_mset_eq_add_mset)
        moreover have \<open>twl_exception_inv (M1, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#}) C\<close>
          using excep_M1 C by auto
        ultimately have \<open>\<forall>K \<in># unwatched C. -K \<in> lits_of_l M1\<close>
          using uK_M
          by (auto simp: twl_exception_inv.simps C_W W add_mset_eq_add_mset all_conj_distrib)
        then show False
          using C_W uL_M1 \<open>- L \<in># clause C\<close> uL_W
          by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)
      qed
      then show \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># {#- L#}) \<or> (\<exists>L. (L, C) \<in># {#})\<close>
        by auto
    next
      case True
      then have \<open>\<forall>K\<in>#remove1_mset L D'. - K \<in> lits_of_l (Propagated L D' # M1)\<close>
        using M1_CNot_L_D by (auto simp: true_annots_true_cls_def_iff_negation_in_model)
      then have \<open>\<forall>K\<in>#remove1_mset L D'. defined_lit (Propagated L D' # M1) K\<close>
        using Decided_Propagated_in_iff_in_lits_of_l by blast
      moreover have \<open>defined_lit (Propagated L D' # M1) L\<close>
        by (auto simp: defined_lit_map)
      ultimately have \<open>\<forall>K\<in>#D'. defined_lit (Propagated L D' # M1) K\<close>
        by (metis in_remove1_mset_neq)
      then have \<open>\<forall>K\<in>#clause ?D. defined_lit (Propagated L D' # M1) K\<close>
        using LD' \<open>defined_lit (Propagated L D' # M1) L\<close> by (auto dest: in_diffD)
      then have False
        using K undef unfolding True by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)
      then show ?thesis by fast
    qed
  qed

  case 3
  then have
    2: \<open>\<And>L. Pair L `# {#C \<in># N + U. clauses_to_update_prop {#} M1 (L, C)#} = {#}\<close> and
    3: \<open>\<And>L C. C \<in># N + U \<Longrightarrow> L \<in># watched C \<Longrightarrow> - L \<in> lits_of_l M1 \<Longrightarrow>
       \<not> has_blit M1 (clause C) L \<Longrightarrow> (L, C) \<notin># {#} \<Longrightarrow> L \<in># {#}\<close>
    using w_q unfolding clauses_to_update_inv.simps by auto
  have \<open>i = count_decided M1\<close>
    using decomp lev_K n_d by (auto dest!: get_all_ann_decomposition_exists_prepend
        simp: get_level_append_if get_level_cons_if
        split: if_splits)
  then have lev_L'_M1: \<open>get_level (Propagated L D' # M1) L' = count_decided M1\<close>
    using decomp lev_L' n_d by (auto dest!: get_all_ann_decomposition_exists_prepend
        simp: get_level_append_if get_level_cons_if
        split: if_splits)
  have blit_L': \<open>has_blit (Propagated L D' # M1) (add_mset L (add_mset L' (D' - {#L, L'#}))) L'\<close>
    unfolding has_blit_def
    by (rule_tac x=L in exI) (auto simp: lev_L'_M1)
  show ?case
  proof (induction rule: clauses_to_update_inv_cases)
    case (WS_nempty L C)
    then show ?case by simp
  next
    case (WS_empty K')

    show ?case
      using 2[of K] "3" n_d_L_M1 L_M1 blit_L'
      apply (simp only: filter_mset_empty_conv Ball_def image_mset_is_empty_iff)
      by (fastforce simp add: clauses_to_update_prop.simps )
  next
    case (Q K' C)
    then show ?case
      using 3[of C K'] uL_M1 blit_L' n_d_L_M1 has_blit_Cons
      by (fastforce simp add: clauses_to_update_prop.simps
          add_mset_eq_add_mset Decided_Propagated_in_iff_in_lits_of_l)
  qed
qed

lemma no_dup_append_decided_Cons_lev:
  assumes \<open>no_dup (M2 @ Decided K # M1)\<close>
  shows \<open>count_decided M1 = get_level (M2 @ Decided K # M1) K - 1\<close>
proof -
  have \<open>undefined_lit (M2 @ M1) K\<close>
    by (rule no_dup_append_in_atm_notin[of _
          \<open>[Decided K]\<close>])
      (use assms in auto)
  then show ?thesis
    by (auto)
qed


subsubsection \<open>The Strategy\<close>

lemma no_literals_to_update_no_cp:
  assumes
    WS: \<open>clauses_to_update S = {#}\<close> and Q: \<open>literals_to_update S = {#}\<close> and
    twl: \<open>twl_struct_invs S\<close>
  shows
    \<open>no_step cdcl_propagate (pstate\<^sub>W_of S)\<close> and
    \<open>no_step cdcl_conflict (pstate\<^sub>W_of S)\<close>
proof -
  obtain M N U NE UE NS US N0 U0 D where
      S: \<open>S = (M, N, U, D, NE, UE, NS, US, N0, U0, {#}, {#})\<close>
    using WS Q by (cases S) auto

  {
    assume confl: \<open>get_conflict S = None\<close>
    then have S: \<open>S = (M, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#})\<close>
      using WS Q S by auto

    have twl_st_inv: \<open>twl_st_inv S\<close> and
      struct_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S)\<close> and
      excep: \<open>twl_st_exception_inv S\<close> and
      confl_cands: \<open>confl_cands_enqueued S\<close> and
      propa_cands: \<open>propa_cands_enqueued S\<close>
      using twl unfolding twl_struct_invs_def pcdcl_all_struct_invs_def by auto
    have n_d: \<open>no_dup M\<close>
      using struct_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: trail.simps S)
    then have L_uL: \<open>L \<in> lits_of_l M \<Longrightarrow> -L \<notin> lits_of_l M\<close> for L
      using consistent_interp_def distinct_consistent_interp by blast
    have no_confl: \<open>\<forall>C \<in># N + U. \<not>M\<Turnstile>as CNot (clause C)\<close>
      using confl_cands unfolding S by auto
    then have ns_confl: \<open>no_step cdcl_conflict (pstate\<^sub>W_of S)\<close>
      by (auto simp: S trail.simps clauses_def cdcl_conflict.simps)

    have ns_propa: \<open>no_step cdcl_propagate (pstate\<^sub>W_of S)\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then obtain C L where
        C: \<open>C \<in># clause `# (N + U)\<close> and
        L: \<open>L \<in># C\<close> and
        M: \<open>M \<Turnstile>as CNot (remove1_mset L C)\<close> and
        undef: \<open>undefined_lit M L\<close>
        by (auto simp: S trail.simps clauses_def cdcl_propagate.simps)
      then show False
         using propa_cands L M undef by (auto simp: S)
    qed
    note ns_confl ns_propa
  }
  moreover {
    assume \<open>get_conflict S \<noteq> None\<close>
    then have \<open>no_step cdcl_propagate (pstate\<^sub>W_of S)\<close>
      \<open>no_step cdcl_conflict (pstate\<^sub>W_of S)\<close>
      by (auto simp: S conflicting.simps cdcl_conflict.simps cdcl_propagate.simps)
  }
  ultimately show \<open>no_step cdcl_propagate (pstate\<^sub>W_of S)\<close>
      \<open>no_step cdcl_conflict (pstate\<^sub>W_of S)\<close>
    by blast+
qed

text \<open>
  When popping a literal from \<^term>\<open>literals_to_update\<close> to the \<^term>\<open>clauses_to_update\<close>,
  we do not do any transition in the abstract transition system. Therefore, we use
  \<^term>\<open>rtranclp\<close> or a case distinction.
  \<close>

lemma cdcl_twl_stgy_cdcl\<^sub>W_stgy2:
  assumes \<open>cdcl_twl_stgy S T\<close> and twl: \<open>twl_struct_invs S\<close>
  shows \<open>pcdcl_tcore_stgy (pstate\<^sub>W_of S) (pstate\<^sub>W_of T) \<or>
    (pstate\<^sub>W_of S = pstate\<^sub>W_of T \<and> (literals_to_update_measure T, literals_to_update_measure S)
    \<in> lexn less_than 2)\<close>
  using assms(1)
proof (induction rule: cdcl_twl_stgy.induct)
  case (cp S')
  then show ?case
    using twl cdcl_twl_cp_cdcl\<^sub>W_stgy[of S S'] by (metis (full_types)
    cdcl_twl_cp_twl_struct_invs pcdcl_all_struct_invs_def
    pcdcl_core_stgy.intros(1) pcdcl_core_stgy.intros(2) pcdcl_tcore_stgy.intros(1) state\<^sub>W_of_def
    twl_cp_propagate_or_conflict twl_struct_invs_def)
next
  case (other' S') note o = this(1)
  have wq: \<open>clauses_to_update S = {#}\<close> and p: \<open>literals_to_update S = {#}\<close>
    using o by (cases rule: cdcl_twl_o.cases; auto)+
  have \<open>pcdcl_tcore_stgy (pstate\<^sub>W_of S) (pstate\<^sub>W_of S')\<close>
    using no_literals_to_update_no_cp[OF wq p twl] cdcl_twl_o_cdcl\<^sub>W_o[of S S', OF o] twl
      pcdcl_tcore_nocp_pcdcl_tcore_stgy[of \<open>pstate\<^sub>W_of S\<close> \<open>pstate\<^sub>W_of S'\<close>]
   by (auto simp: twl_struct_invs_def pcdcl_all_struct_invs_def)

  then show ?case
    by auto
qed

lemma cdcl_twl_stgy_cdcl\<^sub>W_stgy:
  assumes \<open>cdcl_twl_stgy S T\<close> and twl: \<open>twl_struct_invs S\<close>
  shows \<open>pcdcl_tcore_stgy\<^sup>*\<^sup>* (pstate\<^sub>W_of S) (pstate\<^sub>W_of T)\<close>
  using cdcl_twl_stgy_cdcl\<^sub>W_stgy2[OF assms] by auto

lemma cdcl_twl_o_twl_struct_invs:
  assumes
    cdcl: \<open>cdcl_twl_o S T\<close> and
    twl: \<open>twl_struct_invs S\<close>
  shows \<open>twl_struct_invs T\<close>
proof -
  have cdcl\<^sub>W: \<open>pcdcl_tcore (pstate\<^sub>W_of S) (pstate\<^sub>W_of T)\<close>
    by (metis cdcl cdcl_twl_o_cdcl\<^sub>W_o pcdcl_all_struct_invs_def state\<^sub>W_of_def twl twl_struct_invs_def)

  have wq: \<open>clauses_to_update S = {#}\<close> and p: \<open>literals_to_update S = {#}\<close>
    using cdcl by (cases rule: cdcl_twl_o.cases; auto)+

  have struct_invs: \<open>pcdcl_all_struct_invs (pstate\<^sub>W_of T)\<close>
    using cdcl\<^sub>W pcdcl_tcore_pcdcl_all_struct_invs twl twl_struct_invs_def by blast

 show ?thesis
    unfolding twl_struct_invs_def
    apply (intro conjI)
    subgoal by (use cdcl cdcl_twl_o_twl_st_inv twl in \<open>blast; fail\<close>)
    subgoal by (use cdcl cdcl_twl_o_valid in \<open>blast; fail\<close>)
    subgoal by (rule struct_invs)
    subgoal
      by (metis cdcl\<^sub>W no_literals_to_update_no_cp(1) no_literals_to_update_no_cp(2) p
        pcdcl_tcore_nocp_pcdcl_tcore_stgy pcdcl_tcore_stgy_no_smaller_propa state\<^sub>W_of_def
        twl twl_struct_invs_def wq)
    subgoal by (use cdcl cdcl_twl_o_twl_st_exception_inv twl in \<open>blast; fail\<close>)
    subgoal by (use cdcl cdcl_twl_o_no_duplicate_queued in \<open>blast; fail\<close>)
    subgoal by (use cdcl cdcl_twl_o_distinct_queued in \<open>blast; fail\<close>)
    subgoal by (use cdcl cdcl_twl_o_confl_cands_enqueued twl twl_struct_invs_def in \<open>blast; fail\<close>)
    subgoal by (use cdcl cdcl_twl_o_propa_cands_enqueued twl twl_struct_invs_def in \<open>blast; fail\<close>)
    subgoal by (use cdcl twl cdcl_twl_o_conflict_None_queue in \<open>blast; fail\<close>)
    subgoal by (use cdcl twl_o_clauses_to_update twl in blast)
    subgoal by (use cdcl cdcl_twl_o_past_invs twl twl_struct_invs_def in blast)
    done
qed

lemma cdcl_twl_stgy_twl_struct_invs: (*\htmllink{cdcl_twl_stgy_twl_struct_invs} *)
  assumes
    cdcl: \<open>cdcl_twl_stgy S T\<close> and
    twl: \<open>twl_struct_invs S\<close>
  shows \<open>twl_struct_invs T\<close>
  using cdcl by (induction rule: cdcl_twl_stgy.induct)
    (simp_all add: cdcl_twl_cp_twl_struct_invs cdcl_twl_o_twl_struct_invs twl)

lemma rtranclp_cdcl_twl_stgy_twl_struct_invs:
  assumes
    cdcl: \<open>cdcl_twl_stgy\<^sup>*\<^sup>* S T\<close> and
    twl: \<open>twl_struct_invs S\<close>
  shows \<open>twl_struct_invs T\<close>
  using cdcl by (induction rule: rtranclp_induct) (simp_all add: cdcl_twl_stgy_twl_struct_invs twl)

lemma rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy:
  assumes \<open>cdcl_twl_stgy\<^sup>*\<^sup>* S T\<close> and twl: \<open>twl_struct_invs S\<close>
  shows \<open>pcdcl_tcore_stgy\<^sup>*\<^sup>* (pstate\<^sub>W_of S) (pstate\<^sub>W_of T)\<close>
  using assms by (induction rule: rtranclp_induct)
    (auto dest!: cdcl_twl_stgy_cdcl\<^sub>W_stgy intro: rtranclp_cdcl_twl_stgy_twl_struct_invs)

lemma no_step_cdcl_twl_cp_no_step_cdcl\<^sub>W_cp:
  assumes ns_cp: \<open>no_step cdcl_twl_cp S\<close> and twl: \<open>twl_struct_invs S\<close>
  shows \<open>literals_to_update S = {#} \<and> clauses_to_update S = {#}\<close>
proof (cases \<open>get_conflict S\<close>)
  case (Some a)
  then show ?thesis
    using twl unfolding twl_struct_invs_def by simp
next
  case None note confl = this(1)
  then obtain M N U UE NE NS US N0 U0 WS Q where S: \<open>S = (M, N, U, None, NE, UE, NS, US, N0, U0, WS, Q)\<close>
    by (cases S) auto
  have valid: \<open>valid_enqueued S\<close> and twl: \<open>twl_st_inv S\<close>
    using twl unfolding twl_struct_invs_def by fast+
  have wq: \<open>clauses_to_update S = {#}\<close>
  proof (rule ccontr)
    assume \<open>clauses_to_update S \<noteq> {#}\<close>
    then obtain L C WS' where LC: \<open>(L, C) \<in># clauses_to_update S\<close> and
      WS': \<open>WS = add_mset (L, C) WS'\<close>
      by (cases WS) (auto simp: S)

    have C_N_U: \<open>C \<in># N + U\<close> and L_C: \<open>L \<in># watched C\<close> and uL_M: \<open>- L \<in> lits_of_l M\<close>
      using valid LC unfolding S by auto

    have \<open>struct_wf_twl_cls C\<close>
      using C_N_U twl unfolding S by (auto simp: twl_st_inv.simps)
    then obtain L' where watched: \<open>watched C = {#L, L'#}\<close>
      using L_C by (cases C) (auto simp: size_2_iff)
    then have \<open>L \<in># clause C\<close>
      by (cases C) auto
    then have L'_M: \<open>L' \<notin> lits_of_l M\<close>
      using cdcl_twl_cp.delete_from_working[of L' C M N U NE UE NS US N0 U0 L WS' Q] watched
      ns_cp unfolding S WS' by (cases C) auto
    then have \<open>undefined_lit M L' \<or> -L' \<in> lits_of_l M\<close>
      using Decided_Propagated_in_iff_in_lits_of_l by blast
    then have \<open>\<not> (\<forall>L \<in># unwatched C. -L \<in> lits_of_l M)\<close>
      using cdcl_twl_cp.conflict[of C L L' M N U NE UE NS US N0 U0 WS' Q]
        cdcl_twl_cp.propagate[of C L L' M N U NE UE NS US N0 U0 WS' Q] watched
      ns_cp unfolding S WS' by fast
    then obtain K where K: \<open>K \<in># unwatched C\<close> and uK_M: \<open>-K \<notin> lits_of_l M\<close>
      by auto
    then have undef_K_K_M: \<open>undefined_lit M K \<or> K \<in> lits_of_l M\<close>
      using Decided_Propagated_in_iff_in_lits_of_l by blast
    define NU where \<open>NU = (if C \<in># N then (add_mset (update_clause C L K) (remove1_mset C N), U)
      else (N, add_mset (update_clause C L K) (remove1_mset C U)))\<close>
    have upd: \<open>update_clauses (N, U) C L K NU\<close>
      using C_N_U unfolding NU_def by (auto simp: update_clauses.intros)
    have NU: \<open>NU = (fst NU, snd NU)\<close>
      by simp
    show False
      using cdcl_twl_cp.update_clause[of C L L' M K N U \<open>fst NU\<close> \<open>snd NU\<close> NE UE NS US N0 U0 WS' Q]
      watched uL_M L'_M K undef_K_K_M upd ns_cp unfolding S WS' by simp
  qed
  then have p: \<open>literals_to_update S = {#}\<close>
    using cdcl_twl_cp.pop[of M N U NE UE] S ns_cp by (cases \<open>Q\<close>) fastforce+
  show ?thesis using wq p by blast
qed

lemma no_step_cdcl_twl_o_no_step_cdcl\<^sub>W_o:
  assumes
    ns_o: \<open>no_step cdcl_twl_o S\<close> and
    twl: \<open>twl_struct_invs S\<close> and
    p: \<open>literals_to_update S = {#}\<close> and
    w_q: \<open>clauses_to_update S = {#}\<close>
  shows \<open>no_step cdcl_decide (pstate\<^sub>W_of S) \<and> no_step cdcl_skip (pstate\<^sub>W_of S) \<and>
     no_step cdcl_resolve (pstate\<^sub>W_of S) \<and> no_step cdcl_backtrack (pstate\<^sub>W_of S)\<close>
proof (rule ccontr)
  obtain M N U D NE UE NS US N0 U0 where S: \<open>S = (M, N, U, D, NE, UE, NS, US, N0, U0, {#}, {#})\<close>
    using p w_q by (cases S) auto
  assume \<open>\<not> ?thesis\<close>
  then consider
    (decide) T where \<open>cdcl_decide (pstate\<^sub>W_of S) T\<close> |
    (skip) T where \<open>cdcl_skip (pstate\<^sub>W_of S) T\<close> |
    (resolve) T where \<open>cdcl_resolve (pstate\<^sub>W_of S) T\<close> |
    (backtrack) T where \<open>cdcl_backtrack (pstate\<^sub>W_of S) T\<close>
    by blast
  then show False
  proof (cases)
    case (decide T)
    then show ?thesis
      apply (cases rule: cdcl_decide.cases)
      subgoal for M' L' N' NE' NS' U' UE' US'
        using cdcl_twl_o.decide[of M L' N NE NS N0 U UE US U0] ns_o unfolding S
        by (auto simp: cdcl\<^sub>W_restart_mset_state)
      done
  next
    case (skip T)
    then show ?thesis
      apply (cases rule: cdcl_skip.cases)
      subgoal for L E D M'
       using cdcl_twl_o.skip[of L E D M' N U NE UE NS US N0 U0] ns_o unfolding S
       by (auto simp: cdcl\<^sub>W_restart_mset_state)
      done
  next
    case (resolve T)
    then show ?thesis
      apply (cases rule: cdcl_resolve.cases)
      subgoal for L' D E M'
       using cdcl_twl_o.resolve[of L' D E M' N U NE UE NS US N0 U0] ns_o unfolding S
       by (auto simp: cdcl\<^sub>W_restart_mset_state)
      done
  next
    case (backtrack T)
    then show ?thesis
      apply (cases rule: cdcl_backtrack.cases)
      subgoal for K M1 M2 M L D' i C N' U' NE UE NS US N0 U0
        using cdcl_twl_o.backtrack_unit_clause[of L \<open>add_mset L C\<close> K M1 M2 M
            \<open>add_mset L D'\<close> i N U NE UE NS US N0 U0]
        using cdcl_twl_o.backtrack_nonunit_clause[of L \<open>add_mset L C\<close> K M1 M2 M \<open>add_mset L D'\<close>
            i N U NE UE NS US N0 U0] ns_o get_maximum_level_exists_lit_of_max_level[of D' M]
        unfolding S
        by (cases \<open>D' \<noteq> {#}\<close>) auto
      done
  qed
qed

lemma no_step_cdcl_twl_stgy_no_step_cdcl\<^sub>W_stgy:
  assumes ns: \<open>no_step cdcl_twl_stgy S\<close> and twl: \<open>twl_struct_invs S\<close>
  shows \<open>no_step pcdcl_core_stgy (pstate\<^sub>W_of S)\<close>
proof -
  have ns_cp: \<open>no_step cdcl_twl_cp S\<close> and ns_o: \<open>no_step cdcl_twl_o S\<close>
    using ns by (auto simp: cdcl_twl_stgy.simps)
  then have w_q: \<open>clauses_to_update S = {#}\<close> and p: \<open>literals_to_update S = {#}\<close>
    using ns_cp no_step_cdcl_twl_cp_no_step_cdcl\<^sub>W_cp twl by blast+
  then have
    \<open>no_step cdcl_propagate (pstate\<^sub>W_of S)\<close> and
    \<open>no_step cdcl_conflict (pstate\<^sub>W_of S)\<close>
    using no_literals_to_update_no_cp twl by blast+
  moreover have \<open>no_step cdcl_decide (pstate\<^sub>W_of S) \<and> no_step cdcl_skip (pstate\<^sub>W_of S) \<and>
     no_step cdcl_resolve (pstate\<^sub>W_of S) \<and> no_step cdcl_backtrack (pstate\<^sub>W_of S)\<close>
    using w_q p ns_o no_step_cdcl_twl_o_no_step_cdcl\<^sub>W_o twl by blast
  ultimately show ?thesis
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.simps pcdcl_core_stgy.simps)
qed

text \<open>This where things get different from the direct inheritance from CDCL. Originally,
  we had the following theorem:
\<close>
lemma full_cdcl_twl_stgy_cdcl\<^sub>W_stgy: (* \htmllink{full_cdcl_twl_stgy_cdclW_stgy_old} *)
  assumes \<open>full cdcl_twl_stgy S T\<close> and twl: \<open>twl_struct_invs S\<close>
  shows \<open>full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (state\<^sub>W_of S) (state\<^sub>W_of T)\<close>
  oops

text \<open>However, now we have to split the steps part from the end part.\<close>


lemma full_cdcl_twl_stgy_cdcl\<^sub>W_stgy: (* \htmllink{full_cdcl_twl_stgy_cdclW_stgy} *)
  assumes \<open>full cdcl_twl_stgy S T\<close> and twl: \<open>twl_struct_invs S\<close>
  shows \<open>full2 pcdcl_tcore_stgy pcdcl_core (pstate\<^sub>W_of S) (pstate\<^sub>W_of T)\<close>
  using assms
  unfolding full2_def full_def
  by (meson no_step_cdcl_twl_stgy_no_step_cdcl\<^sub>W_stgy pcdcl_core.simps pcdcl_core_stgy.simps
    rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy rtranclp_cdcl_twl_stgy_twl_struct_invs)



definition init_state_twl where
  \<open>init_state_twl N \<equiv> ([], N, {#}, None, {#}, {#}, {#}, {#}, {#}, {#}, {#}, {#})\<close>
lemma
  assumes
    struct: \<open>\<forall>C \<in># N. struct_wf_twl_cls C\<close> and
    tauto: \<open>\<forall>C \<in># N. \<not>tautology (clause C)\<close>
  shows
    twl_stgy_invs_init_state_twl: \<open>twl_stgy_invs (init_state_twl N)\<close> and
    twl_struct_invs_init_state_twl: \<open>twl_struct_invs (init_state_twl N)\<close>
proof -
  have [simp]: \<open>twl_lazy_update [] C\<close> \<open>watched_literals_false_of_max_level [] C\<close>
    \<open>twl_exception_inv ([], N, {#}, None, {#}, {#}, {#}, {#}, {#}, {#}, {#}, {#}) C\<close> for C
    by (cases C; solves \<open>auto simp: twl_exception_inv.simps\<close>)+

  have size_C: \<open>size (clause C) \<ge> 2\<close> if \<open>C \<in># N\<close> for C
  proof -
    have \<open>struct_wf_twl_cls C\<close>
      using that struct by auto
    then show ?thesis by (cases C) auto
  qed
  have
    [simp]: \<open>clause C \<noteq> {#}\<close> (is ?G1) and
    [simp]: \<open>remove1_mset L (clause C) \<noteq> {#}\<close> (is ?G2) if \<open>C \<in># N\<close> for C L
    by (rule size_neq_size_imp_neq[of _ \<open>{#}\<close>]; use size_C[OF that] in
        \<open>auto simp: remove1_mset_empty_iff union_is_single\<close>)+

  have \<open>distinct_mset (clause C)\<close> if \<open>C \<in># N\<close> for C
    using struct that by (cases C) (auto)
  then have dist: \<open>distinct_mset_mset (clause `# N)\<close>
    by (auto simp: distinct_mset_set_def)
  then have [simp]: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv ([], clause `# N, {#}, None)\<close>
    using struct unfolding init_state.simps[symmetric] cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.no_strange_atm_S0
     by (simp only: cdcl\<^sub>W_restart_mset.no_strange_atm_S0
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_S0_cdcl\<^sub>W_restart
       cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_S0_cdcl\<^sub>W_restart[OF dist]
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_S0_cdcl\<^sub>W_restart dist
       cdcl\<^sub>W_restart_mset.all_invariant_S0_cdcl\<^sub>W_restart
       cdcl\<^sub>W_restart_mset.all_invariant_S0_cdcl\<^sub>W_restart(1)[OF dist], simp)

  have [simp]: \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa ([], clause `# N, {#}, None)\<close>
    by(auto simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def cdcl\<^sub>W_restart_mset_state)
  have [simp]: \<open>entailed_clss_inv ([], clauses N, {#}, None, {#}, {#}, {#}, {#}, {#}, {#})\<close>
      \<open>psubsumed_invs ([], clauses N, {#}, None, {#}, {#}, {#}, {#}, {#}, {#})\<close>
    by (auto simp: entailed_clss_inv_def psubsumed_invs_def)
  show stgy_invs: \<open>twl_stgy_invs (init_state_twl N)\<close>
    by (auto simp: twl_stgy_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
        cdcl\<^sub>W_restart_mset.conflict_non_zero_unless_level_0_def
        cdcl\<^sub>W_restart_mset_state cdcl\<^sub>W_restart_mset.no_smaller_confl_def init_state_twl_def)
  show \<open>twl_struct_invs (init_state_twl N)\<close>
    using struct tauto
    by (auto simp: twl_struct_invs_def twl_st_inv.simps clauses_to_update_prop.simps
        past_invs.simps cdcl\<^sub>W_restart_mset_state init_state_twl_def clauses0_inv_def
        cdcl\<^sub>W_restart_mset.no_strange_atm_def pcdcl_all_struct_invs_def)
qed


lemma cdcl_twl_o_cdcl\<^sub>W_o_stgy:
  assumes
    cdcl: \<open>cdcl_twl_o S T\<close> and
    inv: \<open>twl_struct_invs S\<close>
  shows \<open>pcdcl_tcore_stgy (pstate\<^sub>W_of S) (pstate\<^sub>W_of T)\<close>
  using cdcl inv
proof (induction rule: cdcl_twl_o.induct)
  case (decide M L N NE NS N0 U UE US U0) note undef = this(1) and atm = this(2) and inv = this(3)
  have 0: \<open>cdcl_decide (pstate\<^sub>W_of (M, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#}))
    (pstate\<^sub>W_of (Decided L # M, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#-L#}))\<close>
    unfolding pstate\<^sub>W_of.simps
    apply (rule cdcl_decide.intros)
      using undef apply (simp add: trail.simps; fail)
     using atm apply (simp add: cdcl\<^sub>W_restart_mset_state; fail)
     done
  then show dec: ?case
    using no_literals_to_update_no_cp[of \<open>(M, N, U, None, NE, UE, NS, US, N0, U0, {#}, {#})\<close>] inv
     by (auto dest: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o.intros pcdcl_core.intros simp: pcdcl_tcore_stgy.simps
       pcdcl_core_stgy.simps)
next
  case (skip L D C' M N U NE UE NS US N0 U0) note LD = this(1) and D = this(2) and inv = this(3)
  have skip': \<open>cdcl_skip (pstate\<^sub>W_of (Propagated L C' # M, N, U, Some D, NE, UE, NS, US, N0, U0, {#}, {#}))
     (pstate\<^sub>W_of (M, N, U, Some D, NE, UE, NS, US, N0, U0, {#}, {#}))\<close>
    unfolding pstate\<^sub>W_of.simps
    apply (rule cdcl_skip.intros)
      using LD apply (simp; fail)
     using D apply (simp; fail)
    done
  show ?case
    by (rule pcdcl_tcore_stgy.intros(1), rule pcdcl_core_stgy.intros(4)) (rule skip')
next
  case (resolve L D C M N U NE UE NS US N0 U0) note LD = this(1) and lev = this(2) and inv = this(3)
  have \<open>\<forall>La mark a b. a @ Propagated La mark # b = Propagated L C # M \<longrightarrow>
      b \<Turnstile>as CNot (remove1_mset La mark) \<and> La \<in># mark\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
     cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def twl_struct_invs_def pcdcl_all_struct_invs_def
    by (auto simp: trail.simps)
  then have LC: \<open>L \<in># C\<close>
    by blast
  have resolve: \<open>cdcl_resolve (pstate\<^sub>W_of (Propagated L C # M, N, U, Some D, NE, UE, NS, US, N0, U0, {#}, {#}))
     (pstate\<^sub>W_of
       (M, N, U, Some (remove1_mset (- L) D \<union># remove1_mset L C), NE, UE, NS, US, N0, U0, {#}, {#}))\<close>
    unfolding pstate\<^sub>W_of.simps
    apply (rule cdcl_resolve.intros)
     using LD apply (simp; fail)
     using lev apply (simp add: cdcl\<^sub>W_restart_mset_state; fail)
     using LC apply (simp add: trail.simps; fail)
     done
  show ?case
    by (rule pcdcl_tcore_stgy.intros(1), rule pcdcl_core_stgy.intros(5))
      (rule resolve)
next
  case (backtrack_unit_clause L D K M1 M2 M D' i N U NE UE NS US N0 U0) note L_D = this(1) and
     decomp = this(2) and lev_L = this(3) and max_D'_L = this(4) and lev_D = this(5) and
     lev_K = this(6) and D'_D = this(8) and NU_D' = this(9) and
     D'[simp] = this(7) and inv = this(10)
  have D: \<open>D = add_mset L (remove1_mset L D)\<close>
    using L_D by auto
  have bt: \<open>cdcl_backtrack_unit (pstate\<^sub>W_of (M, N, U, Some D, NE, UE, NS, US, N0, U0, {#}, {#}))
     (pstate\<^sub>W_of
       (Propagated L {#L#} # M1, N, U, None, NE, add_mset {#L#} UE, NS, US, N0, U0, {#}, {#- L#}))\<close>
    unfolding pstate\<^sub>W_of.simps
    apply (subst D)
    apply (rule cdcl_backtrack_unit.intros)
    using backtrack_unit_clause by auto
  then show ?case
    by (rule pcdcl_tcore_stgy.intros(4))
next
  case (backtrack_nonunit_clause L D K M1 M2 M D' i N U NE UE NS US N0 U0 L') note LD = this(1) and
    decomp = this(2) and lev_L = this(3) and max_lev = this(4) and i = this(5) and lev_K = this(6)
    and D'_D = this(8) and NU_D' = this(9) and L_D' = this(10) and L' = this(11-12) and
    inv = this(13)
  let ?S = \<open>state\<^sub>W_of (M, N, U, Some D, NE, UE, NS, US, N0, U0, {#}, {#})\<close>
  let ?T = \<open>state\<^sub>W_of (Propagated L D # M1, N, U, None, NE, add_mset {#L#} UE, NS, US, N0, U0, {#}, {#L#})\<close>
  have n_d: \<open>no_dup M\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def twl_struct_invs_def pcdcl_all_struct_invs_def
    by (simp add: cdcl\<^sub>W_restart_mset_state)
  have \<open>undefined_lit M1 L\<close>
    apply (rule cdcl\<^sub>W_restart_mset.backtrack_lit_skiped[of ?S _ K _ M2 i])
    subgoal
      using lev_L inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
      by (simp add: cdcl\<^sub>W_restart_mset_state; fail)
    subgoal using decomp by (simp add: trail.simps; fail)
    subgoal using lev_L inv
      unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
         twl_struct_invs_def pcdcl_all_struct_invs_def
      by (simp add: cdcl\<^sub>W_restart_mset_state; fail)
   subgoal using lev_K by (simp add: trail.simps; fail)
   done
  obtain M3 where M3: \<open>M = M3 @ M2 @ Decided K # M1\<close>
    using decomp by (blast dest!: get_all_ann_decomposition_exists_prepend)

  have \<open>undefined_lit (M3 @ M2) K\<close>
    using n_d unfolding M3 by (auto simp: lits_of_def)
  then have count_M1: \<open>count_decided M1 = i\<close>
    using lev_K unfolding M3 by (auto simp: image_Un)
  have \<open>L \<noteq> L'\<close>
    using L' lev_L lev_K count_decided_ge_get_level[of M K] L' by auto
  then have D: \<open>add_mset L (add_mset L' (D' - {#L, L'#})) = D'\<close>
    using L' L_D'
    by (metis add_mset_diff_bothsides diff_single_eq_union insert_noteq_member mset_add)
  then have D4: \<open>({#L, L'#} + (D' - {#L, L'#})) = add_mset L (add_mset L' (D' - {#L, L'#}))\<close>
    by auto
  have D': \<open>remove1_mset L D' = add_mset L' (D' - {#L, L'#})\<close>
    by (subst D[symmetric]) auto
  have D'': \<open>D = add_mset L (remove1_mset L D)\<close>
    using L_D' D'_D by auto
  show ?case
    apply (subst D[symmetric])
    apply (subst D'')
    apply (rule pcdcl_tcore_stgy.intros(1), rule pcdcl_core_stgy.intros(6))
    unfolding pstate\<^sub>W_of.simps image_mset_add_mset clause.simps D4
    apply (rule cdcl_backtrack.intros[of K M1 M2 _ _ _ i])
    subgoal using decomp by (simp add: trail.simps)
    subgoal using lev_L by (simp add: cdcl\<^sub>W_restart_mset_state; fail)
    subgoal using max_lev L_D' by (simp add: cdcl\<^sub>W_restart_mset_state get_maximum_level_add_mset D)
    subgoal using i by (simp add: cdcl\<^sub>W_restart_mset_state D')
    subgoal using lev_K i unfolding D' by (simp add: trail.simps)
    subgoal using D'_D by (metis D' mset_le_subtract)
    subgoal using NU_D' L_D' by (simp add: mset_le_subtract clauses_def ac_simps D)
    done
qed

lemma pcdcl_tcore_stgy_conflict_non_zero_unless_level_0:
  \<open>pcdcl_tcore_stgy S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.conflict_non_zero_unless_level_0 (state_of S) \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state_of S) \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.conflict_non_zero_unless_level_0 (state_of T)\<close>
  apply (induction rule: pcdcl_tcore_stgy.induct)
  subgoal
    using pcdcl_core_is_cdcl[of S T]
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart_conflict_non_zero_unless_level_0[of \<open>state_of S\<close> \<open>state_of T\<close>]
    by (auto dest!: pcdcl_core_stgy_pcdcl cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_cdcl\<^sub>W_restart)
  subgoal
     by (auto simp: cdcl_subsumed.simps cdcl\<^sub>W_restart_mset.conflict_non_zero_unless_level_0_def)
  subgoal
     by (auto simp: cdcl_flush_unit.simps cdcl\<^sub>W_restart_mset.conflict_non_zero_unless_level_0_def)
   subgoal
     by (metis cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart_conflict_non_zero_unless_level_0
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_cdcl\<^sub>W_restart cdcl_backtrack_unit_is_backtrack
       cdcl_flush_unit_unchanged pcdcl_core.intros(6) pcdcl_core_is_cdcl)
  done

lemma cdcl_twl_o_twl_stgy_invs:
  \<open>cdcl_twl_o S T \<Longrightarrow> twl_struct_invs S \<Longrightarrow> twl_stgy_invs S \<Longrightarrow> twl_stgy_invs T\<close>
  using cdcl_twl_o_cdcl\<^sub>W_o_stgy[of S T]
    pcdcl_tcore_stgy_conflict_non_zero_unless_level_0[of \<open>pstate\<^sub>W_of S\<close> \<open>pstate\<^sub>W_of T\<close>]
  by (auto simp:  twl_struct_invs_def twl_stgy_invs_def pcdcl_all_struct_invs_def
    intro!: rtranclp_pcdcl_stgy_stgy_invariant[of \<open>pstate\<^sub>W_of S\<close> \<open>pstate\<^sub>W_of T\<close>]
    dest: pcdcl_tcore_stgy_pcdcl_stgy')


paragraph \<open>Well-foundedness\<close>

lemma wf_cdcl\<^sub>W_stgy_state\<^sub>W_of:
  \<open>wf {(T, S). pcdcl_all_struct_invs (pstate\<^sub>W_of S) \<and> pcdcl_tcore (pstate\<^sub>W_of S) (pstate\<^sub>W_of T)}\<close>
  using wf_if_measure_f[OF wf_pcdcl_tcore, of pstate\<^sub>W_of] by simp

lemma wf_cdcl_twl_cp:
  \<open>wf {(T, S). twl_struct_invs S \<and> cdcl_twl_cp S T}\<close> (is \<open>wf ?TWL\<close>)
proof -
  let ?CDCL = \<open>{(T, S). pcdcl_all_struct_invs (pstate\<^sub>W_of S) \<and>
      pcdcl_tcore (pstate\<^sub>W_of S) (pstate\<^sub>W_of T)}\<close>
  let ?P = \<open>{(T, S). pstate\<^sub>W_of S = pstate\<^sub>W_of T \<and>
    (literals_to_update_measure T, literals_to_update_measure S) \<in> lexn less_than 2}\<close>

  have wf_p_m:
    \<open>wf {(T, S). (literals_to_update_measure T, literals_to_update_measure S) \<in> lexn less_than 2}\<close>
    using wf_if_measure_f[of \<open>lexn less_than 2\<close> literals_to_update_measure] by (auto simp: wf_lexn)
  have \<open>wf ?CDCL\<close>
    by (rule wf_subset[OF wf_cdcl\<^sub>W_stgy_state\<^sub>W_of])
      (auto simp: twl_struct_invs_def)
  moreover have \<open>wf ?P\<close>
    by (rule wf_subset[OF wf_p_m]) auto
  moreover have \<open>?CDCL O ?P \<subseteq> ?CDCL\<close> by auto
  ultimately have \<open>wf (?CDCL \<union> ?P)\<close>
    by (rule wf_union_compatible)

  moreover have \<open>?TWL \<subseteq> ?CDCL \<union> ?P\<close>
  proof
    fix x
    assume x_TWL: \<open>x \<in> ?TWL\<close>
    then obtain S T where x: \<open>x = (T, S)\<close> by auto

    have twl: \<open>twl_struct_invs S\<close> and cdcl: \<open>cdcl_twl_cp S T\<close>
      using x_TWL x by auto
    have \<open>pcdcl_all_struct_invs (pstate\<^sub>W_of S)\<close>
      using twl by (auto simp: twl_struct_invs_def)
    moreover have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S)\<close>
      using twl by (auto simp: twl_struct_invs_def pcdcl_all_struct_invs_def)
    moreover have \<open>pcdcl_tcore (pstate\<^sub>W_of S) (pstate\<^sub>W_of T) \<or>
      (pstate\<^sub>W_of S = pstate\<^sub>W_of T \<and>
        (literals_to_update_measure T, literals_to_update_measure S) \<in> lexn less_than 2)\<close>
      using calculation cdcl cdcl_twl_cp_cdcl\<^sub>W_stgy[of S T] twl apply (auto simp: pcdcl_tcore.intros
          pcdcl_tcore_stgy.simps twl_cp_propagate_or_conflict pcdcl_core.intros
        dest: pcdcl_core_stgy_pcdcl)
     using calculation pcdcl_core.intros(1,2) pcdcl_tcore.intros(1) twl_cp_propagate_or_conflict
       twl_struct_invs_def by blast

    ultimately show \<open>x \<in> ?CDCL \<union> ?P\<close>
      unfolding x by auto
  qed
  ultimately show ?thesis
    using wf_subset[of \<open>?CDCL \<union> ?P\<close>] by blast
qed

lemma tranclp_wf_cdcl_twl_cp:
  \<open>wf {(T, S). twl_struct_invs S \<and> cdcl_twl_cp\<^sup>+\<^sup>+ S T}\<close>
proof -
  have H: \<open>{(T, S). twl_struct_invs S \<and> cdcl_twl_cp\<^sup>+\<^sup>+ S T} \<subseteq>
     {(T, S). twl_struct_invs S \<and> cdcl_twl_cp S T}\<^sup>+\<close>
  proof -
    { fix T S :: \<open>'v twl_st\<close>
      assume \<open>cdcl_twl_cp\<^sup>+\<^sup>+ S T\<close> \<open>twl_struct_invs S\<close>
      then have \<open>(T, S) \<in> {(T, S). twl_struct_invs S \<and> cdcl_twl_cp S T}\<^sup>+\<close> (is \<open>_ \<in> ?S\<^sup>+\<close>)
      proof (induction rule: tranclp_induct)
        case (base y)
        then show ?case by auto
      next
        case (step T U) note st = this(1) and cp = this(2) and IH = this(3)[OF this(4)] and
          twl = this(4)
        have \<open>twl_struct_invs T\<close>
          by (metis (no_types, lifting) IH Nitpick.tranclp_unfold cdcl_twl_cp_twl_struct_invs
           converse_tranclpE)
        then have \<open>(U, T) \<in> ?S\<^sup>+\<close>
          using cp by auto
        then show ?case using IH by auto
      qed
    }
    then show ?thesis by blast
  qed
  show ?thesis using wf_trancl[OF wf_cdcl_twl_cp]  wf_subset[OF _ H] by blast
qed

lemma wf_cdcl_twl_stgy:
  \<open>wf {(T, S). twl_struct_invs S \<and> cdcl_twl_stgy S T}\<close> (is \<open>wf ?TWL\<close>)
proof -
  let ?CDCL = \<open>{(T, S). pcdcl_all_struct_invs (pstate\<^sub>W_of S) \<and>
      pcdcl_tcore (pstate\<^sub>W_of S) (pstate\<^sub>W_of T)}\<close>
  let ?P = \<open>{(T, S). pstate\<^sub>W_of S = pstate\<^sub>W_of T \<and>
    (literals_to_update_measure T, literals_to_update_measure S) \<in> lexn less_than 2}\<close>

  have wf_p_m:
    \<open>wf {(T, S). (literals_to_update_measure T, literals_to_update_measure S) \<in> lexn less_than 2}\<close>
    using wf_if_measure_f[of \<open>lexn less_than 2\<close> literals_to_update_measure] by (auto simp: wf_lexn)
  have \<open>wf ?CDCL\<close>
    by (rule wf_subset[OF wf_cdcl\<^sub>W_stgy_state\<^sub>W_of])
      (auto simp: twl_struct_invs_def)
  moreover have \<open>wf ?P\<close>
    by (rule wf_subset[OF wf_p_m]) auto
  moreover have \<open>?CDCL O ?P \<subseteq> ?CDCL\<close>
    by auto
  ultimately have \<open>wf (?CDCL \<union> ?P)\<close>
    by (rule wf_union_compatible)

  moreover have \<open>?TWL \<subseteq> ?CDCL \<union> ?P\<close>
  proof
    fix x
    assume x_TWL: \<open>x \<in> ?TWL\<close>
    then obtain S T where x: \<open>x = (T, S)\<close> by auto

    have twl: \<open>twl_struct_invs S\<close> and cdcl: \<open>cdcl_twl_stgy S T\<close>
      using x_TWL x by auto
    have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S)\<close> and
       \<open>pcdcl_all_struct_invs (pstate\<^sub>W_of S)\<close>
      using twl by (auto simp: twl_struct_invs_def pcdcl_all_struct_invs_def)
    moreover have \<open>pcdcl_tcore (pstate\<^sub>W_of S) (pstate\<^sub>W_of T) \<or>
      (pstate\<^sub>W_of S = pstate\<^sub>W_of T \<and>
         (literals_to_update_measure T, literals_to_update_measure S) \<in> lexn less_than 2)\<close>
      using cdcl cdcl_twl_stgy_cdcl\<^sub>W_stgy2[OF cdcl twl] by (auto simp: pcdcl_core_stgy_pcdcl
        pcdcl_tcore.simps pcdcl_tcore_stgy.simps)
    ultimately show \<open>x \<in> ?CDCL \<union> ?P\<close>
      unfolding x by blast
  qed
  ultimately show ?thesis
    using wf_subset[of \<open>?CDCL \<union> ?P\<close>] by blast
qed

lemma tranclp_wf_cdcl_twl_stgy:
  \<open>wf {(T, S). twl_struct_invs S \<and> cdcl_twl_stgy\<^sup>+\<^sup>+ S T}\<close>
proof -
  have H: \<open>{(T, S). twl_struct_invs S \<and> cdcl_twl_stgy\<^sup>+\<^sup>+ S T} \<subseteq>
     {(T, S). twl_struct_invs S \<and> cdcl_twl_stgy S T}\<^sup>+\<close>
  proof -
    { fix T S :: \<open>'v twl_st\<close>
      assume \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ S T\<close> \<open>twl_struct_invs S\<close>
      then have \<open>(T, S) \<in> {(T, S). twl_struct_invs S \<and> cdcl_twl_stgy S T}\<^sup>+\<close> (is \<open>_ \<in> ?S\<^sup>+\<close>)
      proof (induction rule: tranclp_induct)
        case (base y)
        then show ?case by auto
      next
        case (step T U) note st = this(1) and stgy = this(2) and IH = this(3)[OF this(4)] and
          twl = this(4)
        have \<open>twl_struct_invs T\<close>
          by (metis (no_types, lifting) IH Nitpick.tranclp_unfold cdcl_twl_stgy_twl_struct_invs
           converse_tranclpE)
        then have \<open>(U, T) \<in> ?S\<^sup>+\<close>
          using stgy by auto
        then show ?case using IH by auto
      qed
    }
    then show ?thesis by blast
  qed
  show ?thesis using wf_trancl[OF wf_cdcl_twl_stgy]  wf_subset[OF _ H] by blast
qed

lemma rtranclp_cdcl_twl_o_stgyD: \<open>cdcl_twl_o\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl_twl_stgy\<^sup>*\<^sup>* S T\<close>
  using rtranclp_mono[of cdcl_twl_o cdcl_twl_stgy] cdcl_twl_stgy.intros(2)
  by blast

lemma rtranclp_cdcl_twl_cp_stgyD: \<open>cdcl_twl_cp\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl_twl_stgy\<^sup>*\<^sup>* S T\<close>
  using rtranclp_mono[of cdcl_twl_cp cdcl_twl_stgy] cdcl_twl_stgy.intros(1)
  by blast

lemma tranclp_cdcl_twl_o_stgyD: \<open>cdcl_twl_o\<^sup>+\<^sup>+ S T \<Longrightarrow> cdcl_twl_stgy\<^sup>+\<^sup>+ S T\<close>
  using tranclp_mono[of cdcl_twl_o cdcl_twl_stgy] cdcl_twl_stgy.intros(2)
  by blast

lemma tranclp_cdcl_twl_cp_stgyD: \<open>cdcl_twl_cp\<^sup>+\<^sup>+ S T \<Longrightarrow> cdcl_twl_stgy\<^sup>+\<^sup>+ S T\<close>
  using tranclp_mono[of cdcl_twl_cp cdcl_twl_stgy] cdcl_twl_stgy.intros(1)
  by blast

lemma wf_cdcl_twl_o:
  \<open>wf {(T, S::'v twl_st). twl_struct_invs S \<and> cdcl_twl_o S T}\<close>
  by (rule wf_subset[OF wf_cdcl_twl_stgy]) (auto intro: cdcl_twl_stgy.intros)

lemma tranclp_wf_cdcl_twl_o:
  \<open>wf {(T, S::'v twl_st). twl_struct_invs S \<and> cdcl_twl_o\<^sup>+\<^sup>+ S T}\<close>
  by (rule wf_subset[OF tranclp_wf_cdcl_twl_stgy]) (auto dest: tranclp_cdcl_twl_o_stgyD)

lemma (in -)propa_cands_enqueued_mono:
  \<open>U' \<subseteq># U \<Longrightarrow> N' \<subseteq># N \<Longrightarrow>
     propa_cands_enqueued  (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q) \<Longrightarrow>
      propa_cands_enqueued  (M, N', U', D, NE', UE', NS, US, N0, U0, WS, Q)\<close>
  by (cases D) (auto 5 5)

lemma (in -)confl_cands_enqueued_mono:
  \<open>U' \<subseteq># U \<Longrightarrow> N' \<subseteq># N \<Longrightarrow>
     confl_cands_enqueued  (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q) \<Longrightarrow>
      confl_cands_enqueued  (M, N', U', D, NE', UE', NS, US, N0, U0, WS, Q)\<close>
  by (cases D) auto

lemma (in -)twl_st_exception_inv_mono:
  \<open>U' \<subseteq># U \<Longrightarrow> N' \<subseteq># N \<Longrightarrow>
     twl_st_exception_inv  (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q) \<Longrightarrow>
      twl_st_exception_inv  (M, N', U', D, NE', UE', NS, US, N0, U0, WS, Q)\<close>
  by (cases D) (fastforce simp: twl_exception_inv.simps)+

lemma (in -)twl_st_inv_mono:
  \<open>U' \<subseteq># U \<Longrightarrow> N' \<subseteq># N \<Longrightarrow>
     twl_st_inv (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q) \<Longrightarrow>
      twl_st_inv (M, N', U', D, NE', UE', NS, US, N0, U0, WS, Q)\<close>
  by (cases D) (fastforce simp: twl_st_inv.simps)+

lemma (in -)propa_cands_enqueued_subsumed_mono:
  \<open>US' \<subseteq># US \<Longrightarrow>
     propa_cands_enqueued  (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q) \<Longrightarrow>
      propa_cands_enqueued  (M, N, U, D, NE, UE, NS, US', N0, U0, WS, Q)\<close>
  by (cases D) (auto 5 5)

lemma (in -)confl_cands_enqueued_subsumed_mono:
  \<open>US' \<subseteq># US \<Longrightarrow>
     confl_cands_enqueued  (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q) \<Longrightarrow>
      confl_cands_enqueued  (M, N, U, D, NE, UE, NS, US', N0, U0, WS, Q)\<close>
  by (cases D) auto

lemma (in -)twl_st_exception_inv_subsumed_mono:
  \<open>US' \<subseteq># US \<Longrightarrow>
     twl_st_exception_inv  (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q) \<Longrightarrow>
      twl_st_exception_inv  (M, N, U, D, NE, UE, NS, US', N0, U0, WS, Q)\<close>
  by (cases D) (fastforce simp: twl_exception_inv.simps)+

lemma (in -)twl_st_inv_subsumed_mono:
  \<open>US' \<subseteq># US \<Longrightarrow>
     twl_st_inv (M, N, U, D, NE, UE, NS, US, N0, U0, WS, Q) \<Longrightarrow>
      twl_st_inv (M, N, U, D, NE, UE, NS, US', N0, U0, WS, Q)\<close>
  by (cases D) (fastforce simp: twl_st_inv.simps)+

lemma (in -) rtranclp_cdcl_twl_stgy_twl_stgy_invs:
  assumes
    \<open>cdcl_twl_stgy\<^sup>*\<^sup>* S T\<close> and
    \<open>twl_struct_invs S\<close> and
    \<open>twl_stgy_invs S\<close>
  shows \<open>twl_stgy_invs T\<close>
  using assms
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for T U
    using cdcl_twl_cp_twl_stgy_invs cdcl_twl_o_twl_stgy_invs cdcl_twl_stgy.simps
      rtranclp_cdcl_twl_stgy_twl_struct_invs by blast
  using assms cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_stgy_invariant
    rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy
  done


lemma cdcl_twl_stgy_get_init_learned_clss_mono:
  assumes \<open>cdcl_twl_stgy S T\<close>
  shows \<open>get_init_learned_clss S \<subseteq># get_init_learned_clss T\<close>
  using assms
  by induction (auto simp: cdcl_twl_cp.simps cdcl_twl_o.simps)

lemma rtranclp_cdcl_twl_stgy_get_init_learned_clss_mono:
  assumes \<open>cdcl_twl_stgy\<^sup>*\<^sup>* S T\<close>
  shows \<open>get_init_learned_clss S \<subseteq># get_init_learned_clss T\<close>
  using assms
  by induction (auto dest!: cdcl_twl_stgy_get_init_learned_clss_mono)

lemma cdcl_twl_o_all_learned_diff_learned:
  assumes \<open>cdcl_twl_o S T\<close>
  shows
    \<open>clause `# get_learned_clss S \<subseteq># clause `# get_learned_clss T \<and>
     get_init_learned_clss S \<subseteq># get_init_learned_clss T\<and>
     get_all_init_clss S = get_all_init_clss T\<close>
  by (use assms in \<open>induction rule: cdcl_twl_o.induct\<close>)
   (auto simp: update_clauses.simps size_Suc_Diff1)

lemma cdcl_twl_cp_all_learned_diff_learned:
  assumes \<open>cdcl_twl_cp S T\<close>
  shows
    \<open>clause `# get_learned_clss S = clause `# get_learned_clss T \<and>
     get_init_learned_clss S = get_init_learned_clss T \<and>
     get_all_init_clss S = get_all_init_clss T\<close>
  apply (use assms in \<open>induction rule: cdcl_twl_cp.induct\<close>)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal for D
    by (cases D)
      (auto simp: update_clauses.simps size_Suc_Diff1 dest!: multi_member_split)
  done

lemma cdcl_twl_stgy_all_learned_diff_learned:
  assumes \<open>cdcl_twl_stgy S T\<close>
  shows
    \<open>clause `# get_learned_clss S \<subseteq># clause `# get_learned_clss T \<and>
     get_init_learned_clss S \<subseteq># get_init_learned_clss T\<and>
     get_all_init_clss S = get_all_init_clss T\<close>
  by (use assms in \<open>induction rule: cdcl_twl_stgy.induct\<close>)
    (auto simp: cdcl_twl_cp_all_learned_diff_learned cdcl_twl_o_all_learned_diff_learned)

lemma rtranclp_cdcl_twl_stgy_all_learned_diff_learned:
  assumes \<open>cdcl_twl_stgy\<^sup>*\<^sup>* S T\<close>
  shows
    \<open>clause `# get_learned_clss S \<subseteq># clause `# get_learned_clss T \<and>
     get_init_learned_clss S \<subseteq># get_init_learned_clss T \<and>
     get_all_init_clss S = get_all_init_clss T\<close>
  by (use assms in \<open>induction rule: rtranclp_induct\<close>)
   (auto dest: cdcl_twl_stgy_all_learned_diff_learned)

lemma cdcl_twl_stgy_cdcl\<^sub>W_stgy3:
  assumes \<open>cdcl_twl_stgy S T\<close> and twl: \<open>twl_struct_invs S\<close> and
    \<open>clauses_to_update S = {#}\<close> and
    \<open>literals_to_update S = {#}\<close>
  shows \<open>pcdcl_tcore_stgy (pstate\<^sub>W_of S) (pstate\<^sub>W_of T)\<close>
  using cdcl_twl_stgy_cdcl\<^sub>W_stgy2[OF assms(1,2)] assms(3-)
  by (auto simp: lexn2_conv)

lemma tranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy:
  assumes ST: \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ S T\<close> and
    twl: \<open>twl_struct_invs S\<close> and
    \<open>clauses_to_update S = {#}\<close> and
    \<open>literals_to_update S = {#}\<close>
  shows \<open>pcdcl_tcore_stgy\<^sup>+\<^sup>+ (pstate\<^sub>W_of S) (pstate\<^sub>W_of T)\<close>
proof -
  obtain S' where
    SS': \<open>cdcl_twl_stgy S S'\<close> and
    S'T: \<open>cdcl_twl_stgy\<^sup>*\<^sup>* S' T\<close>
    using ST unfolding tranclp_unfold_begin by blast

  have 1: \<open>pcdcl_tcore_stgy (pstate\<^sub>W_of S) (pstate\<^sub>W_of S')\<close>
    using cdcl_twl_stgy_cdcl\<^sub>W_stgy3[OF SS' assms(2-4)]
    by blast
  have struct_S': \<open>twl_struct_invs S'\<close>
    using twl SS' by (blast intro: cdcl_twl_stgy_twl_struct_invs)
  have 2: \<open>pcdcl_tcore_stgy\<^sup>*\<^sup>* (pstate\<^sub>W_of S') (pstate\<^sub>W_of T)\<close>
    apply (rule rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy)
     apply (rule S'T)
    by (rule struct_S')
  show ?thesis
    using 1 2 by auto
qed


definition final_twl_state where
  \<open>final_twl_state S \<longleftrightarrow>
      no_step cdcl_twl_stgy S \<or> (get_conflict S \<noteq> None \<and> count_decided (get_trail S) = 0)\<close>

definition partial_conclusive_TWL_norestart_run :: \<open>'v twl_st \<Rightarrow> (bool \<times> 'v twl_st) nres\<close> where
  \<open>partial_conclusive_TWL_norestart_run S = SPEC(\<lambda>(b, T). b \<longrightarrow>   cdcl_twl_stgy\<^sup>*\<^sup>* S T \<and> final_twl_state T)\<close>

definition conclusive_TWL_norestart_run :: \<open>'v twl_st \<Rightarrow> 'v twl_st nres\<close> where
  \<open>conclusive_TWL_norestart_run S = SPEC(\<lambda>T. cdcl_twl_stgy\<^sup>*\<^sup>* S T \<and> final_twl_state T)\<close>


lemma conflict_of_level_unsatisfiable:
  assumes
    struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv S\<close> and
    dec: \<open>count_decided (trail S) = 0\<close> and
    confl: \<open>conflicting S \<noteq> None\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init S\<close>
  shows \<open>unsatisfiable (set_mset (init_clss S))\<close>
proof -
  obtain M N U D where S: \<open>S = (M, N, U, Some D)\<close>
    by (cases S) (use confl in \<open>auto simp: cdcl\<^sub>W_restart_mset_state\<close>)
  have [simp]: \<open>get_all_ann_decomposition M = [([], M)]\<close>
    by (rule no_decision_get_all_ann_decomposition)
      (use dec in \<open>auto simp: count_decided_def filter_empty_conv S cdcl\<^sub>W_restart_mset_state\<close>)
  have
    N_U: \<open>N \<Turnstile>psm U\<close> and
    M_D: \<open>M \<Turnstile>as CNot D\<close> and
    N_U_M: \<open>set_mset N \<union> set_mset U \<Turnstile>ps unmark_l M\<close> and
    n_d: \<open>no_dup M\<close> and
    N_U_D: \<open>set_mset N \<union> set_mset U \<Turnstile>p D\<close>
    using assms
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def all_decomposition_implies_def
        S clauses_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_alt_def)
  have \<open>set_mset N \<union> set_mset U \<Turnstile>ps CNot D\<close>
    by (rule true_clss_clss_true_clss_cls_true_clss_clss[OF N_U_M M_D])
  then have \<open>set_mset N \<Turnstile>ps CNot D\<close> \<open>set_mset N \<Turnstile>p D\<close>
    using N_U N_U_D true_clss_clss_left_right by blast+
  then have \<open>unsatisfiable (set_mset N)\<close>
    by (rule true_clss_clss_CNot_true_clss_cls_unsatisfiable)

  then show ?thesis
    by (auto simp: S clauses_def dest: satisfiable_decreasing)
qed

lemma conflict_of_level_unsatisfiable2:
  assumes
    struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv S\<close> and
    dec: \<open>count_decided (trail S) = 0\<close> and
    confl: \<open>conflicting S \<noteq> None\<close>
  shows \<open>unsatisfiable (set_mset (init_clss S + learned_clss S))\<close>
proof -
  obtain M N U D where S: \<open>S = (M, N, U, Some D)\<close>
    by (cases S) (use confl in \<open>auto simp: cdcl\<^sub>W_restart_mset_state\<close>)
  have [simp]: \<open>get_all_ann_decomposition M = [([], M)]\<close>
    by (rule no_decision_get_all_ann_decomposition)
      (use dec in \<open>auto simp: count_decided_def filter_empty_conv S\<close>)
  have
    M_D: \<open>M \<Turnstile>as CNot D\<close> and
    N_U_M: \<open>set_mset N \<union> set_mset U \<Turnstile>ps unmark_l M\<close> and
    n_d: \<open>no_dup M\<close> and
    N_U_D: \<open>set_mset N \<union> set_mset U \<Turnstile>p D\<close>
    using assms
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def all_decomposition_implies_def
        S clauses_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_alt_def)
  have \<open>set_mset N \<union> set_mset U \<Turnstile>ps CNot D\<close>
    by (rule true_clss_clss_true_clss_cls_true_clss_clss[OF N_U_M M_D])
  then have \<open>set_mset N \<union> set_mset U \<Turnstile>ps CNot D\<close> \<open>set_mset N \<union> set_mset U \<Turnstile>p D\<close>
    using N_U_D true_clss_clss_left_right by blast+
  then have \<open>unsatisfiable (set_mset N  \<union> set_mset U)\<close>
    by (rule true_clss_clss_CNot_true_clss_cls_unsatisfiable)

  then show ?thesis
    by (auto simp: S clauses_def dest: satisfiable_decreasing)
qed

end