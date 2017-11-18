theory Two_Watched_Literals_Transition_System
  imports Refine_Imperative_HOL.IICF CDCL.CDCL_W_Abstract_State
    CDCL.CDCL_W_Restart "../lib/Explorer"
begin

chapter \<open>Two-Watched Literals\<close>

notation image_mset (infixr "`#" 90)

section \<open>Rule-based system\<close>

subsection \<open>Types and Transitions System\<close>

subsubsection \<open>Types and accessing functions\<close>

datatype 'v twl_clause =
  TWL_Clause (watched: 'v) (unwatched: 'v)

fun clause :: "'a twl_clause \<Rightarrow> 'a :: {plus}" where
"clause (TWL_Clause W UW) = W + UW"

type_synonym 'v twl_cls = "'v clause twl_clause"
type_synonym 'v twl_clss = "'v twl_cls multiset"
type_synonym 'v clauses_to_update = "('v literal \<times> 'v twl_cls) multiset"
type_synonym 'v lit_queue = "'v literal multiset"
type_synonym 'v twl_st =
  "('v, 'v clause) ann_lits \<times> 'v twl_clss \<times> 'v twl_clss \<times>
    'v clause option \<times> 'v clauses \<times> 'v clauses \<times>  'v clauses_to_update \<times> 'v lit_queue"

fun clauses_to_update :: "'v twl_st \<Rightarrow> ('v literal \<times> 'v twl_cls) multiset" where
  \<open>clauses_to_update (_, _, _, _, _, _, WS, _) = WS\<close>

fun set_clauses_to_update :: "('v literal \<times> 'v twl_cls) multiset \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st" where
  \<open>set_clauses_to_update WS (M, N, U, D, NP, UP, _, Q) = (M, N, U, D, NP, UP, WS, Q)\<close>

fun literals_to_update :: "'v twl_st \<Rightarrow> 'v lit_queue" where
  \<open>literals_to_update (_, _, _, _, _, _, _, Q) = Q\<close>

fun set_literals_to_update :: "'v lit_queue \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st" where
  \<open>set_literals_to_update Q (M, N, U, D, NP, UP, WS, _) = (M, N, U, D, NP, UP, WS, Q)\<close>

fun set_conflict :: "'v clause \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st" where
  \<open>set_conflict D (M, N, U, _, NP, UP, WS, Q) = (M, N, U, Some D, NP, UP, WS, Q)\<close>

fun get_conflict :: "'v twl_st \<Rightarrow> 'v clause option" where
  \<open>get_conflict (M, N, U, D, NP, UP, WS, Q) = D\<close>

fun get_clauses :: "'v twl_st \<Rightarrow> 'v twl_clss" where
  \<open>get_clauses (M, N, U, D, NP, UP, WS, Q) = N + U\<close>

fun unit_clss :: "'v twl_st \<Rightarrow> 'v clause multiset" where
  \<open>unit_clss (M, N, U, D, NP, UP, WS, Q) = NP + UP\<close>

fun update_clause where
"update_clause (TWL_Clause W UW) L L' =
  TWL_Clause (add_mset L' (remove1_mset L W)) (add_mset L (remove1_mset L' UW))"

text \<open>
  When updating clause, we do it non-deterministically: in case of duplicate clause in the two
  sets, one of the two can be updated (and it does not matter), contrary to an if-condition. \<close>
inductive update_clauses ::
  "'a multiset twl_clause multiset \<times> 'a multiset twl_clause multiset \<Rightarrow>
  'a multiset twl_clause \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow>
  'a multiset twl_clause multiset \<times> 'a multiset twl_clause multiset \<Rightarrow> bool" where
  \<open>D \<in># N \<Longrightarrow> update_clauses (N, U) D L L' (add_mset (update_clause D L L') (remove1_mset D N), U)\<close>
| \<open>D \<in># U \<Longrightarrow> update_clauses (N, U) D L L' (N, add_mset (update_clause D L L') (remove1_mset D U))\<close>

inductive_cases update_clausesE: \<open>update_clauses (N, U) D L L' (N', U')\<close>

fun get_trail :: "'v twl_st \<Rightarrow> ('v, 'v clause) ann_lit list" where
  \<open>get_trail (M, _, _, _, _, _, _, _) = M\<close>


subsubsection \<open>The Transition System\<close>

text \<open>We ensure that there are always \<^emph>\<open>2\<close> watched literals and that there are different. All
  clauses containing a single literal are put in \<^term>\<open>NP\<close> or \<^term>\<open>UP\<close>.\<close>

inductive cdcl_twl_cp :: "'v twl_st \<Rightarrow> 'v twl_st \<Rightarrow> bool" where
pop:
  "cdcl_twl_cp (M, N, U, None, NP, UP, {#}, add_mset L Q)
    (M, N, U, None, NP, UP, {#(L, C)|C \<in># N + U. L \<in># watched C#}, Q)" |
propagate:
  "cdcl_twl_cp (M, N, U, None, NP, UP, add_mset (L, D) WS, Q)
    (Propagated L' (clause D) # M, N, U, None, NP, UP, WS, add_mset (-L') Q)"
  if
    "watched D = {#L, L'#}" and "undefined_lit M L'" and "\<forall>L \<in># unwatched D. -L \<in> lits_of_l M" |
conflict:
  "cdcl_twl_cp (M, N, U, None, NP, UP, add_mset (L, D) WS, Q)
    (M, N, U, Some (clause D), NP, UP, {#}, {#})"
  if "watched D = {#L, L'#}" and "-L' \<in> lits_of_l M" and "\<forall>L \<in># unwatched D. -L \<in> lits_of_l M" |
delete_from_working:
  "cdcl_twl_cp (M, N, U, None, NP, UP, add_mset (L, D) WS, Q) (M, N, U, None, NP, UP, WS, Q)"
  if "watched D = {#L, L'#}" and "L' \<in> lits_of_l M" |
update_clause:
  "cdcl_twl_cp (M, N, U, None, NP, UP, add_mset (L, D) WS, Q)
    (M, N', U', None, NP, UP, WS, Q)"
  if \<open>watched D = {#L, L'#}\<close> and \<open>-L \<in> lits_of_l M\<close> and \<open>L' \<notin> lits_of_l M\<close> and
    \<open>K \<in># unwatched D\<close> and \<open>undefined_lit M K \<or> K \<in> lits_of_l M\<close> and
    \<open>update_clauses (N, U) D L K (N', U')\<close>
    \<comment> \<open>The condition \<^term>\<open>-L \<in> lits_of_l M\<close> is already implied by \<^term>\<open>valid\<close> invariant.\<close>

inductive_cases cdcl_twl_cpE: \<open>cdcl_twl_cp S T\<close>


text \<open>We do not care about the \<^term>\<open>literals_to_update\<close> literals.\<close>
inductive cdcl_twl_o :: "'v twl_st \<Rightarrow> 'v twl_st \<Rightarrow> bool" where
  decide:
  \<open>cdcl_twl_o (M, N, U, None, NP, UP, {#}, {#}) (Decided L # M, N, U, None, NP, UP, {#}, {#-L#})\<close>
  if \<open>undefined_lit M L\<close> and \<open>atm_of L \<in> atms_of_mm (clause `# N)\<close>
| skip:
  \<open>cdcl_twl_o (Propagated L C' # M, N, U, Some D, NP, UP, {#}, {#})
  (M, N, U, Some D, NP, UP, {#}, {#})\<close>
  if \<open>-L \<notin># D\<close> and \<open>D \<noteq> {#}\<close>
| resolve:
  \<open>cdcl_twl_o (Propagated L C # M, N, U, Some D, NP, UP, {#}, {#})
  (M, N, U, Some (cdcl\<^sub>W_restart_mset.resolve_cls L D C), NP, UP, {#}, {#})\<close>
  if \<open>-L \<in># D\<close> and
    \<open>get_maximum_level (Propagated L C # M) (remove1_mset (-L) D) = count_decided M\<close>
| backtrack_unit_clause:
  \<open>cdcl_twl_o (M, N, U, Some D, NP, UP, {#}, {#})
  (Propagated L {#L#} # M1, N, U, None, NP, add_mset {#L#} UP, {#}, {#-L#})\<close>
  if
    \<open>L \<in># D\<close> and
    \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition M)\<close> and
    \<open>get_level M L = count_decided M\<close> and
    \<open>get_level M L = get_maximum_level M D'\<close> and
    \<open>get_maximum_level M (D' - {#L#}) \<equiv> i\<close> and
    \<open>get_level M K = i + 1\<close>
    \<open>D' = {#L#}\<close> and
    \<open>D' \<subseteq># D\<close> and
    \<open>clause `# (N + U) + NP + UP \<Turnstile>pm D'\<close>
| backtrack_nonunit_clause:
  \<open>cdcl_twl_o (M, N, U, Some D, NP, UP, {#}, {#})
  (Propagated L D' # M1, N, add_mset (TWL_Clause {#L, L'#} (D' - {#L, L'#})) U, None, NP, UP, {#}, {#-L#})\<close>
  if
    \<open>L \<in># D\<close> and
    \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition M)\<close> and
    \<open>get_level M L = count_decided M\<close> and
    \<open>get_level M L = get_maximum_level M D'\<close> and
    \<open>get_maximum_level M (D' - {#L#}) \<equiv> i\<close> and
    \<open>get_level M K = i + 1\<close>
    \<open>D' \<noteq> {#L#}\<close> and
    \<open>D' \<subseteq># D\<close> and
    \<open>clause `# (N + U) + NP + UP \<Turnstile>pm D'\<close> and
    \<open>L \<in># D'\<close>
    \<open>L' \<in># D'\<close> and \<comment> \<open>\<^term>\<open>L'\<close> is the new watched literal\<close>
    \<open>get_level M L' = i\<close>

inductive_cases cdcl_twl_oE: \<open>cdcl_twl_o S T\<close>

inductive cdcl_twl_stgy :: "'v twl_st \<Rightarrow> 'v twl_st \<Rightarrow> bool" for S :: \<open>'v twl_st\<close> where
cp: "cdcl_twl_cp S S' \<Longrightarrow> cdcl_twl_stgy S S'" |
other': "cdcl_twl_o S S' \<Longrightarrow> cdcl_twl_stgy S S'"

inductive_cases cdcl_twl_stgyE: \<open>cdcl_twl_stgy S T\<close>


subsection \<open>Definition of the Two-watched literals Invariants\<close>

subsubsection \<open>Definitions\<close>

text \<open>The structural invariants states that there are at most two watched elements, that the watched
  literals are distinct, and that there are 2 watched literals if there are at least than two
  different literals in the full clauses.\<close>
primrec struct_wf_twl_cls :: "'v multiset twl_clause \<Rightarrow> bool" where
"struct_wf_twl_cls (TWL_Clause W UW) \<longleftrightarrow>
   size W = 2 \<and> distinct_mset (W + UW)"

fun state\<^sub>W_of :: "'v twl_st \<Rightarrow> 'v cdcl\<^sub>W_restart_mset" where
"state\<^sub>W_of (M, N, U, C, NP, UP, Q) =
  (M, clause `# N + NP, clause `# U + UP,  C)"

text \<open>
  The invariant on the clauses is the following:
  \<^item> the structure is correct (the watched part is of length exactly two).
  \<^item> if we do not have to update the clause, then the invariant holds.
  \<close>
definition
  twl_is_an_exception:: "'a multiset twl_clause \<Rightarrow> 'a multiset \<Rightarrow>
     ('b \<times> 'a multiset twl_clause) multiset \<Rightarrow> bool"
where
"twl_is_an_exception C Q WS \<longleftrightarrow>
   (\<exists>L. L \<in># Q \<and> L \<in># watched C) \<or> (\<exists>L. (L, C) \<in># WS)"

text \<open>If one watched literal is true and the other false, then it has been decided earlier.\<close>
fun twl_inv :: "('a, 'b) ann_lits \<Rightarrow> 'a twl_cls \<Rightarrow> bool" where
"twl_inv M (TWL_Clause W UW) \<longleftrightarrow>
  (\<forall>L L'. W = {#L, L'#} \<longrightarrow> L \<in> lits_of_l M \<longrightarrow> -L' \<in> lits_of_l M \<longrightarrow>
    get_level M L \<le> get_level M L')"

text \<open>This invariant state that watched literals are set at the end and are not swapped with an
  unwatched literal later.\<close>
fun twl_lazy_update :: "('a, 'b) ann_lits \<Rightarrow> 'a twl_cls \<Rightarrow> bool" where
\<open>twl_lazy_update M (TWL_Clause W UW) \<longleftrightarrow>
  (\<forall>L L'. W = {#L, L'#} \<longrightarrow> -L \<in> lits_of_l M \<longrightarrow> L' \<notin> lits_of_l M \<longrightarrow>
    (\<forall>K \<in># UW. get_level M L \<ge> get_level M K))\<close>

text \<open>If one watched literals has been assigned to false (\<^term>\<open>-L \<in> lits_of_l M\<close>) and the clause
  has not yet been updated (\<^term>\<open>L' \<notin> lits_of_l M\<close>: it should be removed either by updating \<open>L\<close>,
  propagating \<open>L'\<close>, or marking the conflict), then the literals \<^term>\<open>L\<close> is of maximal level.\<close>
fun watched_literals_false_of_max_level :: "('a, 'b) ann_lits \<Rightarrow> 'a twl_cls \<Rightarrow> bool" where
"watched_literals_false_of_max_level M (TWL_Clause W UW) \<longleftrightarrow>
  (\<forall>L L'. W = {#L, L'#} \<longrightarrow> -L \<in> lits_of_l M \<longrightarrow> L' \<notin> lits_of_l M \<longrightarrow>
    get_level M L = count_decided M)"

text \<open>
  This invariants talks about the enqueued literals:
  \<^item> the working stack contains a single literal;
  \<^item> the working stack and the \<^term>\<open>literals_to_update\<close> literals are false with respect to the trail and there are no
  duplicates;
  \<^item> and the latter condition holds even when \<^term>\<open>WS = {#}\<close>.\<close>
fun no_duplicate_queued :: "'v twl_st \<Rightarrow> bool" where
\<open>no_duplicate_queued (M, N, U, D, NP, UP, WS, Q) \<longleftrightarrow>
  (\<forall>C C'. C \<in># WS \<longrightarrow> C' \<in># WS \<longrightarrow> fst C = fst C') \<and>
  (\<forall>C. C \<in># WS \<longrightarrow> add_mset (fst C) Q \<subseteq># uminus `# lit_of `# mset M) \<and>
  Q \<subseteq># uminus `# lit_of `# mset M\<close>

fun distinct_queued :: "'v twl_st \<Rightarrow> bool" where
\<open>distinct_queued (M, N, U, D, NP, UP, WS, Q) \<longleftrightarrow>
  distinct_mset Q \<and>
  (\<forall>L C. count WS (L, C) \<le> count (N + U) C) \<and>
  (\<forall>L L' C C'. (L, C) \<in># WS \<longrightarrow> (L', C') \<in># WS \<longrightarrow> L = L')\<close>

text \<open>These are the conditions to indicate that the 2-WL invariant does not hold and is not \<^term>\<open>literals_to_update\<close>.\<close>
fun clauses_to_update_prop where
  \<open>clauses_to_update_prop Q M (L, C) \<longleftrightarrow>
    (\<exists>L'. watched C = {#L, L'#} \<and>
    -L \<in> lits_of_l M \<and> L \<notin># Q \<and> L' \<notin> lits_of_l M)\<close>
declare clauses_to_update_prop.simps[simp del]

text \<open>
  This invariants talks about the enqueued literals:
  \<^item> all clauses that should be updated are in \<^term>\<open>WS\<close> and are repeated often enough in it.
  \<^item> if \<^term>\<open>WS = {#}\<close>, then there are no clauses to updated that is not enqueued;
  \<^item> all clauses to updated are either in \<^term>\<open>WS\<close> or \<^term>\<open>Q\<close>.

  The first two conditions are written that way to please Isabelle.\<close>

fun clauses_to_update_inv :: "'v twl_st \<Rightarrow> bool" where
  \<open>clauses_to_update_inv (M, N, U, None, NP, UP, WS, Q) \<longleftrightarrow>
     (\<forall>L C. ((L, C) \<in># WS \<longrightarrow> {#(L, C)| C \<in># N + U. clauses_to_update_prop Q M (L, C)#} \<subseteq># WS)) \<and>
     (\<forall>L. WS = {#} \<longrightarrow> {#(L, C)| C \<in># N + U. clauses_to_update_prop Q M (L, C)#} = {#}) \<and>
     (\<forall>L L' C. C \<in># N + U \<longrightarrow> watched C = {#L, L'#} \<longrightarrow> -L \<in> lits_of_l M \<longrightarrow> L' \<notin> lits_of_l M \<longrightarrow>
       (L, C) \<notin># WS \<longrightarrow> L \<in># Q)\<close>
| \<open>clauses_to_update_inv (M, N, U, D, NP, UP, WS, Q) \<longleftrightarrow> True\<close>


text \<open>This is the invariant of the 2WL structure: if one watched literal is false, then all unwatched
  are false.\<close>
fun twl_exception_inv :: "'v twl_st \<Rightarrow>  'v twl_cls \<Rightarrow> bool" where
  \<open>twl_exception_inv (M, N, U, None, NP, UP, WS, Q) C \<longleftrightarrow>
    (\<forall>L L'. watched C = {#L, L'#} \<longrightarrow> -L \<in> lits_of_l M \<longrightarrow> L' \<notin> lits_of_l M \<longrightarrow>
      L \<notin># Q \<longrightarrow> (L, C) \<notin># WS \<longrightarrow>
      (\<forall>K \<in># unwatched C. -K \<in> lits_of_l M))\<close>
| \<open>twl_exception_inv (M, N, U, D, NP, UP, WS, Q) C \<longleftrightarrow> True\<close>

declare twl_exception_inv.simps[simp del]

fun twl_st_exception_inv :: "'v twl_st \<Rightarrow> bool" where
\<open>twl_st_exception_inv (M, N, U, D, NP, UP, WS, Q) \<longleftrightarrow>
  (\<forall>C \<in># N + U. twl_exception_inv (M, N, U, D, NP, UP, WS, Q) C)\<close>


text \<open>Candidats for propagation (i.e., the clause where only one literals is non
  assigned) are enqueued.\<close>
fun propa_cands_enqueued :: "'v twl_st \<Rightarrow> bool" where
  \<open>propa_cands_enqueued (M, N, U, None, NP, UP, WS, Q) \<longleftrightarrow>
  (\<forall>L C. C \<in># N+U \<longrightarrow> L \<in># clause C \<longrightarrow> M \<Turnstile>as CNot (remove1_mset L (clause C)) \<longrightarrow>
    undefined_lit M L \<longrightarrow>
    (\<exists>L'. L' \<in># watched C \<and> L' \<in># Q) \<or> (\<exists>L. (L, C) \<in># WS))\<close>
  | \<open>propa_cands_enqueued (M, N, U, D, NP, UP, WS, Q) \<longleftrightarrow> True\<close>

fun confl_cands_enqueued :: "'v twl_st \<Rightarrow> bool" where
  \<open>confl_cands_enqueued (M, N, U, None, NP, UP, WS, Q) \<longleftrightarrow>
     (\<forall>C \<in># N + U. M \<Turnstile>as CNot (clause C) \<longrightarrow> (\<exists>L'. L' \<in># watched C \<and> L' \<in># Q) \<or> (\<exists>L. (L, C) \<in># WS))\<close>
| \<open>confl_cands_enqueued (M, N, U, Some _, NP, UP, WS, Q) \<longleftrightarrow>
     True\<close>

text \<open>This invariant talk about the decomposition of the trail and the invariants that holds in
  these states.\<close>
fun past_invs :: "'v twl_st \<Rightarrow> bool" where
  \<open>past_invs (M, N, U, D, NP, UP, WS, Q) \<longleftrightarrow>
    (\<forall>M1 M2 K. M = M2 @ Decided K # M1 \<longrightarrow> (
      (\<forall>C \<in># N + U. twl_lazy_update M1 C \<and> twl_inv M1 C \<and>
        watched_literals_false_of_max_level M1 C \<and>
        twl_exception_inv (M1, N, U, None, NP, UP, {#}, {#}) C) \<and>
      confl_cands_enqueued (M1, N, U, None, NP, UP, {#}, {#}) \<and>
      propa_cands_enqueued (M1, N, U, None, NP, UP, {#}, {#}) \<and>
      clauses_to_update_inv (M1, N, U, None, NP, UP, {#}, {#})))\<close>
declare past_invs.simps[simp del]

fun twl_st_inv :: "'v twl_st \<Rightarrow> bool" where
\<open>twl_st_inv (M, N, U, D, NP, UP, WS, Q) \<longleftrightarrow>
  (\<forall>C \<in># N + U. struct_wf_twl_cls C) \<and>
  (\<forall>C \<in># N + U. D = None \<longrightarrow> \<not>twl_is_an_exception C Q WS \<longrightarrow> (twl_lazy_update M C \<and> twl_inv M C)) \<and>
  (\<forall>C \<in># N + U. D = None \<longrightarrow> watched_literals_false_of_max_level M C)\<close>

text \<open>All the unit clauses are all propagated initially except when we have found a conflict of
  level \<^term>\<open>0::nat\<close>.\<close>
fun unit_clss_inv :: "'v twl_st \<Rightarrow> bool" where
  \<open>unit_clss_inv (M, N, U, D, NP, UP, WS, Q) \<longleftrightarrow>
    (\<forall>C \<in># NP + UP.
      (\<exists>L. C = {#L#} \<and> (D = None \<or> count_decided M > 0 \<longrightarrow> get_level M L = 0 \<and> L \<in> lits_of_l M)))\<close>

text \<open>\<^term>\<open>literals_to_update\<close> literals are of maximum level and their negation is in the trail.\<close>
fun valid_annotation :: "'v twl_st \<Rightarrow> bool" where
"valid_annotation (M, N, U, C, NP, UP, WS, Q) \<longleftrightarrow>
  (\<forall>(L, C) \<in># WS. L \<in># watched C \<and> C \<in># N + U \<and> -L \<in> lits_of_l M \<and>
     get_level M L = count_decided M) \<and>
  (\<forall>L \<in># Q. -L \<in> lits_of_l M \<and> get_level M L = count_decided M)"

text \<open>Putting invariants together:\<close>
definition twl_struct_invs :: \<open>'v twl_st \<Rightarrow> bool\<close> where
  \<open>twl_struct_invs S \<longleftrightarrow>
    (twl_st_inv S \<and>
    valid_annotation S \<and>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S) \<and>
    cdcl\<^sub>W_restart_mset.no_smaller_propa (state\<^sub>W_of S) \<and>
    twl_st_exception_inv S \<and>
    no_duplicate_queued S \<and>
    distinct_queued S \<and>
    confl_cands_enqueued S \<and>
    propa_cands_enqueued S \<and>
    (get_conflict S \<noteq> None \<longrightarrow> clauses_to_update S = {#} \<and> literals_to_update S = {#}) \<and>
    unit_clss_inv S \<and>
    clauses_to_update_inv S \<and>
    past_invs S)
  \<close>

definition twl_stgy_invs :: \<open>'v twl_st \<Rightarrow> bool\<close> where
  \<open>twl_stgy_invs S \<longleftrightarrow> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state\<^sub>W_of S)\<close>


subsubsection \<open>Initial properties\<close>

lemma twl_is_an_exception_add_mset_to_queue: \<open>twl_is_an_exception C (add_mset L Q) WS \<longleftrightarrow>
  (twl_is_an_exception C Q WS \<or> (L \<in># watched C))\<close>
  unfolding twl_is_an_exception_def by auto

lemma twl_is_an_exception_add_mset_to_clauses_to_update:
  \<open>twl_is_an_exception C Q (add_mset (L, D) WS) \<longleftrightarrow> (twl_is_an_exception C Q WS \<or> (C = D))\<close>
  unfolding twl_is_an_exception_def by auto

lemma twl_is_an_exception_empty[simp]: \<open>\<not>twl_is_an_exception C {#} {#}\<close>
  unfolding twl_is_an_exception_def by auto

lemma twl_inv_empty_trail:
  shows
    \<open>watched_literals_false_of_max_level [] C\<close> and
    \<open>twl_lazy_update [] C\<close> and
    \<open>twl_inv [] C\<close>
  by (cases C; auto)+

lemma clauses_to_update_inv_cases[case_names WS_nempty WS_empty Q]:
  assumes
    \<open>\<And>L C. (L, C) \<in># WS \<Longrightarrow> {#(L, C)| C \<in># N + U. clauses_to_update_prop Q M (L, C)#} \<subseteq># WS\<close> and
    \<open>\<And>L. WS = {#} \<Longrightarrow> {#(L, C)| C \<in># N + U. clauses_to_update_prop Q M (L, C)#} = {#}\<close> and
    \<open>\<And>L L' C. C \<in># N + U \<Longrightarrow> watched C = {#L, L'#} \<Longrightarrow> -L \<in> lits_of_l M \<Longrightarrow> L' \<notin> lits_of_l M \<Longrightarrow>
       (L, C) \<notin># WS \<Longrightarrow> L \<in># Q\<close>
  shows
    \<open>clauses_to_update_inv (M, N, U, None, NP, UP, WS, Q)\<close>
  using assms unfolding clauses_to_update_inv.simps by blast

lemma
  assumes \<open>\<And>C. C \<in># N + U \<Longrightarrow> struct_wf_twl_cls C\<close>
  shows
    twl_st_inv_empty_trail: \<open>twl_st_inv ([], N, U, C, NP, UP, WS, Q)\<close>
  by (auto simp: assms twl_inv_empty_trail)

lemma
  shows
    no_duplicate_queued_no_queued: \<open>no_duplicate_queued (M, N, U, D, NP, UP, {#}, {#})\<close> and
    no_distinct_queued_no_queued: \<open>distinct_queued ([], N, U, D, NP, UP, {#}, {#})\<close>
  by auto

lemma twl_st_inv_add_mset_clauses_to_update:
  assumes \<open>D \<in># N + U\<close>
  shows \<open>twl_st_inv (M, N, U, None, NP, UP, WS, Q)
  \<longleftrightarrow> twl_st_inv (M, N, U, None, NP, UP, add_mset (L, D) WS, Q) \<and>
    (\<not> twl_is_an_exception D Q WS \<longrightarrow>twl_lazy_update M D \<and> twl_inv M D)
    \<close>
  using assms by (auto simp: twl_is_an_exception_add_mset_to_clauses_to_update)

lemma twl_st_simps:
"twl_st_inv (M, N, U, D, NP, UP, WS, Q) \<longleftrightarrow>
  (\<forall>C \<in># N + U. struct_wf_twl_cls C \<and>
    (D = None \<longrightarrow> (\<not>twl_is_an_exception C Q WS \<longrightarrow> (twl_lazy_update M C \<and> twl_inv M C)) \<and>
    watched_literals_false_of_max_level M C))"
  unfolding twl_st_inv.simps by fast

lemma propa_cands_enqueued_unit_clause:
  \<open>propa_cands_enqueued (M, N, U, C, add_mset L NP, UP, WS, Q) \<longleftrightarrow>
    propa_cands_enqueued (M, N, U, C, {#}, {#}, WS, Q)\<close>
  \<open>propa_cands_enqueued (M, N, U, C, NP, add_mset L UP, WS, Q) \<longleftrightarrow>
    propa_cands_enqueued (M, N, U, C, {#}, {#}, WS, Q)\<close>
  by (cases C; auto)+

lemma past_invs_enqueud: \<open>past_invs (M, N, U, D, NP, UP, WS, Q) \<longleftrightarrow>
  past_invs (M, N, U, D, NP, UP, {#}, {#})\<close>
  unfolding past_invs.simps by simp

lemma confl_cands_enqueued_unit_clause:
  \<open>confl_cands_enqueued (M, N, U, C, add_mset L NP, UP, WS, Q) \<longleftrightarrow>
    confl_cands_enqueued (M, N, U, C, {#}, {#}, WS, Q)\<close>
  \<open>confl_cands_enqueued (M, N, U, C, NP, add_mset L UP, WS, Q) \<longleftrightarrow>
    confl_cands_enqueued (M, N, U, C, {#}, {#}, WS, Q)\<close>
  by (cases C; auto)+

lemma twl_inv_decomp:
  assumes
    twl: \<open>twl_inv M C\<close> and
    lazy: \<open>twl_lazy_update M C\<close> and
    decomp: \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition M)\<close> and
    n_d: \<open>no_dup M\<close>
  shows
    \<open>twl_inv M1 C\<close> and \<open>twl_lazy_update M1 C\<close>
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
      by (rule cdcl\<^sub>W_restart_mset.no_dup_append_in_atm_notin)
        (use that n_d in \<open>auto simp: M M' defined_lit_map\<close>)
    then show lev_L_M1: \<open>get_level M L = get_level M1 L\<close>
      using that n_d by (auto simp: M image_Un M')
  qed

  show \<open>twl_inv M1 C\<close>
    unfolding C twl_inv.simps
  proof (intro conjI allI impI)
    fix L L'
    assume
      W: \<open>W = {#L, L'#}\<close> and
      L: \<open>L \<in> lits_of_l M1\<close> and
      uL': \<open>- L' \<in> lits_of_l M1\<close>
    then have \<open>get_level M L \<le> get_level M L'\<close>
      using twl unfolding MM' C by auto
    then show \<open>get_level M1 L \<le> get_level M1 L'\<close>
      using lev_M_M1[of L] lev_M_M1[of \<open>-L'\<close>] L uL' by (fastforce simp: get_level_def)
  qed


  show \<open>twl_lazy_update M1 C\<close>
    unfolding C twl_lazy_update.simps
  proof (intro allI impI)
    fix L L'
    assume
      W: \<open>W = {#L, L'#}\<close> and
      uL: \<open>- L \<in> lits_of_l M1\<close> and
      L': \<open>L' \<notin> lits_of_l M1\<close>

    then have lev_L_M1: \<open>get_level M L = get_level M1 L\<close>
      using uL n_d lev_M_M1[of "-L"] by auto

    have L'M: \<open>L' \<notin> lits_of_l M\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then have L'M': \<open>L' \<in> lits_of_l M'\<close>
        using L' MM' by auto
      then have \<open>get_level M L' \<le> get_level M L\<close>
        using twl W uL C MM' by auto
      moreover {
        have \<open>atm_of L' \<in> atm_of ` lits_of_l M'\<close>
          using L'M' by (simp add: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set)
        moreover have \<open>Decided K \<in>set (dropWhile (\<lambda>S. atm_of (lit_of S) \<noteq> atm_of K') M')\<close>
          if \<open>K' \<in> lits_of_l M'\<close> for K'
          unfolding M' append_assoc[symmetric] by (rule last_in_set_dropWhile)
            (use that in \<open>auto simp: lits_of_def M' MM'\<close>)
        ultimately have \<open>get_level M L' > count_decided M1\<close>
          unfolding MM' by (force simp: filter_empty_conv get_level_def count_decided_def lits_of_def) }
      ultimately show False
        using lev_M_M1[of "-L"] uL count_decided_ge_get_level[of M1 "-L"] by auto
    qed

    show \<open>\<forall>K\<in>#UW. get_level M1 K \<le> get_level M1 L\<close>
    proof clarify
      fix K''
      assume \<open>K'' \<in># UW\<close>
      then have lev_K'_L: \<open>get_level M K'' \<le> get_level M L\<close>
        using lazy W uL L' L'M unfolding C MM' by auto
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
          have a1: "get_level M' K'' + count_decided M1 \<le> get_level M1 L"
            using lev_K'_L unfolding lev_L_M1 unfolding MM' get_level_skip_end[OF True] .
          then have "count_decided M1 \<le> get_level M1 L"
            by linarith
          then have "get_level M1 L = count_decided M1"
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
      then show \<open>get_level M1 K'' \<le> get_level M1 L\<close>
        using lev_M_M1[OF uL] lev_K'_L by auto
    qed
  qed
qed

declare twl_st_inv.simps[simp del]

lemma twl_lazy_update_Propagated:
  assumes
    W: \<open>W = {#L, L'#}\<close> and
    \<open>-L \<notin> lits_of_l M\<close>
  shows
    \<open>twl_lazy_update (Propagated L D # M) (TWL_Clause W UW)\<close>
  using assms(2) by (simp add: W add_mset_eq_add_mset)

lemma twl_inv_Propagated:
  assumes
    W: \<open>W = {#L, L'#}\<close> and
    \<open>get_level M L' = count_decided M\<close>
  shows
    \<open>twl_inv (Propagated L D # M) (TWL_Clause W UW)\<close>
  unfolding twl_inv.simps apply (intro conjI allI impI)
  using assms(2) by (auto simp add: W add_mset_eq_add_mset get_level_def count_decided_def)

lemma watched_literals_false_of_max_level_Propagated:
  assumes
    W: \<open>W = {#L, L'#}\<close> and
    \<open>-L \<notin> lits_of_l M\<close>
  shows
    \<open>watched_literals_false_of_max_level (Propagated L D # M) (TWL_Clause W UW)\<close>
  using assms(2) by (simp add: W add_mset_eq_add_mset)

lemma lazy_update_Propagated: \<open>- L' \<notin># watched C \<Longrightarrow> watched_literals_false_of_max_level M C\<Longrightarrow>
  twl_lazy_update (Propagated L' D # M) C\<close>
  by (cases C) (auto simp: count_decided_ge_get_level get_level_cons_if)

lemma pair_in_image_Pair:
  \<open>(La, C) \<in> Pair L ` D \<longleftrightarrow> La = L \<and> C \<in> D\<close>
  by auto

lemma image_Pair_subset_mset:
  \<open>Pair L `# A \<subseteq># Pair L `# B \<longleftrightarrow> A \<subseteq># B\<close>
proof -
  have [simp]: \<open>remove1_mset (L, x) (Pair L `# B) = Pair L `# (remove1_mset x B)\<close> for x :: 'b and B
  proof -
    have "(L, x) \<in># Pair L `# B \<longrightarrow> x \<in># B"
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

(* useful for sledgehammer/proof reconstruction ?*)
lemma member_add_mset: \<open>a \<in># add_mset x xs \<longleftrightarrow> a = x \<or> a \<in># xs\<close>
  by simp

lemma
  assumes
    cdcl: "cdcl_twl_cp S T" and
    twl: "twl_st_inv S" and
    twl_excep: \<open>twl_st_exception_inv S\<close> and
    valid: "valid_annotation S" and
    inv: "cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S)" and
    no_dup: \<open>no_duplicate_queued S\<close> and
    dist_q: \<open>distinct_queued S\<close> and
    ws: \<open>clauses_to_update_inv S\<close>
  shows twl_cp_twl_st_exception_inv: \<open>twl_st_exception_inv T\<close> and
    twl_cp_clauses_to_update: \<open>clauses_to_update_inv T\<close>
  using cdcl twl twl_excep valid inv (* no_taut *) no_dup ws
proof (induction rule: cdcl_twl_cp.induct)
  case (pop M N U NP UP L Q)
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
  case (propagate D L L' M N U NP UP WS Q) note watched = this(1) and undef = this(2) and
    unw = this(3)

  case 1
  note twl = this(1) and twl_excep = this(2) and valid = this(3) and inv = this(4) and
    no_dup = this(5) and ws = this(6)
  have [simp]: \<open>- L' \<notin> lits_of_l M\<close>
    using Decided_Propagated_in_iff_in_lits_of_l propagate.hyps(2) by blast
  have D_N_U: \<open>D \<in># N + U\<close>
    using valid by auto
  then have wf_D: \<open>struct_wf_twl_cls D\<close>
    using twl by (simp add: twl_st_inv.simps)
  have "\<forall>s\<in>#clause `# U. \<not> tautology s"
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def by (simp_all add: cdcl\<^sub>W_restart_mset_state)
  have [simp]: \<open>L \<noteq> L'\<close>
    using wf_D watched by (cases D) auto
  have [simp]: \<open>- L \<in> lits_of_l M\<close>
    using valid by auto
  obtain NU where NU: \<open>N + U = add_mset D NU\<close>
    by (metis D_N_U insert_DiffM)
  have n_d: \<open>no_dup M\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: trail.simps)
  have HH: \<open>\<not>clauses_to_update_prop (add_mset (-L') Q) (Propagated L' (clause D) # M) (L, D)\<close>
    unfolding clauses_to_update_prop.simps by (auto simp: watched)
  have \<open>add_mset L Q \<subseteq># {#- lit_of x. x \<in># mset M#}\<close>
    using no_dup by (auto)
  moreover have \<open>distinct_mset {#- lit_of x. x \<in># mset M#}\<close>
    by (subst distinct_image_mset_inj) (use n_d in \<open>auto simp: lit_of_inj_on_no_dup distinct_map no_dup_def\<close>)
  ultimately have [simp]: \<open>L \<notin># Q\<close>
    by (metis distinct_mset_add_mset distinct_mset_union subset_mset.le_iff_add)
  have w_q_p_D: \<open>clauses_to_update_prop Q M (L, D)\<close>
    by (auto simp: clauses_to_update_prop.simps watched)
      (use unw undef in \<open>auto simp: Decided_Propagated_in_iff_in_lits_of_l\<close>)
  have \<open>Pair L `# {#C \<in># add_mset D NU. clauses_to_update_prop Q M (L, C)#} \<subseteq># add_mset (L, D) WS\<close>
    using ws no_dup unfolding clauses_to_update_inv.simps NU
    by (auto simp: all_conj_distrib)
  then have IH: \<open>Pair L `# {#C \<in># NU. clauses_to_update_prop Q M (L, C)#} \<subseteq># WS\<close>
    using w_q_p_D by auto
  have IH_Q: \<open>\<forall>La L' C. C \<in># add_mset D NU \<longrightarrow> watched C = {#La, L'#} \<longrightarrow> - La \<in> lits_of_l M \<longrightarrow>
    L' \<notin> lits_of_l M \<longrightarrow> (La, C) \<notin># add_mset (L, D) WS \<longrightarrow> La \<in># Q\<close>
    using ws no_dup unfolding clauses_to_update_inv.simps NU
    by (auto simp: all_conj_distrib)

  show ?case
    unfolding Ball_def twl_st_exception_inv.simps twl_exception_inv.simps
  proof (intro allI conjI impI)
    fix C J J' K
    assume C: \<open>C \<in># N + U\<close> and
      watched_C: \<open>watched C = {#J, J'#}\<close> and
      J: \<open>- J \<in> lits_of_l (Propagated L' (clause D) # M)\<close> and
      J': \<open>J' \<notin> lits_of_l (Propagated L' (clause D) # M)\<close> and
      J_notin: \<open>J \<notin># add_mset (- L') Q\<close> and
      C_WS: \<open>(J, C) \<notin># WS\<close> and
      \<open>K \<in># unwatched C\<close>
    then have \<open>- K \<in> lits_of_l (Propagated L' (clause D) # M)\<close> if \<open>C \<noteq> D\<close>
      using twl_excep that by (simp add: uminus_lit_swap twl_exception_inv.simps)

    moreover have CD: False if \<open>C = D\<close>
      using J J' watched_C watched that by (auto simp: add_mset_eq_add_mset)

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
      Pair L `# {#C \<in># NU. clauses_to_update_prop (add_mset (- L') Q) (Propagated L' (clause D) # M) (L'', C)#}\<close>
      unfolding image_Pair_subset_mset multiset_filter_mono2 clauses_to_update_prop.simps
      by auto
    show ?case
      using subset_mset.dual_order.trans[OF IH *]  HH
      unfolding NU \<open>L'' = L\<close>
      by simp
  next
    case (WS_empty K)
    then show ?case
      using IH IH_Q unfolding NU by (fastforce simp: filter_mset_empty_conv clauses_to_update_prop.simps
          watched add_mset_eq_add_mset)+
  next
    case (Q L L' C)
    then show ?case
      using IH_Q watched by (fastforce simp: add_mset_eq_add_mset NU)
  qed
next
  case (conflict D L L' M N U NP UP WS Q)
  case 1
  note twl = this(5)
  show ?case by (auto simp: twl_st_inv.simps twl_exception_inv.simps)

  case 2
  show ?case
    by (auto simp: twl_st_inv.simps twl_exception_inv.simps)
next
  case (delete_from_working D L L' M N U NP UP WS Q) note watched = this(1) and L' = this(2)

  case 1 note twl = this(1) and twl_excep = this(2) and valid = this(3) and inv = this(4) and
    no_dup = this(5) and ws = this(6)
  have n_d: \<open>no_dup M\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: trail.simps)
  have D_N_U: \<open>D \<in># N + U\<close>
    using valid by auto
  then have wf_D: \<open>struct_wf_twl_cls D\<close>
    using twl by (simp add: twl_st_inv.simps)
  obtain NU where NU: \<open>N + U = add_mset D NU\<close>
    by (metis D_N_U insert_DiffM)
  have [simp]: \<open>\<not>clauses_to_update_prop Q M (L, D)\<close>
    using L' by (auto simp: clauses_to_update_prop.simps watched)
  have IH_WS: \<open>Pair L `# {#C \<in># N + U. clauses_to_update_prop Q M (L, C)#} \<subseteq># add_mset (L, D) WS\<close>
    using ws by (auto simp del: filter_union_mset simp: NU)
  then have IH_WS_NU: \<open>Pair L `# {#C \<in># NU. clauses_to_update_prop Q M (L, C)#} \<subseteq># add_mset (L, D) WS\<close>
    using ws by (auto simp del: filter_union_mset simp: NU)

  have IH_WS': \<open>Pair L `# {#C \<in># N + U. clauses_to_update_prop Q M (L, C)#} \<subseteq># WS\<close>
    by (rule subset_add_mset_notin_subset_mset[OF IH_WS]) auto
  have IH_Q: \<open>\<forall>La L' C. C \<in># add_mset D NU \<longrightarrow> watched C = {#La, L'#} \<longrightarrow> - La \<in> lits_of_l M \<longrightarrow>
    L' \<notin> lits_of_l M \<longrightarrow> (La, C) \<notin># add_mset (L, D) WS \<longrightarrow> La \<in># Q\<close>
    using ws no_dup unfolding clauses_to_update_inv.simps NU
    by (auto simp: all_conj_distrib)

  show ?case
    unfolding Ball_def twl_st_exception_inv.simps twl_exception_inv.simps
  proof (intro allI conjI impI)
    fix C J J' K
    assume C: \<open>C \<in># N + U\<close> and
      watched_C: \<open>watched C = {#J, J'#}\<close> and
      J: \<open>- J \<in> lits_of_l M\<close> and
      J': \<open>J' \<notin> lits_of_l M\<close> and
      J_notin: \<open>J \<notin># Q\<close> and
      C_WS: \<open>(J, C) \<notin># WS\<close> and
      \<open>K \<in># unwatched C\<close>
    then have \<open>- K \<in> lits_of_l M\<close> if \<open>C \<noteq> D\<close>
      using twl_excep that by (simp add: uminus_lit_swap twl_exception_inv.simps)

    moreover {
      from n_d have False if \<open> - L' \<in> lits_of_l M\<close> \<open>L' \<in> lits_of_l M\<close>
        using that consistent_interp_def distinct_consistent_interp by blast
      then have CD: False if \<open>C = D\<close>
        using J J' watched_C watched L' by (auto simp: add_mset_eq_add_mset that) }
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
      using L' LK
      by (auto simp del: filter_union_mset simp: pair_in_image_Pair watched add_mset_eq_add_mset
          all_conj_distrib clauses_to_update_prop.simps)
    show ?case
      by (metis (no_types, lifting) "1" LK)
  next
    case (WS_empty K) note [simp] = this(1)
    have [simp]: \<open>\<not>clauses_to_update_prop Q M (K, D)\<close>
      using IH_Q WS_empty.IH watched by (auto simp: clauses_to_update_prop.simps add_mset_eq_add_mset L')
    have \<open>L \<noteq> L'\<close>
      using wf_D watched by (cases D) auto
    then show ?case
      using IH_WS' IH_Q watched by (fastforce simp: add_mset_eq_add_mset NU filter_mset_empty_conv
          all_conj_distrib clauses_to_update_prop.simps)
  next
    case (Q K L' C)
    then show ?case
      using \<open>\<not> clauses_to_update_prop Q M (L, D)\<close> ws
      unfolding clauses_to_update_inv.simps(1) clauses_to_update_prop.simps member_add_mset
      by blast
  qed
next
  case (update_clause D L L' M K N U N' U' NP UP WS Q) note watched = this(1) and uL = this(2) and
    L' = this(3) and K = this(4) and undef = this(5) and N'U' = this(6)

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
    by (auto simp: trail.simps)
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
  have lev_L': \<open>get_level M L' = count_decided M\<close> if \<open>- L' \<in> lits_of_l M \<close>
    using L_M w_max_D D watched L' uL that by (auto simp: add_mset_eq_add_mset)
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
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: trail.simps)
  have HH: \<open>\<not>clauses_to_update_prop (add_mset (-L') Q) (Propagated L' (clause D) # M) (L, D)\<close>
    unfolding clauses_to_update_prop.simps by (auto simp: watched)

  have \<open>add_mset L Q \<subseteq># {#- lit_of x. x \<in># mset M#}\<close>
    using no_dup by (auto)
  moreover have \<open>distinct_mset {#- lit_of x. x \<in># mset M#}\<close>
    by (subst distinct_image_mset_inj)
      (use n_d in \<open>auto simp: lit_of_inj_on_no_dup distinct_map no_dup_def\<close>)
  ultimately have LQ: \<open>L \<notin># Q\<close>
    by (metis distinct_mset_add_mset distinct_mset_union subset_mset.le_iff_add)
  have w_q_p_D: \<open>clauses_to_update_prop Q M (L, D)\<close>
    using watched uL L' by (auto simp: LQ clauses_to_update_prop.simps)
  have \<open>Pair L `# {#C \<in># add_mset D NU. clauses_to_update_prop Q M (L, C)#} \<subseteq># add_mset (L, D) WS\<close>
    using ws no_dup unfolding clauses_to_update_inv.simps NU
    by (auto simp: all_conj_distrib)
  then have IH: \<open>Pair L `# {#C \<in># NU. clauses_to_update_prop Q M (L, C)#} \<subseteq># WS\<close>
    using w_q_p_D by auto
  have IH_Q: \<open>\<And>La L' C. C \<in># add_mset D NU \<Longrightarrow> watched C = {#La, L'#} \<Longrightarrow> - La \<in> lits_of_l M \<Longrightarrow>
    L' \<notin> lits_of_l M \<Longrightarrow> (La, C) \<notin># add_mset (L, D) WS \<Longrightarrow> La \<in># Q\<close>
    using ws no_dup unfolding clauses_to_update_inv.simps NU
    by (auto simp: all_conj_distrib)
  have Q_M_L_WS: \<open>Pair L `# {#C \<in># N + U. clauses_to_update_prop Q M (L, C)#} \<subseteq># add_mset (L, D) WS\<close>
    using ws by (auto simp del: filter_union_mset)
  then have Q_M_L_WS: \<open>Pair L `# {#C \<in># NU. clauses_to_update_prop Q M (L, C)#} \<subseteq># WS\<close>
    by (auto simp del: filter_union_mset simp: NU w_q_p_D)

  have L_ne_L': \<open>L \<noteq> L'\<close>
    using struct_D D watched by auto

  show ?case
    unfolding Ball_def twl_st_exception_inv.simps twl_exception_inv.simps
  proof (intro allI conjI impI)
    fix C J J' K''
    assume C: \<open>C \<in># N' + U'\<close> and
      watched_C: \<open>watched C = {#J, J'#}\<close> and
      J: \<open>- J \<in> lits_of_l M\<close> and
      J': \<open>J' \<notin> lits_of_l M\<close> and
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
      have JL[simp]: \<open>J = L'\<close> and J'K[simp]: \<open>J' = K\<close>
        using CD J J' watched_C watched L' D uK_M undef
        by (auto simp: add_mset_eq_add_mset)
      have \<open>K'' \<noteq> K\<close>
        using K'' uK_M uL D L'_L'_UWD unfolding CD
        by (cases D) auto
      have K''_unwatched_L: \<open>K'' \<in>#  remove1_mset K (unwatched D) \<or> K'' = L\<close>
        using K'' unfolding CD by (cases D) auto
      have \<open>no_dup M\<close>
        using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: trail.simps)
      then have False if \<open>- L' \<in> lits_of_l M\<close> \<open>L' \<in> lits_of_l M\<close>
        using that consistent_interp_def distinct_consistent_interp by blast
      have H: \<open>\<And>x La L'. x \<in># N + U \<Longrightarrow>
            watched x = {#La, L'#} \<Longrightarrow> - La \<in> lits_of_l M \<Longrightarrow>
            L' \<notin> lits_of_l M \<Longrightarrow> La \<notin># Q \<Longrightarrow> (La, x) \<notin># add_mset (L, D) WS \<Longrightarrow>
            (\<forall>xa. xa \<in># unwatched x \<longrightarrow> - xa \<in> lits_of_l M)\<close>
        using twl_excep[unfolded twl_st_exception_inv.simps Ball_def twl_exception_inv.simps]
        by blast
      have LL': \<open>L \<noteq> L'\<close>
        using struct_D watched by (cases D) auto
      have L'D_WS: \<open>(L', D) \<notin># WS\<close>
        using no_dup LL' by (auto dest: multi_member_split)
      have \<open>\<And>xa. xa \<in># unwatched D \<Longrightarrow> - xa \<in> lits_of_l M\<close> if \<open>- L' \<in> lits_of_l M\<close> and \<open>L' \<notin># Q\<close>
        using H[of D L' L] D_N_U watched LL' that L'D_WS K'' that
        by (auto simp: add_mset_eq_add_mset L_M)

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
          using H[of D L' L] D_N_U watched LL' L'D_WS K'' J
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
      using watched uK_M struct_D by (cases D) (auto simp: clauses_to_update_prop.simps add_mset_eq_add_mset LK)
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
      by (fastforce simp: filter_mset_empty_conv clauses_to_update_prop.simps
          add_mset_eq_add_mset watched_D all_conj_distrib)
  next
    case (Q K' K'' C) note C = this(1) and uK'_M = this(2) and uK''_M = this(3) and KC_WS = this(4)
      and watched_C = this(5)
    have ?case if CD: \<open>C \<noteq> D\<close> \<open>C \<noteq> ?D\<close>
      using IH_Q[of C K' K''] (* IH_Q[of C K'' K'] *)  CD watched uK_M L'  L_ne_L' L_M uK'_M uK''_M
        Q unfolding N'U' NU
      by auto
    moreover have ?case if CD: \<open>C = D\<close>
    proof -
      consider
        (KL)   \<open>K' = L\<close> \<open>K'' = L'\<close> |
        (K'L') \<open>K' = L'\<close> \<open>K'' = L\<close>
        using watched watched_C CD by (auto simp: add_mset_eq_add_mset)
      then show ?thesis
      proof cases
        case KL note [simp] = this
        have \<open>(L, C) \<in># Pair L `# {#C \<in># NU. clauses_to_update_prop Q M (L, C)#}\<close>
          using CD C w_q_p_D unfolding NU N'U' by (auto simp: pair_in_image_Pair D_ne_D)
        then have \<open>(L, C) \<in># WS\<close>
          using IH by blast
        then have False using KC_WS unfolding CD by simp
        then show ?thesis by fast
      next
        case K'L' note [simp] = this
        show ?thesis
          by (rule IH_Q[of C _ K'']) (use CD watched_C uK'_M uK''_M KC_WS L_ne_L' in auto)
      qed
    qed
    moreover {
      have \<open>(L', D) \<notin># WS\<close>
        using no_dup L_ne_L' by (auto simp: all_conj_distrib)
      then have ?case if CD: \<open>C = ?D\<close>
        using IH_Q[of D L L'] IH_Q[of D L' L]  CD watched watched_D watched_C watched uK_M L'  L_ne_L' L_M uK'_M uK''_M
          D_ne_D C unfolding NU N'U'
        by (auto simp: add_mset_eq_add_mset all_conj_distrib imp_conjR) }

    ultimately show ?case
      by blast
  qed
qed

lemma twl_cp_twl_inv:
  assumes
    cdcl: "cdcl_twl_cp S T" and
    twl: "twl_st_inv S" and
    valid: "valid_annotation S" and
    inv: "cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S)" and
    twl_excep: \<open>twl_st_exception_inv S\<close> and
    no_dup: \<open>no_duplicate_queued S\<close>
  shows \<open>twl_st_inv T\<close>
  using cdcl twl valid inv twl_excep no_dup
proof (induction rule: cdcl_twl_cp.induct)
  case (pop M N U NP UP L Q) note inv = this(1)
  then show ?case unfolding twl_st_inv.simps twl_is_an_exception_def
    by (fastforce simp add: pair_in_image_Pair)
next
  case (propagate D L L' M N U NP UP WS Q) note watched = this(1) and undef = this(2) and
    twl = this(4) and valid = this(5) and inv = this(6)
  have uL'_M[simp]: \<open>- L' \<notin> lits_of_l M\<close>
    using Decided_Propagated_in_iff_in_lits_of_l propagate.hyps(2) by blast
  have D_N_U: \<open>D \<in># N + U\<close>
    using valid by auto
  then have wf_D: \<open>struct_wf_twl_cls D\<close>
    using twl by (simp add: twl_st_inv.simps)
  have [simp]: \<open>- L \<in> lits_of_l M\<close>
    using valid by auto
  show ?case unfolding twl_st_simps Ball_def
  proof (intro allI conjI impI)
    fix C
    assume C: \<open>C \<in># N + U\<close>
    show \<open>struct_wf_twl_cls C\<close>
      using twl C by (auto simp: twl_st_inv.simps)[]
    have watched_max: \<open>watched_literals_false_of_max_level M C\<close>
      using twl C by (auto simp: twl_st_inv.simps)
    then show \<open>watched_literals_false_of_max_level (Propagated L' (clause D) # M) C\<close>
      by (cases C) (auto simp: get_level_cons_if)

    assume excep: \<open>\<not>twl_is_an_exception C (add_mset (- L') Q) WS\<close>
    show \<open>twl_lazy_update (Propagated L' (clause D) # M) C\<close>
      apply (rule lazy_update_Propagated)
      using excep apply (simp add: twl_is_an_exception_add_mset_to_queue; fail)
      using twl C by (auto simp add: twl_st_inv.simps)[]
    have \<open>\<not> twl_is_an_exception C Q (add_mset (L, D) WS)\<close> if \<open>C \<noteq> D\<close>
      using excep that by (auto simp add: twl_is_an_exception_def)
    then have \<open>twl_inv M C\<close> if \<open>C \<noteq> D\<close>
      using twl that C by (auto simp: twl_st_inv.simps)
    moreover
      have "atm_of L' \<notin> atm_of ` lits_of_l M"
        using uL'_M by (meson Decided_Propagated_in_iff_in_lits_of_l atm_of_in_atm_of_set_in_uminus
            undef)
    ultimately have twl_C: \<open>twl_inv (Propagated L' (clause D) # M) C\<close> if \<open>C \<noteq> D\<close>
      using watched_max undef that by (cases C) (auto simp: count_decided_ge_get_level
          Decided_Propagated_in_iff_in_lits_of_l get_level_cons_if rev_image_eqI)
    have D: \<open>D \<in># N + U\<close> and \<open>L \<in># watched D\<close>
      using valid by auto
    have lev_L: \<open>get_level M L = count_decided M\<close>
      using valid by auto

    have twl_D: \<open>twl_inv (Propagated L' (clause D) # M) D\<close>
      by (cases D, cases \<open>atm_of L = atm_of L'\<close>)
        (use watched in \<open>auto simp: add_mset_eq_add_mset lev_L\<close>)

    show \<open>twl_inv (Propagated L' (clause D) # M) C\<close>
      using twl_C twl_D by blast
  qed
next
  case (conflict D L L' M N U NP UP WS Q) note twl = this(4)
  then show ?case
    by (auto simp: twl_st_inv.simps)
next
  case (delete_from_working D L L' M N U NP UP WS Q) note watched = this(1) and L' = this(2) and
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
    have twl_D: \<open>twl_lazy_update M D\<close>
      by (cases D) (use watched L' in \<open>auto simp: add_mset_eq_add_mset\<close>)
    have twl_C: \<open>twl_lazy_update M C\<close> if \<open>C \<noteq> D\<close>
      using twl C excep that by (auto simp add: twl_st_inv.simps
          twl_is_an_exception_add_mset_to_clauses_to_update)

    show \<open>twl_lazy_update M C\<close>
      using twl_C twl_D by blast
    have \<open>\<not> twl_is_an_exception C Q (add_mset (L, D) WS)\<close> if \<open>C \<noteq> D\<close>
      using excep that by (auto simp add: twl_is_an_exception_def)
    then have twl_C: \<open>twl_inv M C\<close> if \<open>C \<noteq> D\<close>
      using twl that C by (auto simp: twl_st_inv.simps)
    have D: \<open>D \<in># N + U\<close> and \<open>L \<in># watched D\<close>
      using valid by auto
    have lev_L: \<open>get_level M L = count_decided M\<close>
      using valid by auto
    have twl_D: \<open>twl_inv M D\<close>
      by (cases D) (use L L' watched in \<open>auto simp: add_mset_eq_add_mset lev_L
          count_decided_ge_get_level\<close>)

    show \<open>twl_inv M C\<close>
      using twl_C twl_D by blast
  qed
next
  case (update_clause D L L' M K N U N' U' NP UP WS Q) note watched = this(1) and uL = this(2) and
    L' = this(3) and K = this(4) and undef = this(5) and N'U' = this(6) and twl = this(7) and
    valid = this(8) and inv = this(9) and twl_excep = this(10) and
    no_dup = this(11)
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
  have lev_L': \<open>get_level M L' = count_decided M\<close> if \<open>- L' \<in> lits_of_l M \<close>
    using L_M w_max_D D watched L' uL that by (auto simp: add_mset_eq_add_mset)

  show ?case unfolding twl_st_simps Ball_def
  proof (intro allI conjI impI)
    fix C
    assume C: \<open>C \<in># N' + U'\<close>
    moreover have \<open>L \<noteq> L'\<close>
      using struct_D watched by (auto simp: D dest: multi_member_split)
    ultimately have struct_D': \<open>struct_wf_twl_cls ?D\<close>
      using L K struct_D watched by (auto simp: D L'_UWD L'_L'_UWD dest: in_diffD)

    have struct_C: \<open>struct_wf_twl_cls C\<close> if \<open>C \<noteq> ?D\<close>
      using twl C that N'U' by (fastforce simp: twl_st_inv.simps elim!: update_clausesE split: if_splits dest: in_diffD)
    show \<open>struct_wf_twl_cls C\<close>
      using struct_D' struct_C by blast

    have \<open>watched_literals_false_of_max_level M C\<close> if \<open>C \<noteq> ?D\<close>
      using twl C that N'U' by (fastforce simp: twl_st_inv.simps elim!: update_clausesE dest: in_diffD)
    moreover have \<open>watched_literals_false_of_max_level M ?D\<close>
      using w_max_D D watched L' uK_M distinct_consistent_interp[OF n_d] uL
      by (auto simp: add_mset_eq_add_mset consistent_interp_def)
    ultimately show \<open>watched_literals_false_of_max_level M C\<close>
      by blast

    assume excep: \<open>\<not>twl_is_an_exception C Q WS\<close>
    have H: \<open>\<And>C. C \<in># N+U \<Longrightarrow> \<not> twl_is_an_exception C Q WS \<Longrightarrow> C \<noteq> D \<Longrightarrow> twl_lazy_update M C \<and> twl_inv M C \<close>
      using twl by (auto simp add: twl_st_inv.simps twl_is_an_exception_add_mset_to_clauses_to_update)[]
    have excep_WS: \<open>\<not> twl_is_an_exception C Q WS\<close>
      using excep C by (force simp: twl_is_an_exception_def)
    have \<open>twl_lazy_update M C\<close> if \<open>C \<noteq> ?D\<close> \<open>C \<noteq> D\<close>
      using H[of C] that excep_WS * C
      by (auto simp add: twl_st_inv.simps)[]
    moreover have \<open>twl_lazy_update M C\<close> if \<open>C = D\<close>
      using H[of C] that excep_WS * C D count_decided_ge_get_level w_max_D by auto
    moreover {
      have D': \<open>?D = TWL_Clause {#K, L'#} (add_mset L (remove1_mset K UWD))\<close>
        using D watched by auto
      have \<open>twl_lazy_update M ?D\<close>
        using watched uL L' undef unfolding D' twl_lazy_update.simps
        by (auto simp: uK_M D add_mset_eq_add_mset lev_L lev_L' count_decided_ge_get_level)
      }
    ultimately show \<open>twl_lazy_update M C\<close>
      by blast
    have \<open>\<not> twl_is_an_exception C Q (add_mset (L, D) WS)\<close> if \<open>C \<noteq> D\<close>
      using excep that by (force simp add: twl_is_an_exception_def)
    then have twl_C: \<open>twl_inv M C\<close> if \<open>C \<noteq> ?D\<close> \<open>C \<noteq> D\<close>
      using twl that C * by (auto simp: twl_st_inv.simps)
    then have twl_C_D: \<open>twl_inv M C\<close> if \<open>C = D\<close>
      by (smt L L' L_M \<open>watched_literals_false_of_max_level M C\<close> count_decided_ge_get_level
          diff_union_swap empty_iff remove_1_mset_id_iff_notin set_mset_empty that twl_clause.sel(1)
          twl_inv.elims(3) watched watched_literals_false_of_max_level.simps)
    have D_N_U: \<open>D \<in># N + U\<close> and \<open>L \<in># watched D\<close>
      using valid by auto
    have lev_L: \<open>get_level M L = count_decided M\<close>
      using valid by auto

    have in_remove1_mset: \<open>K' \<in># remove1_mset K UWD \<longleftrightarrow> K' \<noteq> K \<and> K' \<in># UWD\<close> for K'
      using struct_D L'_L'_UWD by (auto simp: D in_remove1_mset_neq dest: in_diffD)

    have [simp]: \<open>(L', TWL_Clause {#L', L#} UWD) \<notin># WS\<close>
      using no_dup \<open>L \<noteq> L'\<close> by auto
    have \<open>twl_exception_inv (M, N, U, None, NP, UP, add_mset (L, D) WS, Q) D\<close>
      using twl_excep D_N_U by simp
    then have H: \<open>- K \<in> lits_of_l M\<close> if \<open>- L' \<in> lits_of_l M\<close> and \<open>L' \<notin># Q\<close> and \<open>K \<in># UWD\<close> for K
      using D watched \<open>L \<noteq> L'\<close> uL that L_M by (simp add: add_mset_eq_add_mset twl_exception_inv.simps)

    then have twl_D: \<open>twl_inv M ?D\<close>
      by (use watched uK_M uL D in
          \<open>auto simp: add_mset_eq_add_mset lev_L lev_L' count_decided_ge_get_level
          in_remove1_mset H\<close>)

    have twl_D': \<open>twl_inv M C\<close> if \<open>L' \<in># Q\<close> and \<open>C = ?D\<close>
      using excep that watched
      by (cases D) (auto simp: twl_is_an_exception_def)

    show \<open>twl_inv M C\<close>
      using twl_C twl_D twl_D' twl_C_D by blast
  qed
qed

lemma twl_cp_no_duplicate_queued:
  assumes
    cdcl: "cdcl_twl_cp S T" and
    no_dup: \<open>no_duplicate_queued S\<close>
  shows "no_duplicate_queued T"
  using cdcl no_dup
proof (induction rule: cdcl_twl_cp.induct)
  case (pop M N U NP UP L Q)
  then show ?case
    by (auto simp: image_Un image_image subset_mset.less_imp_le
        dest: mset_subset_eq_insertD)
qed auto

lemma distinct_mset_Pair: "distinct_mset (Pair L `# C) \<longleftrightarrow> distinct_mset C"
  by (induction C) auto

lemma distinct_image_mset_clause:
  \<open>distinct_mset (clause `# C) \<Longrightarrow> distinct_mset C\<close>
  by (induction C) auto

lemma twl_cp_distinct_queued:
  assumes
    cdcl: "cdcl_twl_cp S T" and
    twl: "twl_st_inv S" and
    valid: "valid_annotation S" and
    inv: "cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S)" and
    no_dup: \<open>no_duplicate_queued S\<close> and
    dist: \<open>distinct_queued S\<close>
  shows "distinct_queued T"
  using cdcl twl valid inv no_dup dist
proof (induction rule: cdcl_twl_cp.induct)
  case (pop M N U NP UP L Q) note c_dist = this(4) and dist = this(5)
  show ?case
    using dist by (auto simp: distinct_mset_Pair count_image_mset_Pair simp del: image_mset_union)
next
  case (propagate D L L' M N U NP UP WS Q) note watched = this(1) and undef = this(2) and
    twl = this(4) and valid = this(5)  and inv = this(6) and no_dup = this(7)
    and dist = this(8)
  have \<open>L' \<notin> lits_of_l M\<close>
    using Decided_Propagated_in_iff_in_lits_of_l propagate.hyps(2) by auto
  then have \<open>-L' \<notin># Q\<close>
    using no_dup by (fastforce simp: lits_of_def dest!: mset_subset_eqD)
  then show ?case
    using dist by (auto simp: all_conj_distrib split: if_splits dest!: Suc_leD)
next
  case (conflict D L L' M N U NP UP WS Q) note dist = this(8)
  then show ?case
    by auto
next
  case (delete_from_working D L L' M N U NP UP WS Q) note dist = this(7)
  show ?case using dist by (auto simp: all_conj_distrib split: if_splits dest!: Suc_leD)
next
  case (update_clause D L L' M K N U N' U' NP UP WS Q) note watched = this(1) and uL = this(2) and
    L' = this(3) and K = this(4) and undef = this(5) and N'U' = this(6) and twl = this(7) and
    valid = this(8) and inv = this(9) and  no_dup = this(10) and dist = this(11)

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
        using LD N'U' apply (auto simp: all_conj_distrib elim!: update_clausesE intro: le_SucI; fail)[]
        using LC[of L C] N'U' by (auto simp: all_conj_distrib elim!: update_clausesE intro: le_SucI)[]
    qed
  next
    fix L L' C C'
    show \<open>(L, C) \<in># WS \<longrightarrow> (L', C') \<in># WS \<longrightarrow> L = L'\<close>
      using dist by auto
  qed
qed

lemma twl_cp_valid:
  assumes
    cdcl: "cdcl_twl_cp S T" and
    twl: "twl_st_inv S" and
    valid: "valid_annotation S" and
    inv: "cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S)" and
    no_dup: \<open>no_duplicate_queued S\<close> and
    dist: \<open>distinct_queued S\<close>
  shows "valid_annotation T"
  using cdcl twl valid inv no_dup dist
proof (induction rule: cdcl_twl_cp.induct)
  case (pop M N U NP UP L Q) note valid = this(2)
  then show ?case
    by (auto simp del: filter_union_mset)
next
  case (propagate D L L' M N U NP UP WS Q) note watched = this(1) and twl = this(4) and valid = this(5)
    and inv = this(6) and no_taut = this(7)
  show ?case
    using valid by (auto dest: mset_subset_eq_insertD simp: get_level_cons_if)
next
  case (conflict D L L' M N U NP UP WS Q) note valid = this(5)
  then show ?case
    by auto
next
  case (delete_from_working D L L' M N U NP UP WS Q) note watched = this(1) and L' = this(2) and
  twl = this(3) and valid = this(4) and inv = this(5)
  show ?case unfolding twl_st_simps Ball_def
    using valid by (auto dest: mset_subset_eq_insertD)
next
  case (update_clause D L L' M K N U N' U' NP UP WS Q) note watched = this(1) and uL = this(2) and
    L' = this(3) and K = this(4) and undef = this(5) and N'U' = this(6) and twl = this(7) and
    valid = this(8) and inv = this(9) and no_dup = this(10) and dist = this(11)
  show ?case
    unfolding valid_annotation.simps Ball_def
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
      have "D \<in># remove1_mset D (U + N)"
        using D_DN_U by (simp add: union_commute)
      then have "D \<in># U + remove1_mset D N"
        using that(1) by (metis (no_types) add_mset_remove_trivial insert_DiffM union_mset_add_mset_right) (* 110 ms *)
      then show "D \<in># remove1_mset D N"
        using that(2) by (meson union_iff)
    qed
    have D_D_U: \<open>D \<in># remove1_mset D U\<close> if \<open>D \<in># U\<close> and \<open>D \<notin># N\<close> and [simp]: \<open>C = D\<close>
    proof -
      have "D \<in># remove1_mset D (U + N)"
        using D_DN_U by (simp add: union_commute)
      then have "D \<in># N + remove1_mset D U"
        using D_DN_U that(1) by fastforce
      then show "D \<in># remove1_mset D U"
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
    cdcl: "cdcl_twl_cp S T" and
    twl: "twl_st_inv S" and
    valid: "valid_annotation S" and
    inv: "cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S)" and
    twl_excep: \<open>twl_st_exception_inv S\<close> and
    no_dup: \<open>no_duplicate_queued S\<close> and
    cands: \<open>propa_cands_enqueued S\<close> and
    ws: \<open>clauses_to_update_inv S\<close>
  shows "propa_cands_enqueued T"
  using cdcl twl valid inv twl_excep no_dup cands ws
proof (induction rule: cdcl_twl_cp.induct)
  case (pop M N U NP UP L Q) note inv = this(1) and valid = this(2) and cands = this(6)
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
  case (propagate D L L' M N U NP UP WS Q) note watched = this(1) and undef = this(2) and
    twl = this(4) and valid = this(5) and inv = this(6) and excep = this(7)
    and no_dup = this(8) and cands = this(9)
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
        have "K = L'"
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
        moreover have \<open>twl_st_inv (Propagated L' (clause D) # M, N, U, None, NP, UP, WS, add_mset (- L') Q)\<close>
          using twl_cp_twl_inv[OF _ twl valid inv excep no_dup]
          cdcl_twl_cp.propagate[OF propagate(1-3)] by fast
        ultimately have \<open>twl_lazy_update (Propagated L' (clause D) # M) C\<close> and
           twl_inv: \<open>twl_inv (Propagated L' (clause D) # M) C\<close>
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
        have H': \<open>\<forall>La L'. watched C = {#La, L'#} \<longrightarrow> - La \<in> lits_of_l M \<longrightarrow> L' \<notin> lits_of_l M \<longrightarrow>
          (\<forall>K\<in>#unwatched C. - K \<in> lits_of_l M)\<close>
          using excep C CD Q W WS uab uba by (auto simp: twl_exception_inv.simps)
        then have \<open>\<forall>K\<in>#unwatched C. - K \<in> lits_of_l M\<close>
          using uab uba W C_W_UW ua_or_ub by (auto simp: add_mset_eq_add_mset all_conj_distrib)
        then show False
          by (metis Decided_Propagated_in_iff_in_lits_of_l L' uminus_lit_swap
              Q clause.simps in_diffD propagate.hyps(2) twl_clause.collapse union_iff)
      qed

      ultimately show ?thesis by fast
    qed
  qed
next
  case (conflict D L L' M N U NP UP WS Q) note cands = this(10)
  then show ?case
    by auto
next
  case (delete_from_working D L L' M N U NP UP WS Q) note watched = this(1) and L' = this(2) and
  twl = this(3) and valid = this(4) and inv = this(5) and cands = this(8) and ws = this(9)
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
        local.K n_d by (cases D) fastforce
    ultimately show \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># Q) \<or> (\<exists>L. (L, C) \<in># WS)\<close>
      by auto
  qed
next
  case (update_clause D L L' M K N U N' U' NP UP WS Q) note watched = this(1) and uL = this(2) and
    L' = this(3) and K = this(4) and undef = this(5) and N'U' = this(6) and twl = this(7) and
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
  have lev_L': \<open>get_level M L' = count_decided M\<close> if \<open>- L' \<in> lits_of_l M \<close>
    using L_M w_max_D D watched L' uL that by (auto simp: add_mset_eq_add_mset)
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
        by (metis D clause.simps in_remove1_mset_neq twl_clause.sel(2) union_iff update_clause.hyps(4))

      have uL'_M: \<open>- L' \<in> lits_of_l M\<close>
        using D watched L'_M_C by auto
      have [simp]: \<open>L \<noteq> L'\<close> \<open>L' \<noteq> L\<close>
        using struct_D D watched by auto

      assume \<open>\<not> ((\<exists>L'. L' \<in># watched C \<and> L' \<in># Q) \<or> (\<exists>L. (L, C) \<in># WS))\<close>
      then have [simp]: \<open>L' \<notin># Q\<close> and L'_C_WS: \<open>(L', C) \<notin># WS\<close>
        using watched D by auto

      have [simp]: \<open>(L', TWL_Clause {#L', L#} UWD) \<notin># WS\<close>
        using no_dup by (auto simp: all_conj_distrib)
      have \<open>?D \<noteq> D\<close>
        using C D watched L K uK_M uL by auto
      then have excep: \<open>twl_exception_inv (M, N, U, None, NP, UP, add_mset (L, D) WS, Q) D\<close>
        using twl_excep *[of D] D_N_U by (auto simp: twl_st_inv.simps)
      then have \<open>\<forall>K \<in># unwatched D. -K \<in> lits_of_l M\<close>
        using D watched L'_M_C
        by (auto simp: add_mset_eq_add_mset uL'_M L_M uL twl_exception_inv.simps
            true_annots_true_cls_def_iff_negation_in_model dest: in_diffD)
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

      have HH: \<open>\<not>clauses_to_update_prop (add_mset (-L') Q) (Propagated L' (clause D) # M) (L, D)\<close>
        unfolding clauses_to_update_prop.simps by (auto simp: watched)
      have \<open>add_mset L Q \<subseteq># {#- lit_of x. x \<in># mset M#}\<close>
        using no_dup by (auto)
      moreover have \<open>distinct_mset {#- lit_of x. x \<in># mset M#}\<close>
        by (subst distinct_image_mset_inj)
          (use n_d in \<open>auto simp: lit_of_inj_on_no_dup distinct_map no_dup_def\<close>)
      ultimately have [simp]: \<open>L \<notin># Q\<close>
        by (metis distinct_mset_add_mset distinct_mset_union subset_mset.le_iff_add)
      have w_q_p_D: \<open>clauses_to_update_prop Q M (L, D)\<close>
        by (auto simp: clauses_to_update_prop.simps watched)
           (use uL undef L' in \<open>auto simp: Decided_Propagated_in_iff_in_lits_of_l\<close>)
      have \<open>Pair L `# {#C \<in># add_mset D NU. clauses_to_update_prop Q M (L, C)#} \<subseteq># add_mset (L, D) WS\<close>
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
    cdcl: "cdcl_twl_cp S T" and
    twl: "twl_st_inv S" and
    valid: "valid_annotation S" and
    inv: "cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S)" and
    excep: \<open>twl_st_exception_inv S\<close> and
    no_dup: \<open>no_duplicate_queued S\<close> and
    cands: \<open>confl_cands_enqueued S\<close> and
    ws: \<open>clauses_to_update_inv S\<close>
  shows
    "confl_cands_enqueued T"
  using cdcl
proof (induction rule: cdcl_twl_cp.cases)
  case (pop M N U NP UP L Q) note S = this(1) and T = this(2)
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
  case (propagate D L L' M N U NP UP WS Q) note S = this(1) and T = this(2) and watched = this(3)
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
        using cands C lazy_update_Propagated by (auto simp: S)
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
        moreover have \<open>twl_st_inv (Propagated L' (clause D) # M, N, U, None, NP, UP, WS, add_mset (- L') Q)\<close>
          using twl_cp_twl_inv[OF _ twl valid inv excep no_dup] cdcl unfolding S T by fast
        ultimately have \<open>twl_lazy_update (Propagated L' (clause D) # M) C\<close> and
           twl_inv: \<open>twl_inv (Propagated L' (clause D) # M) C\<close>
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
          (\<forall>K\<in>#unwatched C. - K \<in> lits_of_l M)\<close>
          using excep C CD Q W WS uab uba by (auto simp: twl_exception_inv.simps S)
        then have \<open>\<forall>K\<in>#unwatched C. - K \<in> lits_of_l M\<close>
          using uab uba W C_W_UW ua_ub by (auto simp: add_mset_eq_add_mset all_conj_distrib)
        then show False
          by (metis Decided_Propagated_in_iff_in_lits_of_l L' uminus_lit_swap
              Q clause.simps undef twl_clause.collapse union_iff)
      qed
      ultimately show ?thesis by fast
    qed
  qed
next
  case (conflict D L L' M N U NP UP WS Q)
  then show ?case
    by auto
next
  case (delete_from_working D L L' M N U NP UP WS Q) note S = this(1) and T = this(2) and
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
          simp: consistent_interp_def)
    ultimately show \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># Q) \<or> (\<exists>L. (L, C) \<in># WS)\<close>
      by auto
  qed
next
  case (update_clause D L L' M K N U N' U' NP UP WS Q) note S = this(1) and T = this(2) and
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
  have lev_L': \<open>get_level M L' = count_decided M\<close> if \<open>- L' \<in> lits_of_l M \<close>
    using L_M w_max_D D watched L' uL that by (auto simp: add_mset_eq_add_mset)
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

      have HH: \<open>\<not>clauses_to_update_prop (add_mset (-L') Q) (Propagated L' (clause D) # M) (L, D)\<close>
        unfolding clauses_to_update_prop.simps by (auto simp: watched)
      have \<open>add_mset L Q \<subseteq># {#- lit_of x. x \<in># mset M#}\<close>
        using no_dup by (auto simp: S)
      moreover have \<open>distinct_mset {#- lit_of x. x \<in># mset M#}\<close>
        by (subst distinct_image_mset_inj)
          (use n_d in \<open>auto simp: lit_of_inj_on_no_dup distinct_map no_dup_def\<close>)
      ultimately have [simp]: \<open>L \<notin># Q\<close>
        by (metis distinct_mset_add_mset distinct_mset_union subset_mset.le_iff_add)
      have w_q_p_D: \<open>clauses_to_update_prop Q M (L, D)\<close>
        by (auto simp: clauses_to_update_prop.simps watched)
           (use uL undef L' in \<open>auto simp: Decided_Propagated_in_iff_in_lits_of_l\<close>)
      have \<open>Pair L `# {#C \<in># add_mset D NU. clauses_to_update_prop Q M (L, C)#} \<subseteq># add_mset (L, D) WS\<close>
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
    cdcl: "cdcl_twl_cp S T" and
    twl: "twl_st_inv S" and
    valid: "valid_annotation S" and
    inv: "cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S)" and
    twl_excep: \<open>twl_st_exception_inv S\<close> and
    no_dup: \<open>no_duplicate_queued S\<close> and
    past_invs: \<open>past_invs S\<close>
  shows \<open>past_invs T\<close>
  using cdcl twl valid inv twl_excep no_dup past_invs
proof (induction rule: cdcl_twl_cp.induct)
  case (pop M N U NP UP L Q) note past_invs = this(6)
  then show ?case
    by (subst past_invs_enqueud, subst (asm) past_invs_enqueud)
next
  case (propagate D L L' M N U NP UP WS Q) note watched = this(1) and twl = this(4) and valid = this(5)
    and inv = this(6) and past_invs = this(9)
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
    then show \<open>twl_lazy_update M1 C\<close> and \<open>twl_inv M1 C\<close> and \<open>watched_literals_false_of_max_level M1 C\<close>
      and \<open>twl_exception_inv (M1, N, U, None, NP, UP, {#}, {#}) C\<close>
      using C past_invs by (auto simp add: past_invs.simps)
  next
    fix M1 M2 :: \<open>('a, 'a clause) ann_lits\<close> and K
    assume \<open>Propagated L' (clause D) # M = M2 @ Decided K # M1\<close>
    then have M: \<open>M = tl M2 @ Decided K # M1\<close>
      by (meson cdcl\<^sub>W_restart_mset.propagated_cons_eq_append_decide_cons)
    then show \<open>confl_cands_enqueued (M1, N, U, None, NP, UP, {#}, {#})\<close> and
      \<open>propa_cands_enqueued (M1, N, U, None, NP, UP, {#}, {#})\<close> and
      \<open>clauses_to_update_inv (M1, N, U, None, NP, UP, {#}, {#})\<close>
      using past_invs by (auto simp add: past_invs.simps)
  qed
next
  case (conflict D L L' M N U NP UP WS Q) note twl = this(9)
  then show ?case
    by (auto simp: past_invs.simps)
next
  case (delete_from_working D L L' M N U NP UP WS Q) note watched = this(1) and L' = this(2) and
  twl = this(3) and valid = this(4) and inv = this(5) and past_invs = this(8)
  show ?case unfolding past_invs.simps Ball_def
  proof (intro allI conjI impI)
    fix C
    assume C: \<open>C \<in># N + U\<close>

    fix M1 M2 :: \<open>('a, 'a clause) ann_lits\<close> and K
    assume \<open>M = M2 @ Decided K # M1\<close>
    then show \<open>twl_lazy_update M1 C\<close> and \<open>twl_inv M1 C\<close> \<open>watched_literals_false_of_max_level M1 C\<close> and
      \<open>twl_exception_inv (M1, N, U, None, NP, UP, {#}, {#}) C\<close>
      using C past_invs by (auto simp add: past_invs.simps)
  next
    fix M1 M2 :: \<open>('a, 'a clause) ann_lits\<close> and K
    assume \<open>M = M2 @ Decided K # M1\<close>
    then show \<open>confl_cands_enqueued (M1, N, U, None, NP, UP, {#}, {#})\<close> and
      \<open>propa_cands_enqueued (M1, N, U, None, NP, UP, {#}, {#})\<close> and
      \<open>clauses_to_update_inv (M1, N, U, None, NP, UP, {#}, {#})\<close>
      using past_invs by (auto simp add: past_invs.simps)
  qed
next
  case (update_clause D L L' M K N U N' U' NP UP WS Q) note watched = this(1) and uL = this(2) and
    L' = this(3) and K = this(4) and undef = this(5) and N'U' = this(6) and twl = this(7) and
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
  have lev_L': \<open>get_level M L' = count_decided M\<close> if \<open>- L' \<in> lits_of_l M \<close>
    using L_M w_max_D D watched L' uL that by (auto simp: add_mset_eq_add_mset)

  show ?case unfolding past_invs.simps Ball_def
  proof (intro allI conjI impI)
    fix C
    assume C: \<open>C \<in># N' + U'\<close>

    fix M1 M2 :: \<open>('a, 'a clause) ann_lits\<close> and K'
    assume M: \<open>M = M2 @ Decided K' # M1\<close>

    have H: False if \<open> - L' \<in> lits_of_l M1\<close>
    proof -
      have atm: \<open>undefined_lit (M2 @ [Decided K']) (-L')\<close>
        using that n_d by (metis M append.simps(1) append.simps(2) append_assoc
            cdcl\<^sub>W_restart_mset.no_dup_append_in_atm_notin)
      have uL_M: \<open>-L' \<in> lits_of_l M\<close>
        using that M by auto
      show False
        using lev_L'[OF uL_M] atm count_decided_ge_get_level[of M1 L']
        by (auto simp: M split: if_splits)
    qed
    have \<open>twl_exception_inv (M1, N, U, None, NP, UP, {#}, {#}) C\<close> if \<open>C \<noteq> ?D\<close>
      using * C past_invs that M by (auto simp add: past_invs.simps)
    then have \<open>twl_exception_inv (M1, N', U', None, NP, UP, {#}, {#}) C\<close> if \<open>C \<noteq> ?D\<close>
      using N'U' that by (auto simp add: twl_st_inv.simps twl_exception_inv.simps)
    moreover have \<open>twl_lazy_update M1 C\<close> \<open>twl_inv M1 C\<close> \<open>watched_literals_false_of_max_level M1 C\<close>
      if \<open>C \<noteq> ?D\<close>
      using * C twl past_invs M N'U' that by (auto simp add: past_invs.simps twl_exception_inv.simps)
    moreover have \<open>twl_lazy_update M1 ?D\<close> \<open>twl_inv M1 ?D\<close> \<open>watched_literals_false_of_max_level M1 ?D\<close>
      and \<open>twl_exception_inv (M1, N', U', None, NP, UP, {#}, {#}) ?D\<close>
      using D watched uK_M by (auto simp: M add_mset_eq_add_mset twl_exception_inv.simps dest!: H)
    ultimately show \<open>twl_lazy_update M1 C\<close> \<open>twl_inv M1 C\<close> \<open>watched_literals_false_of_max_level M1 C\<close>
      \<open>twl_exception_inv (M1, N', U', None, NP, UP, {#}, {#}) C\<close>
      by blast+
  next
    have [dest!]: \<open>C \<in># N' \<Longrightarrow> C \<in># N \<or> C = ?D\<close> \<open>C \<in># U' \<Longrightarrow> C \<in># U \<or> C = ?D\<close> for C
      using N'U' by (auto elim!: update_clausesE dest: in_diffD)
    fix M1 M2 :: \<open>('a, 'a clause) ann_lits\<close> and K'
    assume M: \<open>M = M2 @ Decided K' # M1\<close>
    then have \<open>confl_cands_enqueued (M1, N, U, None, NP, UP, {#}, {#})\<close> and
      \<open>propa_cands_enqueued (M1, N, U, None, NP, UP, {#}, {#})\<close> and
      w_q: \<open>clauses_to_update_inv (M1, N, U, None, NP, UP, {#}, {#})\<close>
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
          by (auto simp: lits_of_def uminus_lit_swap no_dup_def defined_lit_map dest: mk_disjoint_insert)
        then show False
          using lev_L_M count_decided_ge_get_level[of M1 L]
          by (auto simp: lits_of_def uminus_lit_swap M)
      qed
      then have \<open>\<not>M1 \<Turnstile>as CNot (remove1_mset K'' (clause ?D))\<close> for K''
        using K uK_M watched D unfolding M by (cases \<open>K'' = L\<close>) auto }
    ultimately show \<open>confl_cands_enqueued (M1, N', U', None, NP, UP, {#}, {#})\<close> and
      \<open>propa_cands_enqueued (M1, N', U', None, NP, UP, {#}, {#})\<close>
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
    have uL'_M1: \<open>- L' \<notin> lits_of_l M1\<close>
    proof (rule ccontr)
      assume uL': \<open>\<not> ?thesis\<close>
      then have uL'_M: \<open>-L' \<in> lits_of_l M\<close>
        unfolding M by auto
      have atm_L': \<open>undefined_lit (M2 @ [Decided K']) L'\<close>
        by (rule cdcl\<^sub>W_restart_mset.no_dup_uminus_append_in_atm_notin[of _ M1])
          (use n_d[unfolded M] uL' in auto)
      have \<open>get_level M L' = count_decided M\<close>
        using lev_L' uL'_M by fast
      moreover have \<open>get_level M L' = get_level M1 L'\<close>
        using atm_L' unfolding M by (auto simp: image_Un)
      moreover have \<open>count_decided M1 < count_decided M\<close>
        unfolding M by auto
      ultimately show False
        using count_decided_ge_get_level[of M1 L'] by simp
    qed
    show \<open>clauses_to_update_inv (M1, N', U', None, NP, UP, {#}, {#})\<close>
    proof (induction rule: clauses_to_update_inv_cases)
      case (WS_nempty L C)
      then show ?case by simp
    next
      case (WS_empty K'')
      have uK_M1: \<open>- K \<notin> lits_of_l M1\<close>
        using uK_M unfolding M by auto
      have \<open>\<not>clauses_to_update_prop {#} M1 (K'', ?D)\<close>
        using uK_M1 uL'_M1 by (auto simp: clauses_to_update_prop.simps watched_D add_mset_eq_add_mset)
      then show ?case
        using w_q unfolding clauses_to_update_inv.simps N'U' NU
        by (auto split: if_splits simp: all_conj_distrib watched_D add_mset_eq_add_mset)
    next
      case (Q J J' C)
      moreover have \<open>- K \<notin> lits_of_l M1\<close>
        using uK_M unfolding M by auto
      moreover have \<open>clauses_to_update_prop {#} M1 (L', D)\<close> if \<open>- L' \<in> lits_of_l M1\<close>
        using watched that uL'_M1 unfolding clauses_to_update_prop.simps by auto
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
    cdcl: "cdcl_twl_cp S T" and
    twl: "twl_st_inv S" and
    valid: "valid_annotation S" and
    inv: "cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S)"
  shows "cdcl\<^sub>W_restart_mset.propagate (state\<^sub>W_of S) (state\<^sub>W_of T) \<or>
    cdcl\<^sub>W_restart_mset.conflict (state\<^sub>W_of S) (state\<^sub>W_of T) \<or>
    (state\<^sub>W_of S = state\<^sub>W_of T \<and> (literals_to_update_measure T, literals_to_update_measure S) \<in> lexn less_than 2)"
  using cdcl twl valid inv
proof (induction rule: cdcl_twl_cp.induct)
  case (pop M N U L Q)
  then show ?case by (simp add: lexn2_conv)
next
  case (propagate D L L' M N U NP UP WS Q) note watched = this(1) and undef = this(2) and no_upd = this(3)
    and twl = this(4) and valid = this(5) and inv = this(6)
  let ?S = \<open>state\<^sub>W_of (M, N, U, None, NP, UP, add_mset (L, D) WS, Q)\<close>
  let ?T = \<open>state\<^sub>W_of (Propagated L' (clause D) # M, N, U, None, NP, UP, WS, add_mset (- L') Q)\<close>
  have "\<forall>s\<in>#clause `# U. \<not> tautology s"
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def by (simp_all add: cdcl\<^sub>W_restart_mset_state)
  have D_N_U: \<open>D \<in># N + U\<close>
    using valid by auto
  have \<open>cdcl\<^sub>W_restart_mset.propagate ?S ?T\<close>
    apply (rule cdcl\<^sub>W_restart_mset.propagate.intros[of _ \<open>clause D\<close> L'])
        apply (simp add: cdcl\<^sub>W_restart_mset_state; fail)
       apply (metis \<open>D \<in># N + U\<close> clauses_def state\<^sub>W_of.simps image_eqI
           in_image_mset union_iff)
      using watched apply (cases D, simp add: clauses_def; fail)
     using no_upd watched valid apply (cases D;
         simp add: trail.simps true_annots_true_cls_def_iff_negation_in_model; fail)
     using undef apply (simp add: trail.simps)
    by (simp add: cdcl\<^sub>W_restart_mset_state del: cdcl\<^sub>W_restart_mset.state_simp)
  then show ?case by blast
next
  case (conflict D L L' M N U NP UP WS Q) note watched = this(1) and defined = this(2)
    and no_upd = this(3) and twl = this(3) and valid = this(5) and inv = this(6)
  let ?S = "state\<^sub>W_of (M, N, U, None, NP, UP, add_mset (L, D) WS, Q)"
  let ?T = "state\<^sub>W_of (M, N, U, Some (clause D), NP, UP, {#}, {#})"
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
  have \<open>cdcl\<^sub>W_restart_mset.conflict ?S ?T\<close>
    apply (rule cdcl\<^sub>W_restart_mset.conflict.intros[of _ \<open>clause D\<close>])
       apply (simp add: cdcl\<^sub>W_restart_mset_state)
      apply (metis \<open>D \<in># N + U\<close> clauses_def state\<^sub>W_of.simps image_eqI
        in_image_mset union_iff)
     using watched defined valid \<open>M \<Turnstile>as CNot (unwatched D)\<close> apply (cases D; auto simp add: clauses_def
         trail.simps twl_st_inv.simps; fail)
    by (simp add: cdcl\<^sub>W_restart_mset_state del: cdcl\<^sub>W_restart_mset.state_simp)
  then show ?case by fast
next
  case (delete_from_working D L L' M N U NP UP WS Q)
  then show ?case by (simp add: lexn2_conv)
next
  case (update_clause D L L' M K N U N' U' NP UP WS Q) note unwatched = this(4) and
    valid = this(8)
  have \<open>D \<in># N + U\<close>
    using valid by auto
  have [simp]: \<open>clause (update_clause D L K) = clause D\<close>
    using valid unwatched by (cases D) (auto simp: diff_union_swap2[symmetric]
        simp del: diff_union_swap2)
  have \<open>state\<^sub>W_of (M, N, U, None, NP, UP, add_mset (L, D) WS, Q) =
    state\<^sub>W_of (M, N', U', None, NP, UP, WS, Q)\<close>
    \<open>(literals_to_update_measure (M, N', U', None, NP, UP, WS, Q), literals_to_update_measure (M, N, U, None, NP, UP, add_mset (L, D) WS, Q)) \<in> lexn less_than 2\<close>
    using update_clause \<open>D \<in># N + U\<close> by (cases \<open>D \<in># N\<close>)
      (fastforce simp: image_mset_remove1_mset_if elim!: update_clausesE
        simp add: lexn2_conv)+
  then show ?case by fast
qed

lemma cdcl_twl_o_cdcl\<^sub>W_o:
  assumes
    cdcl: "cdcl_twl_o S T" and
    twl: "twl_st_inv S" and
    valid: "valid_annotation S" and
    inv: "cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S)"
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o (state\<^sub>W_of S) (state\<^sub>W_of T)\<close>
  using cdcl twl valid inv
proof (induction rule: cdcl_twl_o.induct)
  case (decide M L N U NP UP) note undef = this(1) and atm = this(2)
  have \<open>cdcl\<^sub>W_restart_mset.decide (state\<^sub>W_of (M, N, U, None, NP, UP, {#}, {#}))
    (state\<^sub>W_of (Decided L # M, N, U, None, NP, UP, {#}, {#-L#}))\<close>
    apply (rule cdcl\<^sub>W_restart_mset.decide_rule)
       apply (simp add: cdcl\<^sub>W_restart_mset_state; fail)
      using undef apply (simp add: trail.simps; fail)
     using atm apply (simp add: cdcl\<^sub>W_restart_mset_state; fail)
    by (simp add: state_eq_def cdcl\<^sub>W_restart_mset_state del: cdcl\<^sub>W_restart_mset.state_simp)
  then show ?case
    by (blast dest: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o.intros)
next
  case (skip L D C' M N U NP UP) note LD = this(1) and D = this(2)
  show ?case
    apply (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o.bj)
    apply (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_bj.skip)
    apply (rule cdcl\<^sub>W_restart_mset.skip_rule)
        apply (simp add: trail.simps; fail)
       apply (simp add: cdcl\<^sub>W_restart_mset_state; fail)
      using LD apply (simp; fail)
     using D apply (simp; fail)
    by (simp add: state_eq_def cdcl\<^sub>W_restart_mset_state del: cdcl\<^sub>W_restart_mset.state_simp)
next
  case (resolve L D C M N U NP UP) note LD = this(1) and lev = this(2) and inv = this(5)
  have \<open>\<forall>La mark a b. a @ Propagated La mark # b = Propagated L C # M \<longrightarrow>
      b \<Turnstile>as CNot (remove1_mset La mark) \<and> La \<in># mark\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
     cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    by (auto simp: trail.simps)
  then have LC: \<open>L \<in># C\<close>
    by blast
  show ?case
    apply (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o.bj)
    apply (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_bj.resolve)
    apply (rule cdcl\<^sub>W_restart_mset.resolve_rule)
          apply (simp add: trail.simps; fail)
         apply (simp add: trail.simps; fail)
        using LC apply (simp add: trail.simps; fail)
       apply (simp add: cdcl\<^sub>W_restart_mset_state; fail)
      using LD apply (simp; fail)
     using lev apply (simp add: cdcl\<^sub>W_restart_mset_state; fail)
    by (simp add: state_eq_def cdcl\<^sub>W_restart_mset_state del: cdcl\<^sub>W_restart_mset.state_simp)
next
  case (backtrack_unit_clause L D K M1 M2 M D' i N U NP UP) note L_D = this(1) and
     decomp = this(2) and lev_L = this(3) and max_D'_L = this(4) and lev_D = this(5) and
     lev_K = this(6) and D'_D = this(8) and NU_D' = this(9) and inv = this(12) and D'[simp] = this(7)
  let ?S = \<open>state\<^sub>W_of (M, N, U, Some {#L#}, NP, UP, {#}, {#})\<close>
  let ?T = \<open>state\<^sub>W_of (Propagated L {#L#} # M1, N, U, None, NP, add_mset {#L#} UP, {#}, {#L#})\<close>
  have n_d: "no_dup M"
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (simp add: cdcl\<^sub>W_restart_mset_state)
  have "undefined_lit M1 L"
    apply (rule cdcl\<^sub>W_restart_mset.backtrack_lit_skiped[of ?S])
       using lev_L inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
       apply (simp add: cdcl\<^sub>W_restart_mset_state; fail)
      using decomp apply (simp add: trail.simps; fail)
     using lev_L inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
       apply (simp add: cdcl\<^sub>W_restart_mset_state; fail)
    using lev_K apply (simp add: trail.simps; fail)
    done
  obtain M3 where M3: \<open>M = M3 @ M2 @ Decided K # M1\<close>
    using decomp by (blast dest!: get_all_ann_decomposition_exists_prepend)
  have D: \<open>D = add_mset L (remove1_mset L D)\<close>
    using L_D by auto
  have "undefined_lit (M3 @ M2) K"
    using n_d unfolding M3 by auto
  then have [simp]: \<open>count_decided M1 = 0\<close>
    using lev_D lev_K by (auto simp: M3 image_Un)
  show ?case
    apply (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o.bj)
    apply (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_bj.backtrack)
    apply (rule cdcl\<^sub>W_restart_mset.backtrack_rule[of _ L \<open>remove1_mset L D\<close> K M1 M2 \<open>remove1_mset L D'\<close> i])
    subgoal using L_D by (simp add: cdcl\<^sub>W_restart_mset_state)
    subgoal using decomp by (simp add: cdcl\<^sub>W_restart_mset_state)
    subgoal using lev_L by (simp add: cdcl\<^sub>W_restart_mset_state)
    subgoal using max_D'_L L_D by (simp add: cdcl\<^sub>W_restart_mset_state)
    subgoal using lev_D L_D by (simp add: cdcl\<^sub>W_restart_mset_state)
    subgoal using lev_K by (simp add: cdcl\<^sub>W_restart_mset_state)
    subgoal using D'_D by (simp add: cdcl\<^sub>W_restart_mset_state)
    subgoal using NU_D' by (simp add: cdcl\<^sub>W_restart_mset_state clauses_def inf_sup_aci(6) sup.left_commute)
    subgoal using decomp unfolding state_eq_def state_def prod.inject
        by (simp add: cdcl\<^sub>W_restart_mset_state)
    done
next
  case (backtrack_nonunit_clause L D K M1 M2 M D' i N U NP UP L') note LD = this(1) and
    decomp = this(2) and lev_L = this(3) and max_lev = this(4) and i = this(5) and lev_K = this(6)
    and D'_D = this(8) and NU_D' = this(9) and L_D' = this(10) and L' = this(11-12) and inv = this(15)
  let ?S = \<open>state\<^sub>W_of (M, N, U, Some D, NP, UP, {#}, {#})\<close>
  let ?T = \<open>state\<^sub>W_of (Propagated L D # M1, N, U, None, NP, add_mset {#L#} UP, {#}, {#L#})\<close>
  have n_d: "no_dup M"
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (simp add: cdcl\<^sub>W_restart_mset_state)
  have "undefined_lit M1 L"
    apply (rule cdcl\<^sub>W_restart_mset.backtrack_lit_skiped[of ?S])
      using lev_L inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
      apply (simp add: cdcl\<^sub>W_restart_mset_state; fail)
     using decomp apply (simp add: trail.simps; fail)
    using lev_L inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
      apply (simp add: cdcl\<^sub>W_restart_mset_state; fail)
   using lev_K apply (simp add: trail.simps; fail)
   done
  obtain M3 where M3: \<open>M = M3 @ M2 @ Decided K # M1\<close>
    using decomp by (blast dest!: get_all_ann_decomposition_exists_prepend)

  have "undefined_lit (M3 @ M2) K"
    using n_d unfolding M3 by (auto simp: lits_of_def)
  then have count_M1: \<open>count_decided M1 = i\<close>
    using lev_K unfolding M3 by (auto simp: image_Un)
  have \<open>L \<noteq> L'\<close>
    using L' lev_L lev_K count_decided_ge_get_level[of M K] L' by auto
  then have D: \<open>add_mset L (add_mset L' (D' - {#L, L'#})) = D'\<close>
    using L' L_D'
    by (metis add_mset_diff_bothsides diff_single_eq_union insert_noteq_member mset_add)
  have D': \<open>remove1_mset L D' = add_mset L' (D' - {#L, L'#})\<close>
    by (subst D[symmetric]) auto
  show ?case
    apply (subst D[symmetric])
    apply (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o.bj)
    apply (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_bj.backtrack)
    apply (rule cdcl\<^sub>W_restart_mset.backtrack_rule[of _ L \<open>remove1_mset L D\<close> K M1 M2 \<open>remove1_mset L D'\<close> i])
    subgoal using LD by (simp add: cdcl\<^sub>W_restart_mset_state)
    subgoal using decomp by (simp add: trail.simps)
    subgoal using lev_L by (simp add: cdcl\<^sub>W_restart_mset_state; fail)
    subgoal using max_lev L_D' by (simp add: cdcl\<^sub>W_restart_mset_state get_maximum_level_add_mset)
    subgoal using i by (simp add: cdcl\<^sub>W_restart_mset_state)
    subgoal using lev_K i unfolding D' by (simp add: trail.simps)
    subgoal using D'_D by (simp add: mset_le_subtract)
    subgoal using NU_D' L_D' by (simp add: mset_le_subtract clauses_def inf_sup_aci(6) sup.left_commute)
    subgoal
      using decomp unfolding state_eq_def state_def prod.inject
      using i lev_K count_M1 L_D' by (simp add: cdcl\<^sub>W_restart_mset_state D)
    done
qed

lemma cdcl_twl_cp_cdcl\<^sub>W_stgy:
  \<open>cdcl_twl_cp S T \<Longrightarrow> twl_struct_invs S \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (state\<^sub>W_of S) (state\<^sub>W_of T) \<or>
  (state\<^sub>W_of S = state\<^sub>W_of T \<and> (literals_to_update_measure T, literals_to_update_measure S) \<in> lexn less_than 2)\<close>
  by (auto dest!: twl_cp_propagate_or_conflict
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.conflict'
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.propagate'
      simp: twl_struct_invs_def)

lemma cdcl_twl_cp_conflict:
  \<open>cdcl_twl_cp S T \<Longrightarrow> get_conflict T \<noteq> None \<longrightarrow> clauses_to_update T = {#} \<and> literals_to_update T = {#}\<close>
  by (induction rule: cdcl_twl_cp.induct) auto

lemma cdcl_twl_cp_unit_clss_inv:
  \<open>cdcl_twl_cp S T \<Longrightarrow> unit_clss_inv S \<Longrightarrow> unit_clss_inv T\<close>
proof (induction rule: cdcl_twl_cp.induct)
  case (pop M N U NP UP L Q)
  then show ?case by auto
next
  case (propagate D L L' M N U NP UP WS Q) note undef = this(2) and _ = this
  then have unit: \<open>unit_clss_inv (M, N, U, None, NP, UP, add_mset (L, D) WS, Q)\<close>
    by auto
  show ?case
    unfolding unit_clss_inv.simps Ball_def
  proof (intro allI impI conjI)
    fix C
    assume \<open>C \<in># NP + UP\<close>
    then obtain L where
      C: \<open>C ={#L#}\<close> and lev_L: \<open>get_level M L = 0\<close> and L_M: \<open>L \<in> lits_of_l M\<close>
      using unit by auto
    have \<open>atm_of L' \<noteq> atm_of L\<close>
      using undef L_M by (auto simp: defined_lit_map lits_of_def)
    then show \<open>\<exists>L. C = {#L#} \<and> (None = None \<or> 0 < count_decided (Propagated L' (clause D) # M) \<longrightarrow>
      get_level (Propagated L' (clause D) # M) L = 0 \<and> L \<in> lits_of_l (Propagated L' (clause D) # M))\<close>
      using lev_L L_M unfolding C by auto
  qed
next
  case (conflict D L L' M N U NP UP WS Q)
  then show ?case by auto
next
  case (delete_from_working D L L' M N U NP UP WS Q)
  then show ?case by auto
next
  case (update_clause D L L' M K N' U' N U NP UP WS Q)
  then show ?case by auto
qed


lemma cdcl_twl_cp_init_clss:
  \<open>cdcl_twl_cp S T \<Longrightarrow> twl_struct_invs S \<Longrightarrow> init_clss (state\<^sub>W_of T) = init_clss (state\<^sub>W_of S)\<close>
  by (metis cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_no_more_init_clss cdcl_twl_cp_cdcl\<^sub>W_stgy)

lemma cdcl_twl_cp_twl_struct_invs:
  \<open>cdcl_twl_cp S T \<Longrightarrow> twl_struct_invs S \<Longrightarrow> twl_struct_invs T\<close>
  apply (subst twl_struct_invs_def)
  apply (intro conjI)
  subgoal by (rule twl_cp_twl_inv; auto simp add: twl_struct_invs_def twl_cp_twl_inv)
  subgoal by (simp add: twl_cp_valid twl_struct_invs_def)
  subgoal by (metis cdcl_twl_cp_cdcl\<^sub>W_stgy cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv
      twl_struct_invs_def)
  subgoal by (metis cdcl_twl_cp_cdcl\<^sub>W_stgy twl_struct_invs_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_no_smaller_propa)
  subgoal by (rule twl_cp_twl_st_exception_inv; auto simp add: twl_struct_invs_def; fail)
  subgoal by (use twl_struct_invs_def twl_cp_no_duplicate_queued in blast)
  subgoal by (rule twl_cp_distinct_queued; auto simp add: twl_struct_invs_def)
  subgoal by (rule twl_cp_confl_cands_enqueued; auto simp add: twl_struct_invs_def; fail)
  subgoal by (rule twl_cp_propa_cands_enqueued; auto simp add: twl_struct_invs_def; fail)
  subgoal by (simp add: cdcl_twl_cp_conflict; fail)
  subgoal by (simp add: cdcl_twl_cp_unit_clss_inv twl_struct_invs_def; fail)
  subgoal by (simp add: twl_struct_invs_def twl_cp_clauses_to_update; fail)
  subgoal by (simp add: twl_cp_past_invs twl_struct_invs_def; fail)
  done

lemma cdcl_twl_cp_twl_stgy_invs:
  \<open>cdcl_twl_cp S T \<Longrightarrow> twl_struct_invs S \<Longrightarrow> twl_stgy_invs S \<Longrightarrow> twl_stgy_invs T\<close>
  unfolding twl_stgy_invs_def
  by (metis cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_cdcl\<^sub>W_stgy_invariant cdcl_twl_cp_cdcl\<^sub>W_stgy
      twl_struct_invs_def)

subsubsection \<open>The other rules\<close>

lemma
  assumes
    cdcl: "cdcl_twl_o S T" and
    twl: "twl_struct_invs S"
  shows
    cdcl_twl_o_twl_st_inv: \<open>twl_st_inv T\<close> and
    cdcl_twl_o_past_invs: \<open>past_invs T\<close>
  using cdcl twl
proof (induction rule: cdcl_twl_o.induct)
  case (decide M K N U NP UP) note undef = this(1) and atm = this(2)

  case 1 note invs = this(1)
  let ?S = \<open>(M, N, U, None, NP, UP, {#}, {#})\<close>
  have inv: \<open>twl_st_inv ?S\<close> and excep: \<open>twl_st_exception_inv ?S\<close> and past: \<open>past_invs ?S\<close> and
    w_q: \<open>clauses_to_update_inv ?S\<close>
    using invs unfolding twl_struct_invs_def by blast+
  have n_d: \<open>no_dup M\<close>
    using invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (simp add: cdcl\<^sub>W_restart_mset_state)
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

    have watched: \<open>watched_literals_false_of_max_level M C\<close>
      using C inv by (auto simp: twl_st_inv.simps)

    obtain W UW where C_W: \<open>C = TWL_Clause W UW\<close>
      by (cases C)

    have H: False if
      W: \<open>W = {#L, L'#}\<close> and
      uL: \<open>- L \<in> lits_of_l (Decided K # M)\<close> and
      L': \<open>L' \<notin> lits_of_l (Decided K # M)\<close> and
      False: \<open>-L \<noteq> K\<close> for L L'
    proof -
      have \<open>\<forall>K \<in># UW. -K \<in> lits_of_l M\<close>
        using uL L' False excep C unfolding W C_W by (auto simp: twl_exception_inv.simps)
      then have M_CNot_C: \<open>M \<Turnstile>as CNot (remove1_mset L' (clause C))\<close>
        using uL False unfolding true_annots_true_cls_def_iff_negation_in_model
        by (auto simp: C_W W)
      moreover have L'_C: \<open>L' \<in># clause C\<close>
        unfolding C_W W by auto
      ultimately have \<open>defined_lit M L'\<close>
        using propa_cands C by auto
      then have \<open>-L' \<in> lits_of_l M\<close>
        using L' by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)
      then have \<open>M \<Turnstile>as CNot (clause C)\<close>
        using M_CNot_C unfolding true_annots_true_cls_def_iff_negation_in_model
        by (auto simp: C_W W)
      then show False
        using confl_cands C by auto
    qed

    show \<open>watched_literals_false_of_max_level (Decided K # M) C\<close>
      unfolding C_W watched_literals_false_of_max_level.simps
    proof (intro allI impI)
      fix L L'
      assume
        W: \<open>W = {#L, L'#}\<close> and
        uL: \<open>- L \<in> lits_of_l (Decided K # M)\<close> and
        L': \<open>L' \<notin> lits_of_l (Decided K # M)\<close>
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
        fix L L' K' :: \<open>'a literal\<close>
        assume
          W: \<open>W = {#L, L'#}\<close> and
          uL: \<open>- L \<in> lits_of_l (Decided K # M)\<close> and
          L': \<open>L' \<notin> lits_of_l (Decided K # M)\<close> and
          K': \<open>K' \<in># UW\<close>
        then have \<open>-L = K\<close>
          using H[OF W uL L'] by fast
        then show \<open>get_level (Decided K # M) K' \<le> get_level (Decided K # M) L\<close>
          using lev_le_Suc[of K'] by (auto simp: get_level_cons_if)
      qed

      have twl_inv_C: \<open>twl_inv M C\<close>
        using inv C unfolding twl_st_inv.simps by simp
      show \<open>twl_inv (Decided K # M) C\<close>
        unfolding C_W twl_inv.simps
      proof (intro allI impI conjI)
        fix L L'
        assume
          W: \<open>W = {#L, L'#}\<close> and
          uL: \<open>L \<in> lits_of_l (Decided K # M)\<close> and
          L': \<open>-L' \<in> lits_of_l (Decided K # M)\<close>
        moreover have \<open>L \<noteq> -K\<close> \<open>L' \<noteq> -K\<close>
          using exception unfolding C_W W by (auto simp: twl_is_an_exception_def)
        ultimately have uL': \<open>-L' \<in> lits_of_l M\<close>
          by auto
        show \<open>get_level (Decided K # M) L \<le> get_level (Decided K # M) L'\<close>
        proof (cases \<open>L = K\<close>)
          case True
          have L_M: \<open>L \<notin> lits_of_l M\<close> and uL_M: \<open>-L \<notin> lits_of_l M\<close>
            using n_d' Decided_Propagated_in_iff_in_lits_of_l True undef by blast+
          have \<open>\<forall>K \<in># UW. -K \<in> lits_of_l M\<close>
            using uL' L' W True L_M C excep unfolding W C_W twl_inv.simps
            by (force simp: add_mset_eq_add_mset all_conj_distrib twl_exception_inv.simps)
          then have M_CNot_C: \<open>M \<Turnstile>as CNot (remove1_mset L (clause C))\<close>
            using L_M uL' unfolding true_annots_true_cls_def_iff_negation_in_model
            by (auto simp: C_W W)
          moreover have L'_C: \<open>L \<in># clause C\<close>
            unfolding C_W W by auto
          ultimately have \<open>defined_lit M L\<close>
            using propa_cands C by auto
          then have False
            using L_M uL_M by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)
          then show ?thesis by blast
        next
          case False
          then have L: \<open>L \<in> lits_of_l M\<close>
            using uL by auto
          then have \<open>atm_of L \<noteq> atm_of K\<close>
            by (simp add: False \<open>L \<noteq> - K\<close> atm_of_eq_atm_of)
          moreover have \<open>atm_of K \<noteq> atm_of L'\<close>
            using n_d' uL' by (auto simp: defined_lit_map lits_of_def uminus_lit_swap)
          moreover have \<open>get_level M L \<le> get_level M L'\<close>
            using twl_inv_C L uL'  unfolding C_W W by auto
          ultimately show ?thesis
            by auto
        qed
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
        twl_lazy_update M1 C \<and> twl_inv M1 C \<and> watched_literals_false_of_max_level M1 C \<and>
        twl_exception_inv (M1, N, U, None, NP, UP, {#}, {#}) C\<close>
      using past C unfolding past_invs.simps by blast

    have \<open>twl_lazy_update M C\<close>
      using inv C unfolding twl_st_inv.simps by auto
    then show \<open>twl_lazy_update M1 C\<close>
      using IH M by blast
    have \<open>twl_inv M C\<close>
      using inv C unfolding twl_st_inv.simps by auto
    then show \<open>twl_inv M1 C\<close>
      using IH M by blast
    have \<open>watched_literals_false_of_max_level M C\<close>
      using inv C unfolding twl_st_inv.simps by auto
    then show \<open>watched_literals_false_of_max_level M1 C\<close>
      using IH M by blast

    have \<open>twl_exception_inv (M, N, U, None, NP, UP, {#}, {#}) C\<close>
      using excep inv C unfolding twl_st_inv.simps by auto
    then show \<open>twl_exception_inv (M1, N, U, None, NP, UP, {#}, {#}) C\<close>
      using IH M by blast
  next
    fix M1 M2 :: \<open>('a, 'a clause) ann_lits\<close> and K'
    assume \<open>Decided K # M = M2 @ Decided K' # M1\<close>
    then have M: \<open>M = tl M2 @ Decided K' # M1 \<or> M = M1\<close>
      by (cases M2) auto
    then show \<open>confl_cands_enqueued (M1, N, U, None, NP, UP, {#}, {#})\<close> and
      \<open>propa_cands_enqueued (M1, N, U, None, NP, UP, {#}, {#})\<close> and
      \<open>clauses_to_update_inv (M1, N, U, None, NP, UP, {#}, {#})\<close>
      using confl_cands past propa_cands w_q unfolding past_invs.simps by blast+
  qed
next
  case (skip L D C' M N U NP UP)
  case 1
  then show ?case
    by (auto simp: twl_st_inv.simps twl_struct_invs_def)
  case 2
  then show ?case
    by (auto simp: past_invs.simps twl_struct_invs_def)
next
  case (resolve L D C M N U NP UP)
  case 1
  then show ?case
    by (auto simp: twl_st_inv.simps twl_struct_invs_def)
  case 2
  then show ?case
    by (auto simp: past_invs.simps twl_struct_invs_def)
next
  case (backtrack_unit_clause K' D K M1 M2 M D' i N U NP UP) note decomp = this(2) and lev = this(3-5)

  case 1 note invs = this(1)
  let ?S = \<open>(M, N, U, Some D, NP, UP, {#}, {#})\<close>
  let ?T = \<open>(Propagated K' {#K'#} # M1, N, U, None, NP, add_mset {#K'#} UP, {#}, {#- K'#})\<close>
  let ?M1 = \<open>Propagated K' {#K'#} # M1\<close>
  have bt_twl: \<open>cdcl_twl_o ?S ?T\<close>
    using cdcl_twl_o.backtrack_unit_clause[OF backtrack_unit_clause.hyps] .
  then have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o (state\<^sub>W_of ?S)  (state\<^sub>W_of ?T)\<close>
    by (rule cdcl_twl_o_cdcl\<^sub>W_o) (use invs in \<open>simp_all add: twl_struct_invs_def\<close>)
  then have struct_inv_T: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of ?T)\<close>
    using cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_inv cdcl\<^sub>W_restart_mset.other invs twl_struct_invs_def by blast
  have inv: \<open>twl_st_inv ?S\<close> and w_q: \<open>clauses_to_update_inv ?S\<close> and past: \<open>past_invs ?S\<close>
    using invs unfolding twl_struct_invs_def by blast+
  have n_d: \<open>no_dup M\<close>
    using invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (simp add: cdcl\<^sub>W_restart_mset_state)
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

  have propa_cands_M1: \<open>propa_cands_enqueued (M1, N, U, None, NP, add_mset {#K'#} UP, {#}, {#- K'#})\<close>
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
      using undef M' by (fastforce simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def trail.simps clauses_def)
    then show \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># {#- K'#}) \<or> (\<exists>L. (L, C) \<in># {#})\<close>
      by fast
  qed

  have excep_M1: \<open>twl_st_exception_inv (M1, N, U, None, NP, UP, {#}, {#})\<close>
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
        watched_max: \<open>watched_literals_false_of_max_level M1 C\<close> and
        twl_inv_C: \<open>twl_inv M1 C\<close>
        using C past M by (auto simp: past_invs.simps)
      have lev_le_Suc: \<open>get_level M Ka \<le> Suc (count_decided M)\<close> for Ka
        using count_decided_ge_get_level le_Suc_eq by blast
      show \<open>twl_lazy_update ?M1 C\<close>
        apply (rule lazy_update_Propagated)
        using exception apply (simp add: twl_is_an_exception_add_mset_to_queue; fail)
        using watched_max by auto

      show \<open>twl_inv ?M1 C\<close>
        unfolding twl_inv.simps C_W
      proof (intro allI impI conjI)
        fix L L'
        assume
          W: \<open>CW = {#L, L'#}\<close> and
          uL: \<open>L \<in> lits_of_l ?M1\<close> and
          L': \<open>-L' \<in> lits_of_l ?M1\<close>
        moreover have L_L'_K: \<open>L \<noteq> -K'\<close> \<open>L' \<noteq> -K'\<close>
          using exception unfolding C_W W by (auto simp: twl_is_an_exception_def)
        ultimately have uL': \<open>-L' \<in> lits_of_l M1\<close>
          by auto
        show \<open>get_level ?M1 L \<le> get_level ?M1 L'\<close>
        proof (cases \<open>L = K'\<close>)
          case True
          have L_M: \<open>undefined_lit M1 L\<close>
            using n_d' True by (simp add: atm_lit_of_set_lits_of_l
                atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set)+
          have \<open>\<forall>K \<in># CUW. -K \<in> lits_of_l M1\<close>
          proof -
            { fix ll :: "'a literal"
              have "{#L', L#} = CW"
                by (simp add: W)
              moreover have \<open>twl_exception_inv (M1, N, U, None, NP, UP, {#}, {#}) C\<close>
                using C excep_M1 by auto
              ultimately have "ll \<notin># CUW \<or> - ll \<in> lits_of_l M1"
                using L_M twl_inv_C uL' unfolding C_W twl_inv.simps twl_exception_inv.simps
                by (auto simp: add_mset_eq_add_mset Decided_Propagated_in_iff_in_lits_of_l) }
            then show ?thesis
              by blast
          qed
          then have M_CNot_C: \<open>M1 \<Turnstile>as CNot (remove1_mset L (clause C))\<close>
            using L_M uL' unfolding true_annots_true_cls_def_iff_negation_in_model
            by (auto simp: C_W W)
          moreover have L'_C: \<open>L \<in># clause C\<close>
            unfolding C_W W by auto
          moreover have \<open>- K' \<notin># watched C\<close>
            using C_W W L_L'_K by auto
          ultimately have \<open>defined_lit M1 L\<close>
            using propa_cands_M1 C W by auto
          then have False
            using L_M L_M by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)
          then show ?thesis by blast
        next
          case False
          then have L: \<open>L \<in> lits_of_l M1\<close>
            using uL by auto
          then have \<open>atm_of L \<noteq> atm_of K'\<close>
            by (simp add: False \<open>L \<noteq> - K'\<close> atm_of_eq_atm_of)
          moreover have \<open>atm_of K' \<noteq> atm_of L'\<close>
            using n_d' uL' by (auto simp: defined_lit_map lits_of_def uminus_lit_swap)
          moreover have \<open>get_level M1 L \<le> get_level M1 L'\<close>
            using twl_inv_C L uL'  unfolding C_W W by auto
          ultimately show ?thesis
            by auto
        qed
      qed
    }

    have \<open>watched_literals_false_of_max_level M1 C\<close>
      using past C unfolding M' past_invs.simps by blast
    then show \<open>watched_literals_false_of_max_level ?M1 C\<close>
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
    have \<open>twl_lazy_update M1'' C\<close>\<open>twl_inv M1'' C\<close>\<open>watched_literals_false_of_max_level M1'' C\<close>
      using past C unfolding past_invs.simps M M1 twl_exception_inv.simps by auto
    moreover {
      have \<open>twl_exception_inv (M1'', N, U, None, NP, UP, {#}, {#}) C\<close>
        using past C unfolding past_invs.simps M M1 by auto
      then have \<open>twl_exception_inv (M1'', N, U, None, NP, add_mset {#K'#} UP, {#}, {#}) C\<close>
      using C unfolding twl_exception_inv.simps by auto }
    ultimately show \<open>twl_lazy_update M1'' C\<close>\<open>twl_inv M1'' C\<close>\<open>watched_literals_false_of_max_level M1'' C\<close>
      \<open>twl_exception_inv (M1'', N, U, None, NP, add_mset {#K'#} UP, {#}, {#}) C\<close>
      by fast+
  next
    fix M1'' M2'' K''
    assume \<open>?M1 = M2'' @ Decided K'' # M1''\<close>
    then have M1: \<open>M1 = tl M2'' @ Decided K'' # M1''\<close>
      by (cases M2'') auto
    then show
      \<open>confl_cands_enqueued (M1'', N, U, None, NP, add_mset {#K'#} UP, {#}, {#})\<close> and
      \<open>propa_cands_enqueued (M1'', N, U, None, NP, add_mset {#K'#} UP, {#}, {#})\<close> and
      \<open>clauses_to_update_inv (M1'', N, U, None, NP, add_mset {#K'#} UP, {#}, {#})\<close>
      using past by (auto simp add: past_invs.simps M)
  qed
next
  case (backtrack_nonunit_clause K' D K M1 M2 M D' i N U NP UP K'') note K'_D = this(1) and
    decomp = this(2) and lev_K' = this(3) and i = this(5) and lev_K = this(6) and K'_D' = this(10)
    and K'' = this(11) and lev_K'' = this(12)
  case 1 note invs = this(1)
  let ?S = \<open>(M, N, U, Some D, NP, UP, {#}, {#})\<close>
  let ?M1 = \<open>Propagated K' D' # M1\<close>
  let ?T = \<open>(?M1, N, add_mset (TWL_Clause {#K', K''#} (D' - {#K', K''#})) U, None, NP, UP, {#}, {#- K'#})\<close>
  let ?D = \<open>TWL_Clause {#K', K''#} (D' - {#K', K''#})\<close>
  have bt_twl: \<open>cdcl_twl_o ?S ?T\<close>
    using cdcl_twl_o.backtrack_nonunit_clause[OF backtrack_nonunit_clause.hyps] .
  then have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o (state\<^sub>W_of ?S)  (state\<^sub>W_of ?T)\<close>
    by (rule cdcl_twl_o_cdcl\<^sub>W_o) (use invs in \<open>simp_all add: twl_struct_invs_def\<close>)
  then have struct_inv_T: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of ?T)\<close>
    using cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_inv cdcl\<^sub>W_restart_mset.other invs twl_struct_invs_def by blast
  have inv: \<open>twl_st_inv ?S\<close> and
    w_q: \<open>clauses_to_update_inv ?S\<close> and
    past: \<open>past_invs ?S\<close>
    using invs unfolding twl_struct_invs_def by blast+
  have n_d: \<open>no_dup M\<close>
    using invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (simp add: cdcl\<^sub>W_restart_mset_state)
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
    using invs unfolding twl_struct_invs_def by blast
  then have \<open>distinct_mset D\<close>
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
    by (auto simp: conflicting.simps)

  have "undefined_lit (M3 @ M2) K"
    using n_d unfolding M by auto
  then have count_M1: \<open>count_decided M1 = i\<close>
    using lev_K unfolding M by (auto simp: image_Un)
  then have K''_ne_K: \<open>K' \<noteq> K''\<close>
    using lev_K lev_K' lev_K'' count_decided_ge_get_level[of M K''] unfolding M by auto
  then have D:
    \<open>add_mset K' (add_mset K'' (D' - {#K', K''#})) = D'\<close>
    \<open>add_mset K'' (add_mset K' (D' - {#K', K''#})) = D'\<close>
    using K'' K'_D' multi_member_split by fastforce+
  have propa_cands_M1: \<open>propa_cands_enqueued (M1, N, U, None, NP, UP, {#}, {#- K''#})\<close>
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
      using undef M' by (fastforce simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def trail.simps clauses_def)
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

  have excep_M1: \<open>twl_st_exception_inv (M1, N, U, None, NP, UP, {#}, {#})\<close>
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
      watched_max: \<open>watched_literals_false_of_max_level M1 C\<close> and
      twl_inv_C: \<open>twl_inv M1 C\<close> if \<open>C \<noteq> ?D\<close>
      using C past M' that by (auto simp: past_invs.simps)
    from M1_CNot_D have in_D_M1: \<open>L \<in># remove1_mset K' D' \<Longrightarrow> - L \<in> lits_of_l M1\<close> for L
      by (auto simp: true_annots_true_cls_def_iff_negation_in_model)
    then have in_K_D_M1: \<open>L \<in># D' - {#K', K''#} \<Longrightarrow> - L \<in> lits_of_l M1\<close> for L
      by (metis K'_D' add_mset_diff_bothsides add_mset_remove_trivial in_diffD mset_add)
    have
      lazy_D: \<open>twl_lazy_update ?M1 C\<close> and
      watched_max_D: \<open>watched_literals_false_of_max_level ?M1 C\<close> and
      twl_inv_D: \<open>twl_inv ?M1 C\<close> if \<open>C = ?D\<close>
      using that apply (auto simp: add_mset_eq_add_mset count_decided_ge_get_level get_level_cons_if; fail)[]
      using that apply (auto simp: add_mset_eq_add_mset count_decided_ge_get_level get_level_cons_if; fail)[]
      unfolding that twl_inv.simps
      apply (intro allI conjI impI)
      using that in_D_M1 by (auto simp add: add_mset_eq_add_mset lev_M1_K'' get_level_cons_if dest: in_K_D_M1)

    {
      assume excep: \<open>\<not> twl_is_an_exception C {#-K'#} {#}\<close>

      have lev_le_Suc: \<open>get_level M Ka \<le> Suc (count_decided M)\<close> for Ka
        using count_decided_ge_get_level le_Suc_eq by blast
      have \<open>twl_lazy_update ?M1 C\<close> if \<open>C \<noteq> ?D\<close>
        apply (rule lazy_update_Propagated)
        using excep apply (simp add: twl_is_an_exception_add_mset_to_queue; fail)
        using watched_max that by auto
      then show \<open>twl_lazy_update ?M1 C\<close>
        using lazy_D by blast
      have \<open>twl_inv ?M1 C\<close> if \<open>C \<noteq> ?D\<close>
        unfolding twl_inv.simps C_W
      proof (intro allI impI conjI)
        fix L L'
        assume
          W: \<open>CW = {#L, L'#}\<close> and
          uL: \<open>L \<in> lits_of_l ?M1\<close> and
          L': \<open>-L' \<in> lits_of_l ?M1\<close>
        moreover have L_L'_K: \<open>L \<noteq> -K'\<close> \<open>L' \<noteq> -K'\<close>
          using excep unfolding C_W W by (auto simp: twl_is_an_exception_def)
        ultimately have uL': \<open>-L' \<in> lits_of_l M1\<close>
          by auto
        show \<open>get_level ?M1 L \<le> get_level ?M1 L'\<close>
        proof (cases \<open>L = K'\<close>)
          case True
          have L_M: \<open>undefined_lit M1 L\<close>
            using n_d' True by simp
          have \<open>\<forall>K \<in># CUW. -K \<in> lits_of_l M1\<close>
          proof -
            { fix ll :: "'a literal"
              have "{#L', L#} = CW"
                by (simp add: W)
              moreover have \<open>twl_exception_inv (M1, N, U, None, NP, UP, {#}, {#}) C\<close>
                using that C excep_M1 by auto
              ultimately have "ll \<notin># CUW \<or> - ll \<in> lits_of_l M1"
                using L_M twl_inv_C uL' unfolding C_W twl_inv.simps twl_exception_inv.simps
                by (auto simp: add_mset_eq_add_mset Decided_Propagated_in_iff_in_lits_of_l) }
            then show ?thesis
              by blast
          qed
          then have M_CNot_C: \<open>M1 \<Turnstile>as CNot (remove1_mset L (clause C))\<close>
            using L_M uL' unfolding true_annots_true_cls_def_iff_negation_in_model
            by (auto simp: C_W W)
          moreover have L'_C: \<open>L \<in># clause C\<close>
            unfolding C_W W by auto
          moreover have \<open>- K'' \<notin># watched C\<close>
            using C_W W L_L'_K L_M \<open>- K'' \<in> lits_of_l M1\<close> n_d' uL'
            by (fastforce dest: distinct_consistent_interp mk_disjoint_insert
                simp: Decided_Propagated_in_iff_in_lits_of_l)
          ultimately have \<open>defined_lit M1 L\<close>
            using propa_cands_M1 C W that by auto
          then have False
            using L_M by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)
          then show ?thesis by blast
        next
          case False
          then have L: \<open>L \<in> lits_of_l M1\<close>
            using uL by auto
          then have \<open>atm_of L \<noteq> atm_of K'\<close>
            by (simp add: False \<open>L \<noteq> - K'\<close> atm_of_eq_atm_of)
          moreover have \<open>atm_of K' \<noteq> atm_of L'\<close>
            using n_d' uL' by (auto simp: defined_lit_map lits_of_def uminus_lit_swap)
          moreover have \<open>get_level M1 L \<le> get_level M1 L'\<close>
            using twl_inv_C L uL' that unfolding C_W W by auto
          ultimately show ?thesis
            by auto
        qed
      qed
      then show \<open>twl_inv ?M1 C\<close>
        using twl_inv_D by blast
    }

    have \<open>watched_literals_false_of_max_level M1 C\<close> if \<open>C \<noteq> ?D\<close>
      using past C that unfolding M past_invs.simps by auto
    then have \<open>watched_literals_false_of_max_level ?M1 C\<close> if \<open>C \<noteq> ?D\<close>
      using C_W that by (auto simp: get_level_cons_if)
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
    have \<open>twl_lazy_update M1'' C\<close>\<open>twl_inv M1'' C\<close>\<open>watched_literals_false_of_max_level M1'' C\<close>
      if \<open>C \<noteq> ?D\<close>
      using past C that unfolding past_invs.simps M M1 twl_exception_inv.simps by auto
    moreover {
      have \<open>twl_exception_inv (M1'', N, U, None, NP, UP, {#}, {#}) C\<close> if \<open>C \<noteq> ?D\<close>
        using past C unfolding past_invs.simps M M1 by (auto simp: that)
      then have \<open>twl_exception_inv (M1'', N, add_mset ?D U, None, NP, UP, {#}, {#}) C\<close>
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
                dest: cdcl\<^sub>W_restart_mset.no_dup_uminus_append_in_atm_notin)
          then show False
            using lev_M1_K''  count_decided_ge_get_level[of M1'' K''] unfolding M1
            by (auto simp: image_Un Int_Un_distrib)
        qed }
      ultimately have \<open>twl_lazy_update M1'' ?D\<close> and \<open>twl_inv M1'' ?D\<close> and
         \<open>watched_literals_false_of_max_level M1'' ?D\<close> and
        \<open>twl_exception_inv (M1'', N, add_mset (TWL_Clause {#K', K''#} (D' - {#K', K''#})) U, None, NP, UP, {#}, {#}) ?D\<close>
        by (auto simp: add_mset_eq_add_mset twl_exception_inv.simps get_level_cons_if
            Decided_Propagated_in_iff_in_lits_of_l) }
    ultimately show \<open>twl_lazy_update M1'' C\<close>\<open>twl_inv M1'' C\<close>\<open>watched_literals_false_of_max_level M1'' C\<close>
      \<open>twl_exception_inv (M1'', N, add_mset (TWL_Clause {#K', K''#} (D' - {#K', K''#})) U, None, NP, UP, {#}, {#}) C\<close>
      by blast+
  next
    fix M1'' M2'' K'''
    assume M1: \<open>?M1 = M2'' @ Decided K''' # M1''\<close>
    then have M1: \<open>M1 = tl M2'' @ Decided K''' # M1''\<close>
      by (cases M2'') auto
    then have confl_cands: \<open>confl_cands_enqueued (M1'', N, U, None, NP, UP, {#}, {#})\<close> and
      propa_cands: \<open>propa_cands_enqueued (M1'', N, U, None, NP, UP, {#}, {#})\<close> and
      w_q: \<open>clauses_to_update_inv (M1'', N, U, None, NP, UP, {#}, {#})\<close>
      using past by (auto simp add: M M1 past_invs.simps simp del: propa_cands_enqueued.simps
          confl_cands_enqueued.simps)
    have uK''_M1'': \<open>- K'' \<notin> lits_of_l M1''\<close>
    proof (rule ccontr)
      assume K''_M1'': \<open>\<not> ?thesis\<close>
      have \<open>undefined_lit (tl M2'' @ Decided K''' # []) (-K'')\<close>
        apply (rule CDCL_W_Abstract_State.cdcl\<^sub>W_restart_mset.no_dup_append_in_atm_notin)
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
        apply (rule CDCL_W_Abstract_State.cdcl\<^sub>W_restart_mset.no_dup_append_in_atm_notin)
         prefer 2 using K'_M1'' apply (simp; fail)
        by (use n_d in \<open>auto simp: M M1; fail\<close>)[]
      then show False
        using lev_K' count_decided_ge_get_level[of M1'' K'] unfolding M M1
        by (auto simp: image_Un)
    qed

    have [simp]: \<open>\<not>clauses_to_update_prop {#} M1'' (L, ?D)\<close> for L
      using uK'_M1'' uK''_M1'' by (auto simp: clauses_to_update_prop.simps add_mset_eq_add_mset)
    show \<open>confl_cands_enqueued (M1'', N, add_mset ?D U, None, NP, UP, {#}, {#})\<close> and
      \<open>propa_cands_enqueued (M1'', N, add_mset ?D U, None, NP, UP, {#}, {#})\<close> and
      \<open>clauses_to_update_inv (M1'', N, add_mset ?D U, None, NP, UP, {#}, {#})\<close>
      using confl_cands propa_cands w_q uK'_M1'' uK''_M1''
      by (fastforce simp add: twl_st_inv.simps add_mset_eq_add_mset)+
  qed
qed

lemma
  assumes
    cdcl: "cdcl_twl_o S T"
  shows
    cdcl_twl_o_valid: \<open>valid_annotation T\<close> and
    cdcl_twl_o_conflict_None_queue:
      \<open>get_conflict T \<noteq> None \<Longrightarrow> clauses_to_update T = {#} \<and> literals_to_update T = {#}\<close> and
      cdcl_twl_o_no_duplicate_queued: \<open>no_duplicate_queued T\<close> and
      cdcl_twl_o_distinct_queued: \<open>distinct_queued T\<close>
  using cdcl by (induction rule: cdcl_twl_o.induct) auto

lemma cdcl_twl_o_twl_st_exception_inv:
  assumes
    cdcl: "cdcl_twl_o S T" and
    twl: "twl_struct_invs S"
  shows
    \<open>twl_st_exception_inv T\<close>
  using cdcl twl
proof (induction rule: cdcl_twl_o.induct)
  case (decide M L N U NP UP)
  then show ?case
    unfolding twl_struct_invs_def by (auto simp: twl_exception_inv.simps)
next
  case (skip L D C' M N U NP UP)
  then show ?case
    unfolding twl_struct_invs_def by (auto simp: twl_exception_inv.simps)
next
  case (resolve L D C M N U NP UP)
  then show ?case
    unfolding twl_struct_invs_def by (auto simp: twl_exception_inv.simps)
next
  case (backtrack_unit_clause L D K M1 M2 M D' i N U NP UP) note decomp = this(2) and
    invs = this(10)
  let ?S = \<open>(M, N, U, Some D, NP, UP, {#}, {#})\<close>
  let ?S' = \<open>state\<^sub>W_of S\<close>
  let ?T = \<open>(M1, N, U, None, NP, UP, {#}, {#})\<close>
  let ?T' = \<open>state\<^sub>W_of T\<close>
  let ?U = \<open>(Propagated L {#L#} # M1, N, U, None, NP, add_mset {#L#} UP, {#}, {#- L#})\<close>
  let ?U' = \<open>state\<^sub>W_of ?U\<close>
  have \<open>twl_st_inv ?S\<close> and \<open>past_invs ?S\<close>
    using invs decomp unfolding twl_struct_invs_def by fast+
  then have \<open>twl_exception_inv ?T C\<close> if \<open>C \<in># N + U\<close> for C
    using decomp that unfolding past_invs.simps by auto
  then show ?case
    by (auto simp: twl_exception_inv.simps)
next
  case (backtrack_nonunit_clause L D K M1 M2 M D' i N U NP UP L') note decomp = this(2) and
    invs = this(13)
  let ?S = \<open>(M, N, U, Some D, NP, UP, {#}, {#})\<close>
  let ?D = \<open>TWL_Clause {#L, L'#} (D' - {#L, L'#})\<close>
  let ?T = \<open>(M1, N, U, None, NP, UP, {#}, {#})\<close>
  let ?U = \<open>(Propagated L D' # M1, N, add_mset ?D U, None, NP, UP, {#}, {#- L#})\<close>
  have \<open>twl_st_inv ?S\<close> and \<open>past_invs ?S\<close>
    using invs decomp unfolding twl_struct_invs_def by fast+
  then have \<open>twl_exception_inv ?T C\<close> if \<open>C \<in># N + U\<close> for C
    using decomp that unfolding past_invs.simps by auto
  then have \<open>twl_exception_inv ?U C\<close> if \<open>C \<in># N + U\<close> for C
    using decomp that unfolding twl_st_inv.simps by (auto simp: twl_exception_inv.simps)
  moreover {
    have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o (state\<^sub>W_of ?S) (state\<^sub>W_of ?U)\<close>
      by (rule cdcl_twl_o_cdcl\<^sub>W_o)
        (use cdcl_twl_o.backtrack_nonunit_clause[OF backtrack_nonunit_clause.hyps] invs in \<open>simp_all add: twl_struct_invs_def\<close>)
    then have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of ?U)\<close>
      using cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_inv cdcl\<^sub>W_restart_mset.other invs twl_struct_invs_def
      by blast
    then have \<open>no_dup (Propagated L D' # M1)\<close>
      unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by (simp add: trail.simps)
    then have \<open>- L \<notin> lits_of_l M1\<close>
      by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)
    then have \<open>twl_exception_inv ?U ?D\<close>
      by (auto simp: twl_exception_inv.simps add_mset_eq_add_mset) }
  ultimately show ?case
    by auto
qed

(* TODO refactor: the two backtrack ?cases are copy-paste from each other.*)
lemma
  assumes
    cdcl: "cdcl_twl_o S T" and
    twl: "twl_struct_invs S"
  shows
    cdcl_twl_o_confl_cands_enqueued: \<open>confl_cands_enqueued T\<close> and
    cdcl_twl_o_propa_cands_enqueued: \<open>propa_cands_enqueued T\<close> and
    twl_o_clauses_to_update: \<open>clauses_to_update_inv T\<close>
  using cdcl twl
proof (induction rule: cdcl_twl_o.induct)
  case (decide M L N U NP UP)
  let ?S = \<open>(M, N, U, None, NP, UP, {#}, {#})\<close>
  let ?T = \<open>(Decided L # M, N, U, None, NP, UP, {#}, {#-L#})\<close>
  case 1
  then have confl_cand: \<open>confl_cands_enqueued ?S\<close> and
    twl_st_inv: \<open>twl_st_inv ?S\<close> and
    excep: \<open>twl_st_exception_inv ?S\<close> and
    propa_cands: \<open>propa_cands_enqueued ?S\<close> and
    confl_cands: \<open>confl_cands_enqueued ?S\<close> and
    w_q: \<open>clauses_to_update_inv ?S\<close>
    unfolding twl_struct_invs_def by fast+

  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o (state\<^sub>W_of ?S) (state\<^sub>W_of ?T)\<close>
    by (rule cdcl_twl_o_cdcl\<^sub>W_o) (use cdcl_twl_o.decide[OF decide.hyps] 1 in \<open>simp_all add: twl_struct_invs_def\<close>)
  then have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of ?T)\<close>
    using 1 cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_inv cdcl\<^sub>W_restart_mset.other twl_struct_invs_def by blast
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
      ultimately have \<open>(-K \<in> lits_of_l M \<and> K' \<notin> lits_of_l M) \<or> (-K' \<in> lits_of_l M \<and> K \<notin> lits_of_l M)\<close>
        using neg_C by (auto simp: C_W W)
      moreover have \<open>twl_exception_inv (M, N, U, None, NP, UP, {#}, {#}) C\<close>
        using excep C by auto
      ultimately have \<open>\<forall>K \<in># unwatched C. -K \<in> lits_of_l M\<close>
        by (auto simp: twl_exception_inv.simps C_W W add_mset_eq_add_mset all_conj_distrib)
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
    then have \<open>-L \<in># clause C\<close> and neg_C: \<open>\<forall>K \<in># remove1_mset FK (clause C). -K \<in> lits_of_l (Decided L # M)\<close>
      using LM_C undef_M_K by (force simp: true_annots_true_cls_def_iff_negation_in_model dest: in_diffD)+

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
      moreover have \<open>twl_exception_inv (M, N, U, None, NP, UP, {#}, {#}) C\<close>
        using excep C by auto
      ultimately have \<open>\<forall>K \<in># unwatched C. -K \<in> lits_of_l M\<close>
        using uK_M
        by (auto simp: twl_exception_inv.simps C_W W add_mset_eq_add_mset all_conj_distrib)
      then show False
        using C_W L_M(1) \<open>- L \<in># clause C\<close> uL_W by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)
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
      using w_q unfolding clauses_to_update_prop.simps by (auto simp add: filter_mset_empty_conv)
  next
    case (Q K K' C)
    then show ?case
      using w_q by auto
  qed
next
  case (skip L D C' M N U NP UP)
  case 1 then show ?case by auto
  case 2 then show ?case by auto
  case 3 then show ?case by auto
next
  case (resolve L D C M N U NP UP)
  case 1 then show ?case by auto
  case 2 then show ?case by auto
  case 3 then show ?case by auto
next
  case (backtrack_unit_clause L D K M1 M2 M D' i N U NP UP) note decomp = this(2)
  let ?S = \<open>(M, N, U, Some D, NP, UP, {#}, {#})\<close>
  let ?U = \<open>(Propagated L {#L#} # M1, N, U, None, NP, add_mset {#L#} UP, {#}, {#- L#})\<close>
  obtain M3 where
    M: \<open>M = M3 @ M2 @ Decided K # M1\<close>
    using decomp by blast

  case 1
  then have twl_st_inv: \<open>twl_st_inv ?S\<close> and
    struct_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of ?S)\<close> and
    excep: \<open>twl_st_exception_inv ?S\<close> and
    past: \<open>past_invs ?S\<close>
    using decomp unfolding twl_struct_invs_def by fast+
  then have
    confl_cands: \<open>confl_cands_enqueued (M1, N, U, None, NP, UP, {#}, {#})\<close> and
    propa_cands: \<open>propa_cands_enqueued (M1, N, U, None, NP, UP, {#}, {#})\<close>and
    w_q: \<open>clauses_to_update_inv (M1, N, U, None, NP, UP, {#}, {#})\<close>
    using decomp unfolding past_invs.simps by (auto simp del: clauses_to_update_inv.simps)

  have n_d: \<open>no_dup M\<close>
    using struct_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
     cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: trail.simps)
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o (state\<^sub>W_of ?S) (state\<^sub>W_of ?U)\<close>
    using cdcl_twl_o.backtrack_unit_clause[OF backtrack_unit_clause.hyps]
    by (meson "1.prems" twl_struct_invs_def cdcl_twl_o_cdcl\<^sub>W_o)
  then have struct_inv_T: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of ?U)\<close>
    using struct_inv cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_inv cdcl\<^sub>W_restart_mset.other by blast
  then have n_d_L_M1: \<open>no_dup (Propagated L {#L#} # M1)\<close>
    using struct_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
     cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: trail.simps)
  then have uL_M1: \<open>undefined_lit M1 L\<close>
    by (simp_all add: atm_lit_of_set_lits_of_l atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set)


  have excep_M1: \<open>\<forall>C \<in># N + U. twl_exception_inv (M1, N, U, None, NP, UP, {#}, {#}) C\<close>
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
        have f2: "consistent_interp (lits_of_l M1)"
          using distinct_consistent_interp n_d_L_M1 by auto
        have undef_L: "undefined_lit M1 L"
          using atm_lit_of_set_lits_of_l n_d_L_M1 by force
        then show "K \<notin> lits_of_l M1"
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
      ultimately have \<open>(-K \<in> lits_of_l M1 \<and> K' \<notin> lits_of_l M1) \<or> (-K' \<in> lits_of_l M1 \<and> K \<notin> lits_of_l M1)\<close>
        using neg_C by (auto simp: C_W W)
      moreover have \<open>twl_exception_inv (M1, N, U, None, NP, UP, {#}, {#}) C\<close>
        using excep_M1 C by auto
      ultimately have \<open>\<forall>K \<in># unwatched C. -K \<in> lits_of_l M1\<close>
        by (auto simp: twl_exception_inv.simps C_W W add_mset_eq_add_mset all_conj_distrib L_M)
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
    then have \<open>-L \<in># clause C\<close> and neg_C: \<open>\<forall>K \<in># remove1_mset FK (clause C). -K \<in> lits_of_l (Propagated L D # M1)\<close>
      using LM_C undef_M_K by (force simp: true_annots_true_cls_def_iff_negation_in_model dest: in_diffD)+

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
      moreover have \<open>twl_exception_inv (M1, N, U, None, NP, UP, {#}, {#}) C\<close>
        using excep_M1 C by auto
      ultimately have \<open>\<forall>K \<in># unwatched C. -K \<in> lits_of_l M1\<close>
        using uK_M
        by (auto simp: twl_exception_inv.simps C_W W add_mset_eq_add_mset all_conj_distrib)
      then show False
        using C_W uL_M1 \<open>- L \<in># clause C\<close> uL_W by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)
    qed
    then show \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># {#- L#}) \<or> (\<exists>L. (L, C) \<in># {#})\<close>
      by auto
  qed

  case 3
  have
    2: \<open>\<And>L. Pair L `# {#C \<in># N + U. clauses_to_update_prop {#} M1 (L, C)#} = {#}\<close> and
    3: \<open>\<And>L L' C. C \<in># N + U \<Longrightarrow> watched C = {#L, L'#} \<Longrightarrow> - L \<in> lits_of_l M1 \<Longrightarrow>
      L' \<notin> lits_of_l M1 \<Longrightarrow> (L, C) \<notin># {#} \<Longrightarrow> L \<in># {#}\<close>
    using w_q unfolding clauses_to_update_inv.simps by auto


  show ?case
  proof (induction rule: clauses_to_update_inv_cases)
    case (WS_nempty L C)
    then show ?case by simp
  next
    case (WS_empty K)
    then show ?case
      using 2[of K] apply (simp only: filter_mset_empty_conv Ball_def image_mset_is_empty_iff)
      apply (auto simp add: clauses_to_update_prop.simps)
      done
  next
    case (Q K K' C)
    then show ?case
      using 3[of C K K'] by (auto simp add: clauses_to_update_prop.simps)
  qed
next
  case (backtrack_nonunit_clause L D K M1 M2 M D' i N U NP UP L') note LD = this(1) and
    decomp = this(2) and lev_L = this(3) and lev_max_L = this(4) and i = this(5) and lev_K = this(6)
    and LD' = this(11) and lev_L' = this(12)
  let ?S = \<open>(M, N, U, Some D, NP, UP, {#}, {#})\<close>
  let ?D = \<open>TWL_Clause {#L, L'#} (D' - {#L, L'#})\<close>
  let ?U = \<open>(Propagated L D' # M1, N, add_mset ?D U, None, NP,
    UP, {#}, {#- L#})\<close>
  obtain M3 where
    M: \<open>M = M3 @ M2 @ Decided K # M1\<close>
    using decomp by blast

  case 1
  then have twl_st_inv: \<open>twl_st_inv ?S\<close> and
    struct_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of ?S)\<close> and
    excep: \<open>twl_st_exception_inv ?S\<close> and
    past: \<open>past_invs ?S\<close>
    using decomp unfolding twl_struct_invs_def by fast+
  then have
    confl_cands: \<open>confl_cands_enqueued (M1, N, U, None, NP, UP, {#}, {#})\<close> and
    propa_cands: \<open>propa_cands_enqueued (M1, N, U, None, NP, UP, {#}, {#})\<close> and
    w_q: \<open>clauses_to_update_inv (M1, N, U, None, NP, UP, {#}, {#})\<close>
    using decomp unfolding past_invs.simps by auto

  have n_d: \<open>no_dup M\<close>
    using struct_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
     cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: trail.simps)

  have \<open>undefined_lit (M3 @ M2 @ M1) K\<close>
    by (rule cdcl\<^sub>W_restart_mset.no_dup_append_in_atm_notin[of _ \<open>[Decided K]\<close>])
      (use n_d M in \<open>auto simp: no_dup_def\<close>)
  then have L_uL': \<open>L \<noteq> - L'\<close>
    using lev_L lev_L' lev_K unfolding M by (auto simp: image_Un)

  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o (state\<^sub>W_of ?S) (state\<^sub>W_of ?U)\<close>
    using cdcl_twl_o.backtrack_nonunit_clause[OF backtrack_nonunit_clause.hyps]
    by (meson "1.prems" twl_struct_invs_def cdcl_twl_o_cdcl\<^sub>W_o)
  then have struct_inv_T: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of ?U)\<close>
    using struct_inv cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_inv cdcl\<^sub>W_restart_mset.other by blast
  then have n_d_L_M1: \<open>no_dup (Propagated L D' # M1)\<close>
    using struct_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
     cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: trail.simps)
  then have uL_M1: \<open>undefined_lit M1 L\<close>
    by simp

  have M1_CNot_L_D: \<open>M1 \<Turnstile>as CNot (remove1_mset L D')\<close>
    using struct_inv_T unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
     cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def by (auto simp: trail.simps)

  have excep_M1: \<open>\<forall>C \<in># N + U. twl_exception_inv (M1, N, U, None, NP, UP, {#}, {#}) C\<close>
    using past unfolding past_invs.simps M by auto
  show ?case
    unfolding confl_cands_enqueued.simps Ball_def
  proof (intro allI impI)
    fix C
    assume
      C: \<open>C \<in># N + add_mset ?D U\<close> and
      LM_C: \<open>Propagated L D' # M1 \<Turnstile>as CNot (clause C)\<close>
    have \<open>twl_st_inv ?U\<close>
      using cdcl_twl_o.backtrack_nonunit_clause[OF backtrack_nonunit_clause.hyps] "1.prems" cdcl_twl_o_twl_st_inv by blast
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
          have f2: "consistent_interp (lits_of_l M1)"
            using distinct_consistent_interp n_d_L_M1 by auto
          have undef_L: "undefined_lit M1 L"
            using atm_lit_of_set_lits_of_l n_d_L_M1 by force
          then show "K \<notin> lits_of_l M1"
            using f2 neg_C unfolding C_W W by (metis (no_types) C_W W add_diff_cancel_right'
                atm_of_eq_atm_of clause.simps consistent_interp_def in_diffD insertE list.simps(15)
                lits_of_insert uL_C union_single_eq_member Decided_Propagated_in_iff_in_lits_of_l)
          show \<open>K' \<notin> lits_of_l M1\<close>
            using consistent_interp_def distinct_consistent_interp n_d_L_M1
            using neg_C uL_W n_d unfolding C_W W by auto
          show \<open>L \<notin> lits_of_l M1\<close>
            using undef_L by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)
        qed
        ultimately have \<open>(-K \<in> lits_of_l M1 \<and> K' \<notin> lits_of_l M1) \<or> (-K' \<in> lits_of_l M1 \<and> K \<notin> lits_of_l M1)\<close>
          using neg_C by (auto simp: C_W W)
        moreover have \<open>twl_exception_inv (M1, N, U, None, NP, UP, {#}, {#}) C\<close>
          using excep_M1 C by auto
        ultimately have \<open>\<forall>K \<in># unwatched C. -K \<in> lits_of_l M1\<close>
          by (auto simp: twl_exception_inv.simps C_W W add_mset_eq_add_mset all_conj_distrib L_M)
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
      then have \<open>-L \<in># clause C\<close> and neg_C: \<open>\<forall>K \<in># remove1_mset FK (clause C). -K \<in> lits_of_l (Propagated L D # M1)\<close>
        using LM_C undef_M_K by (force simp: true_annots_true_cls_def_iff_negation_in_model dest: in_diffD)+

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
        moreover have \<open>twl_exception_inv (M1, N, U, None, NP, UP, {#}, {#}) C\<close>
          using excep_M1 C by auto
        ultimately have \<open>\<forall>K \<in># unwatched C. -K \<in> lits_of_l M1\<close>
          using uK_M
          by (auto simp: twl_exception_inv.simps C_W W add_mset_eq_add_mset all_conj_distrib)
        then show False
          using C_W uL_M1 \<open>- L \<in># clause C\<close> uL_W by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)
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
    3: \<open>\<And>L L' C. C \<in># N + U \<Longrightarrow> watched C = {#L, L'#} \<Longrightarrow> - L \<in> lits_of_l M1 \<Longrightarrow>
      L' \<notin> lits_of_l M1 \<Longrightarrow> (L, C) \<notin># {#} \<Longrightarrow> L \<in># {#}\<close>
    using w_q unfolding clauses_to_update_inv.simps by auto

  show ?case
  proof (induction rule: clauses_to_update_inv_cases)
    case (WS_nempty L C)
    then show ?case by simp
  next
    case (WS_empty K')
    then show ?case
      using 2[of K'] uL_M1 by (simp only: filter_mset_empty_conv Ball_def image_mset_is_empty_iff)
       (auto simp add: clauses_to_update_prop.simps add_mset_eq_add_mset Decided_Propagated_in_iff_in_lits_of_l)
  next
    case (Q K' K'' C)
    then show ?case
      using 3[of C K' K''] uL_M1 by (auto simp add: clauses_to_update_prop.simps add_mset_eq_add_mset
          Decided_Propagated_in_iff_in_lits_of_l)
  qed
qed

lemma no_dup_append_decided_Cons_lev:
  assumes \<open>no_dup (M2 @ Decided K # M1)\<close>
  shows \<open>count_decided M1 = get_level (M2 @ Decided K # M1) K - 1\<close>
proof -
  have \<open>undefined_lit (M2 @ M1) K\<close>
    by (rule CDCL_W_Abstract_State.cdcl\<^sub>W_restart_mset.no_dup_append_in_atm_notin[of _ \<open>[Decided K]\<close>])
      (use assms in auto)
  then show ?thesis
    by (auto)
qed

lemma cdcl_twl_o_unit_clss_inv:
  assumes
    cdcl: \<open>cdcl_twl_o S T\<close> and
    unit: \<open>twl_struct_invs S\<close>
  shows \<open>unit_clss_inv T\<close>
  using cdcl unit
proof (induction rule: cdcl_twl_o.induct)
  case (decide M L N U NP UP) note undef = this(1) and twl = this(3)
  then have unit: \<open>unit_clss_inv (M, N, U, None, NP, UP, {#}, {#})\<close>
    unfolding twl_struct_invs_def by fast
  show ?case
    unfolding unit_clss_inv.simps Ball_def
  proof (intro allI impI)
    fix C
    assume \<open>C \<in># NP + UP\<close>
    then obtain K where \<open>C = {#K#}\<close> and K: \<open>K \<in> lits_of_l M\<close> and \<open>get_level M K = 0\<close>
      using unit by auto
    moreover have \<open>atm_of L \<noteq> atm_of K\<close>
      using undef K by (auto simp: defined_lit_map lits_of_def)
    ultimately show \<open>\<exists>La. C = {#La#} \<and> (None = None \<or> 0 < count_decided (Decided L # M) \<longrightarrow>
      get_level (Decided L # M) La = 0 \<and> La \<in> lits_of_l (Decided L # M))\<close>
      by auto
  qed
next
  case (skip L D C' M N U NP UP) note twl = this(3)
  let ?M = \<open>Propagated L C' # M\<close>
  have unit: \<open>unit_clss_inv (?M, N, U, Some D, NP, UP, {#}, {#})\<close>
    using twl unfolding twl_struct_invs_def by fast
  show ?case
    unfolding unit_clss_inv.simps Ball_def
  proof (intro allI impI, cases \<open>count_decided M = 0\<close>)
    case True note [simp] = this
    fix C
    assume \<open>C \<in># NP + UP\<close>
    then obtain K where \<open>C = {#K#}\<close>
      using unit by auto
    then show \<open>\<exists>L. C = {#L#} \<and> (Some D = None \<or> 0 < count_decided M \<longrightarrow> get_level M L = 0 \<and> L \<in> lits_of_l M)\<close>
      by auto
  next
    case False
    fix C
    assume \<open>C \<in># NP + UP\<close>
    then obtain K where \<open>C = {#K#}\<close> and K: \<open>K \<in> lits_of_l ?M\<close> and lev_K: \<open>get_level ?M K = 0\<close>
      using unit False by auto
    moreover {
      have \<open>get_level ?M L > 0\<close>
        using False by auto
      then have \<open>atm_of L \<noteq> atm_of K\<close>
        using lev_K by fastforce }
    ultimately show \<open>\<exists>L. C = {#L#} \<and> (Some D = None \<or> 0 < count_decided M \<longrightarrow> get_level M L = 0 \<and> L \<in> lits_of_l M)\<close>
      using False by auto
  qed
next
  case (resolve L D C M N U NP UP) note twl = this(3)
  let ?M = \<open>Propagated L C # M\<close>
  let ?D = \<open>Some (remove1_mset (- L) D \<union># remove1_mset L C)\<close>
  have unit: \<open>unit_clss_inv (?M, N, U, Some D, NP, UP, {#}, {#})\<close>
    using twl unfolding twl_struct_invs_def by fast
  show ?case
    unfolding unit_clss_inv.simps Ball_def
  proof (intro allI impI, cases \<open>count_decided M = 0\<close>)
    case True note [simp] = this
    fix E
    assume \<open>E \<in># NP + UP\<close>
    then obtain K where \<open>E = {#K#}\<close>
      using unit by auto
    then show \<open>\<exists>La. E = {#La#} \<and> (?D = None \<or> 0 < count_decided M \<longrightarrow> get_level M La = 0 \<and> La \<in> lits_of_l M)\<close>
      by auto
  next
    case False
    fix E
    assume \<open>E \<in># NP + UP\<close>
    then obtain K where \<open>E = {#K#}\<close> and K: \<open>K \<in> lits_of_l ?M\<close> and lev_K: \<open>get_level ?M K = 0\<close>
      using unit False by auto
    moreover {
      have \<open>get_level ?M L > 0\<close>
        using False by auto
      then have \<open>atm_of L \<noteq> atm_of K\<close>
        using lev_K by fastforce }
    ultimately show \<open>\<exists>La. E = {#La#} \<and> (?D = None \<or> 0 < count_decided M \<longrightarrow> get_level M La = 0 \<and> La \<in> lits_of_l M)\<close>
      using False by auto
  qed
next
  case (backtrack_unit_clause L D K M1 M2 M D' i N U NP UP) note decomp = this(2) and
    lev_L = this(3) and i = this(5) and lev_K = this(6) and D'[simp] = this(7) and twl = this(10)
  let ?S = \<open>(M, N, U, Some D, NP, UP, {#}, {#})\<close>
  let ?T = \<open>(Propagated L {#L#} # M1, N, U, None, NP, add_mset {#L#} UP, {#}, {#- L#})\<close>
  let ?M = \<open>Propagated L {#L#} # M1\<close>
  have unit: \<open>unit_clss_inv ?S\<close>
    using twl unfolding twl_struct_invs_def by fast
  obtain M3 where M: \<open>M = M3 @ M2 @ Decided K # M1\<close>
    using decomp by auto
  define M2' where \<open>M2' = (M3 @ M2) @ Decided K # []\<close>
  have M2': \<open>M = M2' @ M1\<close>
    unfolding M M2'_def by simp
  have count_dec_M2': \<open>count_decided M2' \<noteq> 0\<close>
    unfolding M2'_def by auto
  have lev_M: \<open>count_decided M > 0\<close>
    unfolding M by auto
  have n_d: \<open>no_dup M\<close>
    using twl unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def twl_struct_invs_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: trail.simps)
  have count_dec_M1: \<open>count_decided M1 = 0\<close>
    using no_dup_append_decided_Cons_lev[of \<open>M3 @ M2\<close> K M1]
      lev_K n_d i unfolding M by simp

  show ?case
    unfolding unit_clss_inv.simps Ball_def
  proof (intro allI impI)
    fix C
    assume C: \<open>C \<in># NP +  add_mset {#L#} UP\<close>
    show \<open>\<exists>La. C = {#La#} \<and> (None = None \<or> 0 < count_decided ?M \<longrightarrow> get_level ?M La = 0 \<and>
        La \<in> lits_of_l ?M)\<close>
    proof (cases \<open>C \<in># NP + UP\<close>)
      case True
      then obtain K'' where C_K: \<open>C = {#K''#}\<close> and K: \<open>K'' \<in> lits_of_l M\<close> and lev_K'': \<open>get_level M K'' = 0\<close>
        using unit lev_M by auto
      have \<open>K'' \<in> lits_of_l M1\<close> (* and \<open>K'' \<notin> lits_of_l (M3 @ M2 @ Decided K # [])\<close> *)
      proof (rule ccontr)
        assume \<open>\<not> ?thesis\<close>
        then have \<open>K'' \<in> lits_of_l M2'\<close>
          using K unfolding M2' by auto
        then have ex_L: \<open>\<exists>L\<in>set ((M3 @ M2) @ [Decided K]). \<not> atm_of (lit_of L) \<noteq> atm_of K''\<close>
          by (metis M2'_def image_iff lits_of_def)
        have \<open>get_level (M2' @ M1) K'' = get_level M2' K'' + count_decided M1\<close>
          using \<open>K'' \<in> lits_of_l M2'\<close> Decided_Propagated_in_iff_in_lits_of_l get_level_skip_end by blast

        with last_in_set_dropWhile[OF ex_L, unfolded M2'_def[symmetric]] have \<open>\<not>get_level M K'' = 0\<close>
          unfolding M2' using \<open>K'' \<in> lits_of_l M2'\<close> by (force simp: filter_empty_conv get_level_def)
        then show False
        using lev_K'' by arith
      qed
      then have K: \<open>K'' \<in> lits_of_l ?M\<close>
        unfolding M by auto
      moreover {
        have \<open>atm_of L \<noteq> atm_of K''\<close>
          using lev_L lev_K'' lev_M by (auto simp: atm_of_eq_atm_of)
        then have \<open>get_level ?M K'' = 0\<close>
          using count_dec_M1 count_decided_ge_get_level[of ?M K''] by auto }
      ultimately show ?thesis
        using C_K by auto
    next
      case False
      then have \<open>C = {#L#}\<close>
        using C by auto
      then show ?thesis
        using count_dec_M1 by auto
    qed
  qed
next
  case (backtrack_nonunit_clause L D K M1 M2 M D' i N U NP UP L') note decomp = this(2) and
    lev_L_M = this(3) and lev_K = this(6) and twl = this(13)
  let ?S = \<open>(M, N, U, Some D, NP, UP, {#}, {#})\<close>
  let ?T = \<open>(Propagated L D' # M1, N, add_mset (TWL_Clause {#L, L'#} (D' - {#L, L'#})) U, None, NP, UP, {#}, {#-L#})\<close>
  let ?M = \<open>Propagated L D' # M1\<close>
  have unit: \<open>unit_clss_inv ?S\<close>
    using twl unfolding twl_struct_invs_def by fast
  obtain M3 where M: \<open>M = M3 @ M2 @ Decided K # M1\<close>
    using decomp by auto
  define M2' where \<open>M2' = (M3 @ M2) @ Decided K # []\<close>
  have M2': \<open>M = M2' @ M1\<close>
    unfolding M M2'_def by simp
  have count_dec_M2': \<open>count_decided M2' \<noteq> 0\<close>
    unfolding M2'_def by auto
  have lev_M: \<open>count_decided M > 0\<close>
    unfolding M by auto
  have n_d: \<open>no_dup M\<close>
    using twl unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def twl_struct_invs_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: trail.simps)
  have count_dec_M1: \<open>count_decided M1 = i\<close>
    using no_dup_append_decided_Cons_lev[of \<open>M3 @ M2\<close> K M1]
      lev_K n_d unfolding M by simp

  show ?case
    unfolding unit_clss_inv.simps Ball_def
  proof (intro allI impI)
    fix C
    assume C: \<open>C \<in># NP + UP\<close>
    then obtain K'' where C_K: \<open>C = {#K''#}\<close> and K: \<open>K'' \<in> lits_of_l M\<close> and lev_K'': \<open>get_level M K'' = 0\<close>
      using unit lev_M by auto
    have K''_M1: \<open>K'' \<in> lits_of_l M1\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then have \<open>K'' \<in> lits_of_l M2'\<close>
        using K unfolding M2' by auto
      then have \<open>\<exists>L\<in>set ((M3 @ M2) @ [Decided K]). \<not> atm_of (lit_of L) \<noteq> atm_of K''\<close>
        by (metis M2'_def image_iff lits_of_def)
      then have ex_L: \<open>\<exists>L\<in>set ((M3 @ M2) @ [Decided K]). \<not> atm_of (lit_of L) \<noteq> atm_of K''\<close>
        by (metis M2'_def image_iff lits_of_def)
      have \<open>get_level (M2' @ M1) K'' = get_level M2' K'' + count_decided M1\<close>
        using \<open>K'' \<in> lits_of_l M2'\<close> Decided_Propagated_in_iff_in_lits_of_l get_level_skip_end by blast

      with last_in_set_dropWhile[OF ex_L, unfolded M2'_def[symmetric]] have \<open>\<not>get_level M K'' = 0\<close>
        unfolding M2' using \<open>K'' \<in> lits_of_l M2'\<close> by (force simp: filter_empty_conv get_level_def)
      then show False
        using lev_K'' by arith
    qed
    then have K: \<open>K'' \<in> lits_of_l ?M\<close>
      unfolding M by auto
    moreover {
      have \<open>undefined_lit (M3 @ M2 @ [Decided K]) K''\<close>
        by (rule CDCL_W_Abstract_State.cdcl\<^sub>W_restart_mset.no_dup_append_in_atm_notin[of _ \<open>M1\<close>])
          (use n_d M K''_M1 in auto)
      then have \<open>get_level M1 K'' = 0\<close>
        using lev_K'' unfolding M by (auto simp: image_Un)
      moreover have \<open>atm_of L \<noteq> atm_of K''\<close>
        using lev_K'' lev_M lev_L_M by (metis atm_of_eq_atm_of get_level_uminus not_gr_zero)
      ultimately have \<open>get_level ?M K'' = 0\<close>
        by auto }
    ultimately show \<open>\<exists>La. C = {#La#} \<and> (None = None \<or> 0 < count_decided ?M \<longrightarrow> get_level ?M La = 0 \<and>
      La \<in> lits_of_l ?M)\<close>
      using C_K by auto
  qed
qed


subsubsection \<open>The Strategy\<close>

lemma no_literals_to_update_no_cp:
  assumes
    WS: \<open>clauses_to_update S = {#}\<close> and Q: \<open>literals_to_update S = {#}\<close> and
    twl: \<open>twl_struct_invs S\<close>
  shows
    \<open>no_step cdcl\<^sub>W_restart_mset.propagate (state\<^sub>W_of S)\<close> and
    \<open>no_step cdcl\<^sub>W_restart_mset.conflict (state\<^sub>W_of S)\<close>
proof -
  obtain M N U NP UP D where
      S: \<open>S = (M, N, U, D, NP, UP, {#}, {#})\<close>
    using WS Q by (cases S) auto

  {
    assume confl: \<open>get_conflict S = None\<close>
    then have S: \<open>S = (M, N, U, None, NP, UP, {#}, {#})\<close>
      using WS Q S by auto

    have twl_st_inv: \<open>twl_st_inv S\<close> and
      struct_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S)\<close> and
      excep: \<open>twl_st_exception_inv S\<close> and
      confl_cands: \<open>confl_cands_enqueued S\<close> and
      propa_cands: \<open>propa_cands_enqueued S\<close> and
      unit: \<open>unit_clss_inv S\<close>
      using twl unfolding twl_struct_invs_def by fast+
    have n_d: \<open>no_dup M\<close>
      using struct_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: trail.simps S)
    then have L_uL: \<open>L \<in> lits_of_l M \<Longrightarrow> -L \<notin> lits_of_l M\<close> for L
      using consistent_interp_def distinct_consistent_interp by blast
    have \<open>\<forall>C \<in># N + U. \<not>M\<Turnstile>as CNot (clause C)\<close>
      using confl_cands unfolding S by auto
    moreover have \<open>\<not>M\<Turnstile>as CNot C\<close> if C: \<open>C \<in># NP + UP\<close> for C
    proof -
      obtain L where L: \<open>C = {#L#}\<close> and \<open>L \<in> lits_of_l M\<close>
        using unit C unfolding S by auto
      then have \<open>M \<Turnstile>a C\<close>
        by auto
      then show ?thesis
        unfolding L by (auto simp: true_annots_true_cls_def_iff_negation_in_model dest: L_uL)
    qed
    ultimately have ns_confl: \<open>no_step cdcl\<^sub>W_restart_mset.conflict (state\<^sub>W_of S)\<close>
      by (auto elim!: cdcl\<^sub>W_restart_mset.conflictE simp: S trail.simps clauses_def)

    have ns_propa: \<open>no_step cdcl\<^sub>W_restart_mset.propagate (state\<^sub>W_of S)\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then obtain C L where
        C: \<open>C \<in># clause `# (N + U) + NP + UP\<close> and
        L: \<open>L \<in># C\<close> and
        M: \<open>M \<Turnstile>as CNot (remove1_mset L C)\<close> and
        undef: \<open>undefined_lit M L\<close>
        by (auto elim!: cdcl\<^sub>W_restart_mset.propagateE simp: S trail.simps clauses_def) blast+
      show False
      proof (cases \<open>C \<in># clause `# (N + U)\<close>)
        case True
        then show ?thesis
          using propa_cands L M undef by (auto simp: S)
      next
        case False
        then have \<open>C \<in># NP + UP\<close>
          using C by auto
        then obtain L'' where L'': \<open>C = {#L''#}\<close> and L''_def: \<open>L'' \<in> lits_of_l M\<close>
          using unit unfolding S by auto
        then have [simp]: \<open>L'' = L\<close>
          using L by auto
        show ?thesis
          using undef L'' L''_def
          by (auto simp: S true_annots_true_cls_def_iff_negation_in_model
              Decided_Propagated_in_iff_in_lits_of_l dest: L_uL)
      qed
    qed
    note ns_confl ns_propa
  }
  moreover {
    assume \<open>get_conflict S \<noteq> None\<close>
    then have \<open>no_step cdcl\<^sub>W_restart_mset.propagate (state\<^sub>W_of S)\<close>
      \<open>no_step cdcl\<^sub>W_restart_mset.conflict (state\<^sub>W_of S)\<close>
      by (auto elim!: cdcl\<^sub>W_restart_mset.propagateE cdcl\<^sub>W_restart_mset.conflictE
          simp: S conflicting.simps)
  }
  ultimately show \<open>no_step cdcl\<^sub>W_restart_mset.propagate (state\<^sub>W_of S)\<close>
      \<open>no_step cdcl\<^sub>W_restart_mset.conflict (state\<^sub>W_of S)\<close>
    by blast+
qed

text \<open>
  When popping a literal from \<^term>\<open>literals_to_update\<close> to the \<^term>\<open>clauses_to_update\<close>, we do not do any
  transition in the abstract transition system. Therefore, we use \<^term>\<open>rtranclp\<close> or a case distinction
  \<close>

lemma cdcl_twl_stgy_cdcl\<^sub>W_stgy2:
  assumes \<open>cdcl_twl_stgy S T\<close> and twl: \<open>twl_struct_invs S\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (state\<^sub>W_of S) (state\<^sub>W_of T) \<or>
    (state\<^sub>W_of S = state\<^sub>W_of T \<and> (literals_to_update_measure T, literals_to_update_measure S) \<in> lexn less_than 2)\<close>
  using assms(1)
proof (induction rule: cdcl_twl_stgy.induct)
  case (cp S')
  then show ?case
    using twl by (auto dest!: cdcl_twl_cp_cdcl\<^sub>W_stgy)
next
  case (other' S') note o = this(1)
  have wq: \<open>clauses_to_update S = {#}\<close> and p: \<open>literals_to_update S = {#}\<close>
    using o by (cases rule: cdcl_twl_o.cases; auto)+
  show ?case
    apply (rule disjI1)
    apply (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.other')
    using no_literals_to_update_no_cp[OF wq p twl] apply (simp; fail)
    using no_literals_to_update_no_cp[OF wq p twl] apply (simp; fail)
    using cdcl_twl_o_cdcl\<^sub>W_o[of S S', OF o] twl apply (simp add: twl_struct_invs_def; fail)
    done
qed

lemma cdcl_twl_stgy_cdcl\<^sub>W_stgy:
  assumes \<open>cdcl_twl_stgy S T\<close> and twl: \<open>twl_struct_invs S\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (state\<^sub>W_of S) (state\<^sub>W_of T)\<close>
  using cdcl_twl_stgy_cdcl\<^sub>W_stgy2[OF assms] by auto

lemma cdcl_twl_o_twl_struct_invs:
  assumes
    cdcl: \<open>cdcl_twl_o S T\<close> and
    twl: \<open>twl_struct_invs S\<close>
  shows \<open>twl_struct_invs T\<close>
proof -
  have cdcl\<^sub>W: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart (state\<^sub>W_of S) (state\<^sub>W_of T)\<close>
    using twl unfolding twl_struct_invs_def by (meson cdcl cdcl\<^sub>W_restart_mset.other cdcl_twl_o_cdcl\<^sub>W_o)

  have wq: \<open>clauses_to_update S = {#}\<close> and p: \<open>literals_to_update S = {#}\<close>
    using cdcl by (cases rule: cdcl_twl_o.cases; auto)+
  have cdcl\<^sub>W_stgy: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (state\<^sub>W_of S) (state\<^sub>W_of T)\<close>
    apply (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.other')
    using no_literals_to_update_no_cp[OF wq p twl] apply (simp; fail)
    using no_literals_to_update_no_cp[OF wq p twl] apply (simp; fail)
    using cdcl_twl_o_cdcl\<^sub>W_o[of S T, OF cdcl] twl apply (simp add: twl_struct_invs_def; fail)
    done
  have init: \<open>init_clss (state\<^sub>W_of T) = init_clss (state\<^sub>W_of S)\<close>
    using cdcl\<^sub>W by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart_init_clss)
  show ?thesis
    unfolding twl_struct_invs_def
    apply (intro conjI)
    subgoal by (use cdcl cdcl_twl_o_twl_st_inv twl in \<open>blast; fail\<close>)
    subgoal by (use cdcl cdcl_twl_o_valid in \<open>blast; fail\<close>)
    subgoal by (use cdcl\<^sub>W cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_inv twl twl_struct_invs_def in
          \<open>blast; fail\<close>)
    subgoal by (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_no_smaller_propa[OF cdcl\<^sub>W_stgy])
        ((use twl in \<open>simp add: init twl_struct_invs_def; fail\<close>)+)[2]
    subgoal by (use cdcl cdcl_twl_o_twl_st_exception_inv twl in \<open>blast; fail\<close>)
    subgoal by (use cdcl cdcl_twl_o_no_duplicate_queued in \<open>blast; fail\<close>)
    subgoal by (use cdcl cdcl_twl_o_distinct_queued in \<open>blast; fail\<close>)
    subgoal by (use cdcl cdcl_twl_o_confl_cands_enqueued twl twl_struct_invs_def in \<open>blast; fail\<close>)
    subgoal by (use cdcl cdcl_twl_o_propa_cands_enqueued twl twl_struct_invs_def in \<open>blast; fail\<close>)
    subgoal by (use cdcl twl cdcl_twl_o_conflict_None_queue in \<open>blast; fail\<close>)
    subgoal by (use cdcl cdcl_twl_o_unit_clss_inv twl twl_struct_invs_def in blast)
    subgoal by (use cdcl twl_o_clauses_to_update twl in blast)
    subgoal by (use cdcl cdcl_twl_o_past_invs twl twl_struct_invs_def in blast)
    done
qed

lemma cdcl_twl_stgy_twl_struct_invs:
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
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (state\<^sub>W_of S) (state\<^sub>W_of T)\<close>
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
  then obtain M N U UP NP WS Q where S: \<open>S = (M, N, U, None, NP, UP, WS, Q)\<close>
    by (cases S) auto
  have valid: \<open>valid_annotation S\<close> and twl: \<open>twl_st_inv S\<close>
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
    have L'_M: \<open>L' \<notin> lits_of_l M\<close>
      using cdcl_twl_cp.delete_from_working[of C L L' M N U NP UP WS' Q] watched
      ns_cp unfolding S WS' by fast
    then have \<open>undefined_lit M L' \<or> -L' \<in> lits_of_l M\<close>
      using Decided_Propagated_in_iff_in_lits_of_l by blast
    then have \<open>\<not> (\<forall>L \<in># unwatched C. -L \<in> lits_of_l M)\<close>
      using cdcl_twl_cp.conflict[of C L L' M N U NP UP WS' Q]
        cdcl_twl_cp.propagate[of C L L' M N U NP UP WS' Q] watched
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
      using cdcl_twl_cp.update_clause[of C L L' M K N U \<open>fst NU\<close> \<open>snd NU\<close> NP UP WS' Q]
      watched uL_M L'_M K undef_K_K_M upd ns_cp unfolding S WS' by simp
  qed
  then have p: \<open>literals_to_update S = {#}\<close>
    using cdcl_twl_cp.pop[of M N U NP UP] S ns_cp by (cases \<open>Q\<close>) fastforce+
  show ?thesis using wq p by blast
qed

lemma no_step_cdcl_twl_o_no_step_cdcl\<^sub>W_o:
  assumes ns_o: \<open>no_step cdcl_twl_o S\<close> and twl: \<open>twl_struct_invs S\<close> and p: \<open>literals_to_update S = {#}\<close> and
    w_q: \<open>clauses_to_update S = {#}\<close>
  shows \<open>no_step cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o (state\<^sub>W_of S)\<close>
proof (rule ccontr)
  assume \<open>\<not> ?thesis\<close>
  then obtain T where T: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o (state\<^sub>W_of S) T\<close>
    by blast
  obtain M N U D NP UP where S: \<open>S = (M, N, U, D, NP, UP, {#}, {#})\<close>
    using p w_q by (cases S) auto
  have unit: \<open>unit_clss_inv S\<close>
    using twl unfolding twl_struct_invs_def by fast+
  show False
    using T
  proof (cases rule: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o_induct)
    case (decide L T) note confl = this(1) and undef = this(2) and atm = this(3) and T = this(4)
    have \<open>atm_of L \<notin> atms_of_mm NP\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then obtain C where C_NP: \<open>C \<in># NP\<close> and L_uL_C: \<open>L \<in># C \<or> -L \<in># C\<close>
        by (auto simp: atms_of_ms_def atms_of_def atm_of_eq_atm_of)
      obtain L' where \<open>C = {#L'#}\<close> and \<open>L' \<in> lits_of_l M\<close>
        using unit S confl C_NP by (auto simp: cdcl\<^sub>W_restart_mset_state)
      then show False
        using L_uL_C undef unfolding S
        by (auto simp: cdcl\<^sub>W_restart_mset_state Decided_Propagated_in_iff_in_lits_of_l)
    qed
    then show ?thesis
      using cdcl_twl_o.decide[of M L N U NP UP] confl undef atm ns_o unfolding S
      by (auto simp: cdcl\<^sub>W_restart_mset_state)
  next
    case (skip L C' M' E T) note M = this and confl = this(2) and uL_E = this(3) and E = this(4) and
      T = this(5)
    show ?thesis
      using cdcl_twl_o.skip[of L E C' M' N U NP UP] M uL_E E ns_o unfolding S
      by (auto simp: cdcl\<^sub>W_restart_mset_state)
  next
    case (resolve L E M' D T) note M = this(1) and L_E = this(2) and hd = this(3) and confl = this(4)
    and uL_D = this(5) and max_lvl = this(6)
    show ?thesis
      using cdcl_twl_o.resolve[of L D E M' N U NP UP] M L_E ns_o max_lvl uL_D confl unfolding S
      by (auto simp: cdcl\<^sub>W_restart_mset_state)
  next
    case (backtrack L C K i M1 M2 T D') note confl = this(1) and decomp = this(2) and
    lev_L_bt = this(3) and lev_L = this(4) and i = this(5) and lev_K = this(6) and D'_C = this(7)
    show ?thesis
    proof (cases \<open>D' = {#}\<close>)
      case True
      show ?thesis
        using cdcl_twl_o.backtrack_unit_clause[of L \<open>add_mset L C\<close> K M1 M2 M \<open>add_mset L D'\<close> i N U NP UP]
        decomp True lev_L_bt lev_L i lev_K ns_o confl backtrack unfolding S
        by (auto simp: cdcl\<^sub>W_restart_mset_state clauses_def inf_sup_aci(6) sup.left_commute)
    next
      case False
      then obtain L' where
        L'_C: \<open>L' \<in># D'\<close> and lev_L': \<open>get_level M L' = i\<close>
        using i get_maximum_level_exists_lit_of_max_level[of D' M] confl S
        by (auto simp: cdcl\<^sub>W_restart_mset_state S dest: in_diffD)

      show ?thesis
        using cdcl_twl_o.backtrack_nonunit_clause[of L \<open>add_mset L C\<close> K M1 M2 M \<open>add_mset L D'\<close>
            i N U NP UP L']
        using decomp lev_L_bt lev_L i lev_K False L'_C lev_L' ns_o confl backtrack
        by (auto simp: cdcl\<^sub>W_restart_mset_state S  inf_sup_aci(6) sup.left_commute clauses_def
            dest: in_diffD)
    qed
  qed
qed

lemma no_step_cdcl_twl_stgy_no_step_cdcl\<^sub>W_stgy:
  assumes ns: \<open>no_step cdcl_twl_stgy S\<close> and twl: \<open>twl_struct_invs S\<close>
  shows \<open>no_step cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (state\<^sub>W_of S)\<close>
proof -
  have ns_cp: \<open>no_step cdcl_twl_cp S\<close> and ns_o: \<open>no_step cdcl_twl_o S\<close>
    using ns by (auto simp: cdcl_twl_stgy.simps)
  then have w_q: \<open>clauses_to_update S = {#}\<close> and p: \<open>literals_to_update S = {#}\<close>
    using ns_cp no_step_cdcl_twl_cp_no_step_cdcl\<^sub>W_cp twl by blast+
  then have
    \<open>no_step cdcl\<^sub>W_restart_mset.propagate (state\<^sub>W_of S)\<close> and
    \<open>no_step cdcl\<^sub>W_restart_mset.conflict (state\<^sub>W_of S)\<close>
    using no_literals_to_update_no_cp twl by blast+
  moreover have \<open>no_step cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o (state\<^sub>W_of S)\<close>
    using w_q p ns_o no_step_cdcl_twl_o_no_step_cdcl\<^sub>W_o twl by blast
  ultimately show ?thesis
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.simps)
qed


lemma full_cdcl_twl_stgy_cdcl\<^sub>W_stgy:
  assumes \<open>full cdcl_twl_stgy S T\<close> and twl: \<open>twl_struct_invs S\<close>
  shows \<open>full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (state\<^sub>W_of S) (state\<^sub>W_of T)\<close>
  by (metis (no_types, hide_lams) assms(1) full_def no_step_cdcl_twl_stgy_no_step_cdcl\<^sub>W_stgy
      rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy rtranclp_cdcl_twl_stgy_twl_struct_invs twl)

definition init_state_twl where
  \<open>init_state_twl N \<equiv> ([], N, {#}, None, {#}, {#}, {#}, {#})\<close>
lemma
  assumes
    struct: \<open>\<forall>C \<in># N. struct_wf_twl_cls C\<close> and
    tauto: \<open>\<forall>C \<in># N. \<not>tautology (clause C)\<close>
  shows
    twl_stgy_invs_init_state_twl: \<open>twl_stgy_invs (init_state_twl N)\<close> and
    twl_struct_invs_init_state_twl: \<open>twl_struct_invs (init_state_twl N)\<close>
proof -
  have [simp]: \<open>twl_lazy_update [] C\<close> \<open>twl_inv [] C\<close> \<open>watched_literals_false_of_max_level [] C\<close>
    \<open>twl_exception_inv ([], N, {#}, None, {#}, {#}, {#}, {#}) C\<close> for C
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
    by (rule size_ne_size_imp_ne[of _ \<open>{#}\<close>]; use size_C[OF that] in
        \<open>auto simp: remove1_mset_empty_iff union_is_single\<close>)+

  have \<open>distinct_mset (clause C)\<close> if \<open>C \<in># N\<close> for C
    using struct that by (cases C) (auto)
  then have dist: \<open>distinct_mset_mset (clause `# N)\<close>
    by (auto simp: distinct_mset_set_def)
  then have [simp]: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv ([], clause `# N, {#}, None)\<close>
    using struct unfolding init_state.simps[symmetric]
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
  have [simp]: \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa ([], clause `# N, {#}, None)\<close>
    by(auto simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def cdcl\<^sub>W_restart_mset_state)

  show stgy_invs: \<open>twl_stgy_invs (init_state_twl N)\<close>
    by (auto simp: twl_stgy_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
        cdcl\<^sub>W_restart_mset_state cdcl\<^sub>W_restart_mset.no_smaller_confl_def init_state_twl_def)
  show \<open>twl_struct_invs (init_state_twl N)\<close>
    using struct tauto
    by (auto simp: twl_struct_invs_def twl_st_inv.simps clauses_to_update_prop.simps
        past_invs.simps cdcl\<^sub>W_restart_mset_state init_state_twl_def
        cdcl\<^sub>W_restart_mset.no_strange_atm_def)
qed

lemma full_cdcl_twl_stgy_cdcl\<^sub>W_stgy_conclusive_from_init_state:
  fixes N :: \<open>'v twl_clss\<close>
  assumes
    full_cdcl_twl_stgy: \<open>full cdcl_twl_stgy (init_state_twl N) T\<close> and
    struct: \<open>\<forall>C \<in># N. struct_wf_twl_cls C\<close> and
    no_tauto: \<open>\<forall>C \<in># N. \<not>tautology (clause C)\<close>
  shows \<open>conflicting (state\<^sub>W_of T) = Some {#} \<and> unsatisfiable (set_mset (clause `# N)) \<or>
     (conflicting (state\<^sub>W_of T) = None \<and> trail (state\<^sub>W_of T) \<Turnstile>asm clause `# N \<and>
     satisfiable (set_mset (clause `# N)))\<close>
proof -
  have \<open>distinct_mset (clause C)\<close> if \<open>C \<in># N\<close> for C
    using struct that by (cases C) auto
  then have dist: \<open>distinct_mset_mset (clause `# N)\<close>
    using struct by (auto simp: distinct_mset_set_def)

  have \<open>twl_struct_invs (init_state_twl N)\<close>
    using struct no_tauto by (rule twl_struct_invs_init_state_twl)
  with full_cdcl_twl_stgy
  have \<open>full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (state\<^sub>W_of (init_state_twl N)) (state\<^sub>W_of T)\<close>
    by (rule full_cdcl_twl_stgy_cdcl\<^sub>W_stgy)
  then have \<open>full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (init_state (clause `# N)) (state\<^sub>W_of T)\<close>
    by (simp add: init_state.simps init_state_twl_def)
  then show ?thesis
    by (rule cdcl\<^sub>W_restart_mset.full_cdcl\<^sub>W_stgy_final_state_conclusive_from_init_state)
      (use dist in auto)
qed

lemma cdcl_twl_o_twl_stgy_invs:
  \<open>cdcl_twl_o S T \<Longrightarrow> twl_struct_invs S \<Longrightarrow> twl_stgy_invs S \<Longrightarrow> twl_stgy_invs T\<close>
  using cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_stgy_invariant cdcl_twl_stgy_cdcl\<^sub>W_stgy
    other'
  unfolding twl_struct_invs_def twl_stgy_invs_def by blast


paragraph \<open>Well-foundedness\<close>


lemma wf_cdcl\<^sub>W_stgy_state\<^sub>W_of:
  \<open>wf {(T, S). cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S) \<and>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (state\<^sub>W_of S) (state\<^sub>W_of T)}\<close>
  using wf_if_measure_f[OF cdcl\<^sub>W_restart_mset.wf_cdcl\<^sub>W_stgy, of state\<^sub>W_of] by simp

lemma wf_cdcl_twl_cp:
  \<open>wf {(T, S). twl_struct_invs S \<and> cdcl_twl_cp S T}\<close> (is \<open>wf ?TWL\<close>)
proof -
  let ?CDCL = \<open>{(T, S). cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S) \<and>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (state\<^sub>W_of S) (state\<^sub>W_of T)}\<close>
  let ?P = \<open>{(T, S). state\<^sub>W_of S = state\<^sub>W_of T \<and>
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
    have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S)\<close>
      using twl by (auto simp: twl_struct_invs_def)
    moreover have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (state\<^sub>W_of S) (state\<^sub>W_of T) \<or>
      (state\<^sub>W_of S = state\<^sub>W_of T \<and>
        (literals_to_update_measure T, literals_to_update_measure S) \<in> lexn less_than 2)\<close>
      using cdcl cdcl_twl_cp_cdcl\<^sub>W_stgy twl by blast
    ultimately show \<open>x \<in> ?CDCL \<union> ?P\<close>
      unfolding x by blast
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
  let ?CDCL = \<open>{(T, S). cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S) \<and>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (state\<^sub>W_of S) (state\<^sub>W_of T)}\<close>
  let ?P = \<open>{(T, S). state\<^sub>W_of S = state\<^sub>W_of T \<and>
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

    have twl: \<open>twl_struct_invs S\<close> and cdcl: \<open>cdcl_twl_stgy S T\<close>
      using x_TWL x by auto
    have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S)\<close>
      using twl by (auto simp: twl_struct_invs_def)
    moreover have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (state\<^sub>W_of S) (state\<^sub>W_of T) \<or>
      (state\<^sub>W_of S = state\<^sub>W_of T \<and>
         (literals_to_update_measure T, literals_to_update_measure S) \<in> lexn less_than 2)\<close>
      using cdcl cdcl_twl_stgy_cdcl\<^sub>W_stgy2 twl by blast
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

fun get_learned_clss :: "'v twl_st \<Rightarrow> 'v twl_clss" where
  \<open>get_learned_clss (_, N, U, _, _, _, _) = N + U\<close>

lemma (in -)propa_cands_enqueued_mono:
  \<open>U' \<subseteq># U \<Longrightarrow>
     propa_cands_enqueued  (M, N, U, D, NP, UP, WS, Q) \<Longrightarrow>
      propa_cands_enqueued  (M, N, U', D, NP, UP, WS, Q)\<close>
  by (cases D) auto

lemma (in -)confl_cands_enqueued_mono:
  \<open>U' \<subseteq># U \<Longrightarrow>
     confl_cands_enqueued  (M, N, U, D, NP, UP, WS, Q) \<Longrightarrow>
      confl_cands_enqueued  (M, N, U', D, NP, UP, WS, Q)\<close>
  by (cases D) auto

lemma (in -)twl_st_exception_inv_mono:
  \<open>U' \<subseteq># U \<Longrightarrow>
     twl_st_exception_inv  (M, N, U, D, NP, UP, WS, Q) \<Longrightarrow>
      twl_st_exception_inv  (M, N, U', D, NP, UP, WS, Q)\<close>
  by (cases D) (fastforce simp: twl_exception_inv.simps)+

lemma (in -)twl_st_inv_mono:
  \<open>U' \<subseteq># U \<Longrightarrow>
     twl_st_inv  (M, N, U, D, NP, UP, WS, Q) \<Longrightarrow>
      twl_st_inv  (M, N, U', D, NP, UP, WS, Q)\<close>
  by (cases D) (fastforce simp: twl_st_inv.simps)+

lemma (in -) rtranclp_cdcl_twl_stgy_twl_stgy_invs:
  assumes
    \<open>cdcl_twl_stgy\<^sup>*\<^sup>* S T\<close> and
    \<open>twl_struct_invs S\<close> and
    \<open>twl_stgy_invs S\<close>
  shows \<open>twl_stgy_invs T\<close>
  using assms cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_stgy_invariant
    rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy unfolding twl_stgy_invs_def twl_struct_invs_def by blast

lemma after_fast_restart_replay:
  assumes
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M', N, U, None)\<close> and
    stgy_invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (M', N, U, None)\<close> and
    smaller_propa: \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (M', N, U, None)\<close> and
    kept: \<open>\<forall>L E. Propagated L E \<in> set (drop (length M' - n) M') \<longrightarrow> E \<in># N + U'\<close> and
    U'_U: \<open>U' \<subseteq># U\<close>
  shows
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ([], N, U', None) (drop (length M' - n) M', N, U', None)\<close>
proof -
  let ?S = \<open>\<lambda>n. (drop (length M' - n) M', N, U', None)\<close>
  note cdcl\<^sub>W_restart_mset_state[simp]
  have
    M_lev: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (M', N, U, None)\<close> and
    alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (M', N, U, None)\<close> and
    confl: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (M', N, U, None)\<close> and
    learned: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause (M', N, U, None)\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast+

  have smaller_confl: \<open>cdcl\<^sub>W_restart_mset.no_smaller_confl (M', N, U, None)\<close>
    using stgy_invs unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def by blast
  have n_d: \<open>no_dup M'\<close>
    using M_lev unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by simp
  let ?L = \<open>\<lambda>m. M' ! (length M' - Suc m)\<close>
  have undef_nth_Suc:
     \<open>undefined_lit (drop (length M' - m) M') (lit_of (?L m))\<close>
     if \<open>m < length M'\<close>
     for m
  proof -
    define k where
      \<open>k = length M' - Suc m\<close>
    then have Sk: \<open>length M' - m = Suc k\<close>
      using that by linarith
    have k_le_M': \<open>k < length M'\<close>
      using that unfolding k_def by linarith
    have n_d': \<open>no_dup (take k M' @ ?L m # drop (Suc k) M')\<close>
      using n_d
      apply (subst (asm) append_take_drop_id[symmetric, of _ \<open>Suc k\<close>])
      apply (subst (asm) take_Suc_conv_app_nth)
       apply (rule k_le_M')
      apply (subst k_def[symmetric])
      by simp

    show ?thesis
      using n_d'
      apply (subst (asm) no_dup_append_cons)
      apply (subst (asm) k_def[symmetric])+
      apply (subst k_def[symmetric])+
      apply (subst Sk)+
      by blast
  qed

  have atm_in:
    \<open>atm_of (lit_of (M' ! m)) \<in> atms_of_mm N\<close>
    if \<open>m < length M'\<close>
    for m
    using alien that
    by (auto simp: cdcl\<^sub>W_restart_mset.no_strange_atm_def lits_of_def)

  show ?thesis
    using kept
  proof (induction n)
    case 0
    then show ?case by simp
  next
    case (Suc m) note IH = this(1) and kept = this(2)
    consider
      (le) \<open>m < length M'\<close> |
      (ge) \<open>m \<ge> length M'\<close>
      by linarith
    then show ?case
    proof (cases)
      case ge
      then show ?thesis
        using Suc by auto
    next
      case le
      define k where
        \<open>k = length M' - Suc m\<close>
      then have Sk: \<open>length M' - m = Suc k\<close>
        using le by linarith
      have k_le_M': \<open>k < length M'\<close>
        using le unfolding k_def by linarith
      have kept': \<open>\<forall>L E. Propagated L E \<in> set (drop (length M' - m) M') \<longrightarrow> E \<in># N + U'\<close>
        using kept k_le_M' unfolding k_def[symmetric] Sk
        by (subst (asm) Cons_nth_drop_Suc[symmetric]) auto
      have M': \<open>M' = take (length M' - Suc m) M' @ ?L m # trail (?S m)\<close>
        apply (subst append_take_drop_id[symmetric, of _ \<open>Suc k\<close>])
        apply (subst take_Suc_conv_app_nth)
         apply (rule k_le_M')
        apply (subst k_def[symmetric])
        unfolding k_def[symmetric] Sk
        by auto

      have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (?S m) (?S (Suc m))\<close>
      proof (cases \<open>?L (m)\<close>)
        case (Decided K) note K = this
        have dec: \<open>cdcl\<^sub>W_restart_mset.decide (?S m) (?S (Suc m))\<close>
          apply (rule cdcl\<^sub>W_restart_mset.decide_rule[of _ \<open>lit_of (?L m)\<close>])
          subgoal by simp
          subgoal using undef_nth_Suc[of m] le by simp
          subgoal using le by (auto simp: atm_in)
          subgoal using le k_le_M' K unfolding k_def[symmetric] Sk
            by (auto simp: state_eq_def state_def Cons_nth_drop_Suc[symmetric])
          done
        have Dec: \<open>M' ! k = Decided K\<close>
          using K unfolding k_def[symmetric] Sk .

        have H: \<open>D + {#L#} \<in># N + U \<longrightarrow> undefined_lit (trail (?S m)) L \<longrightarrow>
            \<not> (trail (?S m)) \<Turnstile>as CNot D\<close> for D L
          using smaller_propa unfolding cdcl\<^sub>W_restart_mset.no_smaller_propa_def trail.simps clauses_def
            cdcl\<^sub>W_restart_mset_state
          apply (subst (asm) M')
          unfolding Dec Sk k_def[symmetric]
          by (auto simp: clauses_def state_eq_def)
        have \<open>D \<in># N \<longrightarrow> undefined_lit (trail (?S m)) L \<longrightarrow> L \<in># D \<longrightarrow>
            \<not> (trail (?S m)) \<Turnstile>as CNot (remove1_mset L D)\<close> and
          \<open>D \<in># U' \<longrightarrow> undefined_lit (trail (?S m)) L \<longrightarrow> L \<in># D \<longrightarrow>
            \<not> (trail (?S m)) \<Turnstile>as CNot (remove1_mset L D)\<close>for D L
          using H[of \<open>remove1_mset L D\<close> L] U'_U by auto
        then have nss: \<open>no_step cdcl\<^sub>W_restart_mset.propagate (?S m)\<close>
          by (auto simp: cdcl\<^sub>W_restart_mset.propagate.simps clauses_def state_eq_def k_def[symmetric] Sk)

        have H: \<open>D \<in># N + U' \<longrightarrow> \<not> (trail (?S m)) \<Turnstile>as CNot D\<close> for D
          using smaller_confl U'_U unfolding cdcl\<^sub>W_restart_mset.no_smaller_confl_def trail.simps clauses_def
            cdcl\<^sub>W_restart_mset_state
          apply (subst (asm) M')
          unfolding Dec Sk k_def[symmetric]
          by (auto simp: clauses_def state_eq_def)
        then have nsc: \<open>no_step cdcl\<^sub>W_restart_mset.conflict (?S m)\<close>
          by (auto simp: cdcl\<^sub>W_restart_mset.conflict.simps clauses_def state_eq_def k_def[symmetric] Sk)
        show ?thesis
          apply (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.other')
            apply (rule nsc)
           apply (rule nss)
          apply (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o.decide)
          apply (rule dec)
          done
      next
        case K: (Propagated K C)
        have Propa: \<open>M' ! k = Propagated K C\<close>
          using K unfolding k_def[symmetric] Sk .
        have
          M_C: \<open>trail (?S m) \<Turnstile>as CNot (remove1_mset K C)\<close> and
          K_C: \<open>K \<in># C\<close>
          using confl unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def trail.simps
          by (subst (asm)(3) M'; auto simp: k_def[symmetric] Sk Propa)+
        have [simp]: \<open>k - min (length M') k = 0\<close>
          unfolding k_def by auto
        have C_N_U: \<open>C \<in># N + U'\<close>
          using learned kept unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def Sk k_def[symmetric]
          apply (subst (asm)(4)M')
          apply (subst (asm)(10)M')
          unfolding K
          by (auto simp: K k_def[symmetric] Sk Propa clauses_def)
        have \<open>cdcl\<^sub>W_restart_mset.propagate (?S m) (?S (Suc m))\<close>
          apply (rule cdcl\<^sub>W_restart_mset.propagate_rule[of _ C K])
          subgoal by simp
          subgoal using C_N_U by (simp add: clauses_def)
          subgoal using K_C .
          subgoal using M_C .
          subgoal using undef_nth_Suc[of m] le K by (simp add: k_def[symmetric] Sk)
          subgoal
            using le k_le_M' K unfolding k_def[symmetric] Sk
            by (auto simp: state_eq_def
                state_def Cons_nth_drop_Suc[symmetric])
          done
        then show ?thesis
          by (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.propagate')
      qed
      then show ?thesis
        using IH[OF kept'] by simp
    qed
  qed
qed

end