theory CDCL_Two_Watched_Literals_Simple_Implementation
  imports CDCL_W_Abstract_State
   "$AFP/Refine_Imperative_HOL/IICF/IICF"
begin


subsection \<open>Two-watched literals\<close>

notation image_mset (infixr "`#" 90)


subsubsection \<open>Types and Transitions System\<close>

datatype 'v twl_clause =
  TWL_Clause (watched: 'v) (unwatched: 'v)

fun clause :: "'a twl_clause \<Rightarrow> 'a :: {plus}"  where
"clause (TWL_Clause W UW) = W + UW"

type_synonym 'v working_queue = "('v literal \<times> 'v clause twl_clause) multiset"
type_synonym 'v lit_queue = "'v literal multiset"
type_synonym 'v twl_st =
  "('v, 'v clause) ann_lits \<times> 'v clause twl_clause multiset \<times> 'v clause twl_clause multiset \<times>
    'v clause option \<times> 'v clauses \<times> 'v clauses \<times>  'v working_queue \<times> 'v lit_queue"

fun update_clause where
"update_clause (TWL_Clause W UW) L L' =
  TWL_Clause (add_mset L' (remove1_mset L W)) (add_mset L (remove1_mset L' UW))"

fun update_clauses ::
    "'a multiset twl_clause multiset \<times> 'a multiset twl_clause multiset \<Rightarrow>
    'a multiset twl_clause \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow>
    'a multiset twl_clause multiset \<times> 'a multiset twl_clause multiset" where
"update_clauses (N, U) D L L' =
  (if D \<in># N then (add_mset (update_clause D L L') (remove1_mset D N), U)
       else (N, add_mset (update_clause D L L') (remove1_mset D U)))"

text \<open>We can ensure that there are always \<^emph>\<open>2\<close> watched literals and that there are different.
  (TODO: complete this sentence).\<close>

inductive cdcl_twl_cp :: "'v twl_st \<Rightarrow> 'v twl_st \<Rightarrow> bool" where
pop:
  "cdcl_twl_cp (M, N, U, None, NP, UP, {#}, add_mset L Q)
    (M, N, U, None, NP, UP, {#(L, C)|C \<in># N + U. L \<in># watched C#}, Q)" |
propagate:
  "cdcl_twl_cp (M, N, U, None, NP, UP, add_mset (L, D) WS, Q)
    (Propagated L' (clause D) # M, N, U, None, NP, UP, WS, add_mset (-L') Q)"
  if
    "watched D = {#L, L'#}" and  "undefined_lit M L'" and "\<forall>L \<in># unwatched D. -L \<in> lits_of_l M" |
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
  if "watched D = {#L, L'#}" and \<open>-L \<in> lits_of_l M\<close> and \<open>L' \<notin> lits_of_l M\<close> and
    \<open>K \<in># unwatched D\<close> and \<open>undefined_lit M K \<or> K \<in> lits_of_l M\<close> and
    \<open>(N', U') = update_clauses (N, U) D L K\<close>
  (* TODO remove condition \<open>-L \<in> lits_of_l M\<close>, that is already implied by valid invariant *)

text \<open>We do not care about the pending literals.\<close>
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
| backtrack_single_clause:
  \<open>cdcl_twl_o (M, N, U, Some {#L#}, NP, UP, {#}, {#})
  (Propagated L {#L#} # M1, N, U, None, NP, add_mset {#L#} UP, {#}, {#-L#})\<close>
  if
    \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition M)\<close> and
    \<open>get_level M L = count_decided M\<close> and
    \<open>get_level M K = 1\<close>
| backtrack:
  \<open>cdcl_twl_o (M, N, U, Some D, NP, UP, {#}, {#})
  (Propagated L D # M1, N, add_mset (TWL_Clause {#L, L'#} (D - {#L, L'#})) U, None, NP, UP, {#}, {#-L#})\<close>
  if
    \<open>L \<in># D\<close> and
    \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition M)\<close> and
    \<open>get_level M L = count_decided M\<close> and
    \<open>get_level M L = get_maximum_level M D\<close> and
    \<open>get_maximum_level M (D - {#L#}) \<equiv> i\<close> and
    \<open>get_level M K = i + 1\<close>
    \<open>D \<noteq> {#L#}\<close> and
    \<open>L' \<in># D\<close> and -- \<open>\<^term>\<open>L'\<close> is the new watched literal\<close>
    \<open>get_level M L' = i\<close>


subsubsection \<open>Two-watched literals Invariants\<close>

paragraph \<open>Definitions\<close>

text \<open>The structural invariants states that there are at most two watched elements, that the watched
  literals are distinct, and that there are 2 watched literals if there are at least than two
  different literals in the full clauses.\<close>
primrec struct_wf_twl_cls :: "'v multiset twl_clause \<Rightarrow> bool" where
"struct_wf_twl_cls (TWL_Clause W UW) \<longleftrightarrow>
   size W = 2 \<and> distinct_mset (W + UW)"

fun convert_to_state :: "'v twl_st \<Rightarrow> 'v cdcl\<^sub>W_restart_mset" where
"convert_to_state (M, N, U, C, NP, UP, Q) =
  (M, clause `# N + NP, clause `# U + UP, count_decided M, C)"

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

lemma twl_is_an_exception_add_mset_to_queue: \<open>twl_is_an_exception C (add_mset L Q) WS \<longleftrightarrow>
  (twl_is_an_exception C Q WS \<or> (L \<in># watched C))\<close>
  unfolding twl_is_an_exception_def by auto

lemma twl_is_an_exception_add_mset_to_working_queue:
  \<open>twl_is_an_exception C Q (add_mset (L, D) WS) \<longleftrightarrow> (twl_is_an_exception C Q WS \<or> (C = D))\<close>
  unfolding twl_is_an_exception_def by auto

lemma twl_is_an_exception_empty[simp]: \<open>\<not>twl_is_an_exception C {#} {#}\<close>
  unfolding twl_is_an_exception_def by auto

fun twl_inv :: "('a, 'b) ann_lits \<Rightarrow> 'a clause twl_clause \<Rightarrow> bool" where
"twl_inv M (TWL_Clause W UW) \<longleftrightarrow>
  (\<forall>L L'. W = {#L, L'#} \<longrightarrow> L \<in> lits_of_l M \<longrightarrow> -L' \<in> lits_of_l M \<longrightarrow>
    get_level M L \<le> get_level M L')"

fun twl_lazy_update :: "('a, 'b) ann_lits \<Rightarrow> 'a clause twl_clause \<Rightarrow> bool" where
\<open>twl_lazy_update M (TWL_Clause W UW) \<longleftrightarrow>
  (\<forall>L L'. W = {#L, L'#} \<longrightarrow> -L \<in> lits_of_l M \<longrightarrow> L' \<notin> lits_of_l M \<longrightarrow>
    (\<forall>K \<in># UW. get_level M L \<ge> get_level M K))\<close>

text \<open>If one watched literals has been assigned to false (\<^term>\<open>-L \<in> lits_of_l M\<close>) and the clause
  has not yet been updated (\<^term>\<open>L' \<notin> lits_of_l M\<close> should be removed either by updating \<open>L\<close>,
  propagating \<open>L'\<close>, or marking the conflict), then the literals \<^term>\<open>L\<close> is of maximal level.\<close>
fun watched_literals_false_of_max_level :: "('a, 'b) ann_lits \<Rightarrow> 'a clause twl_clause \<Rightarrow> bool" where
"watched_literals_false_of_max_level M (TWL_Clause W UW) \<longleftrightarrow>
  (\<forall>L L'. W = {#L, L'#} \<longrightarrow> -L \<in> lits_of_l M \<longrightarrow> L' \<notin> lits_of_l M \<longrightarrow>
    get_level M L = count_decided M)"

text \<open>The last condition is needed when \<^term>\<open>WS\<close> is \<^term>\<open>{#}\<close>.\<close>
fun no_duplicate_queued :: "'v twl_st \<Rightarrow> bool"  where
\<open>no_duplicate_queued (M, N, U, D, NP, UP, WS, Q) \<longleftrightarrow>
  (\<forall>C C'. C \<in># WS \<longrightarrow> C' \<in># WS \<longrightarrow> fst C = fst C') \<and>
  (\<forall>C. C \<in># WS \<longrightarrow> add_mset (fst C) Q \<subseteq># uminus `# lit_of `# mset M) \<and>
  Q \<subseteq># uminus `# lit_of `# mset M\<close>

fun distinct_queued :: "'v twl_st \<Rightarrow> bool"  where
\<open>distinct_queued (M, N, U, D, NP, UP, WS, Q) \<longleftrightarrow>
  distinct_mset Q \<and>
  distinct_mset WS\<close>

fun twl_exception_inv :: "'v twl_st \<Rightarrow>  'v clause twl_clause \<Rightarrow> bool"  where
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

fun twl_st_inv :: "'v twl_st \<Rightarrow> bool" where
"twl_st_inv (M, N, U, D, NP, UP, WS, Q) \<longleftrightarrow>
  (\<forall>C \<in># N + U. struct_wf_twl_cls C) \<and>
  (\<forall>C \<in># N + U. D = None \<longrightarrow> \<not>twl_is_an_exception C Q WS \<longrightarrow> (twl_lazy_update M C \<and> twl_inv M C)) \<and>
  (\<forall>C \<in># N + U. D = None \<longrightarrow> watched_literals_false_of_max_level M C) \<and>
  (\<forall>M1 M2 K. M = M2 @ Decided K # M1 \<longrightarrow> ((\<forall>C \<in># N + U. twl_lazy_update M1 C \<and> twl_inv M1 C \<and>
     watched_literals_false_of_max_level M1 C \<and>
     twl_exception_inv (M1, N, U, None, NP, UP, {#}, {#}) C) \<and>
     confl_cands_enqueued (M1, N, U, None, NP, UP, {#}, {#}) \<and>
     propa_cands_enqueued (M1, N, U, None, NP, UP, {#}, {#})))"


paragraph \<open>Properties\<close>

lemma twl_inv_empty_trail:
  shows
    \<open>watched_literals_false_of_max_level [] C\<close> and
    \<open>twl_lazy_update [] C\<close> and
    \<open>twl_inv [] C\<close>
  by (cases C; auto)+

lemma
  assumes \<open>\<And>C. C \<in># N + U \<Longrightarrow> struct_wf_twl_cls C\<close>
  shows
    twl_st_inv_empty_trail: \<open>twl_st_inv ([], N, U, C, NP, UP, WS, Q)\<close>
  by (auto simp: assms twl_inv_empty_trail)

lemma
  shows
    no_duplicate_queued_no_queued: \<open>no_duplicate_queued (M, N, U, D, NP, UP, {#}, {#})\<close> and
    no_distinct_queued_no_queued: \<open>distinct_queued (M, N, U, D, NP, UP, {#}, {#})\<close>
  by auto

lemma twl_st_inv_add_mset_working_queue:
  assumes \<open>D \<in># N + U\<close>
  shows \<open>twl_st_inv (M, N, U, None, NP, UP, WS, Q)
  \<longleftrightarrow> twl_st_inv (M, N, U, None, NP, UP, add_mset (L, D) WS, Q) \<and>
    (\<not> twl_is_an_exception D Q WS \<longrightarrow>twl_lazy_update M D \<and> twl_inv M D)
    \<close>
  using assms by (auto simp: twl_is_an_exception_add_mset_to_working_queue)

lemma twl_st_simps:
"twl_st_inv (M, N, U, D, NP, UP, WS, Q) \<longleftrightarrow>
  (\<forall>C \<in># N + U. struct_wf_twl_cls C \<and>
    (D = None \<longrightarrow> (\<not>twl_is_an_exception C Q WS \<longrightarrow> (twl_lazy_update M C \<and> twl_inv M C)) \<and>
    watched_literals_false_of_max_level M C) \<and>
    (\<forall>M1 M2 K. M = M2 @ Decided K # M1 \<longrightarrow> (twl_lazy_update M1 C \<and> twl_inv M1 C \<and>
      watched_literals_false_of_max_level M1 C \<and>
      twl_exception_inv (M1, N, U, None, NP, UP, {#}, {#}) C))) \<and>
  (\<forall>M1 M2 K. M = M2 @ Decided K # M1 \<longrightarrow>
     confl_cands_enqueued (M1, N, U, None, NP, UP, {#}, {#}) \<and>
     propa_cands_enqueued (M1, N, U, None, NP, UP, {#}, {#}))"
  unfolding twl_st_inv.simps by fast

lemma last_in_set_dropWhile:
  assumes \<open>\<exists>L \<in> set (xs @ [x]). \<not>P L\<close>
  shows \<open>x \<in> set (dropWhile P (xs @ [x]))\<close>
  using assms by (induction xs) auto


lemma propa_cands_enqueued_unit_clause:
  \<open>propa_cands_enqueued (M, N, U, C, add_mset L NP, UP, WS, Q) \<longleftrightarrow>
    propa_cands_enqueued (M, N, U, C, {#}, {#}, WS, Q)\<close>
  \<open>propa_cands_enqueued (M, N, U, C, NP, add_mset L UP, WS, Q) \<longleftrightarrow>
    propa_cands_enqueued (M, N, U, C, {#}, {#}, WS, Q)\<close>
  by (cases C; auto)+

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
  have lev_M_M1: \<open>get_level M L = get_level M1 L\<close> if  \<open>L \<in> lits_of_l M1\<close> for L
  proof -
    have LM: \<open>L \<in> lits_of_l M\<close>
      using that unfolding M by auto
    have \<open>atm_of L \<notin> atm_of ` lits_of_l M'\<close>
      by (rule cdcl\<^sub>W_restart_mset.no_dup_append_in_atm_notin)
        (use that n_d in \<open>auto simp: M M'\<close>)
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
      using lev_M_M1[of L] lev_M_M1[of \<open>-L'\<close>] L uL' by fastforce
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
          unfolding MM' by (force simp: filter_empty_conv) }
      ultimately show False
        using lev_M_M1[of "-L"] uL count_decided_ge_get_level[of "-L" M1] by auto
    qed

    show \<open>\<forall>K\<in>#UW. get_level M1 K \<le> get_level M1 L\<close>
    proof clarify
      fix K''
      assume \<open>K'' \<in># UW\<close>
      then have lev_K'_L: \<open>get_level M K'' \<le> get_level M L\<close>
        using lazy W uL L' L'M unfolding C MM' by auto
      have \<open>get_level M K'' = get_level M1 K''\<close>
      proof (rule ccontr, cases \<open>atm_of K'' \<in> atm_of ` lits_of_l M'\<close>)
        case False
        moreover assume \<open>get_level M K'' \<noteq> get_level M1 K''\<close>
        ultimately show False unfolding MM' by auto
      next
        case True
        assume K'': \<open>get_level M K'' \<noteq> get_level M1 K''\<close>
        have \<open>get_level M' K'' = 0\<close>
        proof -
          have a1: "get_level M' K'' + count_decided M1 \<le> get_level M1 L"
            using lev_K'_L unfolding lev_L_M1 unfolding MM' get_rev_level_skip_end[OF True] .
          then have "count_decided M1 \<le> get_level M1 L"
            by linarith
          then have "get_level M1 L = count_decided M1"
            using count_decided_ge_get_level le_antisym by blast
          then show ?thesis
            using a1 by linarith
        qed
        moreover have \<open>Decided K \<in>set (dropWhile (\<lambda>S. atm_of (lit_of S) \<noteq> atm_of K'') M')\<close>
          unfolding M' append_assoc[symmetric] by (rule last_in_set_dropWhile)
            (use True in \<open>auto simp: lits_of_def M' MM'\<close>)
        ultimately show False
          by (auto simp: M' filter_empty_conv)
      qed
      then show \<open>get_level M1 K'' \<le> get_level M1 L\<close>
        using lev_M_M1[OF uL] lev_K'_L by auto
    qed
  qed
qed

declare twl_st_inv.simps[simp del]

fun valid_annotation :: "'v twl_st \<Rightarrow> bool" where
"valid_annotation (M, N, U, C, NP, UP, WS, Q) \<longleftrightarrow>
  (\<forall>(L, C) \<in># WS. L \<in># watched C \<and> C \<in># N + U \<and> -L \<in> lits_of_l M \<and>
     get_level M L = count_decided M) \<and>
  (\<forall>L \<in># Q. -L \<in> lits_of_l M \<and> get_level M L = count_decided M)"

lemma clauses_def: \<open>cdcl\<^sub>W_restart_mset.clauses (M, N, U, k, C) = N + U\<close>
  by (subst cdcl\<^sub>W_restart_mset.clauses_def) (simp add: cdcl\<^sub>W_restart_mset_state)

(* TODO subset_mset.add_diff_assoc should be [simp]\<dots> as Nat.add_diff_assoc*)

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
  unfolding twl_inv.simps
  apply (intro conjI allI impI)
  using assms(2) apply (auto simp add: W add_mset_eq_add_mset; fail)[]
  done

lemma watched_literals_false_of_max_level_Propagated:
  assumes
    W: \<open>W = {#L, L'#}\<close> and
    \<open>-L \<notin> lits_of_l M\<close>
  shows
    \<open>watched_literals_false_of_max_level (Propagated L D # M) (TWL_Clause W UW)\<close>
  using assms(2) by (simp add: W add_mset_eq_add_mset)

(* TODO rename *)
lemma lazy_update_propagate: \<open>- L' \<notin># watched C \<Longrightarrow> watched_literals_false_of_max_level M C\<Longrightarrow>
  twl_lazy_update (Propagated L' D # M) C\<close>
  by (cases C) (auto simp: add_mset_eq_add_mset count_decided_ge_get_level)
(* END TODO *)

(* TODO Move *)
lemma get_level_append_cons_le_count_decided_notin:
  \<open>get_level (M' @ Decided K # M) L \<le> count_decided M \<Longrightarrow>
  atm_of L \<notin> atm_of ` lits_of_l (M' @ [Decided K])\<close>
  by (auto simp add: dropWhile_append3)

lemma pair_in_image_Pair:
  \<open>(La, C) \<in> Pair L ` D \<longleftrightarrow> La = L \<and> C \<in> D\<close>
  by auto
lemma twl_cp_twl_st_exception_inv:
  assumes
    cdcl: "cdcl_twl_cp S T" and
    twl: "twl_st_inv S" and
    twl_excep: \<open>twl_st_exception_inv S\<close> and
    valid: "valid_annotation S" and
    inv: "cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (convert_to_state S)" and
    no_taut: "\<forall>D \<in># init_clss (convert_to_state S). \<not> tautology D" and
    dist: \<open>distinct_mset (cdcl\<^sub>W_restart_mset.clauses (convert_to_state S))\<close> and
    no_dup: \<open>no_duplicate_queued S\<close> and
    dist_q: \<open>distinct_queued S\<close>
  shows "twl_st_exception_inv T"
  using cdcl twl twl_excep valid inv no_taut dist no_dup
proof (induction rule: cdcl_twl_cp.induct)
  case (pop M N U NP UP L Q) note inv = this(2)
  then show ?case unfolding twl_st_inv.simps twl_is_an_exception_def
    by (fastforce simp add: pair_in_image_Pair image_constant_conv uminus_lit_swap
        twl_exception_inv.simps)
next
  case (propagate D L L' M N U NP UP WS Q) note watched = this(1) and twl = this(4) and
    twl_excep = this(5) and valid = this(6) and inv = this(7) and no_taut = this(8) and
    no_dup = this(10)
  have [simp]: \<open>- L' \<notin> lits_of_l M\<close>
    using Decided_Propagated_in_iff_in_lits_of_l propagate.hyps(2) by blast
  have "D \<in># N + U"
    using valid by auto
  then have wf_D: \<open>struct_wf_twl_cls D\<close>
    using twl by (simp add: twl_st_inv.simps)
  have "\<forall>s\<in>#clause `# U. \<not> tautology s"
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def by (simp_all add: cdcl\<^sub>W_restart_mset_state)
  moreover have "D \<in># N + U"
    using valid by auto
  ultimately have taut: "\<not>tautology (clause D)"
    using watched no_taut by (auto simp: cdcl\<^sub>W_restart_mset_state)
  then have [simp]: \<open>L \<noteq> -L'\<close>
    using watched by (cases D) (auto simp: tautology_add_mset)
  have [simp]: \<open>L \<noteq> L'\<close>
    using wf_D watched by (cases D) auto
  have [simp]: \<open>- L \<in> lits_of_l M\<close>
    using valid by auto
  have [simp]: \<open>- La \<noteq> L'\<close> if \<open>La\<in>#unwatched D\<close> for La
    using wf_D watched that taut by (cases D) (auto dest!: multi_member_split simp: tautology_add_mset)
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
next
  case (conflict D L L' M N U NP UP WS Q) note twl = this(5)
  show ?case
    by (auto simp: twl_st_inv.simps twl_exception_inv.simps)
next
  case (delete_from_working D L L' M N U NP UP WS Q) note watched = this(1) and L' = this(2) and
  twl = this(3) and twl_excep = this(4) and valid = this(4) and inv = this(6) and tauto = this(7)
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
      have \<open>no_dup M\<close>
        using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: trail.simps)
      then have False if \<open> - L' \<in> lits_of_l M\<close> \<open>L' \<in> lits_of_l M\<close>
        using that consistent_interp_def distinct_consistent_interp by blast
      then have CD: False if \<open>C = D\<close>
        using J J' watched_C watched L' by (auto simp: add_mset_eq_add_mset that) }
    ultimately show \<open>- K \<in> lits_of_l M\<close>
      by blast
  qed
next
  case (update_clause D L L' M K N' U' N U NP UP WS Q) note watched = this(1) and uL = this(2) and
    L' = this(3) and K = this(4) and undef = this(5) and N'U' = this(6) and twl = this(7) and
    twl_excep = this(8) and valid = this(9) and inv = this(10) and tauto = this(11) and
    dist = this(12) and no_dup = this(13)
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
    using C N'U' that by (auto split: if_splits dest: in_diffD)
  have n_d: \<open>no_dup M\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: trail.simps)
  then have uK_M: \<open>- K \<notin> lits_of_l M\<close>
    using undef Decided_Propagated_in_iff_in_lits_of_l consistent_interp_def
      distinct_consistent_interp by blast
  have add_remove_WD: \<open>add_mset K (remove1_mset L WD) \<noteq> WD\<close>
    using uK_M uL by (auto simp: add_mset_remove_trivial_iff trivial_add_mset_remove_iff)

  have \<open>D \<notin># N' + U'\<close>
  proof
    assume \<open>D \<in># N' + U'\<close>
    then have \<open>D \<in># N + U\<close>
      using N'U' D uK_M uL D_N_U by (auto simp: add_mset_remove_trivial_iff split: if_splits)
    have \<open>count (N + U) D \<ge> 2\<close>
      using N'U' \<open>D \<in># N' + U'\<close> D
      by (auto simp del: count_greater_zero_iff simp: count_greater_zero_iff[symmetric]
          add_remove_WD split: if_splits)
    then have \<open>count (clause `# (N + U)) (clause D) \<ge> 2\<close>
      using count_image_mset_ge_count[of \<open>N + U\<close> D clause] by linarith
    moreover have \<open>distinct_mset (clause `# (N + U))\<close>
      using dist by (auto simp: clauses_def distinct_mset_add inter_mset_empty_distrib_left
          inter_mset_empty_distrib_right)
    ultimately show False
      unfolding distinct_mset_count_less_1 by (metis Suc_1 not_less_eq_eq)
  qed
  then have CD: \<open>C \<noteq> D\<close> if C: \<open>C \<in># N'+U'\<close> for C
    using C by auto

  have L_M: \<open>L \<notin> lits_of_l M\<close>
    using n_d uL by (fastforce dest!: distinct_consistent_interp
        simp: consistent_interp_def lits_of_def uminus_lit_swap)
  have w_max_D: \<open>watched_literals_false_of_max_level M D\<close>
    using D_N_U twl by (auto simp: twl_st_inv.simps)
  have lev_L': \<open>get_level M L' = count_decided M\<close> if \<open>- L' \<in> lits_of_l M \<close>
    using L_M w_max_D D watched L' uL that by (auto simp: add_mset_eq_add_mset)

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
    then have \<open>- K'' \<in> lits_of_l M\<close> if \<open>C \<noteq> ?D\<close>
      using twl_excep that *[OF _ C] CD by (simp add: uminus_lit_swap twl_exception_inv.simps)

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
qed

lemma twl_cp_twl_inv:
  assumes
    cdcl: "cdcl_twl_cp S T" and
    twl: "twl_st_inv S" and
    valid: "valid_annotation S" and
    inv: "cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (convert_to_state S)" and
    no_taut: "\<forall>D \<in># init_clss (convert_to_state S). \<not> tautology D" and
    dist: \<open>distinct_mset (cdcl\<^sub>W_restart_mset.clauses (convert_to_state S))\<close> and
    twl_excep: \<open>twl_st_exception_inv S\<close> and
    no_dup: \<open>no_duplicate_queued S\<close>
  shows "twl_st_inv T"
  using cdcl twl valid inv no_taut dist twl_excep no_dup
proof (induction rule: cdcl_twl_cp.induct)
  case (pop M N U NP UP L Q) note inv = this(1)
  then show ?case unfolding twl_st_inv.simps twl_is_an_exception_def
    by (fastforce simp add: pair_in_image_Pair)
next
  case (propagate D L L' M N U NP UP WS Q) note watched = this(1) and twl = this(4) and valid = this(5)
    and inv = this(6) and no_taut = this(7)
  have [simp]: \<open>- L' \<notin> lits_of_l M\<close>
    using Decided_Propagated_in_iff_in_lits_of_l propagate.hyps(2) by blast
  have "D \<in># N + U"
    using valid by auto
  then have wf_D: \<open>struct_wf_twl_cls D\<close>
    using twl by (simp add: twl_st_inv.simps)
  have "\<forall>s\<in>#clause `# U. \<not> tautology s"
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def by (simp_all add: cdcl\<^sub>W_restart_mset_state)
  moreover have "D \<in># N + U"
    using valid by auto
  ultimately have taut: "\<not>tautology (clause D)"
    using watched no_taut by (auto simp: cdcl\<^sub>W_restart_mset_state)
  then have [simp]: \<open>-L \<noteq> L'\<close>
    using watched by (cases D) (auto simp: tautology_add_mset)
  have [simp]: \<open>L \<noteq> L'\<close>
    using wf_D watched by (cases D) auto
  have [simp]: \<open>- L \<in> lits_of_l M\<close>
    using valid by auto
  have [simp]: \<open>- La \<noteq> L'\<close> if \<open>La\<in>#unwatched D\<close> for La
    using wf_D watched that taut by (cases D) (auto dest!: multi_member_split simp: tautology_add_mset)
  show ?case unfolding twl_st_simps Ball_def
  proof (intro allI conjI impI)
    fix C
    assume C: \<open>C \<in># N + U\<close>
    show \<open>struct_wf_twl_cls C\<close>
      using twl C by (auto simp: twl_st_inv.simps)[]
    have \<open>watched_literals_false_of_max_level M C\<close>
      using twl C by (auto simp: twl_st_inv.simps)
    then show \<open>watched_literals_false_of_max_level (Propagated L' (clause D) # M) C\<close>
      by (cases C) auto

    assume excep: \<open>\<not>twl_is_an_exception C (add_mset (- L') Q) WS\<close>
    show \<open>twl_lazy_update (Propagated L' (clause D) # M) C\<close>
      apply (rule lazy_update_propagate)
      using excep apply (simp add: twl_is_an_exception_add_mset_to_queue; fail)
      using twl C by (auto simp add: twl_st_inv.simps)[]
    have \<open>\<not> twl_is_an_exception C Q (add_mset (L, D) WS)\<close> if \<open>C \<noteq> D\<close>
      using excep that by (auto simp add: twl_is_an_exception_def)
    then have \<open>twl_inv M C\<close> if \<open>C \<noteq> D\<close>
      using twl that C by (auto simp: twl_st_inv.simps)
    then have twl_C: \<open>twl_inv (Propagated L' (clause D) # M) C\<close> if \<open>C \<noteq> D\<close>
      apply (cases C)
      apply (simp only:)
      unfolding twl_inv.simps Ball_def
      apply (intro allI conjI impI)
      by simp (smt Decided_Propagated_in_iff_in_lits_of_l \<open>watched_literals_false_of_max_level M C\<close>
          add_mset_commute atm_of_eq_atm_of count_decided_ge_get_level propagate.hyps(2) that
          watched_literals_false_of_max_level.simps)
    have D: \<open>D \<in># N + U\<close> and \<open>L \<in># watched D\<close>
      using valid by auto
    have lev_L: \<open>get_level M L = count_decided M\<close>
      using valid by auto

    have twl_D: \<open>twl_inv (Propagated L' (clause D) # M) D\<close>
      by (cases D) (use watched in \<open>auto simp: add_mset_eq_add_mset lev_L\<close>)

    show \<open>twl_inv (Propagated L' (clause D) # M) C\<close>
      using twl_C twl_D by blast
  next
    fix C
    assume C: \<open>C \<in># N + U\<close>

    fix M1 M2 :: \<open>('a, 'a clause) ann_lits\<close> and K
    assume \<open>Propagated L' (clause D) # M = M2 @ Decided K # M1\<close>
    then have M: \<open>M = tl M2 @ Decided K # M1\<close>
      by (meson cdcl\<^sub>W_restart_mset.propagated_cons_eq_append_decide_cons)
    then show \<open>twl_lazy_update M1 C\<close> and \<open>twl_inv M1 C\<close> and  \<open>watched_literals_false_of_max_level M1 C\<close>
      and \<open>twl_exception_inv (M1, N, U, None, NP, UP, {#}, {#}) C\<close>
      using C twl by (auto simp add: twl_st_inv.simps)
  next
    fix M1 M2 :: \<open>('a, 'a clause) ann_lits\<close> and K
    assume \<open>Propagated L' (clause D) # M = M2 @ Decided K # M1\<close>
    then have M: \<open>M = tl M2 @ Decided K # M1\<close>
      by (meson cdcl\<^sub>W_restart_mset.propagated_cons_eq_append_decide_cons)
    then show \<open>confl_cands_enqueued (M1, N, U, None, NP, UP, {#}, {#})\<close> and
      \<open>propa_cands_enqueued (M1, N, U, None, NP, UP, {#}, {#})\<close>
      using twl by (auto simp add: twl_st_inv.simps)
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
    then have [simp]: \<open> - L' \<notin> lits_of_l M\<close>
      using L' consistent_interp_def distinct_consistent_interp by blast
    have twl_D: \<open>twl_lazy_update M D\<close>
      by (cases D) (use watched L' in \<open>auto simp: add_mset_eq_add_mset\<close>)
    have twl_C: \<open>twl_lazy_update M C\<close> if \<open>C \<noteq> D\<close>
      using twl C excep that by (auto simp add: twl_st_inv.simps
          twl_is_an_exception_add_mset_to_working_queue)

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
  next
    fix C
    assume C: \<open>C \<in># N + U\<close>

    fix M1 M2 :: \<open>('a, 'a clause) ann_lits\<close> and K
    assume \<open>M = M2 @ Decided K # M1\<close>
    then show \<open>twl_lazy_update M1 C\<close> and \<open>twl_inv M1 C\<close> \<open>watched_literals_false_of_max_level M1 C\<close> and
      \<open>twl_exception_inv (M1, N, U, None, NP, UP, {#}, {#}) C\<close>
      using C twl by (auto simp add: twl_st_inv.simps)
  next
    fix M1 M2 :: \<open>('a, 'a clause) ann_lits\<close> and K
    assume \<open>M = M2 @ Decided K # M1\<close>
    then show \<open>confl_cands_enqueued (M1, N, U, None, NP, UP, {#}, {#})\<close> and
      \<open>propa_cands_enqueued (M1, N, U, None, NP, UP, {#}, {#})\<close>
      using twl by (auto simp add: twl_st_inv.simps)
  qed
next
  case (update_clause D L L' M K N' U' N U NP UP WS Q) note watched = this(1) and uL = this(2) and
    L' = this(3) and K = this(4) and undef = this(5) and N'U' = this(6) and twl = this(7) and
    valid = this(8) and inv = this(9) and tauto = this(10) and dist = this(11) and
    twl_excep = this(12) and no_dup = this(13)
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
    using C N'U' that by (auto split: if_splits dest: in_diffD)
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
  have \<open>D \<notin># N' + U'\<close>
  proof
    assume \<open>D \<in># N' + U'\<close>
    then have \<open>D \<in># N + U\<close>
      using N'U' D uK_M uL D_N_U by (auto simp: add_mset_remove_trivial_iff split: if_splits)
    have \<open>count (N + U) D \<ge> 2\<close>
      using N'U' \<open>D \<in># N' + U'\<close> D
      by (auto simp del: count_greater_zero_iff simp: count_greater_zero_iff[symmetric]
          add_remove_WD split: if_splits)
    then have \<open>count (clause `# (N + U)) (clause D) \<ge> 2\<close>
      using count_image_mset_ge_count[of \<open>N + U\<close> D clause] by linarith
    moreover have \<open>distinct_mset (clause `# (N + U))\<close>
      using dist by (auto simp: clauses_def distinct_mset_add inter_mset_empty_distrib_left
          inter_mset_empty_distrib_right)
    ultimately show False
      unfolding distinct_mset_count_less_1 by (metis Suc_1 not_less_eq_eq)
  qed
  then have CD: \<open>C \<noteq> D\<close> if C: \<open>C \<in># N'+U'\<close> for C
    using C by auto

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
      using twl C that N'U' by  (auto simp: twl_st_inv.simps split: if_splits dest: in_diffD)
    show \<open>struct_wf_twl_cls C\<close>
      using struct_D' struct_C by blast

    have \<open>watched_literals_false_of_max_level M C\<close> if \<open>C \<noteq> ?D\<close>
      using twl C that N'U' by (auto simp: twl_st_inv.simps split: if_splits dest: in_diffD)
    moreover have \<open>watched_literals_false_of_max_level M ?D\<close>
        (* TODO tune proof *)
        using w_max_D D watched L' uK_M apply (auto simp: add_mset_eq_add_mset)
        using consistent_interp_def distinct_consistent_interp n_d uL by blast
    ultimately show \<open>watched_literals_false_of_max_level M C\<close>
      by blast

    assume excep: \<open>\<not>twl_is_an_exception C Q WS\<close>
    have H: \<open>\<And>C. C \<in># N+U \<Longrightarrow> \<not> twl_is_an_exception C Q WS \<Longrightarrow> C \<noteq> D \<Longrightarrow> twl_lazy_update M C \<and> twl_inv M C \<close>
      using twl by (auto simp add: twl_st_inv.simps twl_is_an_exception_add_mset_to_working_queue)[]
    have excep_WS: \<open>\<not> twl_is_an_exception C Q WS\<close>
      using excep CD C by (force simp: twl_is_an_exception_def)
    have \<open>twl_lazy_update M C\<close> if \<open>C \<noteq> ?D\<close>
      using H[of C] that excep_WS * CD C
      by (auto simp add: twl_st_inv.simps)[]
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
    then have twl_C: \<open>twl_inv M C\<close> if \<open>C \<noteq> ?D\<close>
      using twl that C * CD by (auto simp: twl_st_inv.simps)
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

    then have twl_D: \<open>twl_inv M ?D\<close> if \<open>L' \<notin># Q\<close>
      apply (use watched uK_M uL D that in
          \<open>auto simp: add_mset_eq_add_mset lev_L lev_L' count_decided_ge_get_level
          in_remove1_mset H\<close>)
      done

    have twl_D': \<open>twl_inv M ?D\<close> if \<open>L' \<in># Q\<close> and \<open>C = ?D\<close>
      using excep that watched
      by (cases D) (auto simp: twl_is_an_exception_def)

    show \<open>twl_inv M C\<close>
      using twl_C twl_D twl_D' by blast
  next
    fix C
    assume C: \<open>C \<in># N' + U'\<close>

    fix M1 M2 :: \<open>('a, 'a clause) ann_lits\<close> and K'
    assume M: \<open>M = M2 @ Decided K' # M1\<close>

    have H: False if \<open> - L' \<in> lits_of_l M1\<close>
    proof -
      have atm: \<open>atm_of (-L') \<notin> atm_of ` lits_of_l (M2 @ [Decided K'])\<close>
        using that n_d by (metis M append.simps(1) append.simps(2) append_assoc
            cdcl\<^sub>W_restart_mset.no_dup_append_in_atm_notin)
      have uL_M: \<open>-L' \<in> lits_of_l M\<close>
        using that M by auto
      show False
        using lev_L'[OF uL_M] atm count_decided_ge_get_level[of L' M1]
        by (auto simp: M split: if_splits)
    qed
    have \<open>twl_exception_inv (M1, N, U, None, NP, UP, {#}, {#}) C\<close> if \<open>C \<noteq> ?D\<close>
      using * C CD twl that M by (auto simp add: twl_st_inv.simps)
    then have \<open>twl_exception_inv (M1, N', U', None, NP, UP, {#}, {#}) C\<close> if \<open>C \<noteq> ?D\<close>
      using N'U' that by (auto simp add: twl_st_inv.simps twl_exception_inv.simps)
    moreover have \<open>twl_lazy_update M1 C\<close> \<open>twl_inv M1 C\<close> \<open>watched_literals_false_of_max_level M1 C\<close>
      if \<open>C \<noteq> ?D\<close>
      using * C CD twl that M N'U' by (auto simp add: twl_st_inv.simps twl_exception_inv.simps)
    moreover have \<open>twl_lazy_update M1 ?D\<close> \<open>twl_inv M1 ?D\<close> \<open>watched_literals_false_of_max_level M1 ?D\<close>
      and \<open>twl_exception_inv (M1, N', U', None, NP, UP, {#}, {#}) ?D\<close>
      using D watched uK_M by (auto simp: M add_mset_eq_add_mset twl_exception_inv.simps dest!: H)
    ultimately show \<open>twl_lazy_update M1 C\<close> \<open>twl_inv M1 C\<close> \<open>watched_literals_false_of_max_level M1 C\<close>
      \<open>twl_exception_inv (M1, N', U', None, NP, UP, {#}, {#}) C\<close>
      by blast+
  next
    have [dest!]: \<open>C \<in># N' \<Longrightarrow> C \<in># N \<or> C = ?D\<close> \<open>C \<in># U' \<Longrightarrow> C \<in># U \<or> C = ?D\<close> for C
      using N'U' by (auto split: if_splits dest: in_diffD)
    fix M1 M2 :: \<open>('a, 'a clause) ann_lits\<close> and K
    assume M: \<open>M = M2 @ Decided K # M1\<close>
    then have \<open>confl_cands_enqueued (M1, N, U, None, NP, UP, {#}, {#})\<close> and
      \<open>propa_cands_enqueued (M1, N, U, None, NP, UP, {#}, {#})\<close>
      using twl by (auto simp add: twl_st_inv.simps)
    moreover have \<open>\<not>M1 \<Turnstile>as CNot (clause ?D)\<close>
      using K uK_M unfolding true_annots_true_cls_def_iff_negation_in_model cls_D_D M
      by (cases D) auto
    moreover {
      have lev_L_M: \<open>get_level M L = count_decided M\<close> and uL_M: \<open>-L \<in> lits_of_l M\<close>
        using valid by auto
      have \<open>-L \<notin> lits_of_l M1\<close>
      proof (rule ccontr)
        assume \<open>\<not> ?thesis\<close>
        then have \<open>atm_of L \<notin> atm_of ` lits_of_l (M2 @ [Decided K])\<close>
          using uL_M n_d unfolding M
          by (auto simp: lits_of_def uminus_lit_swap dest: mk_disjoint_insert)
        then show False
          using lev_L_M count_decided_ge_get_level[of L M1]
          by (auto simp: lits_of_def uminus_lit_swap M)
      qed
      then have \<open>\<not>M1 \<Turnstile>as CNot (remove1_mset K (clause ?D))\<close> for K
        using K uK_M watched unfolding true_annots_true_cls_def_iff_negation_in_model cls_D_D M
        (* TODO tune proofs *)
        apply auto
        by (metis D Decided_Propagated_in_iff_in_lits_of_l L L_M clause.simps in_remove1_mset_neq
            twl_clause.sel uL undef union_iff) }
    ultimately show \<open>confl_cands_enqueued (M1, N', U', None, NP, UP, {#}, {#})\<close> and
      \<open>propa_cands_enqueued (M1, N', U', None, NP, UP, {#}, {#})\<close>
      by (auto simp add: twl_st_inv.simps split: if_splits)
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
    by (auto simp: image_Un image_image  subset_mset.less_imp_le
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
    inv: "cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (convert_to_state S)" and
    c_dist: \<open>distinct_mset (cdcl\<^sub>W_restart_mset.clauses (convert_to_state S))\<close> and
    no_taut: "\<forall>D \<in># init_clss (convert_to_state S). \<not> tautology D" and
    no_dup: \<open>no_duplicate_queued S\<close> and
    dist: \<open>distinct_queued S\<close>
  shows "distinct_queued T"
  using cdcl twl valid inv c_dist no_taut no_dup dist
proof (induction rule: cdcl_twl_cp.induct)
  case (pop M N U NP UP L Q) note c_dist = this(4) and dist = this(7)
  have dist_N_U: \<open>distinct_mset (N + U)\<close>
    using c_dist
    by (metis clauses_def convert_to_state.simps distinct_image_mset_clause distinct_mset_add
        image_mset_union union_assoc union_lcomm)
  show ?case
    using distinct_mset_filter[of \<open>N+U\<close> \<open>\<lambda>C. L \<in># watched C\<close>] dist_N_U dist
    by (auto simp: distinct_mset_Pair simp del: image_mset_union)
next
  case (propagate D L L' M N U NP UP WS Q) note watched = this(1) and undef = this(2) and
    twl = this(4) and valid = this(5)  and inv = this(6) and no_taut = this(7) and no_dup = this(9)
    and dist = this(10)
  have \<open>L' \<notin> lits_of_l M\<close>
    using Decided_Propagated_in_iff_in_lits_of_l propagate.hyps(2) by auto
  then have \<open>-L' \<notin># Q\<close>
    using no_dup by (fastforce simp: lits_of_def dest!: mset_subset_eqD)
  then show ?case
    using dist by auto
next
  case (conflict D L L' M N U NP UP WS Q) note dist = this(10)
  then show ?case
    by auto
next
  case (delete_from_working D L L' M N U NP UP WS Q) note dist = this(9)
  show ?case using dist by auto
next
  case (update_clause D L L' M K N' U' N U NP UP WS Q) note watched = this(1) and uL = this(2) and
    L' = this(3) and K = this(4) and undef = this(5) and N'U' = this(6) and twl = this(7) and
    valid = this(8) and inv = this(9) and tauto = this(10) and no_dup = this(12) and dist = this(13)
  show ?case
    using dist by auto
qed

lemma twl_cp_valid:
  assumes
    cdcl: "cdcl_twl_cp S T" and
    twl: "twl_st_inv S" and
    valid: "valid_annotation S" and
    inv: "cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (convert_to_state S)" and
    no_taut: "\<forall>D \<in># init_clss (convert_to_state S). \<not> tautology D" and
    no_dup: \<open>no_duplicate_queued S\<close> and
    dist: \<open>distinct_queued S\<close>
  shows "valid_annotation T"
  using cdcl twl valid inv no_taut no_dup dist
proof (induction rule: cdcl_twl_cp.induct)
  case (pop M N U NP UP L Q) note valid = this(2)
  then show ?case
    by (auto simp del: filter_union_mset)
next
  case (propagate D L L' M N U NP UP WS Q) note watched = this(1) and twl = this(4) and valid = this(5)
    and inv = this(6) and no_taut = this(7)
  show ?case
    using valid by (auto dest: mset_subset_eq_insertD)
next
  case (conflict D L L' M N U NP UP WS Q) note valid = this(5)
  then show ?case
    by auto
next
  case (delete_from_working D L L' M N U NP UP WS Q) note watched = this(1) and L' = this(2) and
  twl = this(3) and valid = this(4) and inv = this(5) and tauto = this(6)
  show ?case unfolding twl_st_simps Ball_def
    using valid by (auto dest: mset_subset_eq_insertD)
next
  case (update_clause D L L' M K N' U' N U NP UP WS Q) note watched = this(1) and uL = this(2) and
    L' = this(3) and K = this(4) and undef = this(5) and N'U' = this(6) and twl = this(7) and
    valid = this(8) and inv = this(9) and tauto = this(10) and no_dup = this(11) and dist = this(12)
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
    fix KC :: \<open>'a literal \<times> 'a clause twl_clause\<close>
    assume LC_WS: \<open>KC \<in># WS\<close>
    obtain K'' C where LC: \<open>KC = (K'', C)\<close> by (cases KC)
    have [simp]: \<open>(K'', D) \<notin># WS\<close>
      using no_dup dist by auto
    then have \<open>K'' \<in># watched C\<close>
      using LC_WS valid LC by auto
    show \<open>case KC of (L, C) \<Rightarrow> L \<in># watched C \<and> C \<in># N' + U' \<and> - L \<in> lits_of_l M \<and>
        get_level M L = count_decided M\<close>
      by (cases \<open>C = D\<close>) (use valid LC LC_WS N'U' in \<open>auto simp: in_remove1_mset_neq split: if_splits\<close>)
  qed
qed


lemma twl_cp_propa_cands_enqueued:
  assumes
    cdcl: "cdcl_twl_cp S T" and
    twl: "twl_st_inv S" and
    valid: "valid_annotation S" and
    inv: "cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (convert_to_state S)" and
    no_taut: "\<forall>D \<in># init_clss (convert_to_state S). \<not> tautology D" and
    dist: \<open>distinct_mset (cdcl\<^sub>W_restart_mset.clauses (convert_to_state S))\<close> and
    twl_excep: \<open>twl_st_exception_inv S\<close> and
    no_dup: \<open>no_duplicate_queued S\<close> and
    cands: \<open>propa_cands_enqueued S\<close>
  shows "propa_cands_enqueued T"
  using cdcl twl valid inv no_taut dist twl_excep no_dup cands
proof (induction rule: cdcl_twl_cp.induct)
  case (pop M N U NP UP L Q) note inv = this(1) and valid = this(2) and cands = this(8)
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
  case (propagate D L L' M N U NP UP WS Q) note watched = this(1) and twl = this(4) and
    valid = this(5) and inv = this(6) and no_taut = this(7) and dist = this(8) and excep = this(9)
    and no_dup = this(10) and cands = this(11)
  have [simp]: \<open>- L' \<notin> lits_of_l M\<close>
    using Decided_Propagated_in_iff_in_lits_of_l propagate.hyps(2) by blast
  have "D \<in># N + U"
    using valid by auto
  then have wf_D: \<open>struct_wf_twl_cls D\<close>
    using twl by (simp add: twl_st_inv.simps)
  have "\<forall>s\<in>#clause `# U. \<not> tautology s"
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def by (simp_all add: cdcl\<^sub>W_restart_mset_state)
  moreover have "D \<in># N + U"
    using valid by auto
  ultimately have taut: "\<not>tautology (clause D)"
    using watched no_taut by (auto simp: cdcl\<^sub>W_restart_mset_state)
  then have [simp]: \<open>-L \<noteq> L'\<close>
    using watched by (cases D) (auto simp: tautology_add_mset)
  have [simp]: \<open>L \<noteq> L'\<close>
    using wf_D watched by (cases D) auto
  have [simp]: \<open>- L \<in> lits_of_l M\<close>
    using valid by auto
  have [simp]: \<open>- La \<noteq> L'\<close> if \<open>La\<in>#unwatched D\<close> for La
    using wf_D watched that taut by (cases D) (auto dest!: multi_member_split simp: tautology_add_mset)
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
      (no_L') \<open>M \<Turnstile>as CNot (remove1_mset K (clause C))\<close>
      | (L') \<open>-L' \<in># remove1_mset K (clause C)\<close>
      using L'_M_C
      by (metis \<open>- L' \<notin> lits_of_l M\<close> ann_lit.sel(2) in_CNot_implies_uminus(2) insertE list.simps(15)
          lits_of_insert true_annots_CNot_lit_of_notin_skip)
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
          by (metis that L'_M_C \<open>- L' \<notin> lits_of_l M\<close> ann_lit.sel(2) clause.simps
              in_remove1_mset_neq insert_iff list.simps(15) lits_of_insert
              true_annots_true_cls_def_iff_negation_in_model twl_clause.exhaust_sel uminus_not_id'
              union_iff)
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
          using twl_cp_twl_inv[OF _ twl valid inv no_taut dist excep no_dup]
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
        have \<open>-a \<in> lits_of_l M \<or> -b \<in> lits_of_l M\<close>
          using L'_M_C C_W_UW W \<open>\<forall>L'a. L'a \<in># watched C \<longrightarrow> L'a \<noteq> - L' \<and> L'a \<notin># Q\<close>
          apply (cases \<open>K = a\<close>) by fastforce+

        have \<open>no_dup M\<close>
          using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (simp add: trail.simps)
        then have [dest]: False if \<open>a \<in> lits_of_l M\<close> and \<open>-a \<in> lits_of_l M\<close> for a
          using consistent_interp_def distinct_consistent_interp that(1) that(2) by blast
        have uab: \<open>a \<notin> lits_of_l M\<close> if \<open>-b \<in> lits_of_l M\<close>
          (* TODO tune proof *)
          using L'_M_C C_W_UW W that undef_K_M
          apply (cases \<open>K = a\<close>) apply (fastforce simp: Decided_Propagated_in_iff_in_lits_of_l)
          using \<open>- L' \<notin> lits_of_l M\<close> apply auto
          using \<open>- L' \<notin> lits_of_l M\<close> by auto
        have uba: \<open>b \<notin> lits_of_l M\<close> if \<open>-a \<in> lits_of_l M\<close>
          (* TODO tune proof *)
          using L'_M_C C_W_UW W that undef_K_M
          apply (cases \<open>K = b\<close>) apply (fastforce simp: Decided_Propagated_in_iff_in_lits_of_l
              add_mset_commute[of a b])
          using \<open>- L' \<notin> lits_of_l M\<close>  add_mset_commute[of a b] apply auto
          using \<open>- L' \<notin> lits_of_l M\<close> apply auto[1]
          done
        have [simp]: \<open>-a \<noteq> L'\<close> \<open>-b \<noteq> L'\<close>
          using \<open>\<forall>L'a. L'a \<in># watched C \<longrightarrow> L'a \<noteq> - L' \<and> L'a \<notin># Q\<close> W C_W_UW
          by fastforce+
        have H': \<open>\<forall>La L'. watched C = {#La, L'#} \<longrightarrow> - La \<in> lits_of_l M \<longrightarrow> L' \<notin> lits_of_l M \<longrightarrow>
          (\<forall>K\<in>#unwatched C. - K \<in> lits_of_l M)\<close>
          using excep C CD Q W WS uab uba by (auto simp: twl_exception_inv.simps)
        then have \<open>\<forall>K\<in>#unwatched C. - K \<in> lits_of_l M\<close>
          using uab uba W C_W_UW \<open>- a \<in> lits_of_l M \<or> - b \<in> lits_of_l M\<close>
          by (auto simp: add_mset_eq_add_mset all_conj_distrib)
        then show False
          by (metis Decided_Propagated_in_iff_in_lits_of_l L' uminus_lit_swap
              Q clause.simps in_diffD propagate.hyps(2) twl_clause.collapse union_iff)
      qed

      ultimately show ?thesis by fast
    qed
  qed
next
  case (conflict D L L' M N U NP UP WS Q) note cands = this(11)
  then show ?case
    by auto
next
  case (delete_from_working D L L' M N U NP UP WS Q) note watched = this(1) and L' = this(2) and
  twl = this(3) and valid = this(4) and inv = this(5) and tauto = this(6) and cands = this(10)
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
  case (update_clause D L L' M K N' U' N U NP UP WS Q) note watched = this(1) and uL = this(2) and
    L' = this(3) and K = this(4) and undef = this(5) and N'U' = this(6) and twl = this(7) and
    valid = this(8) and inv = this(9) and tauto = this(10) and dist = this(11) and
    twl_excep = this(12) and no_dup = this(13) and cands = this(14)
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
    using C N'U' that by (auto split: if_splits dest: in_diffD)
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
  have \<open>D \<notin># N' + U'\<close>
  proof
    assume \<open>D \<in># N' + U'\<close>
    then have \<open>count (N + U) D \<ge> 2\<close>
      using N'U' D
      by (auto simp del: count_greater_zero_iff simp: count_greater_zero_iff[symmetric]
          add_remove_WD split: if_splits)
    then have \<open>count (clause `# (N + U)) (clause D) \<ge> 2\<close>
      using count_image_mset_ge_count[of \<open>N + U\<close> D clause] by linarith
    moreover have \<open>distinct_mset (clause `# (N + U))\<close>
      using dist by (auto simp: clauses_def distinct_mset_add inter_mset_empty_distrib_left
          inter_mset_empty_distrib_right)
    ultimately show False
      unfolding distinct_mset_count_less_1 by (metis Suc_1 not_less_eq_eq)
  qed
  then have CD: \<open>C \<noteq> D\<close> if C: \<open>C \<in># N'+U'\<close> for C
    using C by auto

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
    then have \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># Q) \<or> (\<exists>La. (La, C) \<in># WS)\<close> if \<open>C \<noteq> ?D\<close>
      using cands *[OF that C] CD[OF C] by auto
    moreover have \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># Q) \<or> (\<exists>L. (L, C) \<in># WS)\<close> if [simp]: \<open>C = ?D\<close>
    proof (rule ccontr)
      have \<open>K \<notin> lits_of_l M\<close>
        by (metis D Decided_Propagated_in_iff_in_lits_of_l L'_M_C add_diff_cancel_left'
            clause.simps clause_D in_diffD in_remove1_mset_neq that
            true_annots_true_cls_def_iff_negation_in_model twl_clause.sel(2) uK_M undef_K
            update_clause.hyps(4))
      moreover have \<open>\<forall>L\<in>#remove1_mset K2 (clause D). defined_lit M L\<close>
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
        using C \<open>D \<notin># N' + U'\<close> by auto
      then have excep: \<open>twl_exception_inv (M, N, U, None, NP, UP, add_mset (L, D) WS, Q) D\<close>
        using twl_excep *[of D] D_N_U by (auto simp: twl_st_inv.simps simp del: twl_exception_inv.simps)
      then have \<open>\<forall>K \<in># unwatched D. -K \<in> lits_of_l M\<close>
        using D watched L'_M_C
        by (auto simp: add_mset_eq_add_mset uL'_M L_M uL twl_exception_inv.simps
            true_annots_true_cls_def_iff_negation_in_model dest: in_diffD)
      then show False
        using uK_M update_clause.hyps(4) by blast
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
    inv: "cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (convert_to_state S)" and
    no_taut: "\<forall>D \<in># init_clss (convert_to_state S). \<not> tautology D" and
    dist: \<open>distinct_mset (cdcl\<^sub>W_restart_mset.clauses (convert_to_state S))\<close> and
    twl_excep: \<open>twl_st_exception_inv S\<close> and
    no_dup: \<open>no_duplicate_queued S\<close> and
    cands: \<open>confl_cands_enqueued S\<close>
  shows "confl_cands_enqueued T"
  using cdcl twl valid inv no_taut dist twl_excep no_dup cands
proof (induction rule: cdcl_twl_cp.induct)
  case (pop M N U NP UP L Q) note inv = this(1) and valid = this(2) and cands = this(8)
  show ?case unfolding confl_cands_enqueued.simps Ball_def
  proof (intro allI conjI impI)
    fix C K
    assume C: \<open>C \<in># N + U\<close> and
      \<open>M \<Turnstile>as CNot (clause C)\<close>
    then have \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># add_mset L Q)\<close>
      using cands by auto
    then show
      \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># Q) \<or>
        (\<exists>La. (La, C) \<in># Pair L `# {#C \<in># N + U. L \<in># watched C#})\<close>
      using C by auto
  qed
next
  case (propagate D L L' M N U NP UP WS Q) note watched = this(1) and twl = this(4) and
    valid = this(5) and inv = this(6) and no_taut = this(7) and dist = this(8) and excep = this(9)
    and no_dup = this(10) and cands = this(11)
  have [simp]: \<open>- L' \<notin> lits_of_l M\<close>
    using Decided_Propagated_in_iff_in_lits_of_l propagate.hyps(2) by blast
  have "D \<in># N + U"
    using valid by auto
  then have wf_D: \<open>struct_wf_twl_cls D\<close>
    using twl by (simp add: twl_st_inv.simps)
  have "\<forall>s\<in>#clause `# U. \<not> tautology s"
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def by (simp_all add: cdcl\<^sub>W_restart_mset_state)
  moreover have "D \<in># N + U"
    using valid by auto
  ultimately have taut: "\<not>tautology (clause D)"
    using watched no_taut by (auto simp: cdcl\<^sub>W_restart_mset_state)
  then have [simp]: \<open>-L \<noteq> L'\<close>
    using watched by (cases D) (auto simp: tautology_add_mset)
  have [simp]: \<open>L \<noteq> L'\<close>
    using wf_D watched by (cases D) auto
  have [simp]: \<open>- L \<in> lits_of_l M\<close>
    using valid by auto
  have [simp]: \<open>- La \<noteq> L'\<close> if \<open>La\<in>#unwatched D\<close> for La
    using wf_D watched that taut by (cases D) (auto dest!: multi_member_split simp: tautology_add_mset)
  show ?case unfolding confl_cands_enqueued.simps Ball_def
  proof (intro allI conjI impI)
    fix C K
    assume C: \<open>C \<in># N + U\<close> and
      L'_M_C: \<open>Propagated L' (clause D) # M \<Turnstile>as CNot (clause C)\<close>
    consider
      (no_L') \<open>M \<Turnstile>as CNot (clause C)\<close>
      | (L') \<open>-L' \<in># clause C\<close>
      using L'_M_C
      by (metis \<open>- L' \<notin> lits_of_l M\<close> ann_lit.sel(2) in_CNot_implies_uminus(2) insertE list.simps(15)
          lits_of_insert true_annots_CNot_lit_of_notin_skip)
    then show \<open>(\<exists>L'a. L'a \<in># watched C \<and> L'a \<in># add_mset (- L') Q) \<or> (\<exists>L. (L, C) \<in># WS)\<close>
    proof cases
      case no_L'
      then have \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in>#  Q) \<or> (\<exists>La. (La, C) \<in># add_mset (L, D) WS)\<close>
        using cands C lazy_update_propagate by auto
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
        by (metis L'_M_C \<open>- L' \<notin> lits_of_l M\<close> ann_lit.sel(2) clause.simps in_CNot_implies_uminus(2)
            insertE list.simps(15) lits_of_insert twl_clause.exhaust_sel uminus_not_id'
            union_iff)

      moreover have ?thesis
      proof (rule ccontr, clarsimp)
        assume
          Q: \<open>\<forall>L'a. L'a \<in># watched C \<longrightarrow> L'a \<noteq> - L' \<and> L'a \<notin># Q\<close> and
          WS: \<open>\<forall>L. (L, C) \<notin># WS\<close>
        then have \<open>\<not> twl_is_an_exception C (add_mset (- L') Q) WS\<close>
          by (auto simp: twl_is_an_exception_def)
        moreover have \<open>twl_st_inv (Propagated L' (clause D) # M, N, U, None, NP, UP, WS, add_mset (- L') Q)\<close>
          using twl_cp_twl_inv[OF _ twl valid inv no_taut dist excep no_dup]
          cdcl_twl_cp.propagate[OF propagate(1-3)] by fast
        ultimately have \<open>twl_lazy_update (Propagated L' (clause D) # M) C\<close> and
           twl_inv: \<open>twl_inv (Propagated L' (clause D) # M) C\<close>
          using C by (auto simp: twl_st_inv.simps)

        have struct: \<open>struct_wf_twl_cls C\<close>
          using twl C by (simp add: twl_st_inv.simps)
        have CD: \<open>C \<noteq> D\<close>
          using L'_C watched by auto
        have struct: \<open>struct_wf_twl_cls C\<close>
          using twl C by (simp add: twl_st_inv.simps)
        obtain a b W UW where
          C_W_UW: \<open>C = TWL_Clause W UW\<close> and
          W: \<open>W = {#a, b#}\<close>
          using struct by (cases C, auto simp: size_2_iff)
        have \<open>-a \<in> lits_of_l M \<or> -b \<in> lits_of_l M\<close>
          using L'_M_C C_W_UW W \<open>\<forall>L'a. L'a \<in># watched C \<longrightarrow> L'a \<noteq> - L' \<and> L'a \<notin># Q\<close>
          by (cases \<open>K = a\<close>) fastforce+

        have \<open>no_dup M\<close>
          using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (simp add: trail.simps)
        then have [dest]: False if \<open>a \<in> lits_of_l M\<close> and \<open>-a \<in> lits_of_l M\<close> for a
          using consistent_interp_def distinct_consistent_interp that(1) that(2) by blast
        have uab: \<open>a \<notin> lits_of_l M\<close> if \<open>-b \<in> lits_of_l M\<close>
          (* TODO tune proof *)
          using L'_M_C C_W_UW W that
          apply (cases \<open>K = a\<close>)
          using \<open>- L' \<notin> lits_of_l M\<close> apply auto
          using \<open>- L' \<notin> lits_of_l M\<close> by auto
        have uba: \<open>b \<notin> lits_of_l M\<close> if \<open>-a \<in> lits_of_l M\<close>
          (* TODO tune proof *)
          using L'_M_C C_W_UW W that
          apply (cases \<open>K = b\<close>)
          using \<open>- L' \<notin> lits_of_l M\<close>  add_mset_commute[of a b] apply auto
          using \<open>- L' \<notin> lits_of_l M\<close> apply auto
          done
        have [simp]: \<open>-a \<noteq> L'\<close> \<open>-b \<noteq> L'\<close>
          using \<open>\<forall>L'a. L'a \<in># watched C \<longrightarrow> L'a \<noteq> - L' \<and> L'a \<notin># Q\<close> W C_W_UW
          by fastforce+
        have H': \<open>\<forall>La L'. watched C = {#La, L'#} \<longrightarrow> - La \<in> lits_of_l M \<longrightarrow> L' \<notin> lits_of_l M \<longrightarrow>
          (\<forall>K\<in>#unwatched C. - K \<in> lits_of_l M)\<close>
          using excep C CD Q W WS uab uba by (auto simp: twl_exception_inv.simps)
        then have \<open>\<forall>K\<in>#unwatched C. - K \<in> lits_of_l M\<close>
          using uab uba W C_W_UW \<open>- a \<in> lits_of_l M \<or> - b \<in> lits_of_l M\<close>
          by (auto simp: add_mset_eq_add_mset all_conj_distrib)
        then show False
          by (metis Decided_Propagated_in_iff_in_lits_of_l L' uminus_lit_swap
              \<open>\<forall>L'a. L'a \<in># watched C \<longrightarrow> L'a \<noteq> - L' \<and> L'a \<notin># Q\<close> clause.simps
              propagate.hyps(2) twl_clause.collapse union_iff)
      qed

      ultimately show ?thesis by fast
    qed
  qed
next
  case (conflict D L L' M N U NP UP WS Q) note cands = this(11)
  then show ?case
    by auto
next
  case (delete_from_working D L L' M N U NP UP WS Q) note watched = this(1) and L' = this(2) and
  twl = this(3) and valid = this(4) and inv = this(5) and tauto = this(6) and cands = this(10)
  have n_d: \<open>no_dup M\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (simp add: trail.simps)
  show ?case unfolding confl_cands_enqueued.simps Ball_def
  proof (intro allI conjI impI)
    fix C
    assume C: \<open>C \<in># N + U\<close> and
      L'_M_C: \<open>M \<Turnstile>as CNot (clause C)\<close>
    then have \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># Q) \<or> (\<exists>La. La = L \<and> C = D \<or> (La, C) \<in># WS)\<close>
      using cands by auto
    moreover have False if [simp]: \<open>C = D\<close>
      using L'_M_C watched L' n_d by (cases D) (auto dest!: distinct_consistent_interp
          simp: consistent_interp_def)
    ultimately show \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># Q) \<or> (\<exists>L. (L, C) \<in># WS)\<close>
      by auto
  qed
next
  case (update_clause D L L' M K N' U' N U NP UP WS Q) note watched = this(1) and uL = this(2) and
    L' = this(3) and K = this(4) and undef = this(5) and N'U' = this(6) and twl = this(7) and
    valid = this(8) and inv = this(9) and tauto = this(10) and dist = this(11) and
    twl_excep = this(12) and no_dup = this(13) and cands = this(14)
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
    using C N'U' that by (auto split: if_splits dest: in_diffD)
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
  have \<open>D \<notin># N' + U'\<close>
  proof
    assume \<open>D \<in># N' + U'\<close>
    then have \<open>count (N + U) D \<ge> 2\<close>
      using N'U' D
      by (auto simp del: count_greater_zero_iff simp: count_greater_zero_iff[symmetric]
          add_remove_WD split: if_splits)
    then have \<open>count (clause `# (N + U)) (clause D) \<ge> 2\<close>
      using count_image_mset_ge_count[of \<open>N + U\<close> D clause] by linarith
    moreover have \<open>distinct_mset (clause `# (N + U))\<close>
      using dist by (auto simp: clauses_def distinct_mset_add inter_mset_empty_distrib_left
          inter_mset_empty_distrib_right)
    ultimately show False
      unfolding distinct_mset_count_less_1 by (metis Suc_1 not_less_eq_eq)
  qed
  then have CD: \<open>C \<noteq> D\<close> if C: \<open>C \<in># N'+U'\<close> for C
    using C by auto

  have L_M: \<open>L \<notin> lits_of_l M\<close>
    using n_d uL by (fastforce dest!: distinct_consistent_interp
        simp: consistent_interp_def lits_of_def uminus_lit_swap)
  have w_max_D: \<open>watched_literals_false_of_max_level M D\<close>
    using D_N_U twl by (auto simp: twl_st_inv.simps)
  have lev_L': \<open>get_level M L' = count_decided M\<close> if \<open>- L' \<in> lits_of_l M \<close>
    using L_M w_max_D D watched L' uL that by (auto simp: add_mset_eq_add_mset)
  have clause_D: \<open>clause ?D = clause D\<close>
    using D K watched by auto
  show ?case unfolding confl_cands_enqueued.simps Ball_def
  proof (intro allI conjI impI)
    fix C
    assume C: \<open>C \<in># N' + U'\<close> and
      L'_M_C: \<open>M \<Turnstile>as CNot (clause C)\<close>
    then have \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># Q) \<or> (\<exists>La. (La, C) \<in># WS)\<close> if \<open>C \<noteq> ?D\<close>
      using cands *[OF that C] CD[OF C] by auto
    moreover have \<open>C \<noteq> ?D\<close>
      by (metis D L'_M_C add_diff_cancel_left'  clause.simps clause_D in_diffD
          true_annots_true_cls_def_iff_negation_in_model twl_clause.sel(2) uK_M
          update_clause.hyps(4))
    ultimately show \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># Q) \<or> (\<exists>L. (L, C) \<in># WS)\<close>
      by auto
  qed
qed


subsubsection \<open>Properties of the Transition System\<close>

lemma twl_cp_propagate_or_conflict:
  assumes
    cdcl: "cdcl_twl_cp S T" and
    twl: "twl_st_inv S" and
    valid: "valid_annotation S" and
    inv: "cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (convert_to_state S)" and
    no_taut: "\<forall>D \<in># init_clss (convert_to_state S). \<not> tautology D"
  shows "cdcl\<^sub>W_restart_mset.propagate (convert_to_state S) (convert_to_state T) \<or>
    cdcl\<^sub>W_restart_mset.conflict (convert_to_state S) (convert_to_state T) \<or>
    convert_to_state S = convert_to_state T"
  using cdcl twl valid inv no_taut
proof (induction rule: cdcl_twl_cp.induct)
  case (pop M N U L Q)
  then show ?case by simp
next
  case (propagate D L L' M N U NP UP WS Q) note watched = this(1) and undef = this(2) and no_upd = this(3)
    and twl = this(4) and valid = this(5) and inv = this(6) and no_taut = this(7)
  let ?S = \<open>convert_to_state (M, N, U, None, NP, UP, add_mset (L, D) WS, Q)\<close>
  let ?T = \<open>convert_to_state (Propagated L' (clause D) # M, N, U, None, NP, UP, WS, add_mset (- L') Q)\<close>
  have "\<forall>s\<in>#clause `# U. \<not> tautology s"
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def by (simp_all add: cdcl\<^sub>W_restart_mset_state)
  moreover have "D \<in># N + U"
    using valid by auto
  ultimately have "\<not>tautology (clause D)"
    using watched no_taut by (auto simp: cdcl\<^sub>W_restart_mset_state)
  then have [simp]: \<open>-L \<noteq> L'\<close>
    using watched by (cases D) (auto simp: tautology_add_mset)
  have \<open>cdcl\<^sub>W_restart_mset.propagate ?S ?T\<close>
    apply (rule cdcl\<^sub>W_restart_mset.propagate.intros[of _ \<open>clause D\<close> L'])
        apply (simp add: cdcl\<^sub>W_restart_mset_state; fail)
       apply (metis \<open>D \<in># N + U\<close> clauses_def convert_to_state.simps image_eqI
           in_image_mset union_iff)
      using watched apply (cases D, simp add: clauses_def; fail)
     using no_upd watched valid apply (cases D;
         simp add: trail.simps true_annots_true_cls_def_iff_negation_in_model; fail)
     using undef apply (simp add: trail.simps)
    by (simp add: cdcl\<^sub>W_restart_mset_state del: cdcl\<^sub>W_restart_mset.state_simp)
  then show ?case by blast
next
  case (conflict D L L' M N U NP UP WS Q) note watched = this(1) and defined = this(2)
    and no_upd = this(3) and twl = this(3) and valid = this(5) and inv = this(6) and no_taut = this(7)
  let ?S = "convert_to_state (M, N, U, None, NP, UP, add_mset (L, D) WS, Q)"
  let ?T = "convert_to_state (M, N, U, Some (clause D), NP, UP, {#}, {#})"
  have "D \<in># N + U"
    using valid by auto
  have "\<forall>s\<in>#clause `# U. \<not> tautology s"
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def by (simp_all add: cdcl\<^sub>W_restart_mset_state)
  moreover have "D \<in># N + U"
    using valid by auto
  ultimately have "\<not>tautology (clause D)"
    using watched no_taut by (auto simp: cdcl\<^sub>W_restart_mset_state)
  then have [simp]: \<open>-L \<noteq> L'\<close>
    using watched by (cases D) (auto simp: tautology_add_mset)
  have \<open>distinct_mset (clause D)\<close>
    using inv valid \<open>D \<in># N + U\<close> unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def distinct_mset_set_def
    by (auto simp: cdcl\<^sub>W_restart_mset_state)
  then have \<open>L \<noteq> L'\<close>
    using watched by (cases D) simp
  have \<open>M \<Turnstile>as CNot (unwatched D)\<close>
    using no_upd  by (auto simp: true_annots_true_cls_def_iff_negation_in_model)
  have \<open>cdcl\<^sub>W_restart_mset.conflict ?S ?T\<close>
    apply (rule cdcl\<^sub>W_restart_mset.conflict.intros[of _ \<open>clause D\<close>])
       apply (simp add: cdcl\<^sub>W_restart_mset_state)
      apply (metis \<open>D \<in># N + U\<close> clauses_def convert_to_state.simps image_eqI
        in_image_mset union_iff)
     using watched defined valid \<open>M \<Turnstile>as CNot (unwatched D)\<close> apply (cases D; auto simp add: clauses_def
         trail.simps twl_st_inv.simps; fail)
    by (simp add: cdcl\<^sub>W_restart_mset_state del: cdcl\<^sub>W_restart_mset.state_simp)
  then show ?case by fast
next
  case (delete_from_working D L L' M N U NP UP WS Q)
  then show ?case by simp
next
  case (update_clause D L L' M K N' U' N U NP UP WS Q) note unwatched = this(4) and
    valid = this(8)
  have \<open>D \<in># N + U\<close>
    using valid by auto
  have [simp]: \<open>clause (update_clause D L K) = clause D\<close>
    using valid unwatched by (cases D) (auto simp: subset_mset.add_diff_assoc2
        diff_union_swap2[symmetric]
        subset_mset.add_diff_assoc simp del: diff_union_swap2)
  have \<open>convert_to_state (M, N, U, None, NP, UP, add_mset (L, D) WS, Q) =
    convert_to_state (M, N', U', None, NP, UP, WS, Q)\<close>
    using update_clause \<open>D \<in># N + U\<close> by (cases \<open> D \<in># N\<close>)
      (auto simp: image_mset_remove1_mset_if add_mset_remove_trivial_iff)
  then show ?case by fast
qed

lemma twl_cp_o_cdcl\<^sub>W_o:
  assumes
    cdcl: "cdcl_twl_o S T" and
    twl: "twl_st_inv S" and
    valid: "valid_annotation S" and
    inv: "cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (convert_to_state S)" and
    no_taut: "\<forall>D \<in># init_clss (convert_to_state S). \<not> tautology D"
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o (convert_to_state S) (convert_to_state T)\<close>
  using cdcl twl valid inv no_taut
proof (induction rule: cdcl_twl_o.induct)
  case (decide M L N U NP UP) note undef = this(1) and atm = this(2)
  have \<open>cdcl\<^sub>W_restart_mset.decide (convert_to_state (M, N, U, None, NP, UP, {#}, {#}))
    (convert_to_state (Decided L # M, N, U, None, NP, UP, {#}, {#-L#}))\<close>
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
  case (backtrack_single_clause K M1 M2 M L N U NP UP) note decomp = this(1) and lev_L = this(2)
  and lev_K = this(3) and inv = this(6)
  let ?S = \<open>convert_to_state (M, N, U, Some {#L#}, NP, UP, {#}, {#})\<close>
  let ?T = \<open>convert_to_state (Propagated L {#L#} # M1, N, U, None, NP, add_mset {#L#} UP, {#}, {#L#})\<close>
  have n_d: "no_dup M"
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (simp add: cdcl\<^sub>W_restart_mset_state)
  have "atm_of L \<notin> atm_of ` lits_of_l M1"
    apply (rule cdcl\<^sub>W_restart_mset.backtrack_lit_skiped[of _ ?S])
        using lev_L inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
        apply (simp add: cdcl\<^sub>W_restart_mset_state; fail)
       using decomp apply (simp add: trail.simps; fail)
      using lev_L inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
        apply (simp add: cdcl\<^sub>W_restart_mset_state; fail)
     using lev_L inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
     apply (simp add: cdcl\<^sub>W_restart_mset_state; fail)
    using lev_K apply (simp add: trail.simps; fail)
    done
  obtain M3 where M3: \<open>M = M3 @ M2 @ Decided K # M1\<close>
    using decomp by (blast dest!: get_all_ann_decomposition_exists_prepend)

  have "atm_of K \<notin> atm_of ` lits_of_l (M3 @ M2)"
    using n_d unfolding M3 by (auto simp: lits_of_def)
  then have [simp]: \<open>filter is_decided M1 = []\<close>
    using lev_K by (auto simp: M3 image_Un)
  show ?case
    apply (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o.bj)
    apply (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_bj.backtrack)
    apply (rule cdcl\<^sub>W_restart_mset.backtrack_rule)
          apply (simp add: cdcl\<^sub>W_restart_mset_state; fail)
         apply simp
        using decomp apply (simp add: trail.simps; fail)
        using lev_L apply (simp add: cdcl\<^sub>W_restart_mset_state; fail)
       using lev_L apply (simp add: cdcl\<^sub>W_restart_mset_state get_maximum_level_add_mset; fail)
      apply (simp; fail)
     using lev_K apply (simp add: trail.simps; fail)
    using decomp unfolding state_eq_def state_def prod.inject
    by (simp_all add: cdcl\<^sub>W_restart_mset_state)
next
  case (backtrack L D K M1 M2 M i L' N U NP UP) note LD = this(1) and decomp = this(2) and
  lev_L = this(3) and max_lev = this(4) and i = this(5) and lev_K = this(6) and L' = this(8-9) and
  inv = this(12)
  let ?S = \<open>convert_to_state (M, N, U, Some D, NP, UP, {#}, {#})\<close>
  let ?T = \<open>convert_to_state (Propagated L D # M1, N, U, None, NP, add_mset {#L#} UP, {#}, {#L#})\<close>
  have n_d: "no_dup M"
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (simp add: cdcl\<^sub>W_restart_mset_state)
   have "atm_of L \<notin> atm_of ` lits_of_l M1"
    apply (rule cdcl\<^sub>W_restart_mset.backtrack_lit_skiped[of _ ?S])
       using lev_L inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
       apply (simp add: cdcl\<^sub>W_restart_mset_state; fail)
      using decomp apply (simp add: trail.simps; fail)
     using lev_L inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
       apply (simp add: cdcl\<^sub>W_restart_mset_state; fail)
    using lev_L inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
       apply (simp add: cdcl\<^sub>W_restart_mset_state; fail)
   using lev_K apply (simp add: trail.simps; fail)
   done
  obtain M3 where M3: \<open>M = M3 @ M2 @ Decided K # M1\<close>
    using decomp by (blast dest!: get_all_ann_decomposition_exists_prepend)

  have "atm_of K \<notin> atm_of ` lits_of_l (M3 @ M2)"
    using n_d unfolding M3 by (auto simp: lits_of_def)
  then have count_M1: \<open>count_decided M1 = i\<close>
    using lev_K unfolding M3 by (auto simp: image_Un)
  have \<open>L \<noteq> L'\<close>
    using L' lev_L lev_K count_decided_ge_get_level[of K M] by auto
  then have D: \<open>add_mset L (add_mset L' (D - {#L, L'#})) = D\<close>
    using L' LD by (metis add_mset_diff_bothsides diff_single_eq_union insert_noteq_member mset_add)
  show ?case
    apply (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o.bj)
    apply (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_bj.backtrack)
    apply (rule cdcl\<^sub>W_restart_mset.backtrack_rule)
          apply (simp add: cdcl\<^sub>W_restart_mset_state; fail)
         using LD apply simp
        using decomp apply (simp add: trail.simps; fail)
        using lev_L apply (simp add: cdcl\<^sub>W_restart_mset_state; fail)
       using max_lev apply (simp add: cdcl\<^sub>W_restart_mset_state get_maximum_level_add_mset; fail)
      apply (simp; fail)
     using lev_K i apply (simp add: trail.simps; fail)
     using decomp unfolding state_eq_def state_def prod.inject
     using i lev_K count_M1 by (simp_all add: cdcl\<^sub>W_restart_mset_state D)
qed


fun working_queue :: "'v twl_st \<Rightarrow> ('v literal \<times> 'v literal multiset twl_clause) multiset" where
  \<open>working_queue (_, _, _, _, _, _, WS, _) = WS\<close>

fun set_working_queue :: "('v literal \<times> 'v clause twl_clause) multiset \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st" where
  \<open>set_working_queue WS (M, N, U, D, NP, UP, _, Q) = (M, N, U, D, NP, UP, WS, Q)\<close>

fun pending :: "'v twl_st \<Rightarrow> 'v literal multiset" where
  \<open>pending (_, _, _, _, _, _, _, Q) = Q\<close>

fun set_pending :: "'v literal multiset \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st" where
  \<open>set_pending Q (M, N, U, D, NP, UP, WS, _) = (M, N, U, D, NP, UP, WS, Q)\<close>

fun set_conflict :: "'v clause \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st" where
  \<open>set_conflict D (M, N, U, _, NP, UP, WS, Q) = (M, N, U, Some D, NP, UP, WS, Q)\<close>

fun get_conflict :: "'v twl_st \<Rightarrow> 'v literal multiset option" where
  \<open>get_conflict (M, N, U, D, NP, UP, WS, Q) = D\<close>

fun get_clauses :: "'v twl_st \<Rightarrow> 'v clause twl_clause multiset" where
  \<open>get_clauses (M, N, U, D, NP, UP, WS, Q) = N + U\<close>

fun unit_clss :: "'v twl_st \<Rightarrow> 'v clause multiset" where
  \<open>unit_clss (M, N, U, D, NP, UP, WS, Q) = NP + UP\<close>

fun unit_clss_inv :: "'v twl_st \<Rightarrow> bool"  where
  \<open>unit_clss_inv (M, N, U, D, NP, UP, WS, Q) \<longleftrightarrow>
    (\<forall>C \<in># NP + UP. (\<exists>L. C = {#L#} \<and> L \<in> lits_of_l M))\<close>

definition twl_cp_invs where
  \<open>twl_cp_invs S \<longleftrightarrow>
    (twl_st_inv S \<and>
    valid_annotation S \<and>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (convert_to_state S) \<and>
    (\<forall>D \<in># init_clss (convert_to_state S). \<not> tautology D) \<and>
    distinct_mset (cdcl\<^sub>W_restart_mset.clauses (convert_to_state S)) \<and>
    cdcl\<^sub>W_restart_mset.no_smaller_propa (convert_to_state S) \<and>
    twl_st_exception_inv S \<and>
    no_duplicate_queued S \<and>
    distinct_queued S \<and>
    confl_cands_enqueued S \<and>
    propa_cands_enqueued S \<and>
    (get_conflict S \<noteq> None \<longrightarrow> working_queue S = {#} \<and> pending S = {#}) \<and>
    unit_clss_inv S)
  \<close>
thm cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
lemma cdcl_twl_cp_cdcl\<^sub>W_stgy:
  \<open>cdcl_twl_cp S T \<Longrightarrow> twl_cp_invs S \<Longrightarrow>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (convert_to_state S) (convert_to_state T) \<or>
  convert_to_state S = convert_to_state T\<close>
  by (auto dest!: twl_cp_propagate_or_conflict
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.conflict'
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.propagate'
      simp: twl_cp_invs_def)


lemma cdcl_twl_cp_conflict:
  \<open>cdcl_twl_cp S T \<Longrightarrow> get_conflict T \<noteq> None \<longrightarrow> working_queue T = {#} \<and> pending T = {#}\<close>
  by (induction rule: cdcl_twl_cp.induct) auto

lemma cdcl_twl_cp_unit_clss_inv:
  \<open>cdcl_twl_cp S T \<Longrightarrow> unit_clss_inv S \<Longrightarrow> unit_clss_inv T\<close>
  by (induction rule: cdcl_twl_cp.induct) auto

lemma cdcl_twl_cp_init_clss:
  \<open>cdcl_twl_cp S T \<Longrightarrow> twl_cp_invs S \<Longrightarrow> init_clss (convert_to_state T) = init_clss (convert_to_state S)\<close>
  by (metis cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_no_more_init_clss cdcl_twl_cp_cdcl\<^sub>W_stgy)

lemma cdcl_twl_cp_twl_cp_invs:
  \<open>cdcl_twl_cp S T \<Longrightarrow> twl_cp_invs S \<Longrightarrow> twl_cp_invs T\<close>
  apply (subst twl_cp_invs_def)
  apply (intro conjI)
              apply (simp add: twl_cp_invs_def twl_cp_twl_inv; fail)
             apply (simp add: twl_cp_valid twl_cp_invs_def; fail)
            apply (metis cdcl_twl_cp_cdcl\<^sub>W_stgy cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv
      twl_cp_invs_def)
           apply (simp add: cdcl_twl_cp_init_clss twl_cp_invs_def; fail)
          apply (auto dest!: cdcl_twl_cp_cdcl\<^sub>W_stgy simp: twl_cp_invs_def
      intro: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_distinct_mset)[]
         apply (metis cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_no_smaller_propa cdcl_twl_cp_cdcl\<^sub>W_stgy twl_cp_invs_def)
        apply (rule twl_cp_twl_st_exception_inv; auto simp add: twl_cp_invs_def; fail)
       apply (use twl_cp_invs_def twl_cp_no_duplicate_queued in blast)
      apply (rule twl_cp_distinct_queued; auto simp add: twl_cp_invs_def; fail)
     apply (rule twl_cp_confl_cands_enqueued; auto simp add: twl_cp_invs_def; fail)
    apply (rule twl_cp_propa_cands_enqueued; auto simp add: twl_cp_invs_def; fail)
   apply (simp add: cdcl_twl_cp_conflict; fail)
  apply (simp add: cdcl_twl_cp_unit_clss_inv twl_cp_invs_def; fail)
  done

lemma cdcl_twl_o_twl_st_inv:
  assumes
    cdcl: "cdcl_twl_o S T" and
    twl: "twl_cp_invs S"
  shows
    \<open>twl_st_inv T\<close>
  using cdcl twl
proof (induction rule: cdcl_twl_o.induct)
  case (decide M K N U NP UP) note undef = this(1) and atm = this(2) and invs = this(3)
  let ?S = \<open>(M, N, U, None, NP, UP, {#}, {#})\<close>
  have inv: \<open>twl_st_inv ?S\<close> and excep: \<open>twl_st_exception_inv ?S\<close>
    using invs unfolding twl_cp_invs_def by blast+
  have n_d: \<open>no_dup M\<close>
    using invs unfolding twl_cp_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (simp add: cdcl\<^sub>W_restart_mset_state)
  have n_d': \<open>no_dup (Decided K # M)\<close>
    using defined_lit_map n_d undef by auto
  have propa_cands: \<open>propa_cands_enqueued ?S\<close> and
    confl_cands: \<open>confl_cands_enqueued ?S\<close>
    using invs unfolding twl_cp_invs_def by blast+

  show ?case
    unfolding twl_st_inv.simps Ball_def
  proof (intro conjI allI impI)
    fix C :: \<open>'a clause twl_clause\<close>
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
          using lev_le_Suc[of K'] by force
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

    fix M1 M2 K'
    assume \<open>Decided K # M = M2 @ Decided K' # M1\<close>
    then have M: \<open>M = tl M2 @ Decided K' # M1 \<or> M = M1\<close>
      by (cases M2) auto
    have IH: \<open>\<forall>M1 M2 K. M = M2 @ Decided K # M1 \<longrightarrow>
        twl_lazy_update M1 C \<and> twl_inv M1 C \<and> watched_literals_false_of_max_level M1 C \<and>
        twl_exception_inv (M1, N, U, None, NP, UP, {#}, {#}) C\<close>
      using inv C unfolding twl_st_inv.simps by blast

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
      \<open>propa_cands_enqueued (M1, N, U, None, NP, UP, {#}, {#})\<close>
      using confl_cands inv propa_cands unfolding twl_st_inv.simps by blast+
  qed
next
  case (skip L D C' M N U NP UP)
  then show ?case
    by (auto simp: twl_st_inv.simps twl_cp_invs_def)
next
  case (resolve L D C M N U NP UP)
  then show ?case
    by (auto simp: twl_st_inv.simps twl_cp_invs_def)
next
  case (backtrack_single_clause K M1 M2 M K' N U NP UP) note decomp = this(1) and lev = this(2,3) and
  invs = this(4)
  let ?S = \<open>(M, N, U, Some {#K'#}, NP, UP, {#}, {#})\<close>
  let ?T = \<open>(Propagated K' {#K'#} # M1, N, U, None, NP, add_mset {#K'#} UP, {#}, {#- K'#})\<close>
  let ?M1 = \<open>Propagated K' {#K'#} # M1\<close>
  have bt_twl: \<open>cdcl_twl_o ?S ?T\<close>
    using cdcl_twl_o.backtrack_single_clause[OF backtrack_single_clause.hyps] .
  then have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o (convert_to_state ?S)  (convert_to_state ?T)\<close>
    by (rule twl_cp_o_cdcl\<^sub>W_o) (use invs in \<open>simp_all add: twl_cp_invs_def\<close>)
  then have struct_inv_T: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (convert_to_state ?T)\<close>
    using cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_inv cdcl\<^sub>W_restart_mset.other invs twl_cp_invs_def by blast
  have inv: \<open>twl_st_inv ?S\<close>
    using invs unfolding twl_cp_invs_def by blast
  have n_d: \<open>no_dup M\<close>
    using invs unfolding twl_cp_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (simp add: cdcl\<^sub>W_restart_mset_state)
  have n_d': \<open>no_dup (?M1)\<close>
    using struct_inv_T unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (simp add: trail.simps)

  have propa_cands: \<open>propa_cands_enqueued ?S\<close> and
    confl_cands: \<open>confl_cands_enqueued ?S\<close>
    using invs unfolding twl_cp_invs_def by blast+

  have excep: \<open>twl_st_exception_inv ?S\<close>
    using invs unfolding twl_cp_invs_def by fast

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
    moreover have \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (convert_to_state ?S)\<close>
      using invs unfolding twl_cp_invs_def by blast
    ultimately have False
      using undef M' by (fastforce simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def trail.simps clauses_def)
    then show \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># {#- K'#}) \<or> (\<exists>L. (L, C) \<in># {#})\<close>
      by fast
  qed

  have excep_M1: \<open>twl_st_exception_inv (M1, N, U, None, NP, UP, {#}, {#})\<close>
    using inv unfolding twl_st_exception_inv.simps twl_st_inv.simps M' by auto

  show ?case
    unfolding twl_st_inv.simps Ball_def
  proof (intro conjI allI impI)
    fix C :: \<open>'a clause twl_clause\<close>
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
        using C inv M by (auto simp: twl_st_inv.simps)
      have lev_le_Suc: \<open>get_level M Ka \<le> Suc (count_decided M)\<close> for Ka
        using count_decided_ge_get_level le_Suc_eq by blast
      show \<open>twl_lazy_update (?M1) C\<close>
        apply (rule lazy_update_propagate)
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
        show \<open>get_level (?M1) L \<le> get_level (?M1) L'\<close>
        proof (cases \<open>L = K'\<close>)
          case True
          have L_M: \<open>L \<notin> lits_of_l M1\<close> and uL_M: \<open>-L \<notin> lits_of_l M1\<close>
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
                by (auto simp: add_mset_eq_add_mset) }
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
            using L_M uL_M by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)
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
      using inv C unfolding M' twl_st_simps by blast
    then show \<open>watched_literals_false_of_max_level (?M1) C\<close>
      by (auto simp: C_W)
    fix M1'' M2'' K''
    assume \<open>?M1 = M2'' @ Decided K'' # M1''\<close>
    then have M1: \<open>M1 = tl M2'' @ Decided K'' # M1''\<close>
      by (cases M2'') auto
    then show \<open>twl_lazy_update M1'' C\<close>\<open>twl_inv M1'' C\<close>\<open>watched_literals_false_of_max_level M1'' C\<close>
      \<open>twl_exception_inv (M1'', N, U, None, NP, add_mset {#K'#} UP, {#}, {#}) C\<close>
      using inv C unfolding twl_st_inv.simps M' twl_exception_inv.simps by auto

  next
    fix M1'' M2'' K''
    assume \<open>?M1 = M2'' @ Decided K'' # M1''\<close>
    then have M1: \<open>M1 = tl M2'' @ Decided K'' # M1''\<close>
      by (cases M2'') auto
    then show \<open>confl_cands_enqueued (M1'', N, U, None, NP, add_mset {#K'#} UP, {#}, {#})\<close> and
      \<open>propa_cands_enqueued (M1'', N, U, None, NP, add_mset {#K'#} UP, {#}, {#})\<close>
      using inv
      by (auto simp add: twl_st_inv.simps M)
  qed
next
  case (backtrack K' D K M1 M2 M i K'' N U NP UP) note K'_D = this(1) and decomp = this(2) and
    lev_K' = this(3) and i = this(5) and lev_K = this(6) and K'' = this(8) and lev_K'' = this(9) and
    invs = this(10)
  let ?S = \<open>(M, N, U, Some D, NP, UP, {#}, {#})\<close>
  let ?M1 = \<open>Propagated K' D # M1\<close>
  let ?T = \<open>(?M1, N, add_mset (TWL_Clause {#K', K''#} (D - {#K', K''#})) U, None, NP, UP, {#}, {#- K'#})\<close>
  let ?D = \<open>TWL_Clause {#K', K''#} (D - {#K', K''#})\<close>
  have bt_twl: \<open>cdcl_twl_o ?S ?T\<close>
    using cdcl_twl_o.backtrack[OF backtrack.hyps] .
  then have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o (convert_to_state ?S)  (convert_to_state ?T)\<close>
    by (rule twl_cp_o_cdcl\<^sub>W_o) (use invs in \<open>simp_all add: twl_cp_invs_def\<close>)
  then have struct_inv_T: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (convert_to_state ?T)\<close>
    using cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_inv cdcl\<^sub>W_restart_mset.other invs twl_cp_invs_def by blast
  have inv: \<open>twl_st_inv ?S\<close>
    using invs unfolding twl_cp_invs_def by blast
  have n_d: \<open>no_dup M\<close>
    using invs unfolding twl_cp_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (simp add: cdcl\<^sub>W_restart_mset_state)
  have n_d': \<open>no_dup (Propagated K' D # M1)\<close>
    using struct_inv_T unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (simp add: trail.simps)

  have propa_cands: \<open>propa_cands_enqueued ?S\<close> and
    confl_cands: \<open>confl_cands_enqueued ?S\<close>
    using invs unfolding twl_cp_invs_def by blast+
  obtain M3 where M: \<open>M = M3 @ M2 @ Decided K # M1\<close>
    using decomp by blast
  define M2' where \<open>M2' = M3 @ M2\<close>
  have M': \<open>M = M2' @ Decided K # M1\<close>
    unfolding M M2'_def by simp
  have struct_inv_S: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (convert_to_state ?S)\<close>
    using invs unfolding twl_cp_invs_def by blast
  then have \<open>distinct_mset D\<close>
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
    by (auto simp: conflicting.simps)

  have "atm_of K \<notin> atm_of ` lits_of_l (M3 @ M2)"
    using n_d unfolding M by (auto simp: lits_of_def)
  then have count_M1: \<open>count_decided M1 = i\<close>
    using lev_K unfolding M by (auto simp: image_Un)
  then have K''_ne_K: \<open>K' \<noteq> K''\<close>
    using lev_K lev_K' lev_K'' count_decided_ge_get_level[of K'' M] unfolding M by auto
  then have D: \<open>add_mset K' (add_mset K'' (D - {#K', K''#})) = D\<close> \<open>add_mset K'' (add_mset K' (D - {#K', K''#})) = D\<close>
    using K'' K'_D  multi_member_split by fastforce+
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
    moreover have \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (convert_to_state ?S)\<close>
      using invs unfolding twl_cp_invs_def by blast
    ultimately have False
      using undef M' by (fastforce simp: cdcl\<^sub>W_restart_mset.no_smaller_propa_def trail.simps clauses_def)
    then show \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># {#- K''#}) \<or> (\<exists>L. (L, C) \<in># {#})\<close>
      by fast
  qed
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (convert_to_state ?T)\<close>
    using struct_inv_T unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def twl_cp_invs_def
    by (auto simp: conflicting.simps)
  then have M1_CNot_D: \<open>M1 \<Turnstile>as CNot (remove1_mset K' D)\<close>
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    by (auto simp: conflicting.simps trail.simps)
  then have uK''_M1: \<open>-K'' \<in> lits_of_l M1\<close>
    using K'' K''_ne_K unfolding true_annots_true_cls_def_iff_negation_in_model
    by (metis in_remove1_mset_neq)
  then have \<open>atm_of K'' \<notin> atm_of ` lits_of_l (M3 @ M2 @ Decided K # [])\<close>
    using n_d unfolding M
    by (metis append.assoc append_Cons append_Nil cdcl\<^sub>W_restart_mset.no_dup_uminus_append_in_atm_notin)
  then have lev_M1_K'': \<open>get_level M1 K'' = count_decided M1\<close>
    using lev_K'' count_M1 unfolding M by (auto simp: image_Un)

  have excep_M1: \<open>twl_st_exception_inv (M1, N, U, None, NP, UP, {#}, {#})\<close>
    using inv unfolding twl_st_exception_inv.simps twl_st_inv.simps M' by auto

  show ?case
    unfolding twl_st_inv.simps Ball_def
  proof (intro conjI allI impI)
    fix C :: \<open>'a clause twl_clause\<close>
    assume C: \<open>C \<in># N + add_mset ?D U\<close>
    have \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (convert_to_state ?T)\<close>
      using struct_inv_T unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by blast
    then have \<open>distinct_mset D\<close>
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
      using C inv M' that by (auto simp: twl_st_inv.simps)
    from M1_CNot_D have in_D_M1: \<open>L \<in># remove1_mset K' D \<Longrightarrow> - L \<in> lits_of_l M1\<close> for L
      by (auto simp: true_annots_true_cls_def_iff_negation_in_model)
    then have in_K_D_M1: \<open>L \<in># D - {#K', K''#} \<Longrightarrow> - L \<in> lits_of_l M1\<close> for L
      (* TODO think harder how to avoid this step and inline the previous one *)
      by (metis K'_D add_mset_diff_bothsides add_mset_remove_trivial in_diffD mset_add)
    have
      lazy_D: \<open>twl_lazy_update ?M1 C\<close> and
      watched_max_D: \<open>watched_literals_false_of_max_level ?M1 C\<close> and
      twl_inv_D: \<open>twl_inv ?M1 C\<close> if \<open>C = ?D\<close>
      using that apply (auto simp: add_mset_eq_add_mset count_decided_ge_get_level)[]
      using that apply (auto simp: add_mset_eq_add_mset count_decided_ge_get_level)[]
      unfolding that twl_inv.simps
      apply (intro allI conjI impI)
      using that in_D_M1 apply (auto simp add: add_mset_eq_add_mset dest: in_K_D_M1)[ ]
      by (auto simp add: add_mset_eq_add_mset lev_M1_K'')

    {
      assume excep: \<open>\<not> twl_is_an_exception C {#-K'#} {#}\<close>

      have lev_le_Suc: \<open>get_level M Ka \<le> Suc (count_decided M)\<close> for Ka
        using count_decided_ge_get_level le_Suc_eq by blast
      have \<open>twl_lazy_update ?M1 C\<close> if \<open>C \<noteq> ?D\<close>
        apply (rule lazy_update_propagate)
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
          have L_M: \<open>L \<notin> lits_of_l M1\<close> and uL_M: \<open>-L \<notin> lits_of_l M1\<close>
            using n_d' True by (simp add: atm_lit_of_set_lits_of_l
                atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set)+
          have \<open>\<forall>K \<in># CUW. -K \<in> lits_of_l M1\<close>
          proof -
            { fix ll :: "'a literal"
              have "{#L', L#} = CW"
                by (simp add: W)
              moreover have \<open>twl_exception_inv (M1, N, U, None, NP, UP, {#}, {#}) C\<close>
                using that C excep_M1 by auto
              ultimately have "ll \<notin># CUW \<or> - ll \<in> lits_of_l M1"
                using L_M twl_inv_C uL' unfolding C_W twl_inv.simps twl_exception_inv.simps
                by (auto simp: add_mset_eq_add_mset) }
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
            by (fastforce dest: distinct_consistent_interp mk_disjoint_insert)
          ultimately have \<open>defined_lit M1 L\<close>
            using propa_cands_M1 C W that by auto
          then have False
            using L_M uL_M by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)
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
      using inv C that unfolding M twl_st_simps by auto
    then have \<open>watched_literals_false_of_max_level ?M1 C\<close> if \<open>C \<noteq> ?D\<close>
      using C_W that by auto
    then show \<open>watched_literals_false_of_max_level ?M1 C\<close>
      using watched_max_D by blast

    fix M1'' M2'' K'''
    assume M1: \<open>?M1 = M2'' @ Decided K''' # M1''\<close>
    then have M1: \<open>M1 = tl M2'' @ Decided K''' # M1''\<close>
      by (cases M2'') auto
    then have \<open>twl_lazy_update M1'' C\<close>\<open>twl_inv M1'' C\<close>\<open>watched_literals_false_of_max_level M1'' C\<close>
      \<open>twl_exception_inv (M1'', N, add_mset (TWL_Clause {#K', K''#} (D - {#K', K''#})) U, None, NP, UP, {#}, {#}) C\<close> if \<open>C \<noteq> ?D\<close>
      using inv C that unfolding twl_st_inv.simps M twl_exception_inv.simps by auto
    moreover {
      have n_d_M1: \<open>no_dup ?M1\<close>
        using struct_inv_T unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (simp add: cdcl\<^sub>W_restart_mset_state)
      then have \<open>- K' \<notin> lits_of_l M1''\<close>
        unfolding M1 by (auto simp: lits_of_def uminus_lit_swap)
      moreover {
        have \<open>- K'' \<notin> lits_of_l M1''\<close>
        proof (rule ccontr)
          assume \<open>\<not> - K'' \<notin> lits_of_l M1''\<close>
          have \<open>atm_of (- K'') \<notin> atm_of ` lits_of_l (tl M2'' @ Decided K''' # [])\<close>
            using n_d_M1 unfolding M1 by (metis (no_types) \<open>\<not> - K'' \<notin> lits_of_l M1''\<close> append.assoc
                append_Cons append_Nil atm_of_uminus distinct.simps(2) list.simps(9)
                cdcl\<^sub>W_restart_mset.no_dup_uminus_append_in_atm_notin)
          then show False
            using lev_M1_K''  count_decided_ge_get_level[of K'' M1''] unfolding M1
            by (auto simp: image_Un Int_Un_distrib)
        qed }
      ultimately have \<open>twl_lazy_update M1'' ?D\<close> and \<open>twl_inv M1'' ?D\<close> and
         \<open>watched_literals_false_of_max_level M1'' ?D\<close> and
        \<open>twl_exception_inv (M1'', N, add_mset (TWL_Clause {#K', K''#} (D - {#K', K''#})) U, None, NP, UP, {#}, {#}) ?D\<close>
        by (auto simp: add_mset_eq_add_mset twl_exception_inv.simps) }
    ultimately show \<open>twl_lazy_update M1'' C\<close>\<open>twl_inv M1'' C\<close>\<open>watched_literals_false_of_max_level M1'' C\<close>
      \<open>twl_exception_inv (M1'', N, add_mset (TWL_Clause {#K', K''#} (D - {#K', K''#})) U, None, NP, UP, {#}, {#}) C\<close>
      by blast+
  next
    fix M1'' M2'' K'''
    assume M1: \<open>?M1 = M2'' @ Decided K''' # M1''\<close>
    then have M1: \<open>M1 = tl M2'' @ Decided K''' # M1''\<close>
      by (cases M2'') auto
    then have \<open>confl_cands_enqueued (M1'', N, U, None, NP, UP, {#}, {#})\<close> and
      \<open>propa_cands_enqueued (M1'', N, U, None, NP, UP, {#}, {#})\<close>
      using inv by (auto simp add: M M1 twl_st_inv.simps simp del: propa_cands_enqueued.simps
          confl_cands_enqueued.simps)
    moreover {
      have \<open>- K'' \<notin> lits_of_l M1''\<close>
      proof (rule ccontr)
        assume K''_M1'': \<open>\<not> ?thesis\<close>
        have \<open>atm_of (-K'') \<notin> atm_of ` lits_of_l (tl M2'' @ Decided K''' # [])\<close>
          apply (rule CDCL_W_Abstract_State.cdcl\<^sub>W_restart_mset.no_dup_append_in_atm_notin)
           apply (use n_d' in \<open>auto simp: M M1; fail\<close>)[]
          using K''_M1'' by (simp; fail)
        then show False
          using lev_M1_K'' count_decided_ge_get_level[of K'' M1''] unfolding M M1
          by (auto simp: image_Un)
      qed }
    moreover {
      have \<open>- K' \<notin> lits_of_l M1''\<close>
      proof (rule ccontr)
        assume K'_M1'': \<open>\<not> ?thesis\<close>
        have \<open>atm_of (-K') \<notin> atm_of ` lits_of_l (M3 @ M2 @ Decided K # tl M2'' @ Decided K''' # [])\<close>
          apply (rule CDCL_W_Abstract_State.cdcl\<^sub>W_restart_mset.no_dup_append_in_atm_notin)
          prefer 2 using K'_M1'' apply (simp; fail)
          by (use n_d in \<open>auto simp: M M1; fail\<close>)[]
        then show False
          using lev_K' count_decided_ge_get_level[of K' M1''] unfolding M M1
          by (auto simp: image_Un)
      qed }
    ultimately show \<open>confl_cands_enqueued (M1'', N, add_mset (TWL_Clause {#K', K''#} (D - {#K', K''#})) U, None, NP, UP, {#}, {#})\<close> and
      \<open>propa_cands_enqueued(M1'', N, add_mset (TWL_Clause {#K', K''#} (D - {#K', K''#})) U, None, NP, UP, {#}, {#})\<close>
      using twl by (auto simp add: twl_st_inv.simps)
  qed
qed

lemma
  assumes
    cdcl: "cdcl_twl_o S T"
  shows
    cdcl_twl_o_valid: \<open>valid_annotation T\<close> and
    cdcl_twl_o_conflict_None_queue:
      \<open>get_conflict T \<noteq> None \<Longrightarrow> working_queue T = {#} \<and> pending T = {#}\<close> and
      cdcl_twl_o_no_duplicate_queued: \<open>no_duplicate_queued T\<close> and
      cdcl_twl_o_distinct_queued: \<open>distinct_queued T\<close>
  using cdcl by (induction rule: cdcl_twl_o.induct) auto

lemma cdcl_twl_o_twl_st_exception_inv:
  assumes
    cdcl: "cdcl_twl_o S T" and
    twl: "twl_cp_invs S"
  shows
    \<open>twl_st_exception_inv T\<close>
  using cdcl twl
proof (induction rule: cdcl_twl_o.induct)
  case (decide M L N U NP UP)
  then show ?case
    unfolding twl_cp_invs_def by (auto simp: twl_exception_inv.simps)
next
  case (skip L D C' M N U NP UP)
  then show ?case
    unfolding twl_cp_invs_def by (auto simp: twl_exception_inv.simps)
next
  case (resolve L D C M N U NP UP)
  then show ?case
    unfolding twl_cp_invs_def by (auto simp: twl_exception_inv.simps)
next
  case (backtrack_single_clause K M1 M2 M L N U NP UP) note decomp = this(1) and invs = this(4)
  let ?S = \<open>(M, N, U, Some {#L#}, NP, UP, {#}, {#})\<close>
  let ?S' = \<open>convert_to_state ?S\<close>
  let ?T = \<open>(M1, N, U, None, NP, UP, {#}, {#})\<close>
  let ?T' = \<open>convert_to_state ?T\<close>
  let ?U = \<open>(Propagated L {#L#} # M1, N, U, None, NP, add_mset {#L#} UP, {#}, {#- L#})\<close>
  let ?U' = \<open>convert_to_state ?U\<close>
  have \<open>twl_st_inv ?S\<close>
    using invs decomp unfolding twl_cp_invs_def by fast
  then have \<open>twl_exception_inv ?T C\<close> if \<open>C \<in># N + U\<close> for C
    using decomp that unfolding twl_st_inv.simps by auto
  then show ?case
    by (auto simp: twl_exception_inv.simps)
next
  case (backtrack L D K M1 M2 M i L' N U NP UP) note decomp = this(2) and invs = this(10)
  let ?S = \<open>(M, N, U, Some D, NP, UP, {#}, {#})\<close>
  let ?D = \<open>TWL_Clause {#L, L'#} (D - {#L, L'#})\<close>
  let ?T = \<open>(M1, N, U, None, NP, UP, {#}, {#})\<close>
  let ?U = \<open>(Propagated L D # M1, N, add_mset ?D U, None, NP, UP, {#}, {#- L#})\<close>
  have \<open>twl_st_inv ?S\<close>
    using invs decomp unfolding twl_cp_invs_def by fast
  then have \<open>twl_exception_inv ?T C\<close> if \<open>C \<in># N + U\<close> for C
    using decomp that unfolding twl_st_inv.simps by auto
  then have \<open>twl_exception_inv ?U C\<close> if \<open>C \<in># N + U\<close> for C
    using decomp that unfolding twl_st_inv.simps by (auto simp: twl_exception_inv.simps)
  moreover {
    have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o (convert_to_state ?S) (convert_to_state ?U)\<close>
      by (rule twl_cp_o_cdcl\<^sub>W_o)
        (use cdcl_twl_o.backtrack[OF backtrack.hyps] invs in \<open>simp_all add: twl_cp_invs_def\<close>)
    then have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (convert_to_state ?U)\<close>
      using cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_inv cdcl\<^sub>W_restart_mset.other invs twl_cp_invs_def
      by blast
    then have \<open>no_dup (Propagated L D # M1)\<close>
      unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by (simp add: trail.simps)
    then have \<open>- L \<notin> lits_of_l M1\<close>
      by (auto simp: lits_of_def uminus_lit_swap)
    then have \<open>twl_exception_inv ?U ?D\<close>
      by (auto simp: twl_exception_inv.simps add_mset_eq_add_mset) }
  ultimately show ?case
    by auto
qed


(* TODO refactor: the two backtrack cases are copy-paste from each other.*)
lemma
  assumes
    cdcl: "cdcl_twl_o S T" and
    twl: "twl_cp_invs S"
  shows
    cdcl_twl_o_confl_cands_enqueued: \<open>confl_cands_enqueued T\<close> and
    cdcl_twl_o_propa_cands_enqueued: \<open>propa_cands_enqueued T\<close>
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
    confl_cands: \<open>confl_cands_enqueued ?S\<close>
    unfolding twl_cp_invs_def by fast+

  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o (convert_to_state ?S) (convert_to_state ?T)\<close>
    by (rule twl_cp_o_cdcl\<^sub>W_o) (use cdcl_twl_o.decide[OF decide.hyps] 1 in \<open>simp_all add: twl_cp_invs_def\<close>)
  then have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (convert_to_state ?T)\<close>
    using 1 cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_inv cdcl\<^sub>W_restart_mset.other twl_cp_invs_def by blast
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
      have \<open>K \<noteq> -L \<or> K' \<noteq> -L\<close>
        using dist_C C_W W by auto
      moreover have \<open>K \<notin> lits_of_l M\<close> and \<open>K' \<notin> lits_of_l M\<close> and L_M: \<open>L \<notin> lits_of_l M\<close>
        using neg_C uL_W n_d unfolding C_W W by (auto simp: lits_of_def uminus_lit_swap
            no_dup_cannot_not_lit_and_uminus)
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
      have L_M: \<open>L \<notin> lits_of_l M\<close> \<open>-L \<notin> lits_of_l M\<close>
        using neg_C uL_W n_d unfolding C_W W by (auto simp: lits_of_def uminus_lit_swap
            no_dup_cannot_not_lit_and_uminus)
      then have \<open>K \<noteq> -L\<close>
        using uK_M by auto
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
        using C_W L_M(1) \<open>- L \<in># clause C\<close> uL_W by auto
    qed
    then show \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># {#- L#}) \<or> (\<exists>L. (L, C) \<in># {#})\<close>
      by auto
  qed
next
  case (skip L D C' M N U NP UP)
  case 1 then show ?case by auto
  case 2 then show ?case by auto
next
  case (resolve L D C M N U NP UP)
  case 1 then show ?case by auto
  case 2 then show ?case by auto
next
  case (backtrack_single_clause K M1 M2 M L N U NP UP) note decomp = this(1)
  let ?S = \<open>(M, N, U, Some {#L#}, NP, UP, {#}, {#})\<close>
  let ?U = \<open>(Propagated L {#L#} # M1, N, U, None, NP, add_mset {#L#} UP, {#}, {#- L#})\<close>
  obtain M3 where
    M: \<open>M = M3 @ M2 @ Decided K # M1\<close>
    using decomp by blast

  case 1
  then have twl_st_inv: \<open>twl_st_inv ?S\<close> and
    struct_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (convert_to_state ?S)\<close> and
    excep: \<open>twl_st_exception_inv ?S\<close>
    using decomp unfolding twl_cp_invs_def by fast+
  then have
    confl_cands: \<open>confl_cands_enqueued (M1, N, U, None, NP, UP, {#}, {#})\<close> and
    propa_cands: \<open>propa_cands_enqueued (M1, N, U, None, NP, UP, {#}, {#})\<close>
    using decomp unfolding twl_st_inv.simps by auto

  have n_d: \<open>no_dup M\<close>
    using struct_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
     cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: trail.simps)
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o (convert_to_state ?S) (convert_to_state ?U)\<close>
    using cdcl_twl_o.backtrack_single_clause[OF backtrack_single_clause.hyps]
    by (meson "1.prems" twl_cp_invs_def twl_cp_o_cdcl\<^sub>W_o)
  then have struct_inv_T: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (convert_to_state ?U)\<close>
    using struct_inv cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_inv cdcl\<^sub>W_restart_mset.other by blast
  then have n_d_L_M1: \<open>no_dup (Propagated L {#L#} # M1)\<close>
    using struct_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
     cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: trail.simps)
  then have uL_M1: \<open>- L \<notin> lits_of_l M1\<close> and L_M1:  \<open>L \<notin> lits_of_l M1\<close>
    by (simp_all add: atm_lit_of_set_lits_of_l atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set)


  have excep_M1: \<open>\<forall>C \<in># N + U. twl_exception_inv (M1, N, U, None, NP, UP, {#}, {#}) C\<close>
    using twl_st_inv unfolding twl_st_inv.simps M by auto

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
      using C_W LM_C W uL_M1 by auto
    have \<open>-L \<in># watched C\<close>
    proof (rule ccontr)
      assume uL_W: \<open>-L \<notin># watched C\<close>
      have \<open>K \<noteq> -L \<or> K' \<noteq> -L\<close>
        using dist_C C_W W by auto
      moreover have \<open>K \<notin> lits_of_l M1\<close> and \<open>K' \<notin> lits_of_l M1\<close> and L_M: \<open>L \<notin> lits_of_l M1\<close>
      proof -
        have f2: "consistent_interp (lits_of_l M1)"
          using distinct_consistent_interp n_d_L_M1 by auto
        have "atm_of L \<notin> atm_of ` lits_of_l M1"
          using atm_lit_of_set_lits_of_l n_d_L_M1 by force
        then show "K \<notin> lits_of_l M1"
          using f2 neg_C unfolding C_W W by (metis (no_types) C_W W add_diff_cancel_right'
              atm_of_eq_atm_of atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set clause.simps
              consistent_interp_def in_diffD insertE list.simps(15) lits_of_insert uL_C
              union_single_eq_member)
      next
        show \<open>K' \<notin> lits_of_l M1\<close>
          using consistent_interp_def distinct_consistent_interp n_d_L_M1
          using neg_C uL_W n_d unfolding C_W W by auto
        show \<open>L \<notin> lits_of_l M1\<close>
          by (metis (no_types) ann_lit.sel(2) atm_lit_of_set_lits_of_l
              atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set distinct.simps(2) image_set
              list.simps(9) n_d_L_M1)
      qed
      ultimately have \<open>(-K \<in> lits_of_l M1 \<and> K' \<notin> lits_of_l M1) \<or> (-K' \<in> lits_of_l M1 \<and> K \<notin> lits_of_l M1)\<close>
        using neg_C by (auto simp: C_W W)
      moreover have \<open>twl_exception_inv (M1, N, U, None, NP, UP, {#}, {#}) C\<close>
        using excep_M1 C by auto
      ultimately have \<open>\<forall>K \<in># unwatched C. -K \<in> lits_of_l M1\<close>
        apply (auto simp: twl_exception_inv.simps C_W W add_mset_eq_add_mset all_conj_distrib
            L_M)
        done
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
        using uK_M uL_M1 L_M1 by auto
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
        using C_W L_M1 \<open>- L \<in># clause C\<close> uL_W by auto
    qed
    then show \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># {#- L#}) \<or> (\<exists>L. (L, C) \<in># {#})\<close>
      by auto
  qed
next
  case (backtrack L D K M1 M2 M i L' N U NP UP) note LD = this(1) and decomp = this(2) and
    lev_L = this(3) and lev_max_L = this(4) and i = this(5) and lev_K = this(6) and lev_L' = this(9)
  let ?S = \<open>(M, N, U, Some D, NP, UP, {#}, {#})\<close>
  let ?D = \<open>TWL_Clause {#L, L'#} (D - {#L, L'#})\<close>
  let ?U = \<open>(Propagated L D # M1, N, add_mset (TWL_Clause {#L, L'#} (D - {#L, L'#})) U, None, NP,
    UP, {#}, {#- L#})\<close>
  obtain M3 where
    M: \<open>M = M3 @ M2 @ Decided K # M1\<close>
    using decomp by blast

  case 1
  then have twl_st_inv: \<open>twl_st_inv ?S\<close> and
    struct_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (convert_to_state ?S)\<close> and
    excep: \<open>twl_st_exception_inv ?S\<close>
    using decomp unfolding twl_cp_invs_def by fast+
  then have
    confl_cands: \<open>confl_cands_enqueued (M1, N, U, None, NP, UP, {#}, {#})\<close> and
    propa_cands: \<open>propa_cands_enqueued (M1, N, U, None, NP, UP, {#}, {#})\<close>
    using decomp unfolding twl_st_inv.simps by auto

  have n_d: \<open>no_dup M\<close>
    using struct_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
     cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: trail.simps)
  have \<open>atm_of K \<notin> atm_of ` lits_of_l (M3 @ M2 @ M1)\<close>
    by (rule cdcl\<^sub>W_restart_mset.no_dup_append_in_atm_notin[of _ \<open>[Decided K]\<close>])
      (use n_d M in auto)
  then have L_uL': \<open>L \<noteq> - L'\<close>
    using lev_L lev_L' lev_K unfolding M by (auto simp: image_Un)

  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o (convert_to_state ?S) (convert_to_state ?U)\<close>
    using cdcl_twl_o.backtrack[OF backtrack.hyps] by (meson "1.prems" twl_cp_invs_def twl_cp_o_cdcl\<^sub>W_o)
  then have struct_inv_T: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (convert_to_state ?U)\<close>
    using struct_inv cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_inv cdcl\<^sub>W_restart_mset.other by blast
  then have n_d_L_M1: \<open>no_dup (Propagated L D # M1)\<close>
    using struct_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
     cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: trail.simps)
  then have uL_M1: \<open>- L \<notin> lits_of_l M1\<close> and L_M1:  \<open>L \<notin> lits_of_l M1\<close>
    by (simp_all add: atm_lit_of_set_lits_of_l atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set)

  have M1_CNot_L_D: \<open>M1 \<Turnstile>as CNot (remove1_mset L D)\<close>
    using struct_inv_T unfolding  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
     cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def by (auto simp: trail.simps)

  have excep_M1: \<open>\<forall>C \<in># N + U. twl_exception_inv (M1, N, U, None, NP, UP, {#}, {#}) C\<close>
    using twl_st_inv unfolding twl_st_inv.simps M by auto
  show ?case
    unfolding confl_cands_enqueued.simps Ball_def
  proof (intro allI impI)
    fix C
    assume
      C: \<open>C \<in># N + add_mset ?D U\<close> and
      LM_C: \<open>Propagated L D # M1 \<Turnstile>as CNot (clause C)\<close>
    have \<open>twl_st_inv ?U\<close>
      using cdcl_twl_o.backtrack[OF backtrack.hyps] "1.prems" cdcl_twl_o_twl_st_inv by blast
    then have \<open>struct_wf_twl_cls ?D\<close>
      unfolding twl_st_inv.simps by auto


    show \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># {#- L#}) \<or> (\<exists>L. (L, C) \<in># {#})\<close>
    proof (cases \<open>C = ?D\<close>)
      case True
      then have False
        using LM_C by (auto simp: true_annots_true_cls_def_iff_negation_in_model L_uL' uL_M1)
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
        using C_W LM_C W uL_M1 by auto
      have \<open>-L \<in># watched C\<close>
      proof (rule ccontr)
        assume uL_W: \<open>-L \<notin># watched C\<close>
        have \<open>K \<noteq> -L \<or> K' \<noteq> -L\<close>
          using dist_C C_W W by auto
        moreover have \<open>K \<notin> lits_of_l M1\<close> and \<open>K' \<notin> lits_of_l M1\<close> and L_M: \<open>L \<notin> lits_of_l M1\<close>
        proof -
          have f2: "consistent_interp (lits_of_l M1)"
            using distinct_consistent_interp n_d_L_M1 by auto
          have "atm_of L \<notin> atm_of ` lits_of_l M1"
            using atm_lit_of_set_lits_of_l n_d_L_M1 by force
          then show "K \<notin> lits_of_l M1"
            using f2 neg_C unfolding C_W W by (metis (no_types) C_W W add_diff_cancel_right'
                atm_of_eq_atm_of atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set clause.simps
                consistent_interp_def in_diffD insertE list.simps(15) lits_of_insert uL_C
                union_single_eq_member)
        next
          show \<open>K' \<notin> lits_of_l M1\<close>
            using consistent_interp_def distinct_consistent_interp n_d_L_M1
            using neg_C uL_W n_d unfolding C_W W by auto
          show \<open>L \<notin> lits_of_l M1\<close>
            by (metis (no_types) ann_lit.sel(2) atm_lit_of_set_lits_of_l
                atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set distinct.simps(2) image_set
                list.simps(9) n_d_L_M1)
        qed
        ultimately have \<open>(-K \<in> lits_of_l M1 \<and> K' \<notin> lits_of_l M1) \<or> (-K' \<in> lits_of_l M1 \<and> K \<notin> lits_of_l M1)\<close>
          using neg_C by (auto simp: C_W W)
        moreover have \<open>twl_exception_inv (M1, N, U, None, NP, UP, {#}, {#}) C\<close>
          using excep_M1 C by auto
        ultimately have \<open>\<forall>K \<in># unwatched C. -K \<in> lits_of_l M1\<close>
          apply (auto simp: twl_exception_inv.simps C_W W add_mset_eq_add_mset all_conj_distrib
              L_M)
          done
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
      LM_C: \<open>Propagated L D # M1 \<Turnstile>as CNot (remove1_mset FK (clause C))\<close> and
      undef: \<open>undefined_lit (Propagated L D # M1) FK\<close>
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
          using uK_M uL_M1 L_M1 by auto
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
          using C_W L_M1 \<open>- L \<in># clause C\<close> uL_W by auto
      qed
      then show \<open>(\<exists>L'. L' \<in># watched C \<and> L' \<in># {#- L#}) \<or> (\<exists>L. (L, C) \<in># {#})\<close>
        by auto
    next
      case True
      then have \<open>\<forall>K\<in>#remove1_mset L D. - K \<in> lits_of_l (Propagated L D # M1)\<close>
        using M1_CNot_L_D by (auto simp: true_annots_true_cls_def_iff_negation_in_model)
      then have \<open>\<forall>K\<in>#remove1_mset L D. defined_lit (Propagated L D # M1) K\<close>
        using Decided_Propagated_in_iff_in_lits_of_l by blast
      moreover have \<open>defined_lit (Propagated L D # M1) L\<close>
        by (auto simp: defined_lit_map)
      ultimately have \<open>\<forall>K\<in>#D. defined_lit (Propagated L D # M1) K\<close>
        by (metis LD insert_DiffM insert_noteq_member)
      then have \<open>\<forall>K\<in>#clause ?D. defined_lit (Propagated L D # M1) K\<close>
        by (metis \<open>defined_lit (Propagated L D # M1) L\<close> add_mset_remove_trivial backtrack.hyps(8)
            clause.simps in_diffD in_remove1_mset_neq insert_DiffM2 union_iff)
      then have False
        using K undef unfolding True by blast
      then show ?thesis by fast
    qed
  qed
qed

lemma cdcl_twl_o_unit_clss_inv:
  \<open>cdcl_twl_o S T \<Longrightarrow> unit_clss_inv S \<Longrightarrow> unit_clss_inv T\<close>
sorry

inductive cdcl_twl_stgy :: "'v twl_st \<Rightarrow> 'v twl_st \<Rightarrow> bool" for S :: \<open>'v twl_st\<close> where
cp: "cdcl_twl_cp S S' \<Longrightarrow> cdcl_twl_stgy S S'" |
other': "cdcl_twl_o S S' \<Longrightarrow> cdcl_twl_stgy S S'"

lemma
  assumes
    WS: \<open>working_queue S = {#}\<close> and Q: \<open>pending S = {#}\<close> and
    twl: \<open>twl_cp_invs S\<close>
  shows
    \<open>no_step cdcl\<^sub>W_restart_mset.propagate (convert_to_state S)\<close> and
    \<open>no_step cdcl\<^sub>W_restart_mset.conflict (convert_to_state S)\<close>
proof -
  obtain M N U NP UP D where
      S: \<open>S = (M, N, U, D, NP, UP, {#}, {#})\<close>
    using WS Q by (cases S) auto

  {
    assume confl: \<open>get_conflict S = None\<close>
    then have S: \<open>S = (M, N, U, None, NP, UP, {#}, {#})\<close>
      using WS Q S by auto

    have twl_st_inv: \<open>twl_st_inv S\<close> and
      struct_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (convert_to_state S)\<close> and
      excep: \<open>twl_st_exception_inv S\<close> and
      confl_cands: \<open>confl_cands_enqueued S\<close> and
      propa_cands: \<open>propa_cands_enqueued S\<close> and
      unit: \<open>unit_clss_inv S\<close>
      using twl unfolding twl_cp_invs_def by fast+
    have n_d: \<open>no_dup M\<close>
      using struct_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: trail.simps S)
    then have L_uL: \<open>L \<in> lits_of_l M \<Longrightarrow> -L \<notin> lits_of_l M\<close> for L
      using consistent_interp_def distinct_consistent_interp by blast
    have \<open>\<forall>C \<in># N + U. \<not>M\<Turnstile>as CNot (clause C)\<close>
      using confl_cands unfolding S by auto
    moreover have \<open>\<not>M\<Turnstile>as CNot C\<close> if C: \<open>C \<in># NP + UP\<close> for C
    proof -
      obtain L where L: \<open>C = {#L#}\<close> and L_M: \<open>L \<in> lits_of_l M\<close>
        using unit C unfolding S by auto
      show ?thesis
        using L_M unfolding L
        by (auto simp: true_annots_true_cls_def_iff_negation_in_model dest: L_uL)
    qed
    ultimately have ns_confl: \<open>no_step cdcl\<^sub>W_restart_mset.conflict (convert_to_state S)\<close>
      by (auto elim!: cdcl\<^sub>W_restart_mset.conflictE simp: S trail.simps clauses_def)

    have ns_propa: \<open>no_step cdcl\<^sub>W_restart_mset.propagate (convert_to_state S)\<close>
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
        then obtain L'' where L'': \<open>C = {#L''#}\<close> and L_M: \<open>L'' \<in> lits_of_l M\<close>
          using unit unfolding S by auto
        then show ?thesis
          using L M undef
          by (auto simp: true_annots_true_cls_def_iff_negation_in_model
              Decided_Propagated_in_iff_in_lits_of_l dest: L_uL)
      qed
    qed
    note ns_confl ns_propa
  }
  moreover {
    assume \<open>get_conflict S \<noteq> None\<close>
    then have \<open>no_step cdcl\<^sub>W_restart_mset.propagate (convert_to_state S)\<close>
      \<open>no_step cdcl\<^sub>W_restart_mset.conflict (convert_to_state S)\<close>
      by (auto elim!: cdcl\<^sub>W_restart_mset.propagateE cdcl\<^sub>W_restart_mset.conflictE
          simp: S conflicting.simps)
  }
  ultimately show \<open>no_step cdcl\<^sub>W_restart_mset.propagate (convert_to_state S)\<close>
      \<open>no_step cdcl\<^sub>W_restart_mset.conflict (convert_to_state S)\<close>
    by blast+
qed

lemma
  assumes
    cdcl: "cdcl_twl_o S T" and
    twl: \<open>twl_cp_invs S\<close>
  shows
    \<open>twl_cp_invs T\<close>
proof -
  have cdcl\<^sub>W: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart (convert_to_state S) (convert_to_state T)\<close>
    using twl unfolding twl_cp_invs_def by (meson cdcl cdcl\<^sub>W_restart_mset.other twl_cp_o_cdcl\<^sub>W_o)

  have cdcl\<^sub>W_stgy: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (convert_to_state S) (convert_to_state T)\<close>
    sorry
  have init: \<open>init_clss (convert_to_state T) = init_clss (convert_to_state S)\<close>
    using cdcl\<^sub>W by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart_init_clss)
  show ?thesis
    unfolding twl_cp_invs_def
    apply (intro conjI)
               apply (use cdcl cdcl_twl_o_twl_st_inv twl in \<open>blast; fail\<close>)
              apply (use cdcl cdcl_twl_o_valid in \<open>blast; fail\<close>)
             apply (use cdcl\<^sub>W cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_inv twl twl_cp_invs_def in \<open>blast; fail\<close>)
            apply (use twl in \<open>simp add: init twl_cp_invs_def\<close>)
           apply (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_distinct_mset[OF cdcl\<^sub>W_stgy])
             apply ((use twl in \<open>simp add: init twl_cp_invs_def; fail\<close>)+)[3]
          apply (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_no_smaller_propa[OF cdcl\<^sub>W_stgy])
           apply ((use twl in \<open>simp add: init twl_cp_invs_def; fail\<close>)+)[2]
         apply (use cdcl cdcl_twl_o_twl_st_exception_inv twl in \<open>blast; fail\<close>)
        apply (use cdcl cdcl_twl_o_no_duplicate_queued in \<open>blast; fail\<close>)
       apply (use cdcl cdcl_twl_o_distinct_queued in \<open>blast; fail\<close>)
      apply (use cdcl cdcl_twl_o_confl_cands_enqueued twl twl_cp_invs_def in \<open>blast; fail\<close>)
     apply (use cdcl cdcl_twl_o_propa_cands_enqueued twl twl_cp_invs_def in \<open>blast; fail\<close>)
    apply (use cdcl twl cdcl_twl_o_conflict_None_queue in \<open>blast; fail\<close>)
    done
qed

end