theory CDCL_Two_Watched_Literals_Simple_Implementation
imports CDCL_W_Abstract_State
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
    (M, N, U, Some (clause D), NP, UP, add_mset (L, D) WS, Q)"
  -- \<open>we keep \<open>add_mset (L, D) Q\<close> to ease the proofs (it will be thrown away later in the calculus).\<close>
  if "watched D = {#L, L'#}" and "-L' \<in> lits_of_l M" and "\<forall>L \<in># unwatched D. -L \<in> lits_of_l M" |
delete_from_working:
  "cdcl_twl_cp (M, N, U, None, NP, UP, add_mset (L, D) WS, Q) (M, N, U, None, NP, UP,WS, Q)"
  if "watched D = {#L, L'#}" and "L' \<in> lits_of_l M" |
update_clause:
  "cdcl_twl_cp (M, N, U, None, NP, UP, add_mset (L, D) WS, Q)
    (M, N', U', None, NP, UP, WS, Q)"
  if "watched D = {#L, L'#}" and \<open>-L \<in> lits_of_l M\<close> and \<open>L' \<notin> lits_of_l M\<close> and
    \<open>K \<in># unwatched D\<close> and \<open>undefined_lit M K \<or> K \<in> lits_of_l M\<close> and
    \<open>(N', U') = update_clauses (N, U) D L K\<close>


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
definition twl_is_an_exception
  :: "'a multiset twl_clause \<Rightarrow> 'a multiset \<Rightarrow> ('b \<times> 'a multiset twl_clause) multiset \<Rightarrow> bool" where
"twl_is_an_exception C Q WS \<longleftrightarrow>
   (\<exists>L. L \<in># Q \<and> L \<in># watched C) \<or> (\<exists>L. (L, C) \<in># WS)"

lemma twl_is_an_exception_add_mset_to_queue: \<open>twl_is_an_exception C (add_mset L Q) WS \<longleftrightarrow>
  (twl_is_an_exception C Q WS \<or> (L \<in># watched C))\<close>
  unfolding twl_is_an_exception_def by auto

lemma twl_is_an_exception_add_mset_to_working_queue:
  \<open>twl_is_an_exception C Q (add_mset (L, D) WS) \<longleftrightarrow> (twl_is_an_exception C Q WS \<or> (C = D))\<close>
  unfolding twl_is_an_exception_def by auto

fun twl_inv :: "('a, 'b) ann_lits \<Rightarrow> 'a clause twl_clause \<Rightarrow> bool" where
"twl_inv M (TWL_Clause W UW) \<longleftrightarrow>
  (\<forall>L L'. W = {#L, L'#} \<longrightarrow> -L \<in> lits_of_l M \<longrightarrow> L' \<notin> lits_of_l M \<longrightarrow> (\<forall>K \<in># UW. -K \<in> lits_of_l M)) \<and>
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

fun twl_st_inv :: "'v twl_st \<Rightarrow> bool" where
"twl_st_inv (M, N, U, C, NP, UP, WS, Q) \<longleftrightarrow>
  (\<forall>C \<in># N + U. struct_wf_twl_cls C) \<and>
  (\<forall>C \<in># N + U. \<not>twl_is_an_exception C Q WS \<longrightarrow> (twl_lazy_update M C \<and> twl_inv M C)) \<and>
  (\<forall>C \<in># N + U. watched_literals_false_of_max_level M C) \<and>
  (\<forall>M1 M2 K. M = M2 @ Decided K # M1 \<longrightarrow> (\<forall>C \<in># N + U. twl_lazy_update M1 C \<and> twl_inv M1 C))"

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

paragraph \<open>Properties\<close>
lemma twl_st_inv_remove_conflicting:
  \<open>twl_st_inv (M, N, U, Some C, NP, UP, WS, Q) \<longleftrightarrow> twl_st_inv (M, N, U, None, NP, UP, WS, Q)\<close>
  unfolding twl_st_inv.simps by blast

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
    (\<not>twl_is_an_exception C Q WS \<longrightarrow> (twl_lazy_update M C \<and> twl_inv M C)) \<and>
    watched_literals_false_of_max_level M C \<and>
    (\<forall>M1 M2 K. M = M2 @ Decided K # M1 \<longrightarrow> (twl_lazy_update M1 C \<and> twl_inv M1 C)))"
  unfolding twl_st_inv.simps by blast

lemma last_in_set_dropWhile:
  assumes \<open>\<exists>L \<in> set (xs @ [x]). \<not>P L\<close>
  shows \<open>x \<in> set (dropWhile P (xs @ [x]))\<close>
  using assms by (induction xs) auto

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
      L: \<open>- L \<in> lits_of_l M1\<close> and
      L': \<open>L' \<notin> lits_of_l M1\<close>
    have LM: \<open>- L \<in> lits_of_l M\<close>
      using L unfolding M by auto
    then have lev_L_M1: \<open>get_level M L = get_level M1 L\<close>
      using L n_d lev_M_M1[of "-L"] by auto

    have L'M: \<open>L' \<notin> lits_of_l M\<close>
    proof
      assume H: \<open>L' \<in> lits_of_l M\<close>
      then have \<open>get_level M L' \<le> get_level M L\<close>
        using twl W LM unfolding C by auto
      moreover have \<open>get_level M L \<le> count_decided M1\<close>
        using lev_L_M1 count_decided_ge_get_level by metis
      ultimately have *: \<open>get_level (M' @ M1) L' \<le> count_decided M1\<close>
        unfolding M M' by auto
      moreover have \<open>atm_of (-L') \<notin> atm_of ` lits_of_l M'\<close>
      proof (rule ccontr)
        assume H: "\<not> ?thesis"
        then have \<open>get_level M' L' = 0\<close>
          using * by (subst (asm) get_rev_level_skip_end) auto
        moreover have \<open>Decided K \<in> set (dropWhile (\<lambda>S. atm_of (lit_of S) \<noteq> atm_of L') ((M3 @ M2) @ [Decided K]))\<close>
          by (rule last_in_set_dropWhile)  (use H in \<open>auto simp: lits_of_def M'\<close>)
        ultimately show False
          by (auto simp add: filter_empty_conv M')
      qed
      ultimately show False using H L' by (subst (asm) get_rev_level_skip) (auto simp: M M')
    qed
    then have \<open>\<forall>K\<in>#UW. - K \<in> lits_of_l M\<close>
      using twl W LM unfolding C by auto
    show \<open>\<forall>K\<in>#UW. - K \<in> lits_of_l M1\<close>
    proof (clarify, rule ccontr)
      fix K'
      assume K': \<open>K' \<in># UW\<close> and K_M1: \<open>- K' \<notin> lits_of_l M1\<close>
      then have *: \<open>get_level M L \<ge> get_level M K'\<close>
        using lazy LM L'M C W by auto
      have \<open>- K' \<in> lits_of_l M\<close>
        using K' twl W LM L'M unfolding C by auto
      then have K_M': \<open>atm_of K' \<in> atm_of ` lits_of_l M'\<close>
        using K_M1 unfolding MM' by (simp add: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set)
      have \<open>Decided K \<in> set (dropWhile (\<lambda>S. atm_of (lit_of S) \<noteq> atm_of K') M')\<close>
        unfolding M' append_assoc[symmetric] by (rule last_in_set_dropWhile)
          (use K_M' in \<open>auto simp: lits_of_def M' MM'\<close>)
      moreover have \<open>get_level M' K' = 0\<close>
        using * count_decided_ge_get_level[of L M1]
        unfolding lev_L_M1 unfolding MM'
        by (subst (asm) get_rev_level_skip_end[OF K_M']) linarith
      ultimately show False
        by (metis ann_lit.disc(1) filter_empty_conv length_0_conv)
    qed
  next
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
  by (subst cdcl\<^sub>W_restart_mset.clauses_def, subst init_clss_def, subst learned_clss_def) simp

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
    \<open>-L \<notin> lits_of_l M\<close> and
    \<open>get_level M L' = count_decided M\<close>
  shows
    \<open>twl_inv (Propagated L D # M) (TWL_Clause W UW)\<close>
  unfolding twl_inv.simps
  apply (intro conjI allI impI)
   using assms(2) apply (auto simp add: W add_mset_eq_add_mset; fail)[]
  using assms(3) apply (auto simp add: W add_mset_eq_add_mset; fail)[]
  done

lemma watched_literals_false_of_max_level_Propagated:
  assumes
    W: \<open>W = {#L, L'#}\<close> and
    \<open>-L \<notin> lits_of_l M\<close>
  shows
    \<open>watched_literals_false_of_max_level (Propagated L D # M) (TWL_Clause W UW)\<close>
  using assms(2) by (simp add: W add_mset_eq_add_mset)

(* TODO rename *)
lemma K:\<open> - L' \<notin># watched C \<Longrightarrow> watched_literals_false_of_max_level M C\<Longrightarrow>
  twl_lazy_update (Propagated L' (clause D) # M) C\<close>
  by (cases C) (auto simp: add_mset_eq_add_mset count_decided_ge_get_level)
(* END TODO *)

(* TODO Move *)
lemma get_level_append_cons_le_count_decided_notin:
  \<open>get_level (M' @ Decided K # M) L \<le> count_decided M \<Longrightarrow>
  atm_of L \<notin> atm_of ` lits_of_l (M' @ [Decided K])\<close>
  by (auto simp add: dropWhile_append3)

lemma watched_literals_false_of_max_level:
  assumes
    struct_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (convert_to_state S)\<close> and
    stgy_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (convert_to_state S)\<close> and
    propa: \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (convert_to_state S)\<close> and
    S: \<open>S = (M, N, U, D, NP, UP, WS, Q)\<close> and
    C_N_U: \<open>C \<in># N + U\<close> and
    struct: \<open>struct_wf_twl_cls C\<close> and
    twl_inv: \<open>twl_inv M C\<close> and
    lazy: \<open>twl_lazy_update M C\<close>
  shows \<open>watched_literals_false_of_max_level M C\<close>
proof -
  obtain W UW where C: \<open>C = TWL_Clause W UW\<close> by (cases C)
  have n_d: \<open>no_dup M\<close>
    using struct_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: trail_def S)

  show ?thesis
    unfolding C watched_literals_false_of_max_level.simps
  proof (intro allI impI, rule ccontr)
    fix L L'
    assume
      W: \<open>W = {#L, L'#}\<close> and
      uL_M: \<open>- L \<in> lits_of_l M\<close> and
      L'_M: \<open>L' \<notin> lits_of_l M\<close>
    then have UW_neg: \<open>\<And>K. K \<in># UW \<Longrightarrow> -K \<in> lits_of_l M\<close>
      using twl_inv by (auto simp: C)
    define C' where \<open>C' = clause C - {#L'#}\<close>
    have \<open>clause C = add_mset L' C'\<close>
      using W unfolding C'_def by (simp add: C)
    then have C': \<open>add_mset L' C' \<in># clause `# (N + U)\<close>
      using C_N_U by force

    assume \<open>get_level M L \<noteq> count_decided M\<close>
    then have \<open>get_level M L < count_decided M\<close>
      using count_decided_ge_get_level[of L M] by linarith
    then obtain M1 K M2 where
      M: \<open>M = M2 @ Decided K # M1\<close> and
      lev_L: \<open>get_level M K = Suc (get_level M L)\<close>
      using le_count_decided_decomp[of M \<open>get_level M L\<close>] n_d by fast
    have \<open>atm_of K \<notin> atm_of ` lits_of_l M2\<close>
      using n_d unfolding M by (auto simp: lits_of_def)
    then have L_M2_K: \<open>atm_of L \<notin> atm_of ` lits_of_l (M2 @ [Decided K])\<close>
      using lev_L unfolding M
      by auto
    have \<open>M1 \<Turnstile>as CNot C'\<close>
      unfolding true_annots_true_cls_def_iff_negation_in_model
    proof
      fix J
      assume J_C': \<open>J \<in># C'\<close>
      then have uJ_M: \<open>-J \<in> lits_of_l M\<close>
        using UW_neg W uL_M by (auto simp: C'_def C)
      have \<open>J = L \<or> J \<in># UW\<close>
        using J_C' W unfolding C'_def C by auto
      then have lev_J: \<open>get_level M J \<le> get_level M L\<close>
        using lazy uL_M L'_M by (auto simp: C'_def C W add_mset_eq_add_mset)

      have \<open>atm_of J \<notin> atm_of ` lits_of_l (M2 @ [Decided K])\<close>
        by (rule get_level_append_cons_le_count_decided_notin[of J M2 K M1])
        (use L_M2_K lev_J count_decided_ge_get_level[of L M1] in \<open>auto simp: M\<close>)
      then show \<open>-J \<in> lits_of_l M1\<close>
        using uJ_M by (auto simp: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set M)
    qed
    have H: \<open>\<And>Ma K M' Da L. M = M' @ Decided K # Ma \<Longrightarrow>
      Da + {#L#} \<in># clause `# (N + U) \<longrightarrow>
      undefined_lit Ma L \<longrightarrow>
      \<not> Ma \<Turnstile>as CNot Da\<close>
      using propa unfolding S cdcl\<^sub>W_restart_mset.no_smaller_propa_def
      by (auto simp add: clauses_def trail_def)

    have \<open>\<not>undefined_lit M1 L'\<close>
      using C' H[of M2 K M1 C' L'] \<open>M1 \<Turnstile>as CNot C'\<close>
      by (simp add: C clauses_def trail_def M)

    then have \<open>-L' \<in> lits_of_l M1\<close>
      using Decided_Propagated_in_iff_in_lits_of_l M \<open>L' \<notin> lits_of_l M\<close> by auto
    then have \<open>M1 \<Turnstile>as CNot (add_mset L' C')\<close>
      using \<open>M1 \<Turnstile>as CNot C'\<close> by auto
    then show False
      (* TODO tune proof *)
      using stgy_inv C' unfolding  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def S
        cdcl\<^sub>W_restart_mset.no_smaller_confl_def
      apply (simp add: clauses_def conflicting_def trail_def M)
      using \<open>M1 \<Turnstile>as CNot (add_mset L' C')\<close> by blast
  qed
qed

lemma pair_in_image_Pair:
  \<open> (La, C) \<in> Pair L ` D \<longleftrightarrow> La = L \<and> C \<in> D\<close>
  by auto

lemma twl_cp_twl_inv:
  assumes
    cdcl: "cdcl_twl_cp S T" and
    twl: "twl_st_inv S" and
    valid: "valid_annotation S" and
    inv: "cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (convert_to_state S)" and
    no_taut: "\<forall>D \<in># init_clss (convert_to_state S). \<not> tautology D" and
    dist: \<open>distinct_mset (cdcl\<^sub>W_restart_mset.clauses (convert_to_state S))\<close>
  shows "twl_st_inv T"
  using cdcl twl valid inv no_taut dist
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
      cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def by (simp_all add: learned_clss_def init_clss_def)
  moreover have "D \<in># N + U"
    using valid by auto
  ultimately have taut: "\<not>tautology (clause D)"
    using watched no_taut by (auto simp: init_clss_def)
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
      apply (rule K)
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
      using excep that apply (auto simp add: twl_is_an_exception_add_mset_to_queue uminus_lit_swap)[]
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
    then show \<open>twl_lazy_update M1 C\<close> and \<open>twl_inv M1 C\<close>
      using C twl by (auto simp add: twl_st_inv.simps)
  qed
next
  case (conflict D L L' M N U NP UP WS Q) note twl = this(4)
  then show ?case
    by (auto simp: twl_st_inv_remove_conflicting)
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
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (simp add: trail_def)
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
    then show \<open>twl_lazy_update M1 C\<close> and \<open>twl_inv M1 C\<close>
      using C twl by (auto simp add: twl_st_inv.simps)
  qed
next
  case (update_clause D L L' M K N' U' N U NP UP WS Q) note watched = this(1) and uL = this(2) and
    L' = this(3) and K = this(4) and undef = this(5) and N'U' = this(6) and twl = this(7) and
    valid = this(8) and inv = this(9) and tauto = this(10) and dist = this(11)
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
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: trail_def)
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
    have twl_D: \<open>twl_inv M ?D\<close>
      apply (use watched uK_M uL D in
          \<open>auto simp: add_mset_eq_add_mset lev_L lev_L' count_decided_ge_get_level
          in_remove1_mset\<close>)
      sorry
    
    thm twl
    show \<open>twl_inv M C\<close>
      using twl_C twl_D by blast
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
    have \<open>twl_lazy_update M1 C\<close> and \<open>twl_inv M1 C\<close> if \<open>C \<noteq> ?D\<close>
      using * C CD twl that M by (auto simp add: twl_st_inv.simps)
    moreover have \<open>twl_lazy_update M1 ?D\<close> and \<open>twl_inv M1 ?D\<close>
      using D watched uK_M by (auto simp: M add_mset_eq_add_mset dest!: H)
    ultimately show \<open>twl_lazy_update M1 C\<close> and \<open>twl_inv M1 C\<close> by blast+
  qed
qed


lemma twl_cp_no_duplicate_queued:
  assumes
    cdcl: "cdcl_twl_cp S T" and
    no_dup: \<open>no_duplicate_queued S\<close>
  shows "no_duplicate_queued T"
  using cdcl  no_dup
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
    by (auto simp: twl_st_inv_remove_conflicting)
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
    by auto
next
  case (propagate D L L' M N U NP UP WS Q) note watched = this(1) and twl = this(4) and valid = this(5)
    and inv = this(6) and no_taut = this(7)
  show ?case
    using valid by auto
next
  case (conflict D L L' M N U NP UP WS Q) note valid = this(5)
  then show ?case
    by (auto simp: twl_st_inv_remove_conflicting)
next
  case (delete_from_working D L L' M N U NP UP WS Q) note watched = this(1) and L' = this(2) and
  twl = this(3) and valid = this(4) and inv = this(5) and tauto = this(6)
  show ?case unfolding twl_st_simps Ball_def
    using valid by auto
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
    cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def by (simp_all add: learned_clss_def init_clss_def)
  moreover have "D \<in># N + U"
    using valid by auto
  ultimately have "\<not>tautology (clause D)"
    using watched no_taut by (auto simp: init_clss_def)
  then have [simp]: \<open>-L \<noteq> L'\<close>
    using watched by (cases D) (auto simp: tautology_add_mset)
  have \<open>cdcl\<^sub>W_restart_mset.propagate ?S ?T\<close>
    apply (rule cdcl\<^sub>W_restart_mset.propagate.intros[of _ \<open>clause D\<close> L'])
        apply (simp add: conflicting_def; fail)
       apply (metis \<open>D \<in># N + U\<close> clauses_def convert_to_state.simps image_eqI
           in_image_mset union_iff)
      using watched apply (cases D, simp add: clauses_def; fail)
     using no_upd watched valid apply (cases D;
         simp add: trail_def true_annots_true_cls_def_iff_negation_in_model; fail)
     using undef apply (simp add: trail_def)
    by (simp add: cdcl\<^sub>W_restart_mset_state del: cdcl\<^sub>W_restart_mset.state_simp)
  then show ?case by blast
next
  case (conflict D L L' M N U NP UP WS Q) note watched = this(1) and defined = this(2)
    and no_upd = this(3) and twl = this(3) and valid = this(5) and inv = this(6) and no_taut = this(7)
  let ?S = "convert_to_state (M, N, U, None, NP, UP, add_mset (L, D) WS, Q)"
  let ?T = "convert_to_state (M, N, U, Some (clause D), NP, UP, add_mset (L, D) WS, Q)"
  have "D \<in># N + U"
    using valid by auto
  have "\<forall>s\<in>#clause `# U. \<not> tautology s"
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def by (simp_all add: learned_clss_def init_clss_def)
  moreover have "D \<in># N + U"
    using valid by auto
  ultimately have "\<not>tautology (clause D)"
    using watched no_taut by (auto simp: init_clss_def)
  then have [simp]: \<open>-L \<noteq> L'\<close>
    using watched by (cases D) (auto simp: tautology_add_mset)
  have \<open>distinct_mset (clause D)\<close>
    using inv valid \<open>D \<in># N + U\<close> unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def distinct_mset_set_def
    by (auto simp: learned_clss_def init_clss_def)
  then have \<open>L \<noteq> L'\<close>
    using watched by (cases D) simp
  have \<open>M \<Turnstile>as CNot (unwatched D)\<close>
    using no_upd  by (auto simp: true_annots_true_cls_def_iff_negation_in_model)
  have \<open>cdcl\<^sub>W_restart_mset.conflict ?S ?T\<close>
    apply (rule cdcl\<^sub>W_restart_mset.conflict.intros[of _ "clause D"])
       apply (simp add: conflicting_def)
      apply (metis \<open>D \<in># N + U\<close> clauses_def convert_to_state.simps image_eqI
        in_image_mset union_iff)
     using watched defined valid \<open>M \<Turnstile>as CNot (unwatched D)\<close> apply (cases D; auto simp add: clauses_def
         trail_def twl_st_inv.simps; fail)
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

end