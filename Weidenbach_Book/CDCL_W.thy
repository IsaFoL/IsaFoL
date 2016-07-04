theory CDCL_W
imports List_More CDCL_W_Level Wellfounded_More Partial_Annotated_Clausal_Logic
begin
chapter \<open>Weidenbach's CDCL\<close>

text \<open>The organisation of the development is the following:
  \<^item> @{file CDCL_W.thy} contains the specification of the rules: the rules and the strategy are
  defined, and we proof the correctness of CDCL.
  \<^item> @{file CDCL_W_Termination.thy} contains the proof of termination, based on the book.
  \<^item> @{file CDCL_W_Merge.thy} contains a variant of the calculus: some rules of the raw calculus are
  always applied together (like the rules analysing the conflict and then backtracking). We define
  an equivalent version  of the calculus where these rules are applied together. This is useful for
  implementations.
  \<^item> @{file CDCL_WNOT.thy} proves the inclusion of Weidenbach's version of CDCL in NOT's version. We
  use here the version defined in @{file CDCL_W_Merge.thy}. We need this, because NOT's backjump
  corresponds to multiple applications of three rules in Weidenbach's calculus. We show also the
  termination of the calculus without strategy.

We have some variants build on the top of Weidenbach's CDCL calculus:
  \<^item> @{file CDCL_W_Incremental.thy} adds incrementality on the top of @{file CDCL_W.thy}. The way we
  are doing it is not compatible with @{file CDCL_W_Merge.thy} , because we add conflicts and the
  @{file CDCL_W_Merge.thy} cannot analyse conflicts added externally, because the conflict and
  analyse are merged.
  \<^item> @{file CDCL_W_Restart.thy} adds restart. It is built on the top of @{file CDCL_W_Merge.thy}.

\<close>
section \<open>Weidenbach's CDCL with Multisets\<close>
declare upt.simps(2)[simp del]

subsection \<open>The State\<close>
text \<open>We will abstract the representation of clause and clauses via two locales. We here use
  multisets, contrary to @{file CDCL_W_Abstract_State.thy} where we assume only the existence of a
  conversion to the state.\<close>

locale state\<^sub>W_ops =
  fixes
    trail :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" and
    init_clss :: "'st \<Rightarrow> 'v clauses" and
    learned_clss :: "'st \<Rightarrow> 'v clauses" and
    backtrack_lvl :: "'st \<Rightarrow> nat" and
    conflicting :: "'st \<Rightarrow> 'v clause option" and

    cons_trail :: "('v, 'v clause) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_learned_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_backtrack_lvl :: "nat \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conflicting :: "'v clause option \<Rightarrow> 'st \<Rightarrow> 'st" and

    init_state :: "'v clauses \<Rightarrow> 'st"
begin
abbreviation hd_trail :: "'st \<Rightarrow> ('v, 'v clause) ann_lit" where
"hd_trail S \<equiv> hd (trail S)"

definition clauses :: "'st \<Rightarrow> 'v clauses" where
"clauses S = init_clss S + learned_clss S"

abbreviation resolve_cls where
"resolve_cls L D' E \<equiv> remove1_mset (-L) D' #\<union> remove1_mset L E"

abbreviation state :: "'st \<Rightarrow> ('v, 'v clause) ann_lits \<times> 'v clauses \<times> 'v clauses
  \<times> nat \<times> 'v clause option" where
"state S \<equiv> (trail S, init_clss S, learned_clss S, backtrack_lvl S, conflicting S)"
end

text \<open>We are using an abstract state to abstract away the detail of the implementation: we do not
  need to know how the clauses are represented internally, we just need to know that they can be
  converted to multisets.\<close>
text \<open>Weidenbach state is a five-tuple composed of:
  \<^enum> the trail is a list of decided literals;
  \<^enum> the initial set of clauses (that is not changed during the whole calculus);
  \<^enum> the learned clauses (clauses can be added or remove);
  \<^enum> the maximum level of the trail;
  \<^enum> the conflicting clause (if any has been found so far).\<close>
text \<open>
  There are two different clause representation: one for the conflicting clause (@{typ "'v clause"},
  standing for conflicting clause) and one for the initial and learned clauses (@{typ "'v clause"},
  standing for clause). The representation of the clauses annotating literals in the trail
  is slightly different: being able to convert it to @{typ "'v clause"} is enough (needed for function
  @{term "hd_trail"} below).

  There are several axioms to state the independance of the different fields of the state: for
  example, adding a clause to the learned clauses does not change the trail.\<close>
locale state\<^sub>W =
  state\<^sub>W_ops

    \<comment> \<open>functions about the state: \<close>
      \<comment> \<open>getter:\<close>
    trail init_clss learned_clss backtrack_lvl conflicting
      \<comment> \<open>setter:\<close>
    cons_trail tl_trail add_learned_cls remove_cls update_backtrack_lvl
    update_conflicting

      \<comment> \<open>Some specific states:\<close>
    init_state
  for
    trail :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" and
    init_clss :: "'st \<Rightarrow> 'v clauses" and
    learned_clss :: "'st \<Rightarrow> 'v clauses" and
    backtrack_lvl :: "'st \<Rightarrow> nat" and
    conflicting :: "'st \<Rightarrow> 'v clause option" and

    cons_trail :: "('v, 'v clause) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_learned_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_backtrack_lvl :: "nat \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conflicting :: "'v clause option \<Rightarrow> 'st \<Rightarrow> 'st" and

    init_state :: "'v clauses \<Rightarrow> 'st" +
  assumes
    cons_trail:
      "\<And>S'. state st = (M, S') \<Longrightarrow>
        state (cons_trail L st) = (L # M, S')" and

    tl_trail:
      "\<And>S'. state st = (M, S') \<Longrightarrow> state (tl_trail st) = (tl M, S')" and

    remove_cls:
      "\<And>S'. state st = (M, N, U, S') \<Longrightarrow>
        state (remove_cls C st) =
          (M, removeAll_mset C N, removeAll_mset C U, S')" and

    add_learned_cls:
      "\<And>S'. state st = (M, N, U, S') \<Longrightarrow>
        state (add_learned_cls C st) = (M, N, {#C#} + U, S')" and

    update_backtrack_lvl:
      "\<And>S'. state st = (M, N, U, k, S') \<Longrightarrow>
        state (update_backtrack_lvl k' st) = (M, N, U, k', S')" and

    update_conflicting:
      "state st = (M, N, U, k, D) \<Longrightarrow>
        state (update_conflicting E st) = (M, N, U, k, E)" and

    init_state:
      "state (init_state N) = ([], N, {#}, 0, None)"
begin
  lemma
    trail_cons_trail[simp]:
      "trail (cons_trail L st) = L # trail st" and
    trail_tl_trail[simp]: "trail (tl_trail st) = tl (trail st)" and
    trail_add_learned_cls[simp]:
      "trail (add_learned_cls C st) = trail st" and
    trail_remove_cls[simp]:
      "trail (remove_cls C st) = trail st" and
    trail_update_backtrack_lvl[simp]: "trail (update_backtrack_lvl k st) = trail st" and
    trail_update_conflicting[simp]: "trail (update_conflicting E st) = trail st" and

    init_clss_cons_trail[simp]:
      "init_clss (cons_trail M st) = init_clss st"
      and
    init_clss_tl_trail[simp]:
      "init_clss (tl_trail st) = init_clss st" and
    init_clss_add_learned_cls[simp]:
      "init_clss (add_learned_cls C st) = init_clss st" and
    init_clss_remove_cls[simp]:
      "init_clss (remove_cls C st) = removeAll_mset C (init_clss st)" and
    init_clss_update_backtrack_lvl[simp]:
      "init_clss (update_backtrack_lvl k st) = init_clss st" and
    init_clss_update_conflicting[simp]:
      "init_clss (update_conflicting E st) = init_clss st" and

    learned_clss_cons_trail[simp]:
      "learned_clss (cons_trail M st) = learned_clss st" and
    learned_clss_tl_trail[simp]:
      "learned_clss (tl_trail st) = learned_clss st" and
    learned_clss_add_learned_cls[simp]:
      "learned_clss (add_learned_cls C st) = {#C#} + learned_clss st" and
    learned_clss_remove_cls[simp]:
      "learned_clss (remove_cls C st) = removeAll_mset C (learned_clss st)" and
    learned_clss_update_backtrack_lvl[simp]:
      "learned_clss (update_backtrack_lvl k st) = learned_clss st" and
    learned_clss_update_conflicting[simp]:
      "learned_clss (update_conflicting E st) = learned_clss st" and

    backtrack_lvl_cons_trail[simp]:
      "backtrack_lvl (cons_trail M st) = backtrack_lvl st" and
    backtrack_lvl_tl_trail[simp]:
      "backtrack_lvl (tl_trail st) = backtrack_lvl st" and
    backtrack_lvl_add_learned_cls[simp]:
      "backtrack_lvl (add_learned_cls C st) = backtrack_lvl st" and
    backtrack_lvl_remove_cls[simp]:
      "backtrack_lvl (remove_cls C st) = backtrack_lvl st" and
    backtrack_lvl_update_backtrack_lvl[simp]:
      "backtrack_lvl (update_backtrack_lvl k st) = k" and
    backtrack_lvl_update_conflicting[simp]:
      "backtrack_lvl (update_conflicting E st) = backtrack_lvl st" and

    conflicting_cons_trail[simp]:
      "conflicting (cons_trail M st) = conflicting st" and
    conflicting_tl_trail[simp]:
      "conflicting (tl_trail st) = conflicting st" and
    conflicting_add_learned_cls[simp]:
      "conflicting (add_learned_cls C st) = conflicting st"
      and
    conflicting_remove_cls[simp]:
      "conflicting (remove_cls C st) = conflicting st" and
    conflicting_update_backtrack_lvl[simp]:
      "conflicting (update_backtrack_lvl k st) = conflicting st" and
    conflicting_update_conflicting[simp]:
      "conflicting (update_conflicting E st) = E" and

    init_state_trail[simp]: "trail (init_state N) = []" and
    init_state_clss[simp]: "init_clss (init_state N) = N" and
    init_state_learned_clss[simp]: "learned_clss (init_state N) = {#}" and
    init_state_backtrack_lvl[simp]: "backtrack_lvl (init_state N) = 0" and
    init_state_conflicting[simp]: "conflicting (init_state N) = None"

  using cons_trail[of st] tl_trail[of st] add_learned_cls[of st _ _ _ _ C]
  update_backtrack_lvl[of st _ _ _ _ _ k] update_conflicting[of st _ _ _ _ _ E]
  remove_cls[of st _ _ _ _ C]
  init_state[of N]
  by (cases "state st"; auto simp:)+

lemma
  shows
    clauses_cons_trail[simp]:
      "clauses (cons_trail M S) = clauses S" and
    (* non-standard to avoid name clash with NOT's clauses_tl_trail *)
    clss_tl_trail[simp]: "clauses (tl_trail S) = clauses S" and
    clauses_add_learned_cls_unfolded:
      "clauses (add_learned_cls U S) = {#U#} + learned_clss S + init_clss S"
      and
    clauses_update_backtrack_lvl[simp]: "clauses (update_backtrack_lvl k S) = clauses S" and
    clauses_update_conflicting[simp]: "clauses (update_conflicting D S) = clauses S" and
    clauses_remove_cls[simp]:
      "clauses (remove_cls C S) = removeAll_mset C (clauses S)" and
    clauses_add_learned_cls[simp]:
      " clauses (add_learned_cls C S) = {#C#} + clauses S" and
    clauses_init_state[simp]: "clauses (init_state N) = N"
    by (auto simp: ac_simps replicate_mset_plus clauses_def intro: multiset_eqI)

abbreviation incr_lvl :: "'st \<Rightarrow> 'st" where
"incr_lvl S \<equiv> update_backtrack_lvl (backtrack_lvl S + 1) S"

definition state_eq :: "'st \<Rightarrow> 'st \<Rightarrow> bool" (infix "\<sim>" 50) where
"S \<sim> T \<longleftrightarrow> state S = state T"

lemma state_eq_ref[simp, intro]:
  "S \<sim> S"
  unfolding state_eq_def by auto

lemma state_eq_sym:
  "S \<sim> T \<longleftrightarrow> T \<sim> S"
  unfolding state_eq_def by auto

lemma state_eq_trans:
  "S \<sim> T \<Longrightarrow> T \<sim> U \<Longrightarrow> S \<sim> U"
  unfolding state_eq_def by auto

lemma
  shows
    state_eq_trail: "S \<sim> T \<Longrightarrow> trail S = trail T" and
    state_eq_init_clss: "S \<sim> T \<Longrightarrow> init_clss S = init_clss T" and
    state_eq_learned_clss: "S \<sim> T \<Longrightarrow> learned_clss S = learned_clss T" and
    state_eq_backtrack_lvl: "S \<sim> T \<Longrightarrow> backtrack_lvl S = backtrack_lvl T" and
    state_eq_conflicting: "S \<sim> T \<Longrightarrow> conflicting S = conflicting T" and
    state_eq_clauses: "S \<sim> T \<Longrightarrow> clauses S = clauses T" and
    state_eq_undefined_lit: "S \<sim> T \<Longrightarrow> undefined_lit (trail S) L = undefined_lit (trail T) L"
  unfolding state_eq_def clauses_def by auto

lemma state_eq_conflicting_None:
  "S \<sim> T \<Longrightarrow> conflicting T = None \<Longrightarrow> conflicting S = None"
  unfolding state_eq_def clauses_def by auto

text \<open>We combine all simplification rules about @{term state_eq} in a single list of theorems. While
  they are handy as simplification rule as long as we are working on the state, they also cause a
  \<^emph>\<open>huge\<close> slow-down in all other cases.\<close>
lemmas state_simp[simp] = state_eq_trail state_eq_init_clss state_eq_learned_clss
  state_eq_backtrack_lvl state_eq_conflicting state_eq_clauses state_eq_undefined_lit
  state_eq_conflicting_None

function reduce_trail_to :: "'a list \<Rightarrow> 'st \<Rightarrow> 'st" where
"reduce_trail_to F S =
  (if length (trail S) = length F \<or> trail S = [] then S else reduce_trail_to F (tl_trail S))"
by fast+
termination
  by (relation "measure (\<lambda>(_, S). length (trail S))") simp_all

declare reduce_trail_to.simps[simp del]

lemma
  shows
    reduce_trail_to_Nil[simp]: "trail S = [] \<Longrightarrow> reduce_trail_to F S = S" and
    reduce_trail_to_eq_length[simp]: "length (trail S) = length F \<Longrightarrow> reduce_trail_to F S = S"
  by (auto simp: reduce_trail_to.simps)

lemma reduce_trail_to_length_ne:
  "length (trail S) \<noteq> length F \<Longrightarrow> trail S \<noteq> [] \<Longrightarrow>
    reduce_trail_to F S = reduce_trail_to F (tl_trail S)"
  by (auto simp: reduce_trail_to.simps)

lemma trail_reduce_trail_to_length_le:
  assumes "length F > length (trail S)"
  shows "trail (reduce_trail_to F S) = []"
  using assms apply (induction F S rule: reduce_trail_to.induct)
  by (metis (no_types, hide_lams) length_tl less_imp_diff_less less_irrefl trail_tl_trail
    reduce_trail_to.simps)

lemma trail_reduce_trail_to_Nil[simp]:
  "trail (reduce_trail_to [] S) = []"
  apply (induction "[]::('v, 'v clause) ann_lits" S rule: reduce_trail_to.induct)
  by (metis length_0_conv reduce_trail_to_length_ne reduce_trail_to_Nil)

lemma clauses_reduce_trail_to_Nil:
  "clauses (reduce_trail_to [] S) = clauses S"
proof (induction "[]" S rule: reduce_trail_to.induct)
  case (1 Sa)
  then have "clauses (reduce_trail_to ([]::'a list) (tl_trail Sa)) = clauses (tl_trail Sa)
    \<or> trail Sa = []"
    by fastforce
  then show "clauses (reduce_trail_to ([]::'a list) Sa) = clauses Sa"
    by (metis (no_types) length_0_conv reduce_trail_to_eq_length clss_tl_trail
      reduce_trail_to_length_ne)
qed

lemma reduce_trail_to_skip_beginning:
  assumes "trail S = F' @ F"
  shows "trail (reduce_trail_to F S) = F"
  using assms by (induction F' arbitrary: S) (auto simp: reduce_trail_to_length_ne)

lemma clauses_reduce_trail_to[simp]:
  "clauses (reduce_trail_to F S) = clauses S"
  apply (induction F S rule: reduce_trail_to.induct)
  by (metis clss_tl_trail reduce_trail_to.simps)

lemma conflicting_update_trail[simp]:
  "conflicting (reduce_trail_to F S) = conflicting S"
  apply (induction F S rule: reduce_trail_to.induct)
  by (metis conflicting_tl_trail reduce_trail_to.simps)

lemma backtrack_lvl_update_trail[simp]:
  "backtrack_lvl (reduce_trail_to F S) = backtrack_lvl S"
  apply (induction F S rule: reduce_trail_to.induct)
  by (metis backtrack_lvl_tl_trail reduce_trail_to.simps)

lemma init_clss_update_trail[simp]:
  "init_clss (reduce_trail_to F S) = init_clss S"
  apply (induction F S rule: reduce_trail_to.induct)
  by (metis init_clss_tl_trail reduce_trail_to.simps)

lemma learned_clss_update_trail[simp]:
  "learned_clss (reduce_trail_to F S) = learned_clss S"
  apply (induction F S rule: reduce_trail_to.induct)
  by (metis learned_clss_tl_trail reduce_trail_to.simps)

lemma conflicting_reduce_trail_to[simp]:
  "conflicting (reduce_trail_to F S) = None \<longleftrightarrow> conflicting S = None"
  apply (induction F S rule: reduce_trail_to.induct)
  by (metis conflicting_update_trail map_option_is_None)

lemma trail_eq_reduce_trail_to_eq:
  "trail S = trail T \<Longrightarrow> trail (reduce_trail_to F S) = trail (reduce_trail_to F T)"
  apply (induction F S arbitrary: T rule: reduce_trail_to.induct)
  by (metis trail_tl_trail reduce_trail_to.simps)

lemma reduce_trail_to_state_eq\<^sub>N\<^sub>O\<^sub>T_compatible:
  assumes ST: "S \<sim> T"
  shows "reduce_trail_to F S \<sim> reduce_trail_to F T"
proof -
  have "trail (reduce_trail_to F S) = trail (reduce_trail_to F T)"
    using trail_eq_reduce_trail_to_eq[of S T F] ST by auto
  then show ?thesis using ST by (auto simp del: state_simp simp: state_eq_def)
qed

lemma reduce_trail_to_trail_tl_trail_decomp[simp]:
  "trail S = F' @ Decided K # F \<Longrightarrow> (trail (reduce_trail_to F S)) = F "
  apply (rule reduce_trail_to_skip_beginning[of _ "F' @ Decided K # []"])
  by (cases F') (auto simp add:tl_append reduce_trail_to_skip_beginning)

lemma reduce_trail_to_add_learned_cls[simp]:
  "trail (reduce_trail_to F (add_learned_cls C S)) = trail (reduce_trail_to F S)"
  by (rule trail_eq_reduce_trail_to_eq) auto

lemma reduce_trail_to_remove_learned_cls[simp]:
  "trail (reduce_trail_to F (remove_cls C S)) = trail (reduce_trail_to F S)"
  by (rule trail_eq_reduce_trail_to_eq) auto

lemma reduce_trail_to_update_conflicting[simp]:
  "trail (reduce_trail_to F (update_conflicting C S)) = trail (reduce_trail_to F S)"
  by (rule trail_eq_reduce_trail_to_eq) auto

lemma reduce_trail_to_update_backtrack_lvl[simp]:
  "trail (reduce_trail_to F (update_backtrack_lvl k S)) = trail (reduce_trail_to F S)"
  by (rule trail_eq_reduce_trail_to_eq) auto

lemma reduce_trail_to_length:
  "length M = length M' \<Longrightarrow> reduce_trail_to M S = reduce_trail_to M' S"
  apply (induction M S rule: reduce_trail_to.induct)
  by (simp add: reduce_trail_to.simps)

lemma trail_reduce_trail_to_drop:
  "trail (reduce_trail_to F S) =
    (if length (trail S) \<ge> length F
    then drop (length (trail S) - length F) (trail S)
    else [])"
  apply (induction F S rule: reduce_trail_to.induct)
  apply (rename_tac F S, case_tac "trail S")
   apply auto[]
  apply (rename_tac list, case_tac "Suc (length list) > length F")
   prefer 2 apply (metis diff_is_0_eq drop_Cons' length_Cons nat_le_linear nat_less_le
     reduce_trail_to_eq_length trail_reduce_trail_to_length_le)
  apply (subgoal_tac "Suc (length list) - length F = Suc (length list - length F)")
  by (auto simp add: reduce_trail_to_length_ne)

lemma in_get_all_ann_decomposition_trail_update_trail[simp]:
  assumes H: "(L # M1, M2) \<in> set (get_all_ann_decomposition (trail S))"
  shows "trail (reduce_trail_to M1 S) = M1"
proof -
  obtain K where
    L: "L = Decided K"
    using H by (cases L) (auto dest!: in_get_all_ann_decomposition_decided_or_empty)
  obtain c where
    tr_S: "trail S = c @ M2 @ L # M1"
    using H by auto
  show ?thesis
    by (rule reduce_trail_to_trail_tl_trail_decomp[of _ "c @ M2" K])
     (auto simp: tr_S L)
qed

lemma conflicting_cons_trail_conflicting[simp]:
  assumes "undefined_lit (trail S) (lit_of L)"
  shows
    "conflicting (cons_trail L S) = None \<longleftrightarrow> conflicting S = None"
  using assms conflicting_cons_trail[of L S] map_option_is_None by fastforce+

lemma conflicting_add_learned_cls_conflicting[simp]:
  "conflicting (add_learned_cls C S) = None \<longleftrightarrow> conflicting S = None"
  by fastforce+

lemma conflicting_update_backtracl_lvl[simp]:
  "conflicting (update_backtrack_lvl k S) = None \<longleftrightarrow> conflicting S = None"
  using map_option_is_None conflicting_update_backtrack_lvl[of k S] by fastforce+

end \<comment> \<open>end of \<open>state\<^sub>W\<close> locale\<close>


subsection \<open>CDCL Rules\<close>
text \<open>Because of the strategy we will later use, we distinguish propagate, conflict from the other
  rules\<close>
locale conflict_driven_clause_learning\<^sub>W =
  state\<^sub>W
    \<comment> \<open>functions for the state: \<close>
      \<comment> \<open>access functions:\<close>
    trail init_clss learned_clss backtrack_lvl conflicting
      \<comment> \<open>changing state:\<close>
    cons_trail tl_trail add_learned_cls remove_cls update_backtrack_lvl
    update_conflicting

      \<comment> \<open>get state:\<close>
    init_state
  for
    trail :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" and
    init_clss :: "'st \<Rightarrow> 'v clauses" and
    learned_clss :: "'st \<Rightarrow> 'v clauses" and
    backtrack_lvl :: "'st \<Rightarrow> nat" and
    conflicting :: "'st \<Rightarrow> 'v clause option" and

    cons_trail :: "('v, 'v clause) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_learned_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_backtrack_lvl :: "nat \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conflicting :: "'v clause option \<Rightarrow> 'st \<Rightarrow> 'st" and

    init_state :: "'v clauses \<Rightarrow> 'st"
begin

inductive propagate :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
propagate_rule: "conflicting S = None \<Longrightarrow>
  E \<in># clauses S \<Longrightarrow>
  L \<in># E \<Longrightarrow>
  trail S \<Turnstile>as CNot (E - {#L#}) \<Longrightarrow>
  undefined_lit (trail S) L \<Longrightarrow>
  T \<sim> cons_trail (Propagated L E) S \<Longrightarrow>
  propagate S T"

inductive_cases propagateE: "propagate S T"

inductive conflict :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
conflict_rule: "
  conflicting S = None \<Longrightarrow>
  D \<in># clauses S \<Longrightarrow>
  trail S \<Turnstile>as CNot D \<Longrightarrow>
  T \<sim> update_conflicting (Some D) S \<Longrightarrow>
  conflict S T"

inductive_cases conflictE: "conflict S T"

inductive backtrack :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
backtrack_rule: "
  conflicting S = Some D \<Longrightarrow>
  L \<in># D \<Longrightarrow>
  (Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S)) \<Longrightarrow>
  get_level (trail S) L = backtrack_lvl S \<Longrightarrow>
  get_level (trail S) L = get_maximum_level (trail S) D \<Longrightarrow>
  get_maximum_level (trail S) (D - {#L#}) \<equiv> i \<Longrightarrow>
  get_level (trail S) K = i + 1 \<Longrightarrow>
  T \<sim> cons_trail (Propagated L D)
        (reduce_trail_to M1
          (add_learned_cls D
            (update_backtrack_lvl i
              (update_conflicting None S)))) \<Longrightarrow>
  backtrack S T"

inductive_cases backtrackE: "backtrack S T"
thm backtrackE

inductive decide :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
decide_rule:
  "conflicting S = None \<Longrightarrow>
  undefined_lit (trail S) L \<Longrightarrow>
  atm_of L \<in> atms_of_mm (init_clss S) \<Longrightarrow>
  T \<sim> cons_trail (Decided L) (incr_lvl S) \<Longrightarrow>
  decide S T"

inductive_cases decideE: "decide S T"

inductive skip :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
skip_rule:
  "trail S = Propagated L C' # M \<Longrightarrow>
   conflicting S = Some E \<Longrightarrow>
   -L \<notin># E \<Longrightarrow>
   E \<noteq> {#} \<Longrightarrow>
   T \<sim> tl_trail S \<Longrightarrow>
   skip S T"

inductive_cases skipE: "skip S T"

text \<open>@{term "get_maximum_level (Propagated L (C + {#L#}) # M) D = k \<or> k = 0"} (that was in a
  previous version of the book) is equivalent to
  @{term "get_maximum_level (Propagated L (C + {#L#}) # M) D = k"}, when the structural invariants
  holds.\<close>

inductive resolve :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
resolve_rule: "trail S \<noteq> [] \<Longrightarrow>
  hd_trail S = Propagated L E \<Longrightarrow>
  L \<in># E \<Longrightarrow>
  conflicting S = Some D' \<Longrightarrow>
  -L \<in># D' \<Longrightarrow>
  get_maximum_level (trail S) ((remove1_mset (-L) D')) = backtrack_lvl S \<Longrightarrow>
  T \<sim> update_conflicting (Some (resolve_cls L D' E))
    (tl_trail S) \<Longrightarrow>
  resolve S T"

inductive_cases resolveE: "resolve S T"

inductive restart :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
restart: "state S = (M, N, U, k, None) \<Longrightarrow>
  \<not>M \<Turnstile>asm clauses S \<Longrightarrow>
  U' \<subseteq># U \<Longrightarrow>
  state T = ([], N, U', 0, None) \<Longrightarrow>
  restart S T"

inductive_cases restartE: "restart S T"

text \<open>We add the condition @{term "C \<notin># init_clss S"}, to maintain consistency even without the
  strategy.\<close>
inductive forget :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
forget_rule:
  "conflicting S = None \<Longrightarrow>
  C \<in># learned_clss S \<Longrightarrow>
  \<not>(trail S) \<Turnstile>asm clauses S \<Longrightarrow>
  C \<notin> set (get_all_mark_of_propagated (trail S)) \<Longrightarrow>
  C \<notin># init_clss S \<Longrightarrow>
  T \<sim> remove_cls C S \<Longrightarrow>
  forget S T"

inductive_cases forgetE: "forget S T"

inductive cdcl\<^sub>W_rf :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
restart: "restart S T \<Longrightarrow> cdcl\<^sub>W_rf S T" |
forget: "forget S T \<Longrightarrow> cdcl\<^sub>W_rf S T"

inductive cdcl\<^sub>W_bj :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
skip: "skip S S' \<Longrightarrow> cdcl\<^sub>W_bj S S'" |
resolve: "resolve S S' \<Longrightarrow> cdcl\<^sub>W_bj S S'" |
backtrack: "backtrack S S' \<Longrightarrow> cdcl\<^sub>W_bj S S'"

inductive_cases cdcl\<^sub>W_bjE: "cdcl\<^sub>W_bj S T"

inductive cdcl\<^sub>W_o :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
decide: "decide S S' \<Longrightarrow> cdcl\<^sub>W_o S S'" |
bj: "cdcl\<^sub>W_bj S S' \<Longrightarrow> cdcl\<^sub>W_o S S'"

inductive cdcl\<^sub>W_restart :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
propagate: "propagate S S' \<Longrightarrow> cdcl\<^sub>W_restart S S'" |
conflict: "conflict S S' \<Longrightarrow> cdcl\<^sub>W_restart S S'" |
other: "cdcl\<^sub>W_o S S' \<Longrightarrow> cdcl\<^sub>W_restart S S'"|
rf: "cdcl\<^sub>W_rf S S' \<Longrightarrow> cdcl\<^sub>W_restart S S'"

lemma rtranclp_propagate_is_rtranclp_cdcl\<^sub>W_restart:
  "propagate\<^sup>*\<^sup>* S S' \<Longrightarrow> cdcl\<^sub>W_restart\<^sup>*\<^sup>* S S'"
  apply (induction rule: rtranclp_induct)
    apply (simp; fail)
  apply (frule propagate)
  using rtranclp_trans[of cdcl\<^sub>W_restart] by blast

inductive cdcl\<^sub>W :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
W_propagate: "propagate S S' \<Longrightarrow> cdcl\<^sub>W S S'" |
W_conflict: "conflict S S' \<Longrightarrow> cdcl\<^sub>W S S'" |
W_other: "cdcl\<^sub>W_o S S' \<Longrightarrow> cdcl\<^sub>W S S'"

lemma cdcl\<^sub>W_cdcl\<^sub>W_restart:
  "cdcl\<^sub>W S T \<Longrightarrow> cdcl\<^sub>W_restart S T"
  by (induction rule: cdcl\<^sub>W.induct) (auto intro: cdcl\<^sub>W_restart.intros)

lemma cdcl\<^sub>W_restart_all_rules_induct[consumes 1, case_names propagate conflict forget restart decide
    skip resolve backtrack]:
  fixes S :: "'st"
  assumes
    cdcl\<^sub>W_restart: "cdcl\<^sub>W_restart S S'" and
    propagate: "\<And>T. propagate S T \<Longrightarrow> P S T" and
    conflict: "\<And>T. conflict S T \<Longrightarrow> P S T" and
    forget: "\<And>T. forget S T \<Longrightarrow> P S T" and
    restart: "\<And>T. restart S T \<Longrightarrow> P S T" and
    decide: "\<And>T. decide S T \<Longrightarrow> P S T" and
    skip: "\<And>T. skip S T \<Longrightarrow> P S T" and
    resolve: "\<And>T. resolve S T \<Longrightarrow> P S T" and
    backtrack: "\<And>T. backtrack S T \<Longrightarrow> P S T"
  shows "P S S'"
  using assms(1)
proof (induct S' rule: cdcl\<^sub>W_restart.induct)
  case (propagate S') note propagate = this(1)
  then show ?case using assms(2) by auto
next
  case (conflict S')
  then show ?case using assms(3) by auto
next
  case (other S')
  then show ?case
    proof (induct rule: cdcl\<^sub>W_o.induct)
      case (decide U)
      then show ?case using assms(6) by auto
    next
      case (bj S')
      then show ?case using assms(7-9) by (induction rule: cdcl\<^sub>W_bj.induct) auto
    qed
next
  case (rf S')
  then show ?case
    by (induct rule: cdcl\<^sub>W_rf.induct) (fast dest: forget restart)+
qed

lemma cdcl\<^sub>W_restart_all_induct[consumes 1, case_names propagate conflict forget restart decide skip
    resolve backtrack]:
  fixes S :: "'st"
  assumes
    cdcl\<^sub>W_restart: "cdcl\<^sub>W_restart S S'" and
    propagateH: "\<And>C L T. conflicting S = None \<Longrightarrow>
       C \<in># clauses S \<Longrightarrow>
       L \<in># C \<Longrightarrow>
       trail S \<Turnstile>as CNot (remove1_mset L C) \<Longrightarrow>
       undefined_lit (trail S) L \<Longrightarrow>
       T \<sim> cons_trail (Propagated L C) S \<Longrightarrow>
       P S T" and
    conflictH: "\<And>D T. conflicting S = None \<Longrightarrow>
       D \<in># clauses S \<Longrightarrow>
       trail S \<Turnstile>as CNot D \<Longrightarrow>
       T \<sim> update_conflicting (Some D) S \<Longrightarrow>
       P S T" and
    forgetH: "\<And>C T. conflicting S = None \<Longrightarrow>
      C \<in># learned_clss S \<Longrightarrow>
      \<not>(trail S) \<Turnstile>asm clauses S \<Longrightarrow>
      C \<notin> set (get_all_mark_of_propagated (trail S)) \<Longrightarrow>
      C \<notin># init_clss S \<Longrightarrow>
      T \<sim> remove_cls C S \<Longrightarrow>
      P S T" and
    restartH: "\<And>T U. \<not>trail S \<Turnstile>asm clauses S \<Longrightarrow>
      conflicting S = None \<Longrightarrow>
      state T = ([], init_clss S, U, 0, None) \<Longrightarrow>
      U \<subseteq># learned_clss S \<Longrightarrow>
      P S T" and
    decideH: "\<And>L T. conflicting S = None \<Longrightarrow>
      undefined_lit (trail S) L \<Longrightarrow>
      atm_of L \<in> atms_of_mm (init_clss S) \<Longrightarrow>
      T \<sim> cons_trail (Decided L) (incr_lvl S) \<Longrightarrow>
      P S T" and
    skipH: "\<And>L C' M E T.
      trail S = Propagated L C' # M \<Longrightarrow>
      conflicting S = Some E \<Longrightarrow>
      -L \<notin># E \<Longrightarrow> E \<noteq> {#} \<Longrightarrow>
      T \<sim> tl_trail S \<Longrightarrow>
      P S T" and
    resolveH: "\<And>L E M D T.
      trail S = Propagated L E # M \<Longrightarrow>
      L \<in># E \<Longrightarrow>
      hd_trail S = Propagated L E \<Longrightarrow>
      conflicting S = Some D \<Longrightarrow>
      -L \<in># D \<Longrightarrow>
      get_maximum_level (trail S) ((remove1_mset (-L) D)) = backtrack_lvl S \<Longrightarrow>
      T \<sim> update_conflicting
        (Some (resolve_cls L D E)) (tl_trail S) \<Longrightarrow>
      P S T" and
    backtrackH: "\<And>L D K i M1 M2 T.
      conflicting S = Some D \<Longrightarrow>
      L \<in># D \<Longrightarrow>
      (Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S)) \<Longrightarrow>
      get_level (trail S) L = backtrack_lvl S \<Longrightarrow>
      get_level (trail S) L = get_maximum_level (trail S) D \<Longrightarrow>
      get_maximum_level (trail S) (remove1_mset L D) \<equiv> i \<Longrightarrow>
      get_level (trail S) K = i+1 \<Longrightarrow>
      T \<sim> cons_trail (Propagated L D)
            (reduce_trail_to M1
              (add_learned_cls D
                (update_backtrack_lvl i
                  (update_conflicting None S)))) \<Longrightarrow>
       P S T"
  shows "P S S'"
  using cdcl\<^sub>W_restart
proof (induct S S' rule: cdcl\<^sub>W_restart_all_rules_induct)
  case (propagate S')
  then show ?case
    by (auto elim!: propagateE intro!: propagateH)
next
  case (conflict S')
  then show ?case
    by (auto elim!: conflictE intro!: conflictH)
next
  case (restart S')
  then show ?case
    by (auto elim!: restartE intro!: restartH)
next
  case (decide T)
  then show ?case
    by (auto elim!: decideE intro!: decideH)
next
  case (backtrack S')
  then show ?case by (auto elim!: backtrackE intro!: backtrackH
    simp del: state_simp simp add: state_eq_def)
next
  case (forget S')
  then show ?case by (auto elim!: forgetE intro!: forgetH)
next
  case (skip S')
  then show ?case by (auto elim!: skipE intro!: skipH)
next
  case (resolve S')
  then show ?case
    by (cases "trail S") (auto elim!: resolveE intro!: resolveH)
qed

lemma cdcl\<^sub>W_o_induct[consumes 1, case_names decide skip resolve backtrack]:
  fixes S :: "'st"
  assumes cdcl\<^sub>W_restart: "cdcl\<^sub>W_o S T" and
    decideH: "\<And>L T. conflicting S = None \<Longrightarrow> undefined_lit (trail S) L
      \<Longrightarrow> atm_of L \<in> atms_of_mm (init_clss S)
      \<Longrightarrow> T \<sim> cons_trail (Decided L) (incr_lvl S)
      \<Longrightarrow> P S T" and
    skipH: "\<And>L C' M E T.
      trail S = Propagated L C' # M \<Longrightarrow>
      conflicting S = Some E \<Longrightarrow>
      -L \<notin># E \<Longrightarrow> E \<noteq> {#} \<Longrightarrow>
      T \<sim> tl_trail S \<Longrightarrow>
      P S T" and
    resolveH: "\<And>L E M D T.
      trail S = Propagated L E # M \<Longrightarrow>
      L \<in># E \<Longrightarrow>
      hd_trail S = Propagated L E \<Longrightarrow>
      conflicting S = Some D \<Longrightarrow>
      -L \<in># D \<Longrightarrow>
      get_maximum_level (trail S) ((remove1_mset (-L) D)) = backtrack_lvl S \<Longrightarrow>
      T \<sim> update_conflicting
        (Some (resolve_cls L D E)) (tl_trail S) \<Longrightarrow>
      P S T" and
    backtrackH: "\<And>L D K i M1 M2 T.
      conflicting S = Some D \<Longrightarrow>
      L \<in># D \<Longrightarrow>
      (Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S)) \<Longrightarrow>
      get_level (trail S) L = backtrack_lvl S \<Longrightarrow>
      get_level (trail S) L = get_maximum_level (trail S) D \<Longrightarrow>
      get_maximum_level (trail S) (remove1_mset L D) \<equiv> i \<Longrightarrow>
      get_level (trail S) K = i + 1 \<Longrightarrow>
      T \<sim> cons_trail (Propagated L D)
                (reduce_trail_to M1
                  (add_learned_cls D
                    (update_backtrack_lvl i
                      (update_conflicting None S)))) \<Longrightarrow>
       P S T"
  shows "P S T"
  using cdcl\<^sub>W_restart apply (induct T rule: cdcl\<^sub>W_o.induct)
   using assms(2) apply (auto elim: decideE)[1]
  apply (elim cdcl\<^sub>W_bjE skipE resolveE backtrackE)
    apply (frule skipH; simp; fail)
    apply (cases "trail S"; auto elim!: resolveE intro!: resolveH; fail)
  apply (frule backtrackH; simp; fail)
  done

lemma cdcl\<^sub>W_o_all_rules_induct[consumes 1, case_names decide backtrack skip resolve]:
  fixes S T :: 'st
  assumes
    "cdcl\<^sub>W_o S T" and
    "\<And>T. decide S T \<Longrightarrow> P S T" and
    "\<And>T. backtrack S T \<Longrightarrow> P S T" and
    "\<And>T. skip S T \<Longrightarrow> P S T" and
    "\<And>T. resolve S T \<Longrightarrow> P S T"
  shows "P S T"
  using assms by (induct T rule: cdcl\<^sub>W_o.induct) (auto simp: cdcl\<^sub>W_bj.simps)

lemma cdcl\<^sub>W_o_rule_cases[consumes 1, case_names decide backtrack skip resolve]:
  fixes S T :: 'st
  assumes
    "cdcl\<^sub>W_o S T" and
    "decide S T \<Longrightarrow> P" and
    "backtrack S T \<Longrightarrow> P" and
    "skip S T \<Longrightarrow> P" and
    "resolve S T \<Longrightarrow> P"
  shows P
  using assms by (auto simp: cdcl\<^sub>W_o.simps cdcl\<^sub>W_bj.simps)

subsection \<open>Structural Invariants\<close>
subsubsection \<open>Properties of the trail\<close>
text \<open>We here establish that:
  \<^item> the consistency of the trail;
  \<^item> the fact that there is no duplicate in the trail.\<close>
lemma backtrack_lit_skiped:
  assumes
    L: "get_level (trail S) L = backtrack_lvl S" and
    M1: "(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S))" and
    no_dup: "no_dup (trail S)" and
    bt_l: "backtrack_lvl S = length (filter is_decided (trail S))" and
    lev_K: "get_level (trail S) K = i + 1"
  shows "atm_of L \<notin> atm_of ` lits_of_l M1"
proof (rule ccontr)
  let ?M = "trail S"
  assume L_in_M1: "\<not>atm_of L \<notin> atm_of ` lits_of_l M1"
  obtain M2' where
    Mc: "trail S = M2' @ M2 @ Decided K # M1"
    using M1 by blast
  have 
    "atm_of L \<notin> atm_of ` lits_of_l M2'" and
    "atm_of L \<notin> atm_of ` lits_of_l M2" and
    "atm_of L \<noteq> atm_of K" and 
    Kc: "atm_of K \<notin> atm_of ` lits_of_l M2'" and
    KM2: "atm_of K \<notin> atm_of ` lits_of_l M2"
    using L_in_M1 no_dup unfolding Mc lits_of_def by force+
  then have g_M_eq_g_M1: "get_level ?M L = get_level M1 L"
    using L_in_M1 unfolding Mc by auto
  then have "get_level M1 L < Suc i"
    using count_decided_ge_get_level[of L M1] KM2 lev_K Kc unfolding Mc
    by (auto simp del: count_decided_ge_get_level)
  moreover have "Suc i \<le> backtrack_lvl S" using bt_l KM2 lev_K Kc unfolding Mc by (simp add: Mc)
  ultimately show False using L g_M_eq_g_M1 by auto
qed

lemma cdcl\<^sub>W_restart_distinctinv_1:
  assumes
    "cdcl\<^sub>W_restart S S'" and
    "no_dup (trail S)" and
    bt_lev: "backtrack_lvl S = count_decided (trail S)"
  shows "no_dup (trail S')"
  using assms
proof (induct rule: cdcl\<^sub>W_restart_all_induct)
  case (backtrack L D K i M1 M2 T) note decomp = this(3) and L = this(4) and lev_K = this(7) and
    T = this(8) and n_d = this(9)
  obtain c where Mc: "trail S = c @ M2 @ Decided K # M1"
    using decomp by auto
  have "no_dup (M2 @ Decided K # M1)"
    using Mc n_d by fastforce
  moreover have "atm_of L \<notin> atm_of ` lits_of_l M1"
    using backtrack_lit_skiped[of L S K M1 M2 i] L decomp lev_K n_d bt_lev by fast
  moreover then have "undefined_lit M1 L"
     by (simp add: defined_lit_map lits_of_def image_image)
  ultimately show ?case using decomp T n_d by (simp add: lits_of_def image_image)
qed (auto simp: defined_lit_map)

text \<open>\cwref{prop:prop:cdclconsis}{Item 1 page 81}\<close>
lemma cdcl\<^sub>W_restart_consistent_inv_2:
  assumes
    "cdcl\<^sub>W_restart S S'" and
    "no_dup (trail S)" and
    "backtrack_lvl S = count_decided (trail S)"
  shows "consistent_interp (lits_of_l (trail S'))"
  using cdcl\<^sub>W_restart_distinctinv_1[OF assms] distinct_consistent_interp by fast

lemma cdcl\<^sub>W_o_bt:
  assumes
    "cdcl\<^sub>W_o S S'" and
    "backtrack_lvl S = count_decided (trail S)" and
    n_d[simp]: "no_dup (trail S)"
  shows "backtrack_lvl S' = count_decided (trail S')"
  using assms
proof (induct rule: cdcl\<^sub>W_o_induct)
  case (backtrack L D K i M1 M2 T) note decomp = this(3) and levK = this(7) and T = this(8) and
  level = this(9)
  have [simp]: "trail (reduce_trail_to M1 S) = M1"
    using decomp by auto
  obtain c where M: "trail S = c @ M2 @ Decided K # M1" using decomp by auto
  moreover have "atm_of L \<notin> atm_of ` lits_of_l M1"
    using backtrack_lit_skiped[of L S K M1 M2 i] backtrack(4,8,9) levK decomp
    by (fastforce simp add: lits_of_def)
  moreover then have "undefined_lit M1 L"
     by (simp add: defined_lit_map lits_of_def image_image)
  moreover
    have "atm_of K \<notin> atm_of ` lits_of_l M1" and "atm_of K \<notin> atm_of ` lits_of_l c"
      and "atm_of K \<notin> atm_of ` lits_of_l M2"
      using T n_d levK unfolding M by (auto simp: lits_of_def)
  ultimately show ?case
    using T levK unfolding M by (auto dest!: append_cons_eq_upt_length)
qed auto

lemma cdcl\<^sub>W_rf_bt:
  assumes
    "cdcl\<^sub>W_rf S S'" and
    "backtrack_lvl S = count_decided (trail S)"
  shows "backtrack_lvl S' = count_decided (trail S')"
  using assms by (induct rule: cdcl\<^sub>W_rf.induct) (auto elim: restartE forgetE)

text \<open>\cwref{prop:prop:cdclbacktrack}{Item 7 page 81}\<close>
lemma cdcl\<^sub>W_restart_bt:
  assumes
    "cdcl\<^sub>W_restart S S'" and
    "backtrack_lvl S = count_decided (trail S)" and
    "no_dup (trail S)"
  shows "backtrack_lvl S' = count_decided (trail S')"
  using assms by (induct rule: cdcl\<^sub>W_restart.induct) (auto simp: cdcl\<^sub>W_o_bt cdcl\<^sub>W_rf_bt
    elim: conflictE propagateE)

text \<open>We write @{term "1+count_decided (trail S)"} instead of
  @{term "backtrack_lvl S"} to avoid non termination of rewriting.\<close>
definition cdcl\<^sub>W_M_level_inv :: "'st \<Rightarrow> bool" where
"cdcl\<^sub>W_M_level_inv S \<longleftrightarrow>
  consistent_interp (lits_of_l (trail S))
  \<and> no_dup (trail S)
  \<and> backtrack_lvl S = count_decided (trail S)"

lemma cdcl\<^sub>W_M_level_inv_decomp:
  assumes "cdcl\<^sub>W_M_level_inv S"
  shows
    "consistent_interp (lits_of_l (trail S))" and
    "no_dup (trail S)"
  using assms unfolding cdcl\<^sub>W_M_level_inv_def by fastforce+

lemma cdcl\<^sub>W_restart_consistent_inv:
  fixes S S' :: 'st
  assumes
    "cdcl\<^sub>W_restart S S'" and
    "cdcl\<^sub>W_M_level_inv S"
  shows "cdcl\<^sub>W_M_level_inv S'"
  using assms cdcl\<^sub>W_restart_consistent_inv_2 cdcl\<^sub>W_restart_distinctinv_1 cdcl\<^sub>W_restart_bt
  unfolding cdcl\<^sub>W_M_level_inv_def by meson+

lemma rtranclp_cdcl\<^sub>W_restart_consistent_inv:
  assumes
    "cdcl\<^sub>W_restart\<^sup>*\<^sup>* S S'" and
    "cdcl\<^sub>W_M_level_inv S"
  shows "cdcl\<^sub>W_M_level_inv S'"
  using assms by (induct rule: rtranclp_induct) (auto intro: cdcl\<^sub>W_restart_consistent_inv)

lemma tranclp_cdcl\<^sub>W_restart_consistent_inv:
  assumes
    "cdcl\<^sub>W_restart\<^sup>+\<^sup>+ S S'" and
    "cdcl\<^sub>W_M_level_inv S"
  shows "cdcl\<^sub>W_M_level_inv S'"
  using assms by (induct rule: tranclp_induct) (auto intro: cdcl\<^sub>W_restart_consistent_inv)

lemma cdcl\<^sub>W_M_level_inv_S0_cdcl\<^sub>W_restart[simp]:
  "cdcl\<^sub>W_M_level_inv (init_state N)"
  unfolding cdcl\<^sub>W_M_level_inv_def by auto

lemma cdcl\<^sub>W_M_level_inv_get_level_le_backtrack_lvl:
  assumes inv: "cdcl\<^sub>W_M_level_inv S"
  shows "get_level (trail S) L \<le> backtrack_lvl S"
  using inv unfolding cdcl\<^sub>W_M_level_inv_def
  by simp

lemma backtrack_ex_decomp:
  assumes
    M_l: "cdcl\<^sub>W_M_level_inv S" and
    i_S: "i < backtrack_lvl S"
  shows "\<exists>K M1 M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S)) \<and>
    get_level (trail S) K = Suc i"
proof -
  let ?M = "trail S"
  have "i < count_decided (trail S)"
    using i_S M_l by (auto simp: cdcl\<^sub>W_M_level_inv_def)
  then obtain c K c' where tr_S: "trail S = c @ Decided K # c'" and
    lev_K: "get_level (trail S) K = Suc i"
    using le_count_decided_decomp[of "trail S" i] M_l by (auto simp: cdcl\<^sub>W_M_level_inv_def)
  obtain M1 M2 where "(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S))"
    using Decided_cons_in_get_all_ann_decomposition_append_Decided_cons unfolding tr_S by fast
  then show ?thesis using lev_K by blast
qed

lemma backtrack_lvl_backtrack_decrease:
  assumes inv: "cdcl\<^sub>W_M_level_inv S" and bt: "backtrack S T"
  shows "backtrack_lvl T < backtrack_lvl S"
  using inv bt le_count_decided_decomp[of "trail S" "backtrack_lvl T"]
  unfolding cdcl\<^sub>W_M_level_inv_def
  by (fastforce elim!: backtrackE dest!: get_all_ann_decomposition_exists_prepend
    simp: append_assoc[of _ _ "_# _", symmetric] simp del: append_assoc)

subsubsection \<open>Compatibility with @{term state_eq}\<close>
lemma propagate_state_eq_compatible:
  assumes
    propa: "propagate S T" and
    SS': "S \<sim> S'" and
    TT': "T \<sim> T'"
  shows "propagate S' T'"
proof -
  obtain C L where
    conf: "conflicting S = None" and
    C: "C \<in># clauses S" and
    L: "L \<in># C" and
    tr: "trail S \<Turnstile>as CNot (remove1_mset L C)" and
    undef: "undefined_lit (trail S) L" and
    T: "T \<sim> cons_trail (Propagated L C) S"
  using propa by (elim propagateE) auto

  have C': "C \<in># clauses S'"
    using SS' C
    by (auto simp: state_eq_def clauses_def simp del: state_simp)

  show ?thesis
    apply (rule propagate_rule[of _ C])
    using state_eq_sym[of S S'] SS' conf C' L tr undef TT' T
    by (auto simp: state_eq_def simp del: state_simp)
qed

lemma conflict_state_eq_compatible:
  assumes
    confl: "conflict S T" and
    TT': "T \<sim> T'" and
    SS': "S \<sim> S'"
  shows "conflict S' T'"
proof -
  obtain D where
    conf: "conflicting S = None" and
    D: "D \<in># clauses S" and
    tr: " trail S \<Turnstile>as CNot D" and
    T: "T \<sim> update_conflicting (Some D) S"
  using confl by (elim conflictE) auto

  have D': "D \<in># clauses S'"
    using D SS' by fastforce

  show ?thesis
    apply (rule conflict_rule[of _ D])
    using state_eq_sym[of S S'] SS' conf D' tr TT' T
    by (auto simp: state_eq_def simp del: state_simp)
qed

lemma backtrack_state_eq_compatible:
  assumes
    bt: "backtrack S T" and
    SS': "S \<sim> S'" and
    TT': "T \<sim> T'" and
    inv: "cdcl\<^sub>W_M_level_inv S"
  shows "backtrack S' T'"
proof -
  obtain D L K i M1 M2 where
    conf: "conflicting S = Some D" and
    L: "L \<in># D" and
    decomp: "(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S))" and
    lev: "get_level (trail S) L = backtrack_lvl S" and
    max: "get_level (trail S) L = get_maximum_level (trail S) D" and
    max_D: "get_maximum_level (trail S) (remove1_mset L D) \<equiv> i" and
    lev_K: "get_level (trail S) K = Suc i" and
    T: "T \<sim> cons_trail (Propagated L D)
                (reduce_trail_to M1
                  (add_learned_cls D
                    (update_backtrack_lvl i
                      (update_conflicting None S))))"
  using bt inv by (elim backtrackE) metis
  have D': "conflicting S' = Some D"
    using SS' conf by (cases "conflicting S'") auto

  have T': "T' \<sim> cons_trail (Propagated L D)
     (reduce_trail_to M1 (add_learned_cls D
     (update_backtrack_lvl i (update_conflicting None S'))))"
    using TT' unfolding state_eq_def
    using decomp D' inv SS' T by (auto simp add: cdcl\<^sub>W_M_level_inv_def)

  show ?thesis
    apply (rule backtrack_rule[of _ D])
        apply (rule D')
       using state_eq_sym[of S S'] TT' SS' D' conf L decomp lev max max_D T
       apply (auto simp: state_eq_def simp del: state_simp)[]
      using decomp SS' lev SS' max_D max T' lev_K by (auto simp: state_eq_def simp del: state_simp)
qed

lemma decide_state_eq_compatible:
  assumes
    "decide S T" and
    "S \<sim> S'" and
    "T \<sim> T'"
  shows "decide S' T'"
  using assms apply (elim decideE)
  by (rule decide_rule) (auto simp: state_eq_def clauses_def simp del: state_simp)

lemma skip_state_eq_compatible:
  assumes
    skip: "skip S T" and
    SS': "S \<sim> S'" and
    TT': "T \<sim> T'"
  shows "skip S' T'"
proof -
  obtain L C' M E where
    tr: "trail S = Propagated L C' # M" and
    raw: "conflicting S = Some E" and
    L: "-L \<notin># E" and
    E: "E \<noteq> {#}" and
    T: "T \<sim> tl_trail S"
  using skip by (elim skipE) simp
  obtain E' where E': "conflicting S' = Some E'"
    using SS' raw by (cases "conflicting S'") (auto simp: state_eq_def simp del: state_simp)
  show ?thesis
    apply (rule skip_rule)
       using tr raw L E T SS' apply (auto simp: simp del: )[]
      using E' apply simp
     using E' SS' L raw E apply (auto simp: state_eq_def simp del: state_simp)[2]
    using T TT' SS' by (auto simp: state_eq_def simp del: state_simp)
qed

lemma resolve_state_eq_compatible:
  assumes
    res: "resolve S T" and
    TT': "T \<sim> T'" and
    SS': "S \<sim> S'"
  shows "resolve S' T'"
proof -
  obtain E D L where
    tr: "trail S \<noteq> []" and
    hd: "hd_trail S = Propagated L E" and
    L: "L \<in># E" and
    raw: "conflicting S = Some D" and
    LD: "-L \<in># D" and
    i: "get_maximum_level (trail S) ((remove1_mset (-L) D)) = backtrack_lvl S" and
    T: "T \<sim> update_conflicting (Some (resolve_cls L D E)) (tl_trail S)"
  using assms by (elim resolveE) simp

  obtain D' where
    D': "conflicting S' = Some D'"
    using SS' raw by fastforce
  have [simp]: "D = D'"
    using D' SS' raw state_simp(5) by fastforce
  have T'T: "T' \<sim> T"
    using TT' state_eq_sym by auto
  show ?thesis
    apply (rule resolve_rule)
           using tr SS' apply simp
          using hd SS' apply simp
         using L apply simp
        using D' apply simp
       using D' SS' raw LD apply (auto simp add: state_eq_def simp del: state_simp)[]
      using D' SS' raw LD apply (auto simp add: state_eq_def simp del: state_simp)[]
     using raw SS' i apply (auto simp add: state_eq_def simp del: state_simp)[]
    using T T'T SS' by (auto simp: state_eq_def simp del: state_simp )
qed

lemma forget_state_eq_compatible:
  assumes
    forget: "forget S T" and
    SS': "S \<sim> S'" and
    TT': "T \<sim> T'"
  shows "forget S' T'"
proof -
  obtain C where
    conf: "conflicting S = None" and
    C: "C \<in># learned_clss S" and
    tr: "\<not>(trail S) \<Turnstile>asm clauses S" and
    C1: "C \<notin> set (get_all_mark_of_propagated (trail S))" and
    C2: "C \<notin># init_clss S" and
    T: "T \<sim> remove_cls C S"
    using forget by (elim forgetE) simp

  show ?thesis
    apply (rule forget_rule)
         using SS' conf apply simp
        using C SS' apply simp
       using SS' tr apply simp
      using SS' C1 apply simp
     using SS' C2 apply simp
    using T TT' SS' by (auto simp: state_eq_def simp del: state_simp)
qed

lemma cdcl\<^sub>W_restart_state_eq_compatible:
  assumes
    "cdcl\<^sub>W_restart S T" and "\<not>restart S T" and
    "S \<sim> S'"
    "T \<sim> T'" and
    "cdcl\<^sub>W_M_level_inv S"
  shows "cdcl\<^sub>W_restart S' T'"
  using assms by (meson backtrack backtrack_state_eq_compatible bj cdcl\<^sub>W_restart.simps cdcl\<^sub>W_o_rule_cases
    cdcl\<^sub>W_rf.cases conflict_state_eq_compatible decide decide_state_eq_compatible forget
    forget_state_eq_compatible propagate_state_eq_compatible resolve resolve_state_eq_compatible
    skip skip_state_eq_compatible state_eq_ref)

lemma cdcl\<^sub>W_bj_state_eq_compatible:
  assumes
    "cdcl\<^sub>W_bj S T" and "cdcl\<^sub>W_M_level_inv S"
    "T \<sim> T'"
  shows "cdcl\<^sub>W_bj S T'"
  using assms by (meson backtrack backtrack_state_eq_compatible cdcl\<^sub>W_bjE resolve
    resolve_state_eq_compatible skip skip_state_eq_compatible state_eq_ref)

lemma tranclp_cdcl\<^sub>W_bj_state_eq_compatible:
  assumes
    "cdcl\<^sub>W_bj\<^sup>+\<^sup>+ S T" and inv: "cdcl\<^sub>W_M_level_inv S" and
    "S \<sim> S'" and
    "T \<sim> T'"
  shows "cdcl\<^sub>W_bj\<^sup>+\<^sup>+ S' T'"
  using assms
proof (induction arbitrary: S' T')
  case base
  then show ?case
    unfolding tranclp_unfold_end by (meson backtrack_state_eq_compatible cdcl\<^sub>W_bj.simps
      resolve_state_eq_compatible rtranclp_unfold skip_state_eq_compatible)
next
  case (step T U) note IH = this(3)[OF this(4-5)]
  have "cdcl\<^sub>W_restart\<^sup>+\<^sup>+ S T"
    using tranclp_mono[of cdcl\<^sub>W_bj cdcl\<^sub>W_restart] step.hyps(1) cdcl\<^sub>W_restart.other cdcl\<^sub>W_o.bj by blast
  then have "cdcl\<^sub>W_M_level_inv T"
    using inv tranclp_cdcl\<^sub>W_restart_consistent_inv by blast
  then have "cdcl\<^sub>W_bj\<^sup>+\<^sup>+ T T'"
    using \<open>U \<sim> T'\<close> cdcl\<^sub>W_bj_state_eq_compatible[of T U] \<open>cdcl\<^sub>W_bj T U\<close> by auto
  then show ?case
    using IH[of T] by auto
qed

subsubsection \<open>Conservation of some Properties\<close>
lemma cdcl\<^sub>W_o_no_more_init_clss:
  assumes
    "cdcl\<^sub>W_o S S'" and
    inv: "cdcl\<^sub>W_M_level_inv S"
  shows "init_clss S = init_clss S'"
  using assms by (induct rule: cdcl\<^sub>W_o_induct) (auto simp: inv cdcl\<^sub>W_M_level_inv_decomp)

lemma tranclp_cdcl\<^sub>W_o_no_more_init_clss:
  assumes
    "cdcl\<^sub>W_o\<^sup>+\<^sup>+ S S'" and
    inv: "cdcl\<^sub>W_M_level_inv S"
  shows "init_clss S = init_clss S'"
  using assms apply (induct rule: tranclp.induct)
  by (auto dest: cdcl\<^sub>W_o_no_more_init_clss
    dest!: tranclp_cdcl\<^sub>W_restart_consistent_inv dest: tranclp_mono_explicit[of cdcl\<^sub>W_o _ _ cdcl\<^sub>W_restart]
    simp: other)

lemma rtranclp_cdcl\<^sub>W_o_no_more_init_clss:
  assumes
    "cdcl\<^sub>W_o\<^sup>*\<^sup>* S S'" and
    inv: "cdcl\<^sub>W_M_level_inv S"
  shows "init_clss S = init_clss S'"
  using assms unfolding rtranclp_unfold by (auto intro: tranclp_cdcl\<^sub>W_o_no_more_init_clss)

lemma cdcl\<^sub>W_restart_init_clss:
  assumes
    "cdcl\<^sub>W_restart S T" and
    inv: "cdcl\<^sub>W_M_level_inv S"
  shows "init_clss S = init_clss T"
  using assms by (induction rule: cdcl\<^sub>W_restart_all_induct)
  (auto simp: inv cdcl\<^sub>W_M_level_inv_decomp not_in_iff)

lemma rtranclp_cdcl\<^sub>W_restart_init_clss:
  "cdcl\<^sub>W_restart\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W_M_level_inv S \<Longrightarrow> init_clss S = init_clss T"
  by (induct rule: rtranclp_induct) (auto dest: cdcl\<^sub>W_restart_init_clss rtranclp_cdcl\<^sub>W_restart_consistent_inv)

lemma tranclp_cdcl\<^sub>W_restart_init_clss:
  "cdcl\<^sub>W_restart\<^sup>+\<^sup>+ S T \<Longrightarrow> cdcl\<^sub>W_M_level_inv S \<Longrightarrow> init_clss S = init_clss T"
  using rtranclp_cdcl\<^sub>W_restart_init_clss[of S T] unfolding rtranclp_unfold by auto

subsubsection \<open>Learned Clause\<close>
text \<open>This invariant shows that:
  \<^item> the learned clauses are entailed by the initial set of clauses.
  \<^item> the conflicting clause is entailed by the initial set of clauses.
  \<^item> the marks are entailed by the clauses.\<close>

definition "cdcl\<^sub>W_learned_clause (S :: 'st) \<longleftrightarrow>
  (init_clss S \<Turnstile>psm learned_clss S
  \<and> (\<forall>T. conflicting S = Some T \<longrightarrow> init_clss S \<Turnstile>pm T)
  \<and> set (get_all_mark_of_propagated (trail S)) \<subseteq> set_mset (clauses S))"

text \<open>\cwref{prop:prop:cdclConflClause}{} for the inital state and some additional structural
  properties about the trail.\<close>
lemma cdcl\<^sub>W_learned_clause_S0_cdcl\<^sub>W_restart[simp]:
   "cdcl\<^sub>W_learned_clause (init_state N)"
  unfolding cdcl\<^sub>W_learned_clause_def by auto

text \<open>\cwref{prop:prop:cdclvaluation}{Item 4 page 81}\<close>
lemma cdcl\<^sub>W_restart_learned_clss:
  assumes
    "cdcl\<^sub>W_restart S S'" and
    learned: "cdcl\<^sub>W_learned_clause S" and
    lev_inv: "cdcl\<^sub>W_M_level_inv S"
  shows "cdcl\<^sub>W_learned_clause S'"
  using assms(1) lev_inv learned
proof (induct rule: cdcl\<^sub>W_restart_all_induct)
  case (backtrack K i M1 M2 L D T) note decomp = this(3) and confl = this(1) and lev_K = this (7) and
    undef = this(8) and T = this(9)
  show ?case
    using decomp confl learned undef T lev_K unfolding cdcl\<^sub>W_learned_clause_def
    by (auto dest!: get_all_ann_decomposition_exists_prepend
      simp: clauses_def lev_inv cdcl\<^sub>W_M_level_inv_decomp dest: true_clss_clss_left_right)
next
  case (resolve L C M D) note trail = this(1) and CL = this(2) and confl = this(4) and DL = this(5)
    and lvl = this(6) and T = this(7)
  moreover
    have "init_clss S \<Turnstile>psm learned_clss S"
      using learned trail unfolding cdcl\<^sub>W_learned_clause_def clauses_def by auto
    then have "init_clss S \<Turnstile>pm C + {#L#}"
      using trail learned unfolding cdcl\<^sub>W_learned_clause_def clauses_def
      by (auto dest: true_clss_clss_in_imp_true_clss_cls)
  moreover have "remove1_mset (- L) D + {#- L#} = D"
    using DL by (auto simp: multiset_eq_iff)
  moreover have "remove1_mset L C + {#L#} = C"
    using CL by (auto simp: multiset_eq_iff)
  ultimately show ?case
    using learned T
    by (auto dest: mk_disjoint_insert
      simp add: cdcl\<^sub>W_learned_clause_def clauses_def
      intro!: true_clss_cls_union_mset_true_clss_cls_or_not_true_clss_cls_or[of _ _ L])
next
  case (restart T)
  then show ?case
    using learned
    by (auto
      simp: clauses_def state_eq_def cdcl\<^sub>W_learned_clause_def
      simp del: state_simp
      dest: true_clss_clssm_subsetE)
next
  case propagate
  then show ?case using learned by (auto simp: cdcl\<^sub>W_learned_clause_def)
next
  case conflict
  then show ?case using learned
    by (fastforce simp: cdcl\<^sub>W_learned_clause_def clauses_def
      true_clss_clss_in_imp_true_clss_cls)
next
  case (forget U)
  then show ?case using learned
    by (auto simp: cdcl\<^sub>W_learned_clause_def clauses_def split: if_split_asm)
qed (auto simp: cdcl\<^sub>W_learned_clause_def clauses_def)

lemma rtranclp_cdcl\<^sub>W_restart_learned_clss:
  assumes
    "cdcl\<^sub>W_restart\<^sup>*\<^sup>* S S'" and
    "cdcl\<^sub>W_M_level_inv S"
    "cdcl\<^sub>W_learned_clause S"
  shows "cdcl\<^sub>W_learned_clause S'"
  using assms by induction (auto dest: cdcl\<^sub>W_restart_learned_clss intro: rtranclp_cdcl\<^sub>W_restart_consistent_inv)


subsubsection \<open>No alien atom in the state\<close>
text \<open>This invariant means that all the literals are in the set of clauses. These properties are
  implicit in Weidenbach's book.\<close>
definition "no_strange_atm S' \<longleftrightarrow> (
    (\<forall>T. conflicting S' = Some T \<longrightarrow> atms_of T \<subseteq> atms_of_mm (init_clss S'))
  \<and> (\<forall>L mark. Propagated L mark \<in> set (trail S')
      \<longrightarrow> atms_of mark \<subseteq> atms_of_mm (init_clss S'))
  \<and> atms_of_mm (learned_clss S') \<subseteq> atms_of_mm (init_clss S')
  \<and> atm_of ` (lits_of_l (trail S')) \<subseteq> atms_of_mm (init_clss S'))"

lemma no_strange_atm_decomp:
  assumes "no_strange_atm S"
  shows "conflicting S = Some T \<Longrightarrow> atms_of T \<subseteq> atms_of_mm (init_clss S)"
  and "(\<forall>L mark. Propagated L mark \<in> set (trail S)
    \<longrightarrow> atms_of mark \<subseteq> atms_of_mm (init_clss S))"
  and "atms_of_mm (learned_clss S) \<subseteq> atms_of_mm (init_clss S)"
  and "atm_of ` (lits_of_l (trail S)) \<subseteq> atms_of_mm (init_clss S)"
  using assms unfolding no_strange_atm_def by blast+

lemma no_strange_atm_S0 [simp]: "no_strange_atm (init_state N)"
  unfolding no_strange_atm_def by auto

lemma in_atms_of_implies_atm_of_on_atms_of_ms:
  "C + {#L#} \<in># A \<Longrightarrow> x \<in> atms_of C \<Longrightarrow> x \<in> atms_of_mm A"
  using multi_member_split by fastforce

lemma propagate_no_strange_atm_inv:
  assumes
    "propagate S T" and
    alien: "no_strange_atm S"
  shows "no_strange_atm T"
  using assms(1)
proof (induction)
  case (propagate_rule C L T) note confl = this(1) and C = this(2) and C_L = this(3) and
    tr = this(4) and undef = this(5) and T = this(6)
  have atm_CL: "atms_of C \<subseteq> atms_of_mm (init_clss S)"
    using C alien unfolding no_strange_atm_def
    by (auto simp: clauses_def atms_of_ms_def)
  show ?case
    unfolding no_strange_atm_def
    proof (intro conjI allI impI, goal_cases)
      case 1
      then show ?case
        using confl T undef by auto
    next
      case (2 L' mark')
      then show ?case
        using C_L T alien undef atm_CL unfolding no_strange_atm_def clauses_def by (auto 5 5)
    next
      case (3)
      show ?case using T alien undef unfolding no_strange_atm_def by auto
    next
      case (4)
      show ?case
        using T alien undef C_L atm_CL unfolding no_strange_atm_def by (auto simp: atms_of_def)
    qed
qed

lemma in_atms_of_remove1_mset_in_atms_of:
  "x \<in> atms_of (remove1_mset L C) \<Longrightarrow> x \<in> atms_of C"
  using in_diffD unfolding atms_of_def by fastforce

lemma atms_of_ms_learned_clss_restart_state_in_atms_of_ms_learned_clssI:
  "atms_of_mm (learned_clss S) \<subseteq> atms_of_mm (init_clss S) \<Longrightarrow>
   x \<in> atms_of_mm (learned_clss T) \<Longrightarrow>
   learned_clss T \<subseteq># learned_clss S \<Longrightarrow>
   x \<in> atms_of_mm (init_clss S)"
  by (meson atms_of_ms_mono contra_subsetD set_mset_mono)

lemma cdcl\<^sub>W_restart_no_strange_atm_explicit:
  assumes
    "cdcl\<^sub>W_restart S S'" and
    lev: "cdcl\<^sub>W_M_level_inv S" and
    conf: "\<forall>T. conflicting S = Some T \<longrightarrow> atms_of T \<subseteq> atms_of_mm (init_clss S)" and
    decided: "\<forall>L mark. Propagated L mark \<in> set (trail S)
      \<longrightarrow> atms_of mark \<subseteq> atms_of_mm (init_clss S)" and
    learned: "atms_of_mm (learned_clss S) \<subseteq> atms_of_mm (init_clss S)" and
    trail: "atm_of ` (lits_of_l (trail S)) \<subseteq> atms_of_mm (init_clss S)"
  shows
    "(\<forall>T. conflicting S' = Some T \<longrightarrow> atms_of T \<subseteq> atms_of_mm (init_clss S')) \<and>
    (\<forall>L mark. Propagated L mark \<in> set (trail S')
      \<longrightarrow> atms_of mark \<subseteq> atms_of_mm (init_clss S')) \<and>
    atms_of_mm (learned_clss S') \<subseteq> atms_of_mm (init_clss S') \<and>
    atm_of ` (lits_of_l (trail S')) \<subseteq> atms_of_mm (init_clss S')"
    (is "?C S' \<and> ?M S' \<and> ?U S' \<and> ?V S'")
  using assms(1,2)
proof (induct rule: cdcl\<^sub>W_restart_all_induct)
  case (propagate C L T) note confl = this(1) and C_L = this(2) and tr = this(3) and undef = this(4)
  and T = this(5)
  show ?case
    using propagate_rule[OF propagate.hyps(1-3) _ propagate.hyps(5,6), simplified]
    propagate.hyps(4) propagate_no_strange_atm_inv[of S T]
    conf decided learned trail unfolding no_strange_atm_def by presburger
next
  case (decide L)
  then show ?case using learned decided conf trail unfolding clauses_def by auto
next
  case (skip L C M D)
  then show ?case using learned decided conf trail by auto
next
  case (conflict D T) note D_S = this(2) and T = this(4)
  have D: "atm_of ` set_mset D \<subseteq> \<Union>(atms_of ` (set_mset (clauses S)))"
    using D_S by (auto simp add: atms_of_def atms_of_ms_def)
  moreover {
    fix xa :: "'v literal"
    assume a1: "atm_of ` set_mset D \<subseteq> (\<Union>x\<in>set_mset (init_clss S). atms_of x)
      \<union> (\<Union>x\<in>set_mset (learned_clss S). atms_of x)"
    assume a2: "
      (\<Union>x\<in>set_mset (learned_clss S). atms_of x) \<subseteq> (\<Union>x\<in>set_mset (init_clss S). atms_of x)"
    assume "xa \<in># D"
    then have "atm_of xa \<in> UNION (set_mset (init_clss S)) atms_of"
      using a2 a1 by (metis (no_types) Un_iff atm_of_lit_in_atms_of atms_of_def subset_Un_eq)
    then have "\<exists>m\<in>set_mset (init_clss S). atm_of xa \<in> atms_of m"
      by blast
    } note H = this
  ultimately show ?case using conflict.prems T learned decided conf trail
    unfolding atms_of_def atms_of_ms_def clauses_def
    by (auto simp add: H)
next
  case (restart T)
  then show ?case using learned decided conf trail
    by (auto intro: atms_of_ms_learned_clss_restart_state_in_atms_of_ms_learned_clssI)
next
  case (forget C T) note confl = this(1) and C = this(4) and C_le = this(5) and
    T = this(6)
  have H: "\<And>L mark. Propagated L mark \<in> set (trail S) \<Longrightarrow> atms_of mark \<subseteq> atms_of_mm (init_clss S)"
    using decided by simp
  show ?case unfolding clauses_def apply (intro conjI)
       using conf confl T trail C unfolding clauses_def apply (auto dest!: H)[]
      using T trail C C_le apply (auto dest!: H)[]
     using T learned C_le atms_of_ms_remove_subset[of "set_mset (learned_clss S)"] apply auto[]
   using T trail C_le apply (auto simp: clauses_def lits_of_def)[]
   done
next
  case (backtrack L D K i M1 M2 T) note confl = this(1) and LD = this(2) and decomp = this(3) and
    lev_K = this(7) and T = this(8)
  have "?C T"
    using conf T decomp lev lev_K by (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
  moreover have "set M1 \<subseteq> set (trail S)"
    using decomp by auto
  then have M: "?M T"
    using decided conf confl T decomp lev lev_K
    by (auto simp: image_subset_iff clauses_def cdcl\<^sub>W_M_level_inv_decomp)
  moreover have "?U T"
    using learned decomp conf confl T lev lev_K unfolding clauses_def
    by (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
  moreover have "?V T"
    using M conf confl trail T decomp lev LD lev_K
    by (auto simp: cdcl\<^sub>W_M_level_inv_decomp atms_of_def
      dest!: get_all_ann_decomposition_exists_prepend)
  ultimately show ?case by blast
next
  case (resolve L C M D T) note trail_S = this(1) and confl = this(4) and T = this(7)
  let ?T = "update_conflicting (Some (resolve_cls L D C)) (tl_trail S)"
  have "?C ?T"
    using confl trail_S conf decided by (auto dest!: in_atms_of_remove1_mset_in_atms_of)
  moreover have "?M ?T"
    using confl trail_S conf decided by auto
  moreover have "?U ?T"
    using trail learned by auto
  moreover have "?V ?T"
    using confl trail_S trail by auto
  ultimately show ?case using T by simp
qed

lemma cdcl\<^sub>W_restart_no_strange_atm_inv:
  assumes "cdcl\<^sub>W_restart S S'" and "no_strange_atm S" and "cdcl\<^sub>W_M_level_inv S"
  shows "no_strange_atm S'"
  using cdcl\<^sub>W_restart_no_strange_atm_explicit[OF assms(1)] assms(2,3) unfolding no_strange_atm_def by fast

lemma rtranclp_cdcl\<^sub>W_restart_no_strange_atm_inv:
  assumes "cdcl\<^sub>W_restart\<^sup>*\<^sup>* S S'" and "no_strange_atm S" and "cdcl\<^sub>W_M_level_inv S"
  shows "no_strange_atm S'"
  using assms by induction (auto intro: cdcl\<^sub>W_restart_no_strange_atm_inv rtranclp_cdcl\<^sub>W_restart_consistent_inv)

subsubsection \<open>No Duplicates all Around\<close>
text \<open>This invariant shows that there is no duplicate (no literal appearing twice in the formula).
  The last part could be proven using the previous invariant also. Remark that we will show later
  that there cannot be duplicate \<^emph>\<open>clause\<close>.\<close>
definition "distinct_cdcl\<^sub>W_state (S ::'st)
  \<longleftrightarrow> ((\<forall>T. conflicting S = Some T \<longrightarrow> distinct_mset T)
    \<and> distinct_mset_mset (learned_clss S)
    \<and> distinct_mset_mset (init_clss S)
    \<and> (\<forall>L mark. (Propagated L mark \<in> set (trail S) \<longrightarrow> distinct_mset mark)))"

lemma distinct_cdcl\<^sub>W_state_decomp:
  assumes "distinct_cdcl\<^sub>W_state (S ::'st)"
  shows
    "\<forall>T. conflicting S = Some T \<longrightarrow> distinct_mset T" and
    "distinct_mset_mset (learned_clss S)" and
    "distinct_mset_mset (init_clss S)" and
    "\<forall>L mark. (Propagated L mark \<in> set (trail S) \<longrightarrow> distinct_mset mark)"
  using assms unfolding distinct_cdcl\<^sub>W_state_def by blast+

lemma distinct_cdcl\<^sub>W_state_decomp_2:
  assumes "distinct_cdcl\<^sub>W_state (S ::'st)" and "conflicting S = Some T"
  shows "distinct_mset T"
  using assms unfolding distinct_cdcl\<^sub>W_state_def by auto

lemma distinct_cdcl\<^sub>W_state_S0_cdcl\<^sub>W_restart[simp]:
  "distinct_mset_mset N \<Longrightarrow> distinct_cdcl\<^sub>W_state (init_state N)"
  unfolding distinct_cdcl\<^sub>W_state_def by auto

lemma distinct_cdcl\<^sub>W_state_inv:
  assumes
    "cdcl\<^sub>W_restart S S'" and
    lev_inv: "cdcl\<^sub>W_M_level_inv S" and
    "distinct_cdcl\<^sub>W_state S"
  shows "distinct_cdcl\<^sub>W_state S'"
  using assms(1,2,2,3)
proof (induct rule: cdcl\<^sub>W_restart_all_induct)
  case (backtrack L D K i M1 M2)
  then show ?case
    using lev_inv unfolding distinct_cdcl\<^sub>W_state_def
    by (auto dest: get_all_ann_decomposition_incl simp: cdcl\<^sub>W_M_level_inv_decomp)
next
  case restart
  then show ?case
    unfolding distinct_cdcl\<^sub>W_state_def distinct_mset_set_def clauses_def by auto
next
  case resolve
  then show ?case
    by (auto simp add: distinct_cdcl\<^sub>W_state_def distinct_mset_set_def clauses_def
      distinct_mset_single_add
      intro!: distinct_mset_union_mset)
qed (auto simp: distinct_cdcl\<^sub>W_state_def distinct_mset_set_def clauses_def
  dest!: in_diffD)

lemma rtanclp_distinct_cdcl\<^sub>W_state_inv:
  assumes
    "cdcl\<^sub>W_restart\<^sup>*\<^sup>* S S'" and
    "cdcl\<^sub>W_M_level_inv S" and
    "distinct_cdcl\<^sub>W_state S"
  shows "distinct_cdcl\<^sub>W_state S'"
  using assms apply (induct rule: rtranclp_induct)
  using distinct_cdcl\<^sub>W_state_inv rtranclp_cdcl\<^sub>W_restart_consistent_inv by blast+


subsubsection \<open>Conflicts and Annotations\<close>
text \<open>This invariant shows that each mark contains a contradiction only related to the previously
  defined variable.\<close>
abbreviation every_mark_is_a_conflict :: "'st \<Rightarrow> bool" where
"every_mark_is_a_conflict S \<equiv>
 \<forall>L mark a b. a @ Propagated L mark # b = (trail S)
   \<longrightarrow> (b \<Turnstile>as CNot (mark - {#L#}) \<and> L \<in># mark)"

definition "cdcl\<^sub>W_conflicting S \<longleftrightarrow>
  (\<forall>T. conflicting S = Some T \<longrightarrow> trail S \<Turnstile>as CNot T)
  \<and> every_mark_is_a_conflict S"

lemma backtrack_atms_of_D_in_M1:
  fixes M1 :: "('v, 'v clause) ann_lits"
  assumes
    inv: "cdcl\<^sub>W_M_level_inv S" and
    i: "get_maximum_level (trail S) ((remove1_mset L D)) \<equiv> i" and
    decomp: "(Decided K # M1, M2)
       \<in> set (get_all_ann_decomposition (trail S))" and
    S_lvl: "backtrack_lvl S = get_maximum_level (trail S) D" and
    S_confl: "conflicting S = Some D" and
    lev_K: "get_level (trail S) K = Suc i" and
    T: "T \<sim> cons_trail (Propagated L D)
                (reduce_trail_to M1
                  (add_learned_cls D
                    (update_backtrack_lvl i
                      (update_conflicting None S))))" and
    confl: "\<forall>T. conflicting S = Some T \<longrightarrow> trail S \<Turnstile>as CNot T"
  shows "atms_of ((remove1_mset L D)) \<subseteq> atm_of ` lits_of_l (tl (trail T))"
proof (rule ccontr)
  let ?k = "get_maximum_level (trail S) D"
  let ?D' = "remove1_mset L D"
  have "trail S \<Turnstile>as CNot D" using confl S_confl by auto
  then have vars_of_D: "atms_of D \<subseteq> atm_of ` lits_of_l (trail S)" unfolding atms_of_def
    by (meson image_subsetI true_annots_CNot_all_atms_defined)

  obtain M0 where M: "trail S = M0 @ M2 @ Decided K # M1"
    using decomp by auto

  have max: "?k = count_decided (M0 @ M2 @ Decided K # M1)"
    using inv unfolding cdcl\<^sub>W_M_level_inv_def S_lvl M by simp
  assume a: "\<not> ?thesis"
  then obtain L' where
    L': "L' \<in> atms_of ?D'" and
    L'_notin_M1: "L' \<notin> atm_of ` lits_of_l M1"
    using T decomp inv by (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
  then have L'_in: "L' \<in> atm_of ` lits_of_l (M0 @ M2 @ Decided K # [])"
    using vars_of_D unfolding M by (auto dest: in_atms_of_remove1_mset_in_atms_of)
  then obtain L'' where
    "L'' \<in># ?D'" and
    L'': "L' = atm_of L''"
    using L' L'_notin_M1 unfolding atms_of_def by auto
  have "atm_of K \<notin> atm_of ` lits_of_l (M0 @ M2)"
    using inv by (auto simp: cdcl\<^sub>W_M_level_inv_def M lits_of_def)
  then have "count_decided M1 = i"
    using lev_K unfolding M by (auto simp: image_Un)
  then have lev_L'':
    "get_level (trail S) L'' = get_level (M0 @ M2 @ Decided K # []) L'' + i"
    using L'_notin_M1 L'' get_rev_level_skip_end[OF L'_in[unfolded L''], of M1] M by auto
  moreover
    consider
      (M0) "L' \<in> atm_of ` lits_of_l M0" |
      (M2) "L' \<in> atm_of ` lits_of_l M2" |
      (K) "L' = atm_of K"
      using inv L'_in unfolding L'' by (auto simp: cdcl\<^sub>W_M_level_inv_def)
    then have "get_level (M0 @ M2 @ Decided K # []) L'' \<ge> Suc 0"
      proof cases
        case M0
        then have "L' \<noteq> atm_of K"
          using inv \<open>atm_of K \<notin> atm_of ` lits_of_l (M0 @ M2)\<close> unfolding L'' by auto
        then show ?thesis using M0 unfolding L'' by auto
      next
        case M2
        then have "L' \<notin> atm_of ` lits_of_l (M0 @ Decided K # [])"
          using inv \<open>atm_of K \<notin> atm_of ` lits_of_l (M0 @ M2)\<close> unfolding L''
          by (auto simp: M cdcl\<^sub>W_M_level_inv_def atm_lit_of_set_lits_of_l)
        then show ?thesis using M2 unfolding L'' by (auto simp: image_Un)
      next
        case K
        then have "L' \<notin> atm_of ` lits_of_l (M0 @ M2)"
          using inv unfolding L'' by (auto simp: cdcl\<^sub>W_M_level_inv_def atm_lit_of_set_lits_of_l M)
        then show ?thesis using K unfolding L'' by (auto simp: image_Un)
      qed
  ultimately have "get_level (trail S) L'' \<ge> i + 1"
    using lev_L'' unfolding M by simp
  then have "get_maximum_level (trail S) ?D' \<ge> i + 1"
    using get_maximum_level_ge_get_level[OF \<open>L'' \<in># ?D'\<close>, of "trail S"] by auto
  then show False using i by auto
qed

lemma distinct_atms_of_incl_not_in_other:
  assumes
    a1: "no_dup (M @ M')" and
    a2: "atms_of D \<subseteq> atm_of ` lits_of_l M'" and
    a3: "x \<in> atms_of D"
  shows "x \<notin> atm_of ` lits_of_l M"
proof -
  have ff1: "\<And>l ms. undefined_lit ms l \<or> atm_of l
    \<in> set (map (\<lambda>m. atm_of (lit_of (m ::('a, 'b) ann_lit))) ms)"
    by (simp add: defined_lit_map)
  have ff2: "\<And>a. a \<notin> atms_of D \<or> a \<in> atm_of ` lits_of_l M'"
    using a2 by (meson subsetCE)
  have ff3: "\<And>a. a \<notin> set (map (\<lambda>m. atm_of (lit_of m)) M')
    \<or> a \<notin> set (map (\<lambda>m. atm_of (lit_of m)) M)"
    using a1 by (metis (lifting) IntI distinct_append empty_iff map_append)
  have "\<forall>L a f. \<exists>l. ((a::'a) \<notin> f ` L \<or> (l ::'a literal) \<in> L) \<and> (a \<notin> f ` L \<or> f l = a)"
    by blast
  then show "x \<notin> atm_of ` lits_of_l M"
    using ff3 ff2 ff1 a3 by (metis (no_types) Decided_Propagated_in_iff_in_lits_of_l)
qed

text \<open>\cwref{prop:prop:cdclPropLitsUnsat}{Item 5 page 81}\<close>
lemma cdcl\<^sub>W_restart_propagate_is_conclusion:
  assumes
    "cdcl\<^sub>W_restart S S'" and
    inv: "cdcl\<^sub>W_M_level_inv S" and
    decomp: "all_decomposition_implies_m (init_clss S) (get_all_ann_decomposition (trail S))" and
    learned: "cdcl\<^sub>W_learned_clause S" and
    confl: "\<forall>T. conflicting S = Some T \<longrightarrow> trail S \<Turnstile>as CNot T" and
    alien: "no_strange_atm S"
  shows "all_decomposition_implies_m (init_clss S') (get_all_ann_decomposition (trail S'))"
  using assms(1,2)
proof (induct rule: cdcl\<^sub>W_restart_all_induct)
  case restart
  then show ?case by auto
next
  case forget
  then show ?case using decomp by auto
next
  case conflict
  then show ?case using decomp by auto
next
  case (resolve L C M D) note tr = this(1) and T = this(7)
  let ?decomp = "get_all_ann_decomposition M"
  have M: "set ?decomp = insert (hd ?decomp) (set (tl ?decomp))"
    by (cases ?decomp) auto
  show ?case
    using decomp tr T unfolding all_decomposition_implies_def
    by (cases "hd (get_all_ann_decomposition M)")
       (auto simp: M)
next
  case (skip L C' M D) note tr = this(1) and T = this(5)
  have M: "set (get_all_ann_decomposition M)
    = insert (hd (get_all_ann_decomposition M)) (set (tl (get_all_ann_decomposition M)))"
    by (cases "get_all_ann_decomposition M") auto
  show ?case
    using decomp tr T unfolding all_decomposition_implies_def
    by (cases "hd (get_all_ann_decomposition M)")
       (auto simp add: M)
next
  case decide note S = this(1) and undef = this(2) and T = this(4)
  show ?case using decomp T undef unfolding S all_decomposition_implies_def by auto
next
  case (propagate C L T) note propa = this(2) and L = this(3) and undef = this(5) and T = this(6)
  obtain a y where ay: "hd (get_all_ann_decomposition (trail S)) = (a, y)"
    by (cases "hd (get_all_ann_decomposition (trail S))")
  then have M: "trail S = y @ a" using get_all_ann_decomposition_decomp by blast
  have M': "set (get_all_ann_decomposition (trail S))
    = insert (a, y) (set (tl (get_all_ann_decomposition (trail S))))"
    using ay by (cases "get_all_ann_decomposition (trail S)") auto
  have "unmark_l a \<union> set_mset (init_clss S) \<Turnstile>ps unmark_l y"
    using decomp ay unfolding all_decomposition_implies_def
    by (cases "get_all_ann_decomposition (trail S)") fastforce+
  then have a_Un_N_M: "unmark_l a \<union> set_mset (init_clss S)
    \<Turnstile>ps unmark_l (trail S)"
    unfolding M by (auto simp add: all_in_true_clss_clss image_Un)

  have "unmark_l a \<union> set_mset (init_clss S) \<Turnstile>p {#L#}" (is "?I \<Turnstile>p _")
    proof (rule true_clss_cls_plus_CNot)
      show "?I \<Turnstile>p remove1_mset L C + {#L#}"
        apply (rule true_clss_clss_in_imp_true_clss_cls[of _
            "set_mset (init_clss S) \<union> set_mset (learned_clss S)"])
        using learned propa L by (auto simp: clauses_def cdcl\<^sub>W_learned_clause_def
          true_annot_CNot_diff)
    next
      have "unmark_l (trail S) \<Turnstile>ps CNot (remove1_mset L C)"
        using \<open>(trail S) \<Turnstile>as CNot (remove1_mset L C)\<close> true_annots_true_clss_clss
        by blast
      then show "?I \<Turnstile>ps CNot (remove1_mset L C)"
        using a_Un_N_M true_clss_clss_left_right true_clss_clss_union_l_r by blast
    qed
  moreover have "\<And>aa b.
      \<forall> (Ls, seen)\<in>set (get_all_ann_decomposition (y @ a)).
        unmark_l Ls \<union> set_mset (init_clss S) \<Turnstile>ps unmark_l seen \<Longrightarrow>
        (aa, b) \<in> set (tl (get_all_ann_decomposition (y @ a))) \<Longrightarrow>
        unmark_l aa \<union> set_mset (init_clss S) \<Turnstile>ps unmark_l b"
    by (metis (no_types, lifting) case_prod_conv get_all_ann_decomposition_never_empty_sym
      list.collapse list.set_intros(2))

  ultimately show ?case
    using decomp T undef unfolding ay all_decomposition_implies_def
    using M \<open>unmark_l a \<union> set_mset (init_clss S) \<Turnstile>ps unmark_l y\<close>
     ay by auto
next
  case (backtrack L D K i M1 M2 T) note conf = this(1) and LD = this(2) and decomp' = this(3) and
    lev_L = this(4) and lev_K = this(7) and undef = this(8) and T = this(9)
  let ?D' = "remove1_mset L D"
  have "\<forall>l \<in> set M2. \<not>is_decided l"
    using get_all_ann_decomposition_snd_not_decided decomp' by blast
  obtain M0 where M: "trail S = M0 @ M2 @ Decided K # M1"
    using decomp' by auto
  show ?case unfolding all_decomposition_implies_def
    proof
      fix x
      assume "x \<in> set (get_all_ann_decomposition (trail T))"
      then have x: "x \<in> set (get_all_ann_decomposition (Propagated L D # M1))"
        using T decomp' undef inv by (simp add: cdcl\<^sub>W_M_level_inv_decomp)
      let ?m = "get_all_ann_decomposition (Propagated L D # M1)"
      let ?hd = "hd ?m"
      let ?tl = "tl ?m"
      consider
          (hd) "x = ?hd"
        | (tl) "x \<in> set ?tl"
        using x by (cases "?m") auto
      then show "case x of (Ls, seen) \<Rightarrow> unmark_l Ls \<union> set_mset (init_clss T) \<Turnstile>ps unmark_l seen"
        proof cases
          case tl
          then have "x \<in> set (get_all_ann_decomposition (trail S))"
            using tl_get_all_ann_decomposition_skip_some[of x] by (simp add: list.set_sel(2) M)
          then show ?thesis
            using decomp learned decomp confl alien inv T undef M
            unfolding all_decomposition_implies_def cdcl\<^sub>W_M_level_inv_def
            by auto
        next
          case hd
          obtain M1' M1'' where M1: "hd (get_all_ann_decomposition M1) = (M1', M1'')"
            by (cases "hd (get_all_ann_decomposition M1)")
          then have x': "x = (M1', Propagated L D # M1'')"
            using \<open>x = ?hd\<close> by auto
          have "(M1', M1'') \<in> set (get_all_ann_decomposition (trail S))"
            using M1[symmetric] hd_get_all_ann_decomposition_skip_some[OF M1[symmetric],
              of "M0 @ M2"] unfolding M by fastforce
          then have 1: "unmark_l M1' \<union> set_mset (init_clss S) \<Turnstile>ps unmark_l M1''"
            using decomp unfolding all_decomposition_implies_def by auto

          moreover
            have vars_of_D: "atms_of ?D' \<subseteq> atm_of ` lits_of_l M1"
              using backtrack_atms_of_D_in_M1[of S D L i K M1 M2 T] backtrack.hyps inv conf confl
              by (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
            have "no_dup (trail S)" using inv by (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
            then have vars_in_M1:
              "\<forall>x \<in> atms_of ?D'. x \<notin> atm_of ` lits_of_l (M0 @ M2 @ Decided K # [])"
              using vars_of_D distinct_atms_of_incl_not_in_other[of
                "M0 @M2 @ Decided K # []" M1] unfolding M by auto
            have "trail S \<Turnstile>as CNot (remove1_mset L D)"
              using conf confl LD unfolding M true_annots_true_cls_def_iff_negation_in_model
              by (auto dest!: Multiset.in_diffD)
            then have "M1 \<Turnstile>as CNot ?D'"
              using vars_in_M1 true_annots_remove_if_notin_vars[of "M0 @ M2 @ Decided K # []"
                M1 "CNot ?D'"] conf confl unfolding M lits_of_def by simp
            have "M1 = M1'' @ M1'" by (simp add: M1 get_all_ann_decomposition_decomp)
            have TT: "unmark_l M1' \<union> set_mset (init_clss S) \<Turnstile>ps CNot ?D'"
              using true_annots_true_clss_cls[OF \<open>M1 \<Turnstile>as CNot ?D'\<close>] true_clss_clss_left_right[OF 1]
              unfolding \<open>M1 = M1'' @ M1'\<close> by (auto simp add: inf_sup_aci(5,7))
            have "init_clss S \<Turnstile>pm ?D' + {#L#}"
              using conf learned confl LD unfolding cdcl\<^sub>W_learned_clause_def by auto
            then have T': "unmark_l M1' \<union> set_mset (init_clss S) \<Turnstile>p ?D' + {#L#}" by auto
            have "atms_of (?D' + {#L#}) \<subseteq> atms_of_mm (clauses S)"
              using alien conf LD unfolding no_strange_atm_def clauses_def by auto
            then have "unmark_l M1' \<union> set_mset (init_clss S) \<Turnstile>p {#L#}"
              using true_clss_cls_plus_CNot[OF T' TT] by auto

          ultimately show ?thesis
              using T' T decomp' undef inv unfolding x' by (simp add: cdcl\<^sub>W_M_level_inv_decomp)
        qed
    qed
qed

lemma cdcl\<^sub>W_restart_propagate_is_false:
  assumes
    "cdcl\<^sub>W_restart S S'" and
    lev: "cdcl\<^sub>W_M_level_inv S" and
    learned: "cdcl\<^sub>W_learned_clause S" and
    decomp: "all_decomposition_implies_m (init_clss S) (get_all_ann_decomposition (trail S))" and
    confl: "\<forall>T. conflicting S = Some T \<longrightarrow> trail S \<Turnstile>as CNot T" and
    alien: "no_strange_atm S" and
    mark_confl: "every_mark_is_a_conflict S"
  shows "every_mark_is_a_conflict S'"
  using assms(1,2)
proof (induct rule: cdcl\<^sub>W_restart_all_induct)
  case (propagate C L T) note LC = this(3) and confl = this(4) and undef = this(5) and T = this(6)
  show ?case
    proof (intro allI impI)
      fix L' mark a b
      assume "a @ Propagated L' mark # b = trail T"
      then consider
          (hd) "a = []" and "L = L'" and "mark = C" and "b = trail S"
        | (tl) "tl a @ Propagated L' mark # b = trail S"
        using T undef by (cases a) fastforce+
      then show "b \<Turnstile>as CNot (mark - {#L'#}) \<and> L' \<in># mark"
        using mark_confl confl LC by cases auto
    qed
next
  case (decide L) note undef[simp] = this(2) and T = this(4)
  have "\<And>a La mark b. a @ Propagated La mark # b = Decided L # trail S
    \<Longrightarrow> tl a @ Propagated La mark # b = trail S" by (case_tac a) auto
  then show ?case using mark_confl T unfolding decide.hyps(1) by fastforce
next
  case (skip L C' M D T) note tr = this(1) and T = this(5)
  show ?case
    proof (intro allI impI)
      fix L' mark a b
      assume "a @ Propagated L' mark # b = trail T"
      then have "a @ Propagated L' mark # b = M" using tr T by simp
      then have "(Propagated L C' # a) @ Propagated L' mark # b = Propagated L C' # M" by auto
      moreover have "\<forall>La mark a b. a @ Propagated La mark # b = Propagated L C' # M
        \<longrightarrow> b \<Turnstile>as CNot (mark - {#La#}) \<and> La \<in># mark"
        using mark_confl unfolding skip.hyps(1) by simp
      ultimately show "b \<Turnstile>as CNot (mark - {#L'#}) \<and> L' \<in># mark" by blast
    qed
next
  case (conflict D)
  then show ?case using mark_confl by simp
next
  case (resolve L C M D T) note tr_S = this(1) and T = this(7)
  show ?case unfolding resolve.hyps(1)
    proof (intro allI impI)
      fix L' mark a b
      assume "a @ Propagated L' mark # b = trail T"
      then have "(Propagated L (C + {#L#}) # a) @ Propagated L' mark # b
        = Propagated L (C + {#L#}) # M"
        using T tr_S by auto
      then show "b \<Turnstile>as CNot (mark - {#L'#}) \<and> L' \<in># mark"
        using mark_confl unfolding tr_S by (metis Cons_eq_appendI list.sel(3))
    qed
next
  case restart
  then show ?case by auto
next
  case forget
  then show ?case using mark_confl by auto
next
  case (backtrack L D K i M1 M2 T) note conf = this(1) and LD = this(2) and decomp = this(3) and
    lev_K = this(7) and T = this(8)
  have "\<forall>l \<in> set M2. \<not>is_decided l"
    using get_all_ann_decomposition_snd_not_decided decomp by blast
  obtain M0 where M: "trail S = M0 @ M2 @ Decided K # M1"
    using decomp by auto
  have [simp]: "trail (reduce_trail_to M1 (add_learned_cls D
    (update_backtrack_lvl i (update_conflicting None S)))) = M1"
    using decomp lev by (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
  let ?D' = "remove1_mset L D"
  show ?case
    proof (intro allI impI)
      fix La :: "'v literal" and mark :: "'v clause" and
        a b :: "('v, 'v clause) ann_lits"
      assume "a @ Propagated La mark # b = trail T"
      then consider
          (hd_tr) "a = []" and
            "(Propagated La mark :: ('v, 'v clause) ann_lit) = Propagated L D" and
            "b = M1"
        | (tl_tr) "tl a @ Propagated La mark # b = M1"
        using M T decomp lev by (cases a) (auto simp: cdcl\<^sub>W_M_level_inv_def)
      then show "b \<Turnstile>as CNot (mark - {#La#}) \<and> La \<in># mark"
        proof cases
          case hd_tr note A = this(1) and P = this(2) and b = this(3)
          have "trail S \<Turnstile>as CNot D" using conf confl by auto
          then have vars_of_D: "atms_of D \<subseteq> atm_of ` lits_of_l (trail S)"
            unfolding atms_of_def
            by (meson image_subsetI true_annots_CNot_all_atms_defined)
          have vars_of_D: "atms_of ?D' \<subseteq> atm_of ` lits_of_l M1"
            using backtrack_atms_of_D_in_M1[of S D L i K M1 M2 T] T backtrack lev confl
            by (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
          have "no_dup (trail S)" using lev by (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
          then have "\<forall>x \<in> atms_of ?D'. x \<notin> atm_of ` lits_of_l (M0 @ M2 @ Decided K # [])"
            using vars_of_D distinct_atms_of_incl_not_in_other[of
              "M0 @ M2 @ Decided K # []" M1] unfolding M by auto
          then have "M1 \<Turnstile>as CNot ?D'"
            using true_annots_remove_if_notin_vars[of "M0 @ M2 @ Decided K # []"
              M1 "CNot ?D'"] \<open>trail S \<Turnstile>as CNot D\<close> unfolding M lits_of_def
            by (simp add: true_annot_CNot_diff)
          then show "b \<Turnstile>as CNot (mark - {#La#}) \<and> La \<in># mark"
            using P LD b by auto
        next
          case tl_tr
          then obtain c' where "c' @ Propagated La mark # b = trail S"
            unfolding M by auto
          then show "b \<Turnstile>as CNot (mark - {#La#}) \<and> La \<in># mark"
            using mark_confl by auto
        qed
    qed
qed

lemma cdcl\<^sub>W_conflicting_is_false:
  assumes
    "cdcl\<^sub>W_restart S S'" and
    M_lev: "cdcl\<^sub>W_M_level_inv S" and
    confl_inv: "\<forall>T. conflicting S = Some T \<longrightarrow> trail S \<Turnstile>as CNot T" and
    decided_confl: "\<forall>L mark a b. a @ Propagated L mark # b = (trail S)
      \<longrightarrow> (b \<Turnstile>as CNot (mark - {#L#}) \<and> L \<in># mark)" and
    dist: "distinct_cdcl\<^sub>W_state S"
  shows "\<forall>T. conflicting S' = Some T \<longrightarrow> trail S' \<Turnstile>as CNot T"
  using assms(1,2)
proof (induct rule: cdcl\<^sub>W_restart_all_induct)
  case (skip L C' M D T) note tr_S = this(1) and confl = this(2) and L_D = this(3) and T = this(5)
  have D: "Propagated L C' # M \<Turnstile>as CNot D" using assms skip by auto
  moreover
    have "L \<notin># D"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then have "- L \<in> lits_of_l M"
          using in_CNot_implies_uminus(2)[of L D "Propagated L C' # M"]
          \<open>Propagated L C' # M \<Turnstile>as CNot D\<close> by simp
        then show False
          by (metis (no_types, hide_lams) M_lev cdcl\<^sub>W_M_level_inv_decomp(1) consistent_interp_def
            image_insert insert_iff list.set(2) lits_of_def ann_lit.sel(2) tr_S)
      qed
  ultimately show ?case
    using tr_S confl L_D T unfolding cdcl\<^sub>W_M_level_inv_def
    by (auto intro: true_annots_CNot_lit_of_notin_skip)
next
  case (resolve L C M D T) note tr = this(1) and LC = this(2) and confl = this(4) and LD = this(5)
  and T = this(7)
  let ?C = "remove1_mset L C"
  let ?D = "remove1_mset (-L) D"
  show ?case
    proof (intro allI impI)
      fix T'
      have "tl (trail S) \<Turnstile>as CNot ?C" using tr decided_confl by fastforce
      moreover
        have "distinct_mset (?D + {#- L#})" using confl dist LD
          unfolding distinct_cdcl\<^sub>W_state_def by auto
        then have "-L \<notin># ?D" unfolding distinct_mset_def
          by (meson \<open>distinct_mset (?D + {#- L#})\<close> distinct_mset_single_add)
        have "M \<Turnstile>as CNot ?D"
          proof -
            have "Propagated L (?C + {#L#}) # M \<Turnstile>as CNot ?D \<union> CNot {#- L#}"
              using confl tr confl_inv LC by (metis CNot_plus LD insert_DiffM2)
            then show ?thesis
              using M_lev \<open>- L \<notin># ?D\<close> tr true_annots_lit_of_notin_skip
              unfolding cdcl\<^sub>W_M_level_inv_def by force
          qed
      moreover assume "conflicting T = Some T'"
      ultimately
        show "trail T \<Turnstile>as CNot T'"
        using tr T by auto
    qed
qed (auto simp: M_lev cdcl\<^sub>W_M_level_inv_decomp)

lemma cdcl\<^sub>W_conflicting_decomp:
  assumes "cdcl\<^sub>W_conflicting S"
  shows "\<forall>T. conflicting S = Some T \<longrightarrow> trail S \<Turnstile>as CNot T"
  and "\<forall>L mark a b. a @ Propagated L mark # b = (trail S)
    \<longrightarrow> (b \<Turnstile>as CNot (mark - {#L#}) \<and> L \<in># mark)"
  using assms unfolding cdcl\<^sub>W_conflicting_def by blast+

lemma cdcl\<^sub>W_conflicting_decomp2:
  assumes "cdcl\<^sub>W_conflicting S" and "conflicting S = Some T"
  shows "trail S \<Turnstile>as CNot T"
  using assms unfolding cdcl\<^sub>W_conflicting_def by blast+

lemma cdcl\<^sub>W_conflicting_S0_cdcl\<^sub>W_restart[simp]:
  "cdcl\<^sub>W_conflicting (init_state N)"
  unfolding cdcl\<^sub>W_conflicting_def by auto

subsubsection \<open>Putting all the invariants together\<close>
lemma cdcl\<^sub>W_restart_all_inv:
  assumes
    cdcl\<^sub>W_restart: "cdcl\<^sub>W_restart S S'" and
    1: "all_decomposition_implies_m (init_clss S) (get_all_ann_decomposition (trail S))" and
    2: "cdcl\<^sub>W_learned_clause S" and
    4: "cdcl\<^sub>W_M_level_inv S" and
    5: "no_strange_atm S" and
    7: "distinct_cdcl\<^sub>W_state S" and
    8: "cdcl\<^sub>W_conflicting S"
  shows
    "all_decomposition_implies_m (init_clss S') (get_all_ann_decomposition (trail S'))" and
    "cdcl\<^sub>W_learned_clause S'" and
    "cdcl\<^sub>W_M_level_inv S'" and
    "no_strange_atm S'" and
    "distinct_cdcl\<^sub>W_state S'" and
    "cdcl\<^sub>W_conflicting S'"
proof -
  show S1: "all_decomposition_implies_m (init_clss S') (get_all_ann_decomposition (trail S'))"
    using cdcl\<^sub>W_restart_propagate_is_conclusion[OF cdcl\<^sub>W_restart 4 1 2 _ 5] 8 unfolding cdcl\<^sub>W_conflicting_def
    by blast
  show S2: "cdcl\<^sub>W_learned_clause S'" using cdcl\<^sub>W_restart_learned_clss[OF cdcl\<^sub>W_restart 2 4] .
  show S4: "cdcl\<^sub>W_M_level_inv S'" using cdcl\<^sub>W_restart_consistent_inv[OF cdcl\<^sub>W_restart 4] .
  show S5: "no_strange_atm S'" using cdcl\<^sub>W_restart_no_strange_atm_inv[OF cdcl\<^sub>W_restart 5 4] .
  show S7: "distinct_cdcl\<^sub>W_state S'" using distinct_cdcl\<^sub>W_state_inv[OF cdcl\<^sub>W_restart 4 7] .
  show S8: "cdcl\<^sub>W_conflicting S'"
    using cdcl\<^sub>W_conflicting_is_false[OF cdcl\<^sub>W_restart 4 _ _ 7] 8 cdcl\<^sub>W_restart_propagate_is_false[OF cdcl\<^sub>W_restart 4 2 1 _
      5]
    unfolding cdcl\<^sub>W_conflicting_def by fast
qed

lemma rtranclp_cdcl\<^sub>W_restart_all_inv:
  assumes
    cdcl\<^sub>W_restart: "rtranclp cdcl\<^sub>W_restart S S'" and
    1: "all_decomposition_implies_m (init_clss S) (get_all_ann_decomposition (trail S))" and
    2: "cdcl\<^sub>W_learned_clause S" and
    4: "cdcl\<^sub>W_M_level_inv S" and
    5: "no_strange_atm S" and
    7: "distinct_cdcl\<^sub>W_state S" and
    8: "cdcl\<^sub>W_conflicting S"
  shows
    "all_decomposition_implies_m (init_clss S') (get_all_ann_decomposition (trail S'))" and
    "cdcl\<^sub>W_learned_clause S'" and
    "cdcl\<^sub>W_M_level_inv S'" and
    "no_strange_atm S'" and
    "distinct_cdcl\<^sub>W_state S'" and
    "cdcl\<^sub>W_conflicting S'"
   using assms
proof (induct rule: rtranclp_induct)
  case base
    case 1 then show ?case by blast
    case 2 then show ?case by blast
    case 3 then show ?case by blast
    case 4 then show ?case by blast
    case 5 then show ?case by blast
    case 6 then show ?case by blast
next
  case (step S' S'') note H = this
    case 1 with H(3-7)[OF this(1-6)] show ?case using cdcl\<^sub>W_restart_all_inv[OF H(2)]
        H by presburger
    case 2 with H(3-7)[OF this(1-6)] show ?case using cdcl\<^sub>W_restart_all_inv[OF H(2)]
        H by presburger
    case 3 with H(3-7)[OF this(1-6)] show ?case using cdcl\<^sub>W_restart_all_inv[OF H(2)]
        H by presburger
    case 4 with H(3-7)[OF this(1-6)] show ?case using cdcl\<^sub>W_restart_all_inv[OF H(2)]
        H by presburger
    case 5 with H(3-7)[OF this(1-6)] show ?case using cdcl\<^sub>W_restart_all_inv[OF H(2)]
        H by presburger
    case 6 with H(3-7)[OF this(1-6)] show ?case using cdcl\<^sub>W_restart_all_inv[OF H(2)]
        H by presburger
qed

lemma all_invariant_S0_cdcl\<^sub>W_restart:
  assumes "distinct_mset_mset N"
  shows
    "all_decomposition_implies_m (init_clss (init_state N))
                                  (get_all_ann_decomposition (trail (init_state N)))" and
    "cdcl\<^sub>W_learned_clause (init_state N)" and
    "\<forall>T. conflicting (init_state N) = Some T \<longrightarrow> (trail (init_state N))\<Turnstile>as CNot T" and
    "no_strange_atm (init_state N)" and
    "consistent_interp (lits_of_l (trail (init_state N)))" and
    "\<forall>L mark a b. a @ Propagated L mark # b = trail (init_state N) \<longrightarrow>
     (b \<Turnstile>as CNot (mark - {#L#}) \<and> L \<in># mark)" and
     "distinct_cdcl\<^sub>W_state (init_state N)"
  using assms by auto

text \<open>\cwref{prop:prop:cdclUnsat}{Item 6 page 81}\<close>
lemma cdcl\<^sub>W_only_propagated_vars_unsat:
  assumes
    decided: "\<forall>x \<in> set M. \<not> is_decided x" and
    DN: "D \<in># clauses S" and
    D: "M \<Turnstile>as CNot D" and
    inv: "all_decomposition_implies_m N (get_all_ann_decomposition M)" and
    state: "state S = (M, N, U, k, C)" and
    learned_cl: "cdcl\<^sub>W_learned_clause S" and
    atm_incl: "no_strange_atm S"
  shows "unsatisfiable (set_mset N)"
proof (rule ccontr)
  assume "\<not> unsatisfiable (set_mset N)"
  then obtain I where
    I: "I \<Turnstile>s set_mset N" and
    cons: "consistent_interp I" and
    tot: "total_over_m I (set_mset N)"
    unfolding satisfiable_def by auto
  have "atms_of_mm N \<union> atms_of_mm U = atms_of_mm N"
    using atm_incl state unfolding total_over_m_def no_strange_atm_def
     by (auto simp add: clauses_def)
  then have "total_over_m I (set_mset N)" using tot unfolding total_over_m_def by auto
  moreover then have "total_over_m I (set_mset (learned_clss S))"
    using atm_incl state unfolding no_strange_atm_def total_over_m_def total_over_set_def
    by auto
  moreover have "N \<Turnstile>psm U" using learned_cl state unfolding cdcl\<^sub>W_learned_clause_def by auto
  ultimately have I_D: "I \<Turnstile> D"
    using I DN cons state unfolding true_clss_clss_def true_clss_def Ball_def
    by (auto simp add: clauses_def)

  have l0: "{unmark L |L. is_decided L \<and> L \<in> set M} = {}" using decided by auto
  have "atms_of_ms (set_mset N \<union> unmark_l M) = atms_of_mm N"
    using atm_incl state unfolding no_strange_atm_def by auto
  then have "total_over_m I (set_mset N \<union> unmark_l M)"
    using tot unfolding total_over_m_def by auto
  then have "I \<Turnstile>s unmark_l M"
    using all_decomposition_implies_propagated_lits_are_implied[OF inv] cons I
    unfolding true_clss_clss_def l0 by auto
  then have IM: "I \<Turnstile>s unmark_l M" by auto
  {
    fix K
    assume "K \<in># D"
    then have "-K \<in> lits_of_l M"
      using D unfolding true_annots_def Ball_def CNot_def true_annot_def true_cls_def true_lit_def
      Bex_def by force
    then have "-K \<in> I" using IM true_clss_singleton_lit_of_implies_incl lits_of_def by fastforce }
  then have "\<not> I \<Turnstile> D" using cons unfolding true_cls_def true_lit_def consistent_interp_def by auto
  then show False using I_D by blast
qed

text \<open>\cwref{prop:prop:cdclPropLitsUnsat}{Item 5 page 81}\<close>
text \<open>We have actually a much stronger theorem, namely
  @{thm [source] all_decomposition_implies_propagated_lits_are_implied}, that show that the only
  choices we made are decided in the formula\<close>
lemma
  assumes "all_decomposition_implies_m N (get_all_ann_decomposition M)"
  and "\<forall>m \<in> set M. \<not>is_decided m"
  shows "set_mset N \<Turnstile>ps unmark_l M"
proof -
  have T: "{unmark L |L. is_decided L \<and> L \<in> set M} = {}" using assms(2) by auto
  then show ?thesis
    using all_decomposition_implies_propagated_lits_are_implied[OF assms(1)] unfolding T by simp
qed

text \<open>\cwref{prop:prop:cdclbacktrack}{Item 7 page 81} (part 1)\<close>
lemma conflict_with_false_implies_unsat:
  assumes
    cdcl\<^sub>W_restart: "cdcl\<^sub>W_restart S S'" and
    lev: "cdcl\<^sub>W_M_level_inv S" and
    [simp]: "conflicting S' = Some {#}" and
    learned: "cdcl\<^sub>W_learned_clause S"
  shows "unsatisfiable (set_mset (init_clss S))"
  using assms
proof -
  have "cdcl\<^sub>W_learned_clause S'" using cdcl\<^sub>W_restart_learned_clss cdcl\<^sub>W_restart learned lev by auto
  then have "init_clss S' \<Turnstile>pm {#}" using assms(3) unfolding cdcl\<^sub>W_learned_clause_def by auto
  then have "init_clss S \<Turnstile>pm {#}"
    using cdcl\<^sub>W_restart_init_clss[OF assms(1) lev] by auto
  then show ?thesis unfolding satisfiable_def true_clss_cls_def by auto
qed

text \<open>\cwref{prop:prop:cdclbacktrack}{Item 7 page 81} (part 2)\<close>
lemma conflict_with_false_implies_terminated:
  assumes "cdcl\<^sub>W_restart S S'"
  and "conflicting S = Some {#}"
  shows False
  using assms by (induct rule: cdcl\<^sub>W_restart_all_induct) auto

subsubsection \<open>No tautology is learned\<close>
text \<open>This is a simple consequence of all we have shown previously. It is not strictly necessary,
  but helps finding a better bound on the number of learned clauses.\<close>
lemma learned_clss_are_not_tautologies:
  assumes
    "cdcl\<^sub>W_restart S S'" and
    lev: "cdcl\<^sub>W_M_level_inv S" and
    conflicting: "cdcl\<^sub>W_conflicting S" and
    no_tauto: "\<forall>s \<in># learned_clss S. \<not>tautology s"
  shows "\<forall>s \<in># learned_clss S'. \<not>tautology s"
  using assms
proof (induct rule: cdcl\<^sub>W_restart_all_induct)
  case (backtrack L D K i M1 M2 T) note confl = this(1)
  have "consistent_interp (lits_of_l (trail S))" using lev by (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
  moreover
    have "trail S \<Turnstile>as CNot D"
      using conflicting confl unfolding cdcl\<^sub>W_conflicting_def by auto
    then have "lits_of_l (trail S) \<Turnstile>s CNot D"
      using true_annots_true_cls by blast
  ultimately have "\<not>tautology D" using consistent_CNot_not_tautology by blast
  then show ?case using backtrack no_tauto lev
    by (auto simp: cdcl\<^sub>W_M_level_inv_decomp split: if_split_asm)
next
  case restart
  then show ?case using state_eq_learned_clss no_tauto
    by (auto intro: atms_of_ms_learned_clss_restart_state_in_atms_of_ms_learned_clssI)
qed (auto dest!: in_diffD)

definition "final_cdcl\<^sub>W_restart_state (S :: 'st)
  \<longleftrightarrow> (trail S \<Turnstile>asm init_clss S
    \<or> ((\<forall>L \<in> set (trail S). \<not>is_decided L) \<and>
       (\<exists>C \<in># init_clss S. trail S \<Turnstile>as CNot C)))"

definition "termination_cdcl\<^sub>W_restart_state (S :: 'st)
   \<longleftrightarrow> (trail S \<Turnstile>asm init_clss S
     \<or> ((\<forall>L \<in> atms_of_mm (init_clss S). L \<in> atm_of ` lits_of_l (trail S))
        \<and> (\<exists>C \<in># init_clss S. trail S \<Turnstile>as CNot C)))"

subsection \<open>CDCL Strong Completeness\<close>
lemma cdcl\<^sub>W_restart_can_do_step:
  assumes
    "consistent_interp (set M)" and
    "distinct M" and
    "atm_of ` (set M) \<subseteq> atms_of_mm N"
  shows "\<exists>S. rtranclp cdcl\<^sub>W_restart (init_state N) S
    \<and> state S = (map (\<lambda>L. Decided L) M, N, {#}, length M, None)"
  using assms
proof (induct M)
  case Nil
  then show ?case apply - by (rule exI[of _ "init_state N"]) auto
next
  case (Cons L M) note IH = this(1)
  have "consistent_interp (set M)" and "distinct M" and "atm_of ` set M \<subseteq> atms_of_mm N"
    using Cons.prems(1-3) unfolding consistent_interp_def by auto
  then obtain S where
    st: "cdcl\<^sub>W_restart\<^sup>*\<^sup>* (init_state N) S" and
    S: "state S = (map (\<lambda>L. Decided L) M, N, {#}, length M, None)"
    using IH by blast
  let ?S\<^sub>0 = "incr_lvl (cons_trail (Decided L) S)"
  have "undefined_lit (map (\<lambda>L. Decided L) M) L"
    using Cons.prems(1,2) unfolding defined_lit_def consistent_interp_def by fastforce
  moreover have "init_clss S = N"
    using S by blast
  moreover have "atm_of L \<in> atms_of_mm N" using Cons.prems(3) by auto
  moreover have undef: "undefined_lit (trail S) L"
    using S \<open>distinct (L#M)\<close> calculation(1) by (auto simp: defined_lit_map)
  ultimately have "cdcl\<^sub>W_restart S ?S\<^sub>0"
    using cdcl\<^sub>W_restart.other[OF cdcl\<^sub>W_o.decide[OF decide_rule[of S L ?S\<^sub>0]]] S
    by (auto simp: state_eq_def simp del: state_simp)
  then have "cdcl\<^sub>W_restart\<^sup>*\<^sup>* (init_state N) ?S\<^sub>0"
    using st by auto
  then show ?case
    using S undef by (auto intro!: exI[of _ ?S\<^sub>0] del: simp del: )
qed

text \<open>\cwref{cdcl:completeness}{theorem 2.9.11 page 84}\<close>
lemma cdcl\<^sub>W_restart_strong_completeness:
  assumes
    MN: "set M \<Turnstile>sm N" and
    cons: "consistent_interp (set M)" and
    dist: "distinct M" and
    atm: "atm_of ` (set M) \<subseteq> atms_of_mm N"
  obtains S where
    "state S = (map (\<lambda>L. Decided L) M, N, {#}, length M, None)" and
    "rtranclp cdcl\<^sub>W_restart (init_state N) S" and
    "final_cdcl\<^sub>W_restart_state S"
proof -
  obtain S where
    st: "rtranclp cdcl\<^sub>W_restart (init_state N) S" and
    S: "state S = (map (\<lambda>L. Decided L) M, N, {#}, length M, None)"
    using cdcl\<^sub>W_restart_can_do_step[OF cons dist atm] by auto
  have "lits_of_l (map (\<lambda>L. Decided L) M) = set M"
    by (induct M, auto)
  then have "map (\<lambda>L. Decided L) M \<Turnstile>asm N" using MN true_annots_true_cls by metis
  then have "final_cdcl\<^sub>W_restart_state S"
    using S unfolding final_cdcl\<^sub>W_restart_state_def by auto
  then show ?thesis using that st S by blast
qed

subsection \<open>Higher level strategy\<close>

text \<open>The rules described previously do not lead to a conclusive state. We have to add a strategy.\<close>

subsubsection \<open>Definition\<close>
lemma tranclp_conflict:
  "tranclp conflict S S' \<Longrightarrow> conflict S S'"
  apply (induct rule: tranclp.induct)
   apply simp
  by (metis conflictE conflicting_update_conflicting option.distinct(1) state_eq_conflicting)

text \<open>TODO see if useful\<close>
lemma tranclp_conflict_iff[iff]:
  "full1 conflict S S' \<longleftrightarrow> conflict S S'"
proof -
  have "tranclp conflict S S' \<Longrightarrow> conflict S S'" by (meson tranclp_conflict rtranclpD)
  then show ?thesis unfolding full1_def
  by (metis conflict.simps conflicting_update_conflicting option.distinct(1)
    state_eq_conflicting tranclp.intros(1))
qed

lemma skip_unique:
  "skip S T \<Longrightarrow> skip S T' \<Longrightarrow> T \<sim> T'"
  by (fastforce simp: state_eq_def simp del: state_simp elim: skipE)

lemma resolve_unique:
  "resolve S T \<Longrightarrow> resolve S T' \<Longrightarrow> T \<sim> T'"
  by (fastforce simp: state_eq_def simp del: state_simp elim: resolveE)

lemma no_conflict_after_conflict:
  "conflict S T \<Longrightarrow> \<not>conflict T U"
  by (metis conflictE conflicting_update_conflicting option.distinct(1) state_simp(5))

lemma no_propagate_after_conflict:
  "conflict S T \<Longrightarrow> \<not>propagate T U"
  by (metis conflictE conflicting_update_conflicting option.distinct(1) propagate.cases
    state_eq_conflicting)


inductive cdcl\<^sub>W_stgy :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
conflict': "conflict S S' \<Longrightarrow> cdcl\<^sub>W_stgy S S'" |
propagate': "propagate S S' \<Longrightarrow> cdcl\<^sub>W_stgy S S'" |
other': "no_step conflict S \<Longrightarrow> no_step propagate S \<Longrightarrow> cdcl\<^sub>W_o S S' \<Longrightarrow> cdcl\<^sub>W_stgy S S'"

lemma cdcl\<^sub>W_stgy_cdcl\<^sub>W: "cdcl\<^sub>W_stgy S T \<Longrightarrow> cdcl\<^sub>W S T"
  by (induction rule: cdcl\<^sub>W_stgy.induct) (auto intro: cdcl\<^sub>W.intros)


subsubsection \<open>Invariants\<close>

lemma cdcl\<^sub>W_stgy_consistent_inv:
  assumes "cdcl\<^sub>W_stgy S S'" and "cdcl\<^sub>W_M_level_inv S"
  shows "cdcl\<^sub>W_M_level_inv S'"
  using assms by (induct rule: cdcl\<^sub>W_stgy.induct) (blast intro: cdcl\<^sub>W_restart_consistent_inv 
    cdcl\<^sub>W_restart.intros)+

lemma rtranclp_cdcl\<^sub>W_stgy_consistent_inv:
  assumes "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S S'" and "cdcl\<^sub>W_M_level_inv S"
  shows "cdcl\<^sub>W_M_level_inv S'"
  using assms by induction (auto dest!: cdcl\<^sub>W_stgy_consistent_inv)

lemma cdcl\<^sub>W_stgy_no_more_init_clss:
  assumes "cdcl\<^sub>W_stgy S S'" and "cdcl\<^sub>W_M_level_inv S"
  shows "init_clss S = init_clss S'"
  using assms cdcl\<^sub>W_cdcl\<^sub>W_restart cdcl\<^sub>W_restart_init_clss cdcl\<^sub>W_stgy_cdcl\<^sub>W by blast

lemma rtranclp_cdcl\<^sub>W_stgy_no_more_init_clss:
  assumes "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S S'" and "cdcl\<^sub>W_M_level_inv S"
  shows "init_clss S = init_clss S'"
  using assms
  apply (induct rule: rtranclp_induct, simp)
  using cdcl\<^sub>W_stgy_no_more_init_clss by (simp add: rtranclp_cdcl\<^sub>W_stgy_consistent_inv)


subsubsection \<open>Literal of highest level in conflicting clauses\<close>

text \<open>One important property of the @{term cdcl\<^sub>W_restart} with strategy is that, whenever a conflict
  takes place, there is at least a literal of level k involved (except if we have derived the false
  clause). The reason is that we apply conflicts before a decision is taken.\<close>
abbreviation no_clause_is_false :: "'st \<Rightarrow> bool" where
"no_clause_is_false \<equiv>
  \<lambda>S. (conflicting S = None \<longrightarrow> (\<forall>D \<in># clauses S. \<not>trail S \<Turnstile>as CNot D))"

definition conflict_is_false_with_level :: "'st \<Rightarrow> bool" where
"conflict_is_false_with_level S \<equiv> \<forall>D. conflicting S = Some D \<longrightarrow> D \<noteq> {#}
  \<longrightarrow> (\<exists>L \<in># D. get_level (trail S) L = backtrack_lvl S)"

declare conflict_is_false_with_level_def[simp]

lemma not_conflict_not_any_negated_init_clss:
  assumes "\<forall> S'. \<not>conflict S S'"
  shows "no_clause_is_false S"
proof (clarify)
  fix D
  assume "D \<in># local.clauses S" and "conflicting S = None" and "trail S \<Turnstile>as CNot D "
  then show False
    using conflict_rule[of S D "update_conflicting (Some D) S"] assms
    by auto
qed

lemma no_chained_conflict:
  assumes "conflict S S'" and "conflict S' S''"
  shows False
  using assms unfolding conflict.simps
  by (metis conflicting_update_conflicting option.distinct(1) state_eq_conflicting)


subsubsection \<open>Literal of highest level in decided literals\<close>
definition mark_is_false_with_level :: "'st \<Rightarrow> bool" where
"mark_is_false_with_level S' \<equiv>
  \<forall>D M1 M2 L. M1 @ Propagated L D # M2 = trail S' \<longrightarrow> D - {#L#} \<noteq> {#}
    \<longrightarrow> (\<exists>L. L \<in># D \<and> get_level (trail S') L = count_decided M1)"


lemma backtrack_no_decomp:
  assumes
    S: "conflicting S = Some E" and
    LE: "L \<in># E" and
    L: "get_level (trail S) L = backtrack_lvl S" and
    D: "get_maximum_level (trail S) (remove1_mset L E) < backtrack_lvl S" and
    bt: "backtrack_lvl S = get_maximum_level (trail S) E" and
    M_L: "cdcl\<^sub>W_M_level_inv S"
  shows "\<exists>S'. cdcl\<^sub>W_o S S'"
proof -
  have L_D: "get_level (trail S) L = get_maximum_level (trail S) E"
    using L D bt by (simp add: get_maximum_level_plus)
  let ?i = "get_maximum_level (trail S) (remove1_mset L E)"
  obtain K M1 M2 where
    K: "(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S))" and
    lev_K: "get_level (trail S) K = Suc ?i"
    using backtrack_ex_decomp[OF M_L, of ?i] D S by auto
  show ?thesis using backtrack_rule[OF S LE K L, of ?i] bt L lev_K bj by (auto simp: cdcl\<^sub>W_bj.simps)
qed

lemma cdcl\<^sub>W_stgy_final_state_conclusive:
  assumes
    termi: "\<forall>S'. \<not>cdcl\<^sub>W_stgy S S'" and
    decomp: "all_decomposition_implies_m (init_clss S) (get_all_ann_decomposition (trail S))" and
    learned: "cdcl\<^sub>W_learned_clause S" and
    level_inv: "cdcl\<^sub>W_M_level_inv S" and
    alien: "no_strange_atm S" and
    no_dup: "distinct_cdcl\<^sub>W_state S" and
    confl: "cdcl\<^sub>W_conflicting S" and
    confl_k: "conflict_is_false_with_level S"
  shows "(conflicting S = Some {#} \<and> unsatisfiable (set_mset (init_clss S)))
         \<or> (conflicting S = None \<and> trail S \<Turnstile>as set_mset (init_clss S))"
proof -
  let ?M = "trail S"
  let ?N = "init_clss S"
  let ?k = "backtrack_lvl S"
  let ?U = "learned_clss S"
  consider
      (None) "conflicting S = None"
    | (Some_Empty) E where "conflicting S = Some E" and "E = {#}"
    | (Some) E' where "conflicting S = Some E'" and "conflicting S = Some E'" and "E' \<noteq> {#}"
    by (cases "conflicting S", simp) auto
  then show ?thesis
    proof cases
      case (Some_Empty E)
      then have "conflicting S = Some {#}" by auto
      then have "unsatisfiable (set_mset (init_clss S))"
        using assms(3) unfolding cdcl\<^sub>W_learned_clause_def true_clss_cls_def
        by (metis (no_types, lifting) Un_insert_right atms_of_empty satisfiable_def
          sup_bot.right_neutral total_over_m_insert total_over_set_empty true_cls_empty)
      then show ?thesis using Some_Empty by auto
    next
      case None
      have "?M \<Turnstile>asm ?N"
        proof (rule ccontr)
          assume MN: "\<not> ?thesis"
          have all_defined: "atm_of ` (lits_of_l ?M) = atms_of_mm ?N" (is "?A = ?B")
            proof
              show "?A \<subseteq> ?B" using alien unfolding no_strange_atm_def by auto
              show "?B \<subseteq> ?A"
                proof (rule ccontr)
                  assume "\<not>?B \<subseteq> ?A"
                  then obtain l where "l \<in> ?B" and "l \<notin> ?A" by auto
                  then have "undefined_lit ?M (Pos l)"
                    using \<open>l \<notin> ?A\<close> unfolding lits_of_def by (auto simp add: defined_lit_map)
                  then have "\<exists>S'. cdcl\<^sub>W_o S S'"
                    using cdcl\<^sub>W_o.decide decide_rule \<open>l \<in> ?B\<close> no_strange_atm_def None
                    by (metis literal.sel(1) state_eq_def)
                  then show False
                    using termi by (blast intro: cdcl\<^sub>W_stgy.intros)
                qed
            qed
          obtain D where "\<not> ?M \<Turnstile>a D" and "D \<in># ?N"
            using MN unfolding lits_of_def true_annots_def Ball_def by auto
          have "atms_of D \<subseteq> atm_of ` (lits_of_l ?M)"
            using \<open>D \<in># ?N\<close> unfolding all_defined atms_of_ms_def by auto
          then have "total_over_m (lits_of_l ?M) {D}"
            using atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set 
            by (fastforce simp: total_over_set_def)
          then have "?M \<Turnstile>as CNot D"
            using total_not_true_cls_true_clss_CNot \<open>\<not> trail S \<Turnstile>a D\<close> unfolding true_annot_def
            true_annots_true_cls by fastforce
          then have "\<exists>S'. conflict S S'"
            using \<open>trail S \<Turnstile>as CNot D\<close> \<open>D \<in># init_clss S\<close> not_conflict_not_any_negated_init_clss
            None unfolding clauses_def by auto
          then show False
            using termi by (blast intro: cdcl\<^sub>W_stgy.intros)
        qed
      then show ?thesis
        using None by auto
    next
      case (Some E') note conf = this(1) and LD = this(2) and nempty = this(3)
      then obtain L D where
        E'[simp]: "E' = D + {#L#}" and
        lev_L: "get_level ?M L = ?k"
        by (metis (mono_tags) confl_k insert_DiffM2 conflict_is_false_with_level_def)
      let ?D = "D + {#L#}"
      have "?D \<noteq> {#}" by auto
      have "?M \<Turnstile>as CNot ?D" using confl LD unfolding cdcl\<^sub>W_conflicting_def by auto
      then have "?M \<noteq> []" unfolding true_annots_def Ball_def true_annot_def true_cls_def by force
      have M: "?M = hd ?M # tl ?M" using \<open>?M \<noteq> []\<close> list.collapse by fastforce
      
      have n_s: "no_step conflict S" "no_step propagate S"
        using termi by (blast intro: cdcl\<^sub>W_stgy.intros)+

      have g_k: "get_maximum_level (trail S) D \<le> ?k"
        using count_decided_ge_get_maximum_level[of ?M] level_inv unfolding cdcl\<^sub>W_M_level_inv_def
        by auto
      
      have not_is_decided: "\<not> is_decided (hd ?M)"
        proof (rule ccontr)
          assume decided: "\<not> ?thesis"
          then obtain L' where L': "hd ?M = Decided L'" by (cases "hd ?M") auto
          then obtain k' where k': "k' + 1 = ?k"
            using level_inv M unfolding cdcl\<^sub>W_M_level_inv_def by (cases "trail S") auto
          define M' where M': "M' = tl ?M"
            
          have L'_L: "L' = -L"
            proof (rule ccontr)
              assume "\<not> ?thesis"
              moreover have "-L \<in> lits_of_l ?M" 
                using confl LD unfolding cdcl\<^sub>W_conflicting_def by auto
              ultimately have "get_level (hd (trail S) # M') L = get_level (tl ?M) L"
                using cdcl\<^sub>W_M_level_inv_decomp(1)[OF level_inv] M unfolding consistent_interp_def
                by (auto simp add: atm_of_eq_atm_of L' M'[symmetric])
              moreover
                have "count_decided (trail S) = ?k"
                  using level_inv unfolding cdcl\<^sub>W_M_level_inv_def by auto
                then have count: "count_decided M' = ?k - 1"
                  using level_inv M by (auto simp add: L' M'[symmetric])
                then have "get_level (tl ?M) L < ?k"
                  using count_decided_ge_get_level[of L M'] unfolding k'[symmetric] M' by auto
              finally show False using lev_L M unfolding M' by auto
            qed
          then have L: "hd ?M = Decided (-L)" using L' by auto
          
          have H: "get_maximum_level (trail S) D < ?k"
            proof (rule ccontr)
              assume "\<not> ?thesis"
              then have "get_maximum_level (trail S) D = ?k" using M g_k unfolding L by auto
              then obtain L'' where "L'' \<in># D" and L_k: "get_level ?M L'' = ?k"
                using get_maximum_level_exists_lit[of ?k ?M D] unfolding k'[symmetric] by auto
              have "L \<noteq> L''" using no_dup \<open>L'' \<in># D\<close>
                unfolding distinct_cdcl\<^sub>W_state_def LD
                by (metis E' add.right_neutral add_diff_cancel_right'
                  distinct_mem_diff_mset union_commute union_single_eq_member)
              have "L'' = -L"
                proof (rule ccontr)
                  assume "\<not> ?thesis"
                  then have "get_level ?M L'' = get_level (tl ?M) L''"
                    using M \<open>L \<noteq> L''\<close> get_level_skip_beginning[of L'' "hd ?M" "tl ?M"] unfolding L
                    by (auto simp: atm_of_eq_atm_of)
                  moreover
                    have d: "dropWhile (\<lambda>S. atm_of (lit_of S) \<noteq> atm_of L) (tl (trail S)) = []"
                      using level_inv unfolding cdcl\<^sub>W_M_level_inv_def apply (subst (asm)(2) M)
                      by (auto simp: image_iff L' L'_L)
                    have "get_level (tl (trail S)) L = 0"
                      by (auto simp: filter_empty_conv d)
                  moreover
                    have "get_level (tl (trail S)) L'' \<le> count_decided (tl (trail S))"
                      by auto
                    then have "get_level (tl (trail S)) L'' < backtrack_lvl S"
                      using level_inv unfolding cdcl\<^sub>W_M_level_inv_def apply (subst (asm)(5) M)
                      by (auto simp: image_iff L' L'_L simp del: count_decided_ge_get_level)
                  ultimately show False
                    using M[unfolded L' M'[symmetric]] L_k by (auto simp: L' L'_L)
                qed
              then have taut: "tautology (D + {#L#})"
                using \<open>L'' \<in># D\<close> by (metis add.commute mset_subset_eqD mset_subset_eq_add_left 
                  multi_member_this tautology_minus)
              moreover have "consistent_interp (lits_of_l ?M)"
                using level_inv unfolding cdcl\<^sub>W_M_level_inv_def by auto
              ultimately have "\<not>?M \<Turnstile>as CNot ?D"
                by (metis \<open>L'' = - L\<close> \<open>L'' \<in># D\<close> add.commute consistent_interp_def
                  diff_union_cancelR in_CNot_implies_uminus(2) in_diffD multi_member_this)
              moreover have "?M \<Turnstile>as CNot ?D"
                using confl no_dup LD unfolding cdcl\<^sub>W_conflicting_def by auto
              ultimately show False by blast
            qed
          have "get_maximum_level (trail S) D < get_maximum_level (trail S) (D + {#L#})"
            using H by (auto simp: get_maximum_level_plus lev_L max_def)
          moreover have "backtrack_lvl S = get_maximum_level (trail S) (D + {#L#})"
            using H by (auto simp: get_maximum_level_plus lev_L max_def)
          ultimately show False
            using backtrack_no_decomp[OF conf _ lev_L] level_inv termi
            alien other'[of S] by (auto simp add: lev_L max_def n_s)
        qed

      moreover {
        let ?D = "D + {#L#}"
        have "?D \<noteq> {#}" by auto
        have "?M \<Turnstile>as CNot ?D" using confl LD unfolding cdcl\<^sub>W_conflicting_def by auto
        then have "?M \<noteq> []" unfolding true_annots_def Ball_def true_annot_def true_cls_def by force
        assume nm: "\<not>is_decided (hd ?M)"
        then obtain L' C where L'C: "hd_trail S = Propagated L' C" using \<open>trail S \<noteq> []\<close>
          by (cases "hd_trail S") auto
        then have "hd ?M = Propagated L' C"
          using \<open>trail S \<noteq> []\<close> by fastforce
        then have M: "?M = Propagated L' C # tl ?M"
          using \<open>?M \<noteq> []\<close> list.collapse by fastforce
        then obtain C' where C': "C = C' + {#L'#}"
          using confl unfolding cdcl\<^sub>W_conflicting_def by (metis append_Nil diff_single_eq_union)
        have L'D: "-L' \<in># ?D"
          using n_s alien level_inv termi skip_rule[OF M conf] 
          by (auto dest: other' cdcl\<^sub>W_o.intros cdcl\<^sub>W_bj.intros)
        moreover {
          obtain D' where D': "?D = D' + {#-L'#}" using L'D by (metis insert_DiffM2)
          then have "get_maximum_level (trail S) D' \<le> ?k"
            using count_decided_ge_get_maximum_level[of "Propagated L' C # tl ?M"] M
            level_inv unfolding cdcl\<^sub>W_M_level_inv_def by auto
          then have "get_maximum_level (trail S) D' = ?k \<or> get_maximum_level (trail S) D' < ?k"
            using le_neq_implies_less by blast
          moreover {
            assume g_D'_k: "get_maximum_level (trail S) D' = ?k"
            then have f1: "get_maximum_level (trail S) D' = backtrack_lvl S"
              using M by auto
            then have "Ex (cdcl\<^sub>W_o S)"
              using f1 resolve_rule[of S L' C , OF \<open>trail S \<noteq> []\<close> _ _ conf] conf g_D'_k
              L'C L'D by (fastforce simp add: D' C' intro: cdcl\<^sub>W_o.intros cdcl\<^sub>W_bj.intros)
            then have False
              using n_s termi by (auto dest: other' cdcl\<^sub>W_o.intros cdcl\<^sub>W_bj.intros)
          }
          moreover {
            assume a1: "get_maximum_level (trail S) D' < ?k"
            then have f3: "get_maximum_level (trail S) D' < get_level (trail S) (-L')"
              using a1 lev_L by (metis D' get_maximum_level_ge_get_level insert_noteq_member
                not_less)
            moreover have "backtrack_lvl S = get_level (trail S) L'"
              apply (subst M)
              using level_inv unfolding cdcl\<^sub>W_M_level_inv_def
              by (subst (asm)(3) M) (auto simp add: cdcl\<^sub>W_M_level_inv_decomp)[]
            moreover
              then have "get_level (trail S) L' = get_maximum_level (trail S) (D' + {#- L'#})"
                using a1 by (auto simp add: get_maximum_level_plus max_def)
            ultimately have False
              using M backtrack_no_decomp[of S _ "-L'", OF conf] level_inv n_s termi
              by (auto simp: D' dest: other' cdcl\<^sub>W_o.intros cdcl\<^sub>W_bj.intros)
          }
          ultimately have False by blast
        }
        ultimately have False by blast
      }
      ultimately show ?thesis by blast
    qed
qed


lemma cdcl\<^sub>W_stgy_tranclp_cdcl\<^sub>W_restart:
  "cdcl\<^sub>W_stgy S S' \<Longrightarrow> cdcl\<^sub>W_restart\<^sup>+\<^sup>+ S S'"
  by (simp add: cdcl\<^sub>W_cdcl\<^sub>W_restart cdcl\<^sub>W_stgy_cdcl\<^sub>W tranclp.r_into_trancl)

lemma tranclp_cdcl\<^sub>W_stgy_tranclp_cdcl\<^sub>W_restart:
  "cdcl\<^sub>W_stgy\<^sup>+\<^sup>+ S S' \<Longrightarrow> cdcl\<^sub>W_restart\<^sup>+\<^sup>+ S S'"
  apply (induct rule: tranclp.induct)
   using cdcl\<^sub>W_stgy_tranclp_cdcl\<^sub>W_restart apply blast
  by (meson cdcl\<^sub>W_stgy_tranclp_cdcl\<^sub>W_restart tranclp_trans)

lemma rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart:
   "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S S' \<Longrightarrow> cdcl\<^sub>W_restart\<^sup>*\<^sup>* S S'"
  using rtranclp_unfold[of cdcl\<^sub>W_stgy S S'] tranclp_cdcl\<^sub>W_stgy_tranclp_cdcl\<^sub>W_restart[of S S'] by auto

lemma not_empty_get_maximum_level_exists_lit:
  assumes n: "D \<noteq> {#}"
  and max: "get_maximum_level M D = n"
  shows "\<exists>L \<in>#D. get_level M L = n"
proof -
  have f: "finite (insert 0 ((\<lambda>L. get_level M L) ` set_mset D))" by auto
  then have "n \<in> ((\<lambda>L. get_level M L) ` set_mset D)"
    using n max get_maximum_level_exists_lit_of_max_level image_iff
    unfolding get_maximum_level_def by force
  then show "\<exists>L \<in># D. get_level M L = n" by auto
qed

lemma cdcl\<^sub>W_o_conflict_is_false_with_level_inv:
  assumes
    "cdcl\<^sub>W_o S S'" and
    lev: "cdcl\<^sub>W_M_level_inv S" and
    confl_inv: "conflict_is_false_with_level S" and
    n_d: "distinct_cdcl\<^sub>W_state S" and
    conflicting: "cdcl\<^sub>W_conflicting S"
  shows "conflict_is_false_with_level S'"
  using assms(1,2)
proof (induct rule: cdcl\<^sub>W_o_induct)
  case (resolve L C M D T) note tr_S = this(1) and confl = this(4) and LD = this(5) and T = this(7)
  have uL_not_D: "-L \<notin># remove1_mset (-L) D"
    using n_d confl unfolding distinct_cdcl\<^sub>W_state_def distinct_mset_def
    by (metis distinct_cdcl\<^sub>W_state_def distinct_mem_diff_mset multi_member_last n_d)
  moreover have L_not_D: "L \<notin># remove1_mset (-L) D"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have "L \<in># D"
        by (auto simp: in_remove1_mset_neq)
      moreover have "Propagated L C # M \<Turnstile>as CNot D"
        using conflicting confl tr_S unfolding cdcl\<^sub>W_conflicting_def by auto
      ultimately have "-L \<in> lits_of_l (Propagated L C # M)"
        using in_CNot_implies_uminus(2) by blast
      moreover have "no_dup (Propagated L C # M)"
        using lev tr_S unfolding cdcl\<^sub>W_M_level_inv_def by auto
      ultimately show False unfolding lits_of_def by (metis consistent_interp_def image_eqI
        list.set_intros(1) lits_of_def ann_lit.sel(2) distinct_consistent_interp)
    qed

  ultimately
    have g_D: "get_maximum_level (Propagated L C # M) (remove1_mset (-L) D)
      = get_maximum_level M (remove1_mset (-L) D)"
      using get_maximum_level_skip_first[of L "remove1_mset (-L) D" C M]
      by (simp add: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set atms_of_def)
  have lev_L[simp]: "get_level M L = 0"
    apply (rule atm_of_notin_get_rev_level_eq_0)
    using lev unfolding cdcl\<^sub>W_M_level_inv_def tr_S by (auto simp: lits_of_def)

  have D: "get_maximum_level M (remove1_mset (-L) D) = backtrack_lvl S"
    using resolve.hyps(6) LD unfolding tr_S by (auto simp: get_maximum_level_plus max_def g_D)
  have "get_maximum_level M (remove1_mset L C) \<le> backtrack_lvl S"
    using count_decided_ge_get_maximum_level[of M] lev unfolding tr_S cdcl\<^sub>W_M_level_inv_def by auto
  then have
    "get_maximum_level M (remove1_mset (- L) D #\<union> remove1_mset L C) =
      backtrack_lvl S"
    by (auto simp: get_maximum_level_union_mset get_maximum_level_plus max_def D)
  then show ?case
    using tr_S not_empty_get_maximum_level_exists_lit[of
      "remove1_mset (- L) D #\<union> remove1_mset L C" M] T
    by auto
next
  case (skip L C' M D T) note tr_S = this(1) and D = this(2) and T = this(5)
  then obtain La where
    "La \<in># D" and
    "get_level (Propagated L C' # M) La = backtrack_lvl S"
    using skip confl_inv by auto
  moreover
    have "atm_of La \<noteq> atm_of L"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then have La: "La = L" using \<open>La \<in># D\<close> \<open>- L \<notin># D\<close>
          by (auto simp add: atm_of_eq_atm_of)
        have "Propagated L C' # M \<Turnstile>as CNot D"
          using conflicting tr_S D unfolding cdcl\<^sub>W_conflicting_def by auto
        then have "-L \<in> lits_of_l M"
          using \<open>La \<in># D\<close> in_CNot_implies_uminus(2)[of L D "Propagated L C' # M"] unfolding La
          by auto
        then show False using lev tr_S unfolding cdcl\<^sub>W_M_level_inv_def consistent_interp_def by auto
      qed
    then have "get_level (Propagated L C' # M) La = get_level M La" by auto
  ultimately show ?case using D tr_S T by auto
next
  case backtrack
  then show ?case
    by (auto split: if_split_asm simp: cdcl\<^sub>W_M_level_inv_decomp lev)
qed auto


subsubsection \<open>Strong completeness\<close>

lemma propagate_high_levelE:
  assumes "propagate S T"
  obtains M' N' U k L C where
    "state S = (M', N', U, k, None)" and
    "state T = (Propagated L (C + {#L#}) # M', N', U, k, None)" and
    "C + {#L#} \<in># local.clauses S" and
    "M' \<Turnstile>as CNot C" and
    "undefined_lit (trail S) L"
proof -
  obtain E L where
    conf: "conflicting S = None" and
    E: "E \<in># clauses S" and
    LE: "L \<in># E" and
    tr: "trail S \<Turnstile>as CNot (E - {#L#})" and
    undef: "undefined_lit (trail S) L" and
    T: "T \<sim> cons_trail (Propagated L E) S"
    using assms by (elim propagateE) simp
  obtain M N U k where
    S: "state S = (M, N, U, k, None)"
    using conf by auto
  show thesis
    using that[of M N U k L "remove1_mset L E"] S T LE E tr undef
    by auto
qed

text \<open>TODO rename\<close> 
lemma cdcl\<^sub>W_cp_propagate_completeness:
  assumes MN: "set M \<Turnstile>s set_mset N" and
  cons: "consistent_interp (set M)" and
  tot: "total_over_m (set M) (set_mset N)" and
  "lits_of_l (trail S) \<subseteq> set M" and
  "init_clss S = N" and
  "propagate\<^sup>*\<^sup>* S S'" and
  "learned_clss S = {#}"
  shows "length (trail S) \<le> length (trail S') \<and> lits_of_l (trail S') \<subseteq> set M"
  using assms(6,4,5,7)
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by auto
next
  case (step Y Z)
  note st = this(1) and propa = this(2) and IH = this(3) and lits' = this(4) and NS = this(5) and
    learned = this(6)
  then have len: "length (trail S) \<le> length (trail Y)" and LM: "lits_of_l (trail Y) \<subseteq> set M"
     by blast+

  obtain M' N' U k C L where
    Y: "state Y = (M', N', U, k, None)" and
    Z: "state Z = (Propagated L (C + {#L#}) # M', N', U, k, None)" and
    C: "C + {#L#} \<in># clauses Y" and
    M'_C: "M' \<Turnstile>as CNot C" and
    "undefined_lit (trail Y) L"
    using propa by (auto elim: propagate_high_levelE)
  have "init_clss S = init_clss Y"
    using st by induction (auto elim: propagateE)
  then have [simp]: "N' = N" using NS Y Z by simp
  have "learned_clss Y = {#}"
    using st learned by induction (auto elim: propagateE)
  then have [simp]: "U = {#}" using Y by auto
  have "set M \<Turnstile>s CNot C"
    using M'_C LM Y unfolding true_annots_def Ball_def true_annot_def true_clss_def true_cls_def
    by force
  moreover
    have "set M \<Turnstile> C + {#L#}"
      using MN C learned Y NS \<open>init_clss S = init_clss Y\<close> \<open>learned_clss Y = {#}\<close>
      unfolding true_clss_def clauses_def by fastforce
  ultimately have "L \<in> set M" by (simp add: cons consistent_CNot_not)
  then show ?case using LM len Y Z by auto
qed

lemma
  assumes "propagate\<^sup>*\<^sup>* S X"
  shows
    rtranclp_propagate_init_clss: "init_clss X = init_clss S" and
    rtranclp_propagate_learned_clss: "learned_clss X = learned_clss S"
  using assms by (induction rule: rtranclp_induct) (auto elim: propagateE)

lemma cdcl\<^sub>W_stgy_strong_completeness_n:
  assumes
    MN: "set M \<Turnstile>s set_mset N" and
    cons: "consistent_interp (set M)" and
    tot: "total_over_m (set M) (set_mset N)" and
    atm_incl: "atm_of ` (set M) \<subseteq> atms_of_mm N" and
    distM: "distinct M" and
    length: "n \<le> length M"
  shows
    "\<exists>M' k S. length M' \<ge> n \<and>
      lits_of_l M' \<subseteq> set M \<and>
      no_dup M' \<and>
      state S = (M', N, {#}, k, None) \<and>
      cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) S"
  using length
proof (induction n)
  case 0
  have "state (init_state N) = ([], N, {#}, 0, None)"
    by (auto simp: state_eq_def simp del: state_simp)
  moreover have
    "0 \<le> length []" and
    "lits_of_l [] \<subseteq> set M" and
    "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) (init_state N)"
    and "no_dup []"
    by (auto simp: state_eq_def simp del: state_simp)
  ultimately show ?case using state_eq_sym by blast
next
  case (Suc n) note IH = this(1) and n = this(2)
  then obtain M' k S where
    l_M': "length M' \<ge> n" and
    M': "lits_of_l M' \<subseteq> set M" and
    n_d[simp]: "no_dup M'" and
    S: "state S = (M', N, {#}, k, None)" and
    st: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) S"
    by auto
  have
    M: "cdcl\<^sub>W_M_level_inv S" and
    alien: "no_strange_atm S"
      using cdcl\<^sub>W_M_level_inv_S0_cdcl\<^sub>W_restart rtranclp_cdcl\<^sub>W_stgy_consistent_inv st apply blast
    using cdcl\<^sub>W_M_level_inv_S0_cdcl\<^sub>W_restart no_strange_atm_S0 rtranclp_cdcl\<^sub>W_restart_no_strange_atm_inv
    rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart st by blast

  { assume no_step: "\<not>no_step propagate S"
    then obtain S' where S': "propagate S S'"
      by auto
    have lev: "cdcl\<^sub>W_M_level_inv S'"
      using M S' rtranclp_cdcl\<^sub>W_restart_consistent_inv rtranclp_propagate_is_rtranclp_cdcl\<^sub>W_restart by blast
    then have n_d'[simp]: "no_dup (trail S')"
      unfolding cdcl\<^sub>W_M_level_inv_def by auto
    have "length (trail S) \<le> length (trail S') \<and> lits_of_l (trail S') \<subseteq> set M"
      using S' cdcl\<^sub>W_cp_propagate_completeness[OF assms(1-3), of S] M' S
      by (auto simp: comp_def)
    moreover
      have "cdcl\<^sub>W_stgy S S'" using S' by (simp add: cdcl\<^sub>W_stgy.propagate')
    moreover
      have "trail S = M'"
        using S by (auto simp: comp_def rev_map)
      then have "length (trail S') > n"
        using S' l_M' by (auto elim: propagateE)
    moreover
      have stS': "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) S'"
        using st cdcl\<^sub>W_stgy.propagate'[OF S'] by (auto simp: r_into_rtranclp)
      then have "init_clss S' = N"
        using rtranclp_cdcl\<^sub>W_stgy_no_more_init_clss by fastforce
    moreover
      have
        [simp]:"learned_clss S' = {#}" and
        [simp]: "init_clss S' = init_clss S" and
        [simp]: "conflicting S' = None"
        using S S' by (auto elim: propagateE)
      have S_S': "state S' = (trail S', N, {#}, backtrack_lvl S', None)"
        using S by auto
      have "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) S'"
        apply (rule rtranclp.rtrancl_into_rtrancl)
         using st apply simp
        using \<open>cdcl\<^sub>W_stgy S S'\<close> by simp
    ultimately have ?case
      apply -
      apply (rule exI[of _ "trail S'"], rule exI[of _ "backtrack_lvl S'"], rule exI[of _ S'])
      using S_S' by (auto simp: state_eq_def simp del: state_simp)
  }
  moreover {
    assume no_step: "no_step propagate S"
    have ?case
      proof (cases "length M' \<ge> Suc n")
        case True
        then show ?thesis using l_M' M' st M alien S n_d by blast
      next
        case False
        then have n': "length M' = n" using l_M' by auto
        have no_confl: "no_step conflict S"
          proof -
            { fix D
              assume "D \<in># N" and "M' \<Turnstile>as CNot D"
              then have "set M \<Turnstile> D" using MN unfolding true_clss_def by auto
              moreover have "set M \<Turnstile>s CNot D"
                using \<open>M' \<Turnstile>as CNot D\<close> M'
                by (metis le_iff_sup true_annots_true_cls true_clss_union_increase)
              ultimately have False using cons consistent_CNot_not by blast
            }
            then show ?thesis
              using S by (auto simp: true_clss_def comp_def rev_map
                clauses_def elim!: conflictE)
          qed
        have lenM: "length M = card (set M)" using distM by (induction M) auto
        have "no_dup M'" using S M unfolding cdcl\<^sub>W_M_level_inv_def by auto
        then have "card (lits_of_l M') = length M'"
          by (induction M') (auto simp add: lits_of_def card_insert_if)
        then have "lits_of_l M' \<subset> set M"
          using n M' n' lenM by auto
        then obtain L where L: "L \<in> set M" and undef_m: "L \<notin> lits_of_l M'" by auto
        moreover have undef: "undefined_lit M' L"
          using M' Decided_Propagated_in_iff_in_lits_of_l calculation(1,2) cons
          consistent_interp_def by (metis (no_types, lifting) subset_eq)
        moreover have "atm_of L \<in> atms_of_mm (init_clss S)"
          using atm_incl calculation S by auto
        ultimately
          have dec: "decide S (cons_trail (Decided L) (incr_lvl S))"
            using decide_rule[of S _ "cons_trail (Decided L) (incr_lvl S)"] S
            by auto
        let ?S' = "cons_trail (Decided L) (incr_lvl S)"
        have "lits_of_l (trail ?S') \<subseteq> set M" using L M' S undef by auto
        moreover have "no_strange_atm ?S'"
          using alien dec M by (meson cdcl\<^sub>W_restart_no_strange_atm_inv decide other)
        have "cdcl\<^sub>W_M_level_inv ?S'"
          using M dec rtranclp_mono[of decide cdcl\<^sub>W_restart] by (meson cdcl\<^sub>W_restart_consistent_inv decide other)
        then have lev'': "cdcl\<^sub>W_M_level_inv ?S'"
          using S rtranclp_cdcl\<^sub>W_restart_consistent_inv rtranclp_propagate_is_rtranclp_cdcl\<^sub>W_restart by blast
        then have n_d'': "no_dup (trail ?S')"
          unfolding cdcl\<^sub>W_M_level_inv_def by auto
        have "length (trail S) \<le> length (trail ?S') \<and> lits_of_l (trail ?S') \<subseteq> set M"
          using S L M' S undef by simp
        then have "Suc n \<le> length (trail ?S') \<and> lits_of_l (trail ?S') \<subseteq> set M"
          using l_M' S undef by auto
        moreover
          have "cdcl\<^sub>W_M_level_inv (cons_trail (Decided L)
            (update_backtrack_lvl (Suc (backtrack_lvl S)) S))"
            using S \<open>cdcl\<^sub>W_M_level_inv (cons_trail (Decided L) (incr_lvl S))\<close> by auto
          then have S'':
            "state ?S' = (trail ?S', N, {#}, backtrack_lvl ?S', None)"
            using S undef n_d'' lev'' by auto
          then have "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) ?S'"
            using no_step no_confl st dec by (auto dest: decide cdcl\<^sub>W_stgy.intros) 
        ultimately show ?thesis using S'' n_d'' by blast
      qed
  }
  ultimately show ?case by blast
qed

text \<open>\cwref{cdcl:completeness}{theorem 2.9.11 page 84} (with strategy)\<close>
lemma cdcl\<^sub>W_stgy_strong_completeness:
  assumes
    MN: "set M \<Turnstile>s set_mset N" and
    cons: "consistent_interp (set M)" and
    tot: "total_over_m (set M) (set_mset N)" and
    atm_incl: "atm_of ` (set M) \<subseteq> atms_of_mm N" and
    distM: "distinct M"
  shows
    "\<exists>M' k S.
      lits_of_l M' = set M \<and>
      state S = (M', N, {#}, k, None) \<and>
      cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) S \<and>
      final_cdcl\<^sub>W_restart_state S"
proof -
  from cdcl\<^sub>W_stgy_strong_completeness_n[OF assms, of "length M"]
  obtain M' k T where
    l: "length M \<le> length M'" and
    M'_M: "lits_of_l M' \<subseteq> set M" and
    no_dup: "no_dup M'" and
    T: "state T = (M', N, {#}, k, None)" and
    st: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) T"
    by auto
  have "card (set M) = length M" using distM by (simp add: distinct_card)
  moreover
    have "cdcl\<^sub>W_M_level_inv T"
      using rtranclp_cdcl\<^sub>W_stgy_consistent_inv[OF st] T by auto
    then have "card (set ((map (\<lambda>l. atm_of (lit_of l)) M'))) = length M'"
      using distinct_card no_dup by fastforce
  moreover have "card (lits_of_l M') = card (set ((map (\<lambda>l. atm_of (lit_of l)) M')))"
    using no_dup unfolding lits_of_def apply (induction M') by (auto simp add: card_insert_if)
  ultimately have "card (set M) \<le> card (lits_of_l M')" using l unfolding lits_of_def by auto
  then have "set M = lits_of_l M'"
    using M'_M card_seteq by blast
  moreover
    then have "M' \<Turnstile>asm N"
      using MN unfolding true_annots_def Ball_def true_annot_def true_clss_def by auto
    then have "final_cdcl\<^sub>W_restart_state T"
      using T no_dup unfolding final_cdcl\<^sub>W_restart_state_def by auto
  ultimately show ?thesis using st T by blast
qed


subsubsection \<open>No conflict with only variables of level less than backtrack level\<close>

text \<open>This invariant is stronger than the previous argument in the sense that it is a property about
  all possible conflicts.\<close>
definition "no_smaller_confl (S ::'st) \<equiv>
  (\<forall>M K M' D. M' @ Decided K # M = trail S \<longrightarrow> D \<in># clauses S
    \<longrightarrow> \<not>M \<Turnstile>as CNot D)"

lemma no_smaller_confl_init_sate[simp]:
  "no_smaller_confl (init_state N)" unfolding no_smaller_confl_def by auto

lemma cdcl\<^sub>W_o_no_smaller_confl_inv:
  fixes S S' :: "'st"
  assumes
    "cdcl\<^sub>W_o S S'" and
    lev: "cdcl\<^sub>W_M_level_inv S" and
    max_lev: "conflict_is_false_with_level S" and
    smaller: "no_smaller_confl S" and
    no_f: "no_clause_is_false S"
  shows "no_smaller_confl S'"
  using assms(1,2) unfolding no_smaller_confl_def
proof (induct rule: cdcl\<^sub>W_o_induct)
  case (decide L T) note confl = this(1) and undef = this(2) and T = this(4)
  have [simp]: "clauses T = clauses S"
    using T undef by auto
  show ?case
    proof (intro allI impI)
      fix M'' K M' Da
      assume "M'' @ Decided K # M' = trail T"
      and D: "Da \<in># local.clauses T"
      then have "tl M'' @ Decided K # M' = trail S
        \<or> (M'' = [] \<and> Decided K # M' = Decided L # trail S)"
        using T undef by (cases M'') auto
      moreover {
        assume "tl M'' @ Decided K # M' = trail S"
        then have "\<not>M' \<Turnstile>as CNot Da"
          using D T undef no_f confl smaller unfolding no_smaller_confl_def smaller by fastforce
      }
      moreover {
        assume "Decided K # M' = Decided L # trail S"
        then have "\<not>M' \<Turnstile>as CNot Da" using no_f D confl T by auto
      }
      ultimately show "\<not>M' \<Turnstile>as CNot Da" by fast
   qed
next
  case resolve
  then show ?case using smaller no_f max_lev unfolding no_smaller_confl_def by auto
next
  case skip
  then show ?case using smaller no_f max_lev unfolding no_smaller_confl_def by auto
next
  case (backtrack L D K i M1 M2 T) note confl = this(1) and LD = this(2) and decomp = this(3) and
    T = this(8)
  obtain c where M: "trail S = c @ M2 @ Decided K # M1"
    using decomp by auto

  show ?case
    proof (intro allI impI)
      fix M ia K' M' Da
      assume "M' @ Decided K' # M = trail T"
      then have "tl M' @ Decided K' # M = M1"
        using T decomp lev by (cases M') (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
      let ?S' = "(cons_trail (Propagated L D)
                  (reduce_trail_to M1 (add_learned_cls D
                  (update_backtrack_lvl i (update_conflicting None S)))))"
      assume D: "Da \<in># clauses T"
      moreover{
        assume "Da \<in># clauses S"
        then have "\<not>M \<Turnstile>as CNot Da" using \<open>tl M' @ Decided K' # M = M1\<close> M confl smaller
          unfolding no_smaller_confl_def by auto
      }
      moreover {
        assume Da: "Da = D"
        have "\<not>M \<Turnstile>as CNot Da"
          proof (rule ccontr)
            assume "\<not> ?thesis"
            then have "-L \<in> lits_of_l M"
              using LD unfolding Da by (simp add: in_CNot_implies_uminus(2))
            then have "-L \<in> lits_of_l (Propagated L D # M1)"
              using UnI2 \<open>tl M' @ Decided K' # M = M1\<close>
              by auto
            moreover
              have "backtrack S ?S'"
                using backtrack_rule[of S] backtrack.hyps
                by (force simp: state_eq_def simp del: state_simp)
              then have "cdcl\<^sub>W_M_level_inv ?S'"
                using cdcl\<^sub>W_restart_consistent_inv[OF _ lev] other[OF bj] 
                by (auto intro: cdcl\<^sub>W_bj.intros)
              then have "no_dup (Propagated L D # M1)"
                using decomp lev unfolding cdcl\<^sub>W_M_level_inv_def by auto
            ultimately show False
              using Decided_Propagated_in_iff_in_lits_of_l defined_lit_map by auto
          qed
      }
      ultimately show "\<not>M \<Turnstile>as CNot Da"
        using T decomp lev unfolding cdcl\<^sub>W_M_level_inv_def by fastforce
    qed
qed

lemma conflict_no_smaller_confl_inv:
  assumes "conflict S S'"
  and "no_smaller_confl S"
  shows "no_smaller_confl S'"
  using assms unfolding no_smaller_confl_def by (fastforce elim: conflictE)

lemma propagate_no_smaller_confl_inv:
  assumes propagate: "propagate S S'"
  and n_l: "no_smaller_confl S"
  shows "no_smaller_confl S'"
  unfolding no_smaller_confl_def
proof (intro allI impI)
  fix M' K M'' D
  assume M': "M'' @ Decided K # M' = trail S'"
  and "D \<in># clauses S'"
  obtain M N U k C L where
    S: "state S = (M, N, U, k, None)" and
    S': "state S' = (Propagated L (C + {#L#}) # M, N, U, k, None)" and
    "C + {#L#} \<in># clauses S" and
    "M \<Turnstile>as CNot C" and
    "undefined_lit M L"
    using propagate by (auto elim: propagate_high_levelE)
  have "tl M'' @ Decided K # M' = trail S" using M' S S'
    by (metis Pair_inject list.inject list.sel(3) ann_lit.distinct(1) self_append_conv2
      tl_append2)
  then have "\<not>M' \<Turnstile>as CNot D "
    using \<open>D \<in># clauses S'\<close> n_l S S' clauses_def unfolding no_smaller_confl_def by auto
  then show "\<not>M' \<Turnstile>as CNot D" by auto
qed

lemma cdcl\<^sub>W_stgy_no_smaller_confl:
  assumes "cdcl\<^sub>W_stgy S S'"
  and n_l: "no_smaller_confl S"
  and "conflict_is_false_with_level S"
  and "cdcl\<^sub>W_M_level_inv S"
  shows "no_smaller_confl S'"
  using assms
proof (induct rule: cdcl\<^sub>W_stgy.induct)
  case (conflict' S')
  then show ?case using conflict_no_smaller_confl_inv[of S S'] by blast
next
  case (propagate' S')
  then show ?case using propagate_no_smaller_confl_inv[of S S'] by blast
next
  case (other' S')
  then show ?case
    using cdcl\<^sub>W_o_no_smaller_confl_inv[of S] not_conflict_not_any_negated_init_clss by auto
qed

text \<open>TODO use proper function instead of \<open>init_clss S' + learned_clss\<close>\<close>
lemma is_conflicting_exists_conflict:
  assumes "\<not>(\<forall>D\<in>#init_clss S' + learned_clss S'. \<not> trail S' \<Turnstile>as CNot D)"
  and "conflicting S' = None"
  shows "\<exists>S''. conflict S' S''"
  using assms clauses_def not_conflict_not_any_negated_init_clss by fastforce

lemma cdcl\<^sub>W_o_conflict_is_no_clause_is_false:
  fixes S S' :: "'st"
  assumes
    "cdcl\<^sub>W_o S S'" and
    lev: "cdcl\<^sub>W_M_level_inv S" and
    max_lev: "conflict_is_false_with_level S" and
    no_f: "no_clause_is_false S" and
    no_l: "no_smaller_confl S"
  shows "no_clause_is_false S'
    \<or> (conflicting S' = None
        \<longrightarrow> (\<forall>D \<in># clauses S'. trail S' \<Turnstile>as CNot D
             \<longrightarrow> (\<exists>L. L \<in># D \<and> get_level (trail S') L = backtrack_lvl S')))"
  using assms(1,2)
proof (induct rule: cdcl\<^sub>W_o_induct)
  case (decide L T) note S = this(1) and undef = this(2) and T = this(4)
  show ?case
    proof (rule HOL.disjI2, clarify)
      fix D
      assume D: "D \<in># clauses T" and M_D: "trail T \<Turnstile>as CNot D"
      let ?M = "trail S"
      let ?M' = "trail T"
      let ?k = "backtrack_lvl S"
      have "\<not>?M \<Turnstile>as CNot D"
          using no_f D S T undef by auto
      have "-L \<in># D"
        proof (rule ccontr)
          assume "\<not> ?thesis"
          have "?M \<Turnstile>as CNot D"
            unfolding true_annots_def Ball_def true_annot_def CNot_def true_cls_def
            proof (intro allI impI)
              fix x
              assume x: "x \<in> {{#- L#} |L. L \<in># D}"

              then obtain L' where L': "x = {#-L'#}" "L' \<in># D" by auto
              obtain L'' where "L'' \<in># x" and L'': "lits_of_l (Decided L # ?M) \<Turnstile>l L''"
                using M_D x T undef unfolding true_annots_def Ball_def true_annot_def CNot_def
                true_cls_def Bex_def by auto
              show "\<exists>L \<in># x. lits_of_l ?M \<Turnstile>l L" unfolding Bex_def
                using L'(1) L'(2) \<open>- L \<notin># D\<close> \<open>L'' \<in># x\<close>
                \<open>lits_of_l (Decided L # trail S) \<Turnstile>l L''\<close> by auto
            qed
          then show False using \<open>\<not> ?M \<Turnstile>as CNot D\<close> by auto
        qed
      have "atm_of L \<notin> atm_of ` (lits_of_l ?M)"
        using undef defined_lit_map unfolding lits_of_def by fastforce
      then have "get_level (Decided L # ?M) (-L) = ?k + 1"
        using lev unfolding cdcl\<^sub>W_M_level_inv_def by auto
      then have "-L \<in># D \<and> get_level ?M' (-L) = backtrack_lvl T"
        using \<open>-L \<in># D\<close> T undef by auto
      then show "\<exists>La. La \<in># D \<and> get_level ?M' La = backtrack_lvl T"
        by blast
    qed
next
  case resolve
  then show ?case by auto
next
  case skip
  then show ?case by auto
next
  case (backtrack L D K i M1 M2 T) note decomp = this(3) and lev_K = this(7) and T = this(8)
  show ?case
    proof (rule HOL.disjI2, clarify)
      fix Da
      assume Da: "Da \<in># clauses T" and M_D: "trail T \<Turnstile>as CNot Da"
      obtain c where M: "trail S = c @ M2 @ Decided K # M1"
        using decomp by auto
      have tr_T: "trail T = Propagated L D # M1"
        using T decomp lev by (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
      have "backtrack S T"
        using backtrack_rule[of S] backtrack.hyps T
        by (force simp del: state_simp simp: state_eq_def)
      then have lev': "cdcl\<^sub>W_M_level_inv T"
        using cdcl\<^sub>W_restart_consistent_inv lev other cdcl\<^sub>W_bj.backtrack cdcl\<^sub>W_o.bj by blast
      then have "- L \<notin> lits_of_l M1"
        using lev cdcl\<^sub>W_M_level_inv_def tr_T unfolding consistent_interp_def by (metis insert_iff
          list.simps(15) lits_of_insert ann_lit.sel(2))
      { assume "Da \<in># clauses S"
        then have "\<not>M1 \<Turnstile>as CNot Da" using no_l M unfolding no_smaller_confl_def by auto
      }
      moreover {
        assume Da: "Da = D"
        have "\<not>M1 \<Turnstile>as CNot Da" using \<open>- L \<notin> lits_of_l M1\<close> unfolding Da
          using backtrack.hyps(2) in_CNot_implies_uminus(2) by auto
      }
      ultimately have "\<not>M1 \<Turnstile>as CNot Da"
        using Da T decomp lev by (fastforce simp: cdcl\<^sub>W_M_level_inv_decomp)
      then have "-L \<in># Da"
        using M_D \<open>- L \<notin> lits_of_l M1\<close> T unfolding tr_T true_annots_true_cls true_clss_def
        by (auto simp: uminus_lit_swap)
      have "no_dup (Propagated L D # M1)"
        using lev lev' T decomp unfolding cdcl\<^sub>W_M_level_inv_def by auto
      then have L: "atm_of L \<notin> atm_of ` lits_of_l M1" unfolding lits_of_def by auto
      have "get_level (Propagated L D # M1) (-L) = i"
        using lev_K lev unfolding cdcl\<^sub>W_M_level_inv_def
        by (simp add: M image_Un atm_lit_of_set_lits_of_l)

      then have "-L \<in># Da \<and> get_level (trail T) (-L) = backtrack_lvl T"
        using \<open>-L \<in># Da\<close> T decomp lev by (auto simp: cdcl\<^sub>W_M_level_inv_def)
      then show "\<exists>La. La \<in># Da \<and> get_level (trail T) La = backtrack_lvl T"
        by blast
    qed
qed

lemma 
  assumes 
    conflict: "conflict S T" and
    smaller: "no_smaller_confl S" and 
    M_lev: "cdcl\<^sub>W_M_level_inv S"
  shows "conflict_is_false_with_level T"
  using conflict
proof (cases rule: conflict.cases)
  case (conflict_rule D) note confl = this(1) and D = this(2) and not_D = this(3) and T = this(4)
  then have [simp]: "conflicting T = Some D"
    by auto
  have M_lev_T: "cdcl\<^sub>W_M_level_inv T"
    using conflict M_lev by (auto simp: cdcl\<^sub>W_restart_consistent_inv 
      dest: cdcl\<^sub>W_restart.intros)    
  show ?thesis
    proof (rule ccontr, clarsimp)
      assume 
        empty: "D \<noteq> {#}" and
        lev: "\<forall>L\<in>#D. get_level (trail T) L \<noteq> backtrack_lvl T"
      moreover 
        have "get_level (trail T) L \<le> backtrack_lvl T" if "L\<in>#D" for L
          using that count_decided_ge_get_level[of L "trail T"] M_lev_T
          unfolding cdcl\<^sub>W_M_level_inv_def by auto
        then have lev': "get_level (trail T) L < backtrack_lvl T" if "L\<in>#D" for L
          using lev that by fastforce
      ultimately have "count_decided (trail T) > 0" 
        using M_lev_T unfolding cdcl\<^sub>W_M_level_inv_def by (cases D) fastforce+
      then obtain M2 L M1 where
        tr_T: "trail T = M2 @ Decided L # M1" and "\<forall>m \<in> set M2. \<not> is_decided m"
        sorry
      then have "M1 \<Turnstile>as CNot D"
        using lev' not_D T unfolding true_annots_true_cls_def_iff_negation_in_model 
        apply auto
        sorry
      then show False
        using smaller T tr_T D by (auto simp: no_smaller_confl_def)
      let ?M = "dropWhile (\<lambda>L. \<not>(is_decided L)) (trail S)" 
    qed
qed
  
lemma cdcl\<^sub>W_stgy_ex_lit_of_max_level:
  assumes
    "cdcl\<^sub>W_stgy S S'" and
    n_l: "no_smaller_confl S" and
    "conflict_is_false_with_level S" and
    "cdcl\<^sub>W_M_level_inv S" and
    "distinct_cdcl\<^sub>W_state S" and
    "cdcl\<^sub>W_conflicting S"
  shows "conflict_is_false_with_level S'"
  using assms        
proof (induct rule: cdcl\<^sub>W_stgy.induct)
  case (conflict' S')
  then have "no_smaller_confl S'"
    using conflict'.hyps conflict_no_smaller_confl_inv n_l by blast
  moreover have "conflict_is_false_with_level S'"
    using conflict'.hyps conflict'.prems(2-4) 
    apply (auto elim: conflictE)
    sorry
  then show ?case by blast
next
  case (propagate' S')
  then show ?case by (auto elim: propagateE)
next
  case (other' S') note n_s = this(1,2) and o = this(3) and lev = this(6)
  have lev': "cdcl\<^sub>W_M_level_inv S'"
    using cdcl\<^sub>W_restart_consistent_inv other o lev by blast
  moreover
    have "no_clause_is_false S'
      \<or> (conflicting S' = None \<longrightarrow> (\<forall>D\<in>#clauses S'. trail S' \<Turnstile>as CNot D
          \<longrightarrow> (\<exists>L. L \<in># D \<and> get_level (trail S') L = backtrack_lvl S')))"
      using cdcl\<^sub>W_o_conflict_is_no_clause_is_false[of S S'] o other'.prems(1-4) by fast
  moreover {
    assume "no_clause_is_false S'"
    {
      assume "conflicting S' = None"
      then have "conflict_is_false_with_level S'" by auto
    }
    moreover
    {
      assume c: "conflicting S' \<noteq> None"
      have "conflicting S \<noteq> None" using o c
        by (induct rule: cdcl\<^sub>W_o_induct) auto
      then have "conflict_is_false_with_level S'"
        using cdcl\<^sub>W_o_conflict_is_false_with_level_inv[OF o] other'.prems(3,5,6,2) by blast
    }
    ultimately have "conflict_is_false_with_level S'" by blast
  }
  moreover {
     assume
       confl: "conflicting S' = None" and
       D_L: "\<forall>D \<in># clauses S'. trail S' \<Turnstile>as CNot D
         \<longrightarrow> (\<exists>L. L \<in># D \<and> get_level (trail S') L = backtrack_lvl S')"
     then have ?case by simp
  }
  moreover {
    assume "conflicting S' \<noteq> None"
    have "no_clause_is_false S'" using \<open>conflicting S' \<noteq> None\<close> by auto
    then have "conflict_is_false_with_level S'" using calculation(3) by presburger
  }
  ultimately show ?case by blast
qed

lemma rtranclp_cdcl\<^sub>W_stgy_no_smaller_confl_inv:
  assumes
    "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S S'" and
    n_l: "no_smaller_confl S" and
    cls_false: "conflict_is_false_with_level S" and
    lev: "cdcl\<^sub>W_M_level_inv S" and
    no_f: "no_clause_is_false S" and
    dist: "distinct_cdcl\<^sub>W_state S" and
    conflicting: "cdcl\<^sub>W_conflicting S" and
    decomp: "all_decomposition_implies_m (init_clss S) (get_all_ann_decomposition (trail S))" and
    learned: "cdcl\<^sub>W_learned_clause S" and
    alien: "no_strange_atm S"
  shows "no_smaller_confl S' \<and> conflict_is_false_with_level S'"
  using assms(1)
proof (induct rule: rtranclp_induct)
  case base
  then show ?case using n_l cls_false by auto
next
  case (step S' S'') note st = this(1) and cdcl = this(2) and IH = this(3)
  have "no_smaller_confl S'" and "conflict_is_false_with_level S'"
    using IH by blast+
  moreover have "cdcl\<^sub>W_M_level_inv S'"
    using st lev rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart
    by (blast intro: rtranclp_cdcl\<^sub>W_restart_consistent_inv)+
(*   moreover have "no_clause_is_false S'"
    sledgehammer
    using st no_f rtranclp_cdcl\<^sub>W_stgy_not_non_negated_init_clss by presburger *)
  moreover have "distinct_cdcl\<^sub>W_state S'"
    using rtanclp_distinct_cdcl\<^sub>W_state_inv[of S S'] lev rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart[OF st]
    dist by auto
  moreover have "cdcl\<^sub>W_conflicting S'"
    using rtranclp_cdcl\<^sub>W_restart_all_inv(6)[of S S'] st alien conflicting decomp dist learned lev
    rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart by blast
  ultimately show ?case
    apply (cases "conflicting S''")
    using cdcl\<^sub>W_stgy_no_smaller_confl[OF cdcl] cdcl\<^sub>W_stgy_ex_lit_of_max_level[OF cdcl]
    apply simp
    using cdcl\<^sub>W_stgy_no_smaller_confl[OF cdcl] cdcl\<^sub>W_stgy_ex_lit_of_max_level[OF cdcl] cdcl
    apply (cases "conflicting S'")
    apply (auto simp del: simp add: cdcl\<^sub>W_stgy.simps elim!: propagateE)
    sledgehammer
    by fast
qed

subsubsection \<open>Final States are Conclusive\<close>
(*prop 2.10.7*)
lemma full_cdcl\<^sub>W_stgy_final_state_conclusive_non_false:
  fixes S' :: "'st"
  assumes full: "full cdcl\<^sub>W_stgy (init_state N) S'"
  and no_d: "distinct_mset_mset N"
  and no_empty: "\<forall>D\<in>#N. D \<noteq> {#}"
  shows "(conflicting S' = Some {#} \<and> unsatisfiable (set_mset (init_clss S')))
    \<or> (conflicting S' = None \<and> trail S' \<Turnstile>asm init_clss S')"
proof -
  let ?S = "init_state N"
  have
    termi: "\<forall>S''. \<not>cdcl\<^sub>W_stgy S' S''" and
    step: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ?S S'" using full unfolding full_def by auto
  moreover have
    learned: "cdcl\<^sub>W_learned_clause S'" and
    level_inv: "cdcl\<^sub>W_M_level_inv S'" and
    alien: "no_strange_atm S'" and
    no_dup: "distinct_cdcl\<^sub>W_state S'" and
    confl: "cdcl\<^sub>W_conflicting S'" and
    decomp: "all_decomposition_implies_m (init_clss S') (get_all_ann_decomposition (trail S'))"
    using no_d tranclp_cdcl\<^sub>W_stgy_tranclp_cdcl\<^sub>W_restart[of ?S S'] step rtranclp_cdcl\<^sub>W_restart_all_inv(1-6)[of ?S S']
    unfolding rtranclp_unfold by auto
  moreover
    have "\<forall>D\<in>#N. \<not> [] \<Turnstile>as CNot D" using no_empty by auto
    then have confl_k: "conflict_is_false_with_level S'"
      using rtranclp_cdcl\<^sub>W_stgy_no_smaller_confl_inv[OF step] no_d by auto
  show ?thesis
    using cdcl\<^sub>W_stgy_final_state_conclusive[OF termi decomp learned level_inv alien no_dup confl
      confl_k] .
qed


lemma conflict_is_full1_cdcl\<^sub>W_cp:
  assumes cp: "conflict S S'"
  shows "full1 cdcl\<^sub>W_cp S S'"
proof -
  have "cdcl\<^sub>W_cp S S'" and "conflicting S' \<noteq> None"
    using cp cdcl\<^sub>W_cp.intros by (auto elim!: conflictE simp: state_eq_def simp del: state_simp)
  then have "cdcl\<^sub>W_cp\<^sup>+\<^sup>+ S S'" by blast
  moreover have "no_step cdcl\<^sub>W_cp S'"
    using \<open>conflicting S' \<noteq> None\<close> by (metis cdcl\<^sub>W_cp_conflicting_not_empty
      option.exhaust)
  ultimately show "full1 cdcl\<^sub>W_cp S S'" unfolding full1_def by blast+
qed

lemma cdcl\<^sub>W_cp_fst_empty_conflicting_false:
  assumes
    "cdcl\<^sub>W_cp S S'" and
    "trail S = []" and
    "conflicting S \<noteq> None"
  shows False
  using assms by (induct rule: cdcl\<^sub>W_cp.induct) (auto elim: propagateE conflictE)

lemma cdcl\<^sub>W_o_fst_empty_conflicting_false:
  assumes "cdcl\<^sub>W_o S S'"
  and "trail S = []"
  and "conflicting S \<noteq> None"
  shows False
  using assms by (induct rule: cdcl\<^sub>W_o_induct) auto

lemma cdcl\<^sub>W_stgy_fst_empty_conflicting_false:
  assumes "cdcl\<^sub>W_stgy S S'"
  and "trail S = []"
  and "conflicting S \<noteq> None"
  shows False
  using assms apply (induct rule: cdcl\<^sub>W_stgy.induct)
  using tranclpD cdcl\<^sub>W_cp_fst_empty_conflicting_false unfolding full1_def apply metis
  using cdcl\<^sub>W_o_fst_empty_conflicting_false by blast
thm cdcl\<^sub>W_cp.induct[split_format(complete)]

lemma cdcl\<^sub>W_cp_conflicting_is_false:
  "cdcl\<^sub>W_cp S S' \<Longrightarrow> conflicting S = Some {#} \<Longrightarrow> False"
  by (induction rule: cdcl\<^sub>W_cp.induct) (auto elim: propagateE conflictE)

lemma rtranclp_cdcl\<^sub>W_cp_conflicting_is_false:
  "cdcl\<^sub>W_cp\<^sup>+\<^sup>+ S S' \<Longrightarrow> conflicting S = Some {#} \<Longrightarrow> False"
  apply (induction rule: tranclp.induct)
  by (auto dest: cdcl\<^sub>W_cp_conflicting_is_false)

lemma cdcl\<^sub>W_o_conflicting_is_false:
  "cdcl\<^sub>W_o S S' \<Longrightarrow> conflicting S = Some {#} \<Longrightarrow> False"
  by (induction rule: cdcl\<^sub>W_o_induct) auto

lemma cdcl\<^sub>W_stgy_conflicting_is_false:
  "cdcl\<^sub>W_stgy S S' \<Longrightarrow> conflicting S = Some {#} \<Longrightarrow> False"
  apply (induction rule: cdcl\<^sub>W_stgy.induct)
    unfolding full1_def apply (metis (no_types) cdcl\<^sub>W_cp_conflicting_not_empty tranclpD)
  unfolding full_def by (metis conflict_with_false_implies_terminated other)

lemma rtranclp_cdcl\<^sub>W_stgy_conflicting_is_false:
  "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S S' \<Longrightarrow> conflicting S = Some {#} \<Longrightarrow> S' = S"
  apply (induction rule: rtranclp_induct)
    apply simp
  using cdcl\<^sub>W_stgy_conflicting_is_false by blast

lemma full_cdcl\<^sub>W_restart_init_clss_with_false_normal_form:
  assumes
    "\<forall> m\<in> set M. \<not>is_decided m" and
    "E = Some D" and
    "state S = (M, N, U, 0, E)"
    "full cdcl\<^sub>W_stgy S S'" and
    "all_decomposition_implies_m (init_clss S) (get_all_ann_decomposition (trail S))"
    "cdcl\<^sub>W_learned_clause S"
    "cdcl\<^sub>W_M_level_inv S"
    "no_strange_atm S"
    "distinct_cdcl\<^sub>W_state S"
    "cdcl\<^sub>W_conflicting S"
  shows "\<exists>M''. state S' = (M'', N, U, 0, Some {#})"
  using assms(10,9,8,7,6,5,4,3,2,1)
proof (induction M arbitrary: E D S)
  case Nil
  then show ?case
    using rtranclp_cdcl\<^sub>W_stgy_conflicting_is_false unfolding full_def cdcl\<^sub>W_conflicting_def
    by fastforce
next
  case (Cons L M) note IH = this(1) and full = this(8) and E = this(10) and inv = this(2-7) and
    S = this(9) and nm = this(11)
  obtain K p where K: "L = Propagated K p"
    using nm by (cases L) auto
  have "every_mark_is_a_conflict S" using inv unfolding cdcl\<^sub>W_conflicting_def by auto
  then have MpK: "M \<Turnstile>as CNot (p - {#K#})" and Kp: "K \<in># p"
    using S unfolding K by fastforce+
  then have p: "p = (p - {#K#}) + {#K#}"
    by (auto simp add: multiset_eq_iff)
  then have K': "L = Propagated K ((p - {#K#}) + {#K#})"
    using K by auto
  obtain p' where
    p': "hd_trail S = Propagated K p'" and
    pp': "p' = p"
    using S K by (cases "hd_trail S") auto
  have "conflicting S = Some D"
    using S E by (cases "conflicting S") auto
  then have DD: "D = D"
    using S E by auto
  consider (D) "D = {#}" | (D') "D \<noteq> {#}" by blast
  then show ?case
    proof cases
      case D
      then show ?thesis
        using full rtranclp_cdcl\<^sub>W_stgy_conflicting_is_false S unfolding full_def E D by auto
    next
      case D'
      then have no_p: "no_step propagate S" and no_c: "no_step conflict S"
        using S E by (auto elim: propagateE conflictE)
      then have "no_step cdcl\<^sub>W_cp S" by (auto simp: cdcl\<^sub>W_cp.simps)
      have res_skip: "\<exists>T. (resolve S T \<and> no_step skip S \<and> full cdcl\<^sub>W_cp T T)
        \<or> (skip S T \<and> no_step resolve S \<and> full cdcl\<^sub>W_cp T T)"
        proof cases
          assume "-lit_of L \<notin># D"
          then obtain T where sk: "skip S T"
            using S D' K skip_rule unfolding E by fastforce
          then have res: "no_step resolve S"
            using \<open>-lit_of L \<notin># D\<close> S D' K unfolding E
            by (auto elim!: skipE resolveE)
          have "full cdcl\<^sub>W_cp T T"
            using sk by (auto intro!: option_full_cdcl\<^sub>W_cp elim: skipE)
          then show ?thesis
            using sk res by blast
        next
          assume LD: "\<not>-lit_of L \<notin># D"
          then have D: "Some D = Some ((D - {#-lit_of L#}) + {#-lit_of L#})"
            by (auto simp add: multiset_eq_iff)

          have "\<And>L. get_level M L = 0"
            by (simp add: nm)
          then have "get_maximum_level (Propagated K (p - {#K#} + {#K#}) # M) (D - {#- K#}) = 0"
            using LD get_maximum_level_exists_lit_of_max_level
            proof -
              obtain L' where "get_level (L#M) L' = get_maximum_level (L#M) D"
                using LD get_maximum_level_exists_lit_of_max_level[of D "L#M"] by fastforce
              then show ?thesis by (metis (mono_tags) K' get_level_skip_all_not_decided
                get_maximum_level_exists_lit nm not_gr0)
            qed
          then obtain T where sk: "resolve S T"
            using resolve_rule[of S K p' D] S p' \<open>K \<in># p\<close> D LD
            unfolding K' D E pp' by auto
          then have res: "no_step skip S"
            using LD S D' K unfolding E
            by (auto elim!: skipE resolveE)
          have "full cdcl\<^sub>W_cp T T"
            using sk by (auto simp: option_full_cdcl\<^sub>W_cp elim: resolveE)
          then show ?thesis
           using sk res by blast
        qed
      then have step_s: "\<exists>T. cdcl\<^sub>W_stgy S T"
        using \<open>no_step cdcl\<^sub>W_cp S\<close> other' by (meson bj resolve skip)
      have "get_all_ann_decomposition (L # M) = [([], L#M)]"
        using nm unfolding K apply (induction M rule: ann_lit_list_induct, simp)
          by (rename_tac L xs, case_tac "hd (get_all_ann_decomposition xs)", auto)+
      then have no_b: "no_step backtrack S"
        using nm S by (auto elim: backtrackE)
      have no_d: "no_step decide S"
        using S E by (auto elim: decideE)

      have full_S_S: "full cdcl\<^sub>W_cp S S"
        using S E by (auto simp add: option_full_cdcl\<^sub>W_cp)
      then have no_f: "no_step (full1 cdcl\<^sub>W_cp) S"
        unfolding full_def full1_def rtranclp_unfold by (meson tranclpD)
      obtain T where
        s: "cdcl\<^sub>W_stgy S T" and st: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* T S'"
        using full step_s full unfolding full_def by (metis rtranclp_unfold tranclpD)
      have "resolve S T \<or> skip S T"
        using s no_b no_d res_skip full_S_S cdcl\<^sub>W_cp_state_eq_compatible resolve_unique
        skip_unique unfolding cdcl\<^sub>W_stgy.simps cdcl\<^sub>W_o.simps full_unfold
        full1_def by (blast dest!: tranclpD elim!: cdcl\<^sub>W_bj.cases)+
      then obtain D' where T: "state T = (M, N, U, 0, Some D')"
        using S E by (auto elim!: skipE resolveE simp: state_eq_def simp del: state_simp)

      have st_c: "cdcl\<^sub>W_restart\<^sup>*\<^sup>* S T"
        using E T rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart s by blast
      have "cdcl\<^sub>W_conflicting T"
        using rtranclp_cdcl\<^sub>W_restart_all_inv(6)[OF st_c inv(6,5,4,3,2,1)] .
      show ?thesis
        apply (rule IH[of T])
                  using rtranclp_cdcl\<^sub>W_restart_all_inv(6)[OF st_c inv(6,5,4,3,2,1)] apply blast
                using rtranclp_cdcl\<^sub>W_restart_all_inv(5)[OF st_c inv(6,5,4,3,2,1)] apply blast
               using rtranclp_cdcl\<^sub>W_restart_all_inv(4)[OF st_c inv(6,5,4,3,2,1)] apply blast
              using rtranclp_cdcl\<^sub>W_restart_all_inv(3)[OF st_c inv(6,5,4,3,2,1)] apply blast
             using rtranclp_cdcl\<^sub>W_restart_all_inv(2)[OF st_c inv(6,5,4,3,2,1)] apply blast
            using rtranclp_cdcl\<^sub>W_restart_all_inv(1)[OF st_c inv(6,5,4,3,2,1)] apply blast
           apply (metis full_def st full)
          using T E apply blast
         apply auto[]
        using nm by simp
    qed
qed

lemma full_cdcl\<^sub>W_stgy_final_state_conclusive_is_one_false:
  fixes S' :: "'st"
  assumes full: "full cdcl\<^sub>W_stgy (init_state N) S'"
  and no_d: "distinct_mset_mset N"
  and empty: "{#} \<in># N"
  shows "conflicting S' = Some {#} \<and> unsatisfiable (set_mset (init_clss S'))"
proof -
  let ?S = "init_state N"
  have "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ?S S'" and "no_step cdcl\<^sub>W_stgy S'" using full unfolding full_def by auto
  then have plus_or_eq: "cdcl\<^sub>W_stgy\<^sup>+\<^sup>+ ?S S' \<or> S' = ?S" unfolding rtranclp_unfold by auto
  have "\<exists>S''. conflict ?S S''"
    using empty not_conflict_not_any_negated_init_clss[of "init_state N"] by auto


  then have cdcl\<^sub>W_stgy: "\<exists>S'. cdcl\<^sub>W_stgy ?S S'"
    using cdcl\<^sub>W_cp.conflict'[of ?S] conflict_is_full1_cdcl\<^sub>W_cp cdcl\<^sub>W_stgy.intros(1) by metis
  have "S' \<noteq> ?S" using \<open>no_step cdcl\<^sub>W_stgy S'\<close> cdcl\<^sub>W_stgy by blast

  then obtain St :: 'st where St: "cdcl\<^sub>W_stgy ?S St" and "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* St S'"
    using plus_or_eq by (metis (no_types) \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ?S S'\<close> converse_rtranclpE)
  have st: "cdcl\<^sub>W_restart\<^sup>*\<^sup>* ?S St"
    by (simp add: rtranclp_unfold \<open>cdcl\<^sub>W_stgy ?S St\<close> cdcl\<^sub>W_stgy_tranclp_cdcl\<^sub>W_restart)

  have "\<exists>T. conflict ?S T"
    using empty not_conflict_not_any_negated_init_clss[of "?S"] by force
  then have fullSt: "full1 cdcl\<^sub>W_cp ?S St"
    using St unfolding cdcl\<^sub>W_stgy.simps by blast
  then have bt: "backtrack_lvl St = (0::nat)"
    using rtranclp_cdcl\<^sub>W_cp_backtrack_lvl unfolding full1_def
    by (fastforce dest!: tranclp_into_rtranclp)
  have cls_St: "init_clss St = N"
    using fullSt cdcl\<^sub>W_stgy_no_more_init_clss[OF St] by auto
  have "conflicting St \<noteq> None"
    proof (rule ccontr)
      assume conf: "\<not> ?thesis"
      obtain E where
        ES: "E \<in># init_clss St" and
        E: "E = {#}"
        using empty cls_St by metis
      then have "\<exists>T. conflict St T"
        using empty cls_St conflict_rule[of St E] ES conf unfolding E
        by (auto simp: clauses_def dest: )
      then show False using fullSt unfolding full1_def by blast
    qed

  have 1: "\<forall>m\<in>set (trail St). \<not> is_decided m"
    using fullSt unfolding full1_def by (auto dest!: tranclp_into_rtranclp
      rtranclp_cdcl\<^sub>W_cp_dropWhile_trail)
  have 2: "full cdcl\<^sub>W_stgy St S'"
    using \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* St S'\<close> \<open>no_step cdcl\<^sub>W_stgy S'\<close> bt unfolding full_def by auto
  have 3: "all_decomposition_implies_m
      (init_clss St)
      (get_all_ann_decomposition
         (trail St))"
   using rtranclp_cdcl\<^sub>W_restart_all_inv(1)[OF st] no_d bt by simp
  have 4: "cdcl\<^sub>W_learned_clause St"
    using rtranclp_cdcl\<^sub>W_restart_all_inv(2)[OF st] no_d bt bt by simp
  have 5: "cdcl\<^sub>W_M_level_inv St"
    using rtranclp_cdcl\<^sub>W_restart_all_inv(3)[OF st] no_d bt by simp
  have 6: "no_strange_atm St"
    using rtranclp_cdcl\<^sub>W_restart_all_inv(4)[OF st] no_d bt by simp
  have 7: "distinct_cdcl\<^sub>W_state St"
    using rtranclp_cdcl\<^sub>W_restart_all_inv(5)[OF st] no_d bt by simp
  have 8: "cdcl\<^sub>W_conflicting St"
    using rtranclp_cdcl\<^sub>W_restart_all_inv(6)[OF st] no_d bt by simp
  have "init_clss S' = init_clss St" and "conflicting S' = Some {#}"
     using \<open>conflicting St \<noteq> None\<close> full_cdcl\<^sub>W_restart_init_clss_with_false_normal_form[OF 1, of _ _ St]
     2 3 4 5 6 7 8 St apply (metis \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* St S'\<close> rtranclp_cdcl\<^sub>W_stgy_no_more_init_clss)
    using \<open>conflicting St \<noteq> None\<close> full_cdcl\<^sub>W_restart_init_clss_with_false_normal_form[OF 1, of _ _ St _ _
      S'] 2 3 4 5 6 7 8 by (metis bt option.exhaust prod.inject)

  moreover have "init_clss S' = N"
    using \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) S'\<close> rtranclp_cdcl\<^sub>W_stgy_no_more_init_clss by fastforce
  moreover have "unsatisfiable (set_mset N)"
    by (meson empty satisfiable_def true_cls_empty true_clss_def)
  ultimately show ?thesis by auto
qed

text \<open>\cwref{lem:prop:cdclsoundtermStates}{theorem 2.9.9 page 83}\<close>
lemma full_cdcl\<^sub>W_stgy_final_state_conclusive:
  fixes S' :: 'st
  assumes full: "full cdcl\<^sub>W_stgy (init_state N) S'" and no_d: "distinct_mset_mset N"
  shows "(conflicting S' = Some {#} \<and> unsatisfiable (set_mset (init_clss S')))
    \<or> (conflicting S' = None \<and> trail S' \<Turnstile>asm init_clss S')"
  using assms full_cdcl\<^sub>W_stgy_final_state_conclusive_is_one_false
  full_cdcl\<^sub>W_stgy_final_state_conclusive_non_false by blast

text \<open>\cwref{lem:prop:cdclsoundtermStates}{theorem 2.9.9 page 83}\<close>
lemma full_cdcl\<^sub>W_stgy_final_state_conclusive_from_init_state:
  fixes S' :: "'st"
  assumes full: "full cdcl\<^sub>W_stgy (init_state N) S'"
  and no_d: "distinct_mset_mset N"
  shows "(conflicting S' = Some {#} \<and> unsatisfiable (set_mset N))
   \<or> (conflicting S' = None \<and> trail S' \<Turnstile>asm N \<and> satisfiable (set_mset N))"
proof -
  have N: "init_clss S' = N"
    using full unfolding full_def by (auto dest: rtranclp_cdcl\<^sub>W_stgy_no_more_init_clss)
  consider
      (confl) "conflicting S' = Some {#}" and "unsatisfiable (set_mset (init_clss S'))"
    | (sat) "conflicting S' = None" and "trail S' \<Turnstile>asm init_clss S'"
    using full_cdcl\<^sub>W_stgy_final_state_conclusive[OF assms] by auto
  then show ?thesis
    proof cases
      case confl
      then show ?thesis by (auto simp: N)
    next
      case sat
      have "cdcl\<^sub>W_M_level_inv (init_state N)" by auto
      then have "cdcl\<^sub>W_M_level_inv S'"
        using full rtranclp_cdcl\<^sub>W_stgy_consistent_inv unfolding full_def by blast
      then have "consistent_interp (lits_of_l (trail S'))"
        unfolding cdcl\<^sub>W_M_level_inv_def by blast
      moreover have "lits_of_l (trail S') \<Turnstile>s set_mset (init_clss S')"
        using sat(2) by (auto simp add: true_annots_def true_annot_def true_clss_def)
      ultimately have "satisfiable (set_mset (init_clss S'))" by simp
      then show ?thesis using sat unfolding N by blast
    qed
qed

subsection \<open>Structural Invariant\<close>
text \<open>The condition that no learned clause is a tautology is overkill for the termination (in the
  sense that the no-duplicate condition is enough), but it allows to reuse @{term simple_clss}.

  The invariant contains all the structural invariants that holds,\<close>
definition cdcl\<^sub>W_all_struct_inv where
  "cdcl\<^sub>W_all_struct_inv S \<longleftrightarrow>
    no_strange_atm S \<and>
    cdcl\<^sub>W_M_level_inv S \<and>
    (\<forall>s \<in># learned_clss S. \<not>tautology s) \<and>
    distinct_cdcl\<^sub>W_state S \<and>
    cdcl\<^sub>W_conflicting S \<and>
    all_decomposition_implies_m (init_clss S) (get_all_ann_decomposition (trail S)) \<and>
    cdcl\<^sub>W_learned_clause S"

lemma cdcl\<^sub>W_all_struct_inv_inv:
  assumes "cdcl\<^sub>W_restart S S'" and "cdcl\<^sub>W_all_struct_inv S"
  shows "cdcl\<^sub>W_all_struct_inv S'"
  unfolding cdcl\<^sub>W_all_struct_inv_def
proof (intro HOL.conjI)
  show "no_strange_atm S'"
    using cdcl\<^sub>W_restart_all_inv[OF assms(1)] assms(2) unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  show "cdcl\<^sub>W_M_level_inv S'"
    using cdcl\<^sub>W_restart_all_inv[OF assms(1)] assms(2) unfolding cdcl\<^sub>W_all_struct_inv_def by fast
  show "distinct_cdcl\<^sub>W_state S'"
     using cdcl\<^sub>W_restart_all_inv[OF assms(1)] assms(2) unfolding cdcl\<^sub>W_all_struct_inv_def by fast
  show "cdcl\<^sub>W_conflicting S'"
     using cdcl\<^sub>W_restart_all_inv[OF assms(1)] assms(2) unfolding cdcl\<^sub>W_all_struct_inv_def by fast
  show "all_decomposition_implies_m (init_clss S') (get_all_ann_decomposition (trail S'))"
     using cdcl\<^sub>W_restart_all_inv[OF assms(1)] assms(2) unfolding cdcl\<^sub>W_all_struct_inv_def by fast
  show "cdcl\<^sub>W_learned_clause S'"
     using cdcl\<^sub>W_restart_all_inv[OF assms(1)] assms(2) unfolding cdcl\<^sub>W_all_struct_inv_def by fast

  show "\<forall>s\<in>#learned_clss S'. \<not> tautology s"
    using assms(1)[THEN learned_clss_are_not_tautologies] assms(2)
    unfolding cdcl\<^sub>W_all_struct_inv_def by fast
qed

lemma rtranclp_cdcl\<^sub>W_all_struct_inv_inv:
  assumes "cdcl\<^sub>W_restart\<^sup>*\<^sup>* S S'" and "cdcl\<^sub>W_all_struct_inv S"
  shows "cdcl\<^sub>W_all_struct_inv S'"
  using assms by induction (auto intro: cdcl\<^sub>W_all_struct_inv_inv)

lemma cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv:
  "cdcl\<^sub>W_stgy S T \<Longrightarrow> cdcl\<^sub>W_all_struct_inv S \<Longrightarrow> cdcl\<^sub>W_all_struct_inv T"
  by (meson cdcl\<^sub>W_stgy_tranclp_cdcl\<^sub>W_restart rtranclp_cdcl\<^sub>W_all_struct_inv_inv rtranclp_unfold)

lemma rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv:
  "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W_all_struct_inv S \<Longrightarrow> cdcl\<^sub>W_all_struct_inv T"
  by (induction rule: rtranclp_induct) (auto intro: cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv)

lemma beginning_not_decided_invert:
  assumes A: "M @ A = M' @ Decided K # H" and
  nm: "\<forall>m\<in>set M. \<not>is_decided m"
  shows "\<exists>M. A = M @ Decided K # H"
proof -
  have "A = drop (length M) (M' @ Decided K # H)"
    using arg_cong[OF A, of "drop (length M)"] by auto
  moreover have "drop (length M) (M' @ Decided K # H) = drop (length M) M' @ Decided K # H"
    using nm by (metis (no_types, lifting) A drop_Cons' drop_append ann_lit.disc(1) not_gr0
      nth_append nth_append_length nth_mem zero_less_diff)
  finally show ?thesis by fast
qed

end
end
