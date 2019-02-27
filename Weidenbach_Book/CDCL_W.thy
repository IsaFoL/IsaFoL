theory CDCL_W
  imports CDCL_W_Level Weidenbach_Book_Base.Wellfounded_More
begin

chapter \<open>Weidenbach's CDCL\<close>

text \<open>The organisation of the development is the following:
  \<^item> @{file CDCL_W.thy} contains the specification of the rules: the rules and the strategy are
  defined, and we proof the correctness of CDCL.
  \<^item> @{file CDCL_W_Termination.thy} contains the proof of termination, based on the book.
  \<^item> @{file CDCL_W_Merge.thy} contains a variant of the calculus: some rules of the raw calculus are
  always applied together (like the rules analysing the conflict and then backtracking). This is
  useful for the refinement from NOT.
  \<^item> @{file CDCL_WNOT.thy} proves the inclusion of Weidenbach's version of CDCL in NOT's version. We
  use here the version defined in @{file CDCL_W_Merge.thy}. We need this, because NOT's backjump
  corresponds to multiple applications of three rules in Weidenbach's calculus. We show also the
  termination of the calculus without strategy. There are two different refinement: on from NOT's to
  Weidenbach's CDCL and another to W's CDCL with strategy.

We have some variants build on the top of Weidenbach's CDCL calculus:
  \<^item> @{file CDCL_W_Incremental.thy} adds incrementality on the top of @{file CDCL_W.thy}. The way we
  are doing it is not compatible with @{file CDCL_W_Merge.thy}, because we add conflicts and the
  @{file CDCL_W_Merge.thy} cannot analyse conflicts added externally, since the conflict and
  analyse are merged.
  \<^item> @{file CDCL_W_Restart.thy} adds restart and forget while restarting. It is built on the top of
  @{file CDCL_W_Merge.thy}.
\<close>
section \<open>Weidenbach's CDCL with Multisets\<close>
declare upt.simps(2)[simp del]

subsection \<open>The State\<close>
text \<open>We will abstract the representation of clause and clauses via two locales. We here use
  multisets, contrary to @{file CDCL_W_Abstract_State.thy} where we assume only the existence of a
  conversion to the state.\<close>

locale state\<^sub>W_ops =
  fixes
    state :: "'st \<Rightarrow> ('v, 'v clause) ann_lits \<times> 'v clauses \<times> 'v clauses \<times> 'v clause option \<times>
      'b" and
    trail :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" and
    init_clss :: "'st \<Rightarrow> 'v clauses" and
    learned_clss :: "'st \<Rightarrow> 'v clauses" and
    conflicting :: "'st \<Rightarrow> 'v clause option" and

    cons_trail :: "('v, 'v clause) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and

    add_learned_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conflicting :: "'v clause option \<Rightarrow> 'st \<Rightarrow> 'st" and

    init_state :: "'v clauses \<Rightarrow> 'st"
begin

abbreviation hd_trail :: "'st \<Rightarrow> ('v, 'v clause) ann_lit" where
"hd_trail S \<equiv> hd (trail S)"

definition clauses :: "'st \<Rightarrow> 'v clauses" where
"clauses S = init_clss S + learned_clss S"

abbreviation resolve_cls where
"resolve_cls L D' E \<equiv> remove1_mset (-L) D' \<union># remove1_mset L E"

abbreviation state_butlast :: "'st \<Rightarrow> ('v, 'v clause) ann_lits \<times> 'v clauses \<times> 'v clauses
  \<times> 'v clause option" where
"state_butlast S \<equiv> (trail S, init_clss S, learned_clss S, conflicting S)"

definition additional_info :: "'st \<Rightarrow> 'b" where
"additional_info S = (\<lambda>(_, _, _, _, D). D) (state S)"

end

text \<open>We are using an abstract state to abstract away the detail of the implementation: we do not
  need to know how the clauses are represented internally, we just need to know that they can be
  converted to multisets.\<close>
text \<open>Weidenbach state is a five-tuple composed of:
  \<^enum> the trail is a list of decided literals;
  \<^enum> the initial set of clauses (that is not changed during the whole calculus);
  \<^enum> the learned clauses (clauses can be added or remove);
  \<^enum> the conflicting clause (if any has been found so far).\<close>
text \<open>
  Contrary to the original version, we have removed the maximum level of the trail, since the
  information is redundant and required an additional invariant.

  There are two different clause representation: one for the conflicting clause (@{typ "'v clause"},
  standing for conflicting clause) and one for the initial and learned clauses (@{typ "'v clause"},
  standing for clause). The representation of the clauses annotating literals in the trail
  is slightly different: being able to convert it to @{typ "'v clause"} is enough (needed for function
  @{term "hd_trail"} below).

  There are several axioms to state the independance of the different fields of the state: for
  example, adding a clause to the learned clauses does not change the trail.\<close>
locale state\<^sub>W_no_state =
  state\<^sub>W_ops
    state
    \<comment> \<open>functions about the state:\<close>
      \<comment> \<open>getter:\<close>
    trail init_clss learned_clss conflicting
      \<comment> \<open>setter:\<close>
    cons_trail tl_trail add_learned_cls remove_cls
    update_conflicting

      \<comment> \<open>Some specific states:\<close>
    init_state
  for
    state_eq :: "'st \<Rightarrow> 'st \<Rightarrow> bool" (infix "\<sim>" 50) and
    state :: "'st \<Rightarrow> ('v, 'v clause) ann_lits \<times> 'v clauses \<times> 'v clauses \<times> 'v clause option \<times>
      'b" and
    trail :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" and
    init_clss :: "'st \<Rightarrow> 'v clauses" and
    learned_clss :: "'st \<Rightarrow> 'v clauses" and
    conflicting :: "'st \<Rightarrow> 'v clause option" and

    cons_trail :: "('v, 'v clause) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_learned_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conflicting :: "'v clause option \<Rightarrow> 'st \<Rightarrow> 'st" and

    init_state :: "'v clauses \<Rightarrow> 'st" +
  assumes
    state_eq_ref[simp, intro]: \<open>S \<sim> S\<close> and
    state_eq_sym: \<open>S \<sim> T \<longleftrightarrow> T \<sim> S\<close> and
    state_eq_trans: \<open>S \<sim> T \<Longrightarrow> T \<sim> U' \<Longrightarrow> S \<sim> U'\<close> and
    state_eq_state: \<open>S \<sim> T \<Longrightarrow> state S = state T\<close> and

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

    update_conflicting:
      "\<And>S'. state st = (M, N, U, D, S') \<Longrightarrow>
        state (update_conflicting E st) = (M, N, U, E, S')" and

    init_state:
      "state_butlast (init_state N) = ([], N, {#}, None)" and

    cons_trail_state_eq:
      \<open>S \<sim> S' \<Longrightarrow> cons_trail L S \<sim> cons_trail L S'\<close> and

    tl_trail_state_eq:
      \<open>S \<sim> S' \<Longrightarrow> tl_trail S \<sim> tl_trail S'\<close> and

    add_learned_cls_state_eq:
      \<open>S \<sim> S' \<Longrightarrow> add_learned_cls C S \<sim> add_learned_cls C S'\<close> and

    remove_cls_state_eq:
      \<open>S \<sim> S' \<Longrightarrow> remove_cls C S \<sim> remove_cls C S'\<close> and

    update_conflicting_state_eq:
      \<open>S \<sim> S' \<Longrightarrow> update_conflicting D S \<sim> update_conflicting D S'\<close> and

    tl_trail_add_learned_cls_commute:
      \<open>tl_trail (add_learned_cls C T) \<sim> add_learned_cls C (tl_trail T)\<close> and
    tl_trail_update_conflicting:
      \<open>tl_trail (update_conflicting D T) \<sim> update_conflicting D (tl_trail T)\<close> and

    update_conflicting_update_conflicting:
      \<open>\<And>D D' S S'. S \<sim> S' \<Longrightarrow>
        update_conflicting D (update_conflicting D' S) \<sim> update_conflicting D S'\<close> and
    update_conflicting_itself:
    \<open>\<And>D S'. conflicting S' = D \<Longrightarrow> update_conflicting D S' \<sim> S'\<close>

locale state\<^sub>W =
  state\<^sub>W_no_state
    state_eq state
    \<comment> \<open>functions about the state:\<close>
      \<comment> \<open>getter:\<close>
    trail init_clss learned_clss conflicting
      \<comment> \<open>setter:\<close>
    cons_trail tl_trail add_learned_cls remove_cls
    update_conflicting

      \<comment> \<open>Some specific states:\<close>
    init_state
  for
    state_eq :: "'st \<Rightarrow> 'st \<Rightarrow> bool" (infix "\<sim>" 50) and
    state :: "'st \<Rightarrow> ('v, 'v clause) ann_lits \<times> 'v clauses \<times> 'v clauses \<times> 'v clause option \<times>
      'b" and
    trail :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" and
    init_clss :: "'st \<Rightarrow> 'v clauses" and
    learned_clss :: "'st \<Rightarrow> 'v clauses" and
    conflicting :: "'st \<Rightarrow> 'v clause option" and

    cons_trail :: "('v, 'v clause) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_learned_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conflicting :: "'v clause option \<Rightarrow> 'st \<Rightarrow> 'st" and

    init_state :: "'v clauses \<Rightarrow> 'st" +
  assumes
    state_prop[simp]:
      \<open>state S = (trail S, init_clss S, learned_clss S, conflicting S, additional_info S)\<close>
begin

lemma
  trail_cons_trail[simp]:
    "trail (cons_trail L st) = L # trail st" and
  trail_tl_trail[simp]: "trail (tl_trail st) = tl (trail st)" and
  trail_add_learned_cls[simp]:
    "trail (add_learned_cls C st) = trail st" and
  trail_remove_cls[simp]:
    "trail (remove_cls C st) = trail st" and
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
  learned_clss_update_conflicting[simp]:
    "learned_clss (update_conflicting E st) = learned_clss st" and

  conflicting_cons_trail[simp]:
    "conflicting (cons_trail M st) = conflicting st" and
  conflicting_tl_trail[simp]:
    "conflicting (tl_trail st) = conflicting st" and
  conflicting_add_learned_cls[simp]:
    "conflicting (add_learned_cls C st) = conflicting st"
    and
  conflicting_remove_cls[simp]:
    "conflicting (remove_cls C st) = conflicting st" and
  conflicting_update_conflicting[simp]:
    "conflicting (update_conflicting E st) = E" and

  init_state_trail[simp]: "trail (init_state N) = []" and
  init_state_clss[simp]: "init_clss (init_state N) = N" and
  init_state_learned_clss[simp]: "learned_clss (init_state N) = {#}" and
  init_state_conflicting[simp]: "conflicting (init_state N) = None"
  using cons_trail[of st] tl_trail[of st] add_learned_cls[of st _ _ _ _ C]
    update_conflicting[of st _ _ _ _ _ _]
    remove_cls[of st _ _ _ _ C]
    init_state[of N]
  by auto

lemma
  shows
    clauses_cons_trail[simp]:
      "clauses (cons_trail M S) = clauses S" and
    (* non-standard to avoid name clash with NOT's clauses_tl_trail *)
    clss_tl_trail[simp]: "clauses (tl_trail S) = clauses S" and
    clauses_add_learned_cls_unfolded:
      "clauses (add_learned_cls U S) = {#U#} + learned_clss S + init_clss S"
      and
    clauses_update_conflicting[simp]: "clauses (update_conflicting D S) = clauses S" and
    clauses_remove_cls[simp]:
      "clauses (remove_cls C S) = removeAll_mset C (clauses S)" and
    clauses_add_learned_cls[simp]:
      "clauses (add_learned_cls C S) = {#C#} + clauses S" and
    clauses_init_state[simp]: "clauses (init_state N) = N"
    by (auto simp: ac_simps replicate_mset_plus clauses_def intro: multiset_eqI)

lemma state_eq_trans': \<open>S \<sim> S' \<Longrightarrow> T \<sim> S' \<Longrightarrow> T \<sim> S\<close>
  by (meson state_eq_trans state_eq_sym)

abbreviation backtrack_lvl :: "'st \<Rightarrow> nat" where
\<open>backtrack_lvl S \<equiv> count_decided (trail S)\<close>

named_theorems state_simp \<open>contains all theorems of the form @{term \<open>S \<sim> T \<Longrightarrow> P S = P T\<close>}.
  These theorems can cause a signefecant blow-up of the simp-space\<close>

lemma
  shows
    state_eq_trail[state_simp]: "S \<sim> T \<Longrightarrow> trail S = trail T" and
    state_eq_init_clss[state_simp]: "S \<sim> T \<Longrightarrow> init_clss S = init_clss T" and
    state_eq_learned_clss[state_simp]: "S \<sim> T \<Longrightarrow> learned_clss S = learned_clss T" and
    state_eq_conflicting[state_simp]: "S \<sim> T \<Longrightarrow> conflicting S = conflicting T" and
    state_eq_clauses[state_simp]: "S \<sim> T \<Longrightarrow> clauses S = clauses T" and
    state_eq_undefined_lit[state_simp]: "S \<sim> T \<Longrightarrow> undefined_lit (trail S) L = undefined_lit (trail T) L" and
    state_eq_backtrack_lvl[state_simp]: "S \<sim> T \<Longrightarrow> backtrack_lvl S = backtrack_lvl T"
  using state_eq_state unfolding clauses_def by auto

lemma state_eq_conflicting_None:
  "S \<sim> T \<Longrightarrow> conflicting T = None \<Longrightarrow> conflicting S = None"
  using state_eq_state unfolding clauses_def by auto

text \<open>We combine all simplification rules about @{term state_eq} in a single list of theorems. While
  they are handy as simplification rule as long as we are working on the state, they also cause a
  \<^emph>\<open>huge\<close> slow-down in all other cases.\<close>

declare state_simp[simp]

function reduce_trail_to :: "'a list \<Rightarrow> 'st \<Rightarrow> 'st" where
"reduce_trail_to F S =
  (if length (trail S) = length F \<or> trail S = [] then S else reduce_trail_to F (tl_trail S))"
by fast+
termination
  by (relation "measure (\<lambda>(_, S). length (trail S))") simp_all

declare reduce_trail_to.simps[simp del]

lemma reduce_trail_to_induct:
  assumes
    \<open>\<And>F S. length (trail S) = length F \<Longrightarrow> P F S\<close> and
    \<open>\<And>F S. trail S = [] \<Longrightarrow> P F S\<close> and
    \<open>\<And>F S. length (trail S) \<noteq> length F \<Longrightarrow> trail S \<noteq> [] \<Longrightarrow> P F (tl_trail S) \<Longrightarrow> P F S\<close>
  shows
    \<open>P F S\<close>
  apply (induction rule: reduce_trail_to.induct)
  subgoal for F S using assms
    by (cases \<open>length (trail S) = length F\<close>; cases \<open>trail S = []\<close>) auto
  done

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
  by (metis conflicting_update_trail)

lemma trail_eq_reduce_trail_to_eq:
  "trail S = trail T \<Longrightarrow> trail (reduce_trail_to F S) = trail (reduce_trail_to F T)"
  apply (induction F S arbitrary: T rule: reduce_trail_to.induct)
  by (metis trail_tl_trail reduce_trail_to.simps)

lemma reduce_trail_to_trail_tl_trail_decomp[simp]:
  "trail S = F' @ Decided K # F \<Longrightarrow> trail (reduce_trail_to F S) = F "
  apply (rule reduce_trail_to_skip_beginning[of _ "F' @ Decided K # []"])
  by (cases F') (auto simp add: tl_append reduce_trail_to_skip_beginning)

lemma reduce_trail_to_add_learned_cls[simp]:
  "trail (reduce_trail_to F (add_learned_cls C S)) = trail (reduce_trail_to F S)"
  by (rule trail_eq_reduce_trail_to_eq) auto

lemma reduce_trail_to_remove_learned_cls[simp]:
  "trail (reduce_trail_to F (remove_cls C S)) = trail (reduce_trail_to F S)"
  by (rule trail_eq_reduce_trail_to_eq) auto

lemma reduce_trail_to_update_conflicting[simp]:
  "trail (reduce_trail_to F (update_conflicting C S)) = trail (reduce_trail_to F S)"
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
   apply (auto; fail)
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

lemma reduce_trail_to_state_eq:
  \<open>S \<sim> S' \<Longrightarrow> length M = length M' \<Longrightarrow> reduce_trail_to M S \<sim> reduce_trail_to M' S'\<close>
  apply (induction M S arbitrary: M' S' rule: reduce_trail_to_induct)
   apply ((auto;fail)+)[2]
  by (simp add: reduce_trail_to_length_ne tl_trail_state_eq)

lemma conflicting_cons_trail_conflicting[iff]:
  "conflicting (cons_trail L S) = None \<longleftrightarrow> conflicting S = None"
  using conflicting_cons_trail[of L S] map_option_is_None by fastforce+

lemma conflicting_add_learned_cls_conflicting[iff]:
  "conflicting (add_learned_cls C S) = None \<longleftrightarrow> conflicting S = None"
  by fastforce+

lemma reduce_trail_to_compow_tl_trail_le:
  \<open>length M < length (trail M') \<Longrightarrow> reduce_trail_to M M' = (tl_trail^^(length (trail M') - length M)) M'\<close>
  apply (induction M\<equiv>M S\<equiv>M' arbitrary: M M' rule: reduce_trail_to.induct)
  subgoal for F S
    apply (subst reduce_trail_to.simps)
    apply (cases \<open>length F < length (trail S) - Suc 0\<close>)
    apply (auto simp: less_iff_Suc_add funpow_swap1)
    apply (subgoal_tac \<open>k=0\<close>)
    apply auto
    by presburger
  done

lemma reduce_trail_to_compow_tl_trail_eq:
  \<open>length M = length (trail M') \<Longrightarrow> reduce_trail_to M M' = (tl_trail^^(length (trail M') - length M)) M'\<close>
  by auto

lemma tl_trail_reduce_trail_to_cons:
  \<open>length (L # M) < length (trail M') \<Longrightarrow> tl_trail (reduce_trail_to (L # M) M') = reduce_trail_to M M'\<close>
  by (auto simp: reduce_trail_to_compow_tl_trail_le funpow_swap1
      reduce_trail_to_compow_tl_trail_eq less_iff_Suc_add)

lemma compow_tl_trail_add_learned_cls_swap:
  \<open>(tl_trail ^^ n) (add_learned_cls D S) \<sim> add_learned_cls D ((tl_trail ^^ n) S)\<close>
  by (induction n)
   (auto intro: tl_trail_add_learned_cls_commute state_eq_trans
      tl_trail_state_eq)

lemma reduce_trail_to_add_learned_cls_state_eq:
  \<open>length M \<le> length (trail S) \<Longrightarrow>
  reduce_trail_to M (add_learned_cls D S) \<sim> add_learned_cls D (reduce_trail_to M S)\<close>
  by (cases \<open>length M < length (trail S)\<close>)
    (auto simp: compow_tl_trail_add_learned_cls_swap reduce_trail_to_compow_tl_trail_le
      reduce_trail_to_compow_tl_trail_eq)

lemma compow_tl_trail_update_conflicting_swap:
  \<open>(tl_trail ^^ n) (update_conflicting D S) \<sim> update_conflicting D ((tl_trail ^^ n) S)\<close>
  by (induction n)
   (auto intro: tl_trail_add_learned_cls_commute state_eq_trans
      tl_trail_state_eq tl_trail_update_conflicting)

lemma reduce_trail_to_update_conflicting_state_eq:
  \<open>length M \<le> length (trail S) \<Longrightarrow>
  reduce_trail_to M (update_conflicting D S) \<sim> update_conflicting D (reduce_trail_to M S)\<close>
  by (cases \<open>length M < length (trail S)\<close>)
    (auto simp: compow_tl_trail_add_learned_cls_swap reduce_trail_to_compow_tl_trail_le
      reduce_trail_to_compow_tl_trail_eq compow_tl_trail_update_conflicting_swap)

lemma
  additional_info_cons_trail[simp]:
    \<open>additional_info (cons_trail L S) = additional_info S\<close> and
  additional_info_tl_trail[simp]:
    "additional_info (tl_trail S) = additional_info S" and
  additional_info_add_learned_cls_unfolded:
    "additional_info (add_learned_cls U S) = additional_info S" and
  additional_info_update_conflicting[simp]:
    "additional_info (update_conflicting D S) = additional_info S" and
  additional_info_remove_cls[simp]:
    "additional_info (remove_cls C S) = additional_info S" and
  additional_info_add_learned_cls[simp]:
    "additional_info (add_learned_cls C S) = additional_info S"
  unfolding additional_info_def
    using tl_trail[of S] cons_trail[of S] add_learned_cls[of S]
    update_conflicting[of S] remove_cls[of S]
  by (cases \<open>state S\<close>; auto; fail)+

lemma additional_info_reduce_trail_to[simp]:
  \<open>additional_info (reduce_trail_to F S) = additional_info S\<close>
  by (induction F S rule: reduce_trail_to.induct)
    (metis additional_info_tl_trail reduce_trail_to.simps)

lemma reduce_trail_to:
  "state (reduce_trail_to F S) =
    ((if length (trail S) \<ge> length F
    then drop (length (trail S) - length F) (trail S)
    else []), init_clss S, learned_clss S, conflicting S, additional_info S)"
proof (induction F S rule: reduce_trail_to.induct)
  case (1 F S) note IH = this
  show ?case
  proof (cases "trail S")
    case Nil
    then show ?thesis using IH by (subst state_prop) auto
  next
    case (Cons L M)
    show ?thesis
    proof (cases "Suc (length M) > length F")
      case True
      then have "Suc (length M) - length F = Suc (length M - length F)"
        by auto
      then show ?thesis
        using Cons True reduce_trail_to_length_ne[of S F] IH by (auto simp del: state_prop)
    next
      case False
      then show ?thesis
        using IH reduce_trail_to_length_ne[of S F] apply (subst state_prop)
        by (simp add: trail_reduce_trail_to_drop)
    qed
  qed
qed

end \<comment> \<open>end of \<open>state\<^sub>W\<close> locale\<close>


subsection \<open>CDCL Rules\<close>
text \<open>Because of the strategy we will later use, we distinguish propagate, conflict from the other
  rules\<close>
locale conflict_driven_clause_learning\<^sub>W =
  state\<^sub>W
    state_eq
    state
    \<comment> \<open>functions for the state:\<close>
      \<comment> \<open>access functions:\<close>
    trail init_clss learned_clss conflicting
      \<comment> \<open>changing state:\<close>
    cons_trail tl_trail add_learned_cls remove_cls
    update_conflicting

      \<comment> \<open>get state:\<close>
    init_state
  for
    state_eq :: "'st \<Rightarrow> 'st \<Rightarrow> bool" (infix "\<sim>" 50) and
    state :: "'st \<Rightarrow> ('v, 'v clause) ann_lits \<times> 'v clauses \<times> 'v clauses \<times> 'v clause option \<times>
      'b" and
    trail :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" and
    init_clss :: "'st \<Rightarrow> 'v clauses" and
    learned_clss :: "'st \<Rightarrow> 'v clauses" and
    conflicting :: "'st \<Rightarrow> 'v clause option" and

    cons_trail :: "('v, 'v clause) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_learned_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
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
  conflicting S = Some (add_mset L D) \<Longrightarrow>
  (Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S)) \<Longrightarrow>
  get_level (trail S) L = backtrack_lvl S \<Longrightarrow>
  get_level (trail S) L = get_maximum_level (trail S) (add_mset L D') \<Longrightarrow>
  get_maximum_level (trail S) D' \<equiv> i \<Longrightarrow>
  get_level (trail S) K = i + 1 \<Longrightarrow>
  D' \<subseteq># D \<Longrightarrow>
  clauses S \<Turnstile>pm add_mset L D' \<Longrightarrow>
  T \<sim> cons_trail (Propagated L (add_mset L D'))
        (reduce_trail_to M1
          (add_learned_cls (add_mset L D')
            (update_conflicting None S))) \<Longrightarrow>
  backtrack S T"

inductive_cases backtrackE: "backtrack S T"

text \<open>Here is the normal backtrack rule from Weidenbach's book:\<close>
inductive simple_backtrack :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
simple_backtrack_rule: "
  conflicting S = Some (add_mset L D) \<Longrightarrow>
  (Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S)) \<Longrightarrow>
  get_level (trail S) L = backtrack_lvl S \<Longrightarrow>
  get_level (trail S) L = get_maximum_level (trail S) (add_mset L D) \<Longrightarrow>
  get_maximum_level (trail S) D \<equiv> i \<Longrightarrow>
  get_level (trail S) K = i + 1 \<Longrightarrow>
  T \<sim> cons_trail (Propagated L (add_mset L D))
        (reduce_trail_to M1
          (add_learned_cls (add_mset L D)
            (update_conflicting None S))) \<Longrightarrow>
  simple_backtrack S T"

inductive_cases simple_backtrackE: "simple_backtrack S T"

text \<open>This is a generalised version of backtrack: It is general enough te also include
  OCDCL's version.\<close>
inductive backtrackg :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
backtrackg_rule: "
  conflicting S = Some (add_mset L D) \<Longrightarrow>
  (Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S)) \<Longrightarrow>
  get_level (trail S) L = backtrack_lvl S \<Longrightarrow>
  get_level (trail S) L = get_maximum_level (trail S) (add_mset L D') \<Longrightarrow>
  get_maximum_level (trail S) D' \<equiv> i \<Longrightarrow>
  get_level (trail S) K = i + 1 \<Longrightarrow>
  D' \<subseteq># D \<Longrightarrow>
  T \<sim> cons_trail (Propagated L (add_mset L D'))
        (reduce_trail_to M1
          (add_learned_cls (add_mset L D')
            (update_conflicting None S))) \<Longrightarrow>
  backtrackg S T"

inductive_cases backtrackgE: "backtrackg S T"

inductive decide :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
decide_rule:
  "conflicting S = None \<Longrightarrow>
  undefined_lit (trail S) L \<Longrightarrow>
  atm_of L \<in> atms_of_mm (init_clss S) \<Longrightarrow>
  T \<sim> cons_trail (Decided L) S \<Longrightarrow>
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

text \<open>
  Christoph's version restricts restarts to the the case where \<open>\<not>M\<Turnstile> N+U\<close>. While it is possible to
  implement this (by watching a clause), This is an unnecessary restriction.
\<close>
inductive restart :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
restart: "state S = (M, N, U, None, S') \<Longrightarrow>
  U' \<subseteq># U \<Longrightarrow>
  state T = ([], N, U', None, S') \<Longrightarrow>
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
  removeAll_mset C (clauses S) \<Turnstile>pm C \<Longrightarrow>
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
  by (induction rule: cdcl\<^sub>W.induct) (auto intro: cdcl\<^sub>W_restart.intros simp del: state_prop)

lemma rtranclp_cdcl\<^sub>W_cdcl\<^sub>W_restart:
  \<open>cdcl\<^sub>W\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W_restart\<^sup>*\<^sup>* S T\<close>
  apply (induction rule: rtranclp_induct)
   apply (auto; fail)[]
  by (meson cdcl\<^sub>W_cdcl\<^sub>W_restart rtranclp.rtrancl_into_rtrancl)

lemma cdcl\<^sub>W_restart_all_rules_induct[consumes 1, case_names propagate conflict forget restart decide
    skip resolve backtrack]:
  fixes S :: 'st
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
  fixes S :: 'st
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
      removeAll_mset C (clauses S) \<Turnstile>pm C \<Longrightarrow>
      T \<sim> remove_cls C S \<Longrightarrow>
      P S T" and
    restartH: "\<And>T U. conflicting S = None \<Longrightarrow>
      state T = ([], init_clss S, U, None, additional_info S) \<Longrightarrow>
      U \<subseteq># learned_clss S \<Longrightarrow>
      P S T" and
    decideH: "\<And>L T. conflicting S = None \<Longrightarrow>
      undefined_lit (trail S) L \<Longrightarrow>
      atm_of L \<in> atms_of_mm (init_clss S) \<Longrightarrow>
      T \<sim> cons_trail (Decided L) S \<Longrightarrow>
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
    backtrackH: "\<And>L D K i M1 M2 T D'.
      conflicting S = Some (add_mset L D) \<Longrightarrow>
      (Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S)) \<Longrightarrow>
      get_level (trail S) L = backtrack_lvl S \<Longrightarrow>
      get_level (trail S) L = get_maximum_level (trail S) (add_mset L D') \<Longrightarrow>
      get_maximum_level (trail S) D' \<equiv> i \<Longrightarrow>
      get_level (trail S) K = i+1 \<Longrightarrow>
      D' \<subseteq># D \<Longrightarrow>
      clauses S \<Turnstile>pm add_mset L D' \<Longrightarrow>
      T \<sim> cons_trail (Propagated L (add_mset L D'))
            (reduce_trail_to M1
              (add_learned_cls (add_mset L D')
                (update_conflicting None S))) \<Longrightarrow>
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
  then show ?case by (auto elim!: backtrackE intro!: backtrackH simp del: state_simp)
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
      \<Longrightarrow> T \<sim> cons_trail (Decided L) S
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
    backtrackH: "\<And>L D K i M1 M2 T D'.
      conflicting S = Some (add_mset L D) \<Longrightarrow>
      (Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S)) \<Longrightarrow>
      get_level (trail S) L = backtrack_lvl S \<Longrightarrow>
      get_level (trail S) L = get_maximum_level (trail S) (add_mset L D') \<Longrightarrow>
      get_maximum_level (trail S) D' \<equiv> i \<Longrightarrow>
      get_level (trail S) K = i+1 \<Longrightarrow>
      D' \<subseteq># D \<Longrightarrow>
      clauses S \<Turnstile>pm add_mset L D' \<Longrightarrow>
      T \<sim> cons_trail (Propagated L (add_mset L D'))
            (reduce_trail_to M1
              (add_learned_cls (add_mset L D')
                (update_conflicting None S))) \<Longrightarrow>
       P S T"
  shows "P S T"
  using cdcl\<^sub>W_restart apply (induct T rule: cdcl\<^sub>W_o.induct)
  subgoal using assms(2) by (auto elim: decideE; fail)
  subgoal apply (elim cdcl\<^sub>W_bjE skipE resolveE backtrackE)
    apply (frule skipH; simp; fail)
    apply (cases "trail S"; auto elim!: resolveE intro!: resolveH; fail)
    apply (frule backtrackH; simp; fail)
    done
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

lemma backtrack_backtrackg:
  \<open>backtrack S T \<Longrightarrow> backtrackg S T\<close>
  unfolding backtrack.simps backtrackg.simps
  by blast

lemma simple_backtrack_backtrackg:
  \<open>simple_backtrack S T \<Longrightarrow> backtrackg S T\<close>
  unfolding simple_backtrack.simps backtrackg.simps
  by blast


subsection \<open>Structural Invariants\<close>

subsubsection \<open>Properties of the trail\<close>

text \<open>We here establish that:
  \<^item> the consistency of the trail;
  \<^item> the fact that there is no duplicate in the trail.\<close>

text \<open>
\begin{nit}
  As one can see in the following proof, the properties of the levels are \<^emph>\<open>required\<close> to prove
  \cwref{prop:prop:cdclconsis}{Item 1 page 94}. However, this point is only mentioned \<^emph>\<open>later\<close>,
  and only in the proof of \cwref{prop:prop:cdclbacktrack}{Item 7 page 95}.
\end{nit}\<close>
lemma backtrack_lit_skiped:
  assumes
    L: "get_level (trail S) L = backtrack_lvl S" and
    M1: "(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S))" and
    no_dup: "no_dup (trail S)" and
    lev_K: "get_level (trail S) K = i + 1"
  shows "undefined_lit M1 L"
proof (rule ccontr)
  let ?M = "trail S"
  assume L_in_M1: "\<not> ?thesis"
  obtain M2' where
    Mc: "trail S = M2' @ M2 @ Decided K # M1"
    using M1 by blast
  have Kc: \<open>undefined_lit M2' K\<close> and KM2: \<open>undefined_lit M2 K\<close> \<open>atm_of L \<noteq> atm_of K\<close> and
    \<open>undefined_lit M2' L\<close> \<open>undefined_lit M2 L\<close>
    using L_in_M1 no_dup unfolding Mc by (auto simp: atm_of_eq_atm_of dest: defined_lit_no_dupD)
  then have g_M_eq_g_M1: "get_level ?M L = get_level M1 L"
    using L_in_M1 unfolding Mc by auto
  then have "get_level M1 L < Suc i"
    using count_decided_ge_get_level[of M1 L] KM2 lev_K Kc unfolding Mc by auto
  moreover have "Suc i \<le> backtrack_lvl S" using KM2 lev_K Kc unfolding Mc by (simp add: Mc)
  ultimately show False using L g_M_eq_g_M1 by auto
qed

lemma cdcl\<^sub>W_restart_distinctinv_1:
  assumes
    "cdcl\<^sub>W_restart S S'" and
    n_d: "no_dup (trail S)"
  shows "no_dup (trail S')"
  using assms(1)
proof (induct rule: cdcl\<^sub>W_restart_all_induct)
  case (backtrack L D K i M1 M2 T D') note decomp = this(2) and L = this(3) and lev_K = this(6) and
    T = this(9)
  obtain c where Mc: "trail S = c @ M2 @ Decided K # M1"
    using decomp by auto
  have "no_dup (M2 @ Decided K # M1)"
    using Mc n_d by (auto dest: no_dup_appendD simp: defined_lit_map image_Un)
  moreover have L_M1: "undefined_lit M1 L"
    using backtrack_lit_skiped[of S L K M1 M2 i] L decomp lev_K n_d
    unfolding defined_lit_map lits_of_def by fast
  ultimately show ?case using decomp T n_d by (auto dest: no_dup_appendD)
qed (use n_d in auto)

text \<open>\cwref{prop:prop:cdclconsis}{Item 1 page 94}\<close>
lemma cdcl\<^sub>W_restart_consistent_inv_2:
  assumes
    "cdcl\<^sub>W_restart S S'" and
    "no_dup (trail S)"
  shows "consistent_interp (lits_of_l (trail S'))"
  using cdcl\<^sub>W_restart_distinctinv_1[OF assms] distinct_consistent_interp by fast

definition cdcl\<^sub>W_M_level_inv :: "'st \<Rightarrow> bool" where
"cdcl\<^sub>W_M_level_inv S \<longleftrightarrow>
  consistent_interp (lits_of_l (trail S))
  \<and> no_dup (trail S)"

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
  using assms cdcl\<^sub>W_restart_consistent_inv_2 cdcl\<^sub>W_restart_distinctinv_1
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

lemma backtrack_ex_decomp:
  assumes
    M_l: "no_dup (trail S)" and
    i_S: "i < backtrack_lvl S"
  shows "\<exists>K M1 M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S)) \<and>
    get_level (trail S) K = Suc i"
proof -
  let ?M = "trail S"
  have "i < count_decided (trail S)"
    using i_S by auto
  then obtain c K c' where tr_S: "trail S = c @ Decided K # c'" and
    lev_K: "get_level (trail S) K = Suc i"
    using le_count_decided_decomp[of "trail S" i] M_l by auto
  obtain M1 M2 where "(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S))"
    using Decided_cons_in_get_all_ann_decomposition_append_Decided_cons unfolding tr_S by fast
  then show ?thesis using lev_K by blast
qed

lemma backtrack_lvl_backtrack_decrease:
  assumes inv: "cdcl\<^sub>W_M_level_inv S" and bt: "backtrack S T"
  shows "backtrack_lvl T < backtrack_lvl S"
  using inv bt le_count_decided_decomp[of "trail S" "backtrack_lvl T"]
  unfolding cdcl\<^sub>W_M_level_inv_def
  by (fastforce elim!: backtrackE simp: append_assoc[of _ _ "_# _", symmetric]
    simp del: append_assoc)


subsubsection \<open>Compatibility with @{term state_eq}\<close>

declare state_eq_trans[trans]

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
    by (auto simp: clauses_def)
  have T': \<open>T' \<sim> cons_trail (Propagated L C) S'\<close>
    using state_eq_trans[of T' T] SS' TT'
    by (meson T cons_trail_state_eq state_eq_sym state_eq_trans)
  show ?thesis
    apply (rule propagate_rule[of _ C])
    using SS' conf C' L tr undef TT' T T' by auto
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

  have T': \<open>T' \<sim> update_conflicting (Some D) S'\<close>
    using state_eq_trans[of T' T] SS' TT'
    by (meson T update_conflicting_state_eq state_eq_sym state_eq_trans)
  show ?thesis
    apply (rule conflict_rule[of _ D])
    using SS' conf D' tr TT' T T' by auto
qed

lemma backtrack_state_eq_compatible:
  assumes
    bt: "backtrack S T" and
    SS': "S \<sim> S'" and
    TT': "T \<sim> T'"
  shows "backtrack S' T'"
proof -
  obtain D L K i M1 M2 D' where
    conf: "conflicting S = Some (add_mset L D)" and
    decomp: "(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S))" and
    lev: "get_level (trail S) L = backtrack_lvl S" and
    max: "get_level (trail S) L = get_maximum_level (trail S) (add_mset L D')" and
    max_D: "get_maximum_level (trail S) D' \<equiv> i" and
    lev_K: "get_level (trail S) K = Suc i" and
    D'_D: \<open>D' \<subseteq># D\<close> and
    NU_DL: \<open>clauses S \<Turnstile>pm add_mset L D'\<close> and
    T: "T \<sim> cons_trail (Propagated L (add_mset L D'))
                (reduce_trail_to M1
                  (add_learned_cls (add_mset L D')
                    (update_conflicting None S)))"
    using bt by (elim backtrackE) metis
  let ?D = \<open>add_mset L D\<close>
  let ?D' = \<open>add_mset L D'\<close>
  have D': "conflicting S' = Some ?D"
    using SS' conf by (cases "conflicting S'") auto

  have T'_S: "T' \<sim> cons_trail (Propagated L ?D')
     (reduce_trail_to M1 (add_learned_cls ?D'
     (update_conflicting None S)))"
    using T TT' state_eq_sym state_eq_trans by blast
  have T': "T' \<sim> cons_trail (Propagated L ?D')
     (reduce_trail_to M1 (add_learned_cls ?D'
     (update_conflicting None S')))"
    apply (rule state_eq_trans[OF T'_S])
    by (auto simp: cons_trail_state_eq reduce_trail_to_state_eq add_learned_cls_state_eq
        update_conflicting_state_eq SS')
  show ?thesis
    apply (rule backtrack_rule[of _ L D K M1 M2 D' i])
    subgoal by (rule D')
    subgoal using TT' decomp SS' by auto
    subgoal using lev TT'  SS' by auto
    subgoal using max TT' SS' by auto
    subgoal using max_D TT' SS' by auto
    subgoal using lev_K TT' SS' by auto
    subgoal by (rule D'_D)
    subgoal using NU_DL TT' SS' by auto
    subgoal by (rule T')
    done
qed

lemma decide_state_eq_compatible:
  assumes
    dec: "decide S T" and
    SS': "S \<sim> S'" and
    TT': "T \<sim> T'"
  shows "decide S' T'"
  using assms
proof -
  obtain L :: "'v literal" where
    f4: "undefined_lit (trail S) L"
      "atm_of L \<in> atms_of_mm (init_clss S)"
      "T \<sim> cons_trail (Decided L) S"
    using dec decide.simps by blast
  have "cons_trail (Decided L) S' \<sim> T'"
    using f4 SS' TT' by (metis (no_types) cons_trail_state_eq state_eq_sym
        state_eq_trans)
  then show ?thesis
    using f4 SS' TT' dec by (auto simp: decide.simps state_eq_sym)
qed

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
    using SS' raw by (cases "conflicting S'") auto
  have T': \<open>T' \<sim> tl_trail S'\<close>
    by (meson SS' T TT' state_eq_sym state_eq_trans tl_trail_state_eq)
  show ?thesis
    apply (rule skip_rule)
       using tr raw L E T SS' apply (auto; fail)[]
      using E' apply (simp; fail)
     using E' SS' L raw E apply ((auto; fail)+)[2]
    using T' by auto
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
  have T': \<open>T' \<sim> update_conflicting (Some (remove1_mset (- L) D' \<union># remove1_mset L E))
    (tl_trail S')\<close>
  proof -
    have "tl_trail S \<sim> tl_trail S'"
      using SS' by (auto simp: tl_trail_state_eq)
    then show ?thesis
      using T T'T \<open>D = D'\<close> state_eq_trans update_conflicting_state_eq by blast
  qed
  show ?thesis
    apply (rule resolve_rule)
           using tr SS' apply (simp; fail)
         using hd SS' apply (simp; fail)
        using L apply (simp; fail)
       using D' apply (simp; fail)
      using D' SS' raw LD apply (auto; fail)[]
     using D' SS' raw LD i apply (auto; fail)[]
    using T' by auto
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
    ent: \<open>removeAll_mset C (clauses S) \<Turnstile>pm C\<close> and
    T: "T \<sim> remove_cls C S"
    using forget by (elim forgetE) simp
  have T': \<open>T' \<sim> remove_cls C S'\<close>
    by (meson SS' T TT' remove_cls_state_eq state_eq_sym state_eq_trans)
  show ?thesis
    apply (rule forget_rule)
          using SS' conf apply (simp; fail)
         using C SS' apply (simp; fail)
        using SS' tr apply (simp; fail)
       using SS' C1 apply (simp; fail)
      using SS' C2 apply (simp; fail)
     using ent SS' apply (simp; fail)
    using T' by auto
qed

lemma cdcl\<^sub>W_restart_state_eq_compatible:
  assumes
    "cdcl\<^sub>W_restart S T" and "\<not>restart S T" and
    "S \<sim> S'"
    "T \<sim> T'"
  shows "cdcl\<^sub>W_restart S' T'"
  using assms by (meson backtrack backtrack_state_eq_compatible bj cdcl\<^sub>W_restart.simps
    cdcl\<^sub>W_o_rule_cases cdcl\<^sub>W_rf.cases conflict_state_eq_compatible decide decide_state_eq_compatible
    forget forget_state_eq_compatible propagate_state_eq_compatible
    resolve resolve_state_eq_compatible skip skip_state_eq_compatible state_eq_ref)

lemma cdcl\<^sub>W_bj_state_eq_compatible:
  assumes
    "cdcl\<^sub>W_bj S T"
    "T \<sim> T'"
  shows "cdcl\<^sub>W_bj S T'"
  using assms by (meson backtrack backtrack_state_eq_compatible cdcl\<^sub>W_bjE resolve
    resolve_state_eq_compatible skip skip_state_eq_compatible state_eq_ref)

lemma tranclp_cdcl\<^sub>W_bj_state_eq_compatible:
  assumes
    "cdcl\<^sub>W_bj\<^sup>+\<^sup>+ S T"
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
  case (step T U) note IH = this(3)[OF this(4)]
  have "cdcl\<^sub>W_restart\<^sup>+\<^sup>+ S T"
    using tranclp_mono[of cdcl\<^sub>W_bj cdcl\<^sub>W_restart] step.hyps(1) cdcl\<^sub>W_restart.other cdcl\<^sub>W_o.bj by blast
  then have "cdcl\<^sub>W_bj\<^sup>+\<^sup>+ T T'"
    using \<open>U \<sim> T'\<close> cdcl\<^sub>W_bj_state_eq_compatible[of T U] \<open>cdcl\<^sub>W_bj T U\<close> by auto
  then show ?case
    using IH[of T] by auto
qed

lemma skip_unique:
  "skip S T \<Longrightarrow> skip S T' \<Longrightarrow> T \<sim> T'"
  by (auto elim!: skipE intro: state_eq_trans')

lemma resolve_unique:
  "resolve S T \<Longrightarrow> resolve S T' \<Longrightarrow> T \<sim> T'"
  by (fastforce intro: state_eq_trans' elim: resolveE)

text \<open>The same holds for backtrack, but more invariants are needed.\<close>


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
  by (auto
    dest!: tranclp_cdcl\<^sub>W_restart_consistent_inv
    dest: tranclp_mono_explicit[of cdcl\<^sub>W_o _ _ cdcl\<^sub>W_restart] cdcl\<^sub>W_o_no_more_init_clss
    simp: other)

lemma rtranclp_cdcl\<^sub>W_o_no_more_init_clss:
  assumes
    "cdcl\<^sub>W_o\<^sup>*\<^sup>* S S'" and
    inv: "cdcl\<^sub>W_M_level_inv S"
  shows "init_clss S = init_clss S'"
  using assms unfolding rtranclp_unfold by (auto intro: tranclp_cdcl\<^sub>W_o_no_more_init_clss)

lemma cdcl\<^sub>W_restart_init_clss:
  assumes
    "cdcl\<^sub>W_restart S T"
  shows "init_clss S = init_clss T"
  using assms by (induction rule: cdcl\<^sub>W_restart_all_induct)
  (auto simp: not_in_iff)

lemma rtranclp_cdcl\<^sub>W_restart_init_clss:
  "cdcl\<^sub>W_restart\<^sup>*\<^sup>* S T \<Longrightarrow> init_clss S = init_clss T"
  by (induct rule: rtranclp_induct) (auto dest: cdcl\<^sub>W_restart_init_clss rtranclp_cdcl\<^sub>W_restart_consistent_inv)

lemma tranclp_cdcl\<^sub>W_restart_init_clss:
  "cdcl\<^sub>W_restart\<^sup>+\<^sup>+ S T \<Longrightarrow> init_clss S = init_clss T"
  using rtranclp_cdcl\<^sub>W_restart_init_clss[of S T] unfolding rtranclp_unfold by auto


subsubsection \<open>Learned Clause\<close>

text \<open>This invariant shows that:
  \<^item> the learned clauses are entailed by the initial set of clauses.
  \<^item> the conflicting clause is entailed by the initial set of clauses.
  \<^item> the marks belong to the clauses. We could also restrict it to entailment by the clauses, to
  allow forgetting this clauses.\<close>

definition "cdcl\<^sub>W_learned_clause (S :: 'st) \<longleftrightarrow>
  ((\<forall>T. conflicting S = Some T \<longrightarrow> clauses S \<Turnstile>pm T)
  \<and> set (get_all_mark_of_propagated (trail S)) \<subseteq> set_mset (clauses S))"

text \<open>This is a more reduced version of the previous invariant. This is mostly interesting for BnB. However,
  inlining it in the previous definition is a major undertaking.

TODO: remove this duplicate.\<close>
definition "reasons_in_clauses (S :: 'st) \<longleftrightarrow>
  (set (get_all_mark_of_propagated (trail S)) \<subseteq> set_mset (clauses S))"

text \<open>\cwref{prop:prop:cdclConflClause}{Item 3 page 95} for the inital state and some additional structural
  properties about the trail.\<close>
lemma cdcl\<^sub>W_learned_clause_S0_cdcl\<^sub>W_restart[simp]:
   "cdcl\<^sub>W_learned_clause (init_state N)"
  unfolding cdcl\<^sub>W_learned_clause_def by auto

text \<open>\cwref{prop:prop:cdclvaluation}{Item 4 page 95}\<close>
lemma cdcl\<^sub>W_restart_learned_clss:
  assumes
    "cdcl\<^sub>W_restart S S'" and
    learned: "cdcl\<^sub>W_learned_clause S" and
    lev_inv: "cdcl\<^sub>W_M_level_inv S"
  shows "cdcl\<^sub>W_learned_clause S'"
  using assms(1)
proof (induct rule: cdcl\<^sub>W_restart_all_induct)
  case (backtrack L D K i M1 M2 T D') note decomp = this(2) and confl = this(1) and lev_K = this (6)
    and T = this(9)
  show ?case
    using decomp learned confl T unfolding cdcl\<^sub>W_learned_clause_def
    by (auto dest!: get_all_ann_decomposition_exists_prepend)
next
  case (resolve L C M D) note trail = this(1) and CL = this(2) and confl = this(4) and DL = this(5)
    and lvl = this(6) and T = this(7)
  moreover
    have "clauses S \<Turnstile>pm add_mset L C"
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
      intro!: true_clss_cls_union_mset_true_clss_cls_or_not_true_clss_cls_or[of _ L])
next
  case (restart T)
  then show ?case
    using learned
    by (auto
      simp: clauses_def cdcl\<^sub>W_learned_clause_def
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
qed (use learned in \<open>auto simp: cdcl\<^sub>W_learned_clause_def clauses_def\<close>)

lemma rtranclp_cdcl\<^sub>W_restart_learned_clss:
  assumes
    "cdcl\<^sub>W_restart\<^sup>*\<^sup>* S S'" and
    "cdcl\<^sub>W_M_level_inv S"
    "cdcl\<^sub>W_learned_clause S"
  shows "cdcl\<^sub>W_learned_clause S'"
  using assms by induction (auto dest: cdcl\<^sub>W_restart_learned_clss intro: rtranclp_cdcl\<^sub>W_restart_consistent_inv)

lemma cdcl\<^sub>W_restart_reasons_in_clauses:
  assumes
    "cdcl\<^sub>W_restart S S'" and
    learned: "reasons_in_clauses S"
  shows "reasons_in_clauses S'"
  using assms(1) learned
  by (induct rule: cdcl\<^sub>W_restart_all_induct)
    (auto simp: reasons_in_clauses_def dest!: get_all_ann_decomposition_exists_prepend)

lemma rtranclp_cdcl\<^sub>W_restart_reasons_in_clauses:
  assumes
    "cdcl\<^sub>W_restart\<^sup>*\<^sup>* S S'" and
    learned: "reasons_in_clauses S"
  shows "reasons_in_clauses S'"
  using assms(1) learned
  by (induct rule: rtranclp_induct)
    (auto simp: cdcl\<^sub>W_restart_reasons_in_clauses)


subsubsection \<open>No alien atom in the state\<close>

text \<open>This invariant means that all the literals are in the set of clauses. These properties are
  implicit in Weidenbach's book.\<close>
definition "no_strange_atm S' \<longleftrightarrow>
    (\<forall>T. conflicting S' = Some T \<longrightarrow> atms_of T \<subseteq> atms_of_mm (init_clss S'))
  \<and> (\<forall>L mark. Propagated L mark \<in> set (trail S') \<longrightarrow> atms_of mark \<subseteq> atms_of_mm (init_clss S'))
  \<and> atms_of_mm (learned_clss S') \<subseteq> atms_of_mm (init_clss S')
  \<and> atm_of ` (lits_of_l (trail S')) \<subseteq> atms_of_mm (init_clss S')"

lemma no_strange_atm_decomp:
  assumes "no_strange_atm S"
  shows "conflicting S = Some T \<Longrightarrow> atms_of T \<subseteq> atms_of_mm (init_clss S)"
  and "(\<forall>L mark. Propagated L mark \<in> set (trail S) \<longrightarrow> atms_of mark \<subseteq> atms_of_mm (init_clss S))"
  and "atms_of_mm (learned_clss S) \<subseteq> atms_of_mm (init_clss S)"
  and "atm_of ` (lits_of_l (trail S)) \<subseteq> atms_of_mm (init_clss S)"
  using assms unfolding no_strange_atm_def by blast+

lemma no_strange_atm_S0 [simp]: "no_strange_atm (init_state N)"
  unfolding no_strange_atm_def by auto

lemma propagate_no_strange_atm_inv:
  assumes
    "propagate S T" and
    alien: "no_strange_atm S"
  shows "no_strange_atm T"
  using assms(1)
proof (induction rule: propagate.induct)
  case (propagate_rule C L T) note confl = this(1) and C = this(2) and C_L = this(3) and
    tr = this(4) and undef = this(5) and T = this(6)
  have atm_CL: "atms_of C \<subseteq> atms_of_mm (init_clss S)"
    using C alien unfolding no_strange_atm_def
    by (auto simp: clauses_def atms_of_ms_def)
  show ?case
    unfolding no_strange_atm_def
  proof (intro conjI allI impI, goal_cases)
    case (1 C)
    then show ?case
      using confl T undef by auto
  next
    case (2 L' mark')
    then show ?case
      using C_L T alien undef atm_CL unfolding no_strange_atm_def clauses_def by (auto 5 5)
  next
    case 3
    show ?case using T alien undef unfolding no_strange_atm_def by auto
  next
    case 4
    show ?case
      using T alien undef C_L atm_CL unfolding no_strange_atm_def by (auto simp: atms_of_def)
  qed
qed

lemma atms_of_ms_learned_clss_restart_state_in_atms_of_ms_learned_clssI:
  "atms_of_mm (learned_clss S) \<subseteq> atms_of_mm (init_clss S) \<Longrightarrow>
   x \<in> atms_of_mm (learned_clss T) \<Longrightarrow>
   learned_clss T \<subseteq># learned_clss S \<Longrightarrow>
   x \<in> atms_of_mm (init_clss S)"
  by (meson atms_of_ms_mono contra_subsetD set_mset_mono)

lemma (in -) atms_of_subset_mset_mono: \<open>D' \<subseteq># D \<Longrightarrow> atms_of D' \<subseteq> atms_of D\<close>
  by (auto simp: atms_of_def)

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
    (\<forall>L mark. Propagated L mark \<in> set (trail S') \<longrightarrow> atms_of mark \<subseteq> atms_of_mm (init_clss S')) \<and>
    atms_of_mm (learned_clss S') \<subseteq> atms_of_mm (init_clss S') \<and>
    atm_of ` (lits_of_l (trail S')) \<subseteq> atms_of_mm (init_clss S')"
    (is "?C S' \<and> ?M S' \<and> ?U S' \<and> ?V S'")
  using assms(1)
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
    T = this(7)
  have H: "\<And>L mark. Propagated L mark \<in> set (trail S) \<Longrightarrow> atms_of mark \<subseteq> atms_of_mm (init_clss S)"
    using decided by simp
  show ?case unfolding clauses_def apply (intro conjI)
       using conf confl T trail C unfolding clauses_def apply (auto dest!: H)[]
      using T trail C C_le apply (auto dest!: H)[]
     using T learned C_le atms_of_ms_remove_subset[of "set_mset (learned_clss S)"] apply auto[]
   using T trail C_le apply (auto simp: clauses_def lits_of_def)[]
   done
next
  case (backtrack L D K i M1 M2 T D') note confl = this(1) and decomp = this(2) and
    lev_K = this(6) and D_D' = this(7) and M1_D' = this(8) and T = this(9)
  have "?C T"
    using conf T decomp lev lev_K by (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
  moreover have "set M1 \<subseteq> set (trail S)"
    using decomp by auto
  then have M: "?M T"
    using decided conf confl T decomp lev lev_K D_D'
    by (auto simp: image_subset_iff clauses_def cdcl\<^sub>W_M_level_inv_decomp
        dest!: atms_of_subset_mset_mono)
  moreover have "?U T"
    using learned decomp conf confl T lev lev_K D_D' unfolding clauses_def
    by (auto simp: cdcl\<^sub>W_M_level_inv_decomp dest: atms_of_subset_mset_mono)
  moreover have "?V T"
    using M conf confl trail T decomp lev lev_K
    by (auto simp: cdcl\<^sub>W_M_level_inv_decomp atms_of_def
      dest!: get_all_ann_decomposition_exists_prepend)
  ultimately show ?case by blast
next
  case (resolve L C M D T) note trail_S = this(1) and confl = this(4) and T = this(7)
  let ?T = "update_conflicting (Some (resolve_cls L D C)) (tl_trail S)"
  have "?C ?T"
    using confl trail_S conf decided by (auto dest!: in_atms_of_minusD)
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
  using cdcl\<^sub>W_restart_no_strange_atm_explicit[OF assms(1)] assms(2,3) unfolding no_strange_atm_def
  by fast

lemma rtranclp_cdcl\<^sub>W_restart_no_strange_atm_inv:
  assumes "cdcl\<^sub>W_restart\<^sup>*\<^sup>* S S'" and "no_strange_atm S" and "cdcl\<^sub>W_M_level_inv S"
  shows "no_strange_atm S'"
  using assms by (induction rule: rtranclp_induct)
  (auto intro: cdcl\<^sub>W_restart_no_strange_atm_inv rtranclp_cdcl\<^sub>W_restart_consistent_inv)


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
  assumes "distinct_cdcl\<^sub>W_state S"
  shows
    "\<forall>T. conflicting S = Some T \<longrightarrow> distinct_mset T" and
    "distinct_mset_mset (learned_clss S)" and
    "distinct_mset_mset (init_clss S)" and
    "\<forall>L mark. (Propagated L mark \<in> set (trail S) \<longrightarrow> distinct_mset mark)"
  using assms unfolding distinct_cdcl\<^sub>W_state_def by blast+

lemma distinct_cdcl\<^sub>W_state_decomp_2:
  assumes "distinct_cdcl\<^sub>W_state S" and "conflicting S = Some T"
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
  case (backtrack L D K i M1 M2 D')
  then show ?case
    using lev_inv unfolding distinct_cdcl\<^sub>W_state_def
    by (auto dest: get_all_ann_decomposition_incl distinct_mset_mono simp: cdcl\<^sub>W_M_level_inv_decomp)
next
  case restart
  then show ?case
    unfolding distinct_cdcl\<^sub>W_state_def distinct_mset_set_def clauses_def by auto
next
  case resolve
  then show ?case
    by (auto simp add: distinct_cdcl\<^sub>W_state_def distinct_mset_set_def clauses_def)
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

definition cdcl\<^sub>W_conflicting :: "'st \<Rightarrow> bool" where
  "cdcl\<^sub>W_conflicting S \<longleftrightarrow>
    (\<forall>T. conflicting S = Some T \<longrightarrow> trail S \<Turnstile>as CNot T) \<and> every_mark_is_a_conflict S"

lemma backtrack_atms_of_D_in_M1:
  fixes S T :: 'st and D D' :: \<open>'v clause\<close> and K L :: \<open>'v literal\<close> and i :: nat and
    M1 M2:: \<open>('v, 'v clause) ann_lits\<close>
  assumes
    inv: "no_dup (trail S)" and
    i: "get_maximum_level (trail S) D' \<equiv> i" and
    decomp: "(Decided K # M1, M2)
       \<in> set (get_all_ann_decomposition (trail S))" and
    S_lvl: "backtrack_lvl S = get_maximum_level (trail S) (add_mset L D')" and
    S_confl: "conflicting S = Some D" and
    lev_K: "get_level (trail S) K = Suc i" and
    T: "T \<sim> cons_trail K''
                (reduce_trail_to M1
                  (add_learned_cls (add_mset L D')
                    (update_conflicting None S)))" and
    confl: "\<forall>T. conflicting S = Some T \<longrightarrow> trail S \<Turnstile>as CNot T" and
    D_D': \<open>D' \<subseteq># D\<close>
  shows "atms_of D' \<subseteq> atm_of ` lits_of_l (tl (trail T))"
proof (rule ccontr)
  let ?k = "get_maximum_level (trail S) (add_mset L D')"

  have "trail S \<Turnstile>as CNot D" using confl S_confl by auto
  then have "trail S \<Turnstile>as CNot D'"
    using D_D' by (auto simp: true_annots_true_cls_def_iff_negation_in_model)
  then have vars_of_D: "atms_of D' \<subseteq> atm_of ` lits_of_l (trail S)" unfolding atms_of_def
    by (meson image_subsetI true_annots_CNot_all_atms_defined)

  obtain M0 where M: "trail S = M0 @ M2 @ Decided K # M1"
    using decomp by auto

  have max: "?k = count_decided (M0 @ M2 @ Decided K # M1)"
    using S_lvl unfolding M by simp
  assume a: "\<not> ?thesis"
  then obtain L' where
    L': "L' \<in> atms_of D'" and
    L'_notin_M1: "L' \<notin> atm_of ` lits_of_l M1"
    using T decomp inv by (auto simp: cdcl\<^sub>W_M_level_inv_decomp)

  obtain L'' where
    "L'' \<in># D'" and
    L'': "L' = atm_of L''"
    using L' L'_notin_M1 unfolding atms_of_def by auto
  then have L'_in: "defined_lit (M0 @ M2 @ Decided K # []) L''"
    using vars_of_D L'_notin_M1 L' unfolding M
    by (auto dest: in_atms_of_minusD
        simp: defined_lit_append defined_lit_map lits_of_def image_Un)
  have L''_M1: \<open>undefined_lit M1 L''\<close>
    using L'_notin_M1 L'' by (auto simp: defined_lit_map lits_of_def)
  have \<open>undefined_lit (M0 @ M2) K\<close>
    using inv by (auto simp: cdcl\<^sub>W_M_level_inv_def M)
  then have "count_decided M1 = i"
    using lev_K unfolding M by (auto simp: image_Un)
  then have lev_L'':
    "get_level (trail S) L'' = get_level (M0 @ M2 @ Decided K # []) L'' + i"
    using L'_notin_M1 L''_M1 L'' get_level_skip_end[OF L'_in[unfolded L''], of M1] M by auto
  moreover {
    consider
      (M0) "defined_lit M0 L''" |
      (M2) "defined_lit M2 L''" |
      (K) "L' = atm_of K"
      using inv L'_in unfolding L''
      by (auto simp: cdcl\<^sub>W_M_level_inv_def defined_lit_append)
    then have "get_level (M0 @ M2 @ Decided K # []) L'' \<ge> Suc 0"
    proof cases
      case M0
      then have "L' \<noteq> atm_of K"
        using \<open>undefined_lit (M0 @ M2) K\<close> unfolding L'' by (auto simp: atm_of_eq_atm_of)
      then show ?thesis using M0 unfolding L'' by auto
    next
      case M2
      then have "undefined_lit (M0 @ Decided K # []) L''"
        by (rule defined_lit_no_dupD(1))
          (use inv in \<open>auto simp: M L'' cdcl\<^sub>W_M_level_inv_def no_dup_def\<close>)
      then show ?thesis using M2 unfolding L'' by (auto simp: image_Un)
    next
      case K
      have "undefined_lit (M0 @ M2) L''"
        by (rule defined_lit_no_dupD(3)[of \<open>[Decided K]\<close>  _ M1])
          (use inv K in \<open>auto simp: M L'' cdcl\<^sub>W_M_level_inv_def no_dup_def\<close>)
      then show ?thesis using K unfolding L'' by (auto simp: image_Un)
    qed }
  ultimately have "get_level (trail S) L'' \<ge> i + 1"
    using lev_L'' unfolding M by simp
  then have "get_maximum_level (trail S) D' \<ge> i + 1"
    using get_maximum_level_ge_get_level[OF \<open>L'' \<in># D'\<close>, of "trail S"] by auto
  then show False using i by auto
qed

lemma distinct_atms_of_incl_not_in_other:
  assumes
    a1: "no_dup (M @ M')" and
    a2: "atms_of D \<subseteq> atm_of ` lits_of_l M'" and
    a3: "x \<in> atms_of D"
  shows "x \<notin> atm_of ` lits_of_l M"
  using assms by (auto simp: atms_of_def no_dup_def atm_of_eq_atm_of lits_of_def)

lemma backtrack_M1_CNot_D':
  fixes S T :: 'st and D D' :: \<open>'v clause\<close> and K L :: \<open>'v literal\<close> and i :: nat and
    M1 M2:: \<open>('v, 'v clause) ann_lits\<close>
  assumes
    inv: "no_dup (trail S)" and
    i: "get_maximum_level (trail S) D' \<equiv> i" and
    decomp: "(Decided K # M1, M2)
       \<in> set (get_all_ann_decomposition (trail S))" and
    S_lvl: "backtrack_lvl S = get_maximum_level (trail S) (add_mset L D')" and
    S_confl: "conflicting S = Some D" and
    lev_K: "get_level (trail S) K = Suc i" and
    T: "T \<sim> cons_trail K''
                (reduce_trail_to M1
                  (add_learned_cls (add_mset L D')
                    (update_conflicting None S)))" and
    confl: "\<forall>T. conflicting S = Some T \<longrightarrow> trail S \<Turnstile>as CNot T" and
    D_D': \<open>D' \<subseteq># D\<close>
  shows "M1 \<Turnstile>as CNot D'" and
    \<open>atm_of (lit_of K'') = atm_of L \<Longrightarrow> no_dup (trail T)\<close>
proof -
  obtain M0 where M: "trail S = M0 @ M2 @ Decided K # M1"
    using decomp by auto
  have vars_of_D: "atms_of D' \<subseteq> atm_of ` lits_of_l M1"
    using backtrack_atms_of_D_in_M1[OF assms] decomp T by auto
  have "no_dup (trail S)" using inv by (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
  then have vars_in_M1: "\<forall>x \<in> atms_of D'. x \<notin> atm_of ` lits_of_l (M0 @ M2 @ Decided K # [])"
    using vars_of_D distinct_atms_of_incl_not_in_other[of "M0 @M2 @ Decided K # []" M1]
    unfolding M by auto
  have "trail S \<Turnstile>as CNot D"
    using S_confl confl unfolding M true_annots_true_cls_def_iff_negation_in_model
    by (auto dest!: in_diffD)
  then have "trail S \<Turnstile>as CNot D'"
    using D_D' unfolding true_annots_true_cls_def_iff_negation_in_model by auto
  then show M1_D': "M1 \<Turnstile>as CNot D'"
    using true_annots_remove_if_notin_vars[of "M0 @ M2 @ Decided K # []" M1 "CNot D'"]
      vars_in_M1 S_confl confl unfolding M lits_of_def by simp
  have M1: \<open>count_decided M1 = i\<close>
    using lev_K inv i vars_in_M1 unfolding M
    by simp
  have lev_L: \<open>get_level (trail S) L = backtrack_lvl S\<close> and \<open>i < backtrack_lvl S\<close>
    using S_lvl i lev_K
    by (auto simp: max_def get_maximum_level_add_mset)
  have \<open>no_dup M1\<close>
    using T decomp inv by (auto simp: M dest: no_dup_appendD)
  moreover have \<open>undefined_lit M1 L\<close>
    using backtrack_lit_skiped[of S L, OF _ decomp]
    using lev_L inv i M1 \<open>i < backtrack_lvl S\<close> unfolding M
    by (auto simp:  split: if_splits)
  moreover have \<open>atm_of (lit_of K'') = atm_of L \<Longrightarrow>
    undefined_lit M1 L \<longleftrightarrow> undefined_lit M1 (lit_of K'')\<close>
    by (simp add: defined_lit_map)
  ultimately show \<open>atm_of (lit_of K'') = atm_of L \<Longrightarrow> no_dup (trail T)\<close>
    using T decomp inv by auto
qed

text \<open>\cwref{prop:prop:cdclPropLitsUnsat}{Item 5 page 95}\<close>
lemma cdcl\<^sub>W_restart_propagate_is_conclusion:
  assumes
    "cdcl\<^sub>W_restart S S'" and
    inv: "cdcl\<^sub>W_M_level_inv S" and
    decomp: "all_decomposition_implies_m (clauses S) (get_all_ann_decomposition (trail S))" and
    learned: "cdcl\<^sub>W_learned_clause S" and
    confl: "\<forall>T. conflicting S = Some T \<longrightarrow> trail S \<Turnstile>as CNot T" and
    alien: "no_strange_atm S"
  shows "all_decomposition_implies_m (clauses S') (get_all_ann_decomposition (trail S'))"
  using assms(1)
proof (induct rule: cdcl\<^sub>W_restart_all_induct)
  case restart
  then show ?case by auto
next
  case (forget C T) note C = this(2) and cls_C = this(6) and T = this(7)
  show ?case
    unfolding all_decomposition_implies_def Ball_def
  proof (intro allI, clarify)
    fix a b
    assume "(a, b) \<in> set (get_all_ann_decomposition (trail T))"
    then have "unmark_l a \<union> set_mset (clauses S) \<Turnstile>ps unmark_l b"
      using decomp T by (auto simp add: all_decomposition_implies_def)
    moreover {
      have a1:"C \<in># clauses S"
        using C by (auto simp: clauses_def)
      have "clauses T = clauses (remove_cls C S)"
        using T by auto
      then have "clauses T \<Turnstile>psm clauses S"
        using a1 by (metis (no_types) clauses_remove_cls cls_C insert_Diff order_refl
            set_mset_minus_replicate_mset(1) true_clss_clss_def true_clss_clss_insert) }
    ultimately show "unmark_l a \<union> set_mset (clauses T) \<Turnstile>ps unmark_l b"
      using true_clss_clss_generalise_true_clss_clss by blast
  qed
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
  case (propagate C L T) note propa = this(2) and L = this(3) and S_CNot_C = this(4) and
  undef = this(5) and T = this(6)
  obtain a y where ay: "hd (get_all_ann_decomposition (trail S)) = (a, y)"
    by (cases "hd (get_all_ann_decomposition (trail S))")
  then have M: "trail S = y @ a" using get_all_ann_decomposition_decomp by blast
  have M': "set (get_all_ann_decomposition (trail S))
    = insert (a, y) (set (tl (get_all_ann_decomposition (trail S))))"
    using ay by (cases "get_all_ann_decomposition (trail S)") auto
  have unm_ay: "unmark_l a \<union> set_mset (clauses S) \<Turnstile>ps unmark_l y"
    using decomp ay unfolding all_decomposition_implies_def
    by (cases "get_all_ann_decomposition (trail S)") fastforce+
  then have a_Un_N_M: "unmark_l a \<union> set_mset (clauses S) \<Turnstile>ps unmark_l (trail S)"
    unfolding M by (auto simp add: all_in_true_clss_clss image_Un)

  have "unmark_l a \<union> set_mset (clauses S) \<Turnstile>p {#L#}" (is "?I \<Turnstile>p _")
  proof (rule true_clss_cls_plus_CNot)
    show "?I \<Turnstile>p add_mset L (remove1_mset L C)"
      apply (rule true_clss_clss_in_imp_true_clss_cls[of _ "set_mset (clauses S)"])
      using learned propa L by (auto simp: cdcl\<^sub>W_learned_clause_def true_annot_CNot_diff)
  next
    have "unmark_l (trail S) \<Turnstile>ps CNot (remove1_mset L C)"
      using S_CNot_C by (blast dest: true_annots_true_clss_clss)
    then show "?I \<Turnstile>ps CNot (remove1_mset L C)"
      using a_Un_N_M true_clss_clss_left_right true_clss_clss_union_l_r by blast
  qed
  moreover have "\<And>aa b.
      \<forall> (Ls, seen)\<in>set (get_all_ann_decomposition (y @ a)).
        unmark_l Ls \<union> set_mset (clauses S) \<Turnstile>ps unmark_l seen \<Longrightarrow>
        (aa, b) \<in> set (tl (get_all_ann_decomposition (y @ a))) \<Longrightarrow>
        unmark_l aa \<union> set_mset (clauses S) \<Turnstile>ps unmark_l b"
    by (metis (no_types, lifting) case_prod_conv get_all_ann_decomposition_never_empty_sym
      list.collapse list.set_intros(2))

  ultimately show ?case
    using decomp T undef unfolding ay all_decomposition_implies_def
    using M unm_ay ay by auto
next
  case (backtrack L D K i M1 M2 T D') note conf = this(1) and decomp' = this(2) and
    lev_L = this(3) and lev_K = this(6) and D_D' = this(7) and NU_LD' = this(8)
    and T = this(9)
  let ?D' = "remove1_mset L D"
  have "\<forall>l \<in> set M2. \<not>is_decided l"
    using get_all_ann_decomposition_snd_not_decided decomp' by blast
  obtain M0 where M: "trail S = M0 @ M2 @ Decided K # M1"
    using decomp' by auto
  let ?D = \<open>add_mset L D\<close>
  let ?D' = \<open>add_mset L D'\<close>
  show ?case unfolding all_decomposition_implies_def
  proof
    fix x
    assume "x \<in> set (get_all_ann_decomposition (trail T))"
    then have x: "x \<in> set (get_all_ann_decomposition (Propagated L ?D' # M1))"
      using T decomp' inv by (simp add: cdcl\<^sub>W_M_level_inv_decomp)
    let ?m = "get_all_ann_decomposition (Propagated L ?D' # M1)"
    let ?hd = "hd ?m"
    let ?tl = "tl ?m"
    consider
      (hd) "x = ?hd" |
      (tl) "x \<in> set ?tl"
      using x by (cases "?m") auto
    then show "case x of (Ls, seen) \<Rightarrow> unmark_l Ls \<union> set_mset (clauses T) \<Turnstile>ps unmark_l seen"
    proof cases
      case tl
      then have "x \<in> set (get_all_ann_decomposition (trail S))"
        using tl_get_all_ann_decomposition_skip_some[of x] by (simp add: list.set_sel(2) M)
      then show ?thesis
        using decomp learned decomp confl alien inv T M
        unfolding all_decomposition_implies_def cdcl\<^sub>W_M_level_inv_def
        by auto
    next
      case hd
      obtain M1' M1'' where M1: "hd (get_all_ann_decomposition M1) = (M1', M1'')"
        by (cases "hd (get_all_ann_decomposition M1)")
      then have x': "x = (M1', Propagated L ?D' # M1'')"
        using \<open>x = ?hd\<close> by auto
      have "(M1', M1'') \<in> set (get_all_ann_decomposition (trail S))"
        using M1[symmetric] hd_get_all_ann_decomposition_skip_some[OF M1[symmetric],
            of "M0 @ M2"] unfolding M by fastforce
      then have 1: "unmark_l M1' \<union> set_mset (clauses S) \<Turnstile>ps unmark_l M1''"
        using decomp unfolding all_decomposition_implies_def by auto

      have \<open>no_dup (trail S)\<close>
        using inv unfolding cdcl\<^sub>W_M_level_inv_def
	by blast
      then have M1_D': "M1 \<Turnstile>as CNot D'" and \<open>no_dup (trail T)\<close>
        using backtrack_M1_CNot_D'[of S D' \<open>i\<close> K M1 M2 L \<open>add_mset L D\<close> T \<open>Propagated L (add_mset L D')\<close>]
          confl inv backtrack by (auto simp: subset_mset_trans_add_mset)
      have "M1 = M1'' @ M1'" by (simp add: M1 get_all_ann_decomposition_decomp)
      have TT: "unmark_l M1' \<union> set_mset (clauses S) \<Turnstile>ps CNot D'"
        using true_annots_true_clss_cls[OF \<open>M1 \<Turnstile>as CNot D'\<close>] true_clss_clss_left_right[OF 1]
        unfolding \<open>M1 = M1'' @ M1'\<close> by (auto simp add: inf_sup_aci(5,7))
      have T': "unmark_l M1' \<union> set_mset (clauses S) \<Turnstile>p ?D'" using NU_LD' by auto
      moreover have "unmark_l M1' \<union> set_mset (clauses S) \<Turnstile>p {#L#}"
          using true_clss_cls_plus_CNot[OF T' TT] by auto
      ultimately show ?thesis
        using T' T decomp' inv 1 unfolding x' by (simp add: cdcl\<^sub>W_M_level_inv_decomp)
    qed
  qed
qed

lemma cdcl\<^sub>W_restart_propagate_is_false:
  assumes
    "cdcl\<^sub>W_restart S S'" and
    lev: "cdcl\<^sub>W_M_level_inv S" and
    learned: "cdcl\<^sub>W_learned_clause S" and
    decomp: "all_decomposition_implies_m (clauses S) (get_all_ann_decomposition (trail S))" and
    confl: "\<forall>T. conflicting S = Some T \<longrightarrow> trail S \<Turnstile>as CNot T" and
    alien: "no_strange_atm S" and
    mark_confl: "every_mark_is_a_conflict S"
  shows "every_mark_is_a_conflict S'"
  using assms(1)
proof (induct rule: cdcl\<^sub>W_restart_all_induct)
  case (propagate C L T) note LC = this(3) and confl = this(4) and undef = this(5) and T = this(6)
  show ?case
  proof (intro allI impI)
    fix L' mark a b
    assume "a @ Propagated L' mark # b = trail T"
    then consider
      (hd) "a = []" and "L = L'" and "mark = C" and "b = trail S" |
      (tl) "tl a @ Propagated L' mark # b = trail S"
      using T undef by (cases a) fastforce+
    then show "b \<Turnstile>as CNot (mark - {#L'#}) \<and> L' \<in># mark"
      using mark_confl confl LC by cases auto
  qed
next
  case (decide L) note undef[simp] = this(2) and T = this(4)
  have \<open>tl a @ Propagated La mark # b = trail S\<close>
    if \<open>a @ Propagated La mark # b = Decided L # trail S\<close> for a La mark b
    using that by (cases a) auto
  then show ?case using mark_confl T unfolding decide.hyps(1) by fastforce
next
  case (skip L C' M D T) note tr = this(1) and T = this(5)
  show ?case
  proof (intro allI impI)
    fix L' mark a b
    assume "a @ Propagated L' mark # b = trail T"
    then have "a @ Propagated L' mark # b = M" using tr T by simp
    then have "(Propagated L C' # a) @ Propagated L' mark # b = Propagated L C' # M" by auto
    moreover have \<open>b \<Turnstile>as CNot (mark - {#La#}) \<and> La \<in># mark\<close>
      if "a @ Propagated La mark # b = Propagated L C' # M" for La mark a b
      using mark_confl that unfolding skip.hyps(1) by simp
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
  case (backtrack L D K i M1 M2 T D') note conf = this(1) and decomp = this(2) and
    lev_K = this(6) and D_D' = this(7) and M1_D' = this(8) and T = this(9)
  have "\<forall>l \<in> set M2. \<not>is_decided l"
    using get_all_ann_decomposition_snd_not_decided decomp by blast
  obtain M0 where M: "trail S = M0 @ M2 @ Decided K # M1"
    using decomp by auto
  have [simp]: "trail (reduce_trail_to M1 (add_learned_cls D (update_conflicting None S))) = M1"
    using decomp lev by (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
  let ?D = "add_mset L D"
  let ?D' = "add_mset L D'"
  have M1_D': "M1 \<Turnstile>as CNot D'"
    using backtrack_M1_CNot_D'[of S D' \<open>i\<close> K M1 M2 L \<open>add_mset L D\<close> T \<open>Propagated L (add_mset L D')\<close>]
      confl lev backtrack by (auto simp: subset_mset_trans_add_mset cdcl\<^sub>W_M_level_inv_def)

  show ?case
  proof (intro allI impI)
    fix La :: "'v literal" and mark :: "'v clause" and a b :: "('v, 'v clause) ann_lits"
    assume "a @ Propagated La mark # b = trail T"
    then consider
      (hd_tr) "a = []" and
        "(Propagated La mark :: ('v, 'v clause) ann_lit) = Propagated L ?D'" and
        "b = M1" |
      (tl_tr) "tl a @ Propagated La mark # b = M1"
      using M T decomp lev by (cases a) (auto simp: cdcl\<^sub>W_M_level_inv_def)
    then show "b \<Turnstile>as CNot (mark - {#La#}) \<and> La \<in># mark"
    proof cases
      case hd_tr note A = this(1) and P = this(2) and b = this(3)
      show "b \<Turnstile>as CNot (mark - {#La#}) \<and> La \<in># mark"
        using P M1_D' b by auto
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
  moreover have "L \<notin># D"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have "- L \<in> lits_of_l M"
      using in_CNot_implies_uminus(2)[of L D "Propagated L C' # M"]
        \<open>Propagated L C' # M \<Turnstile>as CNot D\<close> by simp
    then show False
      using M_lev tr_S by (fastforce dest: cdcl\<^sub>W_M_level_inv_decomp(2)
          simp: Decided_Propagated_in_iff_in_lits_of_l)
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
    then have "-L \<notin># ?D" using \<open>distinct_mset (?D + {#- L#})\<close> by auto
    have "Propagated L (?C + {#L#}) # M \<Turnstile>as CNot ?D \<union> CNot {#- L#}"
      using confl tr confl_inv LC by (metis CNot_plus LD insert_DiffM2)
    then have "M \<Turnstile>as CNot ?D"
      using M_lev \<open>- L \<notin># ?D\<close> tr
      unfolding cdcl\<^sub>W_M_level_inv_def by (force intro: true_annots_lit_of_notin_skip)
    moreover assume "conflicting T = Some T'"
    ultimately show "trail T \<Turnstile>as CNot T'"
      using tr T by auto
  qed
qed (auto simp: M_lev cdcl\<^sub>W_M_level_inv_decomp)

lemma cdcl\<^sub>W_conflicting_decomp:
  assumes "cdcl\<^sub>W_conflicting S"
  shows
    "\<forall>T. conflicting S = Some T \<longrightarrow> trail S \<Turnstile>as CNot T" and
    "\<forall>L mark a b. a @ Propagated L mark # b = (trail S) \<longrightarrow>
       (b \<Turnstile>as CNot (mark - {#L#}) \<and> L \<in># mark)"
  using assms unfolding cdcl\<^sub>W_conflicting_def by blast+

lemma cdcl\<^sub>W_conflicting_decomp2:
  assumes "cdcl\<^sub>W_conflicting S" and "conflicting S = Some T"
  shows "trail S \<Turnstile>as CNot T"
  using assms unfolding cdcl\<^sub>W_conflicting_def by blast+

lemma cdcl\<^sub>W_conflicting_S0_cdcl\<^sub>W_restart[simp]:
  "cdcl\<^sub>W_conflicting (init_state N)"
  unfolding cdcl\<^sub>W_conflicting_def by auto

definition cdcl\<^sub>W_learned_clauses_entailed_by_init where
  \<open>cdcl\<^sub>W_learned_clauses_entailed_by_init S \<longleftrightarrow> init_clss S \<Turnstile>psm learned_clss S\<close>

lemma cdcl\<^sub>W_learned_clauses_entailed_init[simp]:
  \<open>cdcl\<^sub>W_learned_clauses_entailed_by_init (init_state N)\<close>
  by (auto simp: cdcl\<^sub>W_learned_clauses_entailed_by_init_def)

lemma cdcl\<^sub>W_learned_clauses_entailed:
  assumes
    cdcl\<^sub>W_restart: "cdcl\<^sub>W_restart S S'" and
    2: "cdcl\<^sub>W_learned_clause S" and
    9: \<open>cdcl\<^sub>W_learned_clauses_entailed_by_init S\<close>
  shows \<open>cdcl\<^sub>W_learned_clauses_entailed_by_init S'\<close>
    using cdcl\<^sub>W_restart 9
proof (induction rule: cdcl\<^sub>W_restart_all_induct)
  case backtrack
  then show ?case
    using assms unfolding cdcl\<^sub>W_learned_clause_def cdcl\<^sub>W_learned_clauses_entailed_by_init_def
    by (auto dest!: get_all_ann_decomposition_exists_prepend
      simp: clauses_def cdcl\<^sub>W_M_level_inv_decomp dest: true_clss_clss_left_right)
qed (auto simp: cdcl\<^sub>W_learned_clauses_entailed_by_init_def elim: true_clss_clssm_subsetE)

lemma rtranclp_cdcl\<^sub>W_learned_clauses_entailed:
  assumes
    cdcl\<^sub>W_restart: "cdcl\<^sub>W_restart\<^sup>*\<^sup>* S S'" and
    2: "cdcl\<^sub>W_learned_clause S" and
    4: "cdcl\<^sub>W_M_level_inv S" and
    9: \<open>cdcl\<^sub>W_learned_clauses_entailed_by_init S\<close>
  shows \<open>cdcl\<^sub>W_learned_clauses_entailed_by_init S'\<close>
  using assms apply (induction rule: rtranclp_induct)
   apply (simp; fail)
  using cdcl\<^sub>W_learned_clauses_entailed rtranclp_cdcl\<^sub>W_restart_learned_clss by blast


subsubsection \<open>Putting all the Invariants Together\<close>

lemma cdcl\<^sub>W_restart_all_inv:
  assumes
    cdcl\<^sub>W_restart: "cdcl\<^sub>W_restart S S'" and
    1: "all_decomposition_implies_m (clauses S) (get_all_ann_decomposition (trail S))" and
    2: "cdcl\<^sub>W_learned_clause S" and
    4: "cdcl\<^sub>W_M_level_inv S" and
    5: "no_strange_atm S" and
    7: "distinct_cdcl\<^sub>W_state S" and
    8: "cdcl\<^sub>W_conflicting S"
  shows
    "all_decomposition_implies_m (clauses S') (get_all_ann_decomposition (trail S'))" and
    "cdcl\<^sub>W_learned_clause S'" and
    "cdcl\<^sub>W_M_level_inv S'" and
    "no_strange_atm S'" and
    "distinct_cdcl\<^sub>W_state S'" and
    "cdcl\<^sub>W_conflicting S'"
proof -
  show S1: "all_decomposition_implies_m (clauses S') (get_all_ann_decomposition (trail S'))"
    using cdcl\<^sub>W_restart_propagate_is_conclusion[OF cdcl\<^sub>W_restart 4 1 2 _ 5] 8
    unfolding cdcl\<^sub>W_conflicting_def by blast
  show S2: "cdcl\<^sub>W_learned_clause S'" using cdcl\<^sub>W_restart_learned_clss[OF cdcl\<^sub>W_restart 2 4] .
  show S4: "cdcl\<^sub>W_M_level_inv S'" using cdcl\<^sub>W_restart_consistent_inv[OF cdcl\<^sub>W_restart 4] .
  show S5: "no_strange_atm S'" using cdcl\<^sub>W_restart_no_strange_atm_inv[OF cdcl\<^sub>W_restart 5 4] .
  show S7: "distinct_cdcl\<^sub>W_state S'" using distinct_cdcl\<^sub>W_state_inv[OF cdcl\<^sub>W_restart 4 7] .
  show S8: "cdcl\<^sub>W_conflicting S'"
    using cdcl\<^sub>W_conflicting_is_false[OF cdcl\<^sub>W_restart 4 _ _ 7] 8
    cdcl\<^sub>W_restart_propagate_is_false[OF cdcl\<^sub>W_restart 4 2 1 _ 5] unfolding cdcl\<^sub>W_conflicting_def
    by fast
qed

lemma rtranclp_cdcl\<^sub>W_restart_all_inv:
  assumes
    cdcl\<^sub>W_restart: "rtranclp cdcl\<^sub>W_restart S S'" and
    1: "all_decomposition_implies_m (clauses S) (get_all_ann_decomposition (trail S))" and
    2: "cdcl\<^sub>W_learned_clause S" and
    4: "cdcl\<^sub>W_M_level_inv S" and
    5: "no_strange_atm S" and
    7: "distinct_cdcl\<^sub>W_state S" and
    8: "cdcl\<^sub>W_conflicting S"
  shows
    "all_decomposition_implies_m (clauses S') (get_all_ann_decomposition (trail S'))" and
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

text \<open>\cwref{prop:prop:cdclUnsat}{Item 6 page 95}\<close>
lemma cdcl\<^sub>W_only_propagated_vars_unsat:
  assumes
    decided: "\<forall>x \<in> set M. \<not> is_decided x" and
    DN: "D \<in># clauses S" and
    D: "M \<Turnstile>as CNot D" and
    inv: "all_decomposition_implies_m (N + U) (get_all_ann_decomposition M)" and
    state: "state S = (M, N, U, k, C)" and
    learned_cl: "cdcl\<^sub>W_learned_clause S" and
    atm_incl: "no_strange_atm S"
  shows "unsatisfiable (set_mset (N + U))"
proof (rule ccontr)
  assume "\<not> unsatisfiable (set_mset (N + U))"
  then obtain I where
    I: "I \<Turnstile>s set_mset N" "I \<Turnstile>s set_mset U" and
    cons: "consistent_interp I" and
    tot: "total_over_m I (set_mset N)"
    unfolding satisfiable_def by auto
  have "atms_of_mm N \<union> atms_of_mm U = atms_of_mm N"
    using atm_incl state unfolding total_over_m_def no_strange_atm_def
    by (auto simp add: clauses_def)
  then have tot_N: "total_over_m I (set_mset N)" using tot unfolding total_over_m_def by auto
  moreover have "total_over_m I (set_mset (learned_clss S))"
    using atm_incl state tot_N unfolding no_strange_atm_def total_over_m_def total_over_set_def
    by auto
  ultimately have I_D: "I \<Turnstile> D"
    using I DN cons state unfolding true_clss_clss_def true_clss_def Ball_def
    by (auto simp add: clauses_def)

  have l0: "{unmark L |L. is_decided L \<and> L \<in> set M} = {}" using decided by auto
  have "atms_of_ms (set_mset (N+U) \<union> unmark_l M) = atms_of_mm N"
    using atm_incl state unfolding no_strange_atm_def by auto
  then have "total_over_m I (set_mset (N+U) \<union> unmark_l M)"
    using tot unfolding total_over_m_def by auto
  then have IM: "I \<Turnstile>s unmark_l M"
    using all_decomposition_implies_propagated_lits_are_implied[OF inv] cons I
    unfolding true_clss_clss_def l0 by auto
  have "-K \<in> I" if "K \<in># D" for K
    proof -
      have "-K \<in> lits_of_l M"
        using D that unfolding true_annots_def by force
      then show "-K \<in> I" using IM true_clss_singleton_lit_of_implies_incl by fastforce
    qed
  then have "\<not> I \<Turnstile> D" using cons unfolding true_cls_def true_lit_def consistent_interp_def by auto
  then show False using I_D by blast
qed

text \<open>\cwref{prop:prop:cdclPropLitsUnsat}{Item 5 page 95}\<close>
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

text \<open>\cwref{prop:prop:cdclbacktrack}{Item 7 page 95} (part 1)\<close>
lemma conflict_with_false_implies_unsat:
  assumes
    cdcl\<^sub>W_restart: "cdcl\<^sub>W_restart S S'" and
    lev: "cdcl\<^sub>W_M_level_inv S" and
    [simp]: "conflicting S' = Some {#}" and
    learned: "cdcl\<^sub>W_learned_clause S" and
    learned_entailed: \<open>cdcl\<^sub>W_learned_clauses_entailed_by_init S\<close>
  shows "unsatisfiable (set_mset (clauses S))"
  using assms
proof -
  have "cdcl\<^sub>W_learned_clause S'" using cdcl\<^sub>W_restart_learned_clss cdcl\<^sub>W_restart learned lev by auto
  then have entail_false: "clauses S' \<Turnstile>pm {#}" using assms(3) unfolding cdcl\<^sub>W_learned_clause_def by auto
  moreover have entailed: \<open>cdcl\<^sub>W_learned_clauses_entailed_by_init S'\<close>
    using cdcl\<^sub>W_learned_clauses_entailed[OF cdcl\<^sub>W_restart learned learned_entailed] .
  ultimately have "set_mset (init_clss S') \<Turnstile>ps {{#}}"
    unfolding cdcl\<^sub>W_learned_clauses_entailed_by_init_def
    by (auto simp: clauses_def dest: true_clss_clss_left_right)
  then have "clauses S \<Turnstile>pm {#}"
    by (simp add: cdcl\<^sub>W_restart_init_clss[OF assms(1)] clauses_def)
  then show ?thesis unfolding satisfiable_def true_clss_cls_def by auto
qed

text \<open>\cwref{prop:prop:cdclbacktrack}{Item 7 page 95} (part 2)\<close>
lemma conflict_with_false_implies_terminated:
  assumes "cdcl\<^sub>W_restart S S'" and "conflicting S = Some {#}"
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
  case (backtrack L D K i M1 M2 T D') note confl = this(1) and D_D' = this(7) and M1_D' = this(8) and
    NU_LD' = this(9)
  let ?D = \<open>add_mset L D\<close>
  let ?D' = \<open>add_mset L D'\<close>
  have "consistent_interp (lits_of_l (trail S))" using lev by (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
  moreover {
    have "trail S \<Turnstile>as CNot ?D"
      using conflicting confl unfolding cdcl\<^sub>W_conflicting_def by auto
    then have "lits_of_l (trail S) \<Turnstile>s CNot ?D"
      using true_annots_true_cls by blast }
  ultimately have "\<not>tautology ?D" using consistent_CNot_not_tautology by blast
  then have "\<not>tautology ?D'"
    using D_D' not_tautology_mono[of ?D' ?D] by auto
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
    \<and> state_butlast S = (map (\<lambda>L. Decided L) M, N, {#}, None)"
  using assms
proof (induct M)
  case Nil
  then show ?case apply - by (auto intro!: exI[of _ "init_state N"])
next
  case (Cons L M) note IH = this(1) and dist = this(2)
  have "consistent_interp (set M)" and "distinct M" and "atm_of ` set M \<subseteq> atms_of_mm N"
    using Cons.prems(1-3) unfolding consistent_interp_def by auto
  then obtain S where
    st: "cdcl\<^sub>W_restart\<^sup>*\<^sup>* (init_state N) S" and
    S: "state_butlast S = (map (\<lambda>L. Decided L) M, N, {#}, None)"
    using IH by blast
  let ?S\<^sub>0 = "cons_trail (Decided L) S"
  have undef: "undefined_lit (map (\<lambda>L. Decided L) M) L"
    using Cons.prems(1,2) unfolding defined_lit_def consistent_interp_def by fastforce
  moreover have "init_clss S = N"
    using S by blast
  moreover have "atm_of L \<in> atms_of_mm N" using Cons.prems(3) by auto
  moreover have undef: "undefined_lit (trail S) L"
    using S dist undef by (auto simp: defined_lit_map)
  ultimately have "cdcl\<^sub>W_restart S ?S\<^sub>0"
    using cdcl\<^sub>W_restart.other[OF cdcl\<^sub>W_o.decide[OF decide_rule[of S L ?S\<^sub>0]]] S
    by auto
  then have "cdcl\<^sub>W_restart\<^sup>*\<^sup>* (init_state N) ?S\<^sub>0"
    using st by auto
  then show ?case
    using S undef by (auto intro!: exI[of _ ?S\<^sub>0] simp del: state_prop)
qed

text \<open>\cwref{cdcl:completeness}{theorem 2.9.11 page 98}\<close>
lemma cdcl\<^sub>W_restart_strong_completeness:
  assumes
    MN: "set M \<Turnstile>sm N" and
    cons: "consistent_interp (set M)" and
    dist: "distinct M" and
    atm: "atm_of ` (set M) \<subseteq> atms_of_mm N"
  obtains S where
    "state_butlast S = (map (\<lambda>L. Decided L) M, N, {#}, None)" and
    "rtranclp cdcl\<^sub>W_restart (init_state N) S" and
    "final_cdcl\<^sub>W_restart_state S"
proof -
  obtain S where
    st: "rtranclp cdcl\<^sub>W_restart (init_state N) S" and
    S: "state_butlast S = (map (\<lambda>L. Decided L) M, N, {#}, None)"
    using cdcl\<^sub>W_restart_can_do_step[OF cons dist atm] by auto
  have "lits_of_l (map (\<lambda>L. Decided L) M) = set M"
    by (induct M, auto)
  then have "map (\<lambda>L. Decided L) M \<Turnstile>asm N" using MN true_annots_true_cls by metis
  then have "final_cdcl\<^sub>W_restart_state S"
    using S unfolding final_cdcl\<^sub>W_restart_state_def by auto
  then show ?thesis using that st S by blast
qed


subsection \<open>Higher level strategy\<close>

text \<open>The rules described previously do not necessary lead to a conclusive state. We have to add a
  strategy:
  \<^item> do propagate and conflict when possible;
  \<^item> otherwise, do another rule (except forget and restart).\<close>


subsubsection \<open>Definition\<close>

lemma tranclp_conflict:
  "tranclp conflict S S' \<Longrightarrow> conflict S S'"
  by (induct rule: tranclp.induct) (auto elim!: conflictE)

lemma no_chained_conflict:
  assumes "conflict S S'" and "conflict S' S''"
  shows False
  using assms unfolding conflict.simps
  by (metis conflicting_update_conflicting option.distinct(1) state_eq_conflicting)

lemma tranclp_conflict_iff:
  "full1 conflict S S' \<longleftrightarrow> conflict S S'"
  by (auto simp: full1_def dest: tranclp_conflict no_chained_conflict)

lemma no_conflict_after_conflict:
  "conflict S T \<Longrightarrow> \<not>conflict T U"
  by (auto elim!: conflictE simp: conflict.simps)

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

lemma cdcl\<^sub>W_stgy_induct[consumes 1, case_names conflict propagate decide skip resolve backtrack]:
  assumes
    \<open>cdcl\<^sub>W_stgy S T\<close> and
    \<open>\<And>T. conflict S T \<Longrightarrow> P T\<close> and
    \<open>\<And>T. propagate S T \<Longrightarrow> P T\<close> and
    \<open>\<And>T. no_step conflict S \<Longrightarrow> no_step propagate S \<Longrightarrow> decide S T \<Longrightarrow> P T\<close> and
    \<open>\<And>T. no_step conflict S \<Longrightarrow> no_step propagate S \<Longrightarrow> skip S T \<Longrightarrow> P T\<close> and
    \<open>\<And>T. no_step conflict S \<Longrightarrow> no_step propagate S \<Longrightarrow> resolve S T \<Longrightarrow> P T\<close> and
    \<open>\<And>T. no_step conflict S \<Longrightarrow> no_step propagate S \<Longrightarrow> backtrack S T \<Longrightarrow> P T\<close>
  shows
    \<open>P T\<close>
  using assms(1) by (induction rule: cdcl\<^sub>W_stgy.induct)
  (auto simp: assms(2-) cdcl\<^sub>W_o.simps cdcl\<^sub>W_bj.simps)

lemma cdcl\<^sub>W_stgy_cases[consumes 1, case_names conflict propagate decide skip resolve backtrack]:
  assumes
    \<open>cdcl\<^sub>W_stgy S T\<close> and
    \<open>conflict S T \<Longrightarrow> P\<close> and
    \<open>propagate S T \<Longrightarrow> P\<close> and
    \<open>no_step conflict S \<Longrightarrow> no_step propagate S \<Longrightarrow> decide S T \<Longrightarrow> P\<close> and
    \<open>no_step conflict S \<Longrightarrow> no_step propagate S \<Longrightarrow> skip S T \<Longrightarrow> P\<close> and
    \<open>no_step conflict S \<Longrightarrow> no_step propagate S \<Longrightarrow> resolve S T \<Longrightarrow> P\<close> and
    \<open>no_step conflict S \<Longrightarrow> no_step propagate S \<Longrightarrow> backtrack S T \<Longrightarrow> P\<close>
  shows
    \<open>P\<close>
  using assms(1) by (cases rule: cdcl\<^sub>W_stgy.cases)
  (auto simp: assms(2-) cdcl\<^sub>W_o.simps cdcl\<^sub>W_bj.simps)


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
  assumes "cdcl\<^sub>W_stgy S S'"
  shows "init_clss S = init_clss S'"
  using assms cdcl\<^sub>W_cdcl\<^sub>W_restart cdcl\<^sub>W_restart_init_clss cdcl\<^sub>W_stgy_cdcl\<^sub>W by blast

lemma rtranclp_cdcl\<^sub>W_stgy_no_more_init_clss:
  assumes "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S S'"
  shows "init_clss S = init_clss S'"
  using assms
  apply (induct rule: rtranclp_induct, simp)
  using cdcl\<^sub>W_stgy_no_more_init_clss by (simp add: rtranclp_cdcl\<^sub>W_stgy_consistent_inv)


subsubsection \<open>Literal of highest level in conflicting clauses\<close>

text \<open>One important property of the @{term cdcl\<^sub>W_restart} with strategy is that, whenever a conflict
  takes place, there is at least a literal of level @{term k} involved (except if we have derived
  the false clause). The reason is that we apply conflicts before a decision is taken.\<close>
definition conflict_is_false_with_level :: "'st \<Rightarrow> bool" where
"conflict_is_false_with_level S \<equiv> \<forall>D. conflicting S = Some D \<longrightarrow> D \<noteq> {#}
  \<longrightarrow> (\<exists>L \<in># D. get_level (trail S) L = backtrack_lvl S)"

declare conflict_is_false_with_level_def[simp]


subsubsection \<open>Literal of highest level in decided literals\<close>

definition mark_is_false_with_level :: "'st \<Rightarrow> bool" where
"mark_is_false_with_level S' \<equiv>
  \<forall>D M1 M2 L. M1 @ Propagated L D # M2 = trail S' \<longrightarrow> D - {#L#} \<noteq> {#}
    \<longrightarrow> (\<exists>L. L \<in># D \<and> get_level (trail S') L = count_decided M1)"

lemma backtrack\<^sub>W_rule:
  assumes
    confl: \<open>conflicting S = Some (add_mset L D)\<close> and
    decomp: \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S))\<close> and
    lev_L: \<open>get_level (trail S) L = backtrack_lvl S\<close> and
    max_lev: \<open>get_level (trail S) L = get_maximum_level (trail S) (add_mset L D)\<close> and
    max_D: \<open>get_maximum_level (trail S) D \<equiv> i\<close> and
    lev_K: \<open>get_level (trail S) K = i + 1\<close> and
    T: \<open>T \<sim> cons_trail (Propagated L (add_mset L D))
        (reduce_trail_to M1
          (add_learned_cls (add_mset L D)
            (update_conflicting None S)))\<close> and
    lev_inv: "cdcl\<^sub>W_M_level_inv S" and
    conf: \<open>cdcl\<^sub>W_conflicting S\<close> and
    learned: \<open>cdcl\<^sub>W_learned_clause S\<close>
  shows \<open>backtrack S T\<close>
  using confl decomp lev_L max_lev max_D lev_K
proof (rule backtrack_rule)
  let ?i = "get_maximum_level (trail S) D"
  let ?D = \<open>add_mset L D\<close>
  show \<open>D \<subseteq># D\<close>
    by simp
  obtain M3 where
    M3: \<open>trail S = M3 @ M2 @ Decided K # M1\<close>
    using decomp by auto
  have trail_S_D: \<open>trail S \<Turnstile>as CNot ?D\<close>
    using conf confl unfolding cdcl\<^sub>W_conflicting_def by auto
  then have atms_E_M1: \<open>atms_of D \<subseteq> atm_of ` lits_of_l M1\<close>
    using backtrack_atms_of_D_in_M1[OF _ _ decomp, of D ?i L ?D
      \<open>cons_trail (Propagated L ?D) (reduce_trail_to M1 (add_learned_cls ?D (update_conflicting None S)))\<close>
      \<open>Propagated L (add_mset L D)\<close>]
    conf lev_K decomp max_lev lev_L confl T max_D lev_inv unfolding cdcl\<^sub>W_M_level_inv_def
    by auto
  have n_d: \<open>no_dup (M3 @ M2 @ Decided K # M1)\<close>
    using lev_inv no_dup_rev[of \<open>rev M1 @ rev M2 @ rev M3\<close>, unfolded rev_append]
    by (auto simp: cdcl\<^sub>W_M_level_inv_def M3)
  then have n_d': \<open>no_dup (M3 @ M2 @ M1)\<close>
    by auto
  have atm_L_M1: \<open>atm_of L \<notin> atm_of ` lits_of_l M1\<close>
    using lev_L n_d defined_lit_no_dupD(2-3)[of M1 L M3 M2] count_decided_ge_get_level[of \<open>Decided K # M1\<close> L]
    unfolding M3
    by (auto simp: atm_of_eq_atm_of Decided_Propagated_in_iff_in_lits_of_l get_level_cons_if split: if_splits)

  have \<open>La \<noteq> L\<close>\<open>- La \<notin> lits_of_l M3\<close> \<open>- La \<notin> lits_of_l M2\<close> \<open>-La \<noteq>K\<close> if \<open>La\<in>#D\<close> for La
  proof -
    have \<open>-La \<in> lits_of_l (trail S)\<close>
      using trail_S_D that by (auto simp: true_annots_true_cls_def_iff_negation_in_model
          dest!: get_all_ann_decomposition_exists_prepend)
    moreover have \<open>defined_lit M1 La\<close>
      using atms_E_M1 that by (auto simp: Decided_Propagated_in_iff_in_lits_of_l atms_of_def
          dest!: atm_of_in_atm_of_set_in_uminus)
    moreover have n_d': \<open>no_dup (rev M1 @ rev M2 @ rev M3)\<close>
      by (rule same_mset_no_dup_iff[THEN iffD1, OF _ n_d']) auto
    moreover have \<open>no_dup (rev M3 @ rev M2 @ rev M1)\<close>
      by (rule same_mset_no_dup_iff[THEN iffD1, OF _ n_d']) auto
    ultimately show \<open>La \<noteq> L\<close>\<open>- La \<notin> lits_of_l M3\<close> \<open>- La \<notin> lits_of_l M2\<close>  \<open>-La \<noteq> K\<close>
      using defined_lit_no_dupD(2-3)[of \<open>rev M1\<close> La \<open>rev M3\<close> \<open>rev M2\<close>]
        defined_lit_no_dupD(1)[of \<open>rev M1\<close> La \<open>rev M3 @ rev M2\<close>] atm_L_M1 n_d
      by (auto simp: M3 Decided_Propagated_in_iff_in_lits_of_l atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set)
  qed

  show \<open>clauses S \<Turnstile>pm add_mset L D\<close>
    using cdcl\<^sub>W_learned_clause_def confl learned by blast

  show \<open>T \<sim> cons_trail (Propagated L (add_mset L D)) (reduce_trail_to M1 (add_learned_cls (add_mset L D) (update_conflicting None S)))\<close>
    using T by blast
qed

lemma backtrack_no_decomp:
  assumes
    S: "conflicting S = Some (add_mset L E)" and
    L: "get_level (trail S) L = backtrack_lvl S" and
    D: "get_maximum_level (trail S) E < backtrack_lvl S" and
    bt: "backtrack_lvl S = get_maximum_level (trail S) (add_mset L E)" and
    lev_inv: "cdcl\<^sub>W_M_level_inv S" and
    conf: \<open>cdcl\<^sub>W_conflicting S\<close> and
    learned: \<open>cdcl\<^sub>W_learned_clause S\<close>
  shows "\<exists>S'. cdcl\<^sub>W_o S S'" "\<exists>S'. backtrack S S'"
proof -
  have L_D: "get_level (trail S) L = get_maximum_level (trail S) (add_mset L E)"
    using L D bt by (simp add: get_maximum_level_plus)
  let ?i = "get_maximum_level (trail S) E"
  let ?D = \<open>add_mset L E\<close>
  obtain K M1 M2 where
    K: "(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S))" and
    lev_K: "get_level (trail S) K = ?i + 1"
    using backtrack_ex_decomp[of S ?i] D S lev_inv
    unfolding cdcl\<^sub>W_M_level_inv_def by auto
  show \<open>Ex (backtrack S)\<close>
    using backtrack\<^sub>W_rule[OF S K L L_D _ lev_K] lev_inv conf learned by auto
  then show \<open>Ex (cdcl\<^sub>W_o S)\<close>
    using bj by (auto simp: cdcl\<^sub>W_bj.simps)
qed

lemma no_analyse_backtrack_Ex_simple_backtrack:
  assumes
    bt: \<open>backtrack S T\<close> and
    lev_inv: "cdcl\<^sub>W_M_level_inv S" and
    conf: \<open>cdcl\<^sub>W_conflicting S\<close> and
    learned: \<open>cdcl\<^sub>W_learned_clause S\<close> and
    no_dup: \<open>distinct_cdcl\<^sub>W_state S\<close> and
    ns_s: \<open>no_step skip S\<close> and
    ns_r: \<open>no_step resolve S\<close>
  shows \<open>Ex(simple_backtrack S)\<close>
proof -
  obtain D L K i M1 M2 D' where
    confl: "conflicting S = Some (add_mset L D)" and
    decomp: "(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S))" and
    lev: "get_level (trail S) L = backtrack_lvl S" and
    max: "get_level (trail S) L = get_maximum_level (trail S) (add_mset L D')" and
    max_D: "get_maximum_level (trail S) D' \<equiv> i" and
    lev_K: "get_level (trail S) K = Suc i" and
    D'_D: \<open>D' \<subseteq># D\<close> and
    NU_DL: \<open>clauses S \<Turnstile>pm add_mset L D'\<close> and
    T: "T \<sim> cons_trail (Propagated L (add_mset L D'))
                (reduce_trail_to M1
                  (add_learned_cls (add_mset L D')
                    (update_conflicting None S)))"
    using bt by (elim backtrackE) metis
  have n_d: \<open>no_dup (trail S)\<close>
    using lev_inv unfolding cdcl\<^sub>W_M_level_inv_def by auto
  have trail_S_Nil: \<open>trail S \<noteq> []\<close>
    using decomp by auto
  then have hd_in_annot: \<open>lit_of (hd_trail S) \<in># mark_of (hd_trail S)\<close> if \<open>is_proped (hd_trail S)\<close>
    using conf that unfolding cdcl\<^sub>W_conflicting_def
    by (cases \<open>trail S\<close>; cases \<open>hd (trail S)\<close>) fastforce+
  have max_D_L_hd: \<open>get_maximum_level (trail S) D < get_level (trail S) L \<and> L = -lit_of (hd_trail S)\<close>
  proof cases
    assume is_p: \<open>is_proped (hd (trail S))\<close>
    then have \<open>-lit_of (hd (trail S)) \<in># add_mset L D\<close>
      using ns_s trail_S_Nil confl skip_rule[of S \<open>lit_of (hd (trail S))\<close> _ _ \<open>add_mset L D\<close>]
      by (cases \<open>trail S\<close>; cases \<open>hd (trail S)\<close>) auto
    then have \<open>get_maximum_level (trail S) (remove1_mset (- lit_of (hd_trail S)) (add_mset L D)) \<noteq> backtrack_lvl S\<close>
      using ns_r trail_S_Nil confl resolve_rule[of S \<open>lit_of (hd (trail S))\<close> \<open>mark_of (hd_trail S)\<close> \<open>add_mset L D\<close>] is_p
        hd_in_annot
      by (cases \<open>trail S\<close>; cases \<open>hd (trail S)\<close>) auto
    then have lev_L_D: \<open>get_maximum_level (trail S) (remove1_mset (- lit_of (hd_trail S)) (add_mset L D)) <
         backtrack_lvl S\<close>
      using count_decided_ge_get_maximum_level[of \<open>trail S\<close> \<open>remove1_mset (- lit_of (hd_trail S)) (add_mset L D)\<close>]
      by auto
    then have \<open>L = -lit_of (hd_trail S)\<close>
      using get_maximum_level_ge_get_level[of L \<open>remove1_mset (- lit_of (hd_trail S)) (add_mset L D)\<close>
          \<open>trail S\<close>] lev apply -
      by (rule ccontr) auto
    then show ?thesis
      using lev_L_D lev by auto
  next
    assume is_p: \<open>\<not> is_proped (hd (trail S))\<close>
    obtain L' where
      L': \<open>L' \<in># add_mset L D\<close> and
      lev_L': \<open>get_level (trail S) L' = backtrack_lvl S\<close>
      using lev by auto
    moreover have uL'_trail: \<open>-L' \<in> lits_of_l (trail S)\<close>
      using conf confl L' unfolding cdcl\<^sub>W_conflicting_def true_annots_true_cls_def_iff_negation_in_model
      by auto
    moreover have \<open>L' \<notin> lits_of_l (trail S)\<close>
      using n_d uL'_trail by (blast dest: no_dup_consistentD)
    ultimately have L'_hd: \<open>L' = -lit_of (hd_trail S)\<close>
      using is_p trail_S_Nil by (cases \<open>trail S\<close>; cases \<open>hd (trail S)\<close>)
        (auto simp: get_level_cons_if atm_of_eq_atm_of
          split: if_splits)
    have \<open>distinct_mset (add_mset L D)\<close>
      using no_dup confl unfolding distinct_cdcl\<^sub>W_state_def by auto
    then have \<open>L' \<notin># remove1_mset L' (add_mset L D)\<close>
      using L' by (meson distinct_mem_diff_mset multi_member_last)
    moreover have \<open>-L' \<notin># add_mset L D\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then have \<open>L' \<in> lits_of_l (trail S)\<close>
        using conf confl trail_S_Nil unfolding cdcl\<^sub>W_conflicting_def true_annots_true_cls_def_iff_negation_in_model
        by auto
      then show False
        using n_d L'_hd by (cases \<open>trail S\<close>; cases \<open>hd (trail S)\<close>)
          (auto simp: Decided_Propagated_in_iff_in_lits_of_l)
    qed
    ultimately have \<open>atm_of (lit_of (Decided (- L'))) \<notin> atms_of (remove1_mset L' (add_mset L D))\<close>
      using \<open>- L' \<notin># add_mset L D\<close> by (auto simp: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
          atms_of_def dest: in_diffD)
    then have \<open>get_maximum_level (Decided (-L') # tl (trail S)) (remove1_mset L' (add_mset L D)) =
           get_maximum_level (tl (trail S)) (remove1_mset L' (add_mset L D))\<close>
      by (rule get_maximum_level_skip_first)
    also have \<open>get_maximum_level (tl (trail S)) (remove1_mset L' (add_mset L D)) < backtrack_lvl S\<close>
      using count_decided_ge_get_maximum_level[of \<open>tl (trail S)\<close> \<open>remove1_mset L' (add_mset L D)\<close>]
        trail_S_Nil is_p by (cases \<open>trail S\<close>; cases \<open>hd (trail S)\<close>) auto
    finally have lev_L'_L: \<open>get_maximum_level (trail S) (remove1_mset L' (add_mset L D)) < backtrack_lvl S\<close>
      using trail_S_Nil is_p L'_hd by (cases \<open>trail S\<close>; cases \<open>hd (trail S)\<close>) auto
    then have \<open>L = L'\<close>
      using get_maximum_level_ge_get_level[of L \<open>remove1_mset L' (add_mset L D)\<close>
          \<open>trail S\<close>] L' lev_L' lev by auto
    then show ?thesis
      using lev_L'_L lev L'_hd by auto
  qed
  let ?i = \<open>get_maximum_level (trail S) D\<close>
  obtain K' M1' M2' where
    decomp': \<open>(Decided K' # M1', M2') \<in> set (get_all_ann_decomposition (trail S))\<close> and
    lev_K': \<open>get_level (trail S) K' = Suc ?i\<close>
    using backtrack_ex_decomp[of S ?i] lev_inv max_D_L_hd
    unfolding lev cdcl\<^sub>W_M_level_inv_def by blast

  show ?thesis
    apply standard
    apply (rule simple_backtrack_rule[of S L D K' M1' M2' \<open>get_maximum_level (trail S) D\<close>
          \<open>cons_trail (Propagated L (add_mset L D)) (reduce_trail_to M1' (add_learned_cls (add_mset L D) (update_conflicting None S)))\<close>])
    subgoal using confl by auto
    subgoal using decomp' by auto
    subgoal using lev .
    subgoal using count_decided_ge_get_maximum_level[of \<open>trail S\<close> D] lev
        by (auto simp: get_maximum_level_add_mset)
    subgoal .
    subgoal using lev_K' by simp
    subgoal by simp
    done
qed

lemma trail_begins_with_decided_conflicting_exists_backtrack:
  assumes
    confl_k: \<open>conflict_is_false_with_level S\<close> and
    conf: \<open>cdcl\<^sub>W_conflicting S\<close> and
    level_inv: \<open>cdcl\<^sub>W_M_level_inv S\<close> and
    no_dup: \<open>distinct_cdcl\<^sub>W_state S\<close> and
    learned: \<open>cdcl\<^sub>W_learned_clause S\<close> and
    alien: \<open>no_strange_atm S\<close> and
    tr_ne: \<open>trail S \<noteq> []\<close> and
    L': \<open>hd_trail S = Decided L'\<close> and
    nempty: \<open>C \<noteq> {#}\<close> and
    confl: \<open>conflicting S = Some C\<close>
  shows \<open>Ex (backtrack S)\<close> and \<open>no_step skip S\<close> and \<open>no_step resolve S\<close>
proof -
  let ?M = "trail S"
  let ?N = "init_clss S"
  let ?k = "backtrack_lvl S"
  let ?U = "learned_clss S"
  obtain L D where
    E'[simp]: "C = D + {#L#}" and
    lev_L: "get_level ?M L = ?k"
    using nempty confl by (metis (mono_tags) confl_k insert_DiffM2 conflict_is_false_with_level_def)

  let ?D = "D + {#L#}"
  have "?D \<noteq> {#}" by auto
  have "?M \<Turnstile>as CNot ?D" using confl conf unfolding cdcl\<^sub>W_conflicting_def by auto
  then have "?M \<noteq> []" unfolding true_annots_def Ball_def true_annot_def true_cls_def by force
  define M' where M': \<open>M' = tl ?M\<close>
  have M: "?M = hd ?M # M'" using \<open>?M \<noteq> []\<close> list.collapse M' by fastforce

  obtain k' where k': "k' + 1 = ?k"
    using level_inv tr_ne L' unfolding cdcl\<^sub>W_M_level_inv_def by (cases "trail S") auto

  have n_s: "no_step conflict S" "no_step propagate S"
    using confl by (auto elim!: conflictE propagateE)

  have g_k: "get_maximum_level (trail S) D \<le> ?k"
    using count_decided_ge_get_maximum_level[of ?M] level_inv unfolding cdcl\<^sub>W_M_level_inv_def
    by auto
  have L'_L: "L' = -L"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    moreover {
      have "-L \<in> lits_of_l ?M"
        using confl conf unfolding cdcl\<^sub>W_conflicting_def by auto
      then have \<open>atm_of L \<noteq> atm_of L'\<close>
        using cdcl\<^sub>W_M_level_inv_decomp(2)[OF level_inv] M calculation L'
        by (auto simp: atm_of_eq_atm_of all_conj_distrib uminus_lit_swap lits_of_def no_dup_def) }
    ultimately have "get_level (hd (trail S) # M') L = get_level (tl ?M) L"
      using cdcl\<^sub>W_M_level_inv_decomp(1)[OF level_inv] M unfolding consistent_interp_def
      by (simp add: atm_of_eq_atm_of L' M'[symmetric])
    moreover {
      have "count_decided (trail S) = ?k"
        using level_inv unfolding cdcl\<^sub>W_M_level_inv_def by auto
      then have count: "count_decided M' = ?k - 1"
        using level_inv M by (auto simp add: L' M'[symmetric])
      then have "get_level (tl ?M) L < ?k"
        using count_decided_ge_get_level[of M' L] unfolding k'[symmetric] M' by auto }
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
      unfolding distinct_cdcl\<^sub>W_state_def confl
      by (metis E' add_diff_cancel_right' distinct_mem_diff_mset union_commute union_single_eq_member)
    have "L'' = -L"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have "get_level ?M L'' = get_level (tl ?M) L''"
        using M \<open>L \<noteq> L''\<close> get_level_skip_beginning[of L'' "hd ?M" "tl ?M"] unfolding L
        by (auto simp: atm_of_eq_atm_of)
      moreover have "get_level (tl (trail S)) L = 0"
          using level_inv L' M unfolding cdcl\<^sub>W_M_level_inv_def
          by (auto simp: image_iff L' L'_L)
      moreover {
        have \<open>backtrack_lvl S = count_decided (hd ?M # tl ?M)\<close>
          unfolding M[symmetric] M'[symmetric] ..
        then have "get_level (tl (trail S)) L'' < backtrack_lvl S"
          using count_decided_ge_get_level[of \<open>tl (trail S)\<close> L'']
          by (auto simp: image_iff L' L'_L) }
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
      using confl no_dup conf unfolding cdcl\<^sub>W_conflicting_def by auto
    ultimately show False by blast
  qed
  have confl_D: \<open>conflicting S = Some (add_mset L D)\<close>
    using confl[unfolded E'] by simp
  have "get_maximum_level (trail S) D < get_maximum_level (trail S) (add_mset L D)"
    using H by (auto simp: get_maximum_level_plus lev_L max_def get_maximum_level_add_mset)
  moreover have "backtrack_lvl S = get_maximum_level (trail S) (add_mset L D)"
    using H by (auto simp: get_maximum_level_plus lev_L max_def get_maximum_level_add_mset)
  ultimately show \<open>Ex (backtrack S)\<close>
    using backtrack_no_decomp[OF confl_D _ ] level_inv alien conf learned
    by (auto simp add: lev_L max_def n_s)

  show \<open>no_step resolve S\<close>
    using L by (auto elim!: resolveE)
  show \<open>no_step skip S\<close>
    using L by (auto elim!: skipE)
qed

lemma conflicting_no_false_can_do_step:
  assumes
    confl: \<open>conflicting S = Some C\<close> and
    nempty: \<open>C \<noteq> {#}\<close> and
    confl_k: \<open>conflict_is_false_with_level S\<close> and
    conf: \<open>cdcl\<^sub>W_conflicting S\<close> and
    level_inv: \<open>cdcl\<^sub>W_M_level_inv S\<close> and
    no_dup: \<open>distinct_cdcl\<^sub>W_state S\<close> and
    learned: \<open>cdcl\<^sub>W_learned_clause S\<close> and
    alien: \<open>no_strange_atm S\<close> and
    termi: \<open>no_step cdcl\<^sub>W_stgy S\<close>
  shows False
proof -
  let ?M = "trail S"
  let ?N = "init_clss S"
  let ?k = "backtrack_lvl S"
  let ?U = "learned_clss S"
  define M' where \<open>M' = tl ?M\<close>
  obtain L D where
    E'[simp]: "C = D + {#L#}" and
    lev_L: "get_level ?M L = ?k"
    using nempty confl by (metis (mono_tags) confl_k insert_DiffM2 conflict_is_false_with_level_def)
  let ?D = "D + {#L#}"
  have "?D \<noteq> {#}" by auto
  have "?M \<Turnstile>as CNot ?D" using confl conf unfolding cdcl\<^sub>W_conflicting_def by auto
  then have "?M \<noteq> []" unfolding true_annots_def Ball_def true_annot_def true_cls_def by force
  have M': "?M = hd ?M # tl ?M" using \<open>?M \<noteq> []\<close> by fastforce
  then have M: "?M = hd ?M # M'" unfolding M'_def .

  have n_s: "no_step conflict S" "no_step propagate S"
    using termi by (blast intro: cdcl\<^sub>W_stgy.intros)+
  have \<open>no_step backtrack S\<close>
    using termi by (blast intro: cdcl\<^sub>W_stgy.intros cdcl\<^sub>W_o.intros cdcl\<^sub>W_bj.intros)
  then have not_is_decided: "\<not> is_decided (hd ?M)"
    using trail_begins_with_decided_conflicting_exists_backtrack(1)[OF confl_k conf level_inv no_dup
   learned alien \<open>?M \<noteq> []\<close> _ nempty confl] by (cases \<open>hd_trail S\<close>) (auto)
  have g_k: "get_maximum_level (trail S) D \<le> ?k"
    using count_decided_ge_get_maximum_level[of ?M] level_inv unfolding cdcl\<^sub>W_M_level_inv_def
    by auto

  let ?D = "add_mset L D"
  have "?D \<noteq> {#}" by auto
  have "?M \<Turnstile>as CNot ?D" using confl conf unfolding cdcl\<^sub>W_conflicting_def by auto
  then have "?M \<noteq> []" unfolding true_annots_def Ball_def true_annot_def true_cls_def by force
  then obtain L' C where L'C: "hd_trail S = Propagated L' C"
    using not_is_decided by (cases "hd_trail S") auto
  then have "hd ?M = Propagated L' C"
    using \<open>?M \<noteq> []\<close> by fastforce
  then have M: "?M = Propagated L' C # M'" using M by simp
  then have M': "?M = Propagated L' C # tl ?M" using M by simp
  then obtain C' where C': "C = add_mset L' C'"
    using conf M unfolding cdcl\<^sub>W_conflicting_def by (metis append_Nil diff_single_eq_union)
  have L'D: "-L' \<in># ?D"
    using n_s alien level_inv termi skip_rule[OF M' confl]
    by (auto dest: other' cdcl\<^sub>W_o.intros cdcl\<^sub>W_bj.intros)

  obtain D' where D': "?D = add_mset (-L') D'" using L'D by (metis insert_DiffM)
  then have "get_maximum_level (trail S) D' \<le> ?k"
    using count_decided_ge_get_maximum_level[of "Propagated L' C # tl ?M"] M
    level_inv unfolding cdcl\<^sub>W_M_level_inv_def by auto
  then consider
    (D'_max_lvl) "get_maximum_level (trail S) D' = ?k" |
    (D'_le_max_lvl) "get_maximum_level (trail S) D' < ?k"
    using le_neq_implies_less by blast
  then show False
  proof cases
    case g_D'_k: D'_max_lvl
    then have f1: "get_maximum_level (trail S) D' = backtrack_lvl S"
      using M by auto
    then have "Ex (cdcl\<^sub>W_o S)"
      using resolve_rule[of S L' C , OF \<open>trail S \<noteq> []\<close> _ _ confl] conf
        L'C L'D D' C' by (auto dest: cdcl\<^sub>W_o.intros cdcl\<^sub>W_bj.intros)
    then show False
      using n_s termi by (auto dest: other' cdcl\<^sub>W_o.intros cdcl\<^sub>W_bj.intros)
  next
    case a1: D'_le_max_lvl
    then have f3: "get_maximum_level (trail S) D' < get_level (trail S) (-L')"
      using a1 lev_L D' by (metis D' get_maximum_level_ge_get_level insert_noteq_member
          not_less)
    moreover have "get_level (trail S) L' = get_maximum_level (trail S) (D' + {#- L'#})"
      using a1 by (auto simp add: get_maximum_level_add_mset max_def M)
    ultimately show False
      using M backtrack_no_decomp[of S "-L'" D'] confl level_inv n_s termi E' learned conf
      by (auto simp: D' dest: other' cdcl\<^sub>W_o.intros cdcl\<^sub>W_bj.intros)
  qed
qed

lemma cdcl\<^sub>W_stgy_final_state_conclusive2:
  assumes
    termi: "no_step cdcl\<^sub>W_stgy S" and
    decomp: "all_decomposition_implies_m (clauses S) (get_all_ann_decomposition (trail S))" and
    learned: "cdcl\<^sub>W_learned_clause S" and
    level_inv: "cdcl\<^sub>W_M_level_inv S" and
    alien: "no_strange_atm S" and
    no_dup: "distinct_cdcl\<^sub>W_state S" and
    confl: "cdcl\<^sub>W_conflicting S" and
    confl_k: "conflict_is_false_with_level S"
  shows "(conflicting S = Some {#} \<and> unsatisfiable (set_mset (clauses S)))
         \<or> (conflicting S = None \<and> trail S \<Turnstile>as set_mset (clauses S))"
proof -
  let ?M = "trail S"
  let ?N = "clauses S"
  let ?k = "backtrack_lvl S"
  let ?U = "learned_clss S"
  consider
      (None) "conflicting S = None"
    | (Some_Empty) E where "conflicting S = Some E" and "E = {#}"
    using conflicting_no_false_can_do_step[of S, OF _ _ confl_k confl level_inv no_dup learned alien] termi
    by (cases "conflicting S", simp) auto
  then show ?thesis
  proof cases
    case (Some_Empty E)
    then have "conflicting S = Some {#}" by auto
    then have unsat_clss_S: "unsatisfiable (set_mset (clauses S))"
      using learned unfolding cdcl\<^sub>W_learned_clause_def true_clss_cls_def
        conflict_is_false_with_level_def
      by (metis (no_types, lifting) Un_insert_right atms_of_empty satisfiable_def
          sup_bot.right_neutral total_over_m_insert total_over_set_empty true_cls_empty)
    then show ?thesis using Some_Empty by (auto simp: clauses_def)
  next
    case None
    have "?M \<Turnstile>asm ?N"
    proof (rule ccontr)
      assume MN: "\<not> ?thesis"
      have all_defined: "atm_of ` (lits_of_l ?M) = atms_of_mm ?N" (is "?A = ?B")
      proof
        show "?A \<subseteq> ?B" using alien unfolding no_strange_atm_def clauses_def by auto
        show "?B \<subseteq> ?A"
        proof (rule ccontr)
          assume "\<not>?B \<subseteq> ?A"
          then obtain l where "l \<in> ?B" and "l \<notin> ?A" by auto
          then have "undefined_lit ?M (Pos l)"
            using \<open>l \<notin> ?A\<close> unfolding lits_of_def by (auto simp add: defined_lit_map)
          then have "\<exists>S'. cdcl\<^sub>W_o S S'"
            using cdcl\<^sub>W_o.decide[of S] decide_rule[of S \<open>Pos l\<close> \<open>cons_trail (Decided (Pos l)) S\<close>]
              \<open>l \<in> ?B\<close> None alien unfolding clauses_def no_strange_atm_def by fastforce
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
        using \<open>\<not> trail S \<Turnstile>a D\<close> unfolding true_annot_def true_annots_true_cls
        by (fastforce simp: total_not_true_cls_true_clss_CNot)
      then have "\<exists>S'. conflict S S'"
        using \<open>trail S \<Turnstile>as CNot D\<close> \<open>D \<in># clauses S\<close>
          None unfolding clauses_def by (auto simp: conflict.simps clauses_def)
      then show False
        using termi by (blast intro: cdcl\<^sub>W_stgy.intros)
    qed
    then show ?thesis
      using None by auto
  qed
qed

lemma cdcl\<^sub>W_stgy_final_state_conclusive:
  assumes
    termi: "no_step cdcl\<^sub>W_stgy S" and
    decomp: "all_decomposition_implies_m (clauses S) (get_all_ann_decomposition (trail S))" and
    learned: "cdcl\<^sub>W_learned_clause S" and
    level_inv: "cdcl\<^sub>W_M_level_inv S" and
    alien: "no_strange_atm S" and
    no_dup: "distinct_cdcl\<^sub>W_state S" and
    confl: "cdcl\<^sub>W_conflicting S" and
    confl_k: "conflict_is_false_with_level S" and
    learned_entailed: \<open>cdcl\<^sub>W_learned_clauses_entailed_by_init S\<close>
  shows "(conflicting S = Some {#} \<and> unsatisfiable (set_mset (init_clss S)))
         \<or> (conflicting S = None \<and> trail S \<Turnstile>as set_mset (init_clss S))"
proof -
  let ?M = "trail S"
  let ?N = "init_clss S"
  let ?k = "backtrack_lvl S"
  let ?U = "learned_clss S"
  consider
    (None) "conflicting S = None" |
    (Some_Empty) E where "conflicting S = Some E" and "E = {#}"
    using conflicting_no_false_can_do_step[of S, OF _ _ confl_k confl level_inv no_dup learned alien] termi
    by (cases "conflicting S", simp) auto
  then show ?thesis
  proof cases
    case (Some_Empty E)
    then have "conflicting S = Some {#}" by auto
    then have unsat_clss_S: "unsatisfiable (set_mset (clauses S))"
      using learned learned_entailed unfolding cdcl\<^sub>W_learned_clause_def true_clss_cls_def
        conflict_is_false_with_level_def
      by (metis (no_types, lifting) Un_insert_right atms_of_empty satisfiable_def
          sup_bot.right_neutral total_over_m_insert total_over_set_empty true_cls_empty)
    then have "unsatisfiable (set_mset (init_clss S))"
    proof -
      have "atms_of_mm (learned_clss S) \<subseteq> atms_of_mm (init_clss S)"
        using alien no_strange_atm_decomp(3) by blast
      then have f3: "atms_of_ms (set_mset (init_clss S) \<union> set_mset (learned_clss S)) =
          atms_of_mm (init_clss S)"
        by auto
      have "init_clss S \<Turnstile>psm learned_clss S"
        using learned_entailed
        unfolding cdcl\<^sub>W_learned_clause_def cdcl\<^sub>W_learned_clauses_entailed_by_init_def by blast
      then show ?thesis
        using f3 unsat_clss_S
        unfolding true_clss_clss_def total_over_m_def clauses_def satisfiable_def
        by (metis (no_types) set_mset_union true_clss_union)
    qed
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
            by (metis literal.sel(1) state_eq_ref)
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
      then have M_CNot_D: "?M \<Turnstile>as CNot D"
        using \<open>\<not> trail S \<Turnstile>a D\<close> unfolding true_annot_def true_annots_true_cls
        by (fastforce simp: total_not_true_cls_true_clss_CNot)
      then have "\<exists>S'. conflict S S'"
        using M_CNot_D \<open>D \<in># init_clss S\<close>
          None unfolding clauses_def by (auto simp: conflict.simps clauses_def)
      then show False
        using termi by (blast intro: cdcl\<^sub>W_stgy.intros)
    qed
    then show ?thesis
      using None by auto
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
  moreover {
    have L_not_D: "L \<notin># remove1_mset (-L) D"
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
      ultimately show False unfolding lits_of_def
        by (metis imageI insertCI list.simps(15) lit_of.simps(2) lits_of_def no_dup_consistentD)
    qed
  }
  ultimately have g_D: "get_maximum_level (Propagated L C # M) (remove1_mset (-L) D)
      = get_maximum_level M (remove1_mset (-L) D)"
    by (simp add: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set atms_of_def)
  have lev_L[simp]: "get_level M L = 0"
    using lev unfolding cdcl\<^sub>W_M_level_inv_def tr_S by (auto simp: lits_of_def)

  have D: "get_maximum_level M (remove1_mset (-L) D) = backtrack_lvl S"
    using resolve.hyps(6) LD unfolding tr_S by (auto simp: get_maximum_level_plus max_def g_D)
  have "get_maximum_level M (remove1_mset L C) \<le> backtrack_lvl S"
    using count_decided_ge_get_maximum_level[of M] lev unfolding tr_S cdcl\<^sub>W_M_level_inv_def by auto
  then have
    "get_maximum_level M (remove1_mset (- L) D \<union># remove1_mset L C) = backtrack_lvl S"
    by (auto simp: get_maximum_level_union_mset get_maximum_level_plus max_def D)
  then show ?case
    using tr_S get_maximum_level_exists_lit_of_max_level[of
      "remove1_mset (- L) D \<union># remove1_mset L C" M] T
    by auto
next
  case (skip L C' M D T) note tr_S = this(1) and D = this(2) and T = this(5)
  then obtain La where
    "La \<in># D" and
    "get_level (Propagated L C' # M) La = backtrack_lvl S"
    using skip confl_inv by auto
  moreover {
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
  }
  ultimately show ?case using D tr_S T by auto
next
  case backtrack
  then show ?case
    by (auto split: if_split_asm simp: cdcl\<^sub>W_M_level_inv_decomp lev)
qed auto


subsubsection \<open>Strong completeness\<close>

lemma propagate_high_levelE:
  assumes "propagate S T"
  obtains M' N' U L C where
    "state_butlast S = (M', N', U, None)" and
    "state_butlast T = (Propagated L (C + {#L#}) # M', N', U, None)" and
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
  obtain M N U where
    S: "state_butlast S = (M, N, U, None)"
    using conf by auto
  show thesis
    using that[of M N U L "remove1_mset L E"] S T LE E tr undef
    by auto
qed

lemma cdcl\<^sub>W_propagate_conflict_completeness:
  assumes
    MN: "set M \<Turnstile>s set_mset N" and
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

  obtain M' N' U C L where
    Y: "state_butlast Y = (M', N', U, None)" and
    Z: "state_butlast Z = (Propagated L (C + {#L#}) # M', N', U, None)" and
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
    "\<exists>M' S. length M' \<ge> n \<and>
      lits_of_l M' \<subseteq> set M \<and>
      no_dup M' \<and>
      state_butlast S = (M', N, {#}, None) \<and>
      cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) S"
  using length
proof (induction n)
  case 0
  have "state_butlast (init_state N) = ([], N, {#}, None)"
    by auto
  moreover have
    "0 \<le> length []" and
    "lits_of_l [] \<subseteq> set M" and
    "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) (init_state N)"
    and "no_dup []"
    by auto
  ultimately show ?case by blast
next
  case (Suc n) note IH = this(1) and n = this(2)
  then obtain M' S where
    l_M': "length M' \<ge> n" and
    M': "lits_of_l M' \<subseteq> set M" and
    n_d[simp]: "no_dup M'" and
    S: "state_butlast S = (M', N, {#}, None)" and
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
      using S' cdcl\<^sub>W_propagate_conflict_completeness[OF assms(1-3), of S] M' S
      by (auto simp: comp_def)
    moreover have "cdcl\<^sub>W_stgy S S'" using S' by (simp add: cdcl\<^sub>W_stgy.propagate')
    moreover {
      have "trail S = M'"
        using S by (auto simp: comp_def rev_map)
      then have "length (trail S') > n"
        using S' l_M' by (auto elim: propagateE) }
    moreover {
      have stS': "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) S'"
        using st cdcl\<^sub>W_stgy.propagate'[OF S'] by (auto simp: r_into_rtranclp)
      then have "init_clss S' = N"
        using rtranclp_cdcl\<^sub>W_stgy_no_more_init_clss by fastforce}
    moreover {
      have
        [simp]:"learned_clss S' = {#}" and
        [simp]: "init_clss S' = init_clss S" and
        [simp]: "conflicting S' = None"
        using S S' by (auto elim: propagateE)
      have "state_butlast S' = (trail S', N, {#}, None)"
        using S by auto }
    moreover
    have "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) S'"
      apply (rule rtranclp.rtrancl_into_rtrancl)
      using st apply simp
      using \<open>cdcl\<^sub>W_stgy S S'\<close> by simp
    ultimately have ?case
      apply -
      apply (rule exI[of _ "trail S'"], rule exI[of _ S'])
      by auto
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
          by (induction M') (auto simp add: lits_of_def card_insert_if defined_lit_map)
        then have "lits_of_l M' \<subset> set M"
          using n M' n' lenM by auto
        then obtain L where L: "L \<in> set M" and undef_m: "L \<notin> lits_of_l M'" by auto
        moreover have undef: "undefined_lit M' L"
          using M' Decided_Propagated_in_iff_in_lits_of_l calculation(1,2) cons
          consistent_interp_def by (metis (no_types, lifting) subset_eq)
        moreover have "atm_of L \<in> atms_of_mm (init_clss S)"
          using atm_incl calculation S by auto
        ultimately have dec: "decide S (cons_trail (Decided L) S)"
          using decide_rule[of S _ "cons_trail (Decided L) S"] S by auto
        let ?S' = "cons_trail (Decided L) S"
        have "lits_of_l (trail ?S') \<subseteq> set M" using L M' S undef by auto
        moreover have "no_strange_atm ?S'"
          using alien dec M by (meson cdcl\<^sub>W_restart_no_strange_atm_inv decide other)
        have "cdcl\<^sub>W_M_level_inv ?S'"
          using M dec rtranclp_mono[of decide cdcl\<^sub>W_restart] by (meson cdcl\<^sub>W_restart_consistent_inv
              decide other)
        then have lev'': "cdcl\<^sub>W_M_level_inv ?S'"
          using S rtranclp_cdcl\<^sub>W_restart_consistent_inv rtranclp_propagate_is_rtranclp_cdcl\<^sub>W_restart
          by blast
        then have n_d'': "no_dup (trail ?S')"
          unfolding cdcl\<^sub>W_M_level_inv_def by auto
        have "length (trail S) \<le> length (trail ?S') \<and> lits_of_l (trail ?S') \<subseteq> set M"
          using S L M' S undef by simp
        then have "Suc n \<le> length (trail ?S') \<and> lits_of_l (trail ?S') \<subseteq> set M"
          using l_M' S undef by auto
        moreover have S'': "state_butlast ?S' = (trail ?S', N, {#}, None)"
          using S undef n_d'' lev'' by auto
        moreover have "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) ?S'"
            using S'' no_step no_confl st dec by (auto dest: decide cdcl\<^sub>W_stgy.intros)
        ultimately show ?thesis using n_d'' by blast
      qed
  }
  ultimately show ?case by blast
qed

lemma cdcl\<^sub>W_stgy_strong_completeness':
  assumes
    MN: "set M \<Turnstile>s set_mset N" and
    cons: "consistent_interp (set M)" and
    tot: "total_over_m (set M) (set_mset N)" and
    atm_incl: "atm_of ` (set M) \<subseteq> atms_of_mm N" and
    distM: "distinct M"
  shows
    "\<exists>M' S. lits_of_l M' = set M \<and>
      state_butlast S = (M', N, {#}, None) \<and>
      cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) S"
proof -
  have \<open>\<exists>M' S. lits_of_l M' \<subseteq> set M \<and>
      no_dup M' \<and> length M' = n \<and>
      state_butlast S = (M', N, {#}, None) \<and>
      cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) S\<close>
    if \<open>n \<le> length M\<close> for n :: nat
    using that
  proof (induction n)
    case 0
    then show ?case by (auto intro!: exI[of _ \<open>init_state N\<close>])
  next
    case (Suc n) note IH = this(1) and n_le_M = this(2)
    then obtain M' S where
      M': "lits_of_l M' \<subseteq> set M" and
      n_d[simp]: "no_dup M'" and
      S: "state_butlast S = (M', N, {#}, None)" and
      st: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) S" and
      l_M': \<open>length M' = n\<close>
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
        using S' cdcl\<^sub>W_propagate_conflict_completeness[OF assms(1-3), of S] M' S
        by (auto simp: comp_def)
      moreover have "cdcl\<^sub>W_stgy S S'" using S' by (simp add: cdcl\<^sub>W_stgy.propagate')
      moreover {
        have "trail S = M'"
          using S by (auto simp: comp_def rev_map)
        then have "length (trail S') = Suc n"
          using S' l_M' by (auto elim: propagateE) }
      moreover {
        have stS': "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) S'"
          using st cdcl\<^sub>W_stgy.propagate'[OF S'] by (auto simp: r_into_rtranclp)
        then have "init_clss S' = N"
          using rtranclp_cdcl\<^sub>W_stgy_no_more_init_clss by fastforce}
      moreover {
        have
          [simp]:"learned_clss S' = {#}" and
          [simp]: "init_clss S' = init_clss S" and
          [simp]: "conflicting S' = None"
          using S S' by (auto elim: propagateE)
        have "state_butlast S' = (trail S', N, {#}, None)"
          using S by auto }
      moreover
      have "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) S'"
        apply (rule rtranclp.rtrancl_into_rtrancl)
        using st apply simp
        using \<open>cdcl\<^sub>W_stgy S S'\<close> by simp
      ultimately have ?case
        apply -
        apply (rule exI[of _ "trail S'"], rule exI[of _ S'])
        by auto
    }
    moreover { assume no_step: "no_step propagate S"
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
        by (induction M') (auto simp add: lits_of_def card_insert_if defined_lit_map)
      then have "lits_of_l M' \<subset> set M"
        using M' l_M' lenM n_le_M by auto
      then obtain L where L: "L \<in> set M" and undef_m: "L \<notin> lits_of_l M'" by auto
      moreover have undef: "undefined_lit M' L"
        using M' Decided_Propagated_in_iff_in_lits_of_l calculation(1,2) cons
          consistent_interp_def by (metis (no_types, lifting) subset_eq)
      moreover have "atm_of L \<in> atms_of_mm (init_clss S)"
        using atm_incl calculation S by auto
      ultimately have dec: "decide S (cons_trail (Decided L) S)"
        using decide_rule[of S _ "cons_trail (Decided L) S"] S by auto
      let ?S' = "cons_trail (Decided L) S"
      have "lits_of_l (trail ?S') \<subseteq> set M" using L M' S undef by auto
      moreover have "no_strange_atm ?S'"
        using alien dec M by (meson cdcl\<^sub>W_restart_no_strange_atm_inv decide other)
      have "cdcl\<^sub>W_M_level_inv ?S'"
        using M dec rtranclp_mono[of decide cdcl\<^sub>W_restart] by (meson cdcl\<^sub>W_restart_consistent_inv
            decide other)
      then have lev'': "cdcl\<^sub>W_M_level_inv ?S'"
        using S rtranclp_cdcl\<^sub>W_restart_consistent_inv rtranclp_propagate_is_rtranclp_cdcl\<^sub>W_restart
        by blast
      then have n_d'': "no_dup (trail ?S')"
        unfolding cdcl\<^sub>W_M_level_inv_def by auto
      have "Suc (length (trail S)) = length (trail ?S') \<and> lits_of_l (trail ?S') \<subseteq> set M"
        using S L M' S undef by simp
      then have "Suc n = length (trail ?S') \<and> lits_of_l (trail ?S') \<subseteq> set M"
        using l_M' S undef by auto
      moreover have S'': "state_butlast ?S' = (trail ?S', N, {#}, None)"
        using S undef n_d'' lev'' by auto
      moreover have "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) ?S'"
        using S'' no_step no_confl st dec by (auto dest: decide cdcl\<^sub>W_stgy.intros)
      ultimately have ?case using n_d'' L M' by (auto intro!: exI[of _ \<open>Decided L # trail S\<close>] exI[of _ \<open>?S'\<close>])
    }
    ultimately show ?case by blast
  qed
  from this[of \<open>length M\<close>] obtain M' S where
    M'_M: \<open>lits_of_l M' \<subseteq> set M\<close> and
    n_d: \<open>no_dup M'\<close> and
    \<open>length M' = length M\<close> and
    \<open>state_butlast S = (M', N, {#}, None) \<and> cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) S\<close>
    by auto
  moreover have \<open>lits_of_l M' = set M\<close>
    apply (rule card_subset_eq)
    subgoal by auto
    subgoal using M'_M .
    subgoal using M'_M n_d no_dup_length_eq_card_atm_of_lits_of_l[OF n_d] M'_M \<open>finite (set M)\<close> distinct_card[OF distM] calculation(3)
        card_image_le[of \<open> lits_of_l M'\<close> atm_of] card_seteq[OF \<open>finite (set M)\<close>, of \<open>lits_of_l M'\<close>]
      by auto
    done
  ultimately show ?thesis
    by (auto intro!: exI[of _ S])
qed

text \<open>\cwref{cdcl:completeness}{theorem 2.9.11 page 98} (with strategy)\<close>
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
      state_butlast S = (M', N, {#}, None) \<and>
      cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) S \<and>
      final_cdcl\<^sub>W_restart_state S"
proof -
  from cdcl\<^sub>W_stgy_strong_completeness_n[OF assms, of "length M"]
  obtain M' T where
    l: "length M \<le> length M'" and
    M'_M: "lits_of_l M' \<subseteq> set M" and
    no_dup: "no_dup M'" and
    T: "state_butlast T = (M', N, {#}, None)" and
    st: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) T"
    by auto
  have "card (set M) = length M" using distM by (simp add: distinct_card)
  moreover {
    have "cdcl\<^sub>W_M_level_inv T"
      using rtranclp_cdcl\<^sub>W_stgy_consistent_inv[OF st] T by auto
    then have "card (set ((map (\<lambda>l. atm_of (lit_of l)) M'))) = length M'"
      using distinct_card no_dup by (fastforce simp: lits_of_def image_image no_dup_def) }
  moreover have "card (lits_of_l M') = card (set ((map (\<lambda>l. atm_of (lit_of l)) M')))"
    using no_dup by (induction M') (auto simp add: defined_lit_map card_insert_if lits_of_def)
  ultimately have "card (set M) \<le> card (lits_of_l M')" using l unfolding lits_of_def by auto
  then have s: "set M = lits_of_l M'"
    using M'_M card_seteq by blast
  moreover {
    have "M' \<Turnstile>asm N"
      using MN s unfolding true_annots_def Ball_def true_annot_def true_clss_def by auto
    then have "final_cdcl\<^sub>W_restart_state T"
      using T no_dup unfolding final_cdcl\<^sub>W_restart_state_def by auto }
  ultimately show ?thesis using st T by blast
qed


subsubsection \<open>No conflict with only variables of level less than backtrack level\<close>

text \<open>This invariant is stronger than the previous argument in the sense that it is a property about
  all possible conflicts.\<close>
definition "no_smaller_confl (S ::'st) \<equiv>
  (\<forall>M K M' D. trail S = M' @ Decided K # M \<longrightarrow> D \<in># clauses S \<longrightarrow> \<not>M \<Turnstile>as CNot D)"

lemma no_smaller_confl_init_sate[simp]:
  "no_smaller_confl (init_state N)" unfolding no_smaller_confl_def by auto

lemma cdcl\<^sub>W_o_no_smaller_confl_inv:
  fixes S S' :: "'st"
  assumes
    "cdcl\<^sub>W_o S S'" and
    n_s: "no_step conflict S" and
    lev: "cdcl\<^sub>W_M_level_inv S" and
    max_lev: "conflict_is_false_with_level S" and
    smaller: "no_smaller_confl S"
  shows "no_smaller_confl S'"
  using assms(1,2) unfolding no_smaller_confl_def
proof (induct rule: cdcl\<^sub>W_o_induct)
  case (decide L T) note confl = this(1) and undef = this(2) and T = this(4)
  have [simp]: "clauses T = clauses S"
    using T undef by auto
  show ?case
  proof (intro allI impI)
    fix M'' K M' Da
    assume "trail T = M'' @ Decided K # M'" and D: "Da \<in># local.clauses T"
    then have "trail S = tl M'' @ Decided K # M'
        \<or> (M'' = [] \<and> Decided K # M' = Decided L # trail S)"
      using T undef by (cases M'') auto
    moreover {
      assume "trail S = tl M'' @ Decided K # M'"
      then have "\<not>M' \<Turnstile>as CNot Da"
        using D T undef confl smaller unfolding no_smaller_confl_def smaller by fastforce
    }
    moreover {
      assume "Decided K # M' = Decided L # trail S"
      then have "\<not>M' \<Turnstile>as CNot Da" using smaller D confl T n_s by (auto simp: conflict.simps)
    }
    ultimately show "\<not>M' \<Turnstile>as CNot Da" by fast
  qed
next
  case resolve
  then show ?case using smaller max_lev unfolding no_smaller_confl_def by auto
next
  case skip
  then show ?case using smaller max_lev unfolding no_smaller_confl_def by auto
next
  case (backtrack L D K i M1 M2 T D') note confl = this(1) and decomp = this(2) and
    T = this(9)
  obtain c where M: "trail S = c @ M2 @ Decided K # M1"
    using decomp by auto

  show ?case
  proof (intro allI impI)
    fix M ia K' M' Da
    assume "trail T = M' @ Decided K' # M"
    then have "M1 = tl M' @ Decided K' # M"
      using T decomp lev by (cases M') (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
    let ?D' = \<open>add_mset L D'\<close>
    let ?S' = "(cons_trail (Propagated L ?D')
                  (reduce_trail_to M1 (add_learned_cls ?D' (update_conflicting None S))))"
    assume D: "Da \<in># clauses T"
    moreover{
      assume "Da \<in># clauses S"
      then have "\<not>M \<Turnstile>as CNot Da" using \<open>M1 = tl M' @ Decided K' # M\<close> M confl smaller
        unfolding no_smaller_confl_def by auto
    }
    moreover {
      assume Da: "Da = add_mset L D'"
      have "\<not>M \<Turnstile>as CNot Da"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then have "-L \<in> lits_of_l M"
          unfolding Da by (simp add: in_CNot_implies_uminus(2))
        then have "-L \<in> lits_of_l (Propagated L D # M1)"
          using UnI2 \<open>M1 = tl M' @ Decided K' # M\<close>
          by auto
        moreover
        have "backtrack S ?S'"
          using backtrack_rule[OF backtrack.hyps(1-8) T] backtrack_state_eq_compatible[of S T S] T
          by force
        then have "cdcl\<^sub>W_M_level_inv ?S'"
          using cdcl\<^sub>W_restart_consistent_inv[OF _ lev] other[OF bj]
          by (auto intro: cdcl\<^sub>W_bj.intros)
        then have "no_dup (Propagated L D # M1)"
          using decomp lev unfolding cdcl\<^sub>W_M_level_inv_def by auto
        ultimately show False
          using Decided_Propagated_in_iff_in_lits_of_l defined_lit_map
          by (auto simp: no_dup_def)
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
  assume M': "trail S' = M'' @ Decided K # M'"
  and "D \<in># clauses S'"
  obtain M N U C L where
    S: "state_butlast S = (M, N, U, None)" and
    S': "state_butlast S' = (Propagated L (C + {#L#}) # M, N, U, None)" and
    "C + {#L#} \<in># clauses S" and
    "M \<Turnstile>as CNot C" and
    "undefined_lit M L"
    using propagate by (auto elim: propagate_high_levelE)
  have "tl M'' @ Decided K # M' = trail S" using M' S S'
    by (metis Pair_inject list.inject list.sel(3) annotated_lit.distinct(1) self_append_conv2
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
    using cdcl\<^sub>W_o_no_smaller_confl_inv[of S] by auto
qed

lemma conflict_conflict_is_false_with_level:
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
  then have bt: "backtrack_lvl T = count_decided (trail T)"
    unfolding cdcl\<^sub>W_M_level_inv_def by auto
  have n_d: "no_dup (trail T)"
    using M_lev_T unfolding cdcl\<^sub>W_M_level_inv_def by auto
  show ?thesis
  proof (rule ccontr, clarsimp)
    assume
      empty: "D \<noteq> {#}" and
      lev: "\<forall>L\<in>#D. get_level (trail T) L \<noteq> backtrack_lvl T"
    moreover {
      have "get_level (trail T) L \<le> backtrack_lvl T" if "L\<in>#D" for L
        using that count_decided_ge_get_level[of "trail T" L] M_lev_T
        unfolding cdcl\<^sub>W_M_level_inv_def by auto
      then have "get_level (trail T) L < backtrack_lvl T" if "L\<in>#D" for L
        using lev that by fastforce } note lev' = this
    ultimately have "count_decided (trail T) > 0"
      using M_lev_T unfolding cdcl\<^sub>W_M_level_inv_def by (cases D) fastforce+
    then have ex: \<open>\<exists>x\<in>set (trail T). is_decided x\<close>
      unfolding no_dup_def count_decided_def by cases auto
    have \<open>\<exists>M2 L M1. trail T = M2 @ Decided L # M1 \<and> (\<forall>m\<in>set M2. \<not> is_decided m)\<close>
      by (rule split_list_first_propE[of "trail T" is_decided, OF ex])
        (force elim!: is_decided_ex_Decided)
    then obtain M2 L M1 where
      tr_T: "trail T = M2 @ Decided L # M1" and nm: "\<forall>m \<in> set M2. \<not> is_decided m"
      by blast
    moreover {
      have "get_level (trail T) La = backtrack_lvl T" if "- La \<in> lits_of_l M2" for La
        unfolding tr_T bt
        apply (subst get_level_skip_end)
        using that apply (simp add: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
            Decided_Propagated_in_iff_in_lits_of_l; fail)
        using nm bt tr_T by (simp add: count_decided_0_iff) }
    moreover {
      have tr: "M2 @ Decided L # M1 = (M2 @ [Decided L]) @ M1"
        by auto
      have "get_level (trail T) L = backtrack_lvl T"
        using n_d nm unfolding tr_T tr bt
        by (auto simp: image_image atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
            atm_lit_of_set_lits_of_l count_decided_0_iff[symmetric]) }
    moreover have "trail S = trail T"
      using T by auto
    ultimately have "M1 \<Turnstile>as CNot D"
      using lev' not_D unfolding true_annots_true_cls_def_iff_negation_in_model
      by (force simp: count_decided_0_iff[symmetric] get_level_def)
    then show False
      using smaller T tr_T D by (auto simp: no_smaller_confl_def)
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
    using conflict_conflict_is_false_with_level assms(4) conflict'.hyps n_l by blast
  then show ?case by blast
next
  case (propagate' S')
  then show ?case by (auto elim: propagateE)
next
  case (other' S') note n_s = this(1,2) and o = this(3) and lev = this(6)
  show ?case
    using cdcl\<^sub>W_o_conflict_is_false_with_level_inv[OF o] other'.prems by blast
qed

lemma rtranclp_cdcl\<^sub>W_stgy_no_smaller_confl_inv:
  assumes
    "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S S'" and
    n_l: "no_smaller_confl S" and
    cls_false: "conflict_is_false_with_level S" and
    lev: "cdcl\<^sub>W_M_level_inv S" and
    dist: "distinct_cdcl\<^sub>W_state S" and
    conflicting: "cdcl\<^sub>W_conflicting S" and
    decomp: "all_decomposition_implies_m (clauses S) (get_all_ann_decomposition (trail S))" and
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
  moreover have "distinct_cdcl\<^sub>W_state S'"
    using rtanclp_distinct_cdcl\<^sub>W_state_inv[of S S'] lev rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart[OF st]
    dist by auto
  moreover have "cdcl\<^sub>W_conflicting S'"
    using rtranclp_cdcl\<^sub>W_restart_all_inv(6)[of S S'] st alien conflicting decomp dist learned lev
    rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart by blast
  ultimately show ?case
    using cdcl\<^sub>W_stgy_no_smaller_confl[OF cdcl] cdcl\<^sub>W_stgy_ex_lit_of_max_level[OF cdcl] cdcl
    by (auto simp del: simp add: cdcl\<^sub>W_stgy.simps elim!: propagateE)
qed


subsubsection \<open>Final States are Conclusive\<close>

text \<open>\cwref{lem:prop:cdclsoundtermStates}{theorem 2.9.9 page 97}\<close>
lemma full_cdcl\<^sub>W_stgy_final_state_conclusive:
  fixes S' :: 'st
  assumes full: "full cdcl\<^sub>W_stgy (init_state N) S'"
  and no_d: "distinct_mset_mset N"
  shows "(conflicting S' = Some {#} \<and> unsatisfiable (set_mset (init_clss S')))
    \<or> (conflicting S' = None \<and> trail S' \<Turnstile>asm init_clss S')"
proof -
  let ?S = "init_state N"
  have
    termi: "\<forall>S''. \<not>cdcl\<^sub>W_stgy S' S''" and
    step: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ?S S'" using full unfolding full_def by auto
  have
    learned: "cdcl\<^sub>W_learned_clause S'" and
    level_inv: "cdcl\<^sub>W_M_level_inv S'" and
    alien: "no_strange_atm S'" and
    no_dup: "distinct_cdcl\<^sub>W_state S'" and
    confl: "cdcl\<^sub>W_conflicting S'" and
    decomp: "all_decomposition_implies_m (clauses S') (get_all_ann_decomposition (trail S'))"
    using no_d tranclp_cdcl\<^sub>W_stgy_tranclp_cdcl\<^sub>W_restart[of ?S S'] step
    rtranclp_cdcl\<^sub>W_restart_all_inv(1-6)[of ?S S']
    unfolding rtranclp_unfold by auto
  have confl_k: "conflict_is_false_with_level S'"
    using rtranclp_cdcl\<^sub>W_stgy_no_smaller_confl_inv[OF step] no_d by auto
  have learned_entailed: \<open>cdcl\<^sub>W_learned_clauses_entailed_by_init S'\<close>
    using rtranclp_cdcl\<^sub>W_learned_clauses_entailed[of \<open>?S\<close> \<open>S'\<close>] step
    by (simp add: rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart)

  show ?thesis
    using cdcl\<^sub>W_stgy_final_state_conclusive[OF termi decomp learned level_inv alien no_dup confl
      confl_k learned_entailed] .
qed

lemma cdcl\<^sub>W_o_fst_empty_conflicting_false:
  assumes
    "cdcl\<^sub>W_o S S'" and
    "trail S = []" and
    "conflicting S \<noteq> None"
  shows False
  using assms by (induct rule: cdcl\<^sub>W_o_induct) auto

lemma cdcl\<^sub>W_stgy_fst_empty_conflicting_false:
  assumes
    "cdcl\<^sub>W_stgy S S'" and
    "trail S = []" and
    "conflicting S \<noteq> None"
  shows False
  using assms apply (induct rule: cdcl\<^sub>W_stgy.induct)
    apply (auto elim: conflictE; fail)[]
   apply (auto elim: propagateE; fail)[]
  using cdcl\<^sub>W_o_fst_empty_conflicting_false by blast

lemma cdcl\<^sub>W_o_conflicting_is_false:
  "cdcl\<^sub>W_o S S' \<Longrightarrow> conflicting S = Some {#} \<Longrightarrow> False"
  by (induction rule: cdcl\<^sub>W_o_induct) auto

lemma cdcl\<^sub>W_stgy_conflicting_is_false:
  "cdcl\<^sub>W_stgy S S' \<Longrightarrow> conflicting S = Some {#} \<Longrightarrow> False"
  apply (induction rule: cdcl\<^sub>W_stgy.induct)
    apply (auto elim: conflictE; fail)[]
   apply (auto elim: propagateE; fail)[]
  by (metis conflict_with_false_implies_terminated other)

lemma rtranclp_cdcl\<^sub>W_stgy_conflicting_is_false:
  "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S S' \<Longrightarrow> conflicting S = Some {#} \<Longrightarrow> S' = S"
  apply (induction rule: rtranclp_induct)
    apply simp
  using cdcl\<^sub>W_stgy_conflicting_is_false by blast

definition conflict_or_propagate :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
"conflict_or_propagate S T \<longleftrightarrow> conflict S T \<or> propagate S T"

declare conflict_or_propagate_def[simp]

lemma conflict_or_propagate_intros:
  "conflict S T \<Longrightarrow> conflict_or_propagate S T"
  "propagate S T \<Longrightarrow> conflict_or_propagate S T"
  by auto

text \<open>\cwref{lem:prop:cdclsoundtermStates}{theorem 2.9.9 page 97}\<close>
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
    all_decomposition_implies_m (clauses S) (get_all_ann_decomposition (trail S)) \<and>
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
  show "all_decomposition_implies_m (clauses S') (get_all_ann_decomposition (trail S'))"
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
    using nm by (metis (no_types, lifting) A drop_Cons' drop_append annotated_lit.disc(1) not_gr0
      nth_append nth_append_length nth_mem zero_less_diff)
  finally show ?thesis by fast
qed


subsection \<open>Strategy-Specific Invariant\<close>

definition cdcl\<^sub>W_stgy_invariant where
"cdcl\<^sub>W_stgy_invariant S \<longleftrightarrow>
  conflict_is_false_with_level S
  \<and> no_smaller_confl S"

lemma cdcl\<^sub>W_stgy_cdcl\<^sub>W_stgy_invariant:
  assumes
   cdcl\<^sub>W_restart: "cdcl\<^sub>W_stgy S T" and
   inv_s: "cdcl\<^sub>W_stgy_invariant S" and
   inv: "cdcl\<^sub>W_all_struct_inv S"
  shows
    "cdcl\<^sub>W_stgy_invariant T"
  unfolding cdcl\<^sub>W_stgy_invariant_def cdcl\<^sub>W_all_struct_inv_def apply (intro conjI)
    apply (rule cdcl\<^sub>W_stgy_ex_lit_of_max_level[of S])
    using assms unfolding cdcl\<^sub>W_stgy_invariant_def cdcl\<^sub>W_all_struct_inv_def apply auto[7]
  using cdcl\<^sub>W_stgy_invariant_def cdcl\<^sub>W_stgy_no_smaller_confl inv_s by blast

lemma rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_stgy_invariant:
  assumes
   cdcl\<^sub>W_restart: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S T" and
   inv_s: "cdcl\<^sub>W_stgy_invariant S" and
   inv: "cdcl\<^sub>W_all_struct_inv S"
  shows
    "cdcl\<^sub>W_stgy_invariant T"
  using assms apply induction
    apply (simp; fail)
  using cdcl\<^sub>W_stgy_cdcl\<^sub>W_stgy_invariant rtranclp_cdcl\<^sub>W_all_struct_inv_inv
  rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart by blast

lemma full_cdcl\<^sub>W_stgy_inv_normal_form:
  assumes
    full: "full cdcl\<^sub>W_stgy S T" and
    inv_s: "cdcl\<^sub>W_stgy_invariant S" and
    inv: "cdcl\<^sub>W_all_struct_inv S" and
    learned_entailed: \<open>cdcl\<^sub>W_learned_clauses_entailed_by_init S\<close>
  shows "conflicting T = Some {#} \<and> unsatisfiable (set_mset (init_clss S))
    \<or> conflicting T = None \<and> trail T \<Turnstile>asm init_clss S \<and> satisfiable (set_mset (init_clss S))"
proof -
  have "no_step cdcl\<^sub>W_stgy T" and st: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S T"
    using full unfolding full_def by blast+
  moreover have "cdcl\<^sub>W_all_struct_inv T" and inv_s: "cdcl\<^sub>W_stgy_invariant T"
    apply (metis rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart full full_def inv
      rtranclp_cdcl\<^sub>W_all_struct_inv_inv)
    by (metis full full_def inv inv_s rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_stgy_invariant)
  moreover have \<open>cdcl\<^sub>W_learned_clauses_entailed_by_init T\<close>
    using inv learned_entailed unfolding cdcl\<^sub>W_all_struct_inv_def
    using rtranclp_cdcl\<^sub>W_learned_clauses_entailed rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart[OF st]
    by blast
  ultimately have "conflicting T = Some {#} \<and> unsatisfiable (set_mset (init_clss T))
    \<or> conflicting T = None \<and> trail T \<Turnstile>asm init_clss T"
    using cdcl\<^sub>W_stgy_final_state_conclusive[of T] full
    unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_stgy_invariant_def full_def by fast
  moreover have "consistent_interp (lits_of_l (trail T))"
    using \<open>cdcl\<^sub>W_all_struct_inv T\<close> unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def
    by auto
  moreover have "init_clss S = init_clss T"
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def
    by (metis rtranclp_cdcl\<^sub>W_stgy_no_more_init_clss full full_def)
  ultimately show ?thesis
    by (metis satisfiable_carac' true_annot_def true_annots_def true_clss_def)
qed


lemma full_cdcl\<^sub>W_stgy_inv_normal_form2:
  assumes
    full: "full cdcl\<^sub>W_stgy S T" and
    inv_s: "cdcl\<^sub>W_stgy_invariant S" and
    inv: "cdcl\<^sub>W_all_struct_inv S"
  shows "conflicting T = Some {#} \<and> unsatisfiable (set_mset (clauses T))
    \<or> conflicting T = None \<and> satisfiable (set_mset (clauses T))"
proof -
  have "no_step cdcl\<^sub>W_stgy T" and st: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S T"
    using full unfolding full_def by blast+
  moreover have "cdcl\<^sub>W_all_struct_inv T" and inv_s: "cdcl\<^sub>W_stgy_invariant T"
    apply (metis rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart full full_def inv
      rtranclp_cdcl\<^sub>W_all_struct_inv_inv)
    by (metis full full_def inv inv_s rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_stgy_invariant)
  ultimately have "conflicting T = Some {#} \<and> unsatisfiable (set_mset (clauses T))
    \<or> conflicting T = None \<and> trail T \<Turnstile>asm clauses T"
    using cdcl\<^sub>W_stgy_final_state_conclusive2[of T] full
    unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_stgy_invariant_def full_def by fast
  moreover have "consistent_interp (lits_of_l (trail T))"
    using \<open>cdcl\<^sub>W_all_struct_inv T\<close> unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def
    by auto
  ultimately show ?thesis
    by (metis satisfiable_carac' true_annot_def true_annots_def true_clss_def)
qed


subsection \<open>Additional Invariant: No Smaller Propagation\<close>

definition no_smaller_propa :: \<open>'st \<Rightarrow> bool\<close> where
"no_smaller_propa (S ::'st) \<equiv>
  (\<forall>M K M' D L. trail S = M' @ Decided K # M \<longrightarrow> D + {#L#} \<in># clauses S \<longrightarrow> undefined_lit M L
    \<longrightarrow> \<not>M \<Turnstile>as CNot D)"

lemma propagated_cons_eq_append_decide_cons:
  "Propagated L E # Ms = M' @ Decided K # M \<longleftrightarrow>
    M' \<noteq> [] \<and> Ms = tl M' @ Decided K # M \<and> hd M' = Propagated L E"
  by (metis (no_types, lifting) annotated_lit.disc(1) annotated_lit.disc(2) append_is_Nil_conv hd_append
    list.exhaust_sel list.sel(1) list.sel(3) tl_append2)

lemma in_get_all_mark_of_propagated_in_trail:
 \<open>C \<in> set (get_all_mark_of_propagated M)  \<longleftrightarrow> (\<exists>L. Propagated L C \<in> set M)\<close>
  by (induction M rule: ann_lit_list_induct) auto

lemma no_smaller_propa_tl:
  assumes
    \<open>no_smaller_propa S\<close> and
    \<open>trail S \<noteq> []\<close> and
    \<open>\<not>is_decided(hd_trail S)\<close> and
    \<open>trail U = tl (trail S)\<close> and
    \<open>clauses U = clauses S\<close>
  shows
    \<open>no_smaller_propa U\<close>
  using assms by (cases \<open>trail S\<close>) (auto simp: no_smaller_propa_def)

lemmas rulesE =
  skipE resolveE backtrackE propagateE conflictE decideE restartE forgetE backtrackgE

lemma decide_no_smaller_step:
  assumes dec: \<open>decide S T\<close> and smaller_propa: \<open>no_smaller_propa S\<close> and
    n_s: \<open>no_step propagate S\<close>
  shows \<open>no_smaller_propa T\<close>
    unfolding no_smaller_propa_def
proof clarify
  fix M K M' D L
  assume
    tr: \<open>trail T = M' @ Decided K # M\<close> and
    D: \<open>D+{#L#} \<in># clauses T\<close> and
    undef: \<open>undefined_lit M L\<close> and
    M: \<open>M \<Turnstile>as CNot D\<close>
  then have "Ex (propagate S)"
    apply (cases M')
    using propagate_rule[of S "D+{#L#}" L "cons_trail (Propagated L (D + {#L#})) S"] dec
      smaller_propa
    by (auto simp: no_smaller_propa_def elim!: rulesE)
  then show False
    using n_s by blast
qed

lemma no_smaller_propa_reduce_trail_to:
   \<open>no_smaller_propa S \<Longrightarrow> no_smaller_propa (reduce_trail_to M1 S)\<close>
  unfolding no_smaller_propa_def
  by (subst (asm) append_take_drop_id[symmetric, of _ \<open>length (trail S) - length M1\<close>])
    (auto simp: trail_reduce_trail_to_drop
      simp del: append_take_drop_id)

lemma backtrackg_no_smaller_propa:
  assumes o: \<open>backtrackg S T\<close> and smaller_propa: \<open>no_smaller_propa S\<close> and
    n_d: \<open>no_dup (trail S)\<close> and
    n_s: \<open>no_step propagate S\<close> and
    tr_CNot: \<open>trail S \<Turnstile>as CNot (the (conflicting S))\<close>
  shows \<open>no_smaller_propa T\<close>
proof -
  obtain D D' :: "'v clause" and K L :: "'v literal" and
    M1 M2 :: "('v, 'v clause) ann_lit list" and i :: nat where
    confl: "conflicting S = Some (add_mset L D)" and
    decomp: "(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S))" and
    bt: "get_level (trail S) L = backtrack_lvl S" and
    lev_L: "get_level (trail S) L = get_maximum_level (trail S) (add_mset L D')" and
    i: "get_maximum_level (trail S) D' \<equiv> i" and
    lev_K: "get_level (trail S) K = i + 1" and
    D_D': \<open>D' \<subseteq># D\<close> and
    T: "T \<sim> cons_trail (Propagated L (add_mset L D'))
        (reduce_trail_to M1
          (add_learned_cls (add_mset L D')
            (update_conflicting None S)))"
    using o by (auto elim!: rulesE)
  let ?D' = \<open>add_mset L D'\<close>
  have [simp]: "trail (reduce_trail_to M1 S) = M1"
    using decomp by auto
  obtain M'' c where M'': "trail S = M'' @ tl (trail T)" and c: \<open>M'' = c @ M2 @ [Decided K]\<close>
    using decomp T by auto
  have M1: "M1 = tl (trail T)" and tr_T: "trail T = Propagated L ?D' # M1"
    using decomp T by auto

  have i_lvl: \<open>i = backtrack_lvl T\<close>
    using no_dup_append_in_atm_notin[of \<open>c @ M2\<close> \<open>Decided K # tl (trail T)\<close> K]
    n_d lev_K unfolding c M'' by (auto simp: image_Un tr_T)

  from o show ?thesis
    unfolding no_smaller_propa_def
  proof clarify
    fix M K' M' E' L'
    assume
      tr: \<open>trail T = M' @ Decided K' # M\<close> and
      E: \<open>E'+{#L'#} \<in># clauses T\<close> and
      undef: \<open>undefined_lit M L'\<close> and
      M: \<open>M \<Turnstile>as CNot E'\<close>
    have n_d_T: \<open>no_dup (trail T)\<close> and M1_D': "M1 \<Turnstile>as CNot D'"
      using backtrack_M1_CNot_D'[OF n_d i decomp _ confl _ T] lev_K bt lev_L tr_CNot
	confl D_D'
      by (auto dest: subset_mset_trans_add_mset)
    have False if D: \<open>add_mset L D' = add_mset L' E'\<close> and M_D: \<open>M \<Turnstile>as CNot E'\<close>
    proof -
      have \<open>i \<noteq> 0\<close>
        using i_lvl tr T by auto
      moreover
        have "get_maximum_level M1 D' = i"
          using T i n_d D_D' M1_D' unfolding M'' tr_T
          by (subst (asm) get_maximum_level_skip_beginning)
            (auto dest: defined_lit_no_dupD dest!: true_annots_CNot_definedD)
      ultimately obtain L_max where
        L_max_in: "L_max \<in># D'" and
        lev_L_max: "get_level M1 L_max = i"
        using i get_maximum_level_exists_lit_of_max_level[of D' M1]
        by (cases D') auto
      have count_dec_M: "count_decided M < i"
        using T i_lvl unfolding tr by auto
      have "- L_max \<notin> lits_of_l M"
      proof (rule ccontr)
        assume \<open>\<not> ?thesis\<close>
        then have \<open>undefined_lit (M' @ [Decided K']) L_max\<close>
          using n_d_T unfolding tr
          by (auto dest: in_lits_of_l_defined_litD dest: defined_lit_no_dupD simp: atm_of_eq_atm_of)
        then have "get_level (tl M' @ Decided K' # M) L_max < i"
          apply (subst get_level_skip)
           apply (cases M'; auto simp add: atm_of_eq_atm_of lits_of_def; fail)
          using count_dec_M count_decided_ge_get_level[of M L_max] by auto
        then show False
          using lev_L_max tr unfolding tr_T by (auto simp: propagated_cons_eq_append_decide_cons)
      qed
      moreover have "- L \<notin> lits_of_l M"
      proof (rule ccontr)
        define MM where \<open>MM = tl M'\<close>
        assume \<open>\<not> ?thesis\<close>
        then have \<open>- L \<notin> lits_of_l (M' @ [Decided K'])\<close>
          using n_d_T unfolding tr by (auto simp: lits_of_def no_dup_def)
        have \<open>undefined_lit (M' @ [Decided K']) L\<close>
          apply (rule no_dup_uminus_append_in_atm_notin)
          using n_d_T \<open>\<not> - L \<notin> lits_of_l M\<close> unfolding tr by auto
        moreover have "M' = Propagated L ?D' # MM"
          using tr_T MM_def by (metis hd_Cons_tl propagated_cons_eq_append_decide_cons tr)
        ultimately show False
          by simp
      qed
      moreover have "L_max \<in># D' \<or> L \<in># D'"
        using D L_max_in by (auto split: if_splits)
      ultimately show False
        using M_D D by (auto simp: true_annots_true_cls true_clss_def add_mset_eq_add_mset)
    qed
    then show False
      using M'' smaller_propa tr undef M T E
      by (cases M') (auto simp: no_smaller_propa_def trivial_add_mset_remove_iff elim!: rulesE)
  qed
qed

lemmas backtrack_no_smaller_propa = backtrackg_no_smaller_propa[OF backtrack_backtrackg]

lemma cdcl\<^sub>W_stgy_no_smaller_propa:
  assumes
    cdcl: \<open>cdcl\<^sub>W_stgy S T\<close> and
    smaller_propa: \<open>no_smaller_propa S\<close> and
    inv: \<open>cdcl\<^sub>W_all_struct_inv S\<close>
  shows \<open>no_smaller_propa T\<close>
  using cdcl
proof (cases rule: cdcl\<^sub>W_stgy_cases)
  case conflict
  then show ?thesis
    using smaller_propa by (auto simp: no_smaller_propa_def elim!: rulesE)
next
  case propagate
  then show ?thesis
    using smaller_propa by (auto simp: no_smaller_propa_def propagated_cons_eq_append_decide_cons
      elim!: rulesE)
next
  case skip
  then show ?thesis
    using smaller_propa by (auto intro: no_smaller_propa_tl elim!: rulesE)
next
  case resolve
  then show ?thesis
    using smaller_propa by (auto intro: no_smaller_propa_tl elim!: rulesE)
next
  case decide note n_s = this(1,2) and dec = this(3)
  show ?thesis
    using n_s dec decide_no_smaller_step[of S T] smaller_propa
    by auto
next
  case backtrack note n_s = this(1,2) and o = this(3)
  have inv_T: "cdcl\<^sub>W_all_struct_inv T"
    using cdcl cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv inv by blast
  have \<open>trail S \<Turnstile>as CNot (the (conflicting S))\<close> and \<open>no_dup (trail S)\<close>
    using inv o unfolding cdcl\<^sub>W_all_struct_inv_def
    by (auto simp: cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_conflicting_def
      elim: rulesE)
  then show ?thesis
    using backtrack_no_smaller_propa[of S T] n_s o smaller_propa
    by auto
qed

lemma rtranclp_cdcl\<^sub>W_stgy_no_smaller_propa:
  assumes
    cdcl: \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S T\<close> and
    smaller_propa: \<open>no_smaller_propa S\<close> and
    inv: \<open>cdcl\<^sub>W_all_struct_inv S\<close>
  shows \<open>no_smaller_propa T\<close>
  using cdcl apply (induction rule: rtranclp_induct)
  subgoal using smaller_propa by simp
  subgoal using inv by (auto intro: rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv
      cdcl\<^sub>W_stgy_no_smaller_propa)
  done

lemma hd_trail_level_ge_1_length_gt_1:
  fixes S :: 'st
  defines M[symmetric, simp]: \<open>M \<equiv> trail S\<close>
  defines L[symmetric, simp]: \<open>L \<equiv> hd M\<close>
  assumes
    smaller: \<open>no_smaller_propa S\<close> and
    struct: \<open>cdcl\<^sub>W_all_struct_inv S\<close> and
    dec: \<open>count_decided M \<ge> 1\<close> and
    proped: \<open>is_proped L\<close>
  shows \<open>size (mark_of L) > 1\<close>
proof (rule ccontr)
  assume size_C: \<open>\<not> ?thesis\<close>
  have nd: \<open>no_dup M\<close>
    using struct unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def M[symmetric]
    by blast

  obtain M' where M': \<open>M = L # M'\<close>
    using dec L by (cases M) (auto simp del: L)
  obtain K C where K: \<open>L = Propagated K C\<close>
    using proped by (cases L) auto

  obtain K' M1 M2 where decomp: \<open>M = M2 @ Decided K' # M1\<close>
    using dec le_count_decided_decomp[of M 0] nd by auto
  then have decomp': \<open>M' = tl M2 @ Decided K' # M1\<close>
    unfolding M' K by (cases M2) auto

  have \<open>K \<in># C\<close>
    using struct unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_conflicting_def
    M M' K by blast
  then have C: \<open>C = {#} + {#K#}\<close>
    using size_C K by (cases C) auto
  have \<open>undefined_lit M1 K\<close>
    using nd unfolding M' K decomp' by simp
  moreover have \<open>{#} + {#K#} \<in># clauses S\<close>
    using struct unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_learned_clause_def M M' K C
    by auto
  moreover have \<open>M1 \<Turnstile>as CNot {#}\<close>
    by auto
  ultimately show False
    using smaller unfolding no_smaller_propa_def M decomp
    by blast
qed


subsection \<open>More Invariants: Conflict is False if no decision\<close>

text \<open>If the level is higher than 0, then the conflict is not empty.\<close>
definition conflict_non_zero_unless_level_0 :: \<open>'st \<Rightarrow> bool\<close> where
  \<open>conflict_non_zero_unless_level_0 S \<longleftrightarrow>
    (conflicting S = Some {#} \<longrightarrow> count_decided (trail S) = 0)\<close>

definition no_false_clause:: \<open>'st \<Rightarrow> bool\<close> where
  \<open>no_false_clause S \<longleftrightarrow> (\<forall>C \<in># clauses S. C \<noteq> {#})\<close>


lemma cdcl\<^sub>W_restart_no_false_clause:
  assumes
    \<open>cdcl\<^sub>W_restart S T\<close>
    \<open>no_false_clause S\<close>
  shows \<open>no_false_clause T\<close>
  using assms unfolding no_false_clause_def
  by (induction rule: cdcl\<^sub>W_restart_all_induct) (auto simp add: clauses_def)

text \<open>
  The proofs work smoothly thanks to the side-conditions about levels of the rule
  \<^term>\<open>resolve\<close>.
\<close>
lemma cdcl\<^sub>W_restart_conflict_non_zero_unless_level_0:
  assumes
    \<open>cdcl\<^sub>W_restart S T\<close>
    \<open>no_false_clause S\<close> and
    \<open>conflict_non_zero_unless_level_0 S\<close>
  shows \<open>conflict_non_zero_unless_level_0 T\<close>
  using assms by (induction rule: cdcl\<^sub>W_restart_all_induct)
    (auto simp add: conflict_non_zero_unless_level_0_def no_false_clause_def)

lemma rtranclp_cdcl\<^sub>W_restart_no_false_clause:
  assumes
    \<open>cdcl\<^sub>W_restart\<^sup>*\<^sup>* S T\<close>
    \<open>no_false_clause S\<close>
  shows \<open>no_false_clause T\<close>
  using assms by (induction rule: rtranclp_induct) (auto intro: cdcl\<^sub>W_restart_no_false_clause)

lemma rtranclp_cdcl\<^sub>W_restart_conflict_non_zero_unless_level_0:
  assumes
    \<open>cdcl\<^sub>W_restart\<^sup>*\<^sup>* S T\<close>
    \<open>no_false_clause S\<close> and
    \<open>conflict_non_zero_unless_level_0 S\<close>
  shows \<open>conflict_non_zero_unless_level_0 T\<close>
  using assms by (induction rule: rtranclp_induct)
    (auto intro: rtranclp_cdcl\<^sub>W_restart_no_false_clause cdcl\<^sub>W_restart_conflict_non_zero_unless_level_0)

definition propagated_clauses_clauses :: "'st \<Rightarrow> bool" where
\<open>propagated_clauses_clauses S \<equiv> \<forall>L K. Propagated L K \<in> set (trail S) \<longrightarrow> K \<in># clauses S\<close>

lemma propagate_single_literal_clause_get_level_is_0:
  assumes
    smaller: \<open>no_smaller_propa S\<close> and
    propa_tr: \<open>Propagated L {#L#} \<in> set (trail S)\<close> and
    n_d: \<open>no_dup (trail S)\<close> and
    propa: \<open>propagated_clauses_clauses S\<close>
  shows \<open>get_level (trail S) L = 0\<close>
proof (rule ccontr)
  assume H: \<open>\<not> ?thesis\<close>
  then obtain M M' K where
    tr: \<open>trail S = M' @ Decided K # M\<close> and
    nm: \<open>\<forall>m \<in> set M. \<not>is_decided m\<close>
    using split_list_last_prop[of "trail S" is_decided]
    by (auto simp: filter_empty_conv is_decided_def get_level_def dest!: List.set_dropWhileD)
  have uL: \<open>-L \<notin> lits_of_l (trail S)\<close>
    using n_d propa_tr unfolding lits_of_def by (fastforce simp: no_dup_cannot_not_lit_and_uminus)
  then have [iff]: \<open>defined_lit M' L \<longleftrightarrow> L \<in> lits_of_l M'\<close>
    by (auto simp add: tr Decided_Propagated_in_iff_in_lits_of_l)
  have \<open>get_level M L = 0\<close> for L
    using nm by auto
  have [simp]: \<open>L \<noteq> -K\<close>
    using tr propa_tr n_d unfolding lits_of_def by (fastforce simp: no_dup_cannot_not_lit_and_uminus
        in_set_conv_decomp)
  have \<open>L \<in> lits_of_l (M' @ [Decided K])\<close>
    apply (rule ccontr)
    using H unfolding tr
    apply (subst (asm) get_level_skip)
    using uL tr apply (auto simp: atm_of_eq_atm_of Decided_Propagated_in_iff_in_lits_of_l; fail)[]
    apply (subst (asm) get_level_skip_beginning)
    using \<open>get_level M L = 0\<close> by (auto simp: atm_of_eq_atm_of uminus_lit_swap lits_of_def)
  then have \<open>undefined_lit M L\<close>
    using n_d unfolding tr by (auto simp: defined_lit_map lits_of_def image_Un no_dup_def)
  moreover have "{#} + {#L#} \<in># clauses S"
    using propa propa_tr unfolding propagated_clauses_clauses_def by auto
  moreover have "M \<Turnstile>as CNot {#}"
    by auto
  ultimately show False
    using smaller tr unfolding no_smaller_propa_def by blast
qed


subsubsection \<open>Conflict Minimisation\<close>

paragraph \<open>Remove Literals of Level 0\<close>

lemma conflict_minimisation_level_0:
  fixes S :: 'st
  defines D[simp]: \<open>D \<equiv> the (conflicting S)\<close>
  defines [simp]: \<open>M \<equiv> trail S\<close>
  defines \<open>D' \<equiv> filter_mset (\<lambda>L. get_level M L > 0) D\<close>
  assumes
    ns_s: \<open>no_step skip S\<close> and
    ns_r: \<open>no_step resolve S\<close> and
    inv_s: "cdcl\<^sub>W_stgy_invariant S" and
    inv: "cdcl\<^sub>W_all_struct_inv S" and
    conf: \<open>conflicting S \<noteq> None\<close> \<open>conflicting S \<noteq> Some {#}\<close> and
    M_nempty: \<open>M ~= []\<close>
  shows
      "clauses S \<Turnstile>pm D'" and
      \<open>- lit_of (hd M) \<in># D'\<close>
proof -
  define D0 where D0: \<open>D0 = filter_mset (\<lambda>L. get_level M L = 0) D\<close>
  have D_D0_D': \<open>D = D0 + D'\<close>
    using multiset_partition[of D \<open>(\<lambda>L. get_level M L = 0)\<close>]
    unfolding D0 D'_def by auto
  have
    confl: \<open>cdcl\<^sub>W_conflicting S\<close> and
    decomp: \<open>all_decomposition_implies_m (clauses S) (get_all_ann_decomposition (trail S))\<close> and
    learned: \<open>cdcl\<^sub>W_learned_clause S\<close> and
    M_lev: \<open>cdcl\<^sub>W_M_level_inv S\<close> and
    alien: \<open>no_strange_atm S\<close>
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def by fast+
  have clss_D: \<open>clauses S \<Turnstile>pm D\<close>
    using learned conf unfolding cdcl\<^sub>W_learned_clause_def by auto
  have M_CNot_D: \<open>trail S \<Turnstile>as CNot D\<close> and m_confl: \<open>every_mark_is_a_conflict S\<close>
    using conf confl unfolding cdcl\<^sub>W_conflicting_def by auto
  have n_d: \<open>no_dup M\<close>
    using M_lev unfolding cdcl\<^sub>W_M_level_inv_def by auto
  have uhd_D: \<open>- lit_of (hd M) \<in># D\<close>
    using ns_s ns_r conf M_nempty inv_s M_CNot_D n_d
    unfolding cdcl\<^sub>W_stgy_invariant_def conflict_is_false_with_level_def
    by (cases \<open>trail S\<close>; cases \<open>hd (trail S)\<close>) (auto simp: skip.simps resolve.simps
      get_level_cons_if atm_of_eq_atm_of true_annots_true_cls_def_iff_negation_in_model
      uminus_lit_swap Decided_Propagated_in_iff_in_lits_of_l split: if_splits)

  have count_dec_ge_0: \<open>count_decided M > 0\<close>
  proof (rule ccontr)
    assume H: \<open>~ ?thesis\<close>
    then have \<open>get_maximum_level M D = 0\<close> for D
      by (metis (full_types) count_decided_ge_get_maximum_level gr0I le_0_eq)
    then show False
      using ns_s ns_r conf M_nempty m_confl uhd_D H
      by (cases \<open>trail S\<close>; cases \<open>hd (trail S)\<close>)
        (auto 5 5 simp: skip.simps resolve.simps intro!: state_eq_ref)
  qed
  then obtain M0 K M1 where
    M: \<open>M = M1 @ Decided K # M0\<close> and
    lev_K: \<open>get_level (trail S) K = Suc 0\<close>
    using backtrack_ex_decomp[of S 0, OF ] M_lev
    by (auto dest!: get_all_ann_decomposition_exists_prepend
      simp: cdcl\<^sub>W_M_level_inv_def simp flip: append.assoc
      simp del: append_assoc)

  have count_M0: \<open>count_decided M0 = 0\<close>
    using n_d lev_K unfolding M_def[symmetric] M by auto
  have [simp]: \<open>get_all_ann_decomposition M0 = [([], M0)]\<close>
    using count_M0 by (induction M0 rule: ann_lit_list_induct) auto
  have [simp]: \<open>get_all_ann_decomposition (M1 @ Decided K # M0) \<noteq> [([], M0)]\<close> for M1 K M0
    using length_get_all_ann_decomposition[of \<open>M1 @ Decided K # M0\<close>]
    unfolding M by auto
  have \<open>last (get_all_ann_decomposition (M1 @ Decided K # M0)) = ([], M0)\<close>
    apply (induction M1 rule: ann_lit_list_induct)
    subgoal by auto
    subgoal by auto
    subgoal for L m M1
      by (cases \<open>get_all_ann_decomposition (M1 @ Decided K # M0)\<close>) auto
    done
  then have clss_S_M0: \<open>set_mset (clauses S) \<Turnstile>ps unmark_l M0\<close>
    using decomp unfolding M_def[symmetric] M
    by (cases \<open>get_all_ann_decomposition (M1 @ Decided K # M0)\<close> rule: rev_cases)
      (auto simp: all_decomposition_implies_def)
  have H: \<open>total_over_m I (set_mset (clauses S) \<union> unmark_l M0) = total_over_m I (set_mset (clauses S))\<close>
    for I
    using alien unfolding no_strange_atm_def total_over_m_def total_over_set_def
    M_def[symmetric] M
    by (auto simp: clauses_def)
  have uL_M0_D0: \<open>-L \<in> lits_of_l M0\<close> if \<open>L \<in># D0\<close> for L
  proof (rule ccontr)
    assume L_M0: \<open>~ ?thesis\<close>
    have \<open>L \<in># D\<close> and lev_L: \<open>get_level M L = 0\<close>
      using that unfolding D_D0_D' unfolding D0 by auto
    then have \<open>-L \<in> lits_of_l M\<close>
      using M_CNot_D that by (auto simp: true_annots_true_cls_def_iff_negation_in_model)
    then have \<open>-L \<in> lits_of_l (M1 @ [Decided K])\<close>
      using L_M0 unfolding M by auto
    then have \<open>0 < get_level (M1 @ [Decided K]) L\<close> and \<open>defined_lit (M1 @ [Decided K]) L\<close>
      using get_level_last_decided_ge[of M1 K L] unfolding Decided_Propagated_in_iff_in_lits_of_l
      by fast+
    then show False
      using n_d lev_L get_level_skip_end[of \<open>M1 @ [Decided K]\<close> L M0]
      unfolding M by auto
  qed
  have clss_D0: \<open>clauses S \<Turnstile>pm {#- L#}\<close> if \<open>L \<in># D0\<close> for L
    using that clss_S_M0 uL_M0_D0[of L] unfolding true_clss_clss_def H true_clss_cls_def
      true_clss_def lits_of_def
    by auto
  have lD0D': \<open>l \<in> atms_of D0 \<Longrightarrow> l \<in> atms_of D\<close> \<open>l \<in> atms_of D' \<Longrightarrow> l \<in> atms_of D\<close> for l
    unfolding D_D0_D' by auto
  have
    H1: \<open>total_over_m I (set_mset (clauses S) \<union> {{#-L#}}) = total_over_m I (set_mset (clauses S))\<close>
    if \<open>L \<in># D0\<close> for L
    using alien conf atm_of_lit_in_atms_of[OF that]
    unfolding no_strange_atm_def total_over_m_def total_over_set_def
    M_def[symmetric] M that by (auto 5 5 simp: clauses_def dest!: lD0D')
  then have I_D0: \<open>total_over_m I (set_mset (clauses S)) \<longrightarrow>
            consistent_interp I \<longrightarrow>
            Multiset.Ball (clauses S) ((\<Turnstile>) I) \<longrightarrow> ~I \<Turnstile> D0\<close> for I
    using clss_D0 unfolding true_clss_cls_def true_cls_def consistent_interp_def
    true_cls_def true_cls_mset_def \<comment> \<open>TODO tune proof\<close>
    apply auto
    by (metis atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set literal.sel(1)
    true_cls_def true_cls_mset_def true_lit_def uminus_Pos)

  have
    H1: \<open>total_over_m I (set_mset (clauses S) \<union> {D0 + D'}) = total_over_m I (set_mset (clauses S))\<close> and
    H2: \<open>total_over_m I (set_mset (clauses S) \<union> {D'}) = total_over_m I (set_mset (clauses S))\<close> for I
    using alien conf unfolding no_strange_atm_def total_over_m_def total_over_set_def
    M_def[symmetric] M by (auto 5 5 simp: clauses_def dest!: lD0D')
  show \<open>clauses S \<Turnstile>pm D'\<close>
    using clss_D clss_D0 I_D0 unfolding D_D0_D' true_clss_cls_def true_clss_def H1 H2
    by auto
  have \<open>0 < get_level (trail S) (lit_of (hd_trail S))\<close>
    apply (cases \<open>trail S\<close>)
    using M_nempty count_dec_ge_0 by auto
  then show \<open>- lit_of (hd M) \<in># D'\<close>
    using uhd_D unfolding D'_def by auto
qed

lemma literals_of_level0_entailed:
  assumes
    struct_invs: \<open>cdcl\<^sub>W_all_struct_inv S\<close> and
    in_trail: \<open>L \<in> lits_of_l (trail S)\<close> and
    lev: \<open>get_level (trail S) L = 0\<close>
  shows
    \<open>clauses S \<Turnstile>pm {#L#}\<close>
proof -
  have decomp: \<open>all_decomposition_implies_m (clauses S) (get_all_ann_decomposition (trail S))\<close>
    using struct_invs unfolding cdcl\<^sub>W_all_struct_inv_def
    by fast
  have L_trail: \<open>{#L#} \<in> unmark_l (trail S)\<close>
    using in_trail by (auto simp: in_unmark_l_in_lits_of_l_iff)
  have n_d: \<open>no_dup (trail S)\<close>
    using struct_invs unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def
    by fast

  show ?thesis
  proof (cases \<open>count_decided (trail S) = 0\<close>)
    case True
    have \<open>get_all_ann_decomposition (trail S) = [([], trail S)]\<close>
      apply (rule no_decision_get_all_ann_decomposition)
      using True by (auto simp: count_decided_0_iff)
    then show ?thesis
      using decomp L_trail
      unfolding all_decomposition_implies_def
      by (auto intro: true_clss_clss_in_imp_true_clss_cls)
  next
    case False
    then obtain K M1 M2 M3 where
      decomp': \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S))\<close> and
      lev_K: \<open>get_level (trail S) K = Suc 0\<close> and
      M3: \<open>trail S = M3 @ M2 @ Decided K # M1\<close>
      using struct_invs backtrack_ex_decomp[of S 0] n_d unfolding cdcl\<^sub>W_all_struct_inv_def by blast
    then have dec_M1: \<open>count_decided M1 = 0\<close>
      using n_d by auto
    define M2' where \<open>M2' = M3 @ M2\<close>
    then have M3: \<open>trail S = M2' @ Decided K # M1\<close> using M3 by auto
    have \<open>get_all_ann_decomposition M1 = [([], M1)]\<close>
      apply (rule no_decision_get_all_ann_decomposition)
      using dec_M1 by (auto simp: count_decided_0_iff)
    then have \<open>([], M1) \<in> set (get_all_ann_decomposition (trail S))\<close>
      using hd_get_all_ann_decomposition_skip_some[of Nil M1 M1 \<open>_ @ _\<close>] decomp'
      by auto
    then have \<open>set_mset (clauses S) \<Turnstile>ps unmark_l M1\<close>
      using decomp
      unfolding all_decomposition_implies_def by auto
    moreover {
      have \<open>L \<in> lits_of_l M1\<close>
        using n_d lev M3 in_trail
        by (cases \<open>undefined_lit (M2' @ Decided K # []) L\<close>) (auto dest: in_lits_of_l_defined_litD)
      then have \<open>{#L#} \<in> unmark_l M1\<close>
        using in_trail by (auto simp: in_unmark_l_in_lits_of_l_iff)
    }
    ultimately show ?thesis
      unfolding all_decomposition_implies_def
      by (auto intro: true_clss_clss_in_imp_true_clss_cls)
  qed
qed


subsection \<open>Some higher level use on the invariants\<close>

text \<open>In later refinement we mostly us the group invariants and don't try to be as specific
  as above. The corresponding theorems are collected here.
\<close>
lemma conflict_conflict_is_false_with_level_all_inv:
  \<open>conflict S T \<Longrightarrow>
  no_smaller_confl S \<Longrightarrow>
  cdcl\<^sub>W_all_struct_inv S \<Longrightarrow>
  conflict_is_false_with_level T\<close>
  by (rule conflict_conflict_is_false_with_level) (auto simp: cdcl\<^sub>W_all_struct_inv_def)


lemma cdcl\<^sub>W_stgy_ex_lit_of_max_level_all_inv:
  assumes
    "cdcl\<^sub>W_stgy S S'" and
    n_l: "no_smaller_confl S" and
    "conflict_is_false_with_level S" and
    "cdcl\<^sub>W_all_struct_inv S"
  shows "conflict_is_false_with_level S'"
  by (rule cdcl\<^sub>W_stgy_ex_lit_of_max_level) (use assms in \<open>auto simp: cdcl\<^sub>W_all_struct_inv_def\<close>)

lemma cdcl\<^sub>W_o_conflict_is_false_with_level_inv_all_inv:
  assumes
    \<open>cdcl\<^sub>W_o S T\<close>
    \<open>cdcl\<^sub>W_all_struct_inv S\<close>
    \<open>conflict_is_false_with_level S\<close>
  shows \<open>conflict_is_false_with_level T\<close>
  by (rule cdcl\<^sub>W_o_conflict_is_false_with_level_inv)
    (use assms in \<open>auto simp: cdcl\<^sub>W_all_struct_inv_def\<close>)


lemma no_step_cdcl\<^sub>W_total:
  assumes
    \<open>no_step cdcl\<^sub>W S\<close>
    \<open>conflicting S = None\<close>
    \<open>no_strange_atm S\<close>
  shows \<open>total_over_m (lits_of_l (trail S)) (set_mset (clauses S))\<close>
proof (rule ccontr)
  assume \<open>\<not> ?thesis\<close>
  then obtain L where \<open>L \<in> atms_of_mm (clauses S)\<close> and \<open>undefined_lit  (trail S) (Pos L)\<close>
    by (auto simp: total_over_m_def total_over_set_def
      Decided_Propagated_in_iff_in_lits_of_l)
  then have \<open>Ex (decide S)\<close>
    using decide_rule[of S \<open>Pos L\<close> \<open>cons_trail (Decided (Pos L)) S\<close>] assms
    unfolding no_strange_atm_def clauses_def
    by force
  then show False
    using assms by (auto simp: cdcl\<^sub>W.simps cdcl\<^sub>W_o.simps)
qed

lemma cdcl\<^sub>W_Ex_cdcl\<^sub>W_stgy:
  assumes
    \<open>cdcl\<^sub>W S T\<close>
  shows \<open>Ex(cdcl\<^sub>W_stgy S)\<close>
  using assms by (meson assms cdcl\<^sub>W.simps cdcl\<^sub>W_stgy.simps)


lemma no_step_skip_hd_in_conflicting:
  assumes
    inv_s: \<open>cdcl\<^sub>W_stgy_invariant S\<close> and
    inv: \<open>cdcl\<^sub>W_all_struct_inv S\<close> and
    ns: \<open>no_step skip S\<close> and
    confl: \<open>conflicting S \<noteq> None\<close> \<open>conflicting S \<noteq> Some {#}\<close>
  shows \<open>-lit_of (hd (trail S)) \<in># the (conflicting S)\<close>
proof -
  let
    ?M = \<open>trail S\<close> and
    ?N = \<open>init_clss S\<close> and
    ?U = \<open>learned_clss S\<close> and
    ?k = \<open>backtrack_lvl S\<close> and
    ?D = \<open>conflicting S\<close>
  obtain D where D: \<open>?D = Some D\<close>
    using confl by (cases ?D) auto
  have M_D: \<open>?M \<Turnstile>as CNot D\<close>
    using inv D unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_conflicting_def by auto
  then have tr: \<open>trail S \<noteq> []\<close>
    using confl D by auto
  obtain L M where M: \<open>?M = L # M\<close>
    using tr by (cases \<open>?M\<close>) auto
  have conlf_k: \<open>conflict_is_false_with_level S\<close>
    using inv_s unfolding cdcl\<^sub>W_stgy_invariant_def by simp
  then obtain L_k where
    L_k: \<open>L_k \<in># D\<close> and lev_L_k: \<open>get_level ?M L_k = ?k\<close>
    using confl D by auto
  have dec: \<open>?k = count_decided ?M\<close>
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def by auto
  moreover {
    have \<open>no_dup ?M\<close>
      using inv unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def by auto
    then have \<open>-lit_of L \<notin> lits_of_l M\<close>
      unfolding M by (auto simp: defined_lit_map lits_of_def uminus_lit_swap)
    }
  ultimately have L_D: \<open>lit_of L \<notin># D\<close>
    using M_D unfolding M by (auto simp add: true_annots_true_cls_def_iff_negation_in_model
        uminus_lit_swap)
  show ?thesis
  proof (cases L)
    case (Decided L') note L' = this(1)
    moreover have \<open>atm_of L' = atm_of L_k\<close>
      using lev_L_k count_decided_ge_get_level[of M L_k] unfolding M dec L'
      by (auto simp: get_level_cons_if split: if_splits)
    then have \<open>L' = -L_k\<close>
      using L_k L_D L' by (auto simp: atm_of_eq_atm_of)
    then show ?thesis using L_k unfolding D M L' by simp
  next
    case (Propagated L' C)
    then show ?thesis
      using ns confl by (auto simp: skip.simps M D)
  qed
qed

lemma
  fixes S
  assumes
     nss: \<open>no_step skip S\<close> and
     nsr: \<open>no_step resolve S\<close> and
     invs: \<open>cdcl\<^sub>W_all_struct_inv S\<close> and
     stgy: \<open>cdcl\<^sub>W_stgy_invariant S\<close> and
     confl: \<open>conflicting S \<noteq> None\<close> and
     confl': \<open>conflicting S \<noteq> Some {#}\<close>
  shows no_skip_no_resolve_single_highest_level:
    \<open>the (conflicting S) =
       add_mset (-(lit_of (hd (trail S)))) {#L \<in># the (conflicting S).
         get_level (trail S) L < local.backtrack_lvl S#}\<close> (is ?A) and
      no_skip_no_resolve_level_lvl_nonzero:
    \<open>0 < backtrack_lvl S\<close> (is ?B) and
      no_skip_no_resolve_level_get_maximum_lvl_le:
    \<open>get_maximum_level (trail S) (remove1_mset (-(lit_of (hd (trail S)))) (the (conflicting S)))
        < backtrack_lvl S\<close> (is ?C)
proof -
  define K where \<open>K \<equiv> lit_of (hd (trail S))\<close>
  have K: \<open>-K \<in># the (conflicting S)\<close>
    using no_step_skip_hd_in_conflicting[OF stgy invs nss confl confl']
    unfolding K_def .
  have
    \<open>no_strange_atm S\<close> and
    lev: \<open>cdcl\<^sub>W_M_level_inv S\<close> and
    \<open>\<forall>s\<in>#learned_clss S. \<not> tautology s\<close> and
    dist: \<open>distinct_cdcl\<^sub>W_state S\<close> and
    conf: \<open>cdcl\<^sub>W_conflicting S\<close> and
    \<open>all_decomposition_implies_m (local.clauses S)
      (get_all_ann_decomposition (trail S))\<close> and
    learned: \<open>cdcl\<^sub>W_learned_clause S\<close>
    using invs unfolding cdcl\<^sub>W_all_struct_inv_def
    by auto

  obtain D where
    D[simp]: \<open>conflicting S = Some (add_mset (-K) D)\<close>
    using confl K by (auto dest: multi_member_split)

  have dist: \<open>distinct_mset (the (conflicting S))\<close>
    using dist confl unfolding distinct_cdcl\<^sub>W_state_def by auto
  then have [iff]: \<open>L \<notin># remove1_mset L (the (conflicting S))\<close> for L
    by (meson distinct_mem_diff_mset union_single_eq_member)
  from this[of K] have [simp]: \<open>-K \<notin># D\<close> using dist by auto

  have nd: \<open>no_dup (trail S)\<close>
    using lev unfolding cdcl\<^sub>W_M_level_inv_def by auto
  have CNot: \<open>trail S \<Turnstile>as CNot (add_mset (-K) D)\<close>
    using conf unfolding cdcl\<^sub>W_conflicting_def
    by fastforce
  then have tr: \<open>trail S \<noteq> []\<close>
    by auto
  have [simp]: \<open>K \<notin># D\<close>
    using nd K_def tr CNot unfolding true_annots_true_cls_def_iff_negation_in_model
    by (cases \<open>trail S\<close>)
       (auto simp: uminus_lit_swap Decided_Propagated_in_iff_in_lits_of_l dest!: multi_member_split)
  have H1:
    \<open>0 < backtrack_lvl S\<close>
  proof (cases \<open>is_proped (hd (trail S))\<close>)
    case proped: True
    obtain C M where
      [simp]: \<open>trail S = Propagated K C # M\<close>
      using tr proped K_def
      by (cases \<open>trail S\<close>; cases \<open>hd (trail S)\<close>)
        (auto simp: K_def)
    have \<open>a @ Propagated L mark # b = Propagated K C # M \<longrightarrow>
       b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close> for L mark a b
      using conf unfolding cdcl\<^sub>W_conflicting_def
      by fastforce
    from this[of \<open>[]\<close>] have [simp]: \<open>K \<in># C\<close> \<open>M \<Turnstile>as CNot (remove1_mset K C)\<close>
      by auto
    have [simp]: \<open>get_maximum_level (Propagated K C # M) D = get_maximum_level M D\<close>
      by (rule get_maximum_level_skip_first)
        (auto simp: atms_of_def atm_of_eq_atm_of uminus_lit_swap[symmetric])

    have \<open>get_maximum_level M D < count_decided M\<close>
      using nsr tr confl K proped count_decided_ge_get_maximum_level[of M D]
      by (auto simp: resolve.simps get_level_cons_if atm_of_eq_atm_of)
    then show ?thesis by simp
  next
    case proped: False
    have \<open>get_maximum_level (tl (trail S)) D < count_decided (trail S)\<close>
      using tr confl K proped count_decided_ge_get_maximum_level[of \<open>tl (trail S)\<close> D]
      by (cases \<open>trail S\<close>; cases \<open>hd (trail S)\<close>)
         (auto simp: resolve.simps get_level_cons_if atm_of_eq_atm_of)
    then show ?thesis
      by simp
  qed
  show H2: ?C
  proof (cases \<open>is_proped (hd (trail S))\<close>)
    case proped: True
    obtain C M where
      [simp]: \<open>trail S = Propagated K C # M\<close>
      using tr proped K_def
      by (cases \<open>trail S\<close>; cases \<open>hd (trail S)\<close>)
        (auto simp: K_def)
    have \<open>a @ Propagated L mark # b = Propagated K C # M \<longrightarrow>
       b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close> for L mark a b
      using conf unfolding cdcl\<^sub>W_conflicting_def
      by fastforce
    from this[of \<open>[]\<close>] have [simp]: \<open>K \<in># C\<close> \<open>M \<Turnstile>as CNot (remove1_mset K C)\<close>
      by auto
    have [simp]: \<open>get_maximum_level (Propagated K C # M) D = get_maximum_level M D\<close>
      by (rule get_maximum_level_skip_first)
        (auto simp: atms_of_def atm_of_eq_atm_of uminus_lit_swap[symmetric])

    have \<open>get_maximum_level M D < count_decided M\<close>
      using nsr tr confl K proped count_decided_ge_get_maximum_level[of M D]
      by (auto simp: resolve.simps get_level_cons_if atm_of_eq_atm_of)
    then show ?thesis by simp
  next
    case proped: False
    have \<open>get_maximum_level (tl (trail S)) D = get_maximum_level (trail S) D\<close>
      apply (rule get_maximum_level_cong)
      using K_def \<open>- K \<notin># D\<close> \<open>K \<notin># D\<close>
      apply (cases \<open>trail S\<close>)
      by (auto simp: get_level_cons_if atm_of_eq_atm_of)
    moreover have \<open>get_maximum_level (tl (trail S)) D < count_decided (trail S)\<close>
      using tr confl K proped count_decided_ge_get_maximum_level[of \<open>tl (trail S)\<close> D]
      by (cases \<open>trail S\<close>; cases \<open>hd (trail S)\<close>)
         (auto simp: resolve.simps get_level_cons_if atm_of_eq_atm_of)
    ultimately show ?thesis
      by (simp add: K_def)
  qed

  have H:
    \<open>get_level (trail S) L < local.backtrack_lvl S\<close>
    if \<open>L \<in># remove1_mset (-K) (the (conflicting S))\<close>
    for L
  proof (cases \<open>is_proped (hd (trail S))\<close>)
    case proped: True
    obtain C M where
      [simp]: \<open>trail S = Propagated K C # M\<close>
      using tr proped K_def
      by (cases \<open>trail S\<close>; cases \<open>hd (trail S)\<close>)
        (auto simp: K_def)
    have \<open>a @ Propagated L mark # b = Propagated K C # M \<longrightarrow>
       b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close> for L mark a b
      using conf unfolding cdcl\<^sub>W_conflicting_def
      by fastforce
    from this[of \<open>[]\<close>] have [simp]: \<open>K \<in># C\<close> \<open>M \<Turnstile>as CNot (remove1_mset K C)\<close>
      by auto
    have [simp]: \<open>get_maximum_level (Propagated K C # M) D = get_maximum_level M D\<close>
      by (rule get_maximum_level_skip_first)
        (auto simp: atms_of_def atm_of_eq_atm_of uminus_lit_swap[symmetric])

    have \<open>get_maximum_level M D < count_decided M\<close>
      using nsr tr confl K that proped count_decided_ge_get_maximum_level[of M D]
      by (auto simp: resolve.simps get_level_cons_if atm_of_eq_atm_of)
    then show ?thesis
      using get_maximum_level_ge_get_level[of L D M] that
      by (auto simp: resolve.simps get_level_cons_if atm_of_eq_atm_of)
  next
    case proped: False
    have L_K: \<open>L \<noteq> - K\<close> \<open>-L \<noteq> K\<close> \<open>L \<noteq> -lit_of (hd (trail S))\<close>
      using that by (auto simp: uminus_lit_swap K_def[symmetric])
    have \<open>L \<noteq> lit_of (hd (trail S))\<close>
      using tr that K_def \<open>K \<notin># D\<close>
      by (cases \<open>trail S\<close>; cases \<open>hd (trail S)\<close>)
         (auto simp: resolve.simps get_level_cons_if atm_of_eq_atm_of)

    have \<open>get_maximum_level (tl (trail S)) D < count_decided (trail S)\<close>
      using tr confl K that proped count_decided_ge_get_maximum_level[of \<open>tl (trail S)\<close> D]
      by (cases \<open>trail S\<close>; cases \<open>hd (trail S)\<close>)
         (auto simp: resolve.simps get_level_cons_if atm_of_eq_atm_of)
    then show ?thesis
      using get_maximum_level_ge_get_level[of L D \<open>(trail S)\<close>] that tr L_K \<open>L \<noteq> lit_of (hd (trail S))\<close>
        count_decided_ge_get_level[of \<open>tl (trail S)\<close> L] proped
      by (cases \<open>trail S\<close>; cases \<open>hd (trail S)\<close>)
        (auto simp: resolve.simps get_level_cons_if atm_of_eq_atm_of)
  qed
  have [simp]: \<open>get_level (trail S) K = local.backtrack_lvl S\<close>
    using tr K_def
    by (cases \<open>trail S\<close>; cases \<open>hd (trail S)\<close>)
      (auto simp: resolve.simps get_level_cons_if atm_of_eq_atm_of)
  show ?A
    apply (rule distinct_set_mset_eq)
    subgoal using dist by auto
    subgoal using dist by (auto simp: distinct_mset_filter K_def[symmetric])
    subgoal using H by (auto simp: K_def[symmetric])
    done
  show ?B
    using H1 .
qed

end

end
