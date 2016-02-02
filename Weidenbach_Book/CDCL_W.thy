theory CDCL_W
imports Partial_Annotated_Clausal_Logic List_More CDCL_W_Level Wellfounded_More

begin
declare set_mset_minus_replicate_mset[simp]

lemma Bex_set_set_Bex_set[iff]: "(\<exists>x\<in>set_mset C. P) \<longleftrightarrow> (\<exists>x\<in>#C. P)"
  by auto

section \<open>Weidenbach's CDCL\<close>
sledgehammer_params[verbose, e spass cvc4 z3 verit]
declare upt.simps(2)[simp del]

datatype 'a conflicting_clause = C_True | C_Clause "'a"

subsection \<open>The State\<close>
locale state\<^sub>W =
  fixes
    trail :: "'st \<Rightarrow> ('v, nat, 'v clause) marked_lits" and
    init_clss :: "'st \<Rightarrow> 'v clauses" and
    learned_clss :: "'st \<Rightarrow> 'v clauses" and
    backtrack_lvl :: "'st \<Rightarrow> nat" and
    conflicting :: "'st \<Rightarrow>'v clause conflicting_clause" and

    cons_trail :: "('v, nat, 'v clause) marked_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow>'st" and
    add_init_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    add_learned_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_backtrack_lvl :: "nat \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conflicting :: "'v clause conflicting_clause \<Rightarrow> 'st \<Rightarrow> 'st" and

    init_state :: "'v clauses \<Rightarrow> 'st" and
    restart_state :: "'st \<Rightarrow> 'st"
  assumes
    trail_cons_trail[simp]:
      "\<And>L st. undefined_lit (trail st) (lit_of L) \<Longrightarrow> trail (cons_trail L st) = L # trail st" and
    trail_tl_trail[simp]: "\<And>st. trail (tl_trail st) = tl (trail st)" and
    update_trail_update_clss[simp]: "\<And>st C. trail (add_init_cls C st) = trail st" and
    trail_add_learned_cls[simp]: "\<And>C st. trail (add_learned_cls C st) = trail st" and
    trail_remove_cls[simp]: "\<And>C st. trail (remove_cls C st) = trail st" and
    trail_update_backtrack_lvl[simp]: "\<And>st C. trail (update_backtrack_lvl C st) = trail st" and
    trail_update_conflicting[simp]: "\<And>C st. trail (update_conflicting C st) = trail st" and

    init_clss_cons_trail[simp]:
      "\<And>M st. undefined_lit (trail st) (lit_of M)\<Longrightarrow> init_clss (cons_trail M st) = init_clss st" and
    init_clss_tl_trail[simp]:
      "\<And>st. init_clss (tl_trail st) = init_clss st" and
    init_clss_update_clss[simp]:
      "\<And>st C. init_clss (add_init_cls C st) = {#C#} + init_clss st" and
    init_clss_add_learned_cls[simp]:
      "\<And>C st. init_clss (add_learned_cls C st) = init_clss st" and
    init_clss_remove_cls[simp]:
      "\<And>C st. init_clss (remove_cls C st) = remove_mset C (init_clss st)" and
    init_clss_update_backtrack_lvl[simp]:
      "\<And>st C. init_clss (update_backtrack_lvl C st) = init_clss st" and
    init_clss_update_conflicting[simp]:
      "\<And>C st. init_clss (update_conflicting C st) = init_clss st" and

    learned_clss_cons_trail[simp]:
      "\<And>M st. undefined_lit (trail st) (lit_of M) \<Longrightarrow>
        learned_clss (cons_trail M st) = learned_clss st" and
    learned_clss_tl_trail[simp]: "\<And>st. learned_clss (tl_trail st) = learned_clss st" and
    learned_clss_update_clss[simp]:
      "\<And>st C. learned_clss (add_init_cls C st) = learned_clss st" and
    learned_clss_add_learned_cls[simp]:
      "\<And>C st. learned_clss (add_learned_cls C st) = {#C#} + learned_clss st" and
    learned_clss_remove_cls[simp]:
      "\<And>C st. learned_clss (remove_cls C st) = remove_mset C (learned_clss st)" and
    learned_clss_update_backtrack_lvl[simp]:
      "\<And>st C. learned_clss (update_backtrack_lvl C st) = learned_clss st" and
    learned_clss_update_conflicting[simp]:
      "\<And>C st. learned_clss (update_conflicting C st) = learned_clss st" and

    backtrack_lvl_cons_trail[simp]:
      "\<And>M st. undefined_lit (trail st) (lit_of M) \<Longrightarrow>
        backtrack_lvl (cons_trail M st) = backtrack_lvl st" and
    backtrack_lvl_tl_trail[simp]:
      "\<And>st. backtrack_lvl (tl_trail st) = backtrack_lvl st" and
    backtrack_lvl_add_init_cls[simp]:
      "\<And>st C. backtrack_lvl (add_init_cls C st) = backtrack_lvl st"  and
    backtrack_lvl_add_learned_cls[simp]:
      "\<And>C st. backtrack_lvl (add_learned_cls C st) = backtrack_lvl st" and
    backtrack_lvl_remove_cls[simp]:
      "\<And>C st. backtrack_lvl (remove_cls C st) = backtrack_lvl st" and
    backtrack_lvl_update_backtrack_lvl[simp]:
      "\<And>st k. backtrack_lvl (update_backtrack_lvl k st) = k" and
    backtrack_lvl_update_conflicting[simp]:
      "\<And>C st. backtrack_lvl (update_conflicting C st) = backtrack_lvl st" and

    conflicting_cons_trail[simp]:
      "\<And>M st. undefined_lit (trail st) (lit_of M) \<Longrightarrow>
        conflicting (cons_trail M st) = conflicting st" and
    conflicting_tl_trail[simp]:
      "\<And>st. conflicting (tl_trail st) = conflicting st" and
    conflicting_add_init_cls[simp]:
      "\<And>st C. conflicting (add_init_cls C st) = conflicting st" and
    conflicting_add_learned_cls[simp]:
      "\<And>C st. conflicting (add_learned_cls C st) = conflicting st" and
    conflicting_remove_cls[simp]:
      "\<And>C st. conflicting (remove_cls C st) = conflicting st" and
    conflicting_update_backtrack_lvl[simp]:
      "\<And>st C. conflicting (update_backtrack_lvl C st) = conflicting st" and
    conflicting_update_conflicting[simp]:
      "\<And>C st. conflicting (update_conflicting C st) = C" and

    init_state_trail[simp]: "\<And>N. trail (init_state N) = []" and
    init_state_clss[simp]: "\<And>N. init_clss (init_state N) = N" and
    init_state_learned_clss[simp]: "\<And>N. learned_clss (init_state N) = {#}" and
    init_state_backtrack_lvl[simp]: "\<And>N. backtrack_lvl (init_state N) = 0" and
    init_state_conflicting[simp]: "\<And>N. conflicting (init_state N) = C_True" and

    trail_restart_state[simp]: "trail (restart_state S) = []" and
    init_clss_restart_state[simp]: "init_clss (restart_state S) = init_clss S" and
    learned_clss_restart_state[intro]: "learned_clss (restart_state S) \<subseteq># learned_clss S" and
    backtrack_lvl_restart_state[simp]: "backtrack_lvl (restart_state S) = 0" and
    conflicting_restart_state[simp]: "conflicting (restart_state S) = C_True"
begin

definition clauses :: "'st \<Rightarrow> 'v clauses" where
"clauses S = init_clss S + learned_clss S"

lemma
  shows
    clauses_cons_trail[simp]:
      "undefined_lit (trail S) (lit_of M) \<Longrightarrow>clauses (cons_trail M S) = clauses S" and
    clauses_tl_trail[simp]: "clauses (tl_trail S) = clauses S" and
    clauses_add_learned_cls_unfolded:
      "clauses (add_learned_cls U S) = {#U#} + learned_clss S + init_clss S" and
    clauses_add_init_cls[simp]:
      "clauses (add_init_cls N S) = {#N#} + init_clss S + learned_clss S" and
    clauses_update_backtrack_lvl[simp]: "clauses (update_backtrack_lvl k S) = clauses S" and
    clauses_update_conflicting[simp]: "clauses (update_conflicting D S) = clauses S" and
    clauses_remove_cls[simp]:
      "clauses (remove_cls C S) = clauses S - replicate_mset (count (clauses S) C) C" and
    clauses_add_learned_cls[simp]: "clauses (add_learned_cls C S) = {#C#} + clauses S" and
    clauses_restart[simp]: "clauses (restart_state S) \<subseteq># clauses S" and
    clauses_init_state[simp]: "\<And>N. clauses (init_state N) = N"
    prefer 9 using clauses_def learned_clss_restart_state apply fastforce
    by (auto simp: ac_simps replicate_mset_plus clauses_def intro: multiset_eqI)

abbreviation state ::  "'st \<Rightarrow> ('v, nat, 'v clause) marked_lit list \<times> 'v clauses \<times> 'v clauses
  \<times> nat \<times> 'v clause conflicting_clause" where
"state S \<equiv> (trail S, init_clss S, learned_clss S, backtrack_lvl S, conflicting S)"

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

lemmas state_simp[simp] = state_eq_trail state_eq_init_clss state_eq_learned_clss
  state_eq_backtrack_lvl state_eq_conflicting state_eq_clauses state_eq_undefined_lit


lemma atms_of_m_learned_clss_restart_state_in_atms_of_m_learned_clssI[intro]:
  "x \<in> atms_of_mu (learned_clss (restart_state S)) \<Longrightarrow> x \<in> atms_of_mu (learned_clss S)"
  by (meson atms_of_m_mono learned_clss_restart_state set_mset_mono subsetCE)

function reduce_trail_to :: "('v, nat, 'v clause) marked_lits \<Rightarrow> 'st \<Rightarrow> 'st" where
"reduce_trail_to F S =
  (if length (trail S) = length F \<or> trail S = [] then S else reduce_trail_to F (tl_trail S))"
by fast+
termination
  by (relation "measure (\<lambda>(_, S). length (trail S))") simp_all

declare reduce_trail_to.simps[simp del]

lemma
  shows
  reduce_trail_to_nil[simp]: "trail S = [] \<Longrightarrow> reduce_trail_to F S = S" and
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

lemma trail_reduce_trail_to_nil[simp]:
  "trail (reduce_trail_to [] S) = []"
  apply (induction "[]::  ('v, nat, 'v clause) marked_lits" S rule: reduce_trail_to.induct)
  by (metis length_0_conv reduce_trail_to_length_ne reduce_trail_to_nil)

lemma clauses_reduce_trail_to_nil:
  "clauses (reduce_trail_to [] S) = clauses S"
  apply (induction "[]::  ('v, nat, 'v clause) marked_lits" S rule: reduce_trail_to.induct)
  by (metis clauses_tl_trail reduce_trail_to.simps)

lemma reduce_trail_to_skip_beginning:
  assumes "trail S = F' @ F"
  shows "trail (reduce_trail_to F S) = F"
  using assms by (induction F' arbitrary: S) (auto simp: reduce_trail_to_length_ne)

lemma clauses_reduce_trail_to[simp]:
  "clauses (reduce_trail_to F S) = clauses S"
  apply (induction F S rule: reduce_trail_to.induct)
  by (metis clauses_tl_trail reduce_trail_to.simps)

lemma conflicting_update_trial[simp]:
  "conflicting (reduce_trail_to F S) = conflicting S"
  apply (induction F S rule: reduce_trail_to.induct)
  by (metis conflicting_tl_trail reduce_trail_to.simps)

lemma backtrack_lvl_update_trial[simp]:
  "backtrack_lvl (reduce_trail_to F S) = backtrack_lvl S"
  apply (induction F S rule: reduce_trail_to.induct)
  by (metis backtrack_lvl_tl_trail reduce_trail_to.simps)

lemma init_clss_update_trial[simp]:
  "init_clss (reduce_trail_to F S) = init_clss S"
  apply (induction F S rule: reduce_trail_to.induct)
  by (metis init_clss_tl_trail reduce_trail_to.simps)

lemma learned_clss_update_trial[simp]:
  "learned_clss (reduce_trail_to F S) = learned_clss S"
  apply (induction F S rule: reduce_trail_to.induct)
  by (metis learned_clss_tl_trail reduce_trail_to.simps)

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
  "trail S = F' @ Marked K d # F \<Longrightarrow> (trail (reduce_trail_to F S)) = F "
  apply (rule reduce_trail_to_skip_beginning[of _ "F' @ Marked K d # []"])
  by (cases F') (auto simp add:tl_append reduce_trail_to_skip_beginning)

lemma reduce_trail_to_add_learned_cls[simp]:
  "trail (reduce_trail_to F (add_learned_cls C S)) = trail (reduce_trail_to F S)"
  by (rule trail_eq_reduce_trail_to_eq) auto

lemma reduce_trail_to_add_init_cls[simp]:
  "trail (reduce_trail_to F (add_init_cls C S)) = trail (reduce_trail_to F S)"
  by (rule trail_eq_reduce_trail_to_eq) auto

lemma reduce_trail_to_remove_learned_cls[simp]:
  "trail (reduce_trail_to F (remove_cls C S)) = trail (reduce_trail_to F S)"
  by (rule trail_eq_reduce_trail_to_eq) auto

lemma reduce_trail_to_update_conflicting[simp]:
  "trail (reduce_trail_to F (update_conflicting C S)) = trail (reduce_trail_to F S)"
  by (rule trail_eq_reduce_trail_to_eq) auto

lemma reduce_trail_to_update_backtrack_lvl[simp]:
  "trail (reduce_trail_to F (update_backtrack_lvl C S)) = trail (reduce_trail_to F S)"
  by (rule trail_eq_reduce_trail_to_eq) auto

lemma in_get_all_marked_decomposition_marked_or_empty:
  assumes "(a, b) \<in> set (get_all_marked_decomposition M)"
  shows "a = [] \<or> (is_marked (hd a))"
  using assms
proof (induct M arbitrary: a b)
  case Nil then show ?case by simp
next
  case (Cons m M)
  show ?case
    proof (cases m)
      case (Marked l mark)
      then show ?thesis using Cons by auto
    next
      case (Propagated l mark)
      then show ?thesis using Cons by (cases "get_all_marked_decomposition M") force+
    qed
qed

lemma in_get_all_marked_decomposition_trail_update_trail[simp]:
  assumes  H: "(L # M1, M2) \<in> set (get_all_marked_decomposition (trail S))"
  shows "trail (reduce_trail_to M1 S) = M1"
proof -
  obtain K mark where
    L: "L = Marked K mark"
    using H by (cases L) (auto dest!: in_get_all_marked_decomposition_marked_or_empty)
  obtain c where
    tr_S: "trail S = c @ M2 @ L # M1"
    using H by auto
  show ?thesis
    by (rule reduce_trail_to_trail_tl_trail_decomp[of _ "c @ M2" K mark])
     (auto simp: tr_S L)
qed

fun append_trail where
"append_trail [] S = S" |
"append_trail (L # M) S = append_trail M (cons_trail L S)"

lemma trail_append_trail[simp]:
  "no_dup (M @ trail S) \<Longrightarrow> trail (append_trail M S) = rev M @ trail S"
  by (induction M arbitrary: S) (auto simp: defined_lit_map)


lemma learned_clss_append_trail[simp]:
  "no_dup (M @ trail S) \<Longrightarrow> learned_clss (append_trail M S) = learned_clss S"
  by (induction M arbitrary: S) (auto simp: defined_lit_map)

lemma init_clss_append_trail[simp]:
  "no_dup (M @ trail S) \<Longrightarrow> init_clss (append_trail M S) = init_clss S"
  by (induction M arbitrary: S) (auto simp: defined_lit_map)

lemma conflicting_append_trail[simp]:
  "no_dup (M @ trail S) \<Longrightarrow> conflicting (append_trail M S) = conflicting S"
  by (induction M arbitrary: S) (auto simp: defined_lit_map)

lemma backtrack_lvl_append_trail[simp]:
  "no_dup (M @ trail S) \<Longrightarrow> backtrack_lvl (append_trail M S) = backtrack_lvl S"
  by (induction M arbitrary: S) (auto simp: defined_lit_map)

lemma clauses_append_trail[simp]:
  "no_dup (M @ trail S) \<Longrightarrow> clauses (append_trail M S) = clauses S"
  by (induction M arbitrary: S) (auto simp: defined_lit_map)

text \<open>This function is useful for proofs to speak of a global trail change, but is a bad for
  programs and code in general.\<close>
fun delete_trail_and_rebuild where
"delete_trail_and_rebuild M S = append_trail (rev M) (reduce_trail_to [] S)"

end

subsection \<open>Special Instantiation: using Triples as State\<close>


subsection \<open>CDCL Rules\<close>
text \<open>Because of the strategy we will later use, we distinguish propagate, conflict from the other
  rules\<close>
locale
  cdcl\<^sub>W_ops =
   state\<^sub>W trail init_clss learned_clss backtrack_lvl conflicting cons_trail tl_trail add_init_cls
   add_learned_cls remove_cls update_backtrack_lvl update_conflicting init_state
   restart_state
  for
    trail :: "'st \<Rightarrow> ('v, nat, 'v clause) marked_lits" and
    init_clss :: "'st \<Rightarrow> 'v clauses" and
    learned_clss :: "'st \<Rightarrow> 'v clauses" and
    backtrack_lvl :: "'st \<Rightarrow> nat" and
    conflicting :: "'st \<Rightarrow>'v clause conflicting_clause" and

    cons_trail :: "('v, nat, 'v clause) marked_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_init_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    add_learned_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_backtrack_lvl :: "nat \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conflicting :: "'v clause conflicting_clause \<Rightarrow> 'st \<Rightarrow> 'st" and

    init_state :: "'v clauses \<Rightarrow> 'st" and
    restart_state :: "'st \<Rightarrow> 'st"
begin

inductive propagate :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
propagate_rule[intro]:
  "state S = (M, N, U, k, C_True) \<Longrightarrow>  C + {#L#} \<in># clauses S \<Longrightarrow> M \<Turnstile>as CNot C
  \<Longrightarrow> undefined_lit (trail S) L
  \<Longrightarrow> T \<sim> cons_trail (Propagated L (C + {#L#})) S
  \<Longrightarrow> propagate S T"
inductive_cases propagateE[elim]: "propagate S T"
thm propagateE

inductive conflict ::  "'st \<Rightarrow> 'st \<Rightarrow> bool" where
conflict_rule[intro]: "state S = (M, N, U, k, C_True) \<Longrightarrow> D \<in># clauses S \<Longrightarrow> M \<Turnstile>as CNot D
  \<Longrightarrow> T \<sim> update_conflicting (C_Clause D) S
  \<Longrightarrow> conflict S T"

inductive_cases conflictE[elim]: "conflict S S'"

inductive backtrack ::  "'st \<Rightarrow> 'st \<Rightarrow> bool" where
backtrack_rule[intro]: "state S = (M, N, U, k, C_Clause (D + {#L#}))
  \<Longrightarrow> (Marked K (i+1) # M1, M2) \<in> set (get_all_marked_decomposition M)
  \<Longrightarrow> get_level L M = k
  \<Longrightarrow> get_level L M = get_maximum_level (D+{#L#}) M
  \<Longrightarrow> get_maximum_level D M = i
  \<Longrightarrow> T \<sim> cons_trail (Propagated L (D+{#L#}))
            (reduce_trail_to M1
              (add_learned_cls (D + {#L#})
                (update_backtrack_lvl i
                  (update_conflicting C_True S))))
  \<Longrightarrow> backtrack S T"
inductive_cases backtrackE[elim]: "backtrack S S'"
thm backtrackE

inductive decide ::  "'st \<Rightarrow> 'st \<Rightarrow> bool" where
decide_rule[intro]: "state S = (M, N, U, k, C_True)
\<Longrightarrow> undefined_lit M L \<Longrightarrow> atm_of L \<in> atms_of_mu (init_clss S)
\<Longrightarrow> T \<sim> cons_trail (Marked L (k+1)) (incr_lvl S)
\<Longrightarrow> decide S T"
inductive_cases decideE[elim]: "decide S S'"
thm decideE

inductive skip :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
skip_rule[intro]: "state S = (Propagated L C' # M, N, U, k, C_Clause D) \<Longrightarrow>  -L \<notin># D \<Longrightarrow> D \<noteq> {#}
  \<Longrightarrow> T \<sim> tl_trail S
  \<Longrightarrow> skip S T"
inductive_cases skipE[elim]: "skip S S'"
thm skipE

text \<open>@{term "get_maximum_level D (Propagated L (C + {#L#}) # M) = k \<or> k = 0"} is equivalent to
  @{term "get_maximum_level D (Propagated L (C + {#L#}) # M) = k"}\<close>
inductive resolve :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
resolve_rule[intro]: "
  state S = (Propagated L ( (C + {#L#})) # M, N, U, k, C_Clause (D + {#-L#}))
  \<Longrightarrow> get_maximum_level D (Propagated L (C + {#L#}) # M) = k
  \<Longrightarrow> T \<sim> update_conflicting (C_Clause (D #\<union> C)) (tl_trail S)
  \<Longrightarrow> resolve S T"
inductive_cases resolveE[elim]: "resolve S S'"
thm resolveE

inductive restart :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
restart: "state S = (M, N, U, k, C_True) \<Longrightarrow> \<not>M \<Turnstile>asm clauses S
\<Longrightarrow> T \<sim> restart_state S
\<Longrightarrow> restart S T"
inductive_cases restartE[elim]: "restart S T"
thm restartE

text \<open>We add the condition @{term "C \<notin># init_clss S"}, to maintain consistency even without the
  strategy.\<close>
inductive forget :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
forget_rule: "state S = (M, N, {#C#} + U, k, C_True)
  \<Longrightarrow> \<not>M \<Turnstile>asm clauses S
  \<Longrightarrow>  C \<notin> set (get_all_mark_of_propagated (trail S))
  \<Longrightarrow> C \<notin># init_clss S
  \<Longrightarrow> C \<in># learned_clss S
  \<Longrightarrow> T \<sim> remove_cls C S
  \<Longrightarrow> forget S T"
inductive_cases forgetE[elim]: "forget S T"

inductive cdcl\<^sub>W_rf :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
restart: "restart S T \<Longrightarrow> cdcl\<^sub>W_rf S T" |
forget: "forget S T \<Longrightarrow> cdcl\<^sub>W_rf S T"

inductive cdcl\<^sub>W_bj ::  "'st \<Rightarrow> 'st \<Rightarrow> bool" where
skip[intro]: "skip S S' \<Longrightarrow> cdcl\<^sub>W_bj S S'" |
resolve[intro]: "resolve S S' \<Longrightarrow> cdcl\<^sub>W_bj S S'" |
backtrack[intro]: "backtrack S S' \<Longrightarrow> cdcl\<^sub>W_bj S S'"

inductive_cases cdcl\<^sub>W_bjE: "cdcl\<^sub>W_bj S T"

inductive cdcl\<^sub>W_o:: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
decide[intro]: "decide S S' \<Longrightarrow> cdcl\<^sub>W_o S S'" |
bj[intro]: "cdcl\<^sub>W_bj S S' \<Longrightarrow> cdcl\<^sub>W_o S S'"

inductive cdcl\<^sub>W :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
propagate: "propagate S S' \<Longrightarrow> cdcl\<^sub>W S S'" |
conflict: "conflict S S' \<Longrightarrow> cdcl\<^sub>W S S'" |
other: "cdcl\<^sub>W_o S S' \<Longrightarrow> cdcl\<^sub>W S S'"|
rf: "cdcl\<^sub>W_rf S S' \<Longrightarrow> cdcl\<^sub>W S S'"

lemma rtranclp_propagate_is_rtranclp_cdcl\<^sub>W:
  "propagate\<^sup>*\<^sup>* S S' \<Longrightarrow> cdcl\<^sub>W\<^sup>*\<^sup>* S S'"
  by (induction rule: rtranclp.induct) (fastforce dest!: propagate)+

lemma cdcl\<^sub>W_all_rules_induct[consumes 1, case_names propagate conflict forget restart decide skip
    resolve backtrack]:
  fixes S  :: "'st"
  assumes
    cdcl\<^sub>W: "cdcl\<^sub>W S S'" and
    propagate: "\<And>T. propagate S T \<Longrightarrow> P S T" and
    conflict:  "\<And>T. conflict S T \<Longrightarrow> P S T" and
    forget:  "\<And>T. forget S T \<Longrightarrow> P S T" and
    restart:  "\<And>T. restart S T \<Longrightarrow> P S T" and
    decide:  "\<And>T. decide S T \<Longrightarrow> P S T" and
    skip:  "\<And>T. skip S T \<Longrightarrow> P S T" and
    resolve:  "\<And>T. resolve S T \<Longrightarrow> P S T" and
    backtrack:  "\<And>T. backtrack S T \<Longrightarrow> P S T"
  shows "P S S'"
  using assms(1)
proof (induct S' rule: cdcl\<^sub>W.induct)
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

lemma cdcl\<^sub>W_all_induct[consumes 1, case_names propagate conflict forget restart decide skip
    resolve backtrack]:
  fixes S  :: "'st"
  assumes
    cdcl\<^sub>W: "cdcl\<^sub>W S S'" and
    propagateH: "\<And>C L T. C + {#L#} \<in># clauses S \<Longrightarrow> trail S \<Turnstile>as CNot C
      \<Longrightarrow> undefined_lit (trail S) L \<Longrightarrow> conflicting S = C_True
      \<Longrightarrow> T \<sim> cons_trail (Propagated L (C + {#L#})) S
      \<Longrightarrow> P S T" and
    conflictH: "\<And>D T. D \<in># clauses S \<Longrightarrow> conflicting S = C_True \<Longrightarrow> trail S \<Turnstile>as CNot D
      \<Longrightarrow> T \<sim> update_conflicting (C_Clause D) S
      \<Longrightarrow> P S T" and
    forgetH: "\<And>C T. \<not>trail S \<Turnstile>asm clauses S
      \<Longrightarrow> C \<notin> set (get_all_mark_of_propagated (trail S))
      \<Longrightarrow> C \<notin># init_clss S
      \<Longrightarrow> C \<in># learned_clss S
      \<Longrightarrow> conflicting S = C_True
      \<Longrightarrow> T \<sim> remove_cls C S
      \<Longrightarrow> P S T" and
    restartH: "\<And>T. \<not>trail S \<Turnstile>asm clauses S
      \<Longrightarrow> conflicting S = C_True
      \<Longrightarrow> T \<sim> restart_state S
      \<Longrightarrow> P S T" and
    decideH: "\<And>L T. conflicting S = C_True \<Longrightarrow>  undefined_lit (trail S) L
      \<Longrightarrow> atm_of L \<in> atms_of_mu (init_clss S)
      \<Longrightarrow> T \<sim> cons_trail (Marked L (backtrack_lvl S +1)) (incr_lvl S)
      \<Longrightarrow> P S T" and
    skipH: "\<And>L C' M D T. trail S = Propagated L C' # M
      \<Longrightarrow> conflicting S = C_Clause D \<Longrightarrow> -L \<notin># D \<Longrightarrow> D \<noteq> {#}
      \<Longrightarrow> T \<sim> tl_trail S
      \<Longrightarrow> P S T" and
    resolveH: "\<And>L C M D T.
      trail S = Propagated L ( (C + {#L#})) # M
      \<Longrightarrow> conflicting S = C_Clause (D + {#-L#})
      \<Longrightarrow> get_maximum_level D (Propagated L ( (C + {#L#})) # M) = backtrack_lvl S
      \<Longrightarrow> T \<sim> (update_conflicting (C_Clause (D #\<union> C)) (tl_trail S))
      \<Longrightarrow> P S T" and
    backtrackH: "\<And>K i M1 M2 L D T.
      (Marked K (Suc i) # M1, M2) \<in> set (get_all_marked_decomposition (trail S))
      \<Longrightarrow> get_level L (trail S) = backtrack_lvl S
      \<Longrightarrow> conflicting S = C_Clause (D + {#L#})
      \<Longrightarrow> get_maximum_level (D+{#L#}) (trail S) = get_level L (trail S)
      \<Longrightarrow> get_maximum_level D (trail S) \<equiv> i
      \<Longrightarrow> T \<sim> cons_trail (Propagated L (D+{#L#}))
                (reduce_trail_to M1
                  (add_learned_cls (D + {#L#})
                    (update_backtrack_lvl i
                      (update_conflicting C_True S))))
      \<Longrightarrow> P S T"
  shows "P S S'"
  using cdcl\<^sub>W
proof (induct S S' rule: cdcl\<^sub>W_all_rules_induct)
  case (propagate S')
  then show ?case by (elim propagateE) (frule propagateH; simp)
next
  case (conflict S')
  then show ?case by (elim conflictE) (frule conflictH; simp)
next
  case (restart S')
  then show ?case by (elim restartE) (frule restartH; simp)
next
  case (decide T)
  then show ?case by (elim decideE) (frule decideH; simp)
next
  case (backtrack S')
  then show ?case by (elim backtrackE) (frule backtrackH; simp del: state_simp add: state_eq_def)
next
  case (forget S')
  then show ?case using forgetH by auto
next
  case (skip S')
  then show ?case using skipH by auto
next
  case (resolve S')
  then show ?case by (elim resolveE) (frule resolveH; simp)
qed

lemma cdcl\<^sub>W_o_induct[consumes 1, case_names decide skip resolve backtrack]:
  fixes S  :: "'st"
  assumes cdcl\<^sub>W: "cdcl\<^sub>W_o S T" and
    decideH: "\<And>L T. conflicting S = C_True \<Longrightarrow> undefined_lit (trail S) L
      \<Longrightarrow> atm_of L \<in> atms_of_mu (init_clss S)
      \<Longrightarrow> T \<sim> cons_trail (Marked L (backtrack_lvl S +1)) (incr_lvl S)
      \<Longrightarrow> P S T" and
    skipH: "\<And>L C' M D T. trail S = Propagated L C' # M
      \<Longrightarrow> conflicting S = C_Clause D \<Longrightarrow> -L \<notin># D \<Longrightarrow> D \<noteq> {#}
      \<Longrightarrow> T \<sim> tl_trail S
      \<Longrightarrow> P S T" and
    resolveH: "\<And>L C M D T.
      trail S = Propagated L ( (C + {#L#})) # M
      \<Longrightarrow> conflicting S = C_Clause (D + {#-L#})
      \<Longrightarrow> get_maximum_level D (Propagated L (C + {#L#}) # M) = backtrack_lvl S
      \<Longrightarrow> T \<sim> update_conflicting (C_Clause (D #\<union> C)) (tl_trail S)
      \<Longrightarrow> P S T" and
    backtrackH: "\<And>K i M1 M2 L D T.
      (Marked K (Suc i) # M1, M2) \<in> set (get_all_marked_decomposition (trail S))
      \<Longrightarrow> get_level L (trail S) = backtrack_lvl S
      \<Longrightarrow> conflicting S = C_Clause (D + {#L#})
      \<Longrightarrow> get_level L (trail S) = get_maximum_level (D+{#L#}) (trail S)
      \<Longrightarrow> get_maximum_level D (trail S) \<equiv> i
      \<Longrightarrow> T \<sim> cons_trail (Propagated L (D+{#L#}))
                (reduce_trail_to M1
                  (add_learned_cls (D + {#L#})
                    (update_backtrack_lvl i
                      (update_conflicting C_True S))))
      \<Longrightarrow> P S T"
  shows "P S T"
  using cdcl\<^sub>W apply (induct T rule: cdcl\<^sub>W_o.induct)
   using assms(2) apply auto[1]
  apply (elim cdcl\<^sub>W_bjE skipE resolveE backtrackE)
    apply (frule skipH; simp)
   apply (frule resolveH; simp)
  apply (frule backtrackH; simp_all del: state_simp add: state_eq_def)
  done

thm  cdcl\<^sub>W_o.induct
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

subsection \<open>Invariants\<close>
subsubsection \<open>Properties of the trail\<close>
text \<open>We here establish that:
  * the marks are exactly 1..k where k is the level
  * the consistency of the trail
  * the fact that there is no duplicate in the trail.\<close>
lemma backtrack_lit_skiped:
  assumes L: "get_level L (trail S) = backtrack_lvl S"
  and M1: "(Marked K (i + 1) # M1, M2) \<in> set (get_all_marked_decomposition (trail S))"
  and no_dup: "no_dup (trail S)"
  and bt_l: "backtrack_lvl S = length (get_all_levels_of_marked (trail S))"
  and order: "get_all_levels_of_marked (trail S)
    = rev ([1..<(1+length (get_all_levels_of_marked (trail S)))])"
  shows "atm_of L \<notin> atm_of ` lits_of M1"
proof
  let ?M = "trail S"
  assume L_in_M1: "atm_of L \<in> atm_of ` lits_of M1"
  obtain c where Mc: "trail S = c @ M2 @ Marked K (i + 1) # M1" using M1 by blast
  have "atm_of L \<notin> atm_of ` lits_of c"
    using L_in_M1 no_dup mk_disjoint_insert unfolding Mc lits_of_def by force
  have g_M_eq_g_M1: "get_level L ?M = get_level L M1"
    using L_in_M1 unfolding Mc by auto
  have g: "get_all_levels_of_marked M1 = rev [1..<Suc i]"
    using order unfolding Mc
    by (auto simp del: upt_simps dest!: append_cons_eq_upt_length_i
             simp add: rev_swap[symmetric])
  then have "Max (set (0 # get_all_levels_of_marked (rev M1))) < Suc i" by auto
  then have "get_level L M1 < Suc i"
    using get_rev_level_less_max_get_all_levels_of_marked[of L 0 "rev M1"] by linarith
  moreover have "Suc i \<le> backtrack_lvl S" using bt_l by (simp add: Mc g)
  ultimately show False using L g_M_eq_g_M1 by auto
qed

lemma cdcl\<^sub>W_distinctinv_1:
  assumes
    "cdcl\<^sub>W S S'" and
    "no_dup (trail S)" and
    "backtrack_lvl S = length (get_all_levels_of_marked (trail S))" and
    "get_all_levels_of_marked (trail S) = rev [1..<1+length (get_all_levels_of_marked (trail S))]"
  shows "no_dup (trail S')"
  using assms
proof (induct rule: cdcl\<^sub>W_all_induct)
  case (backtrack K i M1 M2 L D T) note decomp = this(1) and L = this(2) and T = this(6) and
    n_d = this(7)
  obtain c where Mc: "trail S = c @ M2 @ Marked K (i + 1) # M1"
    using decomp by auto
  have "no_dup (M2 @ Marked K (i + 1) # M1)"
    using Mc n_d by fastforce
  moreover have "atm_of L \<notin> (\<lambda>l. atm_of (lit_of l)) ` set M1"
    using backtrack_lit_skiped[of L S K i M1 M2] L decomp backtrack.prems
    by (fastforce simp add: lits_of_def)
  moreover then have "undefined_lit M1 L"
     by (simp add: defined_lit_map)
  ultimately show ?case using decomp T by simp
qed (auto simp add: defined_lit_map)

lemma cdcl\<^sub>W_consistent_inv_2:
  assumes
    "cdcl\<^sub>W S S'" and
    "no_dup (trail S)" and
    "backtrack_lvl S = length (get_all_levels_of_marked (trail S))" and
    "get_all_levels_of_marked (trail S) = rev [1..<1+length (get_all_levels_of_marked (trail S))]"
  shows "consistent_interp (lits_of (trail S'))"
  using cdcl\<^sub>W_distinctinv_1[OF assms] distinctconsistent_interp by fast

lemma cdcl\<^sub>W_o_bt:
  assumes
    "cdcl\<^sub>W_o S S'" and
    "backtrack_lvl S = length (get_all_levels_of_marked (trail S))" and
    "get_all_levels_of_marked (trail S) =
      rev ([1..<(1+length (get_all_levels_of_marked (trail S)))])" and
    "no_dup (trail S)"
  shows "backtrack_lvl S' = length (get_all_levels_of_marked (trail S'))"
  using assms
proof (induct rule: cdcl\<^sub>W_o_induct)
  case (backtrack K i M1 M2 L D T) note decomp = this(1) and T = this(6) and level = this(8)
  have [simp]: "trail (reduce_trail_to M1 S) = M1"
    using decomp by auto
  obtain c where M: "trail S = c @ M2 @ Marked K (i + 1) # M1" using decomp by auto
  have "rev (get_all_levels_of_marked (trail S))
    = [1..<1+ (length (get_all_levels_of_marked (trail S)))]"
    using level by (auto simp: rev_swap[symmetric])
  moreover have "atm_of L \<notin> (\<lambda>l. atm_of (lit_of l)) ` set M1"
    using backtrack_lit_skiped[of L S K i M1 M2] backtrack(2,7,8,9) decomp
    by (fastforce simp add: lits_of_def)
  moreover then have "undefined_lit M1 L"
     by (simp add: defined_lit_map)
  ultimately show ?case
    using T unfolding M by (auto dest!: append_cons_eq_upt_length simp del: upt_simps)
qed (auto simp add: defined_lit_map)

lemma cdcl\<^sub>W_rf_bt:
  assumes "cdcl\<^sub>W_rf S S'"
  and "backtrack_lvl S = length (get_all_levels_of_marked (trail S))"
  and "get_all_levels_of_marked (trail S) = rev [1..<(1+length (get_all_levels_of_marked (trail S)))]"
  shows "backtrack_lvl S' = length (get_all_levels_of_marked (trail S'))"
  using assms by (induct rule: cdcl\<^sub>W_rf.induct) auto

lemma cdcl\<^sub>W_bt:
  assumes
    "cdcl\<^sub>W S S'" and
    "backtrack_lvl S = length (get_all_levels_of_marked (trail S))" and
    "get_all_levels_of_marked (trail S)
    = rev ([1..<(1+length (get_all_levels_of_marked (trail S)))])" and
    "no_dup (trail S)"
  shows "backtrack_lvl S' = length (get_all_levels_of_marked (trail S'))"
  using assms by (induct rule: cdcl\<^sub>W.induct) (auto simp add: cdcl\<^sub>W_o_bt cdcl\<^sub>W_rf_bt)

lemma cdcl\<^sub>W_bt_level':
  assumes
    "cdcl\<^sub>W S S'" and
    "backtrack_lvl S = length (get_all_levels_of_marked (trail S))" and
    "get_all_levels_of_marked (trail S)
      = rev ([1..<(1+length (get_all_levels_of_marked (trail S)))])" and
    "no_dup (trail S)"
  shows "get_all_levels_of_marked (trail S')
    = rev ([1..<(1+length (get_all_levels_of_marked (trail S')))])"
  using assms
proof (induct rule: cdcl\<^sub>W_all_induct)
  case (decide L T) note undef = this(2) and T = this(4)
  let ?k = "backtrack_lvl S"
  let ?M = "trail S"
  let ?M' = "Marked L (?k + 1) # trail S"
  have H: "get_all_levels_of_marked ?M = rev [Suc 0..<1+length (get_all_levels_of_marked ?M)]"
    using decide.prems by simp
  have k: "?k = length (get_all_levels_of_marked ?M)"
    using decide.prems by auto
  have "get_all_levels_of_marked ?M' = Suc ?k # get_all_levels_of_marked ?M" by simp
  then have "get_all_levels_of_marked ?M' = Suc ?k #
      rev [Suc 0..<1+length (get_all_levels_of_marked ?M)]"
    using H by auto
  moreover have "\<dots> = rev [Suc 0..< Suc (1+length (get_all_levels_of_marked ?M))]"
    unfolding k by simp
  finally show ?case using T undef by (auto simp add: defined_lit_map)
next
  case (backtrack K i M1 M2 L D T) note decomp = this(1) and confli = this(2) and T =this(6) and
    all_marked = this(8) and bt_lvl = this(7)
  have "atm_of L \<notin> (\<lambda>l. atm_of (lit_of l)) ` set M1"
    using backtrack_lit_skiped[of L S K i M1 M2] backtrack(2,7,8,9) decomp
    by (fastforce simp add: lits_of_def)
  moreover then have "undefined_lit M1 L"
     by (simp add: defined_lit_map)
  then have [simp]: "trail T = Propagated L (D + {#L#}) # M1"
    using T decomp by auto
  obtain c where M: "trail S = c @ M2 @ Marked K (i + 1) # M1" using decomp by auto
  have "get_all_levels_of_marked (rev (trail S))
    = [Suc 0..<2+length (get_all_levels_of_marked c) + (length (get_all_levels_of_marked M2)
                + length (get_all_levels_of_marked M1))]"
    using all_marked bt_lvl unfolding M by (auto simp add: rev_swap[symmetric] simp del: upt_simps)
  then show ?case
    using T by (auto simp add: rev_swap M dest!: append_cons_eq_upt(1) simp del: upt_simps)
qed auto

text \<open>We write @{term "1+length (get_all_levels_of_marked (trail S))"} instead of
  @{term "backtrack_lvl S"} to avoid non termination of rewriting.\<close>
definition "cdcl\<^sub>W_M_level_inv (S:: 'st) \<longleftrightarrow>
  consistent_interp (lits_of (trail S))
  \<and> no_dup (trail S)
  \<and> backtrack_lvl S = length (get_all_levels_of_marked (trail S))
  \<and> get_all_levels_of_marked (trail S)
      = rev ([1..<1+length (get_all_levels_of_marked (trail S))])"

lemma cdcl\<^sub>W_M_level_inv_decomp[dest]:
  assumes "cdcl\<^sub>W_M_level_inv S"
  shows "consistent_interp (lits_of (trail S))"
  and "no_dup (trail S)"
  and "length (get_all_levels_of_marked (trail S)) = backtrack_lvl S"
  and "get_all_levels_of_marked (trail S) = rev ([Suc 0..< Suc 0+backtrack_lvl S])"
  using assms unfolding cdcl\<^sub>W_M_level_inv_def by fastforce+

lemma cdcl\<^sub>W_consistent_inv:
  fixes S S' :: 'st
  assumes
    "cdcl\<^sub>W S S'" and
    "cdcl\<^sub>W_M_level_inv S"
  shows "cdcl\<^sub>W_M_level_inv S'"
  using assms cdcl\<^sub>W_consistent_inv_2 cdcl\<^sub>W_distinctinv_1 cdcl\<^sub>W_bt cdcl\<^sub>W_bt_level'
  unfolding cdcl\<^sub>W_M_level_inv_def by blast+

lemma rtranclp_cdcl\<^sub>W_consistent_inv:
  assumes "cdcl\<^sub>W\<^sup>*\<^sup>* S S'"
  and "cdcl\<^sub>W_M_level_inv S"
  shows "cdcl\<^sub>W_M_level_inv S'"
  using assms by (induct rule: rtranclp_induct)
  (auto intro: cdcl\<^sub>W_consistent_inv)

lemma tranclp_cdcl\<^sub>W_consistent_inv:
  assumes "cdcl\<^sub>W\<^sup>+\<^sup>+ S S'"
  and "cdcl\<^sub>W_M_level_inv S"
  shows "cdcl\<^sub>W_M_level_inv S'"
  using assms by (induct rule: tranclp_induct)
  (auto intro: cdcl\<^sub>W_consistent_inv)

lemma cdcl\<^sub>W_M_level_inv_S0_cdcl\<^sub>W[simp]:
  "cdcl\<^sub>W_M_level_inv (init_state N)"
  unfolding cdcl\<^sub>W_M_level_inv_def by auto

lemma cdcl\<^sub>W_M_level_inv_get_level_le_backtrack_lvl:
  assumes inv: "cdcl\<^sub>W_M_level_inv S"
  shows "get_level L (trail S) \<le> backtrack_lvl S"
proof -
  have "get_all_levels_of_marked (trail S) = rev [1..<1 + backtrack_lvl S]"
    using inv unfolding cdcl\<^sub>W_M_level_inv_def by auto
  then show ?thesis
    using get_rev_level_less_max_get_all_levels_of_marked[of L 0 "rev (trail S)"]
    by (auto simp: Max_n_upt)
qed

lemma backtrack_ex_decomp:
  assumes M_l: "cdcl\<^sub>W_M_level_inv S"
  and i_S: "i < backtrack_lvl S"
  shows "\<exists>K M1 M2. (Marked K (i + 1) # M1, M2) \<in> set (get_all_marked_decomposition (trail S))"
proof -
  let ?M = "trail S"
  have
    g: "get_all_levels_of_marked (trail S) = rev [Suc 0..<Suc (backtrack_lvl S)]"
    using M_l unfolding cdcl\<^sub>W_M_level_inv_def by simp_all
  then have "i+1 \<in> set (get_all_levels_of_marked (trail S))"
    using i_S by auto

  then obtain c K c' where tr_S: "trail S = c @ Marked K (i + 1) # c'"
    using in_get_all_levels_of_marked_iff_decomp[of "i+1" "trail S"] by auto

  obtain M1 M2 where "(Marked K (i + 1) # M1, M2) \<in> set (get_all_marked_decomposition (trail S))"
    unfolding tr_S apply (induct c rule: marked_lit_list_induct)
      apply auto[2]
    apply (case_tac "hd (get_all_marked_decomposition (xs @ Marked K (Suc i) # c'))")
    apply (case_tac "get_all_marked_decomposition (xs @ Marked K (Suc i) # c')")
    by auto
  then show ?thesis by blast
qed

subsubsection \<open>Better-Suited Induction Principle\<close>

text \<open>Ew generalise the induction principle defined previously: the induction case for
  @{term backtrack} now includes the assumption that @{term "undefined_lit M1 L"}. This helps
  the simplifier and thus the automation.\<close>
lemma backtrack_induction_lev[consumes 1, case_names M_devel_inv backtrack]:
  assumes
    bt: "backtrack S T" and
    inv: "cdcl\<^sub>W_M_level_inv S" and
    backtrackH: "\<And>K i M1 M2 L D T.
      (Marked K (Suc i) # M1, M2) \<in> set (get_all_marked_decomposition (trail S))
      \<Longrightarrow> get_level L (trail S) = backtrack_lvl S
      \<Longrightarrow> conflicting S = C_Clause (D + {#L#})
      \<Longrightarrow> get_level L (trail S) = get_maximum_level (D+{#L#}) (trail S)
      \<Longrightarrow> get_maximum_level D (trail S) \<equiv> i
      \<Longrightarrow> undefined_lit M1 L
      \<Longrightarrow> T \<sim> cons_trail (Propagated L (D+{#L#}))
                (reduce_trail_to M1
                  (add_learned_cls (D + {#L#})
                    (update_backtrack_lvl i
                      (update_conflicting C_True S))))
      \<Longrightarrow> P S T"
  shows "P S T"
proof -
  obtain K i M1 M2 L D where
    decomp: "(Marked K (Suc i) # M1, M2) \<in> set (get_all_marked_decomposition (trail S))" and
    L: "get_level L (trail S) = backtrack_lvl S" and
    confl: "conflicting S = C_Clause (D + {#L#})" and
    lev_L: "get_level L (trail S) = get_maximum_level (D+{#L#}) (trail S)" and
    lev_D: "get_maximum_level D (trail S) \<equiv> i" and
    T: "T \<sim> cons_trail (Propagated L (D+{#L#}))
                (reduce_trail_to M1
                  (add_learned_cls (D + {#L#})
                    (update_backtrack_lvl i
                      (update_conflicting C_True S))))"
    using bt by (elim backtrackE)  metis

  have "atm_of L \<notin> (\<lambda>l. atm_of (lit_of l)) ` set M1"
    using backtrack_lit_skiped[of L S K i M1 M2] L decomp bt confl lev_L lev_D inv
    unfolding cdcl\<^sub>W_M_level_inv_def
    by (fastforce simp add: lits_of_def)
  then have "undefined_lit M1 L"
    by (auto simp: defined_lit_map)
  then show ?thesis
    using backtrackH[OF decomp L confl lev_L lev_D _ T] by simp
qed

lemmas backtrack_induction_lev2 = backtrack_induction_lev[consumes 2, case_names backtrack]

lemma cdcl\<^sub>W_all_induct_lev_full:
  fixes S  :: "'st"
  assumes
    cdcl\<^sub>W: "cdcl\<^sub>W S S'" and
    inv: "cdcl\<^sub>W_M_level_inv S" and
    propagateH: "\<And>C L T. C + {#L#} \<in># clauses S \<Longrightarrow> trail S \<Turnstile>as CNot C
      \<Longrightarrow> undefined_lit (trail S) L \<Longrightarrow> conflicting S = C_True
      \<Longrightarrow> T \<sim> cons_trail (Propagated L (C + {#L#})) S
      \<Longrightarrow> P S T" and
    conflictH: "\<And>D T. D \<in># clauses S \<Longrightarrow> conflicting S = C_True \<Longrightarrow> trail S \<Turnstile>as CNot D
      \<Longrightarrow> T \<sim> update_conflicting (C_Clause D) S
      \<Longrightarrow> P S T" and
    forgetH: "\<And>C T. \<not>trail S \<Turnstile>asm clauses S
      \<Longrightarrow> C \<notin> set (get_all_mark_of_propagated (trail S))
      \<Longrightarrow> C \<notin># init_clss S
      \<Longrightarrow> C \<in># learned_clss S
      \<Longrightarrow> conflicting S = C_True
      \<Longrightarrow> T \<sim> remove_cls C S
      \<Longrightarrow> P S T" and
    restartH: "\<And>T. \<not>trail S \<Turnstile>asm clauses S
      \<Longrightarrow> conflicting S = C_True
      \<Longrightarrow> T \<sim> restart_state S
      \<Longrightarrow> P S T" and
    decideH: "\<And>L T. conflicting S = C_True \<Longrightarrow>  undefined_lit (trail S) L
      \<Longrightarrow> atm_of L \<in> atms_of_mu (init_clss S)
      \<Longrightarrow> T \<sim> cons_trail (Marked L (backtrack_lvl S +1)) (incr_lvl S)
      \<Longrightarrow> P S T" and
    skipH: "\<And>L C' M D T. trail S = Propagated L C' # M
      \<Longrightarrow> conflicting S = C_Clause D \<Longrightarrow> -L \<notin># D \<Longrightarrow> D \<noteq> {#}
      \<Longrightarrow> T \<sim> tl_trail S
      \<Longrightarrow> P S T" and
    resolveH: "\<And>L C M D T.
      trail S = Propagated L ( (C + {#L#})) # M
      \<Longrightarrow> conflicting S = C_Clause (D + {#-L#})
      \<Longrightarrow> get_maximum_level D (Propagated L ( (C + {#L#})) # M) = backtrack_lvl S
      \<Longrightarrow> T \<sim> (update_conflicting (C_Clause (D #\<union> C)) (tl_trail S))
      \<Longrightarrow> P S T" and
    backtrackH: "\<And>K i M1 M2 L D T.
      (Marked K (Suc i) # M1, M2) \<in> set (get_all_marked_decomposition (trail S))
      \<Longrightarrow> get_level L (trail S) = backtrack_lvl S
      \<Longrightarrow> conflicting S = C_Clause (D + {#L#})
      \<Longrightarrow> get_maximum_level (D+{#L#}) (trail S) = get_level L (trail S)
      \<Longrightarrow> get_maximum_level D (trail S) \<equiv> i
      \<Longrightarrow> undefined_lit M1 L
      \<Longrightarrow> T \<sim> cons_trail (Propagated L (D+{#L#}))
                (reduce_trail_to M1
                  (add_learned_cls (D + {#L#})
                    (update_backtrack_lvl i
                      (update_conflicting C_True S))))
      \<Longrightarrow> P S T"
  shows "P S S'"
  using cdcl\<^sub>W
proof (induct S' rule: cdcl\<^sub>W_all_rules_induct)
  case (propagate S')
  then show ?case by (elim propagateE) (frule propagateH; simp)
next
  case (conflict S')
  then show ?case by (elim conflictE) (frule conflictH; simp)
next
  case (restart S')
  then show ?case by (elim restartE) (frule restartH; simp)
next
  case (decide T)
  then show ?case by (elim decideE) (frule decideH; simp)
next
  case (backtrack S')
  then show ?case
    apply (induction rule: backtrack_induction_lev)
     apply (rule inv)
    by (rule backtrackH;
      fastforce simp del: state_simp simp add: state_eq_def dest!: HOL.meta_eq_to_obj_eq)
next
  case (forget S')
  then show ?case using forgetH by auto
next
  case (skip S')
  then show ?case using skipH by auto
next
  case (resolve S')
  then show ?case by (elim resolveE) (frule resolveH; simp)
qed

lemmas cdcl\<^sub>W_all_induct_lev2 = cdcl\<^sub>W_all_induct_lev_full[consumes 2, case_names propagate conflict
  forget restart decide skip resolve backtrack]

lemmas cdcl\<^sub>W_all_induct_lev = cdcl\<^sub>W_all_induct_lev_full[consumes 1, case_names lev_inv propagate
  conflict forget restart decide skip resolve backtrack]

thm cdcl\<^sub>W_o_induct
lemma cdcl\<^sub>W_o_induct_lev[consumes 1, case_names M_lev decide skip resolve backtrack]:
  fixes S  :: "'st"
  assumes
    cdcl\<^sub>W: "cdcl\<^sub>W_o S T" and
    inv: "cdcl\<^sub>W_M_level_inv S" and
    decideH: "\<And>L T. conflicting S = C_True \<Longrightarrow>  undefined_lit (trail S) L
      \<Longrightarrow> atm_of L \<in> atms_of_mu (init_clss S)
      \<Longrightarrow> T \<sim> cons_trail (Marked L (backtrack_lvl S +1)) (incr_lvl S)
      \<Longrightarrow> P S T" and
    skipH: "\<And>L C' M D T. trail S = Propagated L C' # M
      \<Longrightarrow> conflicting S = C_Clause D \<Longrightarrow> -L \<notin># D \<Longrightarrow> D \<noteq> {#}
      \<Longrightarrow> T \<sim> tl_trail S
      \<Longrightarrow> P S T" and
    resolveH: "\<And>L C M D T.
      trail S = Propagated L ( (C + {#L#})) # M
      \<Longrightarrow> conflicting S = C_Clause (D + {#-L#})
      \<Longrightarrow> get_maximum_level D (Propagated L (C + {#L#}) # M) = backtrack_lvl S
      \<Longrightarrow> T \<sim> update_conflicting (C_Clause (D #\<union> C)) (tl_trail S)
      \<Longrightarrow> P S T" and
    backtrackH: "\<And>K i M1 M2 L D T.
      (Marked K (Suc i) # M1, M2) \<in> set (get_all_marked_decomposition (trail S))
      \<Longrightarrow> get_level L (trail S) = backtrack_lvl S
      \<Longrightarrow> conflicting S = C_Clause (D + {#L#})
      \<Longrightarrow> get_level L (trail S) = get_maximum_level (D+{#L#}) (trail S)
      \<Longrightarrow> get_maximum_level D (trail S) \<equiv> i
      \<Longrightarrow> undefined_lit M1 L
      \<Longrightarrow> T \<sim> cons_trail (Propagated L (D+{#L#}))
                (reduce_trail_to M1
                  (add_learned_cls (D + {#L#})
                    (update_backtrack_lvl i
                      (update_conflicting C_True S))))
      \<Longrightarrow> P S T"
  shows "P S T"
  using cdcl\<^sub>W
proof (induct S T rule: cdcl\<^sub>W_o_all_rules_induct)
  case (decide T)
  then show ?case by (elim decideE) (frule decideH; simp)
next
  case (backtrack S')
  then show ?case
    using inv apply (induction rule: backtrack_induction_lev2)
    by (rule backtrackH)
      (fastforce simp del: state_simp simp add: state_eq_def dest!: HOL.meta_eq_to_obj_eq)+
next
  case (skip S')
  then show ?case using skipH by auto
next
  case (resolve S')
  then show ?case by (elim resolveE) (frule resolveH; simp)
qed

lemmas cdcl\<^sub>W_o_induct_lev2 = cdcl\<^sub>W_o_induct_lev[consumes 2, case_names decide skip resolve
  backtrack]

subsubsection \<open>Compatibility with @{term state_eq}\<close>
lemma propagate_state_eq_compatible:
  assumes
    "propagate S T" and
    "S \<sim> S'" and
    "T \<sim> T'"
  shows "propagate S' T'"
  using assms apply (elim propagateE)
  apply (rule propagate_rule)
  by (auto simp: state_eq_def clauses_def simp del: state_simp)

lemma conflict_state_eq_compatible:
  assumes
    "conflict S T" and
    "S \<sim> S'" and
    "T \<sim> T'"
  shows "conflict S' T'"
  using assms apply (elim conflictE)
  apply (rule conflict_rule)
  by (auto simp: state_eq_def clauses_def simp del: state_simp)

lemma backtrack_state_eq_compatible:
  assumes
    "backtrack S T" and
    "S \<sim> S'" and
    "T \<sim> T'" and
    inv: "cdcl\<^sub>W_M_level_inv S"
  shows "backtrack S' T'"
  using assms apply (induction rule: backtrack_induction_lev)
    using inv apply simp
  apply (rule backtrack_rule)
         apply auto[5]
  by (auto simp: state_eq_def clauses_def simp del: state_simp)

lemma decide_state_eq_compatible:
  assumes
    "decide S T" and
    "S \<sim> S'" and
    "T \<sim> T'"
  shows "decide S' T'"
  using assms apply (elim decideE)
  apply (rule decide_rule)
  by (auto simp: state_eq_def clauses_def simp del: state_simp)

lemma skip_state_eq_compatible:
  assumes
    "skip S T" and
    "S \<sim> S'" and
    "T \<sim> T'"
  shows "skip S' T'"
  using assms apply (elim skipE)
  apply (rule skip_rule)
  by (auto simp: state_eq_def clauses_def HOL.eq_sym_conv[of  "_ # _" "trail _"]
     simp del: state_simp dest: arg_cong[of "_ # trail _" "trail _" tl])

lemma resolve_state_eq_compatible:
  assumes
    "resolve S T" and
    "S \<sim> S'" and
    "T \<sim> T'"
  shows "resolve S' T'"
  using assms apply (elim resolveE)
  apply (rule resolve_rule)
  by (auto simp: state_eq_def clauses_def HOL.eq_sym_conv[of  "_ # _" "trail _"]
     simp del: state_simp dest: arg_cong[of "_ # trail _" "trail _" tl])

lemma forget_state_eq_compatible:
  assumes
    "forget S T" and
    "S \<sim> S'" and
    "T \<sim> T'"
  shows "forget S' T'"
  using assms apply (elim forgetE)
  apply (rule forget_rule)
  by (auto simp: state_eq_def clauses_def HOL.eq_sym_conv[of  "{#_#} + _" "_"]
     simp del: state_simp dest: arg_cong[of "_ # trail _" "trail _" tl])

lemma cdcl\<^sub>W_state_eq_compatible:
  assumes
    "cdcl\<^sub>W S T" and "\<not>restart S T" and
    "S \<sim> S'" and
    "T \<sim> T'" and
    inv: "cdcl\<^sub>W_M_level_inv S"
  shows "cdcl\<^sub>W S' T'"
  using assms by (meson assms backtrack_state_eq_compatible bj cdcl\<^sub>W.simps cdcl\<^sub>W_bj.simps
    cdcl\<^sub>W_o_rule_cases cdcl\<^sub>W_rf.cases cdcl\<^sub>W_rf.restart conflict_state_eq_compatible decide
    decide_state_eq_compatible forget forget_state_eq_compatible
    propagate_state_eq_compatible resolve_state_eq_compatible
    skip_state_eq_compatible)

subsubsection \<open>Conservation of some Properties\<close>
lemma level_of_marked_ge_1:
  assumes
    "cdcl\<^sub>W S S'" and
    inv: "cdcl\<^sub>W_M_level_inv S" and
    "\<forall>L l. Marked L l \<in> set (trail S) \<longrightarrow> l > 0"
  shows "\<forall>L l. Marked L l \<in> set (trail S') \<longrightarrow> l > 0"
  using assms apply (induct rule: cdcl\<^sub>W_all_induct_lev2)
  by (auto dest: union_in_get_all_marked_decomposition_is_subset)

lemma cdcl\<^sub>W_o_no_more_init_clss:
  assumes
    "cdcl\<^sub>W_o S S'" and
    inv: "cdcl\<^sub>W_M_level_inv S"
  shows "init_clss S = init_clss S'"
  using assms by (induct rule: cdcl\<^sub>W_o_induct_lev2) auto

lemma tranclp_cdcl\<^sub>W_o_no_more_init_clss:
  assumes
    "cdcl\<^sub>W_o\<^sup>+\<^sup>+ S S'" and
    inv: "cdcl\<^sub>W_M_level_inv S"
  shows "init_clss S = init_clss S'"
  using assms apply (induct rule: tranclp.induct)
  by (auto dest: cdcl\<^sub>W_o_no_more_init_clss
    dest!: tranclp_cdcl\<^sub>W_consistent_inv dest: tranclp_mono_explicit[of cdcl\<^sub>W_o _ _ cdcl\<^sub>W]
    simp: other)

  lemma rtranclp_cdcl\<^sub>W_o_no_more_init_clss:
  assumes
    "cdcl\<^sub>W_o\<^sup>*\<^sup>* S S'" and
    inv: "cdcl\<^sub>W_M_level_inv S"
  shows "init_clss S = init_clss S'"
  using assms unfolding rtranclp_unfold by (auto intro: tranclp_cdcl\<^sub>W_o_no_more_init_clss)

lemma cdcl\<^sub>W_init_clss:
  "cdcl\<^sub>W S T \<Longrightarrow> cdcl\<^sub>W_M_level_inv S \<Longrightarrow> init_clss S = init_clss T"
  by (induct rule: cdcl\<^sub>W_all_induct_lev2) auto

lemma rtranclp_cdcl\<^sub>W_init_clss:
  "cdcl\<^sub>W\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W_M_level_inv S \<Longrightarrow> init_clss S = init_clss T"
  by (induct rule: rtranclp_induct) (auto dest: cdcl\<^sub>W_init_clss rtranclp_cdcl\<^sub>W_consistent_inv)

lemma tranclp_cdcl\<^sub>W_init_clss:
  "cdcl\<^sub>W\<^sup>+\<^sup>+ S T \<Longrightarrow>  cdcl\<^sub>W_M_level_inv S \<Longrightarrow> init_clss S = init_clss T"
  using rtranclp_cdcl\<^sub>W_init_clss[of S T] unfolding rtranclp_unfold by auto

subsubsection \<open>Learned Clause\<close>
text \<open>This invariant shows that:
  \<^item> the learned clauses are entailed by the initial set of clauses.
  \<^item> the conflicting clause is entailed by the initial set of clauses.
  \<^item> the marks are entailed by the clauses. A more precise version would be to show that either
  these marked are learned or are in the set of clauses\<close>

definition "cdcl\<^sub>W_learned_clause (S:: 'st) \<longleftrightarrow>
  (init_clss S \<Turnstile>psm learned_clss S
  \<and> (\<forall>T. conflicting S = C_Clause T \<longrightarrow> init_clss S \<Turnstile>pm T)
  \<and> set (get_all_mark_of_propagated (trail S)) \<subseteq> set_mset (clauses S))"

(*propo 2.9.6.2*)
lemma cdcl\<^sub>W_learned_clause_S0_cdcl\<^sub>W[simp]:
   "cdcl\<^sub>W_learned_clause (init_state N)"
  unfolding cdcl\<^sub>W_learned_clause_def by auto

lemma cdcl\<^sub>W_learned_clss:
  assumes
    "cdcl\<^sub>W S S'" and
    learned: "cdcl\<^sub>W_learned_clause S" and
    lev_inv: "cdcl\<^sub>W_M_level_inv S"
  shows "cdcl\<^sub>W_learned_clause S'"
  using assms(1) lev_inv learned
proof (induct rule: cdcl\<^sub>W_all_induct_lev2)
  case (backtrack K i M1 M2 L D T) note decomp = this(1) and confl = this(3) and undef = this(6)
  and T =this(7)
  show ?case
    using decomp confl learned undef T lev_inv unfolding cdcl\<^sub>W_learned_clause_def
    by (auto dest!: get_all_marked_decomposition_exists_prepend
      simp: clauses_def dest: true_clss_clss_left_right)
next
  case (resolve L C M D) note trail = this(1) and confl = this(2) and lvl = this(3) and
    T =this(4)
  moreover
    have "init_clss S \<Turnstile>psm learned_clss S"
      using learned trail unfolding cdcl\<^sub>W_learned_clause_def clauses_def by auto
    then have "init_clss S \<Turnstile>pm C + {#L#}"
      using trail learned  unfolding cdcl\<^sub>W_learned_clause_def clauses_def
      by (auto dest: true_clss_clss_in_imp_true_clss_cls)
  ultimately show ?case
    using learned
    by (auto dest: mk_disjoint_insert true_clss_clss_left_right
      simp add: cdcl\<^sub>W_learned_clause_def clauses_def
      intro: true_clss_cls_union_mset_true_clss_cls_or_not_true_clss_cls_or)
next
  case (restart T)
  then show ?case
    using learned_clss_restart_state[of T]
    by (auto dest!: get_all_marked_decomposition_exists_prepend
      simp: clauses_def state_eq_def cdcl\<^sub>W_learned_clause_def
       simp del: state_simp
     dest: true_clss_clssm_subsetE)
next
  case propagate
  then show ?case using learned by (auto simp: cdcl\<^sub>W_learned_clause_def clauses_def)
next
  case conflict
  then show ?case  using learned
    by (auto simp: cdcl\<^sub>W_learned_clause_def clauses_def true_clss_clss_in_imp_true_clss_cls)
next
  case forget
  then show ?case
    using learned by (auto simp: cdcl\<^sub>W_learned_clause_def clauses_def split: split_if_asm)
qed (auto simp: cdcl\<^sub>W_learned_clause_def clauses_def)

lemma rtranclp_cdcl\<^sub>W_learned_clss:
  assumes
    "cdcl\<^sub>W\<^sup>*\<^sup>* S S'" and
    "cdcl\<^sub>W_M_level_inv S"
    "cdcl\<^sub>W_learned_clause S"
  shows "cdcl\<^sub>W_learned_clause S'"
  using assms by induction (auto dest: cdcl\<^sub>W_learned_clss intro: rtranclp_cdcl\<^sub>W_consistent_inv)

subsubsection \<open>No alien atom in the state\<close>
text \<open>This invariant means that all the literals are in the set of clauses.\<close>
definition "no_strange_atm S' \<longleftrightarrow> (
    (\<forall>T. conflicting S' = C_Clause T \<longrightarrow> atms_of T \<subseteq> atms_of_mu (init_clss S'))
  \<and> (\<forall>L mark. Propagated L mark \<in> set (trail S')
      \<longrightarrow> atms_of ( mark) \<subseteq> atms_of_mu (init_clss S'))
  \<and> atms_of_mu (learned_clss S') \<subseteq> atms_of_mu (init_clss S')
  \<and> atm_of ` (lits_of (trail S')) \<subseteq> atms_of_mu (init_clss S'))"

lemma no_strange_atm_decomp:
  assumes "no_strange_atm S"
  shows "conflicting S = C_Clause T \<Longrightarrow> atms_of T \<subseteq> atms_of_mu (init_clss S)"
  and "(\<forall>L mark. Propagated L mark \<in> set (trail S)
    \<longrightarrow> atms_of ( mark) \<subseteq> atms_of_mu (init_clss S))"
  and "atms_of_mu (learned_clss S) \<subseteq> atms_of_mu (init_clss S)"
  and "atm_of ` (lits_of (trail S)) \<subseteq> atms_of_mu (init_clss S)"
  using assms unfolding no_strange_atm_def by blast+

lemma no_strange_atm_S0 [simp]: "no_strange_atm (init_state N)"
  unfolding no_strange_atm_def by auto

lemma cdcl\<^sub>W_no_strange_atm_explicit:
  assumes
    "cdcl\<^sub>W S S'" and
    "cdcl\<^sub>W_M_level_inv S" and
    conf: "\<forall>T. conflicting S = C_Clause T \<longrightarrow> atms_of T \<subseteq> atms_of_mu (init_clss S)" and
    marked: "\<forall>L mark. Propagated L mark \<in> set (trail S)
      \<longrightarrow> atms_of mark \<subseteq> atms_of_mu (init_clss S)" and
    learned: "atms_of_mu (learned_clss S) \<subseteq> atms_of_mu (init_clss S)" and
    trail: "atm_of ` (lits_of (trail S)) \<subseteq> atms_of_mu (init_clss S)"
  shows "(\<forall>T. conflicting S' = C_Clause T \<longrightarrow> atms_of T \<subseteq> atms_of_mu (init_clss S')) \<and>
   (\<forall>L mark. Propagated L mark \<in> set (trail S')
     \<longrightarrow> atms_of ( mark) \<subseteq> atms_of_mu (init_clss S')) \<and>
   atms_of_mu (learned_clss S') \<subseteq> atms_of_mu (init_clss S') \<and>
   atm_of ` (lits_of (trail S')) \<subseteq> atms_of_mu (init_clss S')" (is "?C S' \<and> ?M S' \<and> ?U S' \<and> ?V S'")
  using assms(1,2)
proof (induct rule: cdcl\<^sub>W_all_induct_lev2)
  case (propagate C L T) note C_L = this(1) and undef = this(3) and confl = this(4) and T =this(5)
  have "?C (cons_trail (Propagated L (C + {#L#})) S)" using confl undef by auto
  moreover
    have "atms_of (C + {#L#}) \<subseteq> atms_of_mu (init_clss S)"
      by (metis (no_types) atms_of_atms_of_m_mono atms_of_m_union clauses_def mem_set_mset_iff
        C_L learned set_mset_union sup.orderE)
    then have "?M (cons_trail (Propagated L (C + {#L#})) S)" using undef
      by (simp add: marked)
  moreover have "?U  (cons_trail (Propagated L (C + {#L#})) S)"
    using learned undef by auto
  moreover have "?V (cons_trail (Propagated L (C + {#L#})) S)"
    using C_L learned trail undef unfolding clauses_def
    by (auto simp: in_plus_implies_atm_of_on_atms_of_m)
  ultimately show ?case using T by auto
next
  case (decide L)
  then show ?case using learned marked conf trail unfolding clauses_def by auto
next
  case (skip L C M D)
  then show ?case using learned marked conf trail by auto
next
  case (conflict D T) note T =this(4)
  have D: "atm_of ` set_mset D \<subseteq> \<Union>(atms_of ` (set_mset (clauses S)))"
    using \<open>D \<in># clauses S\<close> by (auto simp add: atms_of_def atms_of_m_def)
  moreover {
    fix xa :: "'v literal"
    assume a1: "atm_of ` set_mset D \<subseteq> (\<Union>x\<in>set_mset (init_clss S). atms_of x)
      \<union> (\<Union>x\<in>set_mset (learned_clss S). atms_of x)"
    assume a2: "(\<Union>x\<in>set_mset (learned_clss S). atms_of x) \<subseteq> (\<Union>x\<in>set_mset (init_clss S). atms_of x)"
    assume "xa \<in># D"
    then have "atm_of xa \<in> UNION (set_mset (init_clss S)) atms_of"
      using a2 a1 by (metis (no_types) Un_iff atm_of_lit_in_atms_of atms_of_def subset_Un_eq)
    then have "\<exists>m\<in>set_mset (init_clss S). atm_of xa \<in> atms_of m"
      by blast
    } note H = this
  ultimately show ?case using conflict.prems T learned marked conf trail
    unfolding atms_of_def atms_of_m_def clauses_def
     by (auto simp add: H )
next
  case (restart T)
  then show ?case using  learned marked conf trail by auto
next
  case (forget C T) note C = this(3) and C_le = this(4) and confl = this(5) and
    T = this(6)
  have H: "\<And>L mark. Propagated L mark \<in> set (trail S) \<Longrightarrow> atms_of mark \<subseteq> atms_of_mu (init_clss S)"
    using marked by simp
  show ?case unfolding clauses_def apply standard
    using conf T trail C unfolding clauses_def apply (auto dest!: H)[]
    apply standard
     using T trail C apply (auto dest!: H)[]
    apply standard
      using T learned C C_le atms_of_m_remove_subset[of "set_mset (learned_clss S)"] apply (auto)[]
    using T trail C apply (auto simp: clauses_def lits_of_def)[]
  done
next
  case (backtrack K i M1 M2 L D T) note decomp = this(1) and confl = this(3) and undef= this(6)
    and T =this(7)
  have "?C T"
    using conf T decomp undef by simp
  moreover have "set M1 \<subseteq> set (trail S)"
    using backtrack.hyps(1) by auto
  then have M: "?M T"
    using marked conf undef confl T decomp by (auto simp add: image_subset_iff clauses_def)
  moreover have "?U T"
    using learned decomp conf confl T undef unfolding clauses_def by auto
  moreover have "?V T"
    using M conf confl trail T undef decomp by force
  ultimately show ?case by blast
next
  case (resolve L C M D T) note trail_S = this(1) and confl = this(2) and T = this(4)
  let ?T = "update_conflicting (C_Clause (remdups_mset (D + C))) (tl_trail S)"
  have "?C ?T"
    using confl trail_S conf marked by simp
  moreover have  "?M ?T"
    using confl trail_S conf marked by auto
  moreover have "?U ?T"
    using trail learned by auto
  moreover have "?V ?T"
    using confl trail_S trail by auto
  ultimately show ?case using T by auto
qed

lemma cdcl\<^sub>W_no_strange_atm_inv:
  assumes "cdcl\<^sub>W S S'" and "no_strange_atm S" and "cdcl\<^sub>W_M_level_inv S"
  shows "no_strange_atm S'"
  using cdcl\<^sub>W_no_strange_atm_explicit[OF assms(1)] assms(2,3) unfolding no_strange_atm_def by fast

lemma rtranclp_cdcl\<^sub>W_no_strange_atm_inv:
  assumes "cdcl\<^sub>W\<^sup>*\<^sup>* S S'" and "no_strange_atm S" and "cdcl\<^sub>W_M_level_inv S"
  shows "no_strange_atm S'"
  using assms by induction (auto intro: cdcl\<^sub>W_no_strange_atm_inv rtranclp_cdcl\<^sub>W_consistent_inv)

subsubsection \<open>No duplicates all around\<close>
text \<open>This invariant shows that there is no duplicate (no literal appearing twice in the formula).
  The last part could be proven using the previous invariant moreover.\<close>
definition "distinct_cdcl\<^sub>W_state (S::'st)
  \<longleftrightarrow> ((\<forall>T. conflicting S = C_Clause T \<longrightarrow> distinct_mset T)
    \<and> distinct_mset_mset (learned_clss S)
    \<and> distinct_mset_mset (init_clss S)
    \<and> (\<forall>L mark. (Propagated L mark \<in> set (trail S) \<longrightarrow> distinct_mset (mark))))"

lemma distinct_cdcl\<^sub>W_state_decomp:
  assumes "distinct_cdcl\<^sub>W_state (S::'st)"
  shows "\<forall>T. conflicting S = C_Clause T \<longrightarrow> distinct_mset T"
  and "distinct_mset_mset (learned_clss S)"
  and "distinct_mset_mset (init_clss S)"
  and "\<forall>L mark. (Propagated L mark \<in> set (trail S) \<longrightarrow> distinct_mset ( mark))"
  using assms unfolding distinct_cdcl\<^sub>W_state_def by blast+

lemma distinct_cdcl\<^sub>W_state_decomp_2:
  assumes "distinct_cdcl\<^sub>W_state (S::'st)"
  shows "conflicting S = C_Clause T \<Longrightarrow> distinct_mset T"
  using assms unfolding distinct_cdcl\<^sub>W_state_def by auto

lemma distinct_cdcl\<^sub>W_state_S0_cdcl\<^sub>W[simp]:
  "distinct_mset_mset N \<Longrightarrow>  distinct_cdcl\<^sub>W_state (init_state N)"
  unfolding distinct_cdcl\<^sub>W_state_def by auto

lemma distinct_cdcl\<^sub>W_state_inv:
  assumes
    "cdcl\<^sub>W S S'" and
    "cdcl\<^sub>W_M_level_inv S" and
    "distinct_cdcl\<^sub>W_state S"
  shows "distinct_cdcl\<^sub>W_state S'"
  using assms
proof (induct rule: cdcl\<^sub>W_all_induct_lev2)
  case (backtrack K i M1 M2 L D)
  then show ?case
    unfolding distinct_cdcl\<^sub>W_state_def by (fastforce dest: get_all_marked_decomposition_incl)
next
  case restart
  then show ?case unfolding distinct_cdcl\<^sub>W_state_def distinct_mset_set_def clauses_def
  using learned_clss_restart_state[of S] by auto
next
  case resolve
  then show ?case
    by (auto simp add: distinct_cdcl\<^sub>W_state_def distinct_mset_set_def clauses_def
      distinct_mset_single_add
      intro!: distinct_mset_union_mset)
qed (auto simp add: distinct_cdcl\<^sub>W_state_def distinct_mset_set_def clauses_def)

lemma rtanclp_distinct_cdcl\<^sub>W_state_inv:
  assumes
    "cdcl\<^sub>W\<^sup>*\<^sup>* S S'" and
    "cdcl\<^sub>W_M_level_inv S" and
    "distinct_cdcl\<^sub>W_state S"
  shows "distinct_cdcl\<^sub>W_state S'"
  using assms apply (induct rule: rtranclp.induct)
  using distinct_cdcl\<^sub>W_state_inv rtranclp_cdcl\<^sub>W_consistent_inv by blast+

subsubsection \<open>Conflicts and co\<close>
text \<open>This invariant shows that each mark contains a contradiction only related to the previously
  defined variable.\<close>
abbreviation every_mark_is_a_conflict :: "'st \<Rightarrow> bool" where
"every_mark_is_a_conflict S \<equiv>
 \<forall>L mark a b. a @ Propagated L mark # b = (trail S)
   \<longrightarrow> (b \<Turnstile>as CNot ( mark - {#L#}) \<and> L \<in>#  mark)"

definition "cdcl\<^sub>W_conflicting S \<equiv>
  (\<forall>T. conflicting S = C_Clause T \<longrightarrow> trail S \<Turnstile>as CNot T)
  \<and> every_mark_is_a_conflict S"

lemma backtrack_atms_of_D_in_M1:
  fixes M1 :: "('v, nat, 'v clause) marked_lits"
  assumes
    inv: "cdcl\<^sub>W_M_level_inv S" and
    undef: "undefined_lit M1 L" and
    i: "get_maximum_level D (trail S) = i" and
    decomp: "(Marked K (Suc i) # M1, M2)
       \<in> set (get_all_marked_decomposition (trail S))" and
    S_lvl: "backtrack_lvl S = get_maximum_level (D + {#L#}) (trail S)" and
    S_confl: "conflicting S = C_Clause (D + {#L#})" and
    undef: "undefined_lit M1 L" and
    T: "T \<sim> (cons_trail (Propagated L (D+{#L#}))
                  (reduce_trail_to M1
                      (add_learned_cls (D + {#L#})
                         (update_backtrack_lvl i
                            (update_conflicting C_True S)))))" and
    confl: "\<forall>T. conflicting S = C_Clause T \<longrightarrow> trail S \<Turnstile>as CNot T"
  shows "atms_of D \<subseteq> atm_of ` lits_of (tl (trail T))"
proof (rule ccontr)
  let ?k = "get_maximum_level (D + {#L#}) (trail S)"
  have "trail S \<Turnstile>as CNot D" using confl S_confl by auto
  then have vars_of_D: "atms_of D \<subseteq> atm_of ` lits_of (trail S)" unfolding atms_of_def
    by (meson image_subsetI mem_set_mset_iff true_annots_CNot_all_atms_defined)

  obtain M0 where M: "trail S = M0 @ M2 @ Marked K (Suc i) # M1"
    using decomp by auto

  have max: "get_maximum_level (D + {#L#}) (trail S)
    = length (get_all_levels_of_marked (M0 @ M2 @ Marked K (Suc i) # M1))"
    using inv unfolding cdcl\<^sub>W_M_level_inv_def S_lvl M by simp
  assume a: "\<not> ?thesis"
  then obtain L' where
    L': "L' \<in> atms_of D" and
    L'_notin_M1: "L' \<notin> atm_of ` lits_of M1" using T undef decomp by auto
  then have L'_in: "L' \<in> atm_of ` lits_of (M0 @ M2 @ Marked K (i + 1) # [])"
    using vars_of_D unfolding M by force
  then obtain L'' where
    "L'' \<in># D" and
    L'': "L' = atm_of L''"
    using L' L'_notin_M1 unfolding atms_of_def by auto
  have "get_level L'' (trail S) = get_rev_level L'' (Suc i) (Marked K (Suc i) # rev M2 @ rev M0)"
    using L'_notin_M1 L'' M by (auto simp del: get_rev_level.simps)
  have "get_all_levels_of_marked (trail S) = rev [1..<1+?k]"
    using inv S_lvl unfolding cdcl\<^sub>W_M_level_inv_def by auto
  then have "get_all_levels_of_marked (M0 @ M2)
    = rev [Suc (Suc i)..<Suc (get_maximum_level (D + {#L#}) (trail S))]"
    unfolding M by (auto simp:rev_swap[symmetric] dest!: append_cons_eq_upt_length_i_end)

  then have M: "get_all_levels_of_marked M0 @ get_all_levels_of_marked M2
    = rev [Suc (Suc i)..<Suc (length (get_all_levels_of_marked (M0 @ M2 @ Marked K (Suc i) # M1)))]"
    unfolding max unfolding M by simp

  have "get_rev_level L'' (Suc i) (Marked K (Suc i) # rev (M0 @ M2))
    \<ge> Min (set ((Suc i) # get_all_levels_of_marked (Marked K (Suc i) # rev (M0 @ M2))))"
    using get_rev_level_ge_min_get_all_levels_of_marked[of L''
      "rev (M0 @ M2 @ [Marked K (Suc i)])" "Suc i"] L'_in
    unfolding L'' by (fastforce simp add: lits_of_def)
  also have "Min (set ((Suc i) # get_all_levels_of_marked (Marked K (Suc i) # rev (M0 @ M2))))
    = Min (set ((Suc i) # get_all_levels_of_marked (rev (M0 @ M2))))" by auto
  also have "\<dots> = Min (set ((Suc i) # get_all_levels_of_marked M0 @ get_all_levels_of_marked M2))"
    by (simp add: Un_commute)
  also have "\<dots> =  Min (set ((Suc i) # [Suc (Suc i)..<2 + length (get_all_levels_of_marked M0)
    + (length (get_all_levels_of_marked M2) + length (get_all_levels_of_marked M1))]))"
    unfolding M by (auto simp add: Un_commute)
  also have "\<dots> = Suc i" by (auto intro: Min_eqI)
  finally have "get_rev_level L'' (Suc i) (Marked K (Suc i) # rev (M0 @ M2)) \<ge> Suc i" .
  then have "get_level L'' (trail S) \<ge> i + 1"
    using \<open>get_level L'' (trail S) = get_rev_level L'' (Suc i) (Marked K (Suc i) # rev M2 @ rev M0)\<close>
    by simp
  then have "get_maximum_level D (trail S) \<ge> i + 1"
    using get_maximum_level_ge_get_level[OF \<open>L'' \<in># D\<close>, of "trail S"] by auto
  then show False using i by auto
qed

lemma distinct_atms_of_incl_not_in_other:
  assumes a1: "no_dup (M @ M')"
  and a2: "atms_of D \<subseteq> atm_of ` lits_of M'"
  shows"\<forall>x\<in>atms_of D. x \<notin> atm_of ` lits_of M"
proof -
  { fix aa :: 'a
    have ff1: "\<And>l ms. undefined_lit ms l \<or> atm_of l
      \<in> set (map (\<lambda>m. atm_of (lit_of (m::('a, 'b, 'c) marked_lit))) ms)"
      by (simp add: defined_lit_map)
    have ff2: "\<And>a. a \<notin> atms_of D \<or> a \<in> atm_of ` lits_of M'"
      using a2 by (meson subsetCE)
    have ff3: "\<And>a. a \<notin> set (map (\<lambda>m. atm_of (lit_of m)) M')
      \<or> a \<notin> set (map (\<lambda>m. atm_of (lit_of m)) M)"
      using a1 by (metis (lifting) IntI distinct_append empty_iff map_append)
    have "\<forall>L a f. \<exists>l. ((a::'a) \<notin> f ` L \<or> (l::'a literal) \<in> L) \<and> (a \<notin> f ` L \<or> f l = a)"
      by blast
    then have "aa \<notin> atms_of D \<or> aa \<notin> atm_of ` lits_of M"
      using ff3 ff2 ff1 by (metis (no_types) Marked_Propagated_in_iff_in_lits_of) }
  then show ?thesis
    by blast
qed

lemma cdcl\<^sub>W_propagate_is_conclusion:
  assumes
    "cdcl\<^sub>W S S'" and
    inv: "cdcl\<^sub>W_M_level_inv S" and
    decomp: "all_decomposition_implies_m (init_clss S) (get_all_marked_decomposition (trail S))" and
    learned: "cdcl\<^sub>W_learned_clause S" and
    confl: "\<forall>T. conflicting S = C_Clause T \<longrightarrow> trail S \<Turnstile>as CNot T" and
    alien: "no_strange_atm S"
  shows "all_decomposition_implies_m (init_clss S') (get_all_marked_decomposition (trail S'))"
  using assms(1,2)
proof (induct rule: cdcl\<^sub>W_all_induct_lev2)
  case restart
  then show ?case by auto
next
  case forget
  then show ?case using decomp by auto
next
  case conflict
  then show ?case using decomp by auto
next
  case (resolve L C M D) note tr = this(1) and T = this(4)
  let ?decomp = "get_all_marked_decomposition M"
  have M: "set ?decomp = insert (hd ?decomp) (set (tl ?decomp))"
    by (cases ?decomp) auto
  show ?case
    using decomp tr T unfolding all_decomposition_implies_def
    by (cases "hd (get_all_marked_decomposition M)")
       (auto simp: M)
next
  case (skip L C' M D) note tr = this(1) and T = this(5)
  have M: "set (get_all_marked_decomposition M)
    = insert (hd (get_all_marked_decomposition M)) (set (tl (get_all_marked_decomposition M)))"
    by (cases "get_all_marked_decomposition M") auto
  show ?case
    using decomp tr T unfolding all_decomposition_implies_def
    by (cases "hd (get_all_marked_decomposition M)")
       (auto simp add: M)
next
  case decide note S = this(1) and undef = this(2) and T = this(4)
  show ?case using decomp T undef unfolding S all_decomposition_implies_def by auto
next
  case (propagate C L T) note propa = this(2) and undef = this(3) and T =this(5)
  obtain a y where ay: "hd (get_all_marked_decomposition (trail S)) = (a, y)"
    by (cases "hd (get_all_marked_decomposition (trail S))")
  then have M: "trail S = y @ a" using get_all_marked_decomposition_decomp by blast
  have M': "set (get_all_marked_decomposition (trail S))
    = insert (a, y) (set (tl (get_all_marked_decomposition (trail S))))"
    using ay by (cases "get_all_marked_decomposition (trail S)") auto
  have "(\<lambda>a. {#lit_of a#}) ` set a \<union> set_mset (init_clss S) \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set y"
    using decomp ay unfolding all_decomposition_implies_def
    by (cases "get_all_marked_decomposition (trail S)") fastforce+
  then have a_Un_N_M: "(\<lambda>a. {#lit_of a#}) ` set a \<union> set_mset (init_clss S)
    \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set (trail S)"
    unfolding M by (auto simp add: all_in_true_clss_clss image_Un)

  have "(\<lambda>a. {#lit_of a#}) ` set a \<union> set_mset (init_clss S) \<Turnstile>p {#L#}" (is "?I \<Turnstile>p _")
    proof (rule true_clss_cls_plus_CNot)
      show "?I \<Turnstile>p C + {#L#}"
        using propa propagate.prems learned confl unfolding M
        by (metis Un_iff cdcl\<^sub>W_learned_clause_def clauses_def mem_set_mset_iff propagate.hyps(1)
          set_mset_union true_clss_clss_in_imp_true_clss_cls true_clss_cs_mono_l2
          union_trus_clss_clss)
    next
      have "(\<lambda>m. {#lit_of m#}) ` set (trail S) \<Turnstile>ps CNot C"
        using \<open>(trail S) \<Turnstile>as CNot C\<close> true_annots_true_clss_clss by blast
      then show "?I \<Turnstile>ps CNot C"
        using a_Un_N_M true_clss_clss_left_right true_clss_clss_union_l_r by blast
    qed
  moreover have "\<And>aa b.
      \<forall> (Ls, seen)\<in>set (get_all_marked_decomposition (y @ a)).
        (\<lambda>a. {#lit_of a#}) ` set Ls \<union> set_mset (init_clss S) \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set seen
    \<Longrightarrow> (aa, b) \<in> set (tl (get_all_marked_decomposition (y @ a)))
    \<Longrightarrow> (\<lambda>a. {#lit_of a#}) ` set aa \<union> set_mset (init_clss S) \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set b"
    by (metis (no_types, lifting) case_prod_conv get_all_marked_decomposition_never_empty_sym
      list.collapse list.set_intros(2))

  ultimately show ?case
    using decomp T undef unfolding ay all_decomposition_implies_def
    using M \<open>(\<lambda>a. {#lit_of a#}) ` set a \<union> set_mset (init_clss S) \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set y\<close>
     ay by auto
next
  case (backtrack K i M1 M2 L D T) note decomp' = this(1) and lev_L = this(2) and conf = this(3) and
    undef = this(6) and T = this(7)
  have "\<forall>l \<in> set M2. \<not>is_marked l"
    using get_all_marked_decomposition_snd_not_marked backtrack.hyps(1) by blast
  obtain M0 where M: "trail S = M0 @ M2 @ Marked K (i + 1) # M1"
    using decomp' by auto
  show ?case unfolding all_decomposition_implies_def
    proof
      fix x
      assume "x \<in>set (get_all_marked_decomposition (trail T))"
      then have x: "x \<in> set (get_all_marked_decomposition (Propagated L ((D + {#L#})) # M1))"
        using T decomp' undef by simp
      let ?m = "get_all_marked_decomposition (Propagated L ((D + {#L#})) # M1)"
      let ?hd = "hd ?m"
      let ?tl = "tl ?m"
      have "x = ?hd \<or> x \<in> set ?tl"
        using x by (case_tac "?m") auto
      moreover {
        assume "x \<in> set ?tl"
        then have "x \<in> set (get_all_marked_decomposition (trail S))"
          using tl_get_all_marked_decomposition_skip_some[of x] by (simp add: list.set_sel(2) M)
        then have "case x of (Ls, seen) \<Rightarrow> (\<lambda>a. {#lit_of a#}) ` set Ls
                \<union> set_mset (init_clss (T))
                \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set seen"
          using decomp learned decomp confl alien inv T undef M
          unfolding all_decomposition_implies_def by auto
      }
      moreover {
        assume "x = ?hd"
        obtain M1' M1'' where M1: "hd (get_all_marked_decomposition M1) = (M1', M1'')"
          by (cases "hd (get_all_marked_decomposition M1)")
        then have x': "x = (M1', Propagated L ( (D + {#L#})) # M1'')"
          using \<open>x= ?hd\<close> by auto
        have "(M1', M1'') \<in> set (get_all_marked_decomposition (trail S))"
          using M1[symmetric] hd_get_all_marked_decomposition_skip_some[OF M1[symmetric],
            of "M0 @ M2" _ "i+1"] unfolding M by fastforce
        then have 1: "(\<lambda>a. {#lit_of a#}) ` set M1' \<union> set_mset (init_clss S)
          \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set M1''"
          using decomp unfolding all_decomposition_implies_def by auto
        moreover
          have "trail S \<Turnstile>as CNot D" using conf confl by auto
          then have vars_of_D: "atms_of D \<subseteq> atm_of ` lits_of (trail S)"
            unfolding atms_of_def
            by (meson image_subsetI mem_set_mset_iff true_annots_CNot_all_atms_defined)
          have vars_of_D: "atms_of D \<subseteq> atm_of ` lits_of M1"
            using backtrack_atms_of_D_in_M1[of S M1 L D i  K M2 T] backtrack inv conf confl
            by auto
          have "no_dup (trail S)" using inv  by auto
          then have vars_in_M1:
            "\<forall>x \<in> atms_of D. x \<notin> atm_of ` lits_of (M0 @ M2 @ Marked K (i + 1) # [])"
            using vars_of_D distinct_atms_of_incl_not_in_other[of "M0 @M2 @ Marked K (i + 1) # []"
              M1]
            unfolding M by auto
          have "M1 \<Turnstile>as CNot D"
            using vars_in_M1 true_annots_remove_if_notin_vars[of "M0 @ M2 @ Marked K (i + 1) # []"
              M1 "CNot D"] \<open>trail S \<Turnstile>as CNot D\<close> unfolding M lits_of_def by simp
          have "M1 = M1'' @ M1'" by (simp add: M1 get_all_marked_decomposition_decomp)
          have TT: "(\<lambda>a. {#lit_of a#}) ` set M1' \<union> set_mset (init_clss S) \<Turnstile>ps CNot D"
            using true_annots_true_clss_cls[OF \<open>M1 \<Turnstile>as CNot D\<close>] true_clss_clss_left_right[OF 1,
              of "CNot D"] unfolding \<open>M1 = M1'' @ M1'\<close> by (auto simp add: inf_sup_aci(5,7))
          have "init_clss S \<Turnstile>pm D + {#L#}"
            using conf learned cdcl\<^sub>W_learned_clause_def confl by blast
          then have T': "(\<lambda>a. {#lit_of a#}) ` set M1' \<union> set_mset (init_clss S) \<Turnstile>p D + {#L#}" by auto
          have "atms_of (D + {#L#}) \<subseteq> atms_of_mu (clauses S)"
            using alien conf unfolding no_strange_atm_def clauses_def by auto
          then have "(\<lambda>a. {#lit_of a#}) ` set M1' \<union> set_mset (init_clss S) \<Turnstile>p {#L#}"
            using true_clss_cls_plus_CNot[OF T' TT] by auto
        ultimately
          have "case x of (Ls, seen) \<Rightarrow> (\<lambda>a. {#lit_of a#}) ` set Ls
            \<union> set_mset (init_clss T)
            \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set seen" using T' T decomp' undef unfolding x' by simp
      }
      ultimately show "case x of (Ls, seen) \<Rightarrow> (\<lambda>a. {#lit_of a#}) ` set Ls \<union> set_mset (init_clss T)
        \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set seen" using T by auto
    qed
qed

lemma cdcl\<^sub>W_propagate_is_false:
  assumes
    "cdcl\<^sub>W S S'" and
    lev: "cdcl\<^sub>W_M_level_inv S" and
    learned: "cdcl\<^sub>W_learned_clause S" and
    decomp: "all_decomposition_implies_m (init_clss S) (get_all_marked_decomposition (trail S))" and
    confl: "\<forall>T. conflicting S = C_Clause T \<longrightarrow> trail S \<Turnstile>as CNot T" and
    alien: "no_strange_atm S" and
    mark_confl: "every_mark_is_a_conflict S"
  shows "every_mark_is_a_conflict S'"
  using assms(1,2)
proof (induct rule: cdcl\<^sub>W_all_induct_lev2)
  case (propagate C L T) note undef = this(3) and T =this(5)
  show ?case
    proof (intro allI impI)
      fix L' mark a b
      assume "a @ Propagated L' mark # b = trail T"
      then have "(a=[] \<and> L = L' \<and>  mark = C + {#L#} \<and> b = trail S)
        \<or> tl a @ Propagated L' mark # b = trail S"
        using T undef by (cases a) fastforce+
      moreover {
        assume "tl a @ Propagated L' mark # b = trail S"
        then have "b \<Turnstile>as CNot ( mark - {#L'#}) \<and> L' \<in>#  mark"
          using mark_confl by auto
      }
      moreover {
        assume "a=[]" and "L = L'" and " mark = C + {#L#}" and "b = trail S"
        then have "b \<Turnstile>as CNot ( mark - {#L#}) \<and> L \<in>#  mark"
          using \<open>trail S \<Turnstile>as CNot C\<close> by auto
      }
      ultimately show "b \<Turnstile>as CNot ( mark - {#L'#}) \<and> L' \<in>#  mark" by blast
    qed
next
  case (decide L) note undef[simp] = this(2) and T = this(4)
  have "\<And>a La mark b. a @ Propagated La mark # b = Marked L (backtrack_lvl S+1) # trail S
    \<Longrightarrow> tl a @ Propagated La mark # b = trail S" by (case_tac a, auto)
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
        \<longrightarrow> b \<Turnstile>as CNot ( mark - {#La#}) \<and> La \<in>#  mark"
        using mark_confl unfolding skip.hyps(1) by simp
      ultimately show "b \<Turnstile>as CNot ( mark - {#L'#}) \<and> L' \<in>#  mark" by blast
    qed
next
  case (conflict D)
  then show ?case using mark_confl by simp
next
  case (resolve L C M D T) note tr_S = this(1) and T = this(4)
  show ?case unfolding resolve.hyps(1)
    proof (intro allI impI)
      fix  L' mark a b
      assume "a @ Propagated L' mark # b = trail T"
      then have "Propagated L ( (C + {#L#})) # M
        = (Propagated L ( (C + {#L#})) # a) @ Propagated L' mark # b"
        using T tr_S by auto
      then show "b \<Turnstile>as CNot ( mark - {#L'#}) \<and> L' \<in>#  mark"
        using mark_confl unfolding resolve.hyps(1) by presburger
    qed
next
  case restart
  then show ?case by auto
next
  case forget
  then show ?case using mark_confl by auto
next
  case (backtrack K i M1 M2 L D T) note decomp = this(1) and conf = this(3) and undef = this(6) and
    T =this(7)
  have "\<forall>l \<in> set M2. \<not>is_marked l"
    using get_all_marked_decomposition_snd_not_marked backtrack.hyps(1) by blast
  obtain M0 where M: "trail S = M0 @ M2 @ Marked K (i + 1) # M1"
    using backtrack.hyps(1) by auto
  have [simp]: "trail (reduce_trail_to M1 (add_learned_cls (D + {#L#})
    (update_backtrack_lvl i (update_conflicting C_True S)))) = M1"
    using decomp by auto
  show ?case
    proof (intro allI impI)
      fix La mark a b
      assume "a @ Propagated La mark # b = trail T"
      then have "(a = [] \<and> Propagated La mark = Propagated L (D + {#L#}) \<and> b = M1)
        \<or> tl a @ Propagated La mark # b = M1"
        using M T decomp undef by (cases a) (auto)
      moreover {
        assume A: "a = []" and
          P: "Propagated La mark = Propagated L ( (D + {#L#}))" and
          b: "b = M1"
        have "trail S \<Turnstile>as CNot D" using conf confl by auto
        then have vars_of_D: "atms_of D \<subseteq> atm_of ` lits_of (trail S)"
          unfolding atms_of_def
          by (meson image_subsetI mem_set_mset_iff true_annots_CNot_all_atms_defined)
        have vars_of_D: "atms_of D \<subseteq> atm_of ` lits_of M1"
          using backtrack_atms_of_D_in_M1[of S M1 L D i K M2 T] T  backtrack lev confl by auto
        have "no_dup (trail S)" using lev by auto
        then have vars_in_M1: "\<forall>x \<in> atms_of D. x \<notin>
          atm_of ` lits_of (M0 @ M2 @ Marked K (i + 1) # [])"
          using vars_of_D distinct_atms_of_incl_not_in_other[of "M0 @ M2 @ Marked K (i + 1) # []"
            M1] unfolding M by auto
        have "M1 \<Turnstile>as CNot D"
          using vars_in_M1 true_annots_remove_if_notin_vars[of "M0 @ M2 @ Marked K (i + 1) # []" M1
            "CNot D"] \<open>trail S \<Turnstile>as CNot D\<close> unfolding M lits_of_def by simp
        then have "b \<Turnstile>as CNot ( mark - {#La#}) \<and> La \<in>#  mark"
          using P b by auto
      }
      moreover {
        assume "tl a @ Propagated La mark # b = M1"
        then obtain c' where "c' @ Propagated La mark # b = trail S" unfolding M by auto
        then have "b \<Turnstile>as CNot (mark - {#La#}) \<and> La \<in>#  mark"
          using mark_confl by blast
      }
      ultimately show "b \<Turnstile>as CNot (mark - {#La#}) \<and> La \<in>#  mark" by fast
    qed
qed

lemma cdcl\<^sub>W_conflicting_is_false:
  assumes
    "cdcl\<^sub>W S S'" and
    M_lev: "cdcl\<^sub>W_M_level_inv S" and
    confl_inv: "\<forall>T. conflicting S = C_Clause T \<longrightarrow> trail S \<Turnstile>as CNot T" and
    marked_confl: "\<forall>L mark a b. a @ Propagated L mark # b = (trail S)
      \<longrightarrow> (b \<Turnstile>as CNot (mark - {#L#}) \<and> L \<in>#  mark)" and
      dist: "distinct_cdcl\<^sub>W_state S"
  shows "\<forall>T. conflicting S' = C_Clause T \<longrightarrow> trail S' \<Turnstile>as CNot T"
  using assms(1,2)
proof (induct rule: cdcl\<^sub>W_all_induct_lev2)
  case (skip L C' M D) note tr_S = this(1) and T =this(5)
  then have "Propagated L C' # M \<Turnstile>as CNot D" using assms skip by auto
  moreover
    have "L \<notin># D"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then have "- L \<in> lits_of M"
          using in_CNot_implies_uminus(2)[of D L "Propagated L C' # M"]
          \<open>Propagated L C' # M \<Turnstile>as CNot D\<close> by simp
        then show False
          by (metis M_lev cdcl\<^sub>W_M_level_inv_decomp(1) consistent_interp_def insert_iff
            lits_of_cons marked_lit.sel(2) skip.hyps(1))
      qed
  ultimately show ?case
    using skip.hyps(1-3) true_annots_CNot_lit_of_notin_skip T unfolding cdcl\<^sub>W_M_level_inv_def
     by fastforce
next
  case (resolve L C M D T) note tr = this(1) and confl = this(2) and T = this(4)
  show ?case
    proof (intro allI impI)
      fix T'
      have "tl (trail S) \<Turnstile>as CNot C" using tr assms(4) by fastforce
      moreover
        have "distinct_mset (D + {#- L#})" using confl dist
          unfolding distinct_cdcl\<^sub>W_state_def by auto
        then have "-L \<notin># D" unfolding distinct_mset_def by auto
        have "M \<Turnstile>as CNot D"
          proof -
            have "Propagated L ( (C + {#L#})) # M \<Turnstile>as CNot D \<union> CNot {#- L#}"
              using confl tr confl_inv  by force
            then show ?thesis
              using M_lev \<open>- L \<notin># D\<close> tr true_annots_lit_of_notin_skip by force
          qed
      moreover assume "conflicting T = C_Clause T'"
      ultimately
        show "trail T \<Turnstile>as CNot T'"
        using tr T by auto
    qed
qed (auto simp: assms(2))

lemma cdcl\<^sub>W_conflicting_decomp:
  assumes "cdcl\<^sub>W_conflicting S"
  shows "\<forall>T. conflicting S = C_Clause T \<longrightarrow> trail S \<Turnstile>as CNot T"
  and "\<forall>L mark a b. a @ Propagated L mark # b = (trail S)
    \<longrightarrow> (b \<Turnstile>as CNot ( mark - {#L#}) \<and> L \<in>#  mark)"
  using assms unfolding cdcl\<^sub>W_conflicting_def by blast+

lemma cdcl\<^sub>W_conflicting_decomp2:
  assumes "cdcl\<^sub>W_conflicting S" and "conflicting S = C_Clause T"
  shows "trail S \<Turnstile>as CNot T"
  using assms unfolding cdcl\<^sub>W_conflicting_def by blast+

lemma cdcl\<^sub>W_conflicting_decomp2':
  assumes
    "cdcl\<^sub>W_conflicting S" and
    "conflicting S = C_Clause D"
  shows "trail S \<Turnstile>as CNot D"
  using assms unfolding cdcl\<^sub>W_conflicting_def by auto

lemma cdcl\<^sub>W_conflicting_S0_cdcl\<^sub>W[simp]:
  "cdcl\<^sub>W_conflicting (init_state N)"
  unfolding cdcl\<^sub>W_conflicting_def by auto

subsubsection \<open>Putting all the invariants together\<close>
lemma cdcl\<^sub>W_all_inv:
  assumes cdcl\<^sub>W: "cdcl\<^sub>W S S'" and
  1: "all_decomposition_implies_m (init_clss S) (get_all_marked_decomposition (trail S))" and
  2: "cdcl\<^sub>W_learned_clause S" and
  4: "cdcl\<^sub>W_M_level_inv S" and
  5: "no_strange_atm S" and
  7: "distinct_cdcl\<^sub>W_state S" and
  8: "cdcl\<^sub>W_conflicting S"
  shows "all_decomposition_implies_m (init_clss S') (get_all_marked_decomposition (trail S'))"
  and "cdcl\<^sub>W_learned_clause S'"
  and "cdcl\<^sub>W_M_level_inv S'"
  and "no_strange_atm S'"
  and "distinct_cdcl\<^sub>W_state S'"
  and "cdcl\<^sub>W_conflicting S'"
proof -
  show S1: "all_decomposition_implies_m (init_clss S') (get_all_marked_decomposition (trail S'))"
    using cdcl\<^sub>W_propagate_is_conclusion[OF cdcl\<^sub>W 4 1 2 _ 5] 8 unfolding cdcl\<^sub>W_conflicting_def
    by blast
  show S2: "cdcl\<^sub>W_learned_clause S'" using cdcl\<^sub>W_learned_clss[OF cdcl\<^sub>W 2 4] .
  show S4: "cdcl\<^sub>W_M_level_inv S'" using cdcl\<^sub>W_consistent_inv[OF cdcl\<^sub>W 4] .
  show S5: "no_strange_atm S'"  using  cdcl\<^sub>W_no_strange_atm_inv[OF cdcl\<^sub>W 5 4] .
  show S7: "distinct_cdcl\<^sub>W_state S'" using distinct_cdcl\<^sub>W_state_inv[OF cdcl\<^sub>W 4 7] .
  show S8: "cdcl\<^sub>W_conflicting S'"
    using cdcl\<^sub>W_conflicting_is_false[OF cdcl\<^sub>W 4 _ _ 7]  8 cdcl\<^sub>W_propagate_is_false[OF cdcl\<^sub>W 4 2 1 _
      5]
    unfolding cdcl\<^sub>W_conflicting_def by fast
qed

lemma rtranclp_cdcl\<^sub>W_all_inv:
  assumes
    cdcl\<^sub>W: "rtranclp cdcl\<^sub>W S S'" and
    1: "all_decomposition_implies_m (init_clss S) (get_all_marked_decomposition (trail S))" and
    2: "cdcl\<^sub>W_learned_clause S" and
    4: "cdcl\<^sub>W_M_level_inv S" and
    5: "no_strange_atm S" and
    7: "distinct_cdcl\<^sub>W_state S" and
    8: "cdcl\<^sub>W_conflicting S"
  shows
    "all_decomposition_implies_m (init_clss S') (get_all_marked_decomposition (trail S'))" and
    "cdcl\<^sub>W_learned_clause S'" and
    "cdcl\<^sub>W_M_level_inv S'" and
    "no_strange_atm S'" and
    "distinct_cdcl\<^sub>W_state S'" and
    "cdcl\<^sub>W_conflicting S'"
   using assms
proof (induct rule: rtranclp.induct)
  case (rtrancl_refl S)
    case 1 then show ?case by blast
    case 2 then show ?case by blast
    case 3 then show ?case by blast
    case 4 then show ?case by blast
    case 5 then show ?case by blast
    case 6 then show ?case by blast
next
  case (rtrancl_into_rtrancl S S' S'') note H = this
    case 1 with H(2-7)[OF this(1-6)] show ?case using cdcl\<^sub>W_all_inv[OF H(8)]
        rtrancl_into_rtrancl.hyps(1) by presburger
    case 2 with H(2-7)[OF this(1-6)] show ?case using cdcl\<^sub>W_all_inv[OF H(8)]
        rtrancl_into_rtrancl.hyps(1) by presburger
    case 3 with H(2-7)[OF this(1-6)] show ?case using cdcl\<^sub>W_all_inv[OF H(8)]
        rtrancl_into_rtrancl.hyps(1) by presburger
    case 4 with H(2-7)[OF this(1-6)] show ?case using cdcl\<^sub>W_all_inv[OF H(8)]
        rtrancl_into_rtrancl.hyps(1) by presburger
    case 5 with H(2-7)[OF this(1-6)] show ?case using cdcl\<^sub>W_all_inv[OF H(8)]
        rtrancl_into_rtrancl.hyps(1) by presburger
    case 6 with H(2-7)[OF this(1-6)] show ?case using cdcl\<^sub>W_all_inv[OF H(8)]
        rtrancl_into_rtrancl.hyps(1) by presburger
qed

lemma all_invariant_S0_cdcl\<^sub>W:
  assumes "distinct_mset_mset N"
  shows "all_decomposition_implies_m (init_clss (init_state N))
                                   (get_all_marked_decomposition (trail (init_state N)))"
  and "cdcl\<^sub>W_learned_clause (init_state N)"
  and "\<forall>T. conflicting (init_state N) = C_Clause T \<longrightarrow> (trail (init_state N))\<Turnstile>as CNot T"
  and "no_strange_atm (init_state N)"
  and "consistent_interp (lits_of (trail (init_state N)))"
  and "\<forall>L mark a b. a @ Propagated L mark # b =  trail (init_state N) \<longrightarrow>
     (b \<Turnstile>as CNot ( mark - {#L#}) \<and> L \<in>#  mark)"
  and "distinct_cdcl\<^sub>W_state (init_state N)"
  using assms by auto

(*prop 2.10.5.5*)
lemma cdcl\<^sub>W_only_propagated_vars_unsat:
  assumes
    marked: "\<forall>x \<in> set M. \<not> is_marked x" and
    DN: "D \<in># clauses S" and
    D: "M \<Turnstile>as CNot D" and
    inv: "all_decomposition_implies_m N (get_all_marked_decomposition M)" and
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
  have "atms_of_mu N \<union> atms_of_mu U = atms_of_mu N"
    using atm_incl state unfolding total_over_m_def no_strange_atm_def
     by (auto simp add: clauses_def)
  then have "total_over_m I (set_mset N)" using tot unfolding total_over_m_def by auto
  moreover have "N \<Turnstile>psm U" using learned_cl state unfolding cdcl\<^sub>W_learned_clause_def by auto
  ultimately have I_D: "I \<Turnstile> D"
    using I DN cons state unfolding true_clss_clss_def true_clss_def Ball_def
  by (metis Un_iff \<open>atms_of_mu N \<union> atms_of_mu U = atms_of_mu N\<close> atms_of_m_union clauses_def
    mem_set_mset_iff prod.inject set_mset_union total_over_m_def)

  have l0: "{{#lit_of L#} |L. is_marked L \<and> L \<in> set M} = {}" using marked by auto
  have "atms_of_m (set_mset N \<union> (\<lambda>a. {#lit_of a#}) ` set M) = atms_of_mu N"
    using atm_incl state unfolding no_strange_atm_def by auto
  then have "total_over_m I (set_mset N \<union> (\<lambda>a. {#lit_of a#}) ` (set M))"
    using tot unfolding total_over_m_def by auto
  then have "I \<Turnstile>s (\<lambda>a. {#lit_of a#}) ` (set M)"
    using all_decomposition_implies_propagated_lits_are_implied[OF inv] cons I
    unfolding true_clss_clss_def l0 by auto
  then have IM: "I \<Turnstile>s (\<lambda>a. {#lit_of a#}) ` set M" by auto
  {
    fix K
    assume "K \<in># D"
    then have "-K \<in> lits_of M"
      using D unfolding true_annots_def Ball_def CNot_def true_annot_def true_cls_def true_lit_def
      Bex_mset_def by (metis (mono_tags, lifting) count_single less_not_refl mem_Collect_eq)
    then have " -K \<in> I" using IM true_clss_singleton_lit_of_implies_incl lits_of_def by fastforce
  }
  then have "\<not> I \<Turnstile> D" using cons unfolding true_cls_def true_lit_def consistent_interp_def by auto
  then show False using I_D by blast
qed

(*prop 2.10.5.4*)
text \<open>We have actually a much stronger theorem, namely
  @{thm all_decomposition_implies_propagated_lits_are_implied}, that show that the only choices
  we made are marked in the formula\<close>
lemma
  assumes "all_decomposition_implies_m N (get_all_marked_decomposition M)"
  and "\<forall>m \<in> set M. \<not>is_marked m"
  shows "set_mset N \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set M"
proof -
  have T: "{{#lit_of L#} |L. is_marked L \<and> L \<in> set M} = {}" using assms(2) by auto
  then show ?thesis
    using all_decomposition_implies_propagated_lits_are_implied[OF assms(1)] unfolding T by simp
qed

(*prop 2.10.5.6*)
lemma conflict_with_false_implies_unsat:
  assumes
    cdcl\<^sub>W: "cdcl\<^sub>W S S'" and
    lev: "cdcl\<^sub>W_M_level_inv S" and
    [simp]: "conflicting S' = C_Clause {#}" and
    learned: "cdcl\<^sub>W_learned_clause S"
  shows "unsatisfiable (set_mset (init_clss S))"
  using assms
proof -
  have "cdcl\<^sub>W_learned_clause S'" using cdcl\<^sub>W_learned_clss cdcl\<^sub>W learned lev by auto
  then have "init_clss S' \<Turnstile>pm {#}" using assms(3) unfolding cdcl\<^sub>W_learned_clause_def by auto
  then have "init_clss S \<Turnstile>pm {#}"
    using cdcl\<^sub>W_init_clss[OF assms(1) lev] by auto
  then show ?thesis unfolding satisfiable_def true_clss_cls_def by auto
qed

lemma conflict_with_false_implies_terminated:
  assumes "cdcl\<^sub>W S S'"
  and "conflicting S = C_Clause {#}"
  shows "False"
  using assms by (induct rule: cdcl\<^sub>W_all_induct) auto

subsubsection \<open>No tautology is learned\<close>
text \<open>This is a simple consequence of all we have shown previously. It is not strictly necessary,
  but helps finding a better bound on the number of learned clauses.\<close>
lemma learned_clss_are_not_tautologies:
  assumes
    "cdcl\<^sub>W S S'" and
    lev: "cdcl\<^sub>W_M_level_inv S" and
    conflicting: "cdcl\<^sub>W_conflicting S" and
    no_tauto: "\<forall>s \<in># learned_clss S. \<not>tautology s"
  shows "\<forall>s \<in># learned_clss S'. \<not>tautology s"
  using assms
proof (induct rule: cdcl\<^sub>W_all_induct_lev2)
  case (backtrack K i M1 M2 L D) note confl = this(3)
  have "consistent_interp (lits_of (trail S))" using lev by auto
  moreover
    have "trail S \<Turnstile>as CNot (D + {#L#})"
      using conflicting confl unfolding cdcl\<^sub>W_conflicting_def by auto
    then have "lits_of (trail S) \<Turnstile>s CNot (D + {#L#})" using true_annots_true_cls by blast
  ultimately have "\<not>tautology (D + {#L#})" using consistent_CNot_not_tautology by blast
  then show ?case using backtrack no_tauto by (auto split: split_if_asm)
next
  case restart
  then show ?case using learned_clss_restart_state state_eq_learned_clss no_tauto
    by (metis (no_types, lifting) ball_msetE ball_msetI mem_set_mset_iff set_mset_mono subsetCE)
qed auto

definition "final_cdcl\<^sub>W_state (S:: 'st)
  \<longleftrightarrow> (trail S \<Turnstile>asm init_clss S
    \<or> ((\<forall>L \<in> set (trail S). \<not>is_marked L) \<and>
       (\<exists>C \<in># init_clss S. trail S \<Turnstile>as CNot C)))"

definition "termination_cdcl\<^sub>W_state (S:: 'st)
   \<longleftrightarrow> (trail S \<Turnstile>asm init_clss S
     \<or> ((\<forall>L \<in> atms_of_mu (init_clss S). L \<in> atm_of ` lits_of (trail S))
        \<and> (\<exists>C \<in># init_clss S. trail S \<Turnstile>as CNot C)))"

subsection \<open>CDCL Strong Completeness\<close>
fun mapi :: "('a \<Rightarrow> nat \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'b list" where
"mapi _ _ [] = []" |
"mapi f n (x # xs) = f x n # mapi f (n - 1) xs"

lemma mark_not_in_set_mapi[simp]: "L \<notin> set M \<Longrightarrow> Marked L k \<notin> set (mapi Marked i M)"
  by (induct M arbitrary: i) auto

lemma propagated_not_in_set_mapi[simp]: "L \<notin> set M \<Longrightarrow> Propagated L k \<notin> set (mapi Marked i M)"
  by (induct M arbitrary: i) auto

lemma image_set_mapi:
  "f ` set (mapi g i M) = set (mapi (\<lambda>x i. f (g x i)) i M)"
  by (induction M arbitrary: i) auto

lemma mapi_map_convert:
  "\<forall>x i j. f x i = f x j \<Longrightarrow> mapi f i M = map (\<lambda>x. f x 0) M"
  by (induction M arbitrary: i) auto

lemma defined_lit_mapi: "defined_lit (mapi Marked i M) L \<longleftrightarrow> atm_of L \<in> atm_of ` set M"
  by (induction M) (auto simp: defined_lit_map image_set_mapi mapi_map_convert)

lemma cdcl\<^sub>W_can_do_step:
  assumes
    "consistent_interp (set M)" and
    "distinct M" and
    "atm_of ` (set M) \<subseteq> atms_of_mu N"
  shows "\<exists>S. rtranclp cdcl\<^sub>W (init_state N) S
    \<and> state S = (mapi Marked (length M) M, N, {#}, length M, C_True)"
  using assms
proof (induct M)
  case Nil
  then show ?case by auto
next
  case (Cons L M) note IH = this(1)
  have "consistent_interp (set M)" and "distinct M" and "atm_of ` set M \<subseteq> atms_of_mu N"
    using Cons.prems(1-3) unfolding consistent_interp_def by auto
  then obtain S where
    st: "cdcl\<^sub>W\<^sup>*\<^sup>* (init_state N) S" and
    S: "state S = (mapi Marked (length M) M, N, {#}, length M, C_True)"
    using IH by auto
  let ?S\<^sub>0 = "incr_lvl (cons_trail (Marked L (length M +1)) S)"
  have "undefined_lit (mapi Marked (length M) M) L"
    using Cons.prems(1,2) unfolding defined_lit_def consistent_interp_def by fastforce
  moreover have "init_clss S = N"
    using S by blast
  moreover have "atm_of L \<in> atms_of_mu N" using Cons.prems(3) by auto
  moreover have undef: "undefined_lit (trail S) L"
    using S \<open>distinct (L#M)\<close> calculation(1) by (auto simp: defined_lit_mapi defined_lit_map)
  ultimately have "cdcl\<^sub>W S ?S\<^sub>0"
    using cdcl\<^sub>W.other[OF cdcl\<^sub>W_o.decide[OF decide_rule[OF S,
      of L ?S\<^sub>0]]] S  by (auto simp: state_eq_def simp del: state_simp)
  then show ?case
    using st S undef by (auto intro!: exI[of _ ?S\<^sub>0])
qed

lemma cdcl\<^sub>W_strong_completeness:
  assumes
    "set M \<Turnstile>s set_mset N" and
    "consistent_interp (set M)" and
    "distinct M" and
    "atm_of ` (set M) \<subseteq> atms_of_mu N"
  obtains S where
    "state S = (mapi Marked (length M) M, N, {#}, length M, C_True)" and
    "rtranclp cdcl\<^sub>W (init_state N) S" and
    "final_cdcl\<^sub>W_state S"
proof -
  obtain S where
    st: "rtranclp cdcl\<^sub>W (init_state N) S" and
    S: "state S = (mapi Marked (length M) M, N, {#}, length M, C_True)"
    using cdcl\<^sub>W_can_do_step[OF assms(2-4)] by auto
  have "lits_of (mapi Marked (length M) M) = set M"
    by (induct M, auto)
  then have "mapi Marked (length M) M \<Turnstile>asm N" using assms(1) true_annots_true_cls by metis
  then have "final_cdcl\<^sub>W_state S"
    using S unfolding final_cdcl\<^sub>W_state_def by auto
  then show ?thesis using that st S by blast
qed

subsection \<open>Higher level strategy\<close>

text \<open>The rules described previously do not lead to a conclusive state. We have to add a strategy.\<close>

subsubsection \<open>Definition\<close>

lemma tranclp_conflict_iff[iff]:
  "full1 conflict S S' \<longleftrightarrow> conflict S S'"
proof -
  have "tranclp conflict S S' \<Longrightarrow> conflict S S'"
    unfolding full1_def by (induct rule: tranclp.induct) force+
  then have "tranclp conflict S S' \<Longrightarrow> conflict S S'" by (meson rtranclpD)
  then show ?thesis unfolding full1_def by (metis conflictE conflicting_clause.simps(3)
    conflicting_update_conflicting state_eq_conflicting tranclp.intros(1))
qed

inductive cdcl\<^sub>W_cp :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
conflict'[intro]: "conflict S S' \<Longrightarrow> cdcl\<^sub>W_cp S S'" |
propagate': "propagate S S' \<Longrightarrow> cdcl\<^sub>W_cp S S'"

lemma rtranclp_cdcl\<^sub>W_cp_rtranclp_cdcl\<^sub>W:
  "cdcl\<^sub>W_cp\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W\<^sup>*\<^sup>* S T"
  by (induction rule: rtranclp_induct) (auto simp: cdcl\<^sub>W_cp.simps dest: cdcl\<^sub>W.intros)

lemma cdcl\<^sub>W_cp_state_eq_compatible:
  assumes
    "cdcl\<^sub>W_cp S T" and
    "S \<sim> S'" and
    "T \<sim> T'"
  shows "cdcl\<^sub>W_cp S' T'"
  using assms
  apply (induction)
    using conflict_state_eq_compatible apply auto[1]
  using propagate' propagate_state_eq_compatible by auto

lemma tranclp_cdcl\<^sub>W_cp_state_eq_compatible:
  assumes
    "cdcl\<^sub>W_cp\<^sup>+\<^sup>+ S T" and
    "S \<sim> S'" and
    "T \<sim> T'"
  shows "cdcl\<^sub>W_cp\<^sup>+\<^sup>+ S' T'"
  using assms
proof induction
  case base
  then show ?case
    using cdcl\<^sub>W_cp_state_eq_compatible by blast
next
  case (step U V)
  obtain ss :: 'st where
    "cdcl\<^sub>W_cp S ss \<and> cdcl\<^sub>W_cp\<^sup>*\<^sup>* ss U"
    by (metis (no_types) step(1) tranclpD)
  then show ?case
    by (meson cdcl\<^sub>W_cp_state_eq_compatible rtranclp.rtrancl_into_rtrancl rtranclp_into_tranclp2
      state_eq_ref step(2) step(4) step(5))
qed

lemma conflicting_clause_full_cdcl\<^sub>W_cp:
  "conflicting S \<noteq> C_True \<Longrightarrow> full cdcl\<^sub>W_cp S S"
unfolding full_def rtranclp_unfold tranclp_unfold by (auto simp add: cdcl\<^sub>W_cp.simps)

lemma skip_unique:
  "skip S T \<Longrightarrow> skip S T' \<Longrightarrow> T \<sim> T'"
  by (fastforce simp: state_eq_def simp del: state_simp)

lemma resolve_unique:
  "resolve S T \<Longrightarrow> resolve S T' \<Longrightarrow> T \<sim> T'"
  by (fastforce simp: state_eq_def simp del: state_simp)

lemma cdcl\<^sub>W_cp_no_more_clauses:
  assumes "cdcl\<^sub>W_cp S S'"
  shows "clauses S = clauses S'"
  using assms by (induct rule: cdcl\<^sub>W_cp.induct) (auto elim!: conflictE propagateE)

lemma tranclp_cdcl\<^sub>W_cp_no_more_clauses:
  assumes "cdcl\<^sub>W_cp\<^sup>+\<^sup>+ S S'"
  shows "clauses S = clauses S'"
  using assms by (induct rule: tranclp.induct) (auto dest: cdcl\<^sub>W_cp_no_more_clauses)

lemma rtranclp_cdcl\<^sub>W_cp_no_more_clauses:
  assumes "cdcl\<^sub>W_cp\<^sup>*\<^sup>* S S'"
  shows "clauses S = clauses S'"
  using assms by (induct rule: rtranclp_induct) (fastforce dest: cdcl\<^sub>W_cp_no_more_clauses)+

lemma no_conflict_after_conflict:
  "conflict S T \<Longrightarrow> \<not>conflict T U"
  by fastforce

lemma no_propagate_after_conflict:
  "conflict S T \<Longrightarrow> \<not>propagate T U"
  by fastforce

lemma tranclp_cdcl\<^sub>W_cp_propagate_with_conflict_or_not:
  assumes "cdcl\<^sub>W_cp\<^sup>+\<^sup>+ S U"
  shows "(propagate\<^sup>+\<^sup>+ S U \<and> conflicting U = C_True)
    \<or> (\<exists>T D. propagate\<^sup>*\<^sup>* S T \<and> conflict T U \<and> conflicting U = C_Clause D)"
proof -
  have "propagate\<^sup>+\<^sup>+ S U \<or> (\<exists>T. propagate\<^sup>*\<^sup>* S T \<and> conflict T U)"
    using assms by induction
    (force simp: cdcl\<^sub>W_cp.simps tranclp_into_rtranclp dest: no_conflict_after_conflict
       no_propagate_after_conflict)+
  moreover
    have "propagate\<^sup>+\<^sup>+ S U \<Longrightarrow> conflicting U = C_True"
      unfolding tranclp_unfold_end by auto
  moreover
    have "\<And>T. conflict T U \<Longrightarrow> \<exists>D. conflicting U = C_Clause D"
      by auto
  ultimately show ?thesis by meson
qed

lemma cdcl\<^sub>W_cp_conflicting_not_empty[simp]: "conflicting S = C_Clause D  \<Longrightarrow> \<not>cdcl\<^sub>W_cp S S'"
proof
  assume "cdcl\<^sub>W_cp S S'" and "conflicting S = C_Clause D"
  then show False by (induct rule: cdcl\<^sub>W_cp.induct) auto
qed

lemma no_step_cdcl\<^sub>W_cp_no_conflict_no_propagate:
  assumes "no_step cdcl\<^sub>W_cp S"
  shows "no_step conflict S" and "no_step propagate S"
  using assms conflict' apply blast
  by (meson assms conflict' propagate')

text \<open>CDCL with the reasonable strategy: we fully propagate the conflict and propagate, then we
  apply any other possible rule @{term "cdcl\<^sub>W_o S S'"} and re-apply conflict and propagate
  @{term "full cdcl\<^sub>W_cp S' S''"}\<close>
inductive cdcl\<^sub>W_stgy :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
conflict': "full1 cdcl\<^sub>W_cp S S' \<Longrightarrow> cdcl\<^sub>W_stgy S S'" |
other': "cdcl\<^sub>W_o S S'  \<Longrightarrow> no_step cdcl\<^sub>W_cp S \<Longrightarrow> full cdcl\<^sub>W_cp S' S'' \<Longrightarrow> cdcl\<^sub>W_stgy S S''"

subsubsection \<open>Invariants\<close>
text \<open>These are the same invariants as before, but lifted\<close>
lemma cdcl\<^sub>W_cp_learned_clause_inv:
  assumes "cdcl\<^sub>W_cp S S'"
  shows "learned_clss S = learned_clss S'"
  using assms by (induct rule: cdcl\<^sub>W_cp.induct) fastforce+

lemma rtranclp_cdcl\<^sub>W_cp_learned_clause_inv:
  assumes "cdcl\<^sub>W_cp\<^sup>*\<^sup>* S S'"
  shows "learned_clss S = learned_clss S'"
  using assms by (induct rule: rtranclp.induct) (fastforce dest: cdcl\<^sub>W_cp_learned_clause_inv)+

lemma tranclp_cdcl\<^sub>W_cp_learned_clause_inv:
  assumes "cdcl\<^sub>W_cp\<^sup>+\<^sup>+ S S'"
  shows "learned_clss S = learned_clss S'"
  using assms by (simp add: rtranclp_cdcl\<^sub>W_cp_learned_clause_inv tranclp_into_rtranclp)

lemma cdcl\<^sub>W_cp_backtrack_lvl:
  assumes "cdcl\<^sub>W_cp S S'"
  shows "backtrack_lvl S = backtrack_lvl S'"
  using assms by (induct rule: cdcl\<^sub>W_cp.induct) fastforce+

lemma rtranclp_cdcl\<^sub>W_cp_backtrack_lvl:
  assumes "cdcl\<^sub>W_cp\<^sup>*\<^sup>* S S'"
  shows "backtrack_lvl S = backtrack_lvl S'"
  using assms by (induct rule: rtranclp.induct) (fastforce dest: cdcl\<^sub>W_cp_backtrack_lvl)+

lemma cdcl\<^sub>W_cp_consistent_inv:
  assumes "cdcl\<^sub>W_cp S S'"
  and "cdcl\<^sub>W_M_level_inv S"
  shows "cdcl\<^sub>W_M_level_inv S'"
  using assms
proof (induct rule: cdcl\<^sub>W_cp.induct)
  case (conflict')
  then show ?case using cdcl\<^sub>W_consistent_inv cdcl\<^sub>W.conflict by blast
next
  case (propagate' S S')
  have "cdcl\<^sub>W S S'"
    using propagate'.hyps(1) propagate by blast
  then show "cdcl\<^sub>W_M_level_inv S'"
    using propagate'.prems(1) cdcl\<^sub>W_consistent_inv propagate by blast
qed

lemma full1_cdcl\<^sub>W_cp_consistent_inv:
  assumes "full1 cdcl\<^sub>W_cp S S'"
  and "cdcl\<^sub>W_M_level_inv S"
  shows "cdcl\<^sub>W_M_level_inv S'"
  using assms unfolding full1_def
proof -
  have "cdcl\<^sub>W_cp\<^sup>+\<^sup>+ S S'" and "cdcl\<^sub>W_M_level_inv S" using assms unfolding full1_def by auto
  then show ?thesis by (induct rule: tranclp.induct) (blast intro: cdcl\<^sub>W_cp_consistent_inv)+
qed

lemma rtranclp_cdcl\<^sub>W_cp_consistent_inv:
  assumes "rtranclp cdcl\<^sub>W_cp S S'"
  and "cdcl\<^sub>W_M_level_inv S"
  shows "cdcl\<^sub>W_M_level_inv S'"
  using assms unfolding full1_def
  by (induction rule: rtranclp_induct) (blast intro: cdcl\<^sub>W_cp_consistent_inv)+

lemma cdcl\<^sub>W_stgy_consistent_inv:
  assumes "cdcl\<^sub>W_stgy S S'"
  and "cdcl\<^sub>W_M_level_inv S"
  shows "cdcl\<^sub>W_M_level_inv S'"
  using assms apply (induct rule: cdcl\<^sub>W_stgy.induct)
  unfolding full_unfold by (blast intro: cdcl\<^sub>W_consistent_inv full1_cdcl\<^sub>W_cp_consistent_inv
    cdcl\<^sub>W.other)+

lemma rtranclp_cdcl\<^sub>W_stgy_consistent_inv:
  assumes "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S S'"
  and "cdcl\<^sub>W_M_level_inv S"
  shows "cdcl\<^sub>W_M_level_inv S'"
  using assms by induction (auto dest!: cdcl\<^sub>W_stgy_consistent_inv)

lemma cdcl\<^sub>W_cp_no_more_init_clss:
  assumes "cdcl\<^sub>W_cp S S'"
  shows "init_clss S = init_clss S'"
  using assms by (induct rule: cdcl\<^sub>W_cp.induct) auto

lemma tranclp_cdcl\<^sub>W_cp_no_more_init_clss:
  assumes "cdcl\<^sub>W_cp\<^sup>+\<^sup>+ S S'"
  shows "init_clss S = init_clss S'"
  using assms by (induct rule: tranclp.induct) (auto dest: cdcl\<^sub>W_cp_no_more_init_clss)

lemma cdcl\<^sub>W_stgy_no_more_init_clss:
  assumes "cdcl\<^sub>W_stgy S S'" and "cdcl\<^sub>W_M_level_inv S"
  shows "init_clss S = init_clss S'"
  using assms
  apply (induct rule: cdcl\<^sub>W_stgy.induct)
  unfolding full1_def full_def apply (blast dest: tranclp_cdcl\<^sub>W_cp_no_more_init_clss
    tranclp_cdcl\<^sub>W_o_no_more_init_clss)
  by (metis cdcl\<^sub>W_o_no_more_init_clss rtranclp_unfold tranclp_cdcl\<^sub>W_cp_no_more_init_clss)

lemma rtranclp_cdcl\<^sub>W_stgy_no_more_init_clss:
  assumes "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S S'" and "cdcl\<^sub>W_M_level_inv S"
  shows "init_clss S = init_clss S'"
  using assms
  apply (induct rule: rtranclp.induct, simp)
  using cdcl\<^sub>W_stgy_no_more_init_clss by (simp add: rtranclp_cdcl\<^sub>W_stgy_consistent_inv)

lemma cdcl\<^sub>W_cp_dropWhile_trail':
  assumes "cdcl\<^sub>W_cp S S'"
  obtains M where "trail S' = M @ trail S" and " (\<forall>l \<in> set M. \<not>is_marked l)"
  using assms by induction fastforce+

lemma rtranclp_cdcl\<^sub>W_cp_dropWhile_trail':
  assumes "cdcl\<^sub>W_cp\<^sup>*\<^sup>* S S'"
  obtains M :: "('v, nat, 'v clause) marked_lit list" where
    "trail S' = M @ trail S" and "\<forall>l \<in> set M. \<not>is_marked l"
  using assms by induction (fastforce dest!: cdcl\<^sub>W_cp_dropWhile_trail')+

lemma cdcl\<^sub>W_cp_dropWhile_trail:
  assumes "cdcl\<^sub>W_cp S S'"
  shows "\<exists>M. trail S' = M @ trail S \<and> (\<forall>l \<in> set M. \<not>is_marked l)"
  using assms by induction fastforce+

lemma rtranclp_cdcl\<^sub>W_cp_dropWhile_trail:
  assumes "cdcl\<^sub>W_cp\<^sup>*\<^sup>* S S'"
  shows "\<exists>M. trail S' = M @ trail S \<and> (\<forall>l \<in> set M. \<not>is_marked l)"
  using assms by induction (fastforce dest: cdcl\<^sub>W_cp_dropWhile_trail)+

text \<open>This theorem can be seen a a termination theorem for @{term cdcl\<^sub>W_cp}.\<close>
lemma length_model_le_vars:
  assumes "no_strange_atm S"
  and no_d: "no_dup (trail S)"
  and "finite (atms_of_mu (init_clss S))"
  shows "length (trail S) \<le> card (atms_of_mu (init_clss S))"
proof -
  obtain M N U k D where S: "state S = (M, N, U, k, D)" by (cases "state S", auto)
  have "finite (atm_of ` lits_of (trail S))"
    using assms(1,3) unfolding S by (auto simp add: finite_subset)
  have "length (trail S) = card (atm_of ` lits_of (trail S))"
    using no_dup_length_eq_card_atm_of_lits_of no_d by blast
  then show ?thesis using assms(1) unfolding no_strange_atm_def
  by (auto simp add: assms(3) card_mono)
qed

lemma cdcl\<^sub>W_cp_decreasing_measure:
  assumes cdcl\<^sub>W: "cdcl\<^sub>W_cp S T" and M_lev: "cdcl\<^sub>W_M_level_inv S"
  and alien: "no_strange_atm S"
  shows "(\<lambda>S. card (atms_of_mu (init_clss S)) - length (trail S)
      + (if conflicting S = C_True then 1 else 0)) S
    > (\<lambda>S. card (atms_of_mu (init_clss S)) - length (trail S)
      + (if conflicting S = C_True then 1 else 0)) T"
  using assms
proof -
  have "length (trail T) \<le> card (atms_of_mu (init_clss T))"
    apply (rule length_model_le_vars)
       using cdcl\<^sub>W_no_strange_atm_inv alien M_lev apply (meson cdcl\<^sub>W cdcl\<^sub>W.simps cdcl\<^sub>W_cp.cases)
      using M_lev cdcl\<^sub>W cdcl\<^sub>W_cp_consistent_inv apply blast
      using cdcl\<^sub>W by (auto simp: cdcl\<^sub>W_cp.simps)
  with assms
  show ?thesis by induction (auto split: split_if_asm)+
qed

lemma cdcl\<^sub>W_cp_wf: "wf {(b,a). (cdcl\<^sub>W_M_level_inv a \<and> no_strange_atm a)
  \<and> cdcl\<^sub>W_cp a b}"
  apply (rule wf_wf_if_measure'[of less_than _ _
      "(\<lambda>S. card (atms_of_mu (init_clss S)) - length (trail S)
        + (if conflicting S = C_True then 1 else 0))"])
    apply simp
  using cdcl\<^sub>W_cp_decreasing_measure unfolding less_than_iff by blast

lemma rtranclp_cdcl\<^sub>W_all_struct_inv_cdcl\<^sub>W_cp_iff_rtranclp_cdcl\<^sub>W_cp:
  assumes
    lev: "cdcl\<^sub>W_M_level_inv S" and
    alien: "no_strange_atm S"
  shows "(\<lambda>a b. (cdcl\<^sub>W_M_level_inv a \<and> no_strange_atm a) \<and> cdcl\<^sub>W_cp a b)\<^sup>*\<^sup>* S T
    \<longleftrightarrow> cdcl\<^sub>W_cp\<^sup>*\<^sup>* S T"
  (is "?I S T \<longleftrightarrow> ?C S T")
proof
  assume
    "?I S T"
  then show "?C S T" by induction auto
next
  assume
    "?C S T"
  then show "?I S T"
    proof induction
      case base
      then show ?case by simp
    next
      case (step T U) note st = this(1) and cp = this(2) and IH = this(3)
      have "cdcl\<^sub>W\<^sup>*\<^sup>* S T"
        by (metis rtranclp_unfold cdcl\<^sub>W_cp_conflicting_not_empty cp st
          rtranclp_propagate_is_rtranclp_cdcl\<^sub>W tranclp_cdcl\<^sub>W_cp_propagate_with_conflict_or_not)
      then have
        "cdcl\<^sub>W_M_level_inv T" and
        "no_strange_atm T"
         using \<open>cdcl\<^sub>W\<^sup>*\<^sup>* S T\<close> apply (simp add: assms(1) rtranclp_cdcl\<^sub>W_consistent_inv)
        using \<open>cdcl\<^sub>W\<^sup>*\<^sup>* S T\<close> alien rtranclp_cdcl\<^sub>W_no_strange_atm_inv lev by blast
      then have " (\<lambda>a b. (cdcl\<^sub>W_M_level_inv a \<and> no_strange_atm a)
        \<and> cdcl\<^sub>W_cp a b)\<^sup>*\<^sup>* T U"
        using cp by auto
      then show ?case using IH by auto
    qed
qed

lemma cdcl\<^sub>W_cp_normalized_element:
  assumes
    lev: "cdcl\<^sub>W_M_level_inv S" and
    "no_strange_atm S"
  obtains T where "full cdcl\<^sub>W_cp S T"
proof -
  let ?inv = "\<lambda>a. (cdcl\<^sub>W_M_level_inv a \<and> no_strange_atm a)"
  obtain T where T: "full (\<lambda>a b. ?inv a \<and> cdcl\<^sub>W_cp a b) S T"
    using cdcl\<^sub>W_cp_wf wf_exists_normal_form[of "\<lambda>a b. ?inv a \<and> cdcl\<^sub>W_cp a b"]
    unfolding full_def by blast
    then have "cdcl\<^sub>W_cp\<^sup>*\<^sup>* S T"
      using rtranclp_cdcl\<^sub>W_all_struct_inv_cdcl\<^sub>W_cp_iff_rtranclp_cdcl\<^sub>W_cp assms unfolding full_def
      by blast
    moreover
      then have "cdcl\<^sub>W\<^sup>*\<^sup>* S T"
        using rtranclp_cdcl\<^sub>W_cp_rtranclp_cdcl\<^sub>W by blast
      then have
        "cdcl\<^sub>W_M_level_inv T" and
        "no_strange_atm T"
         using \<open>cdcl\<^sub>W\<^sup>*\<^sup>* S T\<close> apply (simp add: assms(1) rtranclp_cdcl\<^sub>W_consistent_inv)
        using \<open>cdcl\<^sub>W\<^sup>*\<^sup>* S T\<close> assms(2) rtranclp_cdcl\<^sub>W_no_strange_atm_inv lev by blast
      then have "no_step cdcl\<^sub>W_cp T"
        using T unfolding full_def by auto
    ultimately show thesis using that unfolding full_def by blast
qed

lemma in_atms_of_implies_atm_of_on_atms_of_m:
  "C + {#L#} \<in># A \<Longrightarrow> x \<in> atms_of C \<Longrightarrow> x \<in> atms_of_mu A"
  by (metis add.commute atm_iff_pos_or_neg_lit atms_of_atms_of_m_mono contra_subsetD
    mem_set_mset_iff multi_member_skip)

lemma propagate_no_stange_atm:
  assumes
    "propagate S S'" and
    "no_strange_atm S"
  shows "no_strange_atm S'"
  using assms by induction
  (auto simp add: no_strange_atm_def clauses_def in_plus_implies_atm_of_on_atms_of_m
    in_atms_of_implies_atm_of_on_atms_of_m)

lemma always_exists_full_cdcl\<^sub>W_cp_step:
  assumes "no_strange_atm S"
  shows "\<exists>S''. full cdcl\<^sub>W_cp S S''"
  using assms
proof (induct "card (atms_of_mu (init_clss S) - atm_of `lits_of (trail S))" arbitrary: S)
  case 0 note card = this(1) and alien = this(2)
  then have atm: "atms_of_mu (init_clss S) = atm_of ` lits_of (trail S)"
    unfolding no_strange_atm_def by auto
  { assume a: "\<exists>S'. conflict S S'"
    then obtain S' where S': "conflict S S'" by metis
    then have "\<forall>S''. \<not>cdcl\<^sub>W_cp S' S''" by auto
    then have ?case using a S' cdcl\<^sub>W_cp.conflict' unfolding full_def by blast
  }
  moreover {
    assume a: "\<exists>S'. propagate S S'"
    then obtain S' where "propagate S S'" by blast
    then obtain M N U k C L where S: "state S = (M, N, U, k, C_True)"
    and S': "state S' = (Propagated L ( (C + {#L#})) # M, N, U, k, C_True)"
    and "C + {#L#} \<in># clauses S"
    and "M \<Turnstile>as CNot C"
    and "undefined_lit M L"
    using propagate by auto
    have "atms_of_mu U \<subseteq> atms_of_mu N" using alien S unfolding no_strange_atm_def by auto
    then have "atm_of L \<in> atms_of_mu (init_clss S)"
      using \<open>C + {#L#} \<in># clauses S\<close> S  unfolding atms_of_m_def clauses_def by force+
    then have False using \<open>undefined_lit M L\<close> S unfolding atm unfolding lits_of_def
      by (auto simp add: defined_lit_map)
  }
  ultimately show ?case by (metis cdcl\<^sub>W_cp.cases full_def rtranclp.rtrancl_refl)
next
  case (Suc n) note IH = this(1) and card = this(2) and alien = this(3)
  { assume a: "\<exists>S'. conflict S S'"
    then obtain S' where S': "conflict S S'" by metis
    then have "\<forall>S''. \<not>cdcl\<^sub>W_cp S' S''" by auto
    then have ?case  unfolding full_def Ex_def using S' cdcl\<^sub>W_cp.conflict' by blast
  }
  moreover {
    assume a: "\<exists>S'. propagate S S'"
    then obtain S' where propagate: "propagate S S'" by blast
    then obtain M N U k C L where
      S: "state S = (M, N, U, k, C_True)" and
      S': "state S' = (Propagated L ( (C + {#L#})) # M, N, U, k, C_True)" and
      "C + {#L#} \<in># clauses S" and
      "M \<Turnstile>as CNot C" and
      "undefined_lit M L"
      by fastforce
    then have "atm_of L \<notin> atm_of ` lits_of M"
      unfolding lits_of_def by (auto simp add: defined_lit_map)
    moreover
      have "no_strange_atm S'" using alien propagate propagate_no_stange_atm by blast
      then have "atm_of L \<in> atms_of_mu N" using S' unfolding no_strange_atm_def by auto
      then have "\<And>A. {atm_of L} \<subseteq> atms_of_mu N - A \<or> atm_of L \<in> A" by force
    moreover have "Suc n - card {atm_of L} = n" by simp
    moreover have "card (atms_of_mu N - atm_of ` lits_of M) = Suc n"
     using card S S' by simp
    ultimately
      have "card (atms_of_mu N - atm_of ` insert L (lits_of M)) = n"
        by (metis (no_types) Diff_insert card_Diff_subset finite.emptyI finite.insertI image_insert)
      then have "n = card (atms_of_mu (init_clss S') - atm_of ` lits_of (trail S'))"
        using card S S' by simp
    then have a1: "Ex (full cdcl\<^sub>W_cp S')" using IH \<open>no_strange_atm S'\<close>  by blast
    have ?case
      proof -
        obtain S'' :: "'st" where
          ff1: "cdcl\<^sub>W_cp\<^sup>*\<^sup>* S' S'' \<and> no_step cdcl\<^sub>W_cp S''"
          using a1 unfolding full_def by blast
        have "cdcl\<^sub>W_cp\<^sup>*\<^sup>* S S''"
          using ff1 cdcl\<^sub>W_cp.intros(2)[OF propagate]
          by (metis (no_types) converse_rtranclp_into_rtranclp)
        then have "\<exists>S''. cdcl\<^sub>W_cp\<^sup>*\<^sup>* S S'' \<and> (\<forall>S'''. \<not> cdcl\<^sub>W_cp S'' S''')"
          using ff1 by blast
        then show ?thesis unfolding full_def
          by meson
      qed
    }
  ultimately show ?case unfolding full_def by (metis cdcl\<^sub>W_cp.cases rtranclp.rtrancl_refl)
qed

subsubsection \<open>Literal of highest level in conflicting clauses\<close>
text \<open>One important property of the @{term cdcl\<^sub>W} with strategy is that, whenever a conflict takes
  place, there is at least a literal of level k involved (except if we have derived the false
  clause). The reason is that we apply conflicts before a decision is taken.\<close>
abbreviation no_clause_is_false :: "'st \<Rightarrow> bool" where
"no_clause_is_false \<equiv>
  \<lambda>S. (conflicting S = C_True \<longrightarrow> (\<forall>D \<in># clauses S. \<not>trail S \<Turnstile>as CNot D))"

abbreviation conflict_is_false_with_level :: "'st \<Rightarrow> bool" where
"conflict_is_false_with_level S' \<equiv> \<forall>D. conflicting S' = C_Clause D \<longrightarrow> D \<noteq> {#}
  \<longrightarrow> (\<exists>L \<in># D. get_level L (trail S') = backtrack_lvl S')"

lemma not_conflict_not_any_negated_init_clss:
  assumes "\<forall> S'. \<not>conflict S S'"
  shows "no_clause_is_false S"
  using assms state_eq_ref by blast

lemma full_cdcl\<^sub>W_cp_not_any_negated_init_clss:
  assumes "full cdcl\<^sub>W_cp S S'"
  shows "no_clause_is_false S'"
  using assms not_conflict_not_any_negated_init_clss unfolding full_def by blast

lemma full1_cdcl\<^sub>W_cp_not_any_negated_init_clss:
  assumes "full1 cdcl\<^sub>W_cp S S'"
  shows "no_clause_is_false S'"
  using assms not_conflict_not_any_negated_init_clss unfolding full1_def by blast

lemma cdcl\<^sub>W_stgy_not_non_negated_init_clss:
  assumes "cdcl\<^sub>W_stgy S S'"
  shows "no_clause_is_false S'"
  using assms apply (induct rule: cdcl\<^sub>W_stgy.induct)
  using full1_cdcl\<^sub>W_cp_not_any_negated_init_clss full_cdcl\<^sub>W_cp_not_any_negated_init_clss by metis+

lemma rtranclp_cdcl\<^sub>W_stgy_not_non_negated_init_clss:
  assumes "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S S'" and "no_clause_is_false S"
  shows "no_clause_is_false S'"
  using assms by (induct rule: rtranclp_induct) (auto simp: cdcl\<^sub>W_stgy_not_non_negated_init_clss)

lemma cdcl\<^sub>W_stgy_conflict_ex_lit_of_max_level:
  assumes "cdcl\<^sub>W_cp S S'"
  and "no_clause_is_false S"
  and "cdcl\<^sub>W_M_level_inv S"
  shows "conflict_is_false_with_level S'"
  using assms
proof (induct rule: cdcl\<^sub>W_cp.induct)
  case conflict'
  then show ?case by auto
next
  case propagate'
  then show ?case by auto
qed

lemma no_chained_conflict:
  assumes "conflict S S'"
  and "conflict S' S''"
  shows False
  using assms by fastforce

lemma rtranclp_cdcl\<^sub>W_cp_propa_or_propa_confl:
  assumes "cdcl\<^sub>W_cp\<^sup>*\<^sup>* S U"
  shows "propagate\<^sup>*\<^sup>* S U \<or> (\<exists>T. propagate\<^sup>*\<^sup>* S T  \<and> conflict T U)"
  using assms
proof induction
  case base
  then show ?case by auto
next
  case (step U V) note SU = this(1) and UV = this(2) and IH = this(3)
  consider (confl) T where "propagate\<^sup>*\<^sup>* S T" and "conflict T U"
    | (propa) "propagate\<^sup>*\<^sup>* S U" using IH by auto
  then show ?case
    proof cases
      case confl
      then have False using UV by auto
      then show ?thesis by fast
    next
      case propa
      also have "conflict U V \<or> propagate U V" using UV by (auto simp add: cdcl\<^sub>W_cp.simps)
      ultimately show ?thesis by force
    qed
qed

lemma rtranclp_cdcl\<^sub>W_co_conflict_ex_lit_of_max_level:
  assumes full: "full cdcl\<^sub>W_cp S U"
  and cls_f: "no_clause_is_false S"
  and "conflict_is_false_with_level S"
  and lev: "cdcl\<^sub>W_M_level_inv S"
  shows "conflict_is_false_with_level U"
proof (intro allI impI)
  fix D
  assume confl: "conflicting U = C_Clause D" and
    D: "D \<noteq> {#}"
  consider (CT) "conflicting S = C_True" | (SD) D' where "conflicting S = C_Clause D'"
    by (cases "conflicting S") auto
  then show "\<exists>L\<in>#D. get_level L (trail U) = backtrack_lvl U"
    proof cases
      case SD
      then have "S = U"
        by (metis (no_types) assms(1) cdcl\<^sub>W_cp_conflicting_not_empty full_def rtranclpD tranclpD)
      then show  ?thesis using assms(3) confl D by blast-
    next
      case CT
      have "init_clss U = init_clss S" and "learned_clss U = learned_clss S"
        using assms(1) unfolding full_def
          apply (metis (no_types) rtranclpD tranclp_cdcl\<^sub>W_cp_no_more_init_clss)
        by (metis (mono_tags, lifting) assms(1) full_def rtranclp_cdcl\<^sub>W_cp_learned_clause_inv)
      obtain T where "propagate\<^sup>*\<^sup>* S T" and TU: "conflict T U"
        proof -
          have f5: "U \<noteq> S"
            using confl CT by force
          then have "cdcl\<^sub>W_cp\<^sup>+\<^sup>+ S U"
            by (metis full full_def rtranclpD)
          have "\<And>p pa. \<not> propagate p pa \<or> conflicting pa =
            (C_True::'v literal multiset conflicting_clause)"
            by auto
          then show ?thesis
            using f5 that tranclp_cdcl\<^sub>W_cp_propagate_with_conflict_or_not[OF \<open>cdcl\<^sub>W_cp\<^sup>+\<^sup>+ S U\<close>]
            full confl CT unfolding full_def by auto
        qed
      have "init_clss T = init_clss S" and "learned_clss T = learned_clss S"
        using TU \<open>init_clss U = init_clss S\<close> \<open>learned_clss U = learned_clss S\<close> by auto
      then have "D \<in># clauses S"
        using TU confl by (fastforce simp: clauses_def)
      then have  "\<not> trail S \<Turnstile>as CNot D"
        using cls_f CT by simp
      moreover
        obtain M where tr_U: "trail U = M @ trail S" and nm: "\<forall>m\<in>set M. \<not>is_marked m"
          by (metis (mono_tags, lifting) assms(1) full_def rtranclp_cdcl\<^sub>W_cp_dropWhile_trail)
        have "trail U \<Turnstile>as CNot D"
          using TU confl by auto
      ultimately obtain L where "L \<in># D" and "-L \<in> lits_of M"
        unfolding tr_U CNot_def true_annots_def Ball_def true_annot_def true_cls_def by auto

      moreover have inv_U: "cdcl\<^sub>W_M_level_inv U"
        by (metis cdcl\<^sub>W_stgy.conflict' cdcl\<^sub>W_stgy_consistent_inv full full_unfold lev)
      moreover
        have "backtrack_lvl U = backtrack_lvl S"
          using full unfolding full_def by (auto dest: rtranclp_cdcl\<^sub>W_cp_backtrack_lvl)

      moreover
        have "no_dup (trail U)"
          using inv_U unfolding cdcl\<^sub>W_M_level_inv_def by auto
        { fix x :: "('v, nat, 'v literal multiset) marked_lit" and
            xb :: "('v, nat, 'v literal multiset) marked_lit"
          assume a1: "atm_of L = atm_of (lit_of xb)"
          moreover assume a2: "- L = lit_of x"
          moreover assume a3: "(\<lambda>l. atm_of (lit_of l)) ` set M
            \<inter> (\<lambda>l. atm_of (lit_of l)) ` set (trail S) = {}"
          moreover assume a4: "x \<in> set M"
          moreover assume a5: "xb \<in> set (trail S)"
          moreover have "atm_of (- L) = atm_of L"
            by auto
          ultimately have False
            by auto
         }
        then have LS: "atm_of L \<notin> atm_of ` lits_of (trail S)"
          using \<open>-L \<in> lits_of M\<close> \<open>no_dup (trail U)\<close> unfolding tr_U lits_of_def by auto
      ultimately have "get_level L (trail U) = backtrack_lvl U"
        proof (cases "get_all_levels_of_marked (trail S) \<noteq> []", goal_cases)
          case 2 note LD = this(1) and LM = this(2) and inv_U = this(3) and US = this(4) and
            LS = this(5) and ne = this(6)
          have "backtrack_lvl S = 0"
            using lev ne unfolding cdcl\<^sub>W_M_level_inv_def by auto
          moreover have "get_rev_level L 0 (rev M) = 0"
            using nm by auto
          ultimately show ?thesis using LS ne US unfolding tr_U
            by (simp add: get_all_levels_of_marked_nil_iff_not_is_marked lits_of_def)
        next
          case 1 note LD = this(1) and LM = this(2) and inv_U = this(3) and US = this(4) and
            LS = this(5) and ne = this(6)

          have "hd (get_all_levels_of_marked (trail S)) = backtrack_lvl S"
            using ne unfolding cdcl\<^sub>W_M_level_inv_decomp(4)[OF lev] by auto
          moreover have "atm_of L \<in> atm_of ` lits_of M "
            using \<open>-L \<in> lits_of M\<close> by (simp add: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
              lits_of_def)
          ultimately show ?thesis
            using nm ne unfolding tr_U
            using get_level_skip_beginning_hd_get_all_levels_of_marked[OF LS, of M]
               get_level_skip_in_all_not_marked[of "rev M" L "backtrack_lvl S"]
            unfolding lits_of_def US
            by auto
          qed
      then show "\<exists>L\<in>#D. get_level L (trail U) = backtrack_lvl U"
        using \<open>L \<in># D\<close> by blast
    qed
qed

subsubsection \<open>Literal of highest level in marked literals\<close>
definition mark_is_false_with_level :: "'st \<Rightarrow> bool" where
"mark_is_false_with_level S' \<equiv>
  \<forall>D M1 M2 L.  M1 @ Propagated L D # M2 = trail S' \<longrightarrow>  D - {#L#} \<noteq> {#}
    \<longrightarrow> (\<exists>L. L \<in>#  D \<and> get_level L (trail S') = get_maximum_possible_level M1)"

definition no_more_propagation_to_do:: "'st \<Rightarrow> bool" where
"no_more_propagation_to_do S \<equiv>
  \<forall>D M M' L. D + {#L#} \<in># clauses S \<longrightarrow> trail S = M' @ M \<longrightarrow> M \<Turnstile>as CNot D
    \<longrightarrow> undefined_lit M L \<longrightarrow> get_maximum_possible_level M < backtrack_lvl S
    \<longrightarrow> (\<exists>L. L \<in># D \<and> get_level L (trail S) = get_maximum_possible_level M)"

lemma propagate_no_more_propagation_to_do:
  assumes propagate: "propagate S S'"
  and H: "no_more_propagation_to_do S"
  and M: "cdcl\<^sub>W_M_level_inv S"
  shows "no_more_propagation_to_do S'"
  using assms
proof -
  obtain M N U k C L where
    S: "state S = (M, N, U, k, C_True)" and
    S': "state S' = (Propagated L ( (C + {#L#})) # M, N, U, k, C_True)" and
    "C + {#L#} \<in># clauses S" and
    "M \<Turnstile>as CNot C" and
    "undefined_lit M L"
    using propagate by auto
  let ?M' = "Propagated L ( (C + {#L#})) # M"
  show ?thesis unfolding no_more_propagation_to_do_def
    proof (intro allI impI)
      fix D M1 M2 L'
      assume D_L: "D + {#L'#} \<in># clauses S'"
      and "trail S' = M2 @ M1"
      and get_max: "get_maximum_possible_level M1 < backtrack_lvl S'"
      and "M1 \<Turnstile>as CNot D"
      and undef: "undefined_lit M1 L'"
      have "tl M2 @ M1 = trail S \<or> (M2 = [] \<and> M1 = Propagated L ( (C + {#L#})) # M)"
        using \<open>trail S' = M2 @ M1\<close> S' S by (cases M2) auto
      moreover {
        assume "tl M2 @ M1 = trail S"
        moreover have "D + {#L'#} \<in># clauses S" using D_L S S' unfolding clauses_def by auto
        moreover have "get_maximum_possible_level M1 < backtrack_lvl S"
          using get_max S S' by auto
        ultimately obtain L' where "L' \<in># D" and
          "get_level L' (trail S) = get_maximum_possible_level M1"
          using H \<open>M1 \<Turnstile>as CNot D\<close> undef unfolding no_more_propagation_to_do_def by metis
        moreover
          { have "cdcl\<^sub>W_M_level_inv S'"
              using cdcl\<^sub>W_consistent_inv[OF _ M] cdcl\<^sub>W.propagate[OF propagate] by blast
            then have "no_dup ?M'" using S' by auto
            moreover
              have "atm_of L' \<in> atm_of ` (lits_of M1)"
                using \<open>L' \<in># D\<close> \<open>M1 \<Turnstile>as CNot D\<close> by (metis atm_of_uminus image_eqI
                  in_CNot_implies_uminus(2))
              then have "atm_of L' \<in> atm_of ` (lits_of M)"
                using \<open>tl M2 @ M1 = trail S\<close> S by auto
            ultimately have "atm_of L \<noteq> atm_of L'" unfolding lits_of_def by auto
        }
        ultimately have "\<exists>L' \<in># D. get_level L' (trail S') = get_maximum_possible_level M1"
          using S S' by auto
      }
      moreover {
        assume "M2 = []" and M1: "M1 = Propagated L ( (C + {#L#})) # M"
        have "cdcl\<^sub>W_M_level_inv S'"
          using cdcl\<^sub>W_consistent_inv[OF _ M] cdcl\<^sub>W.propagate[OF propagate] by blast
        then have "get_all_levels_of_marked (trail S') = rev ([Suc 0..<(Suc 0+k)])" using S' by auto
        then have "get_maximum_possible_level M1 = backtrack_lvl S'"
          using get_maximum_possible_level_max_get_all_levels_of_marked[of M1] S' M1
          by (auto intro: Max_eqI)
        then have False using get_max by auto
      }
      ultimately show "\<exists>L. L \<in># D \<and> get_level L (trail S') = get_maximum_possible_level M1" by fast
   qed
qed

lemma conflict_no_more_propagation_to_do:
  assumes conflict: "conflict S S'"
  and H: "no_more_propagation_to_do S"
  and M: "cdcl\<^sub>W_M_level_inv S"
  shows "no_more_propagation_to_do S'"
  using assms unfolding no_more_propagation_to_do_def conflict.simps by force

lemma cdcl\<^sub>W_cp_no_more_propagation_to_do:
  assumes conflict: "cdcl\<^sub>W_cp S S'"
  and H: "no_more_propagation_to_do S"
  and M: "cdcl\<^sub>W_M_level_inv S"
  shows "no_more_propagation_to_do S'"
  using assms
  proof (induct rule: cdcl\<^sub>W_cp.induct)
  case (conflict' S S')
  then show ?case using conflict_no_more_propagation_to_do[of S S'] by blast
next
  case (propagate' S S') note S = this
  show 1: "no_more_propagation_to_do S'"
    using propagate_no_more_propagation_to_do[of S S']  S by blast
qed

lemma cdcl\<^sub>W_then_exists_cdcl\<^sub>W_stgy_step:
  assumes
    o: "cdcl\<^sub>W_o S S'" and
    alien: "no_strange_atm S" and
    lev: "cdcl\<^sub>W_M_level_inv S"
  shows "\<exists>S'. cdcl\<^sub>W_stgy S S'"
proof -
  obtain S'' where "full cdcl\<^sub>W_cp S' S''"
    using always_exists_full_cdcl\<^sub>W_cp_step alien cdcl\<^sub>W_no_strange_atm_inv cdcl\<^sub>W_o_no_more_init_clss
     o other lev by (meson cdcl\<^sub>W_consistent_inv)
  then show ?thesis
    using assms by (metis always_exists_full_cdcl\<^sub>W_cp_step cdcl\<^sub>W_stgy.conflict' full_unfold other')
qed

lemma backtrack_no_decomp:
  assumes S: "state S = (M, N, U, k, C_Clause (D + {#L#}))"
  and L: "get_level L M = k"
  and D: "get_maximum_level D M < k"
  and M_L: "cdcl\<^sub>W_M_level_inv S"
  shows "\<exists>S'. cdcl\<^sub>W_o S S'"
proof -
  have L_D: "get_level L M = get_maximum_level (D + {#L#}) M"
    using L D by (simp add: get_maximum_level_plus)
  let ?i = "get_maximum_level D M"
  obtain K M1 M2 where K: "(Marked K (?i + 1) # M1, M2) \<in> set (get_all_marked_decomposition M)"
    using backtrack_ex_decomp[OF M_L, of ?i] D S by auto
  show ?thesis using backtrack_rule[OF S K L L_D] by (meson bj cdcl\<^sub>W_bj.simps state_eq_ref)
qed

lemma cdcl\<^sub>W_stgy_final_state_conclusive:
  assumes termi: "\<forall>S'. \<not>cdcl\<^sub>W_stgy S S'"
  and decomp: "all_decomposition_implies_m (init_clss S) (get_all_marked_decomposition (trail S))"
  and learned: "cdcl\<^sub>W_learned_clause S"
  and level_inv: "cdcl\<^sub>W_M_level_inv S"
  and alien: "no_strange_atm S"
  and no_dup: "distinct_cdcl\<^sub>W_state S"
  and confl: "cdcl\<^sub>W_conflicting S"
  and confl_k: "conflict_is_false_with_level S"
  shows "(conflicting S = C_Clause {#} \<and> unsatisfiable (set_mset (init_clss S)))
         \<or> (conflicting S = C_True \<and> trail S \<Turnstile>as set_mset (init_clss S))"
proof -
  let ?M = "trail S"
  let ?N = "init_clss S"
  let ?k = "backtrack_lvl S"
  let ?U = "learned_clss S"
  have "conflicting S = C_Clause {#}
        \<or> conflicting S = C_True
        \<or> (\<exists>D L. conflicting S = C_Clause (D + {#L#}))"
    apply (case_tac "conflicting S", auto)
    by (case_tac x2, auto)
  moreover {
    assume "conflicting S = C_Clause {#}"
    then have "unsatisfiable (set_mset (init_clss S))"
      using assms(3) unfolding cdcl\<^sub>W_learned_clause_def true_clss_cls_def
      by (metis (no_types, lifting) Un_insert_right atms_of_empty satisfiable_def
        sup_bot.right_neutral total_over_m_insert total_over_set_empty true_cls_empty)
  }
  moreover {
    assume "conflicting S = C_True"
    { assume "\<not>?M \<Turnstile>asm ?N"
      have "atm_of ` (lits_of ?M) = atms_of_mu ?N" (is "?A = ?B")
        proof
          show "?A \<subseteq> ?B" using alien unfolding no_strange_atm_def by auto
          show "?B \<subseteq> ?A"
            proof (rule ccontr)
              assume "\<not>?B \<subseteq> ?A"
              then obtain l where "l \<in> ?B" and "l \<notin> ?A" by auto
              then have "undefined_lit ?M (Pos l)"
                using \<open>l \<notin> ?A\<close> unfolding lits_of_def by (auto simp add: defined_lit_map)
              then have "\<exists>S'. cdcl\<^sub>W_o S S'"
                using cdcl\<^sub>W_o.decide decide.intros \<open>l \<in> ?B\<close> no_strange_atm_def
                by (metis \<open>conflicting S = C_True\<close> literal.sel(1) state_eq_def)
              then show False
                using termi cdcl\<^sub>W_then_exists_cdcl\<^sub>W_stgy_step[OF _ alien]  level_inv by blast
            qed
          qed
        obtain D where "\<not> ?M \<Turnstile>a D" and "D \<in># ?N"
           using \<open>\<not>?M \<Turnstile>asm ?N\<close> unfolding lits_of_def true_annots_def Ball_def by auto
        have "atms_of D \<subseteq> atm_of ` (lits_of ?M)"
          using \<open>D \<in># ?N\<close> unfolding \<open>atm_of ` (lits_of ?M) = atms_of_mu ?N\<close> atms_of_m_def
          by (auto simp add: atms_of_def)
        then have a1: "atm_of ` set_mset D \<subseteq> atm_of ` lits_of (trail S)"
          by (auto simp add: atms_of_def lits_of_def)
        have "total_over_m (lits_of ?M) {D}"
          using \<open>atms_of D \<subseteq> atm_of ` (lits_of ?M)\<close> atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
          by (fastforce simp: total_over_set_def)
        then have "?M \<Turnstile>as CNot D"
          using total_not_true_cls_true_clss_CNot  \<open>\<not> trail S \<Turnstile>a D\<close> true_annot_def
          true_annots_true_cls by fastforce
        then have False
          proof -
            obtain S' where
              f2: "full cdcl\<^sub>W_cp S S'"
              by (meson alien always_exists_full_cdcl\<^sub>W_cp_step level_inv)
            then have "S' = S"
              using cdcl\<^sub>W_stgy.conflict'[of S] by (metis (no_types) full_unfold termi)
            then show ?thesis
              using f2 \<open>D \<in># init_clss S\<close> \<open>conflicting S = C_True\<close> \<open>trail S \<Turnstile>as CNot D\<close>
              clauses_def full_cdcl\<^sub>W_cp_not_any_negated_init_clss by auto
          qed
    }
    then have "?M \<Turnstile>asm ?N" by blast
  }
  moreover {
    assume "\<exists>D L. conflicting S = C_Clause (D + {#L#})"
    obtain D L where LD: "conflicting S = C_Clause (D + {#L#})" and "get_level L ?M = ?k"
      proof -
        obtain mm :: "'v literal multiset" and ll :: "'v literal" where
          f2: "conflicting S = C_Clause (mm + {#ll#})"
          using \<open>\<exists>D L. conflicting S = C_Clause (D + {#L#})\<close> by force
        have "\<forall>m. (conflicting S \<noteq> C_Clause m \<or> m = {#})
          \<or> (\<exists>l. l \<in># m \<and> get_level l (trail S) = backtrack_lvl S)"
          using confl_k by blast
        then show ?thesis
          using f2 that by (metis (no_types) multi_member_split single_not_empty union_eq_empty)
      qed
    let ?D = "D + {#L#}"
    have "?D \<noteq> {#}" by auto
    have "?M \<Turnstile>as CNot ?D" using confl LD unfolding cdcl\<^sub>W_conflicting_def by auto
    then have "?M \<noteq> []" unfolding true_annots_def Ball_def true_annot_def true_cls_def by force
    { have M: "?M = hd ?M # tl ?M" using \<open>?M \<noteq> []\<close> list.collapse by fastforce
      assume marked: "is_marked (hd ?M)"
      then obtain k' where k': "k' + 1 = ?k"
        using level_inv M unfolding cdcl\<^sub>W_M_level_inv_def
        by (cases "hd (trail S)"; cases "trail S") auto
      obtain L' l' where L': "hd ?M = Marked L' l'" using marked by (case_tac "hd ?M") auto
      have "get_all_levels_of_marked (hd (trail S) # tl (trail S))
        = rev [1..<1 + length (get_all_levels_of_marked ?M)]"
        using level_inv \<open>get_level L ?M = ?k\<close> M unfolding cdcl\<^sub>W_M_level_inv_def M[symmetric]
        by blast
      then have l'_tl: "l' # get_all_levels_of_marked (tl ?M)
        = rev [1..<1 + length (get_all_levels_of_marked ?M)]" unfolding L' by simp
      moreover have "\<dots> = length (get_all_levels_of_marked ?M)
        # rev [1..<length (get_all_levels_of_marked ?M)]"
        using M Suc_le_mono calculation by (fastforce simp add: upt.simps(2))
      finally have
        "l' = ?k" and
        g_r: "get_all_levels_of_marked (tl (trail S))
          = rev [1..<length (get_all_levels_of_marked (trail S))]"
        using level_inv \<open>get_level L ?M = ?k\<close> M unfolding cdcl\<^sub>W_M_level_inv_def by auto
      have *: "\<And>list. no_dup list \<Longrightarrow>
            - L \<in> lits_of list \<Longrightarrow> atm_of L \<in> atm_of ` lits_of list"
        by (metis atm_of_uminus imageI)
      have "L' = -L"
        proof (rule ccontr)
          assume "\<not> ?thesis"
          moreover have "-L \<in> lits_of ?M" using confl LD unfolding cdcl\<^sub>W_conflicting_def by auto
          ultimately have "get_level L (hd (trail S) # tl (trail S)) = get_level L (tl ?M)"
            using cdcl\<^sub>W_M_level_inv_decomp(1)[OF level_inv] unfolding L' consistent_interp_def
            by (metis (no_types, lifting) L' M atm_of_eq_atm_of get_level_skip_beginning insert_iff
              lits_of_cons marked_lit.sel(1))

          moreover
            have "length (get_all_levels_of_marked (trail S)) = ?k"
              using level_inv unfolding cdcl\<^sub>W_M_level_inv_def by auto
            then have "Max (set (0#get_all_levels_of_marked (tl (trail S)))) = ?k - 1"
              unfolding g_r by (auto simp add: Max_n_upt)
            then have "get_level L (tl ?M) < ?k"
              using get_maximum_possible_level_ge_get_level[of L "tl ?M"]
              by (metis One_nat_def add.right_neutral add_Suc_right diff_add_inverse2
                get_maximum_possible_level_max_get_all_levels_of_marked k' le_imp_less_Suc
                list.simps(15))
          finally show False using \<open>get_level L ?M = ?k\<close> M by auto
        qed
      have L: "hd ?M = Marked (-L) ?k"  using \<open>l' = ?k\<close> \<open>L' = -L\<close> L' by auto

      have g_a_l: "get_all_levels_of_marked ?M = rev [1..<1 + ?k]"
        using level_inv \<open>get_level L ?M = ?k\<close> M unfolding cdcl\<^sub>W_M_level_inv_def by auto
      have g_k: "get_maximum_level D (trail S) \<le> ?k"
        using get_maximum_possible_level_ge_get_maximum_level[of D ?M]
          get_maximum_possible_level_max_get_all_levels_of_marked[of ?M]
        by (auto simp add: Max_n_upt g_a_l)
      have "get_maximum_level D (trail S) < ?k"
        proof (rule ccontr)
          assume "\<not> ?thesis"
          then have "get_maximum_level D (trail S) = ?k" using M g_k unfolding L by auto
          then obtain L' where "L' \<in># D" and L_k: "get_level L' ?M = ?k"
            using get_maximum_level_exists_lit[of ?k D ?M] unfolding k'[symmetric] by auto
          have "L \<noteq> L'" using no_dup  \<open>L' \<in># D\<close>
            unfolding distinct_cdcl\<^sub>W_state_def LD by (metis add.commute add_eq_self_zero
              count_single count_union less_not_refl3 distinct_mset_def union_single_eq_member)
          have "L' = -L"
            proof (rule ccontr)
              assume "\<not> ?thesis"
              then have "get_level L' ?M = get_level L' (tl ?M)"
                using M \<open>L \<noteq> L'\<close> get_level_skip_beginning[of L' "hd ?M" "tl ?M"] unfolding L
                by (auto simp add: atm_of_eq_atm_of)
              moreover have "\<dots> < ?k"
                using level_inv g_r get_rev_level_less_max_get_all_levels_of_marked[of L' 0
                  "rev (tl ?M)"] L_k l'_tl calculation g_a_l
                by (auto simp add: Max_n_upt cdcl\<^sub>W_M_level_inv_def)
              finally show False using L_k by simp
            qed
          then have taut: "tautology (D + {#L#})"
            using \<open>L' \<in># D\<close> by (metis add.commute mset_leD mset_le_add_left multi_member_this
              tautology_minus)
          have "consistent_interp (lits_of ?M)" using level_inv by auto
          then have "\<not>?M \<Turnstile>as CNot ?D"
            using taut by (metis (no_types) \<open>L' = - L\<close> \<open>L' \<in># D\<close> add.commute consistent_interp_def
              in_CNot_implies_uminus(2) mset_leD mset_le_add_left multi_member_this)
          moreover have "?M \<Turnstile>as CNot ?D"
            using confl no_dup LD unfolding cdcl\<^sub>W_conflicting_def by auto
          ultimately show False by blast
        qed
      then have False
        using backtrack_no_decomp[OF _ \<open>get_level L (trail S) = backtrack_lvl S\<close> _ level_inv]
        LD  alien termi by (metis cdcl\<^sub>W_then_exists_cdcl\<^sub>W_stgy_step level_inv)
    }
    moreover {
      assume "\<not>is_marked (hd ?M)"
      then obtain L' C where L'C: "hd ?M = Propagated L' C" by (case_tac "hd ?M", auto)
      then have M: "?M = Propagated L' C # tl ?M" using \<open>?M \<noteq> []\<close>  list.collapse by fastforce
      then obtain C' where C': " C = C' + {#L'#}"
        using confl unfolding cdcl\<^sub>W_conflicting_def by (metis append_Nil diff_single_eq_union)
      { assume "-L' \<notin># ?D"
        then have False
          using bj[OF cdcl\<^sub>W_bj.skip[OF skip_rule[OF _ \<open>-L' \<notin># ?D\<close> \<open>?D \<noteq> {#}\<close>, of S C "tl (trail S)" _
            ]]]
          termi M by (metis LD alien cdcl\<^sub>W_then_exists_cdcl\<^sub>W_stgy_step state_eq_def level_inv)
      }
      moreover {
        assume "-L' \<in># ?D"
        then obtain D' where D': "?D = D' + {#-L'#}" by (metis insert_DiffM2)
        have g_r: "get_all_levels_of_marked (Propagated L' C # tl (trail S))
          = rev [Suc 0..<Suc (length (get_all_levels_of_marked (trail S)))]"
          using level_inv M unfolding cdcl\<^sub>W_M_level_inv_def by auto
        have "Max (insert 0 (set (get_all_levels_of_marked (Propagated L' C # tl (trail S))))) = ?k"
          using level_inv M unfolding g_r by (auto simp add:Max_n_upt)
        then have "get_maximum_level D' (Propagated L' C # tl ?M) \<le> ?k"
          using get_maximum_possible_level_ge_get_maximum_level[of D' "Propagated L' C # tl ?M"]
          unfolding get_maximum_possible_level_max_get_all_levels_of_marked by auto
        then have "get_maximum_level D' (Propagated L' C # tl ?M) = ?k
          \<or> get_maximum_level D' (Propagated L' C # tl ?M) < ?k"
          using le_neq_implies_less by blast
        moreover {
          assume g_D'_k: "get_maximum_level D' (Propagated L' C # tl ?M) = ?k"
          have False
            proof -
              have f1: "get_maximum_level D' (trail S) = backtrack_lvl S"
                using M g_D'_k by auto
              have "(trail S, init_clss S, learned_clss S, backtrack_lvl S, C_Clause (D + {#L#}))
                = state S"
                by (metis (no_types) LD)
              then have "cdcl\<^sub>W_o S (update_conflicting (C_Clause (D' #\<union> C')) (tl_trail S))"
                using f1 bj[OF cdcl\<^sub>W_bj.resolve[OF resolve_rule[of S L' C' "tl ?M" ?N ?U ?k D']]]
                C' D' M by (metis state_eq_def)
              then show ?thesis
                by (meson alien cdcl\<^sub>W_then_exists_cdcl\<^sub>W_stgy_step termi level_inv)
            qed
        }
        moreover {
          assume "get_maximum_level D' (Propagated L' C # tl ?M) < ?k"
          then have False
            proof -
              assume a1: "get_maximum_level D' (Propagated L' C # tl (trail S)) < backtrack_lvl S"
              obtain mm :: "'v literal multiset" and ll :: "'v literal" where
                f2: "conflicting S = C_Clause (mm + {#ll#})"
                    "get_level ll (trail S) = backtrack_lvl S"
                using LD \<open>get_level L (trail S) = backtrack_lvl S\<close> by blast
              then have f3: "get_maximum_level D' (trail S) \<le> get_level ll (trail S)"
                using M a1 by force
              have "get_level ll (trail S) \<noteq> get_maximum_level D' (trail S)"
                using f2 M calculation(2) by presburger
              have f1: "trail S = Propagated L' C # tl (trail S)"
                  "conflicting S = C_Clause (D' + {#- L'#})"
                using D' LD M by force+
              have f2: "conflicting S = C_Clause (mm + {#ll#}) "
                 "get_level ll (trail S) = backtrack_lvl S"
                using f2 by force+
              have "ll = - L'"
                by (metis (no_types) D' LD \<open>get_level ll (trail S) \<noteq> get_maximum_level D' (trail S)\<close>
                  conflicting_clause.inject f2 f3 get_maximum_level_ge_get_level insert_noteq_member
                  le_antisym)
              then show ?thesis
                using f2 f1 M backtrack_no_decomp[of S]
                by (metis (no_types) a1 alien cdcl\<^sub>W_then_exists_cdcl\<^sub>W_stgy_step level_inv termi)
            qed
        }
        ultimately have False by blast
      }
      ultimately have False by blast
    }
    ultimately have False by blast
  }
  ultimately show ?thesis by blast
qed

lemma cdcl\<^sub>W_cp_tranclp_cdcl\<^sub>W:
   "cdcl\<^sub>W_cp S S' \<Longrightarrow> cdcl\<^sub>W\<^sup>+\<^sup>+ S S'"
   apply (induct rule: cdcl\<^sub>W_cp.induct)
   by (meson cdcl\<^sub>W.conflict cdcl\<^sub>W.propagate tranclp.r_into_trancl tranclp.trancl_into_trancl)+

lemma tranclp_cdcl\<^sub>W_cp_tranclp_cdcl\<^sub>W:
   "cdcl\<^sub>W_cp\<^sup>+\<^sup>+ S S' \<Longrightarrow> cdcl\<^sub>W\<^sup>+\<^sup>+ S S'"
   apply (induct rule: tranclp.induct)
    apply (simp add: cdcl\<^sub>W_cp_tranclp_cdcl\<^sub>W)
    by (meson cdcl\<^sub>W_cp_tranclp_cdcl\<^sub>W tranclp_trans)

lemma cdcl\<^sub>W_stgy_tranclp_cdcl\<^sub>W:
   "cdcl\<^sub>W_stgy S S' \<Longrightarrow> cdcl\<^sub>W\<^sup>+\<^sup>+ S S'"
proof (induct rule: cdcl\<^sub>W_stgy.induct)
  case conflict'
  then show ?case
   unfolding full1_def by (simp add: tranclp_cdcl\<^sub>W_cp_tranclp_cdcl\<^sub>W)
next
  case (other' S  S' S'')
  then have "S' = S'' \<or> cdcl\<^sub>W_cp\<^sup>+\<^sup>+ S' S''"
    by (simp add: rtranclp_unfold full_def)
  then show ?case
    using other' by (meson cdcl\<^sub>W_ops.other cdcl\<^sub>W_ops_axioms tranclp.r_into_trancl
      tranclp_cdcl\<^sub>W_cp_tranclp_cdcl\<^sub>W tranclp_trans)
qed

lemma tranclp_cdcl\<^sub>W_stgy_tranclp_cdcl\<^sub>W:
   "cdcl\<^sub>W_stgy\<^sup>+\<^sup>+ S S' \<Longrightarrow> cdcl\<^sub>W\<^sup>+\<^sup>+ S S'"
   apply (induct rule: tranclp.induct)
   using cdcl\<^sub>W_stgy_tranclp_cdcl\<^sub>W apply blast
   by (meson cdcl\<^sub>W_stgy_tranclp_cdcl\<^sub>W tranclp_trans)

lemma rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W:
   "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S S' \<Longrightarrow> cdcl\<^sub>W\<^sup>*\<^sup>* S S'"
  using rtranclp_unfold[of cdcl\<^sub>W_stgy S S'] tranclp_cdcl\<^sub>W_stgy_tranclp_cdcl\<^sub>W[of S S'] by auto

lemma cdcl\<^sub>W_o_conflict_is_false_with_level_inv:
  assumes
    "cdcl\<^sub>W_o S S'" and
    lev: "cdcl\<^sub>W_M_level_inv S" and
    confl_inv: "conflict_is_false_with_level S" and
    n_d: "distinct_cdcl\<^sub>W_state S" and
    conflicting: "cdcl\<^sub>W_conflicting S"
  shows "conflict_is_false_with_level S'"
  using assms(1,2)
proof (induct rule: cdcl\<^sub>W_o_induct_lev2)
  case (resolve L C M D T) note tr_S = this(1) and confl = this(2) and T = this(4)
  have "-L \<notin># D" using n_d confl unfolding distinct_cdcl\<^sub>W_state_def distinct_mset_def by auto
  moreover have "L \<notin># D"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      moreover have "Propagated L (C + {#L#}) # M \<Turnstile>as CNot D"
        using conflicting confl tr_S unfolding cdcl\<^sub>W_conflicting_def by auto
      ultimately have "-L \<in> lits_of (Propagated L ( (C + {#L#})) # M)"
        using in_CNot_implies_uminus(2) by blast
      moreover have "no_dup (Propagated L ( (C + {#L#})) # M)"
        using lev tr_S unfolding cdcl\<^sub>W_M_level_inv_def by auto
      ultimately show False unfolding lits_of_def by (metis consistent_interp_def image_eqI
        list.set_intros(1) lits_of_def marked_lit.sel(2) distinctconsistent_interp)
    qed

  ultimately
    have g_D: "get_maximum_level D (Propagated L ( (C + {#L#})) # M)
      = get_maximum_level D M"
    proof -
      have "\<forall>a f L. ((a::'v) \<in> f ` L) = (\<exists>l. (l::'v literal) \<in> L \<and> a = f l)"
        by blast
      then show ?thesis
        using get_maximum_level_skip_first[of L D " (C + {#L#})" M] unfolding atms_of_def
        by (metis (no_types) \<open>- L \<notin># D\<close> \<open>L \<notin># D\<close> atm_of_eq_atm_of mem_set_mset_iff)
    qed
  { assume
      "get_maximum_level D (Propagated L ( (C + {#L#})) # M) = backtrack_lvl S" and
      "backtrack_lvl S > 0"
    then have D: "get_maximum_level D M = backtrack_lvl S" unfolding g_D by blast
    then have ?case
      using tr_S \<open>backtrack_lvl S > 0\<close> get_maximum_level_exists_lit[of "backtrack_lvl S" D M] T
      by auto
  }
  moreover {
    assume [simp]: "backtrack_lvl S = 0"
    have "\<And>L. get_level L M = 0"
      proof -
        fix L
        have "atm_of L \<notin> atm_of ` (lits_of M) \<Longrightarrow> get_level L M = 0" by auto
        moreover {
          assume "atm_of L \<in> atm_of ` (lits_of M)"
          have g_r: "get_all_levels_of_marked M = rev [Suc 0..<Suc (backtrack_lvl S)]"
            using lev tr_S unfolding cdcl\<^sub>W_M_level_inv_def by auto
          have "Max (insert 0 (set (get_all_levels_of_marked M))) = (backtrack_lvl S)"
            unfolding g_r by (simp add: Max_n_upt)
          then have "get_level L M = 0"
            using get_maximum_possible_level_ge_get_level[of L M]
            unfolding get_maximum_possible_level_max_get_all_levels_of_marked by auto
        }
        ultimately show "get_level L M = 0" by blast
      qed
    then have ?case using get_maximum_level_exists_lit_of_max_level[of "D#\<union>C" M] tr_S T
      by (auto simp: Bex_mset_def)
  }
  ultimately show ?case using resolve.hyps(3) by blast
next
  case (skip L C' M D T) note tr_S = this(1) and D = this(2) and T =this(5)
  then obtain La where "La \<in># D" and "get_level La (Propagated L C' # M) = backtrack_lvl S"
    using skip confl_inv by auto
  moreover
    have "atm_of La \<noteq> atm_of L"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then have La: "La = L" using \<open>La \<in># D\<close> \<open>- L \<notin># D\<close> by (auto simp add: atm_of_eq_atm_of)
        have "Propagated L C' # M \<Turnstile>as CNot D"
          using conflicting tr_S D unfolding cdcl\<^sub>W_conflicting_def by auto
        then have "-L \<in> lits_of M"
          using \<open>La \<in># D\<close> in_CNot_implies_uminus(2)[of D L "Propagated L C' # M"] unfolding La
          by auto
        then show False using lev tr_S unfolding cdcl\<^sub>W_M_level_inv_def consistent_interp_def by auto
      qed
    then have "get_level La (Propagated L C' # M) = get_level La M"  by auto
  ultimately show ?case using D tr_S T by auto
qed (auto split: split_if_asm)

subsubsection \<open>Strong completeness\<close>
lemma cdcl\<^sub>W_cp_propagate_confl:
  assumes "cdcl\<^sub>W_cp S T"
  shows "propagate\<^sup>*\<^sup>* S T \<or> (\<exists>S'. propagate\<^sup>*\<^sup>* S S' \<and> conflict S' T)"
  using assms by induction blast+

lemma rtranclp_cdcl\<^sub>W_cp_propagate_confl:
  assumes "cdcl\<^sub>W_cp\<^sup>*\<^sup>* S T"
  shows "propagate\<^sup>*\<^sup>* S T \<or> (\<exists>S'. propagate\<^sup>*\<^sup>* S S' \<and> conflict S' T)"
  by (simp add: assms rtranclp_cdcl\<^sub>W_cp_propa_or_propa_confl)

lemma cdcl\<^sub>W_cp_propagate_completeness:
  assumes MN: "set M \<Turnstile>s set_mset N" and
  cons: "consistent_interp (set M)" and
  tot: "total_over_m (set M) (set_mset N)" and
  "lits_of (trail S) \<subseteq> set M" and
  "init_clss S = N" and
  "propagate\<^sup>*\<^sup>* S S'" and
  "learned_clss S = {#}"
  shows "length (trail S) \<le> length (trail S') \<and> lits_of (trail S') \<subseteq> set M"
  using assms(6,4,5,7)
proof (induction rule: rtranclp.induct)
  case rtrancl_refl
  then show ?case by auto
next
  case (rtrancl_into_rtrancl X Y Z)
  note st = this(1) and propa = this(2) and IH = this(3) and lits' = this(4) and NS = this(5) and
    learned = this(6)
  then have len: "length (trail X) \<le> length (trail Y)" and LM: "lits_of (trail Y) \<subseteq> set M"
     by blast+

  obtain M' N' U k C L where
    Y: "state Y = (M', N', U, k, C_True)" and
    Z: "state Z = (Propagated L (C + {#L#}) # M', N', U, k, C_True)" and
    C: "C + {#L#} \<in># clauses Y" and
    M'_C: "M' \<Turnstile>as CNot C" and
    "undefined_lit (trail Y) L"
    using propa by auto
  have "init_clss X = init_clss Y"
    using st by induction auto
  then have [simp]: "N' = N" using NS Y Z by simp
  have "learned_clss Y = {#}"
    using st learned by induction auto
  then have [simp]: "U = {#}" using Y by auto
  have "set M \<Turnstile>s CNot C"
    using M'_C LM Y unfolding true_annots_def Ball_def true_annot_def true_clss_def true_cls_def
    by force
  moreover
    have "set M \<Turnstile> C + {#L#}"
      using MN C learned Y unfolding true_clss_def clauses_def
      by (metis NS \<open>init_clss X = init_clss Y\<close> \<open>learned_clss Y = {#}\<close> add.right_neutral
        mem_set_mset_iff)
  ultimately have "L \<in> set M" by (simp add: cons consistent_CNot_not)
  then show ?case using LM len Y Z by auto
qed

lemma completeness_is_a_full1_propagation:
  fixes S :: "'st" and M :: "'v literal list"
  assumes MN: "set M \<Turnstile>s set_mset N"
  and cons: "consistent_interp (set M)"
  and tot: "total_over_m (set M) (set_mset N)"
  and alien: "no_strange_atm S"
  and learned: "learned_clss S = {#}"
  and clsS[simp]: "init_clss S = N"
  and lits: "lits_of (trail S) \<subseteq> set M"
  shows "\<exists>S'. propagate\<^sup>*\<^sup>* S S' \<and> full cdcl\<^sub>W_cp S S'"
proof -
  obtain S' where full: "full cdcl\<^sub>W_cp S S'"
    using always_exists_full_cdcl\<^sub>W_cp_step alien by blast
  then consider (propa) "propagate\<^sup>*\<^sup>* S S'"
    | (confl) "\<exists>X. propagate\<^sup>*\<^sup>* S X \<and> conflict X S'"
    using rtranclp_cdcl\<^sub>W_cp_propagate_confl unfolding full_def by blast
  then show ?thesis
    proof cases
      case propa then show ?thesis using full by blast
    next
      case confl
      then obtain X where
        X: "propagate\<^sup>*\<^sup>* S X" and
        Xconf: "conflict X S'"
      by blast
      have clsX: "init_clss X = init_clss S"
        using X  by induction auto
      have learnedX: "learned_clss X = {#}" using X learned by induction auto
      obtain E where
        E: "E \<in># init_clss X + learned_clss X" and
        Not_E: "trail X \<Turnstile>as CNot E"
        using Xconf by (auto simp add: conflict.simps clauses_def)
      have "lits_of (trail X) \<subseteq> set M"
        using cdcl\<^sub>W_cp_propagate_completeness[OF assms(1-3) lits _ X learned] learned by auto
      then have MNE: "set M \<Turnstile>s CNot E"
        using Not_E
        by (fastforce simp add: true_annots_def true_annot_def true_clss_def true_cls_def)
      have "\<not> set M \<Turnstile>s set_mset N"
         using E consistent_CNot_not[OF cons MNE]
         unfolding learnedX true_clss_def unfolding clsX clsS by auto
      then show ?thesis using MN by blast
    qed
qed

text \<open>See also @{thm rtranclp_cdcl\<^sub>W_cp_dropWhile_trail}\<close>
lemma rtranclp_propagate_is_trail_append:
  "propagate\<^sup>*\<^sup>* S T \<Longrightarrow> \<exists>c. trail T = c @ trail S"
  by (induction rule: rtranclp_induct) auto

lemma rtranclp_propagate_is_update_trail:
  "propagate\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W_M_level_inv S \<Longrightarrow> T \<sim> delete_trail_and_rebuild (trail T) S"
proof (induction rule: rtranclp_induct)
  case base
  then show ?case unfolding state_eq_def by auto
next
  case (step T U) note IH=this(3)[OF this(4)]
  moreover have "cdcl\<^sub>W_M_level_inv U"
    using rtranclp_cdcl\<^sub>W_consistent_inv \<open>propagate\<^sup>*\<^sup>* S T\<close> \<open>propagate T U\<close>
    rtranclp_mono[of propagate cdcl\<^sub>W] cdcl\<^sub>W_cp_consistent_inv propagate'
    rtranclp_propagate_is_rtranclp_cdcl\<^sub>W step.prems by blast
    then have "no_dup (trail U)" unfolding cdcl\<^sub>W_M_level_inv_def by auto
  ultimately show ?case using \<open>propagate T U\<close> unfolding state_eq_def by fastforce
qed

lemma cdcl\<^sub>W_stgy_strong_completeness_n:
  assumes
    MN: "set M \<Turnstile>s set_mset N" and
    cons: "consistent_interp (set M)" and
    tot: "total_over_m (set M) (set_mset N)" and
    atm_incl: "atm_of ` (set M) \<subseteq> atms_of_mu N" and
    distM: "distinct M" and
    length: "n \<le> length M"
  shows
    "\<exists>M' k S. length M' \<ge> n \<and>
      lits_of M' \<subseteq> set M \<and>
      no_dup M' \<and>
      S \<sim> update_backtrack_lvl k (append_trail (rev M') (init_state N)) \<and>
      cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) S"
  using length
proof (induction n)
  case 0
  have "update_backtrack_lvl 0 (append_trail (rev []) (init_state N)) \<sim> init_state N"
    by (auto simp: state_eq_def simp del: state_simp)
  moreover have
    "0 \<le> length []" and
    "lits_of [] \<subseteq> set M" and
    "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) (init_state N)"
    and "no_dup []"
    by (auto simp: state_eq_def simp del: state_simp)
  ultimately show ?case using state_eq_sym by blast
next
  case (Suc n) note IH = this(1) and n = this(2)
  then obtain M' k S where
    l_M': "length M' \<ge> n" and
    M': "lits_of M' \<subseteq> set M" and
    n_d[simp]: "no_dup M'" and
    S: "S \<sim> update_backtrack_lvl k (append_trail (rev M') (init_state N))" and
    st: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) S"
    by auto
  have
    M: "cdcl\<^sub>W_M_level_inv S" and
    alien: "no_strange_atm S"
      using rtranclp_cdcl\<^sub>W_consistent_inv[OF rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W[OF st]]
      rtranclp_cdcl\<^sub>W_no_strange_atm_inv[OF rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W[OF st]]
      S unfolding state_eq_def cdcl\<^sub>W_M_level_inv_def no_strange_atm_def by auto
  { assume no_step: "\<not>no_step propagate S"

    obtain S' where S': "propagate\<^sup>*\<^sup>* S S'" and full: "full cdcl\<^sub>W_cp S S'"
      using completeness_is_a_full1_propagation[OF assms(1-3), of S] alien M' S by auto
    have lev: "cdcl\<^sub>W_M_level_inv S'"
      using M S' rtranclp_cdcl\<^sub>W_consistent_inv rtranclp_propagate_is_rtranclp_cdcl\<^sub>W by blast
    then have n_d'[simp]: "no_dup (trail S')"
      unfolding cdcl\<^sub>W_M_level_inv_def by auto
    have "length (trail S) \<le> length (trail S') \<and> lits_of (trail S') \<subseteq> set M"
      using S' full cdcl\<^sub>W_cp_propagate_completeness[OF assms(1-3), of S] M' S by auto
    moreover
      have full: "full1 cdcl\<^sub>W_cp S S'"
        using full no_step no_step_cdcl\<^sub>W_cp_no_conflict_no_propagate(2) unfolding full1_def full_def
        rtranclp_unfold by blast
      then have "cdcl\<^sub>W_stgy S S'" by (simp add: cdcl\<^sub>W_stgy.conflict')
    moreover
      have propa: "propagate\<^sup>+\<^sup>+ S S'" using S' full unfolding full1_def by (metis rtranclpD tranclpD)
      have "trail S = M'" using S by auto
      with propa have "length (trail S') > n"
        using l_M' propa by (induction rule: tranclp.induct) auto
    moreover
      have stS': "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) S'"
        using st cdcl\<^sub>W_stgy.conflict'[OF full] by auto
      then have "init_clss S' = N" using stS' rtranclp_cdcl\<^sub>W_stgy_no_more_init_clss by fastforce
    moreover
      have
        [simp]:"learned_clss S' = {#}" and
        [simp]: "init_clss S' = init_clss S" and
        [simp]: "conflicting S' = C_True"
        using tranclp_into_rtranclp[OF \<open>propagate\<^sup>+\<^sup>+ S S'\<close>] S
        rtranclp_propagate_is_update_trail[of S S'] S M unfolding state_eq_def by simp_all
      have S_S': "S' \<sim> update_backtrack_lvl (backtrack_lvl S')
        (append_trail (rev (trail S')) (init_state N))" using S
        by (auto simp: state_eq_def simp del: state_simp)
      have "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state (init_clss S')) S'"
        apply (rule rtranclp.rtrancl_into_rtrancl)
        using st unfolding \<open>init_clss S' = N\<close> apply simp
        using \<open>cdcl\<^sub>W_stgy S S'\<close> by simp
    ultimately have ?case
      apply -
      apply (rule exI[of _ "trail S'"], rule exI[of _ "backtrack_lvl S'"],  rule exI[of _ S'])
      using S_S' by (auto simp: state_eq_def simp del: state_simp)
  }
  moreover {
    assume no_step: "no_step propagate S"
    have ?case
      proof (cases "length M' \<ge> Suc n")
        case True
        then show ?thesis using l_M' M' st M alien S by fastforce
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
            then show ?thesis using S by (auto simp add: conflict.simps true_clss_def)
          qed
        have lenM: "length M = card (set M)" using distM by (induction M) auto
        have "no_dup M'" using S M unfolding cdcl\<^sub>W_M_level_inv_def by auto
        then have "card (lits_of M') = length M'"
          by (induction M') (auto simp add: lits_of_def card_insert_if)
        then have "lits_of M' \<subset> set M"
          using n M' n' lenM by auto
        then obtain m where m: "m \<in> set M" and undef_m: "m \<notin> lits_of M'" by auto
        moreover have undef: "undefined_lit M' m"
          using M' Marked_Propagated_in_iff_in_lits_of calculation(1,2) cons
          consistent_interp_def by blast
        moreover have "atm_of m \<in> atms_of_mu (init_clss S)"
          using atm_incl calculation S by auto
        ultimately
          have dec: "decide S (cons_trail (Marked m (k+1)) (incr_lvl S))"
            using decide.intros[of S "rev M'" N _ k m
              "cons_trail (Marked m (k + 1)) (incr_lvl S)"] S
            by auto
        let ?S' = "cons_trail (Marked m (k+1)) (incr_lvl S)"
        have "lits_of (trail ?S') \<subseteq> set M" using m M' S undef by auto
        moreover have "no_strange_atm ?S'"
          using alien dec M by (meson cdcl\<^sub>W_no_strange_atm_inv decide other)
        ultimately obtain S'' where S'': "propagate\<^sup>*\<^sup>* ?S' S''" and full: "full cdcl\<^sub>W_cp ?S' S''"
          using completeness_is_a_full1_propagation[OF assms(1-3), of ?S'] S undef by auto
        have "cdcl\<^sub>W_M_level_inv ?S'"
          using M dec rtranclp_mono[of decide cdcl\<^sub>W] by (meson cdcl\<^sub>W_consistent_inv decide other)
        then have lev'': "cdcl\<^sub>W_M_level_inv S''"
          using S'' rtranclp_cdcl\<^sub>W_consistent_inv rtranclp_propagate_is_rtranclp_cdcl\<^sub>W by blast
        then have n_d'': "no_dup (trail S'')"
          unfolding cdcl\<^sub>W_M_level_inv_def by auto
        have "length (trail ?S') \<le> length (trail S'') \<and> lits_of (trail S'') \<subseteq> set M"
          using S'' full cdcl\<^sub>W_cp_propagate_completeness[OF assms(1-3), of ?S' S''] m M' S undef
          by simp
        then have "Suc n \<le> length (trail S'') \<and> lits_of (trail S'') \<subseteq> set M"
          using l_M' S undef by auto
        moreover
          have "cdcl\<^sub>W_M_level_inv (cons_trail (Marked m (Suc (backtrack_lvl S)))
            (update_backtrack_lvl (Suc (backtrack_lvl S)) S))"
            using S \<open>cdcl\<^sub>W_M_level_inv (cons_trail (Marked m (k + 1)) (incr_lvl S))\<close> by auto
          then have S'': "S'' \<sim>
            update_backtrack_lvl (backtrack_lvl S'') (append_trail (rev (trail S'')) (init_state N))"
            using rtranclp_propagate_is_update_trail[OF S''] S undef n_d'' lev''
            by (auto simp del: state_simp simp: state_eq_def )
          then have "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) S''"
            using cdcl\<^sub>W_stgy.intros(2)[OF decide[OF dec] _ full] no_step no_confl st
            by (auto simp: cdcl\<^sub>W_cp.simps)
        ultimately show ?thesis using S'' n_d'' by blast
      qed
  }
  ultimately show ?case by blast
qed

lemma cdcl\<^sub>W_stgy_strong_completeness:
  assumes MN: "set M \<Turnstile>s set_mset N"
  and cons: "consistent_interp (set M)"
  and tot: "total_over_m (set M) (set_mset N)"
  and atm_incl: "atm_of ` (set M) \<subseteq> atms_of_mu N"
  and distM: "distinct M"
  shows
    "\<exists>M' k S.
      lits_of M' = set M \<and>
      S \<sim> update_backtrack_lvl k (append_trail (rev M') (init_state N)) \<and>
      cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) S \<and>
      final_cdcl\<^sub>W_state S"
proof -
  from cdcl\<^sub>W_stgy_strong_completeness_n[OF assms, of "length M"]
  obtain M' k T where
    l: "length M \<le> length M'" and
    M'_M: "lits_of M' \<subseteq> set M" and
    no_dup: "no_dup M'" and
    T: "T \<sim> update_backtrack_lvl k (append_trail (rev M') (init_state N))" and
    st: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) T"
    by auto
  have "card (set M) = length M" using distM by (simp add: distinct_card)
  moreover
    have "cdcl\<^sub>W_M_level_inv T"
      using rtranclp_cdcl\<^sub>W_stgy_consistent_inv[OF st] T by auto
    then have "card (set ((map (\<lambda>l. atm_of (lit_of l)) M'))) = length M'"
      using distinct_card no_dup by fastforce
  moreover have "card (lits_of M') = card (set ((map (\<lambda>l. atm_of (lit_of l)) M')))"
    using no_dup unfolding lits_of_def apply (induction M') by (auto simp add: card_insert_if)
  ultimately have "card (set M) \<le> card (lits_of M')" using l unfolding lits_of_def by auto
  then have "set M = lits_of M'"
    using M'_M  card_seteq by blast
  moreover
    then have "M' \<Turnstile>asm N"
      using MN unfolding true_annots_def Ball_def true_annot_def true_clss_def by auto
    then have "final_cdcl\<^sub>W_state T"
      using T no_dup unfolding final_cdcl\<^sub>W_state_def by auto
  ultimately show ?thesis using st T by blast
qed

subsubsection \<open>No conflict with only variables of level less than backtrack level\<close>
text \<open>This invariant is stronger than the previous argument in the sense that it is a property about
  all possible conflicts.\<close>
definition "no_smaller_confl (S::'st) \<equiv>
  (\<forall>M K i M' D. M' @ Marked K i # M = trail S \<longrightarrow> D \<in># clauses S
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
proof (induct rule: cdcl\<^sub>W_o_induct_lev2)
  case (decide L T) note confl = this(1) and undef = this(2) and T = this(4)
  have [simp]: "clauses T = clauses S"
    using T undef by auto
  show ?case
    proof (intro allI impI)
      fix M'' K i M' Da
      assume "M'' @ Marked K i # M' = trail T"
      and D: "Da \<in># local.clauses T"
      then have "tl M'' @ Marked K i # M' = trail S
        \<or> (M'' = [] \<and> Marked K i # M' = Marked L (backtrack_lvl S + 1) # trail S)"
        using T undef by (cases M'') auto
      moreover {
        assume "tl M'' @ Marked K i # M' = trail S"
        then have "\<not>M' \<Turnstile>as CNot Da"
          using D T undef no_f confl smaller unfolding no_smaller_confl_def smaller by fastforce
      }
      moreover {
        assume "Marked K i # M' = Marked L (backtrack_lvl S + 1) # trail S"
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
  case (backtrack K i M1 M2 L D T) note decomp = this(1) and confl = this(3) and undef = this(6) and
    T =this(7)
  obtain c where M: "trail S = c @ M2 @ Marked K (i+1) # M1"
    using decomp by auto

  show ?case
    proof (intro allI impI)
      fix M ia K' M' Da
      assume "M' @ Marked K' ia # M = trail T"
      then have "tl M' @ Marked K' ia # M = M1"
        using T decomp undef by (cases M') auto
      assume D: "Da \<in># clauses T"
      moreover{
        assume "Da \<in># clauses S"
        then have "\<not>M \<Turnstile>as CNot Da" using \<open>tl M' @ Marked K' ia # M = M1\<close> M confl undef smaller
          unfolding no_smaller_confl_def by auto
      }
      moreover {
        assume Da: "Da = D + {#L#}"
        have "\<not>M \<Turnstile>as CNot Da"
          proof (rule ccontr)
            assume "\<not> ?thesis"
            then have "-L \<in> lits_of M" unfolding Da by auto
            then have "-L \<in> lits_of (Propagated L ((D + {#L#})) # M1)"
              using UnI2 \<open>tl M' @ Marked K' ia # M = M1\<close>
              by auto
            moreover
              have "backtrack S
                (cons_trail (Propagated L (D + {#L#}))
                  (reduce_trail_to M1 (add_learned_cls (D + {#L#})
                  (update_backtrack_lvl i (update_conflicting C_True S)))))"
                using backtrack.intros[of S] backtrack.hyps
                by (force simp: state_eq_def simp del: state_simp)
              then have "cdcl\<^sub>W_M_level_inv
                (cons_trail (Propagated L (D + {#L#}))
                  (reduce_trail_to M1 (add_learned_cls (D + {#L#})
                  (update_backtrack_lvl i (update_conflicting C_True S)))))"
                using cdcl\<^sub>W_consistent_inv[OF _ lev] other[OF bj] by auto
              then have "no_dup  (Propagated L ( (D + {#L#})) # M1)" using decomp undef by auto
            ultimately show False by (metis consistent_interp_def distinctconsistent_interp
              insertCI lits_of_cons marked_lit.sel(2))
          qed
      }
      ultimately show "\<not>M \<Turnstile>as CNot Da"
        using T undef  \<open>Da = D + {#L#} \<Longrightarrow> \<not> M \<Turnstile>as CNot Da\<close> decomp by fastforce
    qed
qed

lemma conflict_no_smaller_confl_inv:
  assumes "conflict S S'"
  and "no_smaller_confl S"
  shows "no_smaller_confl S'"
  using assms unfolding no_smaller_confl_def by fastforce

lemma propagate_no_smaller_confl_inv:
  assumes propagate: "propagate S S'"
  and n_l: "no_smaller_confl S"
  shows "no_smaller_confl S'"
  unfolding no_smaller_confl_def
proof (intro allI impI)
  fix M' K i M'' D
  assume M': "M'' @ Marked K i # M' = trail S'"
  and "D \<in># clauses S'"
  obtain M N U k C L where
    S: "state S = (M, N, U, k, C_True)" and
    S': "state S' = (Propagated L ( (C + {#L#})) # M, N, U, k, C_True)" and
    "C + {#L#} \<in># clauses S" and
    "M \<Turnstile>as CNot C" and
    "undefined_lit M L"
    using propagate by auto
  have "tl M'' @ Marked K i # M' = trail S" using M' S S'
    by (metis Pair_inject list.inject list.sel(3) marked_lit.distinct(1) self_append_conv2
      tl_append2)
  then have "\<not>M' \<Turnstile>as CNot D "
    using \<open>D \<in># clauses S'\<close> n_l S S' clauses_def unfolding no_smaller_confl_def by auto
  then show "\<not>M' \<Turnstile>as CNot D" by auto
qed

lemma cdcl\<^sub>W_cp_no_smaller_confl_inv:
  assumes propagate: "cdcl\<^sub>W_cp S S'"
  and n_l: "no_smaller_confl S"
  shows "no_smaller_confl S'"
  using assms
proof (induct rule: cdcl\<^sub>W_cp.induct)
  case (conflict' S S')
  then show ?case using conflict_no_smaller_confl_inv[of S S'] by blast
next
  case (propagate' S S')
  then show ?case using propagate_no_smaller_confl_inv[of S S'] by fastforce
qed

lemma rtrancp_cdcl\<^sub>W_cp_no_smaller_confl_inv:
  assumes propagate: "cdcl\<^sub>W_cp\<^sup>*\<^sup>* S S'"
  and n_l: "no_smaller_confl S"
  shows "no_smaller_confl S'"
  using assms
proof (induct rule: rtranclp.induct)
  case rtrancl_refl
  then show ?case by simp
next
  case (rtrancl_into_rtrancl S S' S'')
  then show ?case using cdcl\<^sub>W_cp_no_smaller_confl_inv[of S' S''] by fast
qed

lemma trancp_cdcl\<^sub>W_cp_no_smaller_confl_inv:
  assumes propagate: "cdcl\<^sub>W_cp\<^sup>+\<^sup>+ S S'"
  and n_l: "no_smaller_confl S"
  shows "no_smaller_confl S'"
  using assms
proof (induct rule: tranclp.induct)
  case (r_into_trancl S S')
  then show ?case using cdcl\<^sub>W_cp_no_smaller_confl_inv[of S S'] by blast
next
  case (trancl_into_trancl S S' S'')
  then show ?case using cdcl\<^sub>W_cp_no_smaller_confl_inv[of S' S''] by fast
qed

lemma full_cdcl\<^sub>W_cp_no_smaller_confl_inv:
  assumes "full cdcl\<^sub>W_cp S S'"
  and n_l: "no_smaller_confl S"
  shows "no_smaller_confl S'"
  using assms unfolding full_def
  using rtrancp_cdcl\<^sub>W_cp_no_smaller_confl_inv[of S S'] by blast

lemma full1_cdcl\<^sub>W_cp_no_smaller_confl_inv:
  assumes "full1 cdcl\<^sub>W_cp S S'"
  and n_l: "no_smaller_confl S"
  shows "no_smaller_confl S'"
  using assms unfolding full1_def
  using trancp_cdcl\<^sub>W_cp_no_smaller_confl_inv[of S S'] by blast

lemma cdcl\<^sub>W_stgy_no_smaller_confl_inv:
  assumes "cdcl\<^sub>W_stgy S S'"
  and n_l: "no_smaller_confl S"
  and "conflict_is_false_with_level S"
  and "cdcl\<^sub>W_M_level_inv S"
  shows "no_smaller_confl S'"
  using assms
proof (induct rule: cdcl\<^sub>W_stgy.induct)
  case (conflict' S S')
  then show ?case using full1_cdcl\<^sub>W_cp_no_smaller_confl_inv[of S S'] by blast
next
  case (other' S S' S'')
  have "no_smaller_confl S'"
    using cdcl\<^sub>W_o_no_smaller_confl_inv[OF other'.hyps(1) other'.prems(3,2,1)]
    not_conflict_not_any_negated_init_clss other'.hyps(2) by blast
  then show ?case using full_cdcl\<^sub>W_cp_no_smaller_confl_inv[of S' S''] other'.hyps by blast
qed


lemma conflict_conflict_is_no_clause_is_false_test:
  assumes "conflict S S'"
  and "(\<forall>D \<in># init_clss S + learned_clss S. trail S \<Turnstile>as CNot D
    \<longrightarrow> (\<exists>L. L \<in># D \<and> get_level L (trail S) = backtrack_lvl S))"
  shows "\<forall>D \<in># init_clss S' + learned_clss S'. trail S' \<Turnstile>as CNot D
    \<longrightarrow> (\<exists>L. L \<in># D \<and> get_level L (trail S') = backtrack_lvl S')"
  using assms by auto

lemma is_conflicting_exists_conflict:
  assumes "\<not>(\<forall>D\<in>#init_clss S' + learned_clss S'. \<not> trail S' \<Turnstile>as CNot D)"
  and "conflicting S' = C_True"
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
    \<or> (conflicting S' = C_True
        \<longrightarrow> (\<forall>D \<in># clauses S'. trail S' \<Turnstile>as CNot D
             \<longrightarrow> (\<exists>L. L \<in># D \<and> get_level L (trail S') = backtrack_lvl S')))"
  using assms(1,2)
proof (induct rule: cdcl\<^sub>W_o_induct_lev2)
  case (decide L T) note S = this(1) and undef = this(2) and T =this(4)
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
              obtain L'' where "L'' \<in># x" and "lits_of (Marked L (?k + 1) # ?M) \<Turnstile>l L''"
                using M_D x T undef unfolding true_annots_def Ball_def true_annot_def CNot_def
                true_cls_def Bex_mset_def by auto
              show "\<exists>L \<in># x. lits_of ?M \<Turnstile>l L" unfolding Bex_mset_def
                by (metis \<open>- L \<notin># D\<close> \<open>L'' \<in># x\<close> L' \<open>lits_of (Marked L (?k + 1) # ?M) \<Turnstile>l L''\<close>
                  count_single insertE less_numeral_extra(3) lits_of_cons marked_lit.sel(1)
                  true_lit_def uminus_of_uminus_id)
            qed
          then show False using \<open>\<not> ?M \<Turnstile>as CNot D\<close> by auto
        qed
      have "atm_of L \<notin> atm_of ` (lits_of ?M)"
        using undef defined_lit_map unfolding lits_of_def by fastforce
      then have "get_level (-L) (Marked L (?k + 1) # ?M) = ?k + 1" by simp
      then show "\<exists>La. La \<in># D \<and> get_level La ?M'
        = backtrack_lvl T"
        using \<open>-L \<in># D\<close> T undef by auto
    qed
next
  case resolve
  then show ?case by auto
next
  case skip
  then show ?case by auto
next
  case (backtrack K i M1 M2 L D T) note decomp = this(1) and undef = this(6) and T =this(7)
  show ?case
    proof (rule HOL.disjI2, clarify)
      fix Da
      assume Da: "Da \<in># clauses T"
      and M_D: "trail T \<Turnstile>as CNot Da"
      obtain c where M: "trail S = c @ M2 @ Marked K (i + 1) # M1"
        using decomp by auto
      have tr_T: "trail T = Propagated L (D + {#L#}) # M1"
        using T decomp undef by auto
      have "backtrack S T"
       using backtrack.intros backtrack.hyps T by (force simp del: state_simp simp: state_eq_def)
      then have lev': "cdcl\<^sub>W_M_level_inv T"
        using cdcl\<^sub>W_consistent_inv lev other by blast
      then have "- L \<notin> lits_of M1"
        unfolding cdcl\<^sub>W_M_level_inv_def lits_of_def
        proof -
          have "consistent_interp (lits_of (trail S)) \<and> no_dup (trail S)
            \<and> backtrack_lvl S = length (get_all_levels_of_marked (trail S))
            \<and> get_all_levels_of_marked (trail S)
              = rev [1..<1 + length (get_all_levels_of_marked (trail S))]"
            using lev cdcl\<^sub>W_M_level_inv_def by blast
          then show "- L \<notin> lit_of ` set M1"
            by (metis (no_types) One_nat_def add.right_neutral add_Suc_right
              atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set backtrack.hyps(2)
              cdcl\<^sub>W_ops.backtrack_lit_skiped cdcl\<^sub>W_ops_axioms decomp lits_of_def)
        qed
      { assume "Da \<in># clauses S"
        then have "\<not>M1 \<Turnstile>as CNot Da" using no_l M unfolding no_smaller_confl_def by auto
      }
      moreover {
        assume Da: "Da = D + {#L#}"
        have "\<not>M1 \<Turnstile>as CNot Da" using \<open>- L \<notin> lits_of M1\<close> unfolding Da by simp
      }
      ultimately have "\<not>M1 \<Turnstile>as CNot Da" using Da T undef decomp by fastforce
      then have "-L \<in># Da"
        using M_D \<open>- L \<notin> lits_of M1\<close> in_CNot_implies_uminus(2)
           true_annots_CNot_lit_of_notin_skip T unfolding tr_T
        by (smt insert_iff lits_of_cons marked_lit.sel(2))
      have g_M1: "get_all_levels_of_marked M1 = rev [1..<i+1]"
        using lev' T decomp undef unfolding cdcl\<^sub>W_M_level_inv_def by auto
      have "no_dup (Propagated L ( (D + {#L#})) # M1)" using lev' T decomp undef by auto
      then have L: "atm_of L \<notin> atm_of ` lits_of M1" unfolding lits_of_def by auto
      have "get_level (-L) (Propagated L ((D + {#L#})) # M1) = i"
        using get_level_get_rev_level_get_all_levels_of_marked[OF L,
          of "[Propagated L ((D + {#L#}))]"]
        by (simp add: g_M1 split: if_splits)
      then show "\<exists>La. La \<in># Da \<and> get_level La (trail T) = backtrack_lvl T"
        using \<open>-L \<in># Da\<close> T decomp undef by auto
    qed
qed

lemma full1_cdcl\<^sub>W_cp_exists_conflict_decompose:
  assumes confl: "\<exists>D\<in>#clauses S. trail S \<Turnstile>as CNot D"
  and full: "full cdcl\<^sub>W_cp S U"
  and no_confl: "conflicting S = C_True"
  shows "\<exists>T. propagate\<^sup>*\<^sup>* S T \<and> conflict T U"
proof -
  consider (propa) "propagate\<^sup>*\<^sup>* S U"
        |  (confl) T where "propagate\<^sup>*\<^sup>* S T" and "conflict T U"
   using full unfolding full_def by (blast dest:rtranclp_cdcl\<^sub>W_cp_propa_or_propa_confl)
  then show ?thesis
    proof cases
      case confl
      then show ?thesis by blast
    next
      case propa
      then have "conflicting U = C_True"
        using no_confl by induction auto
      moreover have [simp]: "learned_clss U = learned_clss S" and [simp]: "init_clss U = init_clss S"
        using propa by induction auto
      moreover
        obtain D where D: "D\<in>#clauses U" and
          trS: "trail S \<Turnstile>as CNot D"
          using confl clauses_def by auto
        obtain M where M: "trail U = M @ trail S"
          using full rtranclp_cdcl\<^sub>W_cp_dropWhile_trail unfolding full_def by meson
        have tr_U: "trail U \<Turnstile>as CNot D"
          apply (rule true_annots_mono)
          using trS unfolding M by simp_all
      have "\<exists>V. conflict U V"
        using \<open>conflicting U = C_True\<close> D clauses_def not_conflict_not_any_negated_init_clss tr_U
        by blast
      then have False using full cdcl\<^sub>W_cp.conflict' unfolding full_def by blast
      then show ?thesis by fast
    qed
qed

lemma full1_cdcl\<^sub>W_cp_exists_conflict_full1_decompose:
  assumes confl: "\<exists>D\<in>#clauses S. trail S \<Turnstile>as CNot D"
  and full: "full cdcl\<^sub>W_cp S U"
  and no_confl: "conflicting S = C_True"
  shows "\<exists>T D. propagate\<^sup>*\<^sup>* S T \<and> conflict T U
    \<and> trail T \<Turnstile>as CNot D \<and> conflicting U = C_Clause D \<and> D \<in># clauses S"
proof -
  obtain T where propa: "propagate\<^sup>*\<^sup>* S T" and conf: "conflict T U"
    using full1_cdcl\<^sub>W_cp_exists_conflict_decompose[OF assms] by blast
  have p: "learned_clss T = learned_clss S" "init_clss T = init_clss S"
     using propa by induction auto
  have c: "learned_clss U = learned_clss T" "init_clss U = init_clss T"
     using conf by induction auto
  obtain D where "trail T \<Turnstile>as CNot D \<and> conflicting U = C_Clause D \<and> D \<in># clauses S"
    using conf p c by (fastforce simp: clauses_def)
  then show ?thesis
    using propa conf by blast
qed

lemma cdcl\<^sub>W_stgy_no_smaller_confl:
  assumes "cdcl\<^sub>W_stgy S S'"
  and n_l: "no_smaller_confl S"
  and "conflict_is_false_with_level S"
  and "cdcl\<^sub>W_M_level_inv S"
  and "no_clause_is_false S"
  and "distinct_cdcl\<^sub>W_state S"
  and "cdcl\<^sub>W_conflicting S"
  shows "no_smaller_confl S'"
  using assms
proof (induct rule: cdcl\<^sub>W_stgy.induct)
  case (conflict' S S')
  show "no_smaller_confl S'"
    using conflict'.hyps conflict'.prems(1) full1_cdcl\<^sub>W_cp_no_smaller_confl_inv by blast
next
  case (other' S S' S'')
  have lev': "cdcl\<^sub>W_M_level_inv S'"
    using cdcl\<^sub>W_consistent_inv other other'.hyps(1) other'.prems(3) by blast
  show "no_smaller_confl S''"
    using cdcl\<^sub>W_stgy_no_smaller_confl_inv[OF cdcl\<^sub>W_stgy.other'[OF other'.hyps(1-3)]] other'.prems(1-3)
    by blast
qed

lemma cdcl\<^sub>W_stgy_ex_lit_of_max_level:
  assumes "cdcl\<^sub>W_stgy S S'"
  and n_l: "no_smaller_confl S"
  and "conflict_is_false_with_level S"
  and "cdcl\<^sub>W_M_level_inv S"
  and "no_clause_is_false S"
  and "distinct_cdcl\<^sub>W_state S"
  and "cdcl\<^sub>W_conflicting S"
  shows "conflict_is_false_with_level S'"
  using assms
proof (induct rule: cdcl\<^sub>W_stgy.induct)
  case (conflict' S S')
  have "no_smaller_confl S'"
    using conflict'.hyps conflict'.prems(1) full1_cdcl\<^sub>W_cp_no_smaller_confl_inv by blast
  moreover have "conflict_is_false_with_level S'"
    using conflict'.hyps conflict'.prems(2-4) rtranclp_cdcl\<^sub>W_co_conflict_ex_lit_of_max_level[of S S']
    unfolding full_def full1_def rtranclp_unfold by blast
  then show ?case by blast
next
  case (other' S S' S'')
  have lev': "cdcl\<^sub>W_M_level_inv S'"
    using cdcl\<^sub>W_consistent_inv other other'.hyps(1) other'.prems(3) by blast
  moreover
    have "no_clause_is_false S'
      \<or> (conflicting S' = C_True \<longrightarrow> (\<forall>D\<in>#clauses S'. trail S' \<Turnstile>as CNot D
          \<longrightarrow> (\<exists>L. L \<in># D \<and> get_level L (trail S') = backtrack_lvl S')))"
      using cdcl\<^sub>W_o_conflict_is_no_clause_is_false[of S S'] other'.hyps(1) other'.prems(1-4) by fast
  moreover {
    assume "no_clause_is_false S'"
    {
      assume "conflicting S' = C_True"
      then have "conflict_is_false_with_level S'" by auto
      moreover have "full cdcl\<^sub>W_cp S' S''"
        by (metis (no_types) other'.hyps(3))
      ultimately have "conflict_is_false_with_level S''"
        using rtranclp_cdcl\<^sub>W_co_conflict_ex_lit_of_max_level[of S' S''] lev' \<open>no_clause_is_false S'\<close>
        by blast
    }
    moreover
    {
      assume c: "conflicting S' \<noteq> C_True"
      have "conflicting S \<noteq> C_True" using other'.hyps(1) c
        by (induct rule: cdcl\<^sub>W_o_induct) auto
      then have "conflict_is_false_with_level S'"
        using cdcl\<^sub>W_o_conflict_is_false_with_level_inv[OF other'.hyps(1)]
        other'.prems(3,5,6,2) by blast
      moreover have "cdcl\<^sub>W_cp\<^sup>*\<^sup>* S' S''" using other'.hyps(3) unfolding full_def by auto
      then have "S' = S''" using c
        by (induct rule: rtranclp.induct)
           (fastforce intro: conflicting_clause.exhaust)+
      ultimately have "conflict_is_false_with_level S''" by auto
    }
    ultimately have "conflict_is_false_with_level S''" by blast
  }
  moreover {
     assume confl: "conflicting S' = C_True"
     and D_L: "\<forall>D \<in># clauses S'. trail S' \<Turnstile>as CNot D
         \<longrightarrow> (\<exists>L. L \<in># D \<and> get_level L (trail S') = backtrack_lvl S')"
     { assume "\<forall>D\<in>#clauses S'. \<not> trail S' \<Turnstile>as CNot D"
       then have "no_clause_is_false S'" using \<open>conflicting S' = C_True\<close> by simp
       then have "conflict_is_false_with_level S''" using calculation(3) by blast
     }
     moreover {
       assume "\<not>(\<forall>D\<in>#clauses S'. \<not> trail S' \<Turnstile>as CNot D)"
       then obtain T D where
         "propagate\<^sup>*\<^sup>* S' T" and
         "conflict T S''" and
         D: "D \<in># clauses S'" and
         "trail S'' \<Turnstile>as CNot D" and
         "conflicting S'' = C_Clause D"
         using full1_cdcl\<^sub>W_cp_exists_conflict_full1_decompose[OF _ _  \<open>conflicting S' = C_True\<close>]
         other'(3) by (metis (mono_tags, lifting) ball_msetI bex_msetI conflictE state_eq_trail
           trail_update_conflicting)
       obtain M where M: "trail S'' = M @ trail S'" and nm: "\<forall>m\<in>set M. \<not>is_marked m"
         using rtranclp_cdcl\<^sub>W_cp_dropWhile_trail other'(3) unfolding full_def by meson
       have btS: "backtrack_lvl S'' = backtrack_lvl S'"
         using other'.hyps(3) unfolding full_def by (metis  rtranclp_cdcl\<^sub>W_cp_backtrack_lvl)
       have inv: "cdcl\<^sub>W_M_level_inv S''"
         by (metis (no_types) cdcl\<^sub>W_stgy.conflict' cdcl\<^sub>W_stgy_consistent_inv full_unfold lev'
           other'.hyps(3))
       then have nd: "no_dup (trail S'')"
         by (metis (no_types) cdcl\<^sub>W_M_level_inv_decomp(2))
       have "conflict_is_false_with_level S''"
         proof cases
           assume "trail S' \<Turnstile>as CNot D"
           moreover then obtain L where "L \<in># D" and "get_level L (trail S') = backtrack_lvl S'"
             using D_L D by blast
           moreover
             have LS': "-L \<in> lits_of (trail S')"
               using \<open>trail S' \<Turnstile>as CNot D\<close> \<open>L \<in># D\<close> in_CNot_implies_uminus(2) by blast
             {  fix x :: "('v, nat, 'v literal multiset) marked_lit" and
                 xb :: "('v, nat, 'v literal multiset) marked_lit"
               assume a1: "x \<in> set (trail S')" and
                 a2: "xb \<in> set M" and
                 a3: "(\<lambda>l. atm_of (lit_of l)) ` set M  \<inter> (\<lambda>l. atm_of (lit_of l)) ` set (trail S')
                   = {}" and
                  a4: "- L = lit_of x" and
                  a5: "atm_of L = atm_of (lit_of xb)"
               moreover have "atm_of (lit_of x) = atm_of L"
                 using a4 by (metis (no_types) atm_of_uminus)
               ultimately have False
                 using a5 a3 a2 a1 by auto
             }
             then have "atm_of L \<notin> atm_of ` lits_of M"
               using nd LS' unfolding M by (auto simp add: lits_of_def)
             then have "get_level L (trail S'') = get_level L (trail S')"
               unfolding M by (simp add: lits_of_def)
           ultimately show ?thesis using btS \<open>conflicting S'' = C_Clause D\<close> by auto
         next
           assume "\<not>trail S' \<Turnstile>as CNot D"
           then obtain L where "L \<in># D" and LM: "-L \<in> lits_of M"
             using \<open>trail S'' \<Turnstile>as CNot D\<close>
               by (auto simp add: CNot_def true_cls_def  M true_annots_def true_annot_def
                     split: split_if_asm)
           { fix x :: "('v, nat, 'v literal multiset) marked_lit" and
               xb :: "('v, nat, 'v literal multiset) marked_lit"
             assume a1: "xb \<in> set (trail S')" and
               a2: "x \<in> set M" and
               a3: "atm_of L = atm_of (lit_of xb)" and
               a4: "- L = lit_of x" and
               a5: "(\<lambda>l. atm_of (lit_of l)) ` set M \<inter> (\<lambda>l. atm_of (lit_of l)) ` set (trail S')
                 = {}"
             moreover have "atm_of (lit_of xb) = atm_of (- L)"
               using a3 by simp
             ultimately have False
               by auto }
           then have LS': "atm_of L \<notin> atm_of ` lits_of (trail S')"
             using nd \<open>L \<in># D\<close> LM unfolding M by (auto simp add: lits_of_def)
           show ?thesis
             proof cases
               assume ne: "get_all_levels_of_marked (trail S') = []"
               have "backtrack_lvl S'' = 0"
                 using inv ne nm unfolding cdcl\<^sub>W_M_level_inv_def M
                 by (simp add: get_all_levels_of_marked_nil_iff_not_is_marked)
               moreover
                 have a1: "get_rev_level L 0 (rev M) = 0"
                   using nm by auto
                 then have "get_level L (M @ trail S') = 0"
                   by (metis LS' get_all_levels_of_marked_nil_iff_not_is_marked
                     get_level_skip_beginning_not_marked lits_of_def ne)
               ultimately show ?thesis using \<open>conflicting S'' = C_Clause D\<close> \<open>L \<in># D\<close> unfolding M
                 by auto
             next
               assume ne: "get_all_levels_of_marked (trail S') \<noteq> []"
               have "hd (get_all_levels_of_marked (trail S')) = backtrack_lvl S'"
                 using ne cdcl\<^sub>W_M_level_inv_decomp(4)[OF lev'] M nm
                 by (simp add: get_all_levels_of_marked_nil_iff_not_is_marked[symmetric])
               moreover have "atm_of L \<in> atm_of ` lits_of M "
                  using \<open>-L \<in> lits_of M\<close>
                  by (simp add: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set lits_of_def)
               ultimately show ?thesis
                 using nm ne \<open>L\<in>#D\<close> \<open>conflicting S'' = C_Clause D\<close>
                   get_level_skip_beginning_hd_get_all_levels_of_marked[OF LS', of M]
                   get_level_skip_in_all_not_marked[of "rev M" L "backtrack_lvl S'"]
                 unfolding lits_of_def btS M
                 by auto
             qed
         qed
     }
     ultimately have "conflict_is_false_with_level S''" by blast
  }
  moreover
  {
    assume "conflicting S' \<noteq> C_True"
    have "no_clause_is_false S'" using \<open>conflicting S' \<noteq> C_True\<close>  by auto
    then have "conflict_is_false_with_level S''" using calculation(3) by blast
  }
  ultimately show ?case by fast
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
    decomp: "all_decomposition_implies_m (init_clss S) (get_all_marked_decomposition (trail S))" and
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
    using  st lev rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W by (blast intro: rtranclp_cdcl\<^sub>W_consistent_inv)+
  moreover have "no_clause_is_false S'"
    using st no_f rtranclp_cdcl\<^sub>W_stgy_not_non_negated_init_clss by blast
  moreover have "distinct_cdcl\<^sub>W_state S'"
    using rtanclp_distinct_cdcl\<^sub>W_state_inv[of S S'] lev rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W[OF st]
    dist by auto
  moreover have "cdcl\<^sub>W_conflicting S'"
    using rtranclp_cdcl\<^sub>W_all_inv(6)[of S S'] st  alien conflicting decomp dist learned lev
    rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W by blast
  ultimately show ?case
    using cdcl\<^sub>W_stgy_no_smaller_confl[OF cdcl] cdcl\<^sub>W_stgy_ex_lit_of_max_level[OF cdcl] by fast
qed

subsubsection \<open>Final States are Conclusive\<close>
(*prop 2.10.7*)
lemma full_cdcl\<^sub>W_stgy_final_state_conclusive_non_false:
  fixes S' :: "'st"
  assumes full: "full cdcl\<^sub>W_stgy (init_state N) S'"
  and no_d: "distinct_mset_mset N"
  and no_empty: "\<forall>D\<in>#N. D \<noteq> {#}"
  shows "(conflicting S' = C_Clause {#} \<and> unsatisfiable (set_mset (init_clss S')))
    \<or> (conflicting S' = C_True \<and> trail S' \<Turnstile>asm init_clss S')"
proof -
  let ?S = "init_state N"
  have
    termi: "\<forall>S''. \<not>cdcl\<^sub>W_stgy S' S''" and
    step: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) S'" using full unfolding full_def by auto
  moreover have
    learned: "cdcl\<^sub>W_learned_clause S'" and
    level_inv: "cdcl\<^sub>W_M_level_inv S'" and
    alien: "no_strange_atm S'" and
    no_dup: "distinct_cdcl\<^sub>W_state S'" and
    confl: "cdcl\<^sub>W_conflicting S'" and
    decomp: "all_decomposition_implies_m (init_clss S') (get_all_marked_decomposition (trail S'))"
    using no_d tranclp_cdcl\<^sub>W_stgy_tranclp_cdcl\<^sub>W[of ?S S'] step rtranclp_cdcl\<^sub>W_all_inv(1-6)[of ?S S']
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
  have "cdcl\<^sub>W_cp S S'" and "conflicting S' \<noteq> C_True" using cp cdcl\<^sub>W_cp.intros by auto
  then have "cdcl\<^sub>W_cp\<^sup>+\<^sup>+ S S'" by blast
  moreover have "no_step cdcl\<^sub>W_cp S'"
    using \<open>conflicting S' \<noteq> C_True\<close> by (metis cdcl\<^sub>W_cp_conflicting_not_empty
      conflicting_clause.exhaust)
  ultimately show "full1 cdcl\<^sub>W_cp S S'" unfolding full1_def by blast+
qed

lemma cdcl\<^sub>W_cp_fst_empty_conflicting_false:
  assumes "cdcl\<^sub>W_cp S S'"
  and "trail S = []"
  and "conflicting S \<noteq> C_True"
  shows False
  using assms by (induct rule: cdcl\<^sub>W_cp.induct) auto

lemma cdcl\<^sub>W_o_fst_empty_conflicting_false:
  assumes "cdcl\<^sub>W_o S S'"
  and "trail S = []"
  and "conflicting S \<noteq> C_True"
  shows False
  using assms by (induct rule: cdcl\<^sub>W_o_induct) auto

lemma cdcl\<^sub>W_stgy_fst_empty_conflicting_false:
  assumes "cdcl\<^sub>W_stgy S S'"
  and "trail S = []"
  and "conflicting S \<noteq> C_True"
  shows False
  using assms apply (induct rule: cdcl\<^sub>W_stgy.induct)
  using tranclpD cdcl\<^sub>W_cp_fst_empty_conflicting_false unfolding full1_def apply metis
  using cdcl\<^sub>W_o_fst_empty_conflicting_false by blast
thm cdcl\<^sub>W_cp.induct[split_format(complete)]

lemma cdcl\<^sub>W_cp_conflicting_is_false:
  "cdcl\<^sub>W_cp S S' \<Longrightarrow> conflicting S = C_Clause {#} \<Longrightarrow> False"
  by (induction rule: cdcl\<^sub>W_cp.induct) auto

lemma rtranclp_cdcl\<^sub>W_cp_conflicting_is_false:
  "cdcl\<^sub>W_cp\<^sup>+\<^sup>+ S S' \<Longrightarrow> conflicting S = C_Clause {#} \<Longrightarrow> False"
  apply (induction rule: tranclp.induct)
  by (auto dest: cdcl\<^sub>W_cp_conflicting_is_false)

lemma cdcl\<^sub>W_o_conflicting_is_false:
  "cdcl\<^sub>W_o S S' \<Longrightarrow> conflicting S = C_Clause {#} \<Longrightarrow> False"
  by (induction rule: cdcl\<^sub>W_o_induct) auto


lemma cdcl\<^sub>W_stgy_conflicting_is_false:
  "cdcl\<^sub>W_stgy S S' \<Longrightarrow> conflicting S = C_Clause {#} \<Longrightarrow> False"
  apply (induction rule: cdcl\<^sub>W_stgy.induct)
    unfolding full1_def apply (metis (no_types) cdcl\<^sub>W_cp_conflicting_not_empty tranclpD)
  unfolding full_def by (metis conflict_with_false_implies_terminated other)

lemma rtranclp_cdcl\<^sub>W_stgy_conflicting_is_false:
  "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S S' \<Longrightarrow> conflicting S = C_Clause {#} \<Longrightarrow> S' = S"
  apply (induction rule: rtranclp.induct)
    apply simp
  using cdcl\<^sub>W_stgy_conflicting_is_false by blast

lemma full_cdcl\<^sub>W_init_clss_with_false_normal_form:
  assumes
    "\<forall> m\<in> set M. \<not>is_marked m" and
    "E = C_Clause D" and
    "state S = (M, N, U, 0, E)"
    "full cdcl\<^sub>W_stgy S S'" and
    "all_decomposition_implies_m (init_clss S) (get_all_marked_decomposition (trail S))"
    "cdcl\<^sub>W_learned_clause S"
    "cdcl\<^sub>W_M_level_inv S"
    "no_strange_atm S"
    "distinct_cdcl\<^sub>W_state S"
    "cdcl\<^sub>W_conflicting S"
  shows "\<exists>M''. state S' = (M'', N, U, 0, C_Clause {#})"
  using assms(10,9,8,7,6,5,4,3,2,1)
proof (induction M arbitrary: E D S)
  case Nil
  then show ?case
    using rtranclp_cdcl\<^sub>W_stgy_conflicting_is_false unfolding full_def cdcl\<^sub>W_conflicting_def by auto
next
  case (Cons L M) note IH = this(1) and full = this(8) and E = this(10) and inv = this(2-7) and
    S = this(9) and nm = this(11)
  obtain K p where K: "L = Propagated K p"
    using nm by (cases L) auto
  have "every_mark_is_a_conflict S" using inv unfolding cdcl\<^sub>W_conflicting_def by auto
  then have MpK: "M \<Turnstile>as CNot ( p - {#K#})" and Kp: "K \<in>#  p"
    using S unfolding K by fastforce+
  then have p: " p = ( p - {#K#}) + {#K#}"
    by (auto simp add: multiset_eq_iff)
  then have K': "L = Propagated K ( (( p - {#K#}) + {#K#}))"
    using K by auto

  consider (D) "D = {#}" | (D') "D \<noteq> {#}" by blast
  then show ?case
    proof cases
      case D
      then show ?thesis
        using full rtranclp_cdcl\<^sub>W_stgy_conflicting_is_false S unfolding full_def E D by auto
    next
      case D'
      then have no_p: "no_step propagate S" and no_c: "no_step conflict S"
        using S E by auto
      then have "no_step cdcl\<^sub>W_cp S" by (auto simp: cdcl\<^sub>W_cp.simps)
      have res_skip: "\<exists>T. (resolve S T \<and> no_step skip S \<and> full cdcl\<^sub>W_cp T T)
        \<or> (skip S T \<and> no_step resolve S \<and> full cdcl\<^sub>W_cp T T)"
        proof cases
          assume "-lit_of L \<notin># D"
          then obtain T where sk: "skip S T" and res: "no_step resolve S"
          using S that D' K unfolding skip.simps E by fastforce
          have "full cdcl\<^sub>W_cp T T"
            using sk by (auto simp add: conflicting_clause_full_cdcl\<^sub>W_cp)
          then show ?thesis
            using sk res by blast
        next
          assume LD: "\<not>-lit_of L \<notin># D"
          then have D: "C_Clause D = C_Clause ((D - {#-lit_of L#}) + {#-lit_of L#})"
            by (auto simp add: multiset_eq_iff)

          have "\<And>L. get_level L M = 0"
            by (simp add: nm)
          then have "get_maximum_level (D - {#- K#})
            (Propagated K ( ( p - {#K#} + {#K#})) # M) = 0"
            using  LD get_maximum_level_exists_lit_of_max_level
            proof -
              obtain L' where "get_level L' (L#M) = get_maximum_level D (L#M)"
                using  LD get_maximum_level_exists_lit_of_max_level[of D "L#M"] by fastforce
              then show ?thesis by (metis (mono_tags) K' bex_msetE get_level_skip_all_not_marked
                get_maximum_level_exists_lit nm not_gr0)
            qed
          then obtain T where sk: "resolve S T" and res: "no_step skip S"
            using resolve_rule[of S K " p - {#K#}" M N U 0 "(D - {#-K#})"
            "update_conflicting (C_Clause (remdups_mset (D - {#- K#} + (p - {#K#})))) (tl_trail S)"]
            S unfolding K' D E  by fastforce
          have "full cdcl\<^sub>W_cp T T"
            using sk by (auto simp add: conflicting_clause_full_cdcl\<^sub>W_cp)
          then show ?thesis
           using sk res by blast
        qed
      then have step_s: "\<exists>T. cdcl\<^sub>W_stgy S T"
        using \<open>no_step cdcl\<^sub>W_cp S\<close> other' by (meson bj resolve skip)
      have "get_all_marked_decomposition (L # M) = [([], L#M)]"
        using nm unfolding K apply (induction M rule: marked_lit_list_induct, simp)
          by (case_tac "hd (get_all_marked_decomposition xs)", auto)+
      then have no_b: "no_step backtrack S"
        using nm S by auto
      have no_d: "no_step decide S"
        using S E by auto

      have full_S_S: "full cdcl\<^sub>W_cp S S"
        using S E by (auto simp add: conflicting_clause_full_cdcl\<^sub>W_cp)
      then have no_f: "no_step (full1 cdcl\<^sub>W_cp) S"
        unfolding full_def full1_def rtranclp_unfold by (meson tranclpD)
      obtain T where
        s: "cdcl\<^sub>W_stgy S T" and st: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* T S'"
        using full step_s full unfolding full_def by (metis rtranclp_unfold tranclpD)
      have "resolve S T \<or> skip S T"
        using s no_b no_d res_skip full_S_S unfolding cdcl\<^sub>W_stgy.simps cdcl\<^sub>W_o.simps full_unfold full1_def
        by (auto dest!: tranclpD simp: cdcl\<^sub>W_bj.simps)
      then obtain D' where T: "state T = (M, N, U, 0, C_Clause D')"
        using S E by auto

      have st_c: "cdcl\<^sub>W\<^sup>*\<^sup>* S T"
        using E T rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W s by blast
      have "cdcl\<^sub>W_conflicting T"
        using rtranclp_cdcl\<^sub>W_all_inv(6)[OF st_c  inv(6,5,4,3,2,1)]  .
      show ?thesis
        apply (rule IH[of T])
                  using rtranclp_cdcl\<^sub>W_all_inv(6)[OF st_c inv(6,5,4,3,2,1)] apply blast
                using rtranclp_cdcl\<^sub>W_all_inv(5)[OF st_c inv(6,5,4,3,2,1)] apply blast
               using rtranclp_cdcl\<^sub>W_all_inv(4)[OF st_c inv(6,5,4,3,2,1)] apply blast
              using rtranclp_cdcl\<^sub>W_all_inv(3)[OF st_c inv(6,5,4,3,2,1)] apply blast
             using rtranclp_cdcl\<^sub>W_all_inv(2)[OF st_c inv(6,5,4,3,2,1)] apply blast
            using rtranclp_cdcl\<^sub>W_all_inv(1)[OF st_c inv(6,5,4,3,2,1)] apply blast
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
  shows "conflicting S' = C_Clause {#} \<and> unsatisfiable (set_mset (init_clss S'))"
proof -
  let ?S = "init_state N"
  have "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ?S S'" and "no_step cdcl\<^sub>W_stgy S'" using full unfolding full_def by auto
  then have plus_or_eq: "cdcl\<^sub>W_stgy\<^sup>+\<^sup>+ ?S S' \<or> S' = ?S" unfolding rtranclp_unfold by auto
  have "\<exists>S''. conflict ?S S''" using empty not_conflict_not_any_negated_init_clss by force

  then have cdcl\<^sub>W_stgy: "\<exists>S'. cdcl\<^sub>W_stgy ?S S'"
    using cdcl\<^sub>W_cp.conflict'[of ?S] conflict_is_full1_cdcl\<^sub>W_cp cdcl\<^sub>W_stgy.intros(1) by metis
  have "S' \<noteq> ?S"  using \<open>no_step cdcl\<^sub>W_stgy S'\<close> cdcl\<^sub>W_stgy by blast

  then obtain St:: 'st where St: "cdcl\<^sub>W_stgy ?S St" and "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* St S'"
    using plus_or_eq by (metis (no_types) \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ?S S'\<close> converse_rtranclpE)
  have st: "cdcl\<^sub>W\<^sup>*\<^sup>* ?S St"
    by (simp add: rtranclp_unfold \<open>cdcl\<^sub>W_stgy ?S St\<close> cdcl\<^sub>W_stgy_tranclp_cdcl\<^sub>W)

  have "\<exists>T. conflict ?S T"
    using empty not_conflict_not_any_negated_init_clss by force
  then have fullSt: "full1 cdcl\<^sub>W_cp ?S St"
    using St unfolding cdcl\<^sub>W_stgy.simps by blast
  then have bt: "backtrack_lvl St = (0::nat)"
    using rtranclp_cdcl\<^sub>W_cp_backtrack_lvl unfolding full1_def
    by (fastforce dest!: tranclp_into_rtranclp)
  have cls_St: "init_clss St = N"
    using fullSt  cdcl\<^sub>W_stgy_no_more_init_clss[OF St] by auto
  have "conflicting St \<noteq> C_True"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have "\<exists>T. conflict St T"
        using empty cls_St by (fastforce simp: clauses_def)
      then show False using fullSt unfolding full1_def by blast
    qed

  have 1: "\<forall>m\<in>set (trail St). \<not> is_marked m"
    using fullSt unfolding full1_def by (auto dest!: tranclp_into_rtranclp
      rtranclp_cdcl\<^sub>W_cp_dropWhile_trail)
  have 2: "full cdcl\<^sub>W_stgy St S'"
    using \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* St S'\<close> \<open>no_step cdcl\<^sub>W_stgy S'\<close> bt unfolding full_def by auto
  have 3: "all_decomposition_implies_m
      (init_clss St)
      (get_all_marked_decomposition
         (trail St))"
   using rtranclp_cdcl\<^sub>W_all_inv(1)[OF st] no_d bt by simp
  have 4: "cdcl\<^sub>W_learned_clause St"
    using rtranclp_cdcl\<^sub>W_all_inv(2)[OF st] no_d bt bt by simp
  have 5: "cdcl\<^sub>W_M_level_inv St"
    using rtranclp_cdcl\<^sub>W_all_inv(3)[OF st] no_d bt by simp
  have 6: "no_strange_atm St"
    using rtranclp_cdcl\<^sub>W_all_inv(4)[OF st] no_d bt by simp
  have 7: "distinct_cdcl\<^sub>W_state St"
    using rtranclp_cdcl\<^sub>W_all_inv(5)[OF st] no_d bt by simp
  have 8: "cdcl\<^sub>W_conflicting St"
    using rtranclp_cdcl\<^sub>W_all_inv(6)[OF st] no_d bt by simp
  have "init_clss S' = init_clss St" and "conflicting S' = C_Clause {#}"
     using \<open>conflicting St \<noteq> C_True\<close> full_cdcl\<^sub>W_init_clss_with_false_normal_form[OF 1, of _ _ St]
     2 3 4 5 6 7 8 St apply (metis \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* St S'\<close> rtranclp_cdcl\<^sub>W_stgy_no_more_init_clss)
    using \<open>conflicting St \<noteq> C_True\<close> full_cdcl\<^sub>W_init_clss_with_false_normal_form[OF 1, of _ _ St _ _
      S'] 2 3 4 5 6 7 8 by (metis bt conflicting_clause.exhaust prod.inject)

  moreover have "init_clss S' = N"
    using \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) S'\<close> rtranclp_cdcl\<^sub>W_stgy_no_more_init_clss by fastforce
  moreover have "unsatisfiable (set_mset N)"
    by (meson empty mem_set_mset_iff satisfiable_def true_cls_empty true_clss_def)
  ultimately show ?thesis by auto
qed

(** prop 2.10.9 \cwref{lem:prop:cddlsoundtermStates}{}*)
lemma full_cdcl\<^sub>W_stgy_final_state_conclusive:
  fixes S' :: 'st
  assumes full: "full cdcl\<^sub>W_stgy (init_state N) S'" and no_d: "distinct_mset_mset N"
  shows "(conflicting S' = C_Clause {#} \<and> unsatisfiable (set_mset (init_clss S')))
    \<or> (conflicting S' = C_True \<and> trail S' \<Turnstile>asm init_clss S')"
  using assms full_cdcl\<^sub>W_stgy_final_state_conclusive_is_one_false
  full_cdcl\<^sub>W_stgy_final_state_conclusive_non_false by blast

lemma full_cdcl\<^sub>W_stgy_final_state_conclusive_from_init_state:
  fixes S' :: "'st"
  assumes full: "full cdcl\<^sub>W_stgy (init_state N) S'"
  and no_d: "distinct_mset_mset N"
  shows "(conflicting S' = C_Clause {#} \<and> unsatisfiable (set_mset N))
    \<or> (conflicting S' = C_True \<and> trail S' \<Turnstile>asm N \<and> satisfiable (set_mset N))"
proof -
  have N: "init_clss S' = N"
    using full unfolding full_def by (auto dest: rtranclp_cdcl\<^sub>W_stgy_no_more_init_clss)
  consider
      (confl) "conflicting S' = C_Clause {#}" and "unsatisfiable (set_mset (init_clss S'))"
    | (sat) "conflicting S' = C_True" and "trail S' \<Turnstile>asm init_clss S'"
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
      then have "consistent_interp (lits_of (trail S'))" unfolding cdcl\<^sub>W_M_level_inv_def by blast
      moreover have "lits_of (trail S') \<Turnstile>s set_mset (init_clss S')"
        using sat(2) by (auto simp add: true_annots_def true_annot_def true_clss_def)
      ultimately have "satisfiable (set_mset (init_clss S'))" by simp
      then show ?thesis using sat unfolding N by blast
    qed
qed
end
end
