theory CDCL_B
imports CDCL_W
begin

section \<open>A CDCL variant\<close>

type_synonym ('v, 'mark) ann_bat = \<open>('v literal list, 'v literal, 'mark) annotated_lit\<close>
type_synonym ('v, 'mark) ann_bats = \<open>('v, 'mark) ann_bat list\<close>
type_synonym 'v bat = \<open>'v literal list multiset\<close>
type_synonym 'v bats = \<open>'v bat list\<close>


fun lit_of\<^sub>B :: \<open>('v, 'mark) ann_bat \<Rightarrow> 'v literal set\<close> where
  \<open>lit_of\<^sub>B (Decided L) = set L\<close> |
  \<open>lit_of\<^sub>B (Propagated L _) = {L}\<close>

definition lits_of\<^sub>B :: \<open>('v, 'mark) ann_bat set \<Rightarrow> 'v literal set\<close> where
\<open>lits_of\<^sub>B Ls = \<Union>(lit_of\<^sub>B ` Ls)\<close>

abbreviation lits_of_l\<^sub>B :: \<open>('v, 'mark) ann_bats \<Rightarrow> 'v literal set\<close> where
\<open>lits_of_l\<^sub>B Ls \<equiv> lits_of\<^sub>B (set Ls)\<close>

definition true_annot\<^sub>B :: \<open>('v, 'mark) ann_bats \<Rightarrow> 'v clause \<Rightarrow> bool\<close> (infix "\<Turnstile>b" 49) where
  \<open>I \<Turnstile>b C \<longleftrightarrow> (lits_of_l\<^sub>B I) \<Turnstile> C\<close>

definition true_annots\<^sub>B :: \<open>('v, 'mark) ann_bats \<Rightarrow> 'v clause set \<Rightarrow> bool\<close> (infix "\<Turnstile>bs" 49) where
  \<open>I \<Turnstile>bs CC \<longleftrightarrow> (\<forall>C \<in> CC. I \<Turnstile>b C)\<close>  (* (set_mset CC). instead works *)

abbreviation true_annots\<^sub>B_mset :: \<open>('v, 'mark) ann_bats \<Rightarrow> 'v clauses \<Rightarrow> bool\<close> (infix "\<Turnstile>bsm" 49) where
  \<open>I \<Turnstile>bsm C \<equiv> I \<Turnstile>bs set_mset C\<close>

locale state\<^sub>B_ops =
  fixes
    state :: "'st \<Rightarrow> ('v, 'v clause) ann_bats \<times> 'v clauses \<times> 'v clauses \<times> 'v clause option \<times>
      'v bats \<times> 'b" and
    trail\<^sub>B :: "'st \<Rightarrow> ('v, 'v clause) ann_bats" and
    init_clss :: "'st \<Rightarrow> 'v clauses" and
    learned_clss :: "'st \<Rightarrow> 'v clauses" and
    conflicting :: "'st \<Rightarrow> 'v clause option" and
    bats :: \<open>'st \<Rightarrow> 'v bats\<close> and

    cons_trail\<^sub>B :: "('v, 'v clause) ann_bat \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail\<^sub>B :: "'st \<Rightarrow> 'st" and
    add_learned_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conflicting :: "'v clause option \<Rightarrow> 'st \<Rightarrow> 'st" and
    cons_bat :: \<open>'v bat \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    tl_bats :: \<open>'st \<Rightarrow> 'st\<close> and

    init_state :: "'v clauses \<Rightarrow> 'st"
begin
abbreviation hd_trail\<^sub>B :: "'st \<Rightarrow> ('v, 'v clause) ann_bat" where
"hd_trail\<^sub>B S \<equiv> hd (trail\<^sub>B S)"

definition additional_info\<^sub>B :: "'st \<Rightarrow> 'b" where
"additional_info\<^sub>B S = (\<lambda>(_, _, _, _, _, D). D) (state S)"

fun lits_of_bats :: \<open>('v, 'v clause) ann_bats \<Rightarrow> ('v, 'v clause) ann_lits\<close> where
  \<open>lits_of_bats [] = []\<close>
| \<open>lits_of_bats (Propagated L C # M) = Propagated L C # lits_of_bats M\<close>
| \<open>lits_of_bats (Decided Ls # M) = map Decided Ls @ lits_of_bats M\<close>

fun trail\<^sub>W :: \<open>'st \<Rightarrow> ('v, 'v clause) ann_lits\<close> where
  \<open>trail\<^sub>W S = lits_of_bats (trail\<^sub>B S)\<close>

definition state\<^sub>W :: "'st \<Rightarrow> ('v, 'v clause) ann_lits \<times> 'v clauses \<times> 'v clauses \<times>
  'v clause option \<times> 'v bats \<times> 'b" where
"state\<^sub>W S \<equiv> (trail\<^sub>W S, init_clss S, learned_clss S, conflicting S, bats S, additional_info\<^sub>B S)"

fun cons_trail\<^sub>W where
  \<open>cons_trail\<^sub>W (Decided L) S = cons_trail\<^sub>B (Decided [L]) S\<close>
| \<open>cons_trail\<^sub>W (Propagated L C) S = cons_trail\<^sub>B (Propagated L C) S\<close>

sublocale state\<^sub>W_ops where
  state = state\<^sub>W and
  trail = trail and
  init_clss = init_clss and
  learned_clss = learned_clss and
  conflicting = conflicting and
  cons_trail = cons_trail\<^sub>W and
  tl_trail = tl_trail\<^sub>B and
  add_learned_cls = add_learned_cls and
  remove_cls = remove_cls and
  update_conflicting = update_conflicting and
  init_state = init_state
  .

abbreviation state_butlast\<^sub>B :: "'st \<Rightarrow> ('v, 'v clause) ann_bats \<times> 'v clauses \<times> 'v clauses \<times>
  'v clause option \<times> 'v bats" where
"state_butlast\<^sub>B S \<equiv> (trail\<^sub>B S, init_clss S, learned_clss S, conflicting S, bats S)"

lemma lits_of_bats_append[simp]:
  \<open>lits_of_bats (xs @ ys) = lits_of_bats xs @ lits_of_bats ys\<close>
  by (induction xs rule: ann_lit_list_induct) auto

abbreviation backtrack_lvl\<^sub>B :: "'st \<Rightarrow> nat" where
\<open>backtrack_lvl\<^sub>B S \<equiv> count_decided (trail\<^sub>B S)\<close>

end

locale state\<^sub>B_no_state =
  state\<^sub>B_ops
    state
    \<comment> \<open>functions about the state: \<close>
      \<comment> \<open>getter:\<close>
    trail\<^sub>B init_clss learned_clss conflicting bats
      \<comment> \<open>setter:\<close>
    cons_trail\<^sub>B tl_trail\<^sub>B add_learned_cls remove_cls
    update_conflicting cons_bat tl_bats

      \<comment> \<open>Some specific states:\<close>
    init_state
  for
    state_eq :: "'st \<Rightarrow> 'st \<Rightarrow> bool" (infix "\<sim>" 50) and
    state :: "'st \<Rightarrow> ('v, 'v clause) ann_bats \<times> 'v clauses \<times> 'v clauses \<times> 'v clause option \<times>
      'v bats \<times> 'b" and
    trail\<^sub>B :: "'st \<Rightarrow> ('v, 'v clause) ann_bats" and
    init_clss :: "'st \<Rightarrow> 'v clauses" and
    learned_clss :: "'st \<Rightarrow> 'v clauses" and
    conflicting :: "'st \<Rightarrow> 'v clause option" and
    bats :: \<open>'st \<Rightarrow> 'v bats\<close> and

    cons_trail\<^sub>B :: "('v, 'v clause) ann_bat \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail\<^sub>B :: "'st \<Rightarrow> 'st" and
    add_learned_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conflicting :: "'v clause option \<Rightarrow> 'st \<Rightarrow> 'st" and
    cons_bat :: \<open>'v bat \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    tl_bats :: \<open>'st \<Rightarrow> 'st\<close> and

    init_state :: "'v clauses \<Rightarrow> 'st" +
  assumes
    state_eq_ref[simp, intro]: \<open>S \<sim> S\<close> and
    state_eq_sym: \<open>S \<sim> T \<longleftrightarrow> T \<sim> S\<close> and
    state_eq_trans: \<open>S \<sim> T \<Longrightarrow> T \<sim> U' \<Longrightarrow> S \<sim> U'\<close> and
    state_eq_state: \<open>S \<sim> T \<Longrightarrow> state S = state T\<close> and

    cons_trail\<^sub>B:
      "\<And>S'. state st = (M, S') \<Longrightarrow>
        state (cons_trail\<^sub>B L st) = (L # M, S')" and

    tl_trail\<^sub>B:
      "\<And>S'. state st = (M, S') \<Longrightarrow> state (tl_trail\<^sub>B st) = (tl M, S')" and

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
      "state_butlast\<^sub>B (init_state N) = ([], N, {#}, None, [])" and

    cons_trail\<^sub>B_state_eq:
      \<open>S \<sim> S' \<Longrightarrow> cons_trail\<^sub>B L S \<sim> cons_trail\<^sub>B L S'\<close> and

    tl_trail\<^sub>B_state_eq:
      \<open>S \<sim> S' \<Longrightarrow> tl_trail\<^sub>B S \<sim> tl_trail\<^sub>B S'\<close> and

    add_learned_cls_state_eq:
      \<open>S \<sim> S' \<Longrightarrow> add_learned_cls C S \<sim> add_learned_cls C S'\<close> and

    remove_cls_state_eq:
      \<open>S \<sim> S' \<Longrightarrow> remove_cls C S \<sim> remove_cls C S'\<close> and

    update_conflicting_state_eq:
      \<open>S \<sim> S' \<Longrightarrow> update_conflicting D S \<sim> update_conflicting D S'\<close> and

    tl_trail\<^sub>B_add_learned_cls_commute:
      \<open>tl_trail\<^sub>B (add_learned_cls C T) \<sim> add_learned_cls C (tl_trail\<^sub>B T)\<close> and
    tl_trail\<^sub>B_update_conflicting:
      \<open>tl_trail\<^sub>B (update_conflicting D T) \<sim> update_conflicting D (tl_trail\<^sub>B T)\<close> and

    cons_bat:
      "\<And>S'. state st = (M, N, U, D, B, S') \<Longrightarrow>
        state (cons_bat B' st) = (M, N, U, D, B' # B, S')" and
    tl_bats:
      "\<And>S'. state st = (M, N, U, D, B, S') \<Longrightarrow>
        state (tl_bats st) = (M, N, U, D, tl B, S')"

locale state\<^sub>B =
  state\<^sub>B_no_state
    state_eq state
    \<comment> \<open>functions about the state: \<close>
      \<comment> \<open>getter:\<close>
    trail\<^sub>B init_clss learned_clss conflicting bats
      \<comment> \<open>setter:\<close>
    cons_trail\<^sub>B tl_trail\<^sub>B add_learned_cls remove_cls
    update_conflicting cons_bat tl_bats

      \<comment> \<open>Some specific states:\<close>
    init_state
  for
    state_eq :: "'st \<Rightarrow> 'st \<Rightarrow> bool" (infix "\<sim>" 50) and
    state :: "'st \<Rightarrow> ('v, 'v clause) ann_bats \<times> 'v clauses \<times> 'v clauses \<times> 'v clause option \<times>
      'v bats \<times> 'b" and
    trail\<^sub>B :: "'st \<Rightarrow> ('v, 'v clause) ann_bats" and
    init_clss :: "'st \<Rightarrow> 'v clauses" and
    learned_clss :: "'st \<Rightarrow> 'v clauses" and
    conflicting :: "'st \<Rightarrow> 'v clause option" and
    bats :: \<open>'st \<Rightarrow> 'v bats\<close> and

    cons_trail\<^sub>B :: "('v, 'v clause) ann_bat \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail\<^sub>B :: "'st \<Rightarrow> 'st" and
    add_learned_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conflicting :: "'v clause option \<Rightarrow> 'st \<Rightarrow> 'st" and
    cons_bat :: \<open>'v bat \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    tl_bats :: \<open>'st \<Rightarrow> 'st\<close> and

    init_state :: "'v clauses \<Rightarrow> 'st" +
  assumes
    state_prop[simp]:
      \<open>state S = (trail\<^sub>B S, init_clss S, learned_clss S, conflicting S, bats S, additional_info\<^sub>B S)\<close>
begin

lemma
  trail\<^sub>B_cons_trail\<^sub>B[simp]:
    "trail\<^sub>B (cons_trail\<^sub>B L st) = L # trail\<^sub>B st" and
  trail\<^sub>B_tl_trail\<^sub>B[simp]: "trail\<^sub>B (tl_trail\<^sub>B st) = tl (trail\<^sub>B st)" and
  trail\<^sub>B_add_learned_cls[simp]:
    "trail\<^sub>B (add_learned_cls C st) = trail\<^sub>B st" and
  trail\<^sub>B_remove_cls[simp]:
    "trail\<^sub>B (remove_cls C st) = trail\<^sub>B st" and
  trail\<^sub>B_update_conflicting[simp]: "trail\<^sub>B (update_conflicting E st) = trail\<^sub>B st" and
  trail\<^sub>B_cons_bat[simp]:
    "trail\<^sub>B (cons_bat B st) = trail\<^sub>B st" and
  trail\<^sub>B_tl_bats[simp]:
    "trail\<^sub>B (tl_bats st) = trail\<^sub>B st" and

  init_clss_cons_trail\<^sub>B[simp]:
    "init_clss (cons_trail\<^sub>B M st) = init_clss st"
    and
  init_clss_tl_trail\<^sub>B[simp]:
    "init_clss (tl_trail\<^sub>B st) = init_clss st" and
  init_clss_add_learned_cls[simp]:
    "init_clss (add_learned_cls C st) = init_clss st" and
  init_clss_remove_cls[simp]:
    "init_clss (remove_cls C st) = removeAll_mset C (init_clss st)" and
  init_clss_update_conflicting[simp]:
    "init_clss (update_conflicting E st) = init_clss st" and
  init_clss_cons_bat[simp]:
    "init_clss (cons_bat B st) = init_clss st" and
  init_clss_tl_bats[simp]:
    "init_clss (tl_bats st) = init_clss st" and

  learned_clss_cons_trail\<^sub>B[simp]:
    "learned_clss (cons_trail\<^sub>B M st) = learned_clss st" and
  learned_clss_tl_trail\<^sub>B[simp]:
    "learned_clss (tl_trail\<^sub>B st) = learned_clss st" and
  learned_clss_add_learned_cls[simp]:
    "learned_clss (add_learned_cls C st) = {#C#} + learned_clss st" and
  learned_clss_remove_cls[simp]:
    "learned_clss (remove_cls C st) = removeAll_mset C (learned_clss st)" and
  learned_clss_update_conflicting[simp]:
    "learned_clss (update_conflicting E st) = learned_clss st" and
  learned_clss_cons_bat[simp]:
    "learned_clss (cons_bat B st) = learned_clss st" and
  learned_clss_tl_bats[simp]:
    "learned_clss (tl_bats st) = learned_clss st" and

  conflicting_cons_trail\<^sub>B[simp]:
    "conflicting (cons_trail\<^sub>B M st) = conflicting st" and
  conflicting_tl_trail\<^sub>B[simp]:
    "conflicting (tl_trail\<^sub>B st) = conflicting st" and
  conflicting_add_learned_cls[simp]:
    "conflicting (add_learned_cls C st) = conflicting st"
    and
  conflicting_remove_cls[simp]:
    "conflicting (remove_cls C st) = conflicting st" and
  conflicting_update_conflicting[simp]:
    "conflicting (update_conflicting E st) = E" and
  conflicting_cons_bat[simp]:
    "conflicting (cons_bat B st) = conflicting st" and
  conflicting_tl_bats[simp]:
    "conflicting (tl_bats st) = conflicting st" and

  bats_cons_trail\<^sub>B[simp]:
    "bats (cons_trail\<^sub>B M st) = bats st" and
  bats_tl_trail\<^sub>B[simp]:
    "bats (tl_trail\<^sub>B st) = bats st" and
  bats_add_learned_cls[simp]:
    "bats (add_learned_cls C st) = bats st"
    and
  bats_remove_cls[simp]:
    "bats (remove_cls C st) = bats st" and
  bats_update_bats[simp]:
    "bats (update_conflicting E st) = bats st" and
  bats_cons_bat[simp]:
    "bats (cons_bat B st) = B # bats st" and
  bats_tl_bats[simp]:
    "bats (tl_bats st) = tl (bats st)" and
  init_state_trail\<^sub>B[simp]: "trail\<^sub>B (init_state N) = []" and
  init_state_clss[simp]: "init_clss (init_state N) = N" and
  init_state_learned_clss[simp]: "learned_clss (init_state N) = {#}" and
  init_state_conflicting[simp]: "conflicting (init_state N) = None"
  using cons_trail\<^sub>B[of st] tl_trail\<^sub>B[of st] add_learned_cls[of st _ _ _ _ C]
    update_conflicting[of st _ _ _ _ _ _]
    remove_cls[of st _ _ _ _ C]
    init_state[of N]
    cons_bat[of st]
    tl_bats[of st]
  by fastforce+

lemma
  shows
    clauses_cons_trail\<^sub>B[simp]:
      "clauses (cons_trail\<^sub>B M S) = clauses S" and
    (* non-standard to avoid name clash with NOT's clauses_tl_trail\<^sub>B *)
    clss_tl_trail\<^sub>B[simp]: "clauses (tl_trail\<^sub>B S) = clauses S" and
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

named_theorems state_simp\<^sub>B \<open>contains all theorems of the form @{term \<open>S \<sim> T \<Longrightarrow> P S = P T\<close>}.
  These theorems can cause a signefecant blow-up of the simp-space\<close>

lemma
  shows
    state_eq_trail\<^sub>B[state_simp\<^sub>B]: "S \<sim> T \<Longrightarrow> trail\<^sub>B S = trail\<^sub>B T" and
    state_eq_init_clss[state_simp\<^sub>B]: "S \<sim> T \<Longrightarrow> init_clss S = init_clss T" and
    state_eq_learned_clss[state_simp\<^sub>B]: "S \<sim> T \<Longrightarrow> learned_clss S = learned_clss T" and
    state_eq_conflicting[state_simp\<^sub>B]: "S \<sim> T \<Longrightarrow> conflicting S = conflicting T" and
    state_eq_clauses[state_simp\<^sub>B]: "S \<sim> T \<Longrightarrow> clauses S = clauses T" and
    state_eq_undefined_lit[state_simp\<^sub>B]: "S \<sim> T \<Longrightarrow> undefined_lit (trail\<^sub>W S) L = undefined_lit (trail\<^sub>W T) L" and
    state_eq_backtrack_lvl[state_simp\<^sub>B]: "S \<sim> T \<Longrightarrow> backtrack_lvl\<^sub>B S = backtrack_lvl\<^sub>B T"
  using state_eq_state[of S T] unfolding clauses_def by auto


lemma state_eq_conflicting_None:
  "S \<sim> T \<Longrightarrow> conflicting T = None \<Longrightarrow> conflicting S = None"
  using state_eq_state unfolding clauses_def by auto

text \<open>We combine all simplification rules about @{term state_eq} in a single list of theorems. While
  they are handy as simplification rule as long as we are working on the state, they also cause a
  \<^emph>\<open>huge\<close> slow-down in all other cases.\<close>

declare state_simp\<^sub>B[simp]

function reduce_trail\<^sub>B_to :: "'a list \<Rightarrow> 'st \<Rightarrow> 'st" where
"reduce_trail\<^sub>B_to F S =
  (if length (trail\<^sub>B S) = length F \<or> trail\<^sub>B S = [] then S else reduce_trail\<^sub>B_to F (tl_trail\<^sub>B S))"
by fast+
termination
  by (relation "measure (\<lambda>(_, S). length (trail\<^sub>B S))") simp_all

declare reduce_trail\<^sub>B_to.simps[simp del]

lemma reduce_trail\<^sub>B_to_induct:
  assumes
    \<open>\<And>F S. length (trail\<^sub>B S) = length F \<Longrightarrow> P F S\<close> and
    \<open>\<And>F S. trail\<^sub>B S = [] \<Longrightarrow> P F S\<close> and
    \<open>\<And>F S. length (trail\<^sub>B S) \<noteq> length F \<Longrightarrow> trail\<^sub>B S \<noteq> [] \<Longrightarrow> P F (tl_trail\<^sub>B S) \<Longrightarrow> P F S\<close>
  shows
    \<open>P F S\<close>
  apply (induction rule: reduce_trail\<^sub>B_to.induct)
  apply (rename_tac F S)
  apply (case_tac \<open>length (trail\<^sub>B S) = length F\<close>)
    apply (simp add: assms(1); fail)
  apply (case_tac \<open>trail\<^sub>B S = []\<close>)
    apply (simp add: assms(2); fail)
  apply (simp add: assms(3); fail)
  done

lemma
  shows
    reduce_trail\<^sub>B_to_Nil[simp]: "trail\<^sub>B S = [] \<Longrightarrow> reduce_trail\<^sub>B_to F S = S" and
    reduce_trail\<^sub>B_to_eq_length[simp]: "length (trail\<^sub>B S) = length F \<Longrightarrow> reduce_trail\<^sub>B_to F S = S"
  by (auto simp: reduce_trail\<^sub>B_to.simps)

lemma reduce_trail\<^sub>B_to_length_ne:
  "length (trail\<^sub>B S) \<noteq> length F \<Longrightarrow> trail\<^sub>B S \<noteq> [] \<Longrightarrow>
    reduce_trail\<^sub>B_to F S = reduce_trail\<^sub>B_to F (tl_trail\<^sub>B S)"
  by (auto simp: reduce_trail\<^sub>B_to.simps)

lemma trail\<^sub>B_reduce_trail\<^sub>B_to_length_le:
  assumes "length F > length (trail\<^sub>B S)"
  shows "trail\<^sub>B (reduce_trail\<^sub>B_to F S) = []"
  using assms apply (induction F S rule: reduce_trail\<^sub>B_to.induct)
  by (metis (no_types, hide_lams) length_tl less_imp_diff_less less_irrefl trail\<^sub>B_tl_trail\<^sub>B
    reduce_trail\<^sub>B_to.simps)

lemma trail\<^sub>B_reduce_trail\<^sub>B_to_Nil[simp]:
  "trail\<^sub>B (reduce_trail\<^sub>B_to [] S) = []"
  apply (induction "[]::('v, 'v clause) ann_lits" S rule: reduce_trail\<^sub>B_to.induct)
  by (metis length_0_conv reduce_trail\<^sub>B_to_length_ne reduce_trail\<^sub>B_to_Nil)

lemma clauses_reduce_trail\<^sub>B_to_Nil:
  "clauses (reduce_trail\<^sub>B_to [] S) = clauses S"
proof (induction "[]" S rule: reduce_trail\<^sub>B_to.induct)
  case (1 Sa)
  then have "clauses (reduce_trail\<^sub>B_to ([]::'a list) (tl_trail\<^sub>B Sa)) = clauses (tl_trail\<^sub>B Sa)
    \<or> trail\<^sub>B Sa = []"
    by fastforce
  then show "clauses (reduce_trail\<^sub>B_to ([]::'a list) Sa) = clauses Sa"
    by (metis (no_types) length_0_conv reduce_trail\<^sub>B_to_eq_length clss_tl_trail\<^sub>B
      reduce_trail\<^sub>B_to_length_ne)
qed

lemma reduce_trail\<^sub>B_to_skip_beginning:
  assumes "trail\<^sub>B S = F' @ F"
  shows "trail\<^sub>B (reduce_trail\<^sub>B_to F S) = F"
  using assms by (induction F' arbitrary: S) (auto simp: reduce_trail\<^sub>B_to_length_ne)

lemma clauses_reduce_trail\<^sub>B_to[simp]:
  "clauses (reduce_trail\<^sub>B_to F S) = clauses S"
  apply (induction F S rule: reduce_trail\<^sub>B_to.induct)
  by (metis clss_tl_trail\<^sub>B reduce_trail\<^sub>B_to.simps)

lemma conflicting_update_trail\<^sub>B[simp]:
  "conflicting (reduce_trail\<^sub>B_to F S) = conflicting S"
  apply (induction F S rule: reduce_trail\<^sub>B_to.induct)
  by (metis conflicting_tl_trail\<^sub>B reduce_trail\<^sub>B_to.simps)

lemma init_clss_update_trail\<^sub>B[simp]:
  "init_clss (reduce_trail\<^sub>B_to F S) = init_clss S"
  apply (induction F S rule: reduce_trail\<^sub>B_to.induct)
  by (metis init_clss_tl_trail\<^sub>B reduce_trail\<^sub>B_to.simps)

lemma learned_clss_update_trail\<^sub>B[simp]:
  "learned_clss (reduce_trail\<^sub>B_to F S) = learned_clss S"
  apply (induction F S rule: reduce_trail\<^sub>B_to.induct)
  by (metis learned_clss_tl_trail\<^sub>B reduce_trail\<^sub>B_to.simps)

lemma conflicting_reduce_trail\<^sub>B_to[simp]:
  "conflicting (reduce_trail\<^sub>B_to F S) = None \<longleftrightarrow> conflicting S = None"
  apply (induction F S rule: reduce_trail\<^sub>B_to.induct)
  by (metis conflicting_update_trail\<^sub>B)

lemma bats_reduce_trail\<^sub>B_to[simp]: \<open>bats (reduce_trail\<^sub>B_to F S) = bats S\<close>
  apply (induction F S rule: reduce_trail\<^sub>B_to.induct)
  by (simp add: reduce_trail\<^sub>B_to.simps)

lemma trail\<^sub>B_eq_reduce_trail\<^sub>B_to_eq:
  "trail\<^sub>B S = trail\<^sub>B T \<Longrightarrow> trail\<^sub>B (reduce_trail\<^sub>B_to F S) = trail\<^sub>B (reduce_trail\<^sub>B_to F T)"
  by (induction F S arbitrary: T rule: reduce_trail\<^sub>B_to_induct) (auto simp: reduce_trail\<^sub>B_to_length_ne)

lemma reduce_trail\<^sub>B_to_trail\<^sub>B_tl_trail\<^sub>B_decomp[simp]:
  "trail\<^sub>B S = F' @ Decision K a # F \<Longrightarrow> trail\<^sub>B (reduce_trail\<^sub>B_to F S) = F "
  apply (rule reduce_trail\<^sub>B_to_skip_beginning[of _ "F' @ Decision K a # []"])
  by (cases F') (auto simp add: tl_append reduce_trail\<^sub>B_to_skip_beginning)

lemma reduce_trail\<^sub>B_to_add_learned_cls[simp]:
  "trail\<^sub>B (reduce_trail\<^sub>B_to F (add_learned_cls C S)) = trail\<^sub>B (reduce_trail\<^sub>B_to F S)"
  by (rule trail\<^sub>B_eq_reduce_trail\<^sub>B_to_eq) auto

lemma reduce_trail\<^sub>B_to_remove_learned_cls[simp]:
  "trail\<^sub>B (reduce_trail\<^sub>B_to F (remove_cls C S)) = trail\<^sub>B (reduce_trail\<^sub>B_to F S)"
  by (rule trail\<^sub>B_eq_reduce_trail\<^sub>B_to_eq) auto

lemma reduce_trail\<^sub>B_to_update_conflicting[simp]:
  "trail\<^sub>B (reduce_trail\<^sub>B_to F (update_conflicting C S)) = trail\<^sub>B (reduce_trail\<^sub>B_to F S)"
  by (rule trail\<^sub>B_eq_reduce_trail\<^sub>B_to_eq) auto

lemma reduce_trail\<^sub>B_to_length:
  "length M = length M' \<Longrightarrow> reduce_trail\<^sub>B_to M S = reduce_trail\<^sub>B_to M' S"
  apply (induction M S rule: reduce_trail\<^sub>B_to.induct)
  by (simp add: reduce_trail\<^sub>B_to.simps)

lemma trail\<^sub>B_reduce_trail\<^sub>B_to_drop:
  "trail\<^sub>B (reduce_trail\<^sub>B_to F S) =
    (if length (trail\<^sub>B S) \<ge> length F
    then drop (length (trail\<^sub>B S) - length F) (trail\<^sub>B S)
    else [])"
  apply (induction F S rule: reduce_trail\<^sub>B_to.induct)
  apply (rename_tac F S, case_tac "trail\<^sub>B S")
   apply auto[]
  apply (rename_tac list, case_tac "Suc (length list) > length F")
   prefer 2 apply (metis diff_is_0_eq drop_Cons' length_Cons nat_le_linear nat_less_le
     reduce_trail\<^sub>B_to_eq_length trail\<^sub>B_reduce_trail\<^sub>B_to_length_le)
  apply (subgoal_tac "Suc (length list) - length F = Suc (length list - length F)")
  by (auto simp add: reduce_trail\<^sub>B_to_length_ne)

lemma in_get_all_ann_decomposition_trail\<^sub>B_update_trail\<^sub>B[simp]:
  assumes H: "(L # M1, M2) \<in> set (get_all_ann_decomposition (trail\<^sub>B S))"
  shows "trail\<^sub>B (reduce_trail\<^sub>B_to M1 S) = M1"
proof -
  obtain K where
    L: "L = Decided K"
    using H by (cases L) (auto dest!: in_get_all_ann_decomposition_decided_or_empty)
  obtain c where
    tr_S: "trail\<^sub>B S = c @ M2 @ L # M1"
    using H by auto
  show ?thesis
    by (rule reduce_trail\<^sub>B_to_trail\<^sub>B_tl_trail\<^sub>B_decomp[of _ "c @ M2" _ K]) (auto simp: tr_S L)
qed

lemma reduce_trail\<^sub>B_to_state_eq:
  \<open>S \<sim> S' \<Longrightarrow> length M = length M' \<Longrightarrow> reduce_trail\<^sub>B_to M S \<sim> reduce_trail\<^sub>B_to M' S'\<close>
  apply (induction M S arbitrary: M' S' rule: reduce_trail\<^sub>B_to_induct)
   apply auto[2]
  by (simp add: reduce_trail\<^sub>B_to_length_ne tl_trail\<^sub>B_state_eq)

lemma conflicting_cons_trail\<^sub>B_conflicting[iff]:
  "conflicting (cons_trail\<^sub>B L S) = None \<longleftrightarrow> conflicting S = None"
  using conflicting_cons_trail\<^sub>B[of L S] map_option_is_None by fastforce+

lemma conflicting_add_learned_cls_conflicting[iff]:
  "conflicting (add_learned_cls C S) = None \<longleftrightarrow> conflicting S = None"
  by fastforce+

lemma
  additional_info\<^sub>B_cons_trail\<^sub>B[simp]:
    \<open>additional_info\<^sub>B (cons_trail\<^sub>B L S) = additional_info\<^sub>B S\<close> and
  additional_info\<^sub>B_tl_trail\<^sub>B[simp]:
    "additional_info\<^sub>B (tl_trail\<^sub>B S) = additional_info\<^sub>B S" and
  additional_info\<^sub>B_add_learned_cls_unfolded:
    "additional_info\<^sub>B (add_learned_cls U S) = additional_info\<^sub>B S"  and
  additional_info\<^sub>B_update_conflicting[simp]:
    "additional_info\<^sub>B (update_conflicting D S) = additional_info\<^sub>B S" and
  additional_info\<^sub>B_remove_cls[simp]:
    "additional_info\<^sub>B (remove_cls C S) = additional_info\<^sub>B S" and
  additional_info\<^sub>B_add_learned_cls[simp]:
    "additional_info\<^sub>B (add_learned_cls C S) = additional_info\<^sub>B S"
  unfolding additional_info\<^sub>B_def
    using tl_trail\<^sub>B[of S] cons_trail\<^sub>B[of S] add_learned_cls[of S]
    update_conflicting[of S] remove_cls[of S]
  by (cases \<open>state S\<close>; auto; fail)+

lemma additional_info_reduce_trail\<^sub>B_to[simp]:
  \<open>additional_info\<^sub>B (reduce_trail\<^sub>B_to F S) = additional_info\<^sub>B S\<close>
  apply (induction F S rule: reduce_trail\<^sub>B_to.induct)
  by (smt prod.inject reduce_trail\<^sub>B_to_Nil reduce_trail\<^sub>B_to_eq_length reduce_trail\<^sub>B_to_length_ne
      state_prop tl_trail\<^sub>B)

lemma reduce_trail\<^sub>B_to:
  "state (reduce_trail\<^sub>B_to F S) =
    ((if length (trail\<^sub>B S) \<ge> length F
    then drop (length (trail\<^sub>B S) - length F) (trail\<^sub>B S)
    else []), init_clss S, learned_clss S, conflicting S, bats S, additional_info\<^sub>B S)"
proof (induction F S rule: reduce_trail\<^sub>B_to.induct)
  case (1 F S) note IH = this
  show ?case
  proof (cases "trail\<^sub>B S")
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
        using Cons True reduce_trail\<^sub>B_to_length_ne[of S F] IH by (auto simp del: state_prop)
    next
      case False
      then show ?thesis
        using IH reduce_trail\<^sub>B_to_length_ne[of S F] apply (subst state_prop)
        by (simp add: trail\<^sub>B_reduce_trail\<^sub>B_to_drop)
    qed
  qed
qed

end \<comment> \<open>end of locale @{locale state\<^sub>B}\<close>


subsection \<open>CDCL Rules\<close>

fun restrict_clause_2fold :: \<open>'a list \<Rightarrow> 'a \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset\<close> where
  \<open>restrict_clause_2fold Ls l C = (if l \<in> set Ls then add_mset l C else C)\<close>

definition restrict_clause :: \<open>'a list \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset\<close> where
  \<open>restrict_clause Ls C = fold_mset (restrict_clause_2fold Ls) {#} C\<close>

lemma restrict_clause_filter_mset: \<open>restrict_clause Ls C = filter_mset (\<lambda>L. L \<in># mset Ls) C\<close>
proof -
  have [simp]: \<open>comp_fun_commute (restrict_clause_2fold Ls)\<close> for Ls
    unfolding comp_fun_commute_def by auto
  show ?thesis
    unfolding restrict_clause_def
    apply (induction C arbitrary: Ls)
    subgoal for C by auto
    subgoal for L C Ls
      by (auto simp del: restrict_clause_2fold.simps simp: comp_fun_commute.fold_mset_add_mset
          restrict_clause_2fold.simps)
    done
qed

fun restrict :: \<open>'v list \<Rightarrow> 'v multiset multiset \<Rightarrow> 'v multiset multiset\<close> where
  \<open>restrict Ls Cs = image_mset (restrict_clause Ls) Cs\<close>

lemma restrict_filter_mset: \<open>restrict Ls Cs = {#filter_mset (\<lambda>L. L \<in># mset Ls) C. C \<in># Cs #}\<close>
  unfolding restrict.simps restrict_clause_filter_mset ..


locale conflict_driven_clause_learning\<^sub>B =
  state\<^sub>B
    state_eq
    state
    \<comment> \<open>functions for the state: \<close>
      \<comment> \<open>access functions:\<close>
    trail\<^sub>B init_clss learned_clss conflicting bats
      \<comment> \<open>changing state:\<close>
    cons_trail\<^sub>B tl_trail\<^sub>B add_learned_cls remove_cls
    update_conflicting cons_bat tl_bats

      \<comment> \<open>get state:\<close>
    init_state
  for
    state_eq :: "'st \<Rightarrow> 'st \<Rightarrow> bool" (infix "\<sim>" 50) and
    state :: "'st \<Rightarrow> ('v, 'v clause) ann_bats \<times> 'v clauses \<times> 'v clauses \<times> 'v clause option \<times>
      'v bats \<times> 'b" and
    trail\<^sub>B :: "'st \<Rightarrow> ('v, 'v clause) ann_bats" and
    init_clss :: "'st \<Rightarrow> 'v clauses" and
    learned_clss :: "'st \<Rightarrow> 'v clauses" and
    conflicting :: "'st \<Rightarrow> 'v clause option" and
    bats :: \<open>'st \<Rightarrow> 'v bats\<close> and

    cons_trail\<^sub>B :: "('v, 'v clause) ann_bat \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail\<^sub>B :: "'st \<Rightarrow> 'st" and
    add_learned_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conflicting :: "'v clause option \<Rightarrow> 'st \<Rightarrow> 'st" and
    cons_bat :: \<open>'v bat \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    tl_bats :: \<open>'st \<Rightarrow> 'st\<close> and

    init_state :: "'v clauses \<Rightarrow> 'st"
begin

declare state_prop[simp del]

inductive propagate\<^sub>B :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
propagate_rule: "conflicting S = None \<Longrightarrow>
  E \<in># clauses S \<Longrightarrow>
  L \<in># E \<Longrightarrow>
  trail\<^sub>B S \<Turnstile>bs CNot (E - {#L#}) \<Longrightarrow> (* to adapt *)
  (* undefined_lit (trail\<^sub>B S) L \<Longrightarrow> (* to adapt *) *)
  T \<sim> cons_trail\<^sub>B (Propagated L E) S \<Longrightarrow>
  propagate\<^sub>B S T"

inductive_cases propagate\<^sub>BE: "propagate\<^sub>B S T"
thm propagate\<^sub>BE

definition valid_bats :: \<open>('v, 'v clause) ann_bats \<Rightarrow> 'v clauses \<Rightarrow> 'v bat \<Rightarrow> bool\<close> where
  \<open>valid_bats M N B \<longleftrightarrow>
    (\<forall>Ls \<in># B. consistent_interp (set Ls)) \<and>
    (\<forall>Ls \<in># B. \<forall>L \<in> set Ls. -L \<notin> lits_of_l\<^sub>B M) \<and>
    (\<forall>Ls \<in># B. \<exists>I. (set Ls \<subseteq> I \<and> I \<Turnstile>sm (restrict Ls N))) \<and> (* new constraint *)
    (\<forall>I. I \<Turnstile>sm N \<longrightarrow> lits_of_l\<^sub>B M \<subseteq> I \<longrightarrow> (\<exists>Ls \<in># B. set Ls \<subseteq> I))\<close>

inductive decide\<^sub>B :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> for S :: 'st where
decide\<^sub>B_rule:
  \<open>decide\<^sub>B S T\<close>
  if
    \<open>T \<sim> cons_trail\<^sub>B (Decided B) (cons_bat (remove1_mset B Bs) S)\<close> and
    \<open>B \<in># Bs\<close> and
    \<open>valid_bats (trail\<^sub>B S) (clauses S) Bs\<close>

inductive conflict\<^sub>B :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
conflict_rule: "
  conflicting S = None \<Longrightarrow>
  D \<in># clauses S \<Longrightarrow>
  trail\<^sub>B S \<Turnstile>bs CNot D \<Longrightarrow>  (* to adapt *)
  T \<sim> update_conflicting (Some D) S \<Longrightarrow>
  conflict\<^sub>B S T"

inductive_cases conflict\<^sub>BE: \<open>conflict\<^sub>B S T\<close>

inductive skip\<^sub>B :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
skip_rule:
  "trail\<^sub>B S = Propagated L C' # M \<Longrightarrow>
   conflicting S = Some E \<Longrightarrow>
   -L \<notin># E \<Longrightarrow>
   E \<noteq> {#} \<Longrightarrow>
   T \<sim> tl_trail\<^sub>B S \<Longrightarrow>
   skip\<^sub>B S T"

inductive_cases skip\<^sub>BE: "skip\<^sub>B S T"

inductive resolve\<^sub>B :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
resolve_rule: "trail\<^sub>B S \<noteq> [] \<Longrightarrow>
  hd_trail S = Propagated L E \<Longrightarrow>
  L \<in># E \<Longrightarrow>
  conflicting S = Some D' \<Longrightarrow>
  -L \<in># D' \<Longrightarrow>
  (* get_maximum_level (trail\<^sub>B S) ((remove1_mset (-L) D')) = backtrack_lvl\<^sub>B S \<Longrightarrow> *) (* to adapt *)
  T \<sim> update_conflicting (Some (resolve_cls L D' E))
    (tl_trail\<^sub>B S) \<Longrightarrow>
  resolve\<^sub>B S T"

inductive_cases resolve\<^sub>BE: "resolve\<^sub>B S T"

end

end