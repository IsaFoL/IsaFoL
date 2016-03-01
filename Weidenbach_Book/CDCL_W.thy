theory CDCL_W
imports Partial_Annotated_Clausal_Logic List_More CDCL_W_Level Wellfounded_More

begin

section \<open>Weidenbach's CDCL\<close>
declare upt.simps(2)[simp del]

subsection \<open>The State\<close>
text \<open>We will abstract the representation of clause and clauses via two locales. We expect our
  representation to behave like multiset, but the internal representation can be done using list
  or whatever other representation.\<close>
locale clause =
  fixes
    mset_cls:: "'cls \<Rightarrow> 'v clause" and
    union_cls :: "'cls \<Rightarrow> 'cls \<Rightarrow> 'cls" and
    insert_cls :: "'v literal \<Rightarrow> 'cls \<Rightarrow> 'cls" and
    remove_lit :: "'v literal \<Rightarrow> 'cls \<Rightarrow> 'cls"
  assumes
    insert_cls[simp]: "mset_cls (insert_cls L C) = mset_cls C + {#L#}" and
    mset_cls_union_cls[simp]: "mset_cls (union_cls C D) = mset_cls C #\<union> mset_cls D" and
    remove_lit[simp]: "mset_cls (remove_lit L C) = remove1_mset L (mset_cls C)"
begin
(*

remove1_lit ? (closer to the mset definition and better)
*)
term  Set.remove
end

text \<open>This is a copy of the unnamed theorem of @{file "~~/src/HOL/Library/Multiset.thy"}.\<close>
lemma union_mset_list:
  "mset xs #\<union> mset ys =
    mset (case_prod append (fold (\<lambda>x (ys, zs). (remove1 x ys, x # zs)) xs (ys, [])))"
proof -
  have "\<And>zs. mset (case_prod append (fold (\<lambda>x (ys, zs). (remove1 x ys, x # zs)) xs (ys, zs))) =
      (mset xs #\<union> mset ys) + mset zs"
    by (induct xs arbitrary: ys) (simp_all add: multiset_eq_iff)
  then show ?thesis by simp
qed

text \<open>Instanciation of the previous locale, in an unnamed context to avoid polluating with simp
  rules\<close>
context
begin
  interpretation list_cls: clause mset
    "\<lambda>xs ys. case_prod append (fold (\<lambda>x (ys, zs). (remove1 x ys, x # zs)) xs (ys, []))"
    "op #" remove1
    by unfold_locales (auto simp: union_mset_list)

  interpretation cls_cls: clause id
    "op #\<union>" "\<lambda>L C. C + {#L#}" remove1_mset
    by unfold_locales (auto simp: union_mset_list)
end

locale clauses =
  clause mset_cls union_cls insert_cls remove_lit
  for
    mset_cls:: "'cls \<Rightarrow> 'v clause" and
    union_cls :: "'cls \<Rightarrow> 'cls \<Rightarrow> 'cls" and
    insert_cls :: "'v literal \<Rightarrow> 'cls \<Rightarrow> 'cls" and
    remove_lit :: "'v literal \<Rightarrow> 'cls \<Rightarrow> 'cls" +
  fixes
    mset_clss:: "'clss \<Rightarrow> 'v clauses" and
    union_clss :: "'clss \<Rightarrow> 'clss \<Rightarrow> 'clss" and
    in_clss :: "'cls \<Rightarrow> 'clss \<Rightarrow> bool" and
    insert_clss :: "'cls \<Rightarrow> 'clss \<Rightarrow> 'clss" and
    remove_from_clss :: "'cls \<Rightarrow> 'clss \<Rightarrow> 'clss"
  assumes
    insert_clss[simp]: "mset_clss (insert_clss L C) = mset_clss C + {#mset_cls L#}" and
    union_clss[simp]: "mset_clss (union_clss C D) = mset_clss C + mset_clss D" and
    mset_clss_union_clss[simp]: "mset_clss (insert_clss C' D) = {#mset_cls C'#} + mset_clss D" and
    in_clss_mset_clss[dest]: "in_clss a C \<Longrightarrow> mset_cls a \<in># mset_clss C" and
    in_mset_clss_exists_preimage: "b \<in># mset_clss C \<Longrightarrow> \<exists>b'. in_clss b' C \<and> mset_cls b' = b" and
    remove_from_clss_mset_clss[simp]:
      "mset_clss (remove_from_clss a C) = mset_clss C - {#mset_cls a#}" and
    in_clss_union_clss[simp]:
      "in_clss a (union_clss C D) \<longleftrightarrow> in_clss a C \<or> in_clss a D"
begin

end

experiment
begin
  fun remove_first where
  "remove_first _ [] = []" |
  "remove_first C (C' # L) = (if mset C = mset C' then L else C' # remove_first C L)"

  lemma remove1_mset_single_add:
    "a \<noteq> b \<Longrightarrow> remove1_mset a ({#b#} + C) = {#b#} + remove1_mset a C"
    "remove1_mset a ({#a#} + C) = C"
    by (auto simp: multiset_eq_iff)

  lemma mset_map_mset_remove_first:
    "mset (map mset (remove_first a C)) = remove1_mset (mset a) (mset (map mset C))"
    by (induction C) (auto simp: ac_simps remove1_mset_single_add)

  interpretation clss_clss: clauses id "op #\<union>" "\<lambda>L C. C + {#L#}" remove1_mset
    id "op +" "op \<in>#" "\<lambda>L C. C + {#L#}" remove1_mset
    by unfold_locales (auto simp: ac_simps)

  interpretation list_clss: clauses mset
    "\<lambda>xs ys. case_prod append (fold (\<lambda>x (ys, zs). (remove1 x ys, x # zs)) xs (ys, []))"
    "op #" remove1 "\<lambda>L. mset (map mset L)" "op @" "\<lambda>L C. L \<in> set C" "op #"
    remove_first
    by unfold_locales (auto simp: ac_simps union_mset_list mset_map_mset_remove_first)
end

locale state\<^sub>W_ops =
  clauses mset_cls union_cls insert_cls remove_lit
    mset_clss union_clss in_clss insert_clss remove_from_clss
    +
  clause mset_ccls union_ccls insert_ccls remove_clit
  for
    -- \<open>Clause\<close>
    mset_cls:: "'cls \<Rightarrow> 'v clause" and
    union_cls :: "'cls \<Rightarrow> 'cls \<Rightarrow> 'cls" and
    insert_cls :: "'v literal \<Rightarrow> 'cls \<Rightarrow> 'cls" and
    remove_lit :: "'v literal \<Rightarrow> 'cls \<Rightarrow> 'cls" and

    -- \<open>Multiset of Clauses\<close>
    mset_clss:: "'clss \<Rightarrow> 'v clauses" and
    union_clss :: "'clss \<Rightarrow> 'clss \<Rightarrow> 'clss" and
    in_clss :: "'cls \<Rightarrow> 'clss \<Rightarrow> bool" and
    insert_clss :: "'cls \<Rightarrow> 'clss \<Rightarrow> 'clss" and
    remove_from_clss :: "'cls \<Rightarrow> 'clss \<Rightarrow> 'clss"  and

    mset_ccls:: "'ccls \<Rightarrow> 'v clause" and
    union_ccls :: "'ccls \<Rightarrow> 'ccls \<Rightarrow> 'ccls" and
    insert_ccls :: "'v literal \<Rightarrow> 'ccls \<Rightarrow> 'ccls" and
    remove_clit :: "'v literal \<Rightarrow> 'ccls \<Rightarrow> 'ccls"
    +
  fixes
    ccls_of_cls :: "'cls \<Rightarrow> 'ccls" and
    cls_of_ccls :: "'ccls \<Rightarrow> 'cls" and

    trail :: "'st \<Rightarrow> ('v, nat, 'v clause) marked_lits" and
    hd_raw_trail :: "'st \<Rightarrow> ('v, nat, 'cls) marked_lit" and
    raw_init_clss :: "'st \<Rightarrow> 'clss" and
    raw_learned_clss :: "'st \<Rightarrow> 'clss" and
    backtrack_lvl :: "'st \<Rightarrow> nat" and
    raw_conflicting :: "'st \<Rightarrow> 'ccls option" and

    cons_trail :: "('v, nat, 'cls) marked_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_init_cls :: "'cls \<Rightarrow> 'st \<Rightarrow> 'st" and
    add_learned_cls :: "'cls \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'cls \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_backtrack_lvl :: "nat \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conflicting :: "'ccls option \<Rightarrow> 'st \<Rightarrow> 'st" and

    init_state :: "'clss \<Rightarrow> 'st" and
    restart_state :: "'st \<Rightarrow> 'st"
  assumes
    mset_ccls_ccls_of_cls[simp]:
      "mset_ccls (ccls_of_cls C) = mset_cls C" and
    mset_cls_cls_of_ccls[simp]:
      "mset_cls (cls_of_ccls D) = mset_ccls D"
begin
fun mmset_of_mlit ::  "('a, 'b, 'cls) marked_lit \<Rightarrow>  ('a, 'b, 'v clause) marked_lit"
  where
"mmset_of_mlit (Propagated L C) = Propagated L (mset_cls C)" |
"mmset_of_mlit (Marked L i) = Marked L i"

lemma lit_of_mmset_of_mlit[simp]:
  "lit_of (mmset_of_mlit a) = lit_of a"
  by (cases a) auto

abbreviation "init_clss \<equiv> \<lambda>S. mset_clss (raw_init_clss S)"
abbreviation "learned_clss \<equiv> \<lambda>S. mset_clss (raw_learned_clss S)"
abbreviation "conflicting \<equiv> \<lambda>S. map_option mset_ccls (raw_conflicting S)"

notation insert_cls (infix "!++" 50)

notation in_clss (infix "!\<in>!" 50)
notation union_clss (infix "\<oplus>" 50)
notation insert_clss (infix "!++!" 50)

notation union_ccls (infix "!\<union>" 50)

definition raw_clauses :: "'st \<Rightarrow> 'clss" where
"raw_clauses S = union_clss (raw_init_clss S) (raw_learned_clss S)"

abbreviation clauses :: "'st \<Rightarrow> 'v clauses" where
"clauses S \<equiv> mset_clss (raw_clauses S)"

end

locale state\<^sub>W =
  state\<^sub>W_ops
    -- \<open>functions for clauses: \<close>
    mset_cls union_cls insert_cls remove_lit
      mset_clss union_clss in_clss insert_clss remove_from_clss

    -- \<open>functions for the conflicting clause: \<close>
    mset_ccls union_ccls insert_ccls remove_clit

    -- \<open>Conversion between conflicting and non-conflicting\<close>
    ccls_of_cls cls_of_ccls

    -- \<open>functions for the state: \<close>
      -- \<open>access functions:\<close>
    trail hd_raw_trail raw_init_clss raw_learned_clss backtrack_lvl raw_conflicting
      -- \<open>changing state:\<close>
    cons_trail tl_trail add_init_cls add_learned_cls remove_cls update_backtrack_lvl
    update_conflicting

      -- \<open>get state:\<close>
    init_state
    restart_state
  for
    mset_cls:: "'cls \<Rightarrow> 'v clause" and
    union_cls :: "'cls \<Rightarrow> 'cls \<Rightarrow> 'cls" and
    insert_cls :: "'v literal \<Rightarrow> 'cls \<Rightarrow> 'cls" and
    remove_lit :: "'v literal \<Rightarrow> 'cls \<Rightarrow> 'cls" and


    mset_clss:: "'clss \<Rightarrow> 'v clauses" and
    union_clss :: "'clss \<Rightarrow> 'clss \<Rightarrow> 'clss" and
    in_clss :: "'cls \<Rightarrow> 'clss \<Rightarrow> bool" and
    insert_clss :: "'cls \<Rightarrow> 'clss \<Rightarrow> 'clss" and
    remove_from_clss :: "'cls \<Rightarrow> 'clss \<Rightarrow> 'clss" and

    mset_ccls:: "'ccls \<Rightarrow> 'v clause" and
    union_ccls :: "'ccls \<Rightarrow> 'ccls \<Rightarrow> 'ccls" and
    insert_ccls :: "'v literal \<Rightarrow> 'ccls \<Rightarrow> 'ccls" and
    remove_clit :: "'v literal \<Rightarrow> 'ccls \<Rightarrow> 'ccls" and

    ccls_of_cls :: "'cls \<Rightarrow> 'ccls" and
    cls_of_ccls :: "'ccls \<Rightarrow> 'cls" and

    trail :: "'st \<Rightarrow> ('v, nat, 'v clause) marked_lits" and
    hd_raw_trail :: "'st \<Rightarrow> ('v, nat, 'cls) marked_lit" and
    raw_init_clss :: "'st \<Rightarrow> 'clss" and
    raw_learned_clss :: "'st \<Rightarrow> 'clss" and
    backtrack_lvl :: "'st \<Rightarrow> nat" and
    raw_conflicting :: "'st \<Rightarrow> 'ccls option" and

    cons_trail :: "('v, nat, 'cls) marked_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_init_cls :: "'cls \<Rightarrow> 'st \<Rightarrow> 'st" and
    add_learned_cls :: "'cls \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'cls \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_backtrack_lvl :: "nat \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conflicting :: "'ccls option \<Rightarrow> 'st \<Rightarrow> 'st" and

    init_state :: "'clss \<Rightarrow> 'st" and
    restart_state :: "'st \<Rightarrow> 'st" +
  assumes
    hd_raw_trail: "trail S \<noteq> [] \<Longrightarrow> mmset_of_mlit (hd_raw_trail S) = hd (trail S)" and
    trail_cons_trail[simp]:
      "\<And>L st. undefined_lit (trail st) (lit_of L) \<Longrightarrow>
        trail (cons_trail L st) = mmset_of_mlit L # trail st" and
    trail_tl_trail[simp]: "\<And>st. trail (tl_trail st) = tl (trail st)" and
    trail_add_init_cls[simp]:
      "\<And>st C. no_dup (trail st) \<Longrightarrow> trail (add_init_cls C st) = trail st" and
    trail_add_learned_cls[simp]:
      "\<And>C st. no_dup (trail st) \<Longrightarrow> trail (add_learned_cls C st) = trail st" and
    trail_remove_cls[simp]:
      "\<And>C st. trail (remove_cls C st) = trail st" and
    trail_update_backtrack_lvl[simp]: "\<And>st C. trail (update_backtrack_lvl C st) = trail st" and
    trail_update_conflicting[simp]: "\<And>C st. trail (update_conflicting C st) = trail st" and

    init_clss_cons_trail[simp]:
      "\<And>M st. undefined_lit (trail st) (lit_of M) \<Longrightarrow>
        raw_init_clss (cons_trail M st) = raw_init_clss st"
      and
    init_clss_tl_trail[simp]:
      "\<And>st. raw_init_clss (tl_trail st) = raw_init_clss st" and
    init_clss_add_init_cls[simp]:
      "\<And>st C. no_dup (trail st) \<Longrightarrow> init_clss (add_init_cls C st) = {#mset_cls C#} + init_clss st"
      and
    init_clss_add_learned_cls[simp]:
      "\<And>C st. no_dup (trail st) \<Longrightarrow> raw_init_clss (add_learned_cls C st) = raw_init_clss st" and
    init_clss_remove_cls[simp]:
      "\<And>C st. init_clss (remove_cls C st) = removeAll_mset (mset_cls C) (init_clss st)" and
    init_clss_update_backtrack_lvl[simp]:
      "\<And>st C. raw_init_clss (update_backtrack_lvl C st) = raw_init_clss st" and
    init_clss_update_conflicting[simp]:
      "\<And>C st. raw_init_clss (update_conflicting C st) = raw_init_clss st" and

    learned_clss_cons_trail[simp]:
      "\<And>M st. undefined_lit (trail st) (lit_of M) \<Longrightarrow>
        raw_learned_clss (cons_trail M st) = raw_learned_clss st" and
    learned_clss_tl_trail[simp]:
      "\<And>st. raw_learned_clss (tl_trail st) = raw_learned_clss st" and
    learned_clss_add_init_cls[simp]:
      "\<And>st C. no_dup (trail st) \<Longrightarrow> raw_learned_clss (add_init_cls C st) = raw_learned_clss st" and
    learned_clss_add_learned_cls[simp]:
      "\<And>C st. no_dup (trail st) \<Longrightarrow>
        learned_clss (add_learned_cls C st) = {#mset_cls C#} + learned_clss st" and
    learned_clss_remove_cls[simp]:
      "\<And>C st. learned_clss (remove_cls C st) = removeAll_mset (mset_cls C) (learned_clss st)" and
    learned_clss_update_backtrack_lvl[simp]:
      "\<And>st C. raw_learned_clss (update_backtrack_lvl C st) = raw_learned_clss st" and
    learned_clss_update_conflicting[simp]:
      "\<And>C st. raw_learned_clss (update_conflicting C st) = raw_learned_clss st" and

    backtrack_lvl_cons_trail[simp]:
      "\<And>M st. undefined_lit (trail st) (lit_of M) \<Longrightarrow>
        backtrack_lvl (cons_trail M st) = backtrack_lvl st" and
    backtrack_lvl_tl_trail[simp]:
      "\<And>st. backtrack_lvl (tl_trail st) = backtrack_lvl st" and
    backtrack_lvl_add_init_cls[simp]:
      "\<And>st C. no_dup (trail st) \<Longrightarrow> backtrack_lvl (add_init_cls C st) = backtrack_lvl st" and
    backtrack_lvl_add_learned_cls[simp]:
      "\<And>C st. no_dup (trail st) \<Longrightarrow> backtrack_lvl (add_learned_cls C st) = backtrack_lvl st" and
    backtrack_lvl_remove_cls[simp]:
      "\<And>C st. backtrack_lvl (remove_cls C st) = backtrack_lvl st" and
    backtrack_lvl_update_backtrack_lvl[simp]:
      "\<And>st k. backtrack_lvl (update_backtrack_lvl k st) = k" and
    backtrack_lvl_update_conflicting[simp]:
      "\<And>C st. backtrack_lvl (update_conflicting C st) = backtrack_lvl st" and

    conflicting_cons_trail[simp]:
      "\<And>M st. undefined_lit (trail st) (lit_of M) \<Longrightarrow>
        raw_conflicting (cons_trail M st) = raw_conflicting st" and
    conflicting_tl_trail[simp]:
      "\<And>st. raw_conflicting (tl_trail st) = raw_conflicting st" and
    conflicting_add_init_cls[simp]:
      "\<And>st C. no_dup (trail st) \<Longrightarrow> raw_conflicting (add_init_cls C st) = raw_conflicting st" and
    conflicting_add_learned_cls[simp]:
      "\<And>C st. no_dup (trail st) \<Longrightarrow> raw_conflicting (add_learned_cls C st) = raw_conflicting st"
      and
    conflicting_remove_cls[simp]:
      "\<And>C st. raw_conflicting (remove_cls C st) = raw_conflicting st" and
    conflicting_update_backtrack_lvl[simp]:
      "\<And>st C. raw_conflicting (update_backtrack_lvl C st) = raw_conflicting st" and
    conflicting_update_conflicting[simp]:
      "\<And>C st. raw_conflicting (update_conflicting C st) = C" and

    init_state_trail[simp]: "\<And>N. trail (init_state N) = []" and
    init_state_clss[simp]: "\<And>N. (init_clss (init_state N)) = mset_clss N" and
    init_state_learned_clss[simp]: "\<And>N. learned_clss (init_state N) = {#}" and
    init_state_backtrack_lvl[simp]: "\<And>N. backtrack_lvl (init_state N) = 0" and
    init_state_conflicting[simp]: "\<And>N. conflicting (init_state N) = None" and

    trail_restart_state[simp]: "trail (restart_state S) = []" and
    init_clss_restart_state[simp]: "init_clss (restart_state S) = init_clss S" and
    learned_clss_restart_state[intro]:
      "learned_clss (restart_state S) \<subseteq># learned_clss S" and
    backtrack_lvl_restart_state[simp]: "backtrack_lvl (restart_state S) = 0" and
    conflicting_restart_state[simp]: "conflicting (restart_state S) = None"
begin


lemma
  shows
    clauses_cons_trail[simp]:
      "undefined_lit (trail S) (lit_of M) \<Longrightarrow> clauses (cons_trail M S) = clauses S" and
    (* non-standard to avoid name clash with NOT's clauses_tl_trail *)
    clss_tl_trail[simp]: "clauses (tl_trail S) = clauses S" and
    clauses_add_learned_cls_unfolded:
      "no_dup (trail S) \<Longrightarrow> clauses (add_learned_cls U S) =
         {#mset_cls U#} + learned_clss S + init_clss S"
      and
    clauses_add_init_cls[simp]:
      "no_dup (trail S) \<Longrightarrow>
        clauses (add_init_cls N S) = {#mset_cls N#} + init_clss S + learned_clss S" and
    clauses_update_backtrack_lvl[simp]: "clauses (update_backtrack_lvl k S) = clauses S" and
    clauses_update_conflicting[simp]: "clauses (update_conflicting D S) = clauses S" and
    clauses_remove_cls[simp]:
      "clauses (remove_cls C S) = removeAll_mset (mset_cls C) (clauses S)" and
    clauses_add_learned_cls[simp]:
      "no_dup (trail S) \<Longrightarrow> clauses (add_learned_cls C S) = {#mset_cls C#} + clauses S" and
    clauses_restart[simp]: "clauses (restart_state S) \<subseteq># clauses S" and
    clauses_init_state[simp]: "\<And>N. clauses (init_state N) = mset_clss N"
    prefer 9 using raw_clauses_def learned_clss_restart_state apply fastforce
    by (auto simp: ac_simps replicate_mset_plus raw_clauses_def intro: multiset_eqI)

abbreviation state ::  "'st \<Rightarrow> ('v, nat, 'v clause) marked_lit list \<times> 'v clauses \<times> 'v clauses
  \<times> nat \<times> 'v clause option" where
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
  unfolding state_eq_def raw_clauses_def by auto

lemma state_eq_raw_conflicting_None:
  "S \<sim> T \<Longrightarrow> conflicting T = None \<Longrightarrow> raw_conflicting S = None"
  unfolding state_eq_def raw_clauses_def by auto

lemmas state_simp[simp] = state_eq_trail state_eq_init_clss state_eq_learned_clss
  state_eq_backtrack_lvl state_eq_conflicting state_eq_clauses state_eq_undefined_lit
  state_eq_raw_conflicting_None

lemma atms_of_ms_learned_clss_restart_state_in_atms_of_ms_learned_clssI[intro]:
  "x \<in> atms_of_mm (learned_clss (restart_state S)) \<Longrightarrow> x \<in> atms_of_mm (learned_clss S)"
  by (meson atms_of_ms_mono learned_clss_restart_state set_mset_mono subsetCE)

function reduce_trail_to :: "'a list \<Rightarrow> 'st \<Rightarrow> 'st" where
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
  apply (induction "[]::('v, nat, 'v clause) marked_lits" S rule: reduce_trail_to.induct)
  by (metis length_0_conv reduce_trail_to_length_ne reduce_trail_to_nil)

lemma clauses_reduce_trail_to_nil:
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
  "no_dup (trail S) \<Longrightarrow>
    trail (reduce_trail_to F (add_learned_cls C S)) = trail (reduce_trail_to F S)"
  by (rule trail_eq_reduce_trail_to_eq) auto

lemma reduce_trail_to_add_init_cls[simp]:
  "no_dup (trail S) \<Longrightarrow>
    trail (reduce_trail_to F (add_init_cls C S)) = trail (reduce_trail_to F S)"
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

fun append_trail :: "('v, nat, 'cls) marked_lit list \<Rightarrow> 'st \<Rightarrow> 'st"  where
"append_trail [] S = S" |
"append_trail (L # M) S = append_trail M (cons_trail L S)"

lemma trail_append_trail:
  "no_dup ((map mmset_of_mlit M) @ trail S) \<Longrightarrow>
    trail (append_trail M S) = rev (map mmset_of_mlit M) @ trail S"
  by (induction M arbitrary: S) (auto simp: defined_lit_map)

lemma init_clss_append_trail:
  "no_dup ((map mmset_of_mlit M) @ trail S) \<Longrightarrow> init_clss (append_trail M S) = init_clss S"
  by (induction M arbitrary: S) (auto simp: defined_lit_map)

lemma learned_clss_append_trail:
  "no_dup ((map mmset_of_mlit M) @ trail S) \<Longrightarrow> learned_clss (append_trail M S) = learned_clss S"
  by (induction M arbitrary: S) (auto simp: defined_lit_map)

lemma conflicting_append_trail:
  "no_dup ((map mmset_of_mlit M) @ trail S) \<Longrightarrow> conflicting (append_trail M S) = conflicting S"
  by (induction M arbitrary: S) (auto simp: defined_lit_map)

lemma backtrack_lvl_append_trail:
  "no_dup ((map mmset_of_mlit M) @ trail S) \<Longrightarrow> backtrack_lvl (append_trail M S) = backtrack_lvl S"
  by (induction M arbitrary: S) (auto simp: defined_lit_map)

lemma clauses_append_trail:
  "no_dup ((map mmset_of_mlit M) @ trail S) \<Longrightarrow> clauses (append_trail M S) = clauses S"
  by (induction M arbitrary: S) (auto simp: defined_lit_map)

lemmas state_append_trail_simp =
  trail_append_trail init_clss_append_trail learned_clss_append_trail backtrack_lvl_append_trail
  clauses_append_trail conflicting_append_trail

text \<open>This function is useful for proofs to speak of a global trail change, but is a bad for
  programs and code in general.\<close>
abbreviation delete_trail_and_rebuild where
"delete_trail_and_rebuild M S == append_trail (rev M) (reduce_trail_to ([]:: 'v list) S)"

end -- \<open>end of \<open>state\<^sub>W\<close> locale\<close>


subsection \<open>CDCL Rules\<close>
text \<open>Because of the strategy we will later use, we distinguish propagate, conflict from the other
  rules\<close>
locale conflict_driven_clause_learning\<^sub>W =
  state\<^sub>W
    -- \<open>functions for clauses: \<close>
    mset_cls union_cls insert_cls remove_lit
    mset_clss union_clss in_clss insert_clss remove_from_clss

    -- \<open>functions for the conflicting clause: \<close>
    mset_ccls union_ccls insert_ccls remove_clit

    -- \<open>conversion\<close>
    ccls_of_cls cls_of_ccls

    -- \<open>functions for the state: \<close>
      -- \<open>access functions:\<close>
    trail hd_raw_trail raw_init_clss raw_learned_clss backtrack_lvl raw_conflicting
      -- \<open>changing state:\<close>
    cons_trail tl_trail add_init_cls add_learned_cls remove_cls update_backtrack_lvl
    update_conflicting

      -- \<open>get state:\<close>
    init_state
    restart_state
  for
    mset_cls:: "'cls \<Rightarrow> 'v clause" and
    union_cls :: "'cls \<Rightarrow> 'cls \<Rightarrow> 'cls" and
    union_clss :: "'clss \<Rightarrow> 'clss \<Rightarrow> 'clss" and
    insert_cls :: "'v literal \<Rightarrow> 'cls \<Rightarrow> 'cls" and
    remove_lit :: "'v literal \<Rightarrow> 'cls \<Rightarrow> 'cls" and

    mset_clss:: "'clss \<Rightarrow> 'v clauses" and
    in_clss :: "'cls \<Rightarrow> 'clss \<Rightarrow> bool" and
    insert_clss :: "'cls \<Rightarrow> 'clss \<Rightarrow> 'clss" and
    remove_from_clss :: "'cls \<Rightarrow> 'clss \<Rightarrow> 'clss"  and

    mset_ccls:: "'ccls \<Rightarrow> 'v clause" and
    union_ccls :: "'ccls \<Rightarrow> 'ccls \<Rightarrow> 'ccls" and
    insert_ccls :: "'v literal \<Rightarrow> 'ccls \<Rightarrow> 'ccls" and
    remove_clit :: "'v literal \<Rightarrow> 'ccls \<Rightarrow> 'ccls" and

    ccls_of_cls :: "'cls \<Rightarrow> 'ccls" and
    cls_of_ccls :: "'ccls \<Rightarrow> 'cls" and

    trail :: "'st \<Rightarrow> ('v, nat, 'v clause) marked_lits" and
    hd_raw_trail :: "'st \<Rightarrow> ('v, nat, 'cls) marked_lit" and
    raw_init_clss :: "'st \<Rightarrow> 'clss" and
    raw_learned_clss :: "'st \<Rightarrow> 'clss" and
    backtrack_lvl :: "'st \<Rightarrow> nat" and
    raw_conflicting :: "'st \<Rightarrow> 'ccls option" and

    cons_trail :: "('v, nat, 'cls) marked_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_init_cls :: "'cls \<Rightarrow> 'st \<Rightarrow> 'st" and
    add_learned_cls :: "'cls \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'cls \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_backtrack_lvl :: "nat \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conflicting :: "'ccls option \<Rightarrow> 'st \<Rightarrow> 'st" and

    init_state :: "'clss \<Rightarrow> 'st" and
    restart_state :: "'st \<Rightarrow> 'st"
begin

inductive propagate :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
propagate_rule: "conflicting S = None \<Longrightarrow>
  E !\<in>! raw_clauses S \<Longrightarrow>
  L \<in># mset_cls E \<Longrightarrow>
  trail S \<Turnstile>as CNot (mset_cls (remove_lit L E)) \<Longrightarrow>
  undefined_lit (trail S) L \<Longrightarrow>
  T \<sim> cons_trail (Propagated L E) S \<Longrightarrow>
  propagate S T"

inductive_cases propagateE: "propagate S T"

inductive conflict ::  "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
conflict_rule: "
  conflicting S = None \<Longrightarrow>
  D !\<in>! raw_clauses S \<Longrightarrow>
  trail S \<Turnstile>as CNot (mset_cls D) \<Longrightarrow>
  T \<sim> update_conflicting (Some (ccls_of_cls D)) S \<Longrightarrow>
  conflict S T"

inductive_cases conflictE: "conflict S T"

inductive backtrack ::  "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
backtrack_rule: "
  raw_conflicting S = Some D \<Longrightarrow>
  L \<in># mset_ccls D \<Longrightarrow>
  (Marked K (i+1) # M1, M2) \<in> set (get_all_marked_decomposition (trail S)) \<Longrightarrow>
  get_level (trail S) L = backtrack_lvl S \<Longrightarrow>
  get_level (trail S) L = get_maximum_level (trail S) (mset_ccls D) \<Longrightarrow>
  get_maximum_level (trail S) (mset_ccls (remove_clit L D)) \<equiv> i \<Longrightarrow>
  T \<sim> cons_trail (Propagated L (cls_of_ccls D))
            (reduce_trail_to M1
              (add_learned_cls (cls_of_ccls D)
                (update_backtrack_lvl i
                  (update_conflicting None S)))) \<Longrightarrow>
  backtrack S T"

inductive_cases backtrackE: "backtrack S T"
thm backtrackE

inductive decide ::  "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
decide_rule:
  "conflicting S = None \<Longrightarrow>
  undefined_lit (trail S) L \<Longrightarrow>
  atm_of L \<in> atms_of_mm (init_clss S) \<Longrightarrow>
  T \<sim> cons_trail (Marked L (backtrack_lvl S +1)) (incr_lvl S) \<Longrightarrow>
  decide S T"

inductive_cases decideE: "decide S T"

inductive skip :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
skip_rule:
  "trail S = Propagated L C' # M \<Longrightarrow>
   raw_conflicting S = Some E \<Longrightarrow>
   -L \<notin># mset_ccls E \<Longrightarrow>
   mset_ccls E \<noteq> {#} \<Longrightarrow>
   T \<sim> tl_trail S \<Longrightarrow>
   skip S T"

(* TODO? inductive_cases skipE: "skip S T" *)
inductive_cases skipE: "skip S T"

text \<open>@{term "get_maximum_level (Propagated L (C + {#L#}) # M) D = k \<or> k = 0"} (that was in a
  previous version of the book) is equivalent to
  @{term "get_maximum_level (Propagated L (C + {#L#}) # M) D = k"}, when the structural invariants
  holds.\<close>

inductive resolve :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
resolve_rule: "trail S \<noteq> [] \<Longrightarrow>
  hd_raw_trail S  = Propagated L E \<Longrightarrow>
  L \<in># mset_cls E \<Longrightarrow>
  raw_conflicting S = Some D' \<Longrightarrow>
  -L \<in># mset_ccls D' \<Longrightarrow>
  get_maximum_level (trail S) (mset_ccls (remove_clit (-L) D')) = backtrack_lvl S \<Longrightarrow>
  T \<sim> update_conflicting (Some (union_ccls (remove_clit (-L) D') (ccls_of_cls (remove_lit L E))))
    (tl_trail S) \<Longrightarrow>
  resolve S T"

inductive_cases resolveE: "resolve S T"

inductive restart :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
restart: "state S = (M, N, U, k, None) \<Longrightarrow> \<not>M \<Turnstile>asm clauses S
  \<Longrightarrow> T \<sim> restart_state S
  \<Longrightarrow> restart S T"

inductive_cases restartE: "restart S T"

text \<open>We add the condition @{term "C \<notin># init_clss S"}, to maintain consistency even without the
  strategy.\<close>
inductive forget:: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
forget_rule:
  "conflicting S = None \<Longrightarrow>
  C !\<in>! raw_learned_clss S \<Longrightarrow>
  \<not>(trail S) \<Turnstile>asm clauses S \<Longrightarrow>
  mset_cls C \<notin> set (get_all_mark_of_propagated (trail S)) \<Longrightarrow>
  mset_cls C \<notin># init_clss S \<Longrightarrow>
  T \<sim> remove_cls C S \<Longrightarrow>
  forget S T"

inductive_cases forgetE: "forget S T"

inductive cdcl\<^sub>W_rf :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
restart: "restart S T \<Longrightarrow> cdcl\<^sub>W_rf S T" |
forget: "forget S T \<Longrightarrow> cdcl\<^sub>W_rf S T"

inductive cdcl\<^sub>W_bj ::  "'st \<Rightarrow> 'st \<Rightarrow> bool" where
skip: "skip S S' \<Longrightarrow> cdcl\<^sub>W_bj S S'" |
resolve: "resolve S S' \<Longrightarrow> cdcl\<^sub>W_bj S S'" |
backtrack: "backtrack S S' \<Longrightarrow> cdcl\<^sub>W_bj S S'"

inductive_cases cdcl\<^sub>W_bjE: "cdcl\<^sub>W_bj S T"

inductive cdcl\<^sub>W_o:: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
decide: "decide S S' \<Longrightarrow> cdcl\<^sub>W_o S S'" |
bj: "cdcl\<^sub>W_bj S S' \<Longrightarrow> cdcl\<^sub>W_o S S'"

inductive cdcl\<^sub>W :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
propagate: "propagate S S' \<Longrightarrow> cdcl\<^sub>W S S'" |
conflict: "conflict S S' \<Longrightarrow> cdcl\<^sub>W S S'" |
other: "cdcl\<^sub>W_o S S' \<Longrightarrow> cdcl\<^sub>W S S'"|
rf: "cdcl\<^sub>W_rf S S' \<Longrightarrow> cdcl\<^sub>W S S'"

lemma rtranclp_propagate_is_rtranclp_cdcl\<^sub>W:
  "propagate\<^sup>*\<^sup>* S S' \<Longrightarrow> cdcl\<^sub>W\<^sup>*\<^sup>* S S'"
  apply (induction rule: rtranclp_induct)
    apply simp
  apply (frule propagate)
  using rtranclp_trans[of cdcl\<^sub>W] by blast

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
    propagateH: "\<And>C L T. conflicting S = None \<Longrightarrow>
       C !\<in>! raw_clauses S \<Longrightarrow>
       L \<in># mset_cls C \<Longrightarrow>
       trail S \<Turnstile>as CNot (remove1_mset L (mset_cls C)) \<Longrightarrow>
       undefined_lit (trail S) L \<Longrightarrow>
       T \<sim> cons_trail (Propagated L C) S \<Longrightarrow>
       P S T" and
    conflictH: "\<And>D T.  conflicting S = None \<Longrightarrow>
       D !\<in>! raw_clauses S \<Longrightarrow>
       trail S \<Turnstile>as CNot (mset_cls D) \<Longrightarrow>
       T \<sim> update_conflicting (Some (ccls_of_cls D)) S \<Longrightarrow>
       P S T" and
    forgetH: "\<And>C U T. conflicting S = None \<Longrightarrow>
      C !\<in>! raw_learned_clss S \<Longrightarrow>
      \<not>(trail S) \<Turnstile>asm clauses S \<Longrightarrow>
      mset_cls C \<notin> set (get_all_mark_of_propagated (trail S)) \<Longrightarrow>
      mset_cls C \<notin># init_clss S \<Longrightarrow>
      T \<sim> remove_cls C S \<Longrightarrow>
      P S T" and
    restartH: "\<And>T. \<not>trail S \<Turnstile>asm clauses S \<Longrightarrow>
      conflicting S = None \<Longrightarrow>
      T \<sim> restart_state S \<Longrightarrow>
      P S T" and
    decideH: "\<And>L T. conflicting S = None \<Longrightarrow>
      undefined_lit (trail S) L \<Longrightarrow>
      atm_of L \<in> atms_of_mm (init_clss S) \<Longrightarrow>
      T \<sim> cons_trail (Marked L (backtrack_lvl S +1)) (incr_lvl S) \<Longrightarrow>
      P S T" and
    skipH: "\<And>L C' M E T.
      trail S = Propagated L C' # M \<Longrightarrow>
      raw_conflicting S = Some E \<Longrightarrow>
      -L \<notin># mset_ccls E \<Longrightarrow>  mset_ccls E \<noteq> {#} \<Longrightarrow>
      T \<sim> tl_trail S \<Longrightarrow>
      P S T" and
    resolveH: "\<And>L E M D T.
      trail S = Propagated L (mset_cls E) # M \<Longrightarrow>
      L \<in># mset_cls E \<Longrightarrow>
      hd_raw_trail S  = Propagated L E \<Longrightarrow>
      raw_conflicting S = Some D \<Longrightarrow>
      -L \<in># mset_ccls D \<Longrightarrow>
      get_maximum_level (trail S) (mset_ccls (remove_clit (-L) D)) = backtrack_lvl S \<Longrightarrow>
      T \<sim> update_conflicting (Some (union_ccls (remove_clit (-L) D) (ccls_of_cls (remove_lit L E))))
        (tl_trail S) \<Longrightarrow>
      P S T" and
    backtrackH: "\<And>L D K i M1 M2 T.
      raw_conflicting S = Some D \<Longrightarrow>
      L \<in># mset_ccls D \<Longrightarrow>
      (Marked K (i+1) # M1, M2) \<in> set (get_all_marked_decomposition (trail S)) \<Longrightarrow>
      get_level (trail S) L = backtrack_lvl S \<Longrightarrow>
      get_level (trail S) L = get_maximum_level (trail S) (mset_ccls D) \<Longrightarrow>
      get_maximum_level (trail S) (remove1_mset L (mset_ccls D)) \<equiv> i \<Longrightarrow>
      T \<sim> cons_trail (Propagated L (cls_of_ccls D))
                (reduce_trail_to M1
                  (add_learned_cls (cls_of_ccls D)
                    (update_backtrack_lvl i
                      (update_conflicting None S)))) \<Longrightarrow>
       P S T"
  shows "P S S'"
  using cdcl\<^sub>W
proof (induct S S' rule: cdcl\<^sub>W_all_rules_induct)
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
    using hd_raw_trail[of S] by (cases "trail S") (auto elim!: resolveE intro!: resolveH)
qed

lemma cdcl\<^sub>W_o_induct[consumes 1, case_names decide skip resolve backtrack]:
  fixes S  :: "'st"
  assumes cdcl\<^sub>W: "cdcl\<^sub>W_o S T" and
    decideH: "\<And>L T. conflicting S = None \<Longrightarrow>  undefined_lit (trail S) L
      \<Longrightarrow> atm_of L \<in> atms_of_mm (init_clss S)
      \<Longrightarrow> T \<sim> cons_trail (Marked L (backtrack_lvl S +1)) (incr_lvl S)
      \<Longrightarrow> P S T" and
    skipH: "\<And>L C' M E T.
      trail S = Propagated L C' # M \<Longrightarrow>
      raw_conflicting S = Some E \<Longrightarrow>
      -L \<notin># mset_ccls E \<Longrightarrow>  mset_ccls E \<noteq> {#} \<Longrightarrow>
      T \<sim> tl_trail S \<Longrightarrow>
      P S T" and
    resolveH: "\<And>L E M D T.
      trail S = Propagated L (mset_cls E) # M \<Longrightarrow>
      L \<in># mset_cls E \<Longrightarrow>
      hd_raw_trail S  = Propagated L E \<Longrightarrow>
      raw_conflicting S = Some D \<Longrightarrow>
      -L \<in># mset_ccls D \<Longrightarrow>
      get_maximum_level (trail S) (mset_ccls (remove_clit (-L) D)) = backtrack_lvl S \<Longrightarrow>
      T \<sim> update_conflicting (Some (union_ccls (remove_clit (-L) D) (ccls_of_cls (remove_lit L E))))
        (tl_trail S) \<Longrightarrow>
      P S T" and
    backtrackH: "\<And>L D K i M1 M2 T.
      raw_conflicting S = Some D \<Longrightarrow>
      L \<in># mset_ccls D \<Longrightarrow>
      (Marked K (i+1) # M1, M2) \<in> set (get_all_marked_decomposition (trail S)) \<Longrightarrow>
      get_level (trail S) L = backtrack_lvl S \<Longrightarrow>
      get_level (trail S) L = get_maximum_level (trail S) (mset_ccls D) \<Longrightarrow>
      get_maximum_level (trail S) (remove1_mset L (mset_ccls D)) \<equiv> i \<Longrightarrow>
      T \<sim> cons_trail (Propagated L (cls_of_ccls D))
                (reduce_trail_to M1
                  (add_learned_cls (cls_of_ccls D)
                    (update_backtrack_lvl i
                      (update_conflicting None S)))) \<Longrightarrow>
       P S T"
  shows "P S T"
  using cdcl\<^sub>W apply (induct T rule: cdcl\<^sub>W_o.induct)
   using assms(2) apply (auto elim: decideE)[1]
  apply (elim cdcl\<^sub>W_bjE skipE resolveE backtrackE)
    apply (frule skipH; simp)
    using hd_raw_trail[of S] apply (cases "trail S"; auto elim!: resolveE intro!: resolveH)
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
  assumes
    L: "get_level (trail S) L = backtrack_lvl S" and
    M1: "(Marked K (i + 1) # M1, M2) \<in> set (get_all_marked_decomposition (trail S))" and
    no_dup: "no_dup (trail S)" and
    bt_l: "backtrack_lvl S = length (get_all_levels_of_marked (trail S))" and
    order: "get_all_levels_of_marked (trail S)
    = rev [1..<(1+length (get_all_levels_of_marked (trail S)))]"
  shows "atm_of L \<notin> atm_of ` lits_of_l M1"
proof (rule ccontr)
  let ?M = "trail S"
  assume L_in_M1: "\<not>atm_of L \<notin> atm_of ` lits_of_l M1"
  obtain c where
    Mc: "trail S = c @ M2 @ Marked K (i + 1) # M1"
    using M1 by blast
  have "atm_of L \<notin> atm_of ` lits_of_l c"
    using L_in_M1 no_dup unfolding Mc lits_of_def by force
  have g_M_eq_g_M1: "get_level ?M L = get_level M1 L"
    using L_in_M1 unfolding Mc by auto
  have g: "get_all_levels_of_marked M1 = rev [1..<Suc i]"
    using order unfolding Mc by (auto simp del: upt_simps simp: rev_swap[symmetric]
      dest: append_cons_eq_upt_length_i)
  then have "Max (set (0 # get_all_levels_of_marked (rev M1))) < Suc i" by auto
  then have "get_level M1 L < Suc i"
    using get_rev_level_less_max_get_all_levels_of_marked[of "rev M1" 0 L] by linarith
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
  case (backtrack L D K i M1 M2 T) note decomp = this(3) and L = this(4) and T = this(7) and
    n_d = this(8)
  obtain c where Mc: "trail S = c @ M2 @ Marked K (i + 1) # M1"
    using decomp by auto
  have "no_dup (M2 @ Marked K (i + 1) # M1)"
    using Mc n_d by fastforce
  moreover have "atm_of L \<notin> (\<lambda>l. atm_of (lit_of l)) ` set M1"
    using backtrack_lit_skiped[of S L K i M1 M2] L decomp backtrack.prems
    by (fastforce simp: lits_of_def)
  moreover then have "undefined_lit M1 L"
     by (simp add: defined_lit_map)
  ultimately show ?case using decomp T n_d by simp
qed (auto simp: defined_lit_map)

lemma cdcl\<^sub>W_consistent_inv_2:
  assumes
    "cdcl\<^sub>W S S'" and
    "no_dup (trail S)" and
    "backtrack_lvl S = length (get_all_levels_of_marked (trail S))" and
    "get_all_levels_of_marked (trail S) = rev [1..<1+length (get_all_levels_of_marked (trail S))]"
  shows "consistent_interp (lits_of_l (trail S'))"
  using cdcl\<^sub>W_distinctinv_1[OF assms] distinct_consistent_interp by fast

lemma cdcl\<^sub>W_o_bt:
  assumes
    "cdcl\<^sub>W_o S S'" and
    "backtrack_lvl S = length (get_all_levels_of_marked (trail S))" and
    "get_all_levels_of_marked (trail S) =
      rev ([1..<(1+length (get_all_levels_of_marked (trail S)))])" and
    n_d[simp]: "no_dup (trail S)"
  shows "backtrack_lvl S' = length (get_all_levels_of_marked (trail S'))"
  using assms
proof (induct rule: cdcl\<^sub>W_o_induct)
  case (backtrack L D K i M1 M2 T) note decomp = this(3) and T = this(7) and level = this(9)
  have [simp]: "trail (reduce_trail_to M1 S) = M1"
    using decomp by auto
  obtain c where M: "trail S = c @ M2 @ Marked K (i + 1) # M1" using decomp by auto
  have "rev (get_all_levels_of_marked (trail S))
    = [1..<1+ (length (get_all_levels_of_marked (trail S)))]"
    using level by (auto simp: rev_swap[symmetric])
  moreover have "atm_of L \<notin> (\<lambda>l. atm_of (lit_of l)) ` set M1"
    using backtrack_lit_skiped[of S L K i M1 M2] backtrack(4,8,9) decomp
    by (fastforce simp add: lits_of_def)
  moreover then have "undefined_lit M1 L"
     by (simp add: defined_lit_map)
  moreover then have "no_dup (trail T)"
    using T decomp n_d by (auto simp: defined_lit_map M)
  ultimately show ?case
    using T n_d unfolding M by (auto dest!: append_cons_eq_upt_length simp del: upt_simps)
qed auto

lemma cdcl\<^sub>W_rf_bt:
  assumes
    "cdcl\<^sub>W_rf S S'" and
    "backtrack_lvl S = length (get_all_levels_of_marked (trail S))" and
    "get_all_levels_of_marked (trail S) = rev [1..<(1+length (get_all_levels_of_marked (trail S)))]"
  shows "backtrack_lvl S' = length (get_all_levels_of_marked (trail S'))"
  using assms by (induct rule: cdcl\<^sub>W_rf.induct) (auto elim: restartE forgetE)

lemma cdcl\<^sub>W_bt:
  assumes
    "cdcl\<^sub>W S S'" and
    "backtrack_lvl S = length (get_all_levels_of_marked (trail S))" and
    "get_all_levels_of_marked (trail S)
    = rev ([1..<(1+length (get_all_levels_of_marked (trail S)))])" and
    "no_dup (trail S)"
  shows "backtrack_lvl S' = length (get_all_levels_of_marked (trail S'))"
  using assms by (induct rule: cdcl\<^sub>W.induct) (auto simp add: cdcl\<^sub>W_o_bt cdcl\<^sub>W_rf_bt
    elim: conflictE propagateE)

lemma cdcl\<^sub>W_bt_level':
  assumes
    "cdcl\<^sub>W S S'" and
    "backtrack_lvl S = length (get_all_levels_of_marked (trail S))" and
    "get_all_levels_of_marked (trail S)
      = rev ([1..<(1+length (get_all_levels_of_marked (trail S)))])" and
    n_d: "no_dup (trail S)"
  shows "get_all_levels_of_marked (trail S')
    = rev [1..<1+length (get_all_levels_of_marked (trail S'))]"
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
  case (backtrack L D K i M1 M2 T) note decomp = this(3) and confli = this(1) and T =this(7) and
    all_marked = this(9) and bt_lvl = this(8)
  have "atm_of L \<notin>  atm_of ` lits_of_l M1"
    using backtrack_lit_skiped[of S L K i M1 M2] backtrack(4,8-10) decomp
    by (fastforce simp add: lits_of_def)
  moreover then have "undefined_lit M1 L"
     by (auto simp: defined_lit_map lits_of_def)
  then have [simp]: "trail T = Propagated L (mset_ccls D) # M1"
    using T decomp n_d by auto
  obtain c where M: "trail S = c @ M2 @ Marked K (i + 1) # M1" using decomp by auto
  have "get_all_levels_of_marked (rev (trail S))
    = [Suc 0..<2+length (get_all_levels_of_marked c) + (length (get_all_levels_of_marked M2)
                + length (get_all_levels_of_marked M1))]"
    using all_marked bt_lvl unfolding M by (auto simp: rev_swap[symmetric] simp del: upt_simps)
  then show ?case
    using T by (auto simp: rev_swap M simp del: upt_simps dest!: append_cons_eq_upt(1))
qed auto

text \<open>We write @{term "1+length (get_all_levels_of_marked (trail S))"} instead of
  @{term "backtrack_lvl S"} to avoid non termination of rewriting.\<close>
definition cdcl\<^sub>W_M_level_inv :: "'st \<Rightarrow> bool" where
"cdcl\<^sub>W_M_level_inv S \<longleftrightarrow>
  consistent_interp (lits_of_l (trail S))
  \<and> no_dup (trail S)
  \<and> backtrack_lvl S = length (get_all_levels_of_marked (trail S))
  \<and> get_all_levels_of_marked (trail S)
      = rev [1..<1+length (get_all_levels_of_marked (trail S))]"

lemma cdcl\<^sub>W_M_level_inv_decomp:
  assumes "cdcl\<^sub>W_M_level_inv S"
  shows
    "consistent_interp (lits_of_l (trail S))" and
    "no_dup (trail S)"
  using assms unfolding cdcl\<^sub>W_M_level_inv_def by fastforce+

lemma cdcl\<^sub>W_consistent_inv:
  fixes S S' :: 'st
  assumes
    "cdcl\<^sub>W S S'" and
    "cdcl\<^sub>W_M_level_inv S"
  shows "cdcl\<^sub>W_M_level_inv S'"
  using assms cdcl\<^sub>W_consistent_inv_2 cdcl\<^sub>W_distinctinv_1 cdcl\<^sub>W_bt cdcl\<^sub>W_bt_level'
  unfolding cdcl\<^sub>W_M_level_inv_def by meson+

lemma rtranclp_cdcl\<^sub>W_consistent_inv:
  assumes
    "cdcl\<^sub>W\<^sup>*\<^sup>* S S'" and
    "cdcl\<^sub>W_M_level_inv S"
  shows "cdcl\<^sub>W_M_level_inv S'"
  using assms by (induct rule: rtranclp_induct) (auto intro: cdcl\<^sub>W_consistent_inv)

lemma tranclp_cdcl\<^sub>W_consistent_inv:
  assumes
    "cdcl\<^sub>W\<^sup>+\<^sup>+ S S'" and
    "cdcl\<^sub>W_M_level_inv S"
  shows "cdcl\<^sub>W_M_level_inv S'"
  using assms by (induct rule: tranclp_induct)
  (auto intro: cdcl\<^sub>W_consistent_inv)

lemma cdcl\<^sub>W_M_level_inv_S0_cdcl\<^sub>W[simp]:
  "cdcl\<^sub>W_M_level_inv (init_state N)"
  unfolding cdcl\<^sub>W_M_level_inv_def by auto

lemma cdcl\<^sub>W_M_level_inv_get_level_le_backtrack_lvl:
  assumes inv: "cdcl\<^sub>W_M_level_inv S"
  shows "get_level (trail S) L \<le> backtrack_lvl S"
proof -
  have "get_all_levels_of_marked (trail S) = rev [1..<1 + backtrack_lvl S]"
    using inv unfolding cdcl\<^sub>W_M_level_inv_def by auto
  then show ?thesis
    using get_rev_level_less_max_get_all_levels_of_marked[of "rev (trail S)" 0 L]
    by (auto simp: Max_n_upt)
qed

lemma backtrack_ex_decomp:
  assumes
    M_l: "cdcl\<^sub>W_M_level_inv S" and
    i_S: "i < backtrack_lvl S"
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
    using Marked_cons_in_get_all_marked_decomposition_append_Marked_cons unfolding tr_S  by fast
  then show ?thesis by blast
qed

subsubsection \<open>Better-Suited Induction Principle\<close>

text \<open>We generalise the induction principle defined previously: the induction case for
  @{term backtrack} now includes the assumption that @{term "undefined_lit M1 L"}. This helps
  the simplifier and thus the automation.\<close>
lemma backtrack_induction_lev[consumes 1, case_names M_devel_inv backtrack]:
  assumes
    bt: "backtrack S T" and
    inv: "cdcl\<^sub>W_M_level_inv S" and
    backtrackH: "\<And>K i M1 M2 L D T.
      raw_conflicting S = Some D \<Longrightarrow>
      L \<in># mset_ccls D \<Longrightarrow>
      (Marked K (Suc i) # M1, M2) \<in> set (get_all_marked_decomposition (trail S)) \<Longrightarrow>
      get_level (trail S) L = backtrack_lvl S \<Longrightarrow>
      get_level (trail S) L = get_maximum_level (trail S) (mset_ccls D) \<Longrightarrow>
      get_maximum_level (trail S) (remove1_mset L (mset_ccls D)) \<equiv> i \<Longrightarrow>
      undefined_lit M1 L \<Longrightarrow>
      T \<sim> cons_trail (Propagated L (cls_of_ccls D))
                (reduce_trail_to M1
                  (add_learned_cls (cls_of_ccls D)
                    (update_backtrack_lvl i
                      (update_conflicting None S)))) \<Longrightarrow>
      P S T"
  shows "P S T"
proof -
  obtain K i M1 M2 L D where
    decomp: "(Marked K (Suc i) # M1, M2) \<in> set (get_all_marked_decomposition (trail S))" and
    L: "get_level (trail S) L = backtrack_lvl S" and
    confl: "raw_conflicting S = Some D" and
    LD: "L \<in># mset_ccls D" and
    lev_L: "get_level (trail S) L = get_maximum_level (trail S) (mset_ccls D)" and
    lev_D: "get_maximum_level (trail S) (remove1_mset L (mset_ccls D)) \<equiv> i" and
    T: "T \<sim> cons_trail (Propagated L (cls_of_ccls D))
                (reduce_trail_to M1
                  (add_learned_cls (cls_of_ccls D)
                    (update_backtrack_lvl i
                      (update_conflicting None S))))"
    using bt by (elim backtrackE) metis

  have "atm_of L \<notin> atm_of ` lits_of_l M1"
    using backtrack_lit_skiped[of S L K i M1 M2] L decomp bt confl lev_L lev_D inv
    unfolding cdcl\<^sub>W_M_level_inv_def by force
  then have "undefined_lit M1 L"
    by (auto simp: defined_lit_map lits_of_def)
  then show ?thesis
    using backtrackH[OF confl LD decomp L lev_L lev_D _ T] by simp
qed

lemmas backtrack_induction_lev2 = backtrack_induction_lev[consumes 2, case_names backtrack]

lemma cdcl\<^sub>W_all_induct_lev_full:
  fixes S  :: "'st"
  assumes
    cdcl\<^sub>W: "cdcl\<^sub>W S S'" and
    inv[simp]: "cdcl\<^sub>W_M_level_inv S" and
    propagateH: "\<And>C L T. conflicting S = None \<Longrightarrow>
       C !\<in>! raw_clauses S \<Longrightarrow>
       L \<in># mset_cls C \<Longrightarrow>
       trail S \<Turnstile>as CNot (remove1_mset L (mset_cls C)) \<Longrightarrow>
       undefined_lit (trail S) L \<Longrightarrow>
       T \<sim> cons_trail (Propagated L C) S \<Longrightarrow>
       P S T" and
    conflictH: "\<And>D T.  conflicting S = None \<Longrightarrow>
       D !\<in>! raw_clauses S \<Longrightarrow>
       trail S \<Turnstile>as CNot (mset_cls D) \<Longrightarrow>
       T \<sim> update_conflicting (Some (ccls_of_cls D)) S \<Longrightarrow>
       P S T" and
    forgetH: "\<And>C T. conflicting S = None \<Longrightarrow>
      C !\<in>! raw_learned_clss S \<Longrightarrow>
      \<not>(trail S) \<Turnstile>asm clauses S \<Longrightarrow>
      mset_cls C \<notin> set (get_all_mark_of_propagated (trail S)) \<Longrightarrow>
      mset_cls C \<notin># init_clss S \<Longrightarrow>
      T \<sim> remove_cls C S \<Longrightarrow>
      P S T" and
    restartH: "\<And>T. \<not>trail S \<Turnstile>asm clauses S \<Longrightarrow>
      conflicting S = None \<Longrightarrow>
      T \<sim> restart_state S \<Longrightarrow>
      P S T" and
    decideH: "\<And>L T. conflicting S = None \<Longrightarrow>
      undefined_lit (trail S) L \<Longrightarrow>
      atm_of L \<in> atms_of_mm (init_clss S) \<Longrightarrow>
      T \<sim> cons_trail (Marked L (backtrack_lvl S +1)) (incr_lvl S) \<Longrightarrow>
      P S T" and
    skipH: "\<And>L C' M E T.
      trail S = Propagated L C' # M \<Longrightarrow>
      raw_conflicting S = Some E \<Longrightarrow>
      -L \<notin># mset_ccls E \<Longrightarrow>  mset_ccls E \<noteq> {#} \<Longrightarrow>
      T \<sim> tl_trail S \<Longrightarrow>
      P S T" and
    resolveH: "\<And>L E M D T.
      trail S = Propagated L (mset_cls E) # M \<Longrightarrow>
      L \<in># mset_cls E \<Longrightarrow>
      hd_raw_trail S  = Propagated L E \<Longrightarrow>
      raw_conflicting S = Some D \<Longrightarrow>
      -L \<in># mset_ccls D \<Longrightarrow>
      get_maximum_level (trail S) (mset_ccls (remove_clit (-L) D)) = backtrack_lvl S \<Longrightarrow>
      T \<sim> update_conflicting (Some (union_ccls (remove_clit (-L) D) (ccls_of_cls (remove_lit L E))))
        (tl_trail S) \<Longrightarrow>
      P S T" and
    backtrackH: "\<And>K i M1 M2 L D T.
      raw_conflicting S = Some D \<Longrightarrow>
      L \<in># mset_ccls D \<Longrightarrow>
      (Marked K (Suc i) # M1, M2) \<in> set (get_all_marked_decomposition (trail S)) \<Longrightarrow>
      get_level (trail S) L = backtrack_lvl S \<Longrightarrow>
      get_level (trail S) L = get_maximum_level (trail S) (mset_ccls D) \<Longrightarrow>
      get_maximum_level (trail S) (remove1_mset L (mset_ccls D)) \<equiv> i \<Longrightarrow>
      undefined_lit M1 L \<Longrightarrow>
      T \<sim> cons_trail (Propagated L (cls_of_ccls D))
                (reduce_trail_to M1
                  (add_learned_cls (cls_of_ccls D)
                    (update_backtrack_lvl i
                      (update_conflicting None S)))) \<Longrightarrow>
      P S T"
  shows "P S S'"
  using cdcl\<^sub>W
proof (induct S' rule: cdcl\<^sub>W_all_rules_induct)
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
  then show ?case
    apply (induction rule: backtrack_induction_lev)
     apply (rule inv)
    by (rule backtrackH;
      fastforce simp del: state_simp simp add: state_eq_def dest!: HOL.meta_eq_to_obj_eq)
next
  case (forget S')
  then show ?case by (auto elim!: forgetE intro!: forgetH)
next
  case (skip S')
  then show ?case by (auto elim!: skipE intro!: skipH)
next
  case (resolve S')
  then show ?case
    using hd_raw_trail[of S] by (cases "trail S") (auto elim!: resolveE intro!: resolveH)
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
    inv[simp]: "cdcl\<^sub>W_M_level_inv S" and
    decideH: "\<And>L T. conflicting S = None \<Longrightarrow>
      undefined_lit (trail S) L \<Longrightarrow>
      atm_of L \<in> atms_of_mm (init_clss S) \<Longrightarrow>
      T \<sim> cons_trail (Marked L (backtrack_lvl S +1)) (incr_lvl S) \<Longrightarrow>
      P S T" and
    skipH: "\<And>L C' M E T.
      trail S = Propagated L C' # M \<Longrightarrow>
      raw_conflicting S = Some E \<Longrightarrow>
      -L \<notin># mset_ccls E \<Longrightarrow>  mset_ccls E \<noteq> {#} \<Longrightarrow>
      T \<sim> tl_trail S \<Longrightarrow>
      P S T" and
    resolveH: "\<And>L E M D T.
      trail S = Propagated L (mset_cls E) # M \<Longrightarrow>
      L \<in># mset_cls E \<Longrightarrow>
      hd_raw_trail S  = Propagated L E \<Longrightarrow>
      raw_conflicting S = Some D \<Longrightarrow>
      -L \<in># mset_ccls D \<Longrightarrow>
      get_maximum_level (trail S) (mset_ccls (remove_clit (-L) D)) = backtrack_lvl S \<Longrightarrow>
      T \<sim> update_conflicting (Some (union_ccls (remove_clit (-L) D) (ccls_of_cls (remove_lit L E))))
        (tl_trail S) \<Longrightarrow>
      P S T" and
    backtrackH: "\<And>K i M1 M2 L D T.
      raw_conflicting S = Some D \<Longrightarrow>
      L \<in># mset_ccls D \<Longrightarrow>
      (Marked K (Suc i) # M1, M2) \<in> set (get_all_marked_decomposition (trail S)) \<Longrightarrow>
      get_level (trail S) L = backtrack_lvl S \<Longrightarrow>
      get_level (trail S) L = get_maximum_level (trail S) (mset_ccls D) \<Longrightarrow>
      get_maximum_level (trail S) (remove1_mset L (mset_ccls D)) \<equiv> i \<Longrightarrow>
      undefined_lit M1 L \<Longrightarrow>
      T \<sim> cons_trail (Propagated L (cls_of_ccls D))
                (reduce_trail_to M1
                  (add_learned_cls (cls_of_ccls D)
                    (update_backtrack_lvl i
                      (update_conflicting None S)))) \<Longrightarrow>
      P S T"
  shows "P S T"
  using cdcl\<^sub>W
proof (induct S T rule: cdcl\<^sub>W_o_all_rules_induct)
  case (decide T)
  then show ?case
    by (auto elim!: decideE intro!: decideH)
next
  case (backtrack S')
  then show ?case
    apply (induction rule: backtrack_induction_lev)
     apply (rule inv)
    by (rule backtrackH;
      fastforce simp del: state_simp simp add: state_eq_def dest!: HOL.meta_eq_to_obj_eq)
next
  case (skip S')
  then show ?case by (auto elim!: skipE intro!: skipH)
next
  case (resolve S')
  then show ?case
    using hd_raw_trail[of S] by (cases "trail S") (auto elim!: resolveE intro!: resolveH)
qed

lemmas cdcl\<^sub>W_o_induct_lev2 = cdcl\<^sub>W_o_induct_lev[consumes 2, case_names decide skip resolve
  backtrack]

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
    C: "C !\<in>! raw_clauses S" and
    L: "L \<in># mset_cls C" and
    tr: "trail S \<Turnstile>as CNot (remove1_mset L (mset_cls C))" and
    undef: "undefined_lit (trail S) L" and
    T: "T \<sim> cons_trail (Propagated L C) S"
  using propa by (elim propagateE) auto

  obtain C' where
    CC': "mset_cls C' = mset_cls C" and
    C': "C' !\<in>! raw_clauses S'"
    using SS' C
    in_mset_clss_exists_preimage[of "mset_cls C" "raw_learned_clss S'"]
    in_mset_clss_exists_preimage[of "mset_cls C" "raw_init_clss S'"]
    apply -
    apply (frule in_clss_mset_clss)
    by (auto simp: state_eq_def raw_clauses_def simp del: state_simp dest: in_clss_mset_clss)

  show ?thesis
    apply (rule propagate_rule[of _ C'])
    using state_eq_sym[of S S'] SS' conf C' CC' L tr undef TT' T
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
    D: "D !\<in>! raw_clauses S" and
    tr: " trail S \<Turnstile>as CNot (mset_cls D)" and
    T: "T \<sim> update_conflicting (Some (ccls_of_cls D)) S"
  using confl by (elim conflictE) auto

  obtain D' where
    DD': "mset_cls D' = mset_cls D" and
    D': "D' !\<in>! raw_clauses S'"
    using D SS' in_mset_clss_exists_preimage by fastforce

  show ?thesis
    apply (rule conflict_rule[of _ D'])
    using state_eq_sym[of S S'] SS' conf D' DD' tr TT' T
    by (auto simp: state_eq_def simp del: state_simp)
qed

lemma backtrack_levE[consumes 2]:
  "backtrack S S' \<Longrightarrow> cdcl\<^sub>W_M_level_inv S \<Longrightarrow>
  (\<And>K i M1 M2 L D.
      raw_conflicting S = Some D \<Longrightarrow>
      L \<in># mset_ccls D \<Longrightarrow>
      (Marked K (Suc i) # M1, M2) \<in> set (get_all_marked_decomposition (trail S)) \<Longrightarrow>
      get_level (trail S) L = backtrack_lvl S \<Longrightarrow>
      get_level (trail S) L = get_maximum_level (trail S) (mset_ccls D) \<Longrightarrow>
      get_maximum_level (trail S) (remove1_mset L (mset_ccls D)) \<equiv> i \<Longrightarrow>
      undefined_lit M1 L \<Longrightarrow>
      S' \<sim> cons_trail (Propagated L (cls_of_ccls D))
                (reduce_trail_to M1
                  (add_learned_cls (cls_of_ccls D)
                    (update_backtrack_lvl i
                      (update_conflicting None S)))) \<Longrightarrow> P) \<Longrightarrow>
  P"
  using assms by (induction rule: backtrack_induction_lev2) metis
thm allI

lemma backtrack_state_eq_compatible:
  assumes
    bt: "backtrack S T" and
    SS': "S \<sim> S'" and
    TT': "T \<sim> T'" and
    inv: "cdcl\<^sub>W_M_level_inv S"
  shows "backtrack S' T'"
proof -
  obtain D L K i M1 M2 where
    conf: "raw_conflicting S = Some D" and
    L: "L \<in># mset_ccls D" and
    decomp: "(Marked K (Suc i) # M1, M2) \<in> set (get_all_marked_decomposition (trail S))" and
    lev: "get_level (trail S) L = backtrack_lvl S" and
    max: "get_level (trail S) L = get_maximum_level (trail S) (mset_ccls D)" and
    max_D: "get_maximum_level (trail S) (remove1_mset L (mset_ccls D)) \<equiv> i" and
    undef: "undefined_lit M1 L" and
    T: "T \<sim> cons_trail (Propagated L (cls_of_ccls D))
                (reduce_trail_to M1
                  (add_learned_cls (cls_of_ccls D)
                    (update_backtrack_lvl i
                      (update_conflicting None S))))"
  using bt inv by (elim backtrack_levE) metis
  obtain D' where
    D': "raw_conflicting S' = Some D'"
    using SS' conf by (cases "raw_conflicting S'") auto
  have [simp]: "mset_ccls D = mset_ccls D'"
    using SS' D' conf by (auto simp: state_eq_def simp del: state_simp)[]

  have T': "T' \<sim> cons_trail (Propagated L (cls_of_ccls D'))
     (reduce_trail_to M1 (add_learned_cls (cls_of_ccls D')
     (update_backtrack_lvl i (update_conflicting None S'))))"
    using TT' unfolding state_eq_def
    using decomp undef inv SS' T  by (auto simp add: cdcl\<^sub>W_M_level_inv_def)

  show ?thesis
    apply (rule backtrack_rule[of _ D'])
        apply (rule D')
       using state_eq_sym[of S S'] TT' SS' D' conf L decomp lev max max_D undef T
       apply (auto simp: state_eq_def simp del: state_simp)[]
      using decomp SS' lev SS' max_D max T' by (auto simp: state_eq_def simp del: state_simp)
qed

lemma decide_state_eq_compatible:
  assumes
    "decide S T" and
    "S \<sim> S'" and
    "T \<sim> T'"
  shows "decide S' T'"
  using assms apply (elim decideE)
  apply (rule decide_rule)
  by (auto simp: state_eq_def raw_clauses_def simp del: state_simp)

lemma skip_state_eq_compatible:
  assumes
    skip: "skip S T" and
    SS': "S \<sim> S'" and
    TT': "T \<sim> T'"
  shows "skip S' T'"
proof -
  obtain L C' M E where
    tr: "trail S = Propagated L C' # M" and
    raw: "raw_conflicting S = Some E" and
    L: "-L \<notin># mset_ccls E" and
    E: "mset_ccls E \<noteq> {#}" and
    T: "T \<sim> tl_trail S"
  using skip by (elim skipE) simp
  obtain E' where E': "raw_conflicting S' = Some E'"
    using SS' raw by (cases "raw_conflicting S'") (auto simp: state_eq_def simp del: state_simp)
  show ?thesis
    apply (rule skip_rule)
       using tr raw L E T SS' apply (auto simp:  simp del: )[]
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
    hd: "hd_raw_trail S  = Propagated L E" and
    L: "L \<in># mset_cls E" and
    raw: "raw_conflicting S = Some D" and
    LD: "-L \<in># mset_ccls D" and
    i: "get_maximum_level (trail S) (mset_ccls (remove_clit (-L) D)) = backtrack_lvl S" and
    T: "T \<sim> update_conflicting (Some (union_ccls (remove_clit (-L) D)
       (ccls_of_cls (remove_lit L E)))) (tl_trail S)"
  using assms by (elim resolveE) simp

  obtain E' where
    E': "hd_raw_trail S' = Propagated L E'"
    using SS' hd by (metis \<open>trail S \<noteq> []\<close> hd_raw_trail is_proped_def marked_lit.disc(3)
      marked_lit.inject(2) mmset_of_mlit.elims state_eq_trail)
  have [simp]: "mset_cls E = mset_cls E'"
    using hd_raw_trail[of S] tr hd_raw_trail[of S'] tr SS' hd E'
    by (metis marked_lit.inject(2) mmset_of_mlit.simps(1) state_eq_trail)
  obtain D' where
    D': "raw_conflicting S' = Some D'"
    using SS' raw by fastforce
  have [simp]: "mset_ccls D = mset_ccls D'"
    using D' SS' raw state_simp(5) by fastforce
  have T'T: "T' \<sim> T"
    using TT' state_eq_sym by auto
  show ?thesis
    apply (rule resolve_rule)
           using tr SS' apply simp
          using E' apply simp
         using L apply simp
        using D' apply simp
       using D' SS' raw LD apply (auto simp add: state_eq_def simp del: state_simp)[]
      using D' SS' raw LD apply (auto simp add: state_eq_def simp del: state_simp)[]
     using raw SS' i apply (auto simp add: state_eq_def simp del: state_simp)[]
    using T T'T  SS' by (auto simp: state_eq_def simp del: state_simp )
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
    "C !\<in>! raw_learned_clss S" and
    tr: "\<not>(trail S) \<Turnstile>asm clauses S" and
    C1: "mset_cls C \<notin> set (get_all_mark_of_propagated (trail S))" and
    C2: "mset_cls C \<notin># init_clss S" and
    T: "T \<sim> remove_cls C S"
    using forget by (elim forgetE) simp

  obtain C' where
    C': "C' !\<in>! raw_learned_clss S'" and
    [simp]: "mset_cls C' = mset_cls C"
    using \<open>C !\<in>! raw_learned_clss S\<close> SS' in_mset_clss_exists_preimage by fastforce
  show ?thesis
    apply (rule forget_rule)
         using SS' conf apply simp
        using C' apply simp
       using SS' tr apply simp
      using SS' C1 apply simp
     using SS' C2 apply simp
    using T TT' SS' by (auto simp: state_eq_def  simp del: state_simp)
qed

lemma cdcl\<^sub>W_state_eq_compatible:
  assumes
    "cdcl\<^sub>W S T" and "\<not>restart S T" and
    "S \<sim> S'"
    "T \<sim> T'" and
    "cdcl\<^sub>W_M_level_inv S"
  shows "cdcl\<^sub>W S' T'"
  using assms by (meson backtrack backtrack_state_eq_compatible bj cdcl\<^sub>W.simps cdcl\<^sub>W_o_rule_cases
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

subsubsection \<open>Conservation of some Properties\<close>
lemma cdcl\<^sub>W_o_no_more_init_clss:
  assumes
    "cdcl\<^sub>W_o S S'" and
    inv: "cdcl\<^sub>W_M_level_inv S"
  shows "init_clss S = init_clss S'"
  using assms by (induct rule: cdcl\<^sub>W_o_induct_lev2) (auto simp: inv cdcl\<^sub>W_M_level_inv_decomp)

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
  assumes
    "cdcl\<^sub>W S T" and
    inv: "cdcl\<^sub>W_M_level_inv S"
  shows "init_clss S = init_clss T"
  using assms by (induct rule: cdcl\<^sub>W_all_induct_lev2)
  (auto simp: inv cdcl\<^sub>W_M_level_inv_decomp not_in_iff)

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
  \<and> (\<forall>T. conflicting S = Some T \<longrightarrow> init_clss S \<Turnstile>pm T)
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
  case (backtrack K i M1 M2 L D T) note decomp = this(3) and confl = this(1) and undef = this(7)
  and T =this(8)
  show ?case
    using decomp confl learned undef T unfolding cdcl\<^sub>W_learned_clause_def
    by (auto dest!: get_all_marked_decomposition_exists_prepend
      simp: raw_clauses_def lev_inv cdcl\<^sub>W_M_level_inv_decomp dest: true_clss_clss_left_right)
next
  case (resolve L C M D) note trail = this(1) and CL = this(2) and confl = this(4) and DL = this(5)
    and lvl = this(6)
    and T =this(7)
  moreover
    have "init_clss S \<Turnstile>psm learned_clss S"
      using learned trail unfolding cdcl\<^sub>W_learned_clause_def raw_clauses_def by auto
    then have "init_clss S \<Turnstile>pm mset_cls C + {#L#}"
      using trail learned  unfolding cdcl\<^sub>W_learned_clause_def raw_clauses_def
      by (auto dest: true_clss_clss_in_imp_true_clss_cls)
  moreover have "remove1_mset (- L) (mset_ccls D) + {#- L#} = mset_ccls D"
    using DL by (auto simp: multiset_eq_iff)
  moreover have "remove1_mset L (mset_cls C) + {#L#} = mset_cls C"
    using CL by (auto simp: multiset_eq_iff)
  ultimately show ?case
    using learned T
    by (auto dest: mk_disjoint_insert
      simp add: cdcl\<^sub>W_learned_clause_def raw_clauses_def
      intro!: true_clss_cls_union_mset_true_clss_cls_or_not_true_clss_cls_or[of _ _ L])
next
  case (restart T)
  then show ?case
    using learned learned_clss_restart_state[of T]
    by (auto
      simp: raw_clauses_def state_eq_def cdcl\<^sub>W_learned_clause_def
      simp del: state_simp
      dest: true_clss_clssm_subsetE)
next
  case propagate
  then show ?case using learned by (auto simp: cdcl\<^sub>W_learned_clause_def)
next
  case conflict
  then show ?case using learned
    by (fastforce simp: cdcl\<^sub>W_learned_clause_def raw_clauses_def
      true_clss_clss_in_imp_true_clss_cls)
next
  case (forget U)
  then show ?case using learned
    by (auto simp: cdcl\<^sub>W_learned_clause_def raw_clauses_def split: if_split_asm)
qed (auto simp: cdcl\<^sub>W_learned_clause_def raw_clauses_def)

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
    (\<forall>T. conflicting S' = Some T \<longrightarrow> atms_of T \<subseteq> atms_of_mm (init_clss S'))
  \<and> (\<forall>L mark. Propagated L mark \<in> set (trail S')
      \<longrightarrow> atms_of ( mark) \<subseteq> atms_of_mm (init_clss S'))
  \<and> atms_of_mm (learned_clss S') \<subseteq> atms_of_mm (init_clss S')
  \<and> atm_of ` (lits_of_l (trail S')) \<subseteq> atms_of_mm (init_clss S'))"

lemma no_strange_atm_decomp:
  assumes "no_strange_atm S"
  shows "conflicting S = Some T \<Longrightarrow> atms_of T \<subseteq> atms_of_mm (init_clss S)"
  and "(\<forall>L mark. Propagated L mark \<in> set (trail S)
    \<longrightarrow> atms_of ( mark) \<subseteq> atms_of_mm (init_clss S))"
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
    tr = this(4) and undef = this(5) and T =this(6)
  have atm_CL: "atms_of (mset_cls C) \<subseteq> atms_of_mm (init_clss S)"
    using C alien unfolding no_strange_atm_def
    by (auto simp: raw_clauses_def atms_of_ms_def dest!:in_clss_mset_clss)
  show ?case
    unfolding no_strange_atm_def
    proof (intro conjI allI impI, goal_cases)
      case 1
      then show ?case
        using confl T undef by auto
    next
      case (2 L' mark')
      then show ?case
        using C_L T alien undef atm_CL
        (* TODO tune proof *)
        unfolding no_strange_atm_def raw_clauses_def apply auto by blast
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
  "x \<in> atms_of (remove1_mset L C) \<Longrightarrow>  x \<in> atms_of C"
  using in_diffD unfolding atms_of_def by fastforce

lemma cdcl\<^sub>W_no_strange_atm_explicit:
  assumes
    "cdcl\<^sub>W S S'" and
    lev: "cdcl\<^sub>W_M_level_inv S" and
    conf: "\<forall>T. conflicting S = Some T \<longrightarrow> atms_of T \<subseteq> atms_of_mm (init_clss S)" and
    marked: "\<forall>L mark. Propagated L mark \<in> set (trail S)
      \<longrightarrow> atms_of mark \<subseteq> atms_of_mm (init_clss S)" and
    learned: "atms_of_mm (learned_clss S) \<subseteq> atms_of_mm (init_clss S)" and
    trail: "atm_of ` (lits_of_l (trail S)) \<subseteq> atms_of_mm (init_clss S)"
  shows
    "(\<forall>T. conflicting S' = Some T \<longrightarrow> atms_of T \<subseteq> atms_of_mm (init_clss S')) \<and>
    (\<forall>L mark. Propagated L mark \<in> set (trail S')
      \<longrightarrow> atms_of ( mark) \<subseteq> atms_of_mm (init_clss S')) \<and>
    atms_of_mm (learned_clss S') \<subseteq> atms_of_mm (init_clss S') \<and>
    atm_of ` (lits_of_l (trail S')) \<subseteq> atms_of_mm (init_clss S')"
    (is "?C S' \<and> ?M S' \<and> ?U S' \<and> ?V S'")
  using assms(1,2)
proof (induct rule: cdcl\<^sub>W_all_induct_lev2)
  case (propagate C L T) note confl = this(1) and C_L = this(2) and tr = this(3) and undef = this(4)
  and T =this(5)
  show ?case
    using propagate_rule[OF propagate.hyps(1-3) _ propagate.hyps(5,6), simplified]
    propagate.hyps(4) propagate_no_strange_atm_inv[of S T]
    conf marked learned trail unfolding no_strange_atm_def by presburger
next
  case (decide L)
  then show ?case using learned marked conf trail unfolding raw_clauses_def by auto
next
  case (skip L C M D)
  then show ?case using learned marked conf trail by auto
next
  case (conflict D T) note D_S = this(2) and T =this(4)
  have D: "atm_of ` set_mset (mset_cls D) \<subseteq> \<Union>(atms_of ` (set_mset (clauses S)))"
    using D_S by (auto simp add: atms_of_def atms_of_ms_def)
  moreover {
    fix xa :: "'v literal"
    assume a1: "atm_of ` set_mset (mset_cls D) \<subseteq> (\<Union>x\<in>set_mset (init_clss S). atms_of x)
      \<union> (\<Union>x\<in>set_mset (learned_clss S). atms_of x)"
    assume a2: "
      (\<Union>x\<in>set_mset (learned_clss S). atms_of x) \<subseteq> (\<Union>x\<in>set_mset (init_clss S). atms_of x)"
    assume "xa \<in># mset_cls D"
    then have "atm_of xa \<in> UNION (set_mset (init_clss S)) atms_of"
      using a2 a1 by (metis (no_types) Un_iff atm_of_lit_in_atms_of atms_of_def subset_Un_eq)
    then have "\<exists>m\<in>set_mset (init_clss S). atm_of xa \<in> atms_of m"
      by blast
    } note H = this
  ultimately show ?case using conflict.prems T learned marked conf trail
    unfolding atms_of_def atms_of_ms_def raw_clauses_def
    by (auto simp add: H)
next
  case (restart T)
  then show ?case using learned marked conf trail by auto
next
  case (forget C T) note confl = this(1) and C = this(4) and C_le = this(5) and
    T = this(6)
  have H: "\<And>L mark. Propagated L mark \<in> set (trail S) \<Longrightarrow> atms_of mark \<subseteq> atms_of_mm (init_clss S)"
    using marked by simp
  show ?case unfolding raw_clauses_def apply (intro conjI)
       using conf confl T trail C unfolding raw_clauses_def apply (auto dest!: H)[]
      using T trail C C_le apply (auto dest!: H)[]
     using T learned C_le atms_of_ms_remove_subset[of "set_mset (learned_clss S)"] apply auto[]
   using T trail C_le apply (auto simp: raw_clauses_def lits_of_def)[]
   done
next
  case (backtrack K i M1 M2 L D T) note confl = this(1) and LD = this(2) and decomp = this(3) and
    undef= this(7)
    and T =this(8)
  have "?C T"
    using conf T decomp undef lev by (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
  moreover have "set M1 \<subseteq> set (trail S)"
    using decomp by auto
  then have M: "?M T"
    using marked conf undef confl T decomp lev
    by (auto simp: image_subset_iff raw_clauses_def cdcl\<^sub>W_M_level_inv_decomp)
  moreover have "?U T"
    using learned decomp conf confl T undef lev unfolding raw_clauses_def
    by (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
  moreover have "?V T"
    using M conf confl trail T undef decomp lev LD
    by (auto simp: cdcl\<^sub>W_M_level_inv_decomp atms_of_def
      dest!: get_all_marked_decomposition_exists_prepend)
  ultimately show ?case by blast
next
  case (resolve L C M D T) note trail_S = this(1) and confl = this(4) and T = this(7)
  let ?T = "update_conflicting (Some ((remove_clit (-L) D) !\<union> ccls_of_cls ((remove_lit L C))))
    (tl_trail S)"
  have "?C ?T"
    using confl trail_S conf marked by (auto dest!: in_atms_of_remove1_mset_in_atms_of)
  moreover have  "?M ?T"
    using confl trail_S conf marked by auto
  moreover have "?U ?T"
    using trail learned by auto
  moreover have "?V ?T"
    using confl trail_S trail by auto
  ultimately show ?case using T by simp
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
  \<longleftrightarrow> ((\<forall>T. conflicting S = Some T \<longrightarrow> distinct_mset T)
    \<and> distinct_mset_mset (learned_clss S)
    \<and> distinct_mset_mset (init_clss S)
    \<and> (\<forall>L mark. (Propagated L mark \<in> set (trail S) \<longrightarrow> distinct_mset (mark))))"

lemma distinct_cdcl\<^sub>W_state_decomp:
  assumes "distinct_cdcl\<^sub>W_state (S::'st)"
  shows "\<forall>T. conflicting S = Some T \<longrightarrow> distinct_mset T"
  and "distinct_mset_mset (learned_clss S)"
  and "distinct_mset_mset (init_clss S)"
  and "\<forall>L mark. (Propagated L mark \<in> set (trail S) \<longrightarrow> distinct_mset ( mark))"
  using assms unfolding distinct_cdcl\<^sub>W_state_def by blast+

lemma distinct_cdcl\<^sub>W_state_decomp_2:
  assumes "distinct_cdcl\<^sub>W_state (S::'st)"
  shows "conflicting S = Some T \<Longrightarrow> distinct_mset T"
  using assms unfolding distinct_cdcl\<^sub>W_state_def by auto

lemma distinct_cdcl\<^sub>W_state_S0_cdcl\<^sub>W[simp]:
  "distinct_mset_mset (mset_clss N) \<Longrightarrow>  distinct_cdcl\<^sub>W_state (init_state N)"
  unfolding distinct_cdcl\<^sub>W_state_def by auto

lemma distinct_cdcl\<^sub>W_state_inv:
  assumes
    "cdcl\<^sub>W S S'" and
    lev_inv: "cdcl\<^sub>W_M_level_inv S" and
    "distinct_cdcl\<^sub>W_state S"
  shows "distinct_cdcl\<^sub>W_state S'"
  using assms(1,2,2,3)
proof (induct rule: cdcl\<^sub>W_all_induct_lev2)
  case (backtrack L D K i M1 M2)
  then show ?case
    using lev_inv unfolding distinct_cdcl\<^sub>W_state_def
    by (auto dest: get_all_marked_decomposition_incl simp: cdcl\<^sub>W_M_level_inv_decomp)
next
  case restart
  then show ?case
    unfolding distinct_cdcl\<^sub>W_state_def distinct_mset_set_def raw_clauses_def
    using learned_clss_restart_state[of S] by auto
next
  case resolve
  then show ?case
    by (auto simp add: distinct_cdcl\<^sub>W_state_def distinct_mset_set_def raw_clauses_def
      distinct_mset_single_add
      intro!: distinct_mset_union_mset)
qed (auto simp: distinct_cdcl\<^sub>W_state_def distinct_mset_set_def raw_clauses_def
  dest!: in_clss_mset_clss in_diffD)

lemma rtanclp_distinct_cdcl\<^sub>W_state_inv:
  assumes
    "cdcl\<^sub>W\<^sup>*\<^sup>* S S'" and
    "cdcl\<^sub>W_M_level_inv S" and
    "distinct_cdcl\<^sub>W_state S"
  shows "distinct_cdcl\<^sub>W_state S'"
  using assms apply (induct rule: rtranclp_induct)
  using distinct_cdcl\<^sub>W_state_inv rtranclp_cdcl\<^sub>W_consistent_inv by blast+

subsubsection \<open>Conflicts and co\<close>
text \<open>This invariant shows that each mark contains a contradiction only related to the previously
  defined variable.\<close>
abbreviation every_mark_is_a_conflict :: "'st \<Rightarrow> bool" where
"every_mark_is_a_conflict S \<equiv>
 \<forall>L mark a b. a @ Propagated L mark # b = (trail S)
   \<longrightarrow> (b \<Turnstile>as CNot ( mark - {#L#}) \<and> L \<in>#  mark)"

definition "cdcl\<^sub>W_conflicting S \<equiv>
  (\<forall>T. conflicting S = Some T \<longrightarrow> trail S \<Turnstile>as CNot T)
  \<and> every_mark_is_a_conflict S"

lemma backtrack_atms_of_m_D_in_M1:
  fixes M1 :: "('v, nat, 'v clause) marked_lits"
  assumes
    inv: "cdcl\<^sub>W_M_level_inv S" and
    undef: "undefined_lit M1 L" and
    i: "get_maximum_level (trail S) (mset_ccls (remove_clit L D)) \<equiv> i" and
    decomp: "(Marked K (Suc i) # M1, M2)
       \<in> set (get_all_marked_decomposition (trail S))" and
    S_lvl: "backtrack_lvl S = get_maximum_level (trail S) (mset_ccls D)" and
    S_confl: "raw_conflicting S = Some D" and
    undef: "undefined_lit M1 L" and
    T: "T \<sim> cons_trail (Propagated L (cls_of_ccls D))
                (reduce_trail_to M1
                  (add_learned_cls (cls_of_ccls D)
                    (update_backtrack_lvl i
                      (update_conflicting None S))))" and
    confl: "\<forall>T. conflicting S = Some T \<longrightarrow> trail S \<Turnstile>as CNot T"
  shows "atms_of (mset_ccls (remove_clit L D)) \<subseteq> atm_of ` lits_of_l (tl (trail T))"
proof (rule ccontr)
  let ?k = "get_maximum_level (trail S) (mset_ccls D)"
  let ?D = "mset_ccls D"
  let ?D' = "mset_ccls (remove_clit L D)"
  have "trail S \<Turnstile>as CNot ?D" using confl S_confl by auto
  then have vars_of_D: "atms_of ?D \<subseteq> atm_of ` lits_of_l (trail S)" unfolding atms_of_def
    by (meson image_subsetI true_annots_CNot_all_atms_defined)

  obtain M0 where M: "trail S = M0 @ M2 @ Marked K (Suc i) # M1"
    using decomp by auto

  have max: "?k = length (get_all_levels_of_marked (M0 @ M2 @ Marked K (Suc i) # M1))"
    using inv unfolding cdcl\<^sub>W_M_level_inv_def S_lvl M by simp
  assume a: "\<not> ?thesis"
  then obtain L' where
    L': "L' \<in> atms_of ?D'" and
    L'_notin_M1: "L' \<notin> atm_of ` lits_of_l M1"
    using T undef decomp inv by (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
  then have L'_in: "L' \<in> atm_of ` lits_of_l (M0 @ M2 @ Marked K (i + 1) # [])"
    using vars_of_D unfolding M by (auto dest: in_atms_of_remove1_mset_in_atms_of)
  then obtain L'' where
    "L'' \<in># ?D'" and
    L'': "L' = atm_of L''"
    using L' L'_notin_M1 unfolding atms_of_def by auto
  have lev_L'':
    "get_level (trail S) L'' = get_rev_level (Marked K (Suc i) # rev M2 @ rev M0) (Suc i) L''"
    using L'_notin_M1 L'' M by (auto simp del: get_rev_level.simps)
  have "get_all_levels_of_marked (trail S) = rev [1..<1+?k]"
    using inv S_lvl unfolding cdcl\<^sub>W_M_level_inv_def by auto
  then have "get_all_levels_of_marked (M0 @ M2) = rev [Suc (Suc i)..<Suc ?k]"
    unfolding M by (auto simp:rev_swap[symmetric] dest!: append_cons_eq_upt_length_i_end)

  then have M: "get_all_levels_of_marked M0 @ get_all_levels_of_marked M2
    = rev [Suc (Suc i)..<Suc (length (get_all_levels_of_marked (M0 @ M2 @ Marked K (Suc i) # M1)))]"
    unfolding max unfolding M by simp

  have "get_rev_level (Marked K (Suc i) # rev (M0 @ M2)) (Suc i) L''
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
  finally have "get_rev_level (Marked K (Suc i) # rev (M0 @ M2)) (Suc i) L'' \<ge> Suc i" .
  then have "get_level (trail S) L'' \<ge> i + 1"
    using lev_L'' by simp
  then have "get_maximum_level (trail S) ?D' \<ge> i + 1"
    using get_maximum_level_ge_get_level[OF \<open>L'' \<in># ?D'\<close>, of "trail S"] by auto
  then show False using i by auto
qed

lemma distinct_atms_of_m_incl_not_in_other:
  assumes
    a1: "no_dup (M @ M')" and
    a2: "atms_of D \<subseteq> atm_of ` lits_of_l M'" and
    a3: "x \<in> atms_of D"
  shows "x \<notin> atm_of ` lits_of_l M"
proof -
  have ff1: "\<And>l ms. undefined_lit ms l \<or> atm_of l
    \<in> set (map (\<lambda>m. atm_of (lit_of (m::('a, 'b, 'c) marked_lit))) ms)"
    by (simp add: defined_lit_map)
  have ff2: "\<And>a. a \<notin> atms_of D \<or> a \<in> atm_of ` lits_of_l M'"
    using a2 by (meson subsetCE)
  have ff3: "\<And>a. a \<notin> set (map (\<lambda>m. atm_of (lit_of m)) M')
    \<or> a \<notin> set (map (\<lambda>m. atm_of (lit_of m)) M)"
    using a1 by (metis (lifting) IntI distinct_append empty_iff map_append)
  have "\<forall>L a f. \<exists>l. ((a::'a) \<notin> f ` L \<or> (l::'a literal) \<in> L) \<and> (a \<notin> f ` L \<or> f l = a)"
    by blast
  then show "x \<notin> atm_of ` lits_of_l M"
    using ff3 ff2 ff1 a3 by (metis (no_types) Marked_Propagated_in_iff_in_lits_of_l)
qed

(* TODO Move, mark as simp? *)
lemma true_annot_CNot_remove1_mset_remove1_mset:
  "I \<Turnstile>as CNot C \<Longrightarrow> I \<Turnstile>as CNot (remove1_mset L C)"
  by (auto simp: true_annots_true_cls_def_iff_negation_in_model dest: in_diffD)

lemma cdcl\<^sub>W_propagate_is_conclusion:
  assumes
    "cdcl\<^sub>W S S'" and
    inv: "cdcl\<^sub>W_M_level_inv S" and
    decomp: "all_decomposition_implies_m (init_clss S) (get_all_marked_decomposition (trail S))" and
    learned: "cdcl\<^sub>W_learned_clause S" and
    confl: "\<forall>T. conflicting S = Some T \<longrightarrow> trail S \<Turnstile>as CNot T" and
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
  case (resolve L C M D) note tr = this(1) and T = this(7)
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
  case (propagate C L T) note propa = this(2) and L = this(3) and undef = this(5) and T =this(6)
  obtain a y where ay: "hd (get_all_marked_decomposition (trail S)) = (a, y)"
    by (cases "hd (get_all_marked_decomposition (trail S))")
  then have M: "trail S = y @ a" using get_all_marked_decomposition_decomp by blast
  have M': "set (get_all_marked_decomposition (trail S))
    = insert (a, y) (set (tl (get_all_marked_decomposition (trail S))))"
    using ay by (cases "get_all_marked_decomposition (trail S)") auto
  have "unmark_l a \<union> set_mset (init_clss S) \<Turnstile>ps unmark_l y"
    using decomp ay unfolding all_decomposition_implies_def
    by (cases "get_all_marked_decomposition (trail S)") fastforce+
  then have a_Un_N_M: "unmark_l a \<union> set_mset (init_clss S)
    \<Turnstile>ps unmark_l (trail S)"
    unfolding M by (auto simp add: all_in_true_clss_clss image_Un)

  have "unmark_l a \<union> set_mset (init_clss S) \<Turnstile>p {#L#}" (is "?I \<Turnstile>p _")
    proof (rule true_clss_cls_plus_CNot)
      show "?I \<Turnstile>p remove1_mset L (mset_cls C) + {#L#}"
        apply (rule true_clss_clss_in_imp_true_clss_cls[of _
            "set_mset (init_clss S) \<union> set_mset (learned_clss S)"])
        using learned propa L by (auto simp: raw_clauses_def cdcl\<^sub>W_learned_clause_def
          true_annot_CNot_remove1_mset_remove1_mset)
    next
      have "(\<lambda>m. {#lit_of m#}) ` set (trail S) \<Turnstile>ps CNot (remove1_mset L (mset_cls C))"
        using \<open>(trail S) \<Turnstile>as CNot (remove1_mset L (mset_cls C))\<close> true_annots_true_clss_clss by blast
      then show "?I \<Turnstile>ps CNot (remove1_mset L (mset_cls C))"
        using a_Un_N_M true_clss_clss_left_right true_clss_clss_union_l_r by blast
    qed
  moreover have "\<And>aa b.
      \<forall> (Ls, seen)\<in>set (get_all_marked_decomposition (y @ a)).
        unmark_l Ls \<union> set_mset (init_clss S) \<Turnstile>ps unmark_l seen
    \<Longrightarrow> (aa, b) \<in> set (tl (get_all_marked_decomposition (y @ a)))
    \<Longrightarrow> unmark_l aa \<union> set_mset (init_clss S) \<Turnstile>ps unmark_l b"
    by (metis (no_types, lifting) case_prod_conv get_all_marked_decomposition_never_empty_sym
      list.collapse list.set_intros(2))

  ultimately show ?case
    using decomp T undef unfolding ay all_decomposition_implies_def
    using M \<open>unmark_l a \<union> set_mset (init_clss S) \<Turnstile>ps unmark_l y\<close>
     ay by auto
next
  case (backtrack K i M1 M2 L D  T) note conf = this(1) and LD = this(2) and decomp' = this(3) and
    lev_L = this(4) and undef = this(7) and T = this(8)
  let ?D = "mset_ccls D"
  let ?D' = "mset_ccls (remove_clit L D)"
  have "\<forall>l \<in> set M2. \<not>is_marked l"
    using get_all_marked_decomposition_snd_not_marked decomp' by blast
  obtain M0 where M: "trail S = M0 @ M2 @ Marked K (i + 1) # M1"
    using decomp' by auto
  show ?case unfolding all_decomposition_implies_def
    proof
      fix x
      assume "x \<in> set (get_all_marked_decomposition (trail T))"
      then have x: "x \<in> set (get_all_marked_decomposition (Propagated L ?D # M1))"
        using T decomp' undef inv by (simp add: cdcl\<^sub>W_M_level_inv_decomp)
      let ?m = "get_all_marked_decomposition (Propagated L ?D # M1)"
      let ?hd = "hd ?m"
      let ?tl = "tl ?m"
      consider
          (hd) "x = ?hd"
        | (tl) "x \<in> set ?tl"
        using x by (cases "?m") auto
      then show "case x of (Ls, seen) \<Rightarrow> unmark_l Ls \<union> set_mset (init_clss T)
        \<Turnstile>ps unmark_l seen"
        proof cases
          case tl
          then have "x \<in> set (get_all_marked_decomposition (trail S))"
            using tl_get_all_marked_decomposition_skip_some[of x] by (simp add: list.set_sel(2) M)
          then show ?thesis
            using decomp learned decomp confl alien inv T undef M
            unfolding all_decomposition_implies_def cdcl\<^sub>W_M_level_inv_def
            by auto
        next
          case hd
          obtain M1' M1'' where M1: "hd (get_all_marked_decomposition M1) = (M1', M1'')"
            by (cases "hd (get_all_marked_decomposition M1)")
          then have x': "x = (M1', Propagated L ?D # M1'')"
            using \<open>x = ?hd\<close> by auto
          have "(M1', M1'') \<in> set (get_all_marked_decomposition (trail S))"
            using M1[symmetric] hd_get_all_marked_decomposition_skip_some[OF M1[symmetric],
              of "M0 @ M2" _ "i+1"] unfolding M by fastforce
          then have 1: "unmark_l M1' \<union> set_mset (init_clss S) \<Turnstile>ps unmark_l M1''"
            using decomp unfolding all_decomposition_implies_def by auto

          moreover
            have vars_of_D: "atms_of ?D' \<subseteq> atm_of ` lits_of_l M1"
              using backtrack_atms_of_m_D_in_M1[of S M1 L D i K M2 T] backtrack.hyps inv conf confl
              by (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
            have "no_dup (trail S)" using inv by (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
            then have vars_in_M1:
              "\<forall>x \<in> atms_of ?D'. x \<notin> atm_of ` lits_of_l (M0 @ M2 @ Marked K (i + 1) # [])"
              using vars_of_D distinct_atms_of_m_incl_not_in_other[of
                "M0 @M2 @ Marked K (i + 1) # []" M1] unfolding M by auto
            have "trail S \<Turnstile>as CNot (remove1_mset L (mset_ccls D))"
              using conf confl LD unfolding M true_annots_true_cls_def_iff_negation_in_model
              by (auto dest!: Multiset.in_diffD)
            then have "M1 \<Turnstile>as CNot ?D'"
              using vars_in_M1 true_annots_remove_if_notin_vars[of "M0 @ M2 @ Marked K (i + 1) # []"
                M1 "CNot ?D'"] conf confl unfolding M lits_of_def by simp
            have "M1 = M1'' @ M1'" by (simp add: M1 get_all_marked_decomposition_decomp)
            have TT: "unmark_l M1' \<union> set_mset (init_clss S) \<Turnstile>ps CNot ?D'"
              using true_annots_true_clss_cls[OF \<open>M1 \<Turnstile>as CNot ?D'\<close>] true_clss_clss_left_right[OF 1]
              unfolding \<open>M1 = M1'' @ M1'\<close> by (auto simp add: inf_sup_aci(5,7))
            have "init_clss S \<Turnstile>pm ?D' + {#L#}"
              using conf learned confl LD unfolding cdcl\<^sub>W_learned_clause_def by auto
            then have T': "unmark_l M1' \<union> set_mset (init_clss S) \<Turnstile>p ?D' + {#L#}" by auto
            have "atms_of (?D' + {#L#}) \<subseteq> atms_of_mm (clauses S)"
              using alien conf LD unfolding no_strange_atm_def raw_clauses_def by auto
            then have "unmark_l M1' \<union> set_mset (init_clss S) \<Turnstile>p {#L#}"
              using true_clss_cls_plus_CNot[OF T' TT] by auto

          ultimately show ?thesis
              using T' T decomp' undef inv unfolding x' by (simp add: cdcl\<^sub>W_M_level_inv_decomp)
        qed
    qed
qed

lemma cdcl\<^sub>W_propagate_is_false:
  assumes
    "cdcl\<^sub>W S S'" and
    lev: "cdcl\<^sub>W_M_level_inv S" and
    learned: "cdcl\<^sub>W_learned_clause S" and
    decomp: "all_decomposition_implies_m (init_clss S) (get_all_marked_decomposition (trail S))" and
    confl: "\<forall>T. conflicting S = Some T \<longrightarrow> trail S \<Turnstile>as CNot T" and
    alien: "no_strange_atm S" and
    mark_confl: "every_mark_is_a_conflict S"
  shows "every_mark_is_a_conflict S'"
  using assms(1,2)
proof (induct rule: cdcl\<^sub>W_all_induct_lev2)
  case (propagate C L T) note LC = this(3) and confl = this(4) and undef = this(5) and T =this(6)
  show ?case
    proof (intro allI impI)
      fix L' mark a b
      assume "a @ Propagated L' mark # b = trail T"
      then consider
          (hd) "a=[]" and "L = L'" and "mark = mset_cls C" and "b = trail S"
        | (tl) "tl a @ Propagated L' mark # b = trail S"
        using T undef by (cases a) fastforce+
      then show "b \<Turnstile>as CNot (mark - {#L'#}) \<and> L' \<in>#  mark"
        using mark_confl confl LC by cases auto
    qed
next
  case (decide L) note undef[simp] = this(2) and T = this(4)
  have "\<And>a La mark b. a @ Propagated La mark # b = Marked L (backtrack_lvl S+1) # trail S
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
        \<longrightarrow> b \<Turnstile>as CNot ( mark - {#La#}) \<and> La \<in>#  mark"
        using mark_confl unfolding skip.hyps(1) by simp
      ultimately show "b \<Turnstile>as CNot (mark - {#L'#}) \<and> L' \<in>#  mark" by blast
    qed
next
  case (conflict D)
  then show ?case using mark_confl by simp
next
  case (resolve L C M D T) note tr_S = this(1) and T = this(7)
  show ?case unfolding resolve.hyps(1)
    proof (intro allI impI)
      fix  L' mark a b
      assume "a @ Propagated L' mark # b = trail T"
      then have "(Propagated L (mset_cls (L !++ C)) # a) @ Propagated L' mark # b
        = Propagated L (mset_cls (L !++ C)) # M"
        using T tr_S by auto
      then show "b \<Turnstile>as CNot (mark - {#L'#}) \<and> L' \<in>#  mark"
        using mark_confl unfolding tr_S by (metis Cons_eq_appendI list.sel(3))
    qed
next
  case restart
  then show ?case by auto
next
  case forget
  then show ?case using mark_confl by auto
next
  case (backtrack K i M1 M2 L D T) note conf = this(1) and LD = this(2) and decomp = this(3) and
    undef = this(7) and T = this(8)
  have "\<forall>l \<in> set M2. \<not>is_marked l"
    using get_all_marked_decomposition_snd_not_marked decomp by blast
  obtain M0 where M: "trail S = M0 @ M2 @ Marked K (i + 1) # M1"
    using decomp by auto
  have [simp]: "trail  (reduce_trail_to M1 (add_learned_cls (cls_of_ccls (insert_ccls L D))
    (update_backtrack_lvl i (update_conflicting None S)))) = M1"
    using decomp lev by (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
  let ?D = "mset_ccls D"
  let ?D' = "mset_ccls (remove_clit L D)"
  show ?case
    proof (intro allI impI)
      fix La :: "'v literal" and  mark :: "'v literal multiset" and
        a b :: "('v, nat, 'v literal multiset) marked_lit list"
      assume "a @ Propagated La mark # b = trail T"
      then consider
          (hd_tr) "a = []" and
            "(Propagated La mark :: ('v, nat, 'v literal multiset) marked_lit)
              = Propagated L ?D" and
            "b = M1"
        | (tl_tr) "tl a @ Propagated La mark # b = M1"
        using M T decomp undef lev by (cases a) (auto simp: cdcl\<^sub>W_M_level_inv_def)
      then show "b \<Turnstile>as CNot (mark - {#La#}) \<and> La \<in>#  mark"
        proof cases
          case hd_tr note A = this(1) and P = this(2) and b = this(3)
          have "trail S \<Turnstile>as CNot ?D" using conf confl by auto
          then have vars_of_D: "atms_of ?D \<subseteq> atm_of ` lits_of_l (trail S)"
            unfolding atms_of_def
            by (meson image_subsetI true_annots_CNot_all_atms_defined)
          have vars_of_D: "atms_of ?D' \<subseteq> atm_of ` lits_of_l M1"
            using backtrack_atms_of_m_D_in_M1[of S M1 L D i K M2 T] T backtrack lev confl
            by (auto simp:  cdcl\<^sub>W_M_level_inv_decomp)
          have "no_dup (trail S)" using lev by (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
          then have "\<forall>x \<in> atms_of ?D'. x \<notin> atm_of ` lits_of_l (M0 @ M2 @ Marked K (i + 1) # [])"
            using vars_of_D distinct_atms_of_m_incl_not_in_other[of
              "M0 @ M2 @ Marked K (i + 1) # []" M1] unfolding M by auto
          then have "M1 \<Turnstile>as CNot ?D'"
            using true_annots_remove_if_notin_vars[of "M0 @ M2 @ Marked K (i + 1) # []"
              M1 "CNot ?D'"] \<open>trail S \<Turnstile>as CNot ?D\<close> unfolding M lits_of_def
            by (simp add: true_annot_CNot_remove1_mset_remove1_mset)
          then show "b \<Turnstile>as CNot (mark - {#La#}) \<and> La \<in>#  mark"
            using P LD b by auto
        next
          case tl_tr
          then obtain c' where "c' @ Propagated La mark # b = trail S"
            unfolding M by auto
          then show "b \<Turnstile>as CNot (mark - {#La#}) \<and> La \<in>#  mark"
            using mark_confl by auto
        qed
    qed
qed

lemma cdcl\<^sub>W_conflicting_is_false:
  assumes
    "cdcl\<^sub>W S S'" and
    M_lev: "cdcl\<^sub>W_M_level_inv S" and
    confl_inv: "\<forall>T. conflicting S = Some T \<longrightarrow> trail S \<Turnstile>as CNot T" and
    marked_confl: "\<forall>L mark a b. a @ Propagated L mark # b = (trail S)
      \<longrightarrow> (b \<Turnstile>as CNot (mark - {#L#}) \<and> L \<in>#  mark)" and
    dist: "distinct_cdcl\<^sub>W_state S"
  shows "\<forall>T. conflicting S' = Some T \<longrightarrow> trail S' \<Turnstile>as CNot T"
  using assms(1,2)
proof (induct rule: cdcl\<^sub>W_all_induct_lev2)
  case (skip L C' M D T) note tr_S = this(1) and confl = this(2) and L_D = this(3) and T =this(5)
  let ?D = "mset_ccls D"
  have D: "Propagated L C' # M \<Turnstile>as CNot (mset_ccls D)" using assms skip by auto
  moreover
    have "L \<notin># ?D"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then have "- L \<in> lits_of_l M"
          using in_CNot_implies_uminus(2)[of L ?D "Propagated L C' # M"]
          \<open>Propagated L C' # M \<Turnstile>as CNot ?D\<close> by simp
        then show False
          by (metis M_lev cdcl\<^sub>W_M_level_inv_decomp(1) consistent_interp_def insert_iff
            lits_of_l_cons marked_lit.sel(2) skip.hyps(1))
      qed
  ultimately show ?case
    using tr_S confl L_D T unfolding cdcl\<^sub>W_M_level_inv_def
    by (auto intro: true_annots_CNot_lit_of_notin_skip)
next
  case (resolve L C M D T) note tr = this(1) and LC = this(2) and confl = this(4) and LD = this(5)
  and T = this(7)
  let ?C = "remove1_mset L (mset_cls C)"
  let ?D = "remove1_mset (-L) (mset_ccls D)"
  show ?case
    proof (intro allI impI)
      fix T'
      have "tl (trail S) \<Turnstile>as CNot ?C" using tr marked_confl by fastforce
      moreover
        have "distinct_mset (?D + {#- L#})" using confl dist LD
          unfolding distinct_cdcl\<^sub>W_state_def by auto
        then have "-L \<notin># ?D" unfolding distinct_mset_def
          by (meson \<open>distinct_mset (?D + {#- L#})\<close> distinct_mset_single_add)
        have "M \<Turnstile>as CNot ?D"
          proof -
            have "Propagated L (?C + {#L#}) # M \<Turnstile>as CNot ?D \<union> CNot {#- L#}"
              using confl tr confl_inv LC by (metis CNot_plus LD insert_DiffM2 option.simps(9))
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
    \<longrightarrow> (b \<Turnstile>as CNot ( mark - {#L#}) \<and> L \<in>#  mark)"
  using assms unfolding cdcl\<^sub>W_conflicting_def by blast+

lemma cdcl\<^sub>W_conflicting_decomp2:
  assumes "cdcl\<^sub>W_conflicting S" and "conflicting S = Some T"
  shows "trail S \<Turnstile>as CNot T"
  using assms unfolding cdcl\<^sub>W_conflicting_def by blast+

lemma cdcl\<^sub>W_conflicting_S0_cdcl\<^sub>W[simp]:
  "cdcl\<^sub>W_conflicting (init_state N)"
  unfolding cdcl\<^sub>W_conflicting_def by auto

subsubsection \<open>Putting all the invariants together\<close>
lemma cdcl\<^sub>W_all_inv:
  assumes
    cdcl\<^sub>W: "cdcl\<^sub>W S S'" and
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
    case 1 with H(3-7)[OF this(1-6)] show ?case using cdcl\<^sub>W_all_inv[OF H(2)]
        H by presburger
    case 2 with H(3-7)[OF this(1-6)] show ?case using cdcl\<^sub>W_all_inv[OF H(2)]
        H by presburger
    case 3 with H(3-7)[OF this(1-6)] show ?case using cdcl\<^sub>W_all_inv[OF H(2)]
        H by presburger
    case 4 with H(3-7)[OF this(1-6)] show ?case using cdcl\<^sub>W_all_inv[OF H(2)]
        H by presburger
    case 5 with H(3-7)[OF this(1-6)] show ?case using cdcl\<^sub>W_all_inv[OF H(2)]
        H by presburger
    case 6 with H(3-7)[OF this(1-6)] show ?case using cdcl\<^sub>W_all_inv[OF H(2)]
        H by presburger
qed

lemma all_invariant_S0_cdcl\<^sub>W:
  assumes "distinct_mset_mset (mset_clss N)"
  shows
    "all_decomposition_implies_m (init_clss (init_state N))
                                  (get_all_marked_decomposition (trail (init_state N)))" and
    "cdcl\<^sub>W_learned_clause (init_state N)" and
    "\<forall>T. conflicting (init_state N) = Some T \<longrightarrow> (trail (init_state N))\<Turnstile>as CNot T" and
    "no_strange_atm (init_state N)" and
    "consistent_interp (lits_of_l (trail (init_state N)))" and
    "\<forall>L mark a b. a @ Propagated L mark # b =  trail (init_state N) \<longrightarrow>
     (b \<Turnstile>as CNot ( mark - {#L#}) \<and> L \<in>#  mark)" and
     "distinct_cdcl\<^sub>W_state (init_state N)"
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
  have "atms_of_mm N \<union> atms_of_mm U = atms_of_mm N"
    using atm_incl state unfolding total_over_m_def no_strange_atm_def
     by (auto simp add: raw_clauses_def)
  then have "total_over_m I (set_mset N)" using tot unfolding total_over_m_def by auto
  moreover then have "total_over_m I (set_mset (learned_clss S))"
    using atm_incl state unfolding no_strange_atm_def total_over_m_def total_over_set_def
    by auto
  moreover have "N \<Turnstile>psm U" using learned_cl state unfolding cdcl\<^sub>W_learned_clause_def by auto
  ultimately have I_D: "I \<Turnstile> D"
    using I DN cons state unfolding true_clss_clss_def true_clss_def Ball_def
    by (auto simp add: raw_clauses_def)

  have l0: "{unmark L |L. is_marked L \<and> L \<in> set M} = {}" using marked by auto
  have "atms_of_ms (set_mset N \<union> unmark_l M) = atms_of_mm N"
    using atm_incl state unfolding no_strange_atm_def by auto
  then have "total_over_m I (set_mset N \<union> (\<lambda>a. {#lit_of a#}) ` (set M))"
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
    then have "-K \<in> I" using IM true_clss_singleton_lit_of_implies_incl lits_of_def by fastforce  }
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
  shows "set_mset N \<Turnstile>ps unmark_l M"
proof -
  have T: "{unmark L |L. is_marked L \<and> L \<in> set M} = {}" using assms(2) by auto
  then show ?thesis
    using all_decomposition_implies_propagated_lits_are_implied[OF assms(1)] unfolding T by simp
qed

(*prop 2.10.5.6*)
lemma conflict_with_false_implies_unsat:
  assumes
    cdcl\<^sub>W: "cdcl\<^sub>W S S'" and
    lev: "cdcl\<^sub>W_M_level_inv S" and
    [simp]: "conflicting S' = Some {#}" and
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
  and "conflicting S = Some {#}"
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
  case (backtrack K i M1 M2 L D T) note confl = this(1)
  have "consistent_interp (lits_of_l (trail S))" using lev by (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
  moreover
    have "trail S \<Turnstile>as CNot (mset_ccls D)"
      using conflicting confl unfolding cdcl\<^sub>W_conflicting_def by auto
    then have "lits_of_l (trail S) \<Turnstile>s CNot (mset_ccls D)"
      using true_annots_true_cls by blast
  ultimately have "\<not>tautology (mset_ccls D)" using consistent_CNot_not_tautology by blast
  then show ?case using backtrack no_tauto lev
    by (auto simp: cdcl\<^sub>W_M_level_inv_decomp split: if_split_asm)
next
  case restart
  then show ?case using learned_clss_restart_state state_eq_learned_clss no_tauto
    by (metis (no_types, lifting) set_mset_mono subsetCE)
qed (auto dest!: in_diffD)

definition "final_cdcl\<^sub>W_state (S:: 'st)
  \<longleftrightarrow> (trail S \<Turnstile>asm init_clss S
    \<or> ((\<forall>L \<in> set (trail S). \<not>is_marked L) \<and>
       (\<exists>C \<in># init_clss S. trail S \<Turnstile>as CNot C)))"

definition "termination_cdcl\<^sub>W_state (S:: 'st)
   \<longleftrightarrow> (trail S \<Turnstile>asm init_clss S
     \<or> ((\<forall>L \<in> atms_of_mm (init_clss S). L \<in> atm_of ` lits_of_l (trail S))
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
    "atm_of ` (set M) \<subseteq> atms_of_mm (mset_clss N)"
  shows "\<exists>S. rtranclp cdcl\<^sub>W (init_state N) S
    \<and> state S = (mapi Marked (length M) M, mset_clss N, {#}, length M, None)"
  using assms
proof (induct M)
  case Nil
  then show ?case apply - by (rule exI[of _ "init_state N"]) auto
next
  case (Cons L M) note IH = this(1)
  have "consistent_interp (set M)" and "distinct M" and "atm_of ` set M \<subseteq> atms_of_mm (mset_clss N)"
    using Cons.prems(1-3) unfolding consistent_interp_def by auto
  then obtain S where
    st: "cdcl\<^sub>W\<^sup>*\<^sup>* (init_state N) S" and
    S: "state S = (mapi Marked (length M) M, mset_clss N, {#}, length M, None)"
    using IH by blast
  let ?S\<^sub>0 = "incr_lvl (cons_trail (Marked L (length M +1)) S)"
  have "undefined_lit (mapi Marked (length M) M) L"
    using Cons.prems(1,2) unfolding defined_lit_def consistent_interp_def by fastforce
  moreover have "init_clss S = mset_clss N"
    using S by blast
  moreover have "atm_of L \<in> atms_of_mm (mset_clss N)" using Cons.prems(3) by auto
  moreover have undef: "undefined_lit (trail S) L"
    using S \<open>distinct (L#M)\<close> calculation(1) by (auto simp: defined_lit_mapi defined_lit_map)
  ultimately have "cdcl\<^sub>W S ?S\<^sub>0"
    using cdcl\<^sub>W.other[OF cdcl\<^sub>W_o.decide[OF decide_rule[of S L ?S\<^sub>0]]] S
    by (auto simp: state_eq_def simp del: state_simp)
  then have "cdcl\<^sub>W\<^sup>*\<^sup>* (init_state N) ?S\<^sub>0"
    using st by auto
  then show ?case
    using S undef by (auto intro!: exI[of _ ?S\<^sub>0] del: simp del: )
qed

lemma cdcl\<^sub>W_strong_completeness:
  assumes
    MN: "set M \<Turnstile>sm mset_clss N" and
    cons: "consistent_interp (set M)" and
    dist: "distinct M" and
    atm: "atm_of ` (set M) \<subseteq> atms_of_mm (mset_clss N)"
  obtains S where
    "state S = (mapi Marked (length M) M, mset_clss N, {#}, length M, None)" and
    "rtranclp cdcl\<^sub>W (init_state N) S" and
    "final_cdcl\<^sub>W_state S"
proof -
  obtain S where
    st: "rtranclp cdcl\<^sub>W (init_state N) S" and
    S: "state S = (mapi Marked (length M) M, mset_clss N, {#}, length M, None)"
    using cdcl\<^sub>W_can_do_step[OF cons dist atm] by auto
  have "lits_of_l (mapi Marked (length M) M) = set M"
    by (induct M, auto)
  then have "mapi Marked (length M) M \<Turnstile>asm mset_clss N" using MN true_annots_true_cls by metis
  then have "final_cdcl\<^sub>W_state S"
    using S unfolding final_cdcl\<^sub>W_state_def by auto
  then show ?thesis using that st S by blast
qed

subsection \<open>Higher level strategy\<close>

text \<open>The rules described previously do not lead to a conclusive state. We have to add a strategy.\<close>

subsubsection \<open>Definition\<close>
lemma tranclp_conflict:
  "tranclp conflict S S' \<Longrightarrow> conflict S S'"
  apply (induct rule: tranclp.induct)
   apply simp
  by (metis conflictE conflicting_update_conflicting option.distinct(1) option.simps(8,9)
    state_eq_conflicting)

lemma tranclp_conflict_iff[iff]:
  "full1 conflict S S' \<longleftrightarrow> conflict S S'"
proof -
  have "tranclp conflict S S' \<Longrightarrow> conflict S S'" by (meson tranclp_conflict rtranclpD)
  then show ?thesis unfolding full1_def
  by (metis conflict.simps conflicting_update_conflicting option.distinct(1) option.simps(9)
    state_eq_conflicting tranclp.intros(1))
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

lemma option_full_cdcl\<^sub>W_cp:
  "conflicting S \<noteq> None \<Longrightarrow> full cdcl\<^sub>W_cp S S"
  unfolding full_def rtranclp_unfold tranclp_unfold
  by (auto simp add: cdcl\<^sub>W_cp.simps elim: conflictE propagateE)

lemma skip_unique:
  "skip S T \<Longrightarrow> skip S T' \<Longrightarrow> T \<sim> T'"
  by (fastforce simp: state_eq_def simp del: state_simp elim: skipE)

lemma resolve_unique:
  "resolve S T \<Longrightarrow> resolve S T' \<Longrightarrow> T \<sim> T'"
  by (fastforce simp: state_eq_def simp del: state_simp elim: resolveE)

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
  by (metis None_eq_map_option_iff conflictE conflicting_update_conflicting option.distinct(1)
    state_simp(5))

lemma no_propagate_after_conflict:
  "conflict S T \<Longrightarrow> \<not>propagate T U"
  by (metis conflictE conflicting_update_conflicting map_option_is_None option.distinct(1)
    propagate.cases state_eq_conflicting)

lemma tranclp_cdcl\<^sub>W_cp_propagate_with_conflict_or_not:
  assumes "cdcl\<^sub>W_cp\<^sup>+\<^sup>+ S U"
  shows "(propagate\<^sup>+\<^sup>+ S U \<and> conflicting U = None)
    \<or> (\<exists>T D. propagate\<^sup>*\<^sup>* S T \<and> conflict T U \<and> conflicting U = Some D)"
proof -
  have "propagate\<^sup>+\<^sup>+ S U \<or> (\<exists>T. propagate\<^sup>*\<^sup>* S T \<and> conflict T U)"
    using assms by induction
    (force simp: cdcl\<^sub>W_cp.simps tranclp_into_rtranclp dest: no_conflict_after_conflict
       no_propagate_after_conflict)+
  moreover
    have "propagate\<^sup>+\<^sup>+ S U \<Longrightarrow> conflicting U = None"
      unfolding tranclp_unfold_end by (auto elim!: propagateE)
  moreover
    have "\<And>T. conflict T U \<Longrightarrow> \<exists>D. conflicting U = Some D"
      by (auto elim!: conflictE simp: state_eq_def simp del: state_simp)
  ultimately show ?thesis by meson
qed

lemma cdcl\<^sub>W_cp_conflicting_not_empty[simp]: "conflicting S = Some D  \<Longrightarrow> \<not>cdcl\<^sub>W_cp S S'"
proof
  assume "cdcl\<^sub>W_cp S S'" and "conflicting S = Some D"
  then show False by (induct rule: cdcl\<^sub>W_cp.induct)
  (auto elim: conflictE propagateE simp: state_eq_def simp del: state_simp)
qed

lemma no_step_cdcl\<^sub>W_cp_no_conflict_no_propagate:
  assumes "no_step cdcl\<^sub>W_cp S"
  shows "no_step conflict S" and "no_step propagate S"
  using assms conflict' apply blast
  by (meson assms conflict' propagate')

text \<open>CDCL with the reasonable strategy: we fully propagate the conflict and propagate, then we
  apply any other possible rule @{term "cdcl\<^sub>W_o S S'"} and re-apply conflict and propagate
  @{term "full cdcl\<^sub>W_cp S' S''"}\<close>
inductive cdcl\<^sub>W_stgy :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
conflict': "full1 cdcl\<^sub>W_cp S S' \<Longrightarrow> cdcl\<^sub>W_stgy S S'" |
other': "cdcl\<^sub>W_o S S'  \<Longrightarrow> no_step cdcl\<^sub>W_cp S \<Longrightarrow> full cdcl\<^sub>W_cp S' S'' \<Longrightarrow> cdcl\<^sub>W_stgy S S''"

subsubsection \<open>Invariants\<close>
text \<open>These are the same invariants as before, but lifted\<close>
lemma cdcl\<^sub>W_cp_learned_clause_inv:
  assumes "cdcl\<^sub>W_cp S S'"
  shows "learned_clss S = learned_clss S'"
  using assms by (induct rule: cdcl\<^sub>W_cp.induct) (fastforce elim: conflictE propagateE)+

lemma rtranclp_cdcl\<^sub>W_cp_learned_clause_inv:
  assumes "cdcl\<^sub>W_cp\<^sup>*\<^sup>* S S'"
  shows "learned_clss S = learned_clss S'"
  using assms by (induct rule: rtranclp_induct) (fastforce dest: cdcl\<^sub>W_cp_learned_clause_inv)+

lemma tranclp_cdcl\<^sub>W_cp_learned_clause_inv:
  assumes "cdcl\<^sub>W_cp\<^sup>+\<^sup>+ S S'"
  shows "learned_clss S = learned_clss S'"
  using assms by (simp add: rtranclp_cdcl\<^sub>W_cp_learned_clause_inv tranclp_into_rtranclp)

lemma cdcl\<^sub>W_cp_backtrack_lvl:
  assumes "cdcl\<^sub>W_cp S S'"
  shows "backtrack_lvl S = backtrack_lvl S'"
  using assms by (induct rule: cdcl\<^sub>W_cp.induct) (fastforce elim: conflictE propagateE)+

lemma rtranclp_cdcl\<^sub>W_cp_backtrack_lvl:
  assumes "cdcl\<^sub>W_cp\<^sup>*\<^sup>* S S'"
  shows "backtrack_lvl S = backtrack_lvl S'"
  using assms by (induct rule: rtranclp_induct) (fastforce dest: cdcl\<^sub>W_cp_backtrack_lvl)+

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
  by (metis rtranclp_cdcl\<^sub>W_cp_rtranclp_cdcl\<^sub>W rtranclp_unfold tranclp_cdcl\<^sub>W_consistent_inv)

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
  using assms by (induct rule: cdcl\<^sub>W_cp.induct) (auto elim: conflictE propagateE)

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
  apply (induct rule: rtranclp_induct, simp)
  using cdcl\<^sub>W_stgy_no_more_init_clss by (simp add: rtranclp_cdcl\<^sub>W_stgy_consistent_inv)

lemma cdcl\<^sub>W_cp_dropWhile_trail':
  assumes "cdcl\<^sub>W_cp S S'"
  obtains M where "trail S' = M @ trail S" and " (\<forall>l \<in> set M. \<not>is_marked l)"
  using assms by induction (fastforce elim: conflictE propagateE)+

lemma rtranclp_cdcl\<^sub>W_cp_dropWhile_trail':
  assumes "cdcl\<^sub>W_cp\<^sup>*\<^sup>* S S'"
  obtains M :: "('v, nat, 'v clause) marked_lit list" where
    "trail S' = M @ trail S" and "\<forall>l \<in> set M. \<not>is_marked l"
  using assms by induction (fastforce dest!: cdcl\<^sub>W_cp_dropWhile_trail')+

lemma cdcl\<^sub>W_cp_dropWhile_trail:
  assumes "cdcl\<^sub>W_cp S S'"
  shows "\<exists>M. trail S' = M @ trail S \<and> (\<forall>l \<in> set M. \<not>is_marked l)"
  using assms by induction (fastforce elim: conflictE propagateE)+

lemma rtranclp_cdcl\<^sub>W_cp_dropWhile_trail:
  assumes "cdcl\<^sub>W_cp\<^sup>*\<^sup>* S S'"
  shows "\<exists>M. trail S' = M @ trail S \<and> (\<forall>l \<in> set M. \<not>is_marked l)"
  using assms by induction (fastforce dest: cdcl\<^sub>W_cp_dropWhile_trail)+

text \<open>This theorem can be seen a a termination theorem for @{term cdcl\<^sub>W_cp}.\<close>
lemma length_model_le_vars:
  assumes
    "no_strange_atm S" and
    no_d: "no_dup (trail S)" and
    "finite (atms_of_mm (init_clss S))"
  shows "length (trail S) \<le> card (atms_of_mm (init_clss S))"
proof -
  obtain M N U k D where S: "state S = (M, N, U, k, D)" by (cases "state S", auto)
  have "finite (atm_of ` lits_of_l (trail S))"
    using assms(1,3) unfolding S by (auto simp add: finite_subset)
  have "length (trail S) = card (atm_of ` lits_of_l (trail S))"
    using no_dup_length_eq_card_atm_of_lits_of_l no_d by blast
  then show ?thesis using assms(1) unfolding no_strange_atm_def
  by (auto simp add: assms(3) card_mono)
qed

lemma cdcl\<^sub>W_cp_decreasing_measure:
  assumes
    cdcl\<^sub>W: "cdcl\<^sub>W_cp S T" and
    M_lev: "cdcl\<^sub>W_M_level_inv S" and
    alien: "no_strange_atm S"
  shows "(\<lambda>S. card (atms_of_mm (init_clss S)) - length (trail S)
      + (if conflicting S = None then 1 else 0)) S
    > (\<lambda>S. card (atms_of_mm (init_clss S)) - length (trail S)
      + (if conflicting S = None then 1 else 0)) T"
  using assms
proof -
  have "length (trail T) \<le> card (atms_of_mm (init_clss T))"
    apply (rule length_model_le_vars)
       using cdcl\<^sub>W_no_strange_atm_inv alien M_lev apply (meson cdcl\<^sub>W cdcl\<^sub>W.simps cdcl\<^sub>W_cp.cases)
      using M_lev cdcl\<^sub>W cdcl\<^sub>W_cp_consistent_inv cdcl\<^sub>W_M_level_inv_def apply blast
      using cdcl\<^sub>W by (auto simp: cdcl\<^sub>W_cp.simps)
  with assms
  show ?thesis by induction (auto elim!: conflictE propagateE
    simp del: state_simp simp: state_eq_def)+
qed

lemma cdcl\<^sub>W_cp_wf: "wf {(b,a). (cdcl\<^sub>W_M_level_inv a \<and> no_strange_atm a)
  \<and> cdcl\<^sub>W_cp a b}"
  apply (rule wf_wf_if_measure'[of less_than _ _
      "(\<lambda>S. card (atms_of_mm (init_clss S)) - length (trail S)
        + (if conflicting S = None then 1 else 0))"])
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

lemma always_exists_full_cdcl\<^sub>W_cp_step:
  assumes "no_strange_atm S"
  shows "\<exists>S''. full cdcl\<^sub>W_cp S S''"
  using assms
proof (induct "card (atms_of_mm (init_clss S) - atm_of `lits_of_l (trail S))" arbitrary: S)
  case 0 note card = this(1) and alien = this(2)
  then have atm: "atms_of_mm (init_clss S) = atm_of ` lits_of_l (trail S)"
    unfolding no_strange_atm_def by auto
  { assume a: "\<exists>S'. conflict S S'"
    then obtain S' where S': "conflict S S'" by metis
    then have "\<forall>S''. \<not>cdcl\<^sub>W_cp S' S''"
      by (auto simp: cdcl\<^sub>W_cp.simps elim!: conflictE propagateE
        simp del: state_simp simp: state_eq_def)
    then have ?case using a S' cdcl\<^sub>W_cp.conflict' unfolding full_def by blast
  }
  moreover {
    assume a: "\<exists>S'. propagate S S'"
    then obtain S' where "propagate S S'" by blast
    then obtain E L where
      S: "conflicting S = None" and
      E:  "E !\<in>! raw_clauses S" and
      LE: "L \<in># mset_cls E" and
      tr: "trail S \<Turnstile>as CNot (mset_cls (remove_lit L E))" and
      undef: "undefined_lit (trail S) L" and
      S': "S' \<sim> cons_trail (Propagated L E) S"
      by (elim propagateE) simp
    have "atms_of_mm (learned_clss S) \<subseteq> atms_of_mm (init_clss S)"
      using alien S unfolding no_strange_atm_def by auto
    then have "atm_of L \<in> atms_of_mm (init_clss S)"
      using E LE S undef unfolding raw_clauses_def by (force simp: in_implies_atm_of_on_atms_of_ms)
    then have False using undef S unfolding atm unfolding lits_of_def
      by (auto simp add: defined_lit_map)
  }
  ultimately show ?case unfolding full_def by (metis cdcl\<^sub>W_cp.cases rtranclp.rtrancl_refl)
next
  case (Suc n) note IH = this(1) and card = this(2) and alien = this(3)
  { assume a: "\<exists>S'. conflict S S'"
    then obtain S' where S': "conflict S S'" by metis
    then have "\<forall>S''. \<not>cdcl\<^sub>W_cp S' S''"
      by (auto simp: cdcl\<^sub>W_cp.simps elim!: conflictE propagateE
        simp del: state_simp simp: state_eq_def)
    then have ?case  unfolding full_def Ex_def using S' cdcl\<^sub>W_cp.conflict' by blast
  }
  moreover {
    assume a: "\<exists>S'. propagate S S'"
    then obtain S' where propagate: "propagate S S'" by blast
    then obtain E L where
      S: "conflicting S = None" and
      E:  "E !\<in>! raw_clauses S" and
      LE: "L \<in># mset_cls E" and
      tr: "trail S \<Turnstile>as CNot (mset_cls (remove_lit L E))" and
      undef: "undefined_lit (trail S) L" and
      S': "S' \<sim> cons_trail (Propagated L E) S"
      by (elim propagateE) simp
    then have "atm_of L \<notin> atm_of ` lits_of_l (trail S)"
      unfolding lits_of_def by (auto simp add: defined_lit_map)
    moreover
      have "no_strange_atm S'" using alien propagate propagate_no_strange_atm_inv by blast
      then have "atm_of L \<in> atms_of_mm (init_clss S)"
        using S' LE E undef unfolding no_strange_atm_def
        by (auto simp: raw_clauses_def in_implies_atm_of_on_atms_of_ms)
      then have "\<And>A. {atm_of L} \<subseteq> atms_of_mm (init_clss S) - A \<or> atm_of L \<in> A" by force
    moreover have "Suc n - card {atm_of L} = n" by simp
    moreover have "card (atms_of_mm (init_clss S) - atm_of ` lits_of_l (trail S)) = Suc n"
     using card S S' by simp
    ultimately
      have "card (atms_of_mm (init_clss S) - atm_of ` insert L (lits_of_l (trail S))) = n"
        by (metis (no_types) Diff_insert card_Diff_subset finite.emptyI finite.insertI image_insert)
      then have "n = card (atms_of_mm (init_clss S') - atm_of ` lits_of_l (trail S'))"
        using card S S' undef by simp
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
  \<lambda>S. (conflicting S = None \<longrightarrow> (\<forall>D \<in># clauses S. \<not>trail S \<Turnstile>as CNot D))"

abbreviation conflict_is_false_with_level :: "'st \<Rightarrow> bool" where
"conflict_is_false_with_level S \<equiv> \<forall>D. conflicting S = Some D \<longrightarrow> D \<noteq> {#}
  \<longrightarrow> (\<exists>L \<in># D. get_level (trail S) L = backtrack_lvl S)"

lemma not_conflict_not_any_negated_init_clss:
  assumes "\<forall> S'. \<not>conflict S S'"
  shows "no_clause_is_false S"
proof (clarify)
  fix D
  assume "D \<in># local.clauses S" and "raw_conflicting S = None" and "trail S \<Turnstile>as CNot D "
  moreover then obtain D' where
    "mset_cls D' = D" and
    "D' !\<in>! raw_clauses S"
    using in_mset_clss_exists_preimage unfolding raw_clauses_def by blast
  ultimately show False
    using conflict_rule[of S D' "update_conflicting (Some (ccls_of_cls D')) S"] assms
    by auto
qed

lemma full_cdcl\<^sub>W_cp_not_any_negated_init_clss:
  assumes "full cdcl\<^sub>W_cp S S'"
  shows "no_clause_is_false S'"
  using assms not_conflict_not_any_negated_init_clss unfolding full_def by auto

lemma full1_cdcl\<^sub>W_cp_not_any_negated_init_clss:
  assumes "full1 cdcl\<^sub>W_cp S S'"
  shows "no_clause_is_false S'"
  using assms not_conflict_not_any_negated_init_clss unfolding full1_def by auto

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
  then show ?case by (auto elim: conflictE)
next
  case propagate'
  then show ?case by (auto elim: propagateE)
qed

lemma no_chained_conflict:
  assumes "conflict S S'"
  and "conflict S' S''"
  shows False
  using assms unfolding conflict.simps
  by (metis conflicting_update_conflicting option.distinct(1) option.simps(9) state_eq_conflicting)

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
      then have False using UV by (auto elim: conflictE)
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
  assume
    confl: "conflicting U = Some D" and
    D: "D \<noteq> {#}"
  consider (CT) "conflicting S = None" | (SD) D' where "conflicting S = Some D'"
    by (cases "conflicting S") auto
  then show "\<exists>L\<in>#D. get_level (trail U) L = backtrack_lvl U"
    proof cases
      case SD
      then have "S = U"
        by (metis (no_types) assms(1) cdcl\<^sub>W_cp_conflicting_not_empty full_def rtranclpD tranclpD)
      then show  ?thesis using assms(3) confl D by blast-
    next
      case CT
      have "init_clss U = init_clss S" and "learned_clss U = learned_clss S"
        using full unfolding full_def
          apply (metis (no_types) rtranclpD tranclp_cdcl\<^sub>W_cp_no_more_init_clss)
        by (metis (mono_tags, lifting) full full_def rtranclp_cdcl\<^sub>W_cp_learned_clause_inv)
      obtain T where "propagate\<^sup>*\<^sup>* S T" and TU: "conflict T U"
        proof -
          have f5: "U \<noteq> S"
            using confl CT by force
          then have "cdcl\<^sub>W_cp\<^sup>+\<^sup>+ S U"
            by (metis full full_def rtranclpD)
          have "\<And>p pa. \<not> propagate p pa \<or> conflicting pa =
            (None::'v clause option)"
            by (auto elim: propagateE)
          then show ?thesis
            using f5 that tranclp_cdcl\<^sub>W_cp_propagate_with_conflict_or_not[OF \<open>cdcl\<^sub>W_cp\<^sup>+\<^sup>+ S U\<close>]
            full confl CT unfolding full_def by auto
        qed
      obtain D' where
        "raw_conflicting T = None" and
        D': "D' !\<in>! raw_clauses T" and
        tr: "trail T \<Turnstile>as CNot (mset_cls D')" and
        U: "U \<sim> update_conflicting (Some (ccls_of_cls D')) T"
        using TU by (auto elim!: conflictE)
      have "init_clss T = init_clss S" and "learned_clss T = learned_clss S"
        using U \<open>init_clss U = init_clss S\<close> \<open>learned_clss U = learned_clss S\<close>  by auto
      then have "D \<in># clauses S"
        using confl U D' by (auto simp: raw_clauses_def)
      then have "\<not> trail S \<Turnstile>as CNot D"
        using cls_f CT by simp

      moreover
        obtain M where tr_U: "trail U = M @ trail S" and nm: "\<forall>m\<in>set M. \<not>is_marked m"
          by (metis (mono_tags, lifting) assms(1) full_def rtranclp_cdcl\<^sub>W_cp_dropWhile_trail)
        have "trail U \<Turnstile>as CNot D"
          using tr confl U by (auto elim!: conflictE)
      ultimately obtain L where "L \<in># D" and "-L \<in> lits_of_l M"
        unfolding tr_U CNot_def true_annots_def Ball_def true_annot_def true_cls_def by force

      moreover have inv_U: "cdcl\<^sub>W_M_level_inv U"
        by (metis cdcl\<^sub>W_stgy.conflict' cdcl\<^sub>W_stgy_consistent_inv full full_unfold lev)
      moreover
        have "backtrack_lvl U = backtrack_lvl S"
          using full unfolding full_def by (auto dest: rtranclp_cdcl\<^sub>W_cp_backtrack_lvl)

      moreover
        have "no_dup (trail U)"
          using inv_U unfolding cdcl\<^sub>W_M_level_inv_def by auto
        { fix x :: "('v, nat, 'v clause) marked_lit" and
            xb :: "('v, nat, 'v clause) marked_lit"
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
        then have LS: "atm_of L \<notin> atm_of ` lits_of_l (trail S)"
          using \<open>-L \<in> lits_of_l M\<close> \<open>no_dup (trail U)\<close> unfolding tr_U lits_of_def by auto
      ultimately have "get_level (trail U) L = backtrack_lvl U"
        proof (cases "get_all_levels_of_marked (trail S) \<noteq> []", goal_cases)
          case 2 note LD = this(1) and LM = this(2) and inv_U = this(3) and US = this(4) and
            LS = this(5) and ne = this(6)
          have "backtrack_lvl S = 0"
            using lev ne unfolding cdcl\<^sub>W_M_level_inv_def by auto
          moreover have "get_rev_level (rev M) 0 L = 0"
            using nm by auto
          ultimately show ?thesis using LS ne US unfolding tr_U
            by (simp add: get_all_levels_of_marked_nil_iff_not_is_marked lits_of_def)
        next
          case 1 note LD = this(1) and LM = this(2) and inv_U = this(3) and US = this(4) and
            LS = this(5) and ne = this(6)

          have "hd (get_all_levels_of_marked (trail S)) = backtrack_lvl S"
            using ne lev unfolding cdcl\<^sub>W_M_level_inv_def
            by (cases "get_all_levels_of_marked (trail S)") auto
          moreover have "atm_of L \<in> atm_of ` lits_of_l M "
            using \<open>-L \<in> lits_of_l M\<close> by (simp add: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
              lits_of_def)
          ultimately show ?thesis
            using nm ne get_level_skip_beginning_hd_get_all_levels_of_marked[OF LS, of M]
              get_level_skip_in_all_not_marked[of "rev M" L "backtrack_lvl S"]
            unfolding lits_of_def US tr_U
            by auto
          qed
      then show "\<exists>L\<in>#D. get_level (trail U) L = backtrack_lvl U"
        using \<open>L \<in># D\<close> by blast
    qed
qed

subsubsection \<open>Literal of highest level in marked literals\<close>
definition mark_is_false_with_level :: "'st \<Rightarrow> bool" where
"mark_is_false_with_level S' \<equiv>
  \<forall>D M1 M2 L.  M1 @ Propagated L D # M2 = trail S' \<longrightarrow>  D - {#L#} \<noteq> {#}
    \<longrightarrow> (\<exists>L. L \<in>#  D \<and> get_level (trail S') L = get_maximum_possible_level M1)"

definition no_more_propagation_to_do:: "'st \<Rightarrow> bool" where
"no_more_propagation_to_do S \<equiv>
  \<forall>D M M' L. D + {#L#} \<in># clauses S \<longrightarrow> trail S = M' @ M \<longrightarrow> M \<Turnstile>as CNot D
    \<longrightarrow> undefined_lit M L \<longrightarrow> get_maximum_possible_level M < backtrack_lvl S
    \<longrightarrow> (\<exists>L. L \<in># D \<and> get_level (trail S) L = get_maximum_possible_level M)"

lemma propagate_no_more_propagation_to_do:
  assumes propagate: "propagate S S'"
  and H: "no_more_propagation_to_do S"
  and lev_inv: "cdcl\<^sub>W_M_level_inv S"
  shows "no_more_propagation_to_do S'"
  using assms
proof -
  obtain E L where
    S: "conflicting S = None" and
    E:  "E !\<in>! raw_clauses S" and
    LE: "L \<in># mset_cls E" and
    tr: "trail S \<Turnstile>as CNot (mset_cls (remove_lit L E))" and
    undefL: "undefined_lit (trail S) L" and
    S': "S' \<sim> cons_trail (Propagated L E) S"
    using propagate by (elim propagateE) simp
  let ?M' = "Propagated L (mset_cls E) # trail S"
  show ?thesis unfolding no_more_propagation_to_do_def
    proof (intro allI impI)
      fix D M1 M2 L'
      assume
        D_L: "D + {#L'#} \<in># clauses S'" and
        "trail S' = M2 @ M1" and
        get_max: "get_maximum_possible_level M1 < backtrack_lvl S'" and
        "M1 \<Turnstile>as CNot D" and
        undef: "undefined_lit M1 L'"
      have "tl M2 @ M1 = trail S \<or> (M2 = [] \<and> M1 = Propagated L (mset_cls E) # trail S)"
        using \<open>trail S' = M2 @ M1\<close> S' S undefL lev_inv
        by (cases M2) (auto simp:cdcl\<^sub>W_M_level_inv_decomp)
      moreover {
        assume "tl M2 @ M1 = trail S"
        moreover have "D + {#L'#} \<in># clauses S"
          using D_L S S' undefL unfolding raw_clauses_def by auto
        moreover have "get_maximum_possible_level M1 < backtrack_lvl S"
          using get_max S S' undefL by auto
        ultimately obtain L' where "L' \<in># D" and
          "get_level (trail S) L' = get_maximum_possible_level M1"
          using H \<open>M1 \<Turnstile>as CNot D\<close> undef unfolding no_more_propagation_to_do_def by metis
        moreover
          { have "cdcl\<^sub>W_M_level_inv S'"
              using cdcl\<^sub>W_consistent_inv lev_inv cdcl\<^sub>W.propagate[OF propagate] by blast
            then have "no_dup ?M'" using S' undefL unfolding cdcl\<^sub>W_M_level_inv_def by auto
            moreover
              have "atm_of L' \<in> atm_of ` (lits_of_l M1)"
                using \<open>L' \<in># D\<close> \<open>M1 \<Turnstile>as CNot D\<close> by (metis atm_of_uminus image_eqI
                  in_CNot_implies_uminus(2))
              then have "atm_of L' \<in> atm_of ` (lits_of_l (trail S))"
                using \<open>tl M2 @ M1 = trail S\<close>[symmetric] S undefL by auto
            ultimately have "atm_of L \<noteq> atm_of L'" unfolding lits_of_def by auto
        }
        ultimately have "\<exists>L' \<in># D. get_level (trail S') L' = get_maximum_possible_level M1"
          using S S' undefL by auto
      }
      moreover {
        assume "M2 = []" and M1: "M1 = Propagated L (mset_cls E) # trail S"
        have "cdcl\<^sub>W_M_level_inv S'"
          using cdcl\<^sub>W_consistent_inv[OF _ lev_inv] cdcl\<^sub>W.propagate[OF propagate] by blast
        then have "get_all_levels_of_marked (trail S') = rev [Suc 0..<(Suc 0+backtrack_lvl S)]"
          using S' undefL unfolding cdcl\<^sub>W_M_level_inv_def by auto
        then have "get_maximum_possible_level M1 = backtrack_lvl S'"
          using get_maximum_possible_level_max_get_all_levels_of_marked[of M1] S' M1 undefL
          by (auto intro: Max_eqI)
        then have False using get_max by auto
      }
      ultimately show "\<exists>L. L \<in># D \<and> get_level (trail S') L = get_maximum_possible_level M1"
        by fast
   qed
qed

lemma conflict_no_more_propagation_to_do:
  assumes
    conflict: "conflict S S'" and
    H: "no_more_propagation_to_do S" and
    M: "cdcl\<^sub>W_M_level_inv S"
  shows "no_more_propagation_to_do S'"
  using assms unfolding no_more_propagation_to_do_def by (force elim!: conflictE)

lemma cdcl\<^sub>W_cp_no_more_propagation_to_do:
  assumes
    conflict: "cdcl\<^sub>W_cp S S'" and
    H: "no_more_propagation_to_do S" and
    M: "cdcl\<^sub>W_M_level_inv S"
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
  assumes
    S: "raw_conflicting S = Some E" and
    LE: "L \<in># mset_ccls E" and
    L: "get_level (trail S) L = backtrack_lvl S" and
    D: "get_maximum_level (trail S) (remove1_mset L (mset_ccls E)) < backtrack_lvl S" and
    bt: "backtrack_lvl S = get_maximum_level (trail S) (mset_ccls E)" and
    M_L: "cdcl\<^sub>W_M_level_inv S"
  shows "\<exists>S'. cdcl\<^sub>W_o S S'"
proof -
  have L_D: "get_level (trail S) L = get_maximum_level (trail S) (mset_ccls E)"
    using L D bt by (simp add: get_maximum_level_plus)
  let ?i = "get_maximum_level (trail S) (remove1_mset L (mset_ccls E))"
  obtain K M1 M2 where
    K: "(Marked K (?i + 1) # M1, M2) \<in> set (get_all_marked_decomposition (trail S))"
    using backtrack_ex_decomp[OF M_L, of ?i] D S by auto
  show ?thesis using backtrack_rule[OF S LE K L] bt L bj cdcl\<^sub>W_bj.simps by auto
qed

lemma cdcl\<^sub>W_stgy_final_state_conclusive:
  assumes
    termi: "\<forall>S'. \<not>cdcl\<^sub>W_stgy S S'" and
    decomp: "all_decomposition_implies_m (init_clss S) (get_all_marked_decomposition (trail S))" and
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
      (None) "raw_conflicting S = None"
    | (Some_Empty) E where "raw_conflicting S = Some E" and "mset_ccls E = {#}"
    | (Some) E' where "raw_conflicting S = Some E'" and
      "conflicting S = Some (mset_ccls E')" and "mset_ccls E' \<noteq> {#}"
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
      { assume "\<not>?M \<Turnstile>asm ?N"
        have "atm_of ` (lits_of_l ?M) = atms_of_mm ?N" (is "?A = ?B")
          proof
            show "?A \<subseteq> ?B" using alien unfolding no_strange_atm_def by auto
            show "?B \<subseteq> ?A"
              proof (rule ccontr)
                assume "\<not>?B \<subseteq> ?A"
                then obtain l where "l \<in> ?B" and "l \<notin> ?A" by auto
                then have "undefined_lit ?M (Pos l)"
                  using \<open>l \<notin> ?A\<close> unfolding lits_of_def by (auto simp add: defined_lit_map)
                moreover have "conflicting S = None"
                  using None by auto
                ultimately have "\<exists>S'. cdcl\<^sub>W_o S S'"
                  using cdcl\<^sub>W_o.decide decide_rule \<open>l \<in> ?B\<close> no_strange_atm_def
                  by (metis literal.sel(1) state_eq_def)
                then show False
                  using termi cdcl\<^sub>W_then_exists_cdcl\<^sub>W_stgy_step[OF _ alien]  level_inv by blast
              qed
          qed
        obtain D where "\<not> ?M \<Turnstile>a D" and "D \<in># ?N"
           using \<open>\<not>?M \<Turnstile>asm ?N\<close> unfolding lits_of_def true_annots_def Ball_def by auto
        have "atms_of D \<subseteq> atm_of ` (lits_of_l ?M)"
          using \<open>D \<in># ?N\<close> unfolding \<open>atm_of ` (lits_of_l ?M) = atms_of_mm ?N\<close> atms_of_ms_def
          by (auto simp add: atms_of_def)
        then have a1: "atm_of ` set_mset D \<subseteq> atm_of ` lits_of_l (trail S)"
          by (auto simp add: atms_of_def lits_of_def)
        have "total_over_m (lits_of_l ?M) {D}"
          using \<open>atms_of D \<subseteq> atm_of ` (lits_of_l ?M)\<close>
          atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set by (fastforce simp: total_over_set_def)
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
              using f2 \<open>D \<in># init_clss S\<close> None \<open>trail S \<Turnstile>as CNot D\<close>
              raw_clauses_def full_cdcl\<^sub>W_cp_not_any_negated_init_clss by auto
          qed
      }
      then have "?M \<Turnstile>asm ?N" by blast
      then show ?thesis
        using None by auto
    next
      case (Some E') note raw_conf = this(1) and LD = this(2) and nempty = this(3)
      then obtain L D where
        E'[simp]: "mset_ccls E' = D + {#L#}" and
        lev_L: "get_level ?M L = ?k"
        by (metis (mono_tags) confl_k insert_DiffM2)
      let ?D = "D + {#L#}"
      have "?D \<noteq> {#}" by auto
      have "?M \<Turnstile>as CNot ?D" using confl LD unfolding cdcl\<^sub>W_conflicting_def by auto
      then have "?M \<noteq> []" unfolding true_annots_def Ball_def true_annot_def true_cls_def by force
      have M: "?M = hd ?M # tl ?M" using \<open>?M \<noteq> []\<close> list.collapse by fastforce
      have g_a_l: "get_all_levels_of_marked ?M = rev [1..<1 + ?k]"
        using level_inv lev_L M unfolding cdcl\<^sub>W_M_level_inv_def by auto
      have g_k: "get_maximum_level (trail S) D \<le> ?k"
        using get_maximum_possible_level_ge_get_maximum_level[of ?M]
          get_maximum_possible_level_max_get_all_levels_of_marked[of ?M]
        by (auto simp add: Max_n_upt g_a_l)
      {
        assume marked: "is_marked (hd ?M)"
        then obtain k' where k': "k' + 1 = ?k"
          using level_inv M unfolding cdcl\<^sub>W_M_level_inv_def
          by (cases "hd (trail S)"; cases "trail S") auto
        obtain L' l' where L': "hd ?M = Marked L' l'" using marked by (cases "hd ?M") auto
        have marked_hd_tl: "get_all_levels_of_marked (hd (trail S) # tl (trail S))
          = rev [1..<1 + length (get_all_levels_of_marked ?M)]"
          using level_inv lev_L M unfolding cdcl\<^sub>W_M_level_inv_def M[symmetric]
          by blast
        then have l'_tl: "l' # get_all_levels_of_marked (tl ?M)
          = rev [1..<1 + length (get_all_levels_of_marked ?M)]" unfolding L' by simp
        moreover have "\<dots> = length (get_all_levels_of_marked ?M)
          # rev [1..<length (get_all_levels_of_marked ?M)]"
          using M Suc_le_mono calculation by (fastforce simp add: upt.simps(2))
        finally have
           l'_cons:  "l' # get_all_levels_of_marked (tl (trail S)) =
             length (get_all_levels_of_marked (trail S))
               # rev [1..<length (get_all_levels_of_marked (trail S))]" and
          "l' = ?k" and
          g_r: "get_all_levels_of_marked (tl (trail S))
            = rev [1..<length (get_all_levels_of_marked (trail S))]"
          using level_inv lev_L M unfolding cdcl\<^sub>W_M_level_inv_def by auto

        have *: "\<And>list. no_dup list \<Longrightarrow>
              - L \<in> lits_of_l list \<Longrightarrow> atm_of L \<in> atm_of ` lits_of_l list"
          by (metis atm_of_uminus imageI)
        have L'_L: "L' = -L"
          proof (rule ccontr)
            assume "\<not> ?thesis"
            moreover have "-L \<in> lits_of_l ?M" using confl LD unfolding cdcl\<^sub>W_conflicting_def by auto
            ultimately have "get_level (hd (trail S) # tl (trail S)) L = get_level (tl ?M) L"
              using cdcl\<^sub>W_M_level_inv_decomp(1)[OF level_inv] unfolding L' consistent_interp_def
              by (metis (no_types, lifting) L' M atm_of_eq_atm_of get_level_skip_beginning
                insert_iff lits_of_l_cons marked_lit.sel(1))
            moreover
              have "length (get_all_levels_of_marked (trail S)) = ?k"
                using level_inv unfolding cdcl\<^sub>W_M_level_inv_def by auto
              then have "Max (set (0#get_all_levels_of_marked (tl (trail S)))) = ?k - 1"
                unfolding g_r by (auto simp add: Max_n_upt)
              then have "get_level (tl ?M) L < ?k"
                using get_maximum_possible_level_ge_get_level[of "tl ?M" L]
                by (metis One_nat_def add.right_neutral add_Suc_right diff_add_inverse2
                  get_maximum_possible_level_max_get_all_levels_of_marked k' le_imp_less_Suc
                  list.simps(15))
            finally show False using lev_L M by auto
          qed
        have L: "hd ?M = Marked (-L) ?k"  using \<open>l' = ?k\<close> L'_L L' by auto

        have "get_maximum_level (trail S) D < ?k"
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
                then show False
                  by (metis L_k Max_n_upt One_nat_def Suc_n_not_le_n \<open>l' = backtrack_lvl S\<close>
                    add_Suc_right add_implies_diff g_r
                    get_all_levels_of_marked_rev_eq_rev_get_all_levels_of_marked list.set(2)
                    get_rev_level_less_max_get_all_levels_of_marked k' l'_cons list.sel(1)
                    rev_rev_ident semiring_normalization_rules(6) set_upt)
              qed
            then have taut: "tautology (D + {#L#})"
              using \<open>L'' \<in># D\<close> by (metis add.commute mset_leD mset_le_add_left multi_member_this
                tautology_minus)
            have "consistent_interp (lits_of_l ?M)"
              using level_inv unfolding cdcl\<^sub>W_M_level_inv_def by auto
            then have "\<not>?M \<Turnstile>as CNot ?D"
              using taut by (metis \<open>L'' = - L\<close> \<open>L'' \<in># D\<close> add.commute consistent_interp_def
                diff_union_cancelR in_CNot_implies_uminus(2) in_diffD multi_member_this)
            moreover have "?M \<Turnstile>as CNot ?D"
              using confl no_dup LD unfolding cdcl\<^sub>W_conflicting_def by auto
            ultimately show False by blast
          qed note H = this
        have "get_maximum_level (trail S) D < get_maximum_level (trail S) (D + {#L#})"
          using H by (auto simp: get_maximum_level_plus lev_L max_def)
        moreover have "backtrack_lvl S = get_maximum_level (trail S) (D + {#L#})"
          using H by (auto simp: get_maximum_level_plus lev_L max_def)
        ultimately have False
          using backtrack_no_decomp[OF raw_conf _ lev_L] level_inv termi
          cdcl\<^sub>W_then_exists_cdcl\<^sub>W_stgy_step[of S] alien unfolding E'
          by (auto simp add: lev_L max_def)
      } note not_is_marked = this

      moreover {
        let ?D = "D + {#L#}"
        have "?D \<noteq> {#}" by auto
        have "?M \<Turnstile>as CNot ?D" using confl LD unfolding cdcl\<^sub>W_conflicting_def by auto
        then have "?M \<noteq> []" unfolding true_annots_def Ball_def true_annot_def true_cls_def by force
        assume nm: "\<not>is_marked (hd ?M)"
        then obtain L' C where L'C: "hd_raw_trail S = Propagated L' C"
          by (metis \<open>trail S \<noteq> []\<close> hd_raw_trail is_marked_def mmset_of_mlit.elims)
        then have "hd ?M = Propagated L' (mset_cls C)"
          using \<open>trail S \<noteq> []\<close> hd_raw_trail mmset_of_mlit.simps(1) by fastforce
        then have M: "?M = Propagated L' (mset_cls C) # tl ?M" using \<open>?M \<noteq> []\<close>  list.collapse by fastforce
        then obtain C' where C': "mset_cls C = C' + {#L'#}"
          using confl unfolding cdcl\<^sub>W_conflicting_def by (metis append_Nil diff_single_eq_union)
        { assume "-L' \<notin># ?D"
          then have "Ex (skip S)"
            using skip_rule[OF M raw_conf] unfolding E' by auto
          then have False
            using cdcl\<^sub>W_then_exists_cdcl\<^sub>W_stgy_step[of S] alien level_inv termi
            by (auto dest: cdcl\<^sub>W_o.intros cdcl\<^sub>W_bj.intros)
        }
        moreover {
          assume L'D: "-L' \<in># ?D"
          then obtain D' where D': "?D = D' + {#-L'#}" by (metis insert_DiffM2)
          have g_r: "get_all_levels_of_marked (Propagated L' (mset_cls C) # tl (trail S))
            = rev [Suc 0..<Suc (length (get_all_levels_of_marked (trail S)))]"
            using level_inv M unfolding cdcl\<^sub>W_M_level_inv_def by auto
          have "Max (insert 0
              (set (get_all_levels_of_marked (Propagated L' (mset_cls C) # tl (trail S))))) = ?k"
            using level_inv M unfolding g_r cdcl\<^sub>W_M_level_inv_def set_rev
            by (auto simp add:Max_n_upt)
          then have "get_maximum_level (trail S) D' \<le> ?k"
            using get_maximum_possible_level_ge_get_maximum_level[of
              "Propagated L' (mset_cls C) # tl ?M"] M
            unfolding get_maximum_possible_level_max_get_all_levels_of_marked by auto
          then have "get_maximum_level (trail S) D' = ?k
            \<or> get_maximum_level (trail S) D' < ?k"
            using le_neq_implies_less by blast
          moreover {
            assume g_D'_k: "get_maximum_level (trail S) D' = ?k"
            then have f1: "get_maximum_level (trail S) D' = backtrack_lvl S"
              using M by auto
            then have "Ex (cdcl\<^sub>W_o S)"
              using f1 resolve_rule[of S L' C , OF \<open>trail S \<noteq> []\<close> _ _ raw_conf] raw_conf g_D'_k
              L'C L'D unfolding C' D' E'
              by (fastforce simp add: D' intro: cdcl\<^sub>W_o.intros cdcl\<^sub>W_bj.intros)
            then have False
              by (meson alien cdcl\<^sub>W_then_exists_cdcl\<^sub>W_stgy_step termi level_inv)
          }
          moreover {
            assume a1: "get_maximum_level (trail S) D' < ?k"
            then have f3: "get_maximum_level (trail S) D' < get_level (trail S) (-L')"
              using a1 lev_L by (metis D' get_maximum_level_ge_get_level insert_noteq_member
                not_less)
            moreover have "backtrack_lvl S = get_level (trail S) L'"
              apply (subst M)
              unfolding rev.simps
              apply (subst get_rev_level_can_skip_correctly_ordered)
              using level_inv unfolding cdcl\<^sub>W_M_level_inv_def
              apply (subst (asm) (2) M) apply (simp add: cdcl\<^sub>W_M_level_inv_decomp)
              using level_inv unfolding cdcl\<^sub>W_M_level_inv_def
              apply (subst (asm) (2) M) apply (auto simp add: cdcl\<^sub>W_M_level_inv_decomp)[]
              using level_inv unfolding cdcl\<^sub>W_M_level_inv_def
              apply (subst (asm) (4) M) apply (auto simp add: cdcl\<^sub>W_M_level_inv_decomp)[]
              using level_inv unfolding cdcl\<^sub>W_M_level_inv_def
              apply (subst (asm) (4) M) by (auto simp add: cdcl\<^sub>W_M_level_inv_decomp)[]
            moreover then have "get_level (trail S) L' = get_maximum_level (trail S) (D' + {#- L'#})"
              using a1 by (auto simp add: get_maximum_level_plus max_def)
            ultimately have False
              using M backtrack_no_decomp[of S _ "-L'", OF raw_conf]
              cdcl\<^sub>W_then_exists_cdcl\<^sub>W_stgy_step L'D level_inv termi alien
              unfolding D' E' by auto
          }
          ultimately have False by blast
        }
        ultimately have False by blast
      }
      ultimately show ?thesis by blast
    qed
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
  case (other' S' S'')
  then have "S' = S'' \<or> cdcl\<^sub>W_cp\<^sup>+\<^sup>+ S' S''"
    by (simp add: rtranclp_unfold full_def)
  then show ?case
    using other' by (meson cdcl\<^sub>W.other tranclp.r_into_trancl
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

(* TODO Move *)
lemma in_remove1_mset_neq:
  assumes ab: "a \<noteq> b"
  shows "a \<in># remove1_mset b C \<longleftrightarrow> a \<in># C"
proof -
  have "count {#b#} a = 0"
    using ab by simp
  then show ?thesis
    by (metis (no_types) count_diff diff_zero mem_Collect_eq set_mset_def)
qed

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

(* TODO Move *)
lemma get_maximum_level_union_mset:
  "get_maximum_level M (A #\<union> B) = get_maximum_level M (A + B)"
  unfolding get_maximum_level_def by (auto simp: image_Un)

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
  case (resolve L C M D T) note tr_S = this(1) and confl = this(4) and LD = this(5) and T = this(7)
  have uL_not_D: "-L \<notin># remove1_mset (-L) (mset_ccls D)"
    using n_d confl unfolding distinct_cdcl\<^sub>W_state_def distinct_mset_def
    by (metis distinct_cdcl\<^sub>W_state_def distinct_mem_diff_mset multi_member_last n_d option.simps(9))
  moreover have L_not_D: "L \<notin># remove1_mset (-L) (mset_ccls D)"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have "L \<in># mset_ccls D"
        by (auto simp: in_remove1_mset_neq)
      moreover have "Propagated L (mset_cls C) # M \<Turnstile>as CNot (mset_ccls D)"
        using conflicting confl tr_S unfolding cdcl\<^sub>W_conflicting_def by auto
      ultimately have "-L \<in> lits_of_l (Propagated L (mset_cls C) # M)"
        using in_CNot_implies_uminus(2) by blast
      moreover have "no_dup (Propagated L (mset_cls C) # M)"
        using lev tr_S unfolding cdcl\<^sub>W_M_level_inv_def by auto
      ultimately show False unfolding lits_of_def by (metis consistent_interp_def image_eqI
        list.set_intros(1) lits_of_def marked_lit.sel(2) distinct_consistent_interp)
    qed

  ultimately
    have g_D: "get_maximum_level (Propagated L (mset_cls C) # M) (remove1_mset (-L) (mset_ccls D))
      = get_maximum_level M (remove1_mset (-L) (mset_ccls D))"
    proof -
      have "\<forall>a f L. ((a::'v) \<in> f ` L) = (\<exists>l. (l::'v literal) \<in> L \<and> a = f l)"
        by blast
      then show ?thesis
        using get_maximum_level_skip_first[of L "remove1_mset (-L) (mset_ccls D)" "mset_cls C" M]
        unfolding atms_of_def
        by (metis (no_types) uL_not_D L_not_D atm_of_eq_atm_of)
    qed
  have lev_L[simp]: "get_level M L = 0"
    apply (rule atm_of_notin_get_rev_level_eq_0)
    using lev unfolding cdcl\<^sub>W_M_level_inv_def tr_S by auto

  have D: "get_maximum_level M (remove1_mset (-L) (mset_ccls D)) = backtrack_lvl S"
    using resolve.hyps(6) LD unfolding tr_S by (auto simp: get_maximum_level_plus max_def g_D)
  have "get_all_levels_of_marked M = rev [Suc 0..<Suc (backtrack_lvl S)]"
    using lev unfolding tr_S cdcl\<^sub>W_M_level_inv_def by auto
  then have "get_maximum_level M (remove1_mset L (mset_cls C)) \<le> backtrack_lvl S"
    using get_maximum_possible_level_ge_get_maximum_level[of M]
    get_maximum_possible_level_max_get_all_levels_of_marked[of M] by (auto simp: Max_n_upt)
  then have "get_maximum_level M (remove1_mset (- L) (mset_ccls D) #\<union> remove1_mset L (mset_cls C)) =
    backtrack_lvl S"
    by (auto simp: get_maximum_level_union_mset get_maximum_level_plus max_def D)
  then show ?case
    using tr_S not_empty_get_maximum_level_exists_lit[of
      "remove1_mset (- L) (mset_ccls D) #\<union> remove1_mset L (mset_cls C)" M] T
    by auto
next
  case (skip L C' M D T) note tr_S = this(1) and D = this(2) and T =this(5)
  then obtain La where "La \<in># mset_ccls D" and "get_level (Propagated L C' # M) La = backtrack_lvl S"
    using skip confl_inv by auto
  moreover
    have "atm_of La \<noteq> atm_of L"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then have La: "La = L" using \<open>La \<in># mset_ccls D\<close> \<open>- L \<notin># mset_ccls D\<close>
          by (auto simp add: atm_of_eq_atm_of)
        have "Propagated L C' # M \<Turnstile>as CNot (mset_ccls D)"
          using conflicting tr_S D unfolding cdcl\<^sub>W_conflicting_def by auto
        then have "-L \<in> lits_of_l M"
          using \<open>La \<in># mset_ccls D\<close> in_CNot_implies_uminus(2)[of L "mset_ccls D" "Propagated L C' # M"] unfolding La
          by auto
        then show False using lev tr_S unfolding cdcl\<^sub>W_M_level_inv_def consistent_interp_def by auto
      qed
    then have "get_level (Propagated L C' # M) La = get_level M La"  by auto
  ultimately show ?case using D tr_S T by auto
next
  case backtrack
  then show ?case
    by (auto split: if_split_asm simp: cdcl\<^sub>W_M_level_inv_decomp lev)
qed auto

subsubsection \<open>Strong completeness\<close>
lemma cdcl\<^sub>W_cp_propagate_confl:
  assumes "cdcl\<^sub>W_cp S T"
  shows "propagate\<^sup>*\<^sup>* S T \<or> (\<exists>S'. propagate\<^sup>*\<^sup>* S S' \<and> conflict S' T)"
  using assms by induction blast+

lemma rtranclp_cdcl\<^sub>W_cp_propagate_confl:
  assumes "cdcl\<^sub>W_cp\<^sup>*\<^sup>* S T"
  shows "propagate\<^sup>*\<^sup>* S T \<or> (\<exists>S'. propagate\<^sup>*\<^sup>* S S' \<and> conflict S' T)"
  by (simp add: assms rtranclp_cdcl\<^sub>W_cp_propa_or_propa_confl)

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
    E: "E !\<in>! raw_clauses S" and
    LE: "L \<in># mset_cls E" and
    tr: "trail S \<Turnstile>as CNot (mset_cls (remove_lit L E))" and
    undef: "undefined_lit (trail S) L" and
    T: "T \<sim> cons_trail (Propagated L E) S"
    using assms by (elim propagateE) simp
  obtain M N U k where
    S: "state S = (M, N, U, k, None)"
    using conf by auto
  show thesis
    using that[of M N U k L "remove1_mset L (mset_cls E)"] S T LE E tr undef
    by auto
qed

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
      unfolding true_clss_def raw_clauses_def by fastforce
  ultimately have "L \<in> set M" by (simp add: cons consistent_CNot_not)
  then show ?case using LM len Y Z by auto
qed

lemma
  assumes "propagate\<^sup>*\<^sup>* S X"
  shows
    rtranclp_propagate_init_clss: "init_clss X = init_clss S" and
    rtranclp_propagate_learned_clss: "learned_clss X = learned_clss S"
  using assms by (induction rule: rtranclp_induct) (auto elim: propagateE)

lemma completeness_is_a_full1_propagation:
  fixes S :: "'st" and M :: "'v literal list"
  assumes MN: "set M \<Turnstile>s set_mset N"
  and cons: "consistent_interp (set M)"
  and tot: "total_over_m (set M) (set_mset N)"
  and alien: "no_strange_atm S"
  and learned: "learned_clss S = {#}"
  and clsS[simp]: "init_clss S = N"
  and lits: "lits_of_l (trail S) \<subseteq> set M"
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
        using X by (blast dest: rtranclp_propagate_init_clss)
      have learnedX: "learned_clss X = {#}"
        using X learned by (auto dest: rtranclp_propagate_learned_clss)
      obtain E where
        E: "E \<in># init_clss X + learned_clss X" and
        Not_E: "trail X \<Turnstile>as CNot E"
        using Xconf by (auto simp add: raw_clauses_def elim!: conflictE)
      have "lits_of_l (trail X) \<subseteq> set M"
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
  by (induction rule: rtranclp_induct) (auto elim: propagateE)

lemma rtranclp_propagate_is_update_trail:
  "propagate\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W_M_level_inv S \<Longrightarrow>
    init_clss S = init_clss T \<and> learned_clss S = learned_clss T \<and> backtrack_lvl S = backtrack_lvl T
    \<and> conflicting S = conflicting T"
proof (induction rule: rtranclp_induct)
  case base
  then show ?case unfolding state_eq_def by (auto simp: cdcl\<^sub>W_M_level_inv_decomp state_append_trail_simp)
next
  case (step T U) note IH=this(3)[OF this(4)]
  moreover have "cdcl\<^sub>W_M_level_inv U"
    using rtranclp_cdcl\<^sub>W_consistent_inv \<open>propagate\<^sup>*\<^sup>* S T\<close> \<open>propagate T U\<close>
    rtranclp_mono[of propagate cdcl\<^sub>W] cdcl\<^sub>W_cp_consistent_inv propagate'
    rtranclp_propagate_is_rtranclp_cdcl\<^sub>W step.prems by blast
    then have "no_dup (trail U)" unfolding cdcl\<^sub>W_M_level_inv_def by auto
  ultimately show ?case using \<open>propagate T U\<close> unfolding state_eq_def
    by (fastforce simp: elim: propagateE)
qed

lemma lit_of_mmset_of_mlit[simp]:
  "lit_of ` mmset_of_mlit ` set M' = lits_of_l M'"
  by (induction M') auto

lemma map_mmset_of_mlit_true_annots_true_cls[simp]:
  "map mmset_of_mlit M' \<Turnstile>as C \<longleftrightarrow> M' \<Turnstile>as C"
  by (simp add: true_annots_true_cls)

lemma cdcl\<^sub>W_stgy_strong_completeness_n:
  assumes
    MN: "set M \<Turnstile>s set_mset (mset_clss N)" and
    cons: "consistent_interp (set M)" and
    tot: "total_over_m (set M) (set_mset (mset_clss N))" and
    atm_incl: "atm_of ` (set M) \<subseteq> atms_of_mm (mset_clss N)" and
    distM: "distinct M" and
    length: "n \<le> length M"
  shows
    "\<exists>M' k S. length M' \<ge> n \<and>
      lits_of_l M' \<subseteq> set M \<and>
      no_dup M' \<and>
      state S = (M', mset_clss N, {#}, k, None) \<and>
      cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) S"
  using length
proof (induction n)
  case 0
  have "state (init_state N) = ([], mset_clss N, {#}, 0, None)"
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
    S: "state S = (M', mset_clss N, {#}, k, None)" and
    st: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) S"
    by auto
  have
    M: "cdcl\<^sub>W_M_level_inv S" and
    alien: "no_strange_atm S"
      using cdcl\<^sub>W_M_level_inv_S0_cdcl\<^sub>W rtranclp_cdcl\<^sub>W_stgy_consistent_inv st apply blast
    using cdcl\<^sub>W_M_level_inv_S0_cdcl\<^sub>W no_strange_atm_S0 rtranclp_cdcl\<^sub>W_no_strange_atm_inv
    rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W st by blast

  { assume no_step: "\<not>no_step propagate S"
    obtain S' where S': "propagate\<^sup>*\<^sup>* S S'" and full: "full cdcl\<^sub>W_cp S S'"
      using completeness_is_a_full1_propagation[OF assms(1-3), of S] alien M' S
      by (auto simp: state_append_trail_simp comp_def)
    have lev: "cdcl\<^sub>W_M_level_inv S'"
      using M S' rtranclp_cdcl\<^sub>W_consistent_inv rtranclp_propagate_is_rtranclp_cdcl\<^sub>W by blast
    then have n_d'[simp]: "no_dup (trail S')"
      unfolding cdcl\<^sub>W_M_level_inv_def by auto
    have "length (trail S) \<le> length (trail S') \<and> lits_of_l (trail S') \<subseteq> set M"
      using S' full cdcl\<^sub>W_cp_propagate_completeness[OF assms(1-3), of S] M' S
      by (auto simp: state_append_trail_simp comp_def)
    moreover
      have full: "full1 cdcl\<^sub>W_cp S S'"
        using full no_step no_step_cdcl\<^sub>W_cp_no_conflict_no_propagate(2) unfolding full1_def full_def
        rtranclp_unfold by blast
      then have "cdcl\<^sub>W_stgy S S'" by (simp add: cdcl\<^sub>W_stgy.conflict')
    moreover
      have propa: "propagate\<^sup>+\<^sup>+ S S'" using S' full unfolding full1_def by (metis rtranclpD tranclpD)
      have "trail S = M'"
        using S by (auto simp: state_append_trail_simp comp_def rev_map)
      with propa have "length (trail S') > n"
        using l_M' propa by (induction rule: tranclp.induct) (auto elim: propagateE)
    moreover
      have stS': "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) S'"
        using st cdcl\<^sub>W_stgy.conflict'[OF full] by auto
      then have "init_clss S' = mset_clss N"
        using stS' rtranclp_cdcl\<^sub>W_stgy_no_more_init_clss by fastforce
    moreover
      have
        [simp]:"learned_clss S' = {#}" and
        [simp]: "init_clss S' = init_clss S" and
        [simp]: "conflicting S' = None"
        using tranclp_into_rtranclp[OF \<open>propagate\<^sup>+\<^sup>+ S S'\<close>] S
        rtranclp_propagate_is_update_trail[of S S'] S M unfolding state_eq_def
        by (auto simp: state_append_trail_simp comp_def)
      have S_S': "state S' = (trail S', mset_clss N, {#}, backtrack_lvl S', None)"
        using S by auto
      have "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) S'"
        apply (rule rtranclp.rtrancl_into_rtrancl)
         using st apply simp
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
        then show ?thesis using l_M' M' st M alien S n_d by blast
      next
        case False
        then have n': "length M' = n" using l_M' by auto
        have no_confl: "no_step conflict S"
          proof -
            { fix D
              assume "D \<in># mset_clss N" and "M' \<Turnstile>as CNot D"
              then have "set M \<Turnstile> D" using MN unfolding true_clss_def by auto
              moreover have "set M \<Turnstile>s CNot D"
                using \<open>M' \<Turnstile>as CNot D\<close> M'
                by (metis le_iff_sup true_annots_true_cls true_clss_union_increase)
              ultimately have False using cons consistent_CNot_not by blast
            }
            then show ?thesis
              using S by (auto simp: true_clss_def comp_def rev_map
                raw_clauses_def dest!: in_clss_mset_clss elim!: conflictE)
          qed
        have lenM: "length M = card (set M)" using distM by (induction M) auto
        have "no_dup M'" using S M unfolding cdcl\<^sub>W_M_level_inv_def by auto
        then have "card (lits_of_l M') = length M'"
          by (induction M') (auto simp add: lits_of_def card_insert_if)
        then have "lits_of_l M' \<subset> set M"
          using n M' n' lenM by auto
        then obtain m where m: "m \<in> set M" and undef_m: "m \<notin> lits_of_l M'" by auto
        moreover have undef: "undefined_lit M' m"
          using M' Marked_Propagated_in_iff_in_lits_of_l calculation(1,2) cons
          consistent_interp_def by (metis (no_types, lifting) subset_eq)
        moreover have "atm_of m \<in> atms_of_mm (init_clss S)"
          using atm_incl calculation S by (auto simp: state_append_trail_simp)
        ultimately
          have dec: "decide S (cons_trail (Marked m (k+1)) (incr_lvl S))"
            using decide_rule[of S _
              "cons_trail (Marked m (k + 1)) (incr_lvl S)"] S
            by auto
        let ?S' = "cons_trail (Marked m (k+1)) (incr_lvl S)"
        have "lits_of_l (trail ?S') \<subseteq> set M" using m M' S undef by (auto simp: state_append_trail_simp)
        moreover have "no_strange_atm ?S'"
          using alien dec M by (meson cdcl\<^sub>W_no_strange_atm_inv decide other)
        ultimately obtain S'' where S'': "propagate\<^sup>*\<^sup>* ?S' S''" and full: "full cdcl\<^sub>W_cp ?S' S''"
          using completeness_is_a_full1_propagation[OF assms(1-3), of ?S'] S undef
          by (auto simp: state_append_trail_simp)
        have "cdcl\<^sub>W_M_level_inv ?S'"
          using M dec rtranclp_mono[of decide cdcl\<^sub>W] by (meson cdcl\<^sub>W_consistent_inv decide other)
        then have lev'': "cdcl\<^sub>W_M_level_inv S''"
          using S'' rtranclp_cdcl\<^sub>W_consistent_inv rtranclp_propagate_is_rtranclp_cdcl\<^sub>W by blast
        then have n_d'': "no_dup (trail S'')"
          unfolding cdcl\<^sub>W_M_level_inv_def by auto
        have "length (trail ?S') \<le> length (trail S'') \<and> lits_of_l (trail S'') \<subseteq> set M"
          using S'' full cdcl\<^sub>W_cp_propagate_completeness[OF assms(1-3), of ?S' S''] m M' S undef
          by (simp add: state_append_trail_simp)
        then have "Suc n \<le> length (trail S'') \<and> lits_of_l (trail S'') \<subseteq> set M"
          using l_M' S undef by (auto simp: state_append_trail_simp)
        moreover
          have "cdcl\<^sub>W_M_level_inv (cons_trail (Marked m (Suc (backtrack_lvl S)))
            (update_backtrack_lvl (Suc (backtrack_lvl S)) S))"
            using S \<open>cdcl\<^sub>W_M_level_inv (cons_trail (Marked m (k + 1)) (incr_lvl S))\<close> by auto
          then have S'':
            "state S'' = (trail S'', mset_clss N, {#}, backtrack_lvl S'', None)"
            using rtranclp_propagate_is_update_trail[OF S''] S undef n_d'' lev''
            by auto
          then have "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) S''"
            using cdcl\<^sub>W_stgy.intros(2)[OF decide[OF dec] _ full] no_step no_confl st
            by (auto simp: cdcl\<^sub>W_cp.simps)
        ultimately show ?thesis using S'' n_d'' by blast
      qed
  }
  ultimately show ?case by blast
qed

lemma cdcl\<^sub>W_stgy_strong_completeness:
  assumes
    MN: "set M \<Turnstile>s set_mset (mset_clss N)" and
    cons: "consistent_interp (set M)" and
    tot: "total_over_m (set M) (set_mset (mset_clss N))" and
    atm_incl: "atm_of ` (set M) \<subseteq> atms_of_mm (mset_clss N)" and
    distM: "distinct M"
  shows
    "\<exists>M' k S.
      lits_of_l M' = set M \<and>
      state S = (M', mset_clss N, {#}, k, None) \<and>
      cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) S \<and>
      final_cdcl\<^sub>W_state S"
proof -
  from cdcl\<^sub>W_stgy_strong_completeness_n[OF assms, of "length M"]
  obtain M' k T where
    l: "length M \<le> length M'" and
    M'_M: "lits_of_l M' \<subseteq> set M" and
    no_dup: "no_dup M'" and
    T: "state T = (M', mset_clss N, {#}, k, None)" and
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
    using M'_M  card_seteq by blast
  moreover
    then have "M' \<Turnstile>asm mset_clss N"
      using MN unfolding true_annots_def Ball_def true_annot_def true_clss_def by auto
    then have "final_cdcl\<^sub>W_state T"
      using T no_dup unfolding final_cdcl\<^sub>W_state_def by (auto simp: state_append_trail_simp)
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
  case (backtrack K i M1 M2 L D T) note confl = this(1) and LD = this(2) and decomp = this(3) and
    undef = this(7) and T =this(8)
  obtain c where M: "trail S = c @ M2 @ Marked K (i+1) # M1"
    using decomp by auto

  show ?case
    proof (intro allI impI)
      fix M ia K' M' Da

      assume "M' @ Marked K' ia # M = trail T"
      then have "tl M' @ Marked K' ia # M = M1"
        using T decomp undef lev by (cases M') (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
      let ?S' = "(cons_trail (Propagated L (cls_of_ccls D))
                  (reduce_trail_to M1 (add_learned_cls (cls_of_ccls D)
                  (update_backtrack_lvl i (update_conflicting None S)))))"
      assume D: "Da \<in># clauses T"
      moreover{
        assume "Da \<in># clauses S"
        then have "\<not>M \<Turnstile>as CNot Da" using \<open>tl M' @ Marked K' ia # M = M1\<close> M confl undef smaller
          unfolding no_smaller_confl_def by auto
      }
      moreover {
        assume Da: "Da = mset_ccls D"
        have "\<not>M \<Turnstile>as CNot Da"
          proof (rule ccontr)
            assume "\<not> ?thesis"
            then have "-L \<in> lits_of_l M"
              using LD unfolding Da by (simp add: in_CNot_implies_uminus(2))
            then have "-L \<in> lits_of_l (Propagated L (mset_ccls D) # M1)"
              using UnI2 \<open>tl M' @ Marked K' ia # M = M1\<close>
              by auto
            moreover
              have "backtrack S ?S'"
                using backtrack_rule[of S] backtrack.hyps
                by (force simp: state_eq_def simp del: state_simp)
              then have "cdcl\<^sub>W_M_level_inv ?S'"
                using cdcl\<^sub>W_consistent_inv[OF _ lev] other[OF bj] by (auto intro: cdcl\<^sub>W_bj.intros)
              then have "no_dup (Propagated L (mset_ccls D) # M1)"
                using decomp undef lev unfolding cdcl\<^sub>W_M_level_inv_def by auto
            ultimately show False by (metis consistent_interp_def distinct_consistent_interp
              insertCI lits_of_l_cons marked_lit.sel(2))
          qed
      }
      ultimately show "\<not>M \<Turnstile>as CNot Da"
        using T undef decomp lev unfolding cdcl\<^sub>W_M_level_inv_def by fastforce
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
  fix M' K i M'' D
  assume M': "M'' @ Marked K i # M' = trail S'"
  and "D \<in># clauses S'"
  obtain M N U k C L where
    S: "state S = (M, N, U, k, None)" and
    S': "state S' = (Propagated L ( (C + {#L#})) # M, N, U, k, None)" and
    "C + {#L#} \<in># clauses S" and
    "M \<Turnstile>as CNot C" and
    "undefined_lit M L"
    using propagate by (auto elim: propagate_high_levelE)
  have "tl M'' @ Marked K i # M' = trail S" using M' S S'
    by (metis Pair_inject list.inject list.sel(3) marked_lit.distinct(1) self_append_conv2
      tl_append2)
  then have "\<not>M' \<Turnstile>as CNot D "
    using \<open>D \<in># clauses S'\<close> n_l S S' raw_clauses_def unfolding no_smaller_confl_def by auto
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
proof (induct rule: rtranclp_induct)
  case base
  then show ?case by simp
next
  case (step S' S'')
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
  case (conflict' S')
  then show ?case using full1_cdcl\<^sub>W_cp_no_smaller_confl_inv[of S S'] by blast
next
  case (other' S' S'')
  have "no_smaller_confl S'"
    using cdcl\<^sub>W_o_no_smaller_confl_inv[OF other'.hyps(1) other'.prems(3,2,1)]
    not_conflict_not_any_negated_init_clss other'.hyps(2) cdcl\<^sub>W_cp.simps by auto
  then show ?case using full_cdcl\<^sub>W_cp_no_smaller_confl_inv[of S' S''] other'.hyps by blast
qed

lemma is_conflicting_exists_conflict:
  assumes "\<not>(\<forall>D\<in>#init_clss S' + learned_clss S'. \<not> trail S' \<Turnstile>as CNot D)"
  and "conflicting S' = None"
  shows "\<exists>S''. conflict S' S''"
  using assms raw_clauses_def not_conflict_not_any_negated_init_clss by fastforce

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
              obtain L'' where "L'' \<in># x" and "lits_of_l (Marked L (?k + 1) # ?M) \<Turnstile>l L''"
                using M_D x T undef unfolding true_annots_def Ball_def true_annot_def CNot_def
                true_cls_def Bex_def by auto
              show "\<exists>L \<in># x. lits_of_l ?M \<Turnstile>l L" unfolding Bex_def
                using L'(1) L'(2) \<open>- L \<notin># D\<close> \<open>L'' \<in># x\<close>
                \<open>lits_of_l (Marked L (backtrack_lvl S + 1) # trail S) \<Turnstile>l L''\<close> by auto
            qed
          then show False using \<open>\<not> ?M \<Turnstile>as CNot D\<close> by auto
        qed
      have "atm_of L \<notin> atm_of ` (lits_of_l ?M)"
        using undef defined_lit_map unfolding lits_of_def by fastforce
      then have "get_level (Marked L (?k + 1) # ?M) (-L) = ?k + 1" by simp
      then show "\<exists>La. La \<in># D \<and> get_level ?M' La = backtrack_lvl T"
        using \<open>-L \<in># D\<close> T undef by auto
    qed
next
  case resolve
  then show ?case by auto
next
  case skip
  then show ?case by auto
next
  case (backtrack K i M1 M2 L D T) note decomp = this(3) and undef = this(7) and T =this(8)
  show ?case
    proof (rule HOL.disjI2, clarify)
      fix Da
      assume Da: "Da \<in># clauses T"
      and M_D: "trail T \<Turnstile>as CNot Da"
      obtain c where M: "trail S = c @ M2 @ Marked K (i + 1) # M1"
        using decomp by auto
      have tr_T: "trail T = Propagated L (mset_ccls D) # M1"
        using T decomp undef lev by (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
      have "backtrack S T"
        using backtrack_rule[of S] backtrack.hyps T
        by (force simp del: state_simp simp: state_eq_def)
      then have lev': "cdcl\<^sub>W_M_level_inv T"
        using cdcl\<^sub>W_consistent_inv lev other cdcl\<^sub>W_bj.backtrack cdcl\<^sub>W_o.bj by blast
      then have "- L \<notin> lits_of_l M1"
        using lev cdcl\<^sub>W_M_level_inv_def Marked_Propagated_in_iff_in_lits_of_l undef by blast
      { assume "Da \<in># clauses S"
        then have "\<not>M1 \<Turnstile>as CNot Da" using no_l M unfolding no_smaller_confl_def by auto
      }
      moreover {
        assume Da: "Da = mset_ccls D"
        have "\<not>M1 \<Turnstile>as CNot Da" using \<open>- L \<notin> lits_of_l M1\<close> unfolding Da
          using backtrack.hyps(2) in_CNot_implies_uminus(2) by auto
      }
      ultimately have "\<not>M1 \<Turnstile>as CNot Da"
        using Da T undef decomp lev by (fastforce simp: cdcl\<^sub>W_M_level_inv_decomp)
      then have "-L \<in># Da"
        using M_D \<open>- L \<notin> lits_of_l M1\<close> in_CNot_implies_uminus(2)
           true_annots_CNot_lit_of_notin_skip T unfolding tr_T
        by (smt insert_iff lits_of_l_cons marked_lit.sel(2))
      have g_M1: "get_all_levels_of_marked M1 = rev [1..<i+1]"
        using lev lev' T decomp undef unfolding cdcl\<^sub>W_M_level_inv_def by auto
      have "no_dup (Propagated L (mset_ccls D) # M1)"
        using lev lev' T decomp undef unfolding cdcl\<^sub>W_M_level_inv_def by auto
      then have L: "atm_of L \<notin> atm_of ` lits_of_l M1" unfolding lits_of_def by auto
      have "get_level (Propagated L (mset_ccls D) # M1) (-L) = i"
        using get_level_get_rev_level_get_all_levels_of_marked[OF L,
          of "[Propagated L (mset_ccls D)]"]
        by (simp add: g_M1 split: if_splits)
      then show "\<exists>La. La \<in># Da \<and> get_level (trail T) La = backtrack_lvl T"
        using \<open>-L \<in># Da\<close> T decomp undef lev by (auto simp: cdcl\<^sub>W_M_level_inv_def)
    qed
qed

lemma full1_cdcl\<^sub>W_cp_exists_conflict_decompose:
  assumes
    confl: "\<exists>D\<in>#clauses S. trail S \<Turnstile>as CNot D" and
    full: "full cdcl\<^sub>W_cp S U" and
    no_confl: "conflicting S = None" and
    lev: "cdcl\<^sub>W_M_level_inv S"
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
      then have "conflicting U = None" and
        [simp]: "learned_clss U = learned_clss S" and
        [simp]: "init_clss U = init_clss S"
        using no_confl rtranclp_propagate_is_update_trail lev by auto
      moreover
        obtain D where D: "D\<in>#clauses U" and
          trS: "trail S \<Turnstile>as CNot D"
          using confl raw_clauses_def by auto
        obtain M where M: "trail U = M @ trail S"
          using full rtranclp_cdcl\<^sub>W_cp_dropWhile_trail unfolding full_def by meson
        have tr_U: "trail U \<Turnstile>as CNot D"
          apply (rule true_annots_mono)
          using trS unfolding M by simp_all
      have "\<exists>V. conflict U V"
        using \<open>conflicting U = None\<close> D raw_clauses_def not_conflict_not_any_negated_init_clss tr_U
        by meson
      then have False using full cdcl\<^sub>W_cp.conflict' unfolding full_def by blast
      then show ?thesis by fast
    qed
qed

lemma full1_cdcl\<^sub>W_cp_exists_conflict_full1_decompose:
  assumes
    confl: "\<exists>D\<in>#clauses S. trail S \<Turnstile>as CNot D" and
    full: "full cdcl\<^sub>W_cp S U" and
    no_confl: "conflicting S = None"and
    lev: "cdcl\<^sub>W_M_level_inv S"
  shows "\<exists>T D. propagate\<^sup>*\<^sup>* S T \<and> conflict T U
    \<and> trail T \<Turnstile>as CNot D \<and> conflicting U = Some D \<and> D \<in># clauses S"
proof -
  obtain T where propa: "propagate\<^sup>*\<^sup>* S T" and conf: "conflict T U"
    using full1_cdcl\<^sub>W_cp_exists_conflict_decompose[OF assms] by blast
  have p: "learned_clss T = learned_clss S" "init_clss T = init_clss S"
     using propa lev rtranclp_propagate_is_update_trail by auto
  have c: "learned_clss U = learned_clss T" "init_clss U = init_clss T"
     using conf by (auto elim: conflictE)
  obtain D where "trail T \<Turnstile>as CNot D \<and> conflicting U = Some D \<and> D \<in># clauses S"
    using conf p c by (fastforce simp: raw_clauses_def elim!: conflictE)
  then show ?thesis
    using propa conf by blast
qed

lemma cdcl\<^sub>W_stgy_no_smaller_confl:
  assumes
    "cdcl\<^sub>W_stgy S S'" and
    n_l: "no_smaller_confl S" and
    "conflict_is_false_with_level S" and
    "cdcl\<^sub>W_M_level_inv S" and
    "no_clause_is_false S" and
    "distinct_cdcl\<^sub>W_state S" and
    "cdcl\<^sub>W_conflicting S"
  shows "no_smaller_confl S'"
  using assms
proof (induct rule: cdcl\<^sub>W_stgy.induct)
  case (conflict' S')
  show "no_smaller_confl S'"
    using conflict'.hyps conflict'.prems(1) full1_cdcl\<^sub>W_cp_no_smaller_confl_inv by blast
next
  case (other' S' S'')
  have lev': "cdcl\<^sub>W_M_level_inv S'"
    using cdcl\<^sub>W_consistent_inv other other'.hyps(1) other'.prems(3) by blast
  show "no_smaller_confl S''"
    using cdcl\<^sub>W_stgy_no_smaller_confl_inv[OF cdcl\<^sub>W_stgy.other'[OF other'.hyps(1-3)]]
    other'.prems(1-3) by blast
qed

lemma cdcl\<^sub>W_stgy_ex_lit_of_max_level:
  assumes
    "cdcl\<^sub>W_stgy S S'" and
    n_l: "no_smaller_confl S" and
    "conflict_is_false_with_level S" and
    "cdcl\<^sub>W_M_level_inv S" and
    "no_clause_is_false S" and
    "distinct_cdcl\<^sub>W_state S" and
    "cdcl\<^sub>W_conflicting S"
  shows "conflict_is_false_with_level S'"
  using assms
proof (induct rule: cdcl\<^sub>W_stgy.induct)
  case (conflict' S')
  have "no_smaller_confl S'"
    using conflict'.hyps conflict'.prems(1) full1_cdcl\<^sub>W_cp_no_smaller_confl_inv by blast
  moreover have "conflict_is_false_with_level S'"
    using conflict'.hyps conflict'.prems(2-4)
    rtranclp_cdcl\<^sub>W_co_conflict_ex_lit_of_max_level[of S S']
    unfolding full_def full1_def rtranclp_unfold by presburger
  then show ?case by blast
next
  case (other' S' S'')
  have lev': "cdcl\<^sub>W_M_level_inv S'"
    using cdcl\<^sub>W_consistent_inv other other'.hyps(1) other'.prems(3) by blast
  moreover
    have "no_clause_is_false S'
      \<or> (conflicting S' = None \<longrightarrow> (\<forall>D\<in>#clauses S'. trail S' \<Turnstile>as CNot D
          \<longrightarrow> (\<exists>L. L \<in># D \<and> get_level (trail S') L = backtrack_lvl S')))"
      using cdcl\<^sub>W_o_conflict_is_no_clause_is_false[of S S'] other'.hyps(1) other'.prems(1-4) by fast
  moreover {
    assume "no_clause_is_false S'"
    {
      assume "conflicting S' = None"
      then have "conflict_is_false_with_level S'" by auto
      moreover have "full cdcl\<^sub>W_cp S' S''"
        by (metis (no_types) other'.hyps(3))
      ultimately have "conflict_is_false_with_level S''"
        using rtranclp_cdcl\<^sub>W_co_conflict_ex_lit_of_max_level[of S' S''] lev' \<open>no_clause_is_false S'\<close>
        by blast
    }
    moreover
    {
      assume c: "conflicting S' \<noteq> None"
      have "conflicting S \<noteq> None" using other'.hyps(1) c
        by (induct rule: cdcl\<^sub>W_o_induct) auto
      then have "conflict_is_false_with_level S'"
        using cdcl\<^sub>W_o_conflict_is_false_with_level_inv[OF other'.hyps(1)]
        other'.prems(3,5,6,2) by blast
      moreover have "cdcl\<^sub>W_cp\<^sup>*\<^sup>* S' S''" using other'.hyps(3) unfolding full_def by auto
      then have "S' = S''" using c
        by (induct rule: rtranclp_induct)
           (fastforce intro: option.exhaust)+
      ultimately have "conflict_is_false_with_level S''" by auto
    }
    ultimately have "conflict_is_false_with_level S''" by blast
  }
  moreover {
     assume
       confl: "conflicting S' = None" and
       D_L: "\<forall>D \<in># clauses S'. trail S' \<Turnstile>as CNot D
         \<longrightarrow> (\<exists>L. L \<in># D \<and> get_level (trail S') L = backtrack_lvl S')"
     { assume "\<forall>D\<in>#clauses S'. \<not> trail S' \<Turnstile>as CNot D"
       then have "no_clause_is_false S'" using confl by simp
       then have "conflict_is_false_with_level S''" using calculation(3) by presburger
     }
     moreover {
       assume "\<not>(\<forall>D\<in>#clauses S'. \<not> trail S' \<Turnstile>as CNot D)"
       then obtain T D where
         "propagate\<^sup>*\<^sup>* S' T" and
         "conflict T S''" and
         D: "D \<in># clauses S'" and
         "trail S'' \<Turnstile>as CNot D" and
         "conflicting S'' = Some D"
         using full1_cdcl\<^sub>W_cp_exists_conflict_full1_decompose[OF _ _  confl]
         other'(3) lev' by (metis (mono_tags, lifting) conflictE state_eq_trail
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
           moreover then obtain L where
             "L \<in># D" and
             lev_L: "get_level (trail S') L = backtrack_lvl S'"
             using D_L D by blast
           moreover
             have LS': "-L \<in> lits_of_l (trail S')"
               using \<open>trail S' \<Turnstile>as CNot D\<close> \<open>L \<in># D\<close> in_CNot_implies_uminus(2) by blast
             {  fix x :: "('v, nat, 'v clause) marked_lit" and
                 xb :: "('v, nat, 'v clause) marked_lit"
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
             then have "atm_of L \<notin> atm_of ` lits_of_l M"
               using nd LS' unfolding M by (auto simp add: lits_of_def)
             then have "get_level (trail S'') L = get_level (trail S') L"
               unfolding M by (simp add: lits_of_def)
           ultimately show ?thesis using btS \<open>conflicting S'' = Some D\<close> by auto
         next
           assume "\<not>trail S' \<Turnstile>as CNot D"
           then obtain L where "L \<in># D" and LM: "-L \<in> lits_of_l M"
             using \<open>trail S'' \<Turnstile>as CNot D\<close> unfolding M
               by (auto simp add:  true_cls_def  M true_annots_def true_annot_def
                     split: if_split_asm)
           { fix x :: "('v, nat, 'v clause) marked_lit" and
               xb :: "('v, nat, 'v clause) marked_lit"
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
           then have LS': "atm_of L \<notin> atm_of ` lits_of_l (trail S')"
             using nd \<open>L \<in># D\<close> LM unfolding M by (auto simp add: lits_of_def)
           show ?thesis
             proof cases
               assume ne: "get_all_levels_of_marked (trail S') = []"
               have "backtrack_lvl S'' = 0"
                 using inv ne nm unfolding cdcl\<^sub>W_M_level_inv_def M
                 by (simp add: get_all_levels_of_marked_nil_iff_not_is_marked)
               moreover
                 have a1: "get_level M L = 0"
                   using nm by auto
                 then have "get_level (M @ trail S') L = 0"
                   by (metis LS' get_all_levels_of_marked_nil_iff_not_is_marked
                     get_level_skip_beginning_not_marked lits_of_def ne)
               ultimately show ?thesis using \<open>conflicting S'' = Some D\<close> \<open>L \<in># D\<close> unfolding M
                 by auto
             next
               assume ne: "get_all_levels_of_marked (trail S') \<noteq> []"
               have "hd (get_all_levels_of_marked (trail S')) = backtrack_lvl S'"
                 using ne lev' M nm unfolding cdcl\<^sub>W_M_level_inv_def
                 by (cases "get_all_levels_of_marked (trail S')")
                 (simp_all add: get_all_levels_of_marked_nil_iff_not_is_marked[symmetric])
               moreover have "atm_of L \<in> atm_of ` lits_of_l M "
                  using \<open>-L \<in> lits_of_l M\<close>
                  by (simp add: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set lits_of_def)
               ultimately show ?thesis
                 using nm ne \<open>L\<in>#D\<close> \<open>conflicting S'' = Some D\<close>
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
    assume "conflicting S' \<noteq> None"
    have "no_clause_is_false S'" using \<open>conflicting S' \<noteq> None\<close>  by auto
    then have "conflict_is_false_with_level S''" using calculation(3) by presburger
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
    using  st lev rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W
    by (blast intro: rtranclp_cdcl\<^sub>W_consistent_inv)+
  moreover have "no_clause_is_false S'"
    using st no_f rtranclp_cdcl\<^sub>W_stgy_not_non_negated_init_clss by presburger
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
  and no_d: "distinct_mset_mset (mset_clss N)"
  and no_empty: "\<forall>D\<in>#mset_clss N. D \<noteq> {#}"
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
    decomp: "all_decomposition_implies_m (init_clss S') (get_all_marked_decomposition (trail S'))"
    using no_d tranclp_cdcl\<^sub>W_stgy_tranclp_cdcl\<^sub>W[of ?S S'] step rtranclp_cdcl\<^sub>W_all_inv(1-6)[of ?S S']
    unfolding rtranclp_unfold by auto
  moreover
    have "\<forall>D\<in>#mset_clss N. \<not> [] \<Turnstile>as CNot D" using no_empty by auto
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

lemma full_cdcl\<^sub>W_init_clss_with_false_normal_form:
  assumes
    "\<forall> m\<in> set M. \<not>is_marked m" and
    "E = Some D" and
    "state S = (M, N, U, 0, E)"
    "full cdcl\<^sub>W_stgy S S'" and
    "all_decomposition_implies_m (init_clss S) (get_all_marked_decomposition (trail S))"
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
  then have MpK: "M \<Turnstile>as CNot ( p - {#K#})" and Kp: "K \<in>#  p"
    using S unfolding K by fastforce+
  then have p: "p = (p - {#K#}) + {#K#}"
    by (auto simp add: multiset_eq_iff)
  then have K': "L = Propagated K ((p - {#K#}) + {#K#})"
    using K by auto
  obtain p' where
    p': "hd_raw_trail S = Propagated K p'" and
    pp': "mset_cls p' = p"
    using hd_raw_trail[of S] S K by (cases "hd_raw_trail S") auto
  obtain raw_D where
    raw_D: "raw_conflicting S = Some raw_D"
    using S E by (cases "raw_conflicting S") auto
  then have raw_DD: "mset_ccls raw_D = D"
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
            using \<open>-lit_of L \<notin># D\<close> S D' K hd_raw_trail[of S] unfolding E
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
            using  LD get_maximum_level_exists_lit_of_max_level
            proof -
              obtain L' where "get_level (L#M) L' = get_maximum_level (L#M) D"
                using  LD get_maximum_level_exists_lit_of_max_level[of D "L#M"] by fastforce
              then show ?thesis by (metis (mono_tags) K' get_level_skip_all_not_marked
                get_maximum_level_exists_lit nm not_gr0)
            qed
          then obtain T where sk: "resolve S T"
            using resolve_rule[of S K p' raw_D] S p' \<open>K \<in># p\<close> raw_D LD
            unfolding K' D E  pp' raw_DD by auto
          then have res: "no_step skip S"
            using LD S D' K hd_raw_trail[of S] unfolding E
            by (auto elim!: skipE resolveE)
          have "full cdcl\<^sub>W_cp T T"
            using sk by (auto simp: option_full_cdcl\<^sub>W_cp elim: resolveE)
          then show ?thesis
           using sk res by blast
        qed
      then have step_s: "\<exists>T. cdcl\<^sub>W_stgy S T"
        using \<open>no_step cdcl\<^sub>W_cp S\<close> other' by (meson bj resolve skip)
      have "get_all_marked_decomposition (L # M) = [([], L#M)]"
        using nm unfolding K apply (induction M rule: marked_lit_list_induct, simp)
          by (rename_tac L l xs, case_tac "hd (get_all_marked_decomposition xs)", auto)+
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
        using s no_b no_d res_skip full_S_S  cdcl\<^sub>W_cp_state_eq_compatible resolve_unique
        skip_unique unfolding cdcl\<^sub>W_stgy.simps cdcl\<^sub>W_o.simps full_unfold
        full1_def by (blast dest!: tranclpD elim!: cdcl\<^sub>W_bj.cases)+
      then obtain D' where T: "state T = (M, N, U, 0, Some D')"
        using S E by (auto elim!: skipE resolveE simp: state_eq_def simp del: state_simp)

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
  and no_d: "distinct_mset_mset (mset_clss N)"
  and empty: "{#} \<in># (mset_clss N)"
  shows "conflicting S' = Some {#} \<and> unsatisfiable (set_mset (init_clss S'))"
proof -
  let ?S = "init_state N"
  have "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ?S S'" and "no_step cdcl\<^sub>W_stgy S'" using full unfolding full_def by auto
  then have plus_or_eq: "cdcl\<^sub>W_stgy\<^sup>+\<^sup>+ ?S S' \<or> S' = ?S" unfolding rtranclp_unfold by auto
  have "\<exists>S''. conflict ?S S''"
    using empty not_conflict_not_any_negated_init_clss[of "init_state N"] by auto


  then have cdcl\<^sub>W_stgy: "\<exists>S'. cdcl\<^sub>W_stgy ?S S'"
    using cdcl\<^sub>W_cp.conflict'[of ?S] conflict_is_full1_cdcl\<^sub>W_cp cdcl\<^sub>W_stgy.intros(1) by metis
  have "S' \<noteq> ?S"  using \<open>no_step cdcl\<^sub>W_stgy S'\<close> cdcl\<^sub>W_stgy by blast

  then obtain St:: 'st where St: "cdcl\<^sub>W_stgy ?S St" and "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* St S'"
    using plus_or_eq by (metis (no_types) \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ?S S'\<close> converse_rtranclpE)
  have st: "cdcl\<^sub>W\<^sup>*\<^sup>* ?S St"
    by (simp add: rtranclp_unfold \<open>cdcl\<^sub>W_stgy ?S St\<close> cdcl\<^sub>W_stgy_tranclp_cdcl\<^sub>W)

  have "\<exists>T. conflict ?S T"
    using empty not_conflict_not_any_negated_init_clss[of "?S"] by force
  then have fullSt: "full1 cdcl\<^sub>W_cp ?S St"
    using St unfolding cdcl\<^sub>W_stgy.simps by blast
  then have bt: "backtrack_lvl St = (0::nat)"
    using rtranclp_cdcl\<^sub>W_cp_backtrack_lvl unfolding full1_def
    by (fastforce dest!: tranclp_into_rtranclp)
  have cls_St: "init_clss St = mset_clss N"
    using fullSt  cdcl\<^sub>W_stgy_no_more_init_clss[OF St] by auto
  have "conflicting St \<noteq> None"
    proof (rule ccontr)
      assume conf: "\<not> ?thesis"
      obtain E where
        ES: "E !\<in>! raw_init_clss St" and
        E: "mset_cls E = {#}"
        using empty cls_St by (metis in_mset_clss_exists_preimage)
      then have "\<exists>T. conflict St T"
        using empty cls_St conflict_rule[of St E] ES conf unfolding E
        by (auto simp: raw_clauses_def dest: in_mset_clss_exists_preimage)
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
  have "init_clss S' = init_clss St" and "conflicting S' = Some {#}"
     using \<open>conflicting St \<noteq> None\<close> full_cdcl\<^sub>W_init_clss_with_false_normal_form[OF 1, of _ _ St]
     2 3 4 5 6 7 8 St apply (metis \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* St S'\<close> rtranclp_cdcl\<^sub>W_stgy_no_more_init_clss)
    using \<open>conflicting St \<noteq> None\<close> full_cdcl\<^sub>W_init_clss_with_false_normal_form[OF 1, of _ _ St _ _
      S'] 2 3 4 5 6 7 8 by (metis bt option.exhaust prod.inject)

  moreover have "init_clss S' = mset_clss N"
    using \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) S'\<close> rtranclp_cdcl\<^sub>W_stgy_no_more_init_clss by fastforce
  moreover have "unsatisfiable (set_mset (mset_clss N))"
    by (meson empty satisfiable_def true_cls_empty true_clss_def)
  ultimately show ?thesis by auto
qed

(** prop 2.10.9 \cwref{lem:prop:cddlsoundtermStates}{}*)
lemma full_cdcl\<^sub>W_stgy_final_state_conclusive:
  fixes S' :: 'st
  assumes full: "full cdcl\<^sub>W_stgy (init_state N) S'" and no_d: "distinct_mset_mset (mset_clss N)"
  shows "(conflicting S' = Some {#} \<and> unsatisfiable (set_mset (init_clss S')))
    \<or> (conflicting S' = None \<and> trail S' \<Turnstile>asm init_clss S')"
  using assms full_cdcl\<^sub>W_stgy_final_state_conclusive_is_one_false
  full_cdcl\<^sub>W_stgy_final_state_conclusive_non_false by blast

lemma full_cdcl\<^sub>W_stgy_final_state_conclusive_from_init_state:
  fixes S' :: "'st"
  assumes full: "full cdcl\<^sub>W_stgy (init_state N) S'"
  and no_d: "distinct_mset_mset (mset_clss N)"
  shows "(conflicting S' = Some {#} \<and> unsatisfiable (set_mset (mset_clss N)))
    \<or> (conflicting S' = None \<and> trail S' \<Turnstile>asm (mset_clss N) \<and> satisfiable (set_mset (mset_clss N)))"
proof -
  have N: "init_clss S' = (mset_clss N)"
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
      then have "consistent_interp (lits_of_l (trail S'))" unfolding cdcl\<^sub>W_M_level_inv_def by blast
      moreover have "lits_of_l (trail S') \<Turnstile>s set_mset (init_clss S')"
        using sat(2) by (auto simp add: true_annots_def true_annot_def true_clss_def)
      ultimately have "satisfiable (set_mset (init_clss S'))" by simp
      then show ?thesis using sat unfolding N by blast
    qed
qed
end
end
