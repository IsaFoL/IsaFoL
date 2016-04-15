theory CDCL_W_Abstract_State
imports CDCL_Abstract_Clause_Representation List_More CDCL_W_Level Wellfounded_More
  CDCL_WNOT

begin

section \<open>Weidenbach's CDCL with Abstract Clause Representation\<close>
declare upt.simps(2)[simp del]

subsubsection \<open>Instantiation of the Multiset Version\<close>

type_synonym 'v cdcl\<^sub>W_mset = "('v, 'v clause) ann_lit list \<times>
  'v clauses \<times>
  'v clauses \<times>
  nat \<times> 'v clause option"

definition trail :: "'v cdcl\<^sub>W_mset \<Rightarrow> ('v, 'v clause) ann_lit list" where
"trail \<equiv> \<lambda>(M, _). M"

definition init_clss :: "'v cdcl\<^sub>W_mset \<Rightarrow> 'v clauses" where
"init_clss \<equiv> \<lambda>(_, N, _). N"

definition learned_clss :: "'v cdcl\<^sub>W_mset \<Rightarrow> 'v clauses" where
"learned_clss \<equiv> \<lambda>(_, _, U, _). U"

definition backtrack_lvl :: "'v cdcl\<^sub>W_mset \<Rightarrow> nat" where
"backtrack_lvl \<equiv> \<lambda>(_, _, _, k, _). k"

definition conflicting :: "'v cdcl\<^sub>W_mset \<Rightarrow> 'v clause option" where
"conflicting \<equiv> \<lambda>(_, _, _, _, C). C"

definition cons_trail :: "('v, 'v clause) ann_lit \<Rightarrow> 'v cdcl\<^sub>W_mset \<Rightarrow> 'v cdcl\<^sub>W_mset" where
"cons_trail \<equiv> \<lambda>L (M, R). (L # M, R)"


definition tl_trail where
"tl_trail \<equiv> \<lambda>(M, R). (tl M, R)"

definition add_learned_cls where
"add_learned_cls \<equiv> \<lambda>C (M, N, U, R). (M, N, {#C#} + U, R)"

definition remove_cls where
"remove_cls \<equiv> \<lambda>C (M, N, U, R). (M, removeAll_mset C N, removeAll_mset C U, R)"

definition update_backtrack_lvl where
"update_backtrack_lvl \<equiv> \<lambda>k (M, N, U, _, D). (M, N, U, k, D)"

definition update_conflicting where
"update_conflicting \<equiv> \<lambda>D (M, N, U, k, _). (M, N, U, k, D)"

definition init_state where
"init_state \<equiv> \<lambda>N. ([], N, {#}, 0, None)"

definition restart_state where
"restart_state \<equiv> \<lambda>(_, N, U, _, _). ([], N, U, 0, None)"

lemmas cdcl\<^sub>W_mset_state = trail_def cons_trail_def tl_trail_def add_learned_cls_def
    remove_cls_def update_backtrack_lvl_def update_conflicting_def init_clss_def learned_clss_def
    backtrack_lvl_def conflicting_def init_state_def restart_state_def

interpretation cdcl\<^sub>W_mset: state\<^sub>W_ops where
  trail = trail and
  init_clss = init_clss and
  learned_clss = learned_clss and
  backtrack_lvl = backtrack_lvl and
  conflicting = conflicting and

  cons_trail = cons_trail and
  tl_trail = tl_trail and
  add_learned_cls = add_learned_cls and
  remove_cls = remove_cls and
  update_backtrack_lvl = update_backtrack_lvl and
  update_conflicting = update_conflicting and
  init_state = init_state and
  restart_state = restart_state
  .

interpretation cdcl\<^sub>W_mset: state\<^sub>W where
  trail = trail and
  init_clss = init_clss and
  learned_clss = learned_clss and
  backtrack_lvl = backtrack_lvl and
  conflicting = conflicting and

  cons_trail = cons_trail and
  tl_trail = tl_trail and
  add_learned_cls = add_learned_cls and
  remove_cls = remove_cls and
  update_backtrack_lvl = update_backtrack_lvl and
  update_conflicting = update_conflicting and
  init_state = init_state and
  restart_state = restart_state
  by unfold_locales (auto simp: cdcl\<^sub>W_mset_state)

interpretation cdcl\<^sub>W_mset: conflict_driven_clause_learning\<^sub>W where
  trail = trail and
  init_clss = init_clss and
  learned_clss = learned_clss and
  backtrack_lvl = backtrack_lvl and
  conflicting = conflicting and

  cons_trail = cons_trail and
  tl_trail = tl_trail and
  add_learned_cls = add_learned_cls and
  remove_cls = remove_cls and
  update_backtrack_lvl = update_backtrack_lvl and
  update_conflicting = update_conflicting and
  init_state = init_state and
  restart_state = restart_state
  by unfold_locales auto

lemma cdcl\<^sub>W_mset_state_eq_eq: "cdcl\<^sub>W_mset.state_eq = (op =)"
   apply (intro ext)
   unfolding cdcl\<^sub>W_mset.state_eq_def
   by (auto simp: cdcl\<^sub>W_mset_state)

notation cdcl\<^sub>W_mset.state_eq (infix "\<sim>m" 49)

(* declare cdcl\<^sub>W_mset.state_simp[simp del] *)

subsection \<open>The State\<close>
text \<open>We will abstract the representation of clause and clauses via two locales. We expect our
  representation to behave like multiset, but the internal representation can be done using list
  or whatever other representation.\<close>

locale abs_state\<^sub>W_ops =
  raw_clss mset_cls
    mset_clss union_clss in_clss insert_clss remove_from_clss
    +
  raw_ccls_union mset_ccls union_ccls remove_clit
  for
    -- \<open>Clause\<close>
    mset_cls :: "'cls \<Rightarrow> 'v clause" and

    -- \<open>Multiset of Clauses\<close>
    mset_clss :: "'clss \<Rightarrow> 'v clauses" and
    union_clss :: "'clss \<Rightarrow> 'clss \<Rightarrow> 'clss" and
    in_clss :: "'cls \<Rightarrow> 'clss \<Rightarrow> bool" and
    insert_clss :: "'cls \<Rightarrow> 'clss \<Rightarrow> 'clss" and
    remove_from_clss :: "'cls \<Rightarrow> 'clss \<Rightarrow> 'clss" and

    mset_ccls :: "'ccls \<Rightarrow> 'v clause" and
    union_ccls :: "'ccls \<Rightarrow> 'ccls \<Rightarrow> 'ccls" and
    remove_clit :: "'v literal \<Rightarrow> 'ccls \<Rightarrow> 'ccls"
    +
  fixes
    ccls_of_cls :: "'cls \<Rightarrow> 'ccls" and
    cls_of_ccls :: "'ccls \<Rightarrow> 'cls" and

    conc_trail :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" and
    hd_raw_conc_trail :: "'st \<Rightarrow> ('v, 'cls) ann_lit" and
    raw_conc_init_clss :: "'st \<Rightarrow> 'clss" and
    raw_conc_learned_clss :: "'st \<Rightarrow> 'clss" and
    conc_backtrack_lvl :: "'st \<Rightarrow> nat" and
    raw_conc_conflicting :: "'st \<Rightarrow> 'ccls option" and

    cons_conc_trail :: "('v, 'cls) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_conc_trail :: "'st \<Rightarrow> 'st" and
    add_conc_learned_cls :: "'cls \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'cls \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conc_backtrack_lvl :: "nat \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conc_conflicting :: "'ccls option \<Rightarrow> 'st \<Rightarrow> 'st" and
    reduce_conc_trail_to :: "('v, 'v clause) ann_lits \<Rightarrow> 'st \<Rightarrow> 'st" and

    init_state :: "'clss \<Rightarrow> 'st" and
    restart_state :: "'st \<Rightarrow> 'st"
  assumes
    mset_ccls_ccls_of_cls[simp]:
      "mset_ccls (ccls_of_cls C) = mset_cls C" and
    mset_cls_cls_of_ccls[simp]:
      "mset_cls (cls_of_ccls D) = mset_ccls D" and
    ex_mset_cls: "\<exists>a. mset_cls a = E"
begin
fun mmset_of_mlit :: "('v, 'cls) ann_lit \<Rightarrow> ('v, 'v clause) ann_lit"
  where
"mmset_of_mlit (Propagated L C) = Propagated L (mset_cls C)" |
"mmset_of_mlit (Decided L) = Decided L"

lemma lit_of_mmset_of_mlit[simp]:
  "lit_of (mmset_of_mlit a) = lit_of a"
  by (cases a) auto

lemma lit_of_mmset_of_mlit_set_lit_of_l[simp]:
  "lit_of ` mmset_of_mlit ` set M' = lits_of_l M'"
  by (induction M') auto

lemma map_mmset_of_mlit_true_annots_true_cls[simp]:
  "map mmset_of_mlit M' \<Turnstile>as C \<longleftrightarrow> M' \<Turnstile>as C"
  by (simp add: true_annots_true_cls lits_of_def)

abbreviation "conc_init_clss \<equiv> \<lambda>S. mset_clss (raw_conc_init_clss S)"
abbreviation "conc_learned_clss \<equiv> \<lambda>S. mset_clss (raw_conc_learned_clss S)"
abbreviation "conc_conflicting \<equiv> \<lambda>S. map_option mset_ccls (raw_conc_conflicting S)"

notation in_clss (infix "!\<in>!" 50)
notation union_clss (infix "\<oplus>" 50)
notation insert_clss (infix "!++!" 50)

notation union_ccls (infix "!\<union>" 50)

definition raw_clauses :: "'st \<Rightarrow> 'clss" where
"raw_clauses S = union_clss (raw_conc_init_clss S) (raw_conc_learned_clss S)"

abbreviation conc_clauses :: "'st \<Rightarrow> 'v clauses" where
"conc_clauses S \<equiv> mset_clss (raw_clauses S)"

abbreviation resolve_cls where
"resolve_cls L D' E \<equiv> union_ccls (remove_clit (-L) D') (remove_clit L (ccls_of_cls E))"

end

text \<open>We are using an abstract state to abstract away the detail of the implementation: we do not
  need to know how the clauses are represented internally, we just need to know that they can be
  converted to multisets.\<close>
text \<open>Weidenbach state is a five-tuple composed of:
  \<^enum> the conc_trail is a list of decided literals;
  \<^enum> the initial set of clauses (that is not changed during the whole calculus);
  \<^enum> the learned clauses (clauses can be added or remove);
  \<^enum> the maximum level of the conc_trail;
  \<^enum> the conc_conflicting clause (if any has been found so far).\<close>
text \<open>
  There are two different clause representation: one for the conc_conflicting clause (@{typ "'ccls"},
  standing for conc_conflicting clause) and one for the initial and learned clauses (@{typ "'cls"},
  standing for clause). The representation of the clauses annotating literals in the conc_trail
  is slightly different: being able to convert it to @{typ 'cls} is enough (needed for function
  @{term "hd_raw_conc_trail"} below).

  There are several axioms to state the independance of the different fields of the state: for
  example, adding a clause to the learned clauses does not change the conc_trail.\<close>
locale abs_state\<^sub>W =
  abs_state\<^sub>W_ops
    -- \<open>functions for clauses: \<close>
    mset_cls
      mset_clss union_clss in_clss insert_clss remove_from_clss

    -- \<open>functions for the conc_conflicting clause: \<close>
    mset_ccls union_ccls remove_clit

    -- \<open>Conversion between conc_conflicting and non-conc_conflicting\<close>
    ccls_of_cls cls_of_ccls

    -- \<open>functions about the state: \<close>
      -- \<open>getter:\<close>
    conc_trail hd_raw_conc_trail raw_conc_init_clss raw_conc_learned_clss conc_backtrack_lvl raw_conc_conflicting
      -- \<open>setter:\<close>
    cons_conc_trail tl_conc_trail add_conc_learned_cls remove_cls update_conc_backtrack_lvl
    update_conc_conflicting reduce_conc_trail_to

      -- \<open>Some specific states:\<close>
    init_state
    restart_state
  for
    mset_cls :: "'cls \<Rightarrow> 'v clause" and

    mset_clss :: "'clss \<Rightarrow> 'v clauses" and
    union_clss :: "'clss \<Rightarrow> 'clss \<Rightarrow> 'clss" and
    in_clss :: "'cls \<Rightarrow> 'clss \<Rightarrow> bool" and
    insert_clss :: "'cls \<Rightarrow> 'clss \<Rightarrow> 'clss" and
    remove_from_clss :: "'cls \<Rightarrow> 'clss \<Rightarrow> 'clss" and

    mset_ccls :: "'ccls \<Rightarrow> 'v clause" and
    union_ccls :: "'ccls \<Rightarrow> 'ccls \<Rightarrow> 'ccls" and
    remove_clit :: "'v literal \<Rightarrow> 'ccls \<Rightarrow> 'ccls" and

    ccls_of_cls :: "'cls \<Rightarrow> 'ccls" and
    cls_of_ccls :: "'ccls \<Rightarrow> 'cls" and

    conc_trail :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" and
    hd_raw_conc_trail :: "'st \<Rightarrow> ('v, 'cls) ann_lit" and
    raw_conc_init_clss :: "'st \<Rightarrow> 'clss" and
    raw_conc_learned_clss :: "'st \<Rightarrow> 'clss" and
    conc_backtrack_lvl :: "'st \<Rightarrow> nat" and
    raw_conc_conflicting :: "'st \<Rightarrow> 'ccls option" and

    cons_conc_trail :: "('v, 'cls) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_conc_trail :: "'st \<Rightarrow> 'st" and
    add_conc_learned_cls :: "'cls \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'cls \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conc_backtrack_lvl :: "nat \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conc_conflicting :: "'ccls option \<Rightarrow> 'st \<Rightarrow> 'st" and
    reduce_conc_trail_to :: "('v, 'v clause) ann_lits \<Rightarrow> 'st \<Rightarrow> 'st" and

    init_state :: "'clss \<Rightarrow> 'st" and
    restart_state :: "'st \<Rightarrow> 'st" +
  assumes
    hd_raw_conc_trail: "conc_trail S \<noteq> [] \<Longrightarrow> mmset_of_mlit (hd_raw_conc_trail S) = hd (conc_trail S)" and
    conc_trail_cons_conc_trail[simp]:
      "\<And>L st. undefined_lit (conc_trail st) (lit_of L) \<Longrightarrow>
        conc_trail (cons_conc_trail L st) = mmset_of_mlit L # conc_trail st" and
    conc_trail_tl_conc_trail[simp]: "\<And>st. conc_trail (tl_conc_trail st) = tl (conc_trail st)" and
    conc_trail_add_conc_learned_cls[simp]:
      "\<And>C st. no_dup (conc_trail st) \<Longrightarrow> conc_trail (add_conc_learned_cls C st) = conc_trail st" and
    conc_trail_remove_cls[simp]:
      "\<And>C st. conc_trail (remove_cls C st) = conc_trail st" and
    conc_trail_update_conc_backtrack_lvl[simp]: "\<And>st C. conc_trail (update_conc_backtrack_lvl C st) = conc_trail st" and
    conc_trail_update_conc_conflicting[simp]: "\<And>C st. conc_trail (update_conc_conflicting C st) = conc_trail st" and

    conc_init_clss_cons_conc_trail[simp]:
      "\<And>M st. undefined_lit (conc_trail st) (lit_of M) \<Longrightarrow>
        conc_init_clss (cons_conc_trail M st) = conc_init_clss st"
      and
    conc_init_clss_tl_conc_trail[simp]:
      "\<And>st. conc_init_clss (tl_conc_trail st) = conc_init_clss st" and
    conc_init_clss_add_conc_learned_cls[simp]:
      "\<And>C st. no_dup (conc_trail st) \<Longrightarrow> conc_init_clss (add_conc_learned_cls C st) = conc_init_clss st" and
    conc_init_clss_remove_cls[simp]:
      "\<And>C st. conc_init_clss (remove_cls C st) = removeAll_mset (mset_cls C) (conc_init_clss st)" and
    conc_init_clss_update_conc_backtrack_lvl[simp]:
      "\<And>st C. conc_init_clss (update_conc_backtrack_lvl C st) = conc_init_clss st" and
    conc_init_clss_update_conc_conflicting[simp]:
      "\<And>C st. conc_init_clss (update_conc_conflicting C st) = conc_init_clss st" and

    conc_learned_clss_cons_conc_trail[simp]:
      "\<And>M st. undefined_lit (conc_trail st) (lit_of M) \<Longrightarrow>
        conc_learned_clss (cons_conc_trail M st) = conc_learned_clss st" and
    conc_learned_clss_tl_conc_trail[simp]:
      "\<And>st. conc_learned_clss (tl_conc_trail st) = conc_learned_clss st" and
    conc_learned_clss_add_conc_learned_cls[simp]:
      "\<And>C st. no_dup (conc_trail st) \<Longrightarrow>
        conc_learned_clss (add_conc_learned_cls C st) = {#mset_cls C#} + conc_learned_clss st" and
    conc_learned_clss_remove_cls[simp]:
      "\<And>C st. conc_learned_clss (remove_cls C st) = removeAll_mset (mset_cls C) (conc_learned_clss st)" and
    conc_learned_clss_update_conc_backtrack_lvl[simp]:
      "\<And>st C. conc_learned_clss (update_conc_backtrack_lvl C st) = conc_learned_clss st" and
    conc_learned_clss_update_conc_conflicting[simp]:
      "\<And>C st. conc_learned_clss (update_conc_conflicting C st) = conc_learned_clss st" and

    conc_backtrack_lvl_cons_conc_trail[simp]:
      "\<And>M st. undefined_lit (conc_trail st) (lit_of M) \<Longrightarrow>
        conc_backtrack_lvl (cons_conc_trail M st) = conc_backtrack_lvl st" and
    conc_backtrack_lvl_tl_conc_trail[simp]:
      "\<And>st. conc_backtrack_lvl (tl_conc_trail st) = conc_backtrack_lvl st" and
    conc_backtrack_lvl_add_conc_learned_cls[simp]:
      "\<And>C st. no_dup (conc_trail st) \<Longrightarrow> conc_backtrack_lvl (add_conc_learned_cls C st) = conc_backtrack_lvl st" and
    conc_backtrack_lvl_remove_cls[simp]:
      "\<And>C st. conc_backtrack_lvl (remove_cls C st) = conc_backtrack_lvl st" and
    conc_backtrack_lvl_update_conc_backtrack_lvl[simp]:
      "\<And>st k. conc_backtrack_lvl (update_conc_backtrack_lvl k st) = k" and
    conc_backtrack_lvl_update_conc_conflicting[simp]:
      "\<And>C st. conc_backtrack_lvl (update_conc_conflicting C st) = conc_backtrack_lvl st" and

    conc_conflicting_cons_conc_trail[simp]:
      "\<And>M st. undefined_lit (conc_trail st) (lit_of M) \<Longrightarrow>
        conc_conflicting (cons_conc_trail M st) = conc_conflicting st" and
    conc_conflicting_tl_conc_trail[simp]:
      "\<And>st. conc_conflicting (tl_conc_trail st) = conc_conflicting st" and
    conc_conflicting_add_conc_learned_cls[simp]:
      "\<And>C st. no_dup (conc_trail st) \<Longrightarrow> conc_conflicting (add_conc_learned_cls C st) = conc_conflicting st"
      and
    conc_conflicting_remove_cls[simp]:
      "\<And>C st. conc_conflicting (remove_cls C st) = conc_conflicting st" and
    conc_conflicting_update_conc_backtrack_lvl[simp]:
      "\<And>st C. conc_conflicting (update_conc_backtrack_lvl C st) = conc_conflicting st" and
    conc_conflicting_update_conc_conflicting[simp]:
      "\<And>C st. raw_conc_conflicting (update_conc_conflicting C st) = C" and

    init_state_conc_trail[simp]: "\<And>N. conc_trail (init_state N) = []" and
    init_state_clss[simp]: "\<And>N. (conc_init_clss (init_state N)) = mset_clss N" and
    init_state_conc_learned_clss[simp]: "\<And>N. conc_learned_clss (init_state N) = {#}" and
    init_state_conc_backtrack_lvl[simp]: "\<And>N. conc_backtrack_lvl (init_state N) = 0" and
    init_state_conc_conflicting[simp]: "\<And>N. conc_conflicting (init_state N) = None" and

    conc_trail_restart_state[simp]: "conc_trail (restart_state S) = []" and
    conc_init_clss_restart_state[simp]: "conc_init_clss (restart_state S) = conc_init_clss S" and
    conc_learned_clss_restart_state[intro]:
      "conc_learned_clss (restart_state S) \<subseteq># conc_learned_clss S" and
    conc_backtrack_lvl_restart_state[simp]: "conc_backtrack_lvl (restart_state S) = 0" and
    conc_conflicting_restart_state[simp]: "conc_conflicting (restart_state S) = None" and

    trail_reduce_conc_trail_to[simp]:
      "conc_trail st = M2 @ M1 \<Longrightarrow> conc_trail (reduce_conc_trail_to M1 st) = M1" and
    raw_conc_init_clss_reduce_conc_trail_to[simp]:
      "raw_conc_init_clss (reduce_conc_trail_to M1 st) = raw_conc_init_clss st" and
    raw_conc_learned_clss_reduce_conc_trail_to[simp]:
    "raw_conc_learned_clss (reduce_conc_trail_to M1 st) = raw_conc_learned_clss st" and
    conc_backtrack_lvl_reduce_conc_trail_to[simp]:
    "conc_backtrack_lvl (reduce_conc_trail_to M1 st) = conc_backtrack_lvl st" and
    conc_conflicting_reduce_conc_trail_to[simp]:
    "conc_conflicting (reduce_conc_trail_to M1 st) = conc_conflicting st"
begin

lemma
  shows
    clauses_cons_conc_trail[simp]:
      "undefined_lit (conc_trail S) (lit_of M) \<Longrightarrow> conc_clauses (cons_conc_trail M S) = conc_clauses S" and
    (* non-standard to avoid name clash with NOT's clauses_tl_conc_trail *)
    clss_tl_conc_trail[simp]: "conc_clauses (tl_conc_trail S) = conc_clauses S" and
    clauses_add_conc_learned_cls_unfolded:
      "no_dup (conc_trail S) \<Longrightarrow> conc_clauses (add_conc_learned_cls U S) =
         {#mset_cls U#} + conc_learned_clss S + conc_init_clss S"
      and
    clauses_update_conc_backtrack_lvl[simp]: "conc_clauses (update_conc_backtrack_lvl k S) = conc_clauses S" and
    clauses_update_conc_conflicting[simp]: "conc_clauses (update_conc_conflicting D S) = conc_clauses S" and
    clauses_remove_cls[simp]:
      "conc_clauses (remove_cls C S) = removeAll_mset (mset_cls C) (conc_clauses S)" and
    clauses_add_conc_learned_cls[simp]:
      "no_dup (conc_trail S) \<Longrightarrow> conc_clauses (add_conc_learned_cls C S) = {#mset_cls C#} + conc_clauses S" and
    clauses_restart[simp]: "conc_clauses (restart_state S) \<subseteq># conc_clauses S" and
    clauses_init_state[simp]: "\<And>N. conc_clauses (init_state N) = mset_clss N"
    prefer 9 using raw_clauses_def conc_learned_clss_restart_state apply fastforce
    by (auto simp: ac_simps replicate_mset_plus raw_clauses_def intro: multiset_eqI)

definition state :: "'st \<Rightarrow> 'v cdcl\<^sub>W_mset" where
"state = (\<lambda>S. (conc_trail S, conc_init_clss S, conc_learned_clss S, conc_backtrack_lvl S,
  conc_conflicting S))"

abbreviation incr_lvl :: "'st \<Rightarrow> 'st" where
"incr_lvl S \<equiv> update_conc_backtrack_lvl (conc_backtrack_lvl S + 1) S"

abbreviation state_eq :: "'st \<Rightarrow> 'st \<Rightarrow> bool" (infix "\<sim>" 30) where
"S \<sim> T \<equiv> state S \<sim>m state T"

lemma state_eq_sym:
  "S \<sim> T \<longleftrightarrow> T \<sim> S"
  using cdcl\<^sub>W_mset.state_eq_sym by blast

lemma state_eq_trans:
  "S \<sim> T \<Longrightarrow> T \<sim> U \<Longrightarrow> S \<sim> U"
  using cdcl\<^sub>W_mset.state_eq_trans by blast


lemma
  shows
    state_eq_conc_trail: "S \<sim> T \<Longrightarrow> conc_trail S = conc_trail T" and
    state_eq_conc_init_clss: "S \<sim> T \<Longrightarrow> conc_init_clss S = conc_init_clss T" and
    state_eq_conc_learned_clss: "S \<sim> T \<Longrightarrow> conc_learned_clss S = conc_learned_clss T" and
    state_eq_conc_backtrack_lvl: "S \<sim> T \<Longrightarrow> conc_backtrack_lvl S = conc_backtrack_lvl T" and
    state_eq_conc_conflicting: "S \<sim> T \<Longrightarrow> conc_conflicting S = conc_conflicting T" and
    state_eq_clauses: "S \<sim> T \<Longrightarrow> conc_clauses S = conc_clauses T" and
    state_eq_undefined_lit: "S \<sim> T \<Longrightarrow> undefined_lit (conc_trail S) L = undefined_lit (conc_trail T) L"
  unfolding raw_clauses_def state_def cdcl\<^sub>W_mset.state_eq_def
  by (auto simp: cdcl\<^sub>W_mset_state)

text \<open>We combine all simplification rules about @{term state_eq} in a single list of theorems. While
  they are handy as simplification rule as long as we are working on the state, they also cause a
  \<^emph>\<open>huge\<close> slow-down in all other cases.\<close>
lemmas state_simp = state_eq_conc_trail state_eq_conc_init_clss state_eq_conc_learned_clss
  state_eq_conc_backtrack_lvl state_eq_conc_conflicting state_eq_clauses state_eq_undefined_lit

lemma atms_of_ms_conc_learned_clss_restart_state_in_atms_of_ms_conc_learned_clssI[intro]:
  "x \<in> atms_of_mm (conc_learned_clss (restart_state S)) \<Longrightarrow> x \<in> atms_of_mm (conc_learned_clss S)"
  by (meson atms_of_ms_mono conc_learned_clss_restart_state set_mset_mono subsetCE)

lemma clauses_reduce_conc_trail_to[simp]:
  "conc_clauses (reduce_conc_trail_to F S) = conc_clauses S"
  unfolding raw_clauses_def by auto

lemma in_get_all_ann_decomposition_conc_trail_update_conc_trail[simp]:
  assumes H: "(L # M1, M2) \<in> set (get_all_ann_decomposition (conc_trail S))"
  shows "conc_trail (reduce_conc_trail_to M1 S) = M1"
  using assms by auto

lemma raw_conc_conflicting_cons_conc_trail[simp]:
  assumes "undefined_lit (conc_trail S) (lit_of L)"
  shows
    "raw_conc_conflicting (cons_conc_trail L S) = None \<longleftrightarrow> raw_conc_conflicting S = None"
  using assms conc_conflicting_cons_conc_trail[of S L] map_option_is_None by fastforce+

lemma raw_conc_conflicting_add_conc_learned_cls[simp]:
  "no_dup (conc_trail S) \<Longrightarrow>
    raw_conc_conflicting (add_conc_learned_cls C S) = None \<longleftrightarrow> raw_conc_conflicting S = None"
  using map_option_is_None conc_conflicting_add_conc_learned_cls[of S C] by fastforce+

lemma raw_conc_conflicting_update_backtracl_lvl[simp]:
  "raw_conc_conflicting (update_conc_backtrack_lvl k S) = None \<longleftrightarrow> raw_conc_conflicting S = None"
  using map_option_is_None conc_conflicting_update_conc_backtrack_lvl[of k S] by fastforce+

end -- \<open>end of \<open>state\<^sub>W\<close> locale\<close>


subsection \<open>CDCL Rules\<close>
text \<open>Because of the strategy we will later use, we distinguish propagate, conflict from the other
  rules\<close>
locale abs_conflict_driven_clause_learning\<^sub>W =
  abs_state\<^sub>W
    -- \<open>functions for clauses: \<close>
    mset_cls
    mset_clss union_clss in_clss insert_clss remove_from_clss

    -- \<open>functions for the conc_conflicting clause: \<close>
    mset_ccls union_ccls remove_clit

    -- \<open>conversion\<close>
    ccls_of_cls cls_of_ccls

    -- \<open>functions for the state: \<close>
      -- \<open>access functions:\<close>
    conc_trail hd_raw_conc_trail raw_conc_init_clss raw_conc_learned_clss conc_backtrack_lvl raw_conc_conflicting
      -- \<open>changing state:\<close>
    cons_conc_trail tl_conc_trail add_conc_learned_cls remove_cls update_conc_backtrack_lvl
    update_conc_conflicting reduce_conc_trail_to

      -- \<open>get state:\<close>
    init_state
    restart_state
  for
    mset_cls :: "'cls \<Rightarrow> 'v clause" and

    mset_clss :: "'clss \<Rightarrow> 'v clauses" and
    union_clss :: "'clss \<Rightarrow> 'clss \<Rightarrow> 'clss" and
    in_clss :: "'cls \<Rightarrow> 'clss \<Rightarrow> bool" and
    insert_clss :: "'cls \<Rightarrow> 'clss \<Rightarrow> 'clss" and
    remove_from_clss :: "'cls \<Rightarrow> 'clss \<Rightarrow> 'clss" and

    mset_ccls :: "'ccls \<Rightarrow> 'v clause" and
    union_ccls :: "'ccls \<Rightarrow> 'ccls \<Rightarrow> 'ccls" and
    remove_clit :: "'v literal \<Rightarrow> 'ccls \<Rightarrow> 'ccls" and

    ccls_of_cls :: "'cls \<Rightarrow> 'ccls" and
    cls_of_ccls :: "'ccls \<Rightarrow> 'cls" and

    conc_trail :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" and
    hd_raw_conc_trail :: "'st \<Rightarrow> ('v, 'cls) ann_lit" and
    raw_conc_init_clss :: "'st \<Rightarrow> 'clss" and
    raw_conc_learned_clss :: "'st \<Rightarrow> 'clss" and
    conc_backtrack_lvl :: "'st \<Rightarrow> nat" and
    raw_conc_conflicting :: "'st \<Rightarrow> 'ccls option" and
    reduce_conc_trail_to :: "('v, 'v clause) ann_lits \<Rightarrow> 'st \<Rightarrow> 'st" and

    cons_conc_trail :: "('v, 'cls) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_conc_trail :: "'st \<Rightarrow> 'st" and
    add_conc_learned_cls :: "'cls \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'cls \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conc_backtrack_lvl :: "nat \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conc_conflicting :: "'ccls option \<Rightarrow> 'st \<Rightarrow> 'st" and

    init_state :: "'clss \<Rightarrow> 'st" and
    restart_state :: "'st \<Rightarrow> 'st"
begin

lemma clauses_state_conc_clauses[simp]: "cdcl\<^sub>W_mset.clauses (state S) = conc_clauses S"
  apply (cases "state S")
  unfolding cdcl\<^sub>W_mset.clauses_def raw_clauses_def
  unfolding cdcl\<^sub>W_mset_state state_def
  by simp

lemma conflicting_None_iff_raw_conc_conflicting[simp]:
  "conflicting (state S) = None \<longleftrightarrow> raw_conc_conflicting S = None"
  unfolding state_def conflicting_def by simp

lemma trail_state_add_conc_learned_cls:
  "no_dup (conc_trail S) \<Longrightarrow> trail (state (add_conc_learned_cls D S)) = trail (state S)"
  unfolding trail_def state_def by simp

lemma trail_state_update_backtrack_lvl:
  "trail (state (update_conc_backtrack_lvl i S)) = trail (state S)"
  unfolding trail_def state_def by simp

lemma trail_state_update_conflicting:
  "trail (state (update_conc_conflicting i S)) = trail (state S)"
  unfolding trail_def state_def by simp

lemma trail_state_conc_trail[simp]:
  "trail (state S) = conc_trail S"
  unfolding trail_def state_def by auto

lemma init_clss_state_conc_init_clss[simp]:
  "init_clss (state S) = conc_init_clss S"
  unfolding init_clss_def state_def by auto

lemma learned_clss_state_conc_learned_clss[simp]:
  "learned_clss (state S) = conc_learned_clss S"
  unfolding learned_clss_def state_def by auto

lemma tl_trail_state_tl_con_trail[simp]:
  "tl_trail (state S) = state (tl_conc_trail S)"
  by (auto simp: cdcl\<^sub>W_mset_state state_def simp del: trail_state_conc_trail
    init_clss_state_conc_init_clss
    learned_clss_state_conc_learned_clss local.state_simp)

lemma add_learned_cls_state_add_conc_learned_cls[simp]:
  assumes "no_dup (conc_trail S)"
  shows "add_learned_cls (mset_ccls D') (state S) = state (add_conc_learned_cls (cls_of_ccls D') S)"
  using assms by (auto simp: cdcl\<^sub>W_mset_state state_def simp del: trail_state_conc_trail
    init_clss_state_conc_init_clss
    learned_clss_state_conc_learned_clss local.state_simp)

lemma state_cons_cons_trail_cons_trail[simp]:
  "undefined_lit (trail (state S)) (lit_of L) \<Longrightarrow>
    state (cons_conc_trail L S) = cons_trail (mmset_of_mlit L) (state S)"
  by (auto simp: cdcl\<^sub>W_mset_state state_def simp del: trail_state_conc_trail
    init_clss_state_conc_init_clss
    learned_clss_state_conc_learned_clss local.state_simp)

lemma state_update_conc_conflicting_update_conflicting[simp]:
  "update_conflicting (Some (mset_ccls D)) (state S) = state (update_conc_conflicting (Some D) S)"
  "update_conflicting (Some (mset_cls D')) (state S) =
    state (update_conc_conflicting (Some (ccls_of_cls D')) S)"
  by (auto simp: cdcl\<^sub>W_mset_state state_def simp del: trail_state_conc_trail
    init_clss_state_conc_init_clss
    learned_clss_state_conc_learned_clss local.state_simp)

lemma update_conflicting_None_state[simp]:
  "update_conflicting None (state S) = state (update_conc_conflicting None S)"
  by (auto simp: cdcl\<^sub>W_mset_state state_def simp del: trail_state_conc_trail
    init_clss_state_conc_init_clss
    learned_clss_state_conc_learned_clss local.state_simp)

lemma update_backtrack_lvl_state[simp]:
  "update_backtrack_lvl i (state S) = state (update_conc_backtrack_lvl i S)"
  by (auto simp: cdcl\<^sub>W_mset_state state_def simp del: trail_state_conc_trail
    init_clss_state_conc_init_clss
    learned_clss_state_conc_learned_clss local.state_simp)

lemma conc_conflicting_conflicting[simp]:
  "conflicting (state S) = conc_conflicting S"
  by (auto simp: cdcl\<^sub>W_mset_state state_def simp del: trail_state_conc_trail
    init_clss_state_conc_init_clss
    learned_clss_state_conc_learned_clss local.state_simp)

lemma update_conflicting_resolve_state_update_conc_conflicting[simp]:
  "update_conflicting (Some (remove1_mset (- L) (mset_ccls D') #\<union> remove1_mset L (mset_cls E')))
    (state (tl_conc_trail S)) =
   state (update_conc_conflicting (Some (resolve_cls L D' E')) (tl_conc_trail S))"
  by (auto simp: cdcl\<^sub>W_mset_state state_def simp del: trail_state_conc_trail
    init_clss_state_conc_init_clss
    learned_clss_state_conc_learned_clss local.state_simp)

lemma conc_backtrack_lvl_backtrack_lvl[simp]:
  "backtrack_lvl (state S) = conc_backtrack_lvl S"
  unfolding state_def by (auto simp: cdcl\<^sub>W_mset_state)

lemma state_state:
  "cdcl\<^sub>W_mset.state (state S) = (trail (state S), init_clss (state S), learned_clss (state S),
  backtrack_lvl (state S), conflicting (state S))"
  by (simp)

lemma state_reduce_conc_trail_to_reduce_conc_trail_to[simp]:
  assumes [simp]: "conc_trail S = M2 @ M1"
  shows "cdcl\<^sub>W_mset.reduce_trail_to M1 (state S) = state (reduce_conc_trail_to M1 S)" (is "?RS = ?SR")
proof -
  have 1: "trail ?SR = trail ?RS"
    apply (subst state_def)
    apply (auto simp add: cdcl\<^sub>W_mset.trail_reduce_trail_to_drop)
    apply (auto simp: trail_def)
    done

  have 2: "init_clss ?SR = init_clss ?RS"
     by simp

  have 3: "learned_clss ?SR = learned_clss ?RS"
     by simp

  have 4: "backtrack_lvl ?SR = backtrack_lvl ?RS"
     by simp

  have 5: "conflicting ?SR = conflicting ?RS"
     by simp

  show ?thesis
    using 1 2 3 4 5 apply -
    apply (subst (asm) trail_def, subst (asm) trail_def)
    apply (subst (asm) init_clss_def, subst (asm) init_clss_def)
    apply (subst (asm) learned_clss_def, subst (asm) learned_clss_def)
    apply (subst (asm) backtrack_lvl_def, subst (asm) backtrack_lvl_def)
    apply (subst (asm) conflicting_def, subst (asm) conflicting_def)
    apply (cases "state (reduce_conc_trail_to M1 S)")
    apply (cases "cdcl\<^sub>W_mset.reduce_trail_to M1 (state S)")
    by simp
qed

text \<open>More robust version of @{thm in_mset_clss_exists_preimage}:\<close>
lemma in_clauses_preimage:
  assumes b: "b \<in># cdcl\<^sub>W_mset.clauses (state C)"
  shows "\<exists>b'. b' !\<in>! raw_clauses C \<and> mset_cls b' = b"
proof -
  have "b \<in># conc_clauses C"
    using b by auto
  from in_mset_clss_exists_preimage[OF this] show ?thesis .
qed

inductive propagate_abs :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
propagate_abs_rule: "conc_conflicting S = None \<Longrightarrow>
  E !\<in>! raw_clauses S \<Longrightarrow>
  L \<in># mset_cls E \<Longrightarrow>
  conc_trail S \<Turnstile>as CNot (mset_cls E - {#L#}) \<Longrightarrow>
  undefined_lit (conc_trail S) L \<Longrightarrow>
  T \<sim> cons_conc_trail (Propagated L E) S \<Longrightarrow>
  propagate_abs S T"

inductive_cases propagate_absE: "propagate_abs S T"

lemma propagate_propagate_abs:
  "cdcl\<^sub>W_mset.propagate (state S) (state T) \<longleftrightarrow> propagate_abs S T" (is "?mset \<longleftrightarrow> ?abs")
proof
  assume ?abs
  then obtain E L where
    confl: "conc_conflicting S = None" and
    E: "E !\<in>! raw_clauses S" and
    L: "L \<in># mset_cls E" and
    tr_E: "conc_trail S \<Turnstile>as CNot (mset_cls E - {#L#})" and
    undef: "undefined_lit (conc_trail S) L" and
    T: "T \<sim> cons_conc_trail (Propagated L E) S"
    by (auto elim: propagate_absE)

  show ?mset
    apply (rule cdcl\<^sub>W_mset.propagate_rule)
        using confl apply auto[]
       using E apply auto[]
      using L apply auto[]
     using tr_E apply auto[]
     using undef apply (auto simp:)[]
    using undef T unfolding cdcl\<^sub>W_mset_state_eq_eq state_def cons_trail_def by simp
next
  assume ?mset
  then obtain E L where
    "conc_conflicting S = None" and
    "E !\<in>! raw_clauses S" and
    "L \<in># mset_cls E" and
    "conc_trail S \<Turnstile>as CNot (mset_cls E - {#L#})" and
    "undefined_lit (conc_trail S) L" and
    "state T \<sim>m cons_trail (Propagated L (mset_cls E)) (state S)"
    by (auto elim!: cdcl\<^sub>W_mset.propagateE dest!: in_clauses_preimage
      simp: cdcl\<^sub>W_mset.clauses_def raw_clauses_def)
  then show ?abs
    by (auto intro!: propagate_abs_rule)
qed

lemma no_step_propagate_no_step_propagate_abs:
  "no_step cdcl\<^sub>W_mset.propagate (state S) \<longleftrightarrow> no_step propagate_abs S" (is "?conc \<longleftrightarrow> ?abs")
proof
  assume ?conc
  show ?abs
    proof (rule ccontr)
      assume "\<not>?abs"
      then show False
        using cdcl\<^sub>W_mset.propagate_rule[OF _ _ _ _ _ cdcl\<^sub>W_mset.state_eq_ref, of "state S"]
        \<open>?conc\<close> by (auto elim!: propagate_absE dest!: in_clss_mset_clss)
    qed
next
  assume ?abs
  show ?conc
    proof (rule ccontr)
      assume "\<not>?conc"
      then have "Ex (propagate_abs S)"
        using propagate_abs_rule[OF _ _ _ _ _ cdcl\<^sub>W_mset.state_eq_ref, of S]
        by (fastforce elim!: cdcl\<^sub>W_mset.propagateE dest!: in_clauses_preimage)
      then show False
        using \<open>?abs\<close> by blast
    qed
qed

inductive conflict_abs :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
conflict_abs_rule: "
  conc_conflicting S = None \<Longrightarrow>
  D !\<in>! raw_clauses S \<Longrightarrow>
  conc_trail S \<Turnstile>as CNot (mset_cls D) \<Longrightarrow>
  T \<sim> update_conc_conflicting (Some (ccls_of_cls D)) S \<Longrightarrow>
  conflict_abs S T"

inductive_cases conflict_absE: "conflict_abs S T"

lemma conflict_conflict_abs:
  "cdcl\<^sub>W_mset.conflict (state S) (state T) \<longleftrightarrow> conflict_abs S T" (is "?mset \<longleftrightarrow> ?abs")
proof
  assume ?abs
  then obtain D where
    confl: "conc_conflicting S = None" and
    D: "D !\<in>! raw_clauses S" and
    tr_D: "conc_trail S \<Turnstile>as CNot (mset_cls D)" and
    T: "T \<sim> update_conc_conflicting (Some (ccls_of_cls D)) S"
    by (auto elim!: conflict_absE)
  show ?mset
    apply (rule cdcl\<^sub>W_mset.conflict_rule)
       using confl apply simp
      using D apply auto[]
     using tr_D apply simp
    using T apply auto
    done
next
  assume ?mset
  then obtain D where
    confl: "conflicting (state S) = None" and
    D: "D \<in># cdcl\<^sub>W_mset.clauses (state S)" and
    tr_D: "trail (state S) \<Turnstile>as CNot D" and
    T: "state T \<sim>m update_conflicting (Some D) (state S)"
    by (cases "state S") (auto elim: cdcl\<^sub>W_mset.conflictE)
  obtain D' where D': "D' !\<in>! raw_clauses S" and DD'[simp]: "D = mset_cls D'"
    using D by (auto dest!: in_mset_clss_exists_preimage)[]
  show ?abs
    apply (rule conflict_abs_rule)
       using confl apply simp
      using D' apply simp
     using tr_D apply simp
    using T by auto
qed

lemma no_step_conflict_no_step_conflict_abs:
  "no_step cdcl\<^sub>W_mset.conflict (state S) \<longleftrightarrow> no_step conflict_abs S" (is "?conc \<longleftrightarrow> ?abs")
proof
  assume ?conc
  show ?abs
    proof (rule ccontr)
      assume "\<not>?abs"
      then show False
        using cdcl\<^sub>W_mset.conflict_rule[OF _ _ _ cdcl\<^sub>W_mset.state_eq_ref, of "state S" "mset_cls _"]
        \<open>?conc\<close> by (auto elim!: conflict_absE dest!: in_clss_mset_clss)
    qed
next
  assume ?abs
  show ?conc
    proof (rule ccontr)
      assume "\<not>?conc"
      then have "Ex (conflict_abs S)"
        using conflict_abs_rule[OF _ _ _ cdcl\<^sub>W_mset.state_eq_ref, of S]
        by (fastforce elim!: cdcl\<^sub>W_mset.conflictE dest!: in_clauses_preimage)
      then show False
        using \<open>?abs\<close> by blast
    qed
qed

inductive backtrack_abs :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
backtrack_abs_rule: "
  raw_conc_conflicting S = Some D \<Longrightarrow>
  L \<in># mset_ccls D \<Longrightarrow>
  (Decided K # M1, M2) \<in> set (get_all_ann_decomposition (conc_trail S)) \<Longrightarrow>
  get_level (conc_trail S) L = conc_backtrack_lvl S \<Longrightarrow>
  get_level (conc_trail S) L = get_maximum_level (conc_trail S) (mset_ccls D) \<Longrightarrow>
  get_maximum_level (conc_trail S) (mset_ccls D - {#L#}) \<equiv> i \<Longrightarrow>
  get_level (conc_trail S) K = i + 1 \<Longrightarrow>
  T \<sim> cons_conc_trail (Propagated L (cls_of_ccls D))
        (reduce_conc_trail_to M1
          (add_conc_learned_cls (cls_of_ccls D)
            (update_conc_backtrack_lvl i
              (update_conc_conflicting None S)))) \<Longrightarrow>
  backtrack_abs S T"

inductive_cases backtrack_absE: "backtrack_abs S T"

lemma backtrack_backtrack_abs:
  assumes inv: "cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv (state S)"
  shows "cdcl\<^sub>W_mset.backtrack (state S) (state T) \<longleftrightarrow> backtrack_abs S T" (is "?conc \<longleftrightarrow> ?abs")
proof
  assume ?abs
  then obtain D L K M1 M2 i where
  D: "raw_conc_conflicting S = Some D" and
  L: "L \<in># mset_ccls D" and
  decomp: "(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (conc_trail S))" and
  lev_L: "get_level (conc_trail S) L = conc_backtrack_lvl S" and
  lev_Max: "get_level (conc_trail S) L = get_maximum_level (conc_trail S) (mset_ccls D)" and
  i: "get_maximum_level (conc_trail S) (mset_ccls D - {#L#}) \<equiv> i" and
  lev_K: "get_level (conc_trail S) K = i + 1" and
  T: "T \<sim> cons_conc_trail (Propagated L (cls_of_ccls D))
        (reduce_conc_trail_to M1
          (add_conc_learned_cls (cls_of_ccls D)
            (update_conc_backtrack_lvl i
              (update_conc_conflicting None S))))"
    by (auto elim!: backtrack_absE)
  have n_d: "no_dup (trail (state S))"
    using lev_L inv unfolding cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_mset.cdcl\<^sub>W_M_level_inv_def
    by simp
  have "atm_of L \<notin> atm_of ` lits_of_l M1"
    apply (rule cdcl\<^sub>W_mset.backtrack_lit_skiped[of _ "state S"])
       using lev_L inv unfolding cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_mset.cdcl\<^sub>W_M_level_inv_def
       apply simp
      using decomp apply simp
     using lev_L inv unfolding cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_mset.cdcl\<^sub>W_M_level_inv_def
       apply simp
    using lev_L inv unfolding cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_mset.cdcl\<^sub>W_M_level_inv_def
       apply simp
   using lev_K apply simp
   done
  then have undef: "undefined_lit M1 L"
    by (auto simp add: defined_lit_map lits_of_def)
  obtain c where tr: "conc_trail S = c @ M2 @ Decided K # M1"
    using decomp by auto
  show ?conc
    apply (rule cdcl\<^sub>W_mset.backtrack_rule)
           using D apply simp
          using L apply simp
         using decomp apply simp
        using lev_L apply simp
       using lev_Max apply simp
      using i apply simp
     using lev_K apply simp
    using T undef n_d tr unfolding cdcl\<^sub>W_mset.state_eq_def
    by auto
next
  assume ?conc
  then obtain L D K M1 M2 i where
    confl: "conflicting (state S) = Some D" and
    L: "L \<in># D" and
    decomp: "(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail (state S)))" and
    lev_L: "get_level (trail (state S)) L = backtrack_lvl (state S)" and
    lev_max: "get_level (trail (state S)) L = get_maximum_level (trail (state S)) (D)" and
    i: "get_maximum_level (trail (state S)) (D - {#L#}) \<equiv> i" and
    lev_K: "get_level (trail (state S)) K = i + 1" and
    T: "state T \<sim>m cons_trail (Propagated L (D))
          (cdcl\<^sub>W_mset.reduce_trail_to M1
            (add_learned_cls D
              (update_backtrack_lvl i
                (update_conflicting None (state S)))))"
    by (auto elim: cdcl\<^sub>W_mset.backtrackE)
  obtain D' where
    confl': "raw_conc_conflicting S = Some D'" and D[simp]: "D = mset_ccls D'"
    using confl by auto
  have n_d: "no_dup (trail (state S))"
    using lev_L inv unfolding cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_mset.cdcl\<^sub>W_M_level_inv_def
    by simp
  have "atm_of L \<notin> atm_of ` lits_of_l M1"
    apply (rule cdcl\<^sub>W_mset.backtrack_lit_skiped[of _ "state S"])
       using lev_L inv unfolding cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_mset.cdcl\<^sub>W_M_level_inv_def
       apply simp
      using decomp apply simp
     using lev_L inv unfolding cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_mset.cdcl\<^sub>W_M_level_inv_def
       apply simp
    using lev_L inv unfolding cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_mset.cdcl\<^sub>W_M_level_inv_def
       apply simp
   using lev_K apply simp
   done
  then have undef: "undefined_lit M1 L"
    by (auto simp add: defined_lit_map lits_of_def)
  show ?abs
    apply (rule backtrack_abs_rule)
           using confl' apply simp
          using L apply simp
         using decomp apply simp
        using lev_L apply simp
       using lev_max apply simp
      using i apply simp
     using lev_K apply simp
    using T undef n_d decomp by auto
qed

inductive decide_abs :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
decide_abs_rule:
  "conc_conflicting S = None \<Longrightarrow>
  undefined_lit (conc_trail S) L \<Longrightarrow>
  atm_of L \<in> atms_of_mm (conc_init_clss S) \<Longrightarrow>
  T \<sim> cons_conc_trail (Decided L) (incr_lvl S) \<Longrightarrow>
  decide_abs S T"

inductive_cases decide_absE: "decide_abs S T"

lemma decide_decide_abs:
  "cdcl\<^sub>W_mset.decide (state S) (state T) \<longleftrightarrow> decide_abs S T"
  by (auto elim!: cdcl\<^sub>W_mset.decideE decide_absE intro!: cdcl\<^sub>W_mset.decide_rule decide_abs_rule)

lemma no_step_decide_no_step_decide_abs:
  "no_step cdcl\<^sub>W_mset.decide (state S) \<longleftrightarrow> no_step decide_abs S" (is "?conc \<longleftrightarrow> ?abs")
proof
  assume ?abs
  then show ?conc
    by (auto elim!: cdcl\<^sub>W_mset.decideE decide_absE intro!: cdcl\<^sub>W_mset.decide_rule decide_abs_rule)[]
next
  assume ?conc
  show ?abs
    proof (rule ccontr)
      assume "\<not> ?abs"
      then obtain T L where
        cond: "conflicting (state S) = None" and
        undef: "undefined_lit (trail (state S)) L " and
        L: "atm_of L \<in> atms_of_mm (init_clss (state S))" and
        T: "state T \<sim>m cons_trail (Decided L) (cdcl\<^sub>W_mset.incr_lvl (state S))"
        by (auto elim!: decide_absE)
      show False
        using cdcl\<^sub>W_mset.decide_rule[OF cond undef L T] \<open>?conc\<close> by fast
    qed
qed

inductive skip_abs :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
skip_abs_rule:
  "conc_trail S = Propagated L C' # M \<Longrightarrow>
   raw_conc_conflicting S = Some E \<Longrightarrow>
   -L \<notin># mset_ccls E \<Longrightarrow>
   mset_ccls E \<noteq> {#} \<Longrightarrow>
   T \<sim> tl_conc_trail S \<Longrightarrow>
   skip_abs S T"

inductive_cases skip_absE: "skip_abs S T"

lemma skip_skip_abs:
  "cdcl\<^sub>W_mset.skip (state S) (state T) \<longleftrightarrow> skip_abs S T" (is "?conc \<longleftrightarrow> ?abs")
proof
  assume ?abs
  then show ?conc
    by (auto elim!: skip_absE intro!: cdcl\<^sub>W_mset.skip_rule)
next
  assume ?conc
  then obtain L C' E M where
    tr: "trail (state S) = Propagated L C' # M" and
    confl: "conflicting (state S) = Some E" and
    L: "-L \<notin># E" and
    E: "E \<noteq> {#}" and
    T: "state T \<sim>m tl_trail (state S)"
    by (auto elim: cdcl\<^sub>W_mset.skipE)
  obtain E' where
    confl': "raw_conc_conflicting S = Some E'" and [simp]: "E = mset_ccls E'"
    using confl by auto
  show ?abs
    apply (rule skip_abs_rule)
        using tr apply simp
       using confl' apply simp
      using L apply simp
     using E apply simp
    using T by simp
qed

lemma skip_exists_skip_abs:
  assumes skip: "cdcl\<^sub>W_mset.skip (state S) T"
  obtains U where "skip_abs S U" and "T \<sim>m state U"
proof -
  obtain L C' E M where
    tr: "trail (state S) = Propagated L C' # M" and
    confl: "conflicting (state S) = Some E" and
    L: "-L \<notin># E" and
    E: "E \<noteq> {#}" and
    T: "T \<sim>m tl_trail (state S)"
    using skip by (auto elim: cdcl\<^sub>W_mset.skipE)
  obtain E' where
    confl': "raw_conc_conflicting S = Some E'" and [simp]: "E = mset_ccls E'"
    using confl by auto
  have "skip_abs S (tl_conc_trail S)"
    apply (rule skip_abs_rule)
        using tr apply simp
       using confl' apply simp
      using L apply simp
     using E apply simp
    using T by simp
  then show ?thesis using that[of "tl_conc_trail S"] T by auto
qed

lemma no_step_skip_no_step_skip_abs:
  "no_step cdcl\<^sub>W_mset.skip (state S) \<longleftrightarrow> no_step skip_abs S"
  apply (rule iffI)
  using skip_skip_abs[symmetric] apply fast
  by (auto dest: skip_exists_skip_abs)

inductive resolve_abs :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
resolve_abs_rule: "conc_trail S \<noteq> [] \<Longrightarrow>
  hd_raw_conc_trail S = Propagated L E \<Longrightarrow>
  L \<in># mset_cls E \<Longrightarrow>
  raw_conc_conflicting S = Some D' \<Longrightarrow>
  -L \<in># mset_ccls D' \<Longrightarrow>
  get_maximum_level (conc_trail S) (mset_ccls (remove_clit (-L) D')) = conc_backtrack_lvl S \<Longrightarrow>
  T \<sim> update_conc_conflicting (Some (resolve_cls L D' E))
    (tl_conc_trail S) \<Longrightarrow>
  resolve_abs S T"

inductive_cases resolve_absE: "resolve_abs S T"

lemma resolve_resolve_abs:
  "cdcl\<^sub>W_mset.resolve (state S) (state T) \<longleftrightarrow> resolve_abs S T" (is "?conc \<longleftrightarrow> ?abs")
proof
  assume ?conc
  then obtain L E D where
    tr: "trail (state S) \<noteq> []" and
    hd: "cdcl\<^sub>W_mset.hd_trail (state S) = Propagated L E" and
    LE: "L \<in># E" and
    confl: "conflicting (state S) = Some D" and
    LD: "-L \<in># D" and
    lvl_max: "get_maximum_level (trail (state S)) ((remove1_mset (-L) D)) = backtrack_lvl (state S)" and
    T: "state T \<sim>m update_conflicting (Some (cdcl\<^sub>W_mset.resolve_cls L D E)) (tl_trail (state S))"
    by (auto elim!: cdcl\<^sub>W_mset.resolveE)
  obtain E' where
    hd': "hd_raw_conc_trail S = Propagated L E'" and
    [simp]: "E = mset_cls E'"
    apply (cases "hd_raw_conc_trail S")
    using hd_raw_conc_trail[of S] tr hd by simp_all
  obtain D' where
    confl': "raw_conc_conflicting S = Some D'" and
    [simp]: "D = mset_ccls D'"
    using confl by auto
  show ?abs
    apply (rule resolve_abs_rule)
          using tr apply simp
         using hd' apply simp
        using LE apply simp
       using confl' apply simp
      using LD apply simp
     using lvl_max apply simp
    using T by simp
next
  assume ?abs
  then show ?conc
    using hd_raw_conc_trail[of S] by (auto elim!: resolve_absE intro!: cdcl\<^sub>W_mset.resolve_rule)
qed

lemma compatible_relation_tranclp_compatible:
  fixes R :: "'v cdcl\<^sub>W_mset \<Rightarrow> 'v cdcl\<^sub>W_mset \<Rightarrow> bool" and
    R' :: "'st \<Rightarrow> 'st \<Rightarrow> bool" and
    S :: 'st
  assumes
    H: "\<And>S S' T. S \<sim>m state S' \<Longrightarrow> R S T \<Longrightarrow> \<exists>U. R' S' U \<and> T \<sim>m state U" and
    R: "R\<^sup>+\<^sup>+ (state S) T"
  shows "\<exists>U. R'\<^sup>+\<^sup>+ S U \<and> T \<sim>m state U"
  using R
proof (induction rule: tranclp_induct)
  case (base T)
  then show ?case
    using H[of "state S" S T] by auto
next
  case (step T U) note st = this(1) and R = this(2) and IH = this(3)
  obtain V where
    SV: "R'\<^sup>+\<^sup>+ S V" and TV: "T \<sim>m state V"
    using IH by auto
  then obtain W where
    VW: "R' V W" and UW: "U \<sim>m state W"
    using H[OF TV R] by blast
  have "R'\<^sup>+\<^sup>+ S W"
    using SV VW by auto
  then show ?case using UW by blast
qed

lemma resolve_exists_resolve_abs:
  assumes
    res: "cdcl\<^sub>W_mset.resolve S T" and
    SS': "S \<sim>m state S'"
  obtains U where "resolve_abs S' U" and "T \<sim>m state U"
proof -
  obtain L E D where
    tr: "trail S \<noteq> []" and
    hd: "cdcl\<^sub>W_mset.hd_trail S = Propagated L E" and
    LE: "L \<in># E" and
    confl: "conflicting S = Some D" and
    LD: "-L \<in># D" and
    lvl_max: "get_maximum_level (trail S) ((remove1_mset (-L) D)) = backtrack_lvl S" and
    T: "T \<sim>m update_conflicting (Some (cdcl\<^sub>W_mset.resolve_cls L D E)) (tl_trail S)"
    using res
    by (auto elim!: cdcl\<^sub>W_mset.resolveE)
  obtain E' where
    hd': "hd_raw_conc_trail S' = Propagated L E'" and
    [simp]: "E = mset_cls E'"
    apply (cases "hd_raw_conc_trail S'")
    using hd_raw_conc_trail[of S'] tr hd SS' by simp_all
  obtain D' where
    confl': "raw_conc_conflicting S' = Some D'" and
    [simp]: "D = mset_ccls D'"
    using confl SS' by auto
  let ?U = "(update_conc_conflicting (Some (resolve_cls L D' E')) (tl_conc_trail S'))"
  have "resolve_abs S' ?U"
    apply (rule resolve_abs_rule)
          using tr SS' apply simp
         using hd' apply simp
        using LE apply simp
       using confl' apply simp
      using LD apply simp
     using lvl_max SS' apply simp
    using T by simp
  moreover have "T \<sim>m state ?U"
    using T SS' unfolding cdcl\<^sub>W_mset.state_eq_def by auto
  ultimately show thesis using that[of ?U] by fast
qed

lemma tranclp_resolve_resolve:
  "cdcl\<^sub>W_mset.resolve\<^sup>+\<^sup>+ (state S) T \<Longrightarrow> \<exists>U. resolve_abs\<^sup>+\<^sup>+ S U \<and> T \<sim>m state U"
  apply (rule compatible_relation_tranclp_compatible[of cdcl\<^sub>W_mset.resolve])
    using resolve_exists_resolve_abs apply metis
  apply simp
  done

lemma no_step_resolve_no_step_resolve_abs:
  "no_step cdcl\<^sub>W_mset.resolve (state S) \<longleftrightarrow> no_step resolve_abs S"
  apply (rule iffI)
  using resolve_resolve_abs[symmetric] apply fast
  by (auto dest: resolve_exists_resolve_abs)

inductive restart :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
restart: "conc_conflicting S = None \<Longrightarrow>
  \<not>conc_trail S \<Turnstile>asm conc_clauses S \<Longrightarrow>
  T \<sim> restart_state S \<Longrightarrow>
  restart S T"

inductive_cases restartE: "restart S T"

text \<open>We add the condition @{term "C \<notin># conc_init_clss S"}, to maintain consistency even without the
  strategy.\<close>
inductive forget :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
forget_rule:
  "conc_conflicting S = None \<Longrightarrow>
  C !\<in>! raw_conc_learned_clss S \<Longrightarrow>
  \<not>(conc_trail S) \<Turnstile>asm clauses S \<Longrightarrow>
  mset_cls C \<notin> set (get_all_mark_of_propagated (conc_trail S)) \<Longrightarrow>
  mset_cls C \<notin># conc_init_clss S \<Longrightarrow>
  T \<sim> remove_cls C S \<Longrightarrow>
  forget S T"

inductive_cases forgetE: "forget S T"

inductive cdcl\<^sub>W_abs_rf :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
restart: "restart_abs S T \<Longrightarrow> cdcl\<^sub>W_abs_rf S T" |
forget: "forget_abs S T \<Longrightarrow> cdcl\<^sub>W_abs_rf S T"

inductive cdcl\<^sub>W_abs_bj :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
skip: "skip_abs S S' \<Longrightarrow> cdcl\<^sub>W_abs_bj S S'" |
resolve: "resolve_abs S S' \<Longrightarrow> cdcl\<^sub>W_abs_bj S S'" |
backtrack: "backtrack_abs S S' \<Longrightarrow> cdcl\<^sub>W_abs_bj S S'"

inductive_cases cdcl\<^sub>W_abs_bjE: "cdcl\<^sub>W_abs_bj S T"

inductive cdcl\<^sub>W_abs_o :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
decide: "decide_abs S S' \<Longrightarrow> cdcl\<^sub>W_abs_o S S'" |
bj: "cdcl\<^sub>W_abs_bj S S' \<Longrightarrow> cdcl\<^sub>W_abs_o S S'"

inductive cdcl\<^sub>W_abs :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
propagate: "propagate_abs S S' \<Longrightarrow> cdcl\<^sub>W_abs S S'" |
conflict: "conflict_abs S S' \<Longrightarrow> cdcl\<^sub>W_abs S S'" |
other: "cdcl\<^sub>W_o S S' \<Longrightarrow> cdcl\<^sub>W_abs S S'"|
rf: "cdcl\<^sub>W_rf S S' \<Longrightarrow> cdcl\<^sub>W_abs S S'"

subsection \<open>Higher level strategy\<close>

text \<open>The rules described previously do not lead to a conclusive state. We have to add a strategy.\<close>

subsubsection \<open>Definition\<close>

inductive cdcl\<^sub>W_abs_cp :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
conflict'[intro]: "conflict_abs S S' \<Longrightarrow> cdcl\<^sub>W_abs_cp S S'" |
propagate': "propagate_abs S S' \<Longrightarrow> cdcl\<^sub>W_abs_cp S S'"

lemma cdcl\<^sub>W_cp_cdcl\<^sub>W_abs_cp:
  "cdcl\<^sub>W_mset.cdcl\<^sub>W_cp (state S) (state T) \<longleftrightarrow> cdcl\<^sub>W_abs_cp S T"
  by (auto simp: cdcl\<^sub>W_mset.cdcl\<^sub>W_cp.simps cdcl\<^sub>W_abs_cp.simps
    conflict_conflict_abs propagate_propagate_abs)

lemma tranclp_cdcl\<^sub>W_cp_tranclp_cdcl\<^sub>W_abs_cp:
  assumes abs: "cdcl\<^sub>W_abs_cp\<^sup>+\<^sup>+ S T"
  shows "cdcl\<^sub>W_mset.cdcl\<^sub>W_cp\<^sup>+\<^sup>+ (state S) (state T)"
  using abs
  apply (induction)
    apply (auto simp: cdcl\<^sub>W_cp_cdcl\<^sub>W_abs_cp intro!: Transitive_Closure.tranclp.r_into_trancl)[]
  apply (erule tranclp.intros(2))
  apply (auto simp: cdcl\<^sub>W_cp_cdcl\<^sub>W_abs_cp
    intro: cdcl\<^sub>W_abs_cp.intros)[]
  done

lemma no_step_cdcl\<^sub>W_cp_no_step_cdcl\<^sub>W_abs_cp:
  assumes abs: "no_step cdcl\<^sub>W_abs_cp S"
  shows "no_step cdcl\<^sub>W_mset.cdcl\<^sub>W_cp (state S)"
proof -
  have "no_step conflict_abs S" and "no_step propagate_abs S"
    using abs by (auto simp: cdcl\<^sub>W_abs_cp.simps)
  then have "no_step cdcl\<^sub>W_mset.conflict (state S)" and "no_step cdcl\<^sub>W_mset.propagate (state S)"
    using no_step_conflict_no_step_conflict_abs no_step_propagate_no_step_propagate_abs by blast+
  then show ?thesis
    by (auto simp: cdcl\<^sub>W_mset.cdcl\<^sub>W_cp.simps)
qed

lemma full1_cdcl\<^sub>W_abs_cp_full1_cdcl\<^sub>W_cp:
  "full1 cdcl\<^sub>W_abs_cp S T \<Longrightarrow> full1 cdcl\<^sub>W_mset.cdcl\<^sub>W_cp (state S) (state T)"
  unfolding full1_def by (simp add: tranclp_cdcl\<^sub>W_cp_tranclp_cdcl\<^sub>W_abs_cp
    no_step_cdcl\<^sub>W_cp_no_step_cdcl\<^sub>W_abs_cp)

inductive cdcl\<^sub>W_abs_stgy :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
conflict': "full1 cdcl\<^sub>W_abs_cp S S' \<Longrightarrow> cdcl\<^sub>W_abs_stgy S S'" |
other': "cdcl\<^sub>W_abs_o S S' \<Longrightarrow> no_step cdcl\<^sub>W_abs_cp S \<Longrightarrow> full cdcl\<^sub>W_abs_cp S' S'' \<Longrightarrow> cdcl\<^sub>W_abs_stgy S S''"

lemma cdcl\<^sub>W_cp_cdcl\<^sub>W_abs_cp:
  "cdcl\<^sub>W_mset.cdcl\<^sub>W_stgy (state S) (state T) \<longleftrightarrow> cdcl\<^sub>W_abs_stgy S T"
  apply (auto simp: cdcl\<^sub>W_cp_cdcl\<^sub>W_abs_cp cdcl\<^sub>W_mset.cdcl\<^sub>W_stgy.simps cdcl\<^sub>W_abs_stgy.simps
    conflict_conflict_abs propagate_propagate_abs)
oops




subsubsection \<open>Invariants\<close>
text \<open>These are the same invariants as before, but lifted\<close>
lemma cdcl\<^sub>W_cp_learned_clause_inv:
  assumes "cdcl\<^sub>W_cp S S'"
  shows "conc_learned_clss S = conc_learned_clss S'"
  using assms by (induct rule: cdcl\<^sub>W_cp.induct) (fastforce elim: conflictE propagateE)+

lemma rtranclp_cdcl\<^sub>W_cp_learned_clause_inv:
  assumes "cdcl\<^sub>W_cp\<^sup>*\<^sup>* S S'"
  shows "conc_learned_clss S = conc_learned_clss S'"
  using assms by (induct rule: rtranclp_induct) (fastforce dest: cdcl\<^sub>W_cp_learned_clause_inv)+

lemma tranclp_cdcl\<^sub>W_cp_learned_clause_inv:
  assumes "cdcl\<^sub>W_cp\<^sup>+\<^sup>+ S S'"
  shows "conc_learned_clss S = conc_learned_clss S'"
  using assms by (simp add: rtranclp_cdcl\<^sub>W_cp_learned_clause_inv tranclp_into_rtranclp)

lemma cdcl\<^sub>W_cp_conc_backtrack_lvl:
  assumes "cdcl\<^sub>W_cp S S'"
  shows "conc_backtrack_lvl S = conc_backtrack_lvl S'"
  using assms by (induct rule: cdcl\<^sub>W_cp.induct) (fastforce elim: conflictE propagateE)+

lemma rtranclp_cdcl\<^sub>W_cp_conc_backtrack_lvl:
  assumes "cdcl\<^sub>W_cp\<^sup>*\<^sup>* S S'"
  shows "conc_backtrack_lvl S = conc_backtrack_lvl S'"
  using assms by (induct rule: rtranclp_induct) (fastforce dest: cdcl\<^sub>W_cp_conc_backtrack_lvl)+

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

lemma cdcl\<^sub>W_cp_no_more_conc_init_clss:
  assumes "cdcl\<^sub>W_cp S S'"
  shows "conc_init_clss S = conc_init_clss S'"
  using assms by (induct rule: cdcl\<^sub>W_cp.induct) (auto elim: conflictE propagateE)

lemma tranclp_cdcl\<^sub>W_cp_no_more_conc_init_clss:
  assumes "cdcl\<^sub>W_cp\<^sup>+\<^sup>+ S S'"
  shows "conc_init_clss S = conc_init_clss S'"
  using assms by (induct rule: tranclp.induct) (auto dest: cdcl\<^sub>W_cp_no_more_conc_init_clss)

lemma cdcl\<^sub>W_stgy_no_more_conc_init_clss:
  assumes "cdcl\<^sub>W_stgy S S'" and "cdcl\<^sub>W_M_level_inv S"
  shows "conc_init_clss S = conc_init_clss S'"
  using assms
  apply (induct rule: cdcl\<^sub>W_stgy.induct)
  unfolding full1_def full_def apply (blast dest: tranclp_cdcl\<^sub>W_cp_no_more_conc_init_clss
    tranclp_cdcl\<^sub>W_o_no_more_conc_init_clss)
  by (metis cdcl\<^sub>W_o_no_more_conc_init_clss rtranclp_unfold tranclp_cdcl\<^sub>W_cp_no_more_conc_init_clss)

lemma rtranclp_cdcl\<^sub>W_stgy_no_more_conc_init_clss:
  assumes "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S S'" and "cdcl\<^sub>W_M_level_inv S"
  shows "conc_init_clss S = conc_init_clss S'"
  using assms
  apply (induct rule: rtranclp_induct, simp)
  using cdcl\<^sub>W_stgy_no_more_conc_init_clss by (simp add: rtranclp_cdcl\<^sub>W_stgy_consistent_inv)

lemma cdcl\<^sub>W_cp_dropWhile_conc_trail':
  assumes "cdcl\<^sub>W_cp S S'"
  obtains M where "conc_trail S' = M @ conc_trail S" and " (\<forall>l \<in> set M. \<not>is_decided l)"
  using assms by induction (fastforce elim: conflictE propagateE)+

lemma rtranclp_cdcl\<^sub>W_cp_dropWhile_conc_trail':
  assumes "cdcl\<^sub>W_cp\<^sup>*\<^sup>* S S'"
  obtains M :: "('v, 'v clause) ann_lits" where
    "conc_trail S' = M @ conc_trail S" and "\<forall>l \<in> set M. \<not>is_decided l"
  using assms by induction (fastforce dest!: cdcl\<^sub>W_cp_dropWhile_conc_trail')+

lemma cdcl\<^sub>W_cp_dropWhile_conc_trail:
  assumes "cdcl\<^sub>W_cp S S'"
  shows "\<exists>M. conc_trail S' = M @ conc_trail S \<and> (\<forall>l \<in> set M. \<not>is_decided l)"
  using assms by induction (fastforce elim: conflictE propagateE)+

lemma rtranclp_cdcl\<^sub>W_cp_dropWhile_conc_trail:
  assumes "cdcl\<^sub>W_cp\<^sup>*\<^sup>* S S'"
  shows "\<exists>M. conc_trail S' = M @ conc_trail S \<and> (\<forall>l \<in> set M. \<not>is_decided l)"
  using assms by induction (fastforce dest: cdcl\<^sub>W_cp_dropWhile_conc_trail)+

text \<open>This theorem can be seen a a termination theorem for @{term cdcl\<^sub>W_cp}.\<close>
lemma length_model_le_vars:
  assumes
    "no_strange_atm S" and
    no_d: "no_dup (conc_trail S)" and
    "finite (atms_of_mm (conc_init_clss S))"
  shows "length (conc_trail S) \<le> card (atms_of_mm (conc_init_clss S))"
proof -
  obtain M N U k D where S: "state S = (M, N, U, k, D)" by (cases "state S", auto)
  have "finite (atm_of ` lits_of_l (conc_trail S))"
    using assms(1,3) unfolding S by (auto simp add: finite_subset)
  have "length (conc_trail S) = card (atm_of ` lits_of_l (conc_trail S))"
    using no_dup_length_eq_card_atm_of_lits_of_l no_d by blast
  then show ?thesis using assms(1) unfolding no_strange_atm_def
  by (auto simp add: assms(3) card_mono)
qed

lemma cdcl\<^sub>W_cp_decreasing_measure:
  assumes
    cdcl\<^sub>W: "cdcl\<^sub>W_cp S T" and
    M_lev: "cdcl\<^sub>W_M_level_inv S" and
    alien: "no_strange_atm S"
  shows "(\<lambda>S. card (atms_of_mm (conc_init_clss S)) - length (conc_trail S)
      + (if conc_conflicting S = None then 1 else 0)) S
    > (\<lambda>S. card (atms_of_mm (conc_init_clss S)) - length (conc_trail S)
      + (if conc_conflicting S = None then 1 else 0)) T"
  using assms
proof -
  have "length (conc_trail T) \<le> card (atms_of_mm (conc_init_clss T))"
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
      "(\<lambda>S. card (atms_of_mm (conc_init_clss S)) - length (conc_trail S)
        + (if conc_conflicting S = None then 1 else 0))"])
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
        by (metis rtranclp_unfold cdcl\<^sub>W_cp_conc_conflicting_not_empty cp st
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
proof (induct "card (atms_of_mm (conc_init_clss S) - atm_of `lits_of_l (conc_trail S))" arbitrary: S)
  case 0 note card = this(1) and alien = this(2)
  then have atm: "atms_of_mm (conc_init_clss S) = atm_of ` lits_of_l (conc_trail S)"
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
      S: "conc_conflicting S = None" and
      E: "E !\<in>! raw_clauses S" and
      LE: "L \<in># mset_cls E" and
      tr: "conc_trail S \<Turnstile>as CNot (mset_cls E - {#L#})" and
      undef: "undefined_lit (conc_trail S) L" and
      S': "S' \<sim> cons_conc_trail (Propagated L E) S"
      by (elim propagateE) simp
    have "atms_of_mm (conc_learned_clss S) \<subseteq> atms_of_mm (conc_init_clss S)"
      using alien S unfolding no_strange_atm_def by auto
    then have "atm_of L \<in> atms_of_mm (conc_init_clss S)"
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
    then have ?case unfolding full_def Ex_def using S' cdcl\<^sub>W_cp.conflict' by blast
  }
  moreover {
    assume a: "\<exists>S'. propagate S S'"
    then obtain S' where propagate: "propagate S S'" by blast
    then obtain E L where
      S: "conc_conflicting S = None" and
      E: "E !\<in>! raw_clauses S" and
      LE: "L \<in># mset_cls E" and
      tr: "conc_trail S \<Turnstile>as CNot (mset_cls E - {#L#})" and
      undef: "undefined_lit (conc_trail S) L" and
      S': "S' \<sim> cons_conc_trail (Propagated L E) S"
      by (elim propagateE) simp
    then have "atm_of L \<notin> atm_of ` lits_of_l (conc_trail S)"
      unfolding lits_of_def by (auto simp add: defined_lit_map)
    moreover
      have "no_strange_atm S'" using alien propagate propagate_no_strange_atm_inv by blast
      then have "atm_of L \<in> atms_of_mm (conc_init_clss S)"
        using S' LE E undef unfolding no_strange_atm_def
        by (auto simp: raw_clauses_def in_implies_atm_of_on_atms_of_ms)
      then have "\<And>A. {atm_of L} \<subseteq> atms_of_mm (conc_init_clss S) - A \<or> atm_of L \<in> A" by force
    moreover have "Suc n - card {atm_of L} = n" by simp
    moreover have "card (atms_of_mm (conc_init_clss S) - atm_of ` lits_of_l (conc_trail S)) = Suc n"
     using card S S' by simp
    ultimately
      have "card (atms_of_mm (conc_init_clss S) - atm_of ` insert L (lits_of_l (conc_trail S))) = n"
        by (metis (no_types) Diff_insert card_Diff_subset finite.emptyI finite.insertI image_insert)
      then have "n = card (atms_of_mm (conc_init_clss S') - atm_of ` lits_of_l (conc_trail S'))"
        using card S S' undef by simp
    then have a1: "Ex (full cdcl\<^sub>W_cp S')" using IH \<open>no_strange_atm S'\<close> by blast
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

subsubsection \<open>Literal of highest level in conc_conflicting clauses\<close>
text \<open>One important property of the @{term cdcl\<^sub>W} with strategy is that, whenever a conflict takes
  place, there is at least a literal of level k involved (except if we have derived the false
  clause). The reason is that we apply conflicts before a decision is taken.\<close>
abbreviation no_clause_is_false :: "'st \<Rightarrow> bool" where
"no_clause_is_false \<equiv>
  \<lambda>S. (conc_conflicting S = None \<longrightarrow> (\<forall>D \<in># clauses S. \<not>conc_trail S \<Turnstile>as CNot D))"

abbreviation conflict_is_false_with_level :: "'st \<Rightarrow> bool" where
"conflict_is_false_with_level S \<equiv> \<forall>D. conc_conflicting S = Some D \<longrightarrow> D \<noteq> {#}
  \<longrightarrow> (\<exists>L \<in># D. get_level (conc_trail S) L = conc_backtrack_lvl S)"

lemma not_conflict_not_any_negated_conc_init_clss:
  assumes "\<forall> S'. \<not>conflict S S'"
  shows "no_clause_is_false S"
proof (clarify)
  fix D
  assume "D \<in># local.clauses S" and "raw_conc_conflicting S = None" and "conc_trail S \<Turnstile>as CNot D "
  moreover then obtain D' where
    "mset_cls D' = D" and
    "D' !\<in>! raw_clauses S"
    using in_mset_clss_exists_preimage unfolding raw_clauses_def by blast
  ultimately show False
    using conflict_rule[of S D' "update_conc_conflicting (Some (ccls_of_cls D')) S"] assms
    by auto
qed

lemma full_cdcl\<^sub>W_cp_not_any_negated_conc_init_clss:
  assumes "full cdcl\<^sub>W_cp S S'"
  shows "no_clause_is_false S'"
  using assms not_conflict_not_any_negated_conc_init_clss unfolding full_def by auto

lemma full1_cdcl\<^sub>W_cp_not_any_negated_conc_init_clss:
  assumes "full1 cdcl\<^sub>W_cp S S'"
  shows "no_clause_is_false S'"
  using assms not_conflict_not_any_negated_conc_init_clss unfolding full1_def by auto

lemma cdcl\<^sub>W_stgy_not_non_negated_conc_init_clss:
  assumes "cdcl\<^sub>W_stgy S S'"
  shows "no_clause_is_false S'"
  using assms apply (induct rule: cdcl\<^sub>W_stgy.induct)
  using full1_cdcl\<^sub>W_cp_not_any_negated_conc_init_clss full_cdcl\<^sub>W_cp_not_any_negated_conc_init_clss by metis+

lemma rtranclp_cdcl\<^sub>W_stgy_not_non_negated_conc_init_clss:
  assumes "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S S'" and "no_clause_is_false S"
  shows "no_clause_is_false S'"
  using assms by (induct rule: rtranclp_induct) (auto simp: cdcl\<^sub>W_stgy_not_non_negated_conc_init_clss)

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
  by (metis conc_conflicting_update_conc_conflicting option.distinct(1) option.simps(9) state_eq_conc_conflicting)

lemma rtranclp_cdcl\<^sub>W_cp_propa_or_propa_confl:
  assumes "cdcl\<^sub>W_cp\<^sup>*\<^sup>* S U"
  shows "propagate\<^sup>*\<^sup>* S U \<or> (\<exists>T. propagate\<^sup>*\<^sup>* S T \<and> conflict T U)"
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
    confl: "conc_conflicting U = Some D" and
    D: "D \<noteq> {#}"
  consider (CT) "conc_conflicting S = None" | (SD) D' where "conc_conflicting S = Some D'"
    by (cases "conc_conflicting S") auto
  then show "\<exists>L\<in>#D. get_level (conc_trail U) L = conc_backtrack_lvl U"
    proof cases
      case SD
      then have "S = U"
        by (metis (no_types) assms(1) cdcl\<^sub>W_cp_conc_conflicting_not_empty full_def rtranclpD tranclpD)
      then show ?thesis using assms(3) confl D by blast-
    next
      case CT
      have "conc_init_clss U = conc_init_clss S" and "conc_learned_clss U = conc_learned_clss S"
        using full unfolding full_def
          apply (metis (no_types) rtranclpD tranclp_cdcl\<^sub>W_cp_no_more_conc_init_clss)
        by (metis (mono_tags, lifting) full full_def rtranclp_cdcl\<^sub>W_cp_learned_clause_inv)
      obtain T where "propagate\<^sup>*\<^sup>* S T" and TU: "conflict T U"
        proof -
          have f5: "U \<noteq> S"
            using confl CT by force
          then have "cdcl\<^sub>W_cp\<^sup>+\<^sup>+ S U"
            by (metis full full_def rtranclpD)
          have "\<And>p pa. \<not> propagate p pa \<or> conc_conflicting pa =
            (None :: 'v clause option)"
            by (auto elim: propagateE)
          then show ?thesis
            using f5 that tranclp_cdcl\<^sub>W_cp_propagate_with_conflict_or_not[OF \<open>cdcl\<^sub>W_cp\<^sup>+\<^sup>+ S U\<close>]
            full confl CT unfolding full_def by auto
        qed
      obtain D' where
        "raw_conc_conflicting T = None" and
        D': "D' !\<in>! raw_clauses T" and
        tr: "conc_trail T \<Turnstile>as CNot (mset_cls D')" and
        U: "U \<sim> update_conc_conflicting (Some (ccls_of_cls D')) T"
        using TU by (auto elim!: conflictE)
      have "conc_init_clss T = conc_init_clss S" and "conc_learned_clss T = conc_learned_clss S"
        using U \<open>conc_init_clss U = conc_init_clss S\<close> \<open>conc_learned_clss U = conc_learned_clss S\<close> by auto
      then have "D \<in># clauses S"
        using confl U D' by (auto simp: raw_clauses_def)
      then have "\<not> conc_trail S \<Turnstile>as CNot D"
        using cls_f CT by simp

      moreover
        obtain M where tr_U: "conc_trail U = M @ conc_trail S" and nm: "\<forall>m\<in>set M. \<not>is_decided m"
          by (metis (mono_tags, lifting) assms(1) full_def rtranclp_cdcl\<^sub>W_cp_dropWhile_conc_trail)
        have "conc_trail U \<Turnstile>as CNot D"
          using tr confl U by (auto elim!: conflictE)
      ultimately obtain L where "L \<in># D" and "-L \<in> lits_of_l M"
        unfolding tr_U CNot_def true_annots_def Ball_def true_annot_def true_cls_def by force

      moreover have inv_U: "cdcl\<^sub>W_M_level_inv U"
        by (metis cdcl\<^sub>W_stgy.conflict' cdcl\<^sub>W_stgy_consistent_inv full full_unfold lev)
      moreover
        have "conc_backtrack_lvl U = conc_backtrack_lvl S"
          using full unfolding full_def by (auto dest: rtranclp_cdcl\<^sub>W_cp_conc_backtrack_lvl)

      moreover
        have "no_dup (conc_trail U)"
          using inv_U unfolding cdcl\<^sub>W_M_level_inv_def by auto
        { fix x :: "('v, 'v clause) ann_lit" and
            xb :: "('v, 'v clause) ann_lit"
          assume a1: "atm_of L = atm_of (lit_of xb)"
          moreover assume a2: "- L = lit_of x"
          moreover assume a3: "(\<lambda>l. atm_of (lit_of l)) ` set M
            \<inter> (\<lambda>l. atm_of (lit_of l)) ` set (conc_trail S) = {}"
          moreover assume a4: "x \<in> set M"
          moreover assume a5: "xb \<in> set (conc_trail S)"
          moreover have "atm_of (- L) = atm_of L"
            by auto
          ultimately have False
            by auto
         }
        then have LS: "atm_of L \<notin> atm_of ` lits_of_l (conc_trail S)"
          using \<open>-L \<in> lits_of_l M\<close> \<open>no_dup (conc_trail U)\<close> unfolding tr_U lits_of_def by auto
      ultimately have "get_level (conc_trail U) L = conc_backtrack_lvl U"
        proof (cases "count_decided (conc_trail S) \<noteq> 0", goal_cases)
          case 2 note LD = this(1) and LM = this(2) and inv_U = this(3) and US = this(4) and
            LS = this(5) and ne = this(6)
          have "conc_backtrack_lvl S = 0"
            using lev ne unfolding cdcl\<^sub>W_M_level_inv_def by auto
          moreover have "get_level M L = 0"
            using nm by auto
          ultimately show ?thesis using LS ne US unfolding tr_U
            by (simp add: lits_of_def filter_empty_conv)
        next
          case 1 note LD = this(1) and LM = this(2) and inv_U = this(3) and US = this(4) and
            LS = this(5) and ne = this(6)

          have "count_decided (conc_trail S) = conc_backtrack_lvl S"
            using ne lev unfolding cdcl\<^sub>W_M_level_inv_def by auto
          moreover have "atm_of L \<in> atm_of ` lits_of_l M "
            using \<open>-L \<in> lits_of_l M\<close> by (simp add: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
              lits_of_def)
          ultimately show ?thesis
            using nm ne get_level_skip_in_all_not_decided[of M L] unfolding lits_of_def US tr_U
            by auto
          qed
      then show "\<exists>L\<in>#D. get_level (conc_trail U) L = conc_backtrack_lvl U"
        using \<open>L \<in># D\<close> by blast
    qed
qed

subsubsection \<open>Literal of highest level in decided literals\<close>
definition mark_is_false_with_level :: "'st \<Rightarrow> bool" where
"mark_is_false_with_level S' \<equiv>
  \<forall>D M1 M2 L. M1 @ Propagated L D # M2 = conc_trail S' \<longrightarrow> D - {#L#} \<noteq> {#}
    \<longrightarrow> (\<exists>L. L \<in># D \<and> get_level (conc_trail S') L = count_decided M1)"

definition no_more_propagation_to_do :: "'st \<Rightarrow> bool" where
"no_more_propagation_to_do S \<equiv>
  \<forall>D M M' L. D + {#L#} \<in># clauses S \<longrightarrow> conc_trail S = M' @ M \<longrightarrow> M \<Turnstile>as CNot D
    \<longrightarrow> undefined_lit M L \<longrightarrow> count_decided M < conc_backtrack_lvl S
    \<longrightarrow> (\<exists>L. L \<in># D \<and> get_level (conc_trail S) L = count_decided M)"

lemma propagate_no_more_propagation_to_do:
  assumes propagate: "propagate S S'"
  and H: "no_more_propagation_to_do S"
  and lev_inv: "cdcl\<^sub>W_M_level_inv S"
  shows "no_more_propagation_to_do S'"
  using assms
proof -
  obtain E L where
    S: "conc_conflicting S = None" and
    E: "E !\<in>! raw_clauses S" and
    LE: "L \<in># mset_cls E" and
    tr: "conc_trail S \<Turnstile>as CNot (mset_cls E - {#L#})" and
    undefL: "undefined_lit (conc_trail S) L" and
    S': "S' \<sim> cons_conc_trail (Propagated L E) S"
    using propagate by (elim propagateE) simp
  let ?M' = "Propagated L (mset_cls E) # conc_trail S"
  show ?thesis unfolding no_more_propagation_to_do_def
    proof (intro allI impI)
      fix D M1 M2 L'
      assume
        D_L: "D + {#L'#} \<in># clauses S'" and
        "conc_trail S' = M2 @ M1" and
        get_max: "count_decided M1 < conc_backtrack_lvl S'" and
        "M1 \<Turnstile>as CNot D" and
        undef: "undefined_lit M1 L'"
      have "tl M2 @ M1 = conc_trail S \<or> (M2 = [] \<and> M1 = Propagated L (mset_cls E) # conc_trail S)"
        using \<open>conc_trail S' = M2 @ M1\<close> S' S undefL lev_inv
        by (cases M2) (auto simp:cdcl\<^sub>W_M_level_inv_decomp)
      moreover {
        assume "tl M2 @ M1 = conc_trail S"
        moreover have "D + {#L'#} \<in># clauses S"
          using D_L S S' undefL unfolding raw_clauses_def by auto
        moreover have "count_decided M1 < conc_backtrack_lvl S"
          using get_max S S' undefL by auto
        ultimately obtain L' where "L' \<in># D" and
          "get_level (conc_trail S) L' = count_decided M1"
          using H \<open>M1 \<Turnstile>as CNot D\<close> undef unfolding no_more_propagation_to_do_def by metis
        moreover
          { have "cdcl\<^sub>W_M_level_inv S'"
              using cdcl\<^sub>W_consistent_inv lev_inv cdcl\<^sub>W.propagate[OF propagate] by blast
            then have "no_dup ?M'" using S' undefL unfolding cdcl\<^sub>W_M_level_inv_def by auto
            moreover
              have "atm_of L' \<in> atm_of ` (lits_of_l M1)"
                using \<open>L' \<in># D\<close> \<open>M1 \<Turnstile>as CNot D\<close> by (metis atm_of_uminus image_eqI
                  in_CNot_implies_uminus(2))
              then have "atm_of L' \<in> atm_of ` (lits_of_l (conc_trail S))"
                using \<open>tl M2 @ M1 = conc_trail S\<close>[symmetric] S undefL by auto
            ultimately have "atm_of L \<noteq> atm_of L'" unfolding lits_of_def by auto
        }
        ultimately have "\<exists>L' \<in># D. get_level (conc_trail S') L' = count_decided M1"
          using S S' undefL by auto
      }
      moreover {
        assume "M2 = []" and M1: "M1 = Propagated L (mset_cls E) # conc_trail S"
        have "cdcl\<^sub>W_M_level_inv S'"
          using cdcl\<^sub>W_consistent_inv[OF _ lev_inv] cdcl\<^sub>W.propagate[OF propagate] by blast
        then have "count_decided M1 = conc_backtrack_lvl S'"
          using S' M1 undefL unfolding cdcl\<^sub>W_M_level_inv_def by (auto intro: Max_eqI)
        then have False using get_max by auto
      }
      ultimately show "\<exists>L. L \<in># D \<and> get_level (conc_trail S') L = count_decided M1"
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
    using propagate_no_more_propagation_to_do[of S S'] S by blast
qed

lemma cdcl\<^sub>W_then_exists_cdcl\<^sub>W_stgy_step:
  assumes
    o: "cdcl\<^sub>W_o S S'" and
    alien: "no_strange_atm S" and
    lev: "cdcl\<^sub>W_M_level_inv S"
  shows "\<exists>S'. cdcl\<^sub>W_stgy S S'"
proof -
  obtain S'' where "full cdcl\<^sub>W_cp S' S''"
    using always_exists_full_cdcl\<^sub>W_cp_step alien cdcl\<^sub>W_no_strange_atm_inv cdcl\<^sub>W_o_no_more_conc_init_clss
     o other lev by (meson cdcl\<^sub>W_consistent_inv)
  then show ?thesis
    using assms by (metis always_exists_full_cdcl\<^sub>W_cp_step cdcl\<^sub>W_stgy.conflict' full_unfold other')
qed

lemma backtrack_no_decomp:
  assumes
    S: "raw_conc_conflicting S = Some E" and
    LE: "L \<in># mset_ccls E" and
    L: "get_level (conc_trail S) L = conc_backtrack_lvl S" and
    D: "get_maximum_level (conc_trail S) (remove1_mset L (mset_ccls E)) < conc_backtrack_lvl S" and
    bt: "conc_backtrack_lvl S = get_maximum_level (conc_trail S) (mset_ccls E)" and
    M_L: "cdcl\<^sub>W_M_level_inv S"
  shows "\<exists>S'. cdcl\<^sub>W_o S S'"
proof -
  have L_D: "get_level (conc_trail S) L = get_maximum_level (conc_trail S) (mset_ccls E)"
    using L D bt by (simp add: get_maximum_level_plus)
  let ?i = "get_maximum_level (conc_trail S) (remove1_mset L (mset_ccls E))"
  obtain K M1 M2 where
    K: "(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (conc_trail S))" and
    lev_K: "get_level (conc_trail S) K = Suc ?i"
    using backtrack_ex_decomp[OF M_L, of ?i] D S by auto
  show ?thesis using backtrack_rule[OF S LE K L, of ?i] bt L lev_K bj by (auto simp: cdcl\<^sub>W_bj.simps)
qed

lemma cdcl\<^sub>W_stgy_final_state_conclusive:
  assumes
    termi: "\<forall>S'. \<not>cdcl\<^sub>W_stgy S S'" and
    decomp: "all_decomposition_implies_m (conc_init_clss S) (get_all_ann_decomposition (conc_trail S))" and
    learned: "cdcl\<^sub>W_learned_clause S" and
    level_inv: "cdcl\<^sub>W_M_level_inv S" and
    alien: "no_strange_atm S" and
    no_dup: "distinct_cdcl\<^sub>W_state S" and
    confl: "cdcl\<^sub>W_conc_conflicting S" and
    confl_k: "conflict_is_false_with_level S"
  shows "(conc_conflicting S = Some {#} \<and> unsatisfiable (set_mset (conc_init_clss S)))
         \<or> (conc_conflicting S = None \<and> conc_trail S \<Turnstile>as set_mset (conc_init_clss S))"
proof -
  let ?M = "conc_trail S"
  let ?N = "conc_init_clss S"
  let ?k = "conc_backtrack_lvl S"
  let ?U = "conc_learned_clss S"
  consider
      (None) "raw_conc_conflicting S = None"
    | (Some_Empty) E where "raw_conc_conflicting S = Some E" and "mset_ccls E = {#}"
    | (Some) E' where "raw_conc_conflicting S = Some E'" and
      "conc_conflicting S = Some (mset_ccls E')" and "mset_ccls E' \<noteq> {#}"
    by (cases "conc_conflicting S", simp) auto
  then show ?thesis
    proof cases
      case (Some_Empty E)
      then have "conc_conflicting S = Some {#}" by auto
      then have "unsatisfiable (set_mset (conc_init_clss S))"
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
                moreover have "conc_conflicting S = None"
                  using None by auto
                ultimately have "\<exists>S'. cdcl\<^sub>W_o S S'"
                  using cdcl\<^sub>W_o.decide decide_rule \<open>l \<in> ?B\<close> no_strange_atm_def
                  by (metis literal.sel(1) state_eq_def)
                then show False
                  using termi cdcl\<^sub>W_then_exists_cdcl\<^sub>W_stgy_step[OF _ alien] level_inv by blast
              qed
          qed
        obtain D where "\<not> ?M \<Turnstile>a D" and "D \<in># ?N"
           using \<open>\<not>?M \<Turnstile>asm ?N\<close> unfolding lits_of_def true_annots_def Ball_def by auto
        have "atms_of D \<subseteq> atm_of ` (lits_of_l ?M)"
          using \<open>D \<in># ?N\<close> unfolding \<open>atm_of ` (lits_of_l ?M) = atms_of_mm ?N\<close> atms_of_ms_def
          by (auto simp add: atms_of_def)
        then have a1: "atm_of ` set_mset D \<subseteq> atm_of ` lits_of_l (conc_trail S)"
          by (auto simp add: atms_of_def lits_of_def)
        have "total_over_m (lits_of_l ?M) {D}"
          using \<open>atms_of D \<subseteq> atm_of ` (lits_of_l ?M)\<close>
          atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set by (fastforce simp: total_over_set_def)
        then have "?M \<Turnstile>as CNot D"
          using total_not_true_cls_true_clss_CNot \<open>\<not> conc_trail S \<Turnstile>a D\<close> true_annot_def
          true_annots_true_cls by fastforce
        then have False
          proof -
            obtain S' where
              f2: "full cdcl\<^sub>W_cp S S'"
              by (meson alien always_exists_full_cdcl\<^sub>W_cp_step level_inv)
            then have "S' = S"
              using cdcl\<^sub>W_stgy.conflict'[of S] by (metis (no_types) full_unfold termi)
            then show ?thesis
              using f2 \<open>D \<in># conc_init_clss S\<close> None \<open>conc_trail S \<Turnstile>as CNot D\<close>
              raw_clauses_def full_cdcl\<^sub>W_cp_not_any_negated_conc_init_clss by auto
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
      have "?M \<Turnstile>as CNot ?D" using confl LD unfolding cdcl\<^sub>W_conc_conflicting_def by auto
      then have "?M \<noteq> []" unfolding true_annots_def Ball_def true_annot_def true_cls_def by force
      have M: "?M = hd ?M # tl ?M" using \<open>?M \<noteq> []\<close> list.collapse by fastforce

      have g_k: "get_maximum_level (conc_trail S) D \<le> ?k"
        using count_decided_ge_get_maximum_level[of ?M] level_inv
        unfolding cdcl\<^sub>W_M_level_inv_def
        by auto
      {
        assume decided: "is_decided (hd ?M)"
        then obtain k' where k': "k' + 1 = ?k"
          using level_inv M unfolding cdcl\<^sub>W_M_level_inv_def
          by (cases "hd (conc_trail S)"; cases "conc_trail S") auto
        obtain L' where L': "hd ?M = Decided L'" using decided by (cases "hd ?M") auto
        have *: "\<And>list. no_dup list \<Longrightarrow>
              - L \<in> lits_of_l list \<Longrightarrow> atm_of L \<in> atm_of ` lits_of_l list"
          by (metis atm_of_uminus imageI)
        have L'_L: "L' = -L"
          proof (rule ccontr)
            assume "\<not> ?thesis"
            moreover have "-L \<in> lits_of_l ?M" using confl LD unfolding cdcl\<^sub>W_conc_conflicting_def by auto
            ultimately have "get_level (hd (conc_trail S) # tl (conc_trail S)) L = get_level (tl ?M) L"
              using cdcl\<^sub>W_M_level_inv_decomp(1)[OF level_inv] unfolding consistent_interp_def
              by (subst (asm) (2) M) (auto simp add: atm_of_eq_atm_of L')
            moreover
              have "count_decided (conc_trail S) = ?k"
                using level_inv unfolding cdcl\<^sub>W_M_level_inv_def by auto
              then have count: "count_decided (tl (conc_trail S)) = ?k - 1"
                using level_inv unfolding cdcl\<^sub>W_M_level_inv_def
                by (subst (asm) M) (auto simp add: L')
              then have "get_level (tl ?M) L < ?k"
                using count_decided_ge_get_level[of L "tl ?M"] unfolding count k'[symmetric]
                by auto
            finally show False using lev_L M by auto
          qed
        have L: "hd ?M = Decided (-L)" using L'_L L' by auto

        have "get_maximum_level (conc_trail S) D < ?k"
          proof (rule ccontr)
            assume "\<not> ?thesis"
            then have "get_maximum_level (conc_trail S) D = ?k" using M g_k unfolding L by auto
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
                  have d: "dropWhile (\<lambda>S. atm_of (lit_of S) \<noteq> atm_of L) (tl (conc_trail S)) = []"
                    using level_inv unfolding cdcl\<^sub>W_M_level_inv_def apply (subst (asm)(2) M)
                    by (auto simp: image_iff L' L'_L)
                  have "get_level (tl (conc_trail S)) L = 0"
                    by (auto simp: filter_empty_conv d)
                moreover
                  have "get_level (tl (conc_trail S)) L'' \<le> count_decided (tl (conc_trail S))"
                    by auto
                  then have "get_level (tl (conc_trail S)) L'' < conc_backtrack_lvl S"
                    using level_inv unfolding cdcl\<^sub>W_M_level_inv_def apply (subst (asm)(5) M)
                    by (auto simp: image_iff L' L'_L simp del: count_decided_ge_get_level)
                ultimately show False
                  apply -
                  apply (subst (asm) M, subst (asm)(3) M, subst (asm) L')
                  using L_k
                  apply (auto simp: L' L'_L split: if_splits)
                  apply (subst (asm)(3) M, subst (asm) L')
                  using \<open>L'' \<noteq> - L\<close> by (auto simp: L' L'_L split: if_splits)
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
              using confl no_dup LD unfolding cdcl\<^sub>W_conc_conflicting_def by auto
            ultimately show False by blast
          qed note H = this
        have "get_maximum_level (conc_trail S) D < get_maximum_level (conc_trail S) (D + {#L#})"
          using H by (auto simp: get_maximum_level_plus lev_L max_def)
        moreover have "conc_backtrack_lvl S = get_maximum_level (conc_trail S) (D + {#L#})"
          using H by (auto simp: get_maximum_level_plus lev_L max_def)
        ultimately have False
          using backtrack_no_decomp[OF raw_conf _ lev_L] level_inv termi
          cdcl\<^sub>W_then_exists_cdcl\<^sub>W_stgy_step[of S] alien unfolding E'
          by (auto simp add: lev_L max_def)
      } note not_is_decided = this

      moreover {
        let ?D = "D + {#L#}"
        have "?D \<noteq> {#}" by auto
        have "?M \<Turnstile>as CNot ?D" using confl LD unfolding cdcl\<^sub>W_conc_conflicting_def by auto
        then have "?M \<noteq> []" unfolding true_annots_def Ball_def true_annot_def true_cls_def by force
        assume nm: "\<not>is_decided (hd ?M)"
        then obtain L' C where L'C: "hd_raw_conc_trail S = Propagated L' C"
          by (metis \<open>conc_trail S \<noteq> []\<close> hd_raw_conc_trail is_decided_def mmset_of_mlit.elims)
        then have "hd ?M = Propagated L' (mset_cls C)"
          using \<open>conc_trail S \<noteq> []\<close> hd_raw_conc_trail mmset_of_mlit.simps(1) by fastforce
        then have M: "?M = Propagated L' (mset_cls C) # tl ?M"
          using \<open>?M \<noteq> []\<close> list.collapse by fastforce
        then obtain C' where C': "mset_cls C = C' + {#L'#}"
          using confl unfolding cdcl\<^sub>W_conc_conflicting_def by (metis append_Nil diff_single_eq_union)
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
          then have "get_maximum_level (conc_trail S) D' \<le> ?k"
            using count_decided_ge_get_maximum_level[of "Propagated L' (mset_cls C) # tl ?M"] M
            level_inv unfolding cdcl\<^sub>W_M_level_inv_def by auto
          then have "get_maximum_level (conc_trail S) D' = ?k
            \<or> get_maximum_level (conc_trail S) D' < ?k"
            using le_neq_implies_less by blast
          moreover {
            assume g_D'_k: "get_maximum_level (conc_trail S) D' = ?k"
            then have f1: "get_maximum_level (conc_trail S) D' = conc_backtrack_lvl S"
              using M by auto
            then have "Ex (cdcl\<^sub>W_o S)"
              using f1 resolve_rule[of S L' C , OF \<open>conc_trail S \<noteq> []\<close> _ _ raw_conf] raw_conf g_D'_k
              L'C L'D unfolding C' D' E'
              by (fastforce simp add: D' intro: cdcl\<^sub>W_o.intros cdcl\<^sub>W_bj.intros)
            then have False
              by (meson alien cdcl\<^sub>W_then_exists_cdcl\<^sub>W_stgy_step termi level_inv)
          }
          moreover {
            assume a1: "get_maximum_level (conc_trail S) D' < ?k"
            then have f3: "get_maximum_level (conc_trail S) D' < get_level (conc_trail S) (-L')"
              using a1 lev_L by (metis D' get_maximum_level_ge_get_level insert_noteq_member
                not_less)
            moreover have "conc_backtrack_lvl S = get_level (conc_trail S) L'"
              apply (subst M)
              using level_inv unfolding cdcl\<^sub>W_M_level_inv_def
              by (subst (asm)(3) M) (auto simp add: cdcl\<^sub>W_M_level_inv_decomp)[]
            moreover
              then have "get_level (conc_trail S) L' = get_maximum_level (conc_trail S) (D' + {#- L'#})"
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
    conc_conflicting: "cdcl\<^sub>W_conc_conflicting S"
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
        using conc_conflicting confl tr_S unfolding cdcl\<^sub>W_conc_conflicting_def by auto
      ultimately have "-L \<in> lits_of_l (Propagated L (mset_cls C) # M)"
        using in_CNot_implies_uminus(2) by blast
      moreover have "no_dup (Propagated L (mset_cls C) # M)"
        using lev tr_S unfolding cdcl\<^sub>W_M_level_inv_def by auto
      ultimately show False unfolding lits_of_def by (metis consistent_interp_def image_eqI
        list.set_intros(1) lits_of_def ann_lit.sel(2) distinct_consistent_interp)
    qed

  ultimately
    have g_D: "get_maximum_level (Propagated L (mset_cls C) # M) (remove1_mset (-L) (mset_ccls D))
      = get_maximum_level M (remove1_mset (-L) (mset_ccls D))"
    proof -
      have "\<forall>a f L. ((a::'v) \<in> f ` L) = (\<exists>l. (l :: 'v literal) \<in> L \<and> a = f l)"
        by blast
      then show ?thesis
        using get_maximum_level_skip_first[of L "remove1_mset (-L) (mset_ccls D)" "mset_cls C" M]
        unfolding atms_of_def
        by (metis (no_types) uL_not_D L_not_D atm_of_eq_atm_of)
    qed
  have lev_L[simp]: "get_level M L = 0"
    apply (rule atm_of_notin_get_rev_level_eq_0)
    using lev unfolding cdcl\<^sub>W_M_level_inv_def tr_S by (auto simp: lits_of_def)

  have D: "get_maximum_level M (remove1_mset (-L) (mset_ccls D)) = conc_backtrack_lvl S"
    using resolve.hyps(6) LD unfolding tr_S by (auto simp: get_maximum_level_plus max_def g_D)
  have "get_maximum_level M (remove1_mset L (mset_cls C)) \<le> conc_backtrack_lvl S"
    using count_decided_ge_get_maximum_level[of M] lev unfolding tr_S cdcl\<^sub>W_M_level_inv_def by auto
  then have
    "get_maximum_level M (remove1_mset (- L) (mset_ccls D) #\<union> remove1_mset L (mset_cls C)) =
      conc_backtrack_lvl S"
    by (auto simp: get_maximum_level_union_mset get_maximum_level_plus max_def D)
  then show ?case
    using tr_S not_empty_get_maximum_level_exists_lit[of
      "remove1_mset (- L) (mset_ccls D) #\<union> remove1_mset L (mset_cls C)" M] T
    by auto
next
  case (skip L C' M D T) note tr_S = this(1) and D = this(2) and T = this(5)
  then obtain La where
    "La \<in># mset_ccls D" and
    "get_level (Propagated L C' # M) La = conc_backtrack_lvl S"
    using skip confl_inv by auto
  moreover
    have "atm_of La \<noteq> atm_of L"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then have La: "La = L" using \<open>La \<in># mset_ccls D\<close> \<open>- L \<notin># mset_ccls D\<close>
          by (auto simp add: atm_of_eq_atm_of)
        have "Propagated L C' # M \<Turnstile>as CNot (mset_ccls D)"
          using conc_conflicting tr_S D unfolding cdcl\<^sub>W_conc_conflicting_def by auto
        then have "-L \<in> lits_of_l M"
          using \<open>La \<in># mset_ccls D\<close> in_CNot_implies_uminus(2)[of L "mset_ccls D"
            "Propagated L C' # M"] unfolding La
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
    "undefined_lit (conc_trail S) L"
proof -
  obtain E L where
    conf: "conc_conflicting S = None" and
    E: "E !\<in>! raw_clauses S" and
    LE: "L \<in># mset_cls E" and
    tr: "conc_trail S \<Turnstile>as CNot (mset_cls E - {#L#})" and
    undef: "undefined_lit (conc_trail S) L" and
    T: "T \<sim> cons_conc_trail (Propagated L E) S"
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
  "lits_of_l (conc_trail S) \<subseteq> set M" and
  "conc_init_clss S = N" and
  "propagate\<^sup>*\<^sup>* S S'" and
  "conc_learned_clss S = {#}"
  shows "length (conc_trail S) \<le> length (conc_trail S') \<and> lits_of_l (conc_trail S') \<subseteq> set M"
  using assms(6,4,5,7)
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by auto
next
  case (step Y Z)
  note st = this(1) and propa = this(2) and IH = this(3) and lits' = this(4) and NS = this(5) and
    learned = this(6)
  then have len: "length (conc_trail S) \<le> length (conc_trail Y)" and LM: "lits_of_l (conc_trail Y) \<subseteq> set M"
     by blast+

  obtain M' N' U k C L where
    Y: "state Y = (M', N', U, k, None)" and
    Z: "state Z = (Propagated L (C + {#L#}) # M', N', U, k, None)" and
    C: "C + {#L#} \<in># clauses Y" and
    M'_C: "M' \<Turnstile>as CNot C" and
    "undefined_lit (conc_trail Y) L"
    using propa by (auto elim: propagate_high_levelE)
  have "conc_init_clss S = conc_init_clss Y"
    using st by induction (auto elim: propagateE)
  then have [simp]: "N' = N" using NS Y Z by simp
  have "conc_learned_clss Y = {#}"
    using st learned by induction (auto elim: propagateE)
  then have [simp]: "U = {#}" using Y by auto
  have "set M \<Turnstile>s CNot C"
    using M'_C LM Y unfolding true_annots_def Ball_def true_annot_def true_clss_def true_cls_def
    by force
  moreover
    have "set M \<Turnstile> C + {#L#}"
      using MN C learned Y NS \<open>conc_init_clss S = conc_init_clss Y\<close> \<open>conc_learned_clss Y = {#}\<close>
      unfolding true_clss_def raw_clauses_def by fastforce
  ultimately have "L \<in> set M" by (simp add: cons consistent_CNot_not)
  then show ?case using LM len Y Z by auto
qed

lemma
  assumes "propagate\<^sup>*\<^sup>* S X"
  shows
    rtranclp_propagate_conc_init_clss: "conc_init_clss X = conc_init_clss S" and
    rtranclp_propagate_conc_learned_clss: "conc_learned_clss X = conc_learned_clss S"
  using assms by (induction rule: rtranclp_induct) (auto elim: propagateE)

lemma completeness_is_a_full1_propagation:
  fixes S :: "'st" and M :: "'v literal list"
  assumes MN: "set M \<Turnstile>s set_mset N"
  and cons: "consistent_interp (set M)"
  and tot: "total_over_m (set M) (set_mset N)"
  and alien: "no_strange_atm S"
  and learned: "conc_learned_clss S = {#}"
  and clsS[simp]: "conc_init_clss S = N"
  and lits: "lits_of_l (conc_trail S) \<subseteq> set M"
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
      have clsX: "conc_init_clss X = conc_init_clss S"
        using X by (blast dest: rtranclp_propagate_conc_init_clss)
      have learnedX: "conc_learned_clss X = {#}"
        using X learned by (auto dest: rtranclp_propagate_conc_learned_clss)
      obtain E where
        E: "E \<in># conc_init_clss X + conc_learned_clss X" and
        Not_E: "conc_trail X \<Turnstile>as CNot E"
        using Xconf by (auto simp add: raw_clauses_def elim!: conflictE)
      have "lits_of_l (conc_trail X) \<subseteq> set M"
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

text \<open>See also @{thm rtranclp_cdcl\<^sub>W_cp_dropWhile_conc_trail}\<close>
lemma rtranclp_propagate_is_conc_trail_append:
  "propagate\<^sup>*\<^sup>* S T \<Longrightarrow> \<exists>c. conc_trail T = c @ conc_trail S"
  by (induction rule: rtranclp_induct) (auto elim: propagateE)

lemma rtranclp_propagate_is_update_conc_trail:
  "propagate\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W_M_level_inv S \<Longrightarrow>
    conc_init_clss S = conc_init_clss T \<and> conc_learned_clss S = conc_learned_clss T \<and> conc_backtrack_lvl S = conc_backtrack_lvl T
    \<and> conc_conflicting S = conc_conflicting T"
proof (induction rule: rtranclp_induct)
  case base
  then show ?case unfolding state_eq_def by (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
next
  case (step T U) note IH = this(3)[OF this(4)]
  moreover have "cdcl\<^sub>W_M_level_inv U"
    using rtranclp_cdcl\<^sub>W_consistent_inv \<open>propagate\<^sup>*\<^sup>* S T\<close> \<open>propagate T U\<close>
    rtranclp_mono[of propagate cdcl\<^sub>W] cdcl\<^sub>W_cp_consistent_inv propagate'
    rtranclp_propagate_is_rtranclp_cdcl\<^sub>W step.prems by blast
    then have "no_dup (conc_trail U)" unfolding cdcl\<^sub>W_M_level_inv_def by auto
  ultimately show ?case using \<open>propagate T U\<close> unfolding state_eq_def
    by (fastforce simp: elim: propagateE)
qed

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
      by (auto simp: comp_def)
    have lev: "cdcl\<^sub>W_M_level_inv S'"
      using M S' rtranclp_cdcl\<^sub>W_consistent_inv rtranclp_propagate_is_rtranclp_cdcl\<^sub>W by blast
    then have n_d'[simp]: "no_dup (conc_trail S')"
      unfolding cdcl\<^sub>W_M_level_inv_def by auto
    have "length (conc_trail S) \<le> length (conc_trail S') \<and> lits_of_l (conc_trail S') \<subseteq> set M"
      using S' full cdcl\<^sub>W_cp_propagate_completeness[OF assms(1-3), of S] M' S
      by (auto simp: comp_def)
    moreover
      have full: "full1 cdcl\<^sub>W_cp S S'"
        using full no_step no_step_cdcl\<^sub>W_cp_no_conflict_no_propagate(2) unfolding full1_def full_def
        rtranclp_unfold by blast
      then have "cdcl\<^sub>W_stgy S S'" by (simp add: cdcl\<^sub>W_stgy.conflict')
    moreover
      have propa: "propagate\<^sup>+\<^sup>+ S S'" using S' full unfolding full1_def by (metis rtranclpD tranclpD)
      have "conc_trail S = M'"
        using S by (auto simp: comp_def rev_map)
      with propa have "length (conc_trail S') > n"
        using l_M' propa by (induction rule: tranclp.induct) (auto elim: propagateE)
    moreover
      have stS': "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) S'"
        using st cdcl\<^sub>W_stgy.conflict'[OF full] by auto
      then have "conc_init_clss S' = mset_clss N"
        using stS' rtranclp_cdcl\<^sub>W_stgy_no_more_conc_init_clss by fastforce
    moreover
      have
        [simp]:"conc_learned_clss S' = {#}" and
        [simp]: "conc_init_clss S' = conc_init_clss S" and
        [simp]: "conc_conflicting S' = None"
        using tranclp_into_rtranclp[OF \<open>propagate\<^sup>+\<^sup>+ S S'\<close>] S
        rtranclp_propagate_is_update_conc_trail[of S S'] S M unfolding state_eq_def
        by (auto simp: comp_def)
      have S_S': "state S' = (conc_trail S', mset_clss N, {#}, conc_backtrack_lvl S', None)"
        using S by auto
      have "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) S'"
        apply (rule rtranclp.rtrancl_into_rtrancl)
         using st apply simp
        using \<open>cdcl\<^sub>W_stgy S S'\<close> by simp
    ultimately have ?case
      apply -
      apply (rule exI[of _ "conc_trail S'"], rule exI[of _ "conc_backtrack_lvl S'"], rule exI[of _ S'])
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
        then obtain L where L: "L \<in> set M" and undef_m: "L \<notin> lits_of_l M'" by auto
        moreover have undef: "undefined_lit M' L"
          using M' Decided_Propagated_in_iff_in_lits_of_l calculation(1,2) cons
          consistent_interp_def by (metis (no_types, lifting) subset_eq)
        moreover have "atm_of L \<in> atms_of_mm (conc_init_clss S)"
          using atm_incl calculation S by auto
        ultimately
          have dec: "decide S (cons_conc_trail (Decided L) (incr_lvl S))"
            using decide_rule[of S _ "cons_conc_trail (Decided L) (incr_lvl S)"] S
            by auto
        let ?S' = "cons_conc_trail (Decided L) (incr_lvl S)"
        have "lits_of_l (conc_trail ?S') \<subseteq> set M" using L M' S undef by auto
        moreover have "no_strange_atm ?S'"
          using alien dec M by (meson cdcl\<^sub>W_no_strange_atm_inv decide other)
        ultimately obtain S'' where S'': "propagate\<^sup>*\<^sup>* ?S' S''" and full: "full cdcl\<^sub>W_cp ?S' S''"
          using completeness_is_a_full1_propagation[OF assms(1-3), of ?S'] S undef
          by auto
        have "cdcl\<^sub>W_M_level_inv ?S'"
          using M dec rtranclp_mono[of decide cdcl\<^sub>W] by (meson cdcl\<^sub>W_consistent_inv decide other)
        then have lev'': "cdcl\<^sub>W_M_level_inv S''"
          using S'' rtranclp_cdcl\<^sub>W_consistent_inv rtranclp_propagate_is_rtranclp_cdcl\<^sub>W by blast
        then have n_d'': "no_dup (conc_trail S'')"
          unfolding cdcl\<^sub>W_M_level_inv_def by auto
        have "length (conc_trail ?S') \<le> length (conc_trail S'') \<and> lits_of_l (conc_trail S'') \<subseteq> set M"
          using S'' full cdcl\<^sub>W_cp_propagate_completeness[OF assms(1-3), of ?S' S''] L M' S undef
          by simp
        then have "Suc n \<le> length (conc_trail S'') \<and> lits_of_l (conc_trail S'') \<subseteq> set M"
          using l_M' S undef by auto
        moreover
          have "cdcl\<^sub>W_M_level_inv (cons_conc_trail (Decided L)
            (update_conc_backtrack_lvl (Suc (conc_backtrack_lvl S)) S))"
            using S \<open>cdcl\<^sub>W_M_level_inv (cons_conc_trail (Decided L) (incr_lvl S))\<close> by auto
          then have S'':
            "state S'' = (conc_trail S'', mset_clss N, {#}, conc_backtrack_lvl S'', None)"
            using rtranclp_propagate_is_update_conc_trail[OF S''] S undef n_d'' lev''
            by auto
          then have "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) S''"
            using cdcl\<^sub>W_stgy.intros(2)[OF decide[OF dec] _ full] no_step no_confl st
            by (auto simp: cdcl\<^sub>W_cp.simps)
        ultimately show ?thesis using S'' n_d'' by blast
      qed
  }
  ultimately show ?case by blast
qed

text \<open>\cwref{cdcl:completeness}{theorem 2.9.11 page 84} (with strategy)\<close>
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
    using M'_M card_seteq by blast
  moreover
    then have "M' \<Turnstile>asm mset_clss N"
      using MN unfolding true_annots_def Ball_def true_annot_def true_clss_def by auto
    then have "final_cdcl\<^sub>W_state T"
      using T no_dup unfolding final_cdcl\<^sub>W_state_def by auto
  ultimately show ?thesis using st T by blast
qed

subsubsection \<open>No conflict with only variables of level less than backtrack level\<close>
text \<open>This invariant is stronger than the previous argument in the sense that it is a property about
  all possible conflicts.\<close>
definition "no_smaller_confl (S ::'st) \<equiv>
  (\<forall>M K M' D. M' @ Decided K # M = conc_trail S \<longrightarrow> D \<in># clauses S
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
      fix M'' K M' Da
      assume "M'' @ Decided K # M' = conc_trail T"
      and D: "Da \<in># local.clauses T"
      then have "tl M'' @ Decided K # M' = conc_trail S
        \<or> (M'' = [] \<and> Decided K # M' = Decided L # conc_trail S)"
        using T undef by (cases M'') auto
      moreover {
        assume "tl M'' @ Decided K # M' = conc_trail S"
        then have "\<not>M' \<Turnstile>as CNot Da"
          using D T undef no_f confl smaller unfolding no_smaller_confl_def smaller by fastforce
      }
      moreover {
        assume "Decided K # M' = Decided L # conc_trail S"
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
    undef = this(8) and T = this(9)
  obtain c where M: "conc_trail S = c @ M2 @ Decided K # M1"
    using decomp by auto

  show ?case
    proof (intro allI impI)
      fix M ia K' M' Da
      assume "M' @ Decided K' # M = conc_trail T"
      then have "tl M' @ Decided K' # M = M1"
        using T decomp undef lev by (cases M') (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
      let ?S' = "(cons_conc_trail (Propagated L (cls_of_ccls D))
                  (reduce_conc_trail_to M1 (add_learned_cls (cls_of_ccls D)
                  (update_conc_backtrack_lvl i (update_conc_conflicting None S)))))"
      assume D: "Da \<in># clauses T"
      moreover{
        assume "Da \<in># clauses S"
        then have "\<not>M \<Turnstile>as CNot Da" using \<open>tl M' @ Decided K' # M = M1\<close> M confl undef smaller
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
              using UnI2 \<open>tl M' @ Decided K' # M = M1\<close>
              by auto
            moreover
              have "backtrack S ?S'"
                using backtrack_rule[of S] backtrack.hyps
                by (force simp: state_eq_def simp del: state_simp)
              then have "cdcl\<^sub>W_M_level_inv ?S'"
                using cdcl\<^sub>W_consistent_inv[OF _ lev] other[OF bj] by (auto intro: cdcl\<^sub>W_bj.intros)
              then have "no_dup (Propagated L (mset_ccls D) # M1)"
                using decomp undef lev unfolding cdcl\<^sub>W_M_level_inv_def by auto
            ultimately show False
               using undef by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)
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
  fix M' K M'' D
  assume M': "M'' @ Decided K # M' = conc_trail S'"
  and "D \<in># clauses S'"
  obtain M N U k C L where
    S: "state S = (M, N, U, k, None)" and
    S': "state S' = (Propagated L (C + {#L#}) # M, N, U, k, None)" and
    "C + {#L#} \<in># clauses S" and
    "M \<Turnstile>as CNot C" and
    "undefined_lit M L"
    using propagate by (auto elim: propagate_high_levelE)
  have "tl M'' @ Decided K # M' = conc_trail S" using M' S S'
    by (metis Pair_inject list.inject list.sel(3) ann_lit.distinct(1) self_append_conv2
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
    not_conflict_not_any_negated_conc_init_clss other'.hyps(2) cdcl\<^sub>W_cp.simps by auto
  then show ?case using full_cdcl\<^sub>W_cp_no_smaller_confl_inv[of S' S''] other'.hyps by blast
qed

lemma is_conc_conflicting_exists_conflict:
  assumes "\<not>(\<forall>D\<in>#conc_init_clss S' + conc_learned_clss S'. \<not> conc_trail S' \<Turnstile>as CNot D)"
  and "conc_conflicting S' = None"
  shows "\<exists>S''. conflict S' S''"
  using assms raw_clauses_def not_conflict_not_any_negated_conc_init_clss by fastforce

lemma cdcl\<^sub>W_o_conflict_is_no_clause_is_false:
  fixes S S' :: "'st"
  assumes
    "cdcl\<^sub>W_o S S'" and
    lev: "cdcl\<^sub>W_M_level_inv S" and
    max_lev: "conflict_is_false_with_level S" and
    no_f: "no_clause_is_false S" and
    no_l: "no_smaller_confl S"
  shows "no_clause_is_false S'
    \<or> (conc_conflicting S' = None
        \<longrightarrow> (\<forall>D \<in># clauses S'. conc_trail S' \<Turnstile>as CNot D
             \<longrightarrow> (\<exists>L. L \<in># D \<and> get_level (conc_trail S') L = conc_backtrack_lvl S')))"
  using assms(1,2)
proof (induct rule: cdcl\<^sub>W_o_induct_lev2)
  case (decide L T) note S = this(1) and undef = this(2) and T = this(4)
  show ?case
    proof (rule HOL.disjI2, clarify)
      fix D
      assume D: "D \<in># clauses T" and M_D: "conc_trail T \<Turnstile>as CNot D"
      let ?M = "conc_trail S"
      let ?M' = "conc_trail T"
      let ?k = "conc_backtrack_lvl S"
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
                \<open>lits_of_l (Decided L # conc_trail S) \<Turnstile>l L''\<close> by auto
            qed
          then show False using \<open>\<not> ?M \<Turnstile>as CNot D\<close> by auto
        qed
      have "atm_of L \<notin> atm_of ` (lits_of_l ?M)"
        using undef defined_lit_map unfolding lits_of_def by fastforce
      then have "get_level (Decided L # ?M) (-L) = ?k + 1"
        using lev unfolding cdcl\<^sub>W_M_level_inv_def by auto
      then have "-L \<in># D \<and> get_level ?M' (-L) = conc_backtrack_lvl T"
        using \<open>-L \<in># D\<close> T undef by auto
      then show "\<exists>La. La \<in># D \<and> get_level ?M' La = conc_backtrack_lvl T"
        by blast
    qed
next
  case resolve
  then show ?case by auto
next
  case skip
  then show ?case by auto
next
  case (backtrack K i M1 M2 L D T) note decomp = this(3) and lev_K = this(7) and undef = this(8)
    and T = this(9)
  show ?case
    proof (rule HOL.disjI2, clarify)
      fix Da
      assume Da: "Da \<in># clauses T" and M_D: "conc_trail T \<Turnstile>as CNot Da"
      obtain c where M: "conc_trail S = c @ M2 @ Decided K # M1"
        using decomp by auto
      have tr_T: "conc_trail T = Propagated L (mset_ccls D) # M1"
        using T decomp undef lev by (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
      have "backtrack S T"
        using backtrack_rule[of S] backtrack.hyps T
        by (force simp del: state_simp simp: state_eq_def)
      then have lev': "cdcl\<^sub>W_M_level_inv T"
        using cdcl\<^sub>W_consistent_inv lev other cdcl\<^sub>W_bj.backtrack cdcl\<^sub>W_o.bj by blast
      then have "- L \<notin> lits_of_l M1"
        using lev cdcl\<^sub>W_M_level_inv_def Decided_Propagated_in_iff_in_lits_of_l undef by blast
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
        using M_D \<open>- L \<notin> lits_of_l M1\<close> T unfolding tr_T true_annots_true_cls true_clss_def
        by (auto simp: uminus_lit_swap)
      have "no_dup (Propagated L (mset_ccls D) # M1)"
        using lev lev' T decomp undef unfolding cdcl\<^sub>W_M_level_inv_def by auto
      then have L: "atm_of L \<notin> atm_of ` lits_of_l M1" unfolding lits_of_def by auto
      have "get_level (Propagated L (mset_ccls D) # M1) (-L) = i"
        using lev_K lev unfolding cdcl\<^sub>W_M_level_inv_def
        by (simp add: M image_Un atm_lit_of_set_lits_of_l)

      then have "-L \<in># Da \<and> get_level (conc_trail T) (-L) = conc_backtrack_lvl T"
        using \<open>-L \<in># Da\<close> T decomp undef lev by (auto simp: cdcl\<^sub>W_M_level_inv_def)
      then show "\<exists>La. La \<in># Da \<and> get_level (conc_trail T) La = conc_backtrack_lvl T"
        by blast
    qed
qed

lemma full1_cdcl\<^sub>W_cp_exists_conflict_decompose:
  assumes
    confl: "\<exists>D\<in>#clauses S. conc_trail S \<Turnstile>as CNot D" and
    full: "full cdcl\<^sub>W_cp S U" and
    no_confl: "conc_conflicting S = None" and
    lev: "cdcl\<^sub>W_M_level_inv S"
  shows "\<exists>T. propagate\<^sup>*\<^sup>* S T \<and> conflict T U"
proof -
  consider (propa) "propagate\<^sup>*\<^sup>* S U"
        | (confl) T where "propagate\<^sup>*\<^sup>* S T" and "conflict T U"
   using full unfolding full_def by (blast dest:rtranclp_cdcl\<^sub>W_cp_propa_or_propa_confl)
  then show ?thesis
    proof cases
      case confl
      then show ?thesis by blast
    next
      case propa
      then have "conc_conflicting U = None" and
        [simp]: "conc_learned_clss U = conc_learned_clss S" and
        [simp]: "conc_init_clss U = conc_init_clss S"
        using no_confl rtranclp_propagate_is_update_conc_trail lev by auto
      moreover
        obtain D where D: "D\<in>#clauses U" and
          trS: "conc_trail S \<Turnstile>as CNot D"
          using confl raw_clauses_def by auto
        obtain M where M: "conc_trail U = M @ conc_trail S"
          using full rtranclp_cdcl\<^sub>W_cp_dropWhile_conc_trail unfolding full_def by meson
        have tr_U: "conc_trail U \<Turnstile>as CNot D"
          apply (rule true_annots_mono)
          using trS unfolding M by simp_all
      have "\<exists>V. conflict U V"
        using \<open>conc_conflicting U = None\<close> D raw_clauses_def not_conflict_not_any_negated_conc_init_clss tr_U
        by meson
      then have False using full cdcl\<^sub>W_cp.conflict' unfolding full_def by blast
      then show ?thesis by fast
    qed
qed

lemma full1_cdcl\<^sub>W_cp_exists_conflict_full1_decompose:
  assumes
    confl: "\<exists>D\<in>#clauses S. conc_trail S \<Turnstile>as CNot D" and
    full: "full cdcl\<^sub>W_cp S U" and
    no_confl: "conc_conflicting S = None"and
    lev: "cdcl\<^sub>W_M_level_inv S"
  shows "\<exists>T D. propagate\<^sup>*\<^sup>* S T \<and> conflict T U
    \<and> conc_trail T \<Turnstile>as CNot D \<and> conc_conflicting U = Some D \<and> D \<in># clauses S"
proof -
  obtain T where propa: "propagate\<^sup>*\<^sup>* S T" and conf: "conflict T U"
    using full1_cdcl\<^sub>W_cp_exists_conflict_decompose[OF assms] by blast
  have p: "conc_learned_clss T = conc_learned_clss S" "conc_init_clss T = conc_init_clss S"
     using propa lev rtranclp_propagate_is_update_conc_trail by auto
  have c: "conc_learned_clss U = conc_learned_clss T" "conc_init_clss U = conc_init_clss T"
     using conf by (auto elim: conflictE)
  obtain D where "conc_trail T \<Turnstile>as CNot D \<and> conc_conflicting U = Some D \<and> D \<in># clauses S"
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
    "cdcl\<^sub>W_conc_conflicting S"
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
    "cdcl\<^sub>W_conc_conflicting S"
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
      \<or> (conc_conflicting S' = None \<longrightarrow> (\<forall>D\<in>#clauses S'. conc_trail S' \<Turnstile>as CNot D
          \<longrightarrow> (\<exists>L. L \<in># D \<and> get_level (conc_trail S') L = conc_backtrack_lvl S')))"
      using cdcl\<^sub>W_o_conflict_is_no_clause_is_false[of S S'] other'.hyps(1) other'.prems(1-4) by fast
  moreover {
    assume "no_clause_is_false S'"
    {
      assume "conc_conflicting S' = None"
      then have "conflict_is_false_with_level S'" by auto
      moreover have "full cdcl\<^sub>W_cp S' S''"
        by (metis (no_types) other'.hyps(3))
      ultimately have "conflict_is_false_with_level S''"
        using rtranclp_cdcl\<^sub>W_co_conflict_ex_lit_of_max_level[of S' S''] lev' \<open>no_clause_is_false S'\<close>
        by blast
    }
    moreover
    {
      assume c: "conc_conflicting S' \<noteq> None"
      have "conc_conflicting S \<noteq> None" using other'.hyps(1) c
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
       confl: "conc_conflicting S' = None" and
       D_L: "\<forall>D \<in># clauses S'. conc_trail S' \<Turnstile>as CNot D
         \<longrightarrow> (\<exists>L. L \<in># D \<and> get_level (conc_trail S') L = conc_backtrack_lvl S')"
     { assume "\<forall>D\<in>#clauses S'. \<not> conc_trail S' \<Turnstile>as CNot D"
       then have "no_clause_is_false S'" using confl by simp
       then have "conflict_is_false_with_level S''" using calculation(3) by presburger
     }
     moreover {
       assume "\<not>(\<forall>D\<in>#clauses S'. \<not> conc_trail S' \<Turnstile>as CNot D)"
       then obtain T D where
         "propagate\<^sup>*\<^sup>* S' T" and
         "conflict T S''" and
         D: "D \<in># clauses S'" and
         "conc_trail S'' \<Turnstile>as CNot D" and
         "conc_conflicting S'' = Some D"
         using full1_cdcl\<^sub>W_cp_exists_conflict_full1_decompose[OF _ _ confl]
         other'(3) lev' by (metis (mono_tags, lifting) conflictE state_eq_conc_trail
           conc_trail_update_conc_conflicting)
       obtain M where M: "conc_trail S'' = M @ conc_trail S'" and nm: "\<forall>m\<in>set M. \<not>is_decided m"
         using rtranclp_cdcl\<^sub>W_cp_dropWhile_conc_trail other'(3) unfolding full_def by meson
       have btS: "conc_backtrack_lvl S'' = conc_backtrack_lvl S'"
         using other'.hyps(3) unfolding full_def by (metis rtranclp_cdcl\<^sub>W_cp_conc_backtrack_lvl)
       have inv: "cdcl\<^sub>W_M_level_inv S''"
         by (metis (no_types) cdcl\<^sub>W_stgy.conflict' cdcl\<^sub>W_stgy_consistent_inv full_unfold lev'
           other'.hyps(3))
       then have nd: "no_dup (conc_trail S'')"
         by (metis (no_types) cdcl\<^sub>W_M_level_inv_decomp(2))
       have "conflict_is_false_with_level S''"
         proof cases
           assume "conc_trail S' \<Turnstile>as CNot D"
           moreover then obtain L where
             "L \<in># D" and
             lev_L: "get_level (conc_trail S') L = conc_backtrack_lvl S'"
             using D_L D by blast
           moreover
             have LS': "-L \<in> lits_of_l (conc_trail S')"
               using \<open>conc_trail S' \<Turnstile>as CNot D\<close> \<open>L \<in># D\<close> in_CNot_implies_uminus(2) by blast
             { fix x :: "('v, 'v clause) ann_lit" and
                 xb :: "('v, 'v clause) ann_lit"
               assume a1: "x \<in> set (conc_trail S')" and
                 a2: "xb \<in> set M" and
                 a3: "(\<lambda>l. atm_of (lit_of l)) ` set M \<inter> (\<lambda>l. atm_of (lit_of l)) ` set (conc_trail S')
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
             then have "get_level (conc_trail S'') L = get_level (conc_trail S') L"
               unfolding M by (simp add: lits_of_def)
           ultimately show ?thesis using btS \<open>conc_conflicting S'' = Some D\<close> by auto
         next
           assume "\<not>conc_trail S' \<Turnstile>as CNot D"
           then obtain L where "L \<in># D" and LM: "-L \<in> lits_of_l M"
             using \<open>conc_trail S'' \<Turnstile>as CNot D\<close> unfolding M
               by (auto simp add: true_cls_def M true_annots_def true_annot_def
                     split: if_split_asm)
           { fix x :: "('v, 'v clause) ann_lit" and
               xb :: "('v, 'v clause) ann_lit"
             assume a1: "xb \<in> set (conc_trail S')" and
               a2: "x \<in> set M" and
               a3: "atm_of L = atm_of (lit_of xb)" and
               a4: "- L = lit_of x" and
               a5: "(\<lambda>l. atm_of (lit_of l)) ` set M \<inter> (\<lambda>l. atm_of (lit_of l)) ` set (conc_trail S')
                 = {}"
             moreover have "atm_of (lit_of xb) = atm_of (- L)"
               using a3 by simp
             ultimately have False
               by auto }
           then have LS': "atm_of L \<notin> atm_of ` lits_of_l (conc_trail S')"
             using nd \<open>L \<in># D\<close> LM unfolding M by (auto simp add: lits_of_def)
           show ?thesis
             proof -
               have "atm_of L \<in> atm_of ` lits_of_l M "
                 using \<open>-L \<in> lits_of_l M\<close>
                 by (simp add: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set lits_of_def)
               then have "get_level (M @ conc_trail S') L = conc_backtrack_lvl S'"
                 using lev' LS' nm unfolding cdcl\<^sub>W_M_level_inv_def by auto
               then show ?thesis
                 using nm \<open>L\<in>#D\<close> \<open>conc_conflicting S'' = Some D\<close>
                 unfolding lits_of_def btS M
                 by auto
             qed
         qed
     }
     ultimately have "conflict_is_false_with_level S''" by blast
  }
  moreover
  {
    assume "conc_conflicting S' \<noteq> None"
    have "no_clause_is_false S'" using \<open>conc_conflicting S' \<noteq> None\<close> by auto
    then have "conflict_is_false_with_level S''" using calculation(3) by presburger
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
    conc_conflicting: "cdcl\<^sub>W_conc_conflicting S" and
    decomp: "all_decomposition_implies_m (conc_init_clss S) (get_all_ann_decomposition (conc_trail S))" and
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
    using st lev rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W
    by (blast intro: rtranclp_cdcl\<^sub>W_consistent_inv)+
  moreover have "no_clause_is_false S'"
    using st no_f rtranclp_cdcl\<^sub>W_stgy_not_non_negated_conc_init_clss by presburger
  moreover have "distinct_cdcl\<^sub>W_state S'"
    using rtanclp_distinct_cdcl\<^sub>W_state_inv[of S S'] lev rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W[OF st]
    dist by auto
  moreover have "cdcl\<^sub>W_conc_conflicting S'"
    using rtranclp_cdcl\<^sub>W_all_inv(6)[of S S'] st alien conc_conflicting decomp dist learned lev
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
  shows "(conc_conflicting S' = Some {#} \<and> unsatisfiable (set_mset (conc_init_clss S')))
    \<or> (conc_conflicting S' = None \<and> conc_trail S' \<Turnstile>asm conc_init_clss S')"
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
    confl: "cdcl\<^sub>W_conc_conflicting S'" and
    decomp: "all_decomposition_implies_m (conc_init_clss S') (get_all_ann_decomposition (conc_trail S'))"
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
  have "cdcl\<^sub>W_cp S S'" and "conc_conflicting S' \<noteq> None"
    using cp cdcl\<^sub>W_cp.intros by (auto elim!: conflictE simp: state_eq_def simp del: state_simp)
  then have "cdcl\<^sub>W_cp\<^sup>+\<^sup>+ S S'" by blast
  moreover have "no_step cdcl\<^sub>W_cp S'"
    using \<open>conc_conflicting S' \<noteq> None\<close> by (metis cdcl\<^sub>W_cp_conc_conflicting_not_empty
      option.exhaust)
  ultimately show "full1 cdcl\<^sub>W_cp S S'" unfolding full1_def by blast+
qed

lemma cdcl\<^sub>W_cp_fst_empty_conc_conflicting_false:
  assumes
    "cdcl\<^sub>W_cp S S'" and
    "conc_trail S = []" and
    "conc_conflicting S \<noteq> None"
  shows False
  using assms by (induct rule: cdcl\<^sub>W_cp.induct) (auto elim: propagateE conflictE)

lemma cdcl\<^sub>W_o_fst_empty_conc_conflicting_false:
  assumes "cdcl\<^sub>W_o S S'"
  and "conc_trail S = []"
  and "conc_conflicting S \<noteq> None"
  shows False
  using assms by (induct rule: cdcl\<^sub>W_o_induct) auto

lemma cdcl\<^sub>W_stgy_fst_empty_conc_conflicting_false:
  assumes "cdcl\<^sub>W_stgy S S'"
  and "conc_trail S = []"
  and "conc_conflicting S \<noteq> None"
  shows False
  using assms apply (induct rule: cdcl\<^sub>W_stgy.induct)
  using tranclpD cdcl\<^sub>W_cp_fst_empty_conc_conflicting_false unfolding full1_def apply metis
  using cdcl\<^sub>W_o_fst_empty_conc_conflicting_false by blast
thm cdcl\<^sub>W_cp.induct[split_format(complete)]

lemma cdcl\<^sub>W_cp_conc_conflicting_is_false:
  "cdcl\<^sub>W_cp S S' \<Longrightarrow> conc_conflicting S = Some {#} \<Longrightarrow> False"
  by (induction rule: cdcl\<^sub>W_cp.induct) (auto elim: propagateE conflictE)

lemma rtranclp_cdcl\<^sub>W_cp_conc_conflicting_is_false:
  "cdcl\<^sub>W_cp\<^sup>+\<^sup>+ S S' \<Longrightarrow> conc_conflicting S = Some {#} \<Longrightarrow> False"
  apply (induction rule: tranclp.induct)
  by (auto dest: cdcl\<^sub>W_cp_conc_conflicting_is_false)

lemma cdcl\<^sub>W_o_conc_conflicting_is_false:
  "cdcl\<^sub>W_o S S' \<Longrightarrow> conc_conflicting S = Some {#} \<Longrightarrow> False"
  by (induction rule: cdcl\<^sub>W_o_induct) auto

lemma cdcl\<^sub>W_stgy_conc_conflicting_is_false:
  "cdcl\<^sub>W_stgy S S' \<Longrightarrow> conc_conflicting S = Some {#} \<Longrightarrow> False"
  apply (induction rule: cdcl\<^sub>W_stgy.induct)
    unfolding full1_def apply (metis (no_types) cdcl\<^sub>W_cp_conc_conflicting_not_empty tranclpD)
  unfolding full_def by (metis conflict_with_false_implies_terminated other)

lemma rtranclp_cdcl\<^sub>W_stgy_conc_conflicting_is_false:
  "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S S' \<Longrightarrow> conc_conflicting S = Some {#} \<Longrightarrow> S' = S"
  apply (induction rule: rtranclp_induct)
    apply simp
  using cdcl\<^sub>W_stgy_conc_conflicting_is_false by blast

lemma full_cdcl\<^sub>W_conc_init_clss_with_false_normal_form:
  assumes
    "\<forall> m\<in> set M. \<not>is_decided m" and
    "E = Some D" and
    "state S = (M, N, U, 0, E)"
    "full cdcl\<^sub>W_stgy S S'" and
    "all_decomposition_implies_m (conc_init_clss S) (get_all_ann_decomposition (conc_trail S))"
    "cdcl\<^sub>W_learned_clause S"
    "cdcl\<^sub>W_M_level_inv S"
    "no_strange_atm S"
    "distinct_cdcl\<^sub>W_state S"
    "cdcl\<^sub>W_conc_conflicting S"
  shows "\<exists>M''. state S' = (M'', N, U, 0, Some {#})"
  using assms(10,9,8,7,6,5,4,3,2,1)
proof (induction M arbitrary: E D S)
  case Nil
  then show ?case
    using rtranclp_cdcl\<^sub>W_stgy_conc_conflicting_is_false unfolding full_def cdcl\<^sub>W_conc_conflicting_def
    by fastforce
next
  case (Cons L M) note IH = this(1) and full = this(8) and E = this(10) and inv = this(2-7) and
    S = this(9) and nm = this(11)
  obtain K p where K: "L = Propagated K p"
    using nm by (cases L) auto
  have "every_mark_is_a_conflict S" using inv unfolding cdcl\<^sub>W_conc_conflicting_def by auto
  then have MpK: "M \<Turnstile>as CNot (p - {#K#})" and Kp: "K \<in># p"
    using S unfolding K by fastforce+
  then have p: "p = (p - {#K#}) + {#K#}"
    by (auto simp add: multiset_eq_iff)
  then have K': "L = Propagated K ((p - {#K#}) + {#K#})"
    using K by auto
  obtain p' where
    p': "hd_raw_conc_trail S = Propagated K p'" and
    pp': "mset_cls p' = p"
    using hd_raw_conc_trail[of S] S K by (cases "hd_raw_conc_trail S") auto
  obtain raw_D where
    raw_D: "raw_conc_conflicting S = Some raw_D"
    using S E by (cases "raw_conc_conflicting S") auto
  then have raw_DD: "mset_ccls raw_D = D"
    using S E by auto
  consider (D) "D = {#}" | (D') "D \<noteq> {#}" by blast
  then show ?case
    proof cases
      case D
      then show ?thesis
        using full rtranclp_cdcl\<^sub>W_stgy_conc_conflicting_is_false S unfolding full_def E D by auto
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
            using \<open>-lit_of L \<notin># D\<close> S D' K hd_raw_conc_trail[of S] unfolding E
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
            using resolve_rule[of S K p' raw_D] S p' \<open>K \<in># p\<close> raw_D LD
            unfolding K' D E pp' raw_DD by auto
          then have res: "no_step skip S"
            using LD S D' K hd_raw_conc_trail[of S] unfolding E
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

      have st_c: "cdcl\<^sub>W\<^sup>*\<^sup>* S T"
        using E T rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W s by blast
      have "cdcl\<^sub>W_conc_conflicting T"
        using rtranclp_cdcl\<^sub>W_all_inv(6)[OF st_c inv(6,5,4,3,2,1)] .
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
  shows "conc_conflicting S' = Some {#} \<and> unsatisfiable (set_mset (conc_init_clss S'))"
proof -
  let ?S = "init_state N"
  have "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ?S S'" and "no_step cdcl\<^sub>W_stgy S'" using full unfolding full_def by auto
  then have plus_or_eq: "cdcl\<^sub>W_stgy\<^sup>+\<^sup>+ ?S S' \<or> S' = ?S" unfolding rtranclp_unfold by auto
  have "\<exists>S''. conflict ?S S''"
    using empty not_conflict_not_any_negated_conc_init_clss[of "init_state N"] by auto


  then have cdcl\<^sub>W_stgy: "\<exists>S'. cdcl\<^sub>W_stgy ?S S'"
    using cdcl\<^sub>W_cp.conflict'[of ?S] conflict_is_full1_cdcl\<^sub>W_cp cdcl\<^sub>W_stgy.intros(1) by metis
  have "S' \<noteq> ?S" using \<open>no_step cdcl\<^sub>W_stgy S'\<close> cdcl\<^sub>W_stgy by blast

  then obtain St :: 'st where St: "cdcl\<^sub>W_stgy ?S St" and "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* St S'"
    using plus_or_eq by (metis (no_types) \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ?S S'\<close> converse_rtranclpE)
  have st: "cdcl\<^sub>W\<^sup>*\<^sup>* ?S St"
    by (simp add: rtranclp_unfold \<open>cdcl\<^sub>W_stgy ?S St\<close> cdcl\<^sub>W_stgy_tranclp_cdcl\<^sub>W)

  have "\<exists>T. conflict ?S T"
    using empty not_conflict_not_any_negated_conc_init_clss[of "?S"] by force
  then have fullSt: "full1 cdcl\<^sub>W_cp ?S St"
    using St unfolding cdcl\<^sub>W_stgy.simps by blast
  then have bt: "conc_backtrack_lvl St = (0::nat)"
    using rtranclp_cdcl\<^sub>W_cp_conc_backtrack_lvl unfolding full1_def
    by (fastforce dest!: tranclp_into_rtranclp)
  have cls_St: "conc_init_clss St = mset_clss N"
    using fullSt cdcl\<^sub>W_stgy_no_more_conc_init_clss[OF St] by auto
  have "conc_conflicting St \<noteq> None"
    proof (rule ccontr)
      assume conf: "\<not> ?thesis"
      obtain E where
        ES: "E !\<in>! raw_conc_init_clss St" and
        E: "mset_cls E = {#}"
        using empty cls_St by (metis in_mset_clss_exists_preimage)
      then have "\<exists>T. conflict St T"
        using empty cls_St conflict_rule[of St E] ES conf unfolding E
        by (auto simp: raw_clauses_def dest: in_mset_clss_exists_preimage)
      then show False using fullSt unfolding full1_def by blast
    qed

  have 1: "\<forall>m\<in>set (conc_trail St). \<not> is_decided m"
    using fullSt unfolding full1_def by (auto dest!: tranclp_into_rtranclp
      rtranclp_cdcl\<^sub>W_cp_dropWhile_conc_trail)
  have 2: "full cdcl\<^sub>W_stgy St S'"
    using \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* St S'\<close> \<open>no_step cdcl\<^sub>W_stgy S'\<close> bt unfolding full_def by auto
  have 3: "all_decomposition_implies_m
      (conc_init_clss St)
      (get_all_ann_decomposition
         (conc_trail St))"
   using rtranclp_cdcl\<^sub>W_all_inv(1)[OF st] no_d bt by simp
  have 4: "cdcl\<^sub>W_learned_clause St"
    using rtranclp_cdcl\<^sub>W_all_inv(2)[OF st] no_d bt bt by simp
  have 5: "cdcl\<^sub>W_M_level_inv St"
    using rtranclp_cdcl\<^sub>W_all_inv(3)[OF st] no_d bt by simp
  have 6: "no_strange_atm St"
    using rtranclp_cdcl\<^sub>W_all_inv(4)[OF st] no_d bt by simp
  have 7: "distinct_cdcl\<^sub>W_state St"
    using rtranclp_cdcl\<^sub>W_all_inv(5)[OF st] no_d bt by simp
  have 8: "cdcl\<^sub>W_conc_conflicting St"
    using rtranclp_cdcl\<^sub>W_all_inv(6)[OF st] no_d bt by simp
  have "conc_init_clss S' = conc_init_clss St" and "conc_conflicting S' = Some {#}"
     using \<open>conc_conflicting St \<noteq> None\<close> full_cdcl\<^sub>W_conc_init_clss_with_false_normal_form[OF 1, of _ _ St]
     2 3 4 5 6 7 8 St apply (metis \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* St S'\<close> rtranclp_cdcl\<^sub>W_stgy_no_more_conc_init_clss)
    using \<open>conc_conflicting St \<noteq> None\<close> full_cdcl\<^sub>W_conc_init_clss_with_false_normal_form[OF 1, of _ _ St _ _
      S'] 2 3 4 5 6 7 8 by (metis bt option.exhaust prod.inject)

  moreover have "conc_init_clss S' = mset_clss N"
    using \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) S'\<close> rtranclp_cdcl\<^sub>W_stgy_no_more_conc_init_clss by fastforce
  moreover have "unsatisfiable (set_mset (mset_clss N))"
    by (meson empty satisfiable_def true_cls_empty true_clss_def)
  ultimately show ?thesis by auto
qed

text \<open>\cwref{lem:prop:cdclsoundtermStates}{theorem 2.9.9 page 83}\<close>
lemma full_cdcl\<^sub>W_stgy_final_state_conclusive:
  fixes S' :: 'st
  assumes full: "full cdcl\<^sub>W_stgy (init_state N) S'" and no_d: "distinct_mset_mset (mset_clss N)"
  shows "(conc_conflicting S' = Some {#} \<and> unsatisfiable (set_mset (conc_init_clss S')))
    \<or> (conc_conflicting S' = None \<and> conc_trail S' \<Turnstile>asm conc_init_clss S')"
  using assms full_cdcl\<^sub>W_stgy_final_state_conclusive_is_one_false
  full_cdcl\<^sub>W_stgy_final_state_conclusive_non_false by blast

text \<open>\cwref{lem:prop:cdclsoundtermStates}{theorem 2.9.9 page 83}\<close>
lemma full_cdcl\<^sub>W_stgy_final_state_conclusive_from_init_state:
  fixes S' :: "'st"
  assumes full: "full cdcl\<^sub>W_stgy (init_state N) S'"
  and no_d: "distinct_mset_mset (mset_clss N)"
  shows "(conc_conflicting S' = Some {#} \<and> unsatisfiable (set_mset (mset_clss N)))
   \<or> (conc_conflicting S' = None \<and> conc_trail S' \<Turnstile>asm (mset_clss N) \<and> satisfiable (set_mset (mset_clss N)))"
proof -
  have N: "conc_init_clss S' = (mset_clss N)"
    using full unfolding full_def by (auto dest: rtranclp_cdcl\<^sub>W_stgy_no_more_conc_init_clss)
  consider
      (confl) "conc_conflicting S' = Some {#}" and "unsatisfiable (set_mset (conc_init_clss S'))"
    | (sat) "conc_conflicting S' = None" and "conc_trail S' \<Turnstile>asm conc_init_clss S'"
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
      then have "consistent_interp (lits_of_l (conc_trail S'))" unfolding cdcl\<^sub>W_M_level_inv_def by blast
      moreover have "lits_of_l (conc_trail S') \<Turnstile>s set_mset (conc_init_clss S')"
        using sat(2) by (auto simp add: true_annots_def true_annot_def true_clss_def)
      ultimately have "satisfiable (set_mset (conc_init_clss S'))" by simp
      then show ?thesis using sat unfolding N by blast
    qed
qed
end
end
