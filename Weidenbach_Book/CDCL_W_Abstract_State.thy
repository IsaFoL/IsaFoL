theory CDCL_W_Abstract_State
imports CDCL_Abstract_Clause_Representation List_More CDCL_W_Level Wellfounded_More
  CDCL_WNOT CDCL_Abstract_Clause_Representation

begin

section \<open>Weidenbach's CDCL with Abstract Clause Representation\<close>

text \<open>We first instantiate the locale of Weidenbach's locale. Then we define another abstract state:
  the goal of this state is to be used for implementations. We add more assumptions on the function
  about the state. For example @{term cons_trail} is restricted to undefined literals.\<close>

subsection \<open>Instantiation of the Multiset Version\<close>

type_synonym 'v cdcl\<^sub>W_mset = "('v, 'v clause) ann_lit list \<times>
  'v clauses \<times>
  'v clauses \<times>
  nat \<times> 'v clause option"

text \<open>We use definition, otherwise we could not use the simplification theorems we have already
  shown.\<close>
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

lemmas cdcl\<^sub>W_mset_state = trail_def cons_trail_def tl_trail_def add_learned_cls_def
    remove_cls_def update_backtrack_lvl_def update_conflicting_def init_clss_def learned_clss_def
    backtrack_lvl_def conflicting_def init_state_def

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
  init_state = init_state
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
  init_state = init_state
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
  init_state = init_state
  by unfold_locales auto

lemma cdcl\<^sub>W_mset_state_eq_eq: "cdcl\<^sub>W_mset.state_eq = (op =)"
   apply (intro ext)
   unfolding cdcl\<^sub>W_mset.state_eq_def
   by (auto simp: cdcl\<^sub>W_mset_state)

notation cdcl\<^sub>W_mset.state_eq (infix "\<sim>m" 49)

subsection \<open>Abstract Relation and Relation Theorems\<close>

text \<open>This locales makes the lifting from the relation defined with multiset @{term R} and the
  version with an abstract state @{term R_abs}. We are lifting many different relations (each rule
  and the the strategy).\<close>
locale relation_implied_relation_abs =
  fixes
    R :: "'v cdcl\<^sub>W_mset \<Rightarrow> 'v cdcl\<^sub>W_mset \<Rightarrow> bool" and
    R_abs :: "'st \<Rightarrow> 'st \<Rightarrow> bool" and
    state :: "'st \<Rightarrow> 'v cdcl\<^sub>W_mset" and
    inv :: "'v cdcl\<^sub>W_mset \<Rightarrow> bool"
  assumes
    relation_compatible_state:
      "inv (state S) \<Longrightarrow> R_abs S T \<Longrightarrow> R (state S) (state T)" and
    relation_compatible_abs:
      "\<And>S S' T. inv S \<Longrightarrow> S \<sim>m state S' \<Longrightarrow> R S T \<Longrightarrow> \<exists>U. R_abs S' U \<and> T \<sim>m state U" and
    relation_invariant:
      "\<And>S T. R S T \<Longrightarrow> inv S \<Longrightarrow> inv T" and
    relation_abs_right_compatible:
      "\<And>S T U. inv (state S) \<Longrightarrow> R_abs S T \<Longrightarrow> state T \<sim>m state U \<Longrightarrow> R_abs S U"
begin

lemma relation_compatible_eq:
  assumes
    inv: "inv (state S)" and
    abs: "R_abs S T" and
    SS': "state S \<sim>m state S'" and
    TT': "state T \<sim>m state T'"
  shows "R_abs S' T'"
proof -
  have "R (state S) (state T)"
    using relation_compatible_state inv abs by blast
  then obtain U where S'U: "R_abs S' U" and TU: "state T \<sim>m state U"
    using relation_compatible_abs[OF inv SS'] by blast
  then show ?thesis
    using relation_abs_right_compatible[OF _ S'U, of T'] TT' inv SS'[unfolded cdcl\<^sub>W_mset_state_eq_eq]
    cdcl\<^sub>W_mset.state_eq_trans[of "state T'" "state T" "state U"]
    by (auto simp add: cdcl\<^sub>W_mset.state_eq_sym)
qed

lemma rtranclp_relation_invariant:
  "R\<^sup>+\<^sup>+ S T \<Longrightarrow> inv S \<Longrightarrow> inv T"
  by (induction rule: tranclp_induct) (auto simp: relation_invariant)

lemma rtranclp_abs_rtranclp:
  "R_abs\<^sup>*\<^sup>* S T \<Longrightarrow> inv (state S) \<Longrightarrow> R\<^sup>*\<^sup>* (state S) (state T)"
  apply (induction rule: rtranclp_induct)
    apply simp
  by (metis relation_compatible_state rtranclp.simps rtranclpD rtranclp_relation_invariant)

lemma tranclp_relation_tranclp_relation_abs_compatible:
  fixes S :: 'st
  assumes
    R: "R\<^sup>+\<^sup>+ (state S) T" and
    inv: "inv (state S)"
  shows "\<exists>U. R_abs\<^sup>+\<^sup>+ S U \<and> T \<sim>m state U"
  using R
proof (induction rule: tranclp_induct)
  case (base T)
  then show ?case
    using relation_compatible_abs[of "state S" S T] inv by auto
next
  case (step T U) note st = this(1) and R = this(2) and IH = this(3)
  obtain V where
    SV: "R_abs\<^sup>+\<^sup>+ S V" and TV: "T \<sim>m state V"
    using IH by auto
  then obtain W where
    VW: "R_abs V W" and UW: "U \<sim>m state W"
    using relation_compatible_abs[OF _ TV R] inv rtranclp_relation_invariant[OF st] by blast
  have "R_abs\<^sup>+\<^sup>+ S W"
    using SV VW by auto
  then show ?case using UW by blast
qed

(* TODO Merge with previous *)
lemma rtranclp_relation_rtranclp_relation_abs_compatible:
  fixes S :: 'st
  assumes
    R: "R\<^sup>*\<^sup>* (state S) T" and
    inv: "inv (state S)"
  shows "\<exists>U. R_abs\<^sup>*\<^sup>* S U \<and> T \<sim>m state U"
  using R inv by (auto simp: rtranclp_unfold dest: tranclp_relation_tranclp_relation_abs_compatible)

lemma no_step_iff:
  "inv (state S) \<Longrightarrow> no_step R (state S) \<longleftrightarrow> no_step R_abs S"
  using relation_compatible_state relation_compatible_abs cdcl\<^sub>W_mset.state_eq_ref
  by blast

lemma tranclp_relation_compatible_eq_and_inv:
  assumes
    inv: "inv (state S)" and
    st: "R_abs\<^sup>+\<^sup>+ S T" and
    SS': "state S \<sim>m state S'" and
    TU: "state T \<sim>m state U"
  shows "R_abs\<^sup>+\<^sup>+ S' U \<and> inv (state U)"
  using st TU
proof (induction arbitrary: U rule: tranclp_induct)
  case (base T)
  moreover then have "inv (state U)"
    by (metis (full_types) cdcl\<^sub>W_mset_state_eq_eq inv relation_compatible_state relation_invariant)
  ultimately show ?case
    using relation_compatible_eq[of S T S' U] SS' inv
    by (auto simp: tranclp.r_into_trancl)
next
  case (step T T') note st = this(1) and R = this(2) and IH = this(3) and TU = this(4)
  have "R_abs\<^sup>+\<^sup>+ S' T" and invT: "inv (state T)" using IH[of T] by auto
  moreover have "R_abs T U"
    using relation_compatible_eq[of T T' T U] R TU inv rtranclp_relation_invariant invT by simp
  moreover have "inv (state U)"
    using calculation(3) invT relation_compatible_state relation_invariant by blast
  ultimately show ?case by auto
qed

lemma
  assumes
    inv: "inv (state S)" and
    st: "R_abs\<^sup>+\<^sup>+ S T" and
    SS': "state S \<sim>m state S'" and
    TU: "state T \<sim>m state U"
  shows
    tranclp_relation_compatible_eq: "R_abs\<^sup>+\<^sup>+ S' U" and
    tranclp_relation_abs_invariant: "inv (state U)"
    using tranclp_relation_compatible_eq_and_inv[OF assms] by blast+

lemma tranclp_abs_tranclp: "R_abs\<^sup>+\<^sup>+ S T \<Longrightarrow> inv (state S) \<Longrightarrow> R\<^sup>+\<^sup>+ (state S) (state T)"
  apply (induction rule: tranclp_induct)
    apply (auto simp add: relation_compatible_state)[]
  apply clarsimp
  apply (erule tranclp.trancl_into_trancl)
  using relation_compatible_state tranclp_relation_abs_invariant by blast

lemma full1_iff:
  assumes inv: "inv (state S)"
  shows "full1 R (state S) (state T) \<longleftrightarrow> full1 R_abs S T" (is "?R \<longleftrightarrow> ?R_abs")
proof
  assume ?R
  then have st: "R\<^sup>+\<^sup>+ (state S) (state T)" and ns: "no_step R (state T)" unfolding full1_def by auto
  have invT: "inv (state T)"
    using inv rtranclp_relation_invariant st by blast
  then have "R_abs\<^sup>+\<^sup>+ S T"
    using tranclp_relation_tranclp_relation_abs_compatible[OF st] inv
    tranclp_relation_compatible_eq[of S _ S T] cdcl\<^sub>W_mset.state_eq_sym by blast
  moreover have "no_step R_abs T"
    using ns inv no_step_iff invT by blast
  ultimately show ?R_abs
    unfolding full1_def by blast
next
  assume ?R_abs
  then have st: "R_abs\<^sup>+\<^sup>+ S T" and ns: "no_step R_abs T" unfolding full1_def by auto
  have "R\<^sup>+\<^sup>+ (state S) (state T)"
    using st tranclp_abs_tranclp inv by blast
  moreover
    have invT: "inv (state T)"
      using inv tranclp_relation_abs_invariant st by blast
    then have "no_step R (state T)"
      using ns inv no_step_iff by blast
  ultimately show ?R
    unfolding full1_def by blast
qed

lemma full1_iff_compatible:
  assumes inv: "inv (state S)" and SS': "S' \<sim>m state S" and TT': "T' \<sim>m state T"
  shows "full1 R S' T' \<longleftrightarrow> full1 R_abs S T" (is "?R \<longleftrightarrow> ?R_abs")
  using full1_iff assms unfolding cdcl\<^sub>W_mset_state_eq_eq by simp

lemma full_if_full_abs:
  assumes "inv (state S)" and "full R_abs S T"
  shows "full R (state S) (state T)"
  using assms full1_iff cdcl\<^sub>W_mset_state_eq_eq relation_compatible_abs
  unfolding full_unfold by blast

text \<open>The converse does \<^emph>\<open>not\<close> hold, since we cannot prove that @{term "S = T"} given
  @{term "state S = state S"}.\<close>
lemma full_abs_if_full:
  assumes "inv (state S)" and "full R (state S) (state T)"
  shows "full R_abs S T \<or> (state S \<sim>m state T \<and> no_step R (state S))"
  using assms full1_iff relation_compatible_abs unfolding full_unfold by auto

lemma full_exists_full_abs:
  assumes inv: "inv (state S)" and full: "full R (state S) T"
  obtains U where "full R_abs S U" and "T \<sim>m state U"
proof -
  consider
    (0)    "state S = T" and "no_step R (state S)" |
    (full1) "full1 R (state S) T"
  using full unfolding full_unfold cdcl\<^sub>W_mset_state_eq_eq by fast
  then show ?thesis
    proof cases
      case 0
      then show ?thesis using that[of S] unfolding full_def
        using cdcl\<^sub>W_mset.state_eq_ref inv relation_compatible_state rtranclp.rtrancl_refl by blast
    next
      case full1
      then obtain U where
        "R_abs\<^sup>+\<^sup>+ S U" and "T \<sim>m state U"
        using tranclp_relation_tranclp_relation_abs_compatible inv unfolding full1_def
        by blast
      then show ?thesis
        using full1 that[of U] full1_iff[OF inv] full1_is_full full_def
        unfolding cdcl\<^sub>W_mset_state_eq_eq by blast
    qed
qed

lemma full1_exists_full1_abs:
  assumes inv: "inv (state S)" and full1: "full1 R (state S) T"
  obtains U where "full1 R_abs S U" and "T \<sim>m state U"
proof -
  obtain U where
    "R_abs\<^sup>+\<^sup>+ S U" and "T \<sim>m state U"
    using tranclp_relation_tranclp_relation_abs_compatible inv full1 unfolding full1_def
    by blast
  then show ?thesis
    using full1 that[of U] full1_iff[OF inv] unfolding cdcl\<^sub>W_mset_state_eq_eq by blast
qed

lemma full1_right_compatible:
  assumes "inv (state S)" and
    full1: "full1 R_abs S T" and TV: "state T \<sim>m state V"
  shows "full1 R_abs S V"
  by (metis (full_types) TV assms(1) cdcl\<^sub>W_mset_state_eq_eq full1 full1_iff)

lemma full_right_compatible:
  assumes inv: "inv (state S)" and
    full_ST: "full R_abs S T" and TU: "state T \<sim>m state U"
  shows "full R_abs S U \<or> (S = T \<and> no_step R_abs S)"
proof -
  consider
    (0) "S = T" and "no_step R_abs T" |
    (full1) "full1 R_abs S T"
    using full_ST unfolding full_unfold by blast
  then show ?thesis
    proof cases
      case full1
      then show ?thesis
        using full1_right_compatible[OF inv, of T U] TU full_unfold by blast
    next
      case 0
      then show ?thesis by fast
    qed
qed

end

locale relation_relation_abs =
  fixes
    R :: "'v cdcl\<^sub>W_mset \<Rightarrow> 'v cdcl\<^sub>W_mset \<Rightarrow> bool" and
    R_abs :: "'st \<Rightarrow> 'st \<Rightarrow> bool" and
    state :: "'st \<Rightarrow> 'v cdcl\<^sub>W_mset" and
    inv :: "'v cdcl\<^sub>W_mset \<Rightarrow> bool"
  assumes
    relation_compatible_state:
      "inv (state S) \<Longrightarrow> R (state S) (state T) \<longleftrightarrow> R_abs S T" and
    relation_compatible_abs:
      "\<And>S S' T. inv S \<Longrightarrow> S \<sim>m state S' \<Longrightarrow> R S T \<Longrightarrow> \<exists>U. R_abs S' U \<and> T \<sim>m state U" and
    relation_invariant:
      "\<And>S T. R S T \<Longrightarrow> inv S \<Longrightarrow> inv T"
begin

lemma relation_compatible_eq:
  "inv (state S) \<Longrightarrow> R_abs S T \<Longrightarrow> state S \<sim>m state S' \<Longrightarrow> state T \<sim>m state T' \<Longrightarrow> R_abs S' T'"
  by (simp add: cdcl\<^sub>W_mset_state_eq_eq relation_compatible_state[symmetric])

lemma relation_right_compatible:
  "inv (state S) \<Longrightarrow> R_abs S T \<Longrightarrow> state T \<sim>m state U \<Longrightarrow> R_abs S U"
  by (simp add: cdcl\<^sub>W_mset_state_eq_eq relation_compatible_state[symmetric])


sublocale relation_implied_relation_abs
  apply unfold_locales
  using relation_compatible_eq relation_compatible_state relation_compatible_abs relation_invariant
  relation_right_compatible by blast+

end

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
    \<comment> \<open>Clause\<close>
    mset_cls :: "'cls \<Rightarrow> 'v clause" and

    \<comment> \<open>Multiset of Clauses\<close>
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
    add_conc_confl_to_learned_cls :: "'st \<Rightarrow> 'st" and
    remove_cls :: "'cls \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conc_backtrack_lvl :: "nat \<Rightarrow> 'st \<Rightarrow> 'st" and
    mark_conflicting :: "'ccls \<Rightarrow> 'st \<Rightarrow> 'st" and
    reduce_conc_trail_to :: "('v, 'v clause) ann_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    resolve_conflicting :: "'v literal \<Rightarrow> 'cls \<Rightarrow> 'st \<Rightarrow> 'st" and

    conc_init_state :: "'clss \<Rightarrow> 'st" and
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

definition state :: "'st \<Rightarrow> 'v cdcl\<^sub>W_mset" where
"state = (\<lambda>S. (conc_trail S, conc_init_clss S, conc_learned_clss S, conc_backtrack_lvl S,
  conc_conflicting S))"

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
  There are two different clause representation: one for the conflicting clause (@{typ "'ccls"},
  standing for conflicting clause) and one for the initial and learned clauses (@{typ "'cls"},
  standing for clause). The representation of the clauses annotating literals in the trail
  is slightly different: being able to convert it to @{typ "'v clause"} is enough (needed for
  function @{term "hd_raw_conc_trail"} below).

  There are several axioms to state the independance of the different fields of the state: for
  example, adding a clause to the learned clauses does not change the trail.

  We define the following operations on the elements
  \<^item> trail: @{term cons_trail}, @{term tl_trail}, and @{term reduce_conc_trail_to}.
  \<^item> initial set of clauses: none.
  \<^item> learned clauses: @{term add_conc_confl_to_learned_cls} moves the conflicting clause to the
  learned clauses.
  \<^item> backtrack level: it can be arbitrary set.
  \<^item> conflicting clause: there is @{term resolve_conflicting} that does a resolve step,
  @{term mark_conflicting} setting a conflict, and @{term add_conc_confl_to_learned_cls} setting
  the conflicting clause to @{term None}.\<close>
locale abs_state\<^sub>W =
  abs_state\<^sub>W_ops
    \<comment> \<open>functions for clauses: \<close>
    mset_cls
      mset_clss union_clss in_clss insert_clss remove_from_clss

    \<comment> \<open>functions for the conflicting clause:\<close>
    mset_ccls union_ccls remove_clit

    \<comment> \<open>Conversion between conflicting and non-conflicting\<close>
    ccls_of_cls cls_of_ccls

    \<comment> \<open>functions about the state:\<close>
      \<comment> \<open>getter:\<close>
    conc_trail hd_raw_conc_trail raw_conc_init_clss raw_conc_learned_clss conc_backtrack_lvl
    raw_conc_conflicting
      \<comment> \<open>setter:\<close>
    cons_conc_trail tl_conc_trail add_conc_confl_to_learned_cls remove_cls update_conc_backtrack_lvl
    mark_conflicting reduce_conc_trail_to resolve_conflicting

      \<comment> \<open>Some specific states:\<close>
    conc_init_state
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
    add_conc_confl_to_learned_cls :: "'st \<Rightarrow> 'st" and
    remove_cls :: "'cls \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conc_backtrack_lvl :: "nat \<Rightarrow> 'st \<Rightarrow> 'st" and
    mark_conflicting :: "'ccls \<Rightarrow> 'st \<Rightarrow> 'st" and
    reduce_conc_trail_to :: "('v, 'v clause) ann_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    resolve_conflicting :: "'v literal \<Rightarrow> 'cls \<Rightarrow> 'st \<Rightarrow> 'st" and

    conc_init_state :: "'clss \<Rightarrow> 'st" and
    restart_state :: "'st \<Rightarrow> 'st" +
  assumes
    \<comment> \<open>Definition of @{term hd_raw_trail}:\<close>
    hd_raw_conc_trail:
      "conc_trail S \<noteq> [] \<Longrightarrow> mmset_of_mlit (hd_raw_conc_trail S) = hd (conc_trail S)" and

    cons_conc_trail:
      "\<And>S'. undefined_lit (conc_trail st) (lit_of L) \<Longrightarrow>
        state st = (M, S') \<Longrightarrow>
        state (cons_conc_trail L st) = (mmset_of_mlit L # M, S')" and

    tl_conc_trail:
      "\<And>S'. state st = (M, S') \<Longrightarrow> state (tl_conc_trail st) = (tl M, S')" and

    remove_cls:
      "\<And>S'. state st = (M, N, U, S') \<Longrightarrow>
        state (remove_cls C st) =
          (M, removeAll_mset (mset_cls C) N, removeAll_mset (mset_cls C) U, S')" and

    add_conc_confl_to_learned_cls:
      "no_dup (conc_trail st) \<Longrightarrow> state st = (M, N, U, k, Some F) \<Longrightarrow>
        state (add_conc_confl_to_learned_cls st) =
          (M, N, {#F#} + U, k, None)" and

    update_conc_backtrack_lvl:
      "\<And>S'. state st = (M, N, U, k, S') \<Longrightarrow>
        state (update_conc_backtrack_lvl k' st) = (M, N, U, k', S')" and

    mark_conflicting:
      "state st = (M, N, U, k, None) \<Longrightarrow>
        state (mark_conflicting E st) = (M, N, U, k, Some (mset_ccls E))" and

    conc_conflicting_mark_conflicting[simp]:
      "raw_conc_conflicting (mark_conflicting E st) = Some E" and
    resolve_conflicting:
      "state st = (M, N, U, k, Some F) \<Longrightarrow> -L' \<in># F \<Longrightarrow> L' \<in># mset_cls D \<Longrightarrow>
        state (resolve_conflicting L' D st) =
          (M, N, U, k, Some (cdcl\<^sub>W_mset.resolve_cls L' F (mset_cls D)))" and

    conc_init_state:
      "state (conc_init_state Ns) = ([], mset_clss Ns, {#}, 0, None)" and

    \<comment> \<open>Properties about restarting @{term restart_state}:\<close>
    conc_trail_restart_state[simp]: "conc_trail (restart_state S) = []" and
    conc_init_clss_restart_state[simp]: "conc_init_clss (restart_state S) = conc_init_clss S" and
    conc_learned_clss_restart_state[intro]:
      "conc_learned_clss (restart_state S) \<subseteq># conc_learned_clss S" and
    conc_backtrack_lvl_restart_state[simp]: "conc_backtrack_lvl (restart_state S) = 0" and
    conc_conflicting_restart_state[simp]: "conc_conflicting (restart_state S) = None" and

    \<comment> \<open>Properties about @{term reduce_conc_trail_to}:\<close>
    reduce_conc_trail_to[simp]:
      "\<And>S'. conc_trail st = M2 @ M1 \<Longrightarrow> state st = (M, S') \<Longrightarrow>
        state (reduce_conc_trail_to M1 st) = (M1, S')"
begin

lemma
    \<comment> \<open>Properties about the trail @{term conc_trail}:\<close>
    conc_trail_cons_conc_trail[simp]:
      "undefined_lit (conc_trail st) (lit_of L) \<Longrightarrow>
        conc_trail (cons_conc_trail L st) = mmset_of_mlit L # conc_trail st" and
    conc_trail_tl_conc_trail[simp]:
      "conc_trail (tl_conc_trail st) = tl (conc_trail st)" and
    conc_trail_add_conc_confl_to_learned_cls[simp]:
      "no_dup (conc_trail st) \<Longrightarrow> conc_conflicting st \<noteq> None \<Longrightarrow>
        conc_trail (add_conc_confl_to_learned_cls st) = conc_trail st" and
    conc_trail_remove_cls[simp]:
      "conc_trail (remove_cls C st) = conc_trail st" and
    conc_trail_update_conc_backtrack_lvl[simp]:
      "conc_trail (update_conc_backtrack_lvl k st) = conc_trail st" and
    conc_trail_mark_conflicting[simp]:
      "raw_conc_conflicting st = None \<Longrightarrow> conc_trail (mark_conflicting E st) = conc_trail st" and
    conc_trail_resolve_conflicting[simp]:
      "conc_conflicting st = Some F \<Longrightarrow> -L' \<in># F \<Longrightarrow> L' \<in># mset_cls D \<Longrightarrow>
        conc_trail (resolve_conflicting L' D st) = conc_trail st" and

    \<comment> \<open>Properties about the initial clauses @{term conc_init_clss}:\<close>
    conc_init_clss_cons_conc_trail[simp]:
      "undefined_lit (conc_trail st) (lit_of L) \<Longrightarrow>
        conc_init_clss (cons_conc_trail L st) = conc_init_clss st"
      and
    conc_init_clss_tl_conc_trail[simp]:
      "conc_init_clss (tl_conc_trail st) = conc_init_clss st" and
    conc_init_clss_add_conc_confl_to_learned_cls[simp]:
      "no_dup (conc_trail st) \<Longrightarrow> conc_conflicting st \<noteq> None \<Longrightarrow>
        conc_init_clss (add_conc_confl_to_learned_cls st) = conc_init_clss st" and
    conc_init_clss_remove_cls[simp]:
      "conc_init_clss (remove_cls C st) = removeAll_mset (mset_cls C) (conc_init_clss st)" and
    conc_init_clss_update_conc_backtrack_lvl[simp]:
      "conc_init_clss (update_conc_backtrack_lvl k st) = conc_init_clss st" and
    conc_init_clss_mark_conflicting[simp]:
      "raw_conc_conflicting st = None \<Longrightarrow>
        conc_init_clss (mark_conflicting E st) = conc_init_clss st" and
    conc_init_clss_resolve_conflicting[simp]:
      "conc_conflicting st = Some F \<Longrightarrow> -L' \<in># F \<Longrightarrow> L' \<in># mset_cls D \<Longrightarrow>
        conc_init_clss (resolve_conflicting L' D st) = conc_init_clss st" and

    \<comment> \<open>Properties about the learned clauses @{term conc_learned_clss}:\<close>
    conc_learned_clss_cons_conc_trail[simp]:
      "undefined_lit (conc_trail st) (lit_of L) \<Longrightarrow>
        conc_learned_clss (cons_conc_trail L st) = conc_learned_clss st" and
    conc_learned_clss_tl_conc_trail[simp]:
      "conc_learned_clss (tl_conc_trail st) = conc_learned_clss st" and
    conc_learned_clss_add_conc_confl_to_learned_cls[simp]:
      "no_dup (conc_trail st) \<Longrightarrow> conc_conflicting st = Some C' \<Longrightarrow>
        conc_learned_clss (add_conc_confl_to_learned_cls st) = {#C'#} + conc_learned_clss st" and
    conc_learned_clss_remove_cls[simp]:
      "conc_learned_clss (remove_cls C st) = removeAll_mset (mset_cls C) (conc_learned_clss st)" and
    conc_learned_clss_update_conc_backtrack_lvl[simp]:
      "conc_learned_clss (update_conc_backtrack_lvl k st) = conc_learned_clss st" and
    conc_learned_clss_mark_conflicting[simp]:
      "raw_conc_conflicting st = None \<Longrightarrow>
        conc_learned_clss (mark_conflicting E st) = conc_learned_clss st" and
    conc_learned_clss_clss_resolve_conflicting[simp]:
      "conc_conflicting st = Some F \<Longrightarrow> -L' \<in># F \<Longrightarrow> L' \<in># mset_cls D \<Longrightarrow>
        conc_learned_clss (resolve_conflicting L' D st) = conc_learned_clss st" and

      \<comment> \<open>Properties about the backtracking level @{term conc_backtrack_lvl}:\<close>
    conc_backtrack_lvl_cons_conc_trail[simp]:
      "undefined_lit (conc_trail st) (lit_of L) \<Longrightarrow>
        conc_backtrack_lvl (cons_conc_trail L st) = conc_backtrack_lvl st" and
    conc_backtrack_lvl_tl_conc_trail[simp]:
      "conc_backtrack_lvl (tl_conc_trail st) = conc_backtrack_lvl st" and
    conc_backtrack_lvl_add_conc_confl_to_learned_cls[simp]:
      "no_dup (conc_trail st) \<Longrightarrow> conc_conflicting st \<noteq> None \<Longrightarrow>
        conc_backtrack_lvl (add_conc_confl_to_learned_cls st) = conc_backtrack_lvl st" and
    conc_backtrack_lvl_remove_cls[simp]:
      "conc_backtrack_lvl (remove_cls C st) = conc_backtrack_lvl st" and
    conc_backtrack_lvl_update_conc_backtrack_lvl[simp]:
      "conc_backtrack_lvl (update_conc_backtrack_lvl k st) = k" and
    conc_backtrack_lvl_mark_conflicting[simp]:
      "raw_conc_conflicting st = None \<Longrightarrow>
        conc_backtrack_lvl (mark_conflicting E st) = conc_backtrack_lvl st" and
    conc_backtrack_lvl_clss_clss_resolve_conflicting[simp]:
      "conc_conflicting st = Some F \<Longrightarrow> -L' \<in># F \<Longrightarrow> L' \<in># mset_cls D \<Longrightarrow>
        conc_backtrack_lvl (resolve_conflicting L' D st) = conc_backtrack_lvl st" and

      \<comment> \<open>Properties about the conflicting clause @{term conc_conflicting}:\<close>
    conc_conflicting_cons_conc_trail[simp]:
      "undefined_lit (conc_trail st) (lit_of L) \<Longrightarrow>
        conc_conflicting (cons_conc_trail L st) = conc_conflicting st" and
    conc_conflicting_tl_conc_trail[simp]:
      "conc_conflicting (tl_conc_trail st) = conc_conflicting st" and
    conc_conflicting_add_conc_confl_to_learned_cls[simp]:
      "no_dup (conc_trail st) \<Longrightarrow> conc_conflicting st = Some C' \<Longrightarrow>
        conc_conflicting (add_conc_confl_to_learned_cls st) = None"
      and
    raw_conc_conflicting_add_conc_confl_to_learned_cls[simp]:
      "no_dup (conc_trail st) \<Longrightarrow> conc_conflicting st = Some C' \<Longrightarrow>
        raw_conc_conflicting (add_conc_confl_to_learned_cls st) = None" and
    conc_conflicting_remove_cls[simp]:
      "conc_conflicting (remove_cls C st) = conc_conflicting st" and
    conc_conflicting_update_conc_backtrack_lvl[simp]:
      "conc_conflicting (update_conc_backtrack_lvl k st) = conc_conflicting st" and
    conc_conflicting_clss_clss_resolve_conflicting[simp]:
      "conc_conflicting st = Some F \<Longrightarrow> -L' \<in># F \<Longrightarrow> L' \<in># mset_cls D \<Longrightarrow>
        conc_conflicting (resolve_conflicting L' D st) =
          Some (cdcl\<^sub>W_mset.resolve_cls L' F (mset_cls D))" and

    \<comment> \<open>Properties about the initial state @{term conc_init_state}:\<close>
    conc_init_state_conc_trail[simp]: "conc_trail (conc_init_state Ns) = []" and
    conc_init_state_clss[simp]: "conc_init_clss (conc_init_state Ns) = mset_clss Ns" and
    conc_init_state_conc_learned_clss[simp]: "conc_learned_clss (conc_init_state Ns) = {#}" and
    conc_init_state_conc_backtrack_lvl[simp]: "conc_backtrack_lvl (conc_init_state Ns) = 0" and
    conc_init_state_conc_conflicting[simp]: "conc_conflicting (conc_init_state Ns) = None" and

    \<comment> \<open>Properties about @{term reduce_conc_trail_to}:\<close>
    trail_reduce_conc_trail_to[simp]:
      "conc_trail st = M2 @ M1 \<Longrightarrow> conc_trail (reduce_conc_trail_to M1 st) = M1" and
    conc_init_clss_reduce_conc_trail_to[simp]:
      "conc_trail st = M2 @ M1 \<Longrightarrow>
        conc_init_clss (reduce_conc_trail_to M1 st) = conc_init_clss st" and
    conc_learned_clss_reduce_conc_trail_to[simp]:
      "conc_trail st = M2 @ M1 \<Longrightarrow>
        conc_learned_clss (reduce_conc_trail_to M1 st) = conc_learned_clss st" and
    conc_backtrack_lvl_reduce_conc_trail_to[simp]:
      "conc_trail st = M2 @ M1 \<Longrightarrow>
        conc_backtrack_lvl (reduce_conc_trail_to M1 st) = conc_backtrack_lvl st" and
    conc_conflicting_reduce_conc_trail_to[simp]:
      "conc_trail st = M2 @ M1 \<Longrightarrow>
        conc_conflicting (reduce_conc_trail_to M1 st) = conc_conflicting st"
  using cons_conc_trail[of st L "conc_trail st" "snd (state st)"] tl_conc_trail[of st]
  add_conc_confl_to_learned_cls[of st  "conc_trail st" _ _ _ ]
  update_conc_backtrack_lvl[of st _ _ _ _ _ k]
  mark_conflicting[of st _ _ _ _ E]
  remove_cls[of st _ _ _ _ C]
  conc_init_state[of Ns]
  reduce_conc_trail_to[of st]
  resolve_conflicting[of st _ _ _ _ F L' D]
  unfolding state_def by auto
  (* TODO very slow ~ 12s, but very stupid proofs *)

lemma
  shows
    clauses_cons_conc_trail[simp]:
      "undefined_lit (conc_trail S) (lit_of L) \<Longrightarrow>
        conc_clauses (cons_conc_trail L S) = conc_clauses S" and
    (* non-standard to avoid name clash with NOT's clauses_tl_conc_trail *)
    clss_tl_conc_trail[simp]: "conc_clauses (tl_conc_trail S) = conc_clauses S" and
    clauses_update_conc_backtrack_lvl[simp]:
      "conc_clauses (update_conc_backtrack_lvl k S) = conc_clauses S" and
    clauses_mark_conflicting[simp]:
      "raw_conc_conflicting S = None \<Longrightarrow>
        conc_clauses (mark_conflicting D S) = conc_clauses S" and
    clauses_remove_cls[simp]:
      "conc_clauses (remove_cls C S) = removeAll_mset (mset_cls C) (conc_clauses S)" and
    clauses_add_conc_confl_to_learned_cls[simp]:
      "no_dup (conc_trail S) \<Longrightarrow> conc_conflicting S = Some C' \<Longrightarrow>
        conc_clauses (add_conc_confl_to_learned_cls S) = {#C'#} + conc_clauses S" and
    clauses_restart[simp]: "conc_clauses (restart_state S) \<subseteq># conc_clauses S" and
    clauses_conc_init_state[simp]: "\<And>N. conc_clauses (conc_init_state N) = mset_clss N"
    prefer 8 using raw_clauses_def conc_learned_clss_restart_state apply fastforce
    by (auto simp: ac_simps replicate_mset_plus raw_clauses_def intro: multiset_eqI)

abbreviation incr_lvl :: "'st \<Rightarrow> 'st" where
"incr_lvl S \<equiv> update_conc_backtrack_lvl (conc_backtrack_lvl S + 1) S"

abbreviation state_eq :: "'st \<Rightarrow> 'st \<Rightarrow> bool" (infix "\<sim>" 36) where
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
    state_eq_undefined_lit:
      "S \<sim> T \<Longrightarrow> undefined_lit (conc_trail S) L = undefined_lit (conc_trail T) L"
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
  "conc_trail S = M2 @ M1 \<Longrightarrow> conc_clauses (reduce_conc_trail_to M1 S) = conc_clauses S"
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

lemma raw_conc_conflicting_update_backtracl_lvl[simp]:
  "raw_conc_conflicting (update_conc_backtrack_lvl k S) = None \<longleftrightarrow> raw_conc_conflicting S = None"
  using map_option_is_None conc_conflicting_update_conc_backtrack_lvl[of k S] by fastforce+

end \<comment> \<open>end of \<open>state\<^sub>W\<close> locale\<close>


subsection \<open>CDCL Rules\<close>

locale abs_conflict_driven_clause_learning\<^sub>W =
  abs_state\<^sub>W
    \<comment> \<open>functions for clauses: \<close>
    mset_cls
    mset_clss union_clss in_clss insert_clss remove_from_clss

    \<comment> \<open>functions for the conflicting clause: \<close>
    mset_ccls union_ccls remove_clit

    \<comment> \<open>conversion\<close>
    ccls_of_cls cls_of_ccls

    \<comment> \<open>functions for the state: \<close>
      \<comment> \<open>access functions:\<close>
    conc_trail hd_raw_conc_trail raw_conc_init_clss raw_conc_learned_clss conc_backtrack_lvl
    raw_conc_conflicting
      \<comment> \<open>changing state:\<close>
    cons_conc_trail tl_conc_trail add_conc_confl_to_learned_cls remove_cls update_conc_backtrack_lvl
    mark_conflicting reduce_conc_trail_to resolve_conflicting

      \<comment> \<open>get state:\<close>
    conc_init_state
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
    add_conc_confl_to_learned_cls :: "'st \<Rightarrow> 'st" and
    remove_cls :: "'cls \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conc_backtrack_lvl :: "nat \<Rightarrow> 'st \<Rightarrow> 'st" and
    mark_conflicting :: "'ccls \<Rightarrow> 'st \<Rightarrow> 'st" and
    reduce_conc_trail_to :: "('v, 'v clause) ann_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    resolve_conflicting :: "'v literal \<Rightarrow> 'cls \<Rightarrow> 'st \<Rightarrow> 'st" and

    conc_init_state :: "'clss \<Rightarrow> 'st" and
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

lemma trail_state_add_conc_confl_to_learned_cls:
  "no_dup (conc_trail S) \<Longrightarrow> conc_conflicting S \<noteq> None \<Longrightarrow>
    trail (state (add_conc_confl_to_learned_cls S)) = trail (state S)"
  unfolding trail_def state_def by simp

lemma trail_state_update_backtrack_lvl:
  "trail (state (update_conc_backtrack_lvl i S)) = trail (state S)"
  unfolding trail_def state_def by simp

lemma trail_state_update_conflicting:
  "raw_conc_conflicting S = None \<Longrightarrow> trail (state (mark_conflicting i S)) = trail (state S)"
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

lemma add_learned_cls_state_add_conc_confl_to_learned_cls[simp]:
  assumes "no_dup (conc_trail S)" and "raw_conc_conflicting S = Some D"
  shows "update_conflicting None (add_learned_cls (mset_ccls D) (state S)) =
    state (add_conc_confl_to_learned_cls S)"
  using assms by (auto simp: cdcl\<^sub>W_mset_state state_def simp del: trail_state_conc_trail
    init_clss_state_conc_init_clss
    learned_clss_state_conc_learned_clss local.state_simp)

lemma state_cons_cons_trail_cons_trail[simp]:
  "undefined_lit (trail (state S)) (lit_of L) \<Longrightarrow>
    cons_trail (mmset_of_mlit L) (state S) = state (cons_conc_trail L S)"
  by (auto simp: cdcl\<^sub>W_mset_state state_def simp del: trail_state_conc_trail
    init_clss_state_conc_init_clss
    learned_clss_state_conc_learned_clss local.state_simp)

lemma state_cons_cons_trail_cons_trail_propagated[simp]:
  "undefined_lit (trail (state S)) K \<Longrightarrow>
    cons_trail (Propagated K (mset_cls C)) (state S) = state (cons_conc_trail (Propagated K C) S)"
  using state_cons_cons_trail_cons_trail[of S "Propagated K C"] by simp

lemma state_cons_cons_trail_cons_trail_propagated_ccls[simp]:
  "undefined_lit (trail (state S)) K \<Longrightarrow>
    cons_trail (Propagated K (mset_ccls C)) (state S) =
      state (cons_conc_trail (Propagated K (cls_of_ccls C)) S)"
  using state_cons_cons_trail_cons_trail[of S "Propagated K (cls_of_ccls C)"] by simp

lemma state_cons_cons_trail_cons_trail_decided[simp]:
  "undefined_lit (trail (state S)) K \<Longrightarrow>
    cons_trail (Decided K) (state S) = state (cons_conc_trail (Decided K) S)"
  using state_cons_cons_trail_cons_trail[of S "Decided K"] by simp

lemma state_mark_conflicting_update_conflicting[simp]:
  assumes "raw_conc_conflicting S = None"
  shows
    "update_conflicting (Some (mset_ccls D)) (state S) = state (mark_conflicting D S)"
    "update_conflicting (Some (mset_cls D')) (state S) =
      state (mark_conflicting ((ccls_of_cls D')) S)"
  using assms by (auto simp: cdcl\<^sub>W_mset_state state_def simp del: trail_state_conc_trail
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

lemma update_conflicting_resolve_state_mark_conflicting[simp]:
  "raw_conc_conflicting S = Some D' \<Longrightarrow>  -L \<in># mset_ccls D' \<Longrightarrow> L \<in># mset_cls E' \<Longrightarrow>
   update_conflicting (Some (remove1_mset (- L) (mset_ccls D') #\<union> remove1_mset L (mset_cls E')))
    (state (tl_conc_trail S)) =
   state (resolve_conflicting L E' (tl_conc_trail S))"
  by (auto simp: cdcl\<^sub>W_mset_state state_def simp del: trail_state_conc_trail
    init_clss_state_conc_init_clss
    learned_clss_state_conc_learned_clss local.state_simp)

lemma add_learned_update_backtrack_update_conflicting[simp]:
"no_dup (conc_trail S) \<Longrightarrow> raw_conc_conflicting S = Some D' \<Longrightarrow> add_learned_cls (mset_ccls D')
         (update_backtrack_lvl i
           (update_conflicting None
             (state S))) =
  state (add_conc_confl_to_learned_cls (update_conc_backtrack_lvl i S))"
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

lemma state_conc_init_state: "state (conc_init_state N) = init_state (mset_clss N)"
  by (auto simp: cdcl\<^sub>W_mset_state state_def simp del: trail_state_conc_trail
    init_clss_state_conc_init_clss
    learned_clss_state_conc_learned_clss local.state_simp)

text \<open>More robust version of @{thm [source] in_mset_clss_exists_preimage}:\<close>
lemma in_clauses_preimage:
  assumes b: "b \<in># cdcl\<^sub>W_mset.clauses (state C)"
  shows "\<exists>b'. b' !\<in>! raw_clauses C \<and> mset_cls b' = b"
proof -
  have "b \<in># conc_clauses C"
    using b by auto
  from in_mset_clss_exists_preimage[OF this] show ?thesis .
qed

lemma state_reduce_conc_trail_to_reduce_conc_trail_to_decomp[simp]:
  assumes "(P # M1, M2) \<in> set (get_all_ann_decomposition (conc_trail S))"
  shows "cdcl\<^sub>W_mset.reduce_trail_to M1 (state S) = state (reduce_conc_trail_to M1 S)"
  using assms by auto

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

lemma propagate_compatible_abs:
  assumes SS': "S \<sim>m state S'" and abs: "cdcl\<^sub>W_mset.propagate S T"
  obtains U where "propagate_abs S' U" and "T \<sim>m state U"
proof -
  obtain E L where
    confl: "conflicting S = None" and
    E: "E \<in># cdcl\<^sub>W_mset.clauses S" and
    L: "L \<in># E" and
    tr: "trail S \<Turnstile>as CNot (E - {#L#})" and
    undef: "undefined_lit (trail S) L" and
    T: "T \<sim>m cons_trail (Propagated L E) S"
    using abs by (auto elim!: cdcl\<^sub>W_mset.propagateE dest!: in_clauses_preimage
      simp: cdcl\<^sub>W_mset.clauses_def raw_clauses_def)
  then obtain E' where
    E': "E' !\<in>! raw_clauses S'" and [simp]: "E = mset_cls E'"
    by (metis SS' cdcl\<^sub>W_mset.state_eq_clauses in_clauses_preimage)
  let ?U = "cons_conc_trail (Propagated L E') S'"
  have "propagate_abs S' ?U"
    apply (rule propagate_abs_rule)
         using confl SS' apply simp
        using E' SS' apply simp
       using L apply simp
      using tr SS' apply simp
     using undef SS' apply simp
    using undef SS' by simp
  moreover have "T \<sim>m state ?U"
    using T SS' undef by (auto simp: cdcl\<^sub>W_mset_state_eq_eq)
  ultimately show thesis using that by blast
qed

interpretation propagate_abs: relation_relation_abs cdcl\<^sub>W_mset.propagate propagate_abs state
  "\<lambda>_. True"
  apply unfold_locales
   apply (simp add: propagate_propagate_abs)
  using propagate_compatible_abs by blast

inductive conflict_abs :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
conflict_abs_rule: "
  conc_conflicting S = None \<Longrightarrow>
  D !\<in>! raw_clauses S \<Longrightarrow>
  conc_trail S \<Turnstile>as CNot (mset_cls D) \<Longrightarrow>
  T \<sim> mark_conflicting (ccls_of_cls D) S \<Longrightarrow>
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
    T: "T \<sim> mark_conflicting (ccls_of_cls D) S"
    by (auto elim!: conflict_absE)
  show ?mset
    apply (rule cdcl\<^sub>W_mset.conflict_rule)
       using confl apply simp
      using D apply auto[]
     using tr_D apply simp
    using T confl apply auto
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
    using T confl by auto
qed

lemma conflict_compatible_abs:
  assumes SS': "S \<sim>m state S'" and conflict: "cdcl\<^sub>W_mset.conflict S T"
  obtains U where "conflict_abs S' U" and "T \<sim>m state U"
proof -
  obtain D where
    confl: "conflicting S = None" and
    D: "D \<in># cdcl\<^sub>W_mset.clauses S" and
    tr_D: "trail S \<Turnstile>as CNot D" and
    T: "T \<sim>m update_conflicting (Some D) S"
    using conflict by (auto elim: cdcl\<^sub>W_mset.conflictE)
  obtain D' where D': "D' !\<in>! raw_clauses S'" and DD'[simp]: "D = mset_cls D'"
    using D SS' by (auto dest!: in_mset_clss_exists_preimage)[]
  let ?U = "mark_conflicting (ccls_of_cls D') S'"
  have "conflict_abs S' ?U"
    apply (rule conflict_abs_rule)
       using confl SS' apply simp
      using D' SS' apply simp
     using tr_D SS' apply simp
    using T by auto
  moreover have "T \<sim>m state ?U"
    using T SS' confl by (auto simp: cdcl\<^sub>W_mset_state_eq_eq)
  ultimately show thesis using that[of ?U] by fast
qed

interpretation conflict_abs: relation_relation_abs cdcl\<^sub>W_mset.conflict conflict_abs state
  "\<lambda>_. True"
  apply unfold_locales
   apply (simp add: conflict_conflict_abs)
  using conflict_compatible_abs by metis

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
          (add_conc_confl_to_learned_cls
            (update_conc_backtrack_lvl i S))) \<Longrightarrow>
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
          (add_conc_confl_to_learned_cls
            (update_conc_backtrack_lvl i S)))"
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
    using T undef n_d tr D unfolding cdcl\<^sub>W_mset.state_eq_def
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
    using T undef n_d decomp confl' by auto
qed

lemma backtrack_exists_backtrack_abs_step:
  assumes bt: "cdcl\<^sub>W_mset.backtrack S T" and inv: "cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv S" and
   SS':  "S \<sim>m state S'"
  obtains U where "backtrack_abs S' U" and "T \<sim>m state U"
proof -
  from bt obtain L D K M1 M2 i where
    confl: "conflicting S = Some D" and
    L: "L \<in># D" and
    decomp: "(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S))" and
    lev_L: "get_level (trail S) L = backtrack_lvl S" and
    lev_max: "get_level (trail S) L = get_maximum_level (trail S) (D)" and
    i: "get_maximum_level (trail S) (D - {#L#}) \<equiv> i" and
    lev_K: "get_level (trail S) K = i + 1" and
    T: "T \<sim>m cons_trail (Propagated L (D))
          (cdcl\<^sub>W_mset.reduce_trail_to M1
            (add_learned_cls D
              (update_backtrack_lvl i
                (update_conflicting None S))))"
    by (auto elim: cdcl\<^sub>W_mset.backtrackE)
  obtain D' where
    confl': "raw_conc_conflicting S' = Some D'" and D[simp]: "D = mset_ccls D'"
    using confl SS' by auto
  have n_d: "no_dup (trail (state S'))"
    using lev_L inv SS' unfolding cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_mset.cdcl\<^sub>W_M_level_inv_def
    by simp
  have "atm_of L \<notin> atm_of ` lits_of_l M1"
    apply (rule cdcl\<^sub>W_mset.backtrack_lit_skiped[of _ "state S'"])
       using lev_L inv SS' unfolding cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_mset.cdcl\<^sub>W_M_level_inv_def
       apply simp
      using decomp SS' apply simp
     using lev_L inv SS' unfolding cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_mset.cdcl\<^sub>W_M_level_inv_def
       apply simp
    using lev_L inv SS' unfolding cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_mset.cdcl\<^sub>W_M_level_inv_def
       apply simp
   using lev_K SS' apply simp
   done
  then have undef: "undefined_lit M1 L"
    by (auto simp add: defined_lit_map lits_of_def)

  let ?U = "cons_conc_trail (Propagated L (cls_of_ccls D'))
          (reduce_conc_trail_to M1
            (add_conc_confl_to_learned_cls
              (update_conc_backtrack_lvl i S')))"
  have "backtrack_abs S' ?U"
    apply (rule backtrack_abs_rule)
           using confl' apply simp
          using L apply simp
         using decomp SS' apply simp
        using lev_L SS' apply simp
       using lev_max SS' apply simp
      using i SS' apply simp
     using lev_K  SS' apply simp
    using T undef n_d decomp by auto
  moreover have "T \<sim>m state ?U"
    using undef decomp T n_d SS'[unfolded cdcl\<^sub>W_mset_state_eq_eq] confl' by auto
  ultimately show thesis using that[of ?U] by fast
qed

interpretation backtrack_abs: relation_relation_abs cdcl\<^sub>W_mset.backtrack backtrack_abs state
  cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv
  apply unfold_locales
     apply (simp add: backtrack_backtrack_abs)
    using backtrack_exists_backtrack_abs_step apply metis
  using cdcl\<^sub>W_mset.backtrack cdcl\<^sub>W_mset.bj cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv_inv by blast

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

interpretation decide_abs: relation_relation_abs cdcl\<^sub>W_mset.decide decide_abs state
  "\<lambda>_. True"
  apply unfold_locales
     apply (simp add: decide_decide_abs)
    apply (metis (full_types) cdcl\<^sub>W_mset.decide.cases cdcl\<^sub>W_mset_state_eq_eq
      conc_trail_update_conc_backtrack_lvl decide_decide_abs
      state_cons_cons_trail_cons_trail_decided trail_state_conc_trail update_backtrack_lvl_state)
  using cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv_inv cdcl\<^sub>W_mset.decide cdcl\<^sub>W_mset.other by blast

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
  assumes skip: "cdcl\<^sub>W_mset.skip S T" and SS': "S \<sim>m state S'"
  obtains U where "skip_abs S' U" and "T \<sim>m state U"
proof -
  obtain L C' E M where
    tr: "trail S = Propagated L C' # M" and
    confl: "conflicting S = Some E" and
    L: "-L \<notin># E" and
    E: "E \<noteq> {#}" and
    T: "T \<sim>m tl_trail S"
    using skip by (auto elim: cdcl\<^sub>W_mset.skipE)
  obtain E' where
    confl': "raw_conc_conflicting S' = Some E'" and [simp]: "E = mset_ccls E'"
    using confl SS' by auto
  have "skip_abs S' (tl_conc_trail S')"
    apply (rule skip_abs_rule)
        using tr SS' apply simp
       using confl' SS' apply simp
      using L SS' apply simp
     using E apply simp
    using T by simp
  then show ?thesis
    using that[of "tl_conc_trail S'"] T SS'[unfolded cdcl\<^sub>W_mset_state_eq_eq ] by auto
qed

interpretation skip_abs: relation_relation_abs cdcl\<^sub>W_mset.skip skip_abs state
  "\<lambda>_. True"
  apply unfold_locales
     apply (simp add: skip_skip_abs)
    using skip_exists_skip_abs apply metis
  using cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv_inv cdcl\<^sub>W_mset.skip cdcl\<^sub>W_mset.other by blast

inductive resolve_abs :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
resolve_abs_rule: "conc_trail S \<noteq> [] \<Longrightarrow>
  hd_raw_conc_trail S = Propagated L E \<Longrightarrow>
  L \<in># mset_cls E \<Longrightarrow>
  raw_conc_conflicting S = Some D' \<Longrightarrow>
  -L \<in># mset_ccls D' \<Longrightarrow>
  get_maximum_level (conc_trail S) (mset_ccls (remove_clit (-L) D')) = conc_backtrack_lvl S \<Longrightarrow>
  T \<sim> resolve_conflicting L E (tl_conc_trail S) \<Longrightarrow>
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
    using T confl' LE LD by simp
next
  assume ?abs
  then show ?conc
    using hd_raw_conc_trail[of S] by (auto elim!: resolve_absE intro!: cdcl\<^sub>W_mset.resolve_rule)
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
  let ?U = "resolve_conflicting L E' (tl_conc_trail S')"
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
    using T SS' confl LE LD unfolding cdcl\<^sub>W_mset.state_eq_def by fastforce
  ultimately show thesis using that[of ?U] by fast
qed

interpretation resolve_abs: relation_relation_abs cdcl\<^sub>W_mset.resolve resolve_abs state
  "\<lambda>_. True"
  apply unfold_locales
     apply (simp add: resolve_resolve_abs)
    using resolve_exists_resolve_abs apply metis
  using cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv_inv cdcl\<^sub>W_mset.resolve cdcl\<^sub>W_mset.other by blast

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

lemma cdcl\<^sub>W_abs_bj_cdcl\<^sub>W_abs_bj:
  "cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv (state S) \<Longrightarrow>
    cdcl\<^sub>W_mset.cdcl\<^sub>W_bj (state S) (state T) \<longleftrightarrow> cdcl\<^sub>W_abs_bj S T"
  by (auto simp: cdcl\<^sub>W_mset.cdcl\<^sub>W_bj.simps cdcl\<^sub>W_abs_bj.simps
    backtrack_backtrack_abs skip_skip_abs resolve_resolve_abs)

interpretation cdcl\<^sub>W_abs_bj: relation_relation_abs cdcl\<^sub>W_mset.cdcl\<^sub>W_bj cdcl\<^sub>W_abs_bj state
  cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv
  apply unfold_locales
     apply (simp add: cdcl\<^sub>W_abs_bj_cdcl\<^sub>W_abs_bj)
    apply (metis (no_types, hide_lams) backtrack_exists_backtrack_abs_step cdcl\<^sub>W_abs_bj.simps
      cdcl\<^sub>W_mset.cdcl\<^sub>W_bj.simps resolve_exists_resolve_abs skip_abs.relation_compatible_abs)
  using cdcl\<^sub>W_mset.bj cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv_inv cdcl\<^sub>W_mset.other by blast

inductive cdcl\<^sub>W_abs_o :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
decide: "decide_abs S S' \<Longrightarrow> cdcl\<^sub>W_abs_o S S'" |
bj: "cdcl\<^sub>W_abs_bj S S' \<Longrightarrow> cdcl\<^sub>W_abs_o S S'"

inductive cdcl\<^sub>W_abs :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
propagate: "propagate_abs S S' \<Longrightarrow> cdcl\<^sub>W_abs S S'" |
conflict: "conflict_abs S S' \<Longrightarrow> cdcl\<^sub>W_abs S S'" |
other: "cdcl\<^sub>W_abs_o S S' \<Longrightarrow> cdcl\<^sub>W_abs S S'"|
rf: "cdcl\<^sub>W_abs_rf S S' \<Longrightarrow> cdcl\<^sub>W_abs S S'"

subsection \<open>Higher level strategy\<close>

text \<open>The rules described previously do not lead to a conclusive state. We have add a strategy and
  show the inclusion in the multiset version.\<close>

inductive cdcl\<^sub>W_merge_abs_cp :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
conflict': "conflict_abs S T \<Longrightarrow> full cdcl\<^sub>W_abs_bj T U \<Longrightarrow> cdcl\<^sub>W_merge_abs_cp S U" |
propagate': "propagate_abs\<^sup>+\<^sup>+ S S' \<Longrightarrow> cdcl\<^sub>W_merge_abs_cp S S'"

lemma cdcl\<^sub>W_merge_cp_cdcl\<^sub>W_abs_merge_cp:
  assumes
    cp: "cdcl\<^sub>W_merge_abs_cp S T" and
    inv: "cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv (state S)"
  shows "cdcl\<^sub>W_mset.cdcl\<^sub>W_merge_cp (state S) (state T)"
  using cp
proof (induction rule: cdcl\<^sub>W_merge_abs_cp.induct)
  case (conflict' T U) note confl = this(1) and bj = this(2)
  then have "cdcl\<^sub>W_mset.conflict (state S) (state T)"
    by (auto simp: conflict_conflict_abs propagate_propagate_abs cdcl\<^sub>W_abs_bj_cdcl\<^sub>W_abs_bj)
  moreover
    have "cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv (state T)"
      using cdcl\<^sub>W_mset.conflict cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv_inv confl inv
      unfolding conflict_conflict_abs[symmetric] by blast
    then have "full cdcl\<^sub>W_mset.cdcl\<^sub>W_bj (state T) (state U)"
      using bj by (auto simp: cdcl\<^sub>W_abs_bj.full_if_full_abs)
  ultimately show ?case by (auto intro: cdcl\<^sub>W_mset.cdcl\<^sub>W_merge_cp.intros)
next
  case (propagate' T)
  then show ?case
    by (auto simp: propagate_abs.tranclp_abs_tranclp intro: cdcl\<^sub>W_mset.cdcl\<^sub>W_merge_cp.propagate')
qed

lemma cdcl\<^sub>W_merge_cp_abs_exists_cdcl\<^sub>W_merge_cp:
  assumes
    cp: "cdcl\<^sub>W_mset.cdcl\<^sub>W_merge_cp (state S) T" and
    inv: "cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv (state S)"
  obtains U where "cdcl\<^sub>W_merge_abs_cp S U" and "T \<sim>m state U"
  using cp
proof (induction rule: cdcl\<^sub>W_mset.cdcl\<^sub>W_merge_cp.induct)
  case (conflict' T U) note confl = this(1) and bj = this(2) and that = this(3)

  obtain V where SV: "conflict_abs S V" and TV: "T \<sim>m state V"
    using conflict_abs.relation_compatible_abs[of "state S" S] confl by blast
  have inv_V: "cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv (state V)" and
    inv_T: "cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv T"
    using TV bj cdcl\<^sub>W_mset.cdcl\<^sub>W_stgy.simps cdcl\<^sub>W_mset.cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv
    cdcl\<^sub>W_mset.conflict_is_full1_cdcl\<^sub>W_cp confl inv unfolding cdcl\<^sub>W_mset_state_eq_eq by blast+
  then obtain T' where "full cdcl\<^sub>W_abs_bj V T'" and "U \<sim>m state T'"
    using TV bj cdcl\<^sub>W_abs_bj.full_exists_full_abs[of V U] unfolding cdcl\<^sub>W_mset_state_eq_eq
    by blast
  then show ?thesis using that cdcl\<^sub>W_merge_abs_cp.conflict'[of S V T'] SV by fast
next
  case (propagate' T)
  then show ?case
    using cdcl\<^sub>W_merge_abs_cp.propagate'
    propagate_abs.tranclp_relation_tranclp_relation_abs_compatible by blast
qed

lemma no_step_cdcl\<^sub>W_merge_cp_no_step_cdcl\<^sub>W_abs_merge_cp:
  assumes
    inv: "cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv (state S)"
  shows "no_step cdcl\<^sub>W_merge_abs_cp S \<longleftrightarrow> no_step cdcl\<^sub>W_mset.cdcl\<^sub>W_merge_cp (state S)"
  (is "?abs \<longleftrightarrow> ?conc")
proof
  assume ?abs
  show ?conc
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain T where "cdcl\<^sub>W_mset.cdcl\<^sub>W_merge_cp (state S) T"
        by blast
      then show False
        using cdcl\<^sub>W_merge_cp_abs_exists_cdcl\<^sub>W_merge_cp[of S T] \<open>?abs\<close>  inv by auto
    qed
next
  assume ?conc
  then show ?abs
    using cdcl\<^sub>W_merge_cp_cdcl\<^sub>W_abs_merge_cp inv by blast
qed

lemma cdcl\<^sub>W_merge_abs_cp_right_compatible:
  "cdcl\<^sub>W_merge_abs_cp S V \<Longrightarrow> cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv (state S) \<Longrightarrow>
  V \<sim> W \<Longrightarrow> cdcl\<^sub>W_merge_abs_cp S W"
proof (induction rule: cdcl\<^sub>W_merge_abs_cp.induct)
  case (conflict' T U) note confl = this(1) and full = this(2) and inv = this(3) and UW = this(4)
  have inv_T: "cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv (state T)"
    using cdcl\<^sub>W_mset.cdcl\<^sub>W_stgy.simps cdcl\<^sub>W_mset.cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv
    cdcl\<^sub>W_mset.conflict_is_full1_cdcl\<^sub>W_cp confl conflict_conflict_abs inv by blast
  then have "full cdcl\<^sub>W_abs_bj T W \<or> (T = U \<and> no_step cdcl\<^sub>W_abs_bj T)"
    using cdcl\<^sub>W_abs_bj.full_right_compatible[OF _ full UW] full by blast
  then consider
      (full) "full cdcl\<^sub>W_abs_bj T W" |
      (0) "T = U" and "no_step cdcl\<^sub>W_abs_bj T"
    by blast
  then show ?case
    proof cases
      case full
      then show ?thesis using confl by (blast intro: cdcl\<^sub>W_merge_abs_cp.intros)
    next
      case 0
      then have "conflict_abs S W" and "no_step cdcl\<^sub>W_abs_bj W"
         using confl UW conflict_abs.relation_right_compatible apply blast
        using full unfolding full_def
        by (metis (mono_tags, lifting) "0"(1) UW inv_T cdcl\<^sub>W_abs_bj_cdcl\<^sub>W_abs_bj
          cdcl\<^sub>W_mset_state_eq_eq)
      moreover then have "full cdcl\<^sub>W_abs_bj W W"
        unfolding full_def by auto
      ultimately show ?thesis by (blast intro: cdcl\<^sub>W_merge_abs_cp.intros)
    qed
next
  case (propagate')
  then show ?case using propagate_abs.tranclp_relation_compatible_eq
    by (blast intro: cdcl\<^sub>W_merge_abs_cp.propagate')
qed

interpretation cdcl\<^sub>W_merge_abs_cp: relation_implied_relation_abs
  cdcl\<^sub>W_mset.cdcl\<^sub>W_merge_cp cdcl\<^sub>W_merge_abs_cp state cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv
  apply unfold_locales
     using cdcl\<^sub>W_merge_cp_cdcl\<^sub>W_abs_merge_cp apply blast
    using cdcl\<^sub>W_merge_cp_abs_exists_cdcl\<^sub>W_merge_cp unfolding cdcl\<^sub>W_mset_state_eq_eq apply blast
   using cdcl\<^sub>W_mset.rtranclp_cdcl\<^sub>W_all_struct_inv_inv
   cdcl\<^sub>W_mset.rtranclp_cdcl\<^sub>W_merge_cp_rtranclp_cdcl\<^sub>W apply blast
  using cdcl\<^sub>W_merge_abs_cp_right_compatible unfolding cdcl\<^sub>W_mset_state_eq_eq by blast

inductive cdcl\<^sub>W_merge_abs_stgy for S :: 'st where
fw_s_cp: "full1 cdcl\<^sub>W_merge_abs_cp S T \<Longrightarrow> cdcl\<^sub>W_merge_abs_stgy S T" |
fw_s_decide: "decide_abs S T \<Longrightarrow> no_step cdcl\<^sub>W_merge_abs_cp S \<Longrightarrow> full cdcl\<^sub>W_merge_abs_cp T U
  \<Longrightarrow> cdcl\<^sub>W_merge_abs_stgy S U"


lemma cdcl\<^sub>W_cp_cdcl\<^sub>W_abs_cp:
  assumes stgy: "cdcl\<^sub>W_merge_abs_stgy S T" and
    inv: "cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv (state S)"
  shows "cdcl\<^sub>W_mset.cdcl\<^sub>W_merge_stgy (state S) (state T)"
  using stgy
proof (induction rule: cdcl\<^sub>W_merge_abs_stgy.induct)
  case (fw_s_cp T)
  show ?case
    apply (rule cdcl\<^sub>W_mset.cdcl\<^sub>W_merge_stgy.fw_s_cp)
    using fw_s_cp inv by (simp add: cdcl\<^sub>W_merge_abs_cp.full1_iff)
next
  case (fw_s_decide T U) note dec = this(1) and ns = this(2) and full = this(3)
  have dec': "cdcl\<^sub>W_mset.decide (state S) (state T)"
    using dec decide_decide_abs by blast
  then have "cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv (state T)"
    using inv cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv_inv
    by (blast dest: cdcl\<^sub>W_mset.cdcl\<^sub>W.other cdcl\<^sub>W_mset.cdcl\<^sub>W_o.decide)
  then have "full cdcl\<^sub>W_mset.cdcl\<^sub>W_merge_cp (state T) (state U)"
    using full cdcl\<^sub>W_merge_abs_cp.full_if_full_abs by blast
  then show ?case
    using dec' cdcl\<^sub>W_mset.cdcl\<^sub>W_merge_stgy.fw_s_decide[of "state S" "state T" "state U"] ns inv
    by (simp add: no_step_cdcl\<^sub>W_merge_cp_no_step_cdcl\<^sub>W_abs_merge_cp)
qed

lemma cdcl\<^sub>W_merge_abs_stgy_exists_cdcl\<^sub>W_merge_stgy:
  assumes
    inv: "cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv S" and
    SS': "S \<sim>m state S'" and
    st: "cdcl\<^sub>W_mset.cdcl\<^sub>W_merge_stgy S T"
  shows "\<exists>U. cdcl\<^sub>W_merge_abs_stgy S' U \<and> T \<sim>m state U"
  using st
proof (induction rule: cdcl\<^sub>W_mset.cdcl\<^sub>W_merge_stgy.induct)
  case (fw_s_cp T)
  then show ?case using cdcl\<^sub>W_merge_abs_cp.full1_exists_full1_abs[of S' T] inv
    unfolding SS'[unfolded cdcl\<^sub>W_mset_state_eq_eq] by (metis cdcl\<^sub>W_merge_abs_stgy.fw_s_cp)
next
  case (fw_s_decide T U) note dec = this(1) and n_s = this(2) and full = this(3)
  have SS': "S = state S'"
    using SS' unfolding cdcl\<^sub>W_mset_state_eq_eq .
  obtain T' where "decide_abs S' T'" and TT': "T \<sim>m state T'"
    using dec decide_abs.relation_compatible_abs[of S S' T] SS' by auto
  moreover
    have "cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv (state T')"
      using SS' calculation(1) cdcl\<^sub>W_mset.cdcl\<^sub>W.intros(3) cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv_inv
      cdcl\<^sub>W_mset.decide decide_decide_abs inv by blast
    then obtain U' where "full cdcl\<^sub>W_merge_abs_cp T' U'" and "U \<sim>m state U'"
      using full cdcl\<^sub>W_merge_abs_cp.full_exists_full_abs unfolding TT'[unfolded cdcl\<^sub>W_mset_state_eq_eq]
      by blast
  moreover have "no_step cdcl\<^sub>W_merge_abs_cp S'"
    using n_s cdcl\<^sub>W_merge_abs_cp.no_step_iff inv unfolding SS' by blast
  ultimately show ?case
    using cdcl\<^sub>W_merge_abs_stgy.fw_s_decide[of S' T' U'] by fast
qed

lemma cdcl\<^sub>W_merge_abs_stgy_right_compatible:
  assumes
    inv: "cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv (state S)" and
    st: "cdcl\<^sub>W_merge_abs_stgy S T" and
    TU: "T \<sim> V"
  shows "cdcl\<^sub>W_merge_abs_stgy S V"
  using st TU
proof (induction rule: cdcl\<^sub>W_merge_abs_stgy.induct)
  case (fw_s_cp T)
  then show ?thesis
    using cdcl\<^sub>W_merge_abs_cp.full1_right_compatible cdcl\<^sub>W_merge_abs_stgy.fw_s_cp inv by blast
next
  case (fw_s_decide T U) note dec = this(1) and n_s = this(2) and full = this(3) and UV = this(4)
  have inv_T: "cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv (state T)"
    using dec inv  cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv_inv[of "state S" "state T"]
    by (auto dest!: cdcl\<^sub>W_mset.cdcl\<^sub>W_o.decide cdcl\<^sub>W_mset.cdcl\<^sub>W.other
      simp: decide_decide_abs[symmetric])
  then have "full cdcl\<^sub>W_merge_abs_cp T V \<or> (T = U \<and> no_step cdcl\<^sub>W_merge_abs_cp T)"
    using cdcl\<^sub>W_merge_abs_cp.full_right_compatible[of T U V] full UV by blast
  then consider
    (full) "full cdcl\<^sub>W_merge_abs_cp T V" |
    (0) "T = U" and "no_step cdcl\<^sub>W_merge_abs_cp T"
    by blast
  then show ?case
    proof cases
      case full
      then show ?thesis
        using n_s dec by (blast intro: cdcl\<^sub>W_merge_abs_stgy.intros)
    next
      case 0 note TU = this(1) and n_s' = this(2)
      have "decide_abs S V"
        using TU dec UV decide_abs.relation_abs_right_compatible by auto
      moreover
        have "cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv (state V)"
          using inv_T by (metis (full_types) TU cdcl\<^sub>W_mset_state_eq_eq fw_s_decide.prems)
        then have "full cdcl\<^sub>W_merge_abs_cp V V"
          using n_s' TU UV[unfolded cdcl\<^sub>W_mset_state_eq_eq]
          unfolding full_def by (metis cdcl\<^sub>W_merge_abs_cp.no_step_iff rtranclp_unfold)
      ultimately show ?thesis using n_s by (blast intro: cdcl\<^sub>W_merge_abs_stgy.intros)
    qed
qed

interpretation cdcl\<^sub>W_merge_abs_stgy: relation_implied_relation_abs
  cdcl\<^sub>W_mset.cdcl\<^sub>W_merge_stgy cdcl\<^sub>W_merge_abs_stgy state cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv
  apply unfold_locales
     using cdcl\<^sub>W_cp_cdcl\<^sub>W_abs_cp apply blast
    using cdcl\<^sub>W_merge_abs_stgy_exists_cdcl\<^sub>W_merge_stgy apply blast
   using cdcl\<^sub>W_mset.cdcl\<^sub>W_merge_stgy_rtranclp_cdcl\<^sub>W cdcl\<^sub>W_mset.rtranclp_cdcl\<^sub>W_all_struct_inv_inv
   apply blast
  using cdcl\<^sub>W_merge_abs_stgy_right_compatible by blast

lemma cdcl\<^sub>W_merge_abs_stgy_final_State_conclusive:
  fixes T :: 'st
  assumes
    full: "full cdcl\<^sub>W_merge_abs_stgy (conc_init_state N) T" and
    n_d: "distinct_mset_mset (mset_clss N)"
  shows "(conc_conflicting T = Some {#} \<and> unsatisfiable (set_mset (mset_clss N)))
    \<or> (conc_conflicting T = None \<and> conc_trail T \<Turnstile>asm mset_clss N
      \<and> satisfiable (set_mset (mset_clss N)))"
proof -
  have "cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv (state (conc_init_state N))"
    using n_d unfolding cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv_def by (auto simp: state_conc_init_state)
  then show ?thesis
    using cdcl\<^sub>W_mset.full_cdcl\<^sub>W_merge_stgy_final_state_conclusive'[of "mset_clss N" "state T"]
    cdcl\<^sub>W_merge_abs_stgy.full_if_full_abs[of "conc_init_state N" T] full
    by (auto simp: state_conc_init_state n_d)
qed

end

end