theory CDCL_W_Incremental
imports CDCL_W_Full
begin

section \<open>Incremental SAT solving\<close>
locale state\<^sub>W_adding_init_clause_no_state =
  state\<^sub>W_no_state
    state_eq
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
  fixes
    add_init_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st"
  assumes
    add_init_cls:
      "state st = (M, N, U, S') \<Longrightarrow>
        state (add_init_cls C st) = (M, {#C#} + N, U, S')"

locale state\<^sub>W_adding_init_clause_ops =
  state\<^sub>W_adding_init_clause_no_state
    state_eq
    state
    \<comment> \<open>functions about the state:\<close>
      \<comment> \<open>getter:\<close>
    trail init_clss learned_clss conflicting
      \<comment> \<open>setter:\<close>
    cons_trail tl_trail add_learned_cls remove_cls update_conflicting

      \<comment> \<open>Some specific states:\<close>
    init_state
    add_init_cls
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

    init_state :: "'v clauses \<Rightarrow> 'st" and
    add_init_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" +
  assumes
    state_prop[simp]:
      \<open>state S = (trail S, init_clss S, learned_clss S, conflicting S, additional_info S)\<close>

locale state\<^sub>W_adding_init_clause =
  state\<^sub>W_adding_init_clause_ops
    state_eq
    state
    \<comment> \<open>functions about the state:\<close>
      \<comment> \<open>getter:\<close>
    trail init_clss learned_clss conflicting
      \<comment> \<open>setter:\<close>
    cons_trail tl_trail add_learned_cls remove_cls update_conflicting

      \<comment> \<open>Some specific states:\<close>
    init_state add_init_cls
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

    init_state :: "'v clauses \<Rightarrow> 'st" and
    add_init_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st"
begin

sublocale state\<^sub>W
  by unfold_locales auto

lemma
  trail_add_init_cls[simp]:
    "trail (add_init_cls C st) = trail st" and
  init_clss_add_init_cls[simp]:
    "init_clss (add_init_cls C st) = {#C#} + init_clss st"
    and
  learned_clss_add_init_cls[simp]:
    "learned_clss (add_init_cls C st) = learned_clss st" and
  conflicting_add_init_cls[simp]:
    "conflicting (add_init_cls C st) = conflicting st"
  using add_init_cls[of st _ _ _ _ C] by (cases "state st"; auto; fail)+

lemma clauses_add_init_cls[simp]:
   "clauses (add_init_cls N S) = {#N#} + init_clss S + learned_clss S"
   unfolding clauses_def by auto

lemma reduce_trail_to_add_init_cls[simp]:
  "trail (reduce_trail_to F (add_init_cls C S)) = trail (reduce_trail_to F S)"
  by (rule trail_eq_reduce_trail_to_eq) auto

lemma conflicting_add_init_cls_iff_conflicting[simp]:
  "conflicting (add_init_cls C S) = None \<longleftrightarrow> conflicting S = None"
  by fastforce+
end

locale conflict_driven_clause_learning_with_adding_init_clause\<^sub>W =
  state\<^sub>W_adding_init_clause
    state_eq
    state
    \<comment> \<open>functions for the state:\<close>
      \<comment> \<open>access functions:\<close>
    trail init_clss learned_clss conflicting
      \<comment> \<open>changing state:\<close>
    cons_trail tl_trail add_learned_cls remove_cls update_conflicting

      \<comment> \<open>get state:\<close>
    init_state
      \<comment> \<open>Adding a clause:\<close>
    add_init_cls
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

    init_state :: "'v clauses \<Rightarrow> 'st" and
    add_init_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st"
begin

sublocale conflict_driven_clause_learning\<^sub>W
  by unfold_locales

text \<open>This invariant holds all the invariant related to the strategy. See the structural invariant
    in @{term cdcl\<^sub>W_all_struct_inv}\<close>

text \<open>When we add a new clause, we reduce the trail until we get to tho first literal included in C.
  Then we can mark the conflict.\<close>
fun cut_trail_wrt_clause where
"cut_trail_wrt_clause C [] S = S" |
"cut_trail_wrt_clause C (Decided L # M) S =
  (if -L \<in># C then S
    else cut_trail_wrt_clause C M (tl_trail S))" |
"cut_trail_wrt_clause C (Propagated L _ # M) S =
  (if -L \<in># C then S
    else cut_trail_wrt_clause C M (tl_trail S))"

definition add_new_clause_and_update :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" where
"add_new_clause_and_update C S =
  (if trail S \<Turnstile>as CNot C
  then update_conflicting (Some C) (add_init_cls C
    (cut_trail_wrt_clause C (trail S) S))
  else add_init_cls C S)"

lemma init_clss_cut_trail_wrt_clause[simp]:
  "init_clss (cut_trail_wrt_clause C M S) = init_clss S"
  by (induction rule: cut_trail_wrt_clause.induct) auto

lemma learned_clss_cut_trail_wrt_clause[simp]:
  "learned_clss (cut_trail_wrt_clause C M S) = learned_clss S"
  by (induction rule: cut_trail_wrt_clause.induct) auto

lemma conflicting_clss_cut_trail_wrt_clause[simp]:
  "conflicting (cut_trail_wrt_clause C M S) = conflicting S"
  by (induction rule: cut_trail_wrt_clause.induct) auto

lemma trail_cut_trail_wrt_clause:
  "\<exists>M.  trail S = M @ trail (cut_trail_wrt_clause C (trail S) S)"
proof (induction "trail S" arbitrary: S rule: ann_lit_list_induct)
  case Nil
  then show ?case by simp
next
  case (Decided L M) note IH = this(1)[of "tl_trail S"] and M = this(2)[symmetric]
  then show ?case using Cons_eq_appendI by fastforce+
next
  case (Propagated L l M) note IH = this(1)[of "tl_trail S"] and M = this(2)[symmetric]
  then show ?case using Cons_eq_appendI by fastforce+
qed

lemma n_dup_no_dup_trail_cut_trail_wrt_clause[simp]:
  assumes n_d: "no_dup (trail T)"
  shows "no_dup (trail (cut_trail_wrt_clause C (trail T) T))"
proof -
  obtain M where
    M: "trail T = M @ trail (cut_trail_wrt_clause C (trail T) T)"
    using trail_cut_trail_wrt_clause[of T C] by auto
  show ?thesis
    using n_d unfolding arg_cong[OF M, of no_dup] by (auto simp: no_dup_def)
qed

lemma cut_trail_wrt_clause_backtrack_lvl_length_decided:
  assumes
     "backtrack_lvl T = count_decided (trail T)"
  shows
    "backtrack_lvl (cut_trail_wrt_clause C (trail T) T) =
      count_decided (trail (cut_trail_wrt_clause C (trail T) T))"
  using assms
proof (induction "trail T" arbitrary:T rule: ann_lit_list_induct)
  case Nil
  then show ?case by simp
next
  case (Decided L M) note IH = this(1)[of "tl_trail T"] and M = this(2)[symmetric]
    and bt = this(3)
  then show ?case by auto
next
  case (Propagated L l M) note IH = this(1)[of "tl_trail T"] and M = this(2)[symmetric] and
    bt = this(3)
  then show ?case by auto
qed

lemma cut_trail_wrt_clause_CNot_trail:
  assumes "trail T \<Turnstile>as CNot C"
  shows
    "(trail ((cut_trail_wrt_clause C (trail T) T))) \<Turnstile>as CNot C"
  using assms
proof (induction "trail T" arbitrary: T rule: ann_lit_list_induct)
  case Nil
  then show ?case by simp
next
  case (Decided L M) note IH = this(1)[of "tl_trail T"] and M = this(2)[symmetric]
    and bt = this(3)
  show ?case
    proof (cases "count C (-L) = 0")
      case False
      then show ?thesis
        using IH M bt by (auto simp: true_annots_true_cls)
    next
      case True
      obtain mma :: "'v clause" where
        f6: "(mma \<in> {{#- l#} |l. l \<in># C} \<longrightarrow> M \<Turnstile>a mma) \<longrightarrow> M \<Turnstile>as {{#- l#} |l. l \<in># C}"
        using true_annots_def by blast
      have "mma \<in> {{#- l#} |l. l \<in># C} \<longrightarrow> trail T \<Turnstile>a mma"
        using CNot_def M bt by (metis (no_types) true_annots_def)
      then have "M \<Turnstile>as {{#- l#} |l. l \<in># C}"
        using f6 True M bt by (force simp: count_eq_zero_iff)
      then show ?thesis
        using IH true_annots_true_cls M by (auto simp: CNot_def)
    qed
next
  case (Propagated L l M) note IH = this(1)[of "tl_trail T"] and M = this(2)[symmetric] and bt = this(3)
  show ?case
    proof (cases "count C (-L) = 0")
      case False
      then show ?thesis
        using IH M bt by (auto simp: true_annots_true_cls)
    next
      case True
      obtain mma :: "'v clause" where
        f6: "(mma \<in> {{#- l#} |l. l \<in># C} \<longrightarrow> M \<Turnstile>a mma) \<longrightarrow> M \<Turnstile>as {{#- l#} |l. l \<in># C}"
        using true_annots_def by blast
      have "mma \<in> {{#- l#} |l. l \<in># C} \<longrightarrow> trail T \<Turnstile>a mma"
        using CNot_def M bt by (metis (no_types) true_annots_def)
      then have "M \<Turnstile>as {{#- l#} |l. l \<in># C}"
        using f6 True M bt by (force simp: count_eq_zero_iff)
      then show ?thesis
        using IH true_annots_true_cls M by (auto simp: CNot_def)
    qed
qed

lemma cut_trail_wrt_clause_hd_trail_in_or_empty_trail:
  "((\<forall>L \<in>#C. -L \<notin> lits_of_l (trail T)) \<and> trail (cut_trail_wrt_clause C (trail T) T) = [])
    \<or> (-lit_of (hd (trail (cut_trail_wrt_clause C (trail T) T))) \<in># C
       \<and> length (trail (cut_trail_wrt_clause C (trail T) T)) \<ge> 1)"
proof (induction "trail T" arbitrary:T rule: ann_lit_list_induct)
  case Nil
  then show ?case by simp
next
  case (Decided L M) note IH = this(1)[of "tl_trail T"] and M = this(2)[symmetric]
  then show ?case by simp force
next
  case (Propagated L l M) note IH = this(1)[of "tl_trail T"] and M = this(2)[symmetric]
  then show ?case by simp force
qed

text \<open>We can fully run @{term cdcl\<^sub>W_restart_s} or add a clause. Remark that we use @{term cdcl\<^sub>W_restart_s} to avoid
an explicit @{term skip}, @{term resolve}, and @{term backtrack} normalisation to get rid of the
conflict @{term C} if possible.\<close>
inductive incremental_cdcl\<^sub>W :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S where
add_confl:
  "trail S \<Turnstile>asm init_clss S \<Longrightarrow> distinct_mset C \<Longrightarrow> conflicting S = None \<Longrightarrow>
   trail S \<Turnstile>as CNot C \<Longrightarrow>
   full cdcl\<^sub>W_stgy
     (update_conflicting (Some C)
       (add_init_cls C (cut_trail_wrt_clause C (trail S) S))) T \<Longrightarrow>
   incremental_cdcl\<^sub>W S T" |
add_no_confl:
  "trail S \<Turnstile>asm init_clss S \<Longrightarrow> distinct_mset C \<Longrightarrow> conflicting S = None \<Longrightarrow>
   \<not>trail S \<Turnstile>as CNot C \<Longrightarrow>
   full cdcl\<^sub>W_stgy (add_init_cls C S) T \<Longrightarrow>
   incremental_cdcl\<^sub>W S T"

lemma cdcl\<^sub>W_all_struct_inv_add_new_clause_and_update_cdcl\<^sub>W_all_struct_inv:
  assumes
    inv_T: "cdcl\<^sub>W_all_struct_inv T" and
    tr_T_N[simp]: "trail T \<Turnstile>asm N" and
    tr_C[simp]: "trail T \<Turnstile>as CNot C" and
    [simp]: "distinct_mset C"
  shows "cdcl\<^sub>W_all_struct_inv (add_new_clause_and_update C T)" (is "cdcl\<^sub>W_all_struct_inv ?T'")
proof -
  let ?T = "update_conflicting (Some C)
    (add_init_cls C (cut_trail_wrt_clause C (trail T) T))"
  obtain M where
    M: "trail T = M @ trail (cut_trail_wrt_clause C (trail T) T)"
      using trail_cut_trail_wrt_clause[of T "C"] by blast
  have H[dest]: "\<And>x. x \<in> lits_of_l (trail (cut_trail_wrt_clause C (trail T) T)) \<Longrightarrow>
    x \<in> lits_of_l (trail T)"
    using inv_T arg_cong[OF M, of lits_of_l] by auto
  have H'[dest]: "\<And>x. x \<in> set (trail (cut_trail_wrt_clause C (trail T) T)) \<Longrightarrow>
    x \<in> set (trail T)"
    using inv_T arg_cong[OF M, of set] by auto

  have H_proped:"\<And>x. x \<in> set (get_all_mark_of_propagated (trail (cut_trail_wrt_clause C
   (trail T) T))) \<Longrightarrow> x \<in> set (get_all_mark_of_propagated (trail T))"
  using inv_T arg_cong[OF M, of get_all_mark_of_propagated] by auto

  have [simp]: "no_strange_atm ?T"
    using inv_T unfolding cdcl\<^sub>W_all_struct_inv_def no_strange_atm_def add_new_clause_and_update_def
    cdcl\<^sub>W_M_level_inv_def by (auto 20 1)
  have M_lev: "cdcl\<^sub>W_M_level_inv T"
    using inv_T unfolding cdcl\<^sub>W_all_struct_inv_def by blast
  then have "no_dup (M @ trail (cut_trail_wrt_clause C (trail T) T))"
    unfolding cdcl\<^sub>W_M_level_inv_def unfolding M[symmetric] by auto
  then have [simp]: "no_dup (trail (cut_trail_wrt_clause C (trail T) T))"
    by (auto simp: no_dup_def)

  have "consistent_interp (lits_of_l (M @ trail (cut_trail_wrt_clause C (trail T) T)))"
    using M_lev unfolding cdcl\<^sub>W_M_level_inv_def unfolding M[symmetric] by auto
  then have [simp]: "consistent_interp (lits_of_l (trail (cut_trail_wrt_clause C
    (trail T) T)))"
    unfolding consistent_interp_def by auto

  have [simp]: "cdcl\<^sub>W_M_level_inv ?T"
    using M_lev unfolding cdcl\<^sub>W_M_level_inv_def
    by (auto simp: M_lev cdcl\<^sub>W_M_level_inv_def cut_trail_wrt_clause_backtrack_lvl_length_decided)

  have [simp]: "\<And>s. s \<in># learned_clss T \<Longrightarrow> \<not>tautology s"
    using inv_T unfolding cdcl\<^sub>W_all_struct_inv_def by auto

  have "distinct_cdcl\<^sub>W_state T"
    using inv_T unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  then have [simp]: "distinct_cdcl\<^sub>W_state ?T"
    unfolding distinct_cdcl\<^sub>W_state_def by auto

  have "cdcl\<^sub>W_conflicting T"
    using inv_T unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  have "trail ?T \<Turnstile>as CNot C"
     by (simp add: cut_trail_wrt_clause_CNot_trail)
  then have [simp]: "cdcl\<^sub>W_conflicting ?T"
    unfolding cdcl\<^sub>W_conflicting_def apply simp
    by (metis M \<open>cdcl\<^sub>W_conflicting T\<close> append_assoc cdcl\<^sub>W_conflicting_decomp(2))

  have
    decomp_T: "all_decomposition_implies_m (clauses T) (get_all_ann_decomposition (trail T))"
    using inv_T unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  have "all_decomposition_implies_m (clauses ?T) (get_all_ann_decomposition (trail ?T))"
    unfolding all_decomposition_implies_def
    proof clarify
      fix a b
      assume "(a, b) \<in> set (get_all_ann_decomposition (trail ?T))"
      from in_get_all_ann_decomposition_in_get_all_ann_decomposition_prepend[OF this, of M]
      obtain b' where
        "(a, b' @ b) \<in> set (get_all_ann_decomposition (trail T))"
        using M by auto
      then have "unmark_l a \<union> set_mset (clauses T) \<Turnstile>ps unmark_l (b' @ b)"
        using decomp_T unfolding all_decomposition_implies_def by fastforce
      then have "unmark_l a \<union> set_mset (clauses ?T) \<Turnstile>ps unmark_l (b' @ b)"
        by (simp add: clauses_def)
      then show "unmark_l a \<union> set_mset (clauses ?T) \<Turnstile>ps unmark_l b"
        by (auto simp: image_Un)
    qed

  have [simp]: "cdcl\<^sub>W_learned_clause ?T"
    using inv_T unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_learned_clause_alt_def
    by (auto dest!: H_proped simp: clauses_def)
  show ?thesis
    using \<open>all_decomposition_implies_m (clauses ?T) (get_all_ann_decomposition (trail ?T))\<close>
    unfolding cdcl\<^sub>W_all_struct_inv_def by (auto simp: add_new_clause_and_update_def)
qed

lemma cdcl\<^sub>W_all_struct_inv_add_new_clause_and_update_cdcl\<^sub>W_stgy_inv:
  assumes
    inv_s: "cdcl\<^sub>W_stgy_invariant T" and
    inv: "cdcl\<^sub>W_all_struct_inv T" and
    tr_T_N[simp]: "trail T \<Turnstile>asm N" and
    tr_C[simp]: "trail T \<Turnstile>as CNot C" and
    [simp]: "distinct_mset C"
  shows "cdcl\<^sub>W_stgy_invariant (add_new_clause_and_update C T)"
    (is "cdcl\<^sub>W_stgy_invariant ?T'")
proof -
  have "cdcl\<^sub>W_all_struct_inv ?T'"
    using cdcl\<^sub>W_all_struct_inv_add_new_clause_and_update_cdcl\<^sub>W_all_struct_inv assms by blast
  then have
    no_dup_cut_T[simp]: "no_dup (trail (cut_trail_wrt_clause C (trail T) T))" and
    n_d[simp]: "no_dup (trail T)"
    using cdcl\<^sub>W_M_level_inv_decomp(2) cdcl\<^sub>W_all_struct_inv_def inv
    n_dup_no_dup_trail_cut_trail_wrt_clause by blast+
  then have "trail (add_new_clause_and_update C T) \<Turnstile>as CNot C"
    by (simp add: add_new_clause_and_update_def cut_trail_wrt_clause_CNot_trail
      cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_all_struct_inv_def)
  obtain MT where
    MT: "trail T = MT @  trail (cut_trail_wrt_clause C (trail T) T)"
    using trail_cut_trail_wrt_clause by blast
  consider
      (false) "\<forall>L\<in>#C. - L \<notin> lits_of_l (trail T)" and
        "trail (cut_trail_wrt_clause C (trail T) T) = []" |
      (not_false)
        "- lit_of (hd (trail (cut_trail_wrt_clause C (trail T) T))) \<in># C" and
        "1 \<le> length (trail (cut_trail_wrt_clause C (trail T) T))"
    using cut_trail_wrt_clause_hd_trail_in_or_empty_trail[of "C" T] by auto
  then show ?thesis
    proof cases
      case false note C = this(1) and empty_tr = this(2)
      then have [simp]: "C = {#}"
        by (simp add: in_CNot_implies_uminus(2) multiset_eqI)
      show ?thesis
        using empty_tr unfolding cdcl\<^sub>W_stgy_invariant_def no_smaller_confl_def
        cdcl\<^sub>W_all_struct_inv_def by (auto simp: add_new_clause_and_update_def)
    next
      case not_false note C = this(1) and l = this(2)
      let ?L = "- lit_of (hd (trail (cut_trail_wrt_clause C (trail T) T)))"
      have L: "get_level (trail (cut_trail_wrt_clause C (trail T) T)) (-?L)
        = count_decided (trail (cut_trail_wrt_clause C (trail T) T))"
        apply (cases "trail (add_init_cls C
            (cut_trail_wrt_clause C (trail T) T))";
         cases "hd (trail (cut_trail_wrt_clause C (trail T) T))")
        using l by (auto split: if_split_asm
          simp:rev_swap[symmetric] add_new_clause_and_update_def)

      have L': "count_decided(trail (cut_trail_wrt_clause C
        (trail T) T))
        = backtrack_lvl (cut_trail_wrt_clause C (trail T) T)"
        using \<open>cdcl\<^sub>W_all_struct_inv ?T'\<close> unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def
        by (auto simp:add_new_clause_and_update_def)

      have [simp]: "no_smaller_confl (update_conflicting (Some C)
        (add_init_cls C (cut_trail_wrt_clause C (trail T) T)))"
        unfolding no_smaller_confl_def
      proof (clarify, goal_cases)
        case (1 M K M' D)
        then consider
            (DC) "D = C"
          | (D_T) "D \<in># clauses T"
          by (auto simp: clauses_def split: if_split_asm)
        then show False
          proof cases
            case D_T
            have "no_smaller_confl T"
              using inv_s unfolding cdcl\<^sub>W_stgy_invariant_def by auto
            have "trail T = (MT @ M') @ Decided K # M"
              using MT 1(1) by auto
            then show False
              using D_T \<open>no_smaller_confl T\<close> 1(3) unfolding no_smaller_confl_def by blast
          next
            case DC note _[simp] = this
            then have "atm_of (-?L) \<in> atm_of ` (lits_of_l M)"
              using 1(3) C in_CNot_implies_uminus(2) by blast
            moreover
              have "lit_of (hd (M' @ Decided K # [])) = -?L"
                using l 1(1)[symmetric] inv
                by (cases M', cases "trail (add_init_cls C
                    (cut_trail_wrt_clause C (trail T) T))")
                (auto dest!: arg_cong[of "_ # _" _ hd] simp: hd_append cdcl\<^sub>W_all_struct_inv_def
                  cdcl\<^sub>W_M_level_inv_def)
              from arg_cong[OF this, of atm_of]
              have "atm_of (-?L) \<in> atm_of ` (lits_of_l (M' @ Decided K # []))"
                by (cases " (M' @ Decided K # [])") auto
            moreover have "no_dup (trail (cut_trail_wrt_clause C (trail T) T))"
              using \<open>cdcl\<^sub>W_all_struct_inv ?T'\<close> unfolding cdcl\<^sub>W_all_struct_inv_def
              cdcl\<^sub>W_M_level_inv_def by (auto simp: add_new_clause_and_update_def)
            ultimately show False
              unfolding 1(1)[simplified] by (auto simp: lits_of_def no_dup_def)
        qed
      qed
      show ?thesis using L L' C
        unfolding cdcl\<^sub>W_stgy_invariant_def cdcl\<^sub>W_all_struct_inv_def
        by (auto simp: add_new_clause_and_update_def get_level_def count_decided_def intro: rev_bexI)
    qed
qed

lemma incremental_cdcl\<^sub>W_inv:
  assumes
    inc: "incremental_cdcl\<^sub>W S T" and
    inv: "cdcl\<^sub>W_all_struct_inv S" and
    s_inv: "cdcl\<^sub>W_stgy_invariant S" and
    learned_entailed: \<open>cdcl\<^sub>W_learned_clauses_entailed_by_init S\<close>
  shows
    "cdcl\<^sub>W_all_struct_inv T" and
    "cdcl\<^sub>W_stgy_invariant T" and
    learned_entailed: \<open>cdcl\<^sub>W_learned_clauses_entailed_by_init T\<close>
  using inc
proof induction
  case (add_confl C T)
  let ?T = "(update_conflicting (Some C) (add_init_cls C
    (cut_trail_wrt_clause C (trail S) S)))"
  have inv': "cdcl\<^sub>W_all_struct_inv ?T" and inv_s_T: "cdcl\<^sub>W_stgy_invariant ?T"
    using add_confl.hyps(1,2,4) add_new_clause_and_update_def
    cdcl\<^sub>W_all_struct_inv_add_new_clause_and_update_cdcl\<^sub>W_all_struct_inv inv apply auto[1]
    using add_confl.hyps(1,2,4) add_new_clause_and_update_def
    cdcl\<^sub>W_all_struct_inv_add_new_clause_and_update_cdcl\<^sub>W_stgy_inv inv s_inv by auto
  case 1 show ?case
     by (metis add_confl.hyps(1,2,4,5) add_new_clause_and_update_def
       cdcl\<^sub>W_all_struct_inv_add_new_clause_and_update_cdcl\<^sub>W_all_struct_inv
       rtranclp_cdcl\<^sub>W_all_struct_inv_inv rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart full_def inv)

  case 2 show ?case
    by (metis inv_s_T add_confl.hyps(1,2,4,5) add_new_clause_and_update_def
      cdcl\<^sub>W_all_struct_inv_add_new_clause_and_update_cdcl\<^sub>W_all_struct_inv full_def inv
      rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_stgy_invariant)

  case 3 show ?case
    using learned_entailed rtranclp_cdcl\<^sub>W_learned_clauses_entailed[of ?T T]  add_confl inv'
    unfolding cdcl\<^sub>W_all_struct_inv_def full_def
    by (auto simp: cdcl\<^sub>W_learned_clauses_entailed_by_init_def
        dest!: rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart)
next
  case (add_no_confl C T)
  have inv': "cdcl\<^sub>W_all_struct_inv (add_init_cls C S)"
    using inv \<open>distinct_mset C\<close> unfolding cdcl\<^sub>W_all_struct_inv_def no_strange_atm_def
    cdcl\<^sub>W_M_level_inv_def distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_conflicting_def cdcl\<^sub>W_learned_clause_alt_def
    by (auto 9 1 simp: all_decomposition_implies_insert_single clauses_def)
    (* SLOW ~2s *)
  case 1
  show ?case
    using inv' add_no_confl(5) unfolding full_def by (auto intro: rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv)

  case 2
  have nc: "\<forall>M. (\<exists>K i M'. trail S = M' @ Decided K # M) \<longrightarrow> \<not> M \<Turnstile>as CNot C"
    using \<open>\<not> trail S \<Turnstile>as CNot C\<close>
    by (auto simp: true_annots_true_cls_def_iff_negation_in_model)

  have "cdcl\<^sub>W_stgy_invariant (add_init_cls C S)"
    using s_inv \<open>\<not> trail S \<Turnstile>as CNot C\<close> inv unfolding cdcl\<^sub>W_stgy_invariant_def
    no_smaller_confl_def eq_commute[of "_" "trail _"] cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_all_struct_inv_def
    by (auto simp: clauses_def nc)
  then show ?case
    by (metis \<open>cdcl\<^sub>W_all_struct_inv (add_init_cls C S)\<close> add_no_confl.hyps(5) full_def
      rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_stgy_invariant)

  case 3
  have \<open>cdcl\<^sub>W_learned_clauses_entailed_by_init (add_init_cls C S)\<close>
    using learned_entailed by (auto simp: cdcl\<^sub>W_learned_clauses_entailed_by_init_def)
  then show ?case
    using add_no_confl(5) learned_entailed rtranclp_cdcl\<^sub>W_learned_clauses_entailed[of _ T]  add_confl inv'
    unfolding cdcl\<^sub>W_all_struct_inv_def full_def
    by (auto simp: cdcl\<^sub>W_learned_clauses_entailed_by_init_def
        dest!: rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart)
qed

lemma rtranclp_incremental_cdcl\<^sub>W_inv:
  assumes
    inc: "incremental_cdcl\<^sub>W\<^sup>*\<^sup>* S T" and
    inv: "cdcl\<^sub>W_all_struct_inv S" and
    s_inv: "cdcl\<^sub>W_stgy_invariant S" and
    learned_entailed: \<open>cdcl\<^sub>W_learned_clauses_entailed_by_init S\<close>
  shows
    "cdcl\<^sub>W_all_struct_inv T" and
    "cdcl\<^sub>W_stgy_invariant T" and
    \<open>cdcl\<^sub>W_learned_clauses_entailed_by_init T\<close>
     using inc apply induction
    using inv apply simp
   using s_inv apply simp
   using learned_entailed apply simp
  using incremental_cdcl\<^sub>W_inv by blast+

lemma incremental_conclusive_state:
  assumes
    inc: "incremental_cdcl\<^sub>W S T" and
    inv: "cdcl\<^sub>W_all_struct_inv S" and
    s_inv: "cdcl\<^sub>W_stgy_invariant S" and
    learned_entailed: \<open>cdcl\<^sub>W_learned_clauses_entailed_by_init S\<close>
  shows "conflicting T = Some {#} \<and> unsatisfiable (set_mset (init_clss T))
    \<or> conflicting T = None \<and> trail T \<Turnstile>asm init_clss T \<and> satisfiable (set_mset (init_clss T))"
  using inc
proof induction
  case (add_confl C T) note tr = this(1) and dist = this(2) and conf = this(3) and C = this(4) and
  full = this(5)
  (* Here I thank Sledgehammer for its invaluable services *)
  have "full cdcl\<^sub>W_stgy T T"
    using full unfolding full_def by auto
  then show ?case
    using C conf dist full incremental_cdcl\<^sub>W.add_confl incremental_cdcl\<^sub>W_inv
      incremental_cdcl\<^sub>W_inv inv learned_entailed
      \<open>full cdcl\<^sub>W_stgy T T\<close> full_cdcl\<^sub>W_stgy_inv_normal_form
      s_inv tr by blast
next
  case (add_no_confl C T) note tr = this(1) and dist = this(2) and conf = this(3) and C = this(4)
    and full = this(5)
  (* Here I thank Sledgehammer for its invaluable services *)
  have "full cdcl\<^sub>W_stgy T T"
    using full unfolding full_def by auto
  then show ?case
    using \<open>full cdcl\<^sub>W_stgy T T\<close> full_cdcl\<^sub>W_stgy_inv_normal_form C conf dist full
      incremental_cdcl\<^sub>W.add_no_confl incremental_cdcl\<^sub>W_inv inv learned_entailed
      s_inv tr by blast
qed

lemma tranclp_incremental_correct:
  assumes
    inc: "incremental_cdcl\<^sub>W\<^sup>+\<^sup>+ S T" and
    inv: "cdcl\<^sub>W_all_struct_inv S" and
    s_inv: "cdcl\<^sub>W_stgy_invariant S" and
    learned_entailed: \<open>cdcl\<^sub>W_learned_clauses_entailed_by_init S\<close>
  shows "conflicting T = Some {#} \<and> unsatisfiable (set_mset (init_clss T))
    \<or> conflicting T = None \<and> trail T \<Turnstile>asm init_clss T \<and> satisfiable (set_mset (init_clss T))"
  using inc apply induction
   using assms incremental_conclusive_state apply blast
  by (meson incremental_conclusive_state inv rtranclp_incremental_cdcl\<^sub>W_inv s_inv
    tranclp_into_rtranclp learned_entailed)

end

end
