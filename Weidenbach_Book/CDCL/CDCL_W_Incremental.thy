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
    add_init_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st"

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
    init_state add_init_cls +
   state\<^sub>W
    state_eq
    state
    \<comment> \<open>functions about the state:\<close>
      \<comment> \<open>getter:\<close>
    trail init_clss learned_clss conflicting
      \<comment> \<open>setter:\<close>
    cons_trail tl_trail add_learned_cls remove_cls update_conflicting

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

    init_state :: "'v clauses \<Rightarrow> 'st" and
    add_init_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st"
begin

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
fun (in state\<^sub>W) cut_trail_wrt_clause where
"cut_trail_wrt_clause C [] S = S" |
"cut_trail_wrt_clause C (Decided L # M) S =
  (if -L \<in># C then S
    else cut_trail_wrt_clause C M (tl_trail S))" |
"cut_trail_wrt_clause C (Propagated L _ # M) S =
  (if -L \<in># C then S
    else cut_trail_wrt_clause C M (tl_trail S))"

definition (in state\<^sub>W) reduce_trail_wrt_clause :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" where
"reduce_trail_wrt_clause C S = update_conflicting (Some C) (cut_trail_wrt_clause C (trail S) S)"

definition add_new_clause_and_update :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" where
"add_new_clause_and_update C S = reduce_trail_wrt_clause C (add_init_cls C S)"

lemma (in state\<^sub>W) init_clss_cut_trail_wrt_clause[simp]:
  "init_clss (cut_trail_wrt_clause C M S) = init_clss S"
  by (induction rule: cut_trail_wrt_clause.induct) auto

lemma (in state\<^sub>W) learned_clss_cut_trail_wrt_clause[simp]:
  "learned_clss (cut_trail_wrt_clause C M S) = learned_clss S"
  by (induction rule: cut_trail_wrt_clause.induct) auto

lemma (in state\<^sub>W) conflicting_clss_cut_trail_wrt_clause[simp]:
  "conflicting (cut_trail_wrt_clause C M S) = conflicting S"
  by (induction rule: cut_trail_wrt_clause.induct) auto

lemma (in state\<^sub>W) clauses_cut_trail_wrt_clause[simp]:
  "clauses (cut_trail_wrt_clause C M S) = clauses S"
  by (auto simp: clauses_def)

lemma (in state\<^sub>W) trail_cut_trail_wrt_clause:
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

lemma (in state\<^sub>W) n_dup_no_dup_trail_cut_trail_wrt_clause[simp]:
  assumes n_d: "no_dup (trail T)"
  shows "no_dup (trail (cut_trail_wrt_clause C (trail T) T))"
proof -
  obtain M where
    M: "trail T = M @ trail (cut_trail_wrt_clause C (trail T) T)"
    using trail_cut_trail_wrt_clause[of T C] by auto
  show ?thesis
    using n_d unfolding arg_cong[OF M, of no_dup] by (auto simp: no_dup_def)
qed


lemma trail_cut_trail_wrt_clause_mono:
  \<open>trail S = trail T \<Longrightarrow> trail (cut_trail_wrt_clause C M S) =
  trail (cut_trail_wrt_clause C M T)\<close>
  by (induction M arbitrary: T S rule: ann_lit_list_induct) auto

lemma trail_cut_trail_wrt_clause_add_init_cls[simp]:
  \<open>trail (cut_trail_wrt_clause C M (add_init_cls C S)) =
  trail (cut_trail_wrt_clause C M S)\<close>
    by (subst trail_cut_trail_wrt_clause_mono)
      auto

lemma (in state\<^sub>W) cut_trail_wrt_clause_CNot_trail:
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

lemma (in state\<^sub>W) cut_trail_wrt_clause_hd_trail_in_or_empty_trail:
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

text \<open>The following function allows to mark a conflict while backtrack at the correct position.\<close>
inductive (in state\<^sub>W)cdcl\<^sub>W_OOO_conflict :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> for S :: 'st where
cdcl\<^sub>W_OOO_conflict_rule: \<open>cdcl\<^sub>W_OOO_conflict S T\<close>
if
  \<open>trail S \<Turnstile>as CNot C\<close> and
  \<open>C \<in># clauses S\<close> and
  \<open>conflicting S = None\<close>
  \<open>T \<sim> reduce_trail_wrt_clause C S\<close>

lemma (in conflict_driven_clause_learning\<^sub>W)
     cdcl\<^sub>W_all_struct_inv_add_new_clause_and_update_cdcl\<^sub>W_all_struct_inv:
  assumes
    inv_T: "cdcl\<^sub>W_all_struct_inv T" and
    tr_C[simp]: "trail T \<Turnstile>as CNot C" and
    [simp]: "distinct_mset C" and
    C: \<open>C \<in># clauses T\<close>
  shows "cdcl\<^sub>W_all_struct_inv (reduce_trail_wrt_clause C T)" (is "cdcl\<^sub>W_all_struct_inv ?T'")
proof -
  let ?T = "update_conflicting (Some C) ((cut_trail_wrt_clause C (trail T) T))"
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
    using inv_T C unfolding cdcl\<^sub>W_all_struct_inv_def no_strange_atm_def
    cdcl\<^sub>W_M_level_inv_def reduce_trail_wrt_clause_def
   by (auto dest!: multi_member_split[of C] simp: clauses_def, auto 20 1)

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
    by (auto simp: M_lev cdcl\<^sub>W_M_level_inv_def)

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
    using inv_T C unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_learned_clause_alt_def
    by (auto dest!: H_proped simp: clauses_def)
  show ?thesis
    using \<open>all_decomposition_implies_m (clauses ?T) (get_all_ann_decomposition (trail ?T))\<close> C
    unfolding cdcl\<^sub>W_all_struct_inv_def
    by (auto simp: reduce_trail_wrt_clause_def)
qed

lemma (in conflict_driven_clause_learning\<^sub>W) cdcl\<^sub>W_OOO_conflict_is_conflict:
  assumes \<open>cdcl\<^sub>W_OOO_conflict S U\<close>
  shows \<open>conflict (cut_trail_wrt_clause (the (conflicting U)) (trail S) S) U\<close>
  using assms by (auto simp: cdcl\<^sub>W_OOO_conflict.simps conflict.simps reduce_trail_wrt_clause_def
      conj_disj_distribR ex_disj_distrib intro: cut_trail_wrt_clause_CNot_trail
    dest!: multi_member_split)

lemma (in conflict_driven_clause_learning\<^sub>W) cdcl\<^sub>W_OOO_conflict_all_struct_invs:
  assumes \<open>cdcl\<^sub>W_OOO_conflict S T\<close> and \<open>cdcl\<^sub>W_all_struct_inv S\<close>
  shows \<open>cdcl\<^sub>W_all_struct_inv T\<close>
  using assms(1)
proof (cases rule: cdcl\<^sub>W_OOO_conflict.cases)
  case (cdcl\<^sub>W_OOO_conflict_rule C)
  then have \<open>distinct_mset C\<close>
    using assms(2) unfolding cdcl\<^sub>W_all_struct_inv_def distinct_cdcl\<^sub>W_state_def
    by (auto simp: clauses_def dest!: multi_member_split)
  then have \<open>cdcl\<^sub>W_all_struct_inv (reduce_trail_wrt_clause C S)\<close>
    using cdcl\<^sub>W_all_struct_inv_add_new_clause_and_update_cdcl\<^sub>W_all_struct_inv[of S C]
     cdcl\<^sub>W_all_struct_inv_cong[of T \<open>reduce_trail_wrt_clause C S\<close>] cdcl\<^sub>W_OOO_conflict_rule
    by (auto simp: assms)
  then show ?thesis
    using cdcl\<^sub>W_all_struct_inv_cong[of T \<open>reduce_trail_wrt_clause C S\<close>] cdcl\<^sub>W_OOO_conflict_rule
     cdcl\<^sub>W_OOO_conflict_is_conflict[OF assms(1)]
    by (auto simp: assms)
qed

lemma (in -) get_maximum_level_Cons_notin:
  \<open>- lit_of L \<notin># C \<Longrightarrow> lit_of L \<notin># C \<Longrightarrow> get_maximum_level M C = get_maximum_level (L # M) C\<close>
  unfolding get_maximum_level_def
  by (subgoal_tac \<open>get_level (L # M) `# C = get_level M `# C\<close>)
   (auto intro!: image_mset_cong simp: get_level_cons_if atm_of_eq_atm_of)

lemma (in state\<^sub>W) backtrack_lvl_cut_trail_wrt_clause_get_maximum_level:
   \<open>M = trail S \<Longrightarrow> M \<Turnstile>as CNot D \<Longrightarrow> no_dup (trail S) \<Longrightarrow>
    backtrack_lvl (cut_trail_wrt_clause D M S) = get_maximum_level M D\<close>
  apply (induction D M S rule: cut_trail_wrt_clause.induct)
  subgoal by auto
  subgoal for C L M S
    using count_decided_ge_get_maximum_level[of \<open>trail S\<close> \<open>C\<close>]
      true_annots_lit_of_notin_skip[of \<open>Decided L\<close> M C]
    by (cases \<open>trail S\<close>)
      (auto 5 3 dest!: multi_member_split intro: get_maximum_level_Cons_notin
      simp: get_maximum_level_add_mset max_def Decided_Propagated_in_iff_in_lits_of_l
      split: if_splits)
  subgoal for C L u M S
    using count_decided_ge_get_maximum_level[of \<open>trail S\<close> \<open>C\<close>]
      true_annots_lit_of_notin_skip[of \<open>Propagated L u\<close> M C]
    by (cases \<open>trail S\<close>)
      (auto 5 3 dest!: multi_member_split intro: get_maximum_level_Cons_notin
      simp: get_maximum_level_add_mset max_def Decided_Propagated_in_iff_in_lits_of_l
      split: if_splits)
  done

lemma (in state\<^sub>W) get_maximum_level_cut_trail_wrt_clause:
   \<open>M = trail S \<Longrightarrow> M \<Turnstile>as CNot C \<Longrightarrow> no_dup (trail S) \<Longrightarrow>
    get_maximum_level (trail (cut_trail_wrt_clause C M S)) C =
           get_maximum_level M C\<close>
  apply (induction C M S arbitrary: rule: cut_trail_wrt_clause.induct)
  subgoal by auto
  subgoal for C L M S
    using count_decided_ge_get_maximum_level[of \<open>trail S\<close> \<open>C\<close>]
      true_annots_lit_of_notin_skip[of \<open>Decided L\<close> M C]
    by (cases \<open>trail S\<close>)
     (auto 5 3 dest!: multi_member_split intro: get_maximum_level_Cons_notin
      simp: get_maximum_level_add_mset max_def Decided_Propagated_in_iff_in_lits_of_l
      split: if_splits)
  subgoal for C L u M S
    using count_decided_ge_get_maximum_level[of \<open>trail S\<close> \<open>C\<close>]
      true_annots_lit_of_notin_skip[of \<open>Propagated L u\<close> M C]
    by (cases \<open>trail S\<close>)
      (auto 5 3 dest!: multi_member_split intro: get_maximum_level_Cons_notin
      simp: get_maximum_level_add_mset max_def Decided_Propagated_in_iff_in_lits_of_l
      split: if_splits)
  done

lemma cdcl\<^sub>W_OOO_conflict_conflict_is_false_with_level:
  assumes \<open>cdcl\<^sub>W_OOO_conflict S T\<close> and \<open>cdcl\<^sub>W_all_struct_inv S\<close>
  shows \<open>conflict_is_false_with_level T\<close>
  using assms
proof (induction rule: cdcl\<^sub>W_OOO_conflict.induct)
  case (cdcl\<^sub>W_OOO_conflict_rule C T)
  have \<open>no_dup (trail S)\<close>
    using assms(2) unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def by fast
  with assms(2) cdcl\<^sub>W_OOO_conflict_rule show ?case
     by (auto simp: backtrack_lvl_cut_trail_wrt_clause_get_maximum_level
        get_maximum_level_cut_trail_wrt_clause reduce_trail_wrt_clause_def
      dest!: get_maximum_level_exists_lit_of_max_level[of _ \<open>trail T\<close>])
qed

text \<open>We can fully run @{term cdcl\<^sub>W_stgy} or add a clause.

Compared to a previous I changed the order and replaced \<^term>\<open>(update_conflicting (Some C)
       (add_init_cls C (cut_trail_wrt_clause C (trail S) S)))\<close> (like in my thesis) by
\<^term>\<open>(update_conflicting (Some C) (cut_trail_wrt_clause C (trail S) (add_init_cls C S)))\<close>.
The motivation behind it is that adding clause first makes it fallback on conflict (with
backtracking, but it is still a conflict) and, therefore, seems more regular than the opposite order.
\<close>
inductive incremental_cdcl\<^sub>W :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S where
add_confl:
  "trail S \<Turnstile>asm init_clss S \<Longrightarrow> distinct_mset C \<Longrightarrow> conflicting S = None \<Longrightarrow>
   trail S \<Turnstile>as CNot C \<Longrightarrow>
   full cdcl\<^sub>W_stgy
     (update_conflicting (Some C)
       (cut_trail_wrt_clause C (trail S) (add_init_cls C S))) T \<Longrightarrow>
   incremental_cdcl\<^sub>W S T" |
add_no_confl:
  "trail S \<Turnstile>asm init_clss S \<Longrightarrow> distinct_mset C \<Longrightarrow> conflicting S = None \<Longrightarrow>
   \<not>trail S \<Turnstile>as CNot C \<Longrightarrow>
   full cdcl\<^sub>W_stgy (add_init_cls C S) T \<Longrightarrow>
   incremental_cdcl\<^sub>W S T"


lemma cdcl\<^sub>W_all_struct_inv_add_init_cls:
  \<open>cdcl\<^sub>W_all_struct_inv (T) \<Longrightarrow> distinct_mset C \<Longrightarrow> cdcl\<^sub>W_all_struct_inv (add_init_cls C T)\<close>
  by (auto 5 4 simp: cdcl\<^sub>W_all_struct_inv_def no_strange_atm_def cdcl\<^sub>W_M_level_inv_def
    distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_conflicting_def cdcl\<^sub>W_learned_clause_def clauses_def
    reasons_in_clauses_def all_decomposition_implies_insert_single)

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
  let ?S = \<open>add_init_cls C T\<close>
  let ?T = \<open>(reduce_trail_wrt_clause C ?S)\<close>

  have "cdcl\<^sub>W_all_struct_inv ?S"
   using assms by (auto simp: cdcl\<^sub>W_all_struct_inv_add_init_cls)
  then have "cdcl\<^sub>W_all_struct_inv ?T"
    using cdcl\<^sub>W_all_struct_inv_add_new_clause_and_update_cdcl\<^sub>W_all_struct_inv[of ?S C] assms
    by auto
  then have
    no_dup_cut_T[simp]: "no_dup (trail (cut_trail_wrt_clause C (trail T) T))" and
    n_d[simp]: "no_dup (trail T)"
    using cdcl\<^sub>W_M_level_inv_decomp(2) cdcl\<^sub>W_all_struct_inv_def inv
    n_dup_no_dup_trail_cut_trail_wrt_clause by blast+
  then have "trail (add_new_clause_and_update C T) \<Turnstile>as CNot C"
    by (simp add: cut_trail_wrt_clause_CNot_trail
      cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_all_struct_inv_def add_new_clause_and_update_def
      reduce_trail_wrt_clause_def)
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
      cdcl\<^sub>W_all_struct_inv_def by (auto simp: add_new_clause_and_update_def
    reduce_trail_wrt_clause_def)
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

    have [simp]: "no_smaller_confl (update_conflicting (Some C)
      (cut_trail_wrt_clause C (trail T) (add_init_cls C T)))"
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
            using \<open>cdcl\<^sub>W_all_struct_inv ?T\<close> unfolding cdcl\<^sub>W_all_struct_inv_def
            cdcl\<^sub>W_M_level_inv_def by (auto simp: add_new_clause_and_update_def)
          ultimately show False
            unfolding 1(1)[simplified] by (auto simp: lits_of_def no_dup_def)
      qed
    qed
    show ?thesis using L C
      unfolding cdcl\<^sub>W_stgy_invariant_def cdcl\<^sub>W_all_struct_inv_def
      by (auto simp: add_new_clause_and_update_def get_level_def count_decided_def
        reduce_trail_wrt_clause_def intro: rev_bexI)
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
  let ?T = "(update_conflicting (Some C) (cut_trail_wrt_clause C (trail S) (add_init_cls C S)))"
  have \<open>cdcl\<^sub>W_all_struct_inv (add_init_cls C S)\<close>
    using cdcl\<^sub>W_all_struct_inv_add_init_cls add_confl.hyps(2) inv by auto
  then have inv': "cdcl\<^sub>W_all_struct_inv ?T" and inv_s_T: "cdcl\<^sub>W_stgy_invariant ?T"
    using add_confl.hyps(1,2,4)
    cdcl\<^sub>W_all_struct_inv_add_new_clause_and_update_cdcl\<^sub>W_all_struct_inv[of \<open>add_init_cls C S\<close> C] inv
     apply (auto simp:  add_new_clause_and_update_def reduce_trail_wrt_clause_def)
    using add_confl.hyps(1,2,4) add_new_clause_and_update_def
    cdcl\<^sub>W_all_struct_inv_add_new_clause_and_update_cdcl\<^sub>W_stgy_inv inv s_inv
    by (auto simp:  add_new_clause_and_update_def reduce_trail_wrt_clause_def)

  case 1 show ?case
    using add_confl rtranclp_cdcl\<^sub>W_all_struct_inv_inv[of ?T T]
     rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart[of ?T T] inv'
    unfolding full_def
    by auto

  case 2 show ?case
    using add_confl rtranclp_cdcl\<^sub>W_all_struct_inv_inv[of ?T T]
     rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart[of ?T T] inv'
     inv_s_T rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_stgy_invariant 
    unfolding full_def by blast

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

lemma incremental_conclusive_state: (* \htmllink{incremental_conclusive_state} *)
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
      full_cdcl\<^sub>W_stgy_inv_normal_form s_inv tr by blast
next
  case (add_no_confl C T) note tr = this(1) and dist = this(2) and conf = this(3) and C = this(4)
    and full = this(5)
  (* Here I thank Sledgehammer for its invaluable services *)
  have "full cdcl\<^sub>W_stgy T T"
    using full unfolding full_def by auto
  then show ?case
    using full_cdcl\<^sub>W_stgy_inv_normal_form C conf dist full
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
