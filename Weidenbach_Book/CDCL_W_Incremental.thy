theory CDCL_W_Incremental
imports CDCL_W_Termination
begin

section \<open>Incremental SAT solving\<close>
locale state\<^sub>W_adding_init_clause =
  state\<^sub>W
    -- \<open>functions for clauses: \<close>
    mset_cls
      mset_clss union_clss in_clss insert_clss remove_from_clss

    -- \<open>functions for the conflicting clause: \<close>
    mset_ccls union_ccls remove_clit

    -- \<open>Conversion between conflicting and non-conflicting\<close>
    ccls_of_cls cls_of_ccls

    -- \<open>functions about the state: \<close>
      -- \<open>getter:\<close>
    trail hd_raw_trail raw_init_clss raw_learned_clss backtrack_lvl raw_conflicting
      -- \<open>setter:\<close>
    cons_trail tl_trail add_learned_cls remove_cls update_backtrack_lvl
    update_conflicting

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

    trail :: "'st \<Rightarrow> ('v, nat, 'v clause) ann_lits" and
    hd_raw_trail :: "'st \<Rightarrow> ('v, nat, 'cls) ann_lit" and
    raw_init_clss :: "'st \<Rightarrow> 'clss" and
    raw_learned_clss :: "'st \<Rightarrow> 'clss" and
    backtrack_lvl :: "'st \<Rightarrow> nat" and
    raw_conflicting :: "'st \<Rightarrow> 'ccls option" and

    cons_trail :: "('v, nat, 'cls) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_learned_cls :: "'cls \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'cls \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_backtrack_lvl :: "nat \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conflicting :: "'ccls option \<Rightarrow> 'st \<Rightarrow> 'st" and

    init_state :: "'clss \<Rightarrow> 'st" and
    restart_state :: "'st \<Rightarrow> 'st" +
  fixes
    add_init_cls :: "'cls \<Rightarrow> 'st \<Rightarrow> 'st"
  assumes
    trail_add_init_cls[simp]:
      "\<And>st C. no_dup (trail st) \<Longrightarrow> trail (add_init_cls C st) = trail st" and
    init_clss_add_init_cls[simp]:
      "\<And>st C. no_dup (trail st) \<Longrightarrow> init_clss (add_init_cls C st) = {#mset_cls C#} + init_clss st"
      and
    learned_clss_add_init_cls[simp]:
      "\<And>st C. no_dup (trail st) \<Longrightarrow> learned_clss (add_init_cls C st) =
        learned_clss st" and
    backtrack_lvl_add_init_cls[simp]:
      "\<And>st C. no_dup (trail st) \<Longrightarrow> backtrack_lvl (add_init_cls C st) = backtrack_lvl st" and
    conflicting_add_init_cls[simp]:
      "\<And>st C. no_dup (trail st) \<Longrightarrow> conflicting (add_init_cls C st) = conflicting st"
begin
lemma clauses_add_init_cls[simp]:
   "no_dup (trail S) \<Longrightarrow>
     clauses (add_init_cls N S) = {#mset_cls N#} + init_clss S + learned_clss S"
   unfolding raw_clauses_def by auto

lemma reduce_trail_to_add_init_cls[simp]:
  "no_dup (trail S) \<Longrightarrow>
    trail (reduce_trail_to F (add_init_cls C S)) = trail (reduce_trail_to F S)"
  by (rule trail_eq_reduce_trail_to_eq) auto

lemma raw_conflicting_add_init_cls[simp]:
  "no_dup (trail S) \<Longrightarrow>
    raw_conflicting (add_init_cls C S) = None \<longleftrightarrow> raw_conflicting S = None"
  using map_option_is_None conflicting_add_init_cls[of S C] by fastforce+
end

locale conflict_driven_clause_learning_with_adding_init_clause\<^sub>W =
  state\<^sub>W_adding_init_clause
    -- \<open>functions for clauses: \<close>
    mset_cls
    mset_clss union_clss in_clss insert_clss remove_from_clss

    -- \<open>functions for the conflicting clause: \<close>
    mset_ccls union_ccls remove_clit

    -- \<open>conversion\<close>
    ccls_of_cls cls_of_ccls

    -- \<open>functions for the state: \<close>
      -- \<open>access functions:\<close>
    trail hd_raw_trail raw_init_clss raw_learned_clss backtrack_lvl raw_conflicting
      -- \<open>changing state:\<close>
    cons_trail tl_trail add_learned_cls remove_cls update_backtrack_lvl
    update_conflicting

      -- \<open>get state:\<close>
    init_state
    restart_state
      -- \<open>Adding a clause:\<close>
    add_init_cls
  for
    mset_cls :: "'cls \<Rightarrow> 'v clause" and

    mset_clss :: "'clss \<Rightarrow> 'v clauses" and
    union_clss :: "'clss \<Rightarrow> 'clss \<Rightarrow> 'clss" and
    in_clss :: "'cls \<Rightarrow> 'clss \<Rightarrow> bool" and
    insert_clss :: "'cls \<Rightarrow> 'clss \<Rightarrow> 'clss" and
    remove_from_clss :: "'cls \<Rightarrow> 'clss \<Rightarrow> 'clss"  and

    mset_ccls :: "'ccls \<Rightarrow> 'v clause" and
    union_ccls :: "'ccls \<Rightarrow> 'ccls \<Rightarrow> 'ccls" and
    remove_clit :: "'v literal \<Rightarrow> 'ccls \<Rightarrow> 'ccls" and

    ccls_of_cls :: "'cls \<Rightarrow> 'ccls" and
    cls_of_ccls :: "'ccls \<Rightarrow> 'cls" and

    trail :: "'st \<Rightarrow> ('v, nat, 'v clause) ann_lits" and
    hd_raw_trail :: "'st \<Rightarrow> ('v, nat, 'cls) ann_lit" and
    raw_init_clss :: "'st \<Rightarrow> 'clss" and
    raw_learned_clss :: "'st \<Rightarrow> 'clss" and
    backtrack_lvl :: "'st \<Rightarrow> nat" and
    raw_conflicting :: "'st \<Rightarrow> 'ccls option" and

    cons_trail :: "('v, nat, 'cls) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_learned_cls :: "'cls \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'cls \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_backtrack_lvl :: "nat \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conflicting :: "'ccls option \<Rightarrow> 'st \<Rightarrow> 'st" and

    init_state :: "'clss \<Rightarrow> 'st" and
    restart_state :: "'st \<Rightarrow> 'st" and
    add_init_cls :: "'cls \<Rightarrow> 'st \<Rightarrow> 'st"
begin

sublocale conflict_driven_clause_learning\<^sub>W 
  by unfold_locales

text \<open>This invariant holds all the invariant related to the strategy. See the structural invariant
    in @{term cdcl\<^sub>W_all_struct_inv}\<close>
definition cdcl\<^sub>W_stgy_invariant where
"cdcl\<^sub>W_stgy_invariant S \<longleftrightarrow>
  conflict_is_false_with_level S
  \<and> no_clause_is_false S
  \<and> no_smaller_confl S
  \<and> no_clause_is_false S"

lemma cdcl\<^sub>W_stgy_cdcl\<^sub>W_stgy_invariant:
  assumes
   cdcl\<^sub>W: "cdcl\<^sub>W_stgy S T" and
   inv_s: "cdcl\<^sub>W_stgy_invariant S" and
   inv: "cdcl\<^sub>W_all_struct_inv S"
  shows
    "cdcl\<^sub>W_stgy_invariant T"
  unfolding cdcl\<^sub>W_stgy_invariant_def cdcl\<^sub>W_all_struct_inv_def apply (intro conjI)
    apply (rule cdcl\<^sub>W_stgy_ex_lit_of_max_level[of S])
    using assms unfolding cdcl\<^sub>W_stgy_invariant_def cdcl\<^sub>W_all_struct_inv_def apply auto[7]
    using cdcl\<^sub>W cdcl\<^sub>W_stgy_not_non_negated_init_clss apply simp
  apply (rule cdcl\<^sub>W_stgy_no_smaller_confl_inv)
   using assms unfolding cdcl\<^sub>W_stgy_invariant_def cdcl\<^sub>W_all_struct_inv_def apply auto[4]
  using cdcl\<^sub>W cdcl\<^sub>W_stgy_not_non_negated_init_clss by auto

lemma rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_stgy_invariant:
  assumes
   cdcl\<^sub>W: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S T" and
   inv_s: "cdcl\<^sub>W_stgy_invariant S" and
   inv: "cdcl\<^sub>W_all_struct_inv S"
  shows
    "cdcl\<^sub>W_stgy_invariant T"
  using assms apply (induction)
    apply simp
  using cdcl\<^sub>W_stgy_cdcl\<^sub>W_stgy_invariant rtranclp_cdcl\<^sub>W_all_struct_inv_inv
  rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W by blast

abbreviation decr_bt_lvl where
"decr_bt_lvl S \<equiv> update_backtrack_lvl (backtrack_lvl S - 1) S"

text \<open>When we add a new clause, we reduce the trail until we get to tho first literal included in C.
  Then we can mark the conflict.\<close>
fun cut_trail_wrt_clause where
"cut_trail_wrt_clause C [] S = S" |
"cut_trail_wrt_clause C (Decided L _ # M) S =
  (if -L \<in># C then S
    else cut_trail_wrt_clause C M (decr_bt_lvl (tl_trail S)))" |
"cut_trail_wrt_clause C (Propagated L _ # M) S =
  (if -L \<in># C then S
    else cut_trail_wrt_clause C M (tl_trail S))"

definition add_new_clause_and_update :: "'ccls \<Rightarrow> 'st \<Rightarrow> 'st" where
"add_new_clause_and_update C S =
  (if trail S \<Turnstile>as CNot (mset_ccls C)
  then update_conflicting (Some C) (add_init_cls (cls_of_ccls C)
    (cut_trail_wrt_clause (mset_ccls C) (trail S) S))
  else add_init_cls (cls_of_ccls C) S)"

thm cut_trail_wrt_clause.induct
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
  case nil
  then show ?case by simp
next
  case (decided L l M) note IH = this(1)[of "decr_bt_lvl (tl_trail S)"] and M = this(2)[symmetric]
  then show ?case using Cons_eq_appendI by fastforce+
next
  case (proped L l M) note IH = this(1)[of "tl_trail S"] and M = this(2)[symmetric]
  then show ?case using Cons_eq_appendI by fastforce+
qed

lemma n_dup_no_dup_trail_cut_trail_wrt_clause[simp]:
  assumes n_d: "no_dup (trail T)"
  shows "no_dup (trail (cut_trail_wrt_clause C (trail T) T))"
proof -
  obtain M where
    M: " trail T = M @ trail (cut_trail_wrt_clause C (trail T) T)"
    using trail_cut_trail_wrt_clause[of T C] by auto
  show ?thesis
    using n_d unfolding arg_cong[OF M, of no_dup] by auto
qed

lemma cut_trail_wrt_clause_backtrack_lvl_length_decided:
  assumes
     "backtrack_lvl T = length (get_all_levels_of_ann (trail T))"
  shows
  "backtrack_lvl (cut_trail_wrt_clause C (trail T) T) =
     length (get_all_levels_of_ann (trail (cut_trail_wrt_clause C (trail T) T)))"
  using assms
proof (induction "trail T" arbitrary:T rule: ann_lit_list_induct)
  case nil
  then show ?case by simp
next
  case (decided L l M) note IH = this(1)[of "decr_bt_lvl (tl_trail T)"] and M = this(2)[symmetric]
    and bt = this(3)
  then show ?case by auto
next
  case (proped L l M) note IH = this(1)[of "tl_trail T"] and M = this(2)[symmetric] and bt = this(3)
  then show ?case by auto
qed

lemma cut_trail_wrt_clause_get_all_levels_of_ann:
  assumes "get_all_levels_of_ann (trail T) = rev [Suc 0..<
    Suc (length (get_all_levels_of_ann (trail T)))]"
  shows
    "get_all_levels_of_ann (trail ((cut_trail_wrt_clause C (trail T) T))) = rev [Suc 0..<
    Suc (length (get_all_levels_of_ann (trail  ((cut_trail_wrt_clause C (trail T) T)))))]"
  using assms
proof (induction "trail T" arbitrary:T rule: ann_lit_list_induct)
  case nil
  then show ?case by simp
next
  case (decided L l M) note IH = this(1)[of "decr_bt_lvl (tl_trail T)"] and M = this(2)[symmetric]
    and bt = this(3)
  then show ?case by (cases "count C L = 0") auto
next
  case (proped L l M) note IH = this(1)[of "tl_trail T"] and M = this(2)[symmetric] and bt = this(3)
  then show ?case by (cases "count C L = 0") auto
qed

lemma cut_trail_wrt_clause_CNot_trail:
  assumes "trail T \<Turnstile>as CNot C"
  shows
    "(trail ((cut_trail_wrt_clause C (trail T) T))) \<Turnstile>as CNot C"
  using assms
proof (induction "trail T" arbitrary:T rule: ann_lit_list_induct)
  case nil
  then show ?case by simp
next
  case (decided L l M) note IH = this(1)[of "decr_bt_lvl (tl_trail T)"] and M = this(2)[symmetric]
    and bt = this(3)
  show ?case
    proof (cases "count C (-L) = 0")
      case False
      then show ?thesis
        using IH M bt by (auto simp: true_annots_true_cls)
    next
      case True
      obtain mma :: "'v literal multiset" where
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
  case (proped L l M) note IH = this(1)[of "tl_trail T"] and M = this(2)[symmetric] and bt = this(3)
  show ?case
    proof (cases "count C (-L) = 0")
      case False
      then show ?thesis
        using IH M bt by (auto simp: true_annots_true_cls)
    next
      case True
      obtain mma :: "'v literal multiset" where
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
  using assms
proof (induction "trail T" arbitrary:T rule: ann_lit_list_induct)
  case nil
  then show ?case by simp
next
  case (decided L l M) note IH = this(1)[of "decr_bt_lvl (tl_trail T)"] and M = this(2)[symmetric]
  then show ?case by simp force
next
  case (proped L l M) note IH = this(1)[of "tl_trail T"] and M = this(2)[symmetric]
  then show ?case by simp force
qed

text \<open>We can fully run @{term cdcl\<^sub>W_s} or add a clause. Remark that we use @{term cdcl\<^sub>W_s} to avoid
an explicit @{term skip}, @{term resolve}, and @{term backtrack} normalisation to get rid of the
conflict @{term C} if possible.\<close>
inductive incremental_cdcl\<^sub>W :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S where
add_confl:
  "trail S \<Turnstile>asm init_clss S \<Longrightarrow> distinct_mset (mset_ccls C) \<Longrightarrow> conflicting S = None \<Longrightarrow>
   trail S \<Turnstile>as CNot (mset_ccls C) \<Longrightarrow>
   full cdcl\<^sub>W_stgy
     (update_conflicting (Some C)
       (add_init_cls (cls_of_ccls C) (cut_trail_wrt_clause (mset_ccls C) (trail S) S))) T \<Longrightarrow>
   incremental_cdcl\<^sub>W S T" |
add_no_confl:
  "trail S \<Turnstile>asm init_clss S \<Longrightarrow> distinct_mset (mset_ccls C) \<Longrightarrow> conflicting S = None \<Longrightarrow>
   \<not>trail S \<Turnstile>as CNot (mset_ccls C) \<Longrightarrow>
   full cdcl\<^sub>W_stgy (add_init_cls (cls_of_ccls C) S) T  \<Longrightarrow>
   incremental_cdcl\<^sub>W S T"

lemma cdcl\<^sub>W_all_struct_inv_add_new_clause_and_update_cdcl\<^sub>W_all_struct_inv:
  assumes
    inv_T: "cdcl\<^sub>W_all_struct_inv T" and
    tr_T_N[simp]: "trail T \<Turnstile>asm N" and
    tr_C[simp]: "trail T \<Turnstile>as CNot (mset_ccls C)" and
    [simp]: "distinct_mset (mset_ccls C)"
  shows "cdcl\<^sub>W_all_struct_inv (add_new_clause_and_update C T)" (is "cdcl\<^sub>W_all_struct_inv ?T'")
proof -
  let ?T = "update_conflicting (Some C)
    (add_init_cls (cls_of_ccls C) (cut_trail_wrt_clause (mset_ccls C) (trail T) T))"
  obtain M where
    M: "trail T = M @ trail (cut_trail_wrt_clause (mset_ccls C) (trail T) T)"
      using trail_cut_trail_wrt_clause[of T "mset_ccls C"] by blast
  have H[dest]: "\<And>x. x \<in> lits_of_l (trail (cut_trail_wrt_clause (mset_ccls C) (trail T) T)) \<Longrightarrow>
    x \<in> lits_of_l (trail T)"
    using inv_T arg_cong[OF M, of lits_of_l] by auto
  have H'[dest]: "\<And>x. x \<in> set (trail (cut_trail_wrt_clause (mset_ccls C) (trail T) T)) \<Longrightarrow> 
    x \<in> set (trail T)"
    using inv_T arg_cong[OF M, of set] by auto

  have H_proped:"\<And>x. x \<in> set (get_all_mark_of_propagated (trail (cut_trail_wrt_clause (mset_ccls C)
   (trail T) T))) \<Longrightarrow> x \<in> set (get_all_mark_of_propagated (trail T))"
  using inv_T arg_cong[OF M, of get_all_mark_of_propagated] by auto

  have [simp]: "no_strange_atm ?T"
    using inv_T unfolding cdcl\<^sub>W_all_struct_inv_def no_strange_atm_def add_new_clause_and_update_def
    cdcl\<^sub>W_M_level_inv_def by (auto 20 1)
  have M_lev: "cdcl\<^sub>W_M_level_inv T"
    using inv_T unfolding cdcl\<^sub>W_all_struct_inv_def by blast
  then have "no_dup (M @ trail (cut_trail_wrt_clause (mset_ccls C) (trail T) T))"
    unfolding cdcl\<^sub>W_M_level_inv_def unfolding M[symmetric] by auto
  then have [simp]: "no_dup (trail (cut_trail_wrt_clause (mset_ccls C) (trail T) T))"
    by auto

  have "consistent_interp (lits_of_l (M @ trail (cut_trail_wrt_clause (mset_ccls C) (trail T) T)))"
    using M_lev unfolding cdcl\<^sub>W_M_level_inv_def unfolding M[symmetric] by auto
  then have [simp]: "consistent_interp (lits_of_l (trail (cut_trail_wrt_clause (mset_ccls C) 
    (trail T) T)))"
    unfolding consistent_interp_def by auto

  have [simp]: "cdcl\<^sub>W_M_level_inv ?T"
    using M_lev cut_trail_wrt_clause_get_all_levels_of_ann[of T "mset_ccls C"]
    unfolding cdcl\<^sub>W_M_level_inv_def by (auto dest: H H'
      simp: M_lev cdcl\<^sub>W_M_level_inv_def cut_trail_wrt_clause_backtrack_lvl_length_decided)

  have [simp]: "\<And>s. s \<in># learned_clss T \<Longrightarrow> \<not>tautology s"
    using inv_T unfolding cdcl\<^sub>W_all_struct_inv_def by auto

  have "distinct_cdcl\<^sub>W_state T"
    using inv_T unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  then have [simp]: "distinct_cdcl\<^sub>W_state ?T"
    unfolding distinct_cdcl\<^sub>W_state_def by auto

  have  "cdcl\<^sub>W_conflicting T"
    using inv_T unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  have "trail ?T \<Turnstile>as CNot (mset_ccls C)"
     by (simp add: cut_trail_wrt_clause_CNot_trail)
  then have [simp]: "cdcl\<^sub>W_conflicting ?T"
    unfolding cdcl\<^sub>W_conflicting_def apply simp
    by (metis M \<open>cdcl\<^sub>W_conflicting T\<close> append_assoc cdcl\<^sub>W_conflicting_decomp(2))

  have
    decomp_T: "all_decomposition_implies_m (init_clss T) (get_all_ann_decomposition (trail T))"
    using inv_T unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  have  "all_decomposition_implies_m  (init_clss ?T)
    (get_all_ann_decomposition (trail ?T))"
    unfolding all_decomposition_implies_def
    proof clarify
      fix a b
      assume "(a, b) \<in> set (get_all_ann_decomposition (trail ?T))"
      from in_get_all_ann_decomposition_in_get_all_ann_decomposition_prepend[OF this, of M]
      obtain b' where
        "(a, b' @ b) \<in> set (get_all_ann_decomposition (trail T))"
        using M by auto
      then have "unmark_l a \<union> set_mset (init_clss T) \<Turnstile>ps unmark_l (b' @ b)"
        using decomp_T unfolding all_decomposition_implies_def by fastforce
      then have "unmark_l a \<union> set_mset (init_clss ?T) \<Turnstile>ps unmark_l (b @ b')"
        by (simp add: Un_commute)
      then show "unmark_l a \<union> set_mset (init_clss ?T) \<Turnstile>ps unmark_l b"
        by (auto simp: image_Un)
    qed

  have [simp]: "cdcl\<^sub>W_learned_clause ?T"
    using inv_T unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_learned_clause_def
    by (auto dest!: H_proped simp: raw_clauses_def)
  show ?thesis
    using \<open>all_decomposition_implies_m  (init_clss ?T)
    (get_all_ann_decomposition (trail ?T))\<close>
    unfolding cdcl\<^sub>W_all_struct_inv_def by (auto simp: add_new_clause_and_update_def)
qed

lemma cdcl\<^sub>W_all_struct_inv_add_new_clause_and_update_cdcl\<^sub>W_stgy_inv:
  assumes
    inv_s: "cdcl\<^sub>W_stgy_invariant T" and
    inv: "cdcl\<^sub>W_all_struct_inv T" and
    tr_T_N[simp]: "trail T \<Turnstile>asm N" and
    tr_C[simp]: "trail T \<Turnstile>as CNot (mset_ccls C)" and
    [simp]: "distinct_mset (mset_ccls C)"
  shows "cdcl\<^sub>W_stgy_invariant (add_new_clause_and_update C T)"
    (is "cdcl\<^sub>W_stgy_invariant ?T'")
proof -
  have "cdcl\<^sub>W_all_struct_inv ?T'"
    using cdcl\<^sub>W_all_struct_inv_add_new_clause_and_update_cdcl\<^sub>W_all_struct_inv assms by blast
  then have
    no_dup_cut_T[simp]: "no_dup (trail (cut_trail_wrt_clause (mset_ccls C) (trail T) T))" and
    n_d[simp]: "no_dup (trail T)"
    using cdcl\<^sub>W_M_level_inv_decomp(2) cdcl\<^sub>W_all_struct_inv_def inv
    n_dup_no_dup_trail_cut_trail_wrt_clause by blast+
  then have "trail (add_new_clause_and_update C T) \<Turnstile>as CNot (mset_ccls C)"
    by (simp add: add_new_clause_and_update_def cut_trail_wrt_clause_CNot_trail
      cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_all_struct_inv_def)
  obtain MT where
    MT: "trail T = MT @  trail (cut_trail_wrt_clause (mset_ccls C) (trail T) T)"
    using trail_cut_trail_wrt_clause by blast
  consider
      (false) "\<forall>L\<in>#mset_ccls C. - L \<notin> lits_of_l (trail T)" and
        "trail (cut_trail_wrt_clause (mset_ccls C) (trail T) T) = []"
    | (not_false)
      "- lit_of (hd (trail (cut_trail_wrt_clause (mset_ccls C) (trail T) T))) \<in># (mset_ccls C)" and
      "1 \<le> length (trail (cut_trail_wrt_clause (mset_ccls C) (trail T) T))"
    using cut_trail_wrt_clause_hd_trail_in_or_empty_trail[of "mset_ccls C" T] by auto
  then show ?thesis
    proof cases
      case false note C = this(1) and empty_tr = this(2)
      then have [simp]: "mset_ccls C = {#}"
        by (simp add: in_CNot_implies_uminus(2) multiset_eqI)
      show ?thesis
        using empty_tr unfolding cdcl\<^sub>W_stgy_invariant_def no_smaller_confl_def
        cdcl\<^sub>W_all_struct_inv_def by (auto simp: add_new_clause_and_update_def)
    next
      case not_false note C = this(1) and l = this(2)
      let ?L = "- lit_of (hd (trail (cut_trail_wrt_clause (mset_ccls C) (trail T) T)))"
      have "get_all_levels_of_ann (trail (add_new_clause_and_update C T)) =
        rev [1..<1 + length (get_all_levels_of_ann (trail (add_new_clause_and_update C T)))]"
        using \<open>cdcl\<^sub>W_all_struct_inv ?T'\<close> unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def
        by blast
      moreover
        have "backtrack_lvl (cut_trail_wrt_clause (mset_ccls C) (trail T) T) =
          length (get_all_levels_of_ann (trail (add_new_clause_and_update C T)))"
          using \<open>cdcl\<^sub>W_all_struct_inv ?T'\<close> unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def
          by (auto simp:add_new_clause_and_update_def)
      moreover
        have "no_dup (trail (cut_trail_wrt_clause (mset_ccls C) (trail T) T))"
          using \<open>cdcl\<^sub>W_all_struct_inv ?T'\<close> unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def
          by (auto simp:add_new_clause_and_update_def)
        then have "atm_of ?L \<notin> atm_of ` lits_of_l
          (tl (trail (cut_trail_wrt_clause (mset_ccls C) (trail T) T)))"
          by (cases "trail (cut_trail_wrt_clause (mset_ccls C) (trail T) T)") 
          (auto simp: lits_of_def)

      ultimately have L: "get_level (trail (cut_trail_wrt_clause (mset_ccls C) (trail T) T)) (-?L)
        = length (get_all_levels_of_ann (trail (cut_trail_wrt_clause (mset_ccls C) (trail T) T)))"
        using get_level_get_rev_level_get_all_levels_of_ann[OF
          \<open>atm_of ?L \<notin> atm_of ` lits_of_l (tl (trail (cut_trail_wrt_clause (mset_ccls C) 
            (trail T) T)))\<close>,
          of "[hd (trail (cut_trail_wrt_clause (mset_ccls C) (trail T) T))]"]
          (* the expression \<open>trail (add_init_cls C (cut_trail_wrt_clause C (trail T) T)))\<close> can be
          simplified, but auto is not able to solve the goal once done.*)
          apply (cases "trail (add_init_cls (cls_of_ccls C)
              (cut_trail_wrt_clause (mset_ccls C) (trail T) T))";
           cases "hd (trail (cut_trail_wrt_clause (mset_ccls C) (trail T) T))")
          using l by (auto split: if_split_asm
            simp:rev_swap[symmetric] add_new_clause_and_update_def)

      have L': "length (get_all_levels_of_ann (trail (cut_trail_wrt_clause (mset_ccls C) 
        (trail T) T)))
        = backtrack_lvl (cut_trail_wrt_clause (mset_ccls C) (trail T) T)"
        using \<open>cdcl\<^sub>W_all_struct_inv ?T'\<close> unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def
        by (auto simp:add_new_clause_and_update_def)

      have [simp]: "no_smaller_confl (update_conflicting (Some C)
        (add_init_cls (cls_of_ccls C) (cut_trail_wrt_clause (mset_ccls C) (trail T) T)))"
        unfolding no_smaller_confl_def
      proof (clarify, goal_cases)
        case (1 M K i M' D)
        then consider
            (DC) "D = mset_ccls C"
          | (D_T) "D \<in># clauses T"
          by (auto simp: raw_clauses_def split: if_split_asm)
        then show False
          proof cases
            case D_T
            have "no_smaller_confl T"
              using inv_s unfolding cdcl\<^sub>W_stgy_invariant_def by auto
            have "(MT @ M') @ Decided K i # M = trail T "
              using MT 1(1) by auto
            thus False using D_T \<open>no_smaller_confl T\<close> 1(3) unfolding no_smaller_confl_def by blast
          next
            case DC note _[simp] = this
            then have "atm_of (-?L) \<in> atm_of ` (lits_of_l M)"
              using 1(3) C in_CNot_implies_uminus(2) by blast
            moreover
              have "lit_of (hd (M' @ Decided K i # [])) = -?L"
                using l 1(1)[symmetric] inv
                by (cases "trail (add_init_cls (cls_of_ccls C)
                    (cut_trail_wrt_clause (mset_ccls C) (trail T) T))")
                (auto dest!: arg_cong[of "_ # _" _ hd] simp: hd_append cdcl\<^sub>W_all_struct_inv_def
                  cdcl\<^sub>W_M_level_inv_def)
              from arg_cong[OF this, of atm_of]
              have "atm_of (-?L) \<in> atm_of ` (lits_of_l (M' @ Decided K i # []))"
                by (cases " (M' @ Decided K i # [])") auto
            moreover have "no_dup (trail (cut_trail_wrt_clause (mset_ccls C) (trail T) T))"
              using \<open>cdcl\<^sub>W_all_struct_inv ?T'\<close> unfolding cdcl\<^sub>W_all_struct_inv_def
              cdcl\<^sub>W_M_level_inv_def by (auto simp: add_new_clause_and_update_def)
            ultimately show False
              unfolding 1(1)[symmetric, simplified] by (auto simp: lits_of_def)
        qed
      qed
      show ?thesis using L L' C
        unfolding cdcl\<^sub>W_stgy_invariant_def
        unfolding cdcl\<^sub>W_all_struct_inv_def by (auto simp: add_new_clause_and_update_def)
    qed
qed

lemma full_cdcl\<^sub>W_stgy_inv_normal_form:
  assumes
    full: "full cdcl\<^sub>W_stgy S T" and
    inv_s: "cdcl\<^sub>W_stgy_invariant S" and
    inv: "cdcl\<^sub>W_all_struct_inv S"
  shows "conflicting T = Some {#} \<and> unsatisfiable (set_mset (init_clss S))
    \<or> conflicting T = None \<and> trail T \<Turnstile>asm init_clss S \<and> satisfiable (set_mset (init_clss S))"
proof -
  have "no_step cdcl\<^sub>W_stgy T"
    using full unfolding full_def by blast
  moreover have "cdcl\<^sub>W_all_struct_inv T" and inv_s: "cdcl\<^sub>W_stgy_invariant T"
    apply (metis rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W full full_def inv
      rtranclp_cdcl\<^sub>W_all_struct_inv_inv)
    by (metis full full_def inv inv_s rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_stgy_invariant)
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

lemma incremental_cdcl\<^sub>W_inv:
  assumes
    inc: "incremental_cdcl\<^sub>W S T" and
    inv: "cdcl\<^sub>W_all_struct_inv S" and
    s_inv: "cdcl\<^sub>W_stgy_invariant S"
  shows
    "cdcl\<^sub>W_all_struct_inv T" and
    "cdcl\<^sub>W_stgy_invariant T"
  using inc
proof (induction)
  case (add_confl C T)
  let ?T = "(update_conflicting (Some C) (add_init_cls (cls_of_ccls C)
    (cut_trail_wrt_clause (mset_ccls C) (trail S) S)))"
  have "cdcl\<^sub>W_all_struct_inv ?T" and inv_s_T: "cdcl\<^sub>W_stgy_invariant ?T"
    using add_confl.hyps(1,2,4) add_new_clause_and_update_def
    cdcl\<^sub>W_all_struct_inv_add_new_clause_and_update_cdcl\<^sub>W_all_struct_inv inv apply auto[1]
    using add_confl.hyps(1,2,4) add_new_clause_and_update_def
    cdcl\<^sub>W_all_struct_inv_add_new_clause_and_update_cdcl\<^sub>W_stgy_inv inv s_inv by auto
  case 1 show ?case
     by (metis add_confl.hyps(1,2,4,5) add_new_clause_and_update_def
       cdcl\<^sub>W_all_struct_inv_add_new_clause_and_update_cdcl\<^sub>W_all_struct_inv
       rtranclp_cdcl\<^sub>W_all_struct_inv_inv rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W full_def inv)

  case 2  show ?case
    by (metis inv_s_T add_confl.hyps(1,2,4,5) add_new_clause_and_update_def
      cdcl\<^sub>W_all_struct_inv_add_new_clause_and_update_cdcl\<^sub>W_all_struct_inv full_def inv
      rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_stgy_invariant)
next
  case (add_no_confl C T)
  case 1
  have "cdcl\<^sub>W_all_struct_inv (add_init_cls (cls_of_ccls C) S)"
    using inv \<open>distinct_mset (mset_ccls C)\<close> unfolding cdcl\<^sub>W_all_struct_inv_def no_strange_atm_def
    cdcl\<^sub>W_M_level_inv_def distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_conflicting_def cdcl\<^sub>W_learned_clause_def
    by (auto 9 1 simp: all_decomposition_implies_insert_single raw_clauses_def)
    (* SLOW ~2s *)
  then show ?case
    using add_no_confl(5) unfolding full_def by (auto intro: rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv)
  case 2
  have nc: "\<forall>M. (\<exists>K i M'. trail S = M' @ Decided K i # M) \<longrightarrow> \<not> M \<Turnstile>as CNot (mset_ccls C)"
    using  \<open>\<not> trail S \<Turnstile>as CNot (mset_ccls C)\<close>
    by (auto simp: true_annots_true_cls_def_iff_negation_in_model)

  have "cdcl\<^sub>W_stgy_invariant (add_init_cls (cls_of_ccls C) S)"
    using s_inv \<open>\<not> trail S \<Turnstile>as CNot (mset_ccls C)\<close> inv unfolding cdcl\<^sub>W_stgy_invariant_def
    no_smaller_confl_def eq_commute[of "_" "trail _"] cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_all_struct_inv_def
    by (auto simp: raw_clauses_def nc)
  then show ?case
    by (metis \<open>cdcl\<^sub>W_all_struct_inv (add_init_cls (cls_of_ccls C) S)\<close> add_no_confl.hyps(5) full_def
      rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_stgy_invariant)
qed

lemma rtranclp_incremental_cdcl\<^sub>W_inv:
  assumes
    inc: "incremental_cdcl\<^sub>W\<^sup>*\<^sup>* S T" and
    inv: "cdcl\<^sub>W_all_struct_inv S" and
    s_inv: "cdcl\<^sub>W_stgy_invariant S"
  shows
    "cdcl\<^sub>W_all_struct_inv T" and
    "cdcl\<^sub>W_stgy_invariant T"
     using inc apply induction
    using inv apply simp
   using s_inv apply simp
  using incremental_cdcl\<^sub>W_inv by blast+

lemma incremental_conclusive_state:
  assumes
    inc: "incremental_cdcl\<^sub>W S T" and
    inv: "cdcl\<^sub>W_all_struct_inv S" and
    s_inv: "cdcl\<^sub>W_stgy_invariant S"
  shows "conflicting T = Some {#} \<and> unsatisfiable (set_mset (init_clss T))
    \<or> conflicting T = None \<and> trail T \<Turnstile>asm init_clss T \<and> satisfiable (set_mset (init_clss T))"
  using inc
proof induction
  print_cases
  case (add_confl C T) note tr = this(1) and dist = this(2) and conf = this(3) and C = this(4) and
  full = this(5)
  (* Here I thank Sledgehammer for its invaluable services *)
  have "full cdcl\<^sub>W_stgy T T"
    using full unfolding full_def by auto
  then show ?case
    using full C conf dist tr
    by (metis full_cdcl\<^sub>W_stgy_inv_normal_form incremental_cdcl\<^sub>W.simps incremental_cdcl\<^sub>W_inv(1)
      incremental_cdcl\<^sub>W_inv(2) inv s_inv)
next
  case (add_no_confl C T) note tr = this(1) and dist = this(2) and conf = this(3) and C = this(4)
    and   full = this(5)
  (* Here I thank Sledgehammer for its invaluable services *)
  have "full cdcl\<^sub>W_stgy T T"
    using full unfolding full_def by auto
  then show ?case
     by (meson C conf dist full full_cdcl\<^sub>W_stgy_inv_normal_form incremental_cdcl\<^sub>W.add_no_confl
       incremental_cdcl\<^sub>W_inv(1) incremental_cdcl\<^sub>W_inv(2) inv s_inv tr)
qed

lemma tranclp_incremental_correct:
  assumes
    inc: "incremental_cdcl\<^sub>W\<^sup>+\<^sup>+ S T" and
    inv: "cdcl\<^sub>W_all_struct_inv S" and
    s_inv: "cdcl\<^sub>W_stgy_invariant S"
  shows "conflicting T = Some {#} \<and> unsatisfiable (set_mset (init_clss T))
    \<or> conflicting T = None \<and> trail T \<Turnstile>asm init_clss T \<and> satisfiable (set_mset (init_clss T))"
  using inc apply induction
   using assms incremental_conclusive_state apply blast
  by (meson incremental_conclusive_state inv rtranclp_incremental_cdcl\<^sub>W_inv s_inv
    tranclp_into_rtranclp)

end

end
