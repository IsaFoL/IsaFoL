theory CDCL_W_Incremental
imports CDCL_W_Termination
begin

section \<open>Incremental SAT solving\<close>
context cdcl\<^sub>W_ops
begin

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
  unfolding cdcl\<^sub>W_stgy_invariant_def cdcl\<^sub>W_all_struct_inv_def apply standard
    apply (rule cdcl\<^sub>W_stgy_ex_lit_of_max_level[of S])
    using assms unfolding cdcl\<^sub>W_stgy_invariant_def cdcl\<^sub>W_all_struct_inv_def apply auto[7]
  apply standard
    using cdcl\<^sub>W cdcl\<^sub>W_stgy_not_non_negated_init_clss apply blast
  apply standard
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
"cut_trail_wrt_clause C (Marked L _ # M) S =
  (if -L \<in># C then S
    else cut_trail_wrt_clause C M (decr_bt_lvl (tl_trail S)))" |
"cut_trail_wrt_clause C (Propagated L _ # M) S =
  (if -L \<in># C then S
    else cut_trail_wrt_clause C M (tl_trail S))"

definition add_new_clause_and_update :: "'v literal multiset \<Rightarrow> 'st \<Rightarrow> 'st" where
"add_new_clause_and_update C S =
  (if trail S \<Turnstile>as CNot C
  then update_conflicting (C_Clause C) (add_init_cls C (cut_trail_wrt_clause C (trail S) S))
  else add_init_cls C S)"

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
proof (induction "trail S" arbitrary:S rule: marked_lit_list_induct)
  case nil
  then show ?case by simp
next
  case (marked L l M) note IH = this(1)[of "decr_bt_lvl (tl_trail S)"] and M = this(2)[symmetric]
  then show ?case using Cons_eq_appendI by fastforce+
next
  case (proped L l M) note IH = this(1)[of " (tl_trail S)"] and M = this(2)[symmetric]
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

lemma cut_trail_wrt_clause_backtrack_lvl_length_marked:
  assumes
     "backtrack_lvl T = length (get_all_levels_of_marked (trail T))"
  shows
  "backtrack_lvl (cut_trail_wrt_clause C (trail T) T) =
     length (get_all_levels_of_marked (trail (cut_trail_wrt_clause C (trail T) T)))"
  using assms
proof (induction "trail T" arbitrary:T rule: marked_lit_list_induct)
  case nil
  then show ?case by simp
next
  case (marked L l M) note IH = this(1)[of "decr_bt_lvl (tl_trail T)"] and M = this(2)[symmetric]
    and bt = this(3)
  then show ?case by auto
next
  case (proped L l M) note IH = this(1)[of "tl_trail T"] and M = this(2)[symmetric] and bt = this(3)
  then show ?case by auto
qed

lemma cut_trail_wrt_clause_get_all_levels_of_marked:
  assumes "get_all_levels_of_marked (trail T) = rev [Suc 0..<
    Suc (length (get_all_levels_of_marked (trail T)))]"
  shows
    "get_all_levels_of_marked (trail ((cut_trail_wrt_clause C (trail T) T))) = rev [Suc 0..<
    Suc (length (get_all_levels_of_marked (trail  ((cut_trail_wrt_clause C (trail T) T)))))]"
  using assms
proof (induction "trail T" arbitrary:T rule: marked_lit_list_induct)
  case nil
  then show ?case by simp
next
  case (marked L l M) note IH = this(1)[of "decr_bt_lvl (tl_trail T)"] and M = this(2)[symmetric]
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
proof (induction "trail T" arbitrary:T rule: marked_lit_list_induct)
  case nil
  then show ?case by simp
next
  case (marked L l M) note IH = this(1)[of "decr_bt_lvl (tl_trail T)"] and M = this(2)[symmetric]
    and bt = this(3)
    (* TODO less ugly proof *)
  then show ?case apply (cases "count C (-L) = 0")
    apply (auto simp: true_annots_true_cls)
    by (smt CNot_def One_nat_def count_single diff_Suc_1 in_CNot_uminus less_numeral_extra(4)
     marked.prems marked_lit.sel(1) mem_Collect_eq true_annot_def true_annot_lit_of_notin_skip
     true_annots_def true_clss_def zero_less_diff)
next
  case (proped L l M) note IH = this(1)[of "tl_trail T"] and M = this(2)[symmetric] and bt = this(3)
  then show ?case
    (* TODO ugly proof *)
    apply (cases "count C (-L) = 0")
    apply (auto simp: true_annots_true_cls)
    by (smt CNot_def One_nat_def count_single diff_Suc_1 in_CNot_uminus less_numeral_extra(4)
     proped.prems marked_lit.sel(2) mem_Collect_eq true_annot_def true_annot_lit_of_notin_skip
     true_annots_def true_clss_def zero_less_diff)
qed

lemma cut_trail_wrt_clause_hd_trail_in_or_empty_trail:
  "((\<forall>L \<in>#C. -L \<notin> lits_of (trail T)) \<and> trail (cut_trail_wrt_clause C (trail T) T) = [])
    \<or> (-lit_of (hd (trail (cut_trail_wrt_clause C (trail T) T))) \<in># C
       \<and> length (trail (cut_trail_wrt_clause C (trail T) T)) \<ge> 1)"
  using assms
proof (induction "trail T" arbitrary:T rule: marked_lit_list_induct)
  case nil
  then show ?case by simp
next
  case (marked L l M) note IH = this(1)[of "decr_bt_lvl (tl_trail T)"] and M = this(2)[symmetric]
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
  "trail S \<Turnstile>asm init_clss S \<Longrightarrow> distinct_mset C \<Longrightarrow> conflicting S = C_True \<Longrightarrow>
   trail S \<Turnstile>as CNot C \<Longrightarrow>
   full cdcl\<^sub>W_stgy
     (update_conflicting (C_Clause C) (add_init_cls C (cut_trail_wrt_clause C (trail S) S))) T \<Longrightarrow>
   incremental_cdcl\<^sub>W S T" |
add_no_confl:
  "trail S \<Turnstile>asm init_clss S \<Longrightarrow> distinct_mset C \<Longrightarrow> conflicting S = C_True \<Longrightarrow>
   \<not>trail S \<Turnstile>as CNot C \<Longrightarrow>
   full cdcl\<^sub>W_stgy (add_init_cls C S) T  \<Longrightarrow>
   incremental_cdcl\<^sub>W S T"

inductive add_learned_clss :: "'st \<Rightarrow> 'v clauses \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
add_learned_clss_nil: "add_learned_clss S {#} S" |
add_learned_clss_plus:
  "add_learned_clss S A T \<Longrightarrow> add_learned_clss S ({#x#} + A) (add_learned_cls x T)"
declare add_learned_clss.intros[intro]

lemma Ex_add_learned_clss:
  "\<exists>T. add_learned_clss S A T"
  by (induction A arbitrary: S rule: multiset_induct) (auto simp: union_commute[of _ "{#_#}"])

lemma add_learned_clss_trail:
  assumes "add_learned_clss S U T" and "no_dup (trail S)"
  shows "trail T = trail S"
  using assms by (induction rule: add_learned_clss.induct) (simp_all add: ac_simps)

lemma add_learned_clss_learned_clss:
  assumes "add_learned_clss S U T" and "no_dup (trail S)"
  shows "learned_clss T = U + learned_clss S"
  using assms by (induction rule: add_learned_clss.induct)
  (auto simp: ac_simps dest: add_learned_clss_trail)

lemma add_learned_clss_init_clss:
  assumes "add_learned_clss S U T" and "no_dup (trail S)"
  shows "init_clss T = init_clss S"
  using assms by (induction rule: add_learned_clss.induct)
  (auto simp: ac_simps dest: add_learned_clss_trail)

lemma add_learned_clss_conflicting:
  assumes "add_learned_clss S U T" and "no_dup (trail S)"
  shows "conflicting T = conflicting S"
  using assms by (induction rule: add_learned_clss.induct)
  (auto simp: ac_simps dest: add_learned_clss_trail)

lemma add_learned_clss_backtrack_lvl:
  assumes "add_learned_clss S U T" and "no_dup (trail S)"
  shows "backtrack_lvl T = backtrack_lvl S"
  using assms by (induction rule: add_learned_clss.induct)
  (auto simp: ac_simps dest: add_learned_clss_trail)

lemma add_learned_clss_init_state_mempty[dest!]:
  "add_learned_clss (init_state N) {#} T \<Longrightarrow> T = init_state N"
  by (cases rule: add_learned_clss.cases) (auto simp: add_learned_clss.cases)

text \<open>For multiset larger that 1 element, there is no way to know in which order the clauses are
  added. But contrary to a definition @{term fold_mset}, there is an element.\<close>
lemma add_learned_clss_init_state_single[dest!]:
  "add_learned_clss (init_state N) {#C#} T \<Longrightarrow> T = add_learned_cls C (init_state N)"
  by (induction  "{#C#}" "T" rule: add_learned_clss.induct)
  (auto simp: add_learned_clss.cases ac_simps union_is_single split: split_if_asm)

thm rtranclp_cdcl\<^sub>W_stgy_no_smaller_confl_inv cdcl\<^sub>W_stgy_final_state_conclusive
lemma cdcl\<^sub>W_all_struct_inv_add_new_clause_and_update_cdcl\<^sub>W_all_struct_inv:
  assumes
    inv_T: "cdcl\<^sub>W_all_struct_inv T" and
    tr_T_N[simp]: "trail T \<Turnstile>asm N" and
    tr_C[simp]: "trail T \<Turnstile>as CNot C" and
    [simp]: "distinct_mset C"
  shows "cdcl\<^sub>W_all_struct_inv (add_new_clause_and_update C T)" (is "cdcl\<^sub>W_all_struct_inv ?T'")
proof -
  let ?T = "update_conflicting (C_Clause C) (add_init_cls C (cut_trail_wrt_clause C (trail T) T))"
  obtain M where
    M: "trail T = M @ trail (cut_trail_wrt_clause C (trail T) T)"
      using trail_cut_trail_wrt_clause[of T C] by blast
  have H[dest]: "\<And>x. x \<in> lits_of (trail (cut_trail_wrt_clause C (trail T) T)) \<Longrightarrow>
    x \<in> lits_of (trail T)"
    using inv_T arg_cong[OF M, of lits_of] by auto
  have H'[dest]: "\<And>x. x \<in> set (trail (cut_trail_wrt_clause C (trail T) T)) \<Longrightarrow> x \<in> set (trail T)"
    using inv_T arg_cong[OF M, of set] by auto

  have H_proped:"\<And>x. x \<in> set (get_all_mark_of_propagated (trail (cut_trail_wrt_clause C (trail T)
    T))) \<Longrightarrow> x \<in> set (get_all_mark_of_propagated (trail T))"
  using inv_T arg_cong[OF M, of get_all_mark_of_propagated] by auto

  have [simp]: "no_strange_atm ?T"
    using inv_T unfolding cdcl\<^sub>W_all_struct_inv_def no_strange_atm_def add_new_clause_and_update_def
    cdcl\<^sub>W_M_level_inv_def
    by (auto dest!: H H')

  have M_lev: "cdcl\<^sub>W_M_level_inv T"
    using inv_T unfolding cdcl\<^sub>W_all_struct_inv_def by blast
  then have "no_dup (M @ trail (cut_trail_wrt_clause C (trail T) T))"
    unfolding cdcl\<^sub>W_M_level_inv_def unfolding M[symmetric] by auto
  then have [simp]: "no_dup (trail (cut_trail_wrt_clause C (trail T) T))"
    by auto

  have "consistent_interp (lits_of (M @ trail (cut_trail_wrt_clause C (trail T) T)))"
    using M_lev unfolding cdcl\<^sub>W_M_level_inv_def unfolding M[symmetric] by auto
  then have [simp]: "consistent_interp (lits_of (trail (cut_trail_wrt_clause C (trail T) T)))"
    unfolding consistent_interp_def by auto

  have [simp]: "cdcl\<^sub>W_M_level_inv ?T"
    unfolding cdcl\<^sub>W_M_level_inv_def apply (auto dest: H H'
      simp: M_lev cdcl\<^sub>W_M_level_inv_def cut_trail_wrt_clause_backtrack_lvl_length_marked)
    using M_lev cut_trail_wrt_clause_get_all_levels_of_marked[of T C]
    by (auto simp: cdcl\<^sub>W_M_level_inv_def cut_trail_wrt_clause_backtrack_lvl_length_marked)

  have [simp]: "\<And>s. s \<in># learned_clss T \<Longrightarrow> \<not>tautology s"
    using inv_T unfolding cdcl\<^sub>W_all_struct_inv_def by auto

  have "distinct_cdcl\<^sub>W_state T"
    using inv_T unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  then have [simp]: "distinct_cdcl\<^sub>W_state ?T"
    unfolding distinct_cdcl\<^sub>W_state_def by auto

  have  "cdcl\<^sub>W_conflicting T"
    using inv_T unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  have "trail ?T \<Turnstile>as CNot C"
     by (simp add: cut_trail_wrt_clause_CNot_trail)
  then have [simp]: "cdcl\<^sub>W_conflicting ?T"
    unfolding cdcl\<^sub>W_conflicting_def apply simp
    by (metis M \<open>cdcl\<^sub>W_conflicting T\<close> append_assoc cdcl\<^sub>W_conflicting_decomp(2))

  have decomp_T: "all_decomposition_implies_m (init_clss T) (get_all_marked_decomposition (trail T))"
    using inv_T unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  have  "all_decomposition_implies_m  (init_clss ?T)
    (get_all_marked_decomposition (trail ?T))"
    unfolding all_decomposition_implies_def
    proof clarify
      fix a b
      assume "(a, b) \<in> set (get_all_marked_decomposition (trail ?T))"
      from in_get_all_marked_decomposition_in_get_all_marked_decomposition_prepend[OF this]
      obtain b' where
        "(a, b' @ b) \<in>  set (get_all_marked_decomposition (trail T))"
        using M (* TODO tune *) by simp metis
      then have "(\<lambda>a. {#lit_of a#}) ` set a \<union> set_mset (init_clss ?T)
        \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set (b @ b')"
        using decomp_T unfolding all_decomposition_implies_def
        (* TODO Tune *)
        apply auto
        by (metis (no_types, lifting) case_prodD set_append sup.commute true_clss_clss_insert_l)

      then show "(\<lambda>a. {#lit_of a#}) ` set a \<union> set_mset (init_clss ?T)
        \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set b"
        by (auto simp: image_Un)
    qed

  have [simp]: "cdcl\<^sub>W_learned_clause ?T"
    using inv_T unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_learned_clause_def
    by (auto dest!: H_proped simp: clauses_def)
  show ?thesis
    using \<open>all_decomposition_implies_m  (init_clss ?T)
    (get_all_marked_decomposition (trail ?T))\<close>
    unfolding cdcl\<^sub>W_all_struct_inv_def by (auto simp: add_new_clause_and_update_def)
qed

lemma cdcl\<^sub>W_all_struct_inv_add_new_clause_and_update_cdcl\<^sub>W_stgy_inv:
  assumes
    inv_s: "cdcl\<^sub>W_stgy_invariant T" and
    inv: "cdcl\<^sub>W_all_struct_inv T" and
    tr_T_N[simp]: "trail T \<Turnstile>asm N" and
    tr_C[simp]: "trail T \<Turnstile>as CNot C" and
    [simp]: "distinct_mset C"
  shows "cdcl\<^sub>W_stgy_invariant (add_new_clause_and_update C T)" (is "cdcl\<^sub>W_stgy_invariant ?T'")
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
      (false) "\<forall>L\<in>#C. - L \<notin> lits_of (trail T)" and"trail (cut_trail_wrt_clause C (trail T) T) = []"
    | (not_false) "- lit_of (hd (trail (cut_trail_wrt_clause C (trail T) T))) \<in># C" and
      "1 \<le> length (trail (cut_trail_wrt_clause C (trail T) T))"
    using cut_trail_wrt_clause_hd_trail_in_or_empty_trail[of C T] by auto
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
      have "get_all_levels_of_marked (trail (add_new_clause_and_update C T)) =
        rev [1..<1 + length (get_all_levels_of_marked (trail (add_new_clause_and_update C T)))]"
        using \<open>cdcl\<^sub>W_all_struct_inv ?T'\<close> unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def
        by blast
      moreover
        have "backtrack_lvl (cut_trail_wrt_clause C (trail T) T) =
          length (get_all_levels_of_marked (trail (add_new_clause_and_update C T)))"
          using \<open>cdcl\<^sub>W_all_struct_inv ?T'\<close> unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def
          by (auto simp:add_new_clause_and_update_def)
      moreover
        have "no_dup (trail (cut_trail_wrt_clause C (trail T) T))"
          using \<open>cdcl\<^sub>W_all_struct_inv ?T'\<close> unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def
          by (auto simp:add_new_clause_and_update_def)
        then have "atm_of ?L \<notin> atm_of ` lits_of (tl (trail (cut_trail_wrt_clause C (trail T) T)))"
          apply (cases "trail (cut_trail_wrt_clause C (trail T) T)")
          apply (auto)
          using Marked_Propagated_in_iff_in_lits_of defined_lit_map by blast

      ultimately have L: "get_level (-?L) (trail (cut_trail_wrt_clause C (trail T) T))
        = length (get_all_levels_of_marked (trail (cut_trail_wrt_clause C (trail T) T)))"
        using get_level_get_rev_level_get_all_levels_of_marked[OF
          \<open>atm_of ?L \<notin> atm_of ` lits_of (tl (trail (cut_trail_wrt_clause C (trail T) T)))\<close>,
          of "[hd (trail (cut_trail_wrt_clause C (trail T) T))]"]
          (* the expression \<open>trail (add_init_cls C (cut_trail_wrt_clause C (trail T) T)))\<close> can be
          simplified, but auto is not able to solve the goal when this is done.*)
          apply (cases "trail (add_init_cls C (cut_trail_wrt_clause C (trail T) T))";
           cases "hd (trail (cut_trail_wrt_clause C (trail T) T))")
          using l by (auto split: split_if_asm
            simp:rev_swap[symmetric] add_new_clause_and_update_def
            simp del:)

      have L': "length (get_all_levels_of_marked (trail (cut_trail_wrt_clause C (trail T) T)))
        = backtrack_lvl (cut_trail_wrt_clause C (trail T) T)"
        using \<open>cdcl\<^sub>W_all_struct_inv ?T'\<close> unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def
        by (auto simp:add_new_clause_and_update_def)

      have [simp]: "no_smaller_confl (update_conflicting (C_Clause C)
        (add_init_cls C (cut_trail_wrt_clause C (trail T) T)))"
        unfolding no_smaller_confl_def
      proof (clarify, goal_cases)
        case (1 M K i M' D)
        then consider
            (DC) "D = C"
          | (D_T) "D \<in># clauses T"
          by (auto simp: clauses_def split: split_if_asm)
        then show False
          proof cases
            case D_T
            have "no_smaller_confl T"
              using inv_s unfolding cdcl\<^sub>W_stgy_invariant_def by auto
            have "(MT @ M') @ Marked K i # M = trail T "
              using MT 1(1) by auto
            thus False using D_T \<open>no_smaller_confl T\<close> 1(3) unfolding no_smaller_confl_def by blast
          next
            case DC note _[simp] = this
            then have "atm_of (-?L) \<in> atm_of ` (lits_of M)"
              using 1(3) C in_CNot_implies_uminus(2) by blast
            moreover
              have "lit_of (hd (M' @ Marked K i # [])) = -?L"
                using l 1(1)[symmetric] inv
                by (cases "trail (add_init_cls C (cut_trail_wrt_clause C (trail T) T))")
                (auto dest!: arg_cong[of "_ # _" _ hd] simp: hd_append cdcl\<^sub>W_all_struct_inv_def
                  cdcl\<^sub>W_M_level_inv_def)
              from arg_cong[OF this, of atm_of]
              have "atm_of (-?L) \<in> atm_of ` (lits_of (M' @ Marked K i # []))"
                by (cases " (M' @ Marked K i # [])") auto
            moreover have "no_dup (trail (cut_trail_wrt_clause C (trail T) T))"
              using \<open>cdcl\<^sub>W_all_struct_inv ?T'\<close> unfolding cdcl\<^sub>W_all_struct_inv_def
              cdcl\<^sub>W_M_level_inv_def by (auto simp: add_new_clause_and_update_def)
            ultimately show False
              unfolding 1(1)[symmetric, simplified]
              apply auto
              using Marked_Propagated_in_iff_in_lits_of defined_lit_map apply blast
              by (metis IntI Marked_Propagated_in_iff_in_lits_of defined_lit_map empty_iff)
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
  shows "conflicting T = C_Clause {#} \<and> unsatisfiable (set_mset (init_clss S))
    \<or> conflicting T = C_True \<and> trail T \<Turnstile>asm init_clss S \<and> satisfiable (set_mset (init_clss S))"
proof -
  have "no_step cdcl\<^sub>W_stgy T"
    using full unfolding full_def by blast
  moreover have "cdcl\<^sub>W_all_struct_inv T" and inv_s: "cdcl\<^sub>W_stgy_invariant T"
    apply (metis cdcl\<^sub>W_ops.rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W cdcl\<^sub>W_ops_axioms full full_def inv
      rtranclp_cdcl\<^sub>W_all_struct_inv_inv)
    by (metis full full_def inv inv_s rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_stgy_invariant)
  ultimately have "conflicting T = C_Clause {#} \<and> unsatisfiable (set_mset (init_clss T))
    \<or> conflicting T = C_True \<and> trail T \<Turnstile>asm init_clss T"
    using cdcl\<^sub>W_stgy_final_state_conclusive[of T] full
    unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_stgy_invariant_def full_def by fast
  moreover have "consistent_interp (lits_of (trail T))"
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
  let ?T = "(update_conflicting (C_Clause C) (add_init_cls C (cut_trail_wrt_clause C (trail S) S)))"
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
  have "cdcl\<^sub>W_all_struct_inv (add_init_cls C S)"
    using inv \<open>distinct_mset C\<close> unfolding cdcl\<^sub>W_all_struct_inv_def no_strange_atm_def
    cdcl\<^sub>W_M_level_inv_def distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_conflicting_def cdcl\<^sub>W_learned_clause_def
    by (auto simp: all_decomposition_implies_insert_single clauses_def) (* SLOW ~2s *)
  then show ?case
    using add_no_confl(5) unfolding full_def by (auto intro: rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv)
  case 2 have "cdcl\<^sub>W_stgy_invariant (add_init_cls C S)"
    using s_inv \<open>\<not> trail S \<Turnstile>as CNot C\<close> inv unfolding cdcl\<^sub>W_stgy_invariant_def no_smaller_confl_def
    eq_commute[of "_" "trail _"] cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_all_struct_inv_def
    by (auto simp: true_annots_true_cls_def_iff_negation_in_model clauses_def split: split_if_asm)
  then show ?case
    by (metis \<open>cdcl\<^sub>W_all_struct_inv (add_init_cls C S)\<close> add_no_confl.hyps(5) full_def
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
  shows "conflicting T = C_Clause {#} \<and> unsatisfiable (set_mset (init_clss T))
    \<or> conflicting T = C_True \<and> trail T \<Turnstile>asm init_clss T \<and> satisfiable (set_mset (init_clss T))"
  using inc apply induction
  (* Here I thank Sledgehammer for its invaluable services *)
  apply (metis Nitpick.rtranclp_unfold add_confl full_cdcl\<^sub>W_stgy_inv_normal_form full_def
    incremental_cdcl\<^sub>W_inv(1) incremental_cdcl\<^sub>W_inv(2) inv s_inv)
  by (metis (full_types) rtranclp_unfold add_no_confl full_cdcl\<^sub>W_stgy_inv_normal_form
    full_def incremental_cdcl\<^sub>W_inv(1) incremental_cdcl\<^sub>W_inv(2) inv s_inv)

lemma tranclp_incremental_correct:
  assumes
    inc: "incremental_cdcl\<^sub>W\<^sup>+\<^sup>+ S T" and
    inv: "cdcl\<^sub>W_all_struct_inv S" and
    s_inv: "cdcl\<^sub>W_stgy_invariant S"
  shows "conflicting T = C_Clause {#} \<and> unsatisfiable (set_mset (init_clss T))
    \<or> conflicting T = C_True \<and> trail T \<Turnstile>asm init_clss T \<and> satisfiable (set_mset (init_clss T))"
  using inc apply induction
   using assms incremental_conclusive_state apply blast
  by (meson incremental_conclusive_state inv rtranclp_incremental_cdcl\<^sub>W_inv s_inv
    tranclp_into_rtranclp)

lemma blocked_induction_with_marked:
  assumes
    n_d: "no_dup (L # M)" and
    nil: "P []" and
    append: "\<And>M L M'. P M \<Longrightarrow> is_marked L \<Longrightarrow> \<forall>m \<in> set M'. \<not>is_marked m \<Longrightarrow> no_dup (L # M' @ M) \<Longrightarrow>
      P (L # M' @ M)" and
    L: "is_marked L"
  shows
    "P (L # M)"
  using n_d L
proof (induction "card {L' \<in> set M. is_marked L'}" arbitrary: L M)
  case 0 note n = this(1) and n_d = this(2) and L = this(3)
  then have "\<forall>m \<in> set M. \<not>is_marked m" by auto
  then show ?case using append[of "[]" L M] L nil n_d by auto
next
  case (Suc n) note IH = this(1) and n = this(2) and n_d = this(3) and L = this(4)
  have "\<exists>L' \<in> set M. is_marked L'"
    proof (rule ccontr)
      assume "\<not>?thesis"
      then have H: "{L' \<in> set M. is_marked L'} = {}"
        by auto
      show False using n unfolding H by auto
    qed
  then obtain L' M' M'' where
    M: "M = M' @ L' # M''" and
    L': "is_marked L'" and
    nm: "\<forall>m\<in>set M'. \<not>is_marked m"
    by (auto elim!: split_list_first_propE)
  have "Suc n = card {L' \<in> set M. is_marked L'}"
    using n .
  moreover have "{L' \<in> set M. is_marked L'} = {L'} \<union> {L' \<in> set M''. is_marked L'}"
    using nm L' n_d unfolding M by auto
  moreover have "L' \<notin> {L' \<in> set M''. is_marked L'}"
    using n_d unfolding M by auto
  ultimately  have "n = card {L'' \<in> set M''. is_marked L''}"
    using n L' by auto
  then have "P (L' # M'')" using IH L' n_d M by auto
  then show ?case using append[of "L' # M''" L M'] nm L n_d unfolding M by blast
qed

lemma trail_bloc_induction:
  assumes
    n_d: "no_dup M" and
    nil: "P []" and
    append: "\<And>M L M'. P M \<Longrightarrow> is_marked L \<Longrightarrow> \<forall>m \<in> set M'. \<not>is_marked m \<Longrightarrow> no_dup (L # M' @ M) \<Longrightarrow>
      P (L # M' @ M)" and
    append_nm: "\<And>M' M''. P M' \<Longrightarrow> M = M'' @  M' \<Longrightarrow> \<forall>m\<in>set M''. \<not>is_marked m \<Longrightarrow> P M"
  shows
    "P M"
proof (cases "{L' \<in> set M. is_marked L'} = {}")
  case True
  then show ?thesis using append_nm[of "[]" M] nil by auto
next
  case False
  then have "\<exists>L' \<in> set M. is_marked L'"
    by auto
  then obtain L' M' M'' where
    M: "M = M' @ L' # M''" and
    L': "is_marked L'" and
    nm: "\<forall>m\<in>set M'. \<not>is_marked m"
    by (auto elim!: split_list_first_propE)
  have "P (L' # M'')"
    apply (rule blocked_induction_with_marked)
       using n_d unfolding M apply simp
      using nil apply simp
     using append apply simp
    using L' by auto
  then show ?thesis
    using append_nm[of _ M'] nm  unfolding M by simp
qed

inductive Tcons :: "('v, nat, 'v clause) marked_lits \<Rightarrow>('v, nat, 'v clause) marked_lits \<Rightarrow> bool"
  for M :: "('v, nat, 'v clause) marked_lits" where
"Tcons M []" |
"Tcons M M' \<Longrightarrow> M = M'' @ M' \<Longrightarrow> (\<forall>m \<in> set M''. \<not>is_marked m) \<Longrightarrow> Tcons M (M'' @ M')" |
"Tcons M M' \<Longrightarrow> is_marked L \<Longrightarrow> M = M''' @ L # M'' @ M' \<Longrightarrow> (\<forall>m \<in> set M''. \<not>is_marked m) \<Longrightarrow>
  Tcons M (L # M'' @ M')"

lemma Tcons_same_end: "Tcons M M' \<Longrightarrow> \<exists>M''. M = M'' @ M'"
  by (induction rule: Tcons.induct) auto

end

end