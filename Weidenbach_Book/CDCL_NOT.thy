theory CDCL_NOT
imports Partial_Annotated_Clausal_Logic List_More Transition Partial_Clausal_Logic
begin

sledgehammer_params[verbose, prover=e spass z3 cvc4 verit remote_vampire]


section \<open>Initial definitions\<close>
subsection \<open>The state\<close>
text \<open>We define here an abstraction over operation on the state we are manipulating.\<close>
locale dpll_state =
  fixes
    trail :: "'st \<Rightarrow> ('v, 'lvl, 'mark) annoted_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    update_trail :: "('v, 'lvl, 'mark) annoted_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    add_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st"
  assumes
    trail_update_trail[simp]: "\<And>M st. trail (update_trail M st) = M" and
    clauses_add_clause[simp]: "\<And>st C. clauses (add_cls C st) = insert C (clauses st)" and
    clause_remove_clause[simp]: "\<And>st C. clauses (remove_cls C st) = clauses st - {C}" and
    clauses_update_trail[simp]: "\<And>st M. clauses(update_trail M st) = clauses st" and
    update_trail_add_cls[simp]: "\<And>st C. trail(add_cls C st) = trail st" and
    update_trail_remove_clauses[simp]: "\<And>st C. trail (remove_cls C st) = trail st"
begin
abbreviation prepend_trail where
"prepend_trail L S \<equiv> update_trail (L # trail S) S"
end

lemma true_clss_clss_union_false_true_clss_clss_cnot:
  "A \<union> {B} \<Turnstile>ps {{#}} \<longleftrightarrow> A \<Turnstile>ps CNot B"
  using total_not_CNot consistent_CNot_not unfolding total_over_m_def true_clss_clss_def
  by fastforce

lemma no_dup_cannot_not_lit_and_uminus:
  "no_dup M \<Longrightarrow> - lit_of xa = lit_of x \<Longrightarrow> x \<in> set M \<Longrightarrow> xa \<in> set M \<Longrightarrow> False"
  by (metis atm_of_uminus distinct_map inj_on_eq_iff uminus_not_id')

lemma true_clss_single_iff_incl:
  "I \<Turnstile>s single ` B \<longleftrightarrow> B \<subseteq> I"
  unfolding true_clss_def by auto

lemma atms_of_m_single_atm_of[simp]:
  "atms_of_m {{#lit_of L#} |L. P L} = atm_of ` {lit_of L |L. P L}"
  unfolding atms_of_m_def by auto

(* TODO Move?*)
lemma atms_of_uminus_lit_atm_of_lit_of:
  "atms_of {#- lit_of x. x \<in># A#} = atm_of ` (lit_of ` (set_mset A))"
  unfolding atms_of_def by (auto simp add: Fun.image_comp)

lemma atms_of_m_single_image_atm_of_lit_of:
  "atms_of_m ((\<lambda>x. {#lit_of x#}) ` A) = atm_of ` (lit_of ` A)"
  unfolding atms_of_m_def by auto

lemma is_marked_ex_Marked:
  "is_marked L \<Longrightarrow> \<exists>K lvl. L = Marked K lvl"
  by (cases L) auto

subsection \<open>Definition of the operation\<close>
locale propagate_ops =
  dpll_state trail clauses update_trail add_cls remove_cls for
    trail :: "'st \<Rightarrow> ('v, 'lvl, 'mark) annoted_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    update_trail :: "('v, 'lvl, 'mark) annoted_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    add_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st"
begin
inductive propagate :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
propagate[intro]: "C + {#L#} \<in> clauses S \<Longrightarrow> trail S \<Turnstile>as CNot C \<Longrightarrow> undefined_lit L (trail S)
  \<Longrightarrow> propagate S (prepend_trail (Propagated L mark) S)"

inductive_cases propagateE[elim]: "propagate S T"
thm propagateE
end

locale decide_ops =
  dpll_state trail clauses update_trail add_cls remove_cls for
    trail :: "'st \<Rightarrow> ('v, 'lvl, 'mark) annoted_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    update_trail :: "('v, 'lvl, 'mark) annoted_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    add_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st"
begin
inductive decide ::  "'st \<Rightarrow> 'st \<Rightarrow> bool" where
decide[intro]: "undefined_lit L (trail S) \<Longrightarrow> atm_of L \<in> atms_of_m (clauses S)
  \<Longrightarrow> decide S (prepend_trail (Marked L d) S)"

inductive_cases decideE[elim]: "decide S S'"
end

locale backjumping_ops =
  dpll_state trail clauses update_trail add_cls remove_cls
  for
    trail :: "'st \<Rightarrow> ('v, 'lvl, 'mark) annoted_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    update_trail :: "('v, 'lvl, 'mark) annoted_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    add_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" +
  fixes
    inv :: "'st \<Rightarrow> bool" and
    backjump_cond :: "'st \<Rightarrow> 'st \<Rightarrow> bool"
begin
inductive backjump where
" trail S = F' @ Marked K d # F
   \<Longrightarrow> T = update_trail (Propagated L l # F) S
   \<Longrightarrow> C \<in> clauses S
   \<Longrightarrow> trail S \<Turnstile>as CNot C
   \<Longrightarrow> undefined_lit L F
   \<Longrightarrow> atm_of L \<in> atms_of_m (clauses S) \<union> atm_of ` (lits_of (trail S))
   \<Longrightarrow> clauses S \<Turnstile>p C' + {#L#}
   \<Longrightarrow> F \<Turnstile>as CNot C'
   \<Longrightarrow> backjump_cond S T
   \<Longrightarrow> backjump S T"
inductive_cases backjumpE: "backjump S T"
end

section \<open>DPLL with backjumping\<close>
locale dpll_with_backjumping_ops =
  dpll_state trail clauses update_trail add_cls remove_cls +
  propagate_ops trail clauses update_trail add_cls remove_cls +
  decide_ops trail clauses update_trail add_cls remove_cls +
  backjumping_ops trail clauses update_trail add_cls remove_cls inv backjump_cond
  for
    trail :: "'st \<Rightarrow> ('v, 'lvl, 'mark) annoted_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    update_trail :: "('v, 'lvl, 'mark) annoted_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    add_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    inv :: "'st \<Rightarrow> bool" and
    backjump_cond :: "'st \<Rightarrow> 'st \<Rightarrow> bool" +
  assumes
      bj_can_jump:
      "\<And>S C F' K d F L.
        inv S
        \<Longrightarrow> trail S = F' @ Marked K d # F
        \<Longrightarrow> C \<in> clauses S
        \<Longrightarrow> trail S \<Turnstile>as CNot C
        \<Longrightarrow> undefined_lit L F
        \<Longrightarrow> atm_of L \<in> atms_of_m (clauses S) \<union> atm_of ` (lits_of (F' @ Marked K d # F))
        \<Longrightarrow> clauses S \<Turnstile>p C' + {#L#}
        \<Longrightarrow> F \<Turnstile>as CNot C'
        \<Longrightarrow> \<not>no_step backjump S"
begin

text \<open>We cannot add a like condition @{term "atms_of C' \<subseteq> atms_of_m N"} because to ensure that we
  can backjump even if the last decision variable has disappeared.

  The part of the condition @{term "atm_of L \<in> atm_of ` (lits_of (F' @ Marked K d # F))"} is
  important, otherwise you are not sure that you can backtrack.\<close>

subsection\<open>Definition\<close>

text \<open>We define dpll with backjumping:\<close>
inductive dpll_bj :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
bj_decide:  "decide S S' \<Longrightarrow> dpll_bj S S'" |
bj_propagate: "propagate S S' \<Longrightarrow> dpll_bj S S'" |
bj_backjump:  "backjump S S' \<Longrightarrow> dpll_bj S S'"

lemmas dpll_bj_induct = dpll_bj.induct[split_format(complete)]
lemma dpll_bj_all_induct[consumes 2, case_names decide propagate backjump]:
  fixes S T :: "'st"
  assumes
    "dpll_bj S T" and
    "inv S"
    "\<And>L S d. undefined_lit L (trail S) \<Longrightarrow> atm_of L \<in> atms_of_m (clauses S)
      \<Longrightarrow> P S (prepend_trail (Marked L d) S)" and
    "\<And>C L S mark. C + {#L#} \<in> clauses S \<Longrightarrow> trail S \<Turnstile>as CNot C \<Longrightarrow> undefined_lit L (trail S)
      \<Longrightarrow> P S (prepend_trail (Propagated L mark) S)" and
    "\<And>S C F' K d F L C' l. C \<in> clauses S \<Longrightarrow> F' @ Marked K d # F \<Turnstile>as CNot C
      \<Longrightarrow> trail S = F' @ Marked K d # F
      \<Longrightarrow> undefined_lit L F
      \<Longrightarrow> atm_of L \<in> atms_of_m (clauses S) \<union> atm_of ` (lits_of (F' @ Marked K d # F))
      \<Longrightarrow> (clauses S) \<Turnstile>p C' + {#L#}
      \<Longrightarrow> F \<Turnstile>as CNot C'
      \<Longrightarrow> P S (update_trail (Propagated L l #  F) S)"
  shows "P S T"
  using assms(2)
  by (induction rule: dpll_bj_induct[OF local.dpll_with_backjumping_ops_axioms assms(1)])
     (auto intro!: assms(3,4) elim!: backjumpE simp add: assms(1,5))[3]

subsection \<open>Basic properties\<close>
paragraph \<open>First, some better suited induction principle\<close>
lemma dpll_bj_clauses:
  assumes "dpll_bj S T" and "inv S"
  shows "clauses S = clauses T"
  using assms by (induction rule: dpll_bj_all_induct) auto

paragraph \<open>No duplicates in the trail\<close>
lemma dpll_bj_no_dup:
  assumes "dpll_bj S T" and "inv S"
  and "no_dup (trail S)"
  shows "no_dup (trail T)"
  using assms by (induction rule: dpll_bj_all_induct) (auto simp add: defined_lit_map)

paragraph \<open>Valuations\<close>
lemma dpll_bj_sat_iff:
  assumes "dpll_bj S T" and "inv S"
  shows "I \<Turnstile>s clauses S \<longleftrightarrow> I \<Turnstile>s clauses T"
  using assms by (induction rule: dpll_bj_all_induct) auto

paragraph \<open>Clauses\<close>
lemma dpll_bj_atms_of_m_clauses_inv:
  assumes
    "dpll_bj S T" and
    "inv S"
  shows "atms_of_m (clauses S) = atms_of_m (clauses T)"
  using assms by (induction rule: dpll_bj_all_induct) auto

lemma dpll_bj_atms_in_trail:
  assumes
    "dpll_bj S T" and
    "inv S" and
    "atm_of ` (lits_of (trail S)) \<subseteq> atms_of_m (clauses S)"
  shows "atm_of ` (lits_of (trail T)) \<subseteq> atms_of_m (clauses S)"
  using assms by (induction rule: dpll_bj_all_induct) auto

lemma dpll_bj_atms_in_trail_in_set:
  assumes "dpll_bj S T"and
    "inv S" and
  "atms_of_m (clauses S) \<subseteq> A" and
  "atm_of ` (lits_of (trail S)) \<subseteq> A"
  shows "atm_of ` (lits_of (trail T)) \<subseteq> A"
  using assms by (induction rule: dpll_bj_all_induct) auto

lemma dpll_bj_all_decomposition_implies_inv:
  assumes
    "dpll_bj S T" and
    "inv S"
    "all_decomposition_implies (clauses S) (get_all_marked_decomposition (trail S))"
  shows "all_decomposition_implies (clauses T) (get_all_marked_decomposition (trail T))"
  using assms
proof (induction rule:dpll_bj_all_induct)
  case decide
  thus ?case by auto
next
  case (propagate C L S mark) note propa = this(1) and decomp = this(4)
  let ?M' = "trail (prepend_trail (Propagated L mark) S)"
  let ?N = "clauses S"
  obtain a y l where ay: "get_all_marked_decomposition ?M' = (a, y) # l"
    by (cases "get_all_marked_decomposition ?M'") fastforce+
  hence M': "?M' = y @ a" using get_all_marked_decomposition_decomp[of ?M'] by auto
  have M: "get_all_marked_decomposition (trail S) = (a, tl y) # l"
    using ay by (cases " get_all_marked_decomposition (trail S)") auto
  have y\<^sub>0: "y = (Propagated L mark) # (tl y)"
    using ay by (auto simp add: M)
  from arg_cong[OF this, of set] have y[simp]: "set y = insert (Propagated L mark) (set (tl y))"
    by simp
  have tr_S: "trail S = tl y @ a"
    using arg_cong[OF M', of tl] y\<^sub>0 M get_all_marked_decomposition_decomp by force
  have a_Un_N_M: "(\<lambda>a. {#lit_of a#}) ` set a \<union> ?N \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set (tl y)"
    using decomp ay unfolding all_decomposition_implies_def by (simp add: M)+

  moreover have "(\<lambda>a. {#lit_of a#}) ` set a \<union> ?N \<Turnstile>p {#L#}" (is "?I \<Turnstile>p _")
    proof (rule true_clss_cls_plus_CNot)
      show "?I \<Turnstile>p C + {#L#}"
        using propa propagate.prems by (auto dest!: true_clss_clss_in_imp_true_clss_cls)
    next
      have "(\<lambda>m. {#lit_of m#}) ` set ?M' \<Turnstile>ps CNot C"
        using \<open>trail S \<Turnstile>as CNot C\<close> by (auto simp add: true_annots_true_clss_clss)
      have a1: "(\<lambda>m. {#lit_of m#}) ` set a \<union> (\<lambda>m. {#lit_of m#}) ` set (tl y)  \<Turnstile>ps CNot C"
        using propagate.hyps(2) tr_S true_annots_true_clss_clss
        by (force simp add: image_Un sup_commute)
      have a2: "clauses S \<union> (\<lambda>a. {#lit_of a#}) ` set a \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set (tl y)"
        using calculation by (auto simp add: sup_commute)
      show "(\<lambda>m. {#lit_of m#}) ` set a  \<union> clauses S\<Turnstile>ps CNot C"
        proof -
          have "clauses S \<union> (\<lambda>m. {#lit_of m#}) ` set a \<Turnstile>ps
            (\<lambda>m. {#lit_of m#}) ` set a \<union> (\<lambda>m. {#lit_of m#}) ` set (tl y)"
            using a2 true_clss_clss_def by blast
          thus "(\<lambda>m. {#lit_of m#}) ` set a  \<union> clauses S\<Turnstile>ps CNot C"
            using a1 unfolding sup_commute by (meson true_clss_clss_left_right
              true_clss_clss_union_and true_clss_clss_union_l_r )
        qed
    qed

  ultimately have "(\<lambda>a. {#lit_of a#}) ` set a \<union> ?N \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set ?M'"
    unfolding M' by (auto simp add: all_in_true_clss_clss image_Un)

  thus ?case
    using decomp unfolding ay M all_decomposition_implies_def by (auto simp add: ay)
next
  case (backjump S C F' K d F L D l) note confl = this(2) and tr = this(3) and undef = this(4)
    and L = this(5) and N_C = this(6) and vars_D = this(5) and decomp = this(8)
  have decomp: "all_decomposition_implies (clauses S) (get_all_marked_decomposition F)"
    using decomp unfolding tr by (smt all_decomposition_implies_def
      get_all_marked_decomposition.simps(1) get_all_marked_decomposition_never_empty hd_Cons_tl
      insert_iff list.sel(3) list.set(2) tl_get_all_marked_decomposition_skip_some)

  moreover have "(\<lambda>a. {#lit_of a#}) ` set (fst (hd (get_all_marked_decomposition F))) \<union> clauses S
    \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set (snd (hd (get_all_marked_decomposition F)))"
    by (metis all_decomposition_implies_cons_single decomp get_all_marked_decomposition_never_empty
      hd_Cons_tl)
  moreover
    have vars_of_D: "atms_of D \<subseteq> atm_of ` lit_of ` set F"
      using \<open>F \<Turnstile>as CNot D\<close> unfolding lits_of_def atms_of_def
      by (meson image_subsetI mem_set_mset_iff true_annots_CNot_all_atms_defined)

  obtain a b li where F: "get_all_marked_decomposition F = (a, b) # li"
    by (cases "get_all_marked_decomposition F") auto
  have "F = b @ a"
    using get_all_marked_decomposition_decomp[of F a b] F by auto
  have a_N_b:"(\<lambda>a. {#lit_of a#}) ` set a \<union> clauses S \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set b"
    using decomp unfolding all_decomposition_implies_def by (auto simp add: F)

  have F_D:"(\<lambda>a. {#lit_of a#}) ` set F \<Turnstile>ps CNot D"
    using \<open>F \<Turnstile>as CNot D\<close> by (simp add: true_annots_true_clss_clss)
  hence "(\<lambda>a. {#lit_of a#}) ` set a \<union> (\<lambda>a. {#lit_of a#}) ` set b \<Turnstile>ps CNot D"
    unfolding \<open>F = b @ a\<close> by (simp add: image_Un sup.commute)
  have a_N_CNot_D: "(\<lambda>a. {#lit_of a#}) ` set a \<union> clauses S \<Turnstile>ps CNot D \<union> (\<lambda>a. {#lit_of a#}) ` set b"
    apply (rule true_clss_clss_left_right)
    using a_N_b  F_D unfolding \<open>F = b @ a\<close> by (auto simp add: image_Un ac_simps)

  have a_N_D_L: "(\<lambda>a. {#lit_of a#}) ` set a \<union> clauses S \<Turnstile>p D+{#L#}"
    by (simp add: N_C)
  have "(\<lambda>a. {#lit_of a#}) ` set a \<union> clauses S \<Turnstile>p {#L#}"
    apply (rule true_clss_cls_plus_CNot)
      using a_N_D_L apply simp
     using a_N_CNot_D apply simp
    done
  thus ?case using decomp unfolding all_decomposition_implies_def by (auto simp add: F)
qed

subsection \<open>Termination\<close>
subsubsection \<open>Using a proper measure\<close>
text \<open>This measure can also be seen as the increasing lexicographic order: it is an order on bounded
  sequences, when each element is bound. The proof involves a measure like the one defined here (the
  same?).\<close>
definition \<mu>\<^sub>C  :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat" where
"\<mu>\<^sub>C s b M \<equiv> (\<Sum>i=0..<length M. M!i * b^ (s +i - length M))"

lemma \<mu>\<^sub>C_nil[simp]:
  "\<mu>\<^sub>C s b [] = 0"
  unfolding \<mu>\<^sub>C_def by auto

lemma \<mu>\<^sub>C_single[simp]:
  "\<mu>\<^sub>C s b [L] = L * b ^ (s - Suc 0)"
  unfolding \<mu>\<^sub>C_def by auto

lemma set_sum_atLeastLessThan_add:
  "(\<Sum>i=k..<k+(b::nat). f i) = (\<Sum>i=0..<b. f (k+ i))"
  by (induction b) auto

lemma set_sum_atLeastLessThan_Suc:
  "(\<Sum>i=1..<Suc j. f i) = (\<Sum>i=0..<j. f (Suc i))"
  using set_sum_atLeastLessThan_add[of _ 1 j] by force

lemma \<mu>\<^sub>C_cons:
  "\<mu>\<^sub>C s b (L # M) = L * b ^ (s - 1 - length M) + \<mu>\<^sub>C s b M"
proof -
  have "\<mu>\<^sub>C s b (L # M) = (\<Sum>i=0..<length (L#M). (L#M)!i * b^ (s +i - length (L#M)))"
    unfolding \<mu>\<^sub>C_def by blast
  also have "\<dots> = (\<Sum>i=0..<1. (L#M)!i * b^ (s +i - length (L#M)))
                 + (\<Sum>i=1..<length (L#M). (L#M)!i * b^ (s +i - length (L#M)))"
     by (smt Nat.le_iff_add One_nat_def add.commute le0 list.size(4) setsum_add_nat_ivl)
  finally have "\<mu>\<^sub>C s b (L # M)= L * b ^ (s - 1 - length M)
                  + (\<Sum>i=1..<length (L#M). (L#M)!i * b^ (s +i - length (L#M)))"
     by auto
  moreover {
    have "(\<Sum>i=1..<length (L#M). (L#M)!i * b^ (s +i - length (L#M))) =
           (\<Sum>i=0..<length (M). (L#M)!(Suc i) * b^ (s + (Suc i) - length (L#M)))"
     unfolding length_Cons set_sum_atLeastLessThan_Suc by blast
    also have "\<dots> = (\<Sum>i=0..<length (M). M!i * b^ (s + i - length M))"
      by auto
    finally have "(\<Sum>i=1..<length (L#M). (L#M)!i * b^ (s +i - length (L#M))) = \<mu>\<^sub>C s b M"
      unfolding \<mu>\<^sub>C_def .
    }
  ultimately show ?thesis by presburger
qed

lemma \<mu>\<^sub>C_append:
  assumes "s \<ge> length (M@M')"
  shows "\<mu>\<^sub>C s b (M@M') = \<mu>\<^sub>C (s - length M') b M + \<mu>\<^sub>C s b M'"
proof -
  have "\<mu>\<^sub>C s b (M@M') = (\<Sum>i=0..<length (M@M'). (M@M')!i * b^ (s +i - length (M@M')))"
    unfolding \<mu>\<^sub>C_def by blast
  moreover hence "\<dots> = (\<Sum>i=0..< length M. (M@M')!i * b^ (s +i - length (M@M')))
                 + (\<Sum>i=length M..<length (M@M'). (M@M')!i * b^ (s +i - length (M@M')))"
    unfolding length_append by (smt Nat.le_iff_add One_nat_def add.commute le0 list.size(4)
      setsum_add_nat_ivl)
  moreover
    have "\<forall>i\<in>{0..< length M}. (M@M')!i * b^ (s +i - length (M@M')) = M ! i * b ^ (s - length M'
      + i - length M)"
      using \<open>s \<ge> length (M@M')\<close> by (auto simp add: nth_append ac_simps)
    hence "\<mu>\<^sub>C (s - length M') b M = (\<Sum>i=0..< length M. (M@M')!i * b^ (s +i - length (M@M')))"
      unfolding \<mu>\<^sub>C_def by auto
  ultimately have "\<mu>\<^sub>C s b (M@M')= \<mu>\<^sub>C (s - length M') b M
                  + (\<Sum>i=length M..<length (M@M'). (M@M')!i * b^ (s +i - length (M@M')))"
     by auto
  moreover {
    have "(\<Sum>i=length M..<length (M@M'). (M@M')!i * b^ (s +i - length (M@M'))) =
           (\<Sum>i=0..<length M'. M'!i * b^ (s + i - length M'))"
     unfolding length_append set_sum_atLeastLessThan_add by auto
    hence "(\<Sum>i=length M..<length (M@M'). (M@M')!i * b^ (s +i - length (M@M'))) = \<mu>\<^sub>C s b M'"
      unfolding \<mu>\<^sub>C_def .
    }
  ultimately show ?thesis by presburger
qed

lemma \<mu>\<^sub>C_cons_non_empty_inf:
  assumes M_ge_1: "\<forall>i\<in>set M. i \<ge> 1" and M: "M \<noteq> []"
  shows "\<mu>\<^sub>C s b M \<ge> b ^  (s - length M)"
  using assms by (cases M) (auto simp: mult_eq_if \<mu>\<^sub>C_cons)

text \<open>Duplicate of "~~/src/HOL/ex/NatSum.thy"\<close>
lemma sum_of_powers: "0 < k \<Longrightarrow> (k - 1) * (\<Sum>i=0..<n. k^i) = k^n - (1::nat)"
  by (induct n) (auto simp add: Nat.nat_distrib)

text \<open>We add 1 to count the marked literal\<close>
abbreviation \<nu> where
"\<nu> S \<equiv> map ((\<lambda>l. 1 + length l) o snd) (get_all_marked_decomposition (trail S))"

text \<open>In the degenerated cases, we only have the large inequality holds. In the other cases, the
  following strict inequality holds:\<close>
lemma \<mu>\<^sub>C_bounded_non_degenerated:
  fixes b ::nat
  assumes
    "b > 0" and
    "M \<noteq> []" and
    M_le: "\<forall>i < length M. M!i < b" and
    "s \<ge> length M"
  shows "\<mu>\<^sub>C s b M < b^s"
proof -
  consider (b1) "b= 1" | (b) "b>1" using \<open>b>0\<close> by (cases b) auto
  thus ?thesis
    proof cases
      case b1
      hence "\<forall>i < length M. M!i = 0" using M_le by auto
      hence "\<mu>\<^sub>C s b M = 0" unfolding \<mu>\<^sub>C_def by auto
      thus ?thesis using \<open>b > 0\<close> by auto
    next
      case b
      have "\<forall> i \<in> {0..<length M}. M!i * b^ (s +i - length M) \<le> (b-1) * b^ (s +i - length M)"
        using M_le \<open>b > 1\<close> by auto
      hence "\<mu>\<^sub>C s b M \<le>  (\<Sum>i=0..<length M. (b-1) * b^ (s +i - length M))"
         using \<open>M\<noteq>[]\<close> \<open>b>0\<close> unfolding \<mu>\<^sub>C_def by (auto intro: setsum_mono)
      also
        have "\<forall> i \<in> {0..<length M}. (b-1) * b^ (s +i - length M) = (b-1) * b^ i * b^(s - length M)"
          by (metis Nat.add_diff_assoc2 add.commute assms(4) mult.assoc power_add)
        hence "(\<Sum>i=0..<length M. (b-1) * b^ (s +i - length M))
          = (\<Sum>i=0..<length M. (b-1)* b^ i * b^(s - length M))"
          by (auto simp add: ac_simps)
      also have "\<dots> = (\<Sum>i=0..<length M. b^ i) * b^(s - length M) * (b-1)"
         by (simp add: setsum_left_distrib setsum_right_distrib ac_simps)
      finally have "\<mu>\<^sub>C s b M \<le> (\<Sum>i=0..<length M. b^ i) * (b-1) * b^(s - length M)"
        by (simp add: ac_simps)

      also
        have "(\<Sum>i=0..<length M. b^ i)* (b-1) = b ^ (length M) - 1"
          using sum_of_powers[of b "length M"] \<open>b>1\<close>
          by (auto simp add: ac_simps)
      finally have "\<mu>\<^sub>C s b M \<le> (b ^ (length M) - 1) * b ^ (s - length M)"
        by auto
      also have "\<dots> < b ^ (length M) * b ^ (s - length M)"
        using \<open>b>1\<close> by auto
      also have "\<dots> = b ^ s"
        by (metis assms(4) le_add_diff_inverse power_add)
      finally show ?thesis unfolding \<mu>\<^sub>C_def by (auto simp add: ac_simps)
    qed
qed

text \<open> In the degenerate case @{term "b=0"}, the list @{term M} is empty (since the list cannot
  contain any element).\<close>
lemma \<mu>\<^sub>C_bounded:
  fixes b ::nat
  assumes
    M_le: "\<forall>i < length M. M!i < b" and
    "s \<ge> length M"
    "b > 0"
  shows "\<mu>\<^sub>C s b M < b ^ s"
proof -
  consider (M0) "M = []" | (M) "b > 0" and "M \<noteq> []"
    using M_le by (cases b, cases M) auto
  thus ?thesis
    proof cases
      case M0
      thus ?thesis using M_le \<open>b > 0\<close> by auto
    next
      case M
      show ?thesis using \<mu>\<^sub>C_bounded_non_degenerated[OF M assms(1,2)] by arith
    qed
qed

text \<open>When @{term "b=(0::nat)"}, we cannot show that the measure is empty, since @{term "0^0 =
  (1::nat)"}.\<close>
lemma \<mu>\<^sub>C_base_0:
  assumes "length M \<le> s"
  shows "\<mu>\<^sub>C s 0 M \<le> M!0"
proof -
  {
    assume "s = length M"
    moreover {
      fix n
      have "(\<Sum>i=0..<n. M ! i * (0::nat) ^ i) \<le> M ! 0"
        apply (induction n rule: nat_induct)
        by simp (case_tac n, auto)
    }
    ultimately have ?thesis unfolding \<mu>\<^sub>C_def by auto
  }
  moreover
  {
    assume "length M < s"
    hence "\<mu>\<^sub>C s 0 M = 0" unfolding \<mu>\<^sub>C_def by auto}
  ultimately show ?thesis using assms unfolding \<mu>\<^sub>C_def by linarith
qed

lemma length_in_get_all_marked_decomposition_bounded:
  assumes i:"i \<in> set (\<nu> S)"
  shows "i \<le> Suc (length (trail S))"
proof -
  obtain a b where
    "(a, b) \<in> set (get_all_marked_decomposition (trail S))" and
    ib: "i = Suc (length b)"
    using i by auto
  then obtain c where "trail S = c @ b @ a"
    using get_all_marked_decomposition_exists_prepend' by metis
  from arg_cong[OF this, of length] show ?thesis using i ib by auto
qed

lemma length_get_all_marked_decomposition_append_Marked:
  "length (get_all_marked_decomposition (F' @ Marked K d # F)) =
    length (get_all_marked_decomposition F')
    + length (get_all_marked_decomposition (Marked K d # F))
    - 1"
  by (induction F' rule: marked_lit_list_induct) auto

lemma take_length_get_all_marked_decomposition_marked_sandwich:
  "take (length (get_all_marked_decomposition F))
      (map (f o snd) (rev (get_all_marked_decomposition (F' @ Marked K d # F))))
      =
     map (f o snd) (rev (get_all_marked_decomposition F))
    "
proof (induction F' rule: marked_lit_list_induct)
  case nil
  thus ?case by auto
next
  case (marked K)
  thus ?case by (simp add: length_get_all_marked_decomposition_append_Marked)
next
  case (proped L m F') note IH = this(1)
  obtain a b l where F': "get_all_marked_decomposition (F' @ Marked K d # F) = (a, b) # l"
    by (cases "get_all_marked_decomposition (F' @ Marked K d # F)") auto
  have "length (get_all_marked_decomposition F) - length l = 0"
    using length_get_all_marked_decomposition_append_Marked[of F' K d F]
    unfolding F' by (cases "get_all_marked_decomposition F'") auto
  thus ?case
    using IH by (simp add: F')
qed

lemma length_get_all_marked_decomposition_length:
  "length (get_all_marked_decomposition M) \<le> 1 + length M"
  by (induction M rule: marked_lit_list_induct) auto

text \<open>The bounds are the following:
  \<^item> @{term "1+card (atms_of_m A)"}: @{term "card (atms_of_m A)"} is an upper bound on the length of
  the list. As @{term get_all_marked_decomposition} appends an possibly empty couple at the end,
  adding one is needed.
  \<^item> @{term "2+card (atms_of_m A)"}: @{term "card (atms_of_m A)"} is an upper bound on the number of
  elements, where adding one is necessary for the same reason as for the bound on the list, and one
  is needed to have a strict bound.
  \<close>
abbreviation unassigned_lit ::  "'b literal multiset set \<Rightarrow> 'a list \<Rightarrow> nat" where
  "unassigned_lit N M \<equiv> card (atms_of_m N) - length M"
lemma dpll_bj_trail_mes_increasing_prop:
  fixes M :: "('v, 'lvl, 'mark) annoted_lits " and N :: "'v clauses"
  assumes "dpll_bj S T" and "inv S"
  "atms_of_m (clauses S) \<subseteq> atms_of_m A" and
  "atm_of ` lits_of (trail S) \<subseteq> atms_of_m A" and
  "no_dup (trail S)" and
  finite: "finite A"
  shows "\<mu>\<^sub>C (1+card (atms_of_m A)) (2+card (atms_of_m A)) (\<nu> T) > \<mu>\<^sub>C (1+card (atms_of_m A))
    (2+card (atms_of_m A)) (\<nu> S)"
  using assms
proof (induction rule: dpll_bj_all_induct)
  case (propagate C L S d) note CLN = this(1) and MC =this(2) and undef_L = this(3) and
    A = this(4) and MA = this(5)
  have incl: "atm_of ` lits_of (Propagated L d # trail S) \<subseteq> atms_of_m A"
    using dpll_bj_atms_in_trail_in_set bj_propagate propagate.propagate[OF propagate.hyps] A MA CLN
    by auto

  have no_dup: "no_dup (Propagated L d # trail S)"
    using defined_lit_map propagate.prems(3) undef_L by auto
  obtain a b l where M: "get_all_marked_decomposition (trail S) = (a, b) # l"
    by (case_tac "get_all_marked_decomposition (trail S)") auto
  have b_le_M: "length b \<le> length (trail S)"
    using get_all_marked_decomposition_decomp[of "trail S"] by (simp add: M)
  have "finite (atms_of_m A)" using finite by simp

  hence "length (Propagated L d # trail S) \<le> card (atms_of_m A)"
    using incl finite unfolding no_dup_length_eq_card_atm_of_lits_of[OF no_dup]
    by (simp add: card_mono)
  hence latm: "unassigned_lit A b = Suc (unassigned_lit A (Propagated L d # b))"
    using b_le_M by auto
  thus ?case by (auto simp: latm M \<mu>\<^sub>C_cons)
next
  case (decide L S lv) note undef_L = this(1) and MC =this(2) and NA = this(3) and A = this(4)
    and MA = this(5)
  have incl: "atm_of ` lits_of (Marked L lv # (trail S)) \<subseteq> atms_of_m A"
    using dpll_bj_atms_in_trail_in_set bj_decide decide.decide[OF decide.hyps] A MA NA MC by auto

  have no_dup: "no_dup (Marked L lv # (trail S))"
    using defined_lit_map decide.prems(3) undef_L by auto
  obtain a b l where M: "get_all_marked_decomposition (trail S) = (a, b) # l"
    by (case_tac "get_all_marked_decomposition (trail S)") auto

  hence "length (Marked L lv # (trail S)) \<le> card (atms_of_m A)"
    using incl finite unfolding no_dup_length_eq_card_atm_of_lits_of[OF no_dup]
    by (simp add: card_mono)
  hence latm: "unassigned_lit A (trail S) = Suc (unassigned_lit A (Marked L lv # (trail S)))" by force
  show ?case by (simp add: latm \<mu>\<^sub>C_cons)
next
  case (backjump S C F' K d F L C' lv) note undef_L = this(4) and MC =this(1) and tr_S = this(3) and
    NA = this(8) and A = this(5) and MA = this(9) and nd = this(10)
  have incl: "atm_of ` lits_of (Propagated L lv # F) \<subseteq> atms_of_m A"
    using dpll_bj_atms_in_trail_in_set backjump(3,5,8,9) by auto

  have no_dup: "no_dup (Propagated L lv # F)"
    using defined_lit_map nd undef_L tr_S by auto
  obtain a b l where M: "get_all_marked_decomposition (trail S) = (a, b) # l"
    by (case_tac "get_all_marked_decomposition (trail S)") auto
  have b_le_M: "length b \<le> length (trail S)"
    using get_all_marked_decomposition_decomp[of "trail S"] by (simp add: M)
  have fin_atms_A: "finite (atms_of_m A)" using finite by simp

  hence F_le_A: "length (Propagated L lv # F) \<le>  card (atms_of_m A)"
    using incl finite unfolding no_dup_length_eq_card_atm_of_lits_of[OF no_dup]
    by (simp add: card_mono)
  have tr_S_le_A: "length (trail S) \<le>  (card (atms_of_m A))"
    using nd MA by (metis fin_atms_A card_mono no_dup_length_eq_card_atm_of_lits_of)
  obtain a b l where F: "get_all_marked_decomposition F = (a, b) # l"
    by (cases "get_all_marked_decomposition F") auto
  hence "F = b @ a"
    using get_all_marked_decomposition_decomp[of "Propagated L lv # F" a "Propagated L lv # b"]
      by simp
  hence latm: "unassigned_lit A b = Suc (unassigned_lit A (Propagated L lv # b))"
     using F_le_A by simp
  obtain rem where
    rem:"(map (\<lambda>a. Suc (length (snd a))) (rev (get_all_marked_decomposition (F' @ Marked K d # F))))
    = map (\<lambda>a. Suc (length (snd a))) (rev (get_all_marked_decomposition F)) @ rem"
    using take_length_get_all_marked_decomposition_marked_sandwich[of F "\<lambda>a. Suc (length a)" F' K d]
    unfolding o_def
    by (metis append_take_drop_id)
  hence rem: "map (\<lambda>a. Suc (length (snd a))) ((get_all_marked_decomposition (F' @ Marked K d # F)))
    = rev rem @ map (\<lambda>a. Suc (length (snd a))) ((get_all_marked_decomposition F))"
    by (simp add: rev_map[symmetric] rev_swap)
  have "length (rev rem @ map (\<lambda>a. Suc (length (snd a))) (get_all_marked_decomposition F))
          \<le> Suc (card (atms_of_m A))"
    using arg_cong[OF rem, of length] tr_S_le_A
    length_get_all_marked_decomposition_length[of "F' @ Marked K d # F"] tr_S by auto
  moreover
    { fix i :: nat and xs :: "'a list"
      have "i < length xs \<Longrightarrow> length xs - Suc i < length xs"
        by auto
      hence H: "i<length xs \<Longrightarrow> rev xs ! i \<in> set xs"
        using rev_nth[of i xs] unfolding in_set_conv_nth by (force simp add: in_set_conv_nth)
    } note H = this
    have "\<forall>i<length rem. rev rem ! i < card (atms_of_m A) + 2"
      using tr_S_le_A length_in_get_all_marked_decomposition_bounded[of _ S] unfolding tr_S
      by (force simp add: o_def rem dest!: H intro: length_get_all_marked_decomposition_length)
  ultimately show ?case
    using \<mu>\<^sub>C_bounded[of "rev rem" "card (atms_of_m A)+2" "unassigned_lit A l"]
    by (simp add: rem \<mu>\<^sub>C_append \<mu>\<^sub>C_cons F tr_S)
qed

lemma dpll_bj_wf:
  assumes fin: "finite A"
  shows "wf {(T, S). dpll_bj S T
    \<and> atms_of_m (clauses S) \<subseteq> atms_of_m A \<and> atm_of ` lits_of (trail S) \<subseteq> atms_of_m A
    \<and> no_dup (trail S) \<and> inv S}"
  (is "wf ?A")
proof (rule wf_bounded_measure[of _
        "\<lambda>_. (2 + card (atms_of_m A))^(1 + card (atms_of_m A))"
        "\<lambda>S. \<mu>\<^sub>C (1+card (atms_of_m A)) (2+card (atms_of_m A)) (\<nu> S)"])
  fix a b :: "'st"
  let ?b = "2+card (atms_of_m A)"
  let ?s = "1+card (atms_of_m A)"
  let ?\<mu> = "\<mu>\<^sub>C ?s ?b"
  assume ab: "(b, a) \<in> {(T, S). dpll_bj S T
    \<and> atms_of_m (clauses S) \<subseteq> atms_of_m A \<and> atm_of ` lits_of (trail S) \<subseteq> atms_of_m A
    \<and> no_dup (trail S) \<and> inv S}"

  have fin_A: "finite (atms_of_m A)"
    using fin by auto
  have
    dpll_bj: "dpll_bj a b" and
    N_A: "atms_of_m (clauses a) \<subseteq> atms_of_m A" and
    M_A: "atm_of ` lits_of (trail a) \<subseteq> atms_of_m A" and
    nd: "no_dup (trail a)" and
    inv: "inv a"
    using ab by auto

  have M'_A: "atm_of ` lits_of (trail b) \<subseteq> atms_of_m A"
    by (meson M_A N_A \<open>dpll_bj a b\<close> dpll_bj_atms_in_trail_in_set inv)
  have nd': "no_dup (trail b)"
    using \<open>dpll_bj a b\<close> dpll_bj_no_dup nd inv by blast
  { fix i :: nat and xs :: "'a list"
    have "i < length xs \<Longrightarrow> length xs - Suc i < length xs"
      by auto
    hence H: "i<length xs \<Longrightarrow>  xs ! i \<in> set xs"
      using rev_nth[of i xs] unfolding in_set_conv_nth by (force simp add: in_set_conv_nth)
  } note H = this

  have l_M_A: "length (trail a) \<le> card (atms_of_m A)"
    by (simp add: fin_A M_A card_mono no_dup_length_eq_card_atm_of_lits_of nd)
  have l_M'_A: "length (trail b) \<le> card (atms_of_m A)"
    by (simp add: fin_A M'_A card_mono no_dup_length_eq_card_atm_of_lits_of nd')
  have l_\<nu>_M: "length (\<nu> b) \<le> 1+card (atms_of_m A)"
     using l_M'_A length_get_all_marked_decomposition_length[of "trail b"] by auto
  have bounded_M: "\<forall>i<length (\<nu> b). (\<nu> b)! i < card (atms_of_m A) + 2"
    using length_in_get_all_marked_decomposition_bounded[of _ b] l_M'_A
    by (metis (no_types, lifting) Nat.le_trans One_nat_def Suc_1 add.right_neutral add_Suc_right
      le_imp_less_Suc less_eq_Suc_le nth_mem)

  from dpll_bj_trail_mes_increasing_prop[OF dpll_bj inv N_A M_A nd fin]
  have "\<mu>\<^sub>C ?s ?b (\<nu> a) < \<mu>\<^sub>C ?s ?b (\<nu> b)" by simp
  moreover from \<mu>\<^sub>C_bounded[OF bounded_M l_\<nu>_M]
    have "\<mu>\<^sub>C ?s ?b (\<nu> b) \<le> ?b ^ ?s" by auto
  ultimately show "?b ^ ?s \<le> ?b ^ ?s \<and>
           \<mu>\<^sub>C ?s ?b (\<nu> b) \<le> ?b ^ ?s \<and>
           \<mu>\<^sub>C ?s ?b (\<nu> a) < \<mu>\<^sub>C ?s ?b (\<nu> b)"
    by blast
qed

subsection \<open>Normal Forms\<close>

text \<open>
  We prove that given a normal form of DPLL, with some invariants, the either @{term N} is
  satisfiable and the built valuation @{term M} is a model; or @{term N} is unsatisfiable.

  Idea of the proof: We have to prove tat @{term "satisfiable N"}, @{term "\<not>M\<Turnstile>as N"}
     and there is no remaining step is incompatible.
     \<^enum> The @{term decide} rules tells us that every variable in @{term N} has a value.
     \<^enum> @{term "\<not>M\<Turnstile>as N"} tells us that there is conflict.
     \<^enum> There is at least one decision in the trail (otherwise, @{term M} is a model of @{term N}).
     \<^enum> Now if we build the clause with all the decision literals of the trail, we can apply the
     @{term backjump} rule.


  The assumption are saying that we have a finite upper bound @{term A} for the literals, that we
  cannot do any step @{term "no_step dpll_bj S"}\<close>
theorem dpll_backjump_normal_forms:
  fixes A :: "'v literal multiset set" and S T :: "'st"
  assumes
    "atms_of_m (clauses S) \<subseteq> atms_of_m A" and
    "atm_of ` lits_of (trail S) \<subseteq> atms_of_m A" and
    "no_dup (trail S)" and
    "finite A" and
    inv: "inv S" and
    n_s: "no_step dpll_bj S" and
    decomp: "all_decomposition_implies (clauses S) (get_all_marked_decomposition (trail S))"
  shows "unsatisfiable (clauses S) \<or> (trail S \<Turnstile>as clauses S \<and> satisfiable (clauses S))"
proof -
  let ?N = "clauses S"
  let ?M = "trail S"
  consider
      (sat) "satisfiable ?N" and "?M \<Turnstile>as ?N"
    | (sat') "satisfiable ?N" and "\<not> ?M \<Turnstile>as ?N"
    | (unsat) "unsatisfiable ?N"
    by auto
  thus ?thesis
    proof cases
      case sat' note sat = this(1) and M = this(2)
      obtain C where "C \<in> ?N" and "\<not>?M \<Turnstile>a C" using M unfolding true_annots_def by auto
      obtain I :: "'v literal set" where
        "I \<Turnstile>s ?N" and
        cons: "consistent_interp I" and
        tot: "total_over_m I ?N" and
        atm_I_N: "atm_of `I \<subseteq> atms_of_m ?N"
        using sat unfolding satisfiable_def_min by auto
      let ?I = "I \<union> {P| P. P \<in> lits_of ?M \<and> atm_of P \<notin> atm_of ` I}"
      let ?O = "{{#lit_of L#} |L. is_marked L \<and> L \<in> set ?M \<and> atm_of (lit_of L) \<notin> atms_of_m ?N}"
      have cons_I': "consistent_interp ?I"
        using cons using \<open>no_dup ?M\<close>  unfolding consistent_interp_def
        by (auto simp add: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set lits_of_def
          dest!: no_dup_cannot_not_lit_and_uminus)
      have tot_I': "total_over_m ?I (?N \<union> (\<lambda>a. {#lit_of a#}) ` set ?M)"
        using tot atms_of_s_def lits_of_def unfolding total_over_m_def total_over_set_def
        by fastforce
      have "{P |P. P \<in> lits_of ?M \<and> atm_of P \<notin> atm_of ` I} \<Turnstile>s ?O"
        using \<open>I\<Turnstile>s ?N\<close> atm_I_N by (auto simp add: atm_of_eq_atm_of true_clss_def lits_of_def)
      hence I'_N: "?I \<Turnstile>s ?N \<union> ?O"
        using \<open>I\<Turnstile>s ?N\<close> by auto
      have tot': "total_over_m ?I (?N\<union>?O)"
        using atm_I_N tot unfolding total_over_m_def total_over_set_def
        by (force simp: image_iff lits_of_def dest!: is_marked_ex_Marked)

      have atms_N_M: "atms_of_m ?N \<subseteq> atm_of ` lits_of ?M"
        proof (rule ccontr)
          assume "\<not> ?thesis"
          then obtain l :: 'v where
            l_N: "l \<in> atms_of_m ?N" and
            l_M: "l \<notin> atm_of ` lits_of ?M"
            by auto
          have "undefined_lit (Pos l) ?M"
            using l_M by (metis Marked_Propagated_in_iff_in_lits_of
              atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set literal.sel(1))
          from bj_decide[OF decide[OF this]] show False
            using l_N  n_s by auto
        qed

      have "?M \<Turnstile>as CNot C"
        by (metis atms_N_M \<open>C \<in> ?N\<close> \<open>\<not> ?M \<Turnstile>a C\<close> all_variables_defined_not_imply_cnot
          atms_of_atms_of_m_mono atms_of_m_CNot_atms_of atms_of_m_CNot_atms_of_m lits_of_def
          subsetCE)
      have "\<exists>l \<in> set ?M. is_marked l"
        proof (rule ccontr)
          let ?O = "{{#lit_of L#} |L. is_marked L \<and> L \<in> set ?M \<and> atm_of (lit_of L) \<notin> atms_of_m ?N}"
          have \<theta>[iff]: "\<And>I. total_over_m I (?N \<union> ?O \<union> (\<lambda>a. {#lit_of a#}) ` set ?M)
            \<longleftrightarrow> total_over_m I (?N \<union>(\<lambda>a. {#lit_of a#}) ` set ?M)"
            unfolding total_over_set_def total_over_m_def atms_of_m_def by auto
          assume "\<not> ?thesis"
          hence [simp]:"{{#lit_of L#} |L. is_marked L \<and> L \<in> set ?M}
            = {{#lit_of L#} |L. is_marked L \<and> L \<in> set ?M \<and> atm_of (lit_of L) \<notin> atms_of_m ?N}" by auto
          hence "?N \<union> ?O \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set ?M"
            using all_decomposition_implies_propagated_lits_are_implied[OF decomp] by auto

          hence "?I \<Turnstile>s (\<lambda>a. {#lit_of a#}) ` set ?M"
            using cons_I' I'_N tot_I' \<open>?I \<Turnstile>s ?N \<union> ?O\<close> unfolding \<theta> true_clss_clss_def by blast
          hence "lits_of ?M \<subseteq> ?I"
            unfolding true_clss_def lits_of_def by auto
          hence "?M \<Turnstile>as ?N"
            using I'_N `C \<in> ?N` `\<not> ?M \<Turnstile>a C` cons_I' atms_N_M
            by (meson `trail S \<Turnstile>as CNot C` consistent_CNot_not rev_subsetD sup_ge1 true_annot_def
              true_annots_def true_cls_mono_set_mset_l true_clss_def)
          thus False using M by fast
        qed
      from List.split_list_first_propE[OF this] obtain K :: "'v literal" and d :: 'lvl and
        F F' :: "('v, 'lvl, 'mark) marked_lit list" where
        M_K: "?M = F' @ Marked K d # F" and
        nm: "\<forall>f\<in>set F'. \<not>is_marked f"
        unfolding is_marked_def by metis
      let ?K = "Marked K d::('v, 'lvl, 'mark) marked_lit"
      have "?K \<in> set ?M"
        unfolding M_K by auto
      let ?C = "image_mset lit_of {#L\<in>#mset ?M. is_marked L \<and> L\<noteq>?K#} :: 'v literal multiset"
      let ?C' = "set_mset (image_mset (\<lambda>L::'v literal. {#L#}) (?C+{#lit_of ?K#}))"
      have "?N \<union> {{#lit_of L#} |L. is_marked L \<and> L \<in> set ?M} \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set ?M"
        using all_decomposition_implies_propagated_lits_are_implied[OF decomp] .
      moreover have C': "?C' = {{#lit_of L#} |L. is_marked L \<and> L \<in> set ?M}"
        unfolding M_K apply standard
          apply force
        using IntI by auto
      ultimately have N_C_M: "?N \<union> ?C' \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set ?M"
        by auto
      have N_M_False: "?N \<union> (\<lambda>L. {#lit_of L#}) ` (set ?M) \<Turnstile>ps {{#}}"
        using M \<open>?M \<Turnstile>as CNot C\<close> \<open>C\<in>?N\<close> unfolding true_clss_clss_def true_annots_def Ball_def
        true_annot_def by (metis consistent_CNot_not sup.orderE sup_commute true_clss_def
          true_clss_singleton_lit_of_implies_incl true_clss_union true_clss_union_increase)

      have "undefined_lit K F" using \<open>no_dup ?M\<close> unfolding M_K by (simp add: defined_lit_map)
      moreover
        have "?N \<union> ?C' \<Turnstile>ps {{#}}"
          proof -
            have A: "?N \<union> ?C' \<union> (\<lambda>a. {#lit_of a#}) ` set ?M  =
              ?N \<union> (\<lambda>a. {#lit_of a#}) ` set ?M"
              unfolding M_K by auto
            show ?thesis
              using true_clss_clss_left_right[OF N_C_M, of "{{#}}"] N_M_False unfolding A by auto
          qed
        have "?N \<Turnstile>p image_mset uminus ?C + {#-K#}"
          unfolding true_clss_cls_def true_clss_clss_def total_over_m_def
          proof (intro allI impI)
            fix I
            assume
              tot: "total_over_set I (atms_of_m (?N \<union> {image_mset uminus ?C+ {#- K#}}))" and
              cons: "consistent_interp I" and
              "I \<Turnstile>s ?N"
            have "(K \<in> I \<and> -K \<notin> I) \<or> (-K \<in> I \<and> K \<notin> I)"
              using cons tot unfolding consistent_interp_def by (cases K) auto
            have tot': "total_over_set I
               (atm_of ` lit_of ` (set ?M \<inter> {L. is_marked L \<and> L \<noteq> Marked K d}))"
              using tot by (auto simp add: atms_of_uminus_lit_atm_of_lit_of)
            { fix x :: "('v, 'lvl, 'mark) marked_lit"
              assume
                a3: "lit_of x \<notin> I" and
                a1: "x \<in> set ?M" and
                a4: "is_marked x" and
                a5: "x \<noteq> Marked K d"
              hence "Pos (atm_of (lit_of x)) \<in> I \<or> Neg (atm_of (lit_of x)) \<in> I"
                using a5 a4 tot' a1 unfolding total_over_set_def atms_of_s_def by blast
              moreover have f6: "Neg (atm_of (lit_of x)) = - Pos (atm_of (lit_of x))"
                by simp

              ultimately have "- lit_of x \<in> I"
                using f6 a3 by (metis (no_types) atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
                  literal.sel(1))
            } note H = this

            have "\<not>I \<Turnstile>s ?C'"
              using \<open>?N \<union> ?C' \<Turnstile>ps {{#}}\<close> tot cons \<open>I \<Turnstile>s ?N\<close>
              unfolding true_clss_clss_def total_over_m_def
              by (simp add: atms_of_uminus_lit_atm_of_lit_of atms_of_m_single_image_atm_of_lit_of)
            thus "I \<Turnstile> image_mset uminus ?C + {#- K#}"
              unfolding true_clss_def true_cls_def Bex_mset_def
              using \<open>(K \<in> I \<and> -K \<notin> I) \<or> (-K \<in> I \<and> K \<notin> I)\<close>
              by (auto dest!: H)
          qed
      moreover have "F \<Turnstile>as CNot (image_mset uminus ?C)"
        using nm unfolding true_annots_def CNot_def M_K by (auto simp add: lits_of_def)
      ultimately have False
        using bj_can_jump[of S F' K d F C "-K"
          "image_mset uminus (image_mset lit_of {# L :# mset ?M. is_marked L \<and> L \<noteq> Marked K d#})"]
          \<open>C\<in>?N\<close> n_s \<open>?M \<Turnstile>as CNot C\<close> bj_backjump inv unfolding M_K by (auto intro: bj_backjump)
        thus ?thesis by fast
    qed auto
qed

end

locale dpll_with_backjumping =
  dpll_with_backjumping_ops trail clauses update_trail add_cls remove_cls inv backjump
  for
    trail :: "'st \<Rightarrow> ('v, 'lvl, 'mark) annoted_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    update_trail :: "('v, 'lvl, 'mark) annoted_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    add_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    inv :: "'st \<Rightarrow> bool" and
    backjump  ::  "'st \<Rightarrow> 'st \<Rightarrow> bool"
  +
  assumes dpll_bj_inv:"\<And>S T. dpll_bj S T \<Longrightarrow> inv S \<Longrightarrow> inv T"
begin

lemma rtranclp_dpll_bj_inv:
  assumes "dpll_bj\<^sup>*\<^sup>* S T" and "inv S"
  shows "inv T"
  using assms by (induction rule: rtranclp_induct)
    (auto simp add: dpll_bj_no_dup intro: dpll_bj_inv)

lemma rtranclp_dpll_bj_no_dup:
  assumes "dpll_bj\<^sup>*\<^sup>* S T" and "inv S"
  and "no_dup (trail S)"
  shows "no_dup (trail T)"
  using assms by (induction rule: rtranclp_induct)
  (auto simp add: dpll_bj_no_dup dest: rtranclp_dpll_bj_inv dpll_bj_inv)

lemma rtranclp_dpll_bj_atms_of_m_clauses_inv:
  assumes
    "dpll_bj\<^sup>*\<^sup>* S T" and "inv S"
  shows "atms_of_m (clauses S) = atms_of_m (clauses T)"
  using assms by (induction rule: rtranclp_induct)
    (auto dest: rtranclp_dpll_bj_inv dpll_bj_atms_of_m_clauses_inv)

lemma rtranclp_dpll_bj_atms_in_trail:
  assumes
    "dpll_bj\<^sup>*\<^sup>* S T" and
    "inv S" and
    "atm_of ` (lits_of (trail S)) \<subseteq> atms_of_m (clauses S)"
  shows "atm_of ` (lits_of (trail T)) \<subseteq> atms_of_m (clauses T)"
  using assms apply (induction rule: rtranclp_induct)
  using dpll_bj_atms_in_trail dpll_bj_atms_of_m_clauses_inv rtranclp_dpll_bj_inv by auto

lemma rtranclp_dpll_bj_sat_iff:
  assumes "dpll_bj\<^sup>*\<^sup>* S T" and "inv S"
  shows "I \<Turnstile>s clauses S \<longleftrightarrow> I \<Turnstile>s clauses T"
  using assms by (induction rule: rtranclp_induct)
    (auto intro!: dpll_bj_sat_iff simp: rtranclp_dpll_bj_inv)

lemma rtranclp_dpll_bj_atms_in_trail_in_set:
  assumes
    "dpll_bj\<^sup>*\<^sup>* S T" and
    "inv S"
    "atms_of_m (clauses S) \<subseteq> A" and
    "atm_of ` (lits_of (trail S)) \<subseteq> A"
  shows "atm_of ` (lits_of (trail T)) \<subseteq> A"
  using assms
    by (induction rule: rtranclp_induct)
       (auto dest: rtranclp_dpll_bj_inv
         simp add: dpll_bj_atms_in_trail_in_set rtranclp_dpll_bj_atms_of_m_clauses_inv
           rtranclp_dpll_bj_inv)

lemma rtranclp_dpll_bj_all_decomposition_implies_inv:
  assumes
    "dpll_bj\<^sup>*\<^sup>* S T" and
    "inv S"
    "all_decomposition_implies (clauses S) (get_all_marked_decomposition (trail S))"
  shows "all_decomposition_implies (clauses T) (get_all_marked_decomposition (trail T))"
  using assms by (induction rule: rtranclp_induct)
    (auto intro: dpll_bj_all_decomposition_implies_inv simp: rtranclp_dpll_bj_inv)

lemma rtranclp_dpll_bj_inv_incl_dpll_bj_inv_trancl:
  "{(T, S). dpll_bj\<^sup>+\<^sup>+ S T
    \<and> atms_of_m (clauses S) \<subseteq> atms_of_m A \<and> atm_of ` lits_of (trail S) \<subseteq> atms_of_m A
    \<and> no_dup (trail S) \<and> inv S}
     \<subseteq> {(T, S). dpll_bj S T \<and> atms_of_m (clauses S) \<subseteq> atms_of_m A
        \<and> atm_of ` lits_of (trail S) \<subseteq> atms_of_m A \<and> no_dup (trail S) \<and> inv S}\<^sup>+"
    (is "?A \<subseteq> ?B\<^sup>+")
proof standard
  fix x
  assume x_A: "x \<in> ?A"
  obtain S T::"'st" where
    x[simp]: "x = (T, S)" by (cases x) auto
  have
    "dpll_bj\<^sup>+\<^sup>+ S T" and
    "atms_of_m (clauses S) \<subseteq> atms_of_m A" and
    "atm_of ` lits_of (trail S) \<subseteq> atms_of_m A" and
    "no_dup (trail S)" and
     "inv S"
    using x_A by auto
  thus "x \<in> ?B\<^sup>+" unfolding x
    proof (induction rule: tranclp_induct)
      case base
      thus ?case by auto
    next
      case (step T U) note step = this(1) and ST = this(2) and IH = this(3)[OF this(4-7)]
        and N_A = this(4) and M_A = this(5) and nd = this(6) and inv = this(7)

      have [simp]: "atms_of_m (clauses S) = atms_of_m (clauses T)"
        using step rtranclp_dpll_bj_atms_of_m_clauses_inv tranclp_into_rtranclp inv by fastforce
      have "no_dup (trail T)"
        using local.step nd rtranclp_dpll_bj_no_dup tranclp_into_rtranclp inv by fastforce
      moreover have "atm_of ` (lits_of (trail T)) \<subseteq> atms_of_m A"
        by (metis inv M_A N_A local.step rtranclp_dpll_bj_atms_in_trail_in_set
          tranclp_into_rtranclp)
      moreover have "inv T"
         using inv local.step rtranclp_dpll_bj_inv tranclp_into_rtranclp by fastforce
      ultimately have "(U, T) \<in> ?B" using ST N_A M_A inv by auto
      thus ?case using IH by (rule trancl_into_trancl2)
    qed
qed

lemma tranclp_dpll_bj_wf:
  assumes fin: "finite A"
  shows "wf {(T, S). dpll_bj\<^sup>+\<^sup>+ S T
    \<and> atms_of_m (clauses S) \<subseteq> atms_of_m A \<and> atm_of ` lits_of (trail S) \<subseteq> atms_of_m A
    \<and> no_dup (trail S) \<and> inv S}"
  using wf_trancl[OF dpll_bj_wf[OF fin]] rtranclp_dpll_bj_inv_incl_dpll_bj_inv_trancl
  by (rule wf_subset)

lemma dpll_bj_sat_ext_iff:
  "dpll_bj S T \<Longrightarrow> inv S \<Longrightarrow> I\<Turnstile>sext clauses S \<longleftrightarrow> I\<Turnstile>sext clauses T"
  by (simp add: dpll_bj_atms_of_m_clauses_inv dpll_bj_sat_iff total_over_m_def true_clss_ext_def)

lemma rtranclp_dpll_bj_sat_ext_iff:
  "dpll_bj\<^sup>*\<^sup>* S T \<Longrightarrow> inv S \<Longrightarrow> I\<Turnstile>sext clauses S \<longleftrightarrow> I\<Turnstile>sext clauses T"
  by (induction rule: rtranclp_induct) (simp_all add: rtranclp_dpll_bj_inv dpll_bj_sat_ext_iff)

theorem full0_dpll_backjump_normal_forms:
  fixes A :: "'v literal multiset set" and S T :: "'st"
  assumes
    full: "full0 dpll_bj S T" and
    atms_S: "atms_of_m (clauses S) \<subseteq> atms_of_m A" and
    atms_trail: "atm_of ` lits_of (trail S) \<subseteq> atms_of_m A" and
    n_d: "no_dup (trail S)" and
    "finite A" and
    inv: "inv S" and
    decomp: "all_decomposition_implies (clauses S) (get_all_marked_decomposition (trail S))"
  shows "unsatisfiable (clauses S) \<or> (trail T \<Turnstile>as clauses S \<and> satisfiable (clauses S))"
proof -
  have st: "dpll_bj\<^sup>*\<^sup>* S T" and "no_step dpll_bj T"
    using full unfolding full0_def by fast+
  moreover have "atms_of_m (clauses T) \<subseteq> atms_of_m A"
    using atms_S inv rtranclp_dpll_bj_atms_of_m_clauses_inv st by blast
  moreover have "atm_of ` lits_of (trail T) \<subseteq> atms_of_m A"
     using atms_S atms_trail inv rtranclp_dpll_bj_atms_in_trail_in_set st by auto
  moreover have "no_dup (trail T)"
    using n_d inv rtranclp_dpll_bj_no_dup st by blast
  moreover have inv: "inv T"
    using inv rtranclp_dpll_bj_inv st by blast
  moreover
    have decomp: "all_decomposition_implies (clauses T) (get_all_marked_decomposition (trail T))"
      using \<open>inv S\<close> decomp rtranclp_dpll_bj_all_decomposition_implies_inv st by blast
  ultimately have "unsatisfiable (clauses T) \<or> (trail T \<Turnstile>as clauses T \<and> satisfiable (clauses T))"
    using \<open>finite A\<close> dpll_backjump_normal_forms by force
  thus ?thesis
    by (meson \<open>inv S\<close> rtranclp_dpll_bj_sat_iff satisfiable_carac st true_annots_true_cls)
qed

lemma dpll_bj_trail_mes_decreasing_prop:
  assumes dpll: "dpll_bj S T"  and inv: "inv S" and
  N_A: "atms_of_m (clauses S) \<subseteq> atms_of_m A" and
  M_A: "atm_of ` lits_of (trail S) \<subseteq> atms_of_m A" and
  nd: "no_dup (trail S)" and
  fin_A: "finite A"
  shows "(2+card (atms_of_m A)) ^ (1+card (atms_of_m A))
               - \<mu>\<^sub>C (1+card (atms_of_m A)) (2+card (atms_of_m A)) (\<nu> T)
            < (2+card (atms_of_m A)) ^ (1+card (atms_of_m A))
               - \<mu>\<^sub>C (1+card (atms_of_m A)) (2+card (atms_of_m A)) (\<nu> S)"
  using dpll_bj_trail_mes_increasing_prop[OF assms] \<mu>\<^sub>C_bounded
proof -
  let ?b = "2+card (atms_of_m A)"
  let ?s = "1+card (atms_of_m A)"
  let ?\<mu> = "\<mu>\<^sub>C ?s ?b"
  have M'_A: "atm_of ` lits_of (trail T) \<subseteq> atms_of_m A"
    by (meson M_A N_A dpll dpll_bj_atms_in_trail_in_set inv)
  have nd': "no_dup (trail T)"
    using \<open>dpll_bj S T\<close> dpll_bj_no_dup nd inv by blast
  { fix i :: nat and xs :: "'a list"
    have "i < length xs \<Longrightarrow> length xs - Suc i < length xs"
      by auto
    hence H: "i<length xs \<Longrightarrow>  xs ! i \<in> set xs"
      using rev_nth[of i xs] unfolding in_set_conv_nth by (force simp add: in_set_conv_nth)
  } note H = this

  have l_M_A: "length (trail S) \<le> card (atms_of_m A)"
    by (simp add: fin_A M_A card_mono no_dup_length_eq_card_atm_of_lits_of nd)
  have l_M'_A: "length (trail T) \<le> card (atms_of_m A)"
    by (simp add: fin_A M'_A card_mono no_dup_length_eq_card_atm_of_lits_of nd')
  have l_\<nu>_M: "length (\<nu> T) \<le> 1+card (atms_of_m A)"
     using l_M'_A length_get_all_marked_decomposition_length[of "trail T"] by auto
  have bounded_M: "\<forall>i<length (\<nu> T). (\<nu> T)! i < card (atms_of_m A) + 2"
    using length_in_get_all_marked_decomposition_bounded[of _ T] l_M'_A
    by (metis (no_types, lifting) Nat.le_trans One_nat_def Suc_1 add.right_neutral add_Suc_right
      le_imp_less_Suc less_eq_Suc_le nth_mem)

  from dpll_bj_trail_mes_increasing_prop[OF dpll inv N_A M_A nd fin_A]
  have "\<mu>\<^sub>C ?s ?b (\<nu> S) < \<mu>\<^sub>C ?s ?b (\<nu> T)" by simp
  moreover from \<mu>\<^sub>C_bounded[OF bounded_M l_\<nu>_M]
    have "\<mu>\<^sub>C ?s ?b (\<nu> T) \<le> ?b ^ ?s" by auto
  ultimately show ?thesis by linarith
qed
end

section \<open>CDCL\<close>
locale learn_ops =
  dpll_state trail clauses update_trail add_cls remove_cls
  for
    trail :: "'st \<Rightarrow> ('v, 'lvl, 'mark) annoted_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    update_trail :: "('v, 'lvl, 'mark) annoted_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    add_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" +
  fixes
    learn_cond :: "'v clause \<Rightarrow> 'st \<Rightarrow> bool"

begin
inductive learn :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
"clauses S \<Turnstile>p C \<Longrightarrow> atms_of C \<subseteq> atms_of_m (clauses S) \<union> atm_of ` (lits_of (trail S))
  \<Longrightarrow> learn_cond C S
  \<Longrightarrow> learn S (add_cls C S)"
inductive_cases learnE: "learn S T"
end

locale forget_ops =
  dpll_state trail clauses update_trail add_cls remove_cls
  for
    trail :: "'st \<Rightarrow> ('v, 'lvl, 'mark) annoted_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    update_trail :: "('v, 'lvl, 'mark) annoted_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    add_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" +
  fixes
    forget_cond :: "'v clause \<Rightarrow> 'st \<Rightarrow> bool"
begin
inductive forget :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
"clauses S - {C} \<Turnstile>p C \<Longrightarrow> forget_cond C S \<Longrightarrow> C \<in> clauses S \<Longrightarrow>
    forget S (remove_cls C S)"
inductive_cases forgetE: "forget S T"
end

locale learn_and_forget =
  learn_ops trail clauses update_trail add_cls remove_cls learn_cond +
  forget_ops trail clauses update_trail add_cls remove_cls forget_cond
  for
    trail :: "'st \<Rightarrow> ('v, 'lvl, 'mark) annoted_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    update_trail :: "('v, 'lvl, 'mark) annoted_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    add_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    learn_cond forget_cond :: "'v clause \<Rightarrow> 'st \<Rightarrow> bool"
begin
inductive learn_and_forget :: "'st \<Rightarrow> 'st \<Rightarrow> bool"
where
lf_learn: "learn S T \<Longrightarrow> learn_and_forget S T" |
lf_forget: "forget S T \<Longrightarrow> learn_and_forget S T"
end

locale conflict_driven_clause_learning_ops =
  dpll_with_backjumping trail clauses update_trail add_cls remove_cls inv backjump +
  learn_and_forget trail clauses update_trail add_cls remove_cls learn_cond forget_cond
    for
      trail :: "'st \<Rightarrow> ('v, 'lvl, 'mark) annoted_lits" and
      clauses :: "'st \<Rightarrow> 'v clauses" and
      update_trail :: "('v, 'lvl, 'mark) annoted_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
      add_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
      remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
      inv :: "'st \<Rightarrow> bool" and
      backjump ::  "'st \<Rightarrow> 'st \<Rightarrow> bool" and
      learn_cond forget_cond :: "'v clause \<Rightarrow> 'st \<Rightarrow> bool"
begin

inductive cdcl:: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
c_dpll_bj:  "dpll_bj S S' \<Longrightarrow> cdcl S S'" |
c_learn:  "learn S S' \<Longrightarrow> cdcl S S'" |
c_forget:  "forget S S' \<Longrightarrow> cdcl S S'"

lemma cdcl_all_induct[consumes 1, case_names dpll_bj learn forget]:
  fixes S T :: "'st"
  assumes "cdcl S T" and
    dpll: "\<And>S T. dpll_bj S T \<Longrightarrow> P S T" and
    learning:
      "\<And>S C. clauses S \<Turnstile>p C \<Longrightarrow> atms_of C \<subseteq> atms_of_m (clauses S) \<union> atm_of ` (lits_of (trail S))
      \<Longrightarrow>  P S (add_cls C S)" and
    forgetting: "\<And>S C. clauses S - {C} \<Turnstile>p C \<Longrightarrow> C \<in> clauses S \<Longrightarrow> P S (remove_cls C S)"
  shows "P S T"
  using assms(1) by (induction rule: cdcl.induct) (auto elim!: learnE forgetE dest: assms(2,3,4))

lemma cdcl_no_dup:
  assumes "cdcl S T" and "inv S"
  and "no_dup (trail S)"
  shows "no_dup (trail T)"
  using assms by (induction rule: cdcl_all_induct) (auto intro: dpll_bj_no_dup)

paragraph \<open>Consistency of the trail\<close>
lemma cdcl_consistent:
  assumes "cdcl S T" and "inv S"
  and "no_dup (trail S)"
  shows "consistent_interp (lits_of (trail T))"
  using cdcl_no_dup[OF assms] distinctconsistent_interp by fast

text \<open>The subtle problem here is that tautologies can be removed, meaning that some variable can
  disappear of the problem. It is also possible that some variable of the trail are not in the
  clauses anymore.\<close>
lemma cdcl_atms_of_m_clauses_decreasing:
  assumes "cdcl S T"and "inv S"
  shows "atms_of_m (clauses T) \<subseteq> atms_of_m (clauses S) \<union> atm_of ` (lits_of (trail S))"
  using assms by (induction rule: cdcl_all_induct)
    (auto dest!: dpll_bj_atms_of_m_clauses_inv set_mp simp add: atms_of_m_def Union_eq)

lemma cdcl_atms_in_trail:
  assumes "cdcl S T"and "inv S"
  and "atm_of ` (lits_of (trail S)) \<subseteq> atms_of_m (clauses S)"
  shows "atm_of ` (lits_of (trail T)) \<subseteq> atms_of_m (clauses S)"
  using assms by (induction rule: cdcl_all_induct) (auto simp add: dpll_bj_atms_in_trail)

lemma cdcl_atms_in_trail_in_set:
  assumes
    "cdcl S T" and "inv S" and
    "atms_of_m (clauses S) \<subseteq> A" and
    "atm_of ` (lits_of (trail S)) \<subseteq> A"
  shows "atm_of ` (lits_of (trail T)) \<subseteq> A"
  using assms
  by (induction rule: cdcl_all_induct)
     (simp_all add: dpll_bj_atms_in_trail_in_set dpll_bj_atms_of_m_clauses_inv)

lemma cdcl_finite_clauses:
  assumes
    "cdcl S T" and "inv S" and
    "finite(clauses S)"
  shows "finite(clauses T)"
  using assms
  by (induction rule: cdcl_all_induct)
     (simp_all add: dpll_bj_atms_in_trail_in_set dpll_bj_atms_of_m_clauses_inv dpll_bj_clauses)

paragraph \<open>Extension of models\<close>
lemma cdcl_bj_sat_ext_iff:
  assumes "cdcl S T"and "inv S"
  shows "I\<Turnstile>sext clauses S \<longleftrightarrow> I\<Turnstile>sext clauses T"
  using assms
proof (induction rule:cdcl_all_induct)
  case (dpll_bj)
  thus ?case by (rule dpll_bj_sat_ext_iff)
next
  case (learn S C)
  { fix J
    assume
      "I \<Turnstile>sext clauses S" and
      "I \<subseteq> J" and
      tot: "total_over_m J (insert C (clauses S))" and
      cons: "consistent_interp J"
    hence "J \<Turnstile>s clauses S" unfolding true_clss_ext_def by auto

    moreover
      with \<open>clauses S\<Turnstile>p C\<close> have "J \<Turnstile> C"
        using tot cons unfolding true_clss_cls_def by auto
    ultimately have "J \<Turnstile>s insert C (clauses S)" by auto
  }
  hence H: "I \<Turnstile>sext (clauses S) \<Longrightarrow> I \<Turnstile>sext insert C (clauses S)"  unfolding true_clss_ext_def by auto
  show ?case
    apply standard
      apply (simp add: H)
    by (metis Diff_insert_absorb clauses_add_clause insert_absorb
      true_clss_ext_decrease_right_remove_r)
next
  case (forget S C)
  { fix J
    assume
      "I \<Turnstile>sext clauses S - {C}" and
      "I \<subseteq> J" and
      tot: "total_over_m J (clauses S)" and
      cons: "consistent_interp J"
    hence "J \<Turnstile>s (clauses S) - {C}"
      unfolding true_clss_ext_def by (meson Diff_subset total_over_m_subset)

    moreover
      with \<open>(clauses S) - {C} \<Turnstile>p C\<close> have "J \<Turnstile> C"
        using tot cons unfolding true_clss_cls_def
      by (metis Un_empty_right Un_insert_right \<open>C\<in>(clauses S)\<close> insert_Diff)
    ultimately have "J \<Turnstile>s (clauses S)" by (metis insert_Diff_single true_clss_insert)
  }
  hence H: "I \<Turnstile>sext (clauses S) - {C} \<Longrightarrow> I \<Turnstile>sext (clauses S)" unfolding true_clss_ext_def by blast
  show ?case
    by standard (simp_all add: true_clss_ext_decrease_right_remove_r H)
qed

end -- \<open>end of \<open>conflict_driven_clause_learning_ops\<close>\<close>

subsection \<open>Restricting restarts\<close>
locale conflict_driven_clause_learning =
  conflict_driven_clause_learning_ops +
  assumes cdcl_inv: "\<And>S T. cdcl S T \<Longrightarrow> inv S \<Longrightarrow> inv T"
begin
lemma rtranclp_cdcl_inv:
  "cdcl\<^sup>*\<^sup>* S T \<Longrightarrow> inv S \<Longrightarrow> inv T"
  by (induction rule: rtranclp.induct) (auto simp add: cdcl_inv)

lemma rtranclp_cdcl_trail_clauses_bound:
  assumes
    "cdcl\<^sup>*\<^sup>* S T" and
    "inv S" and
    "atms_of_m (clauses S) \<subseteq> A" and
    "atm_of `(lits_of (trail S)) \<subseteq> A"
  shows "atm_of `(lits_of (trail T)) \<subseteq> A \<and> atms_of_m (clauses T) \<subseteq>  A"
  using assms
proof (induction rule: rtranclp_induct)
  case base
  thus ?case by simp
next
  case (step T U) note st =this(1) and cdcl = this(2) and IH = this(3)[OF this(4-6)] and
    inv = this(4) and atms_clauses_S = this(5) and atms_trail_S = this(6)
  have "inv T" using inv st rtranclp_cdcl_inv by blast
  hence "atms_of_m (clauses U) \<subseteq> A"
    using cdcl_atms_of_m_clauses_decreasing[OF cdcl] IH by auto
  moreover have "atm_of `(lits_of (trail U)) \<subseteq> A"
    by (meson IH \<open>inv T\<close> cdcl cdcl_atms_in_trail_in_set)
  ultimately show ?case by fast
qed

lemma rtranclp_cdcl_no_dup:
  assumes "cdcl\<^sup>*\<^sup>* S T" and "inv S"
  and "no_dup (trail S)"
  shows "no_dup (trail T)"
  using assms by (induction rule: rtranclp_induct) (auto intro: cdcl_no_dup rtranclp_cdcl_inv)

lemma rtranclp_cdcl_finite_clauses:
  assumes
    "cdcl\<^sup>*\<^sup>* S T" and "inv S" and
    "finite(clauses S)"
  shows "finite(clauses T)"
  using assms
  by (induction rule: rtranclp_induct) (auto intro: cdcl_finite_clauses rtranclp_cdcl_inv)
end

locale conflict_driven_clause_learning_learning_before_backjump_only_distinct_learnt =
  conflict_driven_clause_learning trail clauses update_trail add_cls remove_cls inv backjump
  "\<lambda>C S.  distinct_mset C \<and> \<not>tautology C \<and> learn_restrictions C S \<and>
    (\<exists>F K d F' C' L.  trail S = F' @ Marked K d # F \<and> C = C' + {#L#} \<and> F \<Turnstile>as CNot C'
      \<and> C' + {#L#} \<notin> clauses S)"
  "\<lambda>C S. \<not>(\<exists>F' F K d L. trail S = F' @ Marked K d # F \<and> F \<Turnstile>as CNot (C - {#L#}))
    \<and> forget_restrictions C S"
    for
      trail :: "'st \<Rightarrow> ('v::linorder, 'lvl, 'mark) annoted_lits" and
      clauses :: "'st \<Rightarrow> 'v clauses" and
      update_trail :: "('v, 'lvl, 'mark) annoted_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
      add_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
      remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
      inv :: "'st \<Rightarrow> bool" and
      backjump :: "'st \<Rightarrow> 'st \<Rightarrow> bool" and
      learn_restrictions forget_restrictions :: "'v clause \<Rightarrow> 'st \<Rightarrow> bool"
begin

lemma cdcl_learn_all_induct[consumes 1, case_names dpll_bj learn forget]:
  fixes S T :: "'st"
  assumes "cdcl S T" and
    dpll: "\<And>S T. dpll_bj S T \<Longrightarrow> P S T" and
    learning:
      "\<And>S C F K d F' C' L. clauses S \<Turnstile>p C \<Longrightarrow> atms_of C \<subseteq> atms_of_m (clauses S) \<union> atm_of ` (lits_of (trail S))
      \<Longrightarrow>  distinct_mset C \<Longrightarrow> \<not> tautology C \<Longrightarrow> learn_restrictions C S \<Longrightarrow>
      trail S = F' @ Marked K d # F \<Longrightarrow> C = C' + {#L#} \<Longrightarrow> F \<Turnstile>as CNot C' \<Longrightarrow>
      C' + {#L#} \<notin> clauses S \<Longrightarrow> P S (add_cls C S)" and
    forgetting: "\<And>S C. clauses S - {C} \<Turnstile>p C \<Longrightarrow> C \<in> clauses S
    \<Longrightarrow> \<not>(\<exists>F' F K d L. trail S = F' @ Marked K d # F \<and> F \<Turnstile>as CNot (C - {#L#}))
    \<Longrightarrow> forget_restrictions C S \<Longrightarrow> P S (remove_cls C S)"
  shows "P S T"
  using assms(1)
  apply (induction rule: cdcl.induct)
  apply (auto dest: assms(2) simp add: learn_ops_axioms)[]
  apply (auto elim!: learn_ops.learn.cases[OF learn_ops_axioms] dest: assms(3))[]
  apply (auto elim!: forget_ops.forget.cases[OF forget_ops_axioms] dest!: assms(4))
  done
lemma rtranclp_cdcl_inv:
  "cdcl\<^sup>*\<^sup>* S T \<Longrightarrow> inv S \<Longrightarrow> inv T"
  apply (induction rule: rtranclp_induct)
   apply simp
  using cdcl_inv   unfolding conflict_driven_clause_learning_def
  conflict_driven_clause_learning_axioms_def by blast

lemma learn_always_simple_clauses:
  assumes
    learn: "learn S T" and
    n_d: "no_dup (trail S)" and
    fin: "finite (clauses S)"
  shows "clauses T - clauses S
    \<subseteq> build_all_simple_clss (atms_of_m (clauses S) \<union> atm_of ` lits_of (trail S))"
proof
  fix C assume C: "C \<in>  clauses T - clauses S"
  have "distinct_mset C" "\<not>tautology C" using learn C by induction auto
  hence "C \<in> build_all_simple_clss (atms_of C)"
    using distinct_mset_not_tautology_implies_in_build_all_simple_clss by blast
  moreover have "atms_of C \<subseteq> atms_of_m (clauses S) \<union> atm_of ` lits_of (trail S)"
    using learn C by (force simp add: atms_of_m_def atms_of_def image_Un lits_of_def
      true_annots_CNot_all_atms_defined elim!: learnE)
  moreover have "finite (atms_of_m (clauses S) \<union> atm_of ` lits_of (trail S))"
    using fin unfolding lits_of_def by auto
  ultimately show "C \<in> build_all_simple_clss (atms_of_m (clauses S) \<union> atm_of ` lits_of (trail S))"
    using build_all_simple_clss_mono  by (metis (no_types) insert_subset mk_disjoint_insert)
qed

definition "conflicting_bj_clss S \<equiv>
   {C+{#L#}|C L. C+{#L#} \<in> clauses S \<and> distinct_mset (C+{#L#}) \<and> \<not>tautology (C+{#L#})
     \<and> (\<exists>F' K d F. trail S = F' @ Marked K d # F \<and> F \<Turnstile>as CNot C)}"

lemma conflicting_bj_clss_remove_cls[simp]:
  "conflicting_bj_clss (remove_cls C S) = conflicting_bj_clss S - {C}"
  unfolding conflicting_bj_clss_def by fastforce

lemma conflicting_bj_clss_add_cls:
  "conflicting_bj_clss (add_cls C' S)
    = conflicting_bj_clss S
      \<union> (if \<exists>C L. C' = C +{#L#}\<and> distinct_mset (C+{#L#}) \<and> \<not>tautology (C+{#L#})
     \<and> (\<exists>F' K d F. trail S = F' @ Marked K d # F \<and> F \<Turnstile>as CNot C)
     then {C'} else {})"
  unfolding conflicting_bj_clss_def apply (auto split: split_if_asm) by metis+

lemma conflicting_bj_clss_incl_clauses:
   "conflicting_bj_clss S \<subseteq> clauses S"
  unfolding conflicting_bj_clss_def by auto

lemma finite_conflicting_bj_clss[simp]:
  "finite (clauses S) \<Longrightarrow> finite (conflicting_bj_clss S)"
  using conflicting_bj_clss_incl_clauses[of S] rev_finite_subset by blast

abbreviation "conflicting_bj_clss_yet b S \<equiv>
  3 ^ b - card (conflicting_bj_clss S)"
abbreviation   \<mu>\<^sub>L :: "nat \<Rightarrow> 'st \<Rightarrow> nat \<times> nat" where
  "\<mu>\<^sub>L b S \<equiv> (conflicting_bj_clss_yet b S, card (clauses S))"

lemma do_not_forget_before_backtracking_clause_learned_clause_untouched:
  assumes "forget S T"
  shows "conflicting_bj_clss S = conflicting_bj_clss T"
  using assms apply induction
  unfolding conflicting_bj_clss_def
  by (metis (mono_tags, hide_lams) Diff_iff diff_union_cancelR dpll_state.clause_remove_clause
    dpll_state_axioms equals0D insertE update_trail_remove_clauses)

lemma forget_\<mu>\<^sub>L_decrease:
  assumes forget: "forget S T" and
   fin: "finite (clauses S)"
  shows "(\<mu>\<^sub>L b T, \<mu>\<^sub>L b S) \<in> less_than <*lex*> less_than"
proof -
  have "card (clauses T) < card (clauses S)"
    using forget fin apply (induction)
    using card_Suc_Diff1 by fastforce
  then show ?thesis
    unfolding do_not_forget_before_backtracking_clause_learned_clause_untouched[OF forget]
    by auto
qed

lemma set_condition_or_split:"{a. (a = b \<or> Q a) \<and> S a} = (if S b then {b} else {}) \<union> {a. Q a \<and> S a}"
  by auto

lemma set_insert_neq:
  "A \<noteq> insert a A \<longleftrightarrow> a \<notin> A"
  by auto
lemma learn_\<mu>\<^sub>L_decrease:
  assumes learnST: "learn S T" and
   fin: "finite (clauses S)" and
   A: "atms_of_m (clauses S) \<union> atm_of ` lits_of (trail S) \<subseteq> A" and
   fin_A: "finite A"
  shows "(\<mu>\<^sub>L (card A) T, \<mu>\<^sub>L (card A) S) \<in> less_than <*lex*> less_than"
proof -
  have [simp]: "(atms_of_m (clauses T) \<union> atm_of ` lits_of (trail T))
    = (atms_of_m (clauses S) \<union> atm_of ` lits_of (trail S))"
    using learnST fin by induction auto

  then have "card (atms_of_m (clauses T) \<union> atm_of ` lits_of (trail T))
    = card (atms_of_m (clauses S) \<union> atm_of ` lits_of (trail S))"
    using fin by (auto intro!: card_mono)
  hence 3: "(3::nat) ^ card (atms_of_m (clauses T) \<union> atm_of ` lits_of (trail T))
    = 3 ^ card (atms_of_m (clauses S) \<union> atm_of ` lits_of (trail S))"
    by (auto intro: power_mono)
  moreover have "conflicting_bj_clss S \<subseteq> conflicting_bj_clss T"
    using learnST by induction (auto simp add: conflicting_bj_clss_add_cls)
  moreover have "conflicting_bj_clss S \<noteq> conflicting_bj_clss T"
    using learnST apply induction
    apply (auto simp add: set_condition_or_split set_insert_neq conflicting_bj_clss_add_cls)
    apply (fastforce simp add: conflicting_bj_clss_def)+
    done
  moreover have fin_T: "finite (conflicting_bj_clss T)"
    using learnST fin by induction (auto simp add: conflicting_bj_clss_add_cls )
  ultimately have "card (conflicting_bj_clss T) \<ge> card (conflicting_bj_clss S)"
    using card_mono by blast

  moreover
    have fin': "finite (atms_of_m (clauses T) \<union> atm_of ` lits_of (trail T))"
      using fin by auto
    have 1:"atms_of_m (conflicting_bj_clss T) \<subseteq> atms_of_m (clauses T)"
      unfolding conflicting_bj_clss_def atms_of_m_def by auto
    have 2: "\<And>x. x\<in> conflicting_bj_clss T \<Longrightarrow> \<not> tautology x \<and> distinct_mset x"
      unfolding conflicting_bj_clss_def by auto
    have T: "conflicting_bj_clss T
    \<subseteq> build_all_simple_clss (atms_of_m (clauses T) \<union> atm_of ` lits_of (trail T))"
      by standard (meson "1" "2" fin'  `finite (conflicting_bj_clss T)` build_all_simple_clss_mono
        distinct_mset_set_def  simplified_in_build_all subsetCE sup.coboundedI1)
  moreover
    hence #: "3 ^ card (atms_of_m (clauses T) \<union> atm_of ` lits_of (trail T))
        \<ge> card (conflicting_bj_clss T)"
      by (meson Nat.le_trans build_all_simple_clss_card build_all_simple_clss_finite card_mono fin')
    have "atms_of_m (clauses T) \<union> atm_of ` lits_of (trail T) \<subseteq> A"
      using learnE[OF learnST] A by simp
    hence "3 ^ (card A) \<ge> card (conflicting_bj_clss T)"
      using # fin_A by (meson build_all_simple_clss_card build_all_simple_clss_finite
        build_all_simple_clss_mono calculation(2) card_mono dual_order.trans)
  ultimately show ?thesis
    using psubset_card_mono[OF fin_T ]
    unfolding less_than_iff lex_prod_def by clarify
      (meson `conflicting_bj_clss S \<noteq> conflicting_bj_clss T`
        `conflicting_bj_clss S \<subseteq> conflicting_bj_clss T`
        diff_less_mono2 le_less_trans not_le psubsetI)
qed

text \<open>We have to assume the following:
  \<^item> @{term "inv S"}: the invariant holds in the inital state.
  \<^item> @{term A} is a (finite @{term "finite A"}) superset of the literals in the trail
  @{term "atm_of ` lits_of (trail S) \<subseteq> atms_of_m A"}
  and in the clauses @{term "atms_of_m (clauses S) \<subseteq> atms_of_m A"}. This can the the set of all the
  literals in the starting set of clauses.
  \<^item> @{term "no_dup (trail S)"}: no duplicate in the trail. This is invariant along the path.
  \<^item> there is a finite amount of clauses @{term "finite(clauses S)"} (each clause being finite by
  definition of multisets)\<close>
definition \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L where
"\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L A T \<equiv> ((2+card (atms_of_m A)) ^ (1+card (atms_of_m A))
               - \<mu>\<^sub>C (1+card (atms_of_m A)) (2+card (atms_of_m A)) (\<nu> T),
            conflicting_bj_clss_yet (card (atms_of_m A)) T, card (clauses T))"
lemma cdcl_decreasing_measure:
  assumes "cdcl S T"  and "inv S"
  "atms_of_m (clauses S) \<subseteq> atms_of_m A" and
  "atm_of ` lits_of (trail S) \<subseteq> atms_of_m A" and
  "no_dup (trail S)" and
  fin_S: "finite(clauses S)" and
  fin_A: "finite A"
  shows "(\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L A T, \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L A S)
            \<in> less_than <*lex*> (less_than <*lex*> less_than)"
  using assms(1-6)
proof (induction)
  case (c_dpll_bj S T)
  from dpll_bj_trail_mes_decreasing_prop[OF this(1-5) fin_A] show ?case unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L_def
    by (meson in_lex_prod less_than_iff)
next
  case (c_learn S T) note learn = this(1) and inv = this(2) and N_A = this(3) and M_A = this(4) and
    n_d = this(5) and fin = this(6)
  hence S: "trail S =  trail T"
    by (induction rule: learn.induct) auto
  show ?case
    using learn_\<mu>\<^sub>L_decrease[OF learn fin _ ] N_A M_A fin_A unfolding S \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L_def by auto
next
  case (c_forget S T) note forget = this(1) and fin = this(6)
  have "trail S = trail T" using forget by induction auto
  thus ?case
    using forget_\<mu>\<^sub>L_decrease[OF forget fin] unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L_def by auto
qed

lemma cdcl_restricted_learning_wf:
  assumes "finite A"
  shows "wf {(T, S).
    (atms_of_m (clauses S) \<subseteq> atms_of_m A \<and> atm_of ` lits_of (trail S) \<subseteq> atms_of_m A
    \<and> no_dup (trail S)
    \<and> finite (clauses S) \<and> inv S)
    \<and> cdcl S T }"
  by (rule wf_wf_if_measure'[of "less_than <*lex*> (less_than <*lex*> less_than)"])
     (auto intro: cdcl_decreasing_measure[OF _ _ _ _ _ _ assms])

definition \<mu>\<^sub>C' :: "'a literal multiset set \<Rightarrow> 'st \<Rightarrow> nat" where
"\<mu>\<^sub>C' A T \<equiv> \<mu>\<^sub>C (1+card (atms_of_m A)) (2+card (atms_of_m A)) (\<nu> T)"

definition \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' :: "'a literal multiset set \<Rightarrow> 'st \<Rightarrow> nat" where
"\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' A T \<equiv>
  ((2+card (atms_of_m A)) ^ (1+card (atms_of_m A)) - \<mu>\<^sub>C' A T) * (1+ 3^card (atms_of_m A)) * 2
  + conflicting_bj_clss_yet (card (atms_of_m A)) T * 2
  + card (clauses T)"

lemma cdcl_decreasing_measure':
  assumes
    "cdcl S T" and
    "inv S"
    "atms_of_m (clauses S) \<subseteq> atms_of_m A"
    "atm_of ` lits_of (trail S) \<subseteq> atms_of_m A" and
    "no_dup (trail S)" and
    "finite (clauses S)" and
    fin_A: "finite A"
  shows "\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' A T < \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' A S"
  using assms(1-6)
proof (induction rule: cdcl_learn_all_induct)
  case (dpll_bj S T)
  hence "(2+card (atms_of_m A)) ^ (1+card (atms_of_m A)) - \<mu>\<^sub>C' A T
    < (2+card (atms_of_m A)) ^ (1+card (atms_of_m A)) - \<mu>\<^sub>C' A S"
    using dpll_bj_trail_mes_decreasing_prop fin_A unfolding \<mu>\<^sub>C'_def by blast
  hence "(2+card (atms_of_m A)) ^ (1+card (atms_of_m A)) - \<mu>\<^sub>C' A T + 1
    \<le> (2+card (atms_of_m A)) ^ (1+card (atms_of_m A)) - \<mu>\<^sub>C' A S"
    by auto
  hence  "((2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A)) - \<mu>\<^sub>C' A T) *
      (1 + 3 ^ card (atms_of_m A)) + (1 + 3 ^ card (atms_of_m A))
    \<le> ((2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A)) - \<mu>\<^sub>C' A S)
      * (1 + 3 ^ card (atms_of_m A))"
    by (smt One_nat_def add.commute add_Suc comm_monoid_add_class.add_0 mult.commute mult_Suc_right
      mult_le_mono2)
  moreover
    have cl_T_S:  "clauses T = clauses S"
      using dpll_bj.hyps dpll_bj.prems(1) dpll_bj_clauses by auto
    have "conflicting_bj_clss_yet (card (atms_of_m A)) S < 1+ 3 ^ card (atms_of_m A)"
    by simp
  ultimately have "((2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A)) - \<mu>\<^sub>C' A T)
      * (1 + 3 ^ card (atms_of_m A)) + conflicting_bj_clss_yet (card (atms_of_m A)) T
    < ((2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A)) - \<mu>\<^sub>C' A S)  * (1 + 3 ^ card (atms_of_m A))"
    by linarith
  hence "((2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A)) - \<mu>\<^sub>C' A T)
        * (1 + 3 ^ card (atms_of_m A))
      + conflicting_bj_clss_yet (card (atms_of_m A)) T
    < ((2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A)) - \<mu>\<^sub>C' A S)
        * (1 + 3 ^ card (atms_of_m A))
      + conflicting_bj_clss_yet (card (atms_of_m A)) S"
    by linarith
  hence "((2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A)) - \<mu>\<^sub>C' A T)
      * (1 + 3 ^ card (atms_of_m A)) * 2
    + conflicting_bj_clss_yet (card (atms_of_m A)) T * 2
    < ((2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A)) - \<mu>\<^sub>C' A S)
      * (1 + 3 ^ card (atms_of_m A)) * 2
    + conflicting_bj_clss_yet (card (atms_of_m A)) S * 2"
    by linarith
  thus ?case unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_def cl_T_S by presburger
next
  case (learn S C F' K d F C' L) note clss_S_C = this(1) and atms_C = this(2) and dist = this(3) and
    tauto = this(4) and learn_restr = this(5) and tr_S = this(6) and C' = this(7) and F_C = this(8)
    and C_new = this(9) and inv = this(10) and atms_S_A = this(11) and atms_tr_S_A = this(12) and
    n_d = this(13) and finite_S = this(14)
  have [simp]: "card (insert C (clauses S)) = Suc (card (clauses S))"
    using C_new by (simp add: C' finite_S )
  have "insert C (conflicting_bj_clss S) \<subseteq> build_all_simple_clss (atms_of_m A)"
    proof -
      have "C \<in>  build_all_simple_clss (atms_of_m A)"
        by (metis (no_types, hide_lams) Un_subset_iff atms_of_m_finite build_all_simple_clss_mono
          contra_subsetD dist distinct_mset_not_tautology_implies_in_build_all_simple_clss
          dual_order.trans fin_A atms_C atms_S_A atms_tr_S_A tauto)
      moreover have "conflicting_bj_clss S \<subseteq> build_all_simple_clss (atms_of_m A)"
        unfolding conflicting_bj_clss_def
        proof
          fix x :: "'v literal multiset"
          assume "x \<in> {C + {#L#} |C L. C + {#L#} \<in> clauses S
            \<and> distinct_mset (C + {#L#}) \<and> \<not> tautology (C + {#L#})
            \<and> (\<exists>F' K d F. trail S = F' @ Marked K d # F \<and> F \<Turnstile>as CNot C)}"
          hence "\<exists>m l. x = m + {#l#} \<and> m + {#l#} \<in> clauses S
            \<and> distinct_mset (m + {#l#}) \<and> \<not> tautology (m + {#l#})
            \<and> (\<exists>ms l la msa. trail S = ms @ Marked l la # msa \<and> msa \<Turnstile>as CNot m)"
            by blast
          thus "x \<in> build_all_simple_clss (atms_of_m A)"
            by (meson atms_S_A atms_of_atms_of_m_mono atms_of_m_finite build_all_simple_clss_mono
              contra_subsetD distinct_mset_not_tautology_implies_in_build_all_simple_clss
              dual_order.trans fin_A)
        qed
      ultimately show ?thesis
        by auto
    qed
  hence "card (insert C (conflicting_bj_clss S)) \<le> 3 ^ (card (atms_of_m A))"
    by (meson Nat.le_trans atms_of_m_finite build_all_simple_clss_card build_all_simple_clss_finite
      card_mono fin_A)
  moreover have [simp]: "card (insert C (conflicting_bj_clss S))
    = Suc (card ((conflicting_bj_clss S)))"
    using C' conflicting_bj_clss_incl_clauses contra_subsetD C_new finite_S
    by fastforce
  moreover have [simp]: "conflicting_bj_clss (add_cls C S) = conflicting_bj_clss S \<union> {C}"
     using dist tauto F_C by (force simp add: ac_simps conflicting_bj_clss_add_cls C' tr_S)
  ultimately have [simp]: "conflicting_bj_clss_yet (card (atms_of_m A)) S
    = Suc (conflicting_bj_clss_yet (card (atms_of_m A)) (add_cls C S))"
      by simp

  have "((2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A)) - \<mu>\<^sub>C' A (add_cls C S))
    * (1 + 3 ^ card (atms_of_m A)) * 2
    = ((2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A)) - \<mu>\<^sub>C' A S)
    * (1 + 3 ^ card (atms_of_m A)) * 2"
      unfolding \<mu>\<^sub>C'_def by auto
  moreover
    have "conflicting_bj_clss_yet (card (atms_of_m A)) (add_cls C S)
        * 2
      + card (clauses (add_cls C S))
      < conflicting_bj_clss_yet (card (atms_of_m A)) S * 2
      + card (clauses S)"
     by auto
  ultimately show ?case unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_def by presburger
next
  case (forget S C) note finite_S = this(9)
  have [simp]: "\<mu>\<^sub>C' A (remove_cls C S) =  \<mu>\<^sub>C' A S"
    unfolding \<mu>\<^sub>C'_def by auto
  have "forget S (remove_cls C S)"
    apply (rule forget.intros) using forget by auto
  hence [simp]: "3 ^ card (atms_of_m A) - card (conflicting_bj_clss S - {C})
    = conflicting_bj_clss_yet (card (atms_of_m A)) S"
    using do_not_forget_before_backtracking_clause_learned_clause_untouched
    by (metis (no_types, lifting) conflicting_bj_clss_remove_cls)
  have "finite (clauses S)" using finite_S by blast
  thus ?case using \<open>C \<in> clauses S\<close> card_Diff1_less unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_def by fastforce
qed

lemma cdcl_clauses_bound:
  assumes
    "cdcl S T" and
    "inv S" and
    "atms_of_m (clauses S) \<subseteq> A" and
    "atm_of `(lits_of (trail S)) \<subseteq> A" and
    "finite (clauses S)" and
    "finite A"
  shows "clauses T \<subseteq> clauses S \<union> build_all_simple_clss A"
  using assms
proof (induction rule: cdcl_learn_all_induct)
  case dpll_bj
  thus ?case using dpll_bj_clauses by blast
next
  case forget
  thus ?case using clause_remove_clause by blast
next
  case (learn S C F K d F' C' L) note atms_C = this(2) and dist = this(3) and tauto = this(4) and
  atms_clss_S = this(11) and atms_trail_S = this(12) and finite = this(14)
  have "atms_of C \<subseteq> A"
    using atms_C atms_clss_S atms_trail_S by auto
  hence "build_all_simple_clss (atms_of C) \<subseteq> build_all_simple_clss A"
    using finite by (auto simp add: build_all_simple_clss_mono)
  hence "C \<in> build_all_simple_clss A"
    using finite dist tauto
    by (auto dest: distinct_mset_not_tautology_implies_in_build_all_simple_clss)
  thus ?case by auto
qed

lemma rtranclp_cdcl_clauses_bound:
  assumes
    "cdcl\<^sup>*\<^sup>* S T" and
    "inv S" and
    "atms_of_m (clauses S) \<subseteq> A" and
    "atm_of `(lits_of (trail S)) \<subseteq> A" and
    "finite (clauses S)" and
    finite: "finite A"
  shows "clauses T \<subseteq> clauses S \<union> build_all_simple_clss A"
  using assms(1-5)
proof induction
  case base
  thus ?case by simp
next
  case (step T U) note st = this(1) and cdcl = this(2) and IH = this(3)[OF this(4-7)] and
    inv = this(4) and atms_clss_S = this(5) and atms_trail_S = this(6) and finite_cls_S = this(7)
  have "inv T"
    using rtranclp_cdcl_inv st inv by blast
  moreover have "atms_of_m (clauses T) \<subseteq> A" and "atm_of ` lits_of (trail T) \<subseteq> A"
    using rtranclp_cdcl_trail_clauses_bound[OF st] inv atms_clss_S atms_trail_S by blast+
  moreover have "finite (clauses T)"
    using IH finite_cls_S finite by (meson build_all_simple_clss_finite finite_Un rev_finite_subset)
  ultimately have "clauses U \<subseteq> clauses T \<union> build_all_simple_clss A"
       using cdcl finite by (simp add: cdcl_clauses_bound)
  thus ?case using IH by auto
qed


lemma rtranclp_cdcl_card_clauses_bound:
  assumes
    "cdcl\<^sup>*\<^sup>* S T" and
    "inv S" and
    "atms_of_m (clauses S) \<subseteq> A" and
    "atm_of `(lits_of (trail S)) \<subseteq> A" and
    "finite (clauses S)" and
    finite: "finite A"
  shows "card (clauses T) \<le> card (clauses S) + 3 ^ (card A)"
  using rtranclp_cdcl_clauses_bound[OF assms] finite by (meson Nat.le_trans assms(5)
    build_all_simple_clss_card build_all_simple_clss_finite card_Un_le card_mono finite_UnI
    nat_add_left_cancel_le)

lemma rtranclp_cdcl_card_clauses_bound':
  assumes
    "cdcl\<^sup>*\<^sup>* S T" and
    "inv S" and
    "atms_of_m (clauses S) \<subseteq> A" and
    "atm_of `(lits_of (trail S)) \<subseteq> A" and
    "finite (clauses S)" and
    finite: "finite A"
  shows "card {C \<in> clauses T. tautology C \<or> \<not>distinct_mset C}
    \<le> card {C \<in> clauses S. tautology C \<or> \<not>distinct_mset C} + 3 ^ (card A)"
  using rtranclp_cdcl_clauses_bound[OF assms] finite
proof -
  have "{C \<in> clauses T. tautology C \<or> \<not>distinct_mset C}
    \<subseteq> {C \<in> clauses S. tautology C \<or> \<not>distinct_mset C} \<union> build_all_simple_clss A"
    using rtranclp_cdcl_clauses_bound[OF assms] by auto
  hence "card {C \<in> clauses T. tautology C \<or> \<not>distinct_mset C}
    \<le> card ({C \<in> clauses S. tautology C \<or> \<not>distinct_mset C} \<union> build_all_simple_clss A)"
    using finite by (simp add: assms(5) build_all_simple_clss_finite card_mono)
  thus ?thesis
    by (meson Nat.le_trans build_all_simple_clss_card card_Un_le local.finite nat_add_left_cancel_le)
qed

lemma rtranclp_cdcl_card_simple_clauses_bound:
  assumes
    "cdcl\<^sup>*\<^sup>* S T" and
    "inv S" and
    "atms_of_m (clauses S) \<subseteq> A" and
    "atm_of `(lits_of (trail S)) \<subseteq> A" and
    "finite (clauses S)" and
    finite: "finite A"
  shows "card (clauses T)
    \<le> card {C \<in> clauses S. tautology C \<or> \<not>distinct_mset C} + 3 ^ (card A)"
  using rtranclp_cdcl_clauses_bound[OF assms] finite
proof -
  have "\<And>x. x \<in> clauses T \<Longrightarrow>\<not> tautology x \<Longrightarrow> distinct_mset x \<Longrightarrow> x \<in> build_all_simple_clss A"
    using rtranclp_cdcl_clauses_bound[OF assms] by (metis (full_types) UnE assms(3)
     atms_of_atms_of_m_mono build_all_simple_clss_mono
     distinct_mset_not_tautology_implies_in_build_all_simple_clss local.finite subset_eq)
  hence "clauses T
    \<subseteq> {C \<in> clauses S. tautology C \<or> \<not>distinct_mset C} \<union> build_all_simple_clss A"
    using rtranclp_cdcl_clauses_bound[OF assms] by auto
  hence "card(clauses T)
    \<le> card ({C \<in> clauses S. tautology C \<or> \<not>distinct_mset C} \<union> build_all_simple_clss A)"
    using finite by (simp add: assms(5) build_all_simple_clss_finite card_mono)
  thus ?thesis
    by (meson Nat.le_trans build_all_simple_clss_card card_Un_le local.finite nat_add_left_cancel_le)
qed

definition \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound :: "'v literal multiset set \<Rightarrow> 'st \<Rightarrow> nat" where
"\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A S =
  ((2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A))) * (1 + 3 ^ card (atms_of_m A)) * 2
     + 2*3 ^ (card (atms_of_m A))
     + card {C \<in> clauses S. tautology C \<or> \<not>distinct_mset C} + 3 ^ (card (atms_of_m A))"

lemma \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_update_trail[simp]:
  "\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A (update_trail M S) = \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A S"
  unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_def by auto

lemma rtranclp_cdcl_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_update_trail:
  assumes
    "cdcl\<^sup>*\<^sup>* S T" and
    "inv S" and
    "atms_of_m (clauses S) \<subseteq> atms_of_m A" and
    "atm_of `(lits_of (trail S)) \<subseteq> atms_of_m A" and
    "finite (clauses S)" and
    finite: "finite (atms_of_m A)"
  shows "\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' A (update_trail M T) \<le> \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A S"
proof -
  have " ((2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A)) - \<mu>\<^sub>C' A (update_trail M T))
    \<le> (2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A))"
    by auto
  hence "((2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A)) - \<mu>\<^sub>C' A (update_trail M T))
        * (1 + 3 ^ card (atms_of_m A)) * 2
    \<le> (2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A)) * (1 + 3 ^ card (atms_of_m A)) * 2"
    using mult_le_mono1 by blast
  moreover
    have "conflicting_bj_clss_yet (card (atms_of_m A)) T * 2 \<le> 2 * 3 ^ card (atms_of_m A)"
      by linarith
  moreover have "card (clauses (update_trail M T))
      \<le> card {C \<in> clauses S. tautology C \<or> \<not>distinct_mset C} + 3 ^ card (atms_of_m A)"
    using rtranclp_cdcl_card_simple_clauses_bound[OF assms(1-6)] by simp
  ultimately show ?thesis
    unfolding  \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_def \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_def by linarith
qed

lemma rtranclp_cdcl_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound:
  assumes
    "cdcl\<^sup>*\<^sup>* S T" and
    "inv S" and
    "atms_of_m (clauses S) \<subseteq> atms_of_m A" and
    "atm_of `(lits_of (trail S)) \<subseteq> atms_of_m A" and
    "finite (clauses S)" and
    finite: "finite (atms_of_m A)"
  shows "\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' A T \<le> \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A S"
proof -
  have "\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' A (update_trail (trail T) T) = \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' A T"
    unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_def  \<mu>\<^sub>C'_def conflicting_bj_clss_def by auto
  thus ?thesis using rtranclp_cdcl_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_update_trail[OF assms, of "trail T"] by auto
qed

(* TODO Move *)
lemma distinct_mset_add_single:
  "distinct_mset ({#a#} + L) \<longleftrightarrow> distinct_mset L \<and> a \<notin># L"
  unfolding distinct_mset_def by (smt add.commute add.left_neutral add_diff_cancel_left'
    count_single count_union mset_leD mset_le_add_right not_gr0)

lemma tautology_add_single:
  "tautology ({#a#} + L) \<longleftrightarrow> tautology L \<or> -a \<in># L"
  unfolding tautology_decomp by (cases a) auto

(* TODO Move *)
lemma build_all_simple_clssE:
  "x \<in> build_all_simple_clss atms \<Longrightarrow> finite atms
    \<Longrightarrow> atms_of x \<subseteq> atms \<and> \<not>tautology x \<and> distinct_mset x"
proof (induct "card atms" arbitrary: atms x)
  case (0 atms)
  thus ?case by auto
next
  case (Suc n) note IH = this(1) and card = this(2) and x = this(3) and finite = this(4)
  obtain v where "v \<in> atms" and v: "v = Min atms"
    using Min_in card local.finite by fastforce

  let ?atms' = "atms - {v}"
  have "build_all_simple_clss atms
    = {{#Pos v#} + \<chi> |\<chi>. \<chi> \<in> build_all_simple_clss (?atms')}
      \<union> {{#Neg v#} + \<chi> |\<chi>. \<chi> \<in> build_all_simple_clss (?atms')}
      \<union> build_all_simple_clss (?atms')"
    using build_all_simple_clss_simps_else[of "atms"] finite \<open>v \<in> atms\<close> unfolding v
    by (metis emptyE)
  then consider
      (Pos) \<chi> \<phi> where "x = {#\<phi>#} + \<chi>" and "\<chi> \<in> build_all_simple_clss (?atms')" and
        "\<phi> = Pos v \<or> \<phi> = Neg v"
    | (In) "x \<in> build_all_simple_clss (?atms')"
    using x by auto
  thus ?case
    proof cases
      case In
      thus ?thesis using card finite IH[of ?atms'] \<open>v \<in> atms\<close> by fastforce
    next
      case Pos note x_\<chi> = this(1) and \<chi> = this(2) and \<phi> = this(3)
      have
        "atms_of \<chi> \<subseteq> atms - {v}" and
        "\<not> tautology \<chi>" and
        "distinct_mset \<chi>"
          using card finite IH[of ?atms' \<chi>] \<open>v \<in> atms\<close> x_\<chi> \<chi> by auto
      moreover hence "count \<chi> (Neg v) = 0" and "count \<chi> (Pos v) = 0"
         using \<open>v \<in> atms\<close> unfolding x_\<chi> apply (metis Diff_insert_absorb Set.set_insert
         atm_iff_pos_or_neg_lit gr0I subset_iff)
        using \<open>atms_of \<chi> \<subseteq> atms - {v}\<close>  by (meson Diff_iff atm_iff_pos_or_neg_lit
          contra_subsetD insertI1 not_gr0)
      ultimately show ?thesis
        using \<open>v \<in> atms\<close> \<phi> unfolding x_\<chi>
        by (auto simp add: tautology_add_single distinct_mset_add_single)
    qed
qed

lemma rtranclp_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_decreasing:
  assumes
    "cdcl\<^sup>*\<^sup>* S T" and
    "inv S" and
    "atms_of_m (clauses S) \<subseteq> atms_of_m A" and
    "atm_of `(lits_of (trail S)) \<subseteq> atms_of_m A" and
    "finite (clauses S)" and
    finite: "finite (atms_of_m A)"
  shows "\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A T \<le> \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A S"
proof -
  have "{C \<in> clauses T. tautology C \<or> \<not> distinct_mset C}
    \<subseteq> {C \<in> clauses S. tautology C \<or> \<not> distinct_mset C}"
    using rtranclp_cdcl_clauses_bound[OF assms] finite by (auto dest!: build_all_simple_clssE)
  hence "card {C \<in> clauses T. tautology C \<or> \<not> distinct_mset C} \<le>
    card {C \<in> clauses S. tautology C \<or> \<not> distinct_mset C}"
    by (simp add: assms(5) card_mono)
  thus ?thesis
    unfolding  \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_def by auto
qed

end -- \<open>end of \<open>conflict_driven_clause_learning_learning_before_backjump_only_distinct_learnt\<close>\<close>

section \<open>DPLL with simple backtrack\<close>
locale dpll_with_backtrack
begin
inductive backtrack :: "('v, 'lvl, 'mark) marked_lit list \<times> 'v literal multiset set
  \<Rightarrow> ('v, 'lvl, 'mark) marked_lit list \<times> 'v literal multiset set \<Rightarrow> bool" where
"backtrack_split (fst S)  = (M', L # M) \<Longrightarrow> is_marked L \<Longrightarrow> D \<in> snd S
  \<Longrightarrow> fst S \<Turnstile>as CNot D \<Longrightarrow> backtrack S (Propagated (- (lit_of L)) Proped # M, snd S)"

inductive_cases backtrackE[elim]: "backtrack (M, N) (M', N')"
lemma backtrack_is_backjump:
  fixes M M' :: "('v, 'lvl, 'mark) marked_lit list"
  assumes
    backtrack: "backtrack (M, N) (M', N')" and
    no_dup: "(no_dup \<circ> fst) (M, N)" and
    decomp: "all_decomposition_implies N (get_all_marked_decomposition M)"
    shows "
       \<exists>C F' K d F L l C'.
          M = F' @ Marked K d # F \<and>
          M' = Propagated L l # F \<and> N = N' \<and> C \<in> N \<and> F' @ Marked K d # F \<Turnstile>as CNot C \<and>
          undefined_lit L F \<and> atm_of L \<in> atms_of_m N \<union> atm_of ` lits_of (F' @ Marked K d # F) \<and>
          N \<Turnstile>p C' + {#L#} \<and> F \<Turnstile>as CNot C'"
proof -
  let ?S = "(M, N)"
  let ?T = "(M', N')"
  obtain F F' P L D where
    b_sp: "backtrack_split M = (F', L # F)"  and
    "is_marked L" and
    "D \<in> snd ?S" and
    "M \<Turnstile>as CNot D" and
    bt: "backtrack ?S (Propagated (- (lit_of L)) P # F, N)" and
    M': "M' = Propagated (- (lit_of L)) P # F" and
    [simp]: "N' = N"
  using backtrackE[OF backtrack] by (metis backtrack fstI sndI)
  let ?K = "lit_of L"
  let ?C = "image_mset lit_of {#K\<in>#mset M. is_marked K \<and> K\<noteq>L#} :: 'v literal multiset"
  let ?C' = "set_mset (image_mset single (?C+{#?K#}))"
  obtain K d where L: "L = Marked K d" using \<open>is_marked L\<close> by (cases L) auto

  have M: "M = F' @ Marked K d # F"
    using b_sp  by (metis L backtrack_split_list_eq fst_conv snd_conv)
  moreover have "F' @ Marked K d # F \<Turnstile>as CNot D"
    using \<open>M\<Turnstile>as CNot D\<close> unfolding M .
  moreover have "undefined_lit (-?K) F"
    using no_dup unfolding M L by (simp add: defined_lit_map)
  moreover have "atm_of (-K) \<in> atms_of_m N \<union> atm_of ` lits_of (F' @ Marked K d # F)"
    unfolding lits_of_def by auto
  moreover
    have "N \<union> ?C' \<Turnstile>ps {{#}}"
      proof -
        have A: "N \<union> ?C' \<union> (\<lambda>a. {#lit_of a#}) ` set M  =
          N \<union> (\<lambda>a. {#lit_of a#}) ` set M"
          unfolding M L by auto
        have "N \<union> {{#lit_of L#} |L. is_marked L \<and> L \<in> set M} \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set M"
          using all_decomposition_implies_propagated_lits_are_implied[OF decomp] .
        moreover have C': "?C' = {{#lit_of L#} |L. is_marked L \<and> L \<in> set M}"
          unfolding M L apply standard
            apply force
          using IntI by auto
        ultimately have N_C_M: "N \<union> ?C' \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set M"
          by auto
        have "N \<union> (\<lambda>L. {#lit_of L#}) ` (set M) \<Turnstile>ps {{#}}"
          (* TODO tune proof *)
          using \<open>M \<Turnstile>as CNot D\<close> \<open>D\<in>snd ?S\<close> unfolding true_clss_clss_def true_annots_def Ball_def
           true_annot_def L M apply auto
          apply (smt consistent_CNot_not image_Un insert_absorb2 insert_def mk_disjoint_insert
            sup.absorb_iff2 sup_commute sup_left_commute true_cls_union_increase' true_clss_def
            true_clss_singleton_lit_of_implies_incl true_clss_union)+
          done
        thus ?thesis
          using true_clss_clss_left_right[OF N_C_M, of "{{#}}"] unfolding A by auto
      qed
    have "N \<Turnstile>p image_mset uminus ?C + {#-?K#}"
      unfolding true_clss_cls_def true_clss_clss_def total_over_m_def
      proof (intro allI impI)
        fix I
        assume
          tot: "total_over_set I (atms_of_m (N \<union> {image_mset uminus ?C + {#- ?K#}})) " and
          cons: "consistent_interp I" and
          "I \<Turnstile>s N"
        have "(K \<in> I \<and> -K \<notin> I) \<or> (-K \<in> I \<and> K \<notin> I)"
          using cons tot unfolding consistent_interp_def L by (cases K) auto
        have "total_over_set I (atm_of ` lit_of ` (set M \<inter> {L. is_marked L \<and> L \<noteq> Marked K d}))"
          using tot by (auto simp add: L atms_of_uminus_lit_atm_of_lit_of)

        hence H: "\<And>x.
            lit_of x \<notin> I \<Longrightarrow> x \<in> set M \<Longrightarrow>is_marked x
            \<Longrightarrow> x \<noteq> Marked K d \<Longrightarrow> -lit_of x \<in> I"
            (* TODO one-liner? *)
          unfolding total_over_set_def atms_of_s_def
          proof -
            fix x :: "('v, 'lvl, 'mark) marked_lit"
            assume a1: "x \<in> set M"
            assume a2: "\<forall>l\<in>atm_of ` lit_of ` (set M \<inter> {L. is_marked L \<and> L \<noteq> Marked K d}).
              Pos l \<in> I \<or> Neg l \<in> I"
            assume a3: "lit_of x \<notin> I"
            assume a4: "is_marked x"
            assume a5: "x \<noteq> Marked K d"
            have f6: "Neg (atm_of (lit_of x)) = - Pos (atm_of (lit_of x))"
              by simp
            have "Pos (atm_of (lit_of x)) \<in> I \<or> Neg (atm_of (lit_of x)) \<in> I"
              using a5 a4 a2 a1 by blast
            thus "- lit_of x \<in> I"
              using f6 a3 by (metis (no_types) atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
                literal.sel(1))
          qed
        have "\<not>I \<Turnstile>s ?C'"
          using \<open>N \<union> ?C' \<Turnstile>ps {{#}}\<close> tot cons \<open>I \<Turnstile>s N\<close>
          unfolding true_clss_clss_def total_over_m_def
          by (simp add: atms_of_uminus_lit_atm_of_lit_of atms_of_m_single_image_atm_of_lit_of)
        then show "I \<Turnstile> image_mset uminus ?C + {#- lit_of L#}"
          unfolding true_clss_def true_cls_def Bex_mset_def
          using \<open>(K \<in> I \<and> -K \<notin> I) \<or> (-K \<in> I \<and> K \<notin> I)\<close>
          unfolding L by (auto dest!: H)
      qed
  moreover
    have "set F' \<inter> {K. is_marked K \<and> K \<noteq> L} = {}"
      using backtrack_split_fst_not_marked[of _ M] b_sp by auto
    hence "F \<Turnstile>as CNot (image_mset uminus ?C)"
       unfolding M CNot_def true_annots_def by (auto simp add: L lits_of_def)
  ultimately show ?thesis
    using M' \<open>D \<in> snd ?S\<close> L by auto
qed

lemma backtrack_is_backjump':
  fixes M M' :: "('v, 'lvl, 'mark) marked_lit list"
  assumes
    backtrack: "backtrack S T" and
    no_dup: "(no_dup \<circ> fst) S" and
    decomp: "all_decomposition_implies (snd S) (get_all_marked_decomposition (fst S))"
    shows "
        \<exists>C F' K d F L l C'.
          fst S = F' @ Marked K d # F \<and>
          T = (Propagated L l # F, snd S) \<and> C \<in> snd S \<and> fst S \<Turnstile>as CNot C
          \<and> |L| \<notin>\<^sub>l |F| \<and> atm_of L \<in> atms_of_m (snd S) \<union> atm_of ` lits_of (fst S) \<and>
          snd S \<Turnstile>p C' + {#L#} \<and> F \<Turnstile>as CNot C'"
  apply (cases S, cases T)
  using backtrack_is_backjump[of "fst S" "snd S" "fst T" "snd T"] assms by fastforce

sublocale dpll_state fst snd "\<lambda>M S. (M, snd S)" "\<lambda>C (M, N). (M, insert C N)"
  "\<lambda>C (M, N). (M, N - {C})"
  by unfold_locales auto

lemma bj_ops: "backjumping_ops fst snd (\<lambda>M S. (M, snd S)) (\<lambda>C (M, N). (M, insert C N))
  (\<lambda>C (M, N). (M, N - {C}))"
  by unfold_locales

lemma backtrack_is_backjump'':
  fixes M M' :: "('v, 'lvl, 'mark) marked_lit list"
  assumes
    backtrack: "backtrack S T" and
    no_dup: "(no_dup \<circ> fst) S" and
    decomp: "all_decomposition_implies (snd S) (get_all_marked_decomposition (fst S))"
    shows "backjumping_ops.backjump fst snd (\<lambda>M S. (M, snd S)) backtrack S T"
proof -
  obtain C F' K d F L l C' where
    1: "fst S = F' @ Marked K d # F" and
    2: "T = (Propagated L l # F, snd S)" and
    3: "C \<in> snd S" and
    4: "fst S \<Turnstile>as CNot C" and
    5: "undefined_lit L F" and
    6: "atm_of L \<in> atms_of_m (snd S) \<union> atm_of ` lits_of (fst S)" and
    7: "snd S \<Turnstile>p C' + {#L#}" and
    8: "F \<Turnstile>as CNot C'"
  using backtrack_is_backjump'[OF assms] by blast

  show ?thesis
    using backjumping_ops.backjump.intros[OF bj_ops 1 2 3 4 5 6 7 8] backtrack by simp
qed

lemma can_do_bt_step:
   assumes
     M: "fst S = F' @ Marked K d # F" and
     "C \<in> snd S" and
     C: "fst S \<Turnstile>as CNot C"
   shows "\<not> no_step backtrack S"
proof -
  obtain L G' G where
    "backtrack_split (fst S) = (G', L # G)"
    unfolding M by (induction F' rule: marked_lit_list_induct) auto
  moreover hence "is_marked L"
     by (metis backtrack_split_snd_hd_marked list.distinct(1) list.sel(1) snd_conv)
  ultimately show ?thesis
     using backtrack.intros[of S G' L G C] \<open>C \<in> snd S\<close> C unfolding M by auto
qed

end

sublocale dpll_with_backtrack \<subseteq> dpll_state fst snd "\<lambda>M S. (M, snd S)" "\<lambda>C (M, N). (M, insert C N)"
  "\<lambda>C (M, N). (M, N - {C})"
  by unfold_locales auto

sublocale dpll_with_backtrack \<subseteq> dpll_with_backjumping_ops fst snd "\<lambda>M S. (M, snd S)"
  "\<lambda>C (M, N). (M, insert C N)" "\<lambda>C (M, N). (M, N - {C})"
  "\<lambda>(M, N). no_dup M \<and> all_decomposition_implies N (get_all_marked_decomposition M)"
  backtrack
  apply unfold_locales
    apply (simp (no_asm))
   apply (frule can_do_bt_step; simp)
  using backtrack_is_backjump'' by (smt comp_apply prod.case_eq_if)

sublocale dpll_with_backtrack \<subseteq> dpll_with_backjumping  fst snd "\<lambda>M S. (M, snd S)"
  "\<lambda>C (M, N). (M, insert C N)" "\<lambda>C (M, N). (M, N - {C})"
  "\<lambda>(M, N). no_dup M \<and> all_decomposition_implies N (get_all_marked_decomposition M)" backtrack
  apply unfold_locales
  using dpll_bj_no_dup dpll_bj_all_decomposition_implies_inv apply fastforce
  done

sublocale dpll_with_backtrack \<subseteq> conflict_driven_clause_learning_ops
   fst snd "\<lambda>M S. (M, snd S)" "\<lambda>C (M, N). (M, insert C N)" "\<lambda>C (M, N). (M, N - {C})"
   "\<lambda>(M, N). no_dup M \<and> all_decomposition_implies N (get_all_marked_decomposition M)"
   dpll_with_backtrack.backtrack "\<lambda>_ _. False" "\<lambda>_ _. False"
   by unfold_locales

sublocale dpll_with_backtrack \<subseteq> conflict_driven_clause_learning
   fst snd "\<lambda>M S. (M, snd S)" "\<lambda>C (M, N). (M, insert C N)" "\<lambda>C (M, N). (M, N - {C})"
   "\<lambda>(M, N). no_dup M \<and> all_decomposition_implies N (get_all_marked_decomposition M)"
   dpll_with_backtrack.backtrack "\<lambda>_ _. False" "\<lambda>_ _. False"
   apply unfold_locales
   using cdcl.simps dpll_bj_inv forgetE learnE by blast

context dpll_with_backtrack
begin
lemma tranclp_dpll_wf_inital_state:
  assumes fin: "finite A"
  shows "wf {((M'::('v, 'lvl, 'mark) annoted_lits, N'::'v clauses), ([], N))|M' N' N.
    dpll_bj\<^sup>+\<^sup>+ ([], N) (M', N') \<and> atms_of_m N \<subseteq> atms_of_m A}"
  using tranclp_dpll_bj_wf[OF assms(1)] by (rule wf_subset) auto

theorem full0_dpll_normal_forms:
  fixes M M' :: "('a, 'b, 'c) marked_lit list"
  assumes
    full: "full0 dpll_bj ([], N) (M', N')" and
    "finite N"
  shows "unsatisfiable N \<or> (M' \<Turnstile>as N \<and> satisfiable N)"
  using assms full0_dpll_backjump_normal_forms[of "([],N)" "(M', N')" N] by auto
end

section \<open>CDCL with restarts\<close>
subsection\<open>Definition\<close>
text \<open>To add restarts we needs some assumptions on the predicate (called @{term cdcl} here):
  \<^item> a function @{term f} that is strictly monotonic (and to ease the proof, we assume that
  @{term "f (0::nat) = 0"}). The first step is actually only a restart to clean the state (e.g. to
  ensure that the trail is empty).
  \<^item> a measure @{term "\<mu>"}: it should decrease under the assumptions @{term bound_inv}, whenever a
  @{term cdcl} or a @{term restart} is done. A parameter is given to @{term \<mu>}: for conflict-driven
  clause learning, it is an upper-bound of the clauses. We are assuming that such a bound can be
  found after a restart whenever the invariant holds.
  \<^item> we also assume that the measure decrease after any @{term cdcl} step.
  \<^item> an invariant on the states @{term cdcl_inv} that also holds after restarts.
  \<^item> it is \<^emph>\<open>not required\<close> that the measure decrease with respect to restarts, but the measure has to
  be bound by some function @{term \<mu>_bound} taking the same parameter as @{term \<mu>} and the initial
  state of the considered @{term cdcl} chain.\<close>
locale cdcl_increasing_restarts_ops =
  dpll_state trail clauses update_trail add_cls remove_cls for
    trail :: "'st \<Rightarrow> ('v, 'lvl, 'mark) annoted_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    update_trail :: "('v, 'lvl, 'mark) annoted_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    add_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" +
  fixes
    f :: "nat \<Rightarrow> nat" and
    restart :: "'st \<Rightarrow> 'st \<Rightarrow> bool" and
    bound_inv :: "'bound \<Rightarrow> 'st \<Rightarrow> bool" and
    \<mu> :: "'bound \<Rightarrow> 'st \<Rightarrow> nat" and
    cdcl :: "'st \<Rightarrow> 'st \<Rightarrow> bool" and
    cdcl_inv :: "'st \<Rightarrow> bool" and
    \<mu>_bound :: "'bound \<Rightarrow> 'st \<Rightarrow> nat"
  assumes
    mono_f: "strict_mono f" and
    bound_inv: "\<And>A S T. cdcl_inv S \<Longrightarrow> bound_inv A S \<Longrightarrow> cdcl S T \<Longrightarrow> bound_inv A T" and
    cdcl_measure: "\<And>A S T. cdcl_inv S \<Longrightarrow> bound_inv A S \<Longrightarrow> cdcl S T \<Longrightarrow> \<mu> A T < \<mu> A S" and
    measure_bound2: "\<And>A T U. cdcl_inv T \<Longrightarrow> bound_inv A T \<Longrightarrow> cdcl\<^sup>*\<^sup>* T U
       \<Longrightarrow> \<mu> A U \<le> \<mu>_bound A T" and
    measure_bound4: "\<And>A T U. cdcl_inv T \<Longrightarrow> bound_inv A T \<Longrightarrow> cdcl\<^sup>*\<^sup>* T U
       \<Longrightarrow> \<mu>_bound A U \<le> \<mu>_bound A T" and
    cdcl_restart_inv: "\<And>A U V. cdcl_inv U \<Longrightarrow> restart U V \<Longrightarrow> bound_inv A U \<Longrightarrow> bound_inv A V" and
    [simp]: "f 0 = 0" and
    exists_bound: "\<And>R S. cdcl_inv R \<Longrightarrow> restart R S \<Longrightarrow> \<exists>A. bound_inv A S" and
    cdcl_inv: "\<And>S T. cdcl_inv S \<Longrightarrow> cdcl S T \<Longrightarrow> cdcl_inv T" and
    cdcl_inv_restart: "\<And>S T. cdcl_inv S \<Longrightarrow> restart S T \<Longrightarrow> cdcl_inv T"
begin

lemma f_Suc_not_zero[simp]: "f (Suc n) \<noteq> 0"
  by (metis lessI less_nat_zero_code mono_f strict_mono_def)

lemma strict_mono_ge_id: "strict_mono (g::nat \<Rightarrow> nat) \<Longrightarrow> g n \<ge> n"
  unfolding strict_mono_def apply (induction n, simp)
  by (metis Suc_leI diff_diff_cancel lessI less_imp_diff_less)

lemma cdcl_cdcl_inv:
  assumes
    "(cdcl^^n) S T" and
    "cdcl_inv S"
  shows "cdcl_inv T"
  using assms by (induction n arbitrary: T) (auto intro:bound_inv cdcl_inv)

lemma cdcl_bound_inv:
  assumes
    "(cdcl^^n) S T" and
    "cdcl_inv S"
    "bound_inv A S"
  shows "bound_inv A T"
  using assms by (induction n arbitrary: T) (auto intro:bound_inv cdcl_cdcl_inv)

lemma rtranclp_cdcl_cdcl_inv:
  assumes
    "cdcl\<^sup>*\<^sup>* S T" and
    "cdcl_inv S"
  shows "cdcl_inv T"
  using assms by induction (auto intro: cdcl_inv)

lemma rtranclp_cdcl_bound_inv:
  assumes
    "cdcl\<^sup>*\<^sup>* S T" and
    "bound_inv A S" and
    "cdcl_inv S"
  shows "bound_inv A T"
  using assms by induction (auto intro:bound_inv rtranclp_cdcl_cdcl_inv)

lemma cdcl_comp_n_le:
  assumes
    "(cdcl^^(Suc n)) S T" and
    "bound_inv A S"
    "cdcl_inv S"
  shows "\<mu> A T < \<mu> A S - n"
  using assms
proof (induction n arbitrary: T)
  case 0
  thus ?case using cdcl_measure by auto
next
  case (Suc n) note IH =this(1)[OF _ this(3) this(4)] and S_T =this(2) and b_inv = this(3) and
  c_inv = this(4)
  obtain U :: 'st where S_U: "(cdcl^^(Suc n)) S U" and U_T: "cdcl U T" using S_T by auto
  then have "\<mu> A U < \<mu> A S - n" using IH[of U] by simp
  moreover
    have "bound_inv A U"
      using S_U b_inv  cdcl_bound_inv c_inv by blast
    hence "\<mu> A T < \<mu> A U" using cdcl_measure[OF _ _ U_T] S_U c_inv cdcl_cdcl_inv by auto
  ultimately show ?case by linarith
qed

lemma rtranclp_cdcl_measure:
  assumes
    "cdcl\<^sup>*\<^sup>* S T" and
    "bound_inv A S" and
    "cdcl_inv S"
  shows "\<mu> A T \<le> \<mu> A S"
  using assms
proof (induction rule: rtranclp_induct)
  case base
  thus ?case by auto
next
  case (step T U) note IH =this(3)[OF this(4) this(5)] and st =this(1) and cdcl= this(2) and
    b_inv = this(4) and c_inv = this(5)
  have "bound_inv A T"
    by (meson cdcl_bound_inv rtranclp_imp_relpowp st step.prems)
  moreover have "cdcl_inv T"
    using c_inv rtranclp_cdcl_cdcl_inv st by blast
  ultimately have "\<mu> A U < \<mu> A T" using cdcl_measure[OF _ _ cdcl] by auto
  thus ?case using IH by linarith
qed

lemma cdcl_comp_bounded:
  assumes
    "bound_inv A S" and "cdcl_inv S" and "m \<ge> 1+\<mu> A S"
  shows "\<not>(cdcl ^^ m) S T"
  using assms cdcl_comp_n_le[of "m-1" S T A] by fastforce

text \<open>
  \<^item> @{term "m \<ge> f (Suc n)"} ensure that at least one step has been done.\<close>
inductive cdcl_with_restart where
"cdcl_with_restart (R, n) (S, Suc n) \<Longrightarrow> (cdcl^^m) S T
  \<Longrightarrow> m \<ge> f (Suc n) \<Longrightarrow> restart T U
  \<Longrightarrow> cdcl_with_restart (S, Suc n) (U, Suc (Suc n))" |
"cdcl_with_restart (R, n) (S, Suc n) \<Longrightarrow> full cdcl S T
  \<Longrightarrow> cdcl_with_restart (S, Suc n) (T, Suc (Suc n))" |
"restart S T \<Longrightarrow> cdcl_with_restart (S, 0) (T, 1)"

lemmas cdcl_with_restart_induct = cdcl_with_restart.induct[split_format(complete),
  OF cdcl_increasing_restarts_ops_axioms]

lemma cdcl_with_restart_bound_inv:
  assumes
    "cdcl_with_restart S T" and
    "bound_inv A (fst S)" and
    "cdcl_inv (fst S)"
  shows "bound_inv A (fst T)"
  using assms apply (induction rule: cdcl_with_restart.induct)
    prefer 2 apply (metis Nitpick.rtranclp_unfold fstI full_def rtranclp_cdcl_bound_inv)
  by (metis cdcl_bound_inv cdcl_cdcl_inv cdcl_restart_inv fst_conv)+


lemma cdcl_with_restart_cdcl_inv:
  assumes
    "cdcl_with_restart S T" and
    "cdcl_inv (fst S)"
  shows "cdcl_inv (fst  T)"
  using assms apply (induction)
    apply (metis cdcl_cdcl_inv cdcl_inv_restart fst_conv)
   apply (metis fstI full0_def full0_unfold rtranclp_cdcl_cdcl_inv)
  by (simp add: cdcl_inv_restart)

lemma rtranclp_cdcl_with_restart_cdcl_inv:
  assumes
    "cdcl_with_restart\<^sup>*\<^sup>* S T" and
    "cdcl_inv (fst S)"
  shows "cdcl_inv (fst T)"
  using assms by (induction) (auto intro: cdcl_with_restart_cdcl_inv)

lemma rtranclp_cdcl_with_restart_bound_inv:
  assumes
    "cdcl_with_restart\<^sup>*\<^sup>* S T" and
    "cdcl_inv (fst S)" and
    "bound_inv A (fst S)"
  shows "bound_inv A (fst T)"
  using assms apply (induction)
   apply (simp add: cdcl_cdcl_inv cdcl_with_restart_bound_inv)
  using cdcl_with_restart_bound_inv rtranclp_cdcl_with_restart_cdcl_inv by blast

lemma cdcl_with_restart_increasing_number:
  "cdcl_with_restart S T \<Longrightarrow> snd T = 1 + snd S"
  by (induction rule: cdcl_with_restart.induct) auto
end

locale cdcl_increasing_restarts =
  cdcl_increasing_restarts_ops trail clauses update_trail add_cls remove_cls f restart bound_inv
    \<mu> cdcl cdcl_inv \<mu>_bound
  for
    trail :: "'st \<Rightarrow> ('v, 'lvl, 'mark) annoted_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    update_trail :: "('v, 'lvl, 'mark) annoted_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    add_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    f :: "nat \<Rightarrow> nat" and
    restart :: "'st \<Rightarrow> 'st \<Rightarrow> bool" and
    bound_inv :: "'bound \<Rightarrow> 'st \<Rightarrow> bool" and
    \<mu> :: "'bound \<Rightarrow> 'st \<Rightarrow> nat" and
    cdcl :: "'st \<Rightarrow> 'st \<Rightarrow> bool" and
    cdcl_inv :: "'st \<Rightarrow> bool" and
    \<mu>_bound :: "'bound \<Rightarrow> 'st \<Rightarrow> nat" +
  assumes
    measure_bound: "\<And>A T V n. cdcl_inv T \<Longrightarrow> bound_inv A T \<Longrightarrow> cdcl_with_restart (T, n) (V, Suc n)
      \<Longrightarrow> \<mu> A V \<le> \<mu>_bound A T" and
    cdcl_with_restarts_\<mu>_bound:
      "cdcl_with_restart (T, a) (V, b) \<Longrightarrow>  cdcl_inv T \<Longrightarrow> bound_inv A T
        \<Longrightarrow> \<mu>_bound A V \<le> \<mu>_bound A T"
begin


lemma rtranclp_cdcl_with_restarts_\<mu>_bound:
  "cdcl_with_restart\<^sup>*\<^sup>* (T, a) (V, b) \<Longrightarrow>  cdcl_inv T \<Longrightarrow> bound_inv A T \<Longrightarrow> \<mu>_bound A V \<le> \<mu>_bound A T"
  apply (induction rule: rtranclp_induct2)
   apply simp
  by (metis cdcl_with_restarts_\<mu>_bound dual_order.trans fst_conv
    rtranclp_cdcl_with_restart_bound_inv rtranclp_cdcl_with_restart_cdcl_inv)

lemma cdcl_with_restarts_measure_bound:
  "cdcl_with_restart (T, a) (V, b) \<Longrightarrow>  cdcl_inv T \<Longrightarrow> bound_inv A T \<Longrightarrow> \<mu> A V \<le> \<mu>_bound A T"
  apply (cases rule: cdcl_with_restart.cases)
     apply simp
    using measure_bound relpowp_imp_rtranclp apply fastforce
   apply (metis full0_def full0_unfold measure_bound2 prod.inject)
  using measure_bound by simp

lemma rtranclp_cdcl_with_restarts_measure_bound:
  "cdcl_with_restart\<^sup>*\<^sup>* (T, a) (V, b) \<Longrightarrow>  cdcl_inv T \<Longrightarrow> bound_inv A T \<Longrightarrow> \<mu> A V \<le> \<mu>_bound A T"
  apply (induction rule: rtranclp_induct2)
    apply (simp add: measure_bound2)
  by (metis dual_order.trans fst_conv measure_bound2 r_into_rtranclp rtranclp.rtrancl_refl
    rtranclp_cdcl_with_restart_bound_inv rtranclp_cdcl_with_restart_cdcl_inv
    rtranclp_cdcl_with_restarts_\<mu>_bound)

lemma "wf {(T, S). cdcl_with_restart S T \<and> cdcl_inv (fst S)}" (is "wf ?A")
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain g where
    g: "\<And>i. cdcl_with_restart (g i) (g (Suc i))" and cdcl_inv_g: "\<And>i. cdcl_inv (fst (g i))"
    unfolding wf_iff_no_infinite_down_chain by fast
  hence "\<And>i. snd (g i) < snd (g (i+1))"
    by (metis Suc_eq_plus1 add.left_neutral add_Suc cdcl_with_restart_increasing_number lessI)
  have "strict_mono (snd o g)"
    unfolding strict_mono_def by (smt Suc_eq_plus1 cdcl_with_restart_increasing_number comp_def g
      lessI lift_Suc_mono_less semiring_normalization_rules(24))
  { fix i
    have H: "\<And>T Ta m. (cdcl ^^ m) T Ta \<Longrightarrow> no_step cdcl T \<Longrightarrow> m = 0"
      apply (case_tac m) apply simp by (meson relpowp_E2)
    have "\<exists> T m. (cdcl ^^ m) (fst (g i)) T \<and> m \<ge> f (snd (g (i)))"
      using g[of i] apply (cases rule: cdcl_with_restart.cases)
         apply auto[]
        prefer 2 apply (auto intro!: exI[of _ "(0::nat)"])[]
      using g[of "Suc i"] apply (cases rule: cdcl_with_restart.cases)
      unfolding full0_def by (auto simp add: full_def dest!: H dest: tranclpD)
  } note H = this
  obtain A where "bound_inv A (fst (g 1))"
    using g[of 0] cdcl_inv_g[of 0] apply (cases rule: cdcl_with_restart.cases)
      apply (metis One_nat_def cdcl_inv exists_bound fst_conv relpowp_imp_rtranclp rtranclp_induct)
     apply (metis H f_Suc_not_zero fst_conv full_def le_0_eq relpowp_E2 snd_conv)
    by (metis One_nat_def exists_bound fst_conv)
  have "strict_mono (\<lambda>j. f (snd (g j)))"
    by (metis `strict_mono (snd \<circ> g)` comp_def mono_f strict_monoD strict_monoI)
  let ?j = "\<mu>_bound A (fst (g 1)) + 1"
  have "f ?j \<ge> ?j"
    by (simp add: mono_f strict_mono_ge_id)
  {
     fix i j
     have cdcl_with_restart: "j \<ge> i \<Longrightarrow> cdcl_with_restart\<^sup>*\<^sup>* (g i) (g j)"
       apply (induction j)
         apply simp
       by (metis g le_Suc_eq rtranclp.rtrancl_into_rtrancl rtranclp.rtrancl_refl)
  } note cdcl_with_restart = this
  have "cdcl_inv (fst (g (Suc 0)))"
    by (simp add: cdcl_inv_g)
  have "cdcl_with_restart\<^sup>*\<^sup>* (fst (g 1), snd (g 1)) (fst (g ?j), snd (g ?j))"
    by (simp add: cdcl_with_restart)
  have "\<mu> A (fst (g ?j)) \<le> \<mu>_bound A (fst (g 1))"
    apply (rule rtranclp_cdcl_with_restarts_measure_bound)
    using \<open>cdcl_with_restart\<^sup>*\<^sup>* (fst (g 1), snd (g 1)) (fst (g ?j), snd (g ?j))\<close> apply blast
        apply (simp add: cdcl_inv_g)
       using \<open>bound_inv A (fst (g 1))\<close> apply simp
    done
  hence "\<mu> A (fst (g ?j)) \<le> ?j"
    by auto
  have inv: "bound_inv A (fst (g ?j))"
    using \<open>bound_inv A (fst (g 1))\<close> \<open>cdcl_inv (fst (g (Suc 0)))\<close>
    by (meson cdcl_inv_g cdcl_with_restart not_add_less2 not_less
      rtranclp_cdcl_with_restart_bound_inv)
  obtain T m where
    cdcl_m: "(cdcl ^^ m) (fst (g ?j)) T" and
    f_m: "f (snd (g ?j)) \<le> m"
    using H[of "?j"] by blast
  have "?j \<le> m"
    using f_m \<open>f ?j \<ge> ?j\<close> Nat.le_trans `strict_mono (\<lambda>j. f (snd (g j)))` strict_mono_ge_id by blast
  thus False
    proof -
      have "\<And>n. bound_inv A (fst (g (n + 1)))"
        by (meson \<open>bound_inv A (fst (g 1))\<close> cdcl_inv_g cdcl_with_restart le_add2
          rtranclp_cdcl_with_restart_bound_inv)
      moreover have "\<And>b. \<not> bound_inv b (fst (g (1 + \<mu>_bound A (fst (g 1))))) \<or> \<not> 1 + \<mu> b (fst (g (1 + \<mu>_bound A (fst (g 1))))) \<le> m"
        using cdcl_comp_bounded cdcl_inv_g cdcl_m by force (* 16 ms *)
      ultimately show ?thesis
        using \<open>\<mu> A (fst (g (\<mu>_bound A (fst (g 1)) + 1))) \<le> \<mu>_bound A (fst (g 1))\<close>
        \<open>\<mu>_bound A (fst (g 1)) + 1 \<le> m\<close> by fastforce
    qed
qed
end

section \<open>Combining backjump and learning\<close>
locale cdcl_merge_conflict_propagate =
  dpll_state trail clauses update_trail add_cls remove_cls +
  decide_ops trail clauses update_trail add_cls remove_cls +
  propagate_ops trail clauses update_trail add_cls remove_cls +
  conflict_driven_clause_learning trail clauses update_trail add_cls remove_cls inv "\<lambda>_ _. True"
  "\<lambda>C S.  distinct_mset C \<and> \<not>tautology C \<and>
    (\<exists>F K d F' C' L.  trail S = F' @ Marked K d # F \<and> C = C' + {#L#} \<and> F \<Turnstile>as CNot C'
      \<and> C' + {#L#} \<notin> clauses S)"
  forget_conds
  for
    trail :: "'st \<Rightarrow> ('v::linorder, 'lvl, 'mark) annoted_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    update_trail :: "('v, 'lvl, 'mark) annoted_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    add_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    inv :: "'st \<Rightarrow> bool" and
    backjump :: "'st \<Rightarrow> 'st \<Rightarrow> bool" and
    forget_conds :: "'v clause \<Rightarrow> 'st \<Rightarrow> bool" +
  fixes backjump_l :: "'st \<Rightarrow> 'st \<Rightarrow> bool"
  assumes backjump_l:
    "\<And>S T. backjump_l S T \<Longrightarrow>  inv S \<Longrightarrow>
      \<exists>C F' K d F L l C'.
        trail S = F' @ Marked K d # F
        \<and> T = update_trail (Propagated L l # F) (add_cls (C' + {#L#}) S)
        \<and> C \<in> clauses S
        \<and> trail S \<Turnstile>as CNot C
        \<and> undefined_lit L F
        \<and> atm_of L \<in> atms_of_m (clauses S) \<union> atm_of ` (lits_of (trail S))
        \<and> clauses S \<Turnstile>p C' + {#L#}
        \<and> F \<Turnstile>as CNot C'
        \<and> distinct_mset (C' + {#L#})
        \<and> C' + {#L#} \<notin> clauses S
        \<and> \<not> tautology (C' + {#L#})" and
    bj_can_jump:
      "\<And>S C F' K d F L.
        inv S
        \<Longrightarrow> trail S = F' @ Marked K d # F
        \<Longrightarrow> C \<in> clauses S
        \<Longrightarrow> trail S \<Turnstile>as CNot C
        \<Longrightarrow> undefined_lit L F
        \<Longrightarrow> atm_of L \<in> atms_of_m (clauses S) \<union> atm_of ` (lits_of (F' @ Marked K d # F))
        \<Longrightarrow> clauses S \<Turnstile>p C' + {#L#}
        \<Longrightarrow> F \<Turnstile>as CNot C'
        \<Longrightarrow> distinct_mset (C' + {#L#})
        \<Longrightarrow> \<not>tautology (C' + {#L#})
        \<Longrightarrow> C' + {#L#} \<notin> clauses S
        \<Longrightarrow> \<not>no_step backjump_l S"
begin
declare conflict_driven_clause_learning_axioms[intro]

inductive cdcl_merged :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
cdcl_merged_decide:  "decide S S' \<Longrightarrow> cdcl_merged S S'" |
cdcl_merged_propagate: "propagate S S' \<Longrightarrow> cdcl_merged S S'" |
cdcl_merged_backjump_l:  "backjump_l S S' \<Longrightarrow> cdcl_merged S S'" |
cdcl_merged_forget: "forget S S' \<Longrightarrow> cdcl_merged S S'"

lemma backjump_l_learn_backjump:
  assumes bt: "backjump_l S T" and inv: "inv S"
  shows "\<exists>C' L. learn S (add_cls (C' + {#L#}) S)
    \<and> backjumping_ops.backjump trail clauses update_trail (\<lambda>_ _. True) (add_cls (C' + {#L#}) S) T
    \<and> atms_of (C' + {#L#}) \<subseteq> atms_of_m (clauses S) \<union> atm_of ` (lits_of (trail S))"
proof -
   obtain C F' K d F L l C' where
     tr_S: "trail S = F' @ Marked K d # F" and
     T: "T = update_trail (Propagated L l # F) (add_cls (C' + {#L#}) S)" and
     C_cls_S: "C \<in> clauses S" and
     tr_S_CNot_C: "trail S \<Turnstile>as CNot C" and
     undef: "undefined_lit L F" and
     atm_L: "atm_of L \<in> atms_of_m (clauses S) \<union> atm_of ` (lits_of (trail S))" and
     clss_C: "clauses S \<Turnstile>p C' + {#L#}" and
     "F \<Turnstile>as CNot C'" and
     distinct: "distinct_mset (C' + {#L#})"  and
     not_known: "C' + {#L#} \<notin> clauses S" and
     not_tauto: "\<not> tautology (C' + {#L#})"
     using backjump_l[OF bt inv] by blast
   have atms_C':  "atms_of C' \<subseteq>  atm_of ` (lits_of F)"
     proof -
       obtain ll :: "'v \<Rightarrow> ('v literal \<Rightarrow> 'v) \<Rightarrow> 'v literal set \<Rightarrow> 'v literal" where
         "\<forall>v f L. v \<notin> f ` L \<or> v = f (ll v f L) \<and> ll v f L \<in> L"
         by moura
       thus ?thesis unfolding tr_S
         by (metis (no_types) `F \<Turnstile>as CNot C'` atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
           atms_of_def in_CNot_implies_uminus(2) mem_set_mset_iff subsetI)
     qed
   hence "atms_of (C' + {#L#}) \<subseteq> atms_of_m (clauses S) \<union> atm_of ` (lits_of (trail S))"
     using atm_L tr_S by auto
   moreover have learn: "learn S (add_cls (C' + {#L#}) S)"
     apply (rule learn.intros)
         apply (rule clss_C)
       using atms_C' atm_L apply (fastforce simp add: tr_S)[]
     apply standard
      apply (rule distinct)
     apply standard
      apply (rule not_tauto)
     apply standard
     using \<open>F \<Turnstile>as CNot C'\<close> distinct not_tauto not_known by (auto simp: tr_S)
   moreover have bj: "backjumping_ops.backjump trail clauses update_trail (\<lambda>_ _. True)
     (add_cls (C' + {#L#}) S) T"
     apply (rule backjump.intros[OF _ T, of F' K d C "C'"])
     using \<open>F \<Turnstile>as CNot C'\<close> C_cls_S tr_S_CNot_C undef  by (auto simp add: tr_S lits_of_def)
   ultimately show ?thesis by auto
qed

lemma cdcl_merged_is_tranclp_cdcl:
  "cdcl_merged S T \<Longrightarrow> inv S \<Longrightarrow> cdcl\<^sup>+\<^sup>+ S T"
proof (induction rule: cdcl_merged.induct)
  case (cdcl_merged_decide S T)
  hence "cdcl S T"
    using bj_decide conflict_driven_clause_learning_ops.cdcl.simps
    conflict_driven_clause_learning_ops_axioms by fastforce
  thus ?case by auto
next
  case (cdcl_merged_propagate S T)
  hence "cdcl S T"
    using bj_propagate conflict_driven_clause_learning_ops.cdcl.simps
    conflict_driven_clause_learning_ops_axioms by fastforce
  thus ?case by auto
next
   case (cdcl_merged_forget S T)
   hence "cdcl S T"
     using c_forget by blast
   thus ?case by auto
next
   case (cdcl_merged_backjump_l S T) note bt = this(1) and inv = this(2)
   show ?case
     using backjump_l_learn_backjump[OF bt inv]
     by (metis (no_types, lifting) bj_backjump c_dpll_bj c_learn tranclp.r_into_trancl
       tranclp.trancl_into_trancl)
qed

lemma rtranclp_cdcl_merged_is_rtranclp_cdcl_and_inv:
  "cdcl_merged\<^sup>*\<^sup>* S T \<Longrightarrow> inv S \<Longrightarrow> cdcl\<^sup>*\<^sup>* S T \<and> inv T"
proof (induction rule: rtranclp_induct)
  case base
  thus ?case by auto
next
  case (step T U) note st =this(1) and cdcl = this(2) and IH = this(3)[OF this(4)] and inv = this(4)
  have "cdcl\<^sup>*\<^sup>* T U"
    using cdcl_merged_is_tranclp_cdcl[OF cdcl] IH by (blast dest: tranclp_into_rtranclp)
  hence "cdcl\<^sup>*\<^sup>* S U" using IH by fastforce
  moreover have "inv U" using IH \<open>cdcl\<^sup>*\<^sup>* T U\<close> rtranclp_cdcl_inv by blast
  ultimately show ?case using st by fast
qed

lemma rtranclp_cdcl_merged_is_rtranclp_cdcl:
  "cdcl_merged\<^sup>*\<^sup>* S T \<Longrightarrow> inv S \<Longrightarrow> cdcl\<^sup>*\<^sup>* S T"
  using rtranclp_cdcl_merged_is_rtranclp_cdcl_and_inv by blast

lemma rtranclp_cdcl_merged_inv:
  "cdcl_merged\<^sup>*\<^sup>* S T \<Longrightarrow> inv S \<Longrightarrow> inv T"
  using rtranclp_cdcl_merged_is_rtranclp_cdcl_and_inv by blast

definition \<mu>\<^sub>C' :: "'a literal multiset set \<Rightarrow> 'st \<Rightarrow> nat" where
"\<mu>\<^sub>C' A T \<equiv> \<mu>\<^sub>C (1+card (atms_of_m A)) (2+card (atms_of_m A)) (\<nu> T)"

definition \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged :: "'a literal multiset set \<Rightarrow> 'st \<Rightarrow> nat" where
"\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged A T \<equiv>
  ((2+card (atms_of_m A)) ^ (1+card (atms_of_m A)) - \<mu>\<^sub>C' A T) * 2 + card (clauses T)"
lemma "decide S T \<Longrightarrow> cdcl S T"
using bj_decide c_dpll_bj by blast

lemma cdcl_decreasing_measure':
  assumes
    "cdcl_merged S T" and
    "inv S"
    "atms_of_m (clauses S) \<subseteq> atms_of_m A"
    "atm_of ` lits_of (trail S) \<subseteq> atms_of_m A" and
    "no_dup (trail S)" and
    "finite (clauses S)" and
    fin_A: "finite A"
  shows "\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged A T < \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged A S"
  using assms(1-6)
proof induction
  case (cdcl_merged_decide S T)
  have "clauses S = clauses T"
    using cdcl_merged_decide.hyps clauses_update_trail by blast
  moreover have
    "(2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A))
       - \<mu>\<^sub>C (1 + card (atms_of_m A)) (2 + card (atms_of_m A)) (\<nu> T)
     < (2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A))
       - \<mu>\<^sub>C (1 + card (atms_of_m A)) (2 + card (atms_of_m A)) (\<nu> S)"
    apply (rule dpll_bj_trail_mes_decreasing_prop[of S T A])
       using cdcl_merged_decide fin_A by (simp_all add:  add: bj_decide cdcl_merged_decide.hyps)
  ultimately show ?case
    unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged_def \<mu>\<^sub>C'_def by simp
next
  case (cdcl_merged_propagate S T)
  have "clauses S = clauses T"
    using cdcl_merged_propagate.hyps clauses_update_trail by blast
  moreover have
    "(2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A))
       - \<mu>\<^sub>C (1 + card (atms_of_m A)) (2 + card (atms_of_m A)) (\<nu> T)
     < (2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A))
       - \<mu>\<^sub>C (1 + card (atms_of_m A)) (2 + card (atms_of_m A)) (\<nu> S)"
    apply (rule dpll_bj_trail_mes_decreasing_prop[of S T A])
       using cdcl_merged_propagate fin_A by (simp_all add: bj_propagate cdcl_merged_propagate.hyps)
  ultimately show ?case
    unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged_def \<mu>\<^sub>C'_def by simp
next
  case (cdcl_merged_forget S T)
  have "card (clauses T) < card (clauses S)"
    by (metis card_Diff1_less cdcl_merged_forget.hyps cdcl_merged_forget.prems(5)
      clause_remove_clause forget.cases)
  moreover
    have "trail S = trail T"
      by (metis cdcl_merged_forget.hyps forget.cases update_trail_remove_clauses)
    hence
      "(2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A))
        - \<mu>\<^sub>C (1 + card (atms_of_m A)) (2 + card (atms_of_m A)) (\<nu> T)
       = (2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A))
        - \<mu>\<^sub>C (1 + card (atms_of_m A)) (2 + card (atms_of_m A)) (\<nu> S)"
       by auto
  ultimately show ?case
    unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged_def \<mu>\<^sub>C'_def by simp
next
  case (cdcl_merged_backjump_l S T) note bj_l = this(1) and inv = this(2) and atms_clss = this(3)
    and atms_trail = this(4) and n_d = this(5)
  obtain C' L where
    learn: "learn S (add_cls (C' + {#L#}) S)" and
    bj: "backjumping_ops.backjump trail clauses update_trail (\<lambda>_ _. True)
           (add_cls (C' + {#L#}) S) T" and
    atms_C: "atms_of (C' + {#L#}) \<subseteq> atms_of_m (clauses S) \<union> atm_of ` (lits_of (trail S))"
    using bj_l inv backjump_l_learn_backjump by blast
  have "card (clauses T) = 1 + card (clauses S)"
    using backjump_l[OF bj_l inv] \<open>finite (clauses S)\<close> by auto
  have
    "((2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A))
      - \<mu>\<^sub>C (1 + card (atms_of_m A)) (2 + card (atms_of_m A)) (\<nu> T))
    < ((2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A))
      - \<mu>\<^sub>C (1 + card (atms_of_m A)) (2 + card (atms_of_m A)) (\<nu> (add_cls (C' + {#L#}) S)))"
    apply (rule dpll_bj_trail_mes_decreasing_prop)
         using bj bj_backjump apply blast
        using c_learn cdcl_inv inv learn apply blast
       using atms_C atms_clss atms_trail apply fastforce
      using atms_trail apply simp
     apply (simp add: n_d)
    using fin_A apply simp
    done
  hence "((2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A))
      - \<mu>\<^sub>C (1 + card (atms_of_m A)) (2 + card (atms_of_m A)) (\<nu> T))
    < ((2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A))
      - \<mu>\<^sub>C (1 + card (atms_of_m A)) (2 + card (atms_of_m A)) (\<nu> S))"
    by auto
  then show ?case
    unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged_def \<open>card (clauses T) = 1 + card (clauses S)\<close> \<mu>\<^sub>C'_def
    by linarith
qed

lemma wf_cdcl_merged:
  assumes
    fin_A: "finite A"
  shows "wf {(T, S).
    (inv S \<and> atms_of_m (clauses S) \<subseteq> atms_of_m A \<and> atm_of ` lits_of (trail S) \<subseteq> atms_of_m A
    \<and> no_dup (trail S) \<and> finite (clauses S))
    \<and> cdcl_merged S T}"
  apply (rule wfP_if_measure[of _ _ "\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged A"])
  using cdcl_decreasing_measure' fin_A by simp

lemma tranclp_cdcl_cdcl_tranclp:
  assumes
    "cdcl_merged\<^sup>+\<^sup>+ S T" and
    "inv S" and
    "atms_of_m (clauses S) \<subseteq> atms_of_m A" and
    "atm_of ` lits_of (trail S) \<subseteq> atms_of_m A" and
    "no_dup (trail S)" and
    "finite (clauses S)" and
    "finite A"
  shows "(T, S) \<in> {(T, S).
    (inv S \<and> atms_of_m (clauses S) \<subseteq> atms_of_m A \<and> atm_of ` lits_of (trail S) \<subseteq> atms_of_m A
    \<and> no_dup (trail S) \<and> finite (clauses S))
    \<and> cdcl_merged S T}\<^sup>+" (is "_ \<in> ?P\<^sup>+")
  using assms(1-6)
proof (induction rule: tranclp_induct)
  case base
  thus ?case by auto
next
  case (step T U) note st = this(1) and cdcl = this(2) and IH = this(3)[OF this(4-8)] and
    inv = this(4) and atms_clss = this(5) and atms_trail = this(6) and n_d = this(7) and
    fin = this(8)
  have "cdcl\<^sup>*\<^sup>* S T"
    apply (rule rtranclp_cdcl_merged_is_rtranclp_cdcl)
    using st cdcl inv by auto
  have "inv T"
    apply (rule rtranclp_cdcl_merged_inv)
      using inv st cdcl by auto
  moreover have "atms_of_m (clauses T) \<subseteq> atms_of_m A"
    using rtranclp_cdcl_trail_clauses_bound[OF \<open>cdcl\<^sup>*\<^sup>* S T\<close> inv atms_clss atms_trail] by fast
  moreover have "atm_of ` (lits_of (trail T))\<subseteq> atms_of_m A"
    using rtranclp_cdcl_trail_clauses_bound[OF \<open>cdcl\<^sup>*\<^sup>* S T\<close> inv atms_clss atms_trail] by fast
  moreover have "no_dup (trail T)"
    using rtranclp_cdcl_no_dup[OF  \<open>cdcl\<^sup>*\<^sup>* S T\<close> inv n_d] by fast
  moreover have "finite (clauses T)"
    using rtranclp_cdcl_finite_clauses[OF  \<open>cdcl\<^sup>*\<^sup>* S T\<close> inv fin] by fast
  ultimately have "(U, T) \<in> ?P"
    using cdcl by auto
  thus ?case using IH by (simp add: trancl_into_trancl2)
qed

lemma wf_tranclp_cdcl_merged:
  assumes "finite A"
  shows "wf {(T, S).
    (inv S \<and> atms_of_m (clauses S) \<subseteq> atms_of_m A \<and> atm_of ` lits_of (trail S) \<subseteq> atms_of_m A
    \<and> no_dup (trail S) \<and> finite (clauses S))
    \<and> cdcl_merged\<^sup>+\<^sup>+ S T}"
  apply (rule wf_subset)
   apply (rule wf_trancl[OF wf_cdcl_merged])
   using assms apply simp
  using tranclp_cdcl_cdcl_tranclp[OF _ _ _ _ _ _ \<open>finite A\<close>] by auto
end

subsection \<open>Instantiations\<close>
locale dpll_withbacktrack_and_restarts =
  dpll_with_backtrack +
  fixes f :: "nat \<Rightarrow> nat"
  assumes strict_mono: "strict_mono f" and f_0: "f 0 = 0"
begin
  sublocale cdcl_increasing_restarts fst snd "\<lambda>M S. (M, snd S)" "\<lambda>C (M, N). (M, insert C N)"
  "\<lambda>C (M, N). (M, N - {C})" f "\<lambda>(_, N) S. S = ([], N)"
  "\<lambda>A (M, N). atms_of_m N \<subseteq> atms_of_m A \<and> atm_of ` lits_of M \<subseteq> atms_of_m A \<and> finite A
    \<and> all_decomposition_implies N (get_all_marked_decomposition M)"
  "\<lambda>A T. (2+card (atms_of_m A)) ^ (1+card (atms_of_m A))
               - \<mu>\<^sub>C (1+card (atms_of_m A)) (2+card (atms_of_m A)) (\<nu> T)" dpll_bj
  "\<lambda>(M, N). finite N \<and> no_dup M \<and> all_decomposition_implies N (get_all_marked_decomposition M)"
  "\<lambda>A _.  (2+card (atms_of_m A)) ^ (1+card (atms_of_m A))"
  apply unfold_locales
         apply (rule strict_mono)
        apply (smt dpll_bj_all_decomposition_implies_inv dpll_bj_atms_in_trail_in_set
          dpll_bj_clauses dpll_bj_no_dup prod.case_eq_if)
       apply (rule dpll_bj_trail_mes_decreasing_prop; auto)
      apply (case_tac T, simp)
     apply (case_tac U, simp)
    apply (case_tac U; auto)
        using f_0 apply simp
    using dpll_bj_clauses dpll_bj_all_decomposition_implies_inv dpll_bj_no_dup apply fastforce
    using dpll_bj_clauses dpll_bj_all_decomposition_implies_inv dpll_bj_no_dup apply fastforce
   apply (case_tac S; auto)
    using f_0 apply simp
   apply (case_tac T; auto)
  done
end

locale cdcl_withbacktrack_and_restarts =
  conflict_driven_clause_learning_learning_before_backjump_only_distinct_learnt trail clauses
  update_trail add_cls remove_cls inv backjump learn_restrictions forget_restrictions
    for
    trail :: "'st \<Rightarrow> ('v::linorder, 'lvl, 'mark) annoted_lits" and
    clauses :: "'st \<Rightarrow> 'v::linorder clauses" and
    update_trail :: "('v, 'lvl, 'mark) annoted_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    add_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v::linorder clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    inv :: "'st \<Rightarrow> bool" and
    backjump :: "'st \<Rightarrow> 'st \<Rightarrow> bool" and
    learn_restrictions forget_restrictions :: "'v::linorder clause \<Rightarrow> 'st \<Rightarrow> bool"
    +
  fixes f :: "nat \<Rightarrow> nat"
  assumes
    strict_mono: "strict_mono f" and f_0: "f 0 = 0" and
    inv_restart:"\<And>S. inv S \<Longrightarrow> inv (update_trail [] S)"
begin

lemma bound_inv_inv:
  assumes
    "inv S" and
    "no_dup (trail S)" and
    "finite (clauses S)" and
    atms_clss_S_A: "atms_of_m (clauses S) \<subseteq> atms_of_m A" and
    atms_trail_S_A:"atm_of ` lits_of (trail S) \<subseteq> atms_of_m A" and
    "finite A" and
    cdcl: "cdcl S T"
  shows
    "atms_of_m (clauses T) \<subseteq> atms_of_m A" and
    "atm_of ` lits_of (trail T) \<subseteq> atms_of_m A" and
    "finite A"
proof -
  have "cdcl S T"
    using \<open>inv S\<close> cdcl by linarith
  hence "atms_of_m (clauses T) \<subseteq> atms_of_m (clauses S) \<union> atm_of ` lits_of (trail S)"
    using \<open>inv S\<close>
    by (meson conflict_driven_clause_learning_ops.cdcl_atms_of_m_clauses_decreasing
      conflict_driven_clause_learning_ops_axioms)
  thus "atms_of_m (clauses T) \<subseteq> atms_of_m A"
    using atms_clss_S_A atms_trail_S_A by blast
next
  show "atm_of ` lits_of (trail T) \<subseteq> atms_of_m A"
    by (meson \<open>inv S\<close> atms_clss_S_A atms_trail_S_A cdcl conflict_driven_clause_learning_ops_axioms
      conflict_driven_clause_learning_ops.cdcl_atms_in_trail_in_set)
next
  show "finite A"
    using \<open>finite A\<close> by simp
qed
  sublocale cdcl_increasing_restarts_ops _ _ _ _ _  f "\<lambda>S T. T = update_trail [] S"
    "\<lambda>A S. atms_of_m (clauses S) \<subseteq> atms_of_m A \<and> atm_of ` lits_of (trail S) \<subseteq> atms_of_m A \<and>
    finite A"
    \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' cdcl "\<lambda>S. inv S \<and> no_dup (trail S) \<and> finite (clauses S)"
    \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound
    apply (unfold_locales)
           apply (simp add: strict_mono)
          using bound_inv_inv apply meson
         apply (rule cdcl_decreasing_measure'; simp)
         apply (rule rtranclp_cdcl_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound; simp)
        apply (rule rtranclp_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_decreasing; simp)
       apply auto[]
      apply (simp add: f_0)
     apply auto[]
    using cdcl_inv cdcl_finite_clauses cdcl_no_dup apply blast
  using inv_restart apply auto[]
  done
(*unusable otherwise*)
abbreviation cdcl_l where
"cdcl_l \<equiv> conflict_driven_clause_learning_ops.cdcl trail clauses update_trail add_cls remove_cls backjump
          (\<lambda>C S. distinct_mset C \<and> \<not> tautology C \<and> learn_restrictions C S \<and> (\<exists>F K d F' C' L. trail S = F' @ Marked K d # F \<and> C = C' + {#L#} \<and> F \<Turnstile>as CNot C' \<and> C' + {#L#} \<notin> clauses S))  (\<lambda>C S. \<not> (\<exists>F' F K d L. trail S = F' @ Marked K d # F \<and> F \<Turnstile>as CNot (C - {#L#})) \<and> forget_restrictions C S)"

lemma cdcl_with_restart_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_le_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound:
  assumes
    cdcl: "cdcl_with_restart (T, a) (V, b)" and
    cdcl_inv:
      "inv T"
      "no_dup (trail T)"
      "finite (clauses T)" and
    bound_inv:
      "atms_of_m (clauses T) \<subseteq> atms_of_m A"
      "atm_of ` lits_of (trail T) \<subseteq> atms_of_m A"
      "finite A"
  shows "\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' A V \<le> \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A T"
  using cdcl_inv bound_inv
proof (induction rule: cdcl_with_restart_induct[OF cdcl])
  case (3 S T)
  thus ?case
    using rtranclp_cdcl_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound[of T T] by (simp add: inv_restart)
next
  case (1 R n S m T U) note U = this(4)
  show ?case unfolding U
    apply (rule  rtranclp_cdcl_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_update_trail)
         using \<open>(cdcl_l ^^ m) S T\<close>  apply (fastforce dest: relpowp_imp_rtranclp)
        using 1 by auto
next
  case (2 R n S T) note full = this(2)
  show ?case
    apply (rule rtranclp_cdcl_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound)
    using full 2 unfolding full_def by force+
qed

lemma cdcl_with_restart_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_le_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound:
  assumes
    cdcl: "cdcl_with_restart (T, a) (V, b)" and
    cdcl_inv:
      "inv T"
      "no_dup (trail T)"
      "finite (clauses T)" and
    bound_inv:
      "atms_of_m (clauses T) \<subseteq> atms_of_m A"
      "atm_of ` lits_of (trail T) \<subseteq> atms_of_m A"
      "finite A"
  shows "\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A V \<le> \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A T"
  using cdcl_inv bound_inv
proof (induction rule: cdcl_with_restart_induct[OF cdcl])
  case (3 S T)
  thus ?case by (simp add: inv_restart)
next
  case (1 R n S m T U) note U = this(4)
  have "\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A T \<le> \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A S"
     apply (rule rtranclp_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_decreasing)
         using \<open>(cdcl_l ^^ m) S T\<close>  apply (fastforce dest: relpowp_imp_rtranclp)
        using 1 by auto
  thus ?case unfolding U by auto
next
  case (2 R n S T) note full = this(2)
  show ?case
    apply (rule rtranclp_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_decreasing)
    using full 2 unfolding full_def by force+
qed

sublocale cdcl_increasing_restarts _ _ _ _ _  f "\<lambda>S T. T = update_trail [] S"
    "\<lambda>A S. atms_of_m (clauses S) \<subseteq> atms_of_m A \<and> atm_of ` lits_of (trail S) \<subseteq> atms_of_m A \<and>
    finite A"
    \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' cdcl "\<lambda>S. inv S \<and> no_dup (trail S) \<and> finite (clauses S)"
    \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound
  apply unfold_locales
   using cdcl_with_restart_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_le_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound apply simp
  using cdcl_with_restart_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_le_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound apply simp
  done

end
end