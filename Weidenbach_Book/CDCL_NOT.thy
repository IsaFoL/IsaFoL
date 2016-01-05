theory CDCL_NOT
imports Partial_Annotated_Clausal_Logic List_More Wf_More Partial_Clausal_Logic
begin

section \<open>NOT's CDCL\<close>
sledgehammer_params[verbose, prover=e spass z3 cvc4 verit remote_vampire]

subsection \<open>Auxiliary Lemmas\<close>
lemma no_dup_cannot_not_lit_and_uminus:
  "no_dup M \<Longrightarrow> - lit_of xa = lit_of x \<Longrightarrow> x \<in> set M \<Longrightarrow> xa \<notin> set M"
  by (metis atm_of_uminus distinct_map inj_on_eq_iff uminus_not_id')

lemma true_clss_single_iff_incl:
  "I \<Turnstile>s single ` B \<longleftrightarrow> B \<subseteq> I"
  unfolding true_clss_def by auto

lemma atms_of_m_single_atm_of[simp]:
  "atms_of_m {{#lit_of L#} |L. P L} = atm_of ` {lit_of L |L. P L}"
  unfolding atms_of_m_def by auto

lemma atms_of_uminus_lit_atm_of_lit_of:
  "atms_of {#- lit_of x. x \<in># A#} = atm_of ` (lit_of ` (set_mset A))"
  unfolding atms_of_def by (auto simp add: Fun.image_comp)

lemma atms_of_m_single_image_atm_of_lit_of:
  "atms_of_m ((\<lambda>x. {#lit_of x#}) ` A) = atm_of ` (lit_of ` A)"
  unfolding atms_of_m_def by auto

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

text \<open>Duplicate of "~~/src/HOL/ex/NatSum.thy" (but generalized to @{term "k\<ge>0"})\<close>
lemma sum_of_powers: "0 \<le> k \<Longrightarrow> (k - 1) * (\<Sum>i=0..<n. k^i) = k^n - (1::nat)"
  apply (cases "k = 0")
    apply (cases n; simp)
  by (induct n) (auto simp: Nat.nat_distrib)

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

text \<open>In the degenerate case @{term "b=0"}, the list @{term M} is empty (since the list cannot
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

subsection \<open>Initial definitions\<close>
subsubsection \<open>The state\<close>
datatype dpll_mark = Proped
lemma dpll_mark_only_one_element[simp]:
  "x = Proped" "Proped = x"
  by (case_tac x, simp)+

datatype dpll_marked_level = Level
lemma dpll_marked_level_only_one_element[simp]:
  "x = Level" "Level = x"
  by (case_tac x, simp)+

text \<open>We define here an abstraction over operation on the state we are manipulating.\<close>
locale dpll_state =
  fixes
    trail :: "'st \<Rightarrow> ('v, dpll_marked_level, dpll_mark) annoted_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    update_trail :: "('v, dpll_marked_level, dpll_mark) annoted_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_cls :: "'v clause set \<Rightarrow> 'st \<Rightarrow> 'st"
  assumes
    trail_update_trail[simp]: "\<And>M st. trail (update_trail M st) = M" and
    update_trail_update_cls[simp]: "\<And>st C. trail (update_cls C st) = trail st" and

    clauses_update_trail[simp]: "\<And>st M. clauses (update_trail M st) = clauses st" and
    clauses_update_cls[simp]: "\<And>st C. clauses (update_cls C st) = C"
begin

abbreviation prepend_trail where
"prepend_trail L S \<equiv> update_trail (L # trail S) S"

definition add_cls\<^sub>N\<^sub>O\<^sub>T :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" where
"add_cls\<^sub>N\<^sub>O\<^sub>T C S = update_cls (insert C (clauses S)) S"

definition remove_cls\<^sub>N\<^sub>O\<^sub>T :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" where
"remove_cls\<^sub>N\<^sub>O\<^sub>T C S = update_cls ((clauses S) - {C}) S"

lemma
  shows
    clauses_add_cls\<^sub>N\<^sub>O\<^sub>T[simp]: "\<And>st C. clauses (add_cls\<^sub>N\<^sub>O\<^sub>T C st) = insert C (clauses st)" and
    update_trail_add_cls\<^sub>N\<^sub>O\<^sub>T[simp]: "\<And>st C. trail(add_cls\<^sub>N\<^sub>O\<^sub>T C st) = trail st" and
    update_trail_remove_clss\<^sub>N\<^sub>O\<^sub>T[simp]: "\<And>st C. trail (remove_cls\<^sub>N\<^sub>O\<^sub>T C st) = trail st" and
    clause_remove_cls\<^sub>N\<^sub>O\<^sub>T[simp]: "\<And>st C. clauses (remove_cls\<^sub>N\<^sub>O\<^sub>T C st) = clauses st - {C}"
  unfolding add_cls\<^sub>N\<^sub>O\<^sub>T_def remove_cls\<^sub>N\<^sub>O\<^sub>T_def by auto

abbreviation trail_weight where
"trail_weight S \<equiv> map ((\<lambda>l. 1 + length l) o snd) (get_all_marked_decomposition (trail S))"

definition state_eq\<^sub>N\<^sub>O\<^sub>T :: "'st \<Rightarrow> 'st \<Rightarrow> bool" (infix "\<sim>" 50) where
"S \<sim> T \<longleftrightarrow> trail S = trail T \<and> clauses S = clauses T"

lemma state_eq\<^sub>N\<^sub>O\<^sub>T_ref[simp]:
  "S \<sim> S"
  unfolding state_eq\<^sub>N\<^sub>O\<^sub>T_def by auto

lemma state_eq\<^sub>N\<^sub>O\<^sub>T_sym[simp]:
  "S \<sim> T \<longleftrightarrow> T \<sim> S"
  unfolding state_eq\<^sub>N\<^sub>O\<^sub>T_def by auto

lemma state_eq\<^sub>N\<^sub>O\<^sub>T_trans:
  "S \<sim> T \<Longrightarrow> T \<sim> U \<Longrightarrow> S \<sim> U"
  unfolding state_eq\<^sub>N\<^sub>O\<^sub>T_def by auto

lemma
  shows
    state_eq\<^sub>N\<^sub>O\<^sub>T_trail: "S \<sim> T \<Longrightarrow> trail S = trail T" and
    state_eq\<^sub>N\<^sub>O\<^sub>T_clauses: "S \<sim> T \<Longrightarrow> clauses S = clauses T"
  unfolding state_eq\<^sub>N\<^sub>O\<^sub>T_def by auto

lemmas state_simp\<^sub>N\<^sub>O\<^sub>T[simp]= state_eq\<^sub>N\<^sub>O\<^sub>T_trail state_eq\<^sub>N\<^sub>O\<^sub>T_clauses
end

subsubsection \<open>Definition of the operation\<close>
locale propagate_ops =
  dpll_state trail clauses update_trail update_cls for
    trail :: "'st \<Rightarrow> ('v, dpll_marked_level, dpll_mark) annoted_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    update_trail :: "('v, dpll_marked_level, dpll_mark) annoted_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_cls :: "'v clause set \<Rightarrow> 'st \<Rightarrow> 'st" and
    propagate_cond :: "'st \<Rightarrow> bool"
begin
inductive propagate\<^sub>N\<^sub>O\<^sub>T :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
propagate\<^sub>N\<^sub>O\<^sub>T[intro]: "C + {#L#} \<in> clauses S \<Longrightarrow> trail S \<Turnstile>as CNot C
    \<Longrightarrow> undefined_lit L (trail S)
    \<Longrightarrow> propagate_cond S
    \<Longrightarrow> T \<sim> prepend_trail (Propagated L Proped) S
    \<Longrightarrow> propagate\<^sub>N\<^sub>O\<^sub>T S T"
inductive_cases propagateE[elim]: "propagate\<^sub>N\<^sub>O\<^sub>T S T"

end

locale decide_ops =
  dpll_state trail clauses update_trail update_cls for
    trail :: "'st \<Rightarrow> ('v, dpll_marked_level, dpll_mark) annoted_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    update_trail :: "('v, dpll_marked_level, dpll_mark) annoted_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_cls :: "'v clause set \<Rightarrow> 'st \<Rightarrow> 'st"
begin
inductive decide\<^sub>N\<^sub>O\<^sub>T ::  "'st \<Rightarrow> 'st \<Rightarrow> bool" where
decide\<^sub>N\<^sub>O\<^sub>T[intro]: "undefined_lit L (trail S) \<Longrightarrow> atm_of L \<in> atms_of_m (clauses S)
  \<Longrightarrow> T \<sim> prepend_trail (Marked L Level) S
  \<Longrightarrow> decide\<^sub>N\<^sub>O\<^sub>T S T"

inductive_cases decideE[elim]: "decide\<^sub>N\<^sub>O\<^sub>T S S'"
end

locale backjumping_ops =
  dpll_state trail clauses update_trail update_cls
  for
    trail :: "'st \<Rightarrow> ('v, dpll_marked_level, dpll_mark) annoted_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    update_trail :: "('v, dpll_marked_level, dpll_mark) annoted_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_cls :: "'v clause set \<Rightarrow> 'st \<Rightarrow> 'st" +
  fixes
    inv :: "'st \<Rightarrow> bool" and
    backjump_conds :: "'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool"
begin
inductive backjump where
"trail S = F' @ Marked K d # F
   \<Longrightarrow> T \<sim> update_trail (Propagated L Proped # F) S
   \<Longrightarrow> C \<in> clauses S
   \<Longrightarrow> trail S \<Turnstile>as CNot C
   \<Longrightarrow> undefined_lit L F
   \<Longrightarrow> atm_of L \<in> atms_of_m (clauses S) \<union> atm_of ` (lits_of (trail S))
   \<Longrightarrow> clauses S \<Turnstile>p C' + {#L#}
   \<Longrightarrow> F \<Turnstile>as CNot C'
   \<Longrightarrow> backjump_conds C' L S T
   \<Longrightarrow> backjump S T"
inductive_cases backjumpE: "backjump S T"
end

subsection \<open>DPLL with backjumping\<close>
locale dpll_with_backjumping_ops =
  dpll_state trail clauses update_trail update_cls +
  propagate_ops trail clauses update_trail update_cls propagate_conds +
  decide_ops trail clauses update_trail update_cls +
  backjumping_ops trail clauses update_trail update_cls inv backjump_conds
  for
    trail :: "'st \<Rightarrow> ('v, dpll_marked_level, dpll_mark) annoted_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    update_trail :: "('v, dpll_marked_level, dpll_mark) annoted_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_cls :: "'v clause set \<Rightarrow> 'st \<Rightarrow> 'st" and
    propagate_conds :: "'st \<Rightarrow> bool" and
    inv :: "'st \<Rightarrow> bool" and
    backjump_conds :: "'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool" +
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

subsubsection\<open>Definition\<close>

text \<open>We define dpll with backjumping:\<close>
inductive dpll_bj :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
bj_decide\<^sub>N\<^sub>O\<^sub>T:  "decide\<^sub>N\<^sub>O\<^sub>T S S' \<Longrightarrow> dpll_bj S S'" |
bj_propagate\<^sub>N\<^sub>O\<^sub>T: "propagate\<^sub>N\<^sub>O\<^sub>T S S' \<Longrightarrow> dpll_bj S S'" |
bj_backjump:  "backjump S S' \<Longrightarrow> dpll_bj S S'"

lemmas dpll_bj_induct = dpll_bj.induct[split_format(complete)]
thm dpll_bj_induct[OF dpll_with_backjumping_ops_axioms]
lemma dpll_bj_all_induct[consumes 2, case_names decide\<^sub>N\<^sub>O\<^sub>T propagate\<^sub>N\<^sub>O\<^sub>T backjump]:
  fixes S T :: "'st"
  assumes
    "dpll_bj S T" and
    "inv S"
    "\<And>L T. undefined_lit L (trail S) \<Longrightarrow> atm_of L \<in> atms_of_m (clauses S)
      \<Longrightarrow> T \<sim> prepend_trail (Marked L Level) S
      \<Longrightarrow> P S T" and
    "\<And>C L T. C + {#L#} \<in> clauses S \<Longrightarrow> trail S \<Turnstile>as CNot C \<Longrightarrow> undefined_lit L (trail S)
      \<Longrightarrow> T \<sim> prepend_trail (Propagated L Proped) S
      \<Longrightarrow> P S T" and
    "\<And>C F' K d F L C' T. C \<in> clauses S \<Longrightarrow> F' @ Marked K d # F \<Turnstile>as CNot C
      \<Longrightarrow> trail S = F' @ Marked K d # F
      \<Longrightarrow> undefined_lit L F
      \<Longrightarrow> atm_of L \<in> atms_of_m (clauses S) \<union> atm_of ` (lits_of (F' @ Marked K d # F))
      \<Longrightarrow> (clauses S) \<Turnstile>p C' + {#L#}
      \<Longrightarrow> F \<Turnstile>as CNot C'
      \<Longrightarrow> T \<sim> update_trail (Propagated L Proped #  F) S
      \<Longrightarrow> P S T"
  shows "P S T"
  apply (induct S\<equiv>S T rule: dpll_bj_induct[OF local.dpll_with_backjumping_ops_axioms])
     apply (rule assms(1))
    using assms(3) apply blast
   apply (elim propagateE) using assms(4) apply blast
  apply (elim backjumpE) using assms(5) \<open>inv S\<close> by simp

subsubsection \<open>Basic properties\<close>
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
  using assms by (induction rule: dpll_bj_all_induct)
  (auto simp: in_plus_implies_atm_of_on_atms_of_m)

lemma dpll_bj_atms_in_trail_in_set:
  assumes "dpll_bj S T"and
    "inv S" and
  "atms_of_m (clauses S) \<subseteq> A" and
  "atm_of ` (lits_of (trail S)) \<subseteq> A"
  shows "atm_of ` (lits_of (trail T)) \<subseteq> A"
  using assms by (induction rule: dpll_bj_all_induct)
  (auto simp: in_plus_implies_atm_of_on_atms_of_m)

lemma dpll_bj_all_decomposition_implies_inv:
  assumes
    "dpll_bj S T" and
    inv: "inv S" and
    decomp: "all_decomposition_implies (clauses S) (get_all_marked_decomposition (trail S))"
  shows "all_decomposition_implies (clauses T) (get_all_marked_decomposition (trail T))"
  using assms(1,2)
proof (induction rule:dpll_bj_all_induct)
  case decide\<^sub>N\<^sub>O\<^sub>T
  thus ?case using decomp by auto
next
  case (propagate\<^sub>N\<^sub>O\<^sub>T C L T) note propa = this(1) and T = this(4)
  let ?M' = "trail (prepend_trail (Propagated L Proped) S)"
  let ?N = "clauses S"
  obtain a y l where ay: "get_all_marked_decomposition ?M' = (a, y) # l"
    by (cases "get_all_marked_decomposition ?M'") fastforce+
  hence M': "?M' = y @ a" using get_all_marked_decomposition_decomp[of ?M'] by auto
  have M: "get_all_marked_decomposition (trail S) = (a, tl y) # l"
    using ay by (cases " get_all_marked_decomposition (trail S)") auto
  have y\<^sub>0: "y = (Propagated L Proped) # (tl y)"
    using ay by (auto simp add: M)
  from arg_cong[OF this, of set] have y[simp]: "set y = insert (Propagated L Proped) (set (tl y))"
    by simp
  have tr_S: "trail S = tl y @ a"
    using arg_cong[OF M', of tl] y\<^sub>0 M get_all_marked_decomposition_decomp by force
  have a_Un_N_M: "(\<lambda>a. {#lit_of a#}) ` set a \<union> ?N \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set (tl y)"
    using decomp ay unfolding all_decomposition_implies_def by (simp add: M)+

  moreover have "(\<lambda>a. {#lit_of a#}) ` set a \<union> ?N \<Turnstile>p {#L#}" (is "?I \<Turnstile>p _")
    proof (rule true_clss_cls_plus_CNot)
      show "?I \<Turnstile>p C + {#L#}"
        using propa propagate\<^sub>N\<^sub>O\<^sub>T.prems by (auto dest!: true_clss_clss_in_imp_true_clss_cls)
    next
      have "(\<lambda>m. {#lit_of m#}) ` set ?M' \<Turnstile>ps CNot C"
        using \<open>trail S \<Turnstile>as CNot C\<close> by (auto simp add: true_annots_true_clss_clss)
      have a1: "(\<lambda>m. {#lit_of m#}) ` set a \<union> (\<lambda>m. {#lit_of m#}) ` set (tl y)  \<Turnstile>ps CNot C"
        using propagate\<^sub>N\<^sub>O\<^sub>T.hyps(2) tr_S true_annots_true_clss_clss
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
    using decomp T M unfolding ay all_decomposition_implies_def by (auto simp add: ay)
next
  case (backjump C F' K d F L D T) note confl = this(2) and tr = this(3) and undef = this(4)
    and L = this(5) and N_C = this(6) and vars_D = this(5) and T = this(8)
  have decomp: "all_decomposition_implies (clauses S) (get_all_marked_decomposition F)"
    using decomp unfolding tr by (smt all_decomposition_implies_def
      get_all_marked_decomposition.simps(1) get_all_marked_decomposition_never_empty hd_Cons_tl
      insert_iff list.sel(3) list.set(2) tl_get_all_marked_decomposition_skip_some)

  moreover have "(\<lambda>a. {#lit_of a#}) ` set (fst (hd (get_all_marked_decomposition F))) \<union> clauses S
    \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set (snd (hd (get_all_marked_decomposition F)))"
    by (metis all_decomposition_implies_cons_single decomp get_all_marked_decomposition_never_empty
      hd_Cons_tl)
  moreover
    have vars_of_D: "atms_of D \<subseteq> atm_of ` lits_of F"
      using \<open>F \<Turnstile>as CNot D\<close> unfolding atms_of_def
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
    using a_N_D_L a_N_CNot_D by (blast intro: true_clss_cls_plus_CNot)
  thus ?case
    using decomp T unfolding all_decomposition_implies_def by (auto simp add: F)
qed

subsubsection \<open>Termination\<close>
paragraph \<open>Using a proper measure\<close>
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

lemma length_in_get_all_marked_decomposition_bounded:
  assumes i:"i \<in> set (trail_weight S)"
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

paragraph \<open>Well-foundedness\<close>
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
  fixes M :: "('v, dpll_marked_level, dpll_mark) annoted_lits " and N :: "'v clauses"
  assumes
    "dpll_bj S T" and
    "inv S" and
    NA: "atms_of_m (clauses S) \<subseteq> atms_of_m A" and
    MA: "atm_of ` lits_of (trail S) \<subseteq> atms_of_m A" and
    n_d: "no_dup (trail S)" and
    finite: "finite A"
  shows "\<mu>\<^sub>C (1+card (atms_of_m A)) (2+card (atms_of_m A)) (trail_weight T)
    > \<mu>\<^sub>C (1+card (atms_of_m A)) (2+card (atms_of_m A)) (trail_weight S)"
  using assms(1,2)
proof (induction rule: dpll_bj_all_induct)
  case (propagate\<^sub>N\<^sub>O\<^sub>T C L) note CLN = this(1) and MC =this(2) and undef_L = this(3) and T = this(4)
  have incl: "atm_of ` lits_of (Propagated L Proped # trail S) \<subseteq> atms_of_m A"
    using propagate\<^sub>N\<^sub>O\<^sub>T.hyps propagate_ops.propagate\<^sub>N\<^sub>O\<^sub>T dpll_bj_atms_in_trail_in_set bj_propagate\<^sub>N\<^sub>O\<^sub>T
    NA MA CLN by (auto simp: in_plus_implies_atm_of_on_atms_of_m)

  have no_dup: "no_dup (Propagated L Proped # trail S)"
    using defined_lit_map n_d undef_L by auto
  obtain a b l where M: "get_all_marked_decomposition (trail S) = (a, b) # l"
    by (case_tac "get_all_marked_decomposition (trail S)") auto
  have b_le_M: "length b \<le> length (trail S)"
    using get_all_marked_decomposition_decomp[of "trail S"] by (simp add: M)
  have "finite (atms_of_m A)" using finite by simp

  hence "length (Propagated L Proped # trail S) \<le> card (atms_of_m A)"
    using incl finite unfolding no_dup_length_eq_card_atm_of_lits_of[OF no_dup]
    by (simp add: card_mono)
  hence latm: "unassigned_lit A b = Suc (unassigned_lit A (Propagated L d # b))"
    using b_le_M by auto
  thus ?case using T by (auto simp: latm M \<mu>\<^sub>C_cons)
next
  case (decide\<^sub>N\<^sub>O\<^sub>T L) note undef_L = this(1) and MC = this(2) and T = this(3)
  have incl: "atm_of ` lits_of (Marked L Level # (trail S)) \<subseteq> atms_of_m A"
    using dpll_bj_atms_in_trail_in_set bj_decide\<^sub>N\<^sub>O\<^sub>T decide\<^sub>N\<^sub>O\<^sub>T.decide\<^sub>N\<^sub>O\<^sub>T[OF decide\<^sub>N\<^sub>O\<^sub>T.hyps] NA MA MC
    by auto

  have no_dup: "no_dup (Marked L Level # (trail S))"
    using defined_lit_map n_d undef_L by auto
  obtain a b l where M: "get_all_marked_decomposition (trail S) = (a, b) # l"
    by (case_tac "get_all_marked_decomposition (trail S)") auto

  hence "length (Marked L Level # (trail S)) \<le> card (atms_of_m A)"
    using incl finite unfolding no_dup_length_eq_card_atm_of_lits_of[OF no_dup]
    by (simp add: card_mono)
  then have latm: "unassigned_lit A (trail S) = Suc (unassigned_lit A (Marked L lv # (trail S)))"
    by force
  show ?case using T by (simp add: latm \<mu>\<^sub>C_cons)
next
  case (backjump C F' K d F L C' T) note undef_L = this(4) and MC =this(1) and tr_S = this(3) and
    L = this(5) and T = this(8)
  have incl: "atm_of ` lits_of (Propagated L Proped # F) \<subseteq> atms_of_m A"
    using dpll_bj_atms_in_trail_in_set NA MA tr_S L by auto

  have no_dup: "no_dup (Propagated L Proped # F)"
    using defined_lit_map n_d undef_L tr_S by auto
  obtain a b l where M: "get_all_marked_decomposition (trail S) = (a, b) # l"
    by (cases "get_all_marked_decomposition (trail S)") auto
  have b_le_M: "length b \<le> length (trail S)"
    using get_all_marked_decomposition_decomp[of "trail S"] by (simp add: M)
  have fin_atms_A: "finite (atms_of_m A)" using finite by simp

  hence F_le_A: "length (Propagated L Proped # F) \<le>  card (atms_of_m A)"
    using incl finite unfolding no_dup_length_eq_card_atm_of_lits_of[OF no_dup]
    by (simp add: card_mono)
  have tr_S_le_A: "length (trail S) \<le>  (card (atms_of_m A))"
    using n_d MA by (metis fin_atms_A card_mono no_dup_length_eq_card_atm_of_lits_of)
  obtain a b l where F: "get_all_marked_decomposition F = (a, b) # l"
    by (cases "get_all_marked_decomposition F") auto
  hence "F = b @ a"
    using get_all_marked_decomposition_decomp[of "Propagated L Proped # F" a
      "Propagated L Proped # b"] by simp
  hence latm: "unassigned_lit A b = Suc (unassigned_lit A (Propagated L Proped # b))"
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
    using \<mu>\<^sub>C_bounded[of "rev rem" "card (atms_of_m A)+2" "unassigned_lit A l"] T
    by (simp add: rem \<mu>\<^sub>C_append \<mu>\<^sub>C_cons F tr_S)
qed

lemma dpll_bj_trail_mes_decreasing_prop:
  assumes dpll: "dpll_bj S T"  and inv: "inv S" and
  N_A: "atms_of_m (clauses S) \<subseteq> atms_of_m A" and
  M_A: "atm_of ` lits_of (trail S) \<subseteq> atms_of_m A" and
  nd: "no_dup (trail S)" and
  fin_A: "finite A"
  shows "(2+card (atms_of_m A)) ^ (1+card (atms_of_m A))
               - \<mu>\<^sub>C (1+card (atms_of_m A)) (2+card (atms_of_m A)) (trail_weight T)
            < (2+card (atms_of_m A)) ^ (1+card (atms_of_m A))
               - \<mu>\<^sub>C (1+card (atms_of_m A)) (2+card (atms_of_m A)) (trail_weight S)"
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
  have l_trail_weight_M: "length (trail_weight T) \<le> 1+card (atms_of_m A)"
     using l_M'_A length_get_all_marked_decomposition_length[of "trail T"] by auto
  have bounded_M: "\<forall>i<length (trail_weight T). (trail_weight T)! i < card (atms_of_m A) + 2"
    using length_in_get_all_marked_decomposition_bounded[of _ T] l_M'_A
    by (metis (no_types, lifting) Nat.le_trans One_nat_def Suc_1 add.right_neutral add_Suc_right
      le_imp_less_Suc less_eq_Suc_le nth_mem)

  from dpll_bj_trail_mes_increasing_prop[OF dpll inv N_A M_A nd fin_A]
  have "\<mu>\<^sub>C ?s ?b (trail_weight S) < \<mu>\<^sub>C ?s ?b (trail_weight T)" by simp
  moreover from \<mu>\<^sub>C_bounded[OF bounded_M l_trail_weight_M]
    have "\<mu>\<^sub>C ?s ?b (trail_weight T) \<le> ?b ^ ?s" by auto
  ultimately show ?thesis by linarith
qed

lemma dpll_bj_wf:
  assumes fin: "finite A"
  shows "wf {(T, S). dpll_bj S T
    \<and> atms_of_m (clauses S) \<subseteq> atms_of_m A \<and> atm_of ` lits_of (trail S) \<subseteq> atms_of_m A
    \<and> no_dup (trail S) \<and> inv S}"
  (is "wf ?A")
proof (rule wf_bounded_measure[of _
        "\<lambda>_. (2 + card (atms_of_m A))^(1 + card (atms_of_m A))"
        "\<lambda>S. \<mu>\<^sub>C (1+card (atms_of_m A)) (2+card (atms_of_m A)) (trail_weight S)"])
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
  have l_trail_weight_M: "length (trail_weight b) \<le> 1+card (atms_of_m A)"
     using l_M'_A length_get_all_marked_decomposition_length[of "trail b"] by auto
  have bounded_M: "\<forall>i<length (trail_weight b). (trail_weight b)! i < card (atms_of_m A) + 2"
    using length_in_get_all_marked_decomposition_bounded[of _ b] l_M'_A
    by (metis (no_types, lifting) Nat.le_trans One_nat_def Suc_1 add.right_neutral add_Suc_right
      le_imp_less_Suc less_eq_Suc_le nth_mem)

  from dpll_bj_trail_mes_increasing_prop[OF dpll_bj inv N_A M_A nd fin]
  have "\<mu>\<^sub>C ?s ?b (trail_weight a) < \<mu>\<^sub>C ?s ?b (trail_weight b)" by simp
  moreover from \<mu>\<^sub>C_bounded[OF bounded_M l_trail_weight_M]
    have "\<mu>\<^sub>C ?s ?b (trail_weight b) \<le> ?b ^ ?s" by auto
  ultimately show "?b ^ ?s \<le> ?b ^ ?s \<and>
           \<mu>\<^sub>C ?s ?b (trail_weight b) \<le> ?b ^ ?s \<and>
           \<mu>\<^sub>C ?s ?b (trail_weight a) < \<mu>\<^sub>C ?s ?b (trail_weight b)"
    by blast
qed

subsubsection \<open>Normal Forms\<close>

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
        using tot atms_of_s_def unfolding total_over_m_def total_over_set_def
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
          from bj_decide\<^sub>N\<^sub>O\<^sub>T[OF decide\<^sub>N\<^sub>O\<^sub>T[OF this]] show False
            using l_N n_s by (metis literal.sel(1) state_eq\<^sub>N\<^sub>O\<^sub>T_ref)
        qed

      have "?M \<Turnstile>as CNot C"
        by (metis atms_N_M \<open>C \<in> ?N\<close> \<open>\<not> ?M \<Turnstile>a C\<close> all_variables_defined_not_imply_cnot
          atms_of_atms_of_m_mono atms_of_m_CNot_atms_of atms_of_m_CNot_atms_of_m subsetCE)
      have "\<exists>l \<in> set ?M. is_marked l"
        proof (rule ccontr)
          let ?O = "{{#lit_of L#} |L. is_marked L \<and> L \<in> set ?M \<and> atm_of (lit_of L) \<notin> atms_of_m ?N}"
          have \<theta>[iff]: "\<And>I. total_over_m I (?N \<union> ?O \<union> (\<lambda>a. {#lit_of a#}) ` set ?M)
            \<longleftrightarrow> total_over_m I (?N \<union>(\<lambda>a. {#lit_of a#}) ` set ?M)"
            unfolding total_over_set_def total_over_m_def atms_of_m_def by auto
          assume "\<not> ?thesis"
          hence [simp]:"{{#lit_of L#} |L. is_marked L \<and> L \<in> set ?M}
            = {{#lit_of L#} |L. is_marked L \<and> L \<in> set ?M \<and> atm_of (lit_of L) \<notin> atms_of_m ?N}"
            by auto
          hence "?N \<union> ?O \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set ?M"
            using all_decomposition_implies_propagated_lits_are_implied[OF decomp] by auto

          hence "?I \<Turnstile>s (\<lambda>a. {#lit_of a#}) ` set ?M"
            using cons_I' I'_N tot_I' \<open>?I \<Turnstile>s ?N \<union> ?O\<close> unfolding \<theta> true_clss_clss_def by blast
          hence "lits_of ?M \<subseteq> ?I"
            unfolding true_clss_def lits_of_def by auto
          hence "?M \<Turnstile>as ?N"
            using I'_N \<open>C \<in> ?N\<close> \<open>\<not> ?M \<Turnstile>a C\<close> cons_I' atms_N_M
            by (meson \<open>trail S \<Turnstile>as CNot C\<close> consistent_CNot_not rev_subsetD sup_ge1 true_annot_def
              true_annots_def true_cls_mono_set_mset_l true_clss_def)
          thus False using M by fast
        qed
      from List.split_list_first_propE[OF this] obtain K :: "'v literal" and d :: dpll_marked_level and
        F F' :: "('v, dpll_marked_level, dpll_mark) marked_lit list" where
        M_K: "?M = F' @ Marked K d # F" and
        nm: "\<forall>f\<in>set F'. \<not>is_marked f"
        unfolding is_marked_def by metis
      let ?K = "Marked K d::('v, dpll_marked_level, dpll_mark) marked_lit"
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
            { fix x :: "('v, dpll_marked_level, dpll_mark) marked_lit"
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
          \<open>C\<in>?N\<close> n_s \<open>?M \<Turnstile>as CNot C\<close> bj_backjump inv unfolding M_K  by (auto intro: bj_backjump)
        thus ?thesis by fast
    qed auto
qed

end

locale dpll_with_backjumping =
  dpll_with_backjumping_ops trail clauses update_trail update_cls propagate_conds inv backjump_conds
  for
    trail :: "'st \<Rightarrow> ('v, dpll_marked_level, dpll_mark) annoted_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    update_trail :: "('v, dpll_marked_level, dpll_mark) annoted_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_cls :: "'v clause set \<Rightarrow> 'st \<Rightarrow> 'st" and
    propagate_conds :: "'st \<Rightarrow> bool" and
    inv :: "'st \<Rightarrow> bool" and
    backjump_conds :: "'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool"
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

lemma tranclp_dpll_bj_trail_mes_decreasing_prop:
  assumes dpll: "dpll_bj\<^sup>+\<^sup>+ S T"  and inv: "inv S" and
  N_A: "atms_of_m (clauses S) \<subseteq> atms_of_m A" and
  M_A: "atm_of ` lits_of (trail S) \<subseteq> atms_of_m A" and
  n_d: "no_dup (trail S)" and
  fin_A: "finite A"
  shows "(2+card (atms_of_m A)) ^ (1+card (atms_of_m A))
               - \<mu>\<^sub>C (1+card (atms_of_m A)) (2+card (atms_of_m A)) (trail_weight T)
            < (2+card (atms_of_m A)) ^ (1+card (atms_of_m A))
               - \<mu>\<^sub>C (1+card (atms_of_m A)) (2+card (atms_of_m A)) (trail_weight S)"
  using dpll
proof (induction)
  case base
  thus ?case
    using N_A M_A n_d dpll_bj_trail_mes_decreasing_prop fin_A inv by blast
next
  case (step T U) note st = this(1) and dpll = this(2) and IH = this(3)
  have " atms_of_m (clauses S) = atms_of_m (clauses T)"
    using rtranclp_dpll_bj_atms_of_m_clauses_inv by (metis dpll_bj_clauses dpll_bj_inv inv st
      tranclpD)
  hence N_A': "atms_of_m (clauses T) \<subseteq> atms_of_m A"
     using N_A by auto
  moreover have M_A': "atm_of ` lits_of (trail T) \<subseteq> atms_of_m A"
    by (meson M_A N_A inv rtranclp_dpll_bj_atms_in_trail_in_set st dpll
      tranclp.r_into_trancl tranclp_into_rtranclp tranclp_trans)
  moreover have nd: "no_dup (trail T)"
    by (metis inv n_d rtranclp_dpll_bj_no_dup st tranclp_into_rtranclp)
  moreover have "inv T"
    by (meson dpll dpll_bj_inv inv rtranclp_dpll_bj_inv st tranclp_into_rtranclp)
  ultimately show ?case
    using IH dpll_bj_trail_mes_decreasing_prop[of T U A] dpll fin_A by linarith
qed

end

subsection \<open>CDCL\<close>
locale learn_ops =
  dpll_state trail clauses update_trail update_cls
  for
    trail :: "'st \<Rightarrow> ('v, dpll_marked_level, dpll_mark) annoted_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    update_trail :: "('v, dpll_marked_level, dpll_mark) annoted_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_cls :: "'v clause set \<Rightarrow> 'st \<Rightarrow> 'st" +
  fixes
    learn_cond :: "'v clause \<Rightarrow> 'st \<Rightarrow> bool"

begin
inductive learn :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
"clauses S \<Turnstile>p C \<Longrightarrow> atms_of C \<subseteq> atms_of_m (clauses S) \<union> atm_of ` (lits_of (trail S))
  \<Longrightarrow> learn_cond C S
  \<Longrightarrow> T \<sim> add_cls\<^sub>N\<^sub>O\<^sub>T C S
  \<Longrightarrow> learn S T"
inductive_cases learnE: "learn S T"

lemma learn_\<mu>\<^sub>C_stable:
  assumes "learn S T"
  shows "\<mu>\<^sub>C A B (trail_weight S) = \<mu>\<^sub>C A B (trail_weight T)"
  using assms by (auto elim: learnE)

end

locale forget_ops =
  dpll_state trail clauses update_trail update_cls
  for
    trail :: "'st \<Rightarrow> ('v, dpll_marked_level, dpll_mark) annoted_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    update_trail :: "('v, dpll_marked_level, dpll_mark) annoted_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_cls :: "'v clause set \<Rightarrow> 'st \<Rightarrow> 'st" +
  fixes
    forget_cond :: "'v clause \<Rightarrow> 'st \<Rightarrow> bool"
begin
inductive forget\<^sub>N\<^sub>O\<^sub>T :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
forget\<^sub>N\<^sub>O\<^sub>T:"clauses S - {C} \<Turnstile>p C \<Longrightarrow> forget_cond C S \<Longrightarrow> C \<in> clauses S
  \<Longrightarrow> T \<sim> remove_cls\<^sub>N\<^sub>O\<^sub>T C S
  \<Longrightarrow> forget\<^sub>N\<^sub>O\<^sub>T S T"
inductive_cases forgetE: "forget\<^sub>N\<^sub>O\<^sub>T S T"

lemma forget_\<mu>\<^sub>C_stable:
  assumes "forget\<^sub>N\<^sub>O\<^sub>T S T"
  shows "\<mu>\<^sub>C A B (trail_weight S) = \<mu>\<^sub>C A B (trail_weight T)"
  using assms by (auto elim!: forgetE)

end

locale learn_and_forget\<^sub>N\<^sub>O\<^sub>T =
  learn_ops trail clauses update_trail update_cls learn_cond +
  forget_ops trail clauses update_trail update_cls forget_cond
  for
    trail :: "'st \<Rightarrow> ('v, dpll_marked_level, dpll_mark) annoted_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    update_trail :: "('v, dpll_marked_level, dpll_mark) annoted_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_cls :: "'v clause set \<Rightarrow> 'st \<Rightarrow> 'st" and
    learn_cond forget_cond :: "'v clause \<Rightarrow> 'st \<Rightarrow> bool"
begin
inductive learn_and_forget\<^sub>N\<^sub>O\<^sub>T :: "'st \<Rightarrow> 'st \<Rightarrow> bool"
where
lf_learn: "learn S T \<Longrightarrow> learn_and_forget\<^sub>N\<^sub>O\<^sub>T S T" |
lf_forget: "forget\<^sub>N\<^sub>O\<^sub>T S T \<Longrightarrow> learn_and_forget\<^sub>N\<^sub>O\<^sub>T S T"
end

locale conflict_driven_clause_learning_ops =
  dpll_with_backjumping_ops trail clauses update_trail update_cls propagate_conds inv backjump_conds +
  learn_and_forget\<^sub>N\<^sub>O\<^sub>T trail clauses update_trail update_cls learn_cond forget_cond
    for
      trail :: "'st \<Rightarrow> ('v, dpll_marked_level, dpll_mark) annoted_lits" and
      clauses :: "'st \<Rightarrow> 'v clauses" and
      update_trail :: "('v, dpll_marked_level, dpll_mark) annoted_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
      update_cls :: "'v clause set \<Rightarrow> 'st \<Rightarrow> 'st" and
      propagate_conds ::  "'st \<Rightarrow> bool" and
      inv :: "'st \<Rightarrow> bool" and
      backjump_conds ::  "'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool" and
      learn_cond forget_cond :: "'v clause \<Rightarrow> 'st \<Rightarrow> bool"
begin

inductive cdcl\<^sub>N\<^sub>O\<^sub>T:: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
c_dpll_bj: "dpll_bj S S' \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T S S'" |
c_learn: "learn S S' \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T S S'" |
c_forget\<^sub>N\<^sub>O\<^sub>T: "forget\<^sub>N\<^sub>O\<^sub>T S S' \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T S S'"

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_all_induct[consumes 1, case_names dpll_bj learn forget\<^sub>N\<^sub>O\<^sub>T]:
  fixes S T :: "'st"
  assumes "cdcl\<^sub>N\<^sub>O\<^sub>T S T" and
    dpll: "\<And>S T. dpll_bj S T \<Longrightarrow> P S T" and
    learning:
      "\<And>S C T. clauses S \<Turnstile>p C \<Longrightarrow> atms_of C \<subseteq> atms_of_m (clauses S) \<union> atm_of ` (lits_of (trail S))
      \<Longrightarrow> T \<sim> add_cls\<^sub>N\<^sub>O\<^sub>T C S
      \<Longrightarrow> P S T" and
    forgetting: "\<And>S C T. clauses S - {C} \<Turnstile>p C \<Longrightarrow> C \<in> clauses S \<Longrightarrow> T \<sim> remove_cls\<^sub>N\<^sub>O\<^sub>T C S
    \<Longrightarrow> P S T"
  shows "P S T"
  using assms(1) by (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T.induct)
    (blast intro: assms(2, 3, 4) elim!: learnE forgetE)+

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup:
  assumes "cdcl\<^sub>N\<^sub>O\<^sub>T S T" and "inv S"
  and "no_dup (trail S)"
  shows "no_dup (trail T)"
  using assms by (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_all_induct) (auto intro: dpll_bj_no_dup)

paragraph \<open>Consistency of the trail\<close>
lemma cdcl\<^sub>N\<^sub>O\<^sub>T_consistent:
  assumes "cdcl\<^sub>N\<^sub>O\<^sub>T S T" and "inv S"
  and "no_dup (trail S)"
  shows "consistent_interp (lits_of (trail T))"
  using cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup[OF assms] distinctconsistent_interp by fast

text \<open>The subtle problem here is that tautologies can be removed, meaning that some variable can
  disappear of the problem. It is also possible that some variable of the trail are not in the
  clauses anymore.\<close>
lemma cdcl\<^sub>N\<^sub>O\<^sub>T_atms_of_m_clauses_decreasing:
  assumes "cdcl\<^sub>N\<^sub>O\<^sub>T S T"and "inv S"
  shows "atms_of_m (clauses T) \<subseteq> atms_of_m (clauses S) \<union> atm_of ` (lits_of (trail S))"
  using assms by (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_all_induct)
    (auto dest!: dpll_bj_atms_of_m_clauses_inv set_mp simp add: atms_of_m_def Union_eq)

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_atms_in_trail:
  assumes "cdcl\<^sub>N\<^sub>O\<^sub>T S T"and "inv S"
  and "atm_of ` (lits_of (trail S)) \<subseteq> atms_of_m (clauses S)"
  shows "atm_of ` (lits_of (trail T)) \<subseteq> atms_of_m (clauses S)"
  using assms by (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_all_induct) (auto simp add: dpll_bj_atms_in_trail)

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_atms_in_trail_in_set:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T S T" and "inv S" and
    "atms_of_m (clauses S) \<subseteq> A" and
    "atm_of ` (lits_of (trail S)) \<subseteq> A"
  shows "atm_of ` (lits_of (trail T)) \<subseteq> A"
  using assms
  by (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_all_induct)
     (simp_all add: dpll_bj_atms_in_trail_in_set dpll_bj_atms_of_m_clauses_inv)

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_finite_clauses:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T S T" and "inv S" and
    "finite(clauses S)"
  shows "finite(clauses T)"
  using assms
  by (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_all_induct)
     (simp_all add: dpll_bj_atms_in_trail_in_set dpll_bj_atms_of_m_clauses_inv dpll_bj_clauses)

(* TODO Move *)
lemma true_clss_clss_generalise_true_clss_clss:
  "A \<union> C \<Turnstile>ps D \<Longrightarrow> B \<Turnstile>ps C \<Longrightarrow> A \<union> B \<Turnstile>ps D"
proof -
  assume a1: "A \<union> C \<Turnstile>ps D"
  assume "B \<Turnstile>ps C"
  then have f2: "\<And>M. M \<union> B \<Turnstile>ps C"
    by (meson true_clss_clss_union_l_r)
  have "\<And>M. C \<union> (M \<union> A) \<Turnstile>ps D"
    using a1 by (simp add: Un_commute sup_left_commute)
  then show ?thesis
    using f2 by (metis (no_types) Un_commute true_clss_clss_left_right true_clss_clss_union_and)
qed

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_all_decomposition_implies:
  assumes "cdcl\<^sub>N\<^sub>O\<^sub>T S T" and "inv S" and
    "all_decomposition_implies (clauses S) (get_all_marked_decomposition (trail S))"
  shows
    "all_decomposition_implies (clauses T) (get_all_marked_decomposition (trail T))"
  using assms
proof (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_all_induct)
  case dpll_bj
  then show ?case
     using dpll_bj_all_decomposition_implies_inv by blast
next
  case learn
  then show ?case by (auto simp add: all_decomposition_implies_def)
next
  case forget\<^sub>N\<^sub>O\<^sub>T
  moreover
    { fix S :: 'st and C :: "'v literal multiset" and T :: 'st and
        M :: "('v, dpll_marked_level, dpll_mark) marked_lit list" and
        M' :: "('v, dpll_marked_level, dpll_mark) marked_lit list"
      assume a1: "clauses S - {C} \<Turnstile>p C"
      assume a2: "\<forall>x\<in>set (get_all_marked_decomposition (trail S)). case x of (Ls, seen)
        \<Rightarrow> (\<lambda>a. {#lit_of a#}) ` set Ls \<union> clauses S \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set seen"
      assume "(M, M') \<in> set (get_all_marked_decomposition (trail S))"
      then have f3: "(\<lambda>m. {#lit_of m#}) ` set M \<union> clauses S \<Turnstile>ps (\<lambda>m. {#lit_of m#}) ` set M'"
        using a2 by fastforce
      have "clauses S - {C} \<union> {C} \<Turnstile>ps clauses S"
        by (metis (no_types) Un_Diff_cancel Un_commute union_trus_clss_clss)
      then have "(\<lambda>m. {#lit_of m#}) ` set M \<union> (clauses S - {C}) \<Turnstile>ps (\<lambda>m. {#lit_of m#}) ` set M'"
        using f3 a1 by (metis (no_types) Un_absorb
          true_clss_clss_generalise_true_clss_clss true_clss_clss_true_clss_cls)
    }
  ultimately show ?case
    by (auto simp add: all_decomposition_implies_def)
qed

paragraph \<open>Extension of models\<close>
lemma cdcl\<^sub>N\<^sub>O\<^sub>T_bj_sat_ext_iff:
  assumes "cdcl\<^sub>N\<^sub>O\<^sub>T S T"and "inv S"
  shows "I\<Turnstile>sext clauses S \<longleftrightarrow> I\<Turnstile>sext clauses T"
  using assms
proof (induction rule:cdcl\<^sub>N\<^sub>O\<^sub>T_all_induct)
  case dpll_bj
  thus ?case by (simp add: dpll_bj_clauses)
next
  case (learn S C T) note T = this(3)
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
  hence H: "I \<Turnstile>sext (clauses S) \<Longrightarrow> I \<Turnstile>sext insert C (clauses S)"
    unfolding true_clss_ext_def by auto
  show ?case
    apply standard
      using T apply (simp add: H)
    by (metis Diff_insert_absorb T clauses_add_cls\<^sub>N\<^sub>O\<^sub>T insert_subset state_eq\<^sub>N\<^sub>O\<^sub>T_def subsetI
      subset_antisym true_clss_ext_decrease_right_remove_r)
next
  case (forget\<^sub>N\<^sub>O\<^sub>T S C T) note T = this(3)
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
  show ?case using T by (auto simp: true_clss_ext_decrease_right_remove_r H)
qed

end \<comment> \<open>end of \<open>conflict_driven_clause_learning_ops\<close>\<close>

locale conflict_driven_clause_learning =
  conflict_driven_clause_learning_ops +
  assumes cdcl\<^sub>N\<^sub>O\<^sub>T_inv: "\<And>S T. cdcl\<^sub>N\<^sub>O\<^sub>T S T \<Longrightarrow> inv S \<Longrightarrow> inv T"
begin
sublocale dpll_with_backjumping
  apply unfold_locales
  using cdcl\<^sub>N\<^sub>O\<^sub>T.simps cdcl\<^sub>N\<^sub>O\<^sub>T_inv by auto

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_inv:
  "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T \<Longrightarrow> inv S \<Longrightarrow> inv T"
  by (induction rule: rtranclp.induct) (auto simp add: cdcl\<^sub>N\<^sub>O\<^sub>T_inv)

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_trail_clauses_bound:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T" and
    "inv S" and
    "atms_of_m (clauses S) \<subseteq> A" and
    "atm_of `(lits_of (trail S)) \<subseteq> A"
  shows "atm_of `(lits_of (trail T)) \<subseteq> A \<and> atms_of_m (clauses T) \<subseteq>  A"
  using assms
proof (induction rule: rtranclp_induct)
  case base
  thus ?case by simp
next
  case (step T U) note st =this(1) and cdcl\<^sub>N\<^sub>O\<^sub>T = this(2) and IH = this(3)[OF this(4-6)] and
    inv = this(4) and atms_clauses_S = this(5) and atms_trail_S = this(6)
  have "inv T" using inv st rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_inv by blast
  hence "atms_of_m (clauses U) \<subseteq> A"
    using cdcl\<^sub>N\<^sub>O\<^sub>T_atms_of_m_clauses_decreasing[OF cdcl\<^sub>N\<^sub>O\<^sub>T] IH by auto
  moreover have "atm_of `(lits_of (trail U)) \<subseteq> A"
    by (meson IH \<open>inv T\<close> cdcl\<^sub>N\<^sub>O\<^sub>T cdcl\<^sub>N\<^sub>O\<^sub>T_atms_in_trail_in_set)
  ultimately show ?case by fast
qed

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup:
  assumes "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T" and "inv S"
  and "no_dup (trail S)"
  shows "no_dup (trail T)"
  using assms by (induction rule: rtranclp_induct) (auto intro: cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_inv)

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_finite_clauses:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T" and "inv S" and
    "finite(clauses S)"
  shows "finite(clauses T)"
  using assms
  by (induction rule: rtranclp_induct) (auto intro: cdcl\<^sub>N\<^sub>O\<^sub>T_finite_clauses rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_inv)

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_all_decomposition_implies:
  assumes "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T" and "inv S" and
    "all_decomposition_implies (clauses S) (get_all_marked_decomposition (trail S))"
  shows
    "all_decomposition_implies (clauses T) (get_all_marked_decomposition (trail T))"
  using assms by (induction) (auto intro: rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_inv cdcl\<^sub>N\<^sub>O\<^sub>T_all_decomposition_implies)

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_bj_sat_ext_iff:
  assumes "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T"and "inv S"
  shows "I\<Turnstile>sext clauses S \<longleftrightarrow> I\<Turnstile>sext clauses T"
  using assms apply (induction rule: rtranclp_induct)
  using cdcl\<^sub>N\<^sub>O\<^sub>T_bj_sat_ext_iff by (auto intro: rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_inv)

definition cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv where
"cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv A S \<longleftrightarrow> (finite A \<and> inv S \<and> atms_of_m (clauses S) \<subseteq> atms_of_m A
    \<and> atm_of ` lits_of (trail S) \<subseteq> atms_of_m A \<and> no_dup (trail S))"

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv:
  assumes "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T" and "cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv A S"
  shows "cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv A T"
  using assms unfolding cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv_def
  by (simp add: rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_inv rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_trail_clauses_bound)

abbreviation learn_or_forget where
"learn_or_forget S T \<equiv> (\<lambda>S T. learn S T \<or> forget\<^sub>N\<^sub>O\<^sub>T S T) S T"

lemma rtranclp_learn_or_forget_cdcl\<^sub>N\<^sub>O\<^sub>T:
  "learn_or_forget\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T"
  using rtranclp_mono[of learn_or_forget cdcl\<^sub>N\<^sub>O\<^sub>T] cdcl\<^sub>N\<^sub>O\<^sub>T.c_learn cdcl\<^sub>N\<^sub>O\<^sub>T.c_forget\<^sub>N\<^sub>O\<^sub>T by blast

lemma learn_or_forget_dpll_\<mu>\<^sub>C:
  assumes
    l_f: "learn_or_forget\<^sup>*\<^sup>* S T" and
    dpll: "dpll_bj T U" and
    inv: "cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv A S"
  shows "(2+card (atms_of_m A)) ^ (1+card (atms_of_m A))
      - \<mu>\<^sub>C (1+card (atms_of_m A)) (2+card (atms_of_m A)) (trail_weight U)
    <  (2+card (atms_of_m A)) ^ (1+card (atms_of_m A))
      - \<mu>\<^sub>C (1+card (atms_of_m A)) (2+card (atms_of_m A)) (trail_weight S)"
     (is "?\<mu> U < ?\<mu> S")
proof -
  have "?\<mu> S = ?\<mu> T"
    using l_f apply (induction)
     apply simp
    using forget_\<mu>\<^sub>C_stable learn_\<mu>\<^sub>C_stable by presburger
  moreover have "cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv A T"
     using rtranclp_learn_or_forget_cdcl\<^sub>N\<^sub>O\<^sub>T  cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv  l_f inv by blast
  ultimately show ?thesis
    using dpll_bj_trail_mes_decreasing_prop[of T U A, OF dpll] finite
    unfolding cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv_def by linarith
qed

lemma infinite_cdcl\<^sub>N\<^sub>O\<^sub>T_exists_learn_and_forget_infinite_chain:
  assumes
    "\<And>i. cdcl\<^sub>N\<^sub>O\<^sub>T (f i) (f(Suc i))" and
    inv: "cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv A (f 0)"
  shows "\<exists>j. \<forall>i\<ge>j. learn_or_forget (f i) (f (Suc i))"
  using assms
proof (induction "(2+card (atms_of_m A)) ^ (1+card (atms_of_m A))
    - \<mu>\<^sub>C (1+card (atms_of_m A)) (2+card (atms_of_m A)) (trail_weight (f 0))"
    arbitrary: f
    rule: nat_less_induct_case)
  case (Suc n) note IH = this(1) and \<mu> = this(2) and cdcl\<^sub>N\<^sub>O\<^sub>T = this(3) and inv = this(4)
  consider
      (dpll_end) "\<exists>j. \<forall>i\<ge>j. learn_or_forget (f i) (f (Suc i))"
    | (dpll_more) "\<not>(\<exists>j. \<forall>i\<ge>j. learn_or_forget (f i) (f (Suc i)))"
    by blast
  thus ?case
    proof cases
      case dpll_end
      thus ?thesis by auto
    next
      case dpll_more
      then have j: "\<exists>i. \<not> learn (f i) (f (Suc i)) \<and> \<not>forget\<^sub>N\<^sub>O\<^sub>T (f i) (f (Suc i))"
        by blast
      obtain i where
        "\<not>learn (f i) (f (Suc i)) \<and> \<not>forget\<^sub>N\<^sub>O\<^sub>T (f i) (f (Suc i))" and
        "\<forall>k<i. learn_or_forget (f k) (f (Suc k))"
        proof -
          obtain i\<^sub>0 where "\<not> learn (f i\<^sub>0) (f (Suc i\<^sub>0)) \<and> \<not>forget\<^sub>N\<^sub>O\<^sub>T (f i\<^sub>0) (f (Suc i\<^sub>0))"
            using j by auto
          hence "{i. i\<le>i\<^sub>0 \<and>  \<not> learn (f i) (f (Suc i)) \<and> \<not>forget\<^sub>N\<^sub>O\<^sub>T (f i) (f (Suc i))} \<noteq> {}"
            by auto
          let ?I = "{i. i\<le>i\<^sub>0 \<and>  \<not> learn (f i) (f (Suc i)) \<and> \<not>forget\<^sub>N\<^sub>O\<^sub>T (f i) (f (Suc i))}"
          let ?i = "Min ?I"
          have "finite ?I"
            by auto
          have "\<not> learn (f ?i) (f (Suc ?i)) \<and> \<not>forget\<^sub>N\<^sub>O\<^sub>T (f ?i) (f (Suc ?i))"
            using Min_in[OF \<open>finite ?I\<close> \<open>?I \<noteq> {}\<close>] by auto
          moreover have "\<forall>k<?i. learn_or_forget (f k) (f (Suc k))"
            by (smt Min.coboundedI \<open>finite ?I\<close> \<open>?I \<noteq> {}\<close> dual_order.trans infinite_growing
              less_or_eq_imp_le mem_Collect_eq not_le)
          ultimately show ?thesis using that by blast
        qed
      def g \<equiv> "\<lambda>n. f (n + Suc i)"
      have "dpll_bj (f i) (g 0)"
        using \<open>\<not> learn (f i) (f (Suc i)) \<and> \<not> forget\<^sub>N\<^sub>O\<^sub>T (f i) (f (Suc i))\<close> cdcl\<^sub>N\<^sub>O\<^sub>T cdcl\<^sub>N\<^sub>O\<^sub>T.cases g_def
        by auto
      {
        fix j
        assume "j \<le> i"
        then have "learn_or_forget\<^sup>*\<^sup>* (f 0) (f j)"
          apply (induction j)
           apply simp
          by (metis (no_types, lifting) Suc_leD Suc_le_lessD rtranclp.simps
            \<open>\<forall>k<i. learn (f k) (f (Suc k)) \<or> forget\<^sub>N\<^sub>O\<^sub>T (f k) (f (Suc k))\<close>)
      }
      hence "learn_or_forget\<^sup>*\<^sup>* (f 0) (f i)" by blast
      hence "(2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A))
           - \<mu>\<^sub>C (1 + card (atms_of_m A)) (2 + card (atms_of_m A)) (trail_weight (g 0))
        < (2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A))
          - \<mu>\<^sub>C (1 + card (atms_of_m A)) (2 + card (atms_of_m A)) (trail_weight (f 0))"
        using learn_or_forget_dpll_\<mu>\<^sub>C[of "f 0" "f i" "g 0" A] inv \<open>dpll_bj (f i) (g 0)\<close>
        unfolding cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv_def by linarith

      moreover have cdcl\<^sub>N\<^sub>O\<^sub>T_i: "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* (f 0) (g 0)"
        using rtranclp_learn_or_forget_cdcl\<^sub>N\<^sub>O\<^sub>T[of "f 0" "f i"] \<open>learn_or_forget\<^sup>*\<^sup>* (f 0) (f i)\<close>
        cdcl\<^sub>N\<^sub>O\<^sub>T[of i] unfolding g_def by auto
      moreover have "\<And>i. cdcl\<^sub>N\<^sub>O\<^sub>T (g  i) (g (Suc i))"
        using cdcl\<^sub>N\<^sub>O\<^sub>T g_def by auto
      moreover have "cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv A (g 0)"
        using inv cdcl\<^sub>N\<^sub>O\<^sub>T_i rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_trail_clauses_bound g_def cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv by auto
      ultimately obtain j where j: "\<And>i. i\<ge>j \<Longrightarrow> learn_or_forget (g i) (g (Suc i))"
        using IH unfolding \<mu>[symmetric] by presburger
      show ?thesis
        proof
          {
            fix k
            assume "k \<ge> j + Suc i"
            hence "learn_or_forget (f k) (f (Suc k))"
              using j[of "k-Suc i"] unfolding g_def by auto
          }
          thus "\<forall>k\<ge>j+Suc i. learn_or_forget (f k) (f (Suc k))"
            by auto
        qed
    qed
next
  case 0 note H = this(1) and cdcl\<^sub>N\<^sub>O\<^sub>T = this(2) and inv = this(3)
  show ?case
    proof (rule ccontr)
      assume "\<not> ?case"
      then have j: "\<exists>i. \<not> learn (f i) (f (Suc i)) \<and> \<not>forget\<^sub>N\<^sub>O\<^sub>T (f i) (f (Suc i))"
        by blast
      obtain i where
        "\<not>learn (f i) (f (Suc i)) \<and> \<not>forget\<^sub>N\<^sub>O\<^sub>T (f i) (f (Suc i))" and
        "\<forall>k<i. learn_or_forget (f k) (f (Suc k))"
        proof -
          obtain i\<^sub>0 where "\<not> learn (f i\<^sub>0) (f (Suc i\<^sub>0)) \<and> \<not>forget\<^sub>N\<^sub>O\<^sub>T (f i\<^sub>0) (f (Suc i\<^sub>0))"
            using j by auto
          hence "{i. i\<le>i\<^sub>0 \<and>  \<not> learn (f i) (f (Suc i)) \<and> \<not>forget\<^sub>N\<^sub>O\<^sub>T (f i) (f (Suc i))} \<noteq> {}"
            by auto
          let ?I = "{i. i\<le>i\<^sub>0 \<and>  \<not> learn (f i) (f (Suc i)) \<and> \<not>forget\<^sub>N\<^sub>O\<^sub>T (f i) (f (Suc i))}"
          let ?i = "Min ?I"
          have "finite ?I"
            by auto
          have "\<not> learn (f ?i) (f (Suc ?i)) \<and> \<not>forget\<^sub>N\<^sub>O\<^sub>T (f ?i) (f (Suc ?i))"
            using Min_in[OF \<open>finite ?I\<close> \<open>?I \<noteq> {}\<close>] by auto
          moreover have "\<forall>k<?i. learn_or_forget (f k) (f (Suc k))"
            by (smt Min.coboundedI \<open>finite ?I\<close> \<open>?I \<noteq> {}\<close> dual_order.trans infinite_growing
              less_or_eq_imp_le mem_Collect_eq not_le)
          ultimately show ?thesis using that by blast
        qed
      have "dpll_bj (f i) (f (Suc i))"
        using \<open>\<not> learn (f i) (f (Suc i)) \<and> \<not> forget\<^sub>N\<^sub>O\<^sub>T (f i) (f (Suc i))\<close> cdcl\<^sub>N\<^sub>O\<^sub>T cdcl\<^sub>N\<^sub>O\<^sub>T.cases
        by blast
      {
        fix j
        assume "j \<le> i"
        then have "learn_or_forget\<^sup>*\<^sup>* (f 0) (f j)"
          apply (induction j)
           apply simp
          by (metis (no_types, lifting) Suc_leD Suc_le_lessD rtranclp.simps
            \<open>\<forall>k<i. learn (f k) (f (Suc k)) \<or> forget\<^sub>N\<^sub>O\<^sub>T (f k) (f (Suc k))\<close>)
      }
      hence "learn_or_forget\<^sup>*\<^sup>* (f 0) (f i)" by blast

      thus False
        using learn_or_forget_dpll_\<mu>\<^sub>C[of "f 0" "f i" "f (Suc i)" A] inv  0
        \<open>dpll_bj (f i) (f (Suc i))\<close> unfolding cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv_def by linarith
    qed
qed

lemma wf_cdcl\<^sub>N\<^sub>O\<^sub>T_no_learn_and_forget_infinite_chain:
  assumes
    no_infinite_lf: "\<And>f j. \<not> (\<forall>i\<ge>j. learn_or_forget (f i) (f (Suc i)))"
  shows "wf {(T, S). cdcl\<^sub>N\<^sub>O\<^sub>T S T \<and> cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv A S}" (is "wf {(T, S). cdcl\<^sub>N\<^sub>O\<^sub>T S T
        \<and> ?inv S}")
  unfolding wf_iff_no_infinite_down_chain
proof (rule ccontr)
  assume "\<not> \<not> (\<exists>f. \<forall>i. (f (Suc i), f i) \<in> {(T, S). cdcl\<^sub>N\<^sub>O\<^sub>T S T \<and> ?inv S})"
  then obtain f where
    "\<forall>i. cdcl\<^sub>N\<^sub>O\<^sub>T (f i) (f (Suc i)) \<and> ?inv (f i)"
    by fast
  hence "\<exists>j. \<forall>i\<ge>j. learn_or_forget (f i) (f (Suc i))"
   using infinite_cdcl\<^sub>N\<^sub>O\<^sub>T_exists_learn_and_forget_infinite_chain[of f] by meson
  then show False using no_infinite_lf by blast
qed

lemma inv_and_tranclp_cdcl_\<^sub>N\<^sub>O\<^sub>T_tranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_and_inv:
  "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>+\<^sup>+ S T \<and> cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv A S \<longleftrightarrow> (\<lambda>S T. cdcl\<^sub>N\<^sub>O\<^sub>T S T \<and> cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv A S)\<^sup>+\<^sup>+ S T"
  (is "?A \<and> ?I \<longleftrightarrow> ?B")
proof
  assume "?A \<and> ?I"
  then have ?A and ?I by blast+
  then show ?B
    apply induction
      apply (simp add: tranclp.r_into_trancl)
    by (metis (no_types, lifting) cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv tranclp.simps tranclp_into_rtranclp)
next
  assume ?B
  then have "?A" by induction auto
  moreover have ?I using \<open>?B\<close> tranclpD by fastforce
  ultimately show "?A \<and> ?I" by blast
qed

lemma wf_tranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_no_learn_and_forget_infinite_chain:
  assumes
    no_infinite_lf: "\<And>f j. \<not> (\<forall>i\<ge>j. learn_or_forget (f i) (f (Suc i)))"
  shows "wf {(T, S). cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>+\<^sup>+ S T \<and> cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv A S}"
  using wf_trancl[OF wf_cdcl\<^sub>N\<^sub>O\<^sub>T_no_learn_and_forget_infinite_chain[OF no_infinite_lf]]
  apply (rule wf_subset)
  by (auto simp: trancl_set_tranclp inv_and_tranclp_cdcl_\<^sub>N\<^sub>O\<^sub>T_tranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_and_inv)

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_normal_forms:
  assumes
    n_s: "no_step cdcl\<^sub>N\<^sub>O\<^sub>T S" and
    inv: "cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv A S" and
    decomp: "all_decomposition_implies (clauses S) (get_all_marked_decomposition (trail S))"
  shows "unsatisfiable (clauses S) \<or> (trail S \<Turnstile>as clauses S \<and> satisfiable (clauses S))"
proof -
  have n_s': "no_step dpll_bj S"
    using n_s by (auto simp: cdcl\<^sub>N\<^sub>O\<^sub>T.simps)
  show ?thesis
    apply (rule dpll_backjump_normal_forms[of S A])
    using inv decomp n_s' unfolding cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv_def by auto
qed

lemma full0_cdcl\<^sub>N\<^sub>O\<^sub>T_normal_forms:
  assumes
    full: "full0 cdcl\<^sub>N\<^sub>O\<^sub>T S T" and
    inv: "cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv A S" and
    n_d: "no_dup (trail S)" and
    decomp: "all_decomposition_implies (clauses S) (get_all_marked_decomposition (trail S))"
  shows "unsatisfiable (clauses T) \<or> (trail T \<Turnstile>as clauses T \<and> satisfiable (clauses T))"
proof -
  have st: "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T" and n_s: "no_step cdcl\<^sub>N\<^sub>O\<^sub>T T"
    using full unfolding full0_def by blast+
  have n_s': "cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv A T"
    using cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv inv st by blast
  moreover have "all_decomposition_implies (clauses T) (get_all_marked_decomposition (trail T))"
    using cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv_def decomp inv rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_all_decomposition_implies st by auto
  ultimately show ?thesis
    using cdcl\<^sub>N\<^sub>O\<^sub>T_normal_forms n_s by blast
qed

end \<comment> \<open>end of \<open>conflict_driven_clause_learning\<close>\<close>

subsubsection \<open>Restricting restarts\<close>

locale conflict_driven_clause_learning_learning_before_backjump_only_distinct_learnt =
  conflict_driven_clause_learning trail clauses update_trail update_cls propagate_conds inv
  backjump_conds
  "\<lambda>C S.  distinct_mset C \<and> \<not>tautology C \<and> learn_restrictions C S \<and>
    (\<exists>F K d F' C' L.  trail S = F' @ Marked K d # F \<and> C = C' + {#L#} \<and> F \<Turnstile>as CNot C'
      \<and> C' + {#L#} \<notin> clauses S)"
  "\<lambda>C S. \<not>(\<exists>F' F K d L. trail S = F' @ Marked K d # F \<and> F \<Turnstile>as CNot (C - {#L#}))
    \<and> forget_restrictions C S"
    for
      trail :: "'st \<Rightarrow> ('v::linorder, dpll_marked_level, dpll_mark) annoted_lits" and
      clauses :: "'st \<Rightarrow> 'v clauses" and
      update_trail :: "('v, dpll_marked_level, dpll_mark) annoted_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
      update_cls :: "'v clause set \<Rightarrow> 'st \<Rightarrow> 'st" and
      propagate_conds ::  "'st \<Rightarrow> bool" and
      inv :: "'st \<Rightarrow> bool" and
      backjump_conds :: "'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool" and
      learn_restrictions forget_restrictions :: "'v clause \<Rightarrow> 'st \<Rightarrow> bool"
begin

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_learn_all_induct[consumes 1, case_names dpll_bj learn forget\<^sub>N\<^sub>O\<^sub>T]:
  fixes S T :: "'st"
  assumes "cdcl\<^sub>N\<^sub>O\<^sub>T S T" and
    dpll: "\<And>S T. dpll_bj S T \<Longrightarrow> P S T" and
    learning:
      "\<And>S C F K d F' C' L T. clauses S \<Turnstile>p C
      \<Longrightarrow> atms_of C \<subseteq> atms_of_m (clauses S) \<union> atm_of ` (lits_of (trail S))
      \<Longrightarrow>  distinct_mset C \<Longrightarrow> \<not> tautology C \<Longrightarrow> learn_restrictions C S \<Longrightarrow>
      trail S = F' @ Marked K d # F \<Longrightarrow> C = C' + {#L#} \<Longrightarrow> F \<Turnstile>as CNot C' \<Longrightarrow>
      C' + {#L#} \<notin> clauses S \<Longrightarrow> T \<sim> add_cls\<^sub>N\<^sub>O\<^sub>T C S
      \<Longrightarrow> P S T" and
    forgetting: "\<And>S C T. clauses S - {C} \<Turnstile>p C \<Longrightarrow> C \<in> clauses S
    \<Longrightarrow> \<not>(\<exists>F' F K d L. trail S = F' @ Marked K d # F \<and> F \<Turnstile>as CNot (C - {#L#}))
    \<Longrightarrow> T \<sim> remove_cls\<^sub>N\<^sub>O\<^sub>T C S
    \<Longrightarrow> forget_restrictions C S \<Longrightarrow> P S T"
  shows "P S T"
  using assms(1)
  apply (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T.induct)
    apply (auto dest: assms(2) simp add: learn_ops_axioms)[]
   apply (auto elim!: learn_ops.learn.cases[OF learn_ops_axioms] dest: assms(3))[]
  apply (auto elim!: forget_ops.forget\<^sub>N\<^sub>O\<^sub>T.cases[OF forget_ops_axioms] dest!: assms(4))
  done

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_inv:
  "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T \<Longrightarrow> inv S \<Longrightarrow> inv T"
  apply (induction rule: rtranclp_induct)
   apply simp
  using cdcl\<^sub>N\<^sub>O\<^sub>T_inv   unfolding conflict_driven_clause_learning_def
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
    using learn C by (force simp add: atms_of_m_def atms_of_def image_Un
      true_annots_CNot_all_atms_defined elim!: learnE)
  moreover have "finite (atms_of_m (clauses S) \<union> atm_of ` lits_of (trail S))"
    using fin by auto
  ultimately show "C \<in> build_all_simple_clss (atms_of_m (clauses S) \<union> atm_of ` lits_of (trail S))"
    using build_all_simple_clss_mono  by (metis (no_types) insert_subset mk_disjoint_insert)
qed

definition "conflicting_bj_clss S \<equiv>
   {C+{#L#}|C L. C+{#L#} \<in> clauses S \<and> distinct_mset (C+{#L#}) \<and> \<not>tautology (C+{#L#})
     \<and> (\<exists>F' K d F. trail S = F' @ Marked K d # F \<and> F \<Turnstile>as CNot C)}"

lemma conflicting_bj_clss_remove_cls\<^sub>N\<^sub>O\<^sub>T[simp]:
  "conflicting_bj_clss (remove_cls\<^sub>N\<^sub>O\<^sub>T C S) = conflicting_bj_clss S - {C}"
  unfolding conflicting_bj_clss_def by fastforce

lemma conflicting_bj_clss_add_cls\<^sub>N\<^sub>O\<^sub>T:
  "conflicting_bj_clss (add_cls\<^sub>N\<^sub>O\<^sub>T C' S)
    = conflicting_bj_clss S
      \<union> (if \<exists>C L. C' = C +{#L#}\<and> distinct_mset (C+{#L#}) \<and> \<not>tautology (C+{#L#})
     \<and> (\<exists>F' K d F. trail S = F' @ Marked K d # F \<and> F \<Turnstile>as CNot C)
     then {C'} else {})"
  unfolding conflicting_bj_clss_def apply (auto split: split_if_asm) by metis+

lemma conflicting_bj_clss_add_cls\<^sub>N\<^sub>O\<^sub>T_state_eq:
  "T \<sim> add_cls\<^sub>N\<^sub>O\<^sub>T C' S \<Longrightarrow> conflicting_bj_clss T
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

lemma do_not_forget_before_backtrack_rule_clause_learned_clause_untouched:
  assumes "forget\<^sub>N\<^sub>O\<^sub>T S T"
  shows "conflicting_bj_clss S = conflicting_bj_clss T"
  using assms apply induction
  unfolding conflicting_bj_clss_def
  by (metis (no_types, lifting) clause_remove_cls\<^sub>N\<^sub>O\<^sub>T diff_union_cancelR insert_Diff
    insert_iff state_eq\<^sub>N\<^sub>O\<^sub>T_clauses state_eq\<^sub>N\<^sub>O\<^sub>T_trail update_trail_remove_clss\<^sub>N\<^sub>O\<^sub>T)

lemma forget_\<mu>\<^sub>L_decrease:
  assumes forget\<^sub>N\<^sub>O\<^sub>T: "forget\<^sub>N\<^sub>O\<^sub>T S T" and
   fin: "finite (clauses S)"
  shows "(\<mu>\<^sub>L b T, \<mu>\<^sub>L b S) \<in> less_than <*lex*> less_than"
proof -
  have "card (clauses T) < card (clauses S)"
    using forget\<^sub>N\<^sub>O\<^sub>T fin apply induction
    using card_Suc_Diff1 by fastforce
  then show ?thesis
    unfolding do_not_forget_before_backtrack_rule_clause_learned_clause_untouched[OF forget\<^sub>N\<^sub>O\<^sub>T]
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
    using learnST by induction (auto simp add: conflicting_bj_clss_add_cls\<^sub>N\<^sub>O\<^sub>T_state_eq)
  moreover have "conflicting_bj_clss S \<noteq> conflicting_bj_clss T"
    using learnST
    proof induction
      case (1 S C T) note clss_S = this(1) and atms_C = this(2) and inv = this(3) and T = this(4)
      then obtain F K d F' C' L where
        tr_S: "trail S = F' @ Marked K d # F" and
        C: "C = C' + {#L#}" and
        F: "F \<Turnstile>as CNot C'" and
        C_S:"C' + {#L#} \<notin> clauses S"
        by blast
      moreover have "distinct_mset C" "\<not> tautology C" using inv by blast+
      ultimately have "C' + {#L#} \<in> conflicting_bj_clss T"
        using T unfolding conflicting_bj_clss_def by fastforce
      moreover have "C' + {#L#} \<notin> conflicting_bj_clss S"
        using C_S unfolding conflicting_bj_clss_def by auto
      ultimately show ?case by blast
    qed
  moreover have fin_T: "finite (conflicting_bj_clss T)"
    using learnST fin by induction (auto simp add: conflicting_bj_clss_add_cls\<^sub>N\<^sub>O\<^sub>T )
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
      by standard (meson "1" "2" fin'  \<open>finite (conflicting_bj_clss T)\<close> build_all_simple_clss_mono
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
      (meson \<open>conflicting_bj_clss S \<noteq> conflicting_bj_clss T\<close>
        \<open>conflicting_bj_clss S \<subseteq> conflicting_bj_clss T\<close>
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
               - \<mu>\<^sub>C (1+card (atms_of_m A)) (2+card (atms_of_m A)) (trail_weight T),
            conflicting_bj_clss_yet (card (atms_of_m A)) T, card (clauses T))"
lemma cdcl\<^sub>N\<^sub>O\<^sub>T_decreasing_measure:
  assumes "cdcl\<^sub>N\<^sub>O\<^sub>T S T"  and "inv S"
  "atms_of_m (clauses S) \<subseteq> atms_of_m A" and
  "atm_of ` lits_of (trail S) \<subseteq> atms_of_m A" and
  "no_dup (trail S)" and
  fin_S: "finite(clauses S)" and
  fin_A: "finite A"
  shows "(\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L A T, \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L A S)
            \<in> less_than <*lex*> (less_than <*lex*> less_than)"
  using assms(1-6)
proof induction
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
  case (c_forget\<^sub>N\<^sub>O\<^sub>T S T) note forget\<^sub>N\<^sub>O\<^sub>T = this(1) and fin = this(6)
  have "trail S = trail T" using forget\<^sub>N\<^sub>O\<^sub>T by induction auto
  thus ?case
    using forget_\<mu>\<^sub>L_decrease[OF forget\<^sub>N\<^sub>O\<^sub>T fin] unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L_def by auto
qed

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_restricted_learning_wf:
  assumes "finite A"
  shows "wf {(T, S).
    (atms_of_m (clauses S) \<subseteq> atms_of_m A \<and> atm_of ` lits_of (trail S) \<subseteq> atms_of_m A
    \<and> no_dup (trail S)
    \<and> finite (clauses S) \<and> inv S)
    \<and> cdcl\<^sub>N\<^sub>O\<^sub>T S T }"
  by (rule wf_wf_if_measure'[of "less_than <*lex*> (less_than <*lex*> less_than)"])
     (auto intro: cdcl\<^sub>N\<^sub>O\<^sub>T_decreasing_measure[OF _ _ _ _ _ _ assms])

definition \<mu>\<^sub>C' :: "'a literal multiset set \<Rightarrow> 'st \<Rightarrow> nat" where
"\<mu>\<^sub>C' A T \<equiv> \<mu>\<^sub>C (1+card (atms_of_m A)) (2+card (atms_of_m A)) (trail_weight T)"

definition \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' :: "'a literal multiset set \<Rightarrow> 'st \<Rightarrow> nat" where
"\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' A T \<equiv>
  ((2+card (atms_of_m A)) ^ (1+card (atms_of_m A)) - \<mu>\<^sub>C' A T) * (1+ 3^card (atms_of_m A)) * 2
  + conflicting_bj_clss_yet (card (atms_of_m A)) T * 2
  + card (clauses T)"

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_decreasing_measure':
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T S T" and
    "inv S"
    "atms_of_m (clauses S) \<subseteq> atms_of_m A"
    "atm_of ` lits_of (trail S) \<subseteq> atms_of_m A" and
    "no_dup (trail S)" and
    "finite (clauses S)" and
    fin_A: "finite A"
  shows "\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' A T < \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' A S"
  using assms(1-6)
proof (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_learn_all_induct)
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
  case (learn S C F' K d F C' L T) note clss_S_C = this(1) and atms_C = this(2) and dist = this(3)
    and tauto = this(4) and learn_restr = this(5) and tr_S = this(6) and C' = this(7) and
    F_C = this(8) and C_new = this(9) and T =this(10) and inv = this(11) and atms_S_A = this(12)
    and atms_tr_S_A = this(13) and n_d = this(14) and finite_S = this(15)
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
  moreover have [simp]: "conflicting_bj_clss (add_cls\<^sub>N\<^sub>O\<^sub>T C S) = conflicting_bj_clss S \<union> {C}"
     using dist tauto F_C by (force simp add: ac_simps conflicting_bj_clss_add_cls\<^sub>N\<^sub>O\<^sub>T C' tr_S)
  ultimately have [simp]: "conflicting_bj_clss_yet (card (atms_of_m A)) S
    = Suc (conflicting_bj_clss_yet (card (atms_of_m A)) (add_cls\<^sub>N\<^sub>O\<^sub>T C S))"
      by simp
  have 1: "clauses T = clauses (add_cls\<^sub>N\<^sub>O\<^sub>T C S)" using T by auto
  have 2: "conflicting_bj_clss_yet (card (atms_of_m A)) T
    = conflicting_bj_clss_yet (card (atms_of_m A)) (add_cls\<^sub>N\<^sub>O\<^sub>T C S)"
    using T unfolding conflicting_bj_clss_def by auto
  have 3: "\<mu>\<^sub>C' A T = \<mu>\<^sub>C' A (add_cls\<^sub>N\<^sub>O\<^sub>T C S)"
    using T unfolding \<mu>\<^sub>C'_def by auto
  have "((2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A)) - \<mu>\<^sub>C' A (add_cls\<^sub>N\<^sub>O\<^sub>T C S))
    * (1 + 3 ^ card (atms_of_m A)) * 2
    = ((2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A)) - \<mu>\<^sub>C' A S)
    * (1 + 3 ^ card (atms_of_m A)) * 2"
      unfolding \<mu>\<^sub>C'_def by auto
  moreover
    have "conflicting_bj_clss_yet (card (atms_of_m A)) (add_cls\<^sub>N\<^sub>O\<^sub>T C S)
        * 2
      + card (clauses (add_cls\<^sub>N\<^sub>O\<^sub>T C S))
      < conflicting_bj_clss_yet (card (atms_of_m A)) S * 2
      + card (clauses S)"
     by auto
  ultimately show ?case unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_def 1 2 3 by presburger
next
  case (forget\<^sub>N\<^sub>O\<^sub>T S C T) note T = this(4) and finite_S = this(10)
  have [simp]: "\<mu>\<^sub>C' A (remove_cls\<^sub>N\<^sub>O\<^sub>T C S) =  \<mu>\<^sub>C' A S"
    unfolding \<mu>\<^sub>C'_def by auto
  have "forget\<^sub>N\<^sub>O\<^sub>T S T"
    apply (rule forget\<^sub>N\<^sub>O\<^sub>T.intros) using forget\<^sub>N\<^sub>O\<^sub>T by auto
  then have "conflicting_bj_clss T = conflicting_bj_clss S"
    using do_not_forget_before_backtrack_rule_clause_learned_clause_untouched by blast
  moreover have "card (clauses T) < card (clauses S)"
    by (metis (no_types) T card_Diff1_less clause_remove_cls\<^sub>N\<^sub>O\<^sub>T finite_S forget\<^sub>N\<^sub>O\<^sub>T.hyps(2)
      state_eq\<^sub>N\<^sub>O\<^sub>T_clauses)
  ultimately show ?case unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_def
    by (metis (no_types) T \<open>\<mu>\<^sub>C' A (remove_cls\<^sub>N\<^sub>O\<^sub>T C S) = \<mu>\<^sub>C' A S\<close> add_le_cancel_left
      \<mu>\<^sub>C'_def not_le state_eq\<^sub>N\<^sub>O\<^sub>T_trail)
qed

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_clauses_bound:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T S T" and
    "inv S" and
    "atms_of_m (clauses S) \<subseteq> A" and
    "atm_of `(lits_of (trail S)) \<subseteq> A" and
    "finite (clauses S)" and
    "finite A"
  shows "clauses T \<subseteq> clauses S \<union> build_all_simple_clss A"
  using assms
proof (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_learn_all_induct)
  case dpll_bj
  thus ?case using dpll_bj_clauses by blast
next
  case forget\<^sub>N\<^sub>O\<^sub>T
  thus ?case using clause_remove_cls\<^sub>N\<^sub>O\<^sub>T unfolding state_eq\<^sub>N\<^sub>O\<^sub>T_def by blast
next
  case (learn S C F K d F' C' L) note atms_C = this(2) and dist = this(3) and tauto = this(4) and
  T = this(10) and atms_clss_S = this(12) and atms_trail_S = this(13) and finite = this(15)
  have "atms_of C \<subseteq> A"
    using atms_C atms_clss_S atms_trail_S by auto
  hence "build_all_simple_clss (atms_of C) \<subseteq> build_all_simple_clss A"
    using finite by (auto simp add: build_all_simple_clss_mono)
  hence "C \<in> build_all_simple_clss A"
    using finite dist tauto
    by (auto dest: distinct_mset_not_tautology_implies_in_build_all_simple_clss)
  thus ?case using T by auto
qed

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_clauses_bound:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T" and
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
  case (step T U) note st = this(1) and cdcl\<^sub>N\<^sub>O\<^sub>T = this(2) and IH = this(3)[OF this(4-7)] and
    inv = this(4) and atms_clss_S = this(5) and atms_trail_S = this(6) and finite_cls_S = this(7)
  have "inv T"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_inv st inv by blast
  moreover have "atms_of_m (clauses T) \<subseteq> A" and "atm_of ` lits_of (trail T) \<subseteq> A"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_trail_clauses_bound[OF st] inv atms_clss_S atms_trail_S by blast+
  moreover have "finite (clauses T)"
    using IH finite_cls_S finite by (meson build_all_simple_clss_finite finite_Un rev_finite_subset)
  ultimately have "clauses U \<subseteq> clauses T \<union> build_all_simple_clss A"
       using cdcl\<^sub>N\<^sub>O\<^sub>T finite by (simp add: cdcl\<^sub>N\<^sub>O\<^sub>T_clauses_bound)
  thus ?case using IH by auto
qed


lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_card_clauses_bound:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T" and
    "inv S" and
    "atms_of_m (clauses S) \<subseteq> A" and
    "atm_of `(lits_of (trail S)) \<subseteq> A" and
    "finite (clauses S)" and
    finite: "finite A"
  shows "card (clauses T) \<le> card (clauses S) + 3 ^ (card A)"
  using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_clauses_bound[OF assms] finite by (meson Nat.le_trans assms(5)
    build_all_simple_clss_card build_all_simple_clss_finite card_Un_le card_mono finite_UnI
    nat_add_left_cancel_le)

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_card_clauses_bound':
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T" and
    "inv S" and
    "atms_of_m (clauses S) \<subseteq> A" and
    "atm_of `(lits_of (trail S)) \<subseteq> A" and
    "finite (clauses S)" and
    finite: "finite A"
  shows "card {C \<in> clauses T. tautology C \<or> \<not>distinct_mset C}
    \<le> card {C \<in> clauses S. tautology C \<or> \<not>distinct_mset C} + 3 ^ (card A)"
  using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_clauses_bound[OF assms] finite
proof -
  have "{C \<in> clauses T. tautology C \<or> \<not>distinct_mset C}
    \<subseteq> {C \<in> clauses S. tautology C \<or> \<not>distinct_mset C} \<union> build_all_simple_clss A"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_clauses_bound[OF assms] by auto
  hence "card {C \<in> clauses T. tautology C \<or> \<not>distinct_mset C}
    \<le> card ({C \<in> clauses S. tautology C \<or> \<not>distinct_mset C} \<union> build_all_simple_clss A)"
    using finite by (simp add: assms(5) build_all_simple_clss_finite card_mono)
  thus ?thesis
    by (meson le_trans build_all_simple_clss_card card_Un_le local.finite nat_add_left_cancel_le)
qed

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_card_simple_clauses_bound:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T" and
    "inv S" and
    "atms_of_m (clauses S) \<subseteq> A" and
    "atm_of `(lits_of (trail S)) \<subseteq> A" and
    "finite (clauses S)" and
    finite: "finite A"
  shows "card (clauses T)
    \<le> card {C \<in> clauses S. tautology C \<or> \<not>distinct_mset C} + 3 ^ (card A)"
  using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_clauses_bound[OF assms] finite
proof -
  have "\<And>x. x \<in> clauses T \<Longrightarrow>\<not> tautology x \<Longrightarrow> distinct_mset x \<Longrightarrow> x \<in> build_all_simple_clss A"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_clauses_bound[OF assms] by (metis (full_types) UnE assms(3)
     atms_of_atms_of_m_mono build_all_simple_clss_mono
     distinct_mset_not_tautology_implies_in_build_all_simple_clss local.finite subset_eq)
  hence "clauses T
    \<subseteq> {C \<in> clauses S. tautology C \<or> \<not>distinct_mset C} \<union> build_all_simple_clss A"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_clauses_bound[OF assms] by auto
  hence "card(clauses T)
    \<le> card ({C \<in> clauses S. tautology C \<or> \<not>distinct_mset C} \<union> build_all_simple_clss A)"
    using finite by (simp add: assms(5) build_all_simple_clss_finite card_mono)
  thus ?thesis
    by (meson le_trans build_all_simple_clss_card card_Un_le local.finite nat_add_left_cancel_le)
qed

definition \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound :: "'v literal multiset set \<Rightarrow> 'st \<Rightarrow> nat" where
"\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A S =
  ((2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A))) * (1 + 3 ^ card (atms_of_m A)) * 2
     + 2*3 ^ (card (atms_of_m A))
     + card {C \<in> clauses S. tautology C \<or> \<not>distinct_mset C} + 3 ^ (card (atms_of_m A))"

lemma \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_update_trail[simp]:
  "\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A (update_trail M S) = \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A S"
  unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_def by auto

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_update_trail:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T" and
    "inv S" and
    "atms_of_m (clauses S) \<subseteq> atms_of_m A" and
    "atm_of `(lits_of (trail S)) \<subseteq> atms_of_m A" and
    "finite (clauses S)" and
    finite: "finite (atms_of_m A)" and
    U: "U \<sim> update_trail M T"
  shows "\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' A U \<le> \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A S"
proof -
  have " ((2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A)) - \<mu>\<^sub>C' A U)
    \<le> (2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A))"
    by auto
  hence "((2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A)) - \<mu>\<^sub>C' A U)
        * (1 + 3 ^ card (atms_of_m A)) * 2
    \<le> (2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A)) * (1 + 3 ^ card (atms_of_m A)) * 2"
    using mult_le_mono1 by blast
  moreover
    have "conflicting_bj_clss_yet (card (atms_of_m A)) T * 2 \<le> 2 * 3 ^ card (atms_of_m A)"
      by linarith
  moreover have "card (clauses U)
      \<le> card {C \<in> clauses S. tautology C \<or> \<not>distinct_mset C} + 3 ^ card (atms_of_m A)"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_card_simple_clauses_bound[OF assms(1-6)] U by simp
  ultimately show ?thesis
    unfolding  \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_def \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_def by linarith
qed

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T" and
    "inv S" and
    "atms_of_m (clauses S) \<subseteq> atms_of_m A" and
    "atm_of `(lits_of (trail S)) \<subseteq> atms_of_m A" and
    "finite (clauses S)" and
    finite: "finite (atms_of_m A)"
  shows "\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' A T \<le> \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A S"
proof -
  have "\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' A (update_trail (trail T) T) = \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' A T"
    unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_def  \<mu>\<^sub>C'_def conflicting_bj_clss_def by auto
  thus ?thesis using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_update_trail[OF assms, of _ "trail T"]
    state_eq\<^sub>N\<^sub>O\<^sub>T_ref by fastforce
qed

lemma rtranclp_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_decreasing:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T" and
    "inv S" and
    "atms_of_m (clauses S) \<subseteq> atms_of_m A" and
    "atm_of `(lits_of (trail S)) \<subseteq> atms_of_m A" and
    "finite (clauses S)" and
    finite: "finite (atms_of_m A)"
  shows "\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A T \<le> \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A S"
proof -
  have "{C \<in> clauses T. tautology C \<or> \<not> distinct_mset C}
    \<subseteq> {C \<in> clauses S. tautology C \<or> \<not> distinct_mset C}"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_clauses_bound[OF assms] finite by (auto dest!: build_all_simple_clssE)
  hence "card {C \<in> clauses T. tautology C \<or> \<not> distinct_mset C} \<le>
    card {C \<in> clauses S. tautology C \<or> \<not> distinct_mset C}"
    by (simp add: assms(5) card_mono)
  thus ?thesis
    unfolding  \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_def by auto
qed

end \<comment> \<open>end of \<open>conflict_driven_clause_learning_learning_before_backjump_only_distinct_learnt\<close>\<close>

subsection \<open>DPLL with simple backtrack\<close>
locale dpll_with_backtrack
begin
inductive backtrack :: "('v, dpll_marked_level, dpll_mark) marked_lit list \<times> 'v literal multiset set
  \<Rightarrow> ('v, dpll_marked_level, dpll_mark) marked_lit list \<times> 'v literal multiset set \<Rightarrow> bool" where
"backtrack_split (fst S)  = (M', L # M) \<Longrightarrow> is_marked L \<Longrightarrow> D \<in> snd S
  \<Longrightarrow> fst S \<Turnstile>as CNot D \<Longrightarrow> backtrack S (Propagated (- (lit_of L)) Proped # M, snd S)"

inductive_cases backtrackE[elim]: "backtrack (M, N) (M', N')"
lemma backtrack_is_backjump:
  fixes M M' :: "('v, dpll_marked_level, dpll_mark) marked_lit list"
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
    by auto
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
            fix x :: "('v, dpll_marked_level, dpll_mark) marked_lit"
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
  fixes M M' :: "('v, dpll_marked_level, dpll_mark) marked_lit list"
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

sublocale dpll_state fst snd "\<lambda>M S. (M, snd S)" "\<lambda>N (M, _). (M, N)"
  by unfold_locales auto

lemma bj_ops: "backjumping_ops fst snd (\<lambda>M S. (M, snd S)) (\<lambda>N (M, _). (M, N))"
  by unfold_locales

lemma backtrack_is_backjump'':
  fixes M M' :: "('v, dpll_marked_level, dpll_mark) marked_lit list"
  assumes
    backtrack: "backtrack S T" and
    no_dup: "(no_dup \<circ> fst) S" and
    decomp: "all_decomposition_implies (snd S) (get_all_marked_decomposition (fst S))"
    shows "backjumping_ops.backjump fst snd (\<lambda>M S. (M, snd S)) (\<lambda>_ _ S T. backtrack S T) S T"
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
    using backjumping_ops.backjump.intros[OF bj_ops 1 _ 3 4 5 6 7 8] 2 backtrack
    by (auto simp: state_eq\<^sub>N\<^sub>O\<^sub>T_def simp del: state_simp\<^sub>N\<^sub>O\<^sub>T)
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

sublocale dpll_with_backtrack \<subseteq> dpll_with_backjumping_ops fst snd "\<lambda>M S. (M, snd S)"
  "\<lambda>N (M, _). (M, N)" "\<lambda>_. True"
  "\<lambda>(M, N). no_dup M \<and> all_decomposition_implies N (get_all_marked_decomposition M)"
  "(\<lambda>_ _ S T. backtrack S T)"
  by unfold_locales (metis (mono_tags, lifting) dpll_with_backtrack.backtrack_is_backjump''
   dpll_with_backtrack.can_do_bt_step prod.case_eq_if comp_apply)

sublocale dpll_with_backtrack \<subseteq> dpll_with_backjumping  fst snd "\<lambda>M S. (M, snd S)"
  "\<lambda>N (M, _). (M, N)" "\<lambda>_. True"
  "\<lambda>(M, N). no_dup M \<and> all_decomposition_implies N (get_all_marked_decomposition M)"
  "(\<lambda>_ _ S T. backtrack S T)"
  apply unfold_locales
  using dpll_bj_no_dup dpll_bj_all_decomposition_implies_inv apply fastforce
  done

sublocale dpll_with_backtrack \<subseteq> conflict_driven_clause_learning_ops
   fst snd "\<lambda>M S. (M, snd S)" "\<lambda>N (M, _). (M, N)" "\<lambda>_. True"
   "\<lambda>(M, N). no_dup M \<and> all_decomposition_implies N (get_all_marked_decomposition M)"
   "(\<lambda>_ _ S T. backtrack S T)" "\<lambda>_ _. False" "\<lambda>_ _. False"
   by unfold_locales

sublocale dpll_with_backtrack \<subseteq> conflict_driven_clause_learning
   fst snd "\<lambda>M S. (M, snd S)" "\<lambda>N (M, _). (M, N)" "\<lambda>_. True"
   "\<lambda>(M, N). no_dup M \<and> all_decomposition_implies N (get_all_marked_decomposition M)"
   "(\<lambda>_ _ S T. backtrack S T)" "\<lambda>_ _. False" "\<lambda>_ _. False"
   apply unfold_locales
   using cdcl\<^sub>N\<^sub>O\<^sub>T.simps dpll_bj_inv forgetE learnE by blast

context dpll_with_backtrack
begin
lemma tranclp_dpll_wf_inital_state:
  assumes fin: "finite A"
  shows "wf {((M'::('v, dpll_marked_level, dpll_mark) annoted_lits, N'::'v clauses), ([], N))|M' N' N.
    dpll_bj\<^sup>+\<^sup>+ ([], N) (M', N') \<and> atms_of_m N \<subseteq> atms_of_m A}"
  using tranclp_dpll_bj_wf[OF assms(1)] by (rule wf_subset) auto

theorem full0_dpll_normal_forms:
  fixes M M' :: "('v, dpll_marked_level, dpll_mark) marked_lit list"
  assumes
    full: "full0 dpll_bj ([], N) (M', N')" and
    "finite N"
  shows "unsatisfiable N \<or> (M' \<Turnstile>as N \<and> satisfiable N)"
  using assms full0_dpll_backjump_normal_forms[of "([],N)" "(M', N')" N] by auto

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_is_dpll:
  "cdcl\<^sub>N\<^sub>O\<^sub>T S T \<longleftrightarrow> dpll_bj S T"
  by (auto simp: cdcl\<^sub>N\<^sub>O\<^sub>T.simps learn.simps forget\<^sub>N\<^sub>O\<^sub>T.simps)

text \<open>Another proof of termination:\<close>
lemma "wf {(T, S). dpll_bj S T \<and> cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv A S}"
  unfolding cdcl\<^sub>N\<^sub>O\<^sub>T_is_dpll[symmetric]
  by (rule wf_cdcl\<^sub>N\<^sub>O\<^sub>T_no_learn_and_forget_infinite_chain)
  (auto simp: learn.simps forget\<^sub>N\<^sub>O\<^sub>T.simps)
end

subsection \<open>CDCL with restarts\<close>
subsubsection\<open>Definition\<close>
locale restart_ops =
  fixes
    cdcl\<^sub>N\<^sub>O\<^sub>T :: "'st \<Rightarrow> 'st \<Rightarrow> bool" and
    restart :: "'st \<Rightarrow> 'st \<Rightarrow> bool"
begin
inductive cdcl\<^sub>N\<^sub>O\<^sub>T_with_restarts  :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
"cdcl\<^sub>N\<^sub>O\<^sub>T S T \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_with_restarts S T" |
"restart S T \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_with_restarts S T"

end

locale conflict_driven_clause_learning_with_restarts =
  conflict_driven_clause_learning trail clauses update_trail update_cls propagate_conds inv
  backjump_conds learn_cond forget_cond
    for
      trail :: "'st \<Rightarrow> ('v, dpll_marked_level, dpll_mark) annoted_lits" and
      clauses :: "'st \<Rightarrow> 'v clauses" and
      update_trail :: "('v, dpll_marked_level, dpll_mark) annoted_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
      update_cls :: "'v clause set \<Rightarrow> 'st \<Rightarrow> 'st" and
      propagate_conds :: "'st \<Rightarrow> bool" and
      inv :: "'st \<Rightarrow> bool" and
      backjump_conds ::  "'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool" and
      learn_cond forget_cond :: "'v clause \<Rightarrow> 'st \<Rightarrow> bool"
begin

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_iff_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restarts_no_restarts:
  "cdcl\<^sub>N\<^sub>O\<^sub>T S T \<longleftrightarrow> restart_ops.cdcl\<^sub>N\<^sub>O\<^sub>T_with_restarts cdcl\<^sub>N\<^sub>O\<^sub>T (\<lambda>_ _. False) S T"
  (is "?C S T \<longleftrightarrow> ?R S T")
proof
  fix S T
  assume "?C S T"
  thus "?R S T" by (simp add: restart_ops.cdcl\<^sub>N\<^sub>O\<^sub>T_with_restarts.intros(1))
next
  fix S T
  assume "?R S T"
  thus "?C S T"
    apply (cases rule: restart_ops.cdcl\<^sub>N\<^sub>O\<^sub>T_with_restarts.cases)
    using \<open>?R S T\<close> by fast+
qed

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restarts:
  "cdcl\<^sub>N\<^sub>O\<^sub>T S T \<Longrightarrow> restart_ops.cdcl\<^sub>N\<^sub>O\<^sub>T_with_restarts cdcl\<^sub>N\<^sub>O\<^sub>T restart S T"
  by (simp add: restart_ops.cdcl\<^sub>N\<^sub>O\<^sub>T_with_restarts.intros(1))
end

subsubsection \<open>Increasing restarts\<close>
text \<open>To add restarts we needs some assumptions on the predicate (called @{term cdcl\<^sub>N\<^sub>O\<^sub>T} here):
  \<^item> a function @{term f} that is strictly monotonic (and to ease the proof, we assume that
  @{term "f (0::nat) = 0"}). The first step is actually only a restart to clean the state (e.g. to
  ensure that the trail is empty).
  \<^item> a measure @{term "\<mu>"}: it should decrease under the assumptions @{term bound_inv}, whenever a
  @{term cdcl\<^sub>N\<^sub>O\<^sub>T} or a @{term restart} is done. A parameter is given to @{term \<mu>}: for conflict-
  driven clause learning, it is an upper-bound of the clauses. We are assuming that such a bound
  can be found after a restart whenever the invariant holds.
  \<^item> we also assume that the measure decrease after any @{term cdcl\<^sub>N\<^sub>O\<^sub>T} step.
  \<^item> an invariant on the states @{term cdcl\<^sub>N\<^sub>O\<^sub>T_inv} that also holds after restarts.
  \<^item> it is \<^emph>\<open>not required\<close> that the measure decrease with respect to restarts, but the measure has to
  be bound by some function @{term \<mu>_bound} taking the same parameter as @{term \<mu>} and the initial
  state of the considered @{term cdcl\<^sub>N\<^sub>O\<^sub>T} chain.\<close>
locale cdcl\<^sub>N\<^sub>O\<^sub>T_increasing_restarts_ops =
  restart_ops cdcl\<^sub>N\<^sub>O\<^sub>T restart for
    restart :: "'st \<Rightarrow> 'st \<Rightarrow> bool" and
    cdcl\<^sub>N\<^sub>O\<^sub>T :: "'st \<Rightarrow> 'st \<Rightarrow> bool" +
  fixes
    f :: "nat \<Rightarrow> nat" and
    bound_inv :: "'bound \<Rightarrow> 'st \<Rightarrow> bool" and
    \<mu> :: "'bound \<Rightarrow> 'st \<Rightarrow> nat" and
    cdcl\<^sub>N\<^sub>O\<^sub>T_inv :: "'st \<Rightarrow> bool" and
    \<mu>_bound :: "'bound \<Rightarrow> 'st \<Rightarrow> nat"
  assumes
    mono_f: "strict_mono f" and
    bound_inv: "\<And>A S T. cdcl\<^sub>N\<^sub>O\<^sub>T_inv S \<Longrightarrow> bound_inv A S \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T S T \<Longrightarrow> bound_inv A T" and
    cdcl\<^sub>N\<^sub>O\<^sub>T_measure: "\<And>A S T. cdcl\<^sub>N\<^sub>O\<^sub>T_inv S \<Longrightarrow> bound_inv A S \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T S T \<Longrightarrow> \<mu> A T < \<mu> A S" and
    measure_bound2: "\<And>A T U. cdcl\<^sub>N\<^sub>O\<^sub>T_inv T \<Longrightarrow> bound_inv A T \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* T U
       \<Longrightarrow> \<mu> A U \<le> \<mu>_bound A T" and
    measure_bound4: "\<And>A T U. cdcl\<^sub>N\<^sub>O\<^sub>T_inv T \<Longrightarrow> bound_inv A T \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* T U
       \<Longrightarrow> \<mu>_bound A U \<le> \<mu>_bound A T" and
    cdcl\<^sub>N\<^sub>O\<^sub>T_restart_inv: "\<And>A U V. cdcl\<^sub>N\<^sub>O\<^sub>T_inv U \<Longrightarrow> restart U V \<Longrightarrow> bound_inv A U \<Longrightarrow> bound_inv A V"
      and
    exists_bound: "\<And>R S. cdcl\<^sub>N\<^sub>O\<^sub>T_inv R \<Longrightarrow> restart R S \<Longrightarrow> \<exists>A. bound_inv A S" and
    cdcl\<^sub>N\<^sub>O\<^sub>T_inv: "\<And>S T. cdcl\<^sub>N\<^sub>O\<^sub>T_inv S \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T S T \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_inv T" and
    cdcl\<^sub>N\<^sub>O\<^sub>T_inv_restart: "\<And>S T. cdcl\<^sub>N\<^sub>O\<^sub>T_inv S \<Longrightarrow> restart S T \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_inv T"
begin

lemma f_Suc_not_zero: "f (Suc n) \<noteq> 0"
  by (metis lessI less_nat_zero_code mono_f strict_mono_def)

lemma strict_mono_ge_id: "strict_mono (g::nat \<Rightarrow> nat) \<Longrightarrow> g n \<ge> n"
  unfolding strict_mono_def apply (induction n, simp)
  by (metis Suc_leI diff_diff_cancel lessI less_imp_diff_less)

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_inv:
  assumes
    "(cdcl\<^sub>N\<^sub>O\<^sub>T^^n) S T" and
    "cdcl\<^sub>N\<^sub>O\<^sub>T_inv S"
  shows "cdcl\<^sub>N\<^sub>O\<^sub>T_inv T"
  using assms by (induction n arbitrary: T) (auto intro:bound_inv cdcl\<^sub>N\<^sub>O\<^sub>T_inv)

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_bound_inv:
  assumes
    "(cdcl\<^sub>N\<^sub>O\<^sub>T^^n) S T" and
    "cdcl\<^sub>N\<^sub>O\<^sub>T_inv S"
    "bound_inv A S"
  shows "bound_inv A T"
  using assms by (induction n arbitrary: T) (auto intro:bound_inv cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_inv)

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_inv:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T" and
    "cdcl\<^sub>N\<^sub>O\<^sub>T_inv S"
  shows "cdcl\<^sub>N\<^sub>O\<^sub>T_inv T"
  using assms by induction (auto intro: cdcl\<^sub>N\<^sub>O\<^sub>T_inv)

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_bound_inv:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T" and
    "bound_inv A S" and
    "cdcl\<^sub>N\<^sub>O\<^sub>T_inv S"
  shows "bound_inv A T"
  using assms by induction (auto intro:bound_inv rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_inv)

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_comp_n_le:
  assumes
    "(cdcl\<^sub>N\<^sub>O\<^sub>T^^(Suc n)) S T" and
    "bound_inv A S"
    "cdcl\<^sub>N\<^sub>O\<^sub>T_inv S"
  shows "\<mu> A T < \<mu> A S - n"
  using assms
proof (induction n arbitrary: T)
  case 0
  thus ?case using cdcl\<^sub>N\<^sub>O\<^sub>T_measure by auto
next
  case (Suc n) note IH =this(1)[OF _ this(3) this(4)] and S_T =this(2) and b_inv = this(3) and
  c_inv = this(4)
  obtain U :: 'st where S_U: "(cdcl\<^sub>N\<^sub>O\<^sub>T^^(Suc n)) S U" and U_T: "cdcl\<^sub>N\<^sub>O\<^sub>T U T" using S_T by auto
  then have "\<mu> A U < \<mu> A S - n" using IH[of U] by simp
  moreover
    have "bound_inv A U"
      using S_U b_inv  cdcl\<^sub>N\<^sub>O\<^sub>T_bound_inv c_inv by blast
    hence "\<mu> A T < \<mu> A U" using cdcl\<^sub>N\<^sub>O\<^sub>T_measure[OF _ _ U_T] S_U c_inv cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_inv by auto
  ultimately show ?case by linarith
qed

lemma wf_cdcl\<^sub>N\<^sub>O\<^sub>T:
  "wf {(T, S). cdcl\<^sub>N\<^sub>O\<^sub>T S T \<and> cdcl\<^sub>N\<^sub>O\<^sub>T_inv S \<and> bound_inv A S}" (is "wf ?A")
  apply (rule wfP_if_measure2[of _ _ "\<mu> A"])
  using cdcl\<^sub>N\<^sub>O\<^sub>T_comp_n_le[of 0 _ _ A] by auto

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_measure:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T" and
    "bound_inv A S" and
    "cdcl\<^sub>N\<^sub>O\<^sub>T_inv S"
  shows "\<mu> A T \<le> \<mu> A S"
  using assms
proof (induction rule: rtranclp_induct)
  case base
  thus ?case by auto
next
  case (step T U) note IH =this(3)[OF this(4) this(5)] and st =this(1) and cdcl\<^sub>N\<^sub>O\<^sub>T= this(2) and
    b_inv = this(4) and c_inv = this(5)
  have "bound_inv A T"
    by (meson cdcl\<^sub>N\<^sub>O\<^sub>T_bound_inv rtranclp_imp_relpowp st step.prems)
  moreover have "cdcl\<^sub>N\<^sub>O\<^sub>T_inv T"
    using c_inv rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_inv st by blast
  ultimately have "\<mu> A U < \<mu> A T" using cdcl\<^sub>N\<^sub>O\<^sub>T_measure[OF _ _ cdcl\<^sub>N\<^sub>O\<^sub>T] by auto
  thus ?case using IH by linarith
qed

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_comp_bounded:
  assumes
    "bound_inv A S" and "cdcl\<^sub>N\<^sub>O\<^sub>T_inv S" and "m \<ge> 1+\<mu> A S"
  shows "\<not>(cdcl\<^sub>N\<^sub>O\<^sub>T ^^ m) S T"
  using assms cdcl\<^sub>N\<^sub>O\<^sub>T_comp_n_le[of "m-1" S T A] by fastforce

text \<open>
  \<^item> @{term "m \<ge> f (Suc n)"} ensure that at least one step has been done.\<close>
inductive cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy where
restart_step: "(cdcl\<^sub>N\<^sub>O\<^sub>T^^m) S T \<Longrightarrow> m \<ge> f n \<Longrightarrow> restart T U
  \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy (S, n) (U, Suc n)" |
restart_full: "full cdcl\<^sub>N\<^sub>O\<^sub>T S T \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy (S, n) (T, Suc n)"

lemmas cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_induct = cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy.induct[split_format(complete),
  OF cdcl\<^sub>N\<^sub>O\<^sub>T_increasing_restarts_ops_axioms]

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restarts:
  "cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy S T \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_with_restarts\<^sup>*\<^sup>* (fst S) (fst T)"
proof (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy.induct)
  case (restart_step m S T n U)
  hence "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T" by (meson relpowp_imp_rtranclp)
  hence "cdcl\<^sub>N\<^sub>O\<^sub>T_with_restarts\<^sup>*\<^sup>* S T" using cdcl\<^sub>N\<^sub>O\<^sub>T_with_restarts.intros(1)
    rtranclp_mono[of cdcl\<^sub>N\<^sub>O\<^sub>T cdcl\<^sub>N\<^sub>O\<^sub>T_with_restarts] by blast
  moreover have "cdcl\<^sub>N\<^sub>O\<^sub>T_with_restarts T U"
    using \<open>restart T U\<close> cdcl\<^sub>N\<^sub>O\<^sub>T_with_restarts.intros(2) by blast
  ultimately show ?case by auto
next
  case (restart_full S T)
  hence "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T" unfolding full_def by auto
  thus ?case using cdcl\<^sub>N\<^sub>O\<^sub>T_with_restarts.intros(1)
    rtranclp_mono[of cdcl\<^sub>N\<^sub>O\<^sub>T cdcl\<^sub>N\<^sub>O\<^sub>T_with_restarts] by auto
qed

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_bound_inv:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy S T" and
    "bound_inv A (fst S)" and
    "cdcl\<^sub>N\<^sub>O\<^sub>T_inv (fst S)"
  shows "bound_inv A (fst T)"
  using assms apply (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy.induct)
    prefer 2 apply (metis rtranclp_unfold fstI full_def rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_bound_inv)
  by (metis cdcl\<^sub>N\<^sub>O\<^sub>T_bound_inv cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_inv cdcl\<^sub>N\<^sub>O\<^sub>T_restart_inv fst_conv)

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_inv:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy S T" and
    "cdcl\<^sub>N\<^sub>O\<^sub>T_inv (fst S)"
  shows "cdcl\<^sub>N\<^sub>O\<^sub>T_inv (fst  T)"
  using assms apply induction
    apply (metis cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_inv cdcl\<^sub>N\<^sub>O\<^sub>T_inv_restart fst_conv)
   apply (metis fstI full0_def full0_unfold rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_inv)
  done

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_inv:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy\<^sup>*\<^sup>* S T" and
    "cdcl\<^sub>N\<^sub>O\<^sub>T_inv (fst S)"
  shows "cdcl\<^sub>N\<^sub>O\<^sub>T_inv (fst T)"
  using assms by induction (auto intro: cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_inv)

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_bound_inv:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy\<^sup>*\<^sup>* S T" and
    "cdcl\<^sub>N\<^sub>O\<^sub>T_inv (fst S)" and
    "bound_inv A (fst S)"
  shows "bound_inv A (fst T)"
  using assms apply induction
   apply (simp add: cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_inv cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_bound_inv)
  using cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_bound_inv rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_inv by blast

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_increasing_number:
  "cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy S T \<Longrightarrow> snd T = 1 + snd S"
  by (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy.induct) auto
end

locale cdcl\<^sub>N\<^sub>O\<^sub>T_increasing_restarts =
  cdcl\<^sub>N\<^sub>O\<^sub>T_increasing_restarts_ops restart cdcl\<^sub>N\<^sub>O\<^sub>T f bound_inv \<mu> cdcl\<^sub>N\<^sub>O\<^sub>T_inv \<mu>_bound
  for
    trail :: "'st \<Rightarrow> ('v, dpll_marked_level, dpll_mark) annoted_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    update_trail :: "('v, dpll_marked_level, dpll_mark) annoted_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_cls :: "'v clause set \<Rightarrow> 'st \<Rightarrow> 'st" and
    f :: "nat \<Rightarrow> nat" and
    restart :: "'st \<Rightarrow> 'st \<Rightarrow> bool" and
    bound_inv :: "'bound \<Rightarrow> 'st \<Rightarrow> bool" and
    \<mu> :: "'bound \<Rightarrow> 'st \<Rightarrow> nat" and
    cdcl\<^sub>N\<^sub>O\<^sub>T :: "'st \<Rightarrow> 'st \<Rightarrow> bool" and
    cdcl\<^sub>N\<^sub>O\<^sub>T_inv :: "'st \<Rightarrow> bool" and
    \<mu>_bound :: "'bound \<Rightarrow> 'st \<Rightarrow> nat" +
  assumes
    measure_bound: "\<And>A T V n. cdcl\<^sub>N\<^sub>O\<^sub>T_inv T \<Longrightarrow> bound_inv A T
      \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy (T, n) (V, Suc n) \<Longrightarrow> \<mu> A V \<le> \<mu>_bound A T" and
    cdcl\<^sub>N\<^sub>O\<^sub>T_with_restarts_\<mu>_bound:
      "cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy (T, a) (V, b) \<Longrightarrow>  cdcl\<^sub>N\<^sub>O\<^sub>T_inv T \<Longrightarrow> bound_inv A T
        \<Longrightarrow> \<mu>_bound A V \<le> \<mu>_bound A T"
begin

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restarts_\<mu>_bound:
  "cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy\<^sup>*\<^sup>* (T, a) (V, b) \<Longrightarrow>  cdcl\<^sub>N\<^sub>O\<^sub>T_inv T \<Longrightarrow> bound_inv A T
    \<Longrightarrow> \<mu>_bound A V \<le> \<mu>_bound A T"
  apply (induction rule: rtranclp_induct2)
   apply simp
  by (metis cdcl\<^sub>N\<^sub>O\<^sub>T_with_restarts_\<mu>_bound dual_order.trans fst_conv
    rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_bound_inv rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_inv)

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_with_restarts_measure_bound:
  "cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy (T, a) (V, b) \<Longrightarrow>  cdcl\<^sub>N\<^sub>O\<^sub>T_inv T \<Longrightarrow> bound_inv A T
    \<Longrightarrow> \<mu> A V \<le> \<mu>_bound A T"
  apply (cases rule: cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy.cases)
     apply simp
    using measure_bound relpowp_imp_rtranclp apply fastforce
   by (metis full0_def full0_unfold measure_bound2 prod.inject)

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restarts_measure_bound:
  "cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy\<^sup>*\<^sup>* (T, a) (V, b) \<Longrightarrow>  cdcl\<^sub>N\<^sub>O\<^sub>T_inv T \<Longrightarrow> bound_inv A T
    \<Longrightarrow> \<mu> A V \<le> \<mu>_bound A T"
  apply (induction rule: rtranclp_induct2)
    apply (simp add: measure_bound2)
  by (metis dual_order.trans fst_conv measure_bound2 r_into_rtranclp rtranclp.rtrancl_refl
    rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_bound_inv rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_inv
    rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restarts_\<mu>_bound)

lemma wf_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy:
  "wf {(T, S). cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy S T \<and> cdcl\<^sub>N\<^sub>O\<^sub>T_inv (fst S)}" (is "wf ?A")
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain g where
    g: "\<And>i. cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy (g i) (g (Suc i))" and
    cdcl\<^sub>N\<^sub>O\<^sub>T_inv_g: "\<And>i. cdcl\<^sub>N\<^sub>O\<^sub>T_inv (fst (g i))"
    unfolding wf_iff_no_infinite_down_chain by fast
  hence "\<And>i. snd (g i) < snd (g (i+1))"
    by (metis Suc_eq_plus1 add.left_neutral add_Suc cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_increasing_number lessI)
  have "strict_mono (snd o g)"
    unfolding strict_mono_def by (smt Suc_eq_plus1 cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_increasing_number comp_def g
      lessI lift_Suc_mono_less semiring_normalization_rules(24))
  { fix i
    have H: "\<And>T Ta m. (cdcl\<^sub>N\<^sub>O\<^sub>T ^^ m) T Ta \<Longrightarrow> no_step cdcl\<^sub>N\<^sub>O\<^sub>T T \<Longrightarrow> m = 0"
      apply (case_tac m) apply simp by (meson relpowp_E2)
    have "\<exists> T m. (cdcl\<^sub>N\<^sub>O\<^sub>T ^^ m) (fst (g i)) T \<and> m \<ge> f (snd (g (i)))"
      using g[of i] apply (cases rule: cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy.cases)
        apply auto[]
      using g[of "Suc i"] apply (cases rule: cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy.cases)
        by (auto simp add: full_def full0_def f_Suc_not_zero dest!: H dest: tranclpD)
  } note H = this
  obtain A where "bound_inv A (fst (g 1))"
    using g[of 0] cdcl\<^sub>N\<^sub>O\<^sub>T_inv_g[of 0] apply (cases rule: cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy.cases)
      apply (metis One_nat_def cdcl\<^sub>N\<^sub>O\<^sub>T_inv exists_bound fst_conv relpowp_imp_rtranclp
        rtranclp_induct)
     apply (metis H f_Suc_not_zero fst_conv full_def le_0_eq relpowp_E2 snd_conv)
    done
  have "strict_mono (\<lambda>j. f (snd (g j)))"
    by (metis \<open>strict_mono (snd \<circ> g)\<close> comp_def mono_f strict_monoD strict_monoI)
  let ?j = "\<mu>_bound A (fst (g 1)) + 1"
  have "f ?j \<ge> ?j"
    by (simp add: mono_f strict_mono_ge_id)
  {
     fix i j
     have cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart: "j \<ge> i \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy\<^sup>*\<^sup>* (g i) (g j)"
       apply (induction j)
         apply simp
       by (metis g le_Suc_eq rtranclp.rtrancl_into_rtrancl rtranclp.rtrancl_refl)
  } note cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy = this
  have "cdcl\<^sub>N\<^sub>O\<^sub>T_inv (fst (g (Suc 0)))"
    by (simp add: cdcl\<^sub>N\<^sub>O\<^sub>T_inv_g)
  have "cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy\<^sup>*\<^sup>* (fst (g 1), snd (g 1)) (fst (g ?j), snd (g ?j))"
    by (simp add: cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy)
  have "\<mu> A (fst (g ?j)) \<le> \<mu>_bound A (fst (g 1))"
    apply (rule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restarts_measure_bound)
    using \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy\<^sup>*\<^sup>* (fst (g 1), snd (g 1)) (fst (g ?j), snd (g ?j))\<close> apply blast
        apply (simp add: cdcl\<^sub>N\<^sub>O\<^sub>T_inv_g)
       using \<open>bound_inv A (fst (g 1))\<close> apply simp
    done
  hence "\<mu> A (fst (g ?j)) \<le> ?j"
    by auto
  have inv: "bound_inv A (fst (g ?j))"
    using \<open>bound_inv A (fst (g 1))\<close> \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_inv (fst (g (Suc 0)))\<close>
    by (meson cdcl\<^sub>N\<^sub>O\<^sub>T_inv_g cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy not_add_less2 not_less
      rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_bound_inv)
  obtain T m where
    cdcl\<^sub>N\<^sub>O\<^sub>T_m: "(cdcl\<^sub>N\<^sub>O\<^sub>T ^^ m) (fst (g ?j)) T" and
    f_m: "f (snd (g ?j)) \<le> m"
    using H[of "?j"] by blast
  have "?j \<le> m"
    using f_m \<open>f ?j \<ge> ?j\<close> Nat.le_trans \<open>strict_mono (\<lambda>j. f (snd (g j)))\<close> strict_mono_ge_id by blast
  thus False
    proof -
      have "\<And>n. bound_inv A (fst (g (n + 1)))"
        by (meson \<open>bound_inv A (fst (g 1))\<close> cdcl\<^sub>N\<^sub>O\<^sub>T_inv_g cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy le_add2
          rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_bound_inv)
      moreover have "\<And>b. \<not> bound_inv b (fst (g (1 + \<mu>_bound A (fst (g 1)))))
          \<or> \<not> 1 + \<mu> b (fst (g (1 + \<mu>_bound A (fst (g 1))))) \<le> m"
        using cdcl\<^sub>N\<^sub>O\<^sub>T_comp_bounded cdcl\<^sub>N\<^sub>O\<^sub>T_inv_g cdcl\<^sub>N\<^sub>O\<^sub>T_m by force
      ultimately show ?thesis
        using \<open>\<mu> A (fst (g (\<mu>_bound A (fst (g 1)) + 1))) \<le> \<mu>_bound A (fst (g 1))\<close>
        \<open>\<mu>_bound A (fst (g 1)) + 1 \<le> m\<close> by fastforce
    qed
qed

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy_steps_bigger_than_bound:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy S T" and
    "bound_inv A (fst S)" and
    "cdcl\<^sub>N\<^sub>O\<^sub>T_inv (fst S)" and
    "f (snd S) > \<mu>_bound A (fst S)"
  shows "full cdcl\<^sub>N\<^sub>O\<^sub>T (fst S) (fst T)"
  using assms
proof (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy.induct)
  case restart_full
  thus ?case by auto
next
  case (restart_step m S T n U) note st = this(1) and f = this(2) and bound_inv = this(4) and
    cdcl\<^sub>N\<^sub>O\<^sub>T_inv =this(5) and \<mu> = this(6)
  then obtain m' where m: "m = Suc m'" by (cases m) auto
  have "\<mu> A S - m' = 0"
    using f bound_inv cdcl\<^sub>N\<^sub>O\<^sub>T_inv \<mu> m rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restarts_measure_bound by fastforce
  hence False using cdcl\<^sub>N\<^sub>O\<^sub>T_comp_n_le[of m' S T A] restart_step unfolding m by simp
  thus ?case by fast
qed

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_inv_inv_rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T:
  assumes
    inv: "cdcl\<^sub>N\<^sub>O\<^sub>T_inv S" and
    binv: "bound_inv A S"
  shows "(\<lambda>S T. cdcl\<^sub>N\<^sub>O\<^sub>T S T \<and> cdcl\<^sub>N\<^sub>O\<^sub>T_inv S \<and> bound_inv A S)\<^sup>*\<^sup>* S T \<longleftrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T"
    (is "?A\<^sup>*\<^sup>* S T \<longleftrightarrow> ?B\<^sup>*\<^sup>* S T")
  apply (rule iffI)
    using rtranclp_mono[of ?A ?B] apply blast
  apply (induction rule: rtranclp_induct)
    using inv binv apply simp
  by (metis (mono_tags, lifting) binv inv rtranclp.simps rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_bound_inv
    rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_inv)

lemma no_step_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy_no_step_cdcl\<^sub>N\<^sub>O\<^sub>T:
  assumes
    n_s: "no_step cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy S" and
    inv: "cdcl\<^sub>N\<^sub>O\<^sub>T_inv (fst S)" and
    binv: "bound_inv A (fst S)"
  shows "no_step cdcl\<^sub>N\<^sub>O\<^sub>T (fst S)"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain T where T: "cdcl\<^sub>N\<^sub>O\<^sub>T (fst S) T"
    by blast
  then obtain U where U: "full0 (\<lambda>S T. cdcl\<^sub>N\<^sub>O\<^sub>T S T \<and> cdcl\<^sub>N\<^sub>O\<^sub>T_inv S \<and> bound_inv A S) T U"
     using wf_exists_normal_form_full0[OF wf_cdcl\<^sub>N\<^sub>O\<^sub>T, of A T] by auto
  moreover have inv_T: "cdcl\<^sub>N\<^sub>O\<^sub>T_inv T"
    using \<open>cdcl\<^sub>N\<^sub>O\<^sub>T (fst S) T\<close> cdcl\<^sub>N\<^sub>O\<^sub>T_inv inv by blast
  moreover have b_inv_T: "bound_inv A T"
    using \<open>cdcl\<^sub>N\<^sub>O\<^sub>T (fst S) T\<close> binv bound_inv inv by blast
  ultimately have "full0 cdcl\<^sub>N\<^sub>O\<^sub>T T U"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_inv_inv_rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_bound_inv
    rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_inv unfolding full0_def by blast
  then have "full cdcl\<^sub>N\<^sub>O\<^sub>T (fst S) U"
    using T full0_fullI by metis
  then show False by (metis n_s prod.collapse restart_full)
qed

end

subsection \<open>Combining backjump and learning\<close>
locale cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_ops =
  dpll_state trail clauses update_trail update_cls +
  decide_ops trail clauses update_trail update_cls +
  forget_ops trail clauses update_trail update_cls forget_cond +
  propagate_ops trail clauses update_trail update_cls propagate_conds
  for
    trail :: "'st \<Rightarrow> ('v, dpll_marked_level, dpll_mark) annoted_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    update_trail :: "('v, dpll_marked_level, dpll_mark) annoted_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_cls :: "'v clause set \<Rightarrow> 'st \<Rightarrow> 'st" and
    propagate_conds :: "'st \<Rightarrow> bool" and
    forget_cond :: "'v clause \<Rightarrow> 'st \<Rightarrow> bool" +
  fixes backjump_l_cond :: "'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> bool"
begin
inductive backjump_l where
backjump_l: "trail S = F' @ Marked K d # F
   \<Longrightarrow> no_dup (trail S)
   \<Longrightarrow> T \<sim> update_trail (Propagated L l # F) (add_cls\<^sub>N\<^sub>O\<^sub>T (C' + {#L#}) S)
   \<Longrightarrow> C \<in> clauses S
   \<Longrightarrow> trail S \<Turnstile>as CNot C
   \<Longrightarrow> undefined_lit L F
   \<Longrightarrow> atm_of L \<in> atms_of_m (clauses S) \<union> atm_of ` (lits_of (trail S))
   \<Longrightarrow> clauses S \<Turnstile>p C' + {#L#}
   \<Longrightarrow> F \<Turnstile>as CNot C'
   \<Longrightarrow> backjump_l_cond C' L T
   \<Longrightarrow> backjump_l S T"
inductive_cases backjump_lE: "backjump_l S T"

inductive cdcl\<^sub>N\<^sub>O\<^sub>T_merged :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
cdcl\<^sub>N\<^sub>O\<^sub>T_merged_decide\<^sub>N\<^sub>O\<^sub>T:  "decide\<^sub>N\<^sub>O\<^sub>T S S' \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_merged S S'" |
cdcl\<^sub>N\<^sub>O\<^sub>T_merged_propagate\<^sub>N\<^sub>O\<^sub>T: "propagate\<^sub>N\<^sub>O\<^sub>T S S' \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_merged S S'" |
cdcl\<^sub>N\<^sub>O\<^sub>T_merged_backjump_l:  "backjump_l S S' \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_merged S S'" |
cdcl\<^sub>N\<^sub>O\<^sub>T_merged_forget\<^sub>N\<^sub>O\<^sub>T: "forget\<^sub>N\<^sub>O\<^sub>T S S' \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_merged S S'"

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_merged_no_dup_inv:
  "cdcl\<^sub>N\<^sub>O\<^sub>T_merged S T \<Longrightarrow> no_dup (trail S) \<Longrightarrow> no_dup (trail T)"
  apply (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_merged.induct)
      using defined_lit_map apply fastforce
    using defined_lit_map apply fastforce
   apply (auto simp: defined_lit_map elim: backjump_lE)[]
  using forget\<^sub>N\<^sub>O\<^sub>T.simps apply auto[1]
  done
end

locale cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_proxy =
  cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_ops trail clauses update_trail update_cls propagate_conds
    forget_conds "\<lambda>C L S.  backjump_l_cond C L S \<and> distinct_mset (C + {#L#})
    \<and> \<not>tautology (C + {#L#})"
  for
    trail :: "'st \<Rightarrow> ('v, dpll_marked_level, dpll_mark) annoted_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    update_trail :: "('v, dpll_marked_level, dpll_mark) annoted_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_cls :: "'v clause set \<Rightarrow> 'st \<Rightarrow> 'st" and
    propagate_conds :: "'st \<Rightarrow> bool" and
    forget_conds :: "'v clause \<Rightarrow> 'st \<Rightarrow> bool" and
    backjump_l_cond :: "'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> bool" +
  fixes
    inv :: "'st \<Rightarrow> bool"
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
       \<Longrightarrow> \<not>no_step backjump_l S" and
     cdcl_merged_inv: "\<And>S T. cdcl\<^sub>N\<^sub>O\<^sub>T_merged S T \<Longrightarrow> inv S \<Longrightarrow> inv T"
begin
abbreviation backjump_conds where
"backjump_conds \<equiv> \<lambda>C L _ _.  distinct_mset (C + {#L#}) \<and> \<not>tautology (C + {#L#})"

sublocale dpll_with_backjumping_ops trail clauses update_trail update_cls propagate_conds
   inv backjump_conds
proof (unfold_locales, goal_cases)
  case 1
  { fix S S'
    assume bj: "backjump_l S S'"
    then obtain F' K d F L l C' C where
      S': "S' \<sim> update_trail (Propagated L l # F) (add_cls\<^sub>N\<^sub>O\<^sub>T (C' + {#L#}) S)" and
      tr_S: "trail S = F' @ Marked K d # F" and
      C: "C \<in> clauses S" and
      tr_S_C: "trail S \<Turnstile>as CNot C" and
      undef_L: "undefined_lit L F" and
      atm_L: "atm_of L \<in> atms_of_m (clauses S) \<union> atm_of ` lits_of (trail S)" and
      cls_S_C': "clauses S \<Turnstile>p C' + {#L#}" and
      F_C': "F \<Turnstile>as CNot C'" and
      dist: "distinct_mset (C' + {#L#})" and
      not_tauto: "\<not> tautology (C' + {#L#})"
      by (auto elim!: backjump_lE)

    have "\<exists>S'. backjumping_ops.backjump trail clauses update_trail backjump_conds S S'"
      apply rule
      apply (rule backjumping_ops.backjump.intros)
                apply unfold_locales
               using tr_S apply simp
              apply (rule state_eq\<^sub>N\<^sub>O\<^sub>T_ref)
             using C apply simp
            using tr_S_C apply simp
          using undef_L apply simp
         using atm_L apply simp
        using cls_S_C' apply simp
       using F_C' apply simp
      using dist not_tauto apply simp
      done
    } note H = this(1)
  then show ?case using 1 bj_can_jump by presburger
qed

end

locale cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_proxy2 =
  cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_proxy trail clauses update_trail update_cls propagate_conds
     forget_conds backjump_l_cond inv
  for
    trail :: "'st \<Rightarrow> ('v, dpll_marked_level, dpll_mark) annoted_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    update_trail :: "('v, dpll_marked_level, dpll_mark) annoted_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_cls :: "'v clause set \<Rightarrow> 'st \<Rightarrow> 'st" and
    propagate_conds :: "'st \<Rightarrow> bool" and
    inv :: "'st \<Rightarrow> bool" and
    forget_conds :: "'v clause \<Rightarrow> 'st \<Rightarrow> bool" and
    backjump_l_cond :: "'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> bool"
begin

sublocale conflict_driven_clause_learning_ops trail clauses update_trail update_cls propagate_conds
   inv backjump_conds "\<lambda>C _.  distinct_mset C \<and> \<not>tautology C" forget_conds
  by unfold_locales
end

locale cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn =
  cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_proxy2 trail clauses update_trail update_cls propagate_conds
    inv forget_conds backjump_l_cond
  for
    trail :: "'st \<Rightarrow> ('v, dpll_marked_level, dpll_mark) annoted_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    update_trail :: "('v, dpll_marked_level, dpll_mark) annoted_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_cls :: "'v clause set \<Rightarrow> 'st \<Rightarrow> 'st" and
    propagate_conds :: "'st \<Rightarrow> bool" and
    inv :: "'st \<Rightarrow> bool" and
    forget_conds :: "'v clause \<Rightarrow> 'st \<Rightarrow> bool" and
    backjump_l_cond :: "'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> bool" +
  assumes
     dpll_bj_inv: "\<And>S T.  dpll_bj S T \<Longrightarrow> inv S \<Longrightarrow> inv T" and
     learn_inv: "\<And>S T. learn S T \<Longrightarrow> inv S \<Longrightarrow> inv T"
begin

interpretation cdcl\<^sub>N\<^sub>O\<^sub>T:
   conflict_driven_clause_learning trail clauses update_trail update_cls propagate_conds
   inv backjump_conds "\<lambda>C _. distinct_mset C \<and> \<not>tautology C" forget_conds
  apply unfold_locales
  using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_forget\<^sub>N\<^sub>O\<^sub>T cdcl_merged_inv learn_inv
  by (auto simp add: cdcl\<^sub>N\<^sub>O\<^sub>T.simps dpll_bj_inv)

lemma backjump_l_learn_backjump:
  assumes bt: "backjump_l S T" and inv: "inv S"
  shows "\<exists>C' L. learn S (add_cls\<^sub>N\<^sub>O\<^sub>T (C' + {#L#}) S)
    \<and> backjump (add_cls\<^sub>N\<^sub>O\<^sub>T (C' + {#L#}) S) T
    \<and> atms_of (C' + {#L#}) \<subseteq> atms_of_m (clauses S) \<union> atm_of ` (lits_of (trail S))"
proof -
   obtain C F' K d F L l C' where
     tr_S: "trail S = F' @ Marked K d # F" and
     T: "T \<sim> update_trail (Propagated L l # F) (add_cls\<^sub>N\<^sub>O\<^sub>T (C' + {#L#}) S)" and
     C_cls_S: "C \<in> clauses S" and
     tr_S_CNot_C: "trail S \<Turnstile>as CNot C" and
     undef: "undefined_lit L F" and
     atm_L: "atm_of L \<in> atms_of_m (clauses S) \<union> atm_of ` (lits_of (trail S))" and
     clss_C: "clauses S \<Turnstile>p C' + {#L#}" and
     "F \<Turnstile>as CNot C'" and
     distinct:  "distinct_mset (C' + {#L#})" and
     not_tauto: "\<not> tautology (C' + {#L#})"
     using bt inv by (auto elim!: backjump_lE)
   have atms_C':  "atms_of C' \<subseteq>  atm_of ` (lits_of F)"
     proof -
       obtain ll :: "'v \<Rightarrow> ('v literal \<Rightarrow> 'v) \<Rightarrow> 'v literal set \<Rightarrow> 'v literal" where
         "\<forall>v f L. v \<notin> f ` L \<or> v = f (ll v f L) \<and> ll v f L \<in> L"
         by moura
       thus ?thesis unfolding tr_S
         by (metis (no_types) \<open>F \<Turnstile>as CNot C'\<close> atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
           atms_of_def in_CNot_implies_uminus(2) mem_set_mset_iff subsetI)
     qed
   hence "atms_of (C' + {#L#}) \<subseteq> atms_of_m (clauses S) \<union> atm_of ` (lits_of (trail S))"
     using atm_L tr_S by auto
   moreover have learn: "learn S (add_cls\<^sub>N\<^sub>O\<^sub>T (C' + {#L#}) S)"
     apply (rule learn.intros)
         apply (rule clss_C)
       using atms_C' atm_L apply (fastforce simp add: tr_S  in_plus_implies_atm_of_on_atms_of_m)[]
     apply standard
      apply (rule distinct)
      apply (rule not_tauto)
      apply simp
     done
   moreover have bj: "backjump (add_cls\<^sub>N\<^sub>O\<^sub>T (C' + {#L#}) S) T"
     apply (rule backjumping_ops.backjump.intros[OF backjumping_ops_axioms _, of _ _ ])
     using \<open>F \<Turnstile>as CNot C'\<close> C_cls_S tr_S_CNot_C undef T distinct not_tauto
     by (auto simp: tr_S state_eq\<^sub>N\<^sub>O\<^sub>T_def simp del: state_simp\<^sub>N\<^sub>O\<^sub>T)
   ultimately show ?thesis by auto
qed

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_merged_is_tranclp_cdcl\<^sub>N\<^sub>O\<^sub>T:
  "cdcl\<^sub>N\<^sub>O\<^sub>T_merged S T \<Longrightarrow> inv S \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>+\<^sup>+ S T"
proof (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_merged.induct)
  case (cdcl\<^sub>N\<^sub>O\<^sub>T_merged_decide\<^sub>N\<^sub>O\<^sub>T S T)
  hence "cdcl\<^sub>N\<^sub>O\<^sub>T S T"
    using bj_decide\<^sub>N\<^sub>O\<^sub>T cdcl\<^sub>N\<^sub>O\<^sub>T.simps by fastforce
  thus ?case by auto
next
  case (cdcl\<^sub>N\<^sub>O\<^sub>T_merged_propagate\<^sub>N\<^sub>O\<^sub>T S T)
  hence "cdcl\<^sub>N\<^sub>O\<^sub>T S T"
    using bj_propagate\<^sub>N\<^sub>O\<^sub>T cdcl\<^sub>N\<^sub>O\<^sub>T.simps by fastforce
  thus ?case by auto
next
   case (cdcl\<^sub>N\<^sub>O\<^sub>T_merged_forget\<^sub>N\<^sub>O\<^sub>T S T)
   hence "cdcl\<^sub>N\<^sub>O\<^sub>T S T"
     using c_forget\<^sub>N\<^sub>O\<^sub>T by blast
   thus ?case by auto
next
   case (cdcl\<^sub>N\<^sub>O\<^sub>T_merged_backjump_l S T) note bt = this(1) and inv = this(2)
   show ?case
     using backjump_l_learn_backjump[OF bt inv]
     by (metis (no_types, lifting) bj_backjump c_dpll_bj c_learn
       tranclp.r_into_trancl tranclp.trancl_into_trancl)
qed

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_is_rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_and_inv:
  "cdcl\<^sub>N\<^sub>O\<^sub>T_merged\<^sup>*\<^sup>* S T \<Longrightarrow> inv S \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T \<and> inv T"
proof (induction rule: rtranclp_induct)
  case base
  thus ?case by auto
next
  case (step T U) note st =this(1) and cdcl\<^sub>N\<^sub>O\<^sub>T = this(2) and IH = this(3)[OF this(4)] and
    inv = this(4)
  have "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* T U"
    using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_is_tranclp_cdcl\<^sub>N\<^sub>O\<^sub>T[OF cdcl\<^sub>N\<^sub>O\<^sub>T] IH by (blast dest: tranclp_into_rtranclp)
  hence "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S U" using IH by fastforce
  moreover have "inv U" using IH \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* T U\<close> cdcl\<^sub>N\<^sub>O\<^sub>T.rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_inv by blast
  ultimately show ?case using st by fast
qed

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_is_rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T:
  "cdcl\<^sub>N\<^sub>O\<^sub>T_merged\<^sup>*\<^sup>* S T \<Longrightarrow> inv S \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T"
  using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_is_rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_and_inv by blast

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_inv:
  "cdcl\<^sub>N\<^sub>O\<^sub>T_merged\<^sup>*\<^sup>* S T \<Longrightarrow> inv S \<Longrightarrow> inv T"
  using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_is_rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_and_inv by blast

definition \<mu>\<^sub>C' :: "'a literal multiset set \<Rightarrow> 'st \<Rightarrow> nat" where
"\<mu>\<^sub>C' A T \<equiv> \<mu>\<^sub>C (1+card (atms_of_m A)) (2+card (atms_of_m A)) (trail_weight T)"

definition \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged :: "'a literal multiset set \<Rightarrow> 'st \<Rightarrow> nat" where
"\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged A T \<equiv>
  ((2+card (atms_of_m A)) ^ (1+card (atms_of_m A)) - \<mu>\<^sub>C' A T) * 2 + card (clauses T)"

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_decreasing_measure':
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T_merged S T" and
    "inv S"
    "atms_of_m (clauses S) \<subseteq> atms_of_m A"
    "atm_of ` lits_of (trail S) \<subseteq> atms_of_m A" and
    "no_dup (trail S)" and
    "finite (clauses S)" and
    fin_A: "finite A"
  shows "\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged A T < \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged A S"
  using assms(1-6)
proof induction
  case (cdcl\<^sub>N\<^sub>O\<^sub>T_merged_decide\<^sub>N\<^sub>O\<^sub>T S T)
  have "clauses S = clauses T"
    using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_decide\<^sub>N\<^sub>O\<^sub>T.hyps clauses_update_trail by auto
  moreover have
    "(2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A))
       - \<mu>\<^sub>C (1 + card (atms_of_m A)) (2 + card (atms_of_m A)) (trail_weight T)
     < (2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A))
       - \<mu>\<^sub>C (1 + card (atms_of_m A)) (2 + card (atms_of_m A)) (trail_weight S)"
    apply (rule dpll_bj_trail_mes_decreasing_prop)
     using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_decide\<^sub>N\<^sub>O\<^sub>T fin_A by (simp_all add: bj_decide\<^sub>N\<^sub>O\<^sub>T cdcl\<^sub>N\<^sub>O\<^sub>T_merged_decide\<^sub>N\<^sub>O\<^sub>T.hyps)
  ultimately show ?case
    unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged_def \<mu>\<^sub>C'_def by simp
next
  case (cdcl\<^sub>N\<^sub>O\<^sub>T_merged_propagate\<^sub>N\<^sub>O\<^sub>T S T)
  have "clauses S = clauses T"
    using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_propagate\<^sub>N\<^sub>O\<^sub>T.hyps
    by (simp add: bj_propagate\<^sub>N\<^sub>O\<^sub>T cdcl\<^sub>N\<^sub>O\<^sub>T_merged_propagate\<^sub>N\<^sub>O\<^sub>T.prems(1) dpll_bj_clauses)
  moreover have
    "(2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A))
       - \<mu>\<^sub>C (1 + card (atms_of_m A)) (2 + card (atms_of_m A)) (trail_weight T)
     < (2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A))
       - \<mu>\<^sub>C (1 + card (atms_of_m A)) (2 + card (atms_of_m A)) (trail_weight S)"
    apply (rule dpll_bj_trail_mes_decreasing_prop)
    using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_propagate\<^sub>N\<^sub>O\<^sub>T fin_A by (simp_all add: bj_propagate\<^sub>N\<^sub>O\<^sub>T
      cdcl\<^sub>N\<^sub>O\<^sub>T_merged_propagate\<^sub>N\<^sub>O\<^sub>T.hyps)
  ultimately show ?case
    unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged_def \<mu>\<^sub>C'_def by simp
next
  case (cdcl\<^sub>N\<^sub>O\<^sub>T_merged_forget\<^sub>N\<^sub>O\<^sub>T S T)
  have "card (clauses T) < card (clauses S)"
    using \<open>forget\<^sub>N\<^sub>O\<^sub>T S T\<close> \<open>finite (clauses S)\<close> by (metis card_Diff1_less clause_remove_cls\<^sub>N\<^sub>O\<^sub>T
      forget\<^sub>N\<^sub>O\<^sub>T.cases state_eq\<^sub>N\<^sub>O\<^sub>T_clauses)
  moreover
    have "trail S = trail T"
      using \<open>forget\<^sub>N\<^sub>O\<^sub>T S T\<close> by (auto elim: forgetE)
    hence
      "(2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A))
        - \<mu>\<^sub>C (1 + card (atms_of_m A)) (2 + card (atms_of_m A)) (trail_weight T)
       = (2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A))
        - \<mu>\<^sub>C (1 + card (atms_of_m A)) (2 + card (atms_of_m A)) (trail_weight S)"
       by auto
  ultimately show ?case
    unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged_def \<mu>\<^sub>C'_def by simp
next
  case (cdcl\<^sub>N\<^sub>O\<^sub>T_merged_backjump_l S T) note bj_l = this(1) and inv = this(2) and atms_clss = this(3)
    and atms_trail = this(4) and n_d = this(5)
  obtain C' L where
    learn: "learn S (add_cls\<^sub>N\<^sub>O\<^sub>T (C' + {#L#}) S)" and
    bj: "backjump (add_cls\<^sub>N\<^sub>O\<^sub>T (C' + {#L#}) S) T" and
    atms_C: "atms_of (C' + {#L#}) \<subseteq> atms_of_m (clauses S) \<union> atm_of ` (lits_of (trail S))"
    using bj_l inv backjump_l_learn_backjump by blast
  have "card (clauses T) \<le>1+  card (clauses S)"
    using bj_l inv \<open>finite (clauses S)\<close> by (auto elim!: backjump_lE simp: card_insert_if)
  have
    "((2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A))
      - \<mu>\<^sub>C (1 + card (atms_of_m A)) (2 + card (atms_of_m A)) (trail_weight T))
    < ((2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A))
      - \<mu>\<^sub>C (1 + card (atms_of_m A)) (2 + card (atms_of_m A))
           (trail_weight (add_cls\<^sub>N\<^sub>O\<^sub>T (C' + {#L#}) S)))"
    apply (rule dpll_bj_trail_mes_decreasing_prop)
         using bj bj_backjump apply blast
        using cdcl\<^sub>N\<^sub>O\<^sub>T.c_learn cdcl\<^sub>N\<^sub>O\<^sub>T.cdcl\<^sub>N\<^sub>O\<^sub>T_inv inv learn apply blast
       using atms_C atms_clss atms_trail apply fastforce
      using atms_trail apply simp
     apply (simp add: n_d)
    using fin_A apply simp
    done
  hence "((2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A))
      - \<mu>\<^sub>C (1 + card (atms_of_m A)) (2 + card (atms_of_m A)) (trail_weight T))
    < ((2 + card (atms_of_m A)) ^ (1 + card (atms_of_m A))
      - \<mu>\<^sub>C (1 + card (atms_of_m A)) (2 + card (atms_of_m A)) (trail_weight S))"
    by auto
  then show ?case
    using \<open>card (clauses T) \<le> 1+ card (clauses S)\<close>
    unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged_def \<mu>\<^sub>C'_def
    by linarith
qed

lemma wf_cdcl\<^sub>N\<^sub>O\<^sub>T_merged:
  assumes
    fin_A: "finite A"
  shows "wf {(T, S).
    (inv S \<and> atms_of_m (clauses S) \<subseteq> atms_of_m A \<and> atm_of ` lits_of (trail S) \<subseteq> atms_of_m A
    \<and> no_dup (trail S) \<and> finite (clauses S))
    \<and> cdcl\<^sub>N\<^sub>O\<^sub>T_merged S T}"
  apply (rule wfP_if_measure[of _ _ "\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged A"])
  using cdcl\<^sub>N\<^sub>O\<^sub>T_decreasing_measure' fin_A by simp

lemma tranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_tranclp:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T_merged\<^sup>+\<^sup>+ S T" and
    "inv S" and
    "atms_of_m (clauses S) \<subseteq> atms_of_m A" and
    "atm_of ` lits_of (trail S) \<subseteq> atms_of_m A" and
    "no_dup (trail S)" and
    "finite (clauses S)" and
    "finite A"
  shows "(T, S) \<in> {(T, S).
    (inv S \<and> atms_of_m (clauses S) \<subseteq> atms_of_m A \<and> atm_of ` lits_of (trail S) \<subseteq> atms_of_m A
    \<and> no_dup (trail S) \<and> finite (clauses S))
    \<and> cdcl\<^sub>N\<^sub>O\<^sub>T_merged S T}\<^sup>+" (is "_ \<in> ?P\<^sup>+")
  using assms(1-6)
proof (induction rule: tranclp_induct)
  case base
  thus ?case by auto
next
  case (step T U) note st = this(1) and cdcl\<^sub>N\<^sub>O\<^sub>T = this(2) and IH = this(3)[OF this(4-8)] and
    inv = this(4) and atms_clss = this(5) and atms_trail = this(6) and n_d = this(7) and
    fin = this(8)
  have "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T"
    apply (rule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_is_rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T)
    using st cdcl\<^sub>N\<^sub>O\<^sub>T inv by auto
  have "inv T"
    apply (rule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_inv)
      using inv st cdcl\<^sub>N\<^sub>O\<^sub>T by auto
  moreover have "atms_of_m (clauses T) \<subseteq> atms_of_m A"
    using cdcl\<^sub>N\<^sub>O\<^sub>T.rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_trail_clauses_bound[OF \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T\<close> inv atms_clss atms_trail]
    by fast
  moreover have "atm_of ` (lits_of (trail T))\<subseteq> atms_of_m A"
    using cdcl\<^sub>N\<^sub>O\<^sub>T.rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_trail_clauses_bound[OF \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T\<close> inv atms_clss atms_trail]
    by fast
  moreover have "no_dup (trail T)"
    using cdcl\<^sub>N\<^sub>O\<^sub>T.rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup[OF  \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T\<close> inv n_d] by fast
  moreover have "finite (clauses T)"
    using cdcl\<^sub>N\<^sub>O\<^sub>T.rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_finite_clauses[OF  \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T\<close> inv fin] by fast
  ultimately have "(U, T) \<in> ?P"
    using cdcl\<^sub>N\<^sub>O\<^sub>T by auto
  thus ?case using IH by (simp add: trancl_into_trancl2)
qed

lemma wf_tranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged:
  assumes "finite A"
  shows "wf {(T, S).
    (inv S \<and> atms_of_m (clauses S) \<subseteq> atms_of_m A \<and> atm_of ` lits_of (trail S) \<subseteq> atms_of_m A
    \<and> no_dup (trail S) \<and> finite (clauses S))
    \<and> cdcl\<^sub>N\<^sub>O\<^sub>T_merged\<^sup>+\<^sup>+ S T}"
  apply (rule wf_subset)
   apply (rule wf_trancl[OF wf_cdcl\<^sub>N\<^sub>O\<^sub>T_merged])
   using assms apply simp
  using tranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_tranclp[OF _ _ _ _ _ _ \<open>finite A\<close>] by auto

lemma backjump_no_step_backjump_l:
  "backjump S T \<Longrightarrow> inv S \<Longrightarrow> \<not>no_step backjump_l S"
  apply (elim backjumpE)
  apply (rule bj_can_jump)
    apply auto[7]
  by blast

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_merged_normal_forms:
  fixes A :: "'v literal multiset set" and S T :: "'st"
  assumes
    n_s: "no_step cdcl\<^sub>N\<^sub>O\<^sub>T_merged S" and
    atms_S: "atms_of_m (clauses S) \<subseteq> atms_of_m A" and
    atms_trail: "atm_of ` lits_of (trail S) \<subseteq> atms_of_m A" and
    n_d: "no_dup (trail S)" and
    "finite A" and
    inv: "inv S" and
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
        using tot atms_of_s_def unfolding total_over_m_def total_over_set_def
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
          have "decide\<^sub>N\<^sub>O\<^sub>T S (prepend_trail (Marked (Pos l) Level) S)"
            by (metis \<open>|Pos l| \<notin>\<^sub>l |trail S|\<close> decide\<^sub>N\<^sub>O\<^sub>T.intros l_N literal.sel(1) state_eq\<^sub>N\<^sub>O\<^sub>T_ref)
          then show False
            using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_decide\<^sub>N\<^sub>O\<^sub>T n_s by blast
        qed

      have "?M \<Turnstile>as CNot C"
        by (metis atms_N_M \<open>C \<in> ?N\<close> \<open>\<not> ?M \<Turnstile>a C\<close> all_variables_defined_not_imply_cnot
          atms_of_atms_of_m_mono atms_of_m_CNot_atms_of atms_of_m_CNot_atms_of_m subsetCE)
      have "\<exists>l \<in> set ?M. is_marked l"
        proof (rule ccontr)
          let ?O = "{{#lit_of L#} |L. is_marked L \<and> L \<in> set ?M \<and> atm_of (lit_of L) \<notin> atms_of_m ?N}"
          have \<theta>[iff]: "\<And>I. total_over_m I (?N \<union> ?O \<union> (\<lambda>a. {#lit_of a#}) ` set ?M)
            \<longleftrightarrow> total_over_m I (?N \<union>(\<lambda>a. {#lit_of a#}) ` set ?M)"
            unfolding total_over_set_def total_over_m_def atms_of_m_def by auto
          assume "\<not> ?thesis"
          hence [simp]:"{{#lit_of L#} |L. is_marked L \<and> L \<in> set ?M}
            = {{#lit_of L#} |L. is_marked L \<and> L \<in> set ?M \<and> atm_of (lit_of L) \<notin> atms_of_m ?N}"
            by auto
          hence "?N \<union> ?O \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set ?M"
            using all_decomposition_implies_propagated_lits_are_implied[OF decomp] by auto

          hence "?I \<Turnstile>s (\<lambda>a. {#lit_of a#}) ` set ?M"
            using cons_I' I'_N tot_I' \<open>?I \<Turnstile>s ?N \<union> ?O\<close> unfolding \<theta> true_clss_clss_def by blast
          hence "lits_of ?M \<subseteq> ?I"
            unfolding true_clss_def lits_of_def by auto
          hence "?M \<Turnstile>as ?N"
            using I'_N \<open>C \<in> ?N\<close> \<open>\<not> ?M \<Turnstile>a C\<close> cons_I' atms_N_M
            by (meson \<open>trail S \<Turnstile>as CNot C\<close> consistent_CNot_not rev_subsetD sup_ge1 true_annot_def
              true_annots_def true_cls_mono_set_mset_l true_clss_def)
          thus False using M by fast
        qed
      from List.split_list_first_propE[OF this] obtain K :: "'v literal" and d :: dpll_marked_level and
        F F' :: "('v, dpll_marked_level, dpll_mark) marked_lit list" where
        M_K: "?M = F' @ Marked K d # F" and
        nm: "\<forall>f\<in>set F'. \<not>is_marked f"
        unfolding is_marked_def by metis
      let ?K = "Marked K d::('v, dpll_marked_level, dpll_mark) marked_lit"
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
            { fix x :: "('v, dpll_marked_level, dpll_mark) marked_lit"
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
          \<open>C\<in>?N\<close> n_s \<open>?M \<Turnstile>as CNot C\<close> bj_backjump inv unfolding M_K by (metis (no_types, lifting)
            Un_iff atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set cdcl\<^sub>N\<^sub>O\<^sub>T_merged_backjump_l
            defined_lit_uminus insert_iff lits_of_append lits_of_cons marked_lit.sel(1)
            uminus_of_uminus_id)
        thus ?thesis by fast
    qed auto
qed

lemma full0_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_normal_forms:
  fixes A :: "'v literal multiset set" and S T :: "'st"
  assumes
    full: "full0 cdcl\<^sub>N\<^sub>O\<^sub>T_merged S T" and
    atms_S: "atms_of_m (clauses S) \<subseteq> atms_of_m A" and
    atms_trail: "atm_of ` lits_of (trail S) \<subseteq> atms_of_m A" and
    n_d: "no_dup (trail S)" and
    "finite A" and
    inv: "inv S" and
    decomp: "all_decomposition_implies (clauses S) (get_all_marked_decomposition (trail S))"
  shows "unsatisfiable (clauses T) \<or> (trail T \<Turnstile>as clauses T \<and> satisfiable (clauses T))"
proof -
  have st: "cdcl\<^sub>N\<^sub>O\<^sub>T_merged\<^sup>*\<^sup>* S T" and n_s: "no_step cdcl\<^sub>N\<^sub>O\<^sub>T_merged T"
    using full unfolding full0_def by blast+
  then have st: "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T"
    using inv rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_is_rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_and_inv by auto
  have "atms_of_m (clauses T) \<subseteq> atms_of_m A" and "atm_of ` lits_of (trail T) \<subseteq> atms_of_m A"
    using cdcl\<^sub>N\<^sub>O\<^sub>T.rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_trail_clauses_bound[OF st inv atms_S atms_trail] by blast+
  moreover have "no_dup (trail T)"
    using cdcl\<^sub>N\<^sub>O\<^sub>T.rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup inv n_d st by blast
  moreover have "inv T"
    using cdcl\<^sub>N\<^sub>O\<^sub>T.rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_inv inv st by blast
  moreover have "all_decomposition_implies (clauses T) (get_all_marked_decomposition (trail T))"
    using cdcl\<^sub>N\<^sub>O\<^sub>T.rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_all_decomposition_implies inv st decomp by blast
  ultimately show ?thesis
    using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_normal_forms[of T A] \<open>finite A\<close> n_s by fast
qed

end

subsubsection \<open>Instantiations\<close>
locale dpll_withbacktrack_and_restarts =
  dpll_with_backtrack +
  fixes f :: "nat \<Rightarrow> nat"
  assumes strict_mono: "strict_mono f"
begin
  sublocale cdcl\<^sub>N\<^sub>O\<^sub>T_increasing_restarts fst snd "\<lambda>M S. (M, snd S)" "\<lambda>N (M, _). (M, N)"
  f "\<lambda>(_, N) S. S = ([], N)"
  "\<lambda>A (M, N). atms_of_m N \<subseteq> atms_of_m A \<and> atm_of ` lits_of M \<subseteq> atms_of_m A \<and> finite A
    \<and> all_decomposition_implies N (get_all_marked_decomposition M)"
  "\<lambda>A T. (2+card (atms_of_m A)) ^ (1+card (atms_of_m A))
               - \<mu>\<^sub>C (1+card (atms_of_m A)) (2+card (atms_of_m A)) (trail_weight T)" dpll_bj
  "\<lambda>(M, N). finite N \<and> no_dup M \<and> all_decomposition_implies N (get_all_marked_decomposition M)"
  "\<lambda>A _.  (2+card (atms_of_m A)) ^ (1+card (atms_of_m A))"
  apply unfold_locales
         apply (rule strict_mono)
        apply (smt dpll_bj_all_decomposition_implies_inv dpll_bj_atms_in_trail_in_set
          dpll_bj_clauses dpll_bj_no_dup prod.case_eq_if)
       apply (rule dpll_bj_trail_mes_decreasing_prop; auto)
      apply (case_tac T, simp)
     apply (case_tac U, simp)
    using dpll_bj_clauses dpll_bj_all_decomposition_implies_inv dpll_bj_no_dup by fastforce+
end

locale cdcl\<^sub>N\<^sub>O\<^sub>T_with_backtrack_and_restarts =
  conflict_driven_clause_learning_learning_before_backjump_only_distinct_learnt trail clauses
  update_trail update_cls propagate_conds inv backjump_conds learn_restrictions forget_restrictions
    for
    trail :: "'st \<Rightarrow> ('v::linorder, dpll_marked_level, dpll_mark) annoted_lits" and
    clauses :: "'st \<Rightarrow> 'v::linorder clauses" and
    update_trail :: "('v, dpll_marked_level, dpll_mark) annoted_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_cls :: "'v clause set \<Rightarrow> 'st \<Rightarrow> 'st" and
    propagate_conds :: "'st \<Rightarrow> bool" and
    inv :: "'st \<Rightarrow> bool" and
    backjump_conds :: "'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool" and
    learn_restrictions forget_restrictions :: "'v::linorder clause \<Rightarrow> 'st \<Rightarrow> bool"
    +
  fixes f :: "nat \<Rightarrow> nat"
  assumes
    strict_mono: "strict_mono f" and f_0: "f 0 = 0" and
    inv_restart:"\<And>S T. inv S \<Longrightarrow> T \<sim> update_trail [] S \<Longrightarrow> inv T"
begin

lemma bound_inv_inv:
  assumes
    "inv S" and
    "no_dup (trail S)" and
    "finite (clauses S)" and
    atms_clss_S_A: "atms_of_m (clauses S) \<subseteq> atms_of_m A" and
    atms_trail_S_A:"atm_of ` lits_of (trail S) \<subseteq> atms_of_m A" and
    "finite A" and
    cdcl\<^sub>N\<^sub>O\<^sub>T: "cdcl\<^sub>N\<^sub>O\<^sub>T S T"
  shows
    "atms_of_m (clauses T) \<subseteq> atms_of_m A" and
    "atm_of ` lits_of (trail T) \<subseteq> atms_of_m A" and
    "finite A"
proof -
  have "cdcl\<^sub>N\<^sub>O\<^sub>T S T"
    using \<open>inv S\<close> cdcl\<^sub>N\<^sub>O\<^sub>T by linarith
  hence "atms_of_m (clauses T) \<subseteq> atms_of_m (clauses S) \<union> atm_of ` lits_of (trail S)"
    using \<open>inv S\<close>
    by (meson conflict_driven_clause_learning_ops.cdcl\<^sub>N\<^sub>O\<^sub>T_atms_of_m_clauses_decreasing
      conflict_driven_clause_learning_ops_axioms)
  thus "atms_of_m (clauses T) \<subseteq> atms_of_m A"
    using atms_clss_S_A atms_trail_S_A by blast
next
  show "atm_of ` lits_of (trail T) \<subseteq> atms_of_m A"
    by (meson \<open>inv S\<close> atms_clss_S_A atms_trail_S_A cdcl\<^sub>N\<^sub>O\<^sub>T cdcl\<^sub>N\<^sub>O\<^sub>T_atms_in_trail_in_set)
next
  show "finite A"
    using \<open>finite A\<close> by simp
qed
  sublocale cdcl\<^sub>N\<^sub>O\<^sub>T_increasing_restarts_ops "\<lambda>S T. T \<sim> update_trail [] S" cdcl\<^sub>N\<^sub>O\<^sub>T  f
    "\<lambda>A S. atms_of_m (clauses S) \<subseteq> atms_of_m A \<and> atm_of ` lits_of (trail S) \<subseteq> atms_of_m A \<and>
    finite A"
    \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' "\<lambda>S. inv S \<and> no_dup (trail S) \<and> finite (clauses S)"
    \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound
    apply unfold_locales
           apply (simp add: strict_mono)
          using bound_inv_inv apply meson
         apply (rule cdcl\<^sub>N\<^sub>O\<^sub>T_decreasing_measure'; simp)
         apply (rule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound; simp)
        apply (rule rtranclp_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_decreasing; simp)
       apply auto[]
      apply (simp add: f_0)
     apply auto[]
    using cdcl\<^sub>N\<^sub>O\<^sub>T_inv cdcl\<^sub>N\<^sub>O\<^sub>T_finite_clauses cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup apply blast
  using inv_restart apply auto[]
  done

abbreviation cdcl\<^sub>N\<^sub>O\<^sub>T_l where
"cdcl\<^sub>N\<^sub>O\<^sub>T_l \<equiv>
  conflict_driven_clause_learning_ops.cdcl\<^sub>N\<^sub>O\<^sub>T trail clauses update_trail update_cls propagate_conds
  (\<lambda>_ _ S T. backjump S T)
  (\<lambda>C S. distinct_mset C \<and> \<not> tautology C \<and> learn_restrictions C S
    \<and> (\<exists>F K d F' C' L. trail S = F' @ Marked K d # F \<and> C = C' + {#L#}
       \<and> F \<Turnstile>as CNot C' \<and> C' + {#L#} \<notin> clauses S))
  (\<lambda>C S. \<not> (\<exists>F' F K d L. trail S = F' @ Marked K d # F \<and> F \<Turnstile>as CNot (C - {#L#}))
  \<and> forget_restrictions C S)"

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_le_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound:
  assumes
    cdcl\<^sub>N\<^sub>O\<^sub>T: "cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy (T, a) (V, b)" and
    cdcl\<^sub>N\<^sub>O\<^sub>T_inv:
      "inv T"
      "no_dup (trail T)"
      "finite (clauses T)" and
    bound_inv:
      "atms_of_m (clauses T) \<subseteq> atms_of_m A"
      "atm_of ` lits_of (trail T) \<subseteq> atms_of_m A"
      "finite A"
  shows "\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' A V \<le> \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A T"
  using cdcl\<^sub>N\<^sub>O\<^sub>T_inv bound_inv
proof (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_induct[OF cdcl\<^sub>N\<^sub>O\<^sub>T])
  case (1 m S T n U) note U = this(3)
  show ?case
    apply (rule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_update_trail[of S T])
         using \<open>(cdcl\<^sub>N\<^sub>O\<^sub>T ^^ m) S T\<close>  apply (fastforce dest!: relpowp_imp_rtranclp)
        using 1 by auto
next
  case (2 S T n) note full = this(2)
  show ?case
    apply (rule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound)
    using full 2 unfolding full_def by force+
qed

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_le_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound:
  assumes
    cdcl\<^sub>N\<^sub>O\<^sub>T: "cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy (T, a) (V, b)" and
    cdcl\<^sub>N\<^sub>O\<^sub>T_inv:
      "inv T"
      "no_dup (trail T)"
      "finite (clauses T)" and
    bound_inv:
      "atms_of_m (clauses T) \<subseteq> atms_of_m A"
      "atm_of ` lits_of (trail T) \<subseteq> atms_of_m A"
      "finite A"
  shows "\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A V \<le> \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A T"
  using cdcl\<^sub>N\<^sub>O\<^sub>T_inv bound_inv
proof (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_induct[OF cdcl\<^sub>N\<^sub>O\<^sub>T])
  case (1 m S T n U) note U = this(3)
  have "\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A T \<le> \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A S"
     apply (rule rtranclp_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_decreasing)
         using \<open>(cdcl\<^sub>N\<^sub>O\<^sub>T ^^ m) S T\<close>  apply (fastforce dest: relpowp_imp_rtranclp)
        using 1 by auto
  then show ?case using U unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_def by auto
next
  case (2 S T n) note full = this(2)
  show ?case
    apply (rule rtranclp_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_decreasing)
    using full 2 unfolding full_def by force+
qed

sublocale cdcl\<^sub>N\<^sub>O\<^sub>T_increasing_restarts _ _ _ _ f
   (* restart *) "\<lambda>S T. T \<sim> update_trail [] S"
   (* bound_inv *)"\<lambda>A S. atms_of_m (clauses S) \<subseteq> atms_of_m A
     \<and> atm_of ` lits_of (trail S) \<subseteq> atms_of_m A \<and> finite A"
   \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' cdcl\<^sub>N\<^sub>O\<^sub>T
   (* inv *) "\<lambda>S. inv S \<and> no_dup (trail S) \<and> finite (clauses S)"
   \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound
  apply unfold_locales
   using cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_le_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound apply simp
  using cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_le_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound apply simp
  done

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy_all_decomposition_implies:
  assumes "cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy S T" and
    "inv (fst S)"
    "all_decomposition_implies (clauses (fst S)) (get_all_marked_decomposition (trail (fst S)))"
  shows
    "all_decomposition_implies (clauses (fst T)) (get_all_marked_decomposition (trail (fst T)))"
  using assms apply (induction)
  using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_all_decomposition_implies by (auto dest!: tranclp_into_rtranclp
    simp: full_def)

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy_all_decomposition_implies:
  assumes "cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy\<^sup>*\<^sup>* S T" and
    "inv (fst S)" and
    "no_dup (trail (fst S))" and
    "finite (clauses (fst S))"
    "all_decomposition_implies (clauses (fst S)) (get_all_marked_decomposition (trail (fst S)))"
  shows
    "all_decomposition_implies (clauses (fst T)) (get_all_marked_decomposition (trail (fst T)))"
  using assms
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by simp
next
  case (step T u) note st = this(1) and r = this(2) and IH = this(3)[OF this(4-)] and inv = this(4)
    and n_d = this(5) and fin = this(6)
  have "inv (fst T)"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_inv[OF st] inv n_d fin by blast
  then show ?case
    using cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy_all_decomposition_implies r IH by fast
qed


lemma cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy_sat_ext_iff:
  assumes
    st: "cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy S T" and
    atms_S: "atms_of_m (clauses (fst S)) \<subseteq> atms_of_m A" and
    atms_trail: "atm_of ` lits_of (trail (fst S)) \<subseteq> atms_of_m A" and
    n_d: "no_dup (trail (fst S))" and
    fin_A[simp]: "finite A" and
    fin_clss_S: "finite (clauses (fst S))" and
    inv: "inv (fst S)"
  shows "I \<Turnstile>sext (clauses (fst S)) \<longleftrightarrow> I \<Turnstile>sext clauses(fst T)"
  using assms
proof (induction)
  case (restart_step m S T n U)
  then show ?case using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_bj_sat_ext_iff by (fastforce dest!: relpowp_imp_rtranclp)
next
  case restart_full
  then show ?case using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_bj_sat_ext_iff unfolding full_def
  by (fastforce dest!: tranclp_into_rtranclp)
qed

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy_sat_ext_iff:
  assumes
    st: "cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy\<^sup>*\<^sup>* S T" and
    atms_S: "atms_of_m (clauses (fst S)) \<subseteq> atms_of_m A" and
    atms_trail: "atm_of ` lits_of (trail (fst S)) \<subseteq> atms_of_m A" and
    n_d: "no_dup (trail (fst S))" and
    fin_A[simp]: "finite A" and
    fin_clss_S: "finite (clauses (fst S))" and
    inv: "inv (fst S)"
  shows "I \<Turnstile>sext (clauses (fst S)) \<longleftrightarrow> I \<Turnstile>sext clauses(fst T)"
  using st
proof (induction)
  case base
  then show ?case by simp
next
  case (step T U) note st = this(1) and r = this(2) and IH = this(3)
  have
    "atms_of_m (clauses (fst T)) \<subseteq> atms_of_m A" and
    "atm_of ` lits_of (trail (fst T)) \<subseteq> atms_of_m A"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_bound_inv[OF st, of A] inv n_d atms_S atms_trail fin_clss_S
    fin_A by blast+
  moreover have "inv (fst T)" and "no_dup (trail (fst T))" and "finite (clauses (fst T))"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_inv[OF st] inv n_d fin_clss_S by blast+
  ultimately show ?case
    using cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy_sat_ext_iff[OF r] IH fin_A by blast
qed

theorem full0_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy_backjump_normal_forms:
  fixes A :: "'v literal multiset set" and S T :: "'st"
  assumes
    full: "full0 cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy (S, n) (T, m)" and
    atms_S: "atms_of_m (clauses S) \<subseteq> atms_of_m A" and
    atms_trail: "atm_of ` lits_of (trail S) \<subseteq> atms_of_m A" and
    n_d: "no_dup (trail S)" and
    fin_A[simp]: "finite A" and
    fin_clss_S: "finite (clauses S)" and
    inv: "inv S" and
    decomp: "all_decomposition_implies (clauses S) (get_all_marked_decomposition (trail S))"
  shows "unsatisfiable (clauses S) \<or> (lits_of (trail T) \<Turnstile>sext clauses S \<and> satisfiable (clauses S))"
proof -
  have st: "cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy\<^sup>*\<^sup>* (S, n) (T, m)" and
    n_s: "no_step cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy (T, m)"
    using full unfolding full0_def by fast+
  have binv_T: "atms_of_m (clauses T) \<subseteq> atms_of_m A" "atm_of ` lits_of (trail T) \<subseteq> atms_of_m A"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_bound_inv[OF st, of A] inv n_d fin_clss_S atms_S atms_trail
    by auto
  moreover have inv_T: "no_dup (trail T)" "inv T" "finite (clauses T)"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_inv[OF st] inv n_d fin_clss_S by auto
  moreover have "all_decomposition_implies (clauses T) (get_all_marked_decomposition (trail T))"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy_all_decomposition_implies[OF st] inv n_d fin_clss_S
    decomp by auto
  ultimately have T: "unsatisfiable (clauses T) \<or> (trail T \<Turnstile>as clauses T \<and> satisfiable (clauses T))"
    using no_step_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy_no_step_cdcl\<^sub>N\<^sub>O\<^sub>T[of "(T, m)" A] n_s
    cdcl\<^sub>N\<^sub>O\<^sub>T_normal_forms[of T A] unfolding cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv_def by auto
  have eq_sat_S_T:"\<And>I. I \<Turnstile>sext clauses S \<longleftrightarrow> I \<Turnstile>sext clauses T"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy_sat_ext_iff[OF st, of A] inv n_d fin_clss_S atms_S
        atms_trail by auto
  have cons_T: "consistent_interp (lits_of (trail T))"
    using inv_T(1) distinctconsistent_interp by blast
  consider
      (unsat) "unsatisfiable (clauses T)"
    | (sat) "trail T \<Turnstile>as clauses T" and "satisfiable (clauses T)"
    using T by blast
  then show ?thesis
    proof cases
      case unsat
      then have "unsatisfiable (clauses S)"
        using eq_sat_S_T consistent_true_clss_ext_satisfiable true_clss_imp_true_cls_ext
        unfolding satisfiable_def by blast
      then show ?thesis by fast
    next
      case sat
      then have "lits_of (trail T) \<Turnstile>sext clauses S"
        using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_stgy_sat_ext_iff[OF st, of A] inv n_d fin_clss_S atms_S
        atms_trail by (auto simp: true_clss_imp_true_cls_ext true_annots_true_cls)
      moreover then have "satisfiable (clauses S)"
          using cons_T consistent_true_clss_ext_satisfiable by blast
      ultimately show ?thesis by blast
    qed
qed
end

locale most_general_cdcl\<^sub>N\<^sub>O\<^sub>T =
    dpll_state trail clauses update_trail update_cls +
    propagate_ops trail clauses update_trail update_cls propagate_conds +
    backjumping_ops trail clauses update_trail update_cls inv "\<lambda>_ _ _ _. True" for
    trail :: "'st \<Rightarrow> ('v, dpll_marked_level, dpll_mark) annoted_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    update_trail :: "('v, dpll_marked_level, dpll_mark) annoted_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_cls :: "'v clause set \<Rightarrow> 'st \<Rightarrow> 'st" and
    propagate_conds :: "'st \<Rightarrow> bool" and
    inv :: "'st \<Rightarrow> bool"
begin
lemma backjump_bj_can_jump:
  assumes
    tr_S: "trail S = F' @ Marked K d # F" and
    C: "C \<in> clauses S" and
    tr_S_C: "trail S \<Turnstile>as CNot C" and
    undef: "undefined_lit L F" and
    atm_L: "atm_of L \<in> atms_of_m (clauses S) \<union> atm_of ` (lits_of (F' @ Marked K d # F))" and
    cls_S_C': "clauses S \<Turnstile>p C' + {#L#}" and
    F_C': "F \<Turnstile>as CNot C'"
  shows "\<not>no_step backjump S"
    using backjump.intros[OF tr_S _ C tr_S_C undef _ cls_S_C' F_C',
      of "update_trail (Propagated L _ # F) S "] atm_L unfolding tr_S
    by (auto simp: state_eq\<^sub>N\<^sub>O\<^sub>T_def simp del: state_simp\<^sub>N\<^sub>O\<^sub>T)

sublocale dpll_with_backjumping_ops _ _ _ _ _ inv "\<lambda>_ _ _ _. True"
  using backjump_bj_can_jump by unfold_locales auto
end

end