theory CDCL_NOT
imports Partial_Annotated_Clausal_Logic List_More Wellfounded_More Partial_Clausal_Logic
begin

section \<open>NOT's CDCL\<close>

subsection \<open>Auxiliary Lemmas and Measure\<close>
lemma no_dup_cannot_not_lit_and_uminus:
  "no_dup M \<Longrightarrow> - lit_of xa = lit_of x \<Longrightarrow> x \<in> set M \<Longrightarrow> xa \<notin> set M"
  by (metis atm_of_uminus distinct_map inj_on_eq_iff uminus_not_id')

lemma true_clss_single_iff_incl:
  "I \<Turnstile>s single ` B \<longleftrightarrow> B \<subseteq> I"
  unfolding true_clss_def by auto

lemma atms_of_ms_single_atm_of[simp]:
  "atms_of_ms {{#lit_of L#} |L. P L} = atm_of ` {lit_of L |L. P L}"
  unfolding atms_of_ms_def by auto

lemma atms_of_m_uminus_lit_atm_of_lit_of:
  "atms_of {#- lit_of x. x \<in># A#} = atm_of ` (lit_of ` (set_mset A))"
  unfolding atms_of_def by (auto simp add: Fun.image_comp)

lemma atms_of_ms_single_image_atm_of_lit_of:
  "atms_of_ms ((\<lambda>x. {#lit_of x#}) ` A) = atm_of ` (lit_of ` A)"
  unfolding atms_of_ms_def by auto

text \<open>This measure can also be seen as the increasing lexicographic order: it is an order on bounded
  sequences, when each element is bounded. The proof involves a measure like the one defined here
  (the same?).\<close>
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
     by (rule setsum_add_nat_ivl[symmetric]) simp_all
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
  moreover then have "\<dots> = (\<Sum>i=0..< length M. (M@M')!i * b^ (s +i - length (M@M')))
                 + (\<Sum>i=length M..<length (M@M'). (M@M')!i * b^ (s +i - length (M@M')))"
    by (auto intro!: setsum_add_nat_ivl[symmetric])
  moreover
    have "\<forall>i\<in>{0..< length M}. (M@M')!i * b^ (s +i - length (M@M')) = M ! i * b ^ (s - length M'
      + i - length M)"
      using \<open>s \<ge> length (M@M')\<close> by (auto simp add: nth_append ac_simps)
    then have "\<mu>\<^sub>C (s - length M') b M = (\<Sum>i=0..< length M. (M@M')!i * b^ (s +i - length (M@M')))"
      unfolding \<mu>\<^sub>C_def by auto
  ultimately have "\<mu>\<^sub>C s b (M@M')= \<mu>\<^sub>C (s - length M') b M
                  + (\<Sum>i=length M..<length (M@M'). (M@M')!i * b^ (s +i - length (M@M')))"
     by auto
  moreover {
    have "(\<Sum>i=length M..<length (M@M'). (M@M')!i * b^ (s +i - length (M@M'))) =
           (\<Sum>i=0..<length M'. M'!i * b^ (s + i - length M'))"
     unfolding length_append set_sum_atLeastLessThan_add by auto
    then have "(\<Sum>i=length M..<length (M@M'). (M@M')!i * b^ (s +i - length (M@M'))) = \<mu>\<^sub>C s b M'"
      unfolding \<mu>\<^sub>C_def .
    }
  ultimately show ?thesis by presburger
qed

lemma \<mu>\<^sub>C_cons_non_empty_inf:
  assumes M_ge_1: "\<forall>i\<in>set M. i \<ge> 1" and M: "M \<noteq> []"
  shows "\<mu>\<^sub>C s b M \<ge> b ^  (s - length M)"
  using assms by (cases M) (auto simp: mult_eq_if \<mu>\<^sub>C_cons)

text \<open>Duplicate of @{file "~~/src/HOL/ex/NatSum.thy"} (but generalized to @{term "k\<ge>0"})\<close>
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
  then show ?thesis
    proof cases
      case b1
      then have "\<forall>i < length M. M!i = 0" using M_le by auto
      then have "\<mu>\<^sub>C s b M = 0" unfolding \<mu>\<^sub>C_def by auto
      then show ?thesis using \<open>b > 0\<close> by auto
    next
      case b
      have "\<forall> i \<in> {0..<length M}. M!i * b^ (s +i - length M) \<le> (b-1) * b^ (s +i - length M)"
        using M_le \<open>b > 1\<close> by auto
      then have "\<mu>\<^sub>C s b M \<le>  (\<Sum>i=0..<length M. (b-1) * b^ (s +i - length M))"
         using \<open>M\<noteq>[]\<close> \<open>b>0\<close> unfolding \<mu>\<^sub>C_def by (auto intro: setsum_mono)
      also
        have "\<forall> i \<in> {0..<length M}. (b-1) * b^ (s +i - length M) = (b-1) * b^ i * b^(s - length M)"
          by (metis Nat.add_diff_assoc2 add.commute assms(4) mult.assoc power_add)
        then have "(\<Sum>i=0..<length M. (b-1) * b^ (s +i - length M))
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
  then show ?thesis
    proof cases
      case M0
      then show ?thesis using M_le \<open>b > 0\<close> by auto
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
        by simp (rename_tac n, case_tac n, auto)
    }
    ultimately have ?thesis unfolding \<mu>\<^sub>C_def by auto
  }
  moreover
  {
    assume "length M < s"
    then have "\<mu>\<^sub>C s 0 M = 0" unfolding \<mu>\<^sub>C_def by auto}
  ultimately show ?thesis using assms unfolding \<mu>\<^sub>C_def by linarith
qed

subsection \<open>Initial definitions\<close>
subsubsection \<open>The state\<close>

text \<open>We define here an abstraction over operation on the state we are manipulating.\<close>
locale dpll_state =
  fixes
    trail :: "'st \<Rightarrow> ('v, unit, unit) marked_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    prepend_trail :: "('v, unit, unit) marked_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow>'st" and
    add_cls\<^sub>N\<^sub>O\<^sub>T :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls\<^sub>N\<^sub>O\<^sub>T :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st"
  assumes
    trail_prepend_trail[simp]:
      "\<And>st L. undefined_lit (trail st) (lit_of L) \<Longrightarrow> trail (prepend_trail L st) = L # trail st"
      and
    tl_trail[simp]: "trail (tl_trail S) = tl (trail S)" and
    trail_add_cls\<^sub>N\<^sub>O\<^sub>T[simp]: "\<And>st C. no_dup (trail st) \<Longrightarrow> trail (add_cls\<^sub>N\<^sub>O\<^sub>T C st) = trail st" and
    trail_remove_cls\<^sub>N\<^sub>O\<^sub>T[simp]: "\<And>st C. trail (remove_cls\<^sub>N\<^sub>O\<^sub>T C st) = trail st" and

    clauses_prepend_trail[simp]:
      "\<And>st L. undefined_lit (trail st) (lit_of L) \<Longrightarrow> clauses (prepend_trail L st) = clauses st"
      and
    clauses_tl_trail[simp]: "\<And>st. clauses (tl_trail st) = clauses st" and
    clauses_add_cls\<^sub>N\<^sub>O\<^sub>T[simp]:
      "\<And>st C. no_dup (trail st) \<Longrightarrow> clauses (add_cls\<^sub>N\<^sub>O\<^sub>T C st) = {#C#} + clauses st" and
    clauses_remove_cls\<^sub>N\<^sub>O\<^sub>T[simp]: "\<And>st C. clauses (remove_cls\<^sub>N\<^sub>O\<^sub>T C st) = remove_mset C (clauses st)"
begin

function reduce_trail_to\<^sub>N\<^sub>O\<^sub>T :: "'a list \<Rightarrow> 'st \<Rightarrow> 'st" where
"reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S =
  (if length (trail S) = length F \<or> trail S = [] then S else reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F (tl_trail S))"
by fast+
termination by (relation "measure (\<lambda>(_, S). length (trail S))") auto
declare reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.simps[simp del]

lemma
  shows
  reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_nil[simp]: "trail S = [] \<Longrightarrow> reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S = S" and
  reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_eq_length[simp]: "length (trail S) = length F \<Longrightarrow> reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S = S"
  by (auto simp: reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.simps)

lemma reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_length_ne[simp]:
  "length (trail S) \<noteq> length F \<Longrightarrow> trail S \<noteq> [] \<Longrightarrow>
    reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S = reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F (tl_trail S)"
  by (auto simp: reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.simps)

lemma trail_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_length_le:
  assumes "length F > length (trail S)"
  shows "trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S) = []"
  using assms by (induction F S rule: reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.induct)
  (simp add: less_imp_diff_less reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.simps)

lemma trail_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_nil[simp]:
  "trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T [] S) = []"
  by (induction "[]" S rule: reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.induct)
  (simp add: less_imp_diff_less reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.simps)

lemma clauses_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_nil:
  "clauses (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T [] S) = clauses S"
  by (induction "[]" S rule: reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.induct)
  (simp add: less_imp_diff_less reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.simps)

lemma trail_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_drop:
  "trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S) =
    (if length (trail S) \<ge> length F
    then drop (length (trail S) - length F) (trail S)
    else [])"
  apply (induction F S rule: reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.induct)
  apply (rename_tac F S, case_tac "trail S")
   apply auto[]
  apply (rename_tac list, case_tac "Suc (length list) > length F")
   prefer 2 apply simp
  apply (subgoal_tac "Suc (length list) - length F = Suc (length list - length F)")
   apply simp
  apply simp
  done


lemma reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_skip_beginning:
  assumes "trail S = F' @ F"
  shows "trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S) = F"
  using assms by (auto simp: trail_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_drop)

lemma reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_clauses[simp]:
  "clauses (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S) = clauses S"
  by (induction F S rule: reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.induct)
  (simp add: less_imp_diff_less reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.simps)

abbreviation trail_weight where
"trail_weight S \<equiv> map ((\<lambda>l. 1 + length l) o snd) (get_all_marked_decomposition (trail S))"

definition state_eq\<^sub>N\<^sub>O\<^sub>T :: "'st \<Rightarrow> 'st \<Rightarrow> bool" (infix "\<sim>" 50) where
"S \<sim> T \<longleftrightarrow> trail S = trail T \<and> clauses S = clauses T"

lemma state_eq\<^sub>N\<^sub>O\<^sub>T_ref[simp]:
  "S \<sim> S"
  unfolding state_eq\<^sub>N\<^sub>O\<^sub>T_def by auto

lemma state_eq\<^sub>N\<^sub>O\<^sub>T_sym:
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

lemma trail_eq_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_eq:
  "trail S = trail T \<Longrightarrow> trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S) = trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F T)"
  apply (induction F S arbitrary: T rule: reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.induct)
  by (metis tl_trail reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_eq_length reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_length_ne reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_nil)

lemma reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_state_eq\<^sub>N\<^sub>O\<^sub>T_compatible:
  assumes ST: "S \<sim> T"
  shows "reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S \<sim> reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F T"
proof -
  have "clauses (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S) = clauses (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F T)"
    using ST by auto
  moreover have "trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S) = trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F T)"
    using trail_eq_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_eq[of S T F] ST by auto
  ultimately show ?thesis by (auto simp del: state_simp\<^sub>N\<^sub>O\<^sub>T simp: state_eq\<^sub>N\<^sub>O\<^sub>T_def)
qed

lemma trail_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_add_cls\<^sub>N\<^sub>O\<^sub>T[simp]:
  "no_dup (trail S) \<Longrightarrow>
    trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F (add_cls\<^sub>N\<^sub>O\<^sub>T C S)) = trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S)"
  by (rule trail_eq_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_eq) simp

lemma reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_trail_tl_trail_decomp[simp]:
  "trail S = F' @ Marked K () # F \<Longrightarrow>
     trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F (tl_trail S)) = F"
  apply (rule reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_skip_beginning[of _ "tl (F' @ Marked K () # [])"])
  by (cases F') (auto simp add:tl_append reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_skip_beginning)

end

subsubsection \<open>Definition of the operation\<close>
locale propagate_ops =
  dpll_state trail clauses prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T for
    trail :: "'st \<Rightarrow> ('v, unit, unit) marked_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    prepend_trail :: "('v, unit, unit) marked_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T:: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    propagate_cond :: "('v, unit, unit) marked_lit \<Rightarrow> 'st \<Rightarrow> bool"
begin
inductive propagate\<^sub>N\<^sub>O\<^sub>T :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
propagate\<^sub>N\<^sub>O\<^sub>T[intro]: "C + {#L#} \<in># clauses S \<Longrightarrow> trail S \<Turnstile>as CNot C
    \<Longrightarrow> undefined_lit (trail S) L
    \<Longrightarrow> propagate_cond (Propagated L ()) S
    \<Longrightarrow> T \<sim> prepend_trail (Propagated L ()) S
    \<Longrightarrow> propagate\<^sub>N\<^sub>O\<^sub>T S T"
inductive_cases propagate\<^sub>N\<^sub>O\<^sub>TE[elim]: "propagate\<^sub>N\<^sub>O\<^sub>T S T"

end

locale decide_ops =
  dpll_state trail clauses prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T for
    trail :: "'st \<Rightarrow> ('v, unit, unit) marked_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    prepend_trail :: "('v, unit, unit) marked_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T:: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st"
begin
inductive decide\<^sub>N\<^sub>O\<^sub>T ::  "'st \<Rightarrow> 'st \<Rightarrow> bool" where
decide\<^sub>N\<^sub>O\<^sub>T[intro]: "undefined_lit (trail S) L \<Longrightarrow> atm_of L \<in> atms_of_mm (clauses S)
  \<Longrightarrow> T \<sim> prepend_trail (Marked L ()) S
  \<Longrightarrow> decide\<^sub>N\<^sub>O\<^sub>T S T"

inductive_cases decide\<^sub>N\<^sub>O\<^sub>TE[elim]: "decide\<^sub>N\<^sub>O\<^sub>T S S'"
end

locale backjumping_ops =
  dpll_state trail clauses prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T
  for
    trail :: "'st \<Rightarrow> ('v, unit, unit) marked_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    prepend_trail :: "('v, unit, unit) marked_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T:: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" +
  fixes
    backjump_conds :: "'v clause \<Rightarrow> 'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool"
begin
inductive backjump where
"trail S = F' @ Marked K ()# F
   \<Longrightarrow> T \<sim> prepend_trail (Propagated L ()) (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S)
   \<Longrightarrow> C \<in># clauses S
   \<Longrightarrow> trail S \<Turnstile>as CNot C
   \<Longrightarrow> undefined_lit F L
   \<Longrightarrow> atm_of L \<in> atms_of_mm (clauses S) \<union> atm_of ` (lits_of_l (trail S))
   \<Longrightarrow> clauses S \<Turnstile>pm C' + {#L#}
   \<Longrightarrow> F \<Turnstile>as CNot C'
   \<Longrightarrow> backjump_conds C C' L S T
   \<Longrightarrow> backjump S T"
inductive_cases backjumpE: "backjump S T"
end

subsection \<open>DPLL with backjumping\<close>
locale dpll_with_backjumping_ops =
  dpll_state trail clauses prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T +
  propagate_ops trail clauses prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T propagate_conds +
  decide_ops trail clauses prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T +
  backjumping_ops trail clauses prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T backjump_conds
  for
    trail :: "'st \<Rightarrow> ('v, unit, unit) marked_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    prepend_trail :: "('v, unit, unit) marked_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T:: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    propagate_conds :: "('v, unit, unit) marked_lit \<Rightarrow> 'st \<Rightarrow> bool" and
    inv :: "'st \<Rightarrow> bool" and
    backjump_conds :: "'v clause \<Rightarrow> 'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool" +
  assumes
      bj_can_jump:
      "\<And>S C F' K F L.
        inv S \<Longrightarrow>
        no_dup (trail S) \<Longrightarrow>
        trail S = F' @ Marked K () # F \<Longrightarrow>
        C \<in># clauses S \<Longrightarrow>
        trail S \<Turnstile>as CNot C \<Longrightarrow>
        undefined_lit F L \<Longrightarrow>
        atm_of L \<in> atms_of_mm (clauses S) \<union> atm_of ` (lits_of_l (F' @ Marked K () # F)) \<Longrightarrow>
        clauses S \<Turnstile>pm C' + {#L#} \<Longrightarrow>
        F \<Turnstile>as CNot C' \<Longrightarrow>
        \<not>no_step backjump S"
begin

text \<open>We cannot add a like condition @{term "atms_of C' \<subseteq> atms_of_ms N"} because to ensure that we
  can backjump even if the last decision variable has disappeared.

  The part of the condition @{term "atm_of L \<in> atm_of ` (lits_of_l (F' @ Marked K () # F))"} is
  important, otherwise you are not sure that you can backtrack.\<close>

subsubsection\<open>Definition\<close>

text \<open>We define dpll with backjumping:\<close>
inductive dpll_bj :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
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
    "\<And>L T. undefined_lit (trail S) L \<Longrightarrow> atm_of L \<in> atms_of_mm (clauses S)
      \<Longrightarrow> T \<sim> prepend_trail (Marked L ()) S
      \<Longrightarrow> P S T" and
    "\<And>C L T. C + {#L#} \<in># clauses S \<Longrightarrow> trail S \<Turnstile>as CNot C \<Longrightarrow> undefined_lit (trail S) L
      \<Longrightarrow> T \<sim> prepend_trail (Propagated L ()) S
      \<Longrightarrow> P S T" and
    "\<And>C F' K F L C' T. C \<in># clauses S \<Longrightarrow> F' @ Marked K () # F \<Turnstile>as CNot C
      \<Longrightarrow> trail S = F' @ Marked K () # F
      \<Longrightarrow> undefined_lit F L
      \<Longrightarrow> atm_of L \<in> atms_of_mm (clauses S) \<union> atm_of ` (lits_of_l (F' @ Marked K () # F))
      \<Longrightarrow> clauses S \<Turnstile>pm C' + {#L#}
      \<Longrightarrow> F \<Turnstile>as CNot C'
      \<Longrightarrow> T \<sim> prepend_trail (Propagated L ()) (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S)
      \<Longrightarrow> P S T"
  shows "P S T"
  apply (induct T rule: dpll_bj_induct[OF local.dpll_with_backjumping_ops_axioms])
     apply (rule assms(1))
    using assms(3) apply blast
   apply (elim propagate\<^sub>N\<^sub>O\<^sub>TE) using assms(4) apply blast
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
  using assms by (induction rule: dpll_bj_all_induct)
  (auto simp add: defined_lit_map reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_skip_beginning)

paragraph \<open>Valuations\<close>
lemma dpll_bj_sat_iff:
  assumes "dpll_bj S T" and "inv S"
  shows "I \<Turnstile>sm clauses S \<longleftrightarrow> I \<Turnstile>sm clauses T"
  using assms by (induction rule: dpll_bj_all_induct) auto

paragraph \<open>Clauses\<close>
lemma dpll_bj_atms_of_ms_clauses_inv:
  assumes
    "dpll_bj S T" and
    "inv S"
  shows "atms_of_mm (clauses S) = atms_of_mm (clauses T)"
  using assms by (induction rule: dpll_bj_all_induct) auto

lemma dpll_bj_atms_in_trail:
  assumes
    "dpll_bj S T" and
    "inv S" and
    "atm_of ` (lits_of_l (trail S)) \<subseteq> atms_of_mm (clauses S)"
  shows "atm_of ` (lits_of_l (trail T)) \<subseteq> atms_of_mm (clauses S)"
  using assms by (induction rule: dpll_bj_all_induct)
  (auto simp: in_plus_implies_atm_of_on_atms_of_ms reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_skip_beginning)

lemma dpll_bj_atms_in_trail_in_set:
  assumes "dpll_bj S T"and
    "inv S" and
  "atms_of_mm (clauses S) \<subseteq> A" and
  "atm_of ` (lits_of_l (trail S)) \<subseteq> A"
  shows "atm_of ` (lits_of_l (trail T)) \<subseteq> A"
  using assms by (induction rule: dpll_bj_all_induct)
  (auto simp: in_plus_implies_atm_of_on_atms_of_ms)

lemma dpll_bj_all_decomposition_implies_inv:
  assumes
    "dpll_bj S T" and
    inv: "inv S" and
    decomp: "all_decomposition_implies_m (clauses S) (get_all_marked_decomposition (trail S))"
  shows "all_decomposition_implies_m (clauses T) (get_all_marked_decomposition (trail T))"
  using assms(1,2)
proof (induction rule:dpll_bj_all_induct)
  case decide\<^sub>N\<^sub>O\<^sub>T
  then show ?case using decomp by auto
next
  case (propagate\<^sub>N\<^sub>O\<^sub>T C L T) note propa = this(1) and undef = this(3) and T = this(4)
  let ?M' = "trail (prepend_trail (Propagated L ()) S)"
  let ?N = "clauses S"
  obtain a y l where ay: "get_all_marked_decomposition ?M' = (a, y) # l"
    by (cases "get_all_marked_decomposition ?M'") fastforce+
  then have M': "?M' = y @ a" using get_all_marked_decomposition_decomp[of ?M'] by auto
  have M: "get_all_marked_decomposition (trail S) = (a, tl y) # l"
    using ay undef by (cases " get_all_marked_decomposition (trail S)") auto
  have y\<^sub>0: "y = (Propagated L ()) # (tl y)"
    using ay undef by (auto simp add: M)
  from arg_cong[OF this, of set] have y[simp]: "set y = insert (Propagated L ()) (set (tl y))"
    by simp
  have tr_S: "trail S = tl y @ a"
    using arg_cong[OF M', of tl] y\<^sub>0 M get_all_marked_decomposition_decomp by force
  have a_Un_N_M: "unmark_l a \<union> set_mset ?N \<Turnstile>ps unmark_l (tl y)"
    using decomp ay unfolding all_decomposition_implies_def by (simp add: M)+

  moreover have "unmark_l a \<union> set_mset ?N \<Turnstile>p {#L#}" (is "?I \<Turnstile>p _")
    proof (rule true_clss_cls_plus_CNot)
      show "?I \<Turnstile>p C + {#L#}"
        using propa propagate\<^sub>N\<^sub>O\<^sub>T.prems by (auto dest!: true_clss_clss_in_imp_true_clss_cls)
    next
      have "(\<lambda>m. {#lit_of m#}) ` set ?M' \<Turnstile>ps CNot C"
        using \<open>trail S \<Turnstile>as CNot C\<close> undef by (auto simp add: true_annots_true_clss_clss)
      have a1: "(\<lambda>m. {#lit_of m#}) ` set a \<union> (\<lambda>m. {#lit_of m#}) ` set (tl y)  \<Turnstile>ps CNot C"
        using propagate\<^sub>N\<^sub>O\<^sub>T.hyps(2) tr_S true_annots_true_clss_clss
        by (force simp add: image_Un sup_commute)
      have a2: "set_mset (clauses S)\<union> unmark_l a
        \<Turnstile>ps unmark_l (tl y)"
        using calculation by (auto simp add: sup_commute)
      show "(\<lambda>m. {#lit_of m#}) ` set a  \<union> set_mset (clauses S)\<Turnstile>ps CNot C"
        proof -
          have "set_mset (clauses S) \<union> (\<lambda>m. {#lit_of m#}) ` set a \<Turnstile>ps
            (\<lambda>m. {#lit_of m#}) ` set a \<union> (\<lambda>m. {#lit_of m#}) ` set (tl y)"
            using a2 true_clss_clss_def by blast
          then show "(\<lambda>m. {#lit_of m#}) ` set a  \<union> set_mset (clauses S)\<Turnstile>ps CNot C"
            using a1 unfolding sup_commute by (meson true_clss_clss_left_right
              true_clss_clss_union_and true_clss_clss_union_l_r )
        qed
    qed

  ultimately have "unmark_l a \<union> set_mset ?N \<Turnstile>ps unmark_l ?M'"
    unfolding M' by (auto simp add: all_in_true_clss_clss image_Un)

  then show ?case
    using decomp T M undef unfolding ay all_decomposition_implies_def by (auto simp add: ay)
next
  case (backjump C F' K F L D T) note confl = this(2) and tr = this(3) and undef = this(4)
    and L = this(5) and N_C = this(6) and vars_D = this(5) and T = this(8)
  have decomp: "all_decomposition_implies_m (clauses S) (get_all_marked_decomposition F)"
    using decomp unfolding tr all_decomposition_implies_def
    by (metis (no_types, lifting) get_all_marked_decomposition.simps(1)
      get_all_marked_decomposition_never_empty hd_Cons_tl insert_iff list.sel(3) list.set(2)
      tl_get_all_marked_decomposition_skip_some)

  moreover have "unmark_l (fst (hd (get_all_marked_decomposition F)))
      \<union> set_mset (clauses S)
    \<Turnstile>ps unmark_l (snd (hd (get_all_marked_decomposition F)))"
    by (metis all_decomposition_implies_cons_single decomp get_all_marked_decomposition_never_empty
      hd_Cons_tl)
  moreover
    have vars_of_D: "atms_of D \<subseteq> atm_of ` lits_of_l F"
      using \<open>F \<Turnstile>as CNot D\<close> unfolding atms_of_def
      by (meson image_subsetI true_annots_CNot_all_atms_defined)

  obtain a b li where F: "get_all_marked_decomposition F = (a, b) # li"
    by (cases "get_all_marked_decomposition F") auto
  have "F = b @ a"
    using get_all_marked_decomposition_decomp[of F a b] F by auto
  have a_N_b:"unmark_l a \<union> set_mset (clauses S) \<Turnstile>ps unmark_l b"
    using decomp unfolding all_decomposition_implies_def by (auto simp add: F)

  have F_D:"unmark_l F \<Turnstile>ps CNot D"
    using \<open>F \<Turnstile>as CNot D\<close> by (simp add: true_annots_true_clss_clss)
  then have "unmark_l a \<union> unmark_l b \<Turnstile>ps CNot D"
    unfolding \<open>F = b @ a\<close> by (simp add: image_Un sup.commute)
  have a_N_CNot_D: "unmark_l a \<union> set_mset (clauses S)
    \<Turnstile>ps CNot D \<union> unmark_l b"
    apply (rule true_clss_clss_left_right)
    using a_N_b  F_D unfolding \<open>F = b @ a\<close> by (auto simp add: image_Un ac_simps)

  have a_N_D_L: "unmark_l a \<union> set_mset (clauses S) \<Turnstile>p D+{#L#}"
    by (simp add: N_C)
  have "unmark_l a \<union> set_mset (clauses S) \<Turnstile>p {#L#}"
    using a_N_D_L a_N_CNot_D by (blast intro: true_clss_cls_plus_CNot)
  then show ?case
    using decomp T tr undef unfolding all_decomposition_implies_def by (auto simp add: F)
qed

subsubsection \<open>Termination\<close>
paragraph \<open>Using a proper measure\<close>
lemma length_get_all_marked_decomposition_append_Marked:
  "length (get_all_marked_decomposition (F' @ Marked K () # F)) =
    length (get_all_marked_decomposition F')
    + length (get_all_marked_decomposition (Marked K () # F))
    - 1"
  by (induction F' rule: marked_lit_list_induct) auto

lemma take_length_get_all_marked_decomposition_marked_sandwich:
  "take (length (get_all_marked_decomposition F))
      (map (f o snd) (rev (get_all_marked_decomposition (F' @ Marked K () # F))))
      =
     map (f o snd) (rev (get_all_marked_decomposition F))
    "
proof (induction F' rule: marked_lit_list_induct)
  case nil
  then show ?case by auto
next
  case (marked K)
  then show ?case by (simp add: length_get_all_marked_decomposition_append_Marked)
next
  case (proped L m F') note IH = this(1)
  obtain a b l where F': "get_all_marked_decomposition (F' @ Marked K () # F) = (a, b) # l"
    by (cases "get_all_marked_decomposition (F' @ Marked K () # F)") auto
  have "length (get_all_marked_decomposition F) - length l = 0"
    using length_get_all_marked_decomposition_append_Marked[of F' K F]
    unfolding F' by (cases "get_all_marked_decomposition F'") auto
  then show ?case
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
  \<^item> @{term "1+card (atms_of_ms A)"}: @{term "card (atms_of_ms A)"} is an upper bound on the length of
  the list. As @{term get_all_marked_decomposition} appends an possibly empty couple at the end,
  adding one is needed.
  \<^item> @{term "2+card (atms_of_ms A)"}: @{term "card (atms_of_ms A)"} is an upper bound on the number of
  elements, where adding one is necessary for the same reason as for the bound on the list, and one
  is needed to have a strict bound.
  \<close>
abbreviation unassigned_lit ::  "'b literal multiset set \<Rightarrow> 'a list \<Rightarrow> nat" where
  "unassigned_lit N M \<equiv> card (atms_of_ms N) - length M"
lemma dpll_bj_trail_mes_increasing_prop:
  fixes M :: "('v, unit, unit) marked_lits " and N :: "'v clauses"
  assumes
    "dpll_bj S T" and
    "inv S" and
    NA: "atms_of_mm (clauses S) \<subseteq> atms_of_ms A" and
    MA: "atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A" and
    n_d: "no_dup (trail S)" and
    finite: "finite A"
  shows "\<mu>\<^sub>C (1+card (atms_of_ms A)) (2+card (atms_of_ms A)) (trail_weight T)
    > \<mu>\<^sub>C (1+card (atms_of_ms A)) (2+card (atms_of_ms A)) (trail_weight S)"
  using assms(1,2)
proof (induction rule: dpll_bj_all_induct)
  case (propagate\<^sub>N\<^sub>O\<^sub>T C L) note CLN = this(1) and MC =this(2) and undef_L = this(3) and T = this(4)
  have incl: "atm_of ` lits_of_l (Propagated L () # trail S) \<subseteq> atms_of_ms A"
    using propagate\<^sub>N\<^sub>O\<^sub>T.hyps propagate_ops.propagate\<^sub>N\<^sub>O\<^sub>T dpll_bj_atms_in_trail_in_set bj_propagate\<^sub>N\<^sub>O\<^sub>T
    NA MA CLN by (auto simp: in_plus_implies_atm_of_on_atms_of_ms)

  have no_dup: "no_dup (Propagated L () # trail S)"
    using defined_lit_map n_d undef_L by auto
  obtain a b l where M: "get_all_marked_decomposition (trail S) = (a, b) # l"
    by (cases "get_all_marked_decomposition (trail S)") auto
  have b_le_M: "length b \<le> length (trail S)"
    using get_all_marked_decomposition_decomp[of "trail S"] by (simp add: M)
  have "finite (atms_of_ms A)" using finite by simp

  then have "length (Propagated L () # trail S) \<le> card (atms_of_ms A)"
    using incl finite unfolding no_dup_length_eq_card_atm_of_lits_of_l[OF no_dup]
    by (simp add: card_mono)
  then have latm: "unassigned_lit A b = Suc (unassigned_lit A (Propagated L d # b))"
    using b_le_M by auto
  then show ?case using T undef_L by (auto simp: latm M \<mu>\<^sub>C_cons)
next
  case (decide\<^sub>N\<^sub>O\<^sub>T L) note undef_L = this(1) and MC = this(2) and T = this(3)
  have incl: "atm_of ` lits_of_l (Marked L () # (trail S)) \<subseteq> atms_of_ms A"
    using dpll_bj_atms_in_trail_in_set bj_decide\<^sub>N\<^sub>O\<^sub>T decide\<^sub>N\<^sub>O\<^sub>T.decide\<^sub>N\<^sub>O\<^sub>T[OF decide\<^sub>N\<^sub>O\<^sub>T.hyps] NA MA MC
    by auto

  have no_dup: "no_dup (Marked L () # (trail S))"
    using defined_lit_map n_d undef_L by auto
  obtain a b l where M: "get_all_marked_decomposition (trail S) = (a, b) # l"
    by (cases "get_all_marked_decomposition (trail S)") auto

  then have "length (Marked L () # (trail S)) \<le> card (atms_of_ms A)"
    using incl finite unfolding no_dup_length_eq_card_atm_of_lits_of_l[OF no_dup]
    by (simp add: card_mono)
  then have latm: "unassigned_lit A (trail S) = Suc (unassigned_lit A (Marked L lv # (trail S)))"
    by force
  show ?case using T undef_L by (simp add: latm \<mu>\<^sub>C_cons)
next
  case (backjump C F' K F L C' T) note undef_L = this(4) and MC =this(1) and tr_S = this(3) and
    L = this(5) and T = this(8)
  have incl: "atm_of ` lits_of_l (Propagated L () # F) \<subseteq> atms_of_ms A"
    using dpll_bj_atms_in_trail_in_set NA MA tr_S L by auto

  have no_dup: "no_dup (Propagated L () # F)"
    using defined_lit_map n_d undef_L tr_S by auto
  obtain a b l where M: "get_all_marked_decomposition (trail S) = (a, b) # l"
    by (cases "get_all_marked_decomposition (trail S)") auto
  have b_le_M: "length b \<le> length (trail S)"
    using get_all_marked_decomposition_decomp[of "trail S"] by (simp add: M)
  have fin_atms_A: "finite (atms_of_ms A)" using finite by simp

  then have F_le_A: "length (Propagated L () # F) \<le>  card (atms_of_ms A)"
    using incl finite unfolding no_dup_length_eq_card_atm_of_lits_of_l[OF no_dup]
    by (simp add: card_mono)
  have tr_S_le_A: "length (trail S) \<le>  (card (atms_of_ms A))"
    using n_d MA by (metis fin_atms_A card_mono no_dup_length_eq_card_atm_of_lits_of_l)
  obtain a b l where F: "get_all_marked_decomposition F = (a, b) # l"
    by (cases "get_all_marked_decomposition F") auto
  then have "F = b @ a"
    using get_all_marked_decomposition_decomp[of "Propagated L () # F" a
      "Propagated L () # b"] by simp
  then have latm: "unassigned_lit A b = Suc (unassigned_lit A (Propagated L () # b))"
     using F_le_A by simp
  obtain rem where
    rem:"map (\<lambda>a. Suc (length (snd a))) (rev (get_all_marked_decomposition (F' @ Marked K () # F)))
    = map (\<lambda>a. Suc (length (snd a))) (rev (get_all_marked_decomposition F)) @ rem"
    using take_length_get_all_marked_decomposition_marked_sandwich[of F "\<lambda>a. Suc (length a)" F' K]
    unfolding o_def by (metis append_take_drop_id)
  then have rem: "map (\<lambda>a. Suc (length (snd a)))
      (get_all_marked_decomposition (F' @ Marked K () # F))
    = rev rem @ map (\<lambda>a. Suc (length (snd a))) ((get_all_marked_decomposition F))"
    by (simp add: rev_map[symmetric] rev_swap)
  have "length (rev rem @ map (\<lambda>a. Suc (length (snd a))) (get_all_marked_decomposition F))
          \<le> Suc (card (atms_of_ms A))"
    using arg_cong[OF rem, of length] tr_S_le_A
    length_get_all_marked_decomposition_length[of "F' @ Marked K () # F"] tr_S by auto
  moreover
    { fix i :: nat and xs :: "'a list"
      have "i < length xs \<Longrightarrow> length xs - Suc i < length xs"
        by auto
      then have H: "i<length xs \<Longrightarrow> rev xs ! i \<in> set xs"
        using rev_nth[of i xs] unfolding in_set_conv_nth by (force simp add: in_set_conv_nth)
    } note H = this
    have "\<forall>i<length rem. rev rem ! i < card (atms_of_ms A) + 2"
      using tr_S_le_A length_in_get_all_marked_decomposition_bounded[of _ S] unfolding tr_S
      by (force simp add: o_def rem dest!: H intro: length_get_all_marked_decomposition_length)
  ultimately show ?case
    using \<mu>\<^sub>C_bounded[of "rev rem" "card (atms_of_ms A)+2" "unassigned_lit A l"] T undef_L
    by (simp add: rem \<mu>\<^sub>C_append \<mu>\<^sub>C_cons F tr_S)
qed

lemma dpll_bj_trail_mes_decreasing_prop:
  assumes dpll: "dpll_bj S T"  and inv: "inv S" and
  N_A: "atms_of_mm (clauses S) \<subseteq> atms_of_ms A" and
  M_A: "atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A" and
  nd: "no_dup (trail S)" and
  fin_A: "finite A"
  shows "(2+card (atms_of_ms A)) ^ (1+card (atms_of_ms A))
               - \<mu>\<^sub>C (1+card (atms_of_ms A)) (2+card (atms_of_ms A)) (trail_weight T)
            < (2+card (atms_of_ms A)) ^ (1+card (atms_of_ms A))
               - \<mu>\<^sub>C (1+card (atms_of_ms A)) (2+card (atms_of_ms A)) (trail_weight S)"
proof -
  let ?b = "2+card (atms_of_ms A)"
  let ?s = "1+card (atms_of_ms A)"
  let ?\<mu> = "\<mu>\<^sub>C ?s ?b"
  have M'_A: "atm_of ` lits_of_l (trail T) \<subseteq> atms_of_ms A"
    by (meson M_A N_A dpll dpll_bj_atms_in_trail_in_set inv)
  have nd': "no_dup (trail T)"
    using \<open>dpll_bj S T\<close> dpll_bj_no_dup nd inv by blast
  { fix i :: nat and xs :: "'a list"
    have "i < length xs \<Longrightarrow> length xs - Suc i < length xs"
      by auto
    then have H: "i<length xs \<Longrightarrow>  xs ! i \<in> set xs"
      using rev_nth[of i xs] unfolding in_set_conv_nth by (force simp add: in_set_conv_nth)
  } note H = this

  have l_M_A: "length (trail S) \<le> card (atms_of_ms A)"
    by (simp add: fin_A M_A card_mono no_dup_length_eq_card_atm_of_lits_of_l nd)
  have l_M'_A: "length (trail T) \<le> card (atms_of_ms A)"
    by (simp add: fin_A M'_A card_mono no_dup_length_eq_card_atm_of_lits_of_l nd')
  have l_trail_weight_M: "length (trail_weight T) \<le> 1+card (atms_of_ms A)"
     using l_M'_A length_get_all_marked_decomposition_length[of "trail T"] by auto
  have bounded_M: "\<forall>i<length (trail_weight T). (trail_weight T)! i < card (atms_of_ms A) + 2"
    using length_in_get_all_marked_decomposition_bounded[of _ T] l_M'_A
    by (metis (no_types, lifting) Nat.le_trans One_nat_def Suc_1 add.right_neutral add_Suc_right
      le_imp_less_Suc less_eq_Suc_le nth_mem)

  from dpll_bj_trail_mes_increasing_prop[OF dpll inv N_A M_A nd fin_A]
  have "\<mu>\<^sub>C ?s ?b (trail_weight S) < \<mu>\<^sub>C ?s ?b (trail_weight T)" by simp
  moreover from \<mu>\<^sub>C_bounded[OF bounded_M l_trail_weight_M]
    have "\<mu>\<^sub>C ?s ?b (trail_weight T) \<le> ?b ^ ?s" by auto
  ultimately show ?thesis by linarith
qed

lemma wf_dpll_bj:
  assumes fin: "finite A"
  shows "wf {(T, S). dpll_bj S T
    \<and> atms_of_mm (clauses S) \<subseteq> atms_of_ms A \<and> atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A
    \<and> no_dup (trail S) \<and> inv S}"
  (is "wf ?A")
proof (rule wf_bounded_measure[of _
        "\<lambda>_. (2 + card (atms_of_ms A))^(1 + card (atms_of_ms A))"
        "\<lambda>S. \<mu>\<^sub>C (1+card (atms_of_ms A)) (2+card (atms_of_ms A)) (trail_weight S)"])
  fix a b :: "'st"
  let ?b = "2+card (atms_of_ms A)"
  let ?s = "1+card (atms_of_ms A)"
  let ?\<mu> = "\<mu>\<^sub>C ?s ?b"
  assume ab: "(b, a) \<in> {(T, S). dpll_bj S T
    \<and> atms_of_mm (clauses S) \<subseteq> atms_of_ms A \<and> atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A
    \<and> no_dup (trail S) \<and> inv S}"

  have fin_A: "finite (atms_of_ms A)"
    using fin by auto
  have
    dpll_bj: "dpll_bj a b" and
    N_A: "atms_of_mm (clauses a) \<subseteq> atms_of_ms A" and
    M_A: "atm_of ` lits_of_l (trail a) \<subseteq> atms_of_ms A" and
    nd: "no_dup (trail a)" and
    inv: "inv a"
    using ab by auto

  have M'_A: "atm_of ` lits_of_l (trail b) \<subseteq> atms_of_ms A"
    by (meson M_A N_A \<open>dpll_bj a b\<close> dpll_bj_atms_in_trail_in_set inv)
  have nd': "no_dup (trail b)"
    using \<open>dpll_bj a b\<close> dpll_bj_no_dup nd inv by blast
  { fix i :: nat and xs :: "'a list"
    have "i < length xs \<Longrightarrow> length xs - Suc i < length xs"
      by auto
    then have H: "i<length xs \<Longrightarrow>  xs ! i \<in> set xs"
      using rev_nth[of i xs] unfolding in_set_conv_nth by (force simp add: in_set_conv_nth)
  } note H = this

  have l_M_A: "length (trail a) \<le> card (atms_of_ms A)"
    by (simp add: fin_A M_A card_mono no_dup_length_eq_card_atm_of_lits_of_l nd)
  have l_M'_A: "length (trail b) \<le> card (atms_of_ms A)"
    by (simp add: fin_A M'_A card_mono no_dup_length_eq_card_atm_of_lits_of_l nd')
  have l_trail_weight_M: "length (trail_weight b) \<le> 1+card (atms_of_ms A)"
     using l_M'_A length_get_all_marked_decomposition_length[of "trail b"] by auto
  have bounded_M: "\<forall>i<length (trail_weight b). (trail_weight b)! i < card (atms_of_ms A) + 2"
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
theorem dpll_backjump_final_state:
  fixes A :: "'v literal multiset set" and S T :: "'st"
  assumes
    "atms_of_mm (clauses S) \<subseteq> atms_of_ms A" and
    "atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A" and
    "no_dup (trail S)" and
    "finite A" and
    inv: "inv S" and
    n_s: "no_step dpll_bj S" and
    decomp: "all_decomposition_implies_m (clauses S) (get_all_marked_decomposition (trail S))"
  shows "unsatisfiable (set_mset (clauses S))
    \<or> (trail S \<Turnstile>asm clauses S \<and> satisfiable (set_mset (clauses S)))"
proof -
  let ?N = "set_mset (clauses S)"
  let ?M = "trail S"
  consider
      (sat) "satisfiable ?N" and "?M \<Turnstile>as ?N"
    | (sat') "satisfiable ?N" and "\<not> ?M \<Turnstile>as ?N"
    | (unsat) "unsatisfiable ?N"
    by auto
  then show ?thesis
    proof cases
      case sat' note sat = this(1) and M = this(2)
      obtain C where "C \<in> ?N" and "\<not>?M \<Turnstile>a C" using M unfolding true_annots_def by auto
      obtain I :: "'v literal set" where
        "I \<Turnstile>s ?N" and
        cons: "consistent_interp I" and
        tot: "total_over_m I ?N" and
        atm_I_N: "atm_of `I \<subseteq> atms_of_ms ?N"
        using sat unfolding satisfiable_def_min by auto
      let ?I = "I \<union> {P| P. P \<in> lits_of_l ?M \<and> atm_of P \<notin> atm_of ` I}"
      let ?O = "{{#lit_of L#} |L. is_marked L \<and> L \<in> set ?M \<and> atm_of (lit_of L) \<notin> atms_of_ms ?N}"
      have cons_I': "consistent_interp ?I"
        using cons using \<open>no_dup ?M\<close>  unfolding consistent_interp_def
        by (auto simp add: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set lits_of_def
          dest!: no_dup_cannot_not_lit_and_uminus)
      have tot_I': "total_over_m ?I (?N \<union> unmark_l ?M)"
        using tot atms_of_m_s_def unfolding total_over_m_def total_over_set_def
        by fastforce
      have "{P |P. P \<in> lits_of_l ?M \<and> atm_of P \<notin> atm_of ` I} \<Turnstile>s ?O"
        using \<open>I\<Turnstile>s ?N\<close> atm_I_N by (auto simp add: atm_of_eq_atm_of true_clss_def lits_of_def)
      then have I'_N: "?I \<Turnstile>s ?N \<union> ?O"
        using \<open>I\<Turnstile>s ?N\<close> true_clss_union_increase by force
      have tot': "total_over_m ?I (?N\<union>?O)"
        using atm_I_N tot unfolding total_over_m_def total_over_set_def
        by (force simp: image_iff lits_of_def dest!: is_marked_ex_Marked)

      have atms_N_M: "atms_of_ms ?N \<subseteq> atm_of ` lits_of_l ?M"
        proof (rule ccontr)
          assume "\<not> ?thesis"
          then obtain l :: 'v where
            l_N: "l \<in> atms_of_ms ?N" and
            l_M: "l \<notin> atm_of ` lits_of_l ?M"
            by auto
          have "undefined_lit ?M (Pos l)"
            using l_M by (metis Marked_Propagated_in_iff_in_lits_of_l
              atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set literal.sel(1))
          from bj_decide\<^sub>N\<^sub>O\<^sub>T[OF decide\<^sub>N\<^sub>O\<^sub>T[OF this]] show False
            using l_N n_s by (metis literal.sel(1) state_eq\<^sub>N\<^sub>O\<^sub>T_ref)
        qed

      have "?M \<Turnstile>as CNot C"
        by (metis \<open>C \<in> set_mset (clauses S)\<close> \<open>\<not> trail S \<Turnstile>a C\<close> all_variables_defined_not_imply_cnot
        atms_N_M atms_of_m_atms_of_ms_mono atms_of_ms_CNot_atms_of atms_of_ms_CNot_atms_of_ms
        subset_eq)
      have "\<exists>l \<in> set ?M. is_marked l"
        proof (rule ccontr)
          let ?O = "{{#lit_of L#} |L. is_marked L \<and> L \<in> set ?M \<and> atm_of (lit_of L) \<notin> atms_of_ms ?N}"
          have \<theta>[iff]: "\<And>I. total_over_m I (?N \<union> ?O \<union> unmark_l ?M)
            \<longleftrightarrow> total_over_m I (?N \<union>unmark_l ?M)"
            unfolding total_over_set_def total_over_m_def atms_of_ms_def by auto
          assume "\<not> ?thesis"
          then have [simp]:"{{#lit_of L#} |L. is_marked L \<and> L \<in> set ?M}
            = {{#lit_of L#} |L. is_marked L \<and> L \<in> set ?M \<and> atm_of (lit_of L) \<notin> atms_of_ms ?N}"
            by auto
          then have "?N \<union> ?O \<Turnstile>ps unmark_l ?M"
            using all_decomposition_implies_propagated_lits_are_implied[OF decomp] by auto

          then have "?I \<Turnstile>s unmark_l ?M"
            using cons_I' I'_N tot_I' \<open>?I \<Turnstile>s ?N \<union> ?O\<close> unfolding \<theta> true_clss_clss_def by blast
          then have "lits_of_l ?M \<subseteq> ?I"
            unfolding true_clss_def lits_of_def by auto
          then have "?M \<Turnstile>as ?N"
            using I'_N \<open>C \<in> ?N\<close> \<open>\<not> ?M \<Turnstile>a C\<close> cons_I' atms_N_M
            by (meson \<open>trail S \<Turnstile>as CNot C\<close> consistent_CNot_not rev_subsetD sup_ge1 true_annot_def
              true_annots_def true_cls_mono_set_mset_l true_clss_def)
          then show False using M by fast
        qed
      from List.split_list_first_propE[OF this] obtain K :: "'v literal" and
        F F' :: "('v, unit, unit) marked_lit list" where
        M_K: "?M = F' @ Marked K () # F" and
        nm: "\<forall>f\<in>set F'. \<not>is_marked f"
        unfolding is_marked_def by (metis (full_types) old.unit.exhaust)
      let ?K = "Marked K ()::('v, unit, unit) marked_lit"
      have "?K \<in> set ?M"
        unfolding M_K by auto
      let ?C = "image_mset lit_of {#L\<in>#mset ?M. is_marked L \<and> L\<noteq>?K#} :: 'v literal multiset"
      let ?C' = "set_mset (image_mset (\<lambda>L::'v literal. {#L#}) (?C+{#lit_of ?K#}))"
      have "?N \<union> {{#lit_of L#} |L. is_marked L \<and> L \<in> set ?M} \<Turnstile>ps unmark_l ?M"
        using all_decomposition_implies_propagated_lits_are_implied[OF decomp] .
      moreover have C': "?C' = {{#lit_of L#} |L. is_marked L \<and> L \<in> set ?M}"
        unfolding M_K apply standard
          apply force
        using IntI by auto
      ultimately have N_C_M: "?N \<union> ?C' \<Turnstile>ps unmark_l ?M"
        by auto
      have N_M_False: "?N \<union> (\<lambda>L. {#lit_of L#}) ` (set ?M) \<Turnstile>ps {{#}}"
        using M \<open>?M \<Turnstile>as CNot C\<close> \<open>C\<in>?N\<close> unfolding true_clss_clss_def true_annots_def Ball_def
        true_annot_def by (metis consistent_CNot_not sup.orderE sup_commute true_clss_def
          true_clss_singleton_lit_of_implies_incl true_clss_union true_clss_union_increase)

      have "undefined_lit F K" using \<open>no_dup ?M\<close> unfolding M_K by (simp add: defined_lit_map)
      moreover
        have "?N \<union> ?C' \<Turnstile>ps {{#}}"
          proof -
            have A: "?N \<union> ?C' \<union> unmark_l ?M  =
              ?N \<union> unmark_l ?M"
              unfolding M_K by auto
            show ?thesis
              using true_clss_clss_left_right[OF N_C_M, of "{{#}}"] N_M_False unfolding A by auto
          qed
        have "?N \<Turnstile>p image_mset uminus ?C + {#-K#}"
          unfolding true_clss_cls_def true_clss_clss_def total_over_m_def
          proof (intro allI impI)
            fix I
            assume
              tot: "total_over_set I (atms_of_ms (?N \<union> {image_mset uminus ?C+ {#- K#}}))" and
              cons: "consistent_interp I" and
              "I \<Turnstile>s ?N"
            have "(K \<in> I \<and> -K \<notin> I) \<or> (-K \<in> I \<and> K \<notin> I)"
              using cons tot unfolding consistent_interp_def by (cases K) auto
            have " {a \<in> set (trail S). is_marked a \<and> a \<noteq> Marked K ()} =
              set (trail S) \<inter> {L. is_marked L \<and> L \<noteq> Marked K ()}"
             by auto
            then have tot': "total_over_set I
               (atm_of ` lit_of ` (set ?M \<inter> {L. is_marked L \<and> L \<noteq> Marked K ()}))"
<<<<<<< HEAD
              using tot by (auto simp add: atms_of_m_uminus_lit_atm_of_lit_of)
=======
              using tot by (auto simp add: atms_of_uminus_lit_atm_of_lit_of)

>>>>>>> origin/master
            { fix x :: "('v, unit, unit) marked_lit"
              assume
                a3: "lit_of x \<notin> I" and
                a1: "x \<in> set ?M" and
                a4: "is_marked x" and
                a5: "x \<noteq> Marked K ()"
              then have "Pos (atm_of (lit_of x)) \<in> I \<or> Neg (atm_of (lit_of x)) \<in> I"
                using a5 a4 tot' a1 unfolding total_over_set_def atms_of_m_s_def by blast
              moreover have f6: "Neg (atm_of (lit_of x)) = - Pos (atm_of (lit_of x))"
                by simp
              ultimately have "- lit_of x \<in> I"
                using f6 a3 by (metis (no_types) atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
                  literal.sel(1))
            } note H = this

            have "\<not>I \<Turnstile>s ?C'"
              using \<open>?N \<union> ?C' \<Turnstile>ps {{#}}\<close> tot cons \<open>I \<Turnstile>s ?N\<close>
              unfolding true_clss_clss_def total_over_m_def
              by (simp add: atms_of_m_uminus_lit_atm_of_lit_of atms_of_ms_single_image_atm_of_lit_of)
            then show "I \<Turnstile> image_mset uminus ?C + {#- K#}"
              unfolding true_clss_def true_cls_def Bex_def
              using \<open>(K \<in> I \<and> -K \<notin> I) \<or> (-K \<in> I \<and> K \<notin> I)\<close>
              by (auto dest!: H)
          qed
      moreover have "F \<Turnstile>as CNot (image_mset uminus ?C)"
        using nm unfolding true_annots_def CNot_def M_K by (auto simp add: lits_of_def)
      ultimately have False
        using bj_can_jump[of S F' K F C "-K"
          "image_mset uminus (image_mset lit_of {# L :# mset ?M. is_marked L \<and> L \<noteq> Marked K ()#})"]
          \<open>C\<in>?N\<close> n_s \<open>?M \<Turnstile>as CNot C\<close> bj_backjump inv \<open>no_dup (trail S)\<close> unfolding M_K by auto
        then show ?thesis by fast
    qed auto
qed

end

locale dpll_with_backjumping =
  dpll_with_backjumping_ops trail clauses prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T
  propagate_conds inv backjump_conds
  for
    trail :: "'st \<Rightarrow> ('v, unit, unit) marked_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    prepend_trail :: "('v, unit, unit) marked_lit \<Rightarrow> 'st \<Rightarrow> 'st" and tl_trail :: "'st \<Rightarrow> 'st" and
    add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T:: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    propagate_conds :: "('v, unit, unit) marked_lit \<Rightarrow> 'st \<Rightarrow> bool" and
    inv :: "'st \<Rightarrow> bool" and
    backjump_conds :: "'v clause \<Rightarrow> 'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool"
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

lemma rtranclp_dpll_bj_atms_of_ms_clauses_inv:
  assumes
    "dpll_bj\<^sup>*\<^sup>* S T" and "inv S"
  shows "atms_of_mm (clauses S) = atms_of_mm (clauses T)"
  using assms by (induction rule: rtranclp_induct)
    (auto dest: rtranclp_dpll_bj_inv dpll_bj_atms_of_ms_clauses_inv)

lemma rtranclp_dpll_bj_atms_in_trail:
  assumes
    "dpll_bj\<^sup>*\<^sup>* S T" and
    "inv S" and
    "atm_of ` (lits_of_l (trail S)) \<subseteq> atms_of_mm (clauses S)"
  shows "atm_of ` (lits_of_l (trail T)) \<subseteq> atms_of_mm (clauses T)"
  using assms apply (induction rule: rtranclp_induct)
  using dpll_bj_atms_in_trail dpll_bj_atms_of_ms_clauses_inv rtranclp_dpll_bj_inv by auto

lemma rtranclp_dpll_bj_sat_iff:
  assumes "dpll_bj\<^sup>*\<^sup>* S T" and "inv S"
  shows "I \<Turnstile>sm clauses S \<longleftrightarrow> I \<Turnstile>sm clauses T"
  using assms by (induction rule: rtranclp_induct)
    (auto dest!: dpll_bj_sat_iff simp: rtranclp_dpll_bj_inv)

lemma rtranclp_dpll_bj_atms_in_trail_in_set:
  assumes
    "dpll_bj\<^sup>*\<^sup>* S T" and
    "inv S"
    "atms_of_mm (clauses S) \<subseteq> A" and
    "atm_of ` (lits_of_l (trail S)) \<subseteq> A"
  shows "atm_of ` (lits_of_l (trail T)) \<subseteq> A"
  using assms
    by (induction rule: rtranclp_induct)
       (auto dest: rtranclp_dpll_bj_inv
         simp add: dpll_bj_atms_in_trail_in_set rtranclp_dpll_bj_atms_of_ms_clauses_inv
           rtranclp_dpll_bj_inv)

lemma rtranclp_dpll_bj_all_decomposition_implies_inv:
  assumes
    "dpll_bj\<^sup>*\<^sup>* S T" and
    "inv S"
    "all_decomposition_implies_m (clauses S) (get_all_marked_decomposition (trail S))"
  shows "all_decomposition_implies_m (clauses T) (get_all_marked_decomposition (trail T))"
  using assms by (induction rule: rtranclp_induct)
    (auto intro: dpll_bj_all_decomposition_implies_inv simp: rtranclp_dpll_bj_inv)

lemma rtranclp_dpll_bj_inv_incl_dpll_bj_inv_trancl:
  "{(T, S). dpll_bj\<^sup>+\<^sup>+ S T
    \<and> atms_of_mm (clauses S) \<subseteq> atms_of_ms A \<and> atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A
    \<and> no_dup (trail S) \<and> inv S}
     \<subseteq> {(T, S). dpll_bj S T \<and> atms_of_mm (clauses S) \<subseteq> atms_of_ms A
        \<and> atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A \<and> no_dup (trail S) \<and> inv S}\<^sup>+"
    (is "?A \<subseteq> ?B\<^sup>+")
proof standard
  fix x
  assume x_A: "x \<in> ?A"
  obtain S T::"'st" where
    x[simp]: "x = (T, S)" by (cases x) auto
  have
    "dpll_bj\<^sup>+\<^sup>+ S T" and
    "atms_of_mm (clauses S) \<subseteq> atms_of_ms A" and
    "atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A" and
    "no_dup (trail S)" and
     "inv S"
    using x_A by auto
  then show "x \<in> ?B\<^sup>+" unfolding x
    proof (induction rule: tranclp_induct)
      case base
      then show ?case by auto
    next
      case (step T U) note step = this(1) and ST = this(2) and IH = this(3)[OF this(4-7)]
        and N_A = this(4) and M_A = this(5) and nd = this(6) and inv = this(7)

      have [simp]: "atms_of_mm (clauses S) = atms_of_mm (clauses T)"
        using step rtranclp_dpll_bj_atms_of_ms_clauses_inv tranclp_into_rtranclp inv by fastforce
      have "no_dup (trail T)"
        using local.step nd rtranclp_dpll_bj_no_dup tranclp_into_rtranclp inv by fastforce
      moreover have "atm_of ` (lits_of_l (trail T)) \<subseteq> atms_of_ms A"
        by (metis inv M_A N_A local.step rtranclp_dpll_bj_atms_in_trail_in_set
          tranclp_into_rtranclp)
      moreover have "inv T"
         using inv local.step rtranclp_dpll_bj_inv tranclp_into_rtranclp by fastforce
      ultimately have "(U, T) \<in> ?B" using ST N_A M_A inv by auto
      then show ?case using IH by (rule trancl_into_trancl2)
    qed
qed

lemma wf_tranclp_dpll_bj:
  assumes fin: "finite A"
  shows "wf {(T, S). dpll_bj\<^sup>+\<^sup>+ S T
    \<and> atms_of_mm (clauses S) \<subseteq> atms_of_ms A \<and> atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A
    \<and> no_dup (trail S) \<and> inv S}"
  using wf_trancl[OF wf_dpll_bj[OF fin]] rtranclp_dpll_bj_inv_incl_dpll_bj_inv_trancl
  by (rule wf_subset)

lemma dpll_bj_sat_ext_iff:
  "dpll_bj S T \<Longrightarrow> inv S \<Longrightarrow> I\<Turnstile>sextm clauses S \<longleftrightarrow> I\<Turnstile>sextm clauses T"
  by (simp add: dpll_bj_clauses)

lemma rtranclp_dpll_bj_sat_ext_iff:
  "dpll_bj\<^sup>*\<^sup>* S T \<Longrightarrow> inv S \<Longrightarrow> I\<Turnstile>sextm clauses S \<longleftrightarrow> I\<Turnstile>sextm clauses T"
  by (induction rule: rtranclp_induct) (simp_all add: rtranclp_dpll_bj_inv dpll_bj_sat_ext_iff)

theorem full_dpll_backjump_final_state:
  fixes A :: "'v literal multiset set" and S T :: "'st"
  assumes
    full: "full dpll_bj S T" and
    atms_S: "atms_of_mm (clauses S) \<subseteq> atms_of_ms A" and
    atms_trail: "atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A" and
    n_d: "no_dup (trail S)" and
    "finite A" and
    inv: "inv S" and
    decomp: "all_decomposition_implies_m (clauses S) (get_all_marked_decomposition (trail S))"
  shows "unsatisfiable (set_mset (clauses S))
  \<or> (trail T \<Turnstile>asm clauses S \<and> satisfiable (set_mset (clauses S)))"
proof -
  have st: "dpll_bj\<^sup>*\<^sup>* S T" and "no_step dpll_bj T"
    using full unfolding full_def by fast+
  moreover have "atms_of_mm (clauses T) \<subseteq> atms_of_ms A"
    using atms_S inv rtranclp_dpll_bj_atms_of_ms_clauses_inv st by blast
  moreover have "atm_of ` lits_of_l (trail T) \<subseteq> atms_of_ms A"
     using atms_S atms_trail inv rtranclp_dpll_bj_atms_in_trail_in_set st by auto
  moreover have "no_dup (trail T)"
    using n_d inv rtranclp_dpll_bj_no_dup st by blast
  moreover have inv: "inv T"
    using inv rtranclp_dpll_bj_inv st by blast
  moreover
    have decomp: "all_decomposition_implies_m (clauses T) (get_all_marked_decomposition (trail T))"
      using \<open>inv S\<close> decomp rtranclp_dpll_bj_all_decomposition_implies_inv st by blast
  ultimately have "unsatisfiable (set_mset (clauses T))
    \<or> (trail T \<Turnstile>asm clauses T \<and> satisfiable (set_mset (clauses T)))"
    using \<open>finite A\<close> dpll_backjump_final_state by force
  then show ?thesis
    by (meson \<open>inv S\<close> rtranclp_dpll_bj_sat_iff satisfiable_carac st true_annots_true_cls)
qed

corollary full_dpll_backjump_final_state_from_init_state:
  fixes A :: "'v literal multiset set" and S T :: "'st"
  assumes
    full: "full dpll_bj S T" and
    "trail S = []" and
    "clauses S = N" and
    "inv S"
  shows "unsatisfiable (set_mset N) \<or> (trail T \<Turnstile>asm N \<and> satisfiable (set_mset N))"
  using assms full_dpll_backjump_final_state[of S T "set_mset N"] by auto

lemma tranclp_dpll_bj_trail_mes_decreasing_prop:
  assumes dpll: "dpll_bj\<^sup>+\<^sup>+ S T"  and inv: "inv S" and
  N_A: "atms_of_mm (clauses S) \<subseteq> atms_of_ms A" and
  M_A: "atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A" and
  n_d: "no_dup (trail S)" and
  fin_A: "finite A"
  shows "(2+card (atms_of_ms A)) ^ (1+card (atms_of_ms A))
               - \<mu>\<^sub>C (1+card (atms_of_ms A)) (2+card (atms_of_ms A)) (trail_weight T)
            < (2+card (atms_of_ms A)) ^ (1+card (atms_of_ms A))
               - \<mu>\<^sub>C (1+card (atms_of_ms A)) (2+card (atms_of_ms A)) (trail_weight S)"
  using dpll
proof (induction)
  case base
  then show ?case
    using N_A M_A n_d dpll_bj_trail_mes_decreasing_prop fin_A inv by blast
next
  case (step T U) note st = this(1) and dpll = this(2) and IH = this(3)
  have " atms_of_mm (clauses S) = atms_of_mm (clauses T)"
    using rtranclp_dpll_bj_atms_of_ms_clauses_inv by (metis dpll_bj_clauses dpll_bj_inv inv st
      tranclpD)
  then have N_A': "atms_of_mm (clauses T) \<subseteq> atms_of_ms A"
     using N_A by auto
  moreover have M_A': "atm_of ` lits_of_l (trail T) \<subseteq> atms_of_ms A"
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
subsubsection \<open>Learn and Forget\<close>
locale learn_ops =
  dpll_state trail clauses prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T
  for
    trail :: "'st \<Rightarrow> ('v, unit, unit) marked_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    prepend_trail :: "('v, unit, unit) marked_lit \<Rightarrow> 'st \<Rightarrow> 'st" and tl_trail :: "'st \<Rightarrow> 'st" and
    add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T:: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" +
  fixes
    learn_cond :: "'v clause \<Rightarrow> 'st \<Rightarrow> bool"

begin
inductive learn :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
"clauses S \<Turnstile>pm C \<Longrightarrow> atms_of C \<subseteq> atms_of_mm (clauses S) \<union> atm_of ` (lits_of_l (trail S))
  \<Longrightarrow> learn_cond C S
  \<Longrightarrow> T \<sim> add_cls\<^sub>N\<^sub>O\<^sub>T C S
  \<Longrightarrow> learn S T"
inductive_cases learn\<^sub>N\<^sub>O\<^sub>TE: "learn S T"

lemma learn_\<mu>\<^sub>C_stable:
  assumes "learn S T" and "no_dup (trail S)"
  shows "\<mu>\<^sub>C A B (trail_weight S) = \<mu>\<^sub>C A B (trail_weight T)"
  using assms by (auto elim: learn\<^sub>N\<^sub>O\<^sub>TE)
end

locale forget_ops =
  dpll_state trail clauses prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T
  for
    trail :: "'st \<Rightarrow> ('v, unit, unit) marked_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    prepend_trail :: "('v, unit, unit) marked_lit \<Rightarrow> 'st \<Rightarrow> 'st" and tl_trail :: "'st \<Rightarrow> 'st" and
    add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T:: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" +
  fixes
    forget_cond :: "'v clause \<Rightarrow> 'st \<Rightarrow> bool"
begin
inductive forget\<^sub>N\<^sub>O\<^sub>T :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
forget\<^sub>N\<^sub>O\<^sub>T:"clauses S - replicate_mset (count (clauses S) C) C \<Turnstile>pm C
  \<Longrightarrow> forget_cond C S
  \<Longrightarrow> C \<in># clauses S
  \<Longrightarrow> T \<sim> remove_cls\<^sub>N\<^sub>O\<^sub>T C S
  \<Longrightarrow> forget\<^sub>N\<^sub>O\<^sub>T S T"
inductive_cases forget\<^sub>N\<^sub>O\<^sub>TE: "forget\<^sub>N\<^sub>O\<^sub>T S T"

lemma forget_\<mu>\<^sub>C_stable:
  assumes "forget\<^sub>N\<^sub>O\<^sub>T S T"
  shows "\<mu>\<^sub>C A B (trail_weight S) = \<mu>\<^sub>C A B (trail_weight T)"
  using assms by (auto elim!: forget\<^sub>N\<^sub>O\<^sub>TE)
end

locale learn_and_forget\<^sub>N\<^sub>O\<^sub>T =
  learn_ops trail clauses prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T learn_cond +
  forget_ops trail clauses prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T forget_cond
  for
    trail :: "'st \<Rightarrow> ('v, unit, unit) marked_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    prepend_trail :: "('v, unit, unit) marked_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T:: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    learn_cond forget_cond :: "'v clause \<Rightarrow> 'st \<Rightarrow> bool"
begin
inductive learn_and_forget\<^sub>N\<^sub>O\<^sub>T :: "'st \<Rightarrow> 'st \<Rightarrow> bool"
where
lf_learn: "learn S T \<Longrightarrow> learn_and_forget\<^sub>N\<^sub>O\<^sub>T S T" |
lf_forget: "forget\<^sub>N\<^sub>O\<^sub>T S T \<Longrightarrow> learn_and_forget\<^sub>N\<^sub>O\<^sub>T S T"
end

subsubsection \<open>Definition of CDCL\<close>
locale conflict_driven_clause_learning_ops =
  dpll_with_backjumping_ops trail clauses prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T
    propagate_conds inv backjump_conds +
  learn_and_forget\<^sub>N\<^sub>O\<^sub>T trail clauses prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T learn_cond
    forget_cond
    for
      trail :: "'st \<Rightarrow> ('v, unit, unit) marked_lits" and
      clauses :: "'st \<Rightarrow> 'v clauses" and
      prepend_trail :: "('v, unit, unit) marked_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
      tl_trail :: "'st \<Rightarrow> 'st" and
      add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T:: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
      propagate_conds :: "('v, unit, unit) marked_lit \<Rightarrow>'st \<Rightarrow> bool" and
      inv :: "'st \<Rightarrow> bool" and
      backjump_conds ::  "'v clause \<Rightarrow> 'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool" and
      learn_cond forget_cond :: "'v clause \<Rightarrow> 'st \<Rightarrow> bool"
begin

inductive cdcl\<^sub>N\<^sub>O\<^sub>T :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
c_dpll_bj: "dpll_bj S S' \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T S S'" |
c_learn: "learn S S' \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T S S'" |
c_forget\<^sub>N\<^sub>O\<^sub>T: "forget\<^sub>N\<^sub>O\<^sub>T S S' \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T S S'"

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_all_induct[consumes 1, case_names dpll_bj learn forget\<^sub>N\<^sub>O\<^sub>T]:
  fixes S T :: "'st"
  assumes "cdcl\<^sub>N\<^sub>O\<^sub>T S T" and
    dpll: "\<And>T. dpll_bj S T \<Longrightarrow> P S T" and
    learning:
      "\<And>C T. clauses S \<Turnstile>pm C \<Longrightarrow>
      atms_of C \<subseteq> atms_of_mm (clauses S) \<union> atm_of ` (lits_of_l (trail S)) \<Longrightarrow>
      T \<sim> add_cls\<^sub>N\<^sub>O\<^sub>T C S \<Longrightarrow>
      P S T" and
    forgetting: "\<And>C T. clauses S - replicate_mset (count (clauses S) C) C \<Turnstile>pm C \<Longrightarrow>
      C \<in># clauses S \<Longrightarrow>
      T \<sim> remove_cls\<^sub>N\<^sub>O\<^sub>T C S \<Longrightarrow>
      P S T"
  shows "P S T"
  using assms(1) by (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T.induct)
  (auto intro: assms(2, 3, 4) elim!: learn\<^sub>N\<^sub>O\<^sub>TE forget\<^sub>N\<^sub>O\<^sub>TE)+

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T S T" and
    "inv S" and
    "no_dup (trail S)"
  shows "no_dup (trail T)"
  using assms by (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_all_induct) (auto intro: dpll_bj_no_dup)

paragraph \<open>Consistency of the trail\<close>
lemma cdcl\<^sub>N\<^sub>O\<^sub>T_consistent:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T S T" and
    "inv S" and
    "no_dup (trail S)"
  shows "consistent_interp (lits_of_l (trail T))"
  using cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup[OF assms] distinct_consistent_interp by fast

text \<open>The subtle problem here is that tautologies can be removed, meaning that some variable can
  disappear of the problem. It is also possible that some variable of the trail are not in the
  clauses anymore.\<close>
lemma cdcl\<^sub>N\<^sub>O\<^sub>T_atms_of_ms_clauses_decreasing:
  assumes "cdcl\<^sub>N\<^sub>O\<^sub>T S T"and "inv S" and "no_dup (trail S)"
  shows "atms_of_mm (clauses T) \<subseteq> atms_of_mm (clauses S) \<union> atm_of ` (lits_of_l (trail S))"
  using assms by (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_all_induct)
    (auto dest!: dpll_bj_atms_of_ms_clauses_inv set_mp simp add: atms_of_ms_def Union_eq)

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_atms_in_trail:
  assumes "cdcl\<^sub>N\<^sub>O\<^sub>T S T"and "inv S" and "no_dup (trail S)"
  and "atm_of ` (lits_of_l (trail S)) \<subseteq> atms_of_mm (clauses S)"
  shows "atm_of ` (lits_of_l (trail T)) \<subseteq> atms_of_mm (clauses S)"
  using assms by (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_all_induct) (auto simp add: dpll_bj_atms_in_trail)

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_atms_in_trail_in_set:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T S T" and "inv S" and "no_dup (trail S)" and
    "atms_of_mm (clauses S) \<subseteq> A" and
    "atm_of ` (lits_of_l (trail S)) \<subseteq> A"
  shows "atm_of ` (lits_of_l (trail T)) \<subseteq> A"
  using assms
  by (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_all_induct)
     (simp_all add: dpll_bj_atms_in_trail_in_set dpll_bj_atms_of_ms_clauses_inv)

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_all_decomposition_implies:
  assumes "cdcl\<^sub>N\<^sub>O\<^sub>T S T" and "inv S" and n_d[simp]: "no_dup (trail S)" and
    "all_decomposition_implies_m (clauses S) (get_all_marked_decomposition (trail S))"
  shows
    "all_decomposition_implies_m (clauses T) (get_all_marked_decomposition (trail T))"
  using assms(1,2,4)
proof (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_all_induct)
  case dpll_bj
  then show ?case
     using dpll_bj_all_decomposition_implies_inv n_d by blast
next
  case learn
  then show ?case by (auto simp add: all_decomposition_implies_def)
next
  case (forget\<^sub>N\<^sub>O\<^sub>T C T) note cls_C = this(1) and C = this(2) and T = this(3) and iniv = this(4) and
    decomp = this(5)
  show ?case
    unfolding all_decomposition_implies_def Ball_def
    proof (intro allI, clarify)
      fix a b
      assume "(a, b) \<in> set (get_all_marked_decomposition (trail T))"
      then have "unmark_l a \<union> set_mset (clauses S) \<Turnstile>ps unmark_l b"
        using decomp T by (auto simp add: all_decomposition_implies_def)
      moreover
        have "C \<in> set_mset (clauses S)"
          by (simp add: C)
        then have "set_mset (clauses T) \<Turnstile>ps set_mset (clauses S)"
          by (metis (no_types) T clauses_remove_cls\<^sub>N\<^sub>O\<^sub>T cls_C insert_Diff order_refl
            set_mset_minus_replicate_mset(1) state_eq\<^sub>N\<^sub>O\<^sub>T_clauses true_clss_clss_def
            true_clss_clss_insert)
      ultimately show "unmark_l a \<union> set_mset (clauses T)
        \<Turnstile>ps unmark_l b"
        using true_clss_clss_generalise_true_clss_clss by blast
    qed
qed

paragraph \<open>Extension of models\<close>
lemma cdcl\<^sub>N\<^sub>O\<^sub>T_bj_sat_ext_iff:
  assumes "cdcl\<^sub>N\<^sub>O\<^sub>T S T"and "inv S" and n_d: "no_dup (trail S)"
  shows "I\<Turnstile>sextm clauses S \<longleftrightarrow> I\<Turnstile>sextm clauses T"
  using assms
proof (induction rule:cdcl\<^sub>N\<^sub>O\<^sub>T_all_induct)
  case dpll_bj
  then show ?case by (simp add: dpll_bj_clauses)
next
  case (learn C T) note T = this(3)
  { fix J
    assume
      "I \<Turnstile>sextm clauses S" and
      "I \<subseteq> J" and
      tot: "total_over_m J (set_mset ({#C#} + (clauses S)))" and
      cons: "consistent_interp J"
    then have "J \<Turnstile>sm clauses S" unfolding true_clss_ext_def by auto

    moreover
      with \<open>clauses S\<Turnstile>pm C\<close> have "J \<Turnstile> C"
        using tot cons unfolding true_clss_cls_def by auto
    ultimately have "J \<Turnstile>sm {#C#} + clauses S" by auto
  }
  then have H: "I \<Turnstile>sextm (clauses S) \<Longrightarrow> I \<Turnstile>sext insert C (set_mset (clauses S))"
    unfolding true_clss_ext_def by auto
  show ?case
    apply standard
      using T n_d apply (auto simp add: H)[]
    using T n_d apply simp
    by (metis Diff_insert_absorb insert_subset subsetI subset_antisym
      true_clss_ext_decrease_right_remove_r)
next
  case (forget\<^sub>N\<^sub>O\<^sub>T C T) note cls_C = this(1) and T = this(3)
  { fix J
    assume
      "I \<Turnstile>sext set_mset (clauses S) - {C}" and
      "I \<subseteq> J" and
      tot: "total_over_m J (set_mset (clauses S))" and
      cons: "consistent_interp J"
    then have "J \<Turnstile>s set_mset (clauses S) - {C}"
      unfolding true_clss_ext_def by (meson Diff_subset total_over_m_subset)

    moreover
      with cls_C have "J \<Turnstile> C"
        using tot cons unfolding true_clss_cls_def
        by (metis Un_commute forget\<^sub>N\<^sub>O\<^sub>T.hyps(2) insert_Diff insert_is_Un order_refl
          set_mset_minus_replicate_mset(1))
    ultimately have "J \<Turnstile>sm (clauses S)" by (metis insert_Diff_single true_clss_insert)
  }
  then have H: "I \<Turnstile>sext set_mset (clauses S) - {C} \<Longrightarrow> I \<Turnstile>sextm (clauses S)"
    unfolding true_clss_ext_def by blast
  show ?case using T by (auto simp: true_clss_ext_decrease_right_remove_r H)
qed

end \<comment> \<open>end of \<open>conflict_driven_clause_learning_ops\<close>\<close>

subsection \<open>CDCL with invariant\<close>
locale conflict_driven_clause_learning =
  conflict_driven_clause_learning_ops +
  assumes cdcl\<^sub>N\<^sub>O\<^sub>T_inv: "\<And>S T. cdcl\<^sub>N\<^sub>O\<^sub>T S T \<Longrightarrow> inv S \<Longrightarrow> inv T"
begin
sublocale dpll_with_backjumping
  apply unfold_locales
  using cdcl\<^sub>N\<^sub>O\<^sub>T.simps cdcl\<^sub>N\<^sub>O\<^sub>T_inv by auto

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_inv:
  "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T \<Longrightarrow> inv S \<Longrightarrow> inv T"
  by (induction rule: rtranclp_induct) (auto simp add: cdcl\<^sub>N\<^sub>O\<^sub>T_inv)

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup:
  assumes "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T" and "inv S"
  and "no_dup (trail S)"
  shows "no_dup (trail T)"
  using assms by (induction rule: rtranclp_induct) (auto intro: cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_inv)

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_trail_clauses_bound:
  assumes
    cdcl: "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T" and
    inv: "inv S" and
    n_d: "no_dup (trail S)" and
    atms_clauses_S: "atms_of_mm (clauses S) \<subseteq> A" and
    atms_trail_S: "atm_of `(lits_of_l (trail S)) \<subseteq> A"
  shows "atm_of `(lits_of_l (trail T)) \<subseteq> A \<and> atms_of_mm (clauses T) \<subseteq>  A"
  using cdcl
proof (induction rule: rtranclp_induct)
  case base
  then show ?case using atms_clauses_S atms_trail_S by simp
next
  case (step T U) note st = this(1) and cdcl\<^sub>N\<^sub>O\<^sub>T = this(2) and IH = this(3)
  have "inv T" using inv st rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_inv by blast
  have "no_dup (trail T)"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup[of S T] st cdcl\<^sub>N\<^sub>O\<^sub>T inv n_d by blast
  then have "atms_of_mm (clauses U) \<subseteq> A"
    using cdcl\<^sub>N\<^sub>O\<^sub>T_atms_of_ms_clauses_decreasing[OF cdcl\<^sub>N\<^sub>O\<^sub>T] IH n_d \<open>inv T\<close> by auto
  moreover
    have "atm_of `(lits_of_l (trail U)) \<subseteq> A"
      using cdcl\<^sub>N\<^sub>O\<^sub>T_atms_in_trail_in_set[OF cdcl\<^sub>N\<^sub>O\<^sub>T, of A] \<open>no_dup (trail T)\<close>
      by (meson atms_trail_S atms_clauses_S IH \<open>inv T\<close> cdcl\<^sub>N\<^sub>O\<^sub>T )
  ultimately show ?case by fast
qed

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_all_decomposition_implies:
  assumes "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T" and "inv S" and "no_dup (trail S)" and
    "all_decomposition_implies_m (clauses S) (get_all_marked_decomposition (trail S))"
  shows
    "all_decomposition_implies_m (clauses T) (get_all_marked_decomposition (trail T))"
  using assms by (induction)
  (auto intro: rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_inv cdcl\<^sub>N\<^sub>O\<^sub>T_all_decomposition_implies rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup)

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_bj_sat_ext_iff:
  assumes "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T"and "inv S" and "no_dup (trail S)"
  shows "I\<Turnstile>sextm clauses S \<longleftrightarrow> I\<Turnstile>sextm clauses T"
  using assms apply (induction rule: rtranclp_induct)
  using cdcl\<^sub>N\<^sub>O\<^sub>T_bj_sat_ext_iff by (auto intro: rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_inv rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup)

definition cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv where
"cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv A S \<longleftrightarrow> (finite A \<and> inv S \<and> atms_of_mm (clauses S) \<subseteq> atms_of_ms A
    \<and> atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A \<and> no_dup (trail S))"

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv:
  assumes "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T" and "cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv A S"
  shows "cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv A T"
  using assms unfolding cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv_def
  by (simp add: rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_inv rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_trail_clauses_bound)

(* FIXME: beta-reduce? *)
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
  shows "(2+card (atms_of_ms A)) ^ (1+card (atms_of_ms A))
      - \<mu>\<^sub>C (1+card (atms_of_ms A)) (2+card (atms_of_ms A)) (trail_weight U)
    <  (2+card (atms_of_ms A)) ^ (1+card (atms_of_ms A))
      - \<mu>\<^sub>C (1+card (atms_of_ms A)) (2+card (atms_of_ms A)) (trail_weight S)"
     (is "?\<mu> U < ?\<mu> S")
proof -
  have "?\<mu> S = ?\<mu> T"
    using l_f
    proof (induction)
      case base
      then show ?case by simp
    next
      case (step T U)
      moreover then have "no_dup (trail T)"
        using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup[of S T] cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv_def inv
        rtranclp_learn_or_forget_cdcl\<^sub>N\<^sub>O\<^sub>T by auto
      ultimately show ?case
        using forget_\<mu>\<^sub>C_stable learn_\<mu>\<^sub>C_stable inv unfolding cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv_def by presburger
    qed
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
proof (induction "(2+card (atms_of_ms A)) ^ (1+card (atms_of_ms A))
    - \<mu>\<^sub>C (1+card (atms_of_ms A)) (2+card (atms_of_ms A)) (trail_weight (f 0))"
    arbitrary: f
    rule: nat_less_induct_case)
  case (Suc n) note IH = this(1) and \<mu> = this(2) and cdcl\<^sub>N\<^sub>O\<^sub>T = this(3) and inv = this(4)
  consider
      (dpll_end) "\<exists>j. \<forall>i\<ge>j. learn_or_forget (f i) (f (Suc i))"
    | (dpll_more) "\<not>(\<exists>j. \<forall>i\<ge>j. learn_or_forget (f i) (f (Suc i)))"
    by blast
  then show ?case
    proof cases
      case dpll_end
      then show ?thesis by auto
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
          then have "{i. i\<le>i\<^sub>0 \<and>  \<not> learn (f i) (f (Suc i)) \<and> \<not>forget\<^sub>N\<^sub>O\<^sub>T (f i) (f (Suc i))} \<noteq> {}"
            by auto
          let ?I = "{i. i\<le>i\<^sub>0 \<and>  \<not> learn (f i) (f (Suc i)) \<and> \<not>forget\<^sub>N\<^sub>O\<^sub>T (f i) (f (Suc i))}"
          let ?i = "Min ?I"
          have "finite ?I"
            by auto
          have "\<not> learn (f ?i) (f (Suc ?i)) \<and> \<not>forget\<^sub>N\<^sub>O\<^sub>T (f ?i) (f (Suc ?i))"
            using Min_in[OF \<open>finite ?I\<close> \<open>?I \<noteq> {}\<close>] by auto
          moreover have "\<forall>k<?i. learn_or_forget (f k) (f (Suc k))"
            using Min.coboundedI[of "{i. i \<le> i\<^sub>0 \<and> \<not> learn (f i) (f (Suc i)) \<and> \<not> forget\<^sub>N\<^sub>O\<^sub>T (f i)
              (f (Suc i))}", simplified]
            by (meson \<open>\<not> learn (f i\<^sub>0) (f (Suc i\<^sub>0)) \<and> \<not> forget\<^sub>N\<^sub>O\<^sub>T (f i\<^sub>0) (f (Suc i\<^sub>0))\<close> less_imp_le
              dual_order.trans not_le)
          ultimately show ?thesis using that by blast
        qed
      def g \<equiv> "\<lambda>n. f (n + Suc i)"
      have "dpll_bj (f i) (g 0)"
        using \<open>\<not> learn (f i) (f (Suc i)) \<and> \<not> forget\<^sub>N\<^sub>O\<^sub>T (f i) (f (Suc i))\<close> cdcl\<^sub>N\<^sub>O\<^sub>T cdcl\<^sub>N\<^sub>O\<^sub>T.cases
        g_def by auto
      {
        fix j
        assume "j \<le> i"
        then have "learn_or_forget\<^sup>*\<^sup>* (f 0) (f j)"
          apply (induction j)
           apply simp
          by (metis (no_types, lifting) Suc_leD Suc_le_lessD rtranclp.simps
            \<open>\<forall>k<i. learn (f k) (f (Suc k)) \<or> forget\<^sub>N\<^sub>O\<^sub>T (f k) (f (Suc k))\<close>)
      }
      then have "learn_or_forget\<^sup>*\<^sup>* (f 0) (f i)" by blast
      then have "(2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A))
           - \<mu>\<^sub>C (1 + card (atms_of_ms A)) (2 + card (atms_of_ms A)) (trail_weight (g 0))
        < (2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A))
          - \<mu>\<^sub>C (1 + card (atms_of_ms A)) (2 + card (atms_of_ms A)) (trail_weight (f 0))"
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
            then have "learn_or_forget (f k) (f (Suc k))"
              using j[of "k-Suc i"] unfolding g_def by auto
          }
          then show "\<forall>k\<ge>j+Suc i. learn_or_forget (f k) (f (Suc k))"
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
          then have "{i. i\<le>i\<^sub>0 \<and>  \<not> learn (f i) (f (Suc i)) \<and> \<not>forget\<^sub>N\<^sub>O\<^sub>T (f i) (f (Suc i))} \<noteq> {}"
            by auto
          let ?I = "{i. i\<le>i\<^sub>0 \<and>  \<not> learn (f i) (f (Suc i)) \<and> \<not>forget\<^sub>N\<^sub>O\<^sub>T (f i) (f (Suc i))}"
          let ?i = "Min ?I"
          have "finite ?I"
            by auto
          have "\<not> learn (f ?i) (f (Suc ?i)) \<and> \<not>forget\<^sub>N\<^sub>O\<^sub>T (f ?i) (f (Suc ?i))"
            using Min_in[OF \<open>finite ?I\<close> \<open>?I \<noteq> {}\<close>] by auto
          moreover have "\<forall>k<?i. learn_or_forget (f k) (f (Suc k))"
            using Min.coboundedI[of "{i. i \<le> i\<^sub>0 \<and> \<not> learn (f i) (f (Suc i)) \<and> \<not> forget\<^sub>N\<^sub>O\<^sub>T (f i)
              (f (Suc i))}", simplified]
            by (meson \<open>\<not> learn (f i\<^sub>0) (f (Suc i\<^sub>0)) \<and> \<not> forget\<^sub>N\<^sub>O\<^sub>T (f i\<^sub>0) (f (Suc i\<^sub>0))\<close> less_imp_le
              dual_order.trans not_le)
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
      then have "learn_or_forget\<^sup>*\<^sup>* (f 0) (f i)" by blast

      then show False
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
  then have "\<exists>j. \<forall>i\<ge>j. learn_or_forget (f i) (f (Suc i))"
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

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_final_state:
  assumes
    n_s: "no_step cdcl\<^sub>N\<^sub>O\<^sub>T S" and
    inv: "cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv A S" and
    decomp: "all_decomposition_implies_m (clauses S) (get_all_marked_decomposition (trail S))"
  shows "unsatisfiable (set_mset (clauses S))
    \<or> (trail S \<Turnstile>asm clauses S \<and> satisfiable (set_mset (clauses S)))"
proof -
  have n_s': "no_step dpll_bj S"
    using n_s by (auto simp: cdcl\<^sub>N\<^sub>O\<^sub>T.simps)
  show ?thesis
    apply (rule dpll_backjump_final_state[of S A])
    using inv decomp n_s' unfolding cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv_def by auto
qed

lemma full_cdcl\<^sub>N\<^sub>O\<^sub>T_final_state:
  assumes
    full: "full cdcl\<^sub>N\<^sub>O\<^sub>T S T" and
    inv: "cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv A S" and
    n_d: "no_dup (trail S)" and
    decomp: "all_decomposition_implies_m (clauses S) (get_all_marked_decomposition (trail S))"
  shows "unsatisfiable (set_mset (clauses T))
    \<or> (trail T \<Turnstile>asm clauses T \<and> satisfiable (set_mset (clauses T)))"
proof -
  have st: "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T" and n_s: "no_step cdcl\<^sub>N\<^sub>O\<^sub>T T"
    using full unfolding full_def by blast+
  have n_s': "cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv A T"
    using cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv inv st by blast
  moreover have "all_decomposition_implies_m (clauses T) (get_all_marked_decomposition (trail T))"
    using cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv_def decomp inv rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_all_decomposition_implies st by auto
  ultimately show ?thesis
    using cdcl\<^sub>N\<^sub>O\<^sub>T_final_state n_s by blast
qed

end \<comment> \<open>end of \<open>conflict_driven_clause_learning\<close>\<close>

subsection \<open>Termination\<close>
subsubsection \<open>Restricting learn and forget\<close>

locale conflict_driven_clause_learning_learning_before_backjump_only_distinct_learnt =
  conflict_driven_clause_learning trail clauses prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T
  propagate_conds inv backjump_conds
  "\<lambda>C S.  distinct_mset C \<and> \<not>tautology C \<and> learn_restrictions C S \<and>
    (\<exists>F K d F' C' L.  trail S = F' @ Marked K () # F \<and> C = C' + {#L#} \<and> F \<Turnstile>as CNot C'
      \<and> C' + {#L#} \<notin># clauses S)"
  "\<lambda>C S. \<not>(\<exists>F' F K d L. trail S = F' @ Marked K () # F \<and> F \<Turnstile>as CNot (C - {#L#}))
    \<and> forget_restrictions C S"
    for
      trail :: "'st \<Rightarrow> ('v, unit, unit) marked_lits" and
      clauses :: "'st \<Rightarrow> 'v clauses" and
      prepend_trail :: "('v, unit, unit) marked_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
      tl_trail :: "'st \<Rightarrow> 'st" and
      add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T:: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
      propagate_conds :: "('v, unit, unit) marked_lit \<Rightarrow> 'st \<Rightarrow> bool" and
      inv :: "'st \<Rightarrow> bool" and
      backjump_conds :: "'v clause \<Rightarrow> 'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool" and
      learn_restrictions forget_restrictions :: "'v clause \<Rightarrow> 'st \<Rightarrow> bool"
begin

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_learn_all_induct[consumes 1, case_names dpll_bj learn forget\<^sub>N\<^sub>O\<^sub>T]:
  fixes S T :: "'st"
  assumes "cdcl\<^sub>N\<^sub>O\<^sub>T S T" and
    dpll: "\<And>T. dpll_bj S T \<Longrightarrow> P S T" and
    learning:
      "\<And>C F K F' C' L T. clauses S \<Turnstile>pm C
      \<Longrightarrow> atms_of C \<subseteq> atms_of_mm (clauses S) \<union> atm_of ` (lits_of_l (trail S))
      \<Longrightarrow>  distinct_mset C \<Longrightarrow> \<not> tautology C \<Longrightarrow> learn_restrictions C S
      \<Longrightarrow> trail S = F' @ Marked K () # F \<Longrightarrow> C = C' + {#L#} \<Longrightarrow> F \<Turnstile>as CNot C'
      \<Longrightarrow> C' + {#L#} \<notin># clauses S \<Longrightarrow> T \<sim> add_cls\<^sub>N\<^sub>O\<^sub>T C S
      \<Longrightarrow> P S T" and
    forgetting: "\<And>C T. clauses S - replicate_mset (count (clauses S) C) C \<Turnstile>pm C
      \<Longrightarrow> C \<in># clauses S
      \<Longrightarrow> \<not>(\<exists>F' F K L. trail S = F' @ Marked K () # F \<and> F \<Turnstile>as CNot (C - {#L#}))
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
    n_d: "no_dup (trail S)"
  shows "set_mset (clauses T - clauses S)
    \<subseteq> simple_clss (atms_of_mm (clauses S) \<union> atm_of ` lits_of_l (trail S))"
proof
  fix C assume C: "C \<in> set_mset (clauses T - clauses S)"
  have "distinct_mset C" "\<not>tautology C" using learn C n_d by (elim learn\<^sub>N\<^sub>O\<^sub>TE; auto)+
  then have "C \<in> simple_clss (atms_of C)"
    using distinct_mset_not_tautology_implies_in_simple_clss by blast
  moreover have "atms_of C \<subseteq> atms_of_mm (clauses S) \<union> atm_of ` lits_of_l (trail S)"
    using learn C n_d by (elim learn\<^sub>N\<^sub>O\<^sub>TE) (auto simp: atms_of_ms_def atms_of_def image_Un
      true_annots_CNot_all_atms_defined)
  moreover have "finite (atms_of_mm (clauses S) \<union> atm_of ` lits_of_l (trail S))"
     by auto
  ultimately show "C \<in> simple_clss (atms_of_mm (clauses S) \<union> atm_of ` lits_of_l (trail S))"
    using simple_clss_mono  by (metis (no_types) insert_subset mk_disjoint_insert)
qed

definition "conflicting_bj_clss S \<equiv>
   {C+{#L#}|C L. C+{#L#} \<in># clauses S \<and> distinct_mset (C+{#L#}) \<and> \<not>tautology (C+{#L#})
     \<and> (\<exists>F' K F. trail S = F' @ Marked K () # F \<and> F \<Turnstile>as CNot C)}"

lemma conflicting_bj_clss_remove_cls\<^sub>N\<^sub>O\<^sub>T[simp]:
  "conflicting_bj_clss (remove_cls\<^sub>N\<^sub>O\<^sub>T C S) = conflicting_bj_clss S - {C}"
  unfolding conflicting_bj_clss_def by fastforce

lemma conflicting_bj_clss_add_cls\<^sub>N\<^sub>O\<^sub>T_state_eq:
  "T \<sim> add_cls\<^sub>N\<^sub>O\<^sub>T C' S \<Longrightarrow> no_dup (trail S) \<Longrightarrow> conflicting_bj_clss T
    = conflicting_bj_clss S
      \<union> (if \<exists>C L. C' = C +{#L#} \<and> distinct_mset (C+{#L#}) \<and> \<not>tautology (C+{#L#})
     \<and> (\<exists>F' K d F. trail S = F' @ Marked K () # F \<and> F \<Turnstile>as CNot C)
     then {C'} else {})"
  unfolding conflicting_bj_clss_def by auto metis+

lemma conflicting_bj_clss_add_cls\<^sub>N\<^sub>O\<^sub>T:
  " no_dup (trail S) \<Longrightarrow>
  conflicting_bj_clss (add_cls\<^sub>N\<^sub>O\<^sub>T C' S)
    = conflicting_bj_clss S
      \<union> (if \<exists>C L. C' = C +{#L#}\<and> distinct_mset (C+{#L#}) \<and> \<not>tautology (C+{#L#})
     \<and> (\<exists>F' K d F. trail S = F' @ Marked K () # F \<and> F \<Turnstile>as CNot C)
     then {C'} else {})"
  using conflicting_bj_clss_add_cls\<^sub>N\<^sub>O\<^sub>T_state_eq by auto

lemma conflicting_bj_clss_incl_clauses:
   "conflicting_bj_clss S \<subseteq> set_mset (clauses S)"
  unfolding conflicting_bj_clss_def by auto

lemma finite_conflicting_bj_clss[simp]:
  "finite (conflicting_bj_clss S)"
  using conflicting_bj_clss_incl_clauses[of S] rev_finite_subset by blast

lemma learn_conflicting_increasing:
  "no_dup (trail S) \<Longrightarrow> learn S T \<Longrightarrow> conflicting_bj_clss S \<subseteq> conflicting_bj_clss T"
  apply (elim learn\<^sub>N\<^sub>O\<^sub>TE)
  by (subst conflicting_bj_clss_add_cls\<^sub>N\<^sub>O\<^sub>T_state_eq[of T]) auto

abbreviation "conflicting_bj_clss_yet b S \<equiv>
  3 ^ b - card (conflicting_bj_clss S)"

abbreviation   \<mu>\<^sub>L :: "nat \<Rightarrow> 'st \<Rightarrow> nat \<times> nat" where
  "\<mu>\<^sub>L b S \<equiv> (conflicting_bj_clss_yet b S, card (set_mset (clauses S)))"

lemma do_not_forget_before_backtrack_rule_clause_learned_clause_untouched:
  assumes "forget\<^sub>N\<^sub>O\<^sub>T S T"
  shows "conflicting_bj_clss S = conflicting_bj_clss T"
  using assms apply induction
  unfolding conflicting_bj_clss_def
  by (metis (no_types, lifting) Diff_insert_absorb Set.set_insert clauses_remove_cls\<^sub>N\<^sub>O\<^sub>T
    diff_union_cancelR insert_iff order_refl set_mset_minus_replicate_mset(1)
    state_eq\<^sub>N\<^sub>O\<^sub>T_clauses state_eq\<^sub>N\<^sub>O\<^sub>T_trail trail_remove_cls\<^sub>N\<^sub>O\<^sub>T)

lemma forget_\<mu>\<^sub>L_decrease:
  assumes forget\<^sub>N\<^sub>O\<^sub>T: "forget\<^sub>N\<^sub>O\<^sub>T S T"
  shows "(\<mu>\<^sub>L b T, \<mu>\<^sub>L b S) \<in> less_than <*lex*> less_than"
proof -
  have "card (set_mset  (clauses T)) < card (set_mset  (clauses S))"
    using forget\<^sub>N\<^sub>O\<^sub>T apply induction
    by (metis card_Diff1_less clauses_remove_cls\<^sub>N\<^sub>O\<^sub>T finite_set_mset order_refl
      set_mset_minus_replicate_mset(1) state_eq\<^sub>N\<^sub>O\<^sub>T_clauses)
  then show ?thesis
    unfolding do_not_forget_before_backtrack_rule_clause_learned_clause_untouched[OF forget\<^sub>N\<^sub>O\<^sub>T]
    by auto
qed

lemma set_condition_or_split:
   "{a. (a = b \<or> Q a) \<and> S a} = (if S b then {b} else {}) \<union> {a. Q a \<and> S a}"
  by auto

lemma set_insert_neq:
  "A \<noteq> insert a A \<longleftrightarrow> a \<notin> A"
  by auto

lemma learn_\<mu>\<^sub>L_decrease:
  assumes learnST: "learn S T" and n_d: "no_dup (trail S)" and
   A: "atms_of_mm (clauses S) \<union> atm_of ` lits_of_l (trail S) \<subseteq> A" and
   fin_A: "finite A"
  shows "(\<mu>\<^sub>L (card A) T, \<mu>\<^sub>L (card A) S) \<in> less_than <*lex*> less_than"
proof -
  have [simp]: "(atms_of_mm (clauses T) \<union> atm_of ` lits_of_l (trail T))
    = (atms_of_mm (clauses S) \<union> atm_of ` lits_of_l (trail S))"
    using learnST n_d by (elim learn\<^sub>N\<^sub>O\<^sub>TE) auto

  then have "card (atms_of_mm (clauses T) \<union> atm_of ` lits_of_l (trail T))
    = card (atms_of_mm (clauses S) \<union> atm_of ` lits_of_l (trail S))"
    by (auto intro!: card_mono)
  then have 3: "(3::nat) ^ card (atms_of_mm (clauses T) \<union> atm_of ` lits_of_l (trail T))
    = 3 ^ card (atms_of_mm (clauses S) \<union> atm_of ` lits_of_l (trail S))"
    by (auto intro: power_mono)
  moreover have "conflicting_bj_clss S \<subseteq> conflicting_bj_clss T"
    using learnST n_d by (simp add: learn_conflicting_increasing)
  moreover have "conflicting_bj_clss S \<noteq> conflicting_bj_clss T"
    using learnST
    proof (elim learn\<^sub>N\<^sub>O\<^sub>TE, goal_cases)
      case (1 C) note clss_S = this(1) and atms_C = this(2) and inv = this(3) and T = this(4)
      then obtain F K F' C' L where
        tr_S: "trail S = F' @ Marked K () # F" and
        C: "C = C' + {#L#}" and
        F: "F \<Turnstile>as CNot C'" and
        C_S:"C' + {#L#} \<notin># clauses S"
        by blast
      moreover have "distinct_mset C" "\<not> tautology C" using inv by blast+
      ultimately have "C' + {#L#} \<in> conflicting_bj_clss T"
        using T n_d unfolding conflicting_bj_clss_def by fastforce
      moreover have "C' + {#L#} \<notin> conflicting_bj_clss S"
        using C_S unfolding conflicting_bj_clss_def by auto
      ultimately show ?case by blast
    qed
  moreover have fin_T: "finite (conflicting_bj_clss T)"
    using learnST by induction (auto simp add: conflicting_bj_clss_add_cls\<^sub>N\<^sub>O\<^sub>T )
  ultimately have "card (conflicting_bj_clss T) \<ge> card (conflicting_bj_clss S)"
    using card_mono by blast

  moreover
    have fin': "finite (atms_of_mm (clauses T) \<union> atm_of ` lits_of_l (trail T))"
      by auto
    have 1:"atms_of_ms (conflicting_bj_clss T) \<subseteq> atms_of_mm (clauses T)"
      unfolding conflicting_bj_clss_def atms_of_ms_def by auto
    have 2: "\<And>x. x\<in> conflicting_bj_clss T \<Longrightarrow> \<not> tautology x \<and> distinct_mset x"
      unfolding conflicting_bj_clss_def by auto
    have T: "conflicting_bj_clss T
    \<subseteq> simple_clss (atms_of_mm (clauses T) \<union> atm_of ` lits_of_l (trail T))"
      by standard (meson "1" "2" fin'  \<open>finite (conflicting_bj_clss T)\<close> simple_clss_mono
        distinct_mset_set_def  simplified_in_simple_clss subsetCE sup.coboundedI1)
  moreover
    then have #: "3 ^ card (atms_of_mm (clauses T) \<union> atm_of ` lits_of_l (trail T))
        \<ge> card (conflicting_bj_clss T)"
      by (meson Nat.le_trans simple_clss_card simple_clss_finite card_mono fin')
    have "atms_of_mm (clauses T) \<union> atm_of ` lits_of_l (trail T) \<subseteq> A"
      using learn\<^sub>N\<^sub>O\<^sub>TE[OF learnST] A by simp
    then have "3 ^ (card A) \<ge> card (conflicting_bj_clss T)"
      using # fin_A by (meson simple_clss_card simple_clss_finite
        simple_clss_mono calculation(2) card_mono dual_order.trans)
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
  @{term "atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A"}
  and in the clauses @{term "atms_of_mm (clauses S) \<subseteq> atms_of_ms A"}. This can the the set of all
  the literals in the starting set of clauses.
  \<^item> @{term "no_dup (trail S)"}: no duplicate in the trail. This is invariant along the path.\<close>
definition \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L where
"\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L A T \<equiv> ((2+card (atms_of_ms A)) ^ (1+card (atms_of_ms A))
               - \<mu>\<^sub>C (1+card (atms_of_ms A)) (2+card (atms_of_ms A)) (trail_weight T),
            conflicting_bj_clss_yet (card (atms_of_ms A)) T, card (set_mset (clauses T)))"
lemma cdcl\<^sub>N\<^sub>O\<^sub>T_decreasing_measure:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T S T"  and
    inv: "inv S" and
    atm_clss: "atms_of_mm (clauses S) \<subseteq> atms_of_ms A" and
    atm_lits: "atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A" and
    n_d: "no_dup (trail S)" and
    fin_A: "finite A"
  shows "(\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L A T, \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L A S)
            \<in> less_than <*lex*> (less_than <*lex*> less_than)"
  using assms(1)
proof induction
  case (c_dpll_bj T)
  from dpll_bj_trail_mes_decreasing_prop[OF this(1) inv atm_clss atm_lits n_d fin_A]
  show ?case unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L_def
    by (meson in_lex_prod less_than_iff)
next
  case (c_learn T) note learn = this(1)
  then have S: "trail S =  trail T"
    using inv atm_clss atm_lits n_d fin_A
    by (elim learn\<^sub>N\<^sub>O\<^sub>TE) auto
  show ?case
    using learn_\<mu>\<^sub>L_decrease[OF learn _ ] atm_clss atm_lits fin_A n_d unfolding S \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L_def by auto
next
  case (c_forget\<^sub>N\<^sub>O\<^sub>T T) note forget\<^sub>N\<^sub>O\<^sub>T = this(1)
  have "trail S = trail T" using forget\<^sub>N\<^sub>O\<^sub>T by induction auto
  then show ?case
    using forget_\<mu>\<^sub>L_decrease[OF forget\<^sub>N\<^sub>O\<^sub>T] unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L_def by auto
qed

lemma wf_cdcl\<^sub>N\<^sub>O\<^sub>T_restricted_learning:
  assumes "finite A"
  shows "wf {(T, S).
    (atms_of_mm (clauses S) \<subseteq> atms_of_ms A \<and> atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A
    \<and> no_dup (trail S)
    \<and> inv S)
    \<and> cdcl\<^sub>N\<^sub>O\<^sub>T S T }"
  by (rule wf_wf_if_measure'[of "less_than <*lex*> (less_than <*lex*> less_than)"])
     (auto intro: cdcl\<^sub>N\<^sub>O\<^sub>T_decreasing_measure[OF _ _ _ _ _ assms])

definition \<mu>\<^sub>C' :: "'v literal multiset set \<Rightarrow> 'st \<Rightarrow> nat" where
"\<mu>\<^sub>C' A T \<equiv> \<mu>\<^sub>C (1+card (atms_of_ms A)) (2+card (atms_of_ms A)) (trail_weight T)"

definition \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' :: "'v literal multiset set \<Rightarrow> 'st \<Rightarrow> nat" where
"\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' A T \<equiv>
  ((2+card (atms_of_ms A)) ^ (1+card (atms_of_ms A)) - \<mu>\<^sub>C' A T) * (1+ 3^card (atms_of_ms A)) * 2
  + conflicting_bj_clss_yet (card (atms_of_ms A)) T * 2
  + card (set_mset (clauses T))"

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_decreasing_measure':
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T S T" and
    inv: "inv S" and
    atms_clss: "atms_of_mm (clauses S) \<subseteq> atms_of_ms A" and
    atms_trail: "atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A" and
    n_d: "no_dup (trail S)" and
    fin_A: "finite A"
  shows "\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' A T < \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' A S"
  using assms(1)
proof (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_learn_all_induct)
  case (dpll_bj T)
  then have "(2+card (atms_of_ms A)) ^ (1+card (atms_of_ms A)) - \<mu>\<^sub>C' A T
    < (2+card (atms_of_ms A)) ^ (1+card (atms_of_ms A)) - \<mu>\<^sub>C' A S"
    using dpll_bj_trail_mes_decreasing_prop fin_A inv n_d atms_clss atms_trail
    unfolding \<mu>\<^sub>C'_def by blast
  then have XX: "((2+card (atms_of_ms A)) ^ (1+card (atms_of_ms A)) - \<mu>\<^sub>C' A T) + 1
    \<le> (2+card (atms_of_ms A)) ^ (1+card (atms_of_ms A)) - \<mu>\<^sub>C' A S"
    by auto
  from mult_le_mono1[OF this, of "(1 + 3 ^ card (atms_of_ms A))"]
  have "((2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A)) - \<mu>\<^sub>C' A T) *
      (1 + 3 ^ card (atms_of_ms A)) + (1 + 3 ^ card (atms_of_ms A))
    \<le> ((2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A)) - \<mu>\<^sub>C' A S)
      * (1 + 3 ^ card (atms_of_ms A))"
    unfolding Nat.add_mult_distrib
    by presburger
  moreover
    have cl_T_S:  "clauses T = clauses S"
      using dpll_bj.hyps inv dpll_bj_clauses by auto
    have "conflicting_bj_clss_yet (card (atms_of_ms A)) S < 1+ 3 ^ card (atms_of_ms A)"
    by simp
  ultimately have "((2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A)) - \<mu>\<^sub>C' A T)
      * (1 + 3 ^ card (atms_of_ms A)) + conflicting_bj_clss_yet (card (atms_of_ms A)) T
    < ((2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A)) - \<mu>\<^sub>C' A S) *(1 + 3 ^ card (atms_of_ms A))"
    by linarith
  then have "((2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A)) - \<mu>\<^sub>C' A T)
        * (1 + 3 ^ card (atms_of_ms A))
      + conflicting_bj_clss_yet (card (atms_of_ms A)) T
    < ((2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A)) - \<mu>\<^sub>C' A S)
        * (1 + 3 ^ card (atms_of_ms A))
      + conflicting_bj_clss_yet (card (atms_of_ms A)) S"
    by linarith
  then have "((2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A)) - \<mu>\<^sub>C' A T)
      * (1 + 3 ^ card (atms_of_ms A)) * 2
    + conflicting_bj_clss_yet (card (atms_of_ms A)) T * 2
    < ((2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A)) - \<mu>\<^sub>C' A S)
      * (1 + 3 ^ card (atms_of_ms A)) * 2
    + conflicting_bj_clss_yet (card (atms_of_ms A)) S * 2"
    by linarith
  then show ?case unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_def cl_T_S by presburger
next
  case (learn C F' K F C' L T) note clss_S_C = this(1) and atms_C = this(2) and dist = this(3)
    and tauto = this(4) and learn_restr = this(5) and tr_S = this(6) and C' = this(7) and
    F_C = this(8) and C_new = this(9) and T =this(10)
  have "insert C (conflicting_bj_clss S) \<subseteq> simple_clss (atms_of_ms A)"
    proof -
      have "C \<in> simple_clss (atms_of_ms A)"
        by (metis (no_types, hide_lams) Un_subset_iff atms_of_ms_finite simple_clss_mono
          contra_subsetD dist distinct_mset_not_tautology_implies_in_simple_clss
          dual_order.trans fin_A atms_C atms_clss atms_trail tauto)
      moreover have "conflicting_bj_clss S \<subseteq> simple_clss (atms_of_ms A)"
        unfolding conflicting_bj_clss_def
        proof
          fix x :: "'v literal multiset"
          assume "x \<in> {C + {#L#} |C L. C + {#L#} \<in># clauses S
            \<and> distinct_mset (C + {#L#}) \<and> \<not> tautology (C + {#L#})
            \<and> (\<exists>F' K F. trail S = F' @ Marked K () # F \<and> F \<Turnstile>as CNot C)}"
          then have "\<exists>m l. x = m + {#l#} \<and> m + {#l#} \<in># clauses S
            \<and> distinct_mset (m + {#l#}) \<and> \<not> tautology (m + {#l#})
            \<and> (\<exists>ms l msa. trail S = ms @ Marked l () # msa \<and> msa \<Turnstile>as CNot m)"
            by blast
          then show "x \<in> simple_clss (atms_of_ms A)"
            by (meson atms_clss atms_of_m_atms_of_ms_mono atms_of_ms_finite simple_clss_mono
              distinct_mset_not_tautology_implies_in_simple_clss fin_A finite_subset
              set_rev_mp)
        qed
      ultimately show ?thesis
        by auto
    qed
  then have "card (insert C (conflicting_bj_clss S)) \<le> 3 ^ (card (atms_of_ms A))"
    by (meson Nat.le_trans atms_of_ms_finite simple_clss_card simple_clss_finite
      card_mono fin_A)
  moreover have [simp]: "card (insert C (conflicting_bj_clss S))
    = Suc (card ((conflicting_bj_clss S)))"
    by (metis (no_types) C' C_new card_insert_if conflicting_bj_clss_incl_clauses contra_subsetD
      finite_conflicting_bj_clss)
  moreover have [simp]: "conflicting_bj_clss (add_cls\<^sub>N\<^sub>O\<^sub>T C S) = conflicting_bj_clss S \<union> {C}"
     using dist tauto F_C n_d by (subst conflicting_bj_clss_add_cls\<^sub>N\<^sub>O\<^sub>T)
     (force simp add: ac_simps C' tr_S)+
  ultimately have [simp]: "conflicting_bj_clss_yet (card (atms_of_ms A)) S
    = Suc (conflicting_bj_clss_yet (card (atms_of_ms A)) (add_cls\<^sub>N\<^sub>O\<^sub>T C S))"
      by simp
  have 1: "clauses T = clauses (add_cls\<^sub>N\<^sub>O\<^sub>T C S)" using T by auto
  have 2: "conflicting_bj_clss_yet (card (atms_of_ms A)) T
    = conflicting_bj_clss_yet (card (atms_of_ms A)) (add_cls\<^sub>N\<^sub>O\<^sub>T C S)"
    using T unfolding conflicting_bj_clss_def by auto
  have 3: "\<mu>\<^sub>C' A T = \<mu>\<^sub>C' A (add_cls\<^sub>N\<^sub>O\<^sub>T C S)"
    using T unfolding \<mu>\<^sub>C'_def by auto
  have "((2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A)) - \<mu>\<^sub>C' A (add_cls\<^sub>N\<^sub>O\<^sub>T C S))
    * (1 + 3 ^ card (atms_of_ms A)) * 2
    = ((2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A)) - \<mu>\<^sub>C' A S)
    * (1 + 3 ^ card (atms_of_ms A)) * 2"
      using n_d unfolding \<mu>\<^sub>C'_def by auto
  moreover
    have "conflicting_bj_clss_yet (card (atms_of_ms A)) (add_cls\<^sub>N\<^sub>O\<^sub>T C S)
        * 2
      + card (set_mset (clauses (add_cls\<^sub>N\<^sub>O\<^sub>T C S)))
      < conflicting_bj_clss_yet (card (atms_of_ms A)) S * 2
      + card (set_mset (clauses S))"
      by (simp add: C' C_new n_d)
  ultimately show ?case unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_def 1 2 3 by presburger
next
  case (forget\<^sub>N\<^sub>O\<^sub>T C T) note T = this(4)
  have [simp]: "\<mu>\<^sub>C' A (remove_cls\<^sub>N\<^sub>O\<^sub>T C S) =  \<mu>\<^sub>C' A S"
    unfolding \<mu>\<^sub>C'_def by auto
  have "forget\<^sub>N\<^sub>O\<^sub>T S T"
    apply (rule forget\<^sub>N\<^sub>O\<^sub>T.intros) using forget\<^sub>N\<^sub>O\<^sub>T by auto
  then have "conflicting_bj_clss T = conflicting_bj_clss S"
    using do_not_forget_before_backtrack_rule_clause_learned_clause_untouched by blast
  moreover have "card (set_mset (clauses T)) < card (set_mset (clauses S))"
    by (metis T card_Diff1_less clauses_remove_cls\<^sub>N\<^sub>O\<^sub>T finite_set_mset forget\<^sub>N\<^sub>O\<^sub>T.hyps(2)
      order_refl set_mset_minus_replicate_mset(1) state_eq\<^sub>N\<^sub>O\<^sub>T_clauses)
  ultimately show ?case unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_def
    by (metis (no_types) T \<open>\<mu>\<^sub>C' A (remove_cls\<^sub>N\<^sub>O\<^sub>T C S) = \<mu>\<^sub>C' A S\<close> add_le_cancel_left
      \<mu>\<^sub>C'_def not_le state_eq\<^sub>N\<^sub>O\<^sub>T_trail)
qed

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_clauses_bound:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T S T" and
    "inv S" and
    "atms_of_mm (clauses S) \<subseteq> A" and
    "atm_of `(lits_of_l (trail S)) \<subseteq> A" and
    n_d: "no_dup (trail S)" and
    fin_A[simp]: "finite A"
  shows "set_mset (clauses T) \<subseteq> set_mset (clauses S) \<union> simple_clss A"
  using assms
proof (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_learn_all_induct)
  case dpll_bj
  then show ?case using dpll_bj_clauses by simp
next
  case forget\<^sub>N\<^sub>O\<^sub>T
  then show ?case using clauses_remove_cls\<^sub>N\<^sub>O\<^sub>T unfolding state_eq\<^sub>N\<^sub>O\<^sub>T_def by auto
next
  case (learn C F K d F' C' L) note atms_C = this(2) and dist = this(3) and tauto = this(4) and
  T = this(10) and atms_clss_S = this(12) and atms_trail_S = this(13)
  have "atms_of C \<subseteq> A"
    using atms_C atms_clss_S atms_trail_S by auto
  then have "simple_clss (atms_of C) \<subseteq> simple_clss A"
    by (simp add: simple_clss_mono)
  then have "C \<in> simple_clss A"
    using finite dist tauto
    by (auto dest: distinct_mset_not_tautology_implies_in_simple_clss)
  then show ?case using T n_d by auto
qed

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_clauses_bound:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T" and
    "inv S" and
    "atms_of_mm (clauses S) \<subseteq> A" and
    "atm_of `(lits_of_l (trail S)) \<subseteq> A" and
    n_d: "no_dup (trail S)" and
    finite: "finite A"
  shows "set_mset (clauses T) \<subseteq> set_mset (clauses S) \<union> simple_clss A"
  using assms(1-5)
proof induction
  case base
  then show ?case by simp
next
  case (step T U) note st = this(1) and cdcl\<^sub>N\<^sub>O\<^sub>T = this(2) and IH = this(3)[OF this(4-7)] and
    inv = this(4) and atms_clss_S = this(5) and atms_trail_S = this(6) and finite_cls_S = this(7)
  have "inv T"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_inv st inv by blast
  moreover have "atms_of_mm (clauses T) \<subseteq> A" and "atm_of ` lits_of_l (trail T) \<subseteq> A"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_trail_clauses_bound[OF st] inv atms_clss_S atms_trail_S n_d by blast+
  moreover have "no_dup (trail T)"
   using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup[OF st \<open>inv S\<close> n_d] by simp
  ultimately have "set_mset (clauses U) \<subseteq> set_mset (clauses T) \<union> simple_clss A"
    using cdcl\<^sub>N\<^sub>O\<^sub>T finite n_d by (auto simp: cdcl\<^sub>N\<^sub>O\<^sub>T_clauses_bound)
  then show ?case using IH by auto
qed


lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_card_clauses_bound:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T" and
    "inv S" and
    "atms_of_mm (clauses S) \<subseteq> A" and
    "atm_of `(lits_of_l (trail S)) \<subseteq> A" and
    n_d: "no_dup (trail S)" and
    finite: "finite A"
  shows "card (set_mset (clauses T)) \<le> card (set_mset (clauses S)) + 3 ^ (card A)"
  using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_clauses_bound[OF assms] finite by (meson Nat.le_trans
    simple_clss_card simple_clss_finite card_Un_le card_mono finite_UnI
    finite_set_mset nat_add_left_cancel_le)

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_card_clauses_bound':
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T" and
    "inv S" and
    "atms_of_mm (clauses S) \<subseteq> A" and
    "atm_of `(lits_of_l (trail S)) \<subseteq> A" and
    n_d: "no_dup (trail S)" and
    finite: "finite A"
  shows "card {C|C. C \<in># clauses T \<and> (tautology C \<or> \<not>distinct_mset C)}
    \<le> card {C|C. C\<in># clauses S \<and> (tautology C \<or> \<not>distinct_mset C)} + 3 ^ (card A)"
    (is "card ?T \<le> card ?S + _")
  using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_clauses_bound[OF assms] finite
proof -
  have "?T \<subseteq> ?S \<union> simple_clss A"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_clauses_bound[OF assms] by force
  then have "card ?T \<le> card (?S \<union> simple_clss A)"
    using finite by (simp add: assms(5) simple_clss_finite card_mono)
  then show ?thesis
    by (meson le_trans simple_clss_card card_Un_le local.finite nat_add_left_cancel_le)
qed

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_card_simple_clauses_bound:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T" and
    "inv S" and
    "atms_of_mm (clauses S) \<subseteq> A" and
    "atm_of `(lits_of_l (trail S)) \<subseteq> A" and
    n_d: "no_dup (trail S)" and
    finite: "finite A"
  shows "card (set_mset (clauses T))
  \<le> card {C. C \<in># clauses S \<and> (tautology C \<or> \<not>distinct_mset C)} + 3 ^ (card A)"
    (is "card ?T \<le> card ?S + _")
  using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_clauses_bound[OF assms] finite
proof -
  have "\<And>x. x \<in># clauses T \<Longrightarrow>\<not> tautology x \<Longrightarrow> distinct_mset x \<Longrightarrow> x \<in> simple_clss A"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_clauses_bound[OF assms] by (metis (no_types, hide_lams) Un_iff assms(3)
<<<<<<< HEAD
      atms_of_m_atms_of_ms_mono simple_clss_mono contra_subsetD
      distinct_mset_not_tautology_implies_in_simple_clss local.finite mem_set_mset_iff
      subset_trans)
=======
      atms_of_atms_of_ms_mono simple_clss_mono contra_subsetD
      distinct_mset_not_tautology_implies_in_simple_clss subset_trans)
>>>>>>> origin/master
  then have "set_mset (clauses T) \<subseteq> ?S \<union> simple_clss A"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_clauses_bound[OF assms] by auto
  then have "card(set_mset (clauses T)) \<le> card (?S \<union> simple_clss A)"
    using finite by (simp add: assms(5) simple_clss_finite card_mono)
  then show ?thesis
    by (meson le_trans simple_clss_card card_Un_le local.finite nat_add_left_cancel_le)
qed

definition \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound :: "'v literal multiset set \<Rightarrow> 'st \<Rightarrow> nat" where
"\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A S =
  ((2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A))) * (1 + 3 ^ card (atms_of_ms A)) * 2
     + 2*3 ^ (card (atms_of_ms A))
     + card {C. C \<in># clauses S \<and> (tautology C \<or> \<not>distinct_mset C)} + 3 ^ (card (atms_of_ms A))"

lemma \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T[simp]:
  "\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T M S) = \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A S"
  unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_def by auto

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T" and
    "inv S" and
    "atms_of_mm (clauses S) \<subseteq> atms_of_ms A" and
    "atm_of `(lits_of_l (trail S)) \<subseteq> atms_of_ms A" and
    n_d: "no_dup (trail S)" and
    finite: "finite (atms_of_ms A)" and
    U: "U \<sim> reduce_trail_to\<^sub>N\<^sub>O\<^sub>T M T"
  shows "\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' A U \<le> \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A S"
proof -
  have " ((2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A)) - \<mu>\<^sub>C' A U)
    \<le> (2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A))"
    by auto
  then have "((2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A)) - \<mu>\<^sub>C' A U)
        * (1 + 3 ^ card (atms_of_ms A)) * 2
    \<le> (2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A)) * (1 + 3 ^ card (atms_of_ms A)) * 2"
    using mult_le_mono1 by blast
  moreover
    have "conflicting_bj_clss_yet (card (atms_of_ms A)) T * 2 \<le> 2 * 3 ^ card (atms_of_ms A)"
      by linarith
  moreover have "card (set_mset (clauses U))
      \<le> card {C. C \<in># clauses S \<and> (tautology C \<or> \<not>distinct_mset C)} + 3 ^ card (atms_of_ms A)"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_card_simple_clauses_bound[OF assms(1-6)] U by auto
  ultimately show ?thesis
    unfolding  \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_def \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_def by linarith
qed

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T" and
    "inv S" and
    "atms_of_mm (clauses S) \<subseteq> atms_of_ms A" and
    "atm_of `(lits_of_l (trail S)) \<subseteq> atms_of_ms A" and
    n_d: "no_dup (trail S)" and
    finite: "finite (atms_of_ms A)"
  shows "\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' A T \<le> \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A S"
proof -
  have "\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' A (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T (trail T) T) = \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' A T"
    unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_def  \<mu>\<^sub>C'_def conflicting_bj_clss_def by auto
  then show ?thesis using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T[OF assms, of _ "trail T"]
    state_eq\<^sub>N\<^sub>O\<^sub>T_ref by fastforce
qed

lemma rtranclp_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_decreasing:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T" and
    "inv S" and
    "atms_of_mm (clauses S) \<subseteq> atms_of_ms A" and
    "atm_of `(lits_of_l (trail S)) \<subseteq> atms_of_ms A" and
    n_d: "no_dup (trail S)" and
    finite[simp]: "finite (atms_of_ms A)"
  shows "\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A T \<le> \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A S"
proof -
  have "{C. C \<in># clauses T \<and> (tautology C \<or> \<not> distinct_mset C)}
    \<subseteq> {C. C \<in># clauses S \<and> (tautology C \<or> \<not> distinct_mset C)}" (is "?T \<subseteq> ?S")
    proof (rule Set.subsetI)
      fix C assume "C \<in> ?T"
      then have C_T: "C \<in># clauses T" and t_d: "tautology C \<or> \<not> distinct_mset C"
        by auto
      then have "C \<notin> simple_clss (atms_of_ms A)"
        by (auto dest: simple_clssE)
      then show "C \<in> ?S"
        using C_T rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_clauses_bound[OF assms] t_d by force
    qed
  then have "card {C. C \<in># clauses T \<and> (tautology C \<or> \<not> distinct_mset C)} \<le>
    card {C. C \<in># clauses S \<and> (tautology C \<or> \<not> distinct_mset C)}"
    by (simp add: card_mono)
  then show ?thesis
    unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_def by auto
qed

end \<comment> \<open>end of \<open>conflict_driven_clause_learning_learning_before_backjump_only_distinct_learnt\<close>\<close>


subsection \<open>CDCL with restarts\<close>
subsubsection\<open>Definition\<close>
locale restart_ops =
  fixes
    cdcl\<^sub>N\<^sub>O\<^sub>T :: "'st \<Rightarrow> 'st \<Rightarrow> bool" and
    restart :: "'st \<Rightarrow> 'st \<Rightarrow> bool"
begin
inductive cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart  :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
"cdcl\<^sub>N\<^sub>O\<^sub>T S T \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart S T" |
"restart S T \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart S T"

end

locale conflict_driven_clause_learning_with_restarts =
  conflict_driven_clause_learning trail clauses prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T
  propagate_conds inv backjump_conds learn_cond forget_cond
    for
      trail :: "'st \<Rightarrow> ('v, unit, unit) marked_lits" and
      clauses :: "'st \<Rightarrow> 'v clauses" and
      prepend_trail :: "('v, unit, unit) marked_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
      tl_trail :: "'st \<Rightarrow> 'st" and
      add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T:: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
      propagate_conds :: "('v, unit, unit) marked_lit \<Rightarrow> 'st \<Rightarrow> bool" and
      inv :: "'st \<Rightarrow> bool" and
      backjump_conds ::  "'v clause \<Rightarrow> 'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool" and
      learn_cond forget_cond :: "'v clause \<Rightarrow> 'st \<Rightarrow> bool"
begin

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_iff_cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart_no_restarts:
  "cdcl\<^sub>N\<^sub>O\<^sub>T S T \<longleftrightarrow> restart_ops.cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart cdcl\<^sub>N\<^sub>O\<^sub>T (\<lambda>_ _. False) S T"
  (is "?C S T \<longleftrightarrow> ?R S T")
proof
  fix S T
  assume "?C S T"
  then show "?R S T" by (simp add: restart_ops.cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart.intros(1))
next
  fix S T
  assume "?R S T"
  then show "?C S T"
    apply (cases rule: restart_ops.cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart.cases)
    using \<open>?R S T\<close> by fast+
qed

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart:
  "cdcl\<^sub>N\<^sub>O\<^sub>T S T \<Longrightarrow> restart_ops.cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart cdcl\<^sub>N\<^sub>O\<^sub>T restart S T"
  by (simp add: restart_ops.cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart.intros(1))
end

subsubsection \<open>Increasing restarts\<close>
text \<open>To add restarts we needs some assumptions on the predicate (called @{term cdcl\<^sub>N\<^sub>O\<^sub>T} here):
  \<^item> a function @{term f} that is strictly monotonic. The first step is actually only used as a
  restart  to clean the state (e.g. to ensure that the trail is empty). Then we assume that
  @{term "f n \<ge> 1"} for @{term "n \<ge> 1"}: it means that between two consecutive
  restarts, at least one step will be done. This is necessary to avoid sequence. like:  full --
  restart --  full -- ...
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
    f: "unbounded f" and
    f_ge_1:"\<And>n. n\<ge>1 \<Longrightarrow> f n \<noteq> 0" and
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
  then show ?case using cdcl\<^sub>N\<^sub>O\<^sub>T_measure by auto
next
  case (Suc n) note IH =this(1)[OF _ this(3) this(4)] and S_T =this(2) and b_inv = this(3) and
  c_inv = this(4)
  obtain U :: 'st where S_U: "(cdcl\<^sub>N\<^sub>O\<^sub>T^^(Suc n)) S U" and U_T: "cdcl\<^sub>N\<^sub>O\<^sub>T U T" using S_T by auto
  then have "\<mu> A U < \<mu> A S - n" using IH[of U] by simp
  moreover
    have "bound_inv A U"
      using S_U b_inv  cdcl\<^sub>N\<^sub>O\<^sub>T_bound_inv c_inv by blast
    then have "\<mu> A T < \<mu> A U" using cdcl\<^sub>N\<^sub>O\<^sub>T_measure[OF _ _ U_T] S_U c_inv cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_inv by auto
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
  then show ?case by auto
next
  case (step T U) note IH =this(3)[OF this(4) this(5)] and st =this(1) and cdcl\<^sub>N\<^sub>O\<^sub>T= this(2) and
    b_inv = this(4) and c_inv = this(5)
  have "bound_inv A T"
    by (meson cdcl\<^sub>N\<^sub>O\<^sub>T_bound_inv rtranclp_imp_relpowp st step.prems)
  moreover have "cdcl\<^sub>N\<^sub>O\<^sub>T_inv T"
    using c_inv rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_inv st by blast
  ultimately have "\<mu> A U < \<mu> A T" using cdcl\<^sub>N\<^sub>O\<^sub>T_measure[OF _ _ cdcl\<^sub>N\<^sub>O\<^sub>T] by auto
  then show ?case using IH by linarith
qed

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_comp_bounded:
  assumes
    "bound_inv A S" and "cdcl\<^sub>N\<^sub>O\<^sub>T_inv S" and "m \<ge> 1+\<mu> A S"
  shows "\<not>(cdcl\<^sub>N\<^sub>O\<^sub>T ^^ m) S T"
  using assms cdcl\<^sub>N\<^sub>O\<^sub>T_comp_n_le[of "m-1" S T A] by fastforce

text \<open>
  \<^item> @{term "m > f n"} ensures that at least one step has been done.\<close>
inductive cdcl\<^sub>N\<^sub>O\<^sub>T_restart where
restart_step: "(cdcl\<^sub>N\<^sub>O\<^sub>T^^m) S T \<Longrightarrow> m \<ge> f n \<Longrightarrow> restart T U
  \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_restart (S, n) (U, Suc n)" |
restart_full: "full1 cdcl\<^sub>N\<^sub>O\<^sub>T S T \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_restart (S, n) (T, Suc n)"

lemmas cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_induct = cdcl\<^sub>N\<^sub>O\<^sub>T_restart.induct[split_format(complete),
  OF cdcl\<^sub>N\<^sub>O\<^sub>T_increasing_restarts_ops_axioms]

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart:
  "cdcl\<^sub>N\<^sub>O\<^sub>T_restart S T \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart\<^sup>*\<^sup>* (fst S) (fst T)"
proof (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_restart.induct)
  case (restart_step m S T n U)
  then have "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T" by (meson relpowp_imp_rtranclp)
  then have "cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart\<^sup>*\<^sup>* S T" using cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart.intros(1)
    rtranclp_mono[of cdcl\<^sub>N\<^sub>O\<^sub>T cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart] by blast
  moreover have "cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart T U"
    using \<open>restart T U\<close> cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart.intros(2) by blast
  ultimately show ?case by auto
next
  case (restart_full S T)
  then have "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T" unfolding full1_def by auto
  then show ?case using cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart.intros(1)
    rtranclp_mono[of cdcl\<^sub>N\<^sub>O\<^sub>T cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart] by auto
qed

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_bound_inv:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T_restart S T" and
    "bound_inv A (fst S)" and
    "cdcl\<^sub>N\<^sub>O\<^sub>T_inv (fst S)"
  shows "bound_inv A (fst T)"
  using assms apply (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_restart.induct)
    prefer 2 apply (metis rtranclp_unfold fstI full1_def rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_bound_inv)
  by (metis cdcl\<^sub>N\<^sub>O\<^sub>T_bound_inv cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_inv cdcl\<^sub>N\<^sub>O\<^sub>T_restart_inv fst_conv)

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_inv:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T_restart S T" and
    "cdcl\<^sub>N\<^sub>O\<^sub>T_inv (fst S)"
  shows "cdcl\<^sub>N\<^sub>O\<^sub>T_inv (fst  T)"
  using assms apply induction
    apply (metis cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_inv cdcl\<^sub>N\<^sub>O\<^sub>T_inv_restart fst_conv)
   apply (metis fstI full_def full_unfold rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_inv)
  done

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_inv:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T_restart\<^sup>*\<^sup>* S T" and
    "cdcl\<^sub>N\<^sub>O\<^sub>T_inv (fst S)"
  shows "cdcl\<^sub>N\<^sub>O\<^sub>T_inv (fst T)"
  using assms by induction (auto intro: cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_inv)

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_bound_inv:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T_restart\<^sup>*\<^sup>* S T" and
    "cdcl\<^sub>N\<^sub>O\<^sub>T_inv (fst S)" and
    "bound_inv A (fst S)"
  shows "bound_inv A (fst T)"
  using assms apply induction
   apply (simp add: cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_inv cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_bound_inv)
  using cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_bound_inv rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_inv by blast

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_increasing_number:
  "cdcl\<^sub>N\<^sub>O\<^sub>T_restart S T \<Longrightarrow> snd T = 1 + snd S"
  by (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_restart.induct) auto
end

locale cdcl\<^sub>N\<^sub>O\<^sub>T_increasing_restarts =
  cdcl\<^sub>N\<^sub>O\<^sub>T_increasing_restarts_ops restart cdcl\<^sub>N\<^sub>O\<^sub>T f bound_inv \<mu> cdcl\<^sub>N\<^sub>O\<^sub>T_inv \<mu>_bound
  for
    trail :: "'st \<Rightarrow> ('v, unit, unit) marked_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    prepend_trail :: "('v, unit, unit) marked_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T:: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    f :: "nat \<Rightarrow> nat" and
    restart :: "'st \<Rightarrow> 'st \<Rightarrow> bool" and
    bound_inv :: "'bound \<Rightarrow> 'st \<Rightarrow> bool" and
    \<mu> :: "'bound \<Rightarrow> 'st \<Rightarrow> nat" and
    cdcl\<^sub>N\<^sub>O\<^sub>T :: "'st \<Rightarrow> 'st \<Rightarrow> bool" and
    cdcl\<^sub>N\<^sub>O\<^sub>T_inv :: "'st \<Rightarrow> bool" and
    \<mu>_bound :: "'bound \<Rightarrow> 'st \<Rightarrow> nat" +
  assumes
    measure_bound: "\<And>A T V n. cdcl\<^sub>N\<^sub>O\<^sub>T_inv T \<Longrightarrow> bound_inv A T
      \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_restart (T, n) (V, Suc n) \<Longrightarrow> \<mu> A V \<le> \<mu>_bound A T" and
    cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart_\<mu>_bound:
      "cdcl\<^sub>N\<^sub>O\<^sub>T_restart (T, a) (V, b) \<Longrightarrow>  cdcl\<^sub>N\<^sub>O\<^sub>T_inv T \<Longrightarrow> bound_inv A T
        \<Longrightarrow> \<mu>_bound A V \<le> \<mu>_bound A T"
begin

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart_\<mu>_bound:
  "cdcl\<^sub>N\<^sub>O\<^sub>T_restart\<^sup>*\<^sup>* (T, a) (V, b) \<Longrightarrow>  cdcl\<^sub>N\<^sub>O\<^sub>T_inv T \<Longrightarrow> bound_inv A T
    \<Longrightarrow> \<mu>_bound A V \<le> \<mu>_bound A T"
  apply (induction rule: rtranclp_induct2)
   apply simp
  by (metis cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart_\<mu>_bound dual_order.trans fst_conv
    rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_bound_inv rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_inv)

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart_measure_bound:
  "cdcl\<^sub>N\<^sub>O\<^sub>T_restart (T, a) (V, b) \<Longrightarrow>  cdcl\<^sub>N\<^sub>O\<^sub>T_inv T \<Longrightarrow> bound_inv A T
    \<Longrightarrow> \<mu> A V \<le> \<mu>_bound A T"
  apply (cases rule: cdcl\<^sub>N\<^sub>O\<^sub>T_restart.cases)
     apply simp
    using measure_bound relpowp_imp_rtranclp apply fastforce
   by (metis full_def full_unfold measure_bound2 prod.inject)

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart_measure_bound:
  "cdcl\<^sub>N\<^sub>O\<^sub>T_restart\<^sup>*\<^sup>* (T, a) (V, b) \<Longrightarrow>  cdcl\<^sub>N\<^sub>O\<^sub>T_inv T \<Longrightarrow> bound_inv A T
    \<Longrightarrow> \<mu> A V \<le> \<mu>_bound A T"
  apply (induction rule: rtranclp_induct2)
    apply (simp add: measure_bound2)
  by (metis dual_order.trans fst_conv measure_bound2 r_into_rtranclp rtranclp.rtrancl_refl
    rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_bound_inv rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_inv
    rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart_\<mu>_bound)

lemma wf_cdcl\<^sub>N\<^sub>O\<^sub>T_restart:
  "wf {(T, S). cdcl\<^sub>N\<^sub>O\<^sub>T_restart S T \<and> cdcl\<^sub>N\<^sub>O\<^sub>T_inv (fst S)}" (is "wf ?A")
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain g where
    g: "\<And>i. cdcl\<^sub>N\<^sub>O\<^sub>T_restart (g i) (g (Suc i))" and
    cdcl\<^sub>N\<^sub>O\<^sub>T_inv_g: "\<And>i. cdcl\<^sub>N\<^sub>O\<^sub>T_inv (fst (g i))"
    unfolding wf_iff_no_infinite_down_chain by fast

  have snd_g: "\<And>i. snd (g i) = i + snd (g 0)"
    apply (induct_tac i)
      apply simp
      by (metis Suc_eq_plus1_left add.commute add.left_commute
        cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_increasing_number g)
  then have snd_g_0: "\<And>i. i > 0 \<Longrightarrow> snd (g i) = i + snd (g 0)"
    by blast
  have unbounded_f_g: "unbounded (\<lambda>i. f (snd (g i)))"
    using f unfolding bounded_def by (metis add.commute f less_or_eq_imp_le snd_g
      not_bounded_nat_exists_larger not_le le_iff_add)

  { fix i
    have H: "\<And>T Ta m. (cdcl\<^sub>N\<^sub>O\<^sub>T ^^ m) T Ta \<Longrightarrow> no_step cdcl\<^sub>N\<^sub>O\<^sub>T T \<Longrightarrow> m = 0"
      apply (case_tac m) by simp (meson relpowp_E2)
    have "\<exists> T m. (cdcl\<^sub>N\<^sub>O\<^sub>T ^^ m) (fst (g i)) T \<and> m \<ge> f (snd (g i))"
      using g[of i] apply (cases rule: cdcl\<^sub>N\<^sub>O\<^sub>T_restart.cases)
        apply auto[]
      using g[of "Suc i"] f_ge_1 apply (cases rule: cdcl\<^sub>N\<^sub>O\<^sub>T_restart.cases)
      apply (auto simp add: full1_def full_def dest: H dest: tranclpD)
      using H Suc_leI leD by blast
  } note H = this
  obtain A where "bound_inv A (fst (g 1))"
    using g[of 0] cdcl\<^sub>N\<^sub>O\<^sub>T_inv_g[of 0] apply (cases rule: cdcl\<^sub>N\<^sub>O\<^sub>T_restart.cases)
      apply (metis One_nat_def cdcl\<^sub>N\<^sub>O\<^sub>T_inv exists_bound fst_conv relpowp_imp_rtranclp
        rtranclp_induct)
      using H[of 1] unfolding full1_def by (metis One_nat_def Suc_eq_plus1 diff_is_0_eq' diff_zero
        f_ge_1 fst_conv le_add2 relpowp_E2 snd_conv)
  let ?j = "\<mu>_bound A (fst (g 1)) + 1"
  obtain j where
    j: "f (snd (g j)) > ?j" and "j > 1"
    using unbounded_f_g not_bounded_nat_exists_larger by blast
  {
     fix i j
     have cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart: "j \<ge> i \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_restart\<^sup>*\<^sup>* (g i) (g j)"
       apply (induction j)
         apply simp
       by (metis g le_Suc_eq rtranclp.rtrancl_into_rtrancl rtranclp.rtrancl_refl)
  } note cdcl\<^sub>N\<^sub>O\<^sub>T_restart = this
  have "cdcl\<^sub>N\<^sub>O\<^sub>T_inv (fst (g (Suc 0)))"
    by (simp add: cdcl\<^sub>N\<^sub>O\<^sub>T_inv_g)
  have "cdcl\<^sub>N\<^sub>O\<^sub>T_restart\<^sup>*\<^sup>* (fst (g 1), snd (g 1)) (fst (g j), snd (g j))"
    using \<open>j> 1\<close> by (simp add: cdcl\<^sub>N\<^sub>O\<^sub>T_restart)
  have "\<mu> A (fst (g j)) \<le> \<mu>_bound A (fst (g 1))"
    apply (rule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart_measure_bound)
    using \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_restart\<^sup>*\<^sup>* (fst (g 1), snd (g 1)) (fst (g j), snd (g j))\<close> apply blast
        apply (simp add: cdcl\<^sub>N\<^sub>O\<^sub>T_inv_g)
       using \<open>bound_inv A (fst (g 1))\<close> apply simp
    done
  then have "\<mu> A (fst (g j)) \<le> ?j"
    by auto
  have inv: "bound_inv A (fst (g j))"
    using \<open>bound_inv A (fst (g 1))\<close> \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_inv (fst (g (Suc 0)))\<close>
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_restart\<^sup>*\<^sup>* (fst (g 1), snd (g 1)) (fst (g j), snd (g j))\<close>
    rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_bound_inv by auto
  obtain T m where
    cdcl\<^sub>N\<^sub>O\<^sub>T_m: "(cdcl\<^sub>N\<^sub>O\<^sub>T ^^ m) (fst (g j)) T" and
    f_m: "f (snd (g j)) \<le> m"
    using H[of "j"] by blast
  have "?j < m"
    using f_m j Nat.le_trans by linarith

  then show False
    using \<open>\<mu> A (fst (g j)) \<le> \<mu>_bound A (fst (g 1))\<close>
    cdcl\<^sub>N\<^sub>O\<^sub>T_comp_bounded[OF inv cdcl\<^sub>N\<^sub>O\<^sub>T_inv_g, of ] cdcl\<^sub>N\<^sub>O\<^sub>T_inv_g cdcl\<^sub>N\<^sub>O\<^sub>T_m
    \<open>?j < m\<close> by auto
qed

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_restart_steps_bigger_than_bound:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T_restart S T" and
    "bound_inv A (fst S)" and
    "cdcl\<^sub>N\<^sub>O\<^sub>T_inv (fst S)" and
    "f (snd S) > \<mu>_bound A (fst S)"
  shows "full1 cdcl\<^sub>N\<^sub>O\<^sub>T (fst S) (fst T)"
  using assms
proof (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_restart.induct)
  case restart_full
  then show ?case by auto
next
  case (restart_step m S T n U) note st = this(1) and f = this(2) and bound_inv = this(4) and
    cdcl\<^sub>N\<^sub>O\<^sub>T_inv =this(5) and \<mu> = this(6)
  then obtain m' where m: "m = Suc m'" by (cases m) auto
  have "\<mu> A S - m' = 0"
    using f bound_inv cdcl\<^sub>N\<^sub>O\<^sub>T_inv \<mu> m rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart_measure_bound by fastforce
  then have False using cdcl\<^sub>N\<^sub>O\<^sub>T_comp_n_le[of m' S T A] restart_step unfolding m by simp
  then show ?case by fast
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

lemma no_step_cdcl\<^sub>N\<^sub>O\<^sub>T_restart_no_step_cdcl\<^sub>N\<^sub>O\<^sub>T:
  assumes
    n_s: "no_step cdcl\<^sub>N\<^sub>O\<^sub>T_restart S" and
    inv: "cdcl\<^sub>N\<^sub>O\<^sub>T_inv (fst S)" and
    binv: "bound_inv A (fst S)"
  shows "no_step cdcl\<^sub>N\<^sub>O\<^sub>T (fst S)"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain T where T: "cdcl\<^sub>N\<^sub>O\<^sub>T (fst S) T"
    by blast
  then obtain U where U: "full (\<lambda>S T. cdcl\<^sub>N\<^sub>O\<^sub>T S T \<and> cdcl\<^sub>N\<^sub>O\<^sub>T_inv S \<and> bound_inv A S) T U"
     using wf_exists_normal_form_full[OF wf_cdcl\<^sub>N\<^sub>O\<^sub>T, of A T] by auto
  moreover have inv_T: "cdcl\<^sub>N\<^sub>O\<^sub>T_inv T"
    using \<open>cdcl\<^sub>N\<^sub>O\<^sub>T (fst S) T\<close> cdcl\<^sub>N\<^sub>O\<^sub>T_inv inv by blast
  moreover have b_inv_T: "bound_inv A T"
    using \<open>cdcl\<^sub>N\<^sub>O\<^sub>T (fst S) T\<close> binv bound_inv inv by blast
  ultimately have "full cdcl\<^sub>N\<^sub>O\<^sub>T T U"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_inv_inv_rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_bound_inv
    rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_inv unfolding full_def by blast
  then have "full1 cdcl\<^sub>N\<^sub>O\<^sub>T (fst S) U"
    using T full_fullI by metis
  then show False by (metis n_s prod.collapse restart_full)
qed

end

subsection \<open>Merging backjump and learning\<close>
locale cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_ops =
  dpll_state trail clauses prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T +
  decide_ops trail clauses prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T +
  forget_ops trail clauses prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T forget_cond +
  propagate_ops trail clauses prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T propagate_conds
  for
    trail :: "'st \<Rightarrow> ('v, unit, unit) marked_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    prepend_trail :: "('v, unit, unit) marked_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T:: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    propagate_conds :: "('v, unit, unit) marked_lit \<Rightarrow> 'st \<Rightarrow> bool" and
    forget_cond :: "'v clause \<Rightarrow> 'st \<Rightarrow> bool" +
  fixes backjump_l_cond :: "'v clause \<Rightarrow> 'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> bool"
begin
inductive backjump_l where
backjump_l: "trail S = F' @ Marked K () # F
   \<Longrightarrow> no_dup (trail S)
   \<Longrightarrow> T \<sim> prepend_trail (Propagated L ()) (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F (add_cls\<^sub>N\<^sub>O\<^sub>T (C' + {#L#}) S))
   \<Longrightarrow> C \<in># clauses S
   \<Longrightarrow> trail S \<Turnstile>as CNot C
   \<Longrightarrow> undefined_lit F L
   \<Longrightarrow> atm_of L \<in> atms_of_mm (clauses S) \<union> atm_of ` (lits_of_l (trail S))
   \<Longrightarrow> clauses S \<Turnstile>pm C' + {#L#}
   \<Longrightarrow> F \<Turnstile>as CNot C'
   \<Longrightarrow> backjump_l_cond C C' L T
   \<Longrightarrow> backjump_l S T"
inductive_cases backjump_lE: "backjump_l S T"

inductive cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_decide\<^sub>N\<^sub>O\<^sub>T:  "decide\<^sub>N\<^sub>O\<^sub>T S S' \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S S'" |
cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_propagate\<^sub>N\<^sub>O\<^sub>T: "propagate\<^sub>N\<^sub>O\<^sub>T S S' \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S S'" |
cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_backjump_l:  "backjump_l S S' \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S S'" |
cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_forget\<^sub>N\<^sub>O\<^sub>T: "forget\<^sub>N\<^sub>O\<^sub>T S S' \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S S'"

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_no_dup_inv:
  "cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S T \<Longrightarrow> no_dup (trail S) \<Longrightarrow> no_dup (trail T)"
  apply (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn.induct)
      using defined_lit_map apply fastforce
    using defined_lit_map apply fastforce
   apply (force simp: defined_lit_map elim!: backjump_lE)[]
  using forget\<^sub>N\<^sub>O\<^sub>T.simps apply auto[1]
  done
end

locale cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_proxy =
  cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_ops trail clauses prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T
    propagate_conds forget_conds "\<lambda>C C' L' S.  backjump_l_cond C C' L' S
    \<and> distinct_mset (C' + {#L'#}) \<and> \<not>tautology (C' + {#L'#})"
  for
    trail :: "'st \<Rightarrow> ('v, unit, unit) marked_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    prepend_trail :: "('v, unit, unit) marked_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T:: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    propagate_conds :: "('v, unit, unit) marked_lit \<Rightarrow> 'st \<Rightarrow> bool" and
    forget_conds :: "'v clause \<Rightarrow> 'st \<Rightarrow> bool" and
    backjump_l_cond :: "'v clause \<Rightarrow> 'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> bool" +
  fixes
    inv :: "'st \<Rightarrow> bool"
  assumes
     bj_merge_can_jump:
     "\<And>S C F' K F L.
       inv S
       \<Longrightarrow> trail S = F' @ Marked K () # F
       \<Longrightarrow> C \<in># clauses S
       \<Longrightarrow> trail S \<Turnstile>as CNot C
       \<Longrightarrow> undefined_lit F L
       \<Longrightarrow> atm_of L \<in> atms_of_mm (clauses S) \<union> atm_of ` (lits_of_l (F' @ Marked K () # F))
       \<Longrightarrow> clauses S \<Turnstile>pm C' + {#L#}
       \<Longrightarrow> F \<Turnstile>as CNot C'
       \<Longrightarrow> \<not>no_step backjump_l S" and
     cdcl_merged_inv: "\<And>S T. cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S T \<Longrightarrow> inv S \<Longrightarrow> inv T"
begin
abbreviation backjump_conds where
"backjump_conds \<equiv> \<lambda>_ C L _ _.  distinct_mset (C + {#L#}) \<and> \<not>tautology (C + {#L#})"

sublocale dpll_with_backjumping_ops trail clauses prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T
  propagate_conds inv backjump_conds
proof (unfold_locales, goal_cases)
  case 1
  { fix S S'
    assume bj: "backjump_l S S'" and "no_dup (trail S)"
    then obtain F' K F L C' C where
      S': "S' \<sim> prepend_trail (Propagated L ()) (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F
        (tl_trail(add_cls\<^sub>N\<^sub>O\<^sub>T (C' + {#L#}) S)))"
        and
      tr_S: "trail S = F' @ Marked K () # F" and
      C: "C \<in># clauses S" and
      tr_S_C: "trail S \<Turnstile>as CNot C" and
      undef_L: "undefined_lit F L" and
      atm_L: "atm_of L \<in> atms_of_mm (clauses S) \<union> atm_of ` lits_of_l (trail S)" and
      cls_S_C': "clauses S \<Turnstile>pm C' + {#L#}" and
      F_C': "F \<Turnstile>as CNot C'" and
      dist: "distinct_mset (C' + {#L#})" and
      not_tauto: "\<not> tautology (C' + {#L#})"
      by (elim backjump_lE) simp

    have "\<exists>S'. backjumping_ops.backjump trail clauses prepend_trail tl_trail backjump_conds S S'"
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
  then show ?case using 1 bj_merge_can_jump by meson
qed

end

locale cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_proxy2 =
  cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_proxy trail clauses prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T
    propagate_conds forget_conds backjump_l_cond inv
  for
    trail :: "'st \<Rightarrow> ('v, unit, unit) marked_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    prepend_trail :: "('v, unit, unit) marked_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T:: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    propagate_conds :: "('v, unit, unit) marked_lit \<Rightarrow> 'st \<Rightarrow> bool" and
    inv :: "'st \<Rightarrow> bool" and
    forget_conds :: "'v clause \<Rightarrow> 'st \<Rightarrow> bool" and
    backjump_l_cond :: "'v clause \<Rightarrow> 'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> bool"
begin

sublocale conflict_driven_clause_learning_ops trail clauses prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T
  remove_cls\<^sub>N\<^sub>O\<^sub>T propagate_conds inv backjump_conds "\<lambda>C _.  distinct_mset C \<and> \<not>tautology C"
  forget_conds
  by unfold_locales
end

locale cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn =
  cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_proxy2 trail clauses prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T
    propagate_conds inv forget_conds backjump_l_cond
  for
    trail :: "'st \<Rightarrow> ('v, unit, unit) marked_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    prepend_trail :: "('v, unit, unit) marked_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T:: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    propagate_conds :: "('v, unit, unit) marked_lit \<Rightarrow> 'st \<Rightarrow> bool" and
    inv :: "'st \<Rightarrow> bool" and
    forget_conds :: "'v clause \<Rightarrow> 'st \<Rightarrow> bool" and
    backjump_l_cond :: "'v clause \<Rightarrow> 'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> bool" +
  assumes
     dpll_bj_inv: "\<And>S T.  dpll_bj S T \<Longrightarrow> inv S \<Longrightarrow> inv T" and
     learn_inv: "\<And>S T. learn S T \<Longrightarrow> inv S \<Longrightarrow> inv T"
begin

interpretation cdcl\<^sub>N\<^sub>O\<^sub>T:
   conflict_driven_clause_learning trail clauses prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T
   propagate_conds inv backjump_conds "\<lambda>C _. distinct_mset C \<and> \<not>tautology C" forget_conds
  apply unfold_locales
  apply (simp only: cdcl\<^sub>N\<^sub>O\<^sub>T.simps)
  using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_forget\<^sub>N\<^sub>O\<^sub>T cdcl_merged_inv learn_inv
  by (auto simp add: cdcl\<^sub>N\<^sub>O\<^sub>T.simps dpll_bj_inv)

lemma backjump_l_learn_backjump:
  assumes bt: "backjump_l S T" and inv: "inv S" and n_d: "no_dup (trail S)"
  shows "\<exists>C' L. learn S (add_cls\<^sub>N\<^sub>O\<^sub>T (C' + {#L#}) S)
    \<and> backjump (add_cls\<^sub>N\<^sub>O\<^sub>T (C' + {#L#}) S) T
    \<and> atms_of (C' + {#L#}) \<subseteq> atms_of_mm (clauses S) \<union> atm_of ` (lits_of_l (trail S))"
proof -
   obtain C F' K F L l C' where
     tr_S: "trail S = F' @ Marked K () # F" and
     T: "T \<sim> prepend_trail (Propagated L l) (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F (add_cls\<^sub>N\<^sub>O\<^sub>T (C' + {#L#}) S))" and
     C_cls_S: "C \<in># clauses S" and
     tr_S_CNot_C: "trail S \<Turnstile>as CNot C" and
     undef: "undefined_lit F L" and
     atm_L: "atm_of L \<in> atms_of_mm (clauses S) \<union> atm_of ` (lits_of_l (trail S))" and
     clss_C: "clauses S \<Turnstile>pm C' + {#L#}" and
     "F \<Turnstile>as CNot C'" and
     distinct:  "distinct_mset (C' + {#L#})" and
     not_tauto: "\<not> tautology (C' + {#L#})"
     using bt inv by (elim backjump_lE) simp
   have atms_C':  "atms_of C' \<subseteq>  atm_of ` (lits_of_l F)"
     proof -
       obtain ll :: "'v \<Rightarrow> ('v literal \<Rightarrow> 'v) \<Rightarrow> 'v literal set \<Rightarrow> 'v literal" where
         "\<forall>v f L. v \<notin> f ` L \<or> v = f (ll v f L) \<and> ll v f L \<in> L"
         by moura
       then show ?thesis unfolding tr_S
         by (metis (no_types) \<open>F \<Turnstile>as CNot C'\<close> atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
           atms_of_def in_CNot_implies_uminus(2) subsetI)
     qed
   then have "atms_of (C' + {#L#}) \<subseteq> atms_of_mm (clauses S) \<union> atm_of ` (lits_of_l (trail S))"
     using atm_L tr_S by auto
   moreover have learn: "learn S (add_cls\<^sub>N\<^sub>O\<^sub>T (C' + {#L#}) S)"
     apply (rule learn.intros)
         apply (rule clss_C)
       using atms_C' atm_L apply (fastforce simp add: tr_S  in_plus_implies_atm_of_on_atms_of_ms)[]
     apply standard
      apply (rule distinct)
      apply (rule not_tauto)
      apply simp
     done
   moreover have bj: "backjump (add_cls\<^sub>N\<^sub>O\<^sub>T (C' + {#L#}) S) T"
     apply (rule backjump.intros)
     using \<open>F \<Turnstile>as CNot C'\<close> C_cls_S tr_S_CNot_C undef T distinct not_tauto n_d
     by (auto simp: tr_S state_eq\<^sub>N\<^sub>O\<^sub>T_def simp del: state_simp\<^sub>N\<^sub>O\<^sub>T)
   ultimately show ?thesis by auto
qed

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_is_tranclp_cdcl\<^sub>N\<^sub>O\<^sub>T:
  "cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S T \<Longrightarrow> inv S \<Longrightarrow> no_dup (trail S) \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>+\<^sup>+ S T"
proof (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn.induct)
  case (cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_decide\<^sub>N\<^sub>O\<^sub>T T)
  then have "cdcl\<^sub>N\<^sub>O\<^sub>T S T"
    using bj_decide\<^sub>N\<^sub>O\<^sub>T cdcl\<^sub>N\<^sub>O\<^sub>T.simps by fastforce
  then show ?case by auto
next
  case (cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_propagate\<^sub>N\<^sub>O\<^sub>T T)
  then have "cdcl\<^sub>N\<^sub>O\<^sub>T S T"
    using bj_propagate\<^sub>N\<^sub>O\<^sub>T cdcl\<^sub>N\<^sub>O\<^sub>T.simps by fastforce
  then show ?case by auto
next
   case (cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_forget\<^sub>N\<^sub>O\<^sub>T T)
   then have "cdcl\<^sub>N\<^sub>O\<^sub>T S T"
     using c_forget\<^sub>N\<^sub>O\<^sub>T by blast
   then show ?case by auto
next
   case (cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_backjump_l T) note bt = this(1) and inv = this(2) and
     n_d = this(3)
   obtain C' :: "'v literal multiset" and L :: "'v literal" where
     f3: "learn S (add_cls\<^sub>N\<^sub>O\<^sub>T (C' + {#L#}) S) \<and>
       backjump (add_cls\<^sub>N\<^sub>O\<^sub>T (C' + {#L#}) S) T \<and>
       atms_of (C' + {#L#}) \<subseteq> atms_of_mm (clauses S) \<union> atm_of ` lits_of_l (trail S)"
     using n_d backjump_l_learn_backjump[OF bt inv] by blast
   then have f4: "cdcl\<^sub>N\<^sub>O\<^sub>T S (add_cls\<^sub>N\<^sub>O\<^sub>T (C' + {#L#}) S)"
     using n_d c_learn by blast
   have "cdcl\<^sub>N\<^sub>O\<^sub>T (add_cls\<^sub>N\<^sub>O\<^sub>T (C' + {#L#}) S) T"
     using f3 n_d bj_backjump c_dpll_bj by blast
   then show ?case
     using f4 by (meson tranclp.r_into_trancl tranclp.trancl_into_trancl)
qed

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_is_rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_and_inv:
  "cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn\<^sup>*\<^sup>* S T \<Longrightarrow> inv S \<Longrightarrow> no_dup (trail S) \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T \<and> inv T"
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by auto
next
  case (step T U) note st =this(1) and cdcl\<^sub>N\<^sub>O\<^sub>T = this(2) and IH = this(3)[OF this(4-)] and
    inv = this(4) and n_d = this(5)
  have "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* T U"
    using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_is_tranclp_cdcl\<^sub>N\<^sub>O\<^sub>T[OF cdcl\<^sub>N\<^sub>O\<^sub>T] IH
    cdcl\<^sub>N\<^sub>O\<^sub>T.rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup inv n_d by auto
  then have "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S U" using IH by fastforce
  moreover have "inv U" using n_d IH \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* T U\<close> cdcl\<^sub>N\<^sub>O\<^sub>T.rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_inv by blast
  ultimately show ?case using st by fast
qed

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_is_rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T:
  "cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn\<^sup>*\<^sup>* S T \<Longrightarrow> inv S \<Longrightarrow>no_dup (trail S) \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T"
  using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_is_rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_and_inv by blast

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_inv:
  "cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn\<^sup>*\<^sup>* S T \<Longrightarrow> inv S \<Longrightarrow> no_dup (trail S) \<Longrightarrow> inv T"
  using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_is_rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_and_inv by blast

definition \<mu>\<^sub>C' :: "'v literal multiset set \<Rightarrow> 'st \<Rightarrow> nat" where
"\<mu>\<^sub>C' A T \<equiv> \<mu>\<^sub>C (1+card (atms_of_ms A)) (2+card (atms_of_ms A)) (trail_weight T)"

definition \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged :: "'v literal multiset set \<Rightarrow> 'st \<Rightarrow> nat" where
"\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged A T \<equiv>
  ((2+card (atms_of_ms A)) ^ (1+card (atms_of_ms A)) - \<mu>\<^sub>C' A T) * 2 + card (set_mset (clauses T))"

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_decreasing_measure':
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S T" and
    inv: "inv S" and
    atm_clss: "atms_of_mm (clauses S) \<subseteq> atms_of_ms A" and
    atm_trail: "atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A" and
    n_d: "no_dup (trail S)" and
    fin_A: "finite A"
  shows "\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged A T < \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged A S"
  using assms(1)
proof induction
  case (cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_decide\<^sub>N\<^sub>O\<^sub>T T)
  have "clauses S = clauses T"
    using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_decide\<^sub>N\<^sub>O\<^sub>T.hyps by auto
  moreover have
    "(2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A))
       - \<mu>\<^sub>C (1 + card (atms_of_ms A)) (2 + card (atms_of_ms A)) (trail_weight T)
     < (2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A))
       - \<mu>\<^sub>C (1 + card (atms_of_ms A)) (2 + card (atms_of_ms A)) (trail_weight S)"
    apply (rule dpll_bj_trail_mes_decreasing_prop)
    using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_decide\<^sub>N\<^sub>O\<^sub>T fin_A atm_clss atm_trail n_d inv
    by (simp_all add: bj_decide\<^sub>N\<^sub>O\<^sub>T cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_decide\<^sub>N\<^sub>O\<^sub>T.hyps)
  ultimately show ?case
    unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged_def \<mu>\<^sub>C'_def by simp
next
  case (cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_propagate\<^sub>N\<^sub>O\<^sub>T T)
  have "clauses S = clauses T"
    using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_propagate\<^sub>N\<^sub>O\<^sub>T.hyps
    by (simp add: bj_propagate\<^sub>N\<^sub>O\<^sub>T inv dpll_bj_clauses)
  moreover have
    "(2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A))
       - \<mu>\<^sub>C (1 + card (atms_of_ms A)) (2 + card (atms_of_ms A)) (trail_weight T)
     < (2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A))
       - \<mu>\<^sub>C (1 + card (atms_of_ms A)) (2 + card (atms_of_ms A)) (trail_weight S)"
    apply (rule dpll_bj_trail_mes_decreasing_prop)
    using inv n_d atm_clss atm_trail fin_A by (simp_all add: bj_propagate\<^sub>N\<^sub>O\<^sub>T
      cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_propagate\<^sub>N\<^sub>O\<^sub>T.hyps)
  ultimately show ?case
    unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged_def \<mu>\<^sub>C'_def by simp
next
  case (cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_forget\<^sub>N\<^sub>O\<^sub>T T)
  have "card (set_mset (clauses T)) < card (set_mset (clauses S))"
    using \<open>forget\<^sub>N\<^sub>O\<^sub>T S T\<close> by (metis card_Diff1_less
      cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_forget\<^sub>N\<^sub>O\<^sub>T.hyps clauses_remove_cls\<^sub>N\<^sub>O\<^sub>T finite_set_mset forget\<^sub>N\<^sub>O\<^sub>TE
      order_refl set_mset_minus_replicate_mset(1) state_eq\<^sub>N\<^sub>O\<^sub>T_clauses)
  moreover
    have "trail S = trail T"
      using \<open>forget\<^sub>N\<^sub>O\<^sub>T S T\<close> by (auto elim: forget\<^sub>N\<^sub>O\<^sub>TE)
    then have
      "(2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A))
        - \<mu>\<^sub>C (1 + card (atms_of_ms A)) (2 + card (atms_of_ms A)) (trail_weight T)
       = (2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A))
        - \<mu>\<^sub>C (1 + card (atms_of_ms A)) (2 + card (atms_of_ms A)) (trail_weight S)"
       by auto
  ultimately show ?case
    unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged_def \<mu>\<^sub>C'_def by simp
next
  case (cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_backjump_l T) note bj_l = this(1)
  obtain C' L where
    learn: "learn S (add_cls\<^sub>N\<^sub>O\<^sub>T (C' + {#L#}) S)" and
    bj: "backjump (add_cls\<^sub>N\<^sub>O\<^sub>T (C' + {#L#}) S) T" and
    atms_C: "atms_of (C' + {#L#}) \<subseteq> atms_of_mm (clauses S) \<union> atm_of ` (lits_of_l (trail S))"
    using bj_l inv backjump_l_learn_backjump n_d atm_clss atm_trail by blast
  have card_T_S: "card (set_mset (clauses T)) \<le> 1+ card (set_mset (clauses S))"
    using bj_l inv by (force elim!: backjump_lE simp: card_insert_if)
  have
    "((2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A))
      - \<mu>\<^sub>C (1 + card (atms_of_ms A)) (2 + card (atms_of_ms A)) (trail_weight T))
    < ((2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A))
      - \<mu>\<^sub>C (1 + card (atms_of_ms A)) (2 + card (atms_of_ms A))
           (trail_weight (add_cls\<^sub>N\<^sub>O\<^sub>T (C' + {#L#}) S)))"
    apply (rule dpll_bj_trail_mes_decreasing_prop)
         using bj bj_backjump apply blast
        using cdcl\<^sub>N\<^sub>O\<^sub>T.c_learn cdcl\<^sub>N\<^sub>O\<^sub>T.cdcl\<^sub>N\<^sub>O\<^sub>T_inv inv learn apply blast
       using atms_C atm_clss atm_trail n_d clauses_add_cls\<^sub>N\<^sub>O\<^sub>T apply simp apply fast (* 2 apply-s are
       much faster than a single fastforce call  *)
      using atm_trail n_d apply simp
     apply (simp add: n_d)
    using fin_A apply simp
    done
  then have "((2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A))
      - \<mu>\<^sub>C (1 + card (atms_of_ms A)) (2 + card (atms_of_ms A)) (trail_weight T))
    < ((2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A))
      - \<mu>\<^sub>C (1 + card (atms_of_ms A)) (2 + card (atms_of_ms A)) (trail_weight S))"
    using n_d by auto
  then show ?case
    using card_T_S unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged_def \<mu>\<^sub>C'_def by linarith
qed

lemma wf_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn:
  assumes
    fin_A: "finite A"
  shows "wf {(T, S).
    (inv S \<and> atms_of_mm (clauses S) \<subseteq> atms_of_ms A \<and> atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A
    \<and> no_dup (trail S))
    \<and> cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S T}"
  apply (rule wfP_if_measure[of _ _ "\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged A"])
  using cdcl\<^sub>N\<^sub>O\<^sub>T_decreasing_measure' fin_A by simp

lemma tranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_tranclp:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn\<^sup>+\<^sup>+ S T" and
    inv: "inv S" and
    atm_clss: "atms_of_mm (clauses S) \<subseteq> atms_of_ms A" and
    atm_trail: "atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A" and
    n_d: "no_dup (trail S)" and
    fin_A[simp]: "finite A"
  shows "(T, S) \<in> {(T, S).
    (inv S \<and> atms_of_mm (clauses S) \<subseteq> atms_of_ms A \<and> atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A
    \<and> no_dup (trail S))
    \<and> cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S T}\<^sup>+" (is "_ \<in> ?P\<^sup>+")
  using assms(1)
proof (induction rule: tranclp_induct)
  case base
  then show ?case using n_d atm_clss atm_trail inv by auto
next
  case (step T U) note st = this(1) and cdcl\<^sub>N\<^sub>O\<^sub>T = this(2) and IH = this(3)
  have "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T"
    apply (rule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_is_rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T)
    using st cdcl\<^sub>N\<^sub>O\<^sub>T inv  n_d atm_clss atm_trail inv by auto
  have "inv T"
    apply (rule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_inv)
      using inv st cdcl\<^sub>N\<^sub>O\<^sub>T n_d atm_clss atm_trail inv by auto
  moreover have "atms_of_mm (clauses T) \<subseteq> atms_of_ms A"
    using cdcl\<^sub>N\<^sub>O\<^sub>T.rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_trail_clauses_bound[OF \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T\<close> inv n_d atm_clss atm_trail]
    by fast
  moreover have "atm_of ` (lits_of_l (trail T))\<subseteq> atms_of_ms A"
    using cdcl\<^sub>N\<^sub>O\<^sub>T.rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_trail_clauses_bound[OF \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T\<close> inv n_d atm_clss atm_trail]
    by fast
  moreover have "no_dup (trail T)"
    using cdcl\<^sub>N\<^sub>O\<^sub>T.rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup[OF  \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T\<close> inv n_d] by fast
  ultimately have "(U, T) \<in> ?P"
    using cdcl\<^sub>N\<^sub>O\<^sub>T by auto
  then show ?case using IH by (simp add: trancl_into_trancl2)
qed

lemma wf_tranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn:
  assumes "finite A"
  shows "wf {(T, S).
    (inv S \<and> atms_of_mm (clauses S) \<subseteq> atms_of_ms A \<and> atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A
    \<and> no_dup (trail S))
    \<and> cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn\<^sup>+\<^sup>+ S T}"
  apply (rule wf_subset)
   apply (rule wf_trancl[OF wf_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn])
   using assms apply simp
  using tranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_tranclp[OF _ _ _ _ _ \<open>finite A\<close>] by auto

lemma backjump_no_step_backjump_l:
  "backjump S T \<Longrightarrow> inv S \<Longrightarrow> \<not>no_step backjump_l S"
  apply (elim backjumpE)
  apply (rule bj_merge_can_jump)
    apply auto[7]
  by blast

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_final_state:
  fixes A :: "'v literal multiset set" and S T :: "'st"
  assumes
    n_s: "no_step cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S" and
    atms_S: "atms_of_mm (clauses S) \<subseteq> atms_of_ms A" and
    atms_trail: "atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A" and
    n_d: "no_dup (trail S)" and
    "finite A" and
    inv: "inv S" and
    decomp: "all_decomposition_implies_m (clauses S) (get_all_marked_decomposition (trail S))"
  shows "unsatisfiable (set_mset (clauses S))
    \<or> (trail S \<Turnstile>asm clauses S \<and> satisfiable (set_mset (clauses S)))"
proof -
  let ?N = "set_mset (clauses S)"
  let ?M = "trail S"
  consider
      (sat) "satisfiable ?N" and "?M \<Turnstile>as ?N"
    | (sat') "satisfiable ?N" and "\<not> ?M \<Turnstile>as ?N"
    | (unsat) "unsatisfiable ?N"
    by auto
  then show ?thesis
    proof cases
      case sat' note sat = this(1) and M = this(2)
      obtain C where "C \<in> ?N" and "\<not>?M \<Turnstile>a C" using M unfolding true_annots_def by auto
      obtain I :: "'v literal set" where
        "I \<Turnstile>s ?N" and
        cons: "consistent_interp I" and
        tot: "total_over_m I ?N" and
        atm_I_N: "atm_of `I \<subseteq> atms_of_ms ?N"
        using sat unfolding satisfiable_def_min by auto
      let ?I = "I \<union> {P| P. P \<in> lits_of_l ?M \<and> atm_of P \<notin> atm_of ` I}"
      let ?O = "{{#lit_of L#} |L. is_marked L \<and> L \<in> set ?M \<and> atm_of (lit_of L) \<notin> atms_of_ms ?N}"
      have cons_I': "consistent_interp ?I"
        using cons using \<open>no_dup ?M\<close>  unfolding consistent_interp_def
        by (auto simp add: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set lits_of_def
          dest!: no_dup_cannot_not_lit_and_uminus)
      have tot_I': "total_over_m ?I (?N \<union> unmark_l ?M)"
        using tot atms_of_m_s_def unfolding total_over_m_def total_over_set_def
        by fastforce
      have "{P |P. P \<in> lits_of_l ?M \<and> atm_of P \<notin> atm_of ` I} \<Turnstile>s ?O"
        using \<open>I\<Turnstile>s ?N\<close> atm_I_N by (auto simp add: atm_of_eq_atm_of true_clss_def lits_of_def)
      then have I'_N: "?I \<Turnstile>s ?N \<union> ?O"
        using \<open>I\<Turnstile>s ?N\<close> true_clss_union_increase by force
      have tot': "total_over_m ?I (?N\<union>?O)"
        using atm_I_N tot unfolding total_over_m_def total_over_set_def
        by (force simp: image_iff lits_of_def dest!: is_marked_ex_Marked)

      have atms_N_M: "atms_of_ms ?N \<subseteq> atm_of ` lits_of_l ?M"
        proof (rule ccontr)
          assume "\<not> ?thesis"
          then obtain l :: 'v where
            l_N: "l \<in> atms_of_ms ?N" and
            l_M: "l \<notin> atm_of ` lits_of_l ?M"
            by auto
          have "undefined_lit ?M (Pos l)"
            using l_M by (metis Marked_Propagated_in_iff_in_lits_of_l
              atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set literal.sel(1))
          have "decide\<^sub>N\<^sub>O\<^sub>T S (prepend_trail (Marked (Pos l) ()) S)"
            by (metis \<open>undefined_lit ?M (Pos l)\<close> decide\<^sub>N\<^sub>O\<^sub>T.intros l_N literal.sel(1)
              state_eq\<^sub>N\<^sub>O\<^sub>T_ref)
          then show False
            using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_decide\<^sub>N\<^sub>O\<^sub>T n_s by blast
        qed

      have "?M \<Turnstile>as CNot C"
        by (metis atms_N_M \<open>C \<in> ?N\<close> \<open>\<not> ?M \<Turnstile>a C\<close> all_variables_defined_not_imply_cnot
          atms_of_m_atms_of_ms_mono atms_of_ms_CNot_atms_of atms_of_ms_CNot_atms_of_ms subsetCE)
      have "\<exists>l \<in> set ?M. is_marked l"
        proof (rule ccontr)
          let ?O = "{{#lit_of L#} |L. is_marked L \<and> L \<in> set ?M \<and> atm_of (lit_of L) \<notin> atms_of_ms ?N}"
          have \<theta>[iff]: "\<And>I. total_over_m I (?N \<union> ?O \<union> unmark_l ?M)
            \<longleftrightarrow> total_over_m I (?N \<union>unmark_l ?M)"
            unfolding total_over_set_def total_over_m_def atms_of_ms_def by auto
          assume "\<not> ?thesis"
          then have [simp]:"{{#lit_of L#} |L. is_marked L \<and> L \<in> set ?M}
            = {{#lit_of L#} |L. is_marked L \<and> L \<in> set ?M \<and> atm_of (lit_of L) \<notin> atms_of_ms ?N}"
            by auto
          then have "?N \<union> ?O \<Turnstile>ps unmark_l ?M"
            using all_decomposition_implies_propagated_lits_are_implied[OF decomp] by auto

          then have "?I \<Turnstile>s unmark_l ?M"
            using cons_I' I'_N tot_I' \<open>?I \<Turnstile>s ?N \<union> ?O\<close> unfolding \<theta> true_clss_clss_def by blast
          then have "lits_of_l ?M \<subseteq> ?I"
            unfolding true_clss_def lits_of_def by auto
          then have "?M \<Turnstile>as ?N"
            using I'_N \<open>C \<in> ?N\<close> \<open>\<not> ?M \<Turnstile>a C\<close> cons_I' atms_N_M
            by (meson \<open>trail S \<Turnstile>as CNot C\<close> consistent_CNot_not rev_subsetD sup_ge1 true_annot_def
              true_annots_def true_cls_mono_set_mset_l true_clss_def)
          then show False using M by fast
        qed
      from List.split_list_first_propE[OF this] obtain K :: "'v literal" and d :: unit and
        F F' :: "('v, unit, unit) marked_lit list" where
        M_K: "?M = F' @ Marked K () # F" and
        nm: "\<forall>f\<in>set F'. \<not>is_marked f"
        unfolding is_marked_def by (metis (full_types) old.unit.exhaust)
      let ?K = "Marked K ()::('v, unit, unit) marked_lit"
      have "?K \<in> set ?M"
        unfolding M_K by auto
      let ?C = "image_mset lit_of {#L\<in>#mset ?M. is_marked L \<and> L\<noteq>?K#} :: 'v literal multiset"
      let ?C' = "set_mset (image_mset (\<lambda>L::'v literal. {#L#}) (?C+{#lit_of ?K#}))"
      have "?N \<union> {{#lit_of L#} |L. is_marked L \<and> L \<in> set ?M} \<Turnstile>ps unmark_l ?M"
        using all_decomposition_implies_propagated_lits_are_implied[OF decomp] .
      moreover have C': "?C' = {{#lit_of L#} |L. is_marked L \<and> L \<in> set ?M}"
        unfolding M_K apply standard
          apply force
        using IntI by auto
      ultimately have N_C_M: "?N \<union> ?C' \<Turnstile>ps unmark_l ?M"
        by auto
      have N_M_False: "?N \<union> (\<lambda>L. {#lit_of L#}) ` (set ?M) \<Turnstile>ps {{#}}"
        using M \<open>?M \<Turnstile>as CNot C\<close> \<open>C\<in>?N\<close> unfolding true_clss_clss_def true_annots_def Ball_def
        true_annot_def by (metis consistent_CNot_not sup.orderE sup_commute true_clss_def
          true_clss_singleton_lit_of_implies_incl true_clss_union true_clss_union_increase)

      have "undefined_lit F K" using \<open>no_dup ?M\<close> unfolding M_K by (simp add: defined_lit_map)
      moreover
        have "?N \<union> ?C' \<Turnstile>ps {{#}}"
          proof -
            have A: "?N \<union> ?C' \<union> unmark_l ?M  =
              ?N \<union> unmark_l ?M"
              unfolding M_K by auto
            show ?thesis
              using true_clss_clss_left_right[OF N_C_M, of "{{#}}"] N_M_False unfolding A by auto
          qed
        have "?N \<Turnstile>p image_mset uminus ?C + {#-K#}"
          unfolding true_clss_cls_def true_clss_clss_def total_over_m_def
          proof (intro allI impI)
            fix I
            assume
              tot: "total_over_set I (atms_of_ms (?N \<union> {image_mset uminus ?C+ {#- K#}}))" and
              cons: "consistent_interp I" and
              "I \<Turnstile>s ?N"
            have "(K \<in> I \<and> -K \<notin> I) \<or> (-K \<in> I \<and> K \<notin> I)"
              using cons tot unfolding consistent_interp_def by (cases K) auto
            have " {a \<in> set (trail S). is_marked a \<and> a \<noteq> Marked K ()} =
             set (trail S) \<inter> {L. is_marked L \<and> L \<noteq> Marked K ()}"
             by auto
            then have tot': "total_over_set I
               (atm_of ` lit_of ` (set ?M \<inter> {L. is_marked L \<and> L \<noteq> Marked K ()}))"
              using tot by (auto simp add: atms_of_m_uminus_lit_atm_of_lit_of)
            { fix x :: "('v, unit, unit) marked_lit"
              assume
                a3: "lit_of x \<notin> I" and
                a1: "x \<in> set ?M" and
                a4: "is_marked x" and
                a5: "x \<noteq> Marked K ()"
              then have "Pos (atm_of (lit_of x)) \<in> I \<or> Neg (atm_of (lit_of x)) \<in> I"
                using a5 a4 tot' a1 unfolding total_over_set_def atms_of_m_s_def by blast
              moreover have f6: "Neg (atm_of (lit_of x)) = - Pos (atm_of (lit_of x))"
                by simp
              ultimately have "- lit_of x \<in> I"
                using f6 a3 by (metis (no_types) atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
                  literal.sel(1))
            } note H = this

            have "\<not>I \<Turnstile>s ?C'"
              using \<open>?N \<union> ?C' \<Turnstile>ps {{#}}\<close> tot cons \<open>I \<Turnstile>s ?N\<close>
              unfolding true_clss_clss_def total_over_m_def
              by (simp add: atms_of_m_uminus_lit_atm_of_lit_of atms_of_ms_single_image_atm_of_lit_of)
            then show "I \<Turnstile> image_mset uminus ?C + {#- K#}"
              unfolding true_clss_def true_cls_def Bex_def
              using \<open>(K \<in> I \<and> -K \<notin> I) \<or> (-K \<in> I \<and> K \<notin> I)\<close>
              by (auto dest!: H)
          qed
      moreover have "F \<Turnstile>as CNot (image_mset uminus ?C)"
        using nm unfolding true_annots_def CNot_def M_K by (auto simp add: lits_of_def)
      ultimately have False
        using bj_merge_can_jump[of S F' K F C "-K"
          "image_mset uminus (image_mset lit_of {# L :# mset ?M. is_marked L \<and> L \<noteq> Marked K ()#})"]
          \<open>C\<in>?N\<close> n_s \<open>?M \<Turnstile>as CNot C\<close> bj_backjump inv unfolding M_K
          by (auto simp: cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn.simps)
        then show ?thesis by fast
    qed auto
qed

lemma full_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_final_state:
  fixes A :: "'v literal multiset set" and S T :: "'st"
  assumes
    full: "full cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S T" and
    atms_S: "atms_of_mm (clauses S) \<subseteq> atms_of_ms A" and
    atms_trail: "atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A" and
    n_d: "no_dup (trail S)" and
    "finite A" and
    inv: "inv S" and
    decomp: "all_decomposition_implies_m (clauses S) (get_all_marked_decomposition (trail S))"
  shows "unsatisfiable (set_mset (clauses T))
    \<or> (trail T \<Turnstile>asm clauses T \<and> satisfiable (set_mset (clauses T)))"
proof -
  have st: "cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn\<^sup>*\<^sup>* S T" and n_s: "no_step cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn T"
    using full unfolding full_def by blast+
  then have st: "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T"
    using inv rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_is_rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_and_inv n_d by auto
  have "atms_of_mm (clauses T) \<subseteq> atms_of_ms A" and "atm_of ` lits_of_l (trail T) \<subseteq> atms_of_ms A"
    using cdcl\<^sub>N\<^sub>O\<^sub>T.rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_trail_clauses_bound[OF st inv n_d atms_S atms_trail] by blast+
  moreover have "no_dup (trail T)"
    using cdcl\<^sub>N\<^sub>O\<^sub>T.rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup inv n_d st by blast
  moreover have "inv T"
    using cdcl\<^sub>N\<^sub>O\<^sub>T.rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_inv inv st by blast
  moreover have "all_decomposition_implies_m (clauses T) (get_all_marked_decomposition (trail T))"
    using cdcl\<^sub>N\<^sub>O\<^sub>T.rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_all_decomposition_implies inv st decomp n_d by blast
  ultimately show ?thesis
    using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_final_state[of T A] \<open>finite A\<close> n_s by fast
qed

end

subsubsection \<open>Instantiations\<close>


locale cdcl\<^sub>N\<^sub>O\<^sub>T_with_backtrack_and_restarts =
  conflict_driven_clause_learning_learning_before_backjump_only_distinct_learnt trail clauses
    prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T propagate_conds inv backjump_conds
    learn_restrictions forget_restrictions
  for
    trail :: "'st \<Rightarrow> ('v, unit, unit) marked_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    prepend_trail :: "('v, unit, unit) marked_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T:: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    propagate_conds :: "('v, unit, unit) marked_lit \<Rightarrow> 'st \<Rightarrow> bool" and
    inv :: "'st \<Rightarrow> bool" and
    backjump_conds :: "'v clause \<Rightarrow> 'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool" and
    learn_restrictions forget_restrictions :: "'v clause \<Rightarrow> 'st \<Rightarrow> bool"
    +
  fixes f :: "nat \<Rightarrow> nat"
  assumes
    unbounded: "unbounded f" and f_ge_1: "\<And>n. n \<ge> 1 \<Longrightarrow> f n \<ge> 1" and
    inv_restart:"\<And>S T. inv S \<Longrightarrow> T \<sim> reduce_trail_to\<^sub>N\<^sub>O\<^sub>T ([]::'a list) S \<Longrightarrow> inv T"
begin

lemma bound_inv_inv:
  assumes
    "inv S" and
    n_d: "no_dup (trail S)" and
    atms_clss_S_A: "atms_of_mm (clauses S) \<subseteq> atms_of_ms A" and
    atms_trail_S_A:"atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A" and
    "finite A" and
    cdcl\<^sub>N\<^sub>O\<^sub>T: "cdcl\<^sub>N\<^sub>O\<^sub>T S T"
  shows
    "atms_of_mm (clauses T) \<subseteq> atms_of_ms A" and
    "atm_of ` lits_of_l (trail T) \<subseteq> atms_of_ms A" and
    "finite A"
proof -
  have "cdcl\<^sub>N\<^sub>O\<^sub>T S T"
    using \<open>inv S\<close> cdcl\<^sub>N\<^sub>O\<^sub>T by linarith
  then have "atms_of_mm (clauses T) \<subseteq> atms_of_mm (clauses S) \<union> atm_of ` lits_of_l (trail S)"
    using \<open>inv S\<close>
    by (meson conflict_driven_clause_learning_ops.cdcl\<^sub>N\<^sub>O\<^sub>T_atms_of_ms_clauses_decreasing
      conflict_driven_clause_learning_ops_axioms n_d)
  then show "atms_of_mm (clauses T) \<subseteq> atms_of_ms A"
    using atms_clss_S_A atms_trail_S_A by blast
next
  show "atm_of ` lits_of_l (trail T) \<subseteq> atms_of_ms A"
    by (meson \<open>inv S\<close> atms_clss_S_A atms_trail_S_A cdcl\<^sub>N\<^sub>O\<^sub>T cdcl\<^sub>N\<^sub>O\<^sub>T_atms_in_trail_in_set n_d)
next
  show "finite A"
    using \<open>finite A\<close> by simp
qed

sublocale cdcl\<^sub>N\<^sub>O\<^sub>T_increasing_restarts_ops "\<lambda>S T. T \<sim> reduce_trail_to\<^sub>N\<^sub>O\<^sub>T ([]::'a list) S" cdcl\<^sub>N\<^sub>O\<^sub>T f
  "\<lambda>A S. atms_of_mm (clauses S) \<subseteq> atms_of_ms A \<and> atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A \<and>
  finite A"
  \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' "\<lambda>S. inv S \<and> no_dup (trail S)"
  \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound
  apply unfold_locales
           apply (simp add: unbounded)
          using f_ge_1 apply force
         using bound_inv_inv apply meson
        apply (rule cdcl\<^sub>N\<^sub>O\<^sub>T_decreasing_measure'; simp)
        apply (rule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound; simp)
       apply (rule rtranclp_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_decreasing; simp)
      apply auto[]
    apply auto[]
   using cdcl\<^sub>N\<^sub>O\<^sub>T_inv cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup apply blast
  using inv_restart apply auto[]
  done

abbreviation cdcl\<^sub>N\<^sub>O\<^sub>T_l where
"cdcl\<^sub>N\<^sub>O\<^sub>T_l \<equiv>
  conflict_driven_clause_learning_ops.cdcl\<^sub>N\<^sub>O\<^sub>T trail clauses prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T
  remove_cls\<^sub>N\<^sub>O\<^sub>T propagate_conds (\<lambda>_ _ _ S T. backjump S T)
  (\<lambda>C S. distinct_mset C \<and> \<not> tautology C \<and> learn_restrictions C S
    \<and> (\<exists>F K F' C' L. trail S = F' @ Marked K () # F \<and> C = C' + {#L#}
       \<and> F \<Turnstile>as CNot C' \<and> C' + {#L#} \<notin># clauses S))
  (\<lambda>C S. \<not> (\<exists>F' F K L. trail S = F' @ Marked K () # F \<and> F \<Turnstile>as CNot (C - {#L#}))
  \<and> forget_restrictions C S)"

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_le_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound:
  assumes
    cdcl\<^sub>N\<^sub>O\<^sub>T: "cdcl\<^sub>N\<^sub>O\<^sub>T_restart (T, a) (V, b)" and
    cdcl\<^sub>N\<^sub>O\<^sub>T_inv:
      "inv T"
      "no_dup (trail T)" and
    bound_inv:
      "atms_of_mm (clauses T) \<subseteq> atms_of_ms A"
      "atm_of ` lits_of_l (trail T) \<subseteq> atms_of_ms A"
      "finite A"
  shows "\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' A V \<le> \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A T"
  using cdcl\<^sub>N\<^sub>O\<^sub>T_inv bound_inv
proof (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_induct[OF cdcl\<^sub>N\<^sub>O\<^sub>T])
  case (1 m S T n U) note U = this(3)
  show ?case
    apply (rule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T[of S T])
         using \<open>(cdcl\<^sub>N\<^sub>O\<^sub>T ^^ m) S T\<close>  apply (fastforce dest!: relpowp_imp_rtranclp)
        using 1 by auto
next
  case (2 S T n) note full = this(2)
  show ?case
    apply (rule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound)
    using full 2 unfolding full1_def by force+
qed

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_le_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound:
  assumes
    cdcl\<^sub>N\<^sub>O\<^sub>T: "cdcl\<^sub>N\<^sub>O\<^sub>T_restart (T, a) (V, b)" and
    cdcl\<^sub>N\<^sub>O\<^sub>T_inv:
      "inv T"
      "no_dup (trail T)" and
    bound_inv:
      "atms_of_mm (clauses T) \<subseteq> atms_of_ms A"
      "atm_of ` lits_of_l (trail T) \<subseteq> atms_of_ms A"
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
    using full 2 unfolding full1_def by force+
qed

sublocale cdcl\<^sub>N\<^sub>O\<^sub>T_increasing_restarts _ _ _ _ _ _ f
   (* restart *) "\<lambda>S T. T \<sim> reduce_trail_to\<^sub>N\<^sub>O\<^sub>T ([]::'a list) S"
   (* bound_inv *)"\<lambda>A S. atms_of_mm (clauses S) \<subseteq> atms_of_ms A
     \<and> atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A \<and> finite A"
   \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' cdcl\<^sub>N\<^sub>O\<^sub>T
   (* inv *) "\<lambda>S. inv S \<and> no_dup (trail S)"
   \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound
  apply unfold_locales
   using cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_le_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound apply simp
  using cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_le_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound apply simp
  done

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_restart_all_decomposition_implies:
  assumes "cdcl\<^sub>N\<^sub>O\<^sub>T_restart S T" and
    "inv (fst S)" and
    "no_dup (trail (fst S))"
    "all_decomposition_implies_m (clauses (fst S)) (get_all_marked_decomposition (trail (fst S)))"
  shows
    "all_decomposition_implies_m (clauses (fst T)) (get_all_marked_decomposition (trail (fst T)))"
  using assms apply (induction)
  using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_all_decomposition_implies by (auto dest!: tranclp_into_rtranclp
    simp: full1_def)

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_restart_all_decomposition_implies:
  assumes "cdcl\<^sub>N\<^sub>O\<^sub>T_restart\<^sup>*\<^sup>* S T" and
    inv: "inv (fst S)" and
    n_d: "no_dup (trail (fst S))" and
    decomp:
      "all_decomposition_implies_m (clauses (fst S)) (get_all_marked_decomposition (trail (fst S)))"
  shows
    "all_decomposition_implies_m (clauses (fst T)) (get_all_marked_decomposition (trail (fst T)))"
  using assms(1)
proof (induction rule: rtranclp_induct)
  case base
  then show ?case using decomp by simp
next
  case (step T u) note st = this(1) and r = this(2) and IH = this(3)
  have "inv (fst T)"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_inv[OF st] inv n_d by blast
  moreover have "no_dup (trail (fst T))"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_inv[OF st] inv n_d by blast
  ultimately show ?case
    using cdcl\<^sub>N\<^sub>O\<^sub>T_restart_all_decomposition_implies r IH n_d by fast
qed

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_restart_sat_ext_iff:
  assumes
    st: "cdcl\<^sub>N\<^sub>O\<^sub>T_restart S T" and
    n_d: "no_dup (trail (fst S))" and
    inv: "inv (fst S)"
  shows "I \<Turnstile>sextm clauses (fst S) \<longleftrightarrow> I \<Turnstile>sextm clauses(fst T)"
  using assms
proof (induction)
  case (restart_step m S T n U)
  then show ?case
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_bj_sat_ext_iff n_d by (fastforce dest!: relpowp_imp_rtranclp)
next
  case restart_full
  then show ?case using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_bj_sat_ext_iff unfolding full1_def
  by (fastforce dest!: tranclp_into_rtranclp)
qed

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_restart_sat_ext_iff:
  assumes
    st: "cdcl\<^sub>N\<^sub>O\<^sub>T_restart\<^sup>*\<^sup>* S T" and
    n_d: "no_dup (trail (fst S))" and
    inv: "inv (fst S)"
  shows "I \<Turnstile>sextm clauses (fst S) \<longleftrightarrow> I \<Turnstile>sextm clauses(fst T)"
  using st
proof (induction)
  case base
  then show ?case by simp
next
  case (step T U) note st = this(1) and r = this(2) and IH = this(3)
  have "inv (fst T)"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_inv[OF st] inv n_d by blast+
  moreover have "no_dup (trail (fst T))"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_inv rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup st inv n_d by blast
  ultimately show ?case
    using cdcl\<^sub>N\<^sub>O\<^sub>T_restart_sat_ext_iff[OF r] IH by blast
qed

theorem full_cdcl\<^sub>N\<^sub>O\<^sub>T_restart_backjump_final_state:
  fixes A :: "'v literal multiset set" and S T :: "'st"
  assumes
    full: "full cdcl\<^sub>N\<^sub>O\<^sub>T_restart (S, n) (T, m)" and
    atms_S: "atms_of_mm (clauses S) \<subseteq> atms_of_ms A" and
    atms_trail: "atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A" and
    n_d: "no_dup (trail S)" and
    fin_A[simp]: "finite A" and
    inv: "inv S" and
    decomp: "all_decomposition_implies_m (clauses S) (get_all_marked_decomposition (trail S))"
  shows "unsatisfiable (set_mset (clauses S))
    \<or> (lits_of_l (trail T) \<Turnstile>sextm clauses S \<and> satisfiable (set_mset (clauses S)))"
proof -
  have st: "cdcl\<^sub>N\<^sub>O\<^sub>T_restart\<^sup>*\<^sup>* (S, n) (T, m)" and
    n_s: "no_step cdcl\<^sub>N\<^sub>O\<^sub>T_restart (T, m)"
    using full unfolding full_def by fast+
  have binv_T: "atms_of_mm (clauses T) \<subseteq> atms_of_ms A" "atm_of ` lits_of_l (trail T) \<subseteq> atms_of_ms A"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_bound_inv[OF st, of A] inv n_d atms_S atms_trail
    by auto
  moreover have inv_T: "no_dup (trail T)" "inv T"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_inv[OF st] inv n_d by auto
  moreover have "all_decomposition_implies_m (clauses T) (get_all_marked_decomposition (trail T))"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_restart_all_decomposition_implies[OF st] inv n_d
    decomp by auto
  ultimately have T: "unsatisfiable (set_mset (clauses T))
    \<or> (trail T \<Turnstile>asm clauses T \<and> satisfiable (set_mset (clauses T)))"
    using no_step_cdcl\<^sub>N\<^sub>O\<^sub>T_restart_no_step_cdcl\<^sub>N\<^sub>O\<^sub>T[of "(T, m)" A] n_s
    cdcl\<^sub>N\<^sub>O\<^sub>T_final_state[of T A] unfolding cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv_def by auto
  have eq_sat_S_T:"\<And>I. I \<Turnstile>sextm clauses S \<longleftrightarrow> I \<Turnstile>sextm clauses T"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_restart_sat_ext_iff[OF st] inv n_d atms_S
        atms_trail by auto
  have cons_T: "consistent_interp (lits_of_l (trail T))"
    using inv_T(1) distinct_consistent_interp by blast
  consider
      (unsat) "unsatisfiable (set_mset (clauses T))"
    | (sat) "trail T \<Turnstile>asm clauses T" and "satisfiable (set_mset (clauses T))"
    using T by blast
  then show ?thesis
    proof cases
      case unsat
      then have "unsatisfiable (set_mset (clauses S))"
        using eq_sat_S_T consistent_true_clss_ext_satisfiable true_clss_imp_true_cls_ext
        unfolding satisfiable_def by blast
      then show ?thesis by fast
    next
      case sat
      then have "lits_of_l (trail T) \<Turnstile>sextm clauses S"
        using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_restart_sat_ext_iff[OF st] inv n_d atms_S
        atms_trail by (auto simp: true_clss_imp_true_cls_ext true_annots_true_cls)
      moreover then have "satisfiable (set_mset (clauses S))"
          using cons_T consistent_true_clss_ext_satisfiable by blast
      ultimately show ?thesis by blast
    qed
qed
end \<comment> \<open>end of \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_with_backtrack_and_restarts\<close> locale\<close>

locale most_general_cdcl\<^sub>N\<^sub>O\<^sub>T =
    dpll_state trail clauses prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T +
    propagate_ops trail clauses prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T propagate_conds +
    backjumping_ops trail clauses prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T "\<lambda>_ _ _ _ _. True"
  for
    trail :: "'st \<Rightarrow> ('v, unit, unit) marked_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    prepend_trail :: "('v, unit, unit) marked_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T:: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    propagate_conds :: "('v, unit, unit) marked_lit \<Rightarrow> 'st \<Rightarrow> bool" and
    inv :: "'st \<Rightarrow> bool"
begin
lemma backjump_bj_can_jump:
  assumes
    tr_S: "trail S = F' @ Marked K () # F" and
    C: "C \<in># clauses S" and
    tr_S_C: "trail S \<Turnstile>as CNot C" and
    undef: "undefined_lit F L" and
    atm_L: "atm_of L \<in> atms_of_mm (clauses S) \<union> atm_of ` (lits_of_l (F' @ Marked K () # F))" and
    cls_S_C': "clauses S \<Turnstile>pm C' + {#L#}" and
    F_C': "F \<Turnstile>as CNot C'"
  shows "\<not>no_step backjump S"
    using backjump.intros[OF tr_S _ C tr_S_C undef _ cls_S_C' F_C',
      of "prepend_trail (Propagated L _) (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S)"] atm_L unfolding tr_S
    by (auto simp: state_eq\<^sub>N\<^sub>O\<^sub>T_def simp del: state_simp\<^sub>N\<^sub>O\<^sub>T)

sublocale dpll_with_backjumping_ops _ _ _ _ _ _ _ inv "\<lambda>_ _ _ _ _. True"
  using backjump_bj_can_jump by unfold_locales auto
end

text \<open>The restart does only reset the trail, contrary to Weidenbach's version. But there is a forget
  rule.\<close>
locale cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_with_backtrack_restarts =
  cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn trail clauses prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T
    propagate_conds inv forget_conds
    "\<lambda>C C' L' S. distinct_mset (C' + {#L'#}) \<and> backjump_l_cond C C' L' S"
    for
    trail :: "'st \<Rightarrow> ('v, unit, unit) marked_lits" and
    clauses :: "'st \<Rightarrow> 'v clauses" and
    prepend_trail :: "('v, unit, unit) marked_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T:: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    propagate_conds :: "('v, unit, unit) marked_lit \<Rightarrow> 'st \<Rightarrow> bool" and
    inv :: "'st \<Rightarrow> bool" and
    forget_conds :: "'v clause \<Rightarrow> 'st \<Rightarrow> bool" and
    backjump_l_cond :: "'v clause \<Rightarrow> 'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> bool"
    +
  fixes f :: "nat \<Rightarrow> nat"
  assumes
    unbounded: "unbounded f" and f_ge_1: "\<And>n. n \<ge> 1 \<Longrightarrow> f n \<ge> 1" and
    inv_restart:"\<And>S T. inv S \<Longrightarrow> T \<sim> reduce_trail_to\<^sub>N\<^sub>O\<^sub>T [] S \<Longrightarrow> inv T"
begin

(* is already alround in context *)

interpretation cdcl\<^sub>N\<^sub>O\<^sub>T:
   conflict_driven_clause_learning_ops trail clauses prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T
   propagate_conds inv backjump_conds "(\<lambda>C _. distinct_mset C \<and> \<not> tautology C)" forget_conds
  by unfold_locales

interpretation cdcl\<^sub>N\<^sub>O\<^sub>T:
   conflict_driven_clause_learning trail clauses prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T
   propagate_conds inv backjump_conds "(\<lambda>C _. distinct_mset C \<and> \<not> tautology C)" forget_conds
  apply unfold_locales
  using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_forget\<^sub>N\<^sub>O\<^sub>T cdcl_merged_inv learn_inv
  by (auto simp add: cdcl\<^sub>N\<^sub>O\<^sub>T.simps dpll_bj_inv)

definition "not_simplified_cls A = {#C \<in># A. tautology C \<or> \<not>distinct_mset C#}"

lemma simple_clss_or_not_simplified_cls:
  assumes "atms_of_mm (clauses S) \<subseteq> atms_of_ms A" and
    "x \<in># clauses S" and "finite A"
  shows "x \<in> simple_clss (atms_of_ms A) \<or> x \<in># not_simplified_cls (clauses S)"
proof -
  consider
      (simpl) "\<not>tautology x" and "distinct_mset x"
    | (n_simp) "tautology x \<or> \<not>distinct_mset x"
    by auto
  then show ?thesis
    proof cases
      case simpl
      then have "x \<in> simple_clss (atms_of_ms A)"
        by (meson assms atms_of_m_atms_of_ms_mono atms_of_ms_finite simple_clss_mono
          distinct_mset_not_tautology_implies_in_simple_clss finite_subset
          subsetCE)
      then show ?thesis by blast
    next
      case n_simp
      then have "x \<in># not_simplified_cls (clauses S)"
        using \<open>x \<in># clauses S\<close> unfolding not_simplified_cls_def by auto
      then show ?thesis by blast
    qed
qed

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_clauses_bound:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S T" and
    inv: "inv S" and
    atms_clss: "atms_of_mm (clauses S) \<subseteq> atms_of_ms A" and
    atms_trail: "atm_of `(lits_of_l (trail S)) \<subseteq> atms_of_ms A" and
    n_d: "no_dup (trail S)" and
    fin_A[simp]: "finite A"
  shows "set_mset (clauses T) \<subseteq> set_mset (not_simplified_cls (clauses S))
    \<union> simple_clss (atms_of_ms A)"
  using assms
proof (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn.induct)
  case cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_decide\<^sub>N\<^sub>O\<^sub>T
  then show ?case using dpll_bj_clauses by (force dest!: simple_clss_or_not_simplified_cls)
next
  case cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_propagate\<^sub>N\<^sub>O\<^sub>T
  then show ?case using dpll_bj_clauses by (force dest!: simple_clss_or_not_simplified_cls)
next
  case cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_forget\<^sub>N\<^sub>O\<^sub>T
  then show ?case using clauses_remove_cls\<^sub>N\<^sub>O\<^sub>T unfolding state_eq\<^sub>N\<^sub>O\<^sub>T_def
    by (force elim!: forget\<^sub>N\<^sub>O\<^sub>TE  dest: simple_clss_or_not_simplified_cls)
next
  case (cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_backjump_l T) note bj = this(1) and inv = this(2) and
    atms_clss = this(3) and atms_trail = this(4) and n_d = this(5)

  have "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T"
    apply (rule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_is_rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T)
    using \<open>backjump_l S T\<close> inv cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn.simps n_d by blast+
  have "atm_of `(lits_of_l (trail T)) \<subseteq> atms_of_ms A"
    using cdcl\<^sub>N\<^sub>O\<^sub>T.rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_trail_clauses_bound[OF \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T\<close>] inv atms_trail atms_clss
    n_d by auto
  have "atms_of_mm (clauses T) \<subseteq> atms_of_ms A"
    using cdcl\<^sub>N\<^sub>O\<^sub>T.rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_trail_clauses_bound[OF \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T\<close> inv n_d atms_clss atms_trail]
    by fast
  moreover have "no_dup (trail T)"
    using cdcl\<^sub>N\<^sub>O\<^sub>T.rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup[OF  \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T\<close> inv n_d] by fast

  obtain F' K F L l C' C where
    tr_S: "trail S = F' @ Marked K () # F" and
    T: "T \<sim> prepend_trail (Propagated L l) (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F (add_cls\<^sub>N\<^sub>O\<^sub>T (C' + {#L#}) S))" and
    "C \<in># clauses S" and
    "trail S \<Turnstile>as CNot C" and
    undef: "undefined_lit F L" and
    "atm_of L = atm_of K \<or> atm_of L \<in> atms_of_mm (clauses S)
      \<or> atm_of L \<in> atm_of ` (lits_of_l F' \<union> lits_of_l F)" and
    "clauses S \<Turnstile>pm C' + {#L#}" and
    "F \<Turnstile>as CNot C'" and
    dist: "distinct_mset (C' + {#L#})" and
    tauto: "\<not> tautology (C' + {#L#})" and
    "backjump_l_cond C C' L T"
    using \<open>backjump_l S T\<close> apply (induction rule: backjump_l.induct) by auto

  have "atms_of C' \<subseteq> atm_of ` (lits_of_l F)"
    using \<open>F \<Turnstile>as CNot C'\<close> by (simp add: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
      atms_of_def image_subset_iff in_CNot_implies_uminus(2))
  then have "atms_of (C'+{#L#}) \<subseteq> atms_of_ms A"
    using T \<open>atm_of ` lits_of_l (trail T) \<subseteq> atms_of_ms A\<close> tr_S undef n_d by auto
  then have "simple_clss (atms_of (C' + {#L#})) \<subseteq> simple_clss (atms_of_ms A)"
    apply - by (rule simple_clss_mono) (simp_all)
  then have "C' + {#L#} \<in> simple_clss (atms_of_ms A)"
    using distinct_mset_not_tautology_implies_in_simple_clss[OF dist tauto]
    by auto
  then show ?case
    using T inv atms_clss undef tr_S n_d
    by (force dest!: simple_clss_or_not_simplified_cls)
qed

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_not_simplified_decreasing:
  assumes "cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S T"
  shows "(not_simplified_cls (clauses T)) \<subseteq>#  (not_simplified_cls (clauses S))"
  using assms apply induction
  prefer 4
  unfolding not_simplified_cls_def apply (auto elim!: backjump_lE forget\<^sub>N\<^sub>O\<^sub>TE)[3]
  by (elim backjump_lE) auto

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_not_simplified_decreasing:
  assumes "cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn\<^sup>*\<^sup>* S T"
  shows "(not_simplified_cls (clauses T)) \<subseteq># (not_simplified_cls (clauses S))"
  using assms apply induction
    apply simp
   by (drule cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_not_simplified_decreasing) auto

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_clauses_bound:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn\<^sup>*\<^sup>* S T" and
    "inv S" and
    "atms_of_mm (clauses S) \<subseteq> atms_of_ms A" and
    "atm_of `(lits_of_l (trail S)) \<subseteq> atms_of_ms A" and
    n_d: "no_dup (trail S)" and
    finite[simp]: "finite A"
  shows "set_mset (clauses T) \<subseteq> set_mset (not_simplified_cls (clauses S))
    \<union> simple_clss (atms_of_ms A)"
  using assms(1-5)
proof induction
  case base
  then show ?case by (auto dest!: simple_clss_or_not_simplified_cls)
next
  case (step T U) note st = this(1) and cdcl\<^sub>N\<^sub>O\<^sub>T = this(2) and IH = this(3)[OF this(4-7)] and
    inv = this(4) and atms_clss_S = this(5) and atms_trail_S = this(6) and finite_cls_S = this(7)
  have st': "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T"
    using inv rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_is_rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_and_inv st n_d by blast
  have "inv T"
    using inv rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_inv st n_d by blast
  moreover
    have "atms_of_mm (clauses T) \<subseteq> atms_of_ms A" and
      "atm_of ` lits_of_l (trail T) \<subseteq> atms_of_ms A"
      using cdcl\<^sub>N\<^sub>O\<^sub>T.rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_trail_clauses_bound[OF st'] inv atms_clss_S atms_trail_S n_d
      by blast+
  moreover moreover have "no_dup (trail T)"
    using cdcl\<^sub>N\<^sub>O\<^sub>T.rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup[OF  \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T\<close> inv n_d] by fast
  ultimately have "set_mset (clauses U)
    \<subseteq> set_mset (not_simplified_cls (clauses T)) \<union> simple_clss (atms_of_ms A)"
    using cdcl\<^sub>N\<^sub>O\<^sub>T finite  cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_clauses_bound
    by (auto intro!: cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_clauses_bound)
  moreover have "set_mset (not_simplified_cls (clauses T))
    \<subseteq> set_mset (not_simplified_cls (clauses S))"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_not_simplified_decreasing[OF st] by auto
  ultimately show ?case using IH inv atms_clss_S
    by (auto dest!: simple_clss_or_not_simplified_cls)
qed

abbreviation \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound where
"\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A T ==  ((2+card (atms_of_ms A)) ^ (1+card (atms_of_ms A))) * 2
     + card (set_mset (not_simplified_cls(clauses T)))
     + 3 ^ card (atms_of_ms A) "

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_clauses_bound_card:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn\<^sup>*\<^sup>* S T" and
    "inv S" and
    "atms_of_mm (clauses S) \<subseteq> atms_of_ms A" and
    "atm_of `(lits_of_l (trail S)) \<subseteq> atms_of_ms A" and
    n_d: "no_dup (trail S)" and
    finite: "finite A"
  shows "\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged A T \<le> \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A S"
proof -
  have "set_mset (clauses T) \<subseteq> set_mset (not_simplified_cls(clauses S))
    \<union> simple_clss (atms_of_ms A)"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_clauses_bound[OF assms] .
  moreover have "card (set_mset (not_simplified_cls(clauses S))
      \<union> simple_clss (atms_of_ms A))
    \<le> card (set_mset (not_simplified_cls(clauses S))) + 3 ^ card (atms_of_ms A)"
    by (meson Nat.le_trans atms_of_ms_finite simple_clss_card card_Un_le finite
      nat_add_left_cancel_le)
  ultimately have "card (set_mset (clauses T))
    \<le> card (set_mset (not_simplified_cls(clauses S))) + 3 ^ card (atms_of_ms A)"
    by (meson Nat.le_trans atms_of_ms_finite simple_clss_finite card_mono
      finite_UnI finite_set_mset local.finite)
  moreover have "((2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A)) - \<mu>\<^sub>C' A T) * 2
    \<le> (2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A)) * 2"
    by auto
  ultimately show ?thesis unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged_def by auto
qed

sublocale cdcl\<^sub>N\<^sub>O\<^sub>T_increasing_restarts_ops "\<lambda>S T. T \<sim> reduce_trail_to\<^sub>N\<^sub>O\<^sub>T ([]::'a list) S"
   cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn f
   (* bound_inv *)"\<lambda>A S. atms_of_mm (clauses S) \<subseteq> atms_of_ms A
     \<and> atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A \<and> finite A"
   \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged
   (* inv *) "\<lambda>S. inv S \<and> no_dup (trail S)"
   \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound
   apply unfold_locales
              using unbounded apply simp
             using f_ge_1 apply force
            apply (blast dest!: cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_is_tranclp_cdcl\<^sub>N\<^sub>O\<^sub>T tranclp_into_rtranclp
              cdcl\<^sub>N\<^sub>O\<^sub>T.rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_trail_clauses_bound )
           apply (simp add: cdcl\<^sub>N\<^sub>O\<^sub>T_decreasing_measure')
          using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_clauses_bound_card apply blast
          apply (drule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_not_simplified_decreasing)
          apply (auto dest!: simp: card_mono set_mset_mono )[]
       apply simp
      apply auto[]
     using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_no_dup_inv cdcl_merged_inv apply blast
    apply (auto simp: inv_restart)[]
    done

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_restart_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged_le_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T_restart T V"
    "inv (fst T)" and
    "no_dup (trail (fst T))" and
    "atms_of_mm (clauses (fst T)) \<subseteq> atms_of_ms A" and
    "atm_of ` lits_of_l (trail (fst T)) \<subseteq> atms_of_ms A" and
    "finite A"
  shows "\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged A (fst V) \<le> \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A (fst T)"
  using assms
proof induction
  case (restart_full S T n)
  show ?case
    unfolding fst_conv
    apply (rule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_clauses_bound_card)
    using  restart_full unfolding full1_def by (force dest!: tranclp_into_rtranclp)+
next
  case (restart_step m S T n U) note st = this(1) and U = this(3) and inv = this(4) and
    n_d = this(5) and atms_clss = this(6) and atms_trail = this(7) and finite = this(8)
  then have st': "cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn\<^sup>*\<^sup>* S T"
    by (blast dest: relpowp_imp_rtranclp)
  then have st'': "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T"
    using inv n_d apply - by (rule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_is_rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T) auto
  have "inv T"
    apply (rule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_inv)
      using inv st' n_d by auto
  then have "inv U"
    using U by (auto simp: inv_restart)
  have "atms_of_mm (clauses T) \<subseteq> atms_of_ms A"
    using cdcl\<^sub>N\<^sub>O\<^sub>T.rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_trail_clauses_bound[OF st''] inv atms_clss atms_trail n_d
    by simp
  then have "atms_of_mm (clauses U) \<subseteq> atms_of_ms A"
    using U by simp
  have "not_simplified_cls (clauses U) \<subseteq># not_simplified_cls (clauses T)"
    using \<open>U \<sim> reduce_trail_to\<^sub>N\<^sub>O\<^sub>T [] T\<close> by auto
  moreover have "not_simplified_cls (clauses T) \<subseteq># not_simplified_cls (clauses S)"
    apply (rule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_not_simplified_decreasing)
    using \<open>(cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn ^^ m) S T\<close> by (auto dest!: relpowp_imp_rtranclp)
  ultimately have U_S: "not_simplified_cls (clauses U) \<subseteq># not_simplified_cls (clauses S)"
    by auto

  have "(set_mset (clauses U))
    \<subseteq> set_mset (not_simplified_cls (clauses U)) \<union> simple_clss (atms_of_ms A)"
    apply (rule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_clauses_bound)
         apply simp
        using \<open>inv U\<close> apply simp
       using \<open>atms_of_mm (clauses U) \<subseteq> atms_of_ms A\<close> apply simp
      using U apply simp
     using U apply simp
    using finite apply simp
    done
  then have f1: "card (set_mset (clauses U)) \<le> card (set_mset (not_simplified_cls (clauses U))
    \<union> simple_clss (atms_of_ms A))"
    by (simp add: simple_clss_finite card_mono local.finite)

  moreover have "set_mset (not_simplified_cls (clauses U)) \<union> simple_clss (atms_of_ms A)
    \<subseteq> set_mset (not_simplified_cls (clauses S)) \<union> simple_clss (atms_of_ms A)"
    using U_S by auto
  then have f2:
    "card (set_mset (not_simplified_cls (clauses U)) \<union> simple_clss (atms_of_ms A))
      \<le> card (set_mset (not_simplified_cls (clauses S)) \<union> simple_clss (atms_of_ms A))"
    by (simp add: simple_clss_finite card_mono local.finite)

  moreover have "card (set_mset (not_simplified_cls (clauses S))
      \<union> simple_clss (atms_of_ms A))
    \<le> card (set_mset (not_simplified_cls (clauses S))) + card (simple_clss (atms_of_ms A))"
    using card_Un_le by blast
  moreover have "card (simple_clss (atms_of_ms A)) \<le> 3 ^ card (atms_of_ms A)"
    using atms_of_ms_finite simple_clss_card local.finite by blast
  ultimately have "card (set_mset (clauses U))
    \<le> card (set_mset (not_simplified_cls (clauses S))) + 3 ^ card (atms_of_ms A)"
    by linarith
  then show ?case unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged_def by auto
qed

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_restart_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_le_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T_restart T V" and
    "no_dup (trail (fst T))" and
    "inv (fst T)" and
    fin: "finite A"
  shows "\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A (fst V) \<le> \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A (fst T)"
  using assms(1-3)
proof induction
  case (restart_full S T n)
  have "not_simplified_cls (clauses T) \<subseteq># not_simplified_cls (clauses S)"
    apply (rule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_not_simplified_decreasing)
    using \<open>full1 cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S T\<close> unfolding full1_def
    by (auto dest: tranclp_into_rtranclp)
  then show ?case by (auto simp: card_mono set_mset_mono)
next
  case (restart_step m S T n U) note st = this(1) and U = this(3) and n_d =this(4) and inv = this(5)
  then have st': "cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn\<^sup>*\<^sup>* S T"
    by (blast dest: relpowp_imp_rtranclp)
  then have st'': "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T"
    using inv n_d apply - by (rule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_is_rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T) auto
  have "inv T"
    apply (rule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_inv)
      using inv st' n_d by auto
  then have "inv U"
    using U by (auto simp: inv_restart)
  have "not_simplified_cls (clauses U) \<subseteq># not_simplified_cls (clauses T)"
    using \<open>U \<sim> reduce_trail_to\<^sub>N\<^sub>O\<^sub>T [] T\<close> by auto
  moreover have "not_simplified_cls (clauses T) \<subseteq># not_simplified_cls (clauses S)"
    apply (rule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_not_simplified_decreasing)
    using \<open>(cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn ^^ m) S T\<close> by (auto dest!: relpowp_imp_rtranclp)
  ultimately have U_S: "not_simplified_cls (clauses U) \<subseteq># not_simplified_cls (clauses S)"
    by auto
  then show ?case by (auto simp: card_mono set_mset_mono)
qed


sublocale cdcl\<^sub>N\<^sub>O\<^sub>T_increasing_restarts _ _ _ _ _ _ f "\<lambda>S T. T \<sim> reduce_trail_to\<^sub>N\<^sub>O\<^sub>T ([]::'a list) S"
   (* bound_inv *)"\<lambda>A S. atms_of_mm (clauses S) \<subseteq> atms_of_ms A
     \<and> atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A \<and> finite A"
   \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn
   (* inv *) "\<lambda>S. inv S \<and> no_dup (trail S)"
   "\<lambda>A T. ((2+card (atms_of_ms A)) ^ (1+card (atms_of_ms A))) * 2
     + card (set_mset (not_simplified_cls(clauses T)))
     + 3 ^ card (atms_of_ms A)"
   apply unfold_locales
     using cdcl\<^sub>N\<^sub>O\<^sub>T_restart_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged_le_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound apply force
    using cdcl\<^sub>N\<^sub>O\<^sub>T_restart_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_le_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound by fastforce

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_restart_eq_sat_iff:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T_restart S T" and
    "no_dup (trail (fst S))"
    "inv (fst S)"
  shows "I\<Turnstile>sextm clauses (fst S) \<longleftrightarrow> I \<Turnstile>sextm clauses (fst T)"
  using assms
proof (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_restart.induct)
  case (restart_full S T n)
  then have "cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn\<^sup>*\<^sup>* S T "
    by (simp add: tranclp_into_rtranclp full1_def)
  then show ?case
    using cdcl\<^sub>N\<^sub>O\<^sub>T.rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_bj_sat_ext_iff restart_full.prems(1,2)
    rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_is_rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T by auto
next
  case (restart_step m S T n U)
  then have "cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn\<^sup>*\<^sup>* S T"
    by (auto simp: tranclp_into_rtranclp full1_def dest!: relpowp_imp_rtranclp)
  then have "I \<Turnstile>sextm clauses S \<longleftrightarrow> I \<Turnstile>sextm clauses T"
    using cdcl\<^sub>N\<^sub>O\<^sub>T.rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_bj_sat_ext_iff restart_step.prems(1,2)
    rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_is_rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T by auto
  moreover have "I \<Turnstile>sextm clauses T \<longleftrightarrow> I \<Turnstile>sextm clauses U"
    using restart_step.hyps(3) by auto
  ultimately show ?case by auto
qed

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_restart_eq_sat_iff:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T_restart\<^sup>*\<^sup>* S T" and
    inv: "inv (fst S)" and n_d: "no_dup(trail (fst S))"
  shows "I\<Turnstile>sextm clauses (fst S) \<longleftrightarrow> I \<Turnstile>sextm clauses (fst T)"
  using assms(1)
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by simp
next
  case (step T U) note st = this(1) and cdcl = this(2) and IH = this(3)
  have "inv (fst T)" and "no_dup (trail (fst T))"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_inv using st inv n_d by blast+
  then have "I\<Turnstile>sextm clauses (fst T) \<longleftrightarrow> I \<Turnstile>sextm clauses (fst U)"
    using  cdcl\<^sub>N\<^sub>O\<^sub>T_restart_eq_sat_iff cdcl by blast
  then show ?case using IH by blast
qed

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_restart_all_decomposition_implies_m:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T_restart S T" and
    inv: "inv (fst S)" and n_d: "no_dup(trail (fst S))" and
    "all_decomposition_implies_m (clauses (fst S))
      (get_all_marked_decomposition (trail (fst S)))"
  shows "all_decomposition_implies_m (clauses (fst T))
      (get_all_marked_decomposition (trail (fst T)))"
  using assms
proof (induction)
  case (restart_full S T n) note full = this(1) and inv = this(2) and n_d = this(3) and
    decomp = this(4)
  have st: "cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn\<^sup>*\<^sup>* S T" and
    n_s: "no_step cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn T"
    using full unfolding full1_def by (fast dest: tranclp_into_rtranclp)+
  have st': "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T"
    using inv rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_is_rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_and_inv st n_d by auto
  have "inv T"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_inv[OF st] inv n_d by auto
  then show ?case
    using cdcl\<^sub>N\<^sub>O\<^sub>T.rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_all_decomposition_implies[OF _  _ n_d decomp] st' inv by auto
next
  case (restart_step m S T n U) note st = this(1) and U = this(3) and inv = this(4) and
    n_d = this(5) and decomp = this(6)
  show ?case using U by auto
qed

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_restart_all_decomposition_implies_m:
  assumes
    "cdcl\<^sub>N\<^sub>O\<^sub>T_restart\<^sup>*\<^sup>* S T" and
    inv: "inv (fst S)" and n_d: "no_dup(trail (fst S))" and
    decomp: "all_decomposition_implies_m (clauses (fst S))
      (get_all_marked_decomposition (trail (fst S)))"
  shows "all_decomposition_implies_m (clauses (fst T))
      (get_all_marked_decomposition (trail (fst T)))"
  using assms
proof (induction)
  case base
  then show ?case using decomp by simp
next
  case (step T U) note st = this(1) and cdcl = this(2) and IH = this(3)[OF this(4-)] and
    inv = this(4) and n_d = this(5) and decomp = this(6)
  have "inv (fst T)" and "no_dup (trail (fst T))"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_inv using st inv n_d by blast+
  then show ?case
    using cdcl\<^sub>N\<^sub>O\<^sub>T_restart_all_decomposition_implies_m[OF cdcl] IH by auto
qed

lemma full_cdcl\<^sub>N\<^sub>O\<^sub>T_restart_normal_form:
  assumes
    full: "full cdcl\<^sub>N\<^sub>O\<^sub>T_restart S T" and
    inv: "inv (fst S)" and n_d: "no_dup(trail (fst S))" and
    decomp: "all_decomposition_implies_m (clauses (fst S))
      (get_all_marked_decomposition (trail (fst S)))" and
    atms_cls: "atms_of_mm (clauses (fst S)) \<subseteq> atms_of_ms A" and
    atms_trail: "atm_of ` lits_of_l (trail (fst S)) \<subseteq> atms_of_ms A" and
    fin: "finite A"
  shows "unsatisfiable (set_mset (clauses (fst S)))
    \<or> lits_of_l (trail (fst T)) \<Turnstile>sextm clauses (fst S) \<and> satisfiable (set_mset (clauses (fst S)))"
proof -
  have inv_T: "inv (fst T)" and n_d_T: "no_dup (trail (fst T))"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_inv using full inv n_d unfolding full_def by blast+
  moreover have
    atms_cls_T: "atms_of_mm (clauses (fst T)) \<subseteq> atms_of_ms A" and
    atms_trail_T: "atm_of ` lits_of_l (trail (fst T)) \<subseteq> atms_of_ms A"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_bound_inv[of S T A] full atms_cls atms_trail fin inv n_d
    unfolding full_def by blast+
  ultimately have "no_step cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn (fst T)"
    apply -
    apply (rule no_step_cdcl\<^sub>N\<^sub>O\<^sub>T_restart_no_step_cdcl\<^sub>N\<^sub>O\<^sub>T[of _ A])
       using full unfolding full_def apply simp
      apply simp
    using fin apply simp
    done
  moreover have "all_decomposition_implies_m (clauses (fst T))
    (get_all_marked_decomposition (trail (fst T)))"
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_restart_all_decomposition_implies_m[of S T] inv n_d decomp
    full unfolding full_def by auto
  ultimately have "unsatisfiable (set_mset (clauses (fst T)))
    \<or> trail (fst T) \<Turnstile>asm clauses (fst T) \<and> satisfiable (set_mset (clauses (fst T)))"
    apply -
    apply (rule cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_final_state)
    using atms_cls_T atms_trail_T fin n_d_T fin inv_T by blast+
  then consider
      (unsat) "unsatisfiable (set_mset (clauses (fst T)))"
    | (sat) "trail (fst T) \<Turnstile>asm clauses (fst T)" and "satisfiable (set_mset (clauses (fst T)))"
    by auto
  then show "unsatisfiable (set_mset (clauses (fst S)))
    \<or> lits_of_l (trail (fst T)) \<Turnstile>sextm clauses (fst S) \<and> satisfiable (set_mset (clauses (fst S)))"
    proof cases
      case unsat
      then have "unsatisfiable (set_mset (clauses (fst S)))"
        unfolding satisfiable_def apply auto
        using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_restart_eq_sat_iff[of S T ] full inv n_d
        consistent_true_clss_ext_satisfiable true_clss_imp_true_cls_ext
        unfolding satisfiable_def full_def by blast
      then show ?thesis by blast
    next
      case sat
      then have "lits_of_l (trail (fst T)) \<Turnstile>sextm clauses (fst T)"
        using true_clss_imp_true_cls_ext by (auto simp: true_annots_true_cls)
      then have "lits_of_l (trail (fst T)) \<Turnstile>sextm clauses (fst S)"
        using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_restart_eq_sat_iff[of S T] full inv n_d unfolding full_def by blast
      moreover then have "satisfiable (set_mset (clauses (fst S)))"
        using consistent_true_clss_ext_satisfiable distinct_consistent_interp n_d_T by fast
      ultimately show ?thesis by fast
    qed
qed

corollary full_cdcl\<^sub>N\<^sub>O\<^sub>T_restart_normal_form_init_state:
  assumes
    init_state: "trail S = []" "clauses S = N" and
    full: "full cdcl\<^sub>N\<^sub>O\<^sub>T_restart (S, 0) T" and
    inv: "inv S"
  shows "unsatisfiable (set_mset N)
    \<or> lits_of_l (trail (fst T)) \<Turnstile>sextm N \<and> satisfiable (set_mset N)"
  using  full_cdcl\<^sub>N\<^sub>O\<^sub>T_restart_normal_form[of "(S, 0)" T] assms by auto

end

end
