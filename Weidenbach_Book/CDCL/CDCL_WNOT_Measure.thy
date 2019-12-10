chapter \<open>NOT's CDCL and DPLL\<close>

theory CDCL_WNOT_Measure
imports Weidenbach_Book_Base.WB_List_More
begin

text \<open>The organisation of the development is the following:
  \<^item> @{file CDCL_WNOT_Measure.thy} contains the measure used to show the termination the core of
  CDCL.
  \<^item> @{file CDCL_NOT.thy} contains the specification of the rules: the rules are
  defined, and we proof the correctness and termination for some strategies CDCL.
  \<^item> @{file DPLL_NOT.thy} contains the DPLL calculus based on the CDCL version.
  \<^item> @{file DPLL_W.thy} contains Weidenbach's version of DPLL and the proof of equivalence between
  the two DPLL versions.
\<close>

section \<open>Measure\<close>
text \<open>This measure show the termination of the core of CDCL: each step improves the number of
  literals we know for sure.

  This measure can also be seen as the increasing lexicographic order: it is an order on bounded
  sequences, when each element is bounded. The proof involves a measure like the one defined here
  (the same?).\<close>
definition \<mu>\<^sub>C :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat" where
"\<mu>\<^sub>C s b M \<equiv> (\<Sum>i=0..<length M. M!i * b^ (s +i - length M))"

lemma \<mu>\<^sub>C_Nil[simp]:
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
     by (rule sum.atLeastLessThan_concat[symmetric]) simp_all
  finally have "\<mu>\<^sub>C s b (L # M)= L * b ^ (s - 1 - length M)
                  + (\<Sum>i=1..<length (L#M). (L#M)!i * b^ (s +i - length (L#M)))"
     by auto
  moreover {
    have "(\<Sum>i=1..<length (L#M). (L#M)!i * b^ (s +i - length (L#M))) =
           (\<Sum>i=0..<length M. (L#M)!(Suc i) * b^ (s + (Suc i) - length (L#M)))"
     unfolding length_Cons set_sum_atLeastLessThan_Suc by blast
    also have "\<dots> = (\<Sum>i=0..<length M. M!i * b^ (s + i - length M))"
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
    by (auto intro!: sum.atLeastLessThan_concat[symmetric])
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
  shows "\<mu>\<^sub>C s b M \<ge> b ^ (s - length M)"
  using assms by (cases M) (auto simp: mult_eq_if \<mu>\<^sub>C_cons)

text \<open>Copy of @{file "~~/src/HOL/ex/NatSum.thy"} (but generalized to @{term "k\<ge>(0::nat)"})\<close>
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
      then have "\<mu>\<^sub>C s b M \<le> (\<Sum>i=0..<length M. (b-1) * b^ (s +i - length M))"
         using \<open>M\<noteq>[]\<close> \<open>b>0\<close> unfolding \<mu>\<^sub>C_def by (auto intro: sum_mono)
      also
        have "\<forall> i \<in> {0..<length M}. (b-1) * b^ (s +i - length M) = (b-1) * b^ i * b^(s - length M)"
          by (metis Nat.add_diff_assoc2 add.commute assms(4) mult.assoc power_add)
        then have "(\<Sum>i=0..<length M. (b-1) * b^ (s +i - length M))
          = (\<Sum>i=0..<length M. (b-1)* b^ i * b^(s - length M))"
          by (auto simp add: ac_simps)
      also have "\<dots> = (\<Sum>i=0..<length M. b^ i) * b^(s - length M) * (b-1)"
         by (simp add: sum_distrib_right sum_distrib_left ac_simps)
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
  fixes b :: nat
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

lemma finite_bounded_pair_list:
  fixes b :: nat
  shows "finite {(ys, xs). length xs < s \<and> length ys < s \<and>
    (\<forall>i< length xs. xs ! i < b) \<and> (\<forall>i< length ys. ys ! i < b)}"
proof -
  have H: "{(ys, xs). length xs < s \<and> length ys < s \<and>
    (\<forall>i< length xs. xs ! i < b) \<and> (\<forall>i< length ys. ys ! i < b)}
    \<subseteq>
    {xs. length xs < s \<and> (\<forall>i< length xs. xs ! i < b)} \<times>
    {xs. length xs < s \<and> (\<forall>i< length xs. xs ! i < b)}"
    by auto
  moreover have "finite {xs. length xs < s \<and> (\<forall>i< length xs. xs ! i < b)}"
    by (rule finite_bounded_list)
  ultimately show ?thesis by (auto simp: finite_subset)
qed

definition \<nu>NOT :: "nat \<Rightarrow> nat \<Rightarrow> (nat list \<times> nat list) set" where
"\<nu>NOT s base = {(ys, xs). length xs < s \<and> length ys < s \<and>
  (\<forall>i< length xs. xs ! i < base) \<and> (\<forall>i< length ys. ys ! i < base) \<and>
  (ys, xs) \<in> lenlex less_than}"

lemma finite_\<nu>NOT[simp]:
  "finite (\<nu>NOT s base)"
proof -
  have "\<nu>NOT s base \<subseteq> {(ys, xs). length xs < s \<and> length ys < s \<and>
    (\<forall>i< length xs. xs ! i < base) \<and> (\<forall>i< length ys. ys ! i < base)}"
    by (auto simp: \<nu>NOT_def)
  moreover have "finite {(ys, xs). length xs < s \<and> length ys < s \<and>
    (\<forall>i< length xs. xs ! i < base) \<and> (\<forall>i< length ys. ys ! i < base)}"
      by (rule finite_bounded_pair_list)
  ultimately show ?thesis by (auto simp: finite_subset)
qed

lemma acyclic_\<nu>NOT: "acyclic (\<nu>NOT s base)"
  apply (rule acyclic_subset[of "lenlex less_than" "\<nu>NOT s base"])
    apply (rule wf_acyclic)
  by (auto simp: \<nu>NOT_def)

lemma wf_\<nu>NOT: "wf (\<nu>NOT s base)"
  by (rule finite_acyclic_wf) (auto simp: acyclic_\<nu>NOT)

end
