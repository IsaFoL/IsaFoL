theory IsaSAT_Arena
imports WB_Word_Assn
begin

definition bit_field_as_number where
  \<open>bit_field_as_number n xs \<longleftrightarrow> (\<forall>i < length xs. n !! i = xs ! i)\<close>

lemma nat_set_bit_0: \<open>set_bit x 0 b = nat ((bin_rest (int x)) BIT b)\<close> for x :: nat
  by (auto simp: int_set_bit_0 set_bit_nat_def)

lemma nat_test_bit0_iff: \<open>n !! 0 \<longleftrightarrow> n mod 2 = 1\<close> for n :: nat
proof -
  have 2: \<open>2 = int 2\<close>
    by auto
  have [simp]: \<open>int n mod 2 = 1 \<longleftrightarrow> n mod 2 = Suc 0\<close>
    unfolding 2 zmod_int[symmetric]
    by auto

  show ?thesis
    unfolding test_bit_nat_def
    by (auto simp: bin_last_def zmod_int)
qed
lemma test_bit_2: \<open>m > 0 \<Longrightarrow> (2*n) !! m \<longleftrightarrow> n !! (m - 1)\<close> for n :: nat
  by (cases m)
    (auto simp: test_bit_nat_def bin_rest_def)

lemma test_bit_Suc_2: \<open>m > 0 \<Longrightarrow> Suc (2 * n) !! m \<longleftrightarrow> (2 * n) !! m\<close> for n :: nat
  by (cases m)
    (auto simp: test_bit_nat_def bin_rest_def)

lemma bin_rest_prev_eq:
  assumes [simp]: \<open>m > 0\<close>
  shows  \<open>nat ((bin_rest (int w))) !! (m - Suc (0::nat)) = w !! m\<close>
proof -
  define m' where \<open>m' = w div 2\<close>
  have w: \<open>w = 2 * m' \<or> w = Suc (2 * m')\<close>
    unfolding m'_def
    by auto
  moreover have \<open>bin_nth (int m') (m - Suc 0) = m' !! (m - Suc 0)\<close>
    unfolding test_bit_nat_def test_bit_int_def ..
  ultimately show ?thesis
    by (auto simp: bin_rest_def test_bit_2 test_bit_Suc_2)
qed

lemma bin_sc_ge0: \<open>w >= 0 ==> (0::int) \<le> bin_sc n b w\<close>
  by (induction n arbitrary: w) auto

lemma \<open>nat (bin_sc n True (bin_rest (int w))) !! n = nat (bin_sc n True (int w)) !! n\<close>

  oops
lemma \<open>set_bit w n x !! m = (if m = n then x else w !! m)\<close> for w n :: nat
  supply [[show_types]]
  apply (induction n arbitrary: w)
  subgoal for w
    by (cases x)
      (auto simp: nat_test_bit0_iff Bit_B0 BIT_bin_simps nat_mult_distrib
            Bit_B1 int_set_bit_0 nat_set_bit_0 nat_add_distrib test_bit_2
              test_bit_Suc_2 bin_rest_prev_eq)
  subgoal for n w
    unfolding set_bit_nat_def
    apply (cases x; cases \<open>bin_last (int w)\<close>)
    apply (auto simp: Bit_B0 Bit_B1 nat_add_distrib bin_sc_ge0  test_bit_2
              test_bit_Suc_2 bin_rest_prev_eq nat_mult_distrib
              nat_test_bit0_iff Bit_B0 BIT_bin_simps nat_mult_distrib
            Bit_B1 int_set_bit_0 nat_set_bit_0 nat_add_distrib test_bit_2
              test_bit_Suc_2 bin_rest_prev_eq)
    apply (subst test_bit_Suc_2)
    try0
    oops
find_theorems "nat ( _ + _)"

    apply (cases x)
    apply (auto simp: nat_test_bit0_iff Bit_B0 BIT_bin_simps nat_mult_distrib
            Bit_B1 int_set_bit_0 nat_set_bit_0 nat_add_distrib test_bit_2
              test_bit_Suc_2 bin_rest_prev_eq test_bit_int_def test_bit_nat_def
              )
    sorry
unfolding set_bit_nat_def
apply transfer

  apply (unfold word_size word_test_bit_def word_set_bit_def)
  apply (clarsimp simp add: word_ubin.eq_norm nth_bintr bin_nth_sc_gen)
  apply (auto elim!: test_bit_size [unfolded word_size]
      simp add: word_test_bit_def [symmetric])
  unfolding set_bit_nat_def

  apply (induction n)
  apply auto
  apply (auto simp: nat_test_bit0_iff Bit_B0 BIT_bin_simps
          Bit_B1 int_set_bit_0 nat_set_bit_0 nat_add_distrib)
  sorry
  subgoal
  apply (cases x)
    apply (auto simp: bin_rest_def zdiv_zmult2_eq[symmetric] Bit_B0 BIT_bin_simps
          Bit_B1 int_set_bit_0 nat_set_bit_0 nat_add_distrib)
  oops
  find_theorems " nat ( _ + _)"
  apply transfer
  supply [[show_types]]
  subgoal for w n x m
    unfolding test_bit_set_gen
    sorry
    oops
    thm bin_sc.simps
    find_theorems  "set_bit _ 0"
   apply (auto simp: bit_field_as_number_def test_bit_set_gen)
  oops
lemma \<open>i < length xs \<Longrightarrow> bit_field_as_number n xs \<Longrightarrow> bit_field_as_number (set_bit i n True) (xs [i := True])\<close>
  apply (auto simp: bit_field_as_number_def test_bit_set_gen)
  sorry
find_theorems " (set_bit _ _ _ ) !! _ "
definition extra_information where
  \<open>extra_information st cl = (\<lambda>(ex, l, lbd, act, bl).
     ex < 16 \<and>
     ((ex AND 2 >> 32) = 2 \<longrightarrow> st = DELETED) \<and>
     ((ex AND 3 >> 32) = 4 \<longrightarrow> st = INIT) \<and>
     ((ex AND 3 >> 32) = 0 \<longrightarrow> st = LEARNED) \<and>
     (ex AND 1 >> 32) + l = length cl \<and>
     (length cl > 2 \<longrightarrow> bl \<ge> 2) \<and>
     bl < length cl)\<close>

definition extra_information_mark_to_delete :: \<open>nat \<Rightarrow> nat list \<Rightarrow> nat list\<close> where
  \<open>extra_information_mark_to_delete C mem =
      mem[C - 5 := set_bit (mem ! (C - 5)) 2 False]\<close>

(*
lemma \<open>a \<le> 4294967295 \<Longrightarrow> set_bit a 2 False = a AND 0xFFFFFFFB\<close> for a :: nat
proof -
  have \<open>int a = 8 * (int a div 8) + (if bin_last (int a) then 1 else 0) +
        (if bin_last (int a div 2) then 2 else 0)\<close>
    apply (auto simp: bin_last_def)
    try0
    sorry
  show ?thesis
    unfolding set_bit_nat_def bitAND_nat_def
    apply (cases \<open>bin_last (int a)\<close>; cases \<open>bin_last (int a div 2)\<close>)
       apply (auto simp: bin_rest_def zdiv_zmult2_eq[symmetric] Bit_B0 BIT_bin_simps
        Bit_B1)

  subgoal for a
  apply transfer

  unfolding bitAND_nat_def
  apply auto *)


value \<open>(2::nat) ^ 32 - 1\<close>
term set_digit

inductive arena where
init:
  \<open>arena [] fmempty {#}\<close> |
add_clause:
  \<open>arena (mem @ pad @ ex # l # lbd # act # bl # cl) 
      (fmupd (length (mem @ pad @ ex # l # lbd # act # [bl])) (st, cl) N)
      (add_mset (length (mem @ pad @ ex # l # lbd # act # [bl])) vdom)\<close>
  if
    \<open>arena mem N vdom\<close> and
    \<open>extra_information st cl (ex, l, lbd, act, bl)\<close> |
remove_clause:
  \<open>arena mem 
      (fmdrop C N)
      vdom\<close>
  if
    \<open>arena mem N vdom\<close> and
    \<open>C \<in># dom_m N\<close>


lemma arena_ge5:
  \<open>arena mem N vdom \<Longrightarrow> i \<in># vdom \<Longrightarrow> i \<ge> 5\<close>
  by (induction rule: arena.induct) auto

lemma
  \<open>arena mem N vdom \<longleftrightarrow>
     (\<forall>C \<in># vdom. C \<in># dom)\<close>
end