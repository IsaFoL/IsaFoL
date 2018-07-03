theory IsaSAT_Arena
imports WB_Word_Assn
begin

definition bit_field_as_number where
  \<open>bit_field_as_number n xs \<longleftrightarrow> (\<forall>i < length xs. n !! i = xs ! i)\<close>

lemma \<open>i < length xs \<Longrightarrow> bit_field_as_number n xs \<Longrightarrow> bit_field_as_number (set_bit n i True) (xs [i := True])\<close>
  for n :: nat
  by (auto simp: bit_field_as_number_def test_bit_set_gen nat_set_bit_test_bit)

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