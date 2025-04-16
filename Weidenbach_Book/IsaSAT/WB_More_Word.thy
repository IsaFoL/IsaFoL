theory WB_More_Word
  imports "Word_Lib.Many_More" Isabelle_LLVM.Bits_Natural
begin

lemma nat_uint_XOR: \<open>nat (uint (a XOR b)) = nat (uint a) XOR nat (uint b)\<close>
  if len: \<open>LENGTH('a) > 0\<close>
  for a b :: \<open>'a ::len Word.word\<close>
proof -
  have 1: \<open>uint ((word_of_int:: int \<Rightarrow> 'a Word.word)(uint a)) = uint a\<close>
    by (subst (2) word_of_int_uint[of a, symmetric]) (rule refl)
  have H: \<open>nat (bintrunc n (a XOR b)) = nat (bintrunc n a XOR bintrunc n b)\<close>
    if \<open>n> 0\<close> for n and a :: int and b :: int
    using that
  proof (induction n arbitrary: a b)
    case 0
    then show ?case by auto
  next
    case (Suc n) note IH = this(1) and Suc = this(2)
    then show ?case
      by (cases n) simp_all
  qed
  have \<open>nat (bintrunc LENGTH('a) (a XOR b)) = nat (bintrunc LENGTH('a) a XOR bintrunc LENGTH('a) b)\<close> for a b
    using len H[of \<open>LENGTH('a)\<close> a b] by auto
  then have \<open>nat (uint (a XOR b)) = nat (uint a XOR uint b)\<close>
    by transfer
  then show ?thesis
    unfolding xor_nat_def by auto
qed

lemma bitXOR_1_if_mod_2_int: \<open>L OR 1 = (if L mod 2 = 0 then L + 1 else L)\<close> for L :: int
  apply (rule bin_rl_eqI)
  unfolding bin_rest_OR bin_last_OR
  by (auto simp: )

lemma bitOR_1_if_mod_2_nat:
  \<open>L OR 1 = (if L mod 2 = 0 then L + 1 else L)\<close>
  \<open>L OR (Suc 0) = (if L mod 2 = 0 then L + 1 else L)\<close> for L :: nat
proof -
  have H: \<open>L OR 1 =  L + (if bin_last (int L) then 0 else 1)\<close>
    unfolding or_nat_def
    by (auto simp: or_nat_def bin_last_def xor_one_eq
      bitXOR_1_if_mod_2_int)
  show \<open>L OR 1 = (if L mod 2 = 0 then L + 1 else L)\<close>
    unfolding H
    by (auto simp: or_nat_def bin_last_def) presburger
  then show \<open>L OR (Suc 0) = (if L mod 2 = 0 then L + 1 else L)\<close>
    by simp
qed

lemma bin_pos_same_XOR3:
  \<open>a XOR a XOR c = c\<close>
  \<open>a XOR c XOR a = c\<close> for a c :: int
  by (metis bin_ops_same(3) int_xor_assoc int_xor_zero)+

lemma bin_pos_same_XOR3_nat:
  \<open>a XOR a XOR c = c\<close>
  \<open>a XOR c XOR a = c\<close> for a c :: nat
 unfolding xor_nat_def by (auto simp: bin_pos_same_XOR3)

end