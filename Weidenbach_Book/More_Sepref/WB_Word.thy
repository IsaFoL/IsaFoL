theory WB_Word
  imports
    "HOL-Library.Word"
    "Native_Word.Uint64"
    "Native_Word.Uint32"
    WB_More_Refinement
    "HOL-Imperative_HOL.Heap"
    Collections.HashCode
    "Isabelle_LLVM.Bits_Natural"
    Native_Word.Native_Word_Imperative_HOL
    Native_Word.Code_Target_Bits_Int Native_Word.Uint32 Native_Word.Uint64
begin

lemma less_upper_bintrunc_id: \<open>n < 2 ^b \<Longrightarrow> n \<ge> 0 \<Longrightarrow> bintrunc b n = n\<close>
  unfolding uint32_of_nat_def
  by (simp add: no_bintr_alt1)

definition word_nat_rel :: "('a :: len Word.word \<times> nat) set" where
  \<open>word_nat_rel = br unat (\<lambda>_. True)\<close>


lemma bintrunc_eq_bits_eqI: \<open> (\<And>n. (n < r \<and> bin_nth c n) = (n < r \<and> bin_nth a n)) \<Longrightarrow>
       bintrunc r (a) = bintrunc r c\<close>
proof (induction r arbitrary: a c)
  case 0
  then show ?case by simp
next
  case (Suc r a c) note IH = this(1) and eq = this(2)
  have 1: \<open>(n < r \<and> bin_nth (bin_rest a) n) = (n < r \<and> bin_nth (bin_rest c) n)\<close> for n
    using eq[of \<open>Suc n\<close>] eq[of 1] by (clarsimp simp flip: bit_Suc)
  show ?case
    using IH[OF 1] eq[of 0] by (simp add: mod2_eq_if take_bit_Suc)
qed

lemma and_eq_bits_eqI: \<open>(\<And>n. c !! n = (a !! n \<and> b !! n))\<Longrightarrow> a AND b = c\<close> for a b c :: \<open>_ word\<close>
  by transfer
    (rule bintrunc_eq_bits_eqI, auto simp add: bin_nth_ops)


lemma pow2_mono_word_less:
   \<open>m < LENGTH('a) \<Longrightarrow> n < LENGTH('a) \<Longrightarrow> m < n \<Longrightarrow> (2 :: 'a :: len word) ^m  < 2 ^ n\<close>
proof (induction n arbitrary: m)
  case 0
  then show ?case by auto
next
  case (Suc n m) note IH = this(1) and le = this(2-)
  have [simp]: \<open>nat (bintrunc LENGTH('a) (2::int)) = 2\<close>
    by (metis add_lessD1 le(2) plus_1_eq_Suc power_one_right uint_bintrunc unat_def unat_p2)
  have 1: \<open>unat ((2 :: 'a word) ^ n) \<le> (2 :: nat) ^ n\<close>
    by (metis Suc.prems(2) eq_imp_le le_SucI linorder_not_less unat_p2)
  have 2: \<open>unat ((2 :: 'a word)) \<le> (2 :: nat)\<close>
     by (metis le_unat_uoi nat_le_linear of_nat_numeral)
  have \<open>unat (2 :: 'a word) * unat ((2 :: 'a word) ^ n) \<le> (2 :: nat) ^ Suc n\<close>
    using mult_le_mono[OF 2 1] by auto
  also have \<open>(2 :: nat) ^ Suc n < (2 :: nat) ^ LENGTH('a)\<close>
    using le(2) by (metis unat_lt2p unat_p2)
  finally have \<open>unat (2 :: 'a word) * unat ((2 :: 'a word) ^ n) < 2 ^ LENGTH('a)\<close>
     .
  then have [simp]: \<open>unat (2 * (2 :: 'a word) ^ n) = unat (2 :: 'a word) * unat ((2 :: 'a word) ^ n)\<close>
    using unat_mult_lem[of \<open>2 :: 'a word\<close> \<open>(2 :: 'a word) ^ n\<close>]
    by auto
  have [simp]: \<open>(0::nat) < unat ((2::'a word) ^ n)\<close>
    by (simp add: Suc_lessD le(2) unat_p2)

  show ?case
    using IH(1)[of m] le(2-)
    apply (auto simp: less_Suc_eq word_less_nat_alt
      simp del: unat_lt2p)
    by (metis le(3) one_less_numeral_iff power_Suc power_strict_increasing_iff semiring_norm(76))
qed

lemma pow2_mono_word_le:
  \<open>m < LENGTH('a) \<Longrightarrow> n < LENGTH('a) \<Longrightarrow> m \<le> n \<Longrightarrow> (2 :: 'a :: len word) ^m  \<le> 2 ^ n\<close>
  using pow2_mono_word_less[of m n, where 'a = 'a]
  by (cases \<open>m = n\<close>) auto

definition uint32_max :: nat where
  \<open>uint32_max = 2 ^32 - 1\<close>

lemma unat_le_uint32_max_no_bit_set:
  fixes n :: \<open>'a::len word\<close>
  assumes less: \<open>unat n \<le> uint32_max\<close> and
    n: \<open>n !! na\<close> and
    32: \<open>32 < LENGTH('a)\<close>
  shows \<open>na < 32\<close>
proof (rule ccontr)
  assume H: \<open>\<not> ?thesis\<close>
  have na_le: \<open>na < LENGTH('a)\<close>
    using test_bit_bin[THEN iffD1, OF n]
    by auto
  have \<open>(2 :: nat) ^ 32 < (2 :: nat) ^ LENGTH('a)\<close>
    using 32 power_strict_increasing_iff rel_simps(49) semiring_norm(76) by blast
  then have [simp]: \<open>(4294967296::nat) mod (2::nat) ^ LENGTH('a) = (4294967296::nat)\<close>
    by (auto simp:  word_le_nat_alt unat_numeral uint32_max_def
      simp del: unat_bintrunc)
  have \<open>(2 :: 'a word) ^ na \<ge> 2 ^ 32\<close>
    using pow2_mono_word_le[OF 32 na_le] H by auto
  also have \<open>n \<ge> (2 :: 'a word) ^ na\<close>
    using assms
    unfolding uint32_max_def
    by (auto dest!: bang_is_le)
  finally have \<open>unat n > uint32_max\<close>
      supply [[show_sorts]]
    unfolding word_le_nat_alt
    by (auto simp:  word_le_nat_alt unat_numeral uint32_max_def
      simp del: unat_bintrunc semiring_1_class.unsigned_numeral)

   then show False
    using less by auto
qed

definition uint32_max' where
  [simp, symmetric, code]: \<open>uint32_max' = uint32_max\<close>

lemma [code]: \<open>uint32_max' = 4294967295\<close>
  by (auto simp: uint32_max_def)


text \<open>This lemma is very trivial but maps an \<^typ>\<open>64 word\<close> to its list counterpart. This
  especially allows to combine two numbers together via ther bit representation (which should be
  faster than enumerating all numbers).
\<close>
lemma ex_rbl_word64:
   \<open>\<exists>a64 a63 a62 a61 a60 a59 a58 a57 a56 a55 a54 a53 a52 a51 a50 a49 a48 a47 a46 a45 a44 a43 a42 a41
     a40 a39 a38 a37 a36 a35 a34 a33 a32 a31 a30 a29 a28 a27 a26 a25 a24 a23 a22 a21 a20 a19 a18 a17
     a16 a15 a14 a13 a12 a11 a10 a9 a8 a7 a6 a5 a4 a3 a2 a1.
     to_bl (n :: 64 word) =
         [a64, a63, a62, a61, a60, a59, a58, a57, a56, a55, a54, a53, a52, a51, a50, a49, a48, a47,
          a46, a45, a44, a43, a42, a41, a40, a39, a38, a37, a36, a35, a34, a33, a32, a31, a30, a29,
          a28, a27, a26, a25, a24, a23, a22, a21, a20, a19, a18, a17, a16, a15, a14, a13, a12, a11,
          a10, a9, a8, a7, a6, a5, a4, a3, a2, a1]\<close> (is ?A) and
  ex_rbl_word64_le_uint32_max:
    \<open>unat n \<le> uint32_max \<Longrightarrow> \<exists>a31 a30 a29 a28 a27 a26 a25 a24 a23 a22 a21 a20 a19 a18 a17 a16 a15
        a14 a13 a12 a11 a10 a9 a8 a7 a6 a5 a4 a3 a2 a1 a32.
      to_bl (n :: 64 word) =
      [False, False, False, False, False, False, False, False, False, False, False, False, False,
       False, False, False, False, False, False, False, False, False, False, False, False, False,
       False, False, False, False, False, False,
        a32, a31, a30, a29, a28, a27, a26, a25, a24, a23, a22, a21, a20, a19, a18, a17, a16, a15,
        a14, a13, a12, a11, a10, a9, a8, a7, a6, a5, a4, a3, a2, a1]\<close> (is \<open>_ \<Longrightarrow> ?B\<close>) and
  ex_rbl_word64_ge_uint32_max:
    \<open>n AND (2^32 - 1) = 0 \<Longrightarrow> \<exists>a64 a63 a62 a61 a60 a59 a58 a57 a56 a55 a54 a53 a52 a51 a50 a49 a48
      a47 a46 a45 a44 a43 a42 a41 a40 a39 a38 a37 a36 a35 a34 a33.
      to_bl (n :: 64 word) =
      [a64, a63, a62, a61, a60, a59, a58, a57, a56, a55, a54, a53, a52, a51, a50, a49, a48, a47,
          a46, a45, a44, a43, a42, a41, a40, a39, a38, a37, a36, a35, a34, a33,
        False, False, False, False, False, False, False, False, False, False, False, False, False,
        False, False, False, False, False, False, False, False, False, False, False, False, False,
        False, False, False, False, False, False]\<close> (is \<open>_ \<Longrightarrow> ?C\<close>)
proof -
  have [simp]: "n > 0 \<Longrightarrow> length xs = n \<longleftrightarrow>
     (\<exists>y ys. xs = y # ys \<and> length ys = n - 1)" for ys n xs
    by (cases xs) auto
  show H: ?A
    using word_bl_Rep'[of n]
    by (auto simp del: word_bl_Rep')

  show ?B  if \<open>unat n \<le> uint32_max\<close>
  proof -
    have H': \<open>m \<ge> 32 \<Longrightarrow> \<not>n !! m\<close> for m
      using unat_le_uint32_max_no_bit_set[of n m, OF that] by auto
    show ?thesis using that H'[of 64] H'[of 63] H'[of 62] H'[of 61] H'[of 60] H'[of 59] H'[of 58]
      H'[of 57] H'[of 56] H'[of 55] H'[of 54] H'[of 53] H'[of 52] H'[of 51] H'[of 50] H'[of 49]
      H'[of 48] H'[of 47] H'[of 46] H'[of 45] H'[of 44] H'[of 43] H'[of 42] H'[of 41] H'[of 40]
      H'[of 39] H'[of 38] H'[of 37] H'[of 36] H'[of 35] H'[of 34] H'[of 33] H'[of 32]
      H'[of 31]
      using H unfolding unat_def
      by (clarsimp simp add: test_bit_bl word_size)
  qed
  show ?C if \<open>n AND (2^32 - 1) = 0\<close>
  proof -
    note H' =  test_bit_bl[of \<open>n AND (2^32 - 1)\<close> m for m, unfolded word_size, simplified]
    have H''[simp]: \<open>(n AND 4294967295) !! m = False\<close> for m
      using that by auto
    have H'':\<open>rev (to_bl (n && 0xFFFFFFFF)) ! m = False\<close> if \<open>m < 64\<close> for m
      using test_bit_bl[of \<open>n && 0xFFFFFFFF\<close> \<open>m\<close>]
      apply (simp only: word_size H'')
      apply (clarsimp simp add: that)
      done
    show ?thesis
      using H H'[of 0]
      H'[of 32] H'[of 31] H'[of 30] H'[of 29] H'[of 28] H'[of 27] H'[of 26] H'[of 25] H'[of 24]
      H'[of 23] H'[of 22] H'[of 21] H'[of 20] H'[of 19] H'[of 18] H'[of 17] H'[of 16] H'[of 15]
      H'[of 14] H'[of 13] H'[of 12] H'[of 11] H'[of 10] H'[of 9] H'[of 8] H'[of 7] H'[of 6]
      H'[of 5] H'[of 4] H'[of 3] H'[of 2] H'[of 1]
      unfolding unat_def word_size H''
      apply (simp only: H'')
      unfolding test_bit_bl
      by (clarsimp simp add: word_size bl_word_and word_add_rbl
            simp del: test_bit_bl)
  qed
qed


subsubsection \<open>32-bits\<close>

lemma word_nat_of_uint32_Rep_inject[simp]: \<open>nat_of_uint32 ai = nat_of_uint32 bi \<longleftrightarrow> ai = bi\<close>
  by transfer simp

lemma nat_of_uint32_012[simp]: \<open>nat_of_uint32 0 = 0\<close> \<open>nat_of_uint32 2 = 2\<close> \<open>nat_of_uint32 1 = 1\<close>
  unfolding nat_of_uint32.rep_eq
  by (auto simp: one_uint32.rep_eq zero_uint32.rep_eq)

lemma nat_of_uint32_3: \<open>nat_of_uint32 3 = 3\<close>
  unfolding nat_of_uint32.rep_eq
  by (auto simp: one_uint32.rep_eq zero_uint32.rep_eq)

lemma nat_of_uint32_Suc03_iff:
 \<open>nat_of_uint32 a = Suc 0 \<longleftrightarrow> a = 1\<close>
   \<open>nat_of_uint32 a = 3 \<longleftrightarrow> a = 3\<close>
   using word_nat_of_uint32_Rep_inject nat_of_uint32_3 by fastforce+

lemma   nat_of_uint32_013_neq:
  "(1::uint32) \<noteq> (0 :: uint32)" "(0::uint32) \<noteq> (1 :: uint32)"
  "(3::uint32) \<noteq> (0 :: uint32)"
  "(3::uint32) \<noteq> (1 :: uint32)"
  "(0::uint32) \<noteq> (3 :: uint32)"
  "(1::uint32) \<noteq> (3 :: uint32)"
  by (auto dest: arg_cong[of _ _ nat_of_uint32] simp: nat_of_uint32_3)

definition uint32_nat_rel :: "(uint32 \<times> nat) set" where
  \<open>uint32_nat_rel = br nat_of_uint32 (\<lambda>_. True)\<close>

lemma unat_shiftr: \<open>unat (xi >> n) = unat xi div (2^n)\<close>
proof -
  have [simp]: \<open>nat (2 * 2 ^ n) =  2 * 2 ^ n\<close> for n :: nat
    by (metis nat_numeral nat_power_eq power_Suc rel_simps(27))
  show ?thesis
    unfolding unat_def
    by (induction n arbitrary: xi) (auto simp: shiftr_div_2n nat_div_distrib)
qed

instantiation uint32 :: default
begin
definition default_uint32 :: uint32 where
  \<open>default_uint32 = 0\<close>
instance
  ..
end

instance uint32 :: heap
  by standard (auto simp: inj_def exI[of _ nat_of_uint32])

instance uint32 :: semiring_numeral
  by standard


instantiation uint32 :: hashable
begin
definition hashcode_uint32 :: \<open>uint32 \<Rightarrow> uint32\<close> where
  \<open>hashcode_uint32 n = n\<close>

definition def_hashmap_size_uint32 :: \<open>uint32 itself \<Rightarrow> nat\<close> where
  \<open>def_hashmap_size_uint32 = (\<lambda>_. 16)\<close>
  \<comment> \<open>same as @{typ nat}\<close>
instance
  by standard (simp add: def_hashmap_size_uint32_def)
end

abbreviation uint32_rel :: \<open>(uint32 \<times> uint32) set\<close> where
  \<open>uint32_rel \<equiv> Id\<close>

lemma nat_bin_trunc_ao:
  \<open>nat (bintrunc n a) AND nat (bintrunc n b) = nat (bintrunc n (a AND b))\<close>
  \<open>nat (bintrunc n a) OR nat (bintrunc n b) = nat (bintrunc n (a OR b))\<close>
  unfolding and_nat_def or_nat_def
  by simp_all

lemma nat_of_uint32_ao:
  \<open>nat_of_uint32 n AND nat_of_uint32 m = nat_of_uint32 (n AND m)\<close>
  \<open>nat_of_uint32 n OR nat_of_uint32 m = nat_of_uint32 (n OR m)\<close>
  subgoal apply (transfer, unfold unat_def, transfer, unfold nat_bin_trunc_ao) ..
  subgoal apply (transfer, unfold unat_def, transfer, unfold nat_bin_trunc_ao) ..
  done

lemma nat_of_uint32_mult: \<open>nat_of_uint32 (a * b) = nat_of_uint32 a * nat_of_uint32 b mod 2 ^ 32\<close>
  by (simp add: nat_of_uint32_def uint32.word_of_mult unat_word_ariths)

lemma nat_of_uint32_le:
  \<open>nat_of_uint32 n < 2^32\<close>
  using unat_lt2p[of \<open>Rep_uint32 n\<close>] unfolding nat_of_uint32_def
  by auto

lemma even_even_mod_2power_iff: \<open>k> 1 \<Longrightarrow> even (n mod 2^k) \<longleftrightarrow> even n\<close>
  apply (induction k)
  apply auto
  apply (metis div_mult_mod_eq dvd_add_left_iff dvd_triv_left even_mult_iff)
  by (metis div_mult_mod_eq dvd_triv_left even_add even_mult_iff)
 
lemma even_nat_of_uint32_iff[simp]: \<open>even (nat_of_uint32 n) = even n\<close> (is \<open>?A \<longleftrightarrow> ?B\<close>)
proof
  assume ?A
  then obtain k where n: \<open>nat_of_uint32 n = 2 * k\<close>
    by (auto simp: dvd_def)
  then have [simp]: \<open>nat_of_uint32 (uint32_of_nat k) = k\<close>
    apply (auto simp: nat_of_uint32_def uint32_of_nat_def uint32.word_of_word
      unat_of_nat_eq)
    by (metis Suc_1 Suc_mult_cancel1 \<open>even (nat_of_uint32 n)\<close> dvd_mult_div_cancel n uno_simps(2))
  have [simp]: \<open>k < 2147483648\<close>
    using n nat_of_uint32_le[of n] by auto
  have \<open>n = 2 * uint32_of_nat k\<close>
    using n
    by (subst word_nat_of_uint32_Rep_inject[symmetric])
     (simp add: uint32.word_of_mult nat_of_uint32_mult eq_mod_iff mod_less)
  then show ?B
    unfolding dvd_def by fast
next
  assume ?B
  then obtain k where n: \<open>n = 2 * k\<close>
    by (auto simp: dvd_def)
  then show ?A
    using even_even_mod_2power_iff[of 32 \<open>2 * nat_of_uint32 k\<close>]
    by (auto simp: nat_of_uint32_mult)
qed

lemma nat_of_uint32_mod_2:
  \<open>nat_of_uint32 L mod 2 = nat_of_uint32 (L mod 2)\<close>
  by (simp del: nat_uint_eq add: mod2_eq_if unat_def nat_mod_distrib uint_mod)

lemmas bitAND_1_mod_2_uint32 = and_one_eq[of \<open>L::uint32\<close> for L]

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


lemma nat_of_uint32_XOR: \<open>nat_of_uint32 (a XOR b) = nat_of_uint32 a XOR nat_of_uint32 b\<close>
  by transfer (simp add: unat_def nat_uint_XOR del: nat_uint_eq)

lemma nat_of_uint32_0_iff: \<open>nat_of_uint32 xi = 0 \<longleftrightarrow> xi = 0\<close> for xi
  by transfer (auto simp: unat_def uint_0_iff simp del: nat_uint_eq)

lemma nat_0_AND: \<open>0 AND n = 0\<close> for n :: nat
  unfolding and_nat_def by auto

lemma uint32_0_AND: \<open>0 AND n = 0\<close> for n :: uint32
  by transfer auto

definition uint32_safe_minus where
  \<open>uint32_safe_minus m n = (if m < n then 0 else m - n)\<close>

lemma nat_of_uint32_le_minus: \<open>ai \<le> bi \<Longrightarrow> 0 = nat_of_uint32 ai - nat_of_uint32 bi\<close>
  by transfer (auto simp: unat_def word_le_def simp del: nat_uint_eq)

lemma nat_of_uint32_notle_minus:
  \<open>\<not> ai < bi \<Longrightarrow>
       nat_of_uint32 (ai - bi) = nat_of_uint32 ai - nat_of_uint32 bi\<close>
  apply transfer
  unfolding unat_def
  by (subst uint_sub_lem[THEN iffD1])
    (auto simp: unat_def uint_nonnegative nat_diff_distrib word_le_def[symmetric] intro: leI
    simp del: nat_uint_eq)

lemmas [simp] = uint32.word_of_word
lemma nat_of_uint32_uint32_of_nat_id: \<open>n \<le> uint32_max \<Longrightarrow> nat_of_uint32 (uint32_of_nat n) = n\<close>
  unfolding uint32_of_nat_def uint32_max_def nat_of_uint32_def
  by (simp add: unat_of_nat_eq)


lemma uint32_less_than_0[iff]: \<open>(a::uint32) \<le> 0 \<longleftrightarrow> a = 0\<close>
  by transfer auto

lemma nat_of_uint32_less_iff: \<open>nat_of_uint32 a < nat_of_uint32 b \<longleftrightarrow> a < b\<close>
  apply transfer
  apply (auto simp: unat_def word_less_def  simp del: nat_uint_eq)
  apply transfer
  by (smt bintr_ge0)

lemma nat_of_uint32_le_iff: \<open>nat_of_uint32 a \<le> nat_of_uint32 b \<longleftrightarrow> a \<le> b\<close>
  apply transfer
  by (auto simp: unat_def word_less_def nat_le_iff word_le_def  simp del: nat_uint_eq)

lemma nat_of_uint32_max:
  \<open>nat_of_uint32 (max ai bi) = max (nat_of_uint32 ai) (nat_of_uint32 bi)\<close>
  by (auto simp: max_def nat_of_uint32_le_iff split: if_splits)

lemma mult_mod_mod_mult:
   \<open>b < n div a \<Longrightarrow> a > 0 \<Longrightarrow> b > 0 \<Longrightarrow> a * b mod n = a * (b mod n)\<close> for a b n :: int
  apply (subst int_mod_eq')
  subgoal using not_le zdiv_mono1 by fastforce
  subgoal using not_le zdiv_mono1 by fastforce
  subgoal
    apply (subst int_mod_eq')
    subgoal by auto
    subgoal by (metis (full_types) le_cases not_le order_trans pos_imp_zdiv_nonneg_iff zdiv_le_dividend)
    subgoal by auto
    done
  done

lemma nat_of_uint32_distrib_mult2:
  assumes \<open>nat_of_uint32 xi \<le> uint32_max div 2\<close>
  shows \<open>nat_of_uint32 (2 * xi) = 2 * nat_of_uint32 xi\<close>
proof -
  have H: \<open>\<And>xi::32 Word.word. nat (uint xi) < (2147483648::nat) \<Longrightarrow>
       nat (uint xi mod (4294967296::int)) = nat (uint xi)\<close>
  proof -
    fix xia :: "32 Word.word"
    assume a1: "nat (uint xia) < 2147483648"
    have f2: "\<And>n. (numeral n::nat) \<le> numeral (num.Bit0 n)"
      by (metis (no_types) add_0_right add_mono_thms_linordered_semiring(1)
          dual_order.order_iff_strict numeral_Bit0 rel_simps(51))
    have "unat xia \<le> 4294967296"
      using a1 by (metis (no_types) add_0_right add_mono_thms_linordered_semiring(1)
          dual_order.order_iff_strict nat_int numeral_Bit0 rel_simps(51) uint_nat)
    then show "nat (uint xia mod 4294967296) = nat (uint xia)"
      using f2 a1 by (auto simp: nat_mod_distrib)
  qed
  have [simp]: \<open>xi \<noteq> (0::32 Word.word) \<Longrightarrow> (0::int) < uint xi\<close> for xi
    by (metis unsigned_0 word_less_iff_unsigned word_neq_0_conv)
  show ?thesis
    using assms unfolding uint32_max_def nat_of_uint32_def
    by (simp add: uint32.word_of_mult unat_word_ariths)
qed

lemma nat_of_uint32_distrib_mult2_plus1:
  assumes \<open>nat_of_uint32 xi \<le> uint32_max div 2\<close>
  shows \<open>nat_of_uint32 (2 * xi + 1) = 2 * nat_of_uint32 xi + 1\<close>
proof -
  have mod_is_id: \<open>\<And>xi::32 Word.word. nat (uint xi) < (2147483648::nat) \<Longrightarrow>
      (uint xi mod (4294967296::int)) = uint xi\<close>
    by (subst mod_pos_pos_trivial)
     (auto  simp del: nat_uint_eq)
  have [simp]: \<open>xi \<noteq> (0::32 Word.word) \<Longrightarrow> (0::int) < uint xi\<close> for xi
    by (metis not_less of_int_0 uint_le_0_iff word_of_int_uint)
  show ?thesis
    using assms unfolding uint32_max_def nat_of_uint32_def
    by (simp add: uint32.word_of_mult uint32.word_of_add unat_word_ariths one_uint32.rep_eq)
qed


lemma nat_of_uint32_add:
  \<open>nat_of_uint32 ai + nat_of_uint32 bi \<le> uint32_max \<Longrightarrow>
    nat_of_uint32 (ai + bi) = nat_of_uint32 ai + nat_of_uint32 bi\<close>
  by transfer (auto simp: unat_def uint_plus_if' nat_add_distrib uint32_max_def simp del: nat_uint_eq)

definition zero_uint32_nat where
  [simp]: \<open>zero_uint32_nat = (0 :: nat)\<close>

definition one_uint32_nat where
  [simp]: \<open>one_uint32_nat = (1 :: nat)\<close>

definition two_uint32_nat where [simp]: \<open>two_uint32_nat = (2 :: nat)\<close>

definition two_uint32 where
  [simp]: \<open>two_uint32 = (2 :: uint32)\<close>

definition fast_minus :: \<open>'a::{minus} \<Rightarrow> 'a \<Rightarrow> 'a\<close> where
  [simp]: \<open>fast_minus m n = m - n\<close>

definition fast_minus_code :: \<open>'a::{minus,ord} \<Rightarrow> 'a \<Rightarrow> 'a\<close> where
  [simp]: \<open>fast_minus_code m n = (SOME p. (p = m - n \<and> m \<ge> n))\<close>

definition fast_minus_nat :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  [simp, code del]: \<open>fast_minus_nat = fast_minus_code\<close>

definition fast_minus_nat' :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  [simp, code del]: \<open>fast_minus_nat' = fast_minus_code\<close>

lemma [code]: \<open>fast_minus_nat = fast_minus_nat'\<close>
  unfolding fast_minus_nat_def fast_minus_nat'_def ..

lemma word_of_int_int_unat[simp]: \<open>word_of_int (int (unat x)) = x\<close>
  unfolding unat_def
  apply transfer
  by (simp add: bintr_ge0)

lemma uint32_of_nat_nat_of_uint32[simp]: \<open>uint32_of_nat (nat_of_uint32 x) = x\<close>
  unfolding uint32_of_nat_def
  by simp
    (metis Rep_uint32_inverse nat_of_uint32.abs_eq word_unat.Rep_inverse)


definition sum_mod_uint32_max where
  \<open>sum_mod_uint32_max a b = (a + b) mod (uint32_max + 1)\<close>

lemma nat_of_uint32_plus:
  \<open>nat_of_uint32 (a + b) = (nat_of_uint32 a + nat_of_uint32 b) mod (uint32_max + 1)\<close>
  by transfer (auto simp: unat_word_ariths uint32_max_def)

definition one_uint32 where
  \<open>one_uint32 = (1::uint32)\<close>

  text \<open>This lemma is meant to be used to simplify expressions like \<^term>\<open>nat_of_uint32 5\<close> and therefore
we add the bound explicitely instead of keeping \<^term>\<open>uint32_max\<close>.
Remark the types are non trivial here: we convert a \<^typ>\<open>uint32\<close> to a \<^typ>\<open>nat\<close>, even if the
experession \<^term>\<open>numeral n\<close> looks the same.\<close>
lemma nat_of_uint32_numeral[simp]:
  \<open>numeral n \<le> ((2 ^32 - 1)::nat) \<Longrightarrow> nat_of_uint32 (numeral n) = numeral n\<close>
proof (induction n)
 case One
  then show ?case by auto
next
  case (Bit0 n) note IH = this(1)[unfolded uint32_max_def[symmetric]] and le = this(2)
  define m :: nat where \<open>m \<equiv> numeral n\<close>
  have n_le: \<open>numeral n \<le> uint32_max\<close>
    using le
    by (subst (asm) numeral.numeral_Bit0) (auto simp: m_def[symmetric] uint32_max_def)
  have n_le_div2: \<open>nat_of_uint32 (numeral n) \<le> uint32_max div 2\<close>
    apply (subst IH[OF n_le])
    using le by (subst (asm) numeral.numeral_Bit0) (auto simp: m_def[symmetric] uint32_max_def)

  have \<open>nat_of_uint32 (numeral (num.Bit0 n)) = nat_of_uint32 (2 * numeral n)\<close>
    by (subst numeral.numeral_Bit0)
      (metis comm_monoid_mult_class.mult_1 distrib_right_numeral one_add_one)
  also have \<open>\<dots> = 2 * nat_of_uint32 (numeral n)\<close>
    by (subst nat_of_uint32_distrib_mult2[OF n_le_div2]) (rule refl)
  also have \<open>\<dots> = 2 * numeral n\<close>
    by (subst IH[OF n_le]) (rule refl)
  also have \<open>\<dots> = numeral (num.Bit0 n)\<close>
    by (subst (2) numeral.numeral_Bit0, subst mult_2)
      (rule refl)
  finally show ?case by simp
next
  case (Bit1 n) note IH = this(1)[unfolded uint32_max_def[symmetric]] and le = this(2)

  define m :: nat where \<open>m \<equiv> numeral n\<close>
  have n_le: \<open>numeral n \<le> uint32_max\<close>
    using le
    by (subst (asm) numeral.numeral_Bit1) (auto simp: m_def[symmetric] uint32_max_def)
  have n_le_div2: \<open>nat_of_uint32 (numeral n) \<le> uint32_max div 2\<close>
    apply (subst IH[OF n_le])
    using le by (subst (asm) numeral.numeral_Bit1) (auto simp: m_def[symmetric] uint32_max_def)

  have \<open>nat_of_uint32 (numeral (num.Bit1 n)) = nat_of_uint32 (2 * numeral n + 1)\<close>
    by (subst numeral.numeral_Bit1)
      (metis comm_monoid_mult_class.mult_1 distrib_right_numeral one_add_one)
  also have \<open>\<dots> = 2 * nat_of_uint32 (numeral n) + 1\<close>
    by (subst nat_of_uint32_distrib_mult2_plus1[OF n_le_div2]) (rule refl)
  also have \<open>\<dots> = 2 * numeral n + 1\<close>
    by (subst IH[OF n_le]) (rule refl)
  also have \<open>\<dots> = numeral (num.Bit1 n)\<close>
    by (subst numeral.numeral_Bit1) linarith
  finally show ?case by simp
qed

lemma nat_of_uint32_mod_232:
  shows \<open>nat_of_uint32 xi = nat_of_uint32 xi mod 2^32\<close>
proof -
  show ?thesis
    unfolding uint32_max_def
    subgoal apply transfer
      subgoal for xi
      by (use word_unat.norm_Rep[of xi] in
         \<open>auto simp: uint_word_ariths nat_mult_distrib mult_mod_mod_mult
           simp del: word_unat.norm_Rep\<close>)
    done
  done
qed

lemma transfer_pow_uint32:
  \<open>Transfer.Rel (rel_fun cr_uint32 (rel_fun (=) cr_uint32)) ((^)) ((^))\<close>
proof -
  have [simp]: \<open>Rep_uint32 y ^ x = Rep_uint32 (y ^ x)\<close> for y :: uint32 and x :: nat
    by (induction x)
       (auto simp: one_uint32.rep_eq times_uint32.rep_eq)
  show ?thesis
    by (auto simp: Transfer.Rel_def rel_fun_def cr_uint32_def)
qed

lemma uint32_mod_232_eq:
  fixes xi :: uint32
  shows \<open>xi = xi mod 2^32\<close>
proof -
  have H: \<open>nat_of_uint32 (xi mod 2 ^ 32) = nat_of_uint32 xi\<close>
    unfolding nat_of_uint32_def
    by (simp add: modulo_uint32.rep_eq word_mod_by_0)
  show ?thesis
    by (rule word_nat_of_uint32_Rep_inject[THEN iffD1, OF H[symmetric]])
qed

lemma nat_of_uint32_numeral_mod_232:
  \<open>nat_of_uint32 (numeral n) = numeral n mod 2^32\<close>
  apply (induction "n" rule: num.induct)
  subgoal by simp
  subgoal
    apply (subst numeral.numeral_Bit0)
    apply (subst numeral.numeral_Bit0)
    apply (subst nat_of_uint32_plus)
    apply (simp del: semiring_numeral_class.power_numeral add: uint32_max_def push_mods)
    done
  subgoal
    apply (subst numeral.numeral_Bit1)
    apply (subst numeral.numeral_Bit1)
    apply (subst nat_of_uint32_plus)+
    by (simp del: semiring_numeral_class.power_numeral
      add: numeral_add numeral_1_eq_Suc_0 uint32_max_def mod_Suc_eq push_mods
      del: numeral_add[symmetric] )
  done

lemma int_of_uint32_alt_def: \<open>int_of_uint32 n = int (nat_of_uint32 n)\<close>
  by (simp add: int_of_uint32.rep_eq nat_of_uint32.rep_eq unat_def del: nat_uint_eq)

lemma int_of_uint32_numeral[simp]:
  \<open>numeral n \<le> ((2 ^ 32 - 1)::nat) \<Longrightarrow> int_of_uint32 (numeral n) = numeral n\<close>
  by (subst int_of_uint32_alt_def) simp

lemma nat_of_uint32_numeral_iff[simp]:
  \<open>numeral n \<le> ((2 ^ 32 - 1)::nat) \<Longrightarrow> nat_of_uint32 a = numeral n \<longleftrightarrow> a = numeral n\<close>
  apply (rule iffI)
  prefer 2 apply (solves simp)
  using word_nat_of_uint32_Rep_inject by fastforce



lemma nat_of_uint32_mult_le:
   \<open>nat_of_uint32 ai * nat_of_uint32 bi \<le> uint32_max \<Longrightarrow>
       nat_of_uint32 (ai * bi) = nat_of_uint32 ai * nat_of_uint32 bi\<close>
  apply transfer
  by (auto simp: unat_word_ariths uint32_max_def)

(*lemma nat_and_numerals [simp]:
  "(numeral (Num.Bit0 x) :: nat) AND (numeral (Num.Bit0 y) :: nat) = (2 :: nat) * (numeral x AND numeral y)"
  "numeral (Num.Bit0 x) AND numeral (Num.Bit1 y) = (2 :: nat) * (numeral x AND numeral y)"
  "numeral (Num.Bit1 x) AND numeral (Num.Bit0 y) = (2 :: nat) * (numeral x AND numeral y)"
  "numeral (Num.Bit1 x) AND numeral (Num.Bit1 y) = (2 :: nat) * (numeral x AND numeral y)+1"
  "(1::nat) AND numeral (Num.Bit0 y) = 0"
  "(1::nat) AND numeral (Num.Bit1 y) = 1"
  "numeral (Num.Bit0 x) AND (1::nat) = 0"
  "numeral (Num.Bit1 x) AND (1::nat) = 1"
  "(Suc 0::nat) AND numeral (Num.Bit0 y) = 0"
  "(Suc 0::nat) AND numeral (Num.Bit1 y) = 1"
  "numeral (Num.Bit0 x) AND (Suc 0::nat) = 0"
  "numeral (Num.Bit1 x) AND (Suc 0::nat) = 1"
  "Suc 0 AND Suc 0 = 1"
  supply [[show_types]]
  by (auto simp: and_nat_def Bit_def nat_add_distrib)
*)
lemma nat_of_uint32_div:
  \<open>nat_of_uint32 (a div b) = nat_of_uint32 a div nat_of_uint32 b\<close>
  by transfer (auto simp: unat_div)



subsubsection \<open>64-bits\<close>

definition uint64_nat_rel :: "(uint64 \<times> nat) set" where
  \<open>uint64_nat_rel = br nat_of_uint64 (\<lambda>_. True)\<close>

abbreviation uint64_rel :: \<open>(uint64 \<times> uint64) set\<close> where
  \<open>uint64_rel \<equiv> Id\<close>

lemma word_nat_of_uint64_Rep_inject[simp]: \<open>nat_of_uint64 ai = nat_of_uint64 bi \<longleftrightarrow> ai = bi\<close>
  by transfer simp

instantiation uint64 :: default
begin
definition default_uint64 :: uint64 where
  \<open>default_uint64 = 0\<close>
instance
  ..
end

instance uint64 :: heap
  by standard (auto simp: inj_def exI[of _ nat_of_uint64])

instance uint64 :: semiring_numeral
  by standard

lemma nat_of_uint64_012[simp]: \<open>nat_of_uint64 0 = 0\<close> \<open>nat_of_uint64 2 = 2\<close> \<open>nat_of_uint64 1 = 1\<close>
  unfolding nat_of_uint64.rep_eq
  by (auto simp: one_uint64.rep_eq zero_uint64.rep_eq)


definition zero_uint64_nat where
  [simp]: \<open>zero_uint64_nat = (0 :: nat)\<close>

definition uint64_max :: nat where
  \<open>uint64_max = 2 ^64 - 1\<close>

definition uint64_max' where
  [simp, symmetric, code]: \<open>uint64_max' = uint64_max\<close>

lemma [code]: \<open>uint64_max' = 18446744073709551615\<close>
  by (auto simp: uint64_max_def)

lemma nat_of_uint64_uint64_of_nat_id: \<open>n \<le> uint64_max \<Longrightarrow> nat_of_uint64 (uint64_of_nat n) = n\<close>
  unfolding uint64_of_nat_def uint64_max_def nat_of_uint64_def
  apply (simp add: )
  unfolding uint64.word_of_word
  apply (subst le_unat_uoi[of _ 18446744073709551615])
  by auto


definition one_uint64_nat where
  [simp]: \<open>one_uint64_nat = (1 :: nat)\<close>

lemma uint64_less_than_0[iff]: \<open>(a::uint64) \<le> 0 \<longleftrightarrow> a = 0\<close>
  by transfer auto

lemma nat_of_uint64_less_iff: \<open>nat_of_uint64 a < nat_of_uint64 b \<longleftrightarrow> a < b\<close>
  apply transfer
  apply (auto simp: unat_def word_less_def simp del: nat_uint_eq)
  apply transfer
  by (smt bintr_ge0)


lemma nat_of_uint64_distrib_mult2:
  assumes \<open>nat_of_uint64 xi \<le> uint64_max div 2\<close>
  shows \<open>nat_of_uint64 (2 * xi) = 2 * nat_of_uint64 xi\<close>
  using assms unfolding uint64_max_def nat_of_uint64_def
  by (simp add: uint64.word_of_mult unat_word_ariths)

lemma (in -)nat_of_uint64_distrib_mult2_plus1:
  assumes \<open>nat_of_uint64 xi \<le> uint64_max div 2\<close>
  shows \<open>nat_of_uint64 (2 * xi + 1) = 2 * nat_of_uint64 xi + 1\<close>
  using assms unfolding uint64_max_def nat_of_uint64_def
  by (simp add: uint64.word_of_mult unat_word_ariths plus_uint64.rep_eq
    one_uint64.rep_eq)

lemma nat_of_uint64_numeral[simp]:
  \<open>numeral n \<le> ((2 ^ 64 - 1)::nat) \<Longrightarrow> nat_of_uint64 (numeral n) = numeral n\<close>
proof (induction n)
 case One
  then show ?case by auto
next
  case (Bit0 n) note IH = this(1)[unfolded uint64_max_def[symmetric]] and le = this(2)
  define m :: nat where \<open>m \<equiv> numeral n\<close>
  have n_le: \<open>numeral n \<le> uint64_max\<close>
    using le
    by (subst (asm) numeral.numeral_Bit0) (auto simp: m_def[symmetric] uint64_max_def)
  have n_le_div2: \<open>nat_of_uint64 (numeral n) \<le> uint64_max div 2\<close>
    apply (subst IH[OF n_le])
    using le by (subst (asm) numeral.numeral_Bit0) (auto simp: m_def[symmetric] uint64_max_def)

  have \<open>nat_of_uint64 (numeral (num.Bit0 n)) = nat_of_uint64 (2 * numeral n)\<close>
    by (subst numeral.numeral_Bit0)
      (metis comm_monoid_mult_class.mult_1 distrib_right_numeral one_add_one)
  also have \<open>\<dots> = 2 * nat_of_uint64 (numeral n)\<close>
    by (subst nat_of_uint64_distrib_mult2[OF n_le_div2]) (rule refl)
  also have \<open>\<dots> = 2 * numeral n\<close>
    by (subst IH[OF n_le]) (rule refl)
  also have \<open>\<dots> = numeral (num.Bit0 n)\<close>
    by (subst (2) numeral.numeral_Bit0, subst mult_2)
      (rule refl)
  finally show ?case by simp
next
  case (Bit1 n) note IH = this(1)[unfolded uint64_max_def[symmetric]] and le = this(2)

  define m :: nat where \<open>m \<equiv> numeral n\<close>
  have n_le: \<open>numeral n \<le> uint64_max\<close>
    using le
    by (subst (asm) numeral.numeral_Bit1) (auto simp: m_def[symmetric] uint64_max_def)
  have n_le_div2: \<open>nat_of_uint64 (numeral n) \<le> uint64_max div 2\<close>
    apply (subst IH[OF n_le])
    using le by (subst (asm) numeral.numeral_Bit1) (auto simp: m_def[symmetric] uint64_max_def)

  have \<open>nat_of_uint64 (numeral (num.Bit1 n)) = nat_of_uint64 (2 * numeral n + 1)\<close>
    by (subst numeral.numeral_Bit1)
      (metis comm_monoid_mult_class.mult_1 distrib_right_numeral one_add_one)

  also have \<open>\<dots> = 2 * nat_of_uint64 (numeral n) + 1\<close>
    by (subst nat_of_uint64_distrib_mult2_plus1[OF n_le_div2]) (rule refl)
  also have \<open>\<dots> = 2 * numeral n + 1\<close>
    by (subst IH[OF n_le]) (rule refl)
  also have \<open>\<dots> = numeral (num.Bit1 n)\<close>
    by (subst numeral.numeral_Bit1) linarith
  finally show ?case by simp
qed


lemma int_of_uint64_alt_def: \<open>int_of_uint64 n = int (nat_of_uint64 n)\<close>
  by (simp add: int_of_uint64.rep_eq nat_of_uint64.rep_eq unat_def del: nat_uint_eq)

lemma int_of_uint64_numeral[simp]:
  \<open>numeral n \<le> ((2 ^ 64 - 1)::nat) \<Longrightarrow> int_of_uint64 (numeral n) = numeral n\<close>
  by (subst int_of_uint64_alt_def) simp

lemma nat_of_uint64_numeral_iff[simp]:
  \<open>numeral n \<le> ((2 ^ 64 - 1)::nat) \<Longrightarrow> nat_of_uint64 a = numeral n \<longleftrightarrow> a = numeral n\<close>
  apply (rule iffI)
  prefer 2 apply (solves simp)
  using word_nat_of_uint64_Rep_inject by fastforce

lemma numeral_uint64_eq_iff[simp]:
 \<open>numeral m \<le> (2^64-1 :: nat) \<Longrightarrow> numeral n \<le> (2^64-1 :: nat) \<Longrightarrow> ((numeral m :: uint64) = numeral n) \<longleftrightarrow> numeral m = (numeral n :: nat)\<close>
  by (subst word_nat_of_uint64_Rep_inject[symmetric])
    (auto simp: uint64_max_def)


lemma numeral_uint64_eq0_iff[simp]:
 \<open>numeral n \<le> (2^64-1 :: nat) \<Longrightarrow> ((0 :: uint64) = numeral n) \<longleftrightarrow> 0 = (numeral n :: nat)\<close>
  by (subst word_nat_of_uint64_Rep_inject[symmetric])
    (auto simp: uint64_max_def)


lemma transfer_pow_uint64: \<open>Transfer.Rel (rel_fun cr_uint64 (rel_fun (=) cr_uint64)) (^) (^)\<close>
  apply (auto simp: Transfer.Rel_def rel_fun_def cr_uint64_def)
  subgoal for x y
    by (induction y)
      (auto simp: one_uint64.rep_eq times_uint64.rep_eq)
  done

(*TODO replace*)
lemma shiftl_t2n_uint64: \<open>n << m = n * 2 ^ m\<close> for n :: uint64
  unfolding shiftl_eq_mult ..

lemma mod2_bin_last: \<open>a mod 2 = 0 \<longleftrightarrow> \<not>bin_last a\<close>
  by (auto simp: bin_last_def)

lemma bitXOR_1_if_mod_2_int: \<open>L OR 1 = (if L mod 2 = 0 then L + 1 else L)\<close> for L :: int
  apply (rule bin_rl_eqI)
  unfolding bin_rest_OR bin_last_OR
   apply (auto simp: bin_last_def)
  done

lemma bitOR_1_if_mod_2_nat:
  \<open>L OR 1 = (if L mod 2 = 0 then L + 1 else L)\<close>
  \<open>L OR (Suc 0) = (if L mod 2 = 0 then L + 1 else L)\<close> for L :: nat
proof -
  have H: \<open>L OR 1 =  L + (if bin_last (int L) then 0 else 1)\<close>
    unfolding or_nat_def
    apply (auto simp: or_nat_def bin_last_def
      bitXOR_1_if_mod_2_int)
    apply presburger+
    done
  show \<open>L OR 1 = (if L mod 2 = 0 then L + 1 else L)\<close>
    unfolding H
    apply (auto simp: or_nat_def bin_last_def)
    apply presburger+
    done
  then show \<open>L OR (Suc 0) = (if L mod 2 = 0 then L + 1 else L)\<close>
    by simp
qed

lemma uint64_max_uint_def: \<open>unat (-1 :: 64 Word.word) = uint64_max\<close>
proof -
  have \<open>unat (-1 :: 64 Word.word) = unat (- Numeral1 :: 64 Word.word)\<close>
    unfolding numeral.numeral_One ..
  also have \<open>\<dots> = uint64_max\<close>
    unfolding unat_bintrunc_neg
    apply (simp add: uint64_max_def)
    by (subst numeral_eq_Suc; subst semiring_bit_operations_class.mask_Suc_exp; simp)+
  finally show ?thesis .
qed

lemma nat_of_uint64_le_uint64_max: \<open>nat_of_uint64 x \<le> uint64_max\<close>
  apply transfer
  subgoal for x
    using word_le_nat_alt[of x \<open>- 1\<close>]
    unfolding uint64_max_def[symmetric] uint64_max_uint_def
    by auto
  done

lemma nat_of_uint64_le:
  \<open>nat_of_uint64 n < 2^64\<close>
  using unat_lt2p[of \<open>Rep_uint64 n\<close>] unfolding nat_of_uint64_def
  by auto

lemma nat_of_uint64_mult: \<open>nat_of_uint64 (a * b) = nat_of_uint64 a * nat_of_uint64 b mod 2 ^ 64\<close>
  by (simp add: nat_of_uint64_def uint64.word_of_mult unat_word_ariths)

lemma nat_of_uint64_add: \<open>nat_of_uint64 (a + b) = (nat_of_uint64 a + nat_of_uint64 b) mod 2 ^ 64\<close>
  by (simp add: nat_of_uint64_def uint64.word_of_add unat_word_ariths)

lemma even_nat_of_uint64_iff[simp]: \<open>even (nat_of_uint64 n) = even n\<close> (is \<open>?A \<longleftrightarrow> ?B\<close>)
proof
  assume ?A
  then obtain k where n: \<open>nat_of_uint64 n = 2 * k\<close>
    by (auto simp: dvd_def)
  then have [simp]: \<open>nat_of_uint64 (uint64_of_nat k) = k\<close>
    apply (auto simp: nat_of_uint64_def uint64_of_nat_def uint64.word_of_word
      unat_of_nat_eq)
    by (metis Suc_1 Suc_mult_cancel1 \<open>even (nat_of_uint64 n)\<close> dvd_mult_div_cancel n uno_simps(2))
  have [simp]: \<open>k < 9223372036854775808\<close>
    using n nat_of_uint64_le[of n] by auto
  have \<open>n = 2 * uint64_of_nat k\<close>
    using n
    by (subst word_nat_of_uint64_Rep_inject[symmetric])
     (simp add: uint64.word_of_mult nat_of_uint64_mult eq_mod_iff mod_less)
  then show ?B
    unfolding dvd_def by fast
next
  assume ?B
  then obtain k where n: \<open>n = 2 * k\<close>
    by (auto simp: dvd_def)
  then show ?A
    using even_even_mod_2power_iff[of 64 \<open>2 * nat_of_uint64 k\<close>]
    by (auto simp: nat_of_uint64_mult)
qed


lemma bitOR_1_if_mod_2_uint64: \<open>L OR 1 = (if L mod 2 = 0 then L + 1 else L)\<close> for L :: uint64
proof -
  have H: \<open>L OR 1 = a \<longleftrightarrow> (nat_of_uint64 L) OR 1 = nat_of_uint64 a\<close> for a
    apply transfer
    apply (rule iffI)
    subgoal for L a
      by (auto simp: unat_def uint_or or_nat_def simp del: nat_uint_eq)
    subgoal for L a
      by (auto simp: unat_def uint_or or_nat_def eq_nat_nat_iff
        word_or_def simp del: nat_uint_eq)
    done
  have K: \<open>L mod 2 = 0 \<longleftrightarrow> nat_of_uint64 L mod 2 = 0\<close>
    by (auto simp: mod2_bin_last simp flip: even_iff_mod_2_eq_zero)
  have L: \<open>nat_of_uint64 (if L mod 2 = 0 then L + 1 else L) =
      (if nat_of_uint64 L mod 2 = 0 then nat_of_uint64 L + 1 else nat_of_uint64 L)\<close>
    using nat_of_uint64_le_uint64_max[of L]
    apply (auto simp: K uint64_max_def nat_of_uint64_add unat_of_nat_eq mod_less)
    apply (subst mod_less)
    apply auto
    by (metis K even_iff_mod_2_eq_zero linorder_not_le odd_numeral order_antisym)

  show ?thesis
    apply (subst H)
    unfolding bitOR_1_if_mod_2_nat[symmetric] L ..
qed

lemma nat_of_uint64_plus:
  \<open>nat_of_uint64 (a + b) = (nat_of_uint64 a + nat_of_uint64 b) mod (uint64_max + 1)\<close>
  by transfer (auto simp: unat_word_ariths uint64_max_def)


lemma nat_and:
  \<open>ai\<ge> 0 \<Longrightarrow> bi \<ge> 0 \<Longrightarrow> nat (ai AND bi) = nat ai AND nat bi\<close>
  by (auto simp: and_nat_def)

lemma nat_of_uint64_and:
  \<open>nat_of_uint64 ai \<le> uint64_max \<Longrightarrow> nat_of_uint64 bi \<le> uint64_max \<Longrightarrow>
    nat_of_uint64 (ai AND bi) = nat_of_uint64 ai AND nat_of_uint64 bi\<close>
  unfolding uint64_max_def
  by transfer (auto simp: unat_def uint_and nat_and simp del: nat_uint_eq)

definition two_uint64_nat :: nat where
  [simp]: \<open>two_uint64_nat = 2\<close>

lemma nat_or:
  \<open>ai\<ge> 0 \<Longrightarrow> bi \<ge> 0 \<Longrightarrow> nat (ai OR bi) = nat ai OR nat bi\<close>
  by (auto simp: or_nat_def)

lemma nat_of_uint64_or:
  \<open>nat_of_uint64 ai \<le> uint64_max \<Longrightarrow> nat_of_uint64 bi \<le> uint64_max \<Longrightarrow>
    nat_of_uint64 (ai OR bi) = nat_of_uint64 ai OR nat_of_uint64 bi\<close>
  unfolding uint64_max_def
  by transfer (auto simp: unat_def uint_or nat_or simp del: nat_uint_eq)

lemma Suc_0_le_uint64_max: \<open>Suc 0 \<le> uint64_max\<close>
  by (auto simp: uint64_max_def)

lemma nat_of_uint64_le_iff: \<open>nat_of_uint64 a \<le> nat_of_uint64 b \<longleftrightarrow> a \<le> b\<close>
  apply transfer
  by (auto simp: unat_def word_less_def nat_le_iff word_le_def simp del: nat_uint_eq)

lemma nat_of_uint64_notle_minus:
  \<open>\<not> ai < bi \<Longrightarrow>
       nat_of_uint64 (ai - bi) = nat_of_uint64 ai - nat_of_uint64 bi\<close>
  apply transfer
  unfolding unat_def
  by (subst uint_sub_lem[THEN iffD1])
    (auto simp: unat_def uint_nonnegative nat_diff_distrib word_le_def[symmetric] intro: leI
    simp del: nat_uint_eq)

lemma le_uint32_max_le_uint64_max: \<open>a \<le> uint32_max + 2 \<Longrightarrow> a \<le> uint64_max\<close>
  by (auto simp: uint32_max_def uint64_max_def)

lemma nat_of_uint64_ge_minus:
  \<open>ai \<ge> bi \<Longrightarrow>
       nat_of_uint64 (ai - bi) = nat_of_uint64 ai - nat_of_uint64 bi\<close>
  apply transfer
  unfolding unat_def
  by (subst uint_sub_lem[THEN iffD1])
    (auto simp: unat_def uint_nonnegative nat_diff_distrib word_le_def[symmetric] intro: leI
      simp del: nat_uint_eq)


definition sum_mod_uint64_max where
  \<open>sum_mod_uint64_max a b = (a + b) mod (uint64_max + 1)\<close>

definition uint32_max_uint32 :: uint32 where
  \<open>uint32_max_uint32 = - 1\<close>

lemma nat_of_uint32_uint32_max_uint32[simp]:
   \<open>nat_of_uint32 (uint32_max_uint32) = uint32_max\<close>
proof -
  have \<open>unat (Rep_uint32 (-1) :: 32 Word.word) = unat (- Numeral1 :: 32 Word.word)\<close>
    unfolding numeral.numeral_One uminus_uint32.rep_eq one_uint32.rep_eq ..
  also have \<open>\<dots> = uint32_max\<close>
    unfolding unat_bintrunc_neg
    apply (simp add: uint32_max_def)
    apply (subst numeral_eq_Suc; subst semiring_bit_operations_class.mask_Suc_exp; simp)+
    done
  finally show ?thesis by (simp add: nat_of_uint32_def uint32_max_uint32_def)
qed

lemma sum_mod_uint64_max_le_uint64_max[simp]: \<open>sum_mod_uint64_max a b \<le> uint64_max\<close>
  unfolding sum_mod_uint64_max_def
  by auto


definition uint64_of_uint32 where
  \<open>uint64_of_uint32 n = uint64_of_nat (nat_of_uint32 n)\<close>

export_code uint64_of_uint32 in SML

text \<open>We do not want to follow the definition in the generated code (that would be crazy).
\<close>
definition uint64_of_uint32' where
  [symmetric, code]: \<open>uint64_of_uint32' = uint64_of_uint32\<close>

code_printing constant uint64_of_uint32' \<rightharpoonup>
   (SML) "(Uint64.fromLarge (Word32.toLarge (_)))"

export_code uint64_of_uint32 checking SML_imp

export_code uint64_of_uint32 in SML_imp

lemma
  assumes n[simp]: \<open>n \<le> uint32_max_uint32\<close>
  shows \<open>nat_of_uint64 (uint64_of_uint32 n) = nat_of_uint32 n\<close>
proof -

  have H: \<open>nat_of_uint32 n \<le> uint32_max\<close> if \<open>n \<le> uint32_max_uint32\<close> for n
    apply (subst nat_of_uint32_uint32_max_uint32[symmetric])
    apply (subst nat_of_uint32_le_iff)
    by (auto simp: that)
  have [simp]: \<open>nat_of_uint32 n \<le> uint64_max\<close> if \<open>n \<le> uint32_max_uint32\<close> for n
    using H[of n] by (auto simp: that uint64_max_def uint32_max_def)
  show ?thesis
    apply (auto simp: uint64_of_uint32_def
      nat_of_uint64_uint64_of_nat_id uint64_max_def)
    by (subst nat_of_uint64_uint64_of_nat_id) auto
qed


definition zero_uint64 where
  \<open>zero_uint64 \<equiv> (0 :: uint64)\<close>
definition zero_uint32 where
  \<open>zero_uint32 \<equiv> (0 :: uint32)\<close>
definition two_uint64 where \<open>two_uint64 = (2 :: uint64)\<close>

lemma nat_of_uint64_ao:
  \<open>nat_of_uint64 m AND nat_of_uint64 n = nat_of_uint64 (m AND n)\<close>
  \<open>nat_of_uint64 m OR nat_of_uint64 n = nat_of_uint64 (m OR n)\<close>
  by (simp_all add: nat_of_uint64_and nat_of_uint64_or nat_of_uint64_le_uint64_max)


subsubsection \<open>Conversions\<close>

paragraph \<open>From nat to 64 bits\<close>

definition uint64_of_nat_conv :: \<open>nat \<Rightarrow> nat\<close> where
\<open>uint64_of_nat_conv i = i\<close>

paragraph \<open>From nat to 32 bits\<close>

definition nat_of_uint32_spec :: \<open>nat \<Rightarrow> nat\<close> where
  [simp]: \<open>nat_of_uint32_spec n = n\<close>

paragraph \<open>From 64 to nat bits\<close>


definition nat_of_uint64_conv :: \<open>nat \<Rightarrow> nat\<close> where
[simp]: \<open>nat_of_uint64_conv i = i\<close>

paragraph \<open>From 32 to nat bits\<close>

definition nat_of_uint32_conv :: \<open>nat \<Rightarrow> nat\<close> where
[simp]: \<open>nat_of_uint32_conv i = i\<close>

definition convert_to_uint32 :: \<open>nat \<Rightarrow> nat\<close> where
  [simp]: \<open>convert_to_uint32 = id\<close>


paragraph \<open>From 32 to 64 bits\<close>

definition uint64_of_uint32_conv :: \<open>nat \<Rightarrow> nat\<close> where
  [simp]: \<open>uint64_of_uint32_conv x = x\<close>

lemma nat_of_uint32_le_uint32_max: \<open>nat_of_uint32 n \<le> uint32_max\<close>
  using nat_of_uint32_plus[of n 0]
  pos_mod_bound[of \<open>uint32_max + 1\<close> \<open>nat_of_uint32 n\<close>]
  by auto


lemma nat_of_uint32_le_uint64_max: \<open>nat_of_uint32 n \<le> uint64_max\<close>
  using nat_of_uint32_le_uint32_max[of n] unfolding uint64_max_def uint32_max_def
  by auto

lemma nat_of_uint64_uint64_of_uint32: \<open>nat_of_uint64 (uint64_of_uint32 n) = nat_of_uint32 n\<close>
  unfolding uint64_of_uint32_def
  by (auto simp: nat_of_uint64_uint64_of_nat_id nat_of_uint32_le_uint64_max)


paragraph \<open>From 64 to 32 bits\<close>

definition uint32_of_uint64 where
  \<open>uint32_of_uint64 n = uint32_of_nat (nat_of_uint64 n)\<close>

definition uint32_of_uint64_conv where
  [simp]: \<open>uint32_of_uint64_conv n = n\<close>

lemma (in -) uint64_neq0_gt: \<open>j \<noteq> (0::uint64) \<longleftrightarrow> j > 0\<close>
  by transfer (auto simp: word_neq_0_conv)

lemma uint64_gt0_ge1: \<open>j > 0 \<longleftrightarrow> j \<ge> (1::uint64)\<close>
  apply (subst nat_of_uint64_less_iff[symmetric])
  apply (subst nat_of_uint64_le_iff[symmetric])
  by auto

definition three_uint32 where \<open>three_uint32 = (3 :: uint32)\<close>

definition nat_of_uint64_id_conv :: \<open>uint64 \<Rightarrow> nat\<close> where
\<open>nat_of_uint64_id_conv = nat_of_uint64\<close>


definition op_map :: "('b \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'a list nres" where
  \<open>op_map R e xs = do {
    let zs = replicate (length xs) e;
    (_, zs) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i,zs). i \<le> length xs \<and> take i zs = map R (take i xs) \<and>
        length zs = length xs \<and> (\<forall>k\<ge>i. k < length xs \<longrightarrow> zs ! k = e)\<^esup>
      (\<lambda>(i, zs). i < length zs)
      (\<lambda>(i, zs). do {ASSERT(i < length zs); RETURN (i+1, zs[i := R (xs!i)])})
      (0, zs);
    RETURN zs
  }\<close>

lemma op_map_map: \<open>op_map R e xs \<le> RETURN (map R xs)\<close>
  unfolding op_map_def Let_def
  by (refine_vcg WHILEIT_rule[where R=\<open>measure (\<lambda>(i,_). length xs - i)\<close>])
    (auto simp: last_conv_nth take_Suc_conv_app_nth list_update_append split: nat.splits)

lemma op_map_map_rel:
  \<open>(op_map R e, RETURN o (map R)) \<in> \<langle>Id\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>\<langle>Id\<rangle>list_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: op_map_map)

definition array_nat_of_uint64_conv :: \<open>nat list \<Rightarrow> nat list\<close> where
\<open>array_nat_of_uint64_conv = id\<close>

definition array_nat_of_uint64 :: "nat list \<Rightarrow> nat list nres" where
\<open>array_nat_of_uint64 xs = op_map nat_of_uint64_conv 0 xs\<close>

lemma array_nat_of_uint64_conv_alt_def:
  \<open>array_nat_of_uint64_conv = map nat_of_uint64_conv\<close>
  unfolding nat_of_uint64_conv_def array_nat_of_uint64_conv_def by auto

definition array_uint64_of_nat_conv :: \<open>nat list \<Rightarrow> nat list\<close> where
\<open>array_uint64_of_nat_conv = id\<close>

definition array_uint64_of_nat :: "nat list \<Rightarrow> nat list nres" where
\<open>array_uint64_of_nat xs = op_map uint64_of_nat_conv zero_uint64_nat xs\<close>

end
