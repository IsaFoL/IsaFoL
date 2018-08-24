theory IsaSAT_Watch_List
  imports IsaSAT_Clauses
begin

text \<open>There is not much to say about watch list,s since they are arrays of resizeable arrays,
  which are defined in a separate theory.

  However, when replacing the elements in our watch lists from \<^typ>\<open>(nat \<times> uint32)\<close>
  to \<^typ>\<open>(nat \<times> uint32 \<times> bool)\<close>, we got a huge and unexpected slowdown, due to a much higher
  number of cache misses (roughly 3.5 times as many on a eq.atree.braun.8.unsat.cnf who also took
  66s instead of 50s). While toying with the generated ML code, we found out that our version of
  the tuples with booleans were using 40 bytes instead of 24 previously. Just merging the
  \<^typ>\<open>uint32\<close> and the \<^typ>\<open>bool\<close> to a single \<^typ>\<open>uint64\<close> was sufficient to get the
  performance back.
\<close>

type_synonym watched_wl_uint32 = \<open>((uint64 \<times> uint32 \<times> bool) array_list) array\<close>

definition watcher_enc where
  \<open>watcher_enc = {(n, (L, b)). \<exists>L'. (L', L) \<in> unat_lit_rel \<and>
      n = uint64_of_uint32 L' + (if b then 1 << 32 else 0)}\<close>

definition take_only_lower32 :: \<open>uint64 \<Rightarrow> uint64\<close> where
  \<open>take_only_lower32 n = n AND ((1 << 32) - 1)\<close>

lemma bintrunc_eq_bits_eqI: \<open> (\<And>n. (n < r \<and> bin_nth c n) = (n < r \<and> bin_nth a n)) \<Longrightarrow>
       bintrunc r (a) = bintrunc r c\<close>
proof (induction r arbitrary: a c)
  case 0
  then show ?case by (simp_all flip: bin_nth.Z)
next
  case (Suc r a c) note IH = this(1) and eq = this(2)
  have 1: \<open>(n < r \<and> bin_nth (bin_rest a) n) = (n < r \<and> bin_nth (bin_rest c) n)\<close> for n
    using eq[of \<open>Suc n\<close>] eq[of 1] by (clarsimp simp flip: bin_nth.Z)
  show ?case
    using IH[OF 1] eq[of 0] by (simp_all flip: bin_nth.Z)
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
    by (auto simp: less_Suc_eq word_less_nat_alt
      simp del: unat_lt2p)
qed

lemma pow2_mono_word_le:
  \<open>m < LENGTH('a) \<Longrightarrow> n < LENGTH('a) \<Longrightarrow> m \<le> n \<Longrightarrow> (2 :: 'a :: len word) ^m  \<le> 2 ^ n\<close>
  using pow2_mono_word_less[of m n, where 'a = 'a]
  by (cases \<open>m = n\<close>) auto

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
    by (auto simp:  word_le_nat_alt unat_numeral uint_max_def mod_less
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
    by (auto simp:  word_le_nat_alt unat_numeral uint_max_def
      simp del: unat_bintrunc)

   then show False
    using less by auto
qed

lemma le32_enum: \<open>na < (32 :: nat) \<longleftrightarrow> na \<in> {0..<32}\<close>
  by auto

lemma bin_nth2_32_iff: \<open>bin_nth 4294967295 na \<longleftrightarrow> na < 32\<close>
  by (auto simp: bin_nth_Bit1 bin_nth_Bit0 nat_less_numeral_unfold)

lemma take_only_lower32_le_uint32_max:
  \<open>nat_of_uint64 n \<le> uint32_max \<Longrightarrow> take_only_lower32 n = n\<close>
  unfolding take_only_lower32_def
  apply transfer
  by (auto intro!: and_eq_bits_eqI dest: unat_le_uint32_max_no_bit_set
    intro!: bin_nth2_32_iff[THEN iffD2])


lemma uint32_of_uint64_uint64_of_uint32[simp]: \<open>uint32_of_uint64 (uint64_of_uint32 n) = n\<close>
  by (auto simp: uint64_of_uint32_def uint32_of_uint64_def
    nat_of_uint64_uint64_of_nat_id nat_of_uint32_le_uint32_max nat_of_uint32_le_uint64_max)

lemma uint64_enumerate_all:
  fixes  n :: uint64
   assumes \<open>(P 0)\<close> and
      \<open>(\<And>n. nat_of_uint64 n \<le> 2 ^64 \<Longrightarrow> n \<ge> 1 \<Longrightarrow> P (n))\<close>
    shows \<open>P n\<close>
    using assms(1) assms(2)[of \<open>n\<close>] nat_of_uint64_le_uint64_max[of n]
  apply (cases \<open>n = 0\<close>)
  subgoal
    by (auto simp: uint64_max_def nat_of_uint64_ge_minus)
  subgoal
    apply (subgoal_tac \<open>n \<ge> 1\<close>)
    apply auto
    apply (auto simp: uint64_max_def)
    by (metis nat_geq_1_eq_neqz nat_of_uint64_012(1) nat_of_uint64_012(3) nat_of_uint64_le_iff word_nat_of_uint64_Rep_inject)
  done

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
    have [simp]: \<open>(n AND 4294967295) !! m = False\<close> for m
      using that by auto
    show ?thesis
      using H H'[of 0]
      H'[of 32] H'[of 31] H'[of 30] H'[of 29] H'[of 28] H'[of 27] H'[of 26] H'[of 25] H'[of 24]
      H'[of 23] H'[of 22] H'[of 21] H'[of 20] H'[of 19] H'[of 18] H'[of 17] H'[of 16] H'[of 15]
      H'[of 14] H'[of 13] H'[of 12] H'[of 11] H'[of 10] H'[of 9] H'[of 8] H'[of 7] H'[of 6]
      H'[of 5] H'[of 4] H'[of 3] H'[of 2] H'[of 1]
      unfolding unat_def word_size that
      by (clarsimp simp add: word_size bl_word_and word_add_rbl)
  qed
qed

lemma take_only_lower32_le_uint32_max_ge_uint32_max:
  \<open>nat_of_uint64 n \<le> uint32_max \<Longrightarrow> nat_of_uint64 m \<ge> uint32_max \<Longrightarrow> take_only_lower32 m = 0 \<Longrightarrow> take_only_lower32 (n + m) = n\<close>
  unfolding take_only_lower32_def
  apply transfer
  subgoal for m n
    using ex_rbl_word64_le_uint32_max[of m] ex_rbl_word64_ge_uint32_max[of n]
    apply (auto intro: and_eq_bits_eqI simp: bin_nth2_32_iff word_add_rbl
      dest: unat_le_uint32_max_no_bit_set)
    apply (rule word_bl.Rep_inject[THEN iffD1])
    apply (auto simp del: word_bl.Rep_inject simp: bl_word_and word_add_rbl
      split!: if_splits)
    done
  done

lemma take_only_lower32_1_32: \<open>take_only_lower32 (1 << 32) = 0\<close>
  unfolding take_only_lower32_def
  by transfer (auto simp: )

lemma nat_of_uint64_1_32: \<open>nat_of_uint64 (1 << 32) = uint32_max + 1\<close>
  unfolding uint32_max_def
  by transfer auto

lemma watcher_enc_extract_blit:
  assumes \<open>(n, (L, b)) \<in> watcher_enc\<close>
  shows \<open>(uint32_of_uint64 (take_only_lower32 n), L) \<in> unat_lit_rel\<close>
  using assms
  by (auto simp: watcher_enc_def take_only_lower32_le_uint32_max nat_of_uint64_uint64_of_uint32
    nat_of_uint32_le_uint32_max nat_of_uint64_1_32 take_only_lower32_1_32
      take_only_lower32_le_uint32_max_ge_uint32_max)

abbreviation watcher_enc_assn where
  \<open>watcher_enc_assn \<equiv> pure watcher_enc \<close>

abbreviation watcher_assn where
  \<open>watcher_assn \<equiv> nat_assn *a watcher_enc_assn \<close>

fun blit_of where
  \<open>blit_of (_, (L, _)) = L\<close>

fun blit_of_code where
  \<open>blit_of_code (n, bL) = uint32_of_uint64 (take_only_lower32 bL)\<close>

lemma blit_of_code_hnr:
  \<open>(return o blit_of_code, RETURN o blit_of) \<in> watcher_assn\<^sup>k \<rightarrow>\<^sub>a unat_lit_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: watcher_enc_extract_blit)

fun is_binary where
  \<open>is_binary (_, (_, b)) = b\<close>

fun is_binary_code where
  \<open>is_binary_code (n, bL) = (bL AND (2^32) = 2^32)\<close>

lemma AND_2_32_bool:
  \<open>nat_of_uint64 n \<le> uint32_max \<Longrightarrow> n + (1 << 32) AND 4294967296 = 4294967296\<close>
  apply transfer
  subgoal for n
    using ex_rbl_word64_ge_uint32_max[of \<open>1 << 32\<close>] ex_rbl_word64_le_uint32_max[of n]
    apply (auto intro: and_eq_bits_eqI simp: bin_nth2_32_iff word_add_rbl
      dest: unat_le_uint32_max_no_bit_set)
    apply (rule word_bl.Rep_inject[THEN iffD1])
    apply (auto simp del: word_bl.Rep_inject simp: bl_word_and word_add_rbl
      split!: if_splits)
    done
  done


instance uint64 :: semiring_numeral
  by standard

instance uint32 :: semiring_numeral
  by standard

lemma watcher_enc_extract_bool_True:
  assumes \<open>(n, (L, True)) \<in> watcher_enc\<close>
  shows \<open>n AND 4294967296 = 4294967296\<close>
  using assms
  by (auto simp: watcher_enc_def take_only_lower32_le_uint32_max nat_of_uint64_uint64_of_uint32
    nat_of_uint32_le_uint32_max nat_of_uint64_1_32 take_only_lower32_1_32 AND_2_32_bool
      take_only_lower32_le_uint32_max_ge_uint32_max)

lemma le_uint32_max_AND2_32_eq0: \<open>nat_of_uint64 n \<le> uint32_max \<Longrightarrow> n AND 4294967296 = 0\<close>
  apply transfer
  subgoal for n
    using ex_rbl_word64_le_uint32_max[of n]
    apply (auto intro!: )
    apply (rule word_bl.Rep_inject[THEN iffD1])
    apply (auto simp del: word_bl.Rep_inject simp: bl_word_and word_add_rbl
      split!: if_splits)
    done
  done

lemma watcher_enc_extract_bool_False:
  assumes \<open>(n, (L, False)) \<in> watcher_enc\<close>
  shows \<open>(n AND 4294967296 = 0)\<close>
  using assms
  by (auto simp: watcher_enc_def take_only_lower32_le_uint32_max nat_of_uint64_uint64_of_uint32
    nat_of_uint32_le_uint32_max nat_of_uint64_1_32 take_only_lower32_1_32 AND_2_32_bool
      take_only_lower32_le_uint32_max_ge_uint32_max le_uint32_max_AND2_32_eq0)

lemma numeral_uint64_eq_iff[simp]:
 \<open>numeral m \<le> (2^64-1 :: nat) \<Longrightarrow> numeral n \<le> (2^64-1 :: nat) \<Longrightarrow> ((numeral m :: uint64) = numeral n) \<longleftrightarrow> numeral m = (numeral n :: nat)\<close>
  by (subst word_nat_of_uint64_Rep_inject[symmetric])
    (auto simp: uint64_max_def)


lemma numeral_uint64_eq0_iff[simp]:
 \<open>numeral n \<le> (2^64-1 :: nat) \<Longrightarrow> ((0 :: uint64) = numeral n) \<longleftrightarrow> 0 = (numeral n :: nat)\<close>
  by (subst word_nat_of_uint64_Rep_inject[symmetric])
    (auto simp: uint64_max_def)


lemma watcher_enc_extract_bool:
  assumes \<open>(n, (L, b)) \<in> watcher_enc \<close>
  shows \<open>b \<longleftrightarrow> (n AND 4294967296 \<noteq> 0)\<close>
  using assms
  supply [[show_sorts]]
  by (cases b)
   (auto dest!: watcher_enc_extract_bool_False watcher_enc_extract_bool_True)

lemma is_binary_code_hnr:
  \<open>(return o is_binary_code, RETURN o is_binary) \<in> watcher_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare
    (sep_auto dest: watcher_enc_extract_bool watcher_enc_extract_bool_True)

definition watcher_of :: \<open>nat \<times> (nat literal \<times> bool) \<Rightarrow> _\<close> where
  [simp]: \<open>watcher_of = id\<close>

definition watcher_of_code :: \<open>nat \<times> uint64 \<Rightarrow> nat \<times> (uint32 \<times> bool)\<close> where
  \<open>watcher_of_code = (\<lambda>(a, b). (a, (blit_of_code (a, b), is_binary_code (a, b))))\<close>

lemma watcher_of_code_hnr:
  \<open>(return o watcher_of_code, RETURN o watcher_of) \<in>
    watcher_assn\<^sup>k \<rightarrow>\<^sub>a (nat_assn *a unat_lit_assn *a bool_assn)\<close>
  by sepref_to_hoare
    (sep_auto dest: watcher_enc_extract_bool watcher_enc_extract_bool_True watcher_enc_extract_blit
      simp: watcher_of_code_def)

end