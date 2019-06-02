theory IsaSAT_Watch_List
  imports IsaSAT_Clauses
begin

text \<open>There is not much to say about watch lists since they are arrays of resizeable arrays,
  which are defined in a separate theory.

  However, when replacing the elements in our watch lists from \<^typ>\<open>(nat \<times> uint32)\<close>
  to \<^typ>\<open>(nat \<times> uint32 \<times> bool)\<close>, we got a huge and unexpected slowdown, due to a much higher
  number of cache misses (roughly 3.5 times as many on a eq.atree.braun.8.unsat.cnf which also took
  66s instead of 50s). While toying with the generated ML code, we found out that our version of
  the tuples with booleans were using 40 bytes instead of 24 previously. Just merging the
  \<^typ>\<open>uint32\<close> and the \<^typ>\<open>bool\<close> to a single \<^typ>\<open>uint64\<close> was sufficient to get the
  performance back.

  Remark that however, the evaluation of terms like \<^term>\<open>(2::uint64) ^ 32\<close> was not done automatically
  and even worse, was redone each time, leading to a complete performance blow-up (75s on my macbook
  for eq.atree.braun.7.unsat.cnf instead of 7s).
\<close>

type_synonym watched_wl = \<open>((nat \<times> uint64) array_list) array\<close>
type_synonym watched_wl_uint32 = \<open>((uint64 \<times> uint64) array_list) array\<close>

definition watcher_enc where
  \<open>watcher_enc = {(n, (L, b)). \<exists>L'. (L', L) \<in> unat_lit_rel \<and>
      n = uint64_of_uint32 L' + (if b then 1 << 32 else 0)}\<close>

definition take_only_lower32 :: \<open>uint64 \<Rightarrow> uint64\<close> where
  [code del]: \<open>take_only_lower32 n = n AND ((1 << 32) - 1)\<close>


lemma nat_less_numeral_unfold: fixes n :: nat shows
  "n < numeral w \<longleftrightarrow> n = pred_numeral w \<or> n < pred_numeral w"
by(auto simp add: numeral_eq_Suc)

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

lemma take_only_lower32_le_uint32_max_ge_uint32_max:
  \<open>nat_of_uint64 n \<le> uint32_max \<Longrightarrow> nat_of_uint64 m \<ge> uint32_max \<Longrightarrow> take_only_lower32 m = 0 \<Longrightarrow>
    take_only_lower32 (n + m) = n\<close>
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
  \<open>watcher_enc_assn \<equiv> pure watcher_enc\<close>

abbreviation watcher_assn where
  \<open>watcher_assn \<equiv> nat_assn *a watcher_enc_assn\<close>

abbreviation watcher_fast_assn where
  \<open>watcher_fast_assn \<equiv> uint64_nat_assn *a watcher_enc_assn\<close>

fun blit_of where
  \<open>blit_of (_, (L, _)) = L\<close>

fun blit_of_code where
  \<open>blit_of_code (n, bL) = uint32_of_uint64 (take_only_lower32 bL)\<close>

lemma blit_of_code_hnr:
  \<open>(return o blit_of_code, RETURN o blit_of) \<in> watcher_assn\<^sup>k \<rightarrow>\<^sub>a unat_lit_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: watcher_enc_extract_blit)

fun is_marked_binary where
  \<open>is_marked_binary (_, (_, b)) = b\<close>

fun is_marked_binary_code :: \<open>_ \<times> uint64 \<Rightarrow> bool\<close> where
  [code del]: \<open>is_marked_binary_code (_, bL) = (bL AND ((2 :: uint64)^32) \<noteq> 0)\<close>

lemma [code]:
  \<open>is_marked_binary_code (n, bL) = (bL AND 4294967296 \<noteq> 0)\<close>
  by auto

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


lemma watcher_enc_extract_bool:
  assumes \<open>(n, (L, b)) \<in> watcher_enc \<close>
  shows \<open>b \<longleftrightarrow> (n AND 4294967296 \<noteq> 0)\<close>
  using assms
  supply [[show_sorts]]
  by (cases b)
   (auto dest!: watcher_enc_extract_bool_False watcher_enc_extract_bool_True)

lemma is_marked_binary_code_hnr:
  \<open>(return o is_marked_binary_code, RETURN o is_marked_binary) \<in> watcher_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare
    (sep_auto dest: watcher_enc_extract_bool watcher_enc_extract_bool_True)

definition watcher_of :: \<open>nat \<times> (nat literal \<times> bool) \<Rightarrow> _\<close> where
  [simp]: \<open>watcher_of = id\<close>

definition watcher_of_code :: \<open>nat \<times> uint64 \<Rightarrow> nat \<times> (uint32 \<times> bool)\<close> where
  \<open>watcher_of_code = (\<lambda>(a, b). (a, (blit_of_code (a, b), is_marked_binary_code (a, b))))\<close>

lemma watcher_of_code_hnr[sepref_fr_rules]:
  \<open>(return o watcher_of_code, RETURN o watcher_of) \<in>
    watcher_assn\<^sup>k \<rightarrow>\<^sub>a (nat_assn *a unat_lit_assn *a bool_assn)\<close>
  by sepref_to_hoare
    (sep_auto dest: watcher_enc_extract_bool watcher_enc_extract_bool_True watcher_enc_extract_blit
      simp: watcher_of_code_def)


definition watcher_of_fast_code :: \<open>uint64 \<times> uint64 \<Rightarrow> uint64 \<times> (uint32 \<times> bool)\<close> where
  \<open>watcher_of_fast_code = (\<lambda>(a, b). (a, (blit_of_code (a, b), is_marked_binary_code (a, b))))\<close>

lemma watcher_of_fast_code_hnr[sepref_fr_rules]:
  \<open>(return o watcher_of_fast_code, RETURN o watcher_of) \<in>
    watcher_fast_assn\<^sup>k \<rightarrow>\<^sub>a (uint64_nat_assn *a unat_lit_assn *a bool_assn)\<close>
  by sepref_to_hoare
    (sep_auto dest: watcher_enc_extract_bool watcher_enc_extract_bool_True watcher_enc_extract_blit
      simp: watcher_of_fast_code_def)

definition to_watcher :: \<open>nat \<Rightarrow> nat literal \<Rightarrow> bool \<Rightarrow> _\<close> where
  [simp]: \<open>to_watcher n L b = (n, (L, b))\<close>

definition to_watcher_code :: \<open>nat \<Rightarrow> uint32 \<Rightarrow> bool \<Rightarrow> nat \<times> uint64\<close> where
  [code del]:
    \<open>to_watcher_code = (\<lambda>a L b. (a, uint64_of_uint32 L OR (if b then 1 << 32 else (0 :: uint64))))\<close>


lemma to_watcher_code[code]:
  \<open>to_watcher_code a L b = (a, uint64_of_uint32 L OR (if b then 4294967296 else (0 :: uint64)))\<close>
  by (auto simp: shiftl_integer_conv_mult_pow2 to_watcher_code_def shiftl_t2n_uint64)

lemma OR_int64_0[simp]: \<open>A OR (0 :: uint64) = A\<close>
  by transfer auto

lemma OR_132_is_sum:
  \<open>nat_of_uint64 n \<le> uint32_max \<Longrightarrow> n OR (1 << 32) = n + (1 << 32)\<close>
  apply transfer
  subgoal for n
    using ex_rbl_word64_le_uint32_max[of n]
    apply (auto intro: and_eq_bits_eqI simp: bin_nth2_32_iff word_add_rbl
      dest: unat_le_uint32_max_no_bit_set)
    apply (rule word_bl.Rep_inject[THEN iffD1])
    by (auto simp del: word_bl.Rep_inject simp: bl_word_or word_add_rbl
      split!: if_splits)
  done

lemma to_watcher_code_hnr[sepref_fr_rules]:
  \<open>(uncurry2 (return ooo to_watcher_code), uncurry2 (RETURN ooo to_watcher)) \<in>
    nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a bool_assn\<^sup>k \<rightarrow>\<^sub>a watcher_assn\<close>
  by sepref_to_hoare
    (sep_auto dest: watcher_enc_extract_bool watcher_enc_extract_bool_True watcher_enc_extract_blit
      simp: to_watcher_code_def watcher_enc_def OR_132_is_sum nat_of_uint64_uint64_of_uint32
       nat_of_uint32_le_uint32_max)

definition (in -)to_watcher_fast where
 [simp]:  \<open>to_watcher_fast = to_watcher\<close>

definition to_watcher_fast_code :: \<open>uint64 \<Rightarrow> uint32 \<Rightarrow> bool \<Rightarrow> uint64 \<times> uint64\<close> where
  \<open>to_watcher_fast_code = (\<lambda>a L b. (a, uint64_of_uint32 L OR (if b then 1 << 32 else (0 :: uint64))))\<close>

lemma to_watcher_fast_code_hnr[sepref_fr_rules]:
  \<open>(uncurry2 (return ooo to_watcher_fast_code), uncurry2 (RETURN ooo to_watcher_fast)) \<in>
    uint64_nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a bool_assn\<^sup>k \<rightarrow>\<^sub>a watcher_fast_assn\<close>
  by sepref_to_hoare
    (sep_auto dest: watcher_enc_extract_bool watcher_enc_extract_bool_True watcher_enc_extract_blit
      simp: to_watcher_fast_code_def watcher_enc_def OR_132_is_sum nat_of_uint64_uint64_of_uint32
       nat_of_uint32_le_uint32_max)

lemma take_only_lower_code[code]:
  \<open>take_only_lower32 n = n AND 4294967295\<close>
  by (auto simp: take_only_lower32_def shiftl_t2n_uint64)

end