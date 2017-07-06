theory WB_Word_Assn
imports
  "$AFP/Word/Word"
  IICF
  Bits_Natural
  WB_More_Refinement
begin

lemma less_upper_bintrunc_id: \<open>n < 2 ^b \<Longrightarrow> n \<ge> 0 \<Longrightarrow> bintrunc b n = n\<close>
  unfolding uint32_of_nat_def
  by (simp add: no_bintr_alt1 semiring_numeral_div_class.mod_less)

definition word_nat_rel :: "('a :: len0 Word.word \<times> nat) set" where
  \<open>word_nat_rel = br unat (\<lambda>_. True)\<close>

abbreviation word_nat_assn :: "nat \<Rightarrow> 'a::len0 Word.word \<Rightarrow> assn" where
  \<open>word_nat_assn \<equiv> pure word_nat_rel\<close>

lemma op_eq_word_nat:
  \<open>(uncurry (return oo (op = :: 'a :: len Word.word \<Rightarrow> _)), uncurry (RETURN oo op =)) \<in>
    word_nat_assn\<^sup>k *\<^sub>a word_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: word_nat_rel_def br_def)

definition uint32_nat_rel :: "(uint32 \<times> nat) set" where
  \<open>uint32_nat_rel = br nat_of_uint32 (\<lambda>_. True)\<close>

abbreviation uint32_nat_assn :: "nat \<Rightarrow> uint32 \<Rightarrow> assn" where
  \<open>uint32_nat_assn \<equiv> pure uint32_nat_rel\<close>

lemma word_nat_of_uint32_Rep_inject[simp]: \<open>nat_of_uint32 ai = nat_of_uint32 bi \<longleftrightarrow> ai = bi\<close>
  by transfer simp

lemma op_eq_uint32_nat[sepref_fr_rules]:
  \<open>(uncurry (return oo (op = :: uint32 \<Rightarrow> _)), uncurry (RETURN oo op =)) \<in>
    uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def)

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

instantiation uint32 :: hashable
begin
definition hashcode_uint32 :: \<open>uint32 \<Rightarrow> uint32\<close> where
  \<open>hashcode_uint32 n = n\<close>

definition def_hashmap_size_uint32 :: \<open>uint32 itself \<Rightarrow> nat\<close> where
  \<open>def_hashmap_size_uint32 = (\<lambda>_. 16)\<close>
  -- \<open>same as @{typ nat}\<close>
instance
  by standard (simp add: def_hashmap_size_uint32_def)
end

abbreviation uint32_rel :: \<open>(uint32 \<times> uint32) set\<close> where
  \<open>uint32_rel \<equiv> Id\<close>

abbreviation uint32_assn :: \<open>uint32 \<Rightarrow> uint32 \<Rightarrow> assn\<close> where
  \<open>uint32_assn \<equiv> id_assn\<close>

lemma op_eq_uint32:
  \<open>(uncurry (return oo (op = :: uint32 \<Rightarrow> _)), uncurry (RETURN oo op =)) \<in>
    uint32_assn\<^sup>k *\<^sub>a uint32_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def)

lemmas [id_rules] =
  itypeI[Pure.of 0 "TYPE (uint32)"]
  itypeI[Pure.of 1 "TYPE (uint32)"]

lemma param_uint32[param, sepref_import_param]:
  "(0, 0::uint32) \<in> Id"
  "(1, 1::uint32) \<in> Id"
  by (rule IdI)+

lemma param_max_uint32[param,sepref_import_param]:
  "(max,max)\<in>uint32_rel \<rightarrow> uint32_rel \<rightarrow> uint32_rel" by auto

lemma max_uint32[sepref_fr_rules]:
  \<open>(uncurry (return oo max), uncurry (RETURN oo max)) \<in>
    uint32_assn\<^sup>k *\<^sub>a uint32_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def)

lemma nat_bin_trunc_ao:
  \<open>nat (bintrunc n a) AND nat (bintrunc n b) = nat (bintrunc n (a AND b))\<close>
  \<open>nat (bintrunc n a) OR nat (bintrunc n b) = nat (bintrunc n (a OR b))\<close>
  unfolding bitAND_nat_def bitOR_nat_def
  by (auto simp add: bin_trunc_ao bintr_ge0)

lemma nat_of_uint32_ao:
  \<open>nat_of_uint32 n AND nat_of_uint32 m = nat_of_uint32 (n AND m)\<close>
  \<open>nat_of_uint32 n OR nat_of_uint32 m = nat_of_uint32 (n OR m)\<close>
  subgoal apply (transfer, unfold unat_def, transfer, unfold nat_bin_trunc_ao) ..
  subgoal apply (transfer, unfold unat_def, transfer, unfold nat_bin_trunc_ao) ..
  done

lemma nat_of_uint32_012: \<open>nat_of_uint32 0 = 0\<close> \<open>nat_of_uint32 2 = 2\<close> \<open>nat_of_uint32 1 = 1\<close>
  by (transfer, auto)+

lemma nat_uint_XOR: \<open>nat (uint (a XOR b)) = nat (uint a) XOR nat (uint b)\<close>
  if len: \<open>LENGTH('a) > 0\<close>
  for a b :: \<open>'a ::len0 Word.word\<close>
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
    proof (cases n)
      case (Suc m)
      moreover have
        \<open>nat (bintrunc m (bin_rest (bin_rest a) XOR bin_rest (bin_rest b)) BIT
            ((bin_last (bin_rest a) \<or> bin_last (bin_rest b)) \<and>
             (bin_last (bin_rest a) \<longrightarrow> \<not> bin_last (bin_rest b))) BIT
            ((bin_last a \<or> bin_last b) \<and> (bin_last a \<longrightarrow> \<not> bin_last b))) =
         nat ((bintrunc m (bin_rest (bin_rest a)) XOR bintrunc m (bin_rest (bin_rest b))) BIT
              ((bin_last (bin_rest a) \<or> bin_last (bin_rest b)) \<and>
               (bin_last (bin_rest a) \<longrightarrow> \<not> bin_last (bin_rest b))) BIT
              ((bin_last a \<or> bin_last b) \<and> (bin_last a \<longrightarrow> \<not> bin_last b)))\<close>
        (is \<open>nat (?n1 BIT ?b) = nat (?n2 BIT ?b)\<close>)
      proof - (* Sledgehammer proof changed to use the more readable ?n1 and ?n2 *)
        have a1:  "nat ?n1 = nat ?n2"
          using IH Suc by auto
        have f2: "0 \<le> ?n2"
          by (simp add: bintr_ge0)
        have "0 \<le> ?n1"
          using bintr_ge0 by auto
        then have "?n2 = ?n1"
          using f2 a1 by presburger
        then show ?thesis by simp
      qed
      ultimately show ?thesis by simp
    qed simp
  qed
  have \<open>nat (bintrunc LENGTH('a) (a XOR b)) = nat (bintrunc LENGTH('a) a XOR bintrunc LENGTH('a) b)\<close> for a b
    using len H[of \<open>LENGTH('a)\<close> a b] by auto
  then have \<open>nat (uint (a XOR b)) = nat (uint a XOR uint b)\<close>
    by transfer
  then show ?thesis
    unfolding bitXOR_nat_def by auto
qed

lemma nat_of_uint32_XOR: \<open>nat_of_uint32 (a XOR b) = nat_of_uint32 a XOR nat_of_uint32 b\<close>
  by transfer (auto simp: unat_def nat_uint_XOR)

lemma nat_of_uint32_0_iff: \<open>nat_of_uint32 xi = 0 \<longleftrightarrow> xi = 0\<close> for xi
  by transfer (auto simp: unat_def uint_0_iff)

lemma nat_0_AND: \<open>0 AND n = 0\<close> for n :: nat
  unfolding bitAND_nat_def by auto

lemma uint32_0_AND: \<open>0 AND n = 0\<close> for n :: uint32
  by transfer auto

definition (in -) uint32_safe_minus where
  \<open>uint32_safe_minus m n = (if m < n then 0 else m - n)\<close>

lemma nat_of_uint32_le_minus: \<open>ai \<le> bi \<Longrightarrow> 0 = nat_of_uint32 ai - nat_of_uint32 bi\<close>
  by transfer (auto simp: unat_def word_le_def)

lemma nat_of_uint32_notle_minus:
  \<open>\<not> ai < bi \<Longrightarrow>
       nat_of_uint32 (ai - bi) = nat_of_uint32 ai - nat_of_uint32 bi\<close>
  apply transfer
  unfolding unat_def
  by (subst uint_sub_lem[THEN iffD1])
    (auto simp: unat_def uint_nonnegative nat_diff_distrib word_le_def[symmetric] intro: leI)

lemma uint32_nat_assn_minus[sepref_fr_rules]:
  \<open>(uncurry (return oo uint32_safe_minus), uncurry (RETURN oo op -)) \<in>
     uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: uint32_nat_rel_def nat_of_uint32_le_minus
      br_def uint32_safe_minus_def nat_of_uint32_012 nat_of_uint32_notle_minus)

lemma [safe_constraint_rules]:
  \<open>CONSTRAINT IS_LEFT_UNIQUE uint32_nat_rel\<close>
  \<open>CONSTRAINT IS_RIGHT_UNIQUE uint32_nat_rel\<close>
  by (auto simp: IS_LEFT_UNIQUE_def single_valued_def uint32_nat_rel_def br_def)

lemma nat_of_uint32_uint32_of_nat_id: \<open>n < 2 ^32 \<Longrightarrow> nat_of_uint32 (uint32_of_nat n) = n\<close>
  unfolding uint32_of_nat_def
  apply simp
  apply transfer
  apply (auto simp: unat_def)
  apply transfer
  by (auto simp: less_upper_bintrunc_id)

lemma shiftr1[sepref_fr_rules]:
   \<open>(uncurry (return oo (op >> )), uncurry (RETURN oo (op >>))) \<in> uint32_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a
      uint32_assn\<close>
  by sepref_to_hoare (sep_auto simp: shiftr1_def uint32_nat_rel_def br_def)

lemma shiftl1[sepref_fr_rules]: \<open>(return o shiftl1, RETURN o shiftl1) \<in> nat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare sep_auto

lemma nat_of_uint32_rule[sepref_fr_rules]:
  \<open>(return o nat_of_uint32, RETURN o nat_of_uint32) \<in> uint32_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare sep_auto

lemma uint32_less_than_0[iff]: \<open>(a::uint32) \<le> 0 \<longleftrightarrow> a = 0\<close>
  by transfer auto

lemma nat_of_uint32_less_iff: \<open>nat_of_uint32 a < nat_of_uint32 b \<longleftrightarrow> a < b\<close>
  apply transfer
  apply (auto simp: unat_def word_less_def)
  apply transfer
  by (smt bintr_ge0)

lemma nat_of_uint32_le_iff: \<open>nat_of_uint32 a \<le> nat_of_uint32 b \<longleftrightarrow> a \<le> b\<close>
  apply transfer
  by (auto simp: unat_def word_less_def nat_le_iff word_le_def)

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
  assumes \<open>nat_of_uint32 xi < 2^32 div 2\<close>
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
      using f2 a1 by (metis (no_types) Divides.mod_less Divides.transfer_int_nat_functions(2) dual_order.order_iff_strict linorder_not_less nat_int of_nat_numeral uint_nat) (* 546 ms *)
  qed
  have [simp]: \<open>xi \<noteq> (0::32 Word.word) \<Longrightarrow> (0::int) < uint xi\<close> for xi
    by (metis (full_types) uint_eq_0 word_gt_0 word_less_def)
  show ?thesis
    using assms
    apply (case_tac \<open>xi = 0\<close>)
    subgoal by (auto simp: nat_of_uint32_012)
    subgoal by transfer (auto simp: unat_def uint_word_ariths nat_mult_distrib mult_mod_mod_mult H)
    done
qed

lemma nat_of_uint32_distrib_mult2_plus1:
  assumes \<open>nat_of_uint32 xi < 2^32 div 2\<close>
  shows \<open>nat_of_uint32 (2 * xi + 1) = 2 * nat_of_uint32 xi + 1\<close>
proof -
  have mod_is_id: \<open>\<And>xi::32 Word.word. nat (uint xi) < (2147483648::nat) \<Longrightarrow>
      (uint xi mod (4294967296::int)) = uint xi\<close>
    by (subst zmod_trival_iff) auto
  have [simp]: \<open>xi \<noteq> (0::32 Word.word) \<Longrightarrow> (0::int) < uint xi\<close> for xi
    by (metis (full_types) uint_eq_0 word_gt_0 word_less_def)
  show ?thesis
    using assms by transfer (auto simp: unat_def uint_word_ariths nat_mult_distrib mult_mod_mod_mult
        mod_is_id nat_mod_distrib nat_add_distrib)
qed



lemma max_uint32_nat[sepref_fr_rules]:
  \<open>(uncurry (return oo max), uncurry (RETURN oo max)) \<in> uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a
     uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def nat_of_uint32_max)

lemma array_set_hnr_u[sepref_fr_rules]:
    \<open>CONSTRAINT is_pure A \<Longrightarrow>
    (uncurry2 (\<lambda>xs i. heap_array_set xs (nat_of_uint32 i)), uncurry2 (RETURN \<circ>\<circ>\<circ> op_list_set)) \<in>
     [pre_list_set]\<^sub>a (array_assn A)\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow> array_assn A\<close>
  by sepref_to_hoare
    (sep_auto simp: uint32_nat_rel_def br_def ex_assn_up_eq2 array_assn_def is_array_def
      hr_comp_def list_rel_pres_length list_rel_update)

lemma  array_get_hnr_u[sepref_fr_rules]:
  assumes \<open>CONSTRAINT is_pure A\<close>
  shows \<open>(uncurry (\<lambda>xs i. Array.nth xs (nat_of_uint32 i)),
      uncurry (RETURN \<circ>\<circ> op_list_get)) \<in> [pre_list_get]\<^sub>a (array_assn A)\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> A\<close>
proof -
  obtain A' where
    A: \<open>pure A' = A\<close>
    using assms pure_the_pure by auto
  then have A': \<open>the_pure A = A'\<close>
    by auto
  have [simp]: \<open>the_pure (\<lambda>a c. \<up> ((c, a) \<in> A')) = A'\<close>
    unfolding pure_def[symmetric] by auto
  show ?thesis
    by sepref_to_hoare
      (sep_auto simp: uint32_nat_rel_def br_def ex_assn_up_eq2 array_assn_def is_array_def
       hr_comp_def list_rel_pres_length list_rel_update param_nth A' A[symmetric] ent_refl_true
     list_rel_eq_listrel listrel_iff_nth pure_def)
qed

lemma arl_get_hnr_u[sepref_fr_rules]:
  assumes \<open>CONSTRAINT is_pure A\<close>
  shows \<open>(uncurry (\<lambda>xs i. arl_get xs (nat_of_uint32 i)), uncurry (RETURN \<circ>\<circ> op_list_get))
\<in> [pre_list_get]\<^sub>a (arl_assn A)\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> A\<close>
proof -
  obtain A' where
    A: \<open>pure A' = A\<close>
    using assms pure_the_pure by auto
  then have A': \<open>the_pure A = A'\<close>
    by auto
  have [simp]: \<open>the_pure (\<lambda>a c. \<up> ((c, a) \<in> A')) = A'\<close>
    unfolding pure_def[symmetric] by auto
  show ?thesis
    by sepref_to_hoare
      (sep_auto simp: uint32_nat_rel_def br_def ex_assn_up_eq2 array_assn_def is_array_def
        hr_comp_def list_rel_pres_length list_rel_update param_nth arl_assn_def
        A' A[symmetric] pure_def)
qed

lemma nat_of_uint32_add:
  \<open>nat_of_uint32 ai + nat_of_uint32 bi < 2 ^32 \<Longrightarrow>
    nat_of_uint32 (ai + bi) = nat_of_uint32 ai + nat_of_uint32 bi\<close>
  by transfer (auto simp: unat_def uint_plus_if' nat_add_distrib)

lemma uint32_nat_assn_plus[sepref_fr_rules]:
  \<open>(uncurry (return oo op +), uncurry (RETURN oo op +)) \<in> [\<lambda>(m, n). m + n < 2^32]\<^sub>a
     uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def nat_of_uint32_add br_def)


lemma uint32_nat_assn_one:
  \<open>(uncurry0 (return 1), uncurry0 (RETURN 1)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def nat_of_uint32_012)

lemma uint32_nat_assn_zero:
  \<open>(uncurry0 (return 0), uncurry0 (RETURN 0)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def nat_of_uint32_012)

lemma nat_of_uint32_int32_assn:
  \<open>(return o id, RETURN o nat_of_uint32) \<in> uint32_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def)


definition \<open>zero_uint32 = (0 :: nat)\<close>

lemma uint32_nat_assn_zero_uint32:
  \<open>(uncurry0 (return 0), uncurry0 (RETURN zero_uint32)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def nat_of_uint32_012 zero_uint32_def)

lemma nat_assn_zero:
  \<open>(uncurry0 (return 0), uncurry0 (RETURN 0)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def nat_of_uint32_012)

lemma uint32_nat_assn_less[sepref_fr_rules]:
  \<open>(uncurry (return oo op <), uncurry (RETURN oo op <)) \<in>
    uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def max_def
      nat_of_uint32_less_iff)

text \<open>Do NOT declare this theorem as \<open>sepref_fr_rules\<close> to avoid bad unexpected conversions.\<close>
lemma (in -) le_uint32_nat_hnr:
  \<open>(uncurry (return oo (\<lambda>a b. nat_of_uint32 a < b)), uncurry (RETURN oo op <)) \<in>
   uint32_nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def)

lemma (in -) le_nat_uint32_hnr:
  \<open>(uncurry (return oo (\<lambda>a b. a < nat_of_uint32 b)), uncurry (RETURN oo op <)) \<in>
   nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def)

definition (in -) fast_minus :: \<open>'a::minus \<Rightarrow> 'a \<Rightarrow> 'a\<close> where
  \<open>fast_minus m n = m - n\<close>

lemma (in -) safe_minus[sepref_fr_rules]:
  \<open>(uncurry (return oo fast_minus), uncurry (RETURN oo fast_minus)) \<in>
     [\<lambda>(m, n). m \<ge> n]\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  by sepref_to_hoare
   (sep_auto simp: fast_minus_def uint32_nat_rel_def br_def nat_of_uint32_le_minus
      nat_of_uint32_notle_minus nat_of_uint32_le_iff)

end