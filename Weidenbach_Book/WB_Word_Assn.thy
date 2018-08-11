theory WB_Word_Assn
imports
  "HOL-Word.Word"
  Bits_Natural
  WB_More_Refinement
  "Native_Word.Uint64"
begin

subsection \<open>More Setup for Fixed Size Natural Numbers\<close>

subsubsection \<open>Words\<close>

lemma less_upper_bintrunc_id: \<open>n < 2 ^b \<Longrightarrow> n \<ge> 0 \<Longrightarrow> bintrunc b n = n\<close>
  unfolding uint32_of_nat_def
  by (simp add: no_bintr_alt1)

definition word_nat_rel :: "('a :: len0 Word.word \<times> nat) set" where
  \<open>word_nat_rel = br unat (\<lambda>_. True)\<close>

abbreviation word_nat_assn :: "nat \<Rightarrow> 'a::len0 Word.word \<Rightarrow> assn" where
  \<open>word_nat_assn \<equiv> pure word_nat_rel\<close>

lemma op_eq_word_nat:
  \<open>(uncurry (return oo ((=) :: 'a :: len Word.word \<Rightarrow> _)), uncurry (RETURN oo (=))) \<in>
    word_nat_assn\<^sup>k *\<^sub>a word_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: word_nat_rel_def br_def)


subsubsection \<open>32-bits\<close>

lemma word_nat_of_uint32_Rep_inject[simp]: \<open>nat_of_uint32 ai = nat_of_uint32 bi \<longleftrightarrow> ai = bi\<close>
  by transfer simp

lemma nat_of_uint32_012[simp]: \<open>nat_of_uint32 0 = 0\<close> \<open>nat_of_uint32 2 = 2\<close> \<open>nat_of_uint32 1 = 1\<close>
  by (transfer, auto)+

lemma nat_of_uint32_3: \<open>nat_of_uint32 3 = 3\<close>
  by (transfer, auto)+

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

abbreviation uint32_nat_assn :: "nat \<Rightarrow> uint32 \<Rightarrow> assn" where
  \<open>uint32_nat_assn \<equiv> pure uint32_nat_rel\<close>

lemma op_eq_uint32_nat[sepref_fr_rules]:
  \<open>(uncurry (return oo ((=) :: uint32 \<Rightarrow> _)), uncurry (RETURN oo (=))) \<in>
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
  \<comment> \<open>same as @{typ nat}\<close>
instance
  by standard (simp add: def_hashmap_size_uint32_def)
end

abbreviation uint32_rel :: \<open>(uint32 \<times> uint32) set\<close> where
  \<open>uint32_rel \<equiv> Id\<close>

abbreviation uint32_assn :: \<open>uint32 \<Rightarrow> uint32 \<Rightarrow> assn\<close> where
  \<open>uint32_assn \<equiv> id_assn\<close>

lemma op_eq_uint32:
  \<open>(uncurry (return oo ((=) :: uint32 \<Rightarrow> _)), uncurry (RETURN oo (=))) \<in>
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

lemma nat_of_uint32_mod_2:
  \<open>nat_of_uint32 L mod 2 = nat_of_uint32 (L mod 2)\<close>
  by transfer (auto simp: uint_mod unat_def nat_mod_distrib)

lemma bitAND_1_mod_2_uint32: \<open>bitAND L 1 = L mod 2\<close> for L :: uint32
proof -
  have H: \<open>unat L mod 2 = 1 \<or> unat L mod 2 = 0\<close> for L
    by auto

  show ?thesis
    apply (subst word_nat_of_uint32_Rep_inject[symmetric])
    apply (subst nat_of_uint32_ao[symmetric])
    apply (subst nat_of_uint32_012)
    unfolding bitAND_1_mod_2
    by (rule nat_of_uint32_mod_2)
qed

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

definition uint32_safe_minus where
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

lemma uint32_nat_assn_minus:
  \<open>(uncurry (return oo uint32_safe_minus), uncurry (RETURN oo (-))) \<in>
     uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: uint32_nat_rel_def nat_of_uint32_le_minus
      br_def uint32_safe_minus_def nat_of_uint32_012 nat_of_uint32_notle_minus)

lemma [safe_constraint_rules]:
  \<open>CONSTRAINT IS_LEFT_UNIQUE uint32_nat_rel\<close>
  \<open>CONSTRAINT IS_RIGHT_UNIQUE uint32_nat_rel\<close>
  by (auto simp: IS_LEFT_UNIQUE_def single_valued_def uint32_nat_rel_def br_def)

definition uint32_max :: nat where
  \<open>uint32_max = 2 ^32 - 1\<close>

lemma nat_of_uint32_uint32_of_nat_id: \<open>n \<le> uint32_max \<Longrightarrow> nat_of_uint32 (uint32_of_nat n) = n\<close>
  unfolding uint32_of_nat_def uint32_max_def
  apply simp
  apply transfer
  apply (auto simp: unat_def)
  apply transfer
  by (auto simp: less_upper_bintrunc_id)

lemma shiftr1[sepref_fr_rules]:
   \<open>(uncurry (return oo ((>>) )), uncurry (RETURN oo (>>))) \<in> uint32_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a
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
      using f2 a1 by auto
  qed
  have [simp]: \<open>xi \<noteq> (0::32 Word.word) \<Longrightarrow> (0::int) < uint xi\<close> for xi
    by (metis (full_types) uint_eq_0 word_gt_0 word_less_def)
  show ?thesis
    using assms unfolding uint32_max_def
    apply (case_tac \<open>xi = 0\<close>)
    subgoal by auto
    subgoal by transfer (auto simp: unat_def uint_word_ariths nat_mult_distrib mult_mod_mod_mult H)
    done
qed

lemma nat_of_uint32_distrib_mult2_plus1:
  assumes \<open>nat_of_uint32 xi \<le> uint32_max div 2\<close>
  shows \<open>nat_of_uint32 (2 * xi + 1) = 2 * nat_of_uint32 xi + 1\<close>
proof -
  have mod_is_id: \<open>\<And>xi::32 Word.word. nat (uint xi) < (2147483648::nat) \<Longrightarrow>
      (uint xi mod (4294967296::int)) = uint xi\<close>
    by (subst zmod_trival_iff) auto
  have [simp]: \<open>xi \<noteq> (0::32 Word.word) \<Longrightarrow> (0::int) < uint xi\<close> for xi
    by (metis (full_types) uint_eq_0 word_gt_0 word_less_def)
  show ?thesis
    using assms by transfer (auto simp: unat_def uint_word_ariths nat_mult_distrib mult_mod_mod_mult
        mod_is_id nat_mod_distrib nat_add_distrib uint32_max_def)
qed



lemma max_uint32_nat[sepref_fr_rules]:
  \<open>(uncurry (return oo max), uncurry (RETURN oo max)) \<in> uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a
     uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def nat_of_uint32_max)

lemma array_set_hnr_u:
    \<open>CONSTRAINT is_pure A \<Longrightarrow>
    (uncurry2 (\<lambda>xs i. heap_array_set xs (nat_of_uint32 i)), uncurry2 (RETURN \<circ>\<circ>\<circ> op_list_set)) \<in>
     [pre_list_set]\<^sub>a (array_assn A)\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow> array_assn A\<close>
  by sepref_to_hoare
    (sep_auto simp: uint32_nat_rel_def br_def ex_assn_up_eq2 array_assn_def is_array_def
      hr_comp_def list_rel_pres_length list_rel_update)

lemma array_get_hnr_u:
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

lemma arl_get_hnr_u:
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
  \<open>nat_of_uint32 ai + nat_of_uint32 bi \<le> uint32_max \<Longrightarrow>
    nat_of_uint32 (ai + bi) = nat_of_uint32 ai + nat_of_uint32 bi\<close>
  by transfer (auto simp: unat_def uint_plus_if' nat_add_distrib uint32_max_def)

lemma uint32_nat_assn_plus[sepref_fr_rules]:
  \<open>(uncurry (return oo (+)), uncurry (RETURN oo (+))) \<in> [\<lambda>(m, n). m + n \<le> uint32_max]\<^sub>a
     uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def nat_of_uint32_add br_def)


lemma uint32_nat_assn_one:
  \<open>(uncurry0 (return 1), uncurry0 (RETURN 1)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def)

lemma uint32_nat_assn_zero:
  \<open>(uncurry0 (return 0), uncurry0 (RETURN 0)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def)

lemma nat_of_uint32_int32_assn:
  \<open>(return o id, RETURN o nat_of_uint32) \<in> uint32_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def)


definition zero_uint32_nat where
  [simp]: \<open>zero_uint32_nat = (0 :: nat)\<close>

lemma uint32_nat_assn_zero_uint32_nat[sepref_fr_rules]:
  \<open>(uncurry0 (return 0), uncurry0 (RETURN zero_uint32_nat)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def)

lemma nat_assn_zero:
  \<open>(uncurry0 (return 0), uncurry0 (RETURN 0)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def)

definition one_uint32_nat where
  [simp]: \<open>one_uint32_nat = (1 :: nat)\<close>

lemma one_uint32_nat[sepref_fr_rules]:
  \<open>(uncurry0 (return 1), uncurry0 (RETURN one_uint32_nat)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: uint32_nat_rel_def br_def)

lemma uint32_nat_assn_less[sepref_fr_rules]:
  \<open>(uncurry (return oo (<)), uncurry (RETURN oo (<))) \<in>
    uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def max_def
      nat_of_uint32_less_iff)

definition two_uint32_nat where [simp]: \<open>two_uint32_nat = (2 :: nat)\<close>

definition two_uint32 where
  [simp]: \<open>two_uint32 = (2 :: uint32)\<close>

lemma uint32_2_hnr[sepref_fr_rules]: \<open>(uncurry0 (return two_uint32), uncurry0 (RETURN two_uint32_nat)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def two_uint32_nat_def)


text \<open>Do NOT declare this theorem as \<open>sepref_fr_rules\<close> to avoid bad unexpected conversions.\<close>
lemma le_uint32_nat_hnr:
  \<open>(uncurry (return oo (\<lambda>a b. nat_of_uint32 a < b)), uncurry (RETURN oo (<))) \<in>
   uint32_nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def)

lemma le_nat_uint32_hnr:
  \<open>(uncurry (return oo (\<lambda>a b. a < nat_of_uint32 b)), uncurry (RETURN oo (<))) \<in>
   nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def)

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

code_printing constant fast_minus_nat' \<rightharpoonup> (SML_imp) "(Nat(integer'_of'_nat/ (_)/ -/ integer'_of'_nat/ (_)))"

lemma fast_minus_nat[sepref_fr_rules]:
  \<open>(uncurry (return oo fast_minus_nat), uncurry (RETURN oo fast_minus)) \<in>
     [\<lambda>(m, n). m \<ge> n]\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  by sepref_to_hoare
   (sep_auto simp: uint32_nat_rel_def br_def nat_of_uint32_le_minus
      nat_of_uint32_notle_minus nat_of_uint32_le_iff)

definition fast_minus_uint32 :: \<open>uint32 \<Rightarrow> uint32 \<Rightarrow> uint32\<close> where
  [simp]: \<open>fast_minus_uint32 = fast_minus\<close>

lemma fast_minus_uint32[sepref_fr_rules]:
  \<open>(uncurry (return oo fast_minus_uint32), uncurry (RETURN oo fast_minus)) \<in>
     [\<lambda>(m, n). m \<ge> n]\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  by sepref_to_hoare
   (sep_auto simp: uint32_nat_rel_def br_def nat_of_uint32_le_minus
      nat_of_uint32_notle_minus nat_of_uint32_le_iff)

lemma word_of_int_int_unat[simp]: \<open>word_of_int (int (unat x)) = x\<close>
  unfolding unat_def
  apply transfer
  by (simp add: bintr_ge0)

lemma uint32_of_nat_nat_of_uint32[simp]: \<open>uint32_of_nat (nat_of_uint32 x) = x\<close>
  unfolding uint32_of_nat_def
  by transfer auto


lemma uint32_nat_assn_0_eq: \<open>uint32_nat_assn 0 a = \<up> (a = 0)\<close>
  by (auto simp: uint32_nat_rel_def br_def pure_def nat_of_uint32_0_iff)

lemma uint32_nat_assn_nat_assn_nat_of_uint32:
   \<open>uint32_nat_assn aa a = nat_assn aa (nat_of_uint32 a)\<close>
  by (auto simp: pure_def uint32_nat_rel_def br_def)

definition sum_mod_uint32_max where
  \<open>sum_mod_uint32_max a b = (a + b) mod (uint32_max + 1)\<close>

lemma nat_of_uint32_plus:
  \<open>nat_of_uint32 (a + b) = (nat_of_uint32 a + nat_of_uint32 b) mod (uint32_max + 1)\<close>
  by transfer (auto simp: unat_word_ariths uint32_max_def)

lemma sum_mod_uint32_max: \<open>(uncurry (return oo (+)), uncurry (RETURN oo sum_mod_uint32_max)) \<in>
  uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a
  uint32_nat_assn\<close>
  by sepref_to_hoare
     (sep_auto simp: sum_mod_uint32_max_def uint32_nat_rel_def br_def nat_of_uint32_plus)

lemma le_uint32_nat_rel_hnr[sepref_fr_rules]:
  \<open>(uncurry (return oo (\<le>)), uncurry (RETURN oo (\<le>))) \<in>
   uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def nat_of_uint32_le_iff)

definition one_uint32 where
  \<open>one_uint32 = (1::uint32)\<close>

lemma one_uint32_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return 1), uncurry0 (RETURN one_uint32)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  by sepref_to_hoare (sep_auto simp: one_uint32_def)

lemma sum_uint32_assn[sepref_fr_rules]:
  \<open>(uncurry (return oo (+)), uncurry (RETURN oo (+))) \<in> uint32_assn\<^sup>k *\<^sub>a uint32_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  by sepref_to_hoare sep_auto

lemma Suc_uint32_nat_assn_hnr:
  \<open>(return o (\<lambda>n. n + 1), RETURN o Suc) \<in> [\<lambda>n. n < uint32_max]\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: br_def uint32_nat_rel_def nat_of_uint32_add)


subsubsection \<open>64-bits\<close>

definition uint64_nat_rel :: "(uint64 \<times> nat) set" where
  \<open>uint64_nat_rel = br nat_of_uint64 (\<lambda>_. True)\<close>

abbreviation uint64_nat_assn :: "nat \<Rightarrow> uint64 \<Rightarrow> assn" where
  \<open>uint64_nat_assn \<equiv> pure uint64_nat_rel\<close>


abbreviation uint64_rel :: \<open>(uint64 \<times> uint64) set\<close> where
  \<open>uint64_rel \<equiv> Id\<close>

abbreviation uint64_assn :: \<open>uint64 \<Rightarrow> uint64 \<Rightarrow> assn\<close> where
  \<open>uint64_assn \<equiv> id_assn\<close>

lemma op_eq_uint64:
  \<open>(uncurry (return oo ((=) :: uint64 \<Rightarrow> _)), uncurry (RETURN oo (=))) \<in>
    uint64_assn\<^sup>k *\<^sub>a uint64_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare sep_auto

lemma word_nat_of_uint64_Rep_inject[simp]: \<open>nat_of_uint64 ai = nat_of_uint64 bi \<longleftrightarrow> ai = bi\<close>
  by transfer simp

lemma op_eq_uint64_nat[sepref_fr_rules]:
  \<open>(uncurry (return oo ((=) :: uint64 \<Rightarrow> _)), uncurry (RETURN oo (=))) \<in>
    uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint64_nat_rel_def br_def)

instantiation uint64 :: default
begin
definition default_uint64 :: uint64 where
  \<open>default_uint64 = 0\<close>
instance
  ..
end

instance uint64 :: heap
  by standard (auto simp: inj_def exI[of _ nat_of_uint64])

lemma nat_of_uint64_012[simp]: \<open>nat_of_uint64 0 = 0\<close> \<open>nat_of_uint64 2 = 2\<close> \<open>nat_of_uint64 1 = 1\<close>
  by (transfer, auto)+

definition zero_uint64_nat where
  [simp]: \<open>zero_uint64_nat = (0 :: nat)\<close>

lemma uint64_nat_assn_zero_uint64_nat[sepref_fr_rules]:
  \<open>(uncurry0 (return 0), uncurry0 (RETURN zero_uint64_nat)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint64_nat_rel_def br_def)


definition uint64_max :: nat where
  \<open>uint64_max = 2 ^64 - 1\<close>

lemma nat_of_uint64_uint64_of_nat_id: \<open>n \<le> uint64_max \<Longrightarrow> nat_of_uint64 (uint64_of_nat n) = n\<close>
  unfolding uint64_of_nat_def uint64_max_def
  apply simp
  apply transfer
  apply (auto simp: unat_def)
  apply transfer
  by (auto simp: less_upper_bintrunc_id)

lemma nat_of_uint64_add:
  \<open>nat_of_uint64 ai + nat_of_uint64 bi \<le> uint64_max \<Longrightarrow>
    nat_of_uint64 (ai + bi) = nat_of_uint64 ai + nat_of_uint64 bi\<close>
  by transfer (auto simp: unat_def uint_plus_if' nat_add_distrib uint64_max_def)

lemma uint64_nat_assn_plus[sepref_fr_rules]:
  \<open>(uncurry (return oo (+)), uncurry (RETURN oo (+))) \<in> [\<lambda>(m, n). m + n \<le> uint64_max]\<^sub>a
     uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint64_nat_rel_def nat_of_uint64_add br_def)


definition one_uint64_nat where
  [simp]: \<open>one_uint64_nat = (1 :: nat)\<close>

lemma one_uint64_nat[sepref_fr_rules]:
  \<open>(uncurry0 (return 1), uncurry0 (RETURN one_uint64_nat)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: uint64_nat_rel_def br_def)

lemma uint64_less_than_0[iff]: \<open>(a::uint64) \<le> 0 \<longleftrightarrow> a = 0\<close>
  by transfer auto

lemma nat_of_uint64_less_iff: \<open>nat_of_uint64 a < nat_of_uint64 b \<longleftrightarrow> a < b\<close>
  apply transfer
  apply (auto simp: unat_def word_less_def)
  apply transfer
  by (smt bintr_ge0)

lemma uint64_nat_assn_less[sepref_fr_rules]:
  \<open>(uncurry (return oo (<)), uncurry (RETURN oo (<))) \<in>
    uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint64_nat_rel_def br_def max_def
      nat_of_uint64_less_iff)

lemma mult_uint64[sepref_fr_rules]:
 \<open>(uncurry (return oo ( * ) ), uncurry (RETURN oo ( * )))
  \<in>  uint64_assn\<^sup>k *\<^sub>a uint64_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  by sepref_to_hoare sep_auto

lemma shiftr_uint64[sepref_fr_rules]:
 \<open>(uncurry (return oo (>>) ), uncurry (RETURN oo (>>)))
  \<in>  uint64_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  by sepref_to_hoare sep_auto

text \<open>
  Taken from theory @{theory Native_Word.Uint64}. We use real Word64 instead of the unbounded integer as
  done by default.

  Remark that all this setup is taken from @{theory Native_Word.Uint64}.
\<close>
code_printing code_module "Uint64" \<rightharpoonup> (SML) \<open>(* Test that words can handle numbers between 0 and 63 *)
val _ = if 6 <= Word.wordSize then () else raise (Fail ("wordSize less than 6"));

structure Uint64 : sig
  eqtype uint64;
  val zero : uint64;
  val one : uint64;
  val fromInt : IntInf.int -> uint64;
  val toInt : uint64 -> IntInf.int;
  val toFixedInt : uint64 -> Int.int;
  val toLarge : uint64 -> LargeWord.word;
  val fromLarge : LargeWord.word -> uint64
  val fromFixedInt : Int.int -> uint64
  val plus : uint64 -> uint64 -> uint64;
  val minus : uint64 -> uint64 -> uint64;
  val times : uint64 -> uint64 -> uint64;
  val divide : uint64 -> uint64 -> uint64;
  val modulus : uint64 -> uint64 -> uint64;
  val negate : uint64 -> uint64;
  val less_eq : uint64 -> uint64 -> bool;
  val less : uint64 -> uint64 -> bool;
  val notb : uint64 -> uint64;
  val andb : uint64 -> uint64 -> uint64;
  val orb : uint64 -> uint64 -> uint64;
  val xorb : uint64 -> uint64 -> uint64;
  val shiftl : uint64 -> IntInf.int -> uint64;
  val shiftr : uint64 -> IntInf.int -> uint64;
  val shiftr_signed : uint64 -> IntInf.int -> uint64;
  val set_bit : uint64 -> IntInf.int -> bool -> uint64;
  val test_bit : uint64 -> IntInf.int -> bool;
end = struct

type uint64 = Word64.word;

val zero = (0wx0 : uint64);

val one = (0wx1 : uint64);

fun fromInt x = Word64.fromLargeInt (IntInf.toLarge x);

fun toInt x = IntInf.fromLarge (Word64.toLargeInt x);

fun toFixedInt x = Word64.toInt x;

fun fromLarge x = Word64.fromLarge x;

fun fromFixedInt x = Word64.fromInt x;

fun toLarge x = Word64.toLarge x;

fun plus x y = Word64.+(x, y);

fun minus x y = Word64.-(x, y);

fun negate x = Word64.~(x);

fun times x y = Word64.*(x, y);

fun divide x y = Word64.div(x, y);

fun modulus x y = Word64.mod(x, y);

fun less_eq x y = Word64.<=(x, y);

fun less x y = Word64.<(x, y);

fun set_bit x n b =
  let val mask = Word64.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))
  in if b then Word64.orb (x, mask)
     else Word64.andb (x, Word64.notb mask)
  end

fun shiftl x n =
  Word64.<< (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr x n =
  Word64.>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr_signed x n =
  Word64.~>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun test_bit x n =
  Word64.andb (x, Word64.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))) <> Word64.fromInt 0

val notb = Word64.notb

fun andb x y = Word64.andb(x, y);

fun orb x y = Word64.orb(x, y);

fun xorb x y = Word64.xorb(x, y);

end (*struct Uint64*)
\<close>

(* TODO Move *)
lemma mod2_bin_last: \<open>a mod 2 = 0 \<longleftrightarrow> \<not>bin_last a\<close>
  by (auto simp: bin_last_def)

lemma bitXOR_1_if_mod_2_int: \<open>bitOR L 1 = (if L mod 2 = 0 then L + 1 else L)\<close> for L :: int
  apply (rule bin_rl_eqI)
  unfolding bin_rest_OR bin_last_OR
   apply (auto simp: bin_rest_def bin_last_def)
  done

lemma bitOR_1_if_mod_2_nat:
  \<open>bitOR L 1 = (if L mod 2 = 0 then L + 1 else L)\<close>
  \<open>bitOR L (Suc 0) = (if L mod 2 = 0 then L + 1 else L)\<close> for L :: nat
proof -
  have H: \<open>bitOR L 1 =  L + (if bin_last (int L) then 0 else 1)\<close>
    unfolding bitOR_nat_def
    apply (auto simp: bitOR_nat_def bin_last_def
        bitXOR_1_if_mod_2_int)
    done
  show \<open>bitOR L 1 = (if L mod 2 = 0 then L + 1 else L)\<close>
    unfolding H
    apply (auto simp: bitOR_nat_def bin_last_def)
    apply presburger+
    done
  then show \<open>bitOR L (Suc 0) = (if L mod 2 = 0 then L + 1 else L)\<close>
    by simp
qed

lemma uint64_max_uint_def:\<open>unat (-1 :: 64 Word.word) = uint64_max\<close>
  by normalization

lemma nat_of_uint64_le_uint64_max: \<open>nat_of_uint64 x \<le> uint64_max\<close>
  apply transfer
  subgoal for x
    using word_le_nat_alt[of x \<open>- 1\<close>]
    unfolding uint64_max_def[symmetric] uint64_max_uint_def
    by auto
  done

lemma bitOR_1_if_mod_2_uint64: \<open>bitOR L 1 = (if L mod 2 = 0 then L + 1 else L)\<close> for L :: uint64
proof -
  have H: \<open>bitOR L 1 = a \<longleftrightarrow> bitOR (nat_of_uint64 L) 1 = nat_of_uint64 a\<close> for a
    apply transfer
    apply (rule iffI)
    subgoal for L a
      by (auto simp: unat_def uint_or bitOR_nat_def)
    subgoal for L a
      apply (auto simp: unat_def uint_or bitOR_nat_def eq_nat_nat_iff
          word_or_def)
      apply (subst (asm)eq_nat_nat_iff)
        apply (auto simp: uint_1 uint_ge_0 uint_or)
       apply (metis uint_1 uint_ge_0 uint_or)
      done
    done
  have K: \<open>L mod 2 = 0 \<longleftrightarrow> nat_of_uint64 L mod 2 = 0\<close>
    apply transfer
    subgoal for L
      using unat_mod[of L 2]
      by (auto simp: unat_eq_0)
    done
  have L: \<open>nat_of_uint64 (if L mod 2 = 0 then L + 1 else L) =
      (if nat_of_uint64 L mod 2 = 0 then nat_of_uint64 L + 1 else nat_of_uint64 L)\<close>
    using nat_of_uint64_le_uint64_max[of L]
    by (auto simp: K nat_of_uint64_add uint64_max_def)

  show ?thesis
    apply (subst H)
    unfolding bitOR_1_if_mod_2_nat[symmetric] L ..
qed

lemma nat_of_uint64_plus:
  \<open>nat_of_uint64 (a + b) = (nat_of_uint64 a + nat_of_uint64 b) mod (uint64_max + 1)\<close>
  by transfer (auto simp: unat_word_ariths uint64_max_def)


lemma nat_and:
  \<open>ai\<ge> 0 \<Longrightarrow> bi \<ge> 0 \<Longrightarrow> nat (ai AND bi) = nat ai AND nat bi\<close>
  by (auto simp: bitAND_nat_def)

lemma nat_of_uint64_and:
  \<open>nat_of_uint64 ai \<le> uint64_max \<Longrightarrow> nat_of_uint64 bi \<le> uint64_max \<Longrightarrow>
    nat_of_uint64 (ai AND bi) = nat_of_uint64 ai AND nat_of_uint64 bi\<close>
  unfolding uint64_max_def
  by transfer (auto simp: unat_def uint_and nat_and)

lemma bitAND_uint64_max_hnr[sepref_fr_rules]:
  \<open>(uncurry (return oo  (AND)), uncurry (RETURN oo (AND)))
   \<in> [\<lambda>(a, b). a \<le> uint64_max \<and> b \<le> uint64_max]\<^sub>a
     uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: uint64_nat_rel_def br_def nat_of_uint64_plus
      nat_of_uint64_and)


definition two_uint64_nat :: nat where
  [simp]: \<open>two_uint64_nat = 2\<close>

lemma two_uint64_nat[sepref_fr_rules]:
  \<open>(uncurry0 (return 2), uncurry0 (RETURN two_uint64_nat))
   \<in>  unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: two_uint64_nat_def uint64_nat_rel_def br_def)

lemma nat_or:
  \<open>ai\<ge> 0 \<Longrightarrow> bi \<ge> 0 \<Longrightarrow> nat (ai OR bi) = nat ai OR nat bi\<close>
  by (auto simp: bitOR_nat_def)

lemma nat_of_uint64_or:
  \<open>nat_of_uint64 ai \<le> uint64_max \<Longrightarrow> nat_of_uint64 bi \<le> uint64_max \<Longrightarrow>
    nat_of_uint64 (ai OR bi) = nat_of_uint64 ai OR nat_of_uint64 bi\<close>
  unfolding uint64_max_def
  by transfer (auto simp: unat_def uint_or nat_or)

lemma bitOR_uint64_max_hnr[sepref_fr_rules]:
  \<open>(uncurry (return oo  (OR)), uncurry (RETURN oo (OR)))
   \<in> [\<lambda>(a, b). a \<le> uint64_max \<and> b \<le> uint64_max]\<^sub>a
     uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: uint64_nat_rel_def br_def nat_of_uint64_plus
      nat_of_uint64_or)

lemma Suc_0_le_uint64_max: \<open>Suc 0 \<le> uint64_max\<close>
  by (auto simp: uint64_max_def)

lemma nat_of_uint64_le_iff: \<open>nat_of_uint64 a \<le> nat_of_uint64 b \<longleftrightarrow> a \<le> b\<close>
  apply transfer
  by (auto simp: unat_def word_less_def nat_le_iff word_le_def)

lemma nat_of_uint64_notle_minus:
  \<open>\<not> ai < bi \<Longrightarrow>
       nat_of_uint64 (ai - bi) = nat_of_uint64 ai - nat_of_uint64 bi\<close>
  apply transfer
  unfolding unat_def
  by (subst uint_sub_lem[THEN iffD1])
    (auto simp: unat_def uint_nonnegative nat_diff_distrib word_le_def[symmetric] intro: leI)

lemma fast_minus_uint64_nat[sepref_fr_rules]:
  \<open>(uncurry (return oo fast_minus), uncurry (RETURN oo fast_minus))
   \<in> [\<lambda>(a, b). a \<ge> b]\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  by (sepref_to_hoare)
    (sep_auto simp: uint64_nat_rel_def br_def nat_of_uint64_notle_minus
      nat_of_uint64_less_iff nat_of_uint64_le_iff)

lemma fast_minus_uint64[sepref_fr_rules]:
  \<open>(uncurry (return oo fast_minus), uncurry (RETURN oo fast_minus))
   \<in> [\<lambda>(a, b). a \<ge> b]\<^sub>a uint64_assn\<^sup>k *\<^sub>a uint64_assn\<^sup>k \<rightarrow> uint64_assn\<close>
  by (sepref_to_hoare)
    (sep_auto simp: uint64_nat_rel_def br_def nat_of_uint64_notle_minus
      nat_of_uint64_less_iff nat_of_uint64_le_iff)

definition sum_mod_uint64_max where
  \<open>sum_mod_uint64_max a b = (a + b) mod (uint64_max + 1)\<close>

definition uint32_max_uint32 :: uint32 where
  \<open>uint32_max_uint32 = - 1\<close>

lemma nat_of_uint32_uint32_max_uint32[simp]:
   \<open>nat_of_uint32 (uint32_max_uint32) = uint32_max\<close>
  by eval

lemma sum_mod_uint64_max_le_uint64_max[simp]: \<open>sum_mod_uint64_max a b \<le> uint64_max\<close>
  unfolding sum_mod_uint64_max_def
  by auto

lemma sum_mod_uint64_max_hnr[sepref_fr_rules]:
  \<open>(uncurry (return oo  (+)), uncurry (RETURN oo sum_mod_uint64_max))
   \<in> uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  apply sepref_to_hoare
  apply (sep_auto simp: uint64_nat_rel_def br_def nat_of_uint64_plus
      sum_mod_uint64_max_def)
  done

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

lemma uint64_of_uint32_hnr[sepref_fr_rules]:
  \<open>(return o uint64_of_uint32, RETURN o uint64_of_uint32) \<in> uint32_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  by sepref_to_hoare (sep_auto simp: br_def)

definition zero_uint64 where
  \<open>zero_uint64 \<equiv> (0 :: uint64)\<close>

lemma zero_uint64_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return 0), uncurry0 (RETURN zero_uint64)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  by sepref_to_hoare (sep_auto simp: zero_uint64_def)

definition zero_uint32 where
  \<open>zero_uint32 \<equiv> (0 :: uint32)\<close>

lemma zero_uint32_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return 0), uncurry0 (RETURN zero_uint32)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  by sepref_to_hoare (sep_auto simp: zero_uint32_def)

lemma zero_uin64_hnr: \<open>(uncurry0 (return 0), uncurry0 (RETURN 0)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  by sepref_to_hoare sep_auto

definition two_uint64 where \<open>two_uint64 = (2 :: uint64)\<close>

lemma two_uin64_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return 2), uncurry0 (RETURN two_uint64)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  by sepref_to_hoare (sep_auto simp: two_uint64_def)

lemma two_uint32_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return 2), uncurry0 (RETURN two_uint32)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  by sepref_to_hoare sep_auto

lemma sum_uint64_assn:
  \<open>(uncurry (return oo (+)), uncurry (RETURN oo (+))) \<in> uint64_assn\<^sup>k *\<^sub>a uint64_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  by (sepref_to_hoare) sep_auto

paragraph \<open>Conversions\<close>

definition nat_of_uint64_spec :: \<open>nat \<Rightarrow> nat\<close> where
  [simp]: \<open>nat_of_uint64_spec n = n\<close>

lemma nat_of_uint64_spec_hnr[sepref_fr_rules]:
  \<open>(return o uint64_of_nat, RETURN o nat_of_uint64_spec) \<in>
     [\<lambda>n. n \<le> uint64_max]\<^sub>a nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: uint64_nat_rel_def br_def nat_of_uint64_spec_def
      nat_of_uint64_uint64_of_nat_id)


definition nat_of_uint32_spec :: \<open>nat \<Rightarrow> nat\<close> where
  [simp]: \<open>nat_of_uint32_spec n = n\<close>

lemma nat_of_uint32_spec_hnr[sepref_fr_rules]:
  \<open>(return o uint32_of_nat, RETURN o nat_of_uint32_spec) \<in>
     [\<lambda>n. n \<le> uint32_max]\<^sub>a nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: uint32_nat_rel_def br_def nat_of_uint32_spec_def
      nat_of_uint32_uint32_of_nat_id)

definition nat_of_uint64_conv :: \<open>nat \<Rightarrow> nat\<close> where
[simp]: \<open>nat_of_uint64_conv i = i\<close>

lemma nat_of_uint64_conv_hnr[sepref_fr_rules]:
  \<open>(return o nat_of_uint64, RETURN o nat_of_uint64_conv) \<in> uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint64_nat_rel_def br_def nat_of_uint64_conv_def)

lemma nat_of_uint64[sepref_fr_rules]:
  \<open>(return o nat_of_uint64, RETURN o nat_of_uint64) \<in>
    (uint64_assn)\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint64_nat_rel_def br_def
     nat_of_uint64_conv_def nat_of_uint64_def
    split: option.splits)

definition nat_of_uint32_conv :: \<open>nat \<Rightarrow> nat\<close> where
[simp]: \<open>nat_of_uint32_conv i = i\<close>

lemma nat_of_uint32_conv_hnr[sepref_fr_rules]:
  \<open>(return o nat_of_uint32, RETURN o nat_of_uint32_conv) \<in> uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def nat_of_uint32_conv_def)

(* TODO Move inside this file + remove theorems about nat_of_uint32 2 = 2 *)
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
  have [simp]: \<open>nat_of_uint32 (xi mod 2 ^ 32) = nat_of_uint32 xi\<close>
    apply transfer
    prefer 2
      apply (rule transfer_pow_uint32)
    subgoal for xi
      using uint_word_ariths(1)[of xi 0]
      supply [[show_types]]
      apply auto
      apply (rule word_uint_eq_iff[THEN iffD2])
      apply (subst uint_mod_alt)
      by auto
    done

  show ?thesis
    by (rule word_nat_of_uint32_Rep_inject[THEN iffD1]) auto
qed

lemma nat_of_uint32_numeral_mod_232:
  \<open>nat_of_uint32 (numeral n) = numeral n mod 2^32\<close>
  apply transfer
  apply (subst unat_numeral)
  by auto

lemma int_of_uint32_alt_def: \<open>int_of_uint32 n = int (nat_of_uint32 n)\<close>
   by (simp add: int_of_uint32.rep_eq nat_of_uint32.rep_eq unat_def)

lemma int_of_uint32_numeral[simp]:
  \<open>numeral n \<le> ((2 ^ 32 - 1)::nat) \<Longrightarrow> int_of_uint32 (numeral n) = numeral n\<close>
  by (subst int_of_uint32_alt_def) simp

lemma nat_of_uint64_distrib_mult2:
  assumes \<open>nat_of_uint64 xi \<le> uint64_max div 2\<close>
  shows \<open>nat_of_uint64 (2 * xi) = 2 * nat_of_uint64 xi\<close>
proof -
  show ?thesis
    using assms unfolding uint64_max_def
    apply (case_tac \<open>xi = 0\<close>)
    subgoal by auto
    subgoal by transfer (auto simp: unat_def uint_word_ariths nat_mult_distrib mult_mod_mod_mult)
    done
qed

lemma (in -)nat_of_uint64_distrib_mult2_plus1:
  assumes \<open>nat_of_uint64 xi \<le> uint64_max div 2\<close>
  shows \<open>nat_of_uint64 (2 * xi + 1) = 2 * nat_of_uint64 xi + 1\<close>
proof -
  show ?thesis
    using assms by transfer (auto simp: unat_def uint_word_ariths nat_mult_distrib mult_mod_mod_mult
        nat_mod_distrib nat_add_distrib uint64_max_def)
qed

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
   by (simp add: int_of_uint64.rep_eq nat_of_uint64.rep_eq unat_def)

lemma int_of_uint64_numeral[simp]:
  \<open>numeral n \<le> ((2 ^ 64 - 1)::nat) \<Longrightarrow> int_of_uint64 (numeral n) = numeral n\<close>
  by (subst int_of_uint64_alt_def) simp

lemma nat_of_uint32_numeral_iff[simp]:
  \<open>numeral n \<le> ((2 ^ 32 - 1)::nat) \<Longrightarrow> nat_of_uint32 a = numeral n \<longleftrightarrow> a = numeral n\<close>
  apply (rule iffI)
  prefer 2 apply (solves simp)
  using word_nat_of_uint32_Rep_inject by fastforce

lemma nat_of_uint64_numeral_iff[simp]:
  \<open>numeral n \<le> ((2 ^ 64 - 1)::nat) \<Longrightarrow> nat_of_uint64 a = numeral n \<longleftrightarrow> a = numeral n\<close>
  apply (rule iffI)
  prefer 2 apply (solves simp)
  using word_nat_of_uint64_Rep_inject by fastforce

(* End Move *)

end
