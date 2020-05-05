theory WB_Word_Assn
imports  Refine_Imperative_HOL.IICF
  More_Sepref.WB_Word Isabelle_LLVM.Bits_Natural
  More_Sepref.WB_More_Refinement WB_More_IICF_SML
begin

context includes natural.lifting begin
lemma [code]:
  "integer_of_natural (m >> n) = (integer_of_natural m) >> n"
  apply transfer
  by (smt integer_of_natural.rep_eq msb_int_def msb_shiftr nat_eq_iff2 negative_zle
      shiftr_int_code shiftr_int_def shiftr_nat_def shiftr_natural.rep_eq
      type_definition.Rep_inject type_definition_integer)

lemma [code]:
  "integer_of_natural (m << n) = (integer_of_natural m) << n"
  apply transfer
  by (smt integer_of_natural.rep_eq msb_int_def msb_shiftl nat_eq_iff2 negative_zle
      shiftl_int_code shiftl_int_def shiftl_nat_def shiftl_natural.rep_eq
      type_definition.Rep_inject type_definition_integer)

end


lemma shiftl_0_uint32[simp]: \<open>n << 0 = n\<close> for n :: uint32
  by transfer auto

lemma shiftl_Suc_uint32: \<open>n << Suc m = (n << m) << 1\<close> for n :: uint32
  apply transfer
  apply transfer
  by auto




subsection \<open>More Setup for Fixed Size Natural Numbers\<close>

subsubsection \<open>Words\<close>

abbreviation word_nat_assn :: "nat \<Rightarrow> 'a::len0 Word.word \<Rightarrow> assn" where
  \<open>word_nat_assn \<equiv> pure word_nat_rel\<close>

lemma op_eq_word_nat:
  \<open>(uncurry (return oo ((=) :: 'a :: len Word.word \<Rightarrow> _)), uncurry (RETURN oo (=))) \<in>
    word_nat_assn\<^sup>k *\<^sub>a word_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: word_nat_rel_def br_def)


abbreviation uint32_nat_assn :: "nat \<Rightarrow> uint32 \<Rightarrow> assn" where
  \<open>uint32_nat_assn \<equiv> pure uint32_nat_rel\<close>

lemma op_eq_uint32_nat[sepref_fr_rules]:
  \<open>(uncurry (return oo ((=) :: uint32 \<Rightarrow> _)), uncurry (RETURN oo (=))) \<in>
    uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def)

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

lemma uint32_nat_assn_minus:
  \<open>(uncurry (return oo uint32_safe_minus), uncurry (RETURN oo (-))) \<in>
     uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: uint32_nat_rel_def nat_of_uint32_le_minus
      br_def uint32_safe_minus_def nat_of_uint32_notle_minus)

lemma [safe_constraint_rules]:
  \<open>CONSTRAINT IS_LEFT_UNIQUE uint32_nat_rel\<close>
  \<open>CONSTRAINT IS_RIGHT_UNIQUE uint32_nat_rel\<close>
  by (auto simp: IS_LEFT_UNIQUE_def single_valued_def uint32_nat_rel_def br_def)

lemma shiftr1[sepref_fr_rules]:
   \<open>(uncurry (return oo ((>>))), uncurry (RETURN oo (>>))) \<in> uint32_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a
      uint32_assn\<close>
  by sepref_to_hoare (sep_auto simp: shiftr1_def uint32_nat_rel_def br_def)

lemma shiftl1[sepref_fr_rules]: \<open>(return o shiftl1, RETURN o shiftl1) \<in> nat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare sep_auto

lemma nat_of_uint32_rule[sepref_fr_rules]:
  \<open>(return o nat_of_uint32, RETURN o nat_of_uint32) \<in> uint32_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare sep_auto


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


lemma uint32_nat_assn_zero_uint32_nat[sepref_fr_rules]:
  \<open>(uncurry0 (return 0), uncurry0 (RETURN zero_uint32_nat)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def)

lemma nat_assn_zero:
  \<open>(uncurry0 (return 0), uncurry0 (RETURN 0)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def)

lemma one_uint32_nat[sepref_fr_rules]:
  \<open>(uncurry0 (return 1), uncurry0 (RETURN one_uint32_nat)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: uint32_nat_rel_def br_def)

lemma uint32_nat_assn_less[sepref_fr_rules]:
  \<open>(uncurry (return oo (<)), uncurry (RETURN oo (<))) \<in>
    uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def max_def
      nat_of_uint32_less_iff)

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

lemma uint32_nat_assn_0_eq: \<open>uint32_nat_assn 0 a = \<up> (a = 0)\<close>
  by (auto simp: uint32_nat_rel_def br_def pure_def nat_of_uint32_0_iff)

lemma uint32_nat_assn_nat_assn_nat_of_uint32:
   \<open>uint32_nat_assn aa a = nat_assn aa (nat_of_uint32 a)\<close>
  by (auto simp: pure_def uint32_nat_rel_def br_def)

lemma sum_mod_uint32_max: \<open>(uncurry (return oo (+)), uncurry (RETURN oo sum_mod_uint32_max)) \<in>
  uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a
  uint32_nat_assn\<close>
  by sepref_to_hoare
     (sep_auto simp: sum_mod_uint32_max_def uint32_nat_rel_def br_def nat_of_uint32_plus)

lemma le_uint32_nat_rel_hnr[sepref_fr_rules]:
  \<open>(uncurry (return oo (\<le>)), uncurry (RETURN oo (\<le>))) \<in>
   uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def nat_of_uint32_le_iff)

lemma one_uint32_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return 1), uncurry0 (RETURN one_uint32)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  by sepref_to_hoare (sep_auto simp: one_uint32_def)

lemma sum_uint32_assn[sepref_fr_rules]:
  \<open>(uncurry (return oo (+)), uncurry (RETURN oo (+))) \<in> uint32_assn\<^sup>k *\<^sub>a uint32_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  by sepref_to_hoare sep_auto

lemma Suc_uint32_nat_assn_hnr:
  \<open>(return o (\<lambda>n. n + 1), RETURN o Suc) \<in> [\<lambda>n. n < uint32_max]\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: br_def uint32_nat_rel_def nat_of_uint32_add)

lemma minus_uint32_assn:
 \<open>(uncurry (return oo (-)), uncurry (RETURN oo (-))) \<in> uint32_assn\<^sup>k *\<^sub>a uint32_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
 by sepref_to_hoare sep_auto

lemma bitAND_uint32_nat_assn[sepref_fr_rules]:
  \<open>(uncurry (return oo (AND)), uncurry (RETURN oo (AND))) \<in>
    uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: uint32_nat_rel_def br_def nat_of_uint32_ao)

lemma bitAND_uint32_assn[sepref_fr_rules]:
  \<open>(uncurry (return oo (AND)), uncurry (RETURN oo (AND))) \<in>
    uint32_assn\<^sup>k *\<^sub>a uint32_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: uint32_nat_rel_def br_def nat_of_uint32_ao)

lemma bitOR_uint32_nat_assn[sepref_fr_rules]:
  \<open>(uncurry (return oo (OR)), uncurry (RETURN oo (OR))) \<in>
    uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: uint32_nat_rel_def br_def nat_of_uint32_ao)

lemma bitOR_uint32_assn[sepref_fr_rules]:
  \<open>(uncurry (return oo (OR)), uncurry (RETURN oo (OR))) \<in>
    uint32_assn\<^sup>k *\<^sub>a uint32_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: uint32_nat_rel_def br_def nat_of_uint32_ao)

lemma uint32_nat_assn_mult:
  \<open>(uncurry (return oo ((*))), uncurry (RETURN oo ((*)))) \<in> [\<lambda>(a, b). a * b \<le> uint32_max]\<^sub>a
      uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  by sepref_to_hoare
     (sep_auto simp: uint32_nat_rel_def br_def nat_of_uint32_mult_le)


lemma [sepref_fr_rules]:
  \<open>(uncurry (return oo (div)), uncurry (RETURN oo (div))) \<in>
     uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare
   (sep_auto simp: uint32_nat_rel_def br_def nat_of_uint32_div)


subsubsection \<open>64-bits\<close>

lemmas [id_rules] =
  itypeI[Pure.of 0 "TYPE (uint64)"]
  itypeI[Pure.of 1 "TYPE (uint64)"]

lemma param_uint64[param, sepref_import_param]:
  "(0, 0::uint64) \<in> Id"
  "(1, 1::uint64) \<in> Id"
  by (rule IdI)+

abbreviation uint64_nat_assn :: "nat \<Rightarrow> uint64 \<Rightarrow> assn" where
  \<open>uint64_nat_assn \<equiv> pure uint64_nat_rel\<close>


abbreviation uint64_assn :: \<open>uint64 \<Rightarrow> uint64 \<Rightarrow> assn\<close> where
  \<open>uint64_assn \<equiv> id_assn\<close>

lemma op_eq_uint64:
  \<open>(uncurry (return oo ((=) :: uint64 \<Rightarrow> _)), uncurry (RETURN oo (=))) \<in>
    uint64_assn\<^sup>k *\<^sub>a uint64_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare sep_auto

lemma op_eq_uint64_nat[sepref_fr_rules]:
  \<open>(uncurry (return oo ((=) :: uint64 \<Rightarrow> _)), uncurry (RETURN oo (=))) \<in>
    uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint64_nat_rel_def br_def)

lemma uint64_nat_assn_zero_uint64_nat[sepref_fr_rules]:
  \<open>(uncurry0 (return 0), uncurry0 (RETURN zero_uint64_nat)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint64_nat_rel_def br_def)

lemma uint64_nat_assn_plus[sepref_fr_rules]:
  \<open>(uncurry (return oo (+)), uncurry (RETURN oo (+))) \<in> [\<lambda>(m, n). m + n \<le> uint64_max]\<^sub>a
     uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint64_nat_rel_def nat_of_uint64_add br_def)


lemma one_uint64_nat[sepref_fr_rules]:
  \<open>(uncurry0 (return 1), uncurry0 (RETURN one_uint64_nat)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: uint64_nat_rel_def br_def)


lemma uint64_nat_assn_less[sepref_fr_rules]:
  \<open>(uncurry (return oo (<)), uncurry (RETURN oo (<))) \<in>
    uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint64_nat_rel_def br_def max_def
      nat_of_uint64_less_iff)

lemma mult_uint64[sepref_fr_rules]:
 \<open>(uncurry (return oo (*) ), uncurry (RETURN oo (*)))
  \<in>  uint64_assn\<^sup>k *\<^sub>a uint64_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  by sepref_to_hoare sep_auto

lemma shiftr_uint64[sepref_fr_rules]:
 \<open>(uncurry (return oo (>>) ), uncurry (RETURN oo (>>)))
    \<in> uint64_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
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

lemma bitAND_uint64_max_hnr[sepref_fr_rules]:
  \<open>(uncurry (return oo  (AND)), uncurry (RETURN oo (AND)))
   \<in> [\<lambda>(a, b). a \<le> uint64_max \<and> b \<le> uint64_max]\<^sub>a
     uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: uint64_nat_rel_def br_def nat_of_uint64_plus
      nat_of_uint64_and)


lemma two_uint64_nat[sepref_fr_rules]:
  \<open>(uncurry0 (return 2), uncurry0 (RETURN two_uint64_nat))
   \<in>  unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint64_nat_rel_def br_def)

lemma bitOR_uint64_max_hnr[sepref_fr_rules]:
  \<open>(uncurry (return oo  (OR)), uncurry (RETURN oo (OR)))
   \<in> [\<lambda>(a, b). a \<le> uint64_max \<and> b \<le> uint64_max]\<^sub>a
     uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: uint64_nat_rel_def br_def nat_of_uint64_plus
      nat_of_uint64_or)

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

lemma minus_uint64_nat_assn[sepref_fr_rules]:
  \<open>(uncurry (return oo (-)), uncurry (RETURN oo (-))) \<in>
    [\<lambda>(a, b). a \<ge> b]\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: uint64_nat_rel_def br_def nat_of_uint64_ge_minus
   nat_of_uint64_le_iff)

lemma le_uint64_nat_assn_hnr[sepref_fr_rules]:
  \<open>(uncurry (return oo (\<le>)), uncurry (RETURN oo (\<le>))) \<in> uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare
   (sep_auto simp: uint64_nat_rel_def br_def nat_of_uint64_le_iff)

lemma sum_mod_uint64_max_hnr[sepref_fr_rules]:
  \<open>(uncurry (return oo  (+)), uncurry (RETURN oo sum_mod_uint64_max))
   \<in> uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  apply sepref_to_hoare
  apply (sep_auto simp: uint64_nat_rel_def br_def nat_of_uint64_plus
      sum_mod_uint64_max_def)
  done

lemma zero_uint64_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return 0), uncurry0 (RETURN zero_uint64)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  by sepref_to_hoare (sep_auto simp: zero_uint64_def)


lemma zero_uint32_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return 0), uncurry0 (RETURN zero_uint32)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  by sepref_to_hoare (sep_auto simp: zero_uint32_def)

lemma zero_uin64_hnr: \<open>(uncurry0 (return 0), uncurry0 (RETURN 0)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  by sepref_to_hoare sep_auto

lemma two_uin64_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return 2), uncurry0 (RETURN two_uint64)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  by sepref_to_hoare (sep_auto simp: two_uint64_def)

lemma two_uint32_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return 2), uncurry0 (RETURN two_uint32)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  by sepref_to_hoare sep_auto

lemma sum_uint64_assn:
  \<open>(uncurry (return oo (+)), uncurry (RETURN oo (+))) \<in> uint64_assn\<^sup>k *\<^sub>a uint64_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  by (sepref_to_hoare) sep_auto

lemma bitAND_uint64_nat_assn[sepref_fr_rules]:
  \<open>(uncurry (return oo (AND)), uncurry (RETURN oo (AND))) \<in>
    uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: uint64_nat_rel_def br_def nat_of_uint64_ao)

lemma bitAND_uint64_assn[sepref_fr_rules]:
  \<open>(uncurry (return oo (AND)), uncurry (RETURN oo (AND))) \<in>
    uint64_assn\<^sup>k *\<^sub>a uint64_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: uint64_nat_rel_def br_def nat_of_uint64_ao)

lemma bitOR_uint64_nat_assn[sepref_fr_rules]:
  \<open>(uncurry (return oo (OR)), uncurry (RETURN oo (OR))) \<in>
    uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: uint64_nat_rel_def br_def nat_of_uint64_ao)

lemma bitOR_uint64_assn[sepref_fr_rules]:
  \<open>(uncurry (return oo (OR)), uncurry (RETURN oo (OR))) \<in>
    uint64_assn\<^sup>k *\<^sub>a uint64_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: uint64_nat_rel_def br_def nat_of_uint64_ao)

lemma nat_of_uint64_mult_le:
   \<open>nat_of_uint64 ai * nat_of_uint64 bi \<le> uint64_max \<Longrightarrow>
       nat_of_uint64 (ai * bi) = nat_of_uint64 ai * nat_of_uint64 bi\<close>
  apply transfer
  by (auto simp: unat_word_ariths uint64_max_def)

lemma uint64_nat_assn_mult:
  \<open>(uncurry (return oo ((*))), uncurry (RETURN oo ((*)))) \<in> [\<lambda>(a, b). a * b \<le> uint64_max]\<^sub>a
      uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  by sepref_to_hoare
     (sep_auto simp: uint64_nat_rel_def br_def nat_of_uint64_mult_le)

lemma uint64_max_uint64_nat_assn:
 \<open>(uncurry0 (return 18446744073709551615), uncurry0 (RETURN uint64_max)) \<in>
  unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint64_nat_rel_def br_def uint64_max_def)

lemma uint64_max_nat_assn[sepref_fr_rules]:
 \<open>(uncurry0 (return 18446744073709551615), uncurry0 (RETURN uint64_max)) \<in>
  unit_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint64_nat_rel_def br_def uint64_max_def)


subsubsection \<open>Conversions\<close>

paragraph \<open>From nat to 64 bits\<close>

lemma uint64_of_nat_conv_hnr[sepref_fr_rules]:
  \<open>(return o uint64_of_nat, RETURN o uint64_of_nat_conv) \<in>
    [\<lambda>n. n \<le> uint64_max]\<^sub>a nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint64_nat_rel_def br_def uint64_of_nat_conv_def
      nat_of_uint64_uint64_of_nat_id)


paragraph \<open>From nat to 32 bits\<close>

lemma nat_of_uint32_spec_hnr[sepref_fr_rules]:
  \<open>(return o uint32_of_nat, RETURN o nat_of_uint32_spec) \<in>
     [\<lambda>n. n \<le> uint32_max]\<^sub>a nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: uint32_nat_rel_def br_def nat_of_uint32_uint32_of_nat_id)


paragraph \<open>From 64 to nat bits\<close>

lemma nat_of_uint64_conv_hnr[sepref_fr_rules]:
  \<open>(return o nat_of_uint64, RETURN o nat_of_uint64_conv) \<in> uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint64_nat_rel_def br_def)

lemma nat_of_uint64[sepref_fr_rules]:
  \<open>(return o nat_of_uint64, RETURN o nat_of_uint64) \<in>
    (uint64_assn)\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint64_nat_rel_def br_def
     nat_of_uint64_def
    split: option.splits)

paragraph \<open>From 32 to nat bits\<close>

lemma nat_of_uint32_conv_hnr[sepref_fr_rules]:
  \<open>(return o nat_of_uint32, RETURN o nat_of_uint32_conv) \<in> uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def nat_of_uint32_conv_def)

lemma convert_to_uint32_hnr[sepref_fr_rules]:
  \<open>(return o uint32_of_nat, RETURN o convert_to_uint32)
    \<in> [\<lambda>n. n \<le> uint32_max]\<^sub>a nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: uint32_nat_rel_def br_def uint32_max_def nat_of_uint32_uint32_of_nat_id)


paragraph \<open>From 32 to 64 bits\<close>

lemma uint64_of_uint32_hnr[sepref_fr_rules]:
  \<open>(return o uint64_of_uint32, RETURN o uint64_of_uint32) \<in> uint32_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  by sepref_to_hoare (sep_auto simp: br_def)

lemma uint64_of_uint32_conv_hnr[sepref_fr_rules]:
  \<open>(return o uint64_of_uint32, RETURN o uint64_of_uint32_conv) \<in>
    uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: br_def uint32_nat_rel_def uint64_nat_rel_def
      nat_of_uint32_code nat_of_uint64_uint64_of_uint32)


paragraph \<open>From 64 to 32 bits\<close>

lemma uint32_of_uint64_conv_hnr[sepref_fr_rules]:
  \<open>(return o uint32_of_uint64, RETURN o uint32_of_uint64_conv) \<in>
     [\<lambda>a. a \<le> uint32_max]\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: uint32_of_uint64_def uint32_nat_rel_def br_def nat_of_uint64_le_iff
      nat_of_uint32_uint32_of_nat_id uint64_nat_rel_def)


paragraph \<open>From nat to 32 bits\<close>


lemma (in -) uint32_of_nat[sepref_fr_rules]:
  \<open>(return o uint32_of_nat, RETURN o uint32_of_nat) \<in> [\<lambda>n. n \<le> uint32_max]\<^sub>a nat_assn\<^sup>k \<rightarrow> uint32_assn\<close>
  by sepref_to_hoare sep_auto

paragraph \<open>Setup for numerals\<close>

text \<open>The refinement framework still defaults to \<^typ>\<open>nat\<close>, making the constants
like \<^term>\<open>two_uint32_nat\<close> still useful, but they can be omitted in some cases: For example, in
\<^term>\<open>2 + n\<close>, \<^term>\<open>2 :: nat\<close> will be refined to \<^typ>\<open>nat\<close> (independently of \<^term>\<open>n\<close>). However,
if the expression is \<^term>\<open>n + 2\<close> and if  \<^term>\<open>n\<close> is refined to \<^typ>\<open>uint32\<close>, then everything will
work as one might expect.
\<close>

lemmas [id_rules] =
  itypeI[Pure.of numeral "TYPE (num \<Rightarrow> uint32)"]
  itypeI[Pure.of numeral "TYPE (num \<Rightarrow> uint64)"]

lemma id_uint32_const[id_rules]: "(PR_CONST (a::uint32)) ::\<^sub>i TYPE(uint32)" by simp
lemma id_uint64_const[id_rules]: "(PR_CONST (a::uint64)) ::\<^sub>i TYPE(uint64)" by simp

lemma param_uint32_numeral[sepref_import_param]:
  \<open>(numeral n, numeral n) \<in> uint32_rel\<close>
  by auto

lemma param_uint64_numeral[sepref_import_param]:
  \<open>(numeral n, numeral n) \<in> uint64_rel\<close>
  by auto


(* TODO Move + is there a way to generate these constants on the fly? *)
locale nat_of_uint64_loc =
  fixes n :: num
  assumes le_uint64_max: \<open>numeral n \<le> uint64_max\<close>
begin

definition nat_of_uint64_numeral :: nat where
  [simp]: \<open>nat_of_uint64_numeral = (numeral n)\<close>

definition nat_of_uint64 :: uint64 where
 [simp]: \<open>nat_of_uint64 = (numeral n)\<close>

lemma nat_of_uint64_numeral_hnr:
  \<open>(uncurry0 (return nat_of_uint64), uncurry0 (PR_CONST (RETURN nat_of_uint64_numeral)))
      \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  using le_uint64_max
  by (sepref_to_hoare; sep_auto simp: uint64_nat_rel_def br_def uint64_max_def)
sepref_register nat_of_uint64_numeral
end

(* TODO a solution based on that, potentially with a simproc, would make wonders! *)
lemma (in -) [sepref_fr_rules]:
  \<open>CONSTRAINT (\<lambda>n. numeral n \<le> uint64_max) n \<Longrightarrow>
(uncurry0 (return (nat_of_uint64_loc.nat_of_uint64 n)),
     uncurry0 (RETURN (PR_CONST (nat_of_uint64_loc.nat_of_uint64_numeral n))))
   \<in>  unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  using nat_of_uint64_loc.nat_of_uint64_numeral_hnr[of n]
  by (auto simp: nat_of_uint64_loc_def)

lemma uint32_max_uint32_nat_assn:
  \<open>(uncurry0 (return 4294967295), uncurry0 (RETURN uint32_max)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: uint32_max_def uint32_nat_rel_def br_def)

lemma minus_uint64_assn:
 \<open>(uncurry (return oo (-)), uncurry (RETURN oo (-))) \<in> uint64_assn\<^sup>k *\<^sub>a uint64_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
 by sepref_to_hoare sep_auto

lemma uint32_of_nat_uint32_nat_assn[sepref_fr_rules]:
  \<open>(return o id, RETURN o uint32_of_nat) \<in>  uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def)

lemma uint32_of_nat2[sepref_fr_rules]:
  \<open>(return o uint32_of_uint64, RETURN o uint32_of_nat) \<in>
    [\<lambda>n. n \<le> uint32_max]\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint32_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: uint32_nat_rel_def br_def uint64_nat_rel_def uint32_of_uint64_def)

lemma three_uint32_hnr:
  \<open>(uncurry0 (return 3), uncurry0 (RETURN (three_uint32 :: uint32)) ) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def three_uint32_def)


lemma nat_of_uint64_id_conv_hnr[sepref_fr_rules]:
  \<open>(return o id, RETURN o nat_of_uint64_id_conv) \<in> uint64_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: nat_of_uint64_id_conv_def uint64_nat_rel_def br_def)


end
