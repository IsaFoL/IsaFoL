theory WB_Word_Assn
imports
  CDCL_Two_Watched_Literals_List_Watched_Init_Code
  "$AFP/Word/Word"
begin
definition word_nat_rel :: "('a :: len0 Word.word \<times> nat) set" where
  \<open>word_nat_rel = {(n, n'). unat n = n'}\<close>

abbreviation word_nat_assn :: "nat \<Rightarrow> 'a::len0 Word.word \<Rightarrow> assn" where
  \<open>word_nat_assn \<equiv> pure word_nat_rel\<close>
 
lemma op_eq_word_nat:
  \<open>(uncurry (return oo (op = :: 'a :: len Word.word \<Rightarrow> _)), uncurry (RETURN oo op =)) \<in>
    word_nat_assn\<^sup>k *\<^sub>a word_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: word_nat_rel_def)

definition uint32_nat_rel :: "(uint32 \<times> nat) set" where
  \<open>uint32_nat_rel = {(n, n'). nat_of_uint32 n = n'}\<close>

abbreviation uint32_nat_assn :: "nat \<Rightarrow> uint32 \<Rightarrow> assn" where
  \<open>uint32_nat_assn \<equiv> pure uint32_nat_rel\<close>

lemma word_nat_of_uint32_Rep_inject[simp]: \<open>nat_of_uint32 ai = nat_of_uint32 bi \<longleftrightarrow> ai = bi\<close>
  by transfer simp

lemma op_eq_uint32_nat:
  \<open>(uncurry (return oo (op = :: uint32 \<Rightarrow> _)), uncurry (RETURN oo op =)) \<in>
    uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def)

lemma unat_shiftr: \<open>unat (xi >> n) = unat xi div (2^n)\<close>
  by (metis nat_int nat_shifl_div shiftr_div_2n shiftr_nat_def uint_nat)

lemma \<open>(return o (\<lambda>n. shiftr n 1), RETURN o shiftr1) \<in> word_nat_assn\<^sup>k \<rightarrow>\<^sub>a word_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: shiftr1_def word_nat_rel_def unat_shiftr)

end