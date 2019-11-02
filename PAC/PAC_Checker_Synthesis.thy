theory PAC_Checker_Synthesis
  imports PAC_Checker
begin

definition string_rel :: \<open>(String.literal \<times> string) set\<close> where
  \<open>string_rel = {(x, y). y = String.explode x}\<close>

abbreviation string_assn :: \<open>string \<Rightarrow> String.literal \<Rightarrow> assn\<close> where
  \<open>string_assn \<equiv> pure string_rel\<close>

lemma var_order_string_le[sepref_import_param]:
  \<open>((<), var_order) \<in> string_rel \<rightarrow> string_rel \<rightarrow> bool_rel\<close>
  by (auto intro!: frefI simp: string_rel_def String.less_literal_def
    less_than_char_def rel2p_def linorder.lexordp_conv_lexord[OF char.linorder_axioms,
      unfolded less_eq_char_def less_char_def])

lemma eq_string_eq[sepref_import_param]:
  \<open>((=), (=)) \<in> string_rel \<rightarrow> string_rel \<rightarrow> bool_rel\<close>
 by (auto intro!: frefI simp: string_rel_def String.less_literal_def
    less_than_char_def rel2p_def literal.explode_inject)


end