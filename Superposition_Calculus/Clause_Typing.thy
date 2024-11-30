theory Clause_Typing
  imports 
    Typing 
    Uprod_Extra 
    Multiset_Extra 
    Clausal_Calculus_Extra 
    Natural_Semigroup
begin

locale monoid_typing_lifting = typing_lifting + natural_semigroup
begin

lemma is_typed_add [simp]: 
  "is_typed (add sub M) \<longleftrightarrow> is_typed_sub sub \<and> is_typed M"
  using to_set_add 
  by auto

lemma is_typed_plus [simp]: 
  "is_typed (plus M M') \<longleftrightarrow> is_typed M \<and> is_typed M'"
  by (auto simp: to_set_plus)

lemma is_welltyped_add [simp]: 
  "is_welltyped (add sub M) \<longleftrightarrow> is_welltyped_sub sub \<and> is_welltyped M"
  using to_set_add 
  by auto

lemma is_welltyped_plus [simp]: 
  "is_welltyped (plus M M') \<longleftrightarrow> is_welltyped M \<and> is_welltyped M'"
  by (auto simp: to_set_plus)

end

locale mulitset_typing_lifting = 
  typing_lifting where to_set = set_mset
begin

sublocale monoid_typing_lifting 
  where to_set = set_mset and plus = "(+)" and wrap = "\<lambda>l. {#l#}" and add = add_mset
  by unfold_locales

end

locale clause_typing =
  "term": explicit_typing term_typed term_welltyped
  for term_typed term_welltyped
begin

sublocale atom: uniform_typing_lifting where 
  typed_sub = term_typed and 
  welltyped_sub = term_welltyped and
  to_set = set_uprod
  by unfold_locales 

sublocale literal: typing_lifting where 
  is_typed_sub = atom.is_typed and 
  is_welltyped_sub = atom.is_welltyped and
  to_set = set_literal
  by unfold_locales

lemma atom_is_typed_iff [simp]:
  "atom.is_typed (Upair t t') \<longleftrightarrow> (\<exists>\<tau>. term_typed t \<tau> \<and> term_typed t' \<tau>)"
  by auto

lemma atom_is_welltyped_iff [simp]:
  "atom.is_welltyped (Upair t t') \<longleftrightarrow> (\<exists>\<tau>. term_welltyped t \<tau> \<and> term_welltyped t' \<tau>)"
  by auto

lemma literal_is_typed_iff:
  "literal.is_typed l \<longleftrightarrow> atom.is_typed (atm_of l)" and
  [simp]: "literal.is_typed (t \<approx> t') \<longleftrightarrow> atom.is_typed (Upair t t')" and
  [simp]: "literal.is_typed (t !\<approx> t') \<longleftrightarrow> atom.is_typed (Upair t t')"
  by (simp_all add: set_literal_atm_of)

lemma literal_is_welltyped_iff:
  "literal.is_welltyped l \<longleftrightarrow> atom.is_welltyped (atm_of l)" and
  [simp]: "literal.is_welltyped (t \<approx> t') \<longleftrightarrow> atom.is_welltyped (Upair t t')" and
  [simp]: "literal.is_welltyped (t !\<approx> t') \<longleftrightarrow> atom.is_welltyped (Upair t t')"
  by (simp_all add: set_literal_atm_of)

sublocale clause: mulitset_typing_lifting where 
  is_typed_sub = literal.is_typed and 
  is_welltyped_sub = literal.is_welltyped
  by unfold_locales

lemma welltyped_add_literal:
  assumes "clause.is_welltyped c" "term_welltyped t\<^sub>1 \<tau>" "term_welltyped t\<^sub>2 \<tau>" 
  shows "clause.is_welltyped (add_mset (t\<^sub>1 !\<approx> t\<^sub>2) c)"
  using assms
  by auto

end

end
