theory Clause_Typing
  imports Typing Uprod_Extra Multiset_Extra Clausal_Calculus_Extra Natural_Monoid
begin

locale monoid_typing_lifting = typing_lifting + natural_monoid
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

sublocale atom: uniform_explicit_typing_lifting where 
  typed_sub = term_typed and 
  welltyped_sub = term_welltyped and
  to_set = set_uprod
  by unfold_locales (rule set_uprod_not_empty)

sublocale literal: uniform_explicit_typing_lifting where 
  typed_sub = atom.typed and 
  welltyped_sub = atom.welltyped and
  to_set = "\<lambda>l. {atm_of l}"
  by unfold_locales simp

lemma atom_typed_iff [simp]:
  "atom.typed (Upair t t') \<tau> \<longleftrightarrow> term_typed t \<tau> \<and> term_typed t' \<tau>"
  by (simp add: atom.typed_def)

lemma atom_is_typed_iff [simp]:
  "atom.is_typed (Upair t t') \<longleftrightarrow> (\<exists>\<tau>. term_typed t \<tau> \<and> term_typed t' \<tau>)"
  by auto

lemma atom_welltyped_iff [simp]:
  "atom.welltyped (Upair t t') \<tau> \<longleftrightarrow> term_welltyped t \<tau> \<and> term_welltyped t' \<tau>"
  by (simp add: atom.welltyped_def)

lemma atom_is_welltyped_iff [simp]:
  "atom.is_welltyped (Upair t t') \<longleftrightarrow> (\<exists>\<tau>. term_welltyped t \<tau> \<and> term_welltyped t' \<tau>)"
  by auto

lemma literal_typed_iff:
  "literal.typed l \<tau> \<longleftrightarrow> atom.typed (atm_of l) \<tau>" and
  [simp]: "literal.typed (t \<approx> t') \<tau> \<longleftrightarrow> atom.typed (Upair t t') \<tau>" and
  [simp]: "literal.typed (t !\<approx> t') \<tau> \<longleftrightarrow> atom.typed (Upair t t') \<tau>"
  by (simp_all add: literal.typed_def)

lemma literal_is_typed_iff:
  "literal.is_typed l \<longleftrightarrow> atom.is_typed (atm_of l)" and
  [simp]: "literal.is_typed (t \<approx> t') \<longleftrightarrow> atom.is_typed (Upair t t')" and
  [simp]: "literal.is_typed (t !\<approx> t') \<longleftrightarrow> atom.is_typed (Upair t t')"
  by (simp_all add: literal.typed_def)

lemma literal_welltyped_iff:
  "literal.welltyped l \<tau> \<longleftrightarrow> atom.welltyped (atm_of l) \<tau>" and
  [simp]: "literal.welltyped (t \<approx> t') \<tau> \<longleftrightarrow> atom.welltyped (Upair t t') \<tau>" and
  [simp]: "literal.welltyped (t !\<approx> t') \<tau> \<longleftrightarrow> atom.welltyped (Upair t t') \<tau>"
  by (simp_all add: literal.welltyped_def)

lemma literal_is_welltyped_iff:
  "literal.is_welltyped l \<longleftrightarrow> atom.is_welltyped (atm_of l)" and
  [simp]: "literal.is_welltyped (t \<approx> t') \<longleftrightarrow> atom.is_welltyped (Upair t t')" and
  [simp]: "literal.is_welltyped (t !\<approx> t') \<longleftrightarrow> atom.is_welltyped (Upair t t')"
  by (simp_all add: literal.welltyped_def)

sublocale clause: mulitset_typing_lifting where 
  is_typed_sub = literal.is_typed and 
  is_welltyped_sub = literal.is_welltyped
  by unfold_locales

end

end
