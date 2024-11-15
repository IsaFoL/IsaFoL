theory Clause_Typing
  imports Typing Uprod_Extra Multiset_Extra Clausal_Calculus_Extra
begin

locale mulitset_typing_lifting = typing_lifting where to_set = set_mset
begin

lemma is_welltyped_add_mset: 
  "is_welltyped (add_mset sub M) \<longleftrightarrow> is_welltyped_sub sub \<and> is_welltyped M"
  by (simp add: is_welltyped_def)

lemma is_welltyped_plus: 
  "is_welltyped (C + D) \<longleftrightarrow> is_welltyped C \<and> is_welltyped D"
  by (auto simp: is_welltyped_def)

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

sublocale clause: mulitset_typing_lifting where 
  is_typed_sub = literal.is_typed and 
  is_welltyped_sub = literal.is_welltyped
  by unfold_locales

end

end
