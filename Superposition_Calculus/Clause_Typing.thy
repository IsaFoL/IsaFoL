theory Clause_Typing
  imports 
    Typing 
    Uprod_Extra 
    Multiset_Extra 
    Clausal_Calculus_Extra 
    Natural_Magma
begin

locale monoid_typing_lifting = typing_lifting + natural_magma
begin

lemma is_typed_add [simp]: 
  "is_typed (add sub M) \<longleftrightarrow> sub_is_typed sub \<and> is_typed M"
  using to_set_add 
  unfolding is_typed_def
  by auto

lemma is_typed_plus [simp]: 
  "is_typed (plus M M') \<longleftrightarrow> is_typed M \<and> is_typed M'"
  unfolding is_typed_def
  by (auto simp: to_set_plus)

lemma is_welltyped_add [simp]: 
  "is_welltyped (add sub M) \<longleftrightarrow> sub_is_welltyped sub \<and> is_welltyped M"
  unfolding is_welltyped_def
  using to_set_add 
  by auto

lemma is_welltyped_plus [simp]: 
  "is_welltyped (plus M M') \<longleftrightarrow> is_welltyped M \<and> is_welltyped M'"
  unfolding is_welltyped_def
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
  sub_typed = term_typed and 
  sub_welltyped = term_welltyped and
  to_set = set_uprod
  by unfold_locales 

sublocale literal: typing_lifting where 
  sub_is_typed = atom.is_typed and 
  sub_is_welltyped = atom.is_welltyped and
  to_set = set_literal
  by unfold_locales

lemma atom_is_typed_iff [simp]:
  "atom.is_typed (Upair t t') \<longleftrightarrow> (\<exists>\<tau>. term_typed t \<tau> \<and> term_typed t' \<tau>)"
  unfolding atom.is_typed_def
  by auto

lemma atom_is_welltyped_iff [simp]:
  "atom.is_welltyped (Upair t t') \<longleftrightarrow> (\<exists>\<tau>. term_welltyped t \<tau> \<and> term_welltyped t' \<tau>)"
  unfolding atom.is_welltyped_def
  by auto

lemma literal_is_typed_iff_atm_of: "literal.is_typed l \<longleftrightarrow> atom.is_typed (atm_of l)"
  unfolding literal.is_typed_def
  by (simp add: set_literal_atm_of)

lemma literal_is_typed_iff [simp]:
   "literal.is_typed (t \<approx> t') \<longleftrightarrow> atom.is_typed (Upair t t')"
   "literal.is_typed (t !\<approx> t') \<longleftrightarrow> atom.is_typed (Upair t t')"
  unfolding literal.is_typed_def
  by (simp_all add: set_literal_atm_of)

lemma literal_is_welltyped_iff [simp]:
  "literal.is_welltyped (t \<approx> t') \<longleftrightarrow> atom.is_welltyped (Upair t t')"
  "literal.is_welltyped (t !\<approx> t') \<longleftrightarrow> atom.is_welltyped (Upair t t')"
  unfolding literal.is_welltyped_def
  by simp_all

lemma literal_is_welltyped_iff_atm_of:
  "literal.is_welltyped l \<longleftrightarrow> atom.is_welltyped (atm_of l)"
  unfolding literal.is_welltyped_def
  by (simp add: set_literal_atm_of)

lemmas is_welltyped_iff = 
  literal_is_welltyped_iff atom_is_welltyped_iff

sublocale clause: mulitset_typing_lifting where 
  sub_is_typed = literal.is_typed and 
  sub_is_welltyped = literal.is_welltyped
  by unfold_locales

lemma welltyped_add_literal:
  assumes "clause.is_welltyped c" "term_welltyped t\<^sub>1 \<tau>" "term_welltyped t\<^sub>2 \<tau>" 
  shows "clause.is_welltyped (add_mset (t\<^sub>1 !\<approx> t\<^sub>2) c)"
  using assms
  by auto

end

end
