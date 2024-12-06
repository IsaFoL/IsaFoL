theory Nonground_Typing
  imports
    Clause_Typing
    Nonground_Term_Typing
    Typed_Functional_Substitution_Lifting
    Nonground_Clause
    Fun_Extra

    Nonground_Order
begin

locale nonground_typing_lifting = 
  is_typed: typed_subst_stability_lifting where base_typed = base_typed +
  is_welltyped: typed_subst_stability_lifting where 
  sub_is_typed = sub_is_welltyped and base_typed = base_welltyped +

  is_typed: replaceable_\<V>_lifting where base_typed = base_typed +
  is_welltyped: replaceable_\<V>_lifting where 
  sub_is_typed = sub_is_welltyped and base_typed = base_welltyped +

  is_typed: typed_renaming_lifting where base_typed = base_typed +
  is_welltyped: typed_renaming_lifting where 
  sub_is_typed = sub_is_welltyped and base_typed = base_welltyped
for base_typed base_welltyped :: "('var, 'ty) var_types \<Rightarrow> 'base \<Rightarrow> 'ty \<Rightarrow> bool" and 
    sub_is_welltyped

locale nonground_uniform_typing_lifting =

  is_typed: uniform_typed_subst_stability_lifting where base_typed = base_typed + 
  is_welltyped: uniform_typed_subst_stability_lifting where base_typed = base_welltyped +

  is_typed: uniform_replaceable_\<V>_lifting where base_typed = base_typed + 
  is_welltyped: uniform_replaceable_\<V>_lifting where base_typed = base_welltyped + 

  is_typed: uniform_typed_renaming_lifting where base_typed = base_typed + 
  is_welltyped: uniform_typed_renaming_lifting where base_typed = base_welltyped 
for base_typed base_welltyped :: "('var, 'ty) var_types \<Rightarrow> 'base \<Rightarrow> 'ty \<Rightarrow> bool"

locale term_based_nonground_typing_lifting =
  nonground_typing_lifting where  
  id_subst = Var and comp_subst = "(\<odot>)" and base_subst = "(\<cdot>t)" and base_vars = term.vars

locale term_based_nonground_uniform_typing_lifting =
  nonground_uniform_typing_lifting where  
  id_subst = Var and comp_subst = "(\<odot>)" and map = map_uprod and to_set = set_uprod and 
  sub_vars = term.vars and sub_subst = "(\<cdot>t)"

locale nonground_typing = 
  test +
  fixes \<F> :: "('f, 'ty) fun_types"
begin 

sublocale nonground_term_typing "\<F> :: ('f, 'ty) fun_types" 
  by unfold_locales

sublocale clause_typing "typed (\<V> :: ('v, 'ty) var_types)" "welltyped \<V>"
  by unfold_locales

sublocale atom: term_based_nonground_uniform_typing_lifting where 
  base_typed = "typed :: ('v \<Rightarrow> 'ty) \<Rightarrow> ('f, 'v) Term.term \<Rightarrow> 'ty \<Rightarrow> bool" and base_welltyped = welltyped 
  by unfold_locales

sublocale literal: term_based_nonground_typing_lifting where 
  base_typed = "typed :: ('v \<Rightarrow> 'ty) \<Rightarrow> ('f, 'v) Term.term \<Rightarrow> 'ty \<Rightarrow> bool" and base_welltyped = welltyped and
  sub_vars = atom.vars and sub_subst = "(\<cdot>a)" and map = map_literal and to_set = set_literal and
  sub_is_typed = atom.is_typed and sub_is_welltyped = atom.is_welltyped 
  by unfold_locales

sublocale clause: term_based_nonground_typing_lifting where 
  base_typed = typed and base_welltyped = welltyped and
  sub_vars = literal.vars and sub_subst = "(\<cdot>l)" and map = image_mset and to_set = set_mset and
  sub_is_typed = literal.is_typed and sub_is_welltyped = literal.is_welltyped
  by unfold_locales

end

end
