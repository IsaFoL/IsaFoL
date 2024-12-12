theory Nonground_Typing
  imports
    Clause_Typing
    Nonground_Term_Typing
    Typed_Functional_Substitution_Lifting
    Nonground_Clause
    Fun_Extra

    Nonground_Order
begin

type_synonym ('f, 'v, 'ty) typed_clause = "('f, 'v) atom clause \<times> ('v, 'ty) var_types"

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
  "term": nonground_term +
  nonground_typing_lifting where  
  id_subst = Var and comp_subst = "(\<odot>)" and base_subst = "(\<cdot>t)" and base_vars = term.vars

locale term_based_nonground_uniform_typing_lifting =
  "term": nonground_term +
  nonground_uniform_typing_lifting where  
  id_subst = Var and comp_subst = "(\<odot>)" and map = map_uprod and to_set = set_uprod and 
  sub_vars = term.vars and sub_subst = "(\<cdot>t)"

locale nonground_typing =
  nonground_clause +
  fixes \<F> :: "('f, 'ty) fun_types"
begin 

sublocale nonground_term_typing "\<F> :: ('f, 'ty) fun_types" 
  by unfold_locales

sublocale clause_typing "typed (\<V> :: ('v, 'ty) var_types)" "welltyped \<V>"
  by unfold_locales

sublocale atom: term_based_nonground_uniform_typing_lifting where 
  base_typed = "typed :: ('v \<Rightarrow> 'ty) \<Rightarrow> ('f, 'v) Term.term \<Rightarrow> 'ty \<Rightarrow> bool" and 
  base_welltyped = welltyped 
  by unfold_locales

sublocale literal: term_based_nonground_typing_lifting where 
  base_typed = "typed :: ('v \<Rightarrow> 'ty) \<Rightarrow> ('f, 'v) Term.term \<Rightarrow> 'ty \<Rightarrow> bool" and 
  base_welltyped = welltyped and sub_vars = atom.vars and sub_subst = "(\<cdot>a)" and 
  map = map_literal and to_set = set_literal and sub_is_typed = atom.is_typed and
  sub_is_welltyped = atom.is_welltyped 
  by unfold_locales

sublocale clause: term_based_nonground_typing_lifting where 
  base_typed = typed and base_welltyped = welltyped and
  sub_vars = literal.vars and sub_subst = "(\<cdot>l)" and map = image_mset and to_set = set_mset and
  sub_is_typed = literal.is_typed and sub_is_welltyped = literal.is_welltyped
  by unfold_locales

definition infinite_variables_per_type where 
  "infinite_variables_per_type \<V> \<equiv> \<forall>ty. infinite {x. \<V> x = ty}"

(* TODO: Separate Locale *)
lemma exists_infinite_variables_per_type:
  assumes "|UNIV :: 'ty set| \<le>o |UNIV :: ('v :: infinite) set|"
  shows "\<exists>\<V> :: ('v :: infinite \<Rightarrow> 'ty). infinite_variables_per_type \<V>"
  using infinite_domain[OF assms infinite_UNIV]
  unfolding infinite_variables_per_type_def
  by argo

(* TODO: Needed? *)
abbreviation is_welltyped_grounding where 
  "is_welltyped_grounding C \<V> \<gamma> \<equiv> 
    clause.is_ground (C \<cdot> \<gamma>) \<and> 
    clause.is_welltyped \<V> C \<and>
    is_welltyped_on (clause.vars C) \<V> \<gamma> \<and>
    infinite_variables_per_type \<V>"

definition clause_groundings :: "('f, 'v, 'ty) typed_clause \<Rightarrow> 'f ground_atom clause set"   where
  "clause_groundings C = 
    { clause.to_ground (fst C \<cdot> \<gamma>) | \<gamma>. is_welltyped_grounding (fst C) (snd C) \<gamma> }"

end


end
