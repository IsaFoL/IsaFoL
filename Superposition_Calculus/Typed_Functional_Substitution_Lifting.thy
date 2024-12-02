theory Typed_Functional_Substitution_Lifting
  imports 
    Typed_Functional_Substitution 
    Functional_Substitution_Lifting
begin

locale typed_functional_substitution_lifting = 
  sub: typed_functional_substitution where 
  vars = sub_vars and subst = sub_subst and expr_is_typed = sub_expr_is_typed and 
  base_vars = base_vars +
  based_functional_substitution_lifting where to_set = to_set and base_vars = base_vars
for
  sub_expr_is_typed :: "('var, 'ty) var_types \<Rightarrow> 'sub \<Rightarrow> bool" and
  to_set :: "'expr \<Rightarrow> 'sub set" and
  base_vars :: "'base \<Rightarrow> 'var set"
begin

abbreviation expr_is_typed where 
  "expr_is_typed \<V> \<equiv> is_typed_lifting to_set (sub_expr_is_typed \<V>)"

sublocale typed_functional_substitution where vars = vars and subst = subst and 
  expr_is_typed = expr_is_typed
  by unfold_locales

end

(* TODO: Names sub \<rightarrow> base *)
locale uniform_typed_functional_substitution_lifting = 
  sub: explicitly_typed_functional_substitution where 
  vars = sub_vars and subst = sub_subst and expr_typed = sub_typed +
  based_functional_substitution_lifting where 
  to_set = to_set and base_vars = sub_vars and base_subst = sub_subst
for
  sub_typed :: "('var, 'ty) var_types \<Rightarrow> 'base \<Rightarrow> 'ty \<Rightarrow> bool" and
  to_set :: "'expr \<Rightarrow> 'base set"
begin

abbreviation expr_is_typed where 
  "expr_is_typed \<V> \<equiv> uniform_typed_lifting to_set (sub_typed \<V>)"

sublocale typed_functional_substitution where vars = vars and subst = subst and 
  expr_is_typed = expr_is_typed and base_subst = sub_subst and base_vars = sub_vars and 
  base_typed = sub_typed
  by unfold_locales

end

locale functional_substitution_typing_lifting =
  sub: functional_substitution_typing where 
  vars = sub_vars and subst = sub_subst and expr_is_typed = is_typed_sub and 
  expr_is_welltyped = is_welltyped_sub +
  based_functional_substitution_lifting where to_set = to_set
for
  to_set :: "'expr \<Rightarrow> 'sub set" and 
  is_typed_sub is_welltyped_sub :: "('var, 'ty) var_types \<Rightarrow> 'sub \<Rightarrow> bool"
begin

sublocale expr: typing_lifting where 
  is_typed_sub = "is_typed_sub \<V>" and is_welltyped_sub = "is_welltyped_sub \<V>" 
  by unfold_locales

sublocale functional_substitution_typing where 
  expr_is_typed = expr.is_typed and expr_is_welltyped = expr.is_welltyped and vars = vars and 
  subst = subst 
  by unfold_locales

end

locale functional_substitution_uniform_typing_lifting =
  sub: base_functional_substitution_typing where 
  vars = sub_vars and subst = sub_subst and expr_typed = typed_sub and 
  expr_welltyped = welltyped_sub +
  based_functional_substitution_lifting where to_set = to_set
for
  to_set :: "'expr \<Rightarrow> 'sub set" and
  typed_sub welltyped_sub :: "('var, 'ty) var_types \<Rightarrow> 'sub \<Rightarrow> 'ty \<Rightarrow> bool"
begin

sublocale expr: uniform_typing_lifting where 
  typed_sub = "typed_sub \<V>" and welltyped_sub = "welltyped_sub \<V>"
  by unfold_locales

sublocale functional_substitution_typing where 
  expr_is_typed = expr.is_typed and expr_is_welltyped = expr.is_welltyped and vars = vars and 
  subst = subst and base_typed = typed_sub and base_welltyped = welltyped_sub
  by unfold_locales

end

locale typed_subst_stability_lifting =
  typed_functional_substitution_lifting +  
  sub: typed_subst_stability where 
  expr_is_typed = sub_expr_is_typed and vars = sub_vars and subst = sub_subst
begin

sublocale typed_subst_stability where 
  expr_is_typed = expr_is_typed and subst = subst and vars = vars
proof unfold_locales
  fix expr \<V> \<sigma>
  assume "sub.base.is_typed_on (vars expr) \<V> \<sigma>"
  
  then show "expr_is_typed \<V> (expr \<cdot> \<sigma>) \<longleftrightarrow> expr_is_typed \<V> expr"
    unfolding vars_def
    using sub.subst_stability to_set_image 
    by fastforce
 
qed

end

locale uniform_typed_subst_stability_lifting =
  uniform_typed_functional_substitution_lifting +  
  sub: explicitly_typed_subst_stability where 
  expr_typed = sub_typed and vars = sub_vars and subst = sub_subst
begin

sublocale typed_subst_stability where 
  expr_is_typed = expr_is_typed and subst = subst and vars = vars and base_subst = sub_subst and 
  base_vars = sub_vars and base_typed = sub_typed
proof unfold_locales
  fix expr \<V> \<sigma>
  assume "sub.is_typed_on (vars expr) \<V> \<sigma>"
  
  then show "expr_is_typed \<V> (expr \<cdot> \<sigma>) \<longleftrightarrow> expr_is_typed \<V> expr"
    unfolding vars_def 
    using sub.subst_stability to_set_image
    by force
qed

end

locale replaceable_\<V>_lifting = 
  typed_functional_substitution_lifting + 
  sub: replaceable_\<V> where 
  subst = sub_subst and vars = sub_vars and expr_is_typed = sub_expr_is_typed
begin

sublocale replaceable_\<V> where 
  subst = subst and vars = vars and expr_is_typed = expr_is_typed
  by unfold_locales (auto simp: sub.replace_\<V> vars_def)

end

locale uniform_replaceable_\<V>_lifting =
  uniform_typed_functional_substitution_lifting +  
  sub: explicitly_replaceable_\<V> where
  expr_typed = sub_typed and vars = sub_vars and subst = sub_subst
begin

sublocale replaceable_\<V> where 
  expr_is_typed = expr_is_typed and subst = subst and vars = vars and base_subst = sub_subst and 
  base_vars = sub_vars and base_typed = sub_typed
  by unfold_locales (auto 4 4 simp: vars_def intro: sub.replace_\<V>)

end

locale typed_renaming_lifting = 
  typed_functional_substitution_lifting + 
  sub: typed_renaming where 
  subst = sub_subst and vars = sub_vars and expr_is_typed = sub_expr_is_typed
begin
                  
sublocale typed_renaming where 
  subst = subst and vars = vars and expr_is_typed = expr_is_typed
  (* TODO: *)
  apply unfold_locales
  unfolding vars_def subst_def
  using sub.typed_renaming
  by force

end

locale uniform_typed_renaming_lifting =
  uniform_typed_functional_substitution_lifting +  
  sub: explicitly_typed_renaming where
  expr_typed = sub_typed and vars = sub_vars and subst = sub_subst
begin

sublocale typed_renaming where 
  expr_is_typed = expr_is_typed and subst = subst and vars = vars and base_subst = sub_subst and 
  base_vars = sub_vars and base_typed = sub_typed
  apply unfold_locales
  unfolding vars_def subst_def
  using sub.typed_renaming
  by force

end

end
