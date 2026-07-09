theory HO_Terms
  imports "Binders.MRBNF_Recursor"
begin

binder_datatype ('\<tau>, '\<Sigma>, '\<V>) lpreterm =
  Const '\<Sigma> "'\<tau> list" "('\<tau>, '\<Sigma>, '\<V>) lpreterm list" '\<tau> |
  Var '\<V> '\<tau> |
  App "('\<tau>, '\<Sigma>, '\<V>) lpreterm" "('\<tau>, '\<Sigma>, '\<V>) lpreterm" |
  Abs x::'\<V> '\<tau> t::"('\<tau>, '\<Sigma>, '\<V>) lpreterm" binds x in t

find_consts "(_, _) lpreterm \<Rightarrow> _"

term FVars_lpreterm
term set2_lpreterm

find_theorems "FVars_lpreterm"

thm lpreterm.set


datatype \<tau> = Unit | Arrow \<tau> \<tau> (infixr "\<rightarrow>" 40)

declare [[mrbnf_internals]]

binder_datatype 'a terms =
  Var 'a
| App "'a terms" "'a terms"
| Abs x::'a \<tau> t::"'a terms" binds x in t
for
  vvsubst: vvsubst
  tvsubst: tvsubst

lemma finite_vars_term: "finite (free_vars t)"
  by (induction t) simp_all

declare fset_of_list.rep_eq[termination_simp]

fun free_vars_fset :: "('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> '\<V> fset" where
  "free_vars_fset (Const _ _ ts) = ffUnion (free_vars_fset |`| fset_of_list ts)" |
  "free_vars_fset (Free x) = {|x|}" |
  "free_vars_fset (Bound _) = {||}" |
  "free_vars_fset (App t\<^sub>1 t\<^sub>2) = free_vars_fset t\<^sub>1 |\<union>| free_vars_fset t\<^sub>2" |
  "free_vars_fset (Abs _ t) = free_vars_fset t"

end