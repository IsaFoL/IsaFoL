theory Functional_Substitution_Lifting_Example
  imports
    Functional_Substitution_Lifting
    Functional_Substitution_Example
begin

text \<open>Lifting of properties from term to equations (modelled as pairs)\<close>

type_synonym ('f,'v) equation = "('f, 'v) term \<times> ('f, 'v) term"

text \<open>All property locales have corresponding lifting locales\<close>
locale lifting_term_subst_properties =
  based_functional_substitution_lifting where
  id_subst = Var and comp_subst = subst_compose and base_subst = subst_apply_term and
  base_vars = "vars_term :: ('f, 'v) term \<Rightarrow> 'v set" +
  finite_variables_lifting where id_subst = Var and comp_subst = subst_compose

global_interpretation equation_subst:
  lifting_term_subst_properties where
  sub_vars = vars_term and sub_subst = subst_apply_term and map = "\<lambda>f. map_prod f f" and
  to_set = set_prod
  by unfold_locales fastforce+

text \<open>Lifted lemmas and defintions\<close>
thm
  equation_subst.subst_reduntant_upd
  equation_subst.subst_reduntant_if
  equation_subst.vars_subst_subset

  equation_subst.vars_def
  equation_subst.subst_def

text \<open>We can lift multiple levels\<close>
global_interpretation equation_set_subst:
  lifting_term_subst_properties where
  sub_vars = equation_subst.vars and sub_subst = equation_subst.subst and map = fimage and 
  to_set = fset
  by unfold_locales (auto simp: rev_image_eqI)

text \<open>Lifted lemmas and defintions\<close>
thm
  equation_set_subst.subst_reduntant_upd
  equation_set_subst.subst_reduntant_if
  equation_set_subst.vars_subst_subset

  equation_set_subst.vars_def
  equation_set_subst.subst_def

end
