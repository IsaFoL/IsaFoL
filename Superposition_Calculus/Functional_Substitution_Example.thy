theory Functional_Substitution_Example
  imports Functional_Substitution Substitution_First_Order_Term
begin

text \<open>A selection of substitution properties for terms.\<close>
locale term_subst_properties =
  base_functional_substitution +
  finite_variables

global_interpretation term_subst: term_subst_properties where
  subst = subst_apply_term and id_subst = Var and comp_subst = subst_compose and
  vars = "vars_term :: ('f, 'v) term \<Rightarrow> 'v set"
rewrites "\<And>t. term_subst.is_ground t \<longleftrightarrow> ground t"
text \<open>"rewrites" enables us to use our own equivalent definitions.\<close>
proof unfold_locales
  fix t :: "('f, 'v) term"  and \<sigma> \<tau> :: "('f, 'v) subst"
  assume "\<And>x. x \<in> vars_term t \<Longrightarrow> \<sigma> x = \<tau> x"
  then show "t \<cdot> \<sigma> = t \<cdot> \<tau>"
    by(rule term_subst_eq)
next
  fix t :: "('f, 'v) term"
  show "finite (vars_term t)"
    by simp
next
  fix t :: "('f, 'v) term" and \<rho> :: "('f, 'v) subst"

  show "vars_term (t \<cdot> \<rho>) = \<Union> (vars_term ` \<rho> ` vars_term t)"
    using vars_term_subst.
next
  show "\<exists>t. vars_term t = {}"
    by(rule exI[of _ "Fun (SOME f. True) []"]) auto
next
  fix x :: 'v
  show "vars_term (Var x) = {x}"
    by simp
next
  fix \<sigma> \<sigma>' :: "('f, 'v) subst" and x
  show "(\<sigma> \<circ>\<^sub>s \<sigma>') x = \<sigma> x \<cdot> \<sigma>'"
    using subst_compose.
next
  fix t :: "('f, 'v) term"
  show "is_ground_trm t = ground t"
    by (induction t) auto
qed

text \<open>Examples of generated lemmas and definitions\<close>
thm
  term_subst.subst_reduntant_upd
  term_subst.subst_reduntant_if

  term_subst.subst_domain_def
  term_subst.range_vars_def

  term_subst.vars_subst_subset



end
