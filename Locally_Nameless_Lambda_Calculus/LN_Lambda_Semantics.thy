theory LN_Lambda_Semantics
  imports LN_Lambda_Typing
begin

term monoid

class domain_universe =
  fixes \<U> :: "'a set set" and ap_domain :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes no_empty_domain: "{} \<notin> \<U>"

type_synonym ('\<Sigma>\<^sub>t\<^sub>y, 'd) type_interp_fun = "'\<Sigma>\<^sub>t\<^sub>y \<Rightarrow> 'd set list \<Rightarrow> 'd set"
type_synonym ('\<V>\<^sub>t\<^sub>y, 'd) type_valuation = "'\<V>\<^sub>t\<^sub>y \<Rightarrow> 'd set"

type_synonym ('\<Sigma>, 'd) term_interp_fun = "'\<Sigma> \<Rightarrow> 'd set list \<Rightarrow> 'd list \<Rightarrow> 'd"
type_synonym ('\<V>, 'd) term_valuation = "'\<V> \<Rightarrow> 'd"

type_synonym ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y, '\<V>, '\<Sigma>, 'd) lambda_designation_fun =
  "('\<V>\<^sub>t\<^sub>y, 'd) type_valuation \<Rightarrow> ('\<V>, 'd) term_valuation \<Rightarrow> (('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) ty, '\<Sigma>, '\<V>) preterm \<Rightarrow> 'd"

type_synonym ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y, '\<V>, '\<Sigma>, 'd) interp =
  "('\<Sigma>\<^sub>t\<^sub>y, 'd) type_interp_fun \<times>
    ('\<Sigma>, 'd) term_interp_fun \<times>
    ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y, '\<V>, '\<Sigma>, 'd) lambda_designation_fun"
type_synonym ('\<V>\<^sub>t\<^sub>y, '\<V>, 'd) valuation =
  "('\<V>\<^sub>t\<^sub>y, 'd) type_valuation \<times> ('\<V>, 'd) term_valuation"

type_synonym ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y, '\<V>, '\<Sigma>, 'd) model =
  "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y, '\<V>, '\<Sigma>, 'd) interp \<times> ('\<V>\<^sub>t\<^sub>y, '\<V>, 'd) valuation"

locale type_interp =
  fixes \<J>\<^sub>t\<^sub>y :: "('\<Sigma>\<^sub>t\<^sub>y :: arity, 'd :: domain_universe) type_interp_fun"
  assumes \<J>\<^sub>t\<^sub>y_codom: "\<And>\<kappa> \<D>s.
    arity \<kappa> = length \<D>s \<Longrightarrow> (\<And>\<D>. \<D> \<in> set \<D>s \<Longrightarrow> \<D> \<in> \<U>) \<Longrightarrow> \<J>\<^sub>t\<^sub>y \<kappa> \<D>s \<in> \<U>"

primrec prety_denotation ::
  "('\<V>\<^sub>t\<^sub>y, 'd) type_valuation \<Rightarrow> ('\<Sigma>\<^sub>t\<^sub>y, 'd) type_interp_fun \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) prety \<Rightarrow> 'd set" where
  "prety_denotation \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y (PretyVar x) = \<xi>\<^sub>t\<^sub>y x" |
  "prety_denotation \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y (PretyCtr \<kappa> \<tau>s) = \<J>\<^sub>t\<^sub>y \<kappa> (map (prety_denotation \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y) \<tau>s)"

definition ty_denotation ::
  "('\<V>\<^sub>t\<^sub>y, 'd) type_valuation \<Rightarrow> ('\<Sigma>\<^sub>t\<^sub>y, 'd) type_interp_fun \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: arity) ty \<Rightarrow> 'd set" where
  "ty_denotation \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y \<tau> = prety_denotation \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y (Rep_ty \<tau>)"

locale type_valuation =
  fixes \<xi>\<^sub>t\<^sub>y :: "('\<V>\<^sub>t\<^sub>y, 'd :: domain_universe) type_valuation"
  assumes \<xi>\<^sub>t\<^sub>y_codom[intro]: "\<And>x. \<xi>\<^sub>t\<^sub>y x \<in> \<U>"

lemma ty_denotation_codom:
  assumes "type_interp \<J>\<^sub>t\<^sub>y" and "type_valuation \<xi>\<^sub>t\<^sub>y"
  shows "ty_denotation \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y \<tau> \<in> \<U>"
proof (cases \<tau>)
  case (Abs_ty \<tau>')

  then have "wf_prety \<tau>'"
    by simp

  then have "prety_denotation \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y \<tau>' \<in> \<U>"
  proof (induction \<tau>')
    case (PretyVar \<alpha>)
    then show ?case
      by (metis assms(2) prety_denotation.simps(1) type_valuation.\<xi>\<^sub>t\<^sub>y_codom)
  next
    case (PretyCtr \<kappa> \<tau>s)
    show ?case
      unfolding prety_denotation.simps
    proof (rule type_interp.\<J>\<^sub>t\<^sub>y_codom[OF assms(1)])
      show "arity \<kappa> = length (map (prety_denotation \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y) \<tau>s)"
        using PretyCtr.hyps by simp
    next
      show "\<And>\<D>. \<D> \<in> set (map (prety_denotation \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y) \<tau>s) \<Longrightarrow> \<D> \<in> \<U>"
        using PretyCtr.IH by auto
    qed
  qed

  then show ?thesis
    using Abs_ty
    by (metis Abs_ty_inverse[of \<tau>'] ty_denotation_def)
qed

locale interp_fun = type_interp \<J>\<^sub>t\<^sub>y
  for \<J>\<^sub>t\<^sub>y :: "('\<Sigma>\<^sub>t\<^sub>y :: arity, 'd :: domain_universe) type_interp_fun" +
  fixes typeof :: "'\<Sigma> \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) const_ty"
  fixes \<J> :: "('\<Sigma>, 'd) term_interp_fun"
  assumes
    \<J>_codom[intro]: "\<And>(\<xi>\<^sub>t\<^sub>y :: ('\<V>\<^sub>t\<^sub>y, 'd) type_valuation) \<kappa> \<D>s \<alpha>s \<tau>s \<pi> as.
      type_valuation \<xi>\<^sub>t\<^sub>y \<Longrightarrow>
      typeof \<kappa> = (\<alpha>s, \<tau>s, \<pi>) \<Longrightarrow> Dlist.length \<alpha>s = length \<D>s \<Longrightarrow>
      list_all2 (\<lambda>a \<tau>. a \<in> ty_denotation \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y \<tau>) as \<tau>s \<Longrightarrow> \<J> \<kappa> \<D>s as \<in> ty_denotation \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y \<pi>"

locale valuation =
  fixes typeof_var :: "'\<V> \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: arity) ty"
  fixes \<xi> :: "('\<V>, 'd :: domain_universe) term_valuation"
  assumes \<xi>_codom[intro]: "\<And>(\<xi>\<^sub>t\<^sub>y :: ('\<V>\<^sub>t\<^sub>y, 'd) type_valuation) x.
    type_valuation \<xi>\<^sub>t\<^sub>y \<Longrightarrow> \<xi> x \<in> ty_denotation \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y (typeof_var x)"

locale lambda_designation = type_interp \<J>\<^sub>t\<^sub>y
  for \<J>\<^sub>t\<^sub>y :: "('\<Sigma>\<^sub>t\<^sub>y :: type_signature, 'd :: domain_universe) type_interp_fun" +
  fixes typeof :: "'\<Sigma> \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) const_ty"
  fixes \<L> :: "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y, '\<V>, '\<Sigma>, 'd) lambda_designation_fun"
  assumes "\<And>(\<xi>\<^sub>t\<^sub>y :: ('\<V>\<^sub>t\<^sub>y, 'd) type_valuation) (\<xi> :: ('\<V>, 'd) term_valuation) (typeof_var :: '\<V> \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) ty) t \<tau>.
    type_valuation \<xi>\<^sub>t\<^sub>y \<Longrightarrow>
    has_type typeof typeof_var t \<tau> \<Longrightarrow> is_Abs t \<Longrightarrow> \<L> \<xi>\<^sub>t\<^sub>y \<xi> t \<in> ty_denotation \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y \<tau>"
  assumes \<L>_depends_only_on_\<xi>_on_vars:
    "\<And>(\<xi>\<^sub>t\<^sub>y :: ('\<V>\<^sub>t\<^sub>y, 'd) type_valuation) (\<xi>\<^sub>t\<^sub>y' :: ('\<V>\<^sub>t\<^sub>y, 'd) type_valuation)
      (\<xi> :: ('\<V>, 'd) term_valuation) (\<xi>' :: ('\<V>, 'd) term_valuation) t.
    (\<And>\<tau> x. \<tau> \<in> type_symbols t \<Longrightarrow> x \<in> type_vars \<tau> \<Longrightarrow> \<xi>\<^sub>t\<^sub>y x = \<xi>\<^sub>t\<^sub>y' x) \<Longrightarrow>
    (\<And>x. x \<in> free_vars t \<Longrightarrow> \<xi> x = \<xi>' x) \<Longrightarrow> \<L> \<xi>\<^sub>t\<^sub>y \<xi> t = \<L> \<xi>\<^sub>t\<^sub>y' \<xi>' t"

locale interp =
  type_interp \<J>\<^sub>t\<^sub>y +
  interp_fun \<J>\<^sub>t\<^sub>y typeof \<J> +
  lambda_designation \<J>\<^sub>t\<^sub>y typeof \<L>
  for
    \<J>\<^sub>t\<^sub>y :: "('\<Sigma>\<^sub>t\<^sub>y :: type_signature, 'd :: domain_universe) type_interp_fun" and
    typeof :: "'\<Sigma> \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) const_ty" and
    \<J> :: "('\<Sigma>, 'd) term_interp_fun" and
    \<L> :: "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y, '\<V>, '\<Sigma>, 'd) lambda_designation_fun"

primrec preterm_denotation ::
  "('\<V>\<^sub>t\<^sub>y, 'd :: domain_universe) type_valuation \<Rightarrow> ('\<V>, 'd) term_valuation \<Rightarrow>
    ('\<Sigma>\<^sub>t\<^sub>y :: arity, 'd) type_interp_fun \<Rightarrow> ('\<Sigma>, 'd) term_interp_fun \<Rightarrow>
    ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y, '\<V>, '\<Sigma>, 'd) lambda_designation_fun \<Rightarrow>
    (('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) ty, '\<Sigma>, '\<V>) preterm \<Rightarrow> 'd" where
  "preterm_denotation \<xi>\<^sub>t\<^sub>y \<xi> \<J>\<^sub>t\<^sub>y \<J> \<L> (Free x) = \<xi> x" |
  "preterm_denotation \<xi>\<^sub>t\<^sub>y \<xi> \<J>\<^sub>t\<^sub>y \<J> \<L> (Const f \<tau>s ts) =
    \<J> f (map (ty_denotation \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y) \<tau>s) (map (preterm_denotation \<xi>\<^sub>t\<^sub>y \<xi> \<J>\<^sub>t\<^sub>y \<J> \<L>) ts)" |
  "preterm_denotation \<xi>\<^sub>t\<^sub>y \<xi> \<J>\<^sub>t\<^sub>y \<J> \<L> (App t\<^sub>1 t\<^sub>2) = ap_domain (preterm_denotation \<xi>\<^sub>t\<^sub>y \<xi> \<J>\<^sub>t\<^sub>y \<J> \<L> t\<^sub>1) (preterm_denotation \<xi>\<^sub>t\<^sub>y \<xi> \<J>\<^sub>t\<^sub>y \<J> \<L> t\<^sub>1)" |
  "preterm_denotation \<xi>\<^sub>t\<^sub>y \<xi> \<J>\<^sub>t\<^sub>y \<J> \<L> (Abs \<tau> t) = \<L> \<xi>\<^sub>t\<^sub>y \<xi> (Abs \<tau> t)" |
  "preterm_denotation \<xi>\<^sub>t\<^sub>y \<xi> \<J>\<^sub>t\<^sub>y \<J> \<L> (Bound _) = undefined"

lemma (in type_interp) ty_denotation_of_ground:
  assumes "type_vars \<tau> = {}"
  shows "ty_denotation \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y \<tau> = ty_denotation \<xi>\<^sub>t\<^sub>y' \<J>\<^sub>t\<^sub>y \<tau>"
proof (cases \<tau>)
  case (Abs_ty \<tau>')

  then have "type_vars_prety \<tau>' = {}"
    using assms
    by (metis Abs_ty_inverse type_vars.rep_eq)

  then have "prety_denotation \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y \<tau>' = prety_denotation \<xi>\<^sub>t\<^sub>y' \<J>\<^sub>t\<^sub>y \<tau>'"
  proof (induction \<tau>')
    case (PretyVar x)
    then have False
      by simp

    then show ?case ..
  next
    case (PretyCtr \<kappa> \<pi>s)

    then have "\<pi> \<in> set \<pi>s \<Longrightarrow> prety_denotation \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y \<pi> = prety_denotation \<xi>\<^sub>t\<^sub>y' \<J>\<^sub>t\<^sub>y \<pi>"
      for \<pi>
      by simp

    then show ?case
      by (metis (no_types, lifting) map_eq_conv prety_denotation.simps(2))
  qed

  then show ?thesis
    using Abs_ty
    by (metis Abs_ty_inverse ty_denotation_def)
qed

lemma (in interp)
  assumes "free_vars t = {}" and "(\<Union>\<tau> \<in> type_symbols t. type_vars \<tau>) = {}"
  shows "preterm_denotation \<xi>\<^sub>t\<^sub>y \<xi> \<J>\<^sub>t\<^sub>y \<J> \<L> t = preterm_denotation \<xi>\<^sub>t\<^sub>y' \<xi>' \<J>\<^sub>t\<^sub>y \<J> \<L> t"
  using assms
proof (induction t)
  case (Const f \<tau>s ts)

  then have IH': "preterm_denotation \<xi>\<^sub>t\<^sub>y \<xi> \<J>\<^sub>t\<^sub>y \<J> \<L> t = preterm_denotation \<xi>\<^sub>t\<^sub>y' \<xi>' \<J>\<^sub>t\<^sub>y \<J> \<L> t"
    if "t \<in> set ts" for t
    by (simp add: that)

  then have "\<J> f (map (ty_denotation \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y) \<tau>s) (map (preterm_denotation \<xi>\<^sub>t\<^sub>y \<xi> \<J>\<^sub>t\<^sub>y \<J> \<L>) ts) =
    \<J> f (map (ty_denotation \<xi>\<^sub>t\<^sub>y' \<J>\<^sub>t\<^sub>y) \<tau>s) (map (preterm_denotation \<xi>\<^sub>t\<^sub>y' \<xi>' \<J>\<^sub>t\<^sub>y \<J> \<L>) ts)"
    using ty_denotation_of_ground
    by (metis (mono_tags, lifting) Const.prems(2)
        UNION_empty_conv(1) list.map_cong0[of \<tau>s] list.map_cong0[of ts]
        preterm.set_intros(1))

  then show ?case
    by simp
next
  case (Abs \<tau> t)
  have "\<L> \<xi>\<^sub>t\<^sub>y \<xi> (Abs \<tau> t) = \<L> \<xi>\<^sub>t\<^sub>y' \<xi>' (Abs \<tau> t)"
  proof (rule \<L>_depends_only_on_\<xi>_on_vars)
    show "\<And>\<tau>' x. \<tau>' \<in> type_symbols (Abs \<tau> t) \<Longrightarrow> x \<in> type_vars \<tau>' \<Longrightarrow> \<xi>\<^sub>t\<^sub>y x = \<xi>\<^sub>t\<^sub>y' x"
      using Abs.prems(2) by blast
  next
    show "\<And>x. x \<in> free_vars (Abs \<tau> t) \<Longrightarrow> \<xi> x = \<xi>' x"
      by (metis Abs.prems(1) emptyE)
  qed

  then show ?case
    by simp
qed simp_all

locale proper_interp = interp +
  assumes "ap_domain (\<L> \<xi>\<^sub>t\<^sub>y \<xi> (Abs \<tau> t)) a = \<L> \<xi>\<^sub>t\<^sub>y (\<xi>(x := a)) (subst_bound 0 (Free x) t)"

type_synonym ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y, '\<V>, '\<Sigma>) atom = "(('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) ty, '\<Sigma>, '\<V>) preterm uprod"
datatype 'a literal =
  is_pos: Pos (atm: 'a) |
  is_neg: Neg (atm: 'a)

instantiation literal :: (type) uminus
begin

primrec uminus_literal :: "'a literal \<Rightarrow> 'a literal" where
  "uminus (Pos A) = Neg A" |
  "uminus (Neg A) = Pos A"

instance ..

end

fun true_lit ::
  "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: arity, '\<V>, '\<Sigma>, 'd :: domain_universe) model \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y, '\<V>, '\<Sigma>) atom literal \<Rightarrow> bool"
  (infix \<open>\<Turnstile>\<^sub>l\<close> 50) where
  "((\<J>\<^sub>t\<^sub>y, \<J>, \<L>), (\<xi>\<^sub>t\<^sub>y, \<xi>)) \<Turnstile>\<^sub>l (Pos A) \<longleftrightarrow>
    case_uprod (Abs_commute (=)) (map_uprod (preterm_denotation \<xi>\<^sub>t\<^sub>y \<xi> \<J>\<^sub>t\<^sub>y \<J> \<L>) A)" |
  "((\<J>\<^sub>t\<^sub>y, \<J>, \<L>), (\<xi>\<^sub>t\<^sub>y, \<xi>)) \<Turnstile>\<^sub>l (Neg A) \<longleftrightarrow>
    case_uprod (Abs_commute (\<noteq>)) (map_uprod (preterm_denotation \<xi>\<^sub>t\<^sub>y \<xi> \<J>\<^sub>t\<^sub>y \<J> \<L>) A)"

lemma model_exhaust[case_names Model]:
  fixes \<M> :: "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y, '\<V>, '\<Sigma>, 'd) model" and P :: bool
  assumes "\<And>\<J>\<^sub>t\<^sub>y \<J> \<L> \<xi>\<^sub>t\<^sub>y \<xi>. \<M> = ((\<J>\<^sub>t\<^sub>y, \<J>, \<L>), (\<xi>\<^sub>t\<^sub>y, \<xi>)) \<Longrightarrow> P"
  shows P
  using assms
  by (metis prod.exhaust)

lemma apply_commute_Abs_commute_ident_if_commutative[simp]:
  assumes commutative: "\<And>x y. R x y = R y x"
  shows "apply_commute (Abs_commute (\<lambda>x y. R (f x) (f y))) = (\<lambda>x y. R (f x) (f y))"
proof (intro commute.Abs_commute_inverse CollectI allI)
  show "\<And>x y. R (f x) (f y) = R (f y) (f x)"
    using commutative .
qed

lemma apply_commute_Abs_commute_ident_if_eq[simp]:
  shows "apply_commute (Abs_commute (\<lambda>x y. (f x) = (f y))) = (\<lambda>x y. (f x) = (f y))"
  using apply_commute_Abs_commute_ident_if_commutative[of "(=)" f] by metis

lemma case_uprod_Abs_commute_neq[simp]:
  "case_uprod (Abs_commute (\<noteq>)) p \<longleftrightarrow> \<not> case_uprod (Abs_commute (=)) p"
  by (smt (verit) Abs_commute_inverse CollectI
      case_uprod_simps uprod_exhaust)

lemma true_lit_iff_not_true_uminus_lit[simp]: "\<not> (\<M> \<Turnstile>\<^sub>l L) \<longleftrightarrow> \<M> \<Turnstile>\<^sub>l -L"
proof (cases \<M> rule: model_exhaust)
  case (Model \<J>\<^sub>t\<^sub>y \<J> \<L> \<xi>\<^sub>t\<^sub>y \<xi>)
  then show ?thesis
    by (cases L) simp_all
qed

lemma true_lit_Pos_ident: "\<M> \<Turnstile>\<^sub>l (Pos (Upair t t))"
proof (cases \<M> rule: model_exhaust)
  case (Model \<J>\<^sub>t\<^sub>y \<J> \<L> \<xi>\<^sub>t\<^sub>y \<xi>)
  then show ?thesis
    by simp
qed

lemma not_true_lit_Neg_ident: "\<not> (\<M> \<Turnstile>\<^sub>l (Neg (Upair t t)))"
  by (simp add: true_lit_Pos_ident)

definition true_cls ::
  "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: arity, '\<V>, '\<Sigma>, 'd :: domain_universe) model \<Rightarrow>
    ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y, '\<V>, '\<Sigma>) atom literal multiset \<Rightarrow> bool"
  (infix \<open>\<Turnstile>\<^sub>c\<close> 50) where
  "\<M> \<Turnstile>\<^sub>c C \<longleftrightarrow> (\<exists>L \<in># C. \<M> \<Turnstile>\<^sub>l L)"

locale type_interp_with_bool_and_fun = type_interp \<J>\<^sub>t\<^sub>y
  for \<J>\<^sub>t\<^sub>y :: "('\<Sigma>\<^sub>t\<^sub>y :: type_signature, 'd :: {domain_universe, zero, one}) type_interp_fun" +
  assumes
    zero_neq_one: "(0 :: 'd) \<noteq> 1" and
    \<J>\<^sub>t\<^sub>y_bool: "\<J>\<^sub>t\<^sub>y bool_tyctr [] = {0, 1}" (* and
    \<J>\<^sub>t\<^sub>y_fun: "\<And>\<D>\<^sub>1 \<D>\<^sub>2. \<D>\<^sub>1 \<in> \<U> \<Longrightarrow> \<D>\<^sub>2 \<in> \<U> \<Longrightarrow> \<J>\<^sub>t\<^sub>y fun_tyctr [\<D>\<^sub>1, \<D>\<^sub>2] \<subseteq> {}" *)

locale lambda_designation_with_consts = lambda_designation \<J>\<^sub>t\<^sub>y typeof \<L>
  for \<J>\<^sub>t\<^sub>y :: "('\<Sigma>\<^sub>t\<^sub>y :: type_signature, 'd :: domain_universe) type_interp_fun" and
    typeof :: "'\<Sigma> :: term_signature \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) const_ty" and
    \<L> :: "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y, '\<V>, '\<Sigma>, 'd) lambda_designation_fun" +
  assumes
    "typeof True_tconst = (Dlist.empty, [], Bool_ty)"
    "typeof False_tconst = (Dlist.empty, [], Bool_ty)"
    "typeof Neg_tconst = (Dlist.empty, [], Fun_ty Bool_ty Bool_ty)"
    "typeof Conj_tconst = (Dlist.empty, [], Fun_ty Bool_ty (Fun_ty Bool_ty Bool_ty))"
    "typeof Disj_tconst = (Dlist.empty, [], Fun_ty Bool_ty (Fun_ty Bool_ty Bool_ty))"
    "typeof Imp_tconst = (Dlist.empty, [], Fun_ty Bool_ty (Fun_ty Bool_ty Bool_ty))"
    "\<exists>(x :: '\<V>\<^sub>t\<^sub>y). typeof Eq_tconst = (Dlist [x], [], Fun_ty (Tyvar_ty x) (Fun_ty (Tyvar_ty x) Bool_ty))"
    "\<exists>(x :: '\<V>\<^sub>t\<^sub>y). typeof Neq_tconst = (Dlist[x], [], Fun_ty (Tyvar_ty x) (Fun_ty (Tyvar_ty x) Bool_ty))"


datatype mytypes = MyBool | MyInt | MyList | MyFun

instantiation mytypes :: arity
begin

definition arity_mytypes :: "mytypes \<Rightarrow> nat" where
  "arity_mytypes \<tau> \<equiv>
    (case \<tau> of
      MyBool \<Rightarrow> 0 |
      MyInt \<Rightarrow> 0 |
      MyList \<Rightarrow> 1 |
      MyFun \<Rightarrow> 2)"

instance ..

end

lemma arity_mytypes_simps[simp]:
  "arity MyBool = 0"
  "arity MyInt = 0"
  "arity MyList = 1"
  "arity MyFun = 2"
  by (simp_all add: arity_mytypes_def)

lemma "wf_prety (PretyCtr MyList [PretyCtr MyInt []])"
proof (intro wf_prety.PretyCtr ballI)
  show "length [PretyCtr MyInt []] = arity MyList"
    by (simp add: arity_mytypes_def)
next
  show "\<And>\<tau>. \<tau> \<in> set [PretyCtr MyInt []] \<Longrightarrow> wf_prety \<tau>"
    by (auto simp add: arity_mytypes_def intro: wf_prety.intros)
qed

lemma "\<not> wf_prety (PretyCtr MyList [])"
  using wf_prety.cases by fastforce

instantiation mytypes :: type_signature
begin

definition "bool_tyctr_mytypes \<equiv> MyBool"
definition "fun_tyctr_mytypes \<equiv> MyFun"

instance
  by standard (simp_all add: bool_tyctr_mytypes_def fun_tyctr_mytypes_def)

end

datatype mydomain = Dint int | Dbool bool | Dlist "mydomain list"

fun mytypeinterp where
  "mytypeinterp MyInt \<D>s = (if \<D>s = [] then Some {Dint n | n :: int. True} else None)" |
  "mytypeinterp MyBool \<D>s = (if \<D>s = [] then Some {Dbool b | b :: bool. True} else None)" |
  "mytypeinterp MyList \<D>s = (case \<D>s of [\<D>] \<Rightarrow> Some {Dlist ds | ds :: mydomain list. set ds \<subseteq> \<D>} | _ \<Rightarrow> None)"

inductive_set myuniverse where
  "{Dint n | n :: int. True} \<in> myuniverse" |
  "{Dbool b | b :: bool. True} \<in> myuniverse" |
  "\<D> \<in> myuniverse \<Longrightarrow> {Dlist ds | ds :: mydomain list. set ds \<subseteq> \<D>} \<in> myuniverse"

interpretation semantics where
  \<U> = "myuniverse" and
  \<J>\<^sub>t\<^sub>y = "mytypeinterp"
proof unfold_locales
  show "{} \<notin> myuniverse"
    by (metis (mono_tags, lifting)
        empty_Collect_eq empty_subsetI
        list.set(1) myuniverse.simps)
next
  fix \<kappa> \<D>s
  show "(arity \<kappa> = length \<D>s) = (mytypeinterp \<kappa> \<D>s \<noteq> None)"
  proof (cases \<kappa>)
    case MyBool
    then show ?thesis
      by simp
  next
    case MyInt
    then show ?thesis
      by simp
  next
    case MyList
    then show ?thesis
    proof (cases "\<exists>\<D>. \<D>s = [\<D>]")
      case True
      then show ?thesis
        using MyList by auto
    next
      case False
      then show ?thesis
        unfolding MyList arity_mytypes_simps
        by (metis (no_types, lifting) One_nat_def Suc_le_eq
            impossible_Cons length_Cons length_greater_0_conv
            list.simps(4,5) list.size(3) mytypeinterp.simps(3)
            neq_Nil_conv)
    qed
  next
    case MyFun
    then show ?thesis
      sorry
  qed
qed

end