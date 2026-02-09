theory LN_Lambda_Semantics
  imports
    LN_Lambda_Typing
    "HOL-Library.FuncSet"
    ZFC_in_HOL.ZFC_Typeclasses
begin

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

lemma apply_commute_Abs_commute_eq[simp]: "apply_commute (Abs_commute (=)) = (=)"
proof (rule apply_commute_Abs_commute_ident_if_commutative)
  show "\<And>x y. (x = y) = (y = x)"
    by metis
qed

lemma apply_commute_Abs_commute_neq[simp]: "apply_commute (Abs_commute (\<noteq>)) = (\<noteq>)"
proof (rule apply_commute_Abs_commute_ident_if_commutative)
  show "\<And>x y. (x \<noteq> y) = (y \<noteq> x)"
    by metis
qed

lemma case_uprod_Abs_commute_neq[simp]:
  "case_uprod (Abs_commute (\<noteq>)) p \<longleftrightarrow> \<not> case_uprod (Abs_commute (=)) p"
  by (smt (verit) Abs_commute_inverse CollectI case_uprod_simps uprod_exhaust)

term funcset

typ V

find_consts "_ \<Rightarrow> V"

term V_of
term elts


definition V_of :: "'a::embeddable \<Rightarrow> V"
  where "V_of \<equiv> SOME f. inj f"

abbreviation vfunspace :: "V \<Rightarrow> V \<Rightarrow> V"
  where "vfunspace A B \<equiv> VPi A (\<lambda>_. B)"

locale universe =
  fixes \<U> :: "V set"
  assumes nonempty_\<U>: "0 \<notin> \<U>"
  assumes boolset_in_\<U>: "set {0,1} \<in> \<U>"

type_synonym '\<Sigma>\<^sub>t\<^sub>y type_interp_fun = "'\<Sigma>\<^sub>t\<^sub>y \<Rightarrow> V list \<Rightarrow> V"

locale type_interp = universe +
  fixes \<J>\<^sub>t\<^sub>y :: "('\<Sigma>\<^sub>t\<^sub>y :: type_signature) type_interp_fun"
  assumes
    \<J>\<^sub>t\<^sub>y_codom[intro]: "\<And>\<D>s \<kappa>.
      length \<D>s = arity \<kappa> \<Longrightarrow> (\<And>\<D>. \<D> \<in> list.set \<D>s \<Longrightarrow> \<D> \<in> \<U>) \<Longrightarrow> \<J>\<^sub>t\<^sub>y \<kappa> \<D>s \<in> \<U>" and
    \<J>\<^sub>t\<^sub>y_bool[simp]: "\<J>\<^sub>t\<^sub>y bool_tyctr [] = set {0,1}" and
    \<J>\<^sub>t\<^sub>y_fun[intro]: "\<And>\<D>\<^sub>1 \<D>\<^sub>2. \<D>\<^sub>1 \<in> \<U> \<Longrightarrow> \<D>\<^sub>2 \<in> \<U> \<Longrightarrow> \<J>\<^sub>t\<^sub>y fun_tyctr [\<D>\<^sub>1, \<D>\<^sub>2] \<le> vfunspace \<D>\<^sub>1 \<D>\<^sub>2"

locale type_valuation = universe +
  fixes \<xi>\<^sub>t\<^sub>y :: "'\<V>\<^sub>t\<^sub>y \<Rightarrow> V"
  assumes \<xi>\<^sub>t\<^sub>y_codom[intro]: "\<And>x. \<xi>\<^sub>t\<^sub>y x \<in> \<U>"

primrec denotation_prety ::
  "('\<V>\<^sub>t\<^sub>y \<Rightarrow> V) \<Rightarrow> '\<Sigma>\<^sub>t\<^sub>y type_interp_fun \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) prety \<Rightarrow> V" where
  "denotation_prety \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y (PretyVar \<alpha>) = \<xi>\<^sub>t\<^sub>y \<alpha>" |
  "denotation_prety \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y (PretyCtr \<kappa> \<tau>s) = \<J>\<^sub>t\<^sub>y \<kappa> (map (denotation_prety \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y) \<tau>s)"

definition denotation_ty ::
  "('\<V>\<^sub>t\<^sub>y \<Rightarrow> V) \<Rightarrow> '\<Sigma>\<^sub>t\<^sub>y type_interp_fun \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: arity) ty \<Rightarrow> V" where
  "denotation_ty \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y \<tau> = denotation_prety \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y (Rep_ty \<tau>)"

lemma
  assumes "type_interp \<U> \<J>\<^sub>t\<^sub>y" and "type_valuation \<U> \<xi>\<^sub>t\<^sub>y"
  shows
    denotation_prety_in_universe: "\<And>\<tau>. wf_prety \<tau> \<Longrightarrow> denotation_prety \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y \<tau> \<in> \<U>" and
    denotation_ty_in_universe: "\<And>\<tau>. denotation_ty \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y \<tau> \<in> \<U>"
proof -
  show 1: "denotation_prety \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y \<tau> \<in> \<U>" if "wf_prety \<tau>" for \<tau>
    using that
  proof (induction \<tau>)
    case (PretyVar \<alpha>)
    then show ?case
      by (metis assms(2) denotation_prety.simps(1) type_valuation.\<xi>\<^sub>t\<^sub>y_codom)
  next
    case (PretyCtr \<kappa> \<tau>s)
    show ?case
      unfolding denotation_prety.simps
    proof (rule type_interp.\<J>\<^sub>t\<^sub>y_codom[OF assms(1)])
      show "length (map (denotation_prety \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y) \<tau>s) = arity \<kappa>"
        using PretyCtr.hyps by simp
    next
      show "\<And>\<D>. \<D> \<in> list.set (map (denotation_prety \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y) \<tau>s) \<Longrightarrow> \<D> \<in> \<U>"
        using PretyCtr.IH by auto
    qed
  qed

  show "denotation_ty \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y \<tau> \<in> \<U>" for \<tau>
  proof (cases \<tau>)
    case (Abs_ty \<tau>')
    then have "wf_prety \<tau>'"
      by simp
    then have "denotation_prety \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y \<tau>' \<in> \<U>"
      using 1 by iprover
    then show ?thesis
      using Abs_ty
      by (metis Abs_ty_inverse[of \<tau>'] denotation_ty_def)
  qed
qed

locale term_valuation = type_interp \<U> \<J>\<^sub>t\<^sub>y + type_valuation \<U> \<xi>\<^sub>t\<^sub>y for  \<U> \<J>\<^sub>t\<^sub>y \<xi>\<^sub>t\<^sub>y +
  fixes \<xi>\<^sub>t\<^sub>e :: "'\<V>\<^sub>t\<^sub>e \<Rightarrow> V"
  assumes \<xi>\<^sub>t\<^sub>e_codom[intro]: "\<And>x \<tau>. \<xi>\<^sub>t\<^sub>e x \<in> elts (denotation_ty \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y \<tau>)"

locale valuation = type_valuation \<U> \<xi>\<^sub>t\<^sub>y + term_valuation \<U> \<J>\<^sub>t\<^sub>y \<xi>\<^sub>t\<^sub>y \<xi>\<^sub>t\<^sub>e
  for \<U> \<J>\<^sub>t\<^sub>y \<xi>\<^sub>t\<^sub>y \<xi>\<^sub>t\<^sub>e

type_synonym '\<Sigma> term_interp_fun = "'\<Sigma> \<Rightarrow> V list \<Rightarrow> V list \<Rightarrow> V"

locale interp_fun = type_interp \<U> \<J>\<^sub>t\<^sub>y
  for \<U> and \<J>\<^sub>t\<^sub>y :: "('\<Sigma>\<^sub>t\<^sub>y :: type_signature) type_interp_fun" +
  fixes \<C> :: "'\<Sigma> :: term_signature \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) const_ty"
  fixes \<J> :: "'\<Sigma> term_interp_fun"
  assumes "\<And>(\<xi>\<^sub>t\<^sub>y :: '\<V>\<^sub>t\<^sub>y \<Rightarrow> V) f \<alpha>s \<tau>s v \<D>s as.
    type_valuation \<U> \<xi>\<^sub>t\<^sub>y \<Longrightarrow>
    \<C> f = (\<alpha>s, \<tau>s, v) \<Longrightarrow> length \<D>s = Dlist.length \<alpha>s \<Longrightarrow>
    (\<And>\<D>. \<D> \<in> list.set \<D>s \<Longrightarrow> \<D> \<in> \<U>) \<Longrightarrow>
    list_all2 (\<lambda>a \<tau>. a \<in> elts (denotation_ty \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y \<tau>)) as \<tau>s \<Longrightarrow>
    \<J> f \<D>s as \<in> elts (denotation_ty \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y v)"
  assumes \<J>_True: "
    \<J> True_tconst [] [] = 1"
  assumes \<J>_False: "
    \<J> False_tconst [] [] = 0"
  assumes \<J>_Neg: "a \<in> {0, 1} \<Longrightarrow> b \<in> {0, 1} \<Longrightarrow>
    \<J> Neg_tconst [] [a] = (if a = 0 then 1 else 0)"
  assumes \<J>_Conj: "a \<in> {0, 1} \<Longrightarrow> b \<in> {0, 1} \<Longrightarrow>
    \<J> Conj_tconst [] [a, b] = (if a = 1 \<and> b = 1 then 1 else 0)"
  assumes \<J>_Disj: "a \<in> {0, 1} \<Longrightarrow> b \<in> {0, 1} \<Longrightarrow>
    \<J> Disj_tconst [] [a, b] = (if a = 1 \<or> b = 1 then 1 else 0)"
  assumes \<J>_Imp: "a \<in> {0, 1} \<Longrightarrow> b \<in> {0, 1} \<Longrightarrow>
    \<J> Imp_tconst [] [a, b] = (if a = 0 \<or> b = 1 then 1 else 0)"
  assumes \<J>_Eq: "\<D> \<in> \<U> \<Longrightarrow> c \<in> elts \<D> \<Longrightarrow> d \<in> elts \<D> \<Longrightarrow>
    \<J> Eq_tconst [] [c, d] = (if c = d then 1 else 0)"
  assumes \<J>_Neq: "\<D> \<in> \<U> \<Longrightarrow> c \<in> elts \<D> \<Longrightarrow> d \<in> elts \<D> \<Longrightarrow>
    \<J> Neq_tconst [] [c, d] = (if c = d then 0 else 1)"

type_synonym ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y, '\<V>, '\<Sigma>) lambda_designation_fun =
  "('\<V>\<^sub>t\<^sub>y \<Rightarrow> V) \<Rightarrow> ('\<V> \<Rightarrow> V) \<Rightarrow> (('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) ty, '\<Sigma>, '\<V>) preterm \<Rightarrow> V"

locale lambda_designation = type_interp \<U> \<J>\<^sub>t\<^sub>y
  for \<U> and \<J>\<^sub>t\<^sub>y :: "('\<Sigma>\<^sub>t\<^sub>y :: type_signature) type_interp_fun" +
  fixes \<C> :: "'\<Sigma> \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) const_ty"
  fixes \<L> :: "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y, '\<V>, '\<Sigma>) lambda_designation_fun"
  assumes "\<And>(\<xi>\<^sub>t\<^sub>y :: '\<V>\<^sub>t\<^sub>y \<Rightarrow> V) (\<xi>\<^sub>t\<^sub>e :: '\<V> \<Rightarrow> V) (\<F> :: '\<V> \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) ty) t \<tau>.
    type_valuation \<U> \<xi>\<^sub>t\<^sub>y \<Longrightarrow> term_valuation \<U> \<J>\<^sub>t\<^sub>y \<xi>\<^sub>t\<^sub>y \<xi>\<^sub>t\<^sub>e \<Longrightarrow>
    has_type \<C> \<F> t \<tau> \<Longrightarrow> is_Abs t \<Longrightarrow>
    \<L> \<xi>\<^sub>t\<^sub>y \<xi>\<^sub>t\<^sub>e t \<in> elts (denotation_ty \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y \<tau>)"
  assumes \<L>_depends_only_on_\<xi>_on_vars:
    "\<And>(\<xi>\<^sub>t\<^sub>y :: '\<V>\<^sub>t\<^sub>y \<Rightarrow> V) (\<xi>\<^sub>t\<^sub>y' :: '\<V>\<^sub>t\<^sub>y \<Rightarrow> V) (\<xi>\<^sub>t\<^sub>e :: '\<V> \<Rightarrow> V) (\<xi>\<^sub>t\<^sub>e' :: '\<V> \<Rightarrow> V) t.
    (\<And>\<tau> x. \<tau> \<in> type_symbols t \<Longrightarrow> x \<in> type_vars \<tau> \<Longrightarrow> \<xi>\<^sub>t\<^sub>y x = \<xi>\<^sub>t\<^sub>y' x) \<Longrightarrow>
    (\<And>x. x \<in> free_vars t \<Longrightarrow> \<xi>\<^sub>t\<^sub>e x = \<xi>\<^sub>t\<^sub>e' x) \<Longrightarrow> \<L> \<xi>\<^sub>t\<^sub>y \<xi>\<^sub>t\<^sub>e t = \<L> \<xi>\<^sub>t\<^sub>y' \<xi>\<^sub>t\<^sub>e' t"

locale interp =
  type_interp \<U> \<J>\<^sub>t\<^sub>y +
  interp_fun \<U> \<J>\<^sub>t\<^sub>y \<C> \<J> +
  lambda_designation \<U> \<J>\<^sub>t\<^sub>y \<C> \<L>
  for \<U> and
    \<J>\<^sub>t\<^sub>y :: "('\<Sigma>\<^sub>t\<^sub>y :: type_signature) type_interp_fun" and
    \<C> :: "'\<Sigma> :: term_signature \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) const_ty" and
    \<J> :: "'\<Sigma> term_interp_fun" and
    \<L> :: "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y, '\<V>, '\<Sigma>) lambda_designation_fun"

primrec denotation_preterm ::
  "('\<V>\<^sub>t\<^sub>y \<Rightarrow> V) \<Rightarrow> ('\<V> \<Rightarrow> V) \<Rightarrow>
    ('\<Sigma>\<^sub>t\<^sub>y :: arity) type_interp_fun \<Rightarrow> '\<Sigma> term_interp_fun \<Rightarrow>
    ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y, '\<V>, '\<Sigma>) lambda_designation_fun \<Rightarrow>
    (('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) ty, '\<Sigma>, '\<V>) preterm \<Rightarrow> V" where
  "denotation_preterm \<xi>\<^sub>t\<^sub>y \<xi>\<^sub>t\<^sub>e \<J>\<^sub>t\<^sub>y \<J> \<L> (Free x) = \<xi>\<^sub>t\<^sub>e x" |
  "denotation_preterm \<xi>\<^sub>t\<^sub>y \<xi>\<^sub>t\<^sub>e \<J>\<^sub>t\<^sub>y \<J> \<L> (Const f \<tau>s ts) =
    \<J> f (map (denotation_ty \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y) \<tau>s) (map (denotation_preterm \<xi>\<^sub>t\<^sub>y \<xi>\<^sub>t\<^sub>e \<J>\<^sub>t\<^sub>y \<J> \<L>) ts)" |
  "denotation_preterm \<xi>\<^sub>t\<^sub>y \<xi>\<^sub>t\<^sub>e \<J>\<^sub>t\<^sub>y \<J> \<L> (App t\<^sub>1 t\<^sub>2) =
    app (denotation_preterm \<xi>\<^sub>t\<^sub>y \<xi>\<^sub>t\<^sub>e \<J>\<^sub>t\<^sub>y \<J> \<L> t\<^sub>1) (denotation_preterm \<xi>\<^sub>t\<^sub>y \<xi>\<^sub>t\<^sub>e \<J>\<^sub>t\<^sub>y \<J> \<L> t\<^sub>1)" |
  "denotation_preterm \<xi>\<^sub>t\<^sub>y \<xi>\<^sub>t\<^sub>e \<J>\<^sub>t\<^sub>y \<J> \<L> (Abs \<tau> t) = \<L> \<xi>\<^sub>t\<^sub>y \<xi>\<^sub>t\<^sub>e (Abs \<tau> t)" |
  "denotation_preterm \<xi>\<^sub>t\<^sub>y \<xi>\<^sub>t\<^sub>e \<J>\<^sub>t\<^sub>y \<J> \<L> (Bound x) = undefined"


subsection \<open>Denotation of ground terms\<close>

lemma (in type_interp) denotation_ty_of_ground:
  assumes "type_vars \<tau> = {}"
  shows "denotation_ty \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y \<tau> = denotation_ty \<xi>\<^sub>t\<^sub>y' \<J>\<^sub>t\<^sub>y \<tau>"
proof (cases \<tau>)
  case (Abs_ty \<tau>')

  then have "type_vars_prety \<tau>' = {}"
    using assms
    by (metis Abs_ty_inverse type_vars.rep_eq)

  then have "denotation_prety \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y \<tau>' = denotation_prety \<xi>\<^sub>t\<^sub>y' \<J>\<^sub>t\<^sub>y \<tau>'"
  proof (induction \<tau>')
    case (PretyVar x)
    then have False
      by simp
    then show ?case ..
  next
    case (PretyCtr \<kappa> \<pi>s)
    then have "denotation_prety \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y \<pi> = denotation_prety \<xi>\<^sub>t\<^sub>y' \<J>\<^sub>t\<^sub>y \<pi>"
      if "\<pi> \<in> list.set \<pi>s" for \<pi>
      using that by simp
    then show ?case
      by (metis (no_types, lifting) map_eq_conv denotation_prety.simps(2))
  qed

  then show ?thesis
    using Abs_ty
    by (simp add: Abs_ty_inverse denotation_ty_def)
qed

lemma (in interp) denotation_preterm_of_ground:
  assumes "free_vars t = {}" and "(\<Union>\<tau> \<in> type_symbols t. type_vars \<tau>) = {}"
  shows "denotation_preterm \<xi>\<^sub>t\<^sub>y \<xi>\<^sub>t\<^sub>e \<J>\<^sub>t\<^sub>y \<J> \<L> t = denotation_preterm \<xi>\<^sub>t\<^sub>y' \<xi>\<^sub>t\<^sub>e' \<J>\<^sub>t\<^sub>y \<J> \<L> t"
  using assms
proof (induction t)
  case (Const f \<tau>s ts)

  then have IH': "denotation_preterm \<xi>\<^sub>t\<^sub>y \<xi>\<^sub>t\<^sub>e \<J>\<^sub>t\<^sub>y \<J> \<L> t = denotation_preterm \<xi>\<^sub>t\<^sub>y' \<xi>\<^sub>t\<^sub>e' \<J>\<^sub>t\<^sub>y \<J> \<L> t"
    if "t \<in> list.set ts" for t
    using that by simp

  then have "\<J> f (map (denotation_ty \<xi>\<^sub>t\<^sub>y \<J>\<^sub>t\<^sub>y) \<tau>s) (map (denotation_preterm \<xi>\<^sub>t\<^sub>y \<xi>\<^sub>t\<^sub>e \<J>\<^sub>t\<^sub>y \<J> \<L>) ts) =
    \<J> f (map (denotation_ty \<xi>\<^sub>t\<^sub>y' \<J>\<^sub>t\<^sub>y) \<tau>s) (map (denotation_preterm \<xi>\<^sub>t\<^sub>y' \<xi>\<^sub>t\<^sub>e' \<J>\<^sub>t\<^sub>y \<J> \<L>) ts)"
    using denotation_ty_of_ground
    by (metis (mono_tags, lifting) Const.prems(2)
        UNION_empty_conv(1) list.map_cong0[of \<tau>s] list.map_cong0[of ts]
        preterm.set_intros(1))

  then show ?case
    by simp
next
  case (Abs \<tau> t)
  have "\<L> \<xi>\<^sub>t\<^sub>y \<xi>\<^sub>t\<^sub>e (Abs \<tau> t) = \<L> \<xi>\<^sub>t\<^sub>y' \<xi>\<^sub>t\<^sub>e' (Abs \<tau> t)"
  proof (rule \<L>_depends_only_on_\<xi>_on_vars)
    show "\<And>\<tau>' x. \<tau>' \<in> type_symbols (Abs \<tau> t) \<Longrightarrow> x \<in> type_vars \<tau>' \<Longrightarrow> \<xi>\<^sub>t\<^sub>y x = \<xi>\<^sub>t\<^sub>y' x"
      using Abs.prems(2) by blast
  next
    show "\<And>x. x \<in> free_vars (Abs \<tau> t) \<Longrightarrow> \<xi>\<^sub>t\<^sub>e x = \<xi>\<^sub>t\<^sub>e' x"
      by (metis Abs.prems(1) emptyE)
  qed

  then show ?case
    by simp
qed simp_all


subsection \<open>Rest\<close>

locale proper_interp = interp +
  assumes "app (\<L> \<xi>\<^sub>t\<^sub>y \<xi> (Abs \<tau> t)) a = \<L> \<xi>\<^sub>t\<^sub>y (\<xi>(x := a)) (subst_bound 0 (Free x) t)"

declare [[typedef_overloaded]]
record ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: arity, '\<V>, '\<Sigma>) interp =
  \<U> :: "V set"
  \<C> :: "'\<Sigma> \<Rightarrow> '\<V>\<^sub>t\<^sub>y dlist \<times> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) ty list \<times> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) ty"
  \<J>\<^sub>t\<^sub>y :: "'\<Sigma>\<^sub>t\<^sub>y \<Rightarrow> V list \<Rightarrow> V"
  \<J> :: "'\<Sigma> \<Rightarrow> V list \<Rightarrow> V list \<Rightarrow> V"
  \<L> :: "('\<V>\<^sub>t\<^sub>y \<Rightarrow> V) \<Rightarrow> ('\<V> \<Rightarrow> V) \<Rightarrow> (('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) ty, '\<Sigma>, '\<V>) preterm \<Rightarrow> V"

type_synonym ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y, '\<V>, '\<Sigma>) atom = "(('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) ty, '\<Sigma>, '\<V>) preterm uprod"
datatype 'a literal =
  is_pos: Pos (atom: 'a) |
  is_neg: Neg (atom: 'a)

instantiation literal :: (type) uminus
begin

primrec uminus_literal :: "'a literal \<Rightarrow> 'a literal" where
  "uminus (Pos A) = Neg A" |
  "uminus (Neg A) = Pos A"

instance ..

end

fun true_lit ::
  "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: arity, '\<V>, '\<Sigma>) interp \<times> ('\<V>\<^sub>t\<^sub>y \<Rightarrow> V) \<times> ('\<V> \<Rightarrow> V) \<Rightarrow>
    ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y, '\<V>, '\<Sigma>) atom literal \<Rightarrow> bool"
  (infix \<open>\<Turnstile>\<^sub>l\<close> 50) where
  "(\<I>, \<xi>\<^sub>t\<^sub>y, \<xi>\<^sub>t\<^sub>e) \<Turnstile>\<^sub>l (Pos A) \<longleftrightarrow> (case_uprod (Abs_commute (=))
    (map_uprod (denotation_preterm \<xi>\<^sub>t\<^sub>y \<xi>\<^sub>t\<^sub>e (interp.\<J>\<^sub>t\<^sub>y \<I>) (interp.\<J> \<I>) (interp.\<L> \<I>)) A))" |
  "(\<I>, \<xi>\<^sub>t\<^sub>y, \<xi>\<^sub>t\<^sub>e) \<Turnstile>\<^sub>l (Neg A) \<longleftrightarrow> (case_uprod (Abs_commute (\<noteq>))
    (map_uprod (denotation_preterm \<xi>\<^sub>t\<^sub>y \<xi>\<^sub>t\<^sub>e (interp.\<J>\<^sub>t\<^sub>y \<I>) (interp.\<J> \<I>) (interp.\<L> \<I>)) A))"

lemma true_lit_iff_not_true_uminus_lit[simp]: "\<not> (\<I>\<xi> \<Turnstile>\<^sub>l L) \<longleftrightarrow> \<I>\<xi> \<Turnstile>\<^sub>l (-L)"
  by (cases \<I>\<xi>, cases L) simp_all

lemma true_lit_Pos_ident: "\<I>\<xi> \<Turnstile>\<^sub>l (Pos (Upair t t))"
  by (cases \<I>\<xi>) simp

lemma not_true_lit_Neg_ident: "\<not> (\<I>\<xi> \<Turnstile>\<^sub>l (Neg (Upair t t)))"
  by (cases \<I>\<xi>) simp

definition true_cls ::
  "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: arity, '\<V>, '\<Sigma>) interp \<times> ('\<V>\<^sub>t\<^sub>y \<Rightarrow> V) \<times> ('\<V> \<Rightarrow> V) \<Rightarrow>
    ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y, '\<V>, '\<Sigma>) atom literal multiset \<Rightarrow> bool"
  (infix \<open>\<Turnstile>\<^sub>c\<close> 50) where
  "\<I>\<xi> \<Turnstile>\<^sub>c C \<longleftrightarrow> (\<exists>L \<in># C. \<I>\<xi> \<Turnstile>\<^sub>l L)"

definition true_clss ::
  "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: type_signature, '\<V>, '\<Sigma> :: term_signature) interp \<Rightarrow>
    ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y, '\<V>, '\<Sigma>) atom literal multiset set \<Rightarrow> bool"
  (infix \<open>\<Turnstile>\<^sub>c\<^sub>s\<close> 50) where
  "\<I> \<Turnstile>\<^sub>c\<^sub>s N \<longleftrightarrow>
    proper_interp (interp.\<U> \<I>) (interp.\<J>\<^sub>t\<^sub>y \<I>) (interp.\<C> \<I>) (interp.\<J> \<I>) (interp.\<L> \<I>) \<and>
    (\<forall>\<xi>\<^sub>t\<^sub>y \<xi>\<^sub>t\<^sub>e. \<forall>C \<in> N. (\<I>, \<xi>\<^sub>t\<^sub>y, \<xi>\<^sub>t\<^sub>e) \<Turnstile>\<^sub>c C)"

locale diff_aware_proper_interp = proper_interp +
  assumes \<J>_Neq: "
    \<lparr>\<U> = \<U>, \<C> = \<C>, \<J>\<^sub>t\<^sub>y = \<J>\<^sub>t\<^sub>y, \<J> = \<J>, \<L> = \<L>\<rparr> \<Turnstile>\<^sub>c\<^sub>s {
      {#Neg (Upair
          (App z (Const Diff_tconst [\<alpha>, \<beta>] [z, y]))
          (App y (Const Diff_tconst [\<alpha>, \<beta>] [z, y]))),
        Pos (Upair z y)#}}"

end