theory LN_Lambda_Typing_Safety
  imports
    LN_Lambda_Reduction
    LN_Lambda_Typing
begin

context begin

qualified theorem preservation:
  fixes t t' :: "(_, _, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes typed: "has_type \<C> \<F> t \<tau>"
    and reduction: "beta_reduce t t'"
  shows "has_type \<C> \<F> t' \<tau>"
  using reduction typed
proof (induction arbitrary: \<C> \<F> \<tau> rule: beta_reduce.induct)
  case (beta t \<tau>' u)
  from beta.prems obtain sigma where
    abs_typed: "has_type \<C> \<F> (Abs u t) (TyFun sigma \<tau>)" and
    arg_typed: "has_type \<C> \<F> \<tau>' sigma"
    by (cases rule: has_type.cases) auto
  from abs_typed obtain \<X> where sigma_eq: "sigma = u" and
    opened: "\<And>x. x |\<notin>| \<X> \<Longrightarrow>
      has_type \<C> (\<F>(x := u)) (subst_bound 0 (Free x) t) \<tau>"
    by (cases rule: has_type.cases) auto
  have arg_typed_u: "has_type \<C> \<F> \<tau>' u"
    using arg_typed sigma_eq by simp
  obtain x where fresh_\<X>: "x |\<notin>| \<X>" and
    fresh: "\<And>s. s |\<in>| {|t, \<tau>'|} \<Longrightarrow> x \<notin> free_vars s"
    using fresh_for_fset_and_terms[OF inf_vars,
        where \<X> = \<X> and \<T> = "{|t, \<tau>'|}"] by blast
  have fresh_t: "x \<notin> free_vars t" and fresh_arg: "x \<notin> free_vars \<tau>'"
    by (rule fresh; simp)+
  have arg_typed': "has_type \<C> (\<F>(x := u)) \<tau>' u"
    by (rule has_type_weaken_funenv[OF arg_typed_u fresh_arg])
  have substituted:
      "has_type \<C> (\<F>(x := u))
        (subst_free x \<tau>' (subst_bound 0 (Free x) t)) \<tau>"
  proof (rule has_type_subst_free[OF opened[OF fresh_\<X>]])
    show "(\<F>(x := u)) x = u" by simp
    show "has_type \<C> (\<F>(x := u)) \<tau>' u" by (rule arg_typed')
  qed
  have result_typed': "has_type \<C> (\<F>(x := u)) (subst_bound 0 \<tau>' t) \<tau>"
    using substituted
    by (simp only: subst_free_subst_bound_Free_eq_subst_bound[OF fresh_t])
  have fresh_result: "x \<notin> free_vars (subst_bound 0 \<tau>' t)"
  proof
    assume "x \<in> free_vars (subst_bound 0 \<tau>' t)"
    then have "x \<in> free_vars t \<union> free_vars \<tau>'"
      using free_vars_subst_bound_subset by fast
    then show False
      using fresh_t fresh_arg by simp
  qed
  have "has_type \<C> (\<F>(x := u, x := \<F> x)) (subst_bound 0 \<tau>' t) \<tau>"
    by (rule has_type_weaken_funenv[OF result_typed' fresh_result])
  then show ?case
    by simp
next
  case (App_left t t' u)
  from App_left.prems obtain sigma where
    left: "has_type \<C> \<F> t (TyFun sigma \<tau>)" and right: "has_type \<C> \<F> u sigma"
    by (cases rule: has_type.cases) auto
  have "has_type \<C> \<F> t' (TyFun sigma \<tau>)"
    by (rule App_left.IH[OF left])
  then show ?case
    using right by (rule has_type.App)
next
  case (App_right t u u')
  from App_right.prems obtain sigma where
    left: "has_type \<C> \<F> t (TyFun sigma \<tau>)" and right: "has_type \<C> \<F> u sigma"
    by (cases rule: has_type.cases) auto
  have right': "has_type \<C> \<F> u' sigma"
    by (rule App_right.IH[OF right])
  show ?case
    by (rule has_type.App[OF left right'])
next
  case (Abs \<X> t t' \<tau>')
  from Abs.prems obtain rho \<Y> where
    \<tau>_eq: "\<tau> = TyFun \<tau>' rho" and
    opened: "\<And>x. x |\<notin>| \<Y> \<Longrightarrow>
      has_type \<C> (\<F>(x := \<tau>')) (subst_bound 0 (Free x) t) rho"
    by (cases rule: has_type.cases) auto
  show ?case
    unfolding \<tau>_eq
  proof (rule has_type.Abs[where \<X> = "\<X> |\<union>| \<Y>"])
    fix x
    assume fresh: "x |\<notin>| \<X> |\<union>| \<Y>"
    show "has_type \<C> (\<F>(x := \<tau>')) (subst_bound 0 (Free x) t') rho"
      by (rule Abs.IH[OF _ opened]) (use fresh in auto)
  qed
next
  case (Const ts i t' c \<tau>s)
  from Const.prems obtain alphas sigma_tys result_ty sigma where
    const: "\<C> c = (alphas, sigma_tys, result_ty)" and
    arity: "Dlist.length alphas = length \<tau>s" and
    sigma: "sigma = fun_upds TyVar (list_of_dlist alphas) \<tau>s" and
    args: "list_all2 (has_type \<C> \<F>) ts
      (map (\<lambda>sigma_ty. sigma_ty \<cdot>\<^sub>t\<^sub>y sigma) sigma_tys)" and
    result: "\<tau> = result_ty \<cdot>\<^sub>t\<^sub>y sigma"
    by (cases rule: has_type.cases) auto
  have args': "list_all2 (has_type \<C> \<F>) (ts[i := t'])
      (map (\<lambda>sigma_ty. sigma_ty \<cdot>\<^sub>t\<^sub>y sigma) sigma_tys)"
    using args Const.hyps(2)
    by (auto simp: list_all2_conv_all_nth nth_list_update intro: Const.IH)
  show ?case
    by (rule has_type.Const[OF const arity sigma args' result])
qed

end

end
