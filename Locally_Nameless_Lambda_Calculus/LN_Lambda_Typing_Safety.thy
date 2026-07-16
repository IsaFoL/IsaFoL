theory LN_Lambda_Typing_Safety
  imports
    LN_Lambda_Reduction
    LN_Lambda_Typing
begin

context begin

qualified theorem preservation:
  fixes t t' :: "(_, _, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes typed: "has_type \<C> t \<tau>"
    and reduction: "beta_reduce t t'"
  shows "has_type \<C> t' \<tau>"
  using reduction typed
proof (induction arbitrary: \<C> \<tau> rule: beta_reduce.induct)
  case (beta \<tau>' t u)
  from beta.prems obtain sigma where
    abs_typed: "has_type \<C> (Abs \<tau>' t) (TyFun sigma \<tau>)" and
    arg_typed: "has_type \<C> u sigma"
    by (cases rule: has_type.cases) auto
  from abs_typed obtain \<X> where sigma_eq: "sigma = \<tau>'" and
    opened: "\<And>x. x |\<notin>| \<X> \<Longrightarrow>
      has_type \<C> (open_bound 0 \<tau>' (Free x \<tau>') t) \<tau>"
    by (cases rule: has_type.cases) auto
  have arg_typed_\<tau>': "has_type \<C> u \<tau>'"
    using arg_typed sigma_eq by simp
  show ?case
    by (rule has_type_open_bound[OF inf_vars opened arg_typed_\<tau>'])
next
  case (App_left t t' u)
  from App_left.prems obtain sigma where
    left: "has_type \<C> t (TyFun sigma \<tau>)" and right: "has_type \<C> u sigma"
    by (cases rule: has_type.cases) auto
  have "has_type \<C> t' (TyFun sigma \<tau>)"
    by (rule App_left.IH[OF left])
  then show ?case
    using right by (rule has_type.App)
next
  case (App_right t u u')
  from App_right.prems obtain sigma where
    left: "has_type \<C> t (TyFun sigma \<tau>)" and right: "has_type \<C> u sigma"
    by (cases rule: has_type.cases) auto
  have right': "has_type \<C> u' sigma"
    by (rule App_right.IH[OF right])
  show ?case
    by (rule has_type.App[OF left right'])
next
  case (Abs \<X> \<tau>' t t')
  from Abs.prems obtain rho \<Y> where
    \<tau>_eq: "\<tau> = TyFun \<tau>' rho" and
    opened: "\<And>x. x |\<notin>| \<Y> \<Longrightarrow>
      has_type \<C> (open_bound 0 \<tau>' (Free x \<tau>') t) rho"
    by (cases rule: has_type.cases) auto
  show ?case
    unfolding \<tau>_eq
  proof (rule has_type.Abs[where \<X> = "\<X> |\<union>| \<Y>"])
    fix x
    assume fresh: "x |\<notin>| \<X> |\<union>| \<Y>"
    show "has_type \<C> (open_bound 0 \<tau>' (Free x \<tau>') t') rho"
      by (rule Abs.IH[OF _ opened]) (use fresh in auto)
  qed
next
  case (Const ts i t' c \<tau>s)
  from Const.prems obtain alphas sigma_tys result_ty sigma where
    const: "Rep_const_ty (\<C> c) = (alphas, sigma_tys, result_ty)" and
    arity: "Dlist.length alphas = length \<tau>s" and
    sigma: "sigma = fun_upds TyVar (list_of_dlist alphas) \<tau>s" and
    args: "list_all2 (has_type \<C>) ts
      (map (\<lambda>sigma_ty. sigma_ty \<cdot>\<^sub>t\<^sub>y sigma) sigma_tys)" and
    result: "\<tau> = result_ty \<cdot>\<^sub>t\<^sub>y sigma"
    by (cases rule: has_type.cases) auto
  have args': "list_all2 (has_type \<C>) (ts[i := t'])
      (map (\<lambda>sigma_ty. sigma_ty \<cdot>\<^sub>t\<^sub>y sigma) sigma_tys)"
    using args Const.hyps(2)
    by (auto simp: list_all2_conv_all_nth nth_list_update intro: Const.IH)
  show ?case
    by (rule has_type.Const[OF const arity sigma args' result])
qed

end

end
