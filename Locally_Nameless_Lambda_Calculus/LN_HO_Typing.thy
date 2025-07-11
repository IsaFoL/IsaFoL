theory LN_HO_Typing
  imports
    LN_HO_Term
begin

datatype ('\<alpha>, '\<kappa>) ty =
  TyVar '\<alpha> |
  TyCtr '\<kappa> "('\<alpha>, '\<kappa>) ty list" |
  TyBool |
  TyFun "('\<alpha>, '\<kappa>) ty" "('\<alpha>, '\<kappa>) ty"

type_synonym ('\<alpha>, '\<kappa>) const_ty = "'\<alpha> list \<times> ('\<alpha>, '\<kappa>) ty list \<times> ('\<alpha>, '\<kappa>) ty"

inductive has_type ::
  "('c \<rightharpoonup> ('\<alpha>, '\<kappa>) const_ty) \<Rightarrow> ('f \<rightharpoonup> ('\<alpha>, '\<kappa>) ty) \<Rightarrow>
    (('\<alpha>, '\<kappa>) ty, 'c, 'f) preterm \<Rightarrow> ('\<alpha>, '\<kappa>) ty \<Rightarrow> bool"
  for \<C> where
  Const: "has_type \<C> \<F> (Const c \<tau>\<^sub>1s ts) \<tau>\<^sub>3"
    if "\<C> c = Some (\<alpha>s, \<tau>\<^sub>2s, \<tau>\<^sub>3)" and "length \<tau>\<^sub>1s = length \<alpha>s" and "list_all2 (has_type \<C> \<F>) ts \<tau>\<^sub>2s"
    for \<F> c \<tau>\<^sub>1s ts \<tau>\<^sub>3 |
  Free: "has_type \<C> \<F> (Free f) \<tau>"
    if "\<F> f = Some \<tau>"
    for \<F> f \<tau> |
  App: "has_type \<C> \<F> (App t\<^sub>1 t\<^sub>2) \<tau>\<^sub>2"
    if "has_type \<C> \<F> t\<^sub>1 (Fun \<tau>\<^sub>1 \<tau>\<^sub>2)" and "has_type \<C> \<F> t\<^sub>2 \<tau>\<^sub>1"
    for \<F> t\<^sub>1 t\<^sub>2 \<tau>\<^sub>1 \<tau>\<^sub>2 |
  Abs: "has_type \<C> \<F> (Abs \<tau>\<^sub>1 t) (TyFun \<tau>\<^sub>1 \<tau>\<^sub>2)"
    if "\<And>x. x |\<notin>| \<X> \<Longrightarrow> has_type \<C> (\<F>(x \<mapsto> \<tau>\<^sub>1)) (subst_bound 0 (Free x) t) \<tau>\<^sub>2"
    for \<F> t \<tau>\<^sub>1 \<tau>\<^sub>2 \<X>

lemma locally_closed_if_has_type[intro]: "has_type \<C> \<F> t \<tau> \<Longrightarrow> locally_closed t"
proof (induction \<F> t \<tau> rule: has_type.induct)
  case (Const \<F> c \<tau>\<^sub>1s ts \<tau>\<^sub>3 \<alpha>s \<tau>\<^sub>2s)
  show ?case
  proof (rule locally_closed.Const)
    show "list_all locally_closed ts"
      using Const.IH
      by (simp add: list_all2_conv_all_nth list_all_length)
  qed
qed (auto intro: locally_closed.intros)


lemma has_type_weaken_funenv: "has_type \<C> \<F> t \<tau>\<^sub>1 \<Longrightarrow> x \<notin> dom \<F> \<Longrightarrow> has_type \<C> (\<F>(x \<mapsto> \<tau>\<^sub>2)) t \<tau>\<^sub>1"
proof (induction \<F> t \<tau>\<^sub>1 rule: has_type.induct)
  case (Const \<F> c \<tau>\<^sub>1s ts \<tau>\<^sub>3 \<alpha>s \<tau>\<^sub>2s)
  then show ?case
    by (simp add: has_type.Const list_all2_mono)
next
  case (Free \<F> f \<tau>)
  then show ?case
    by (metis Free.prems Free.hyps fun_upd_apply has_type.Free domI)
next
  case (App \<F> t\<^sub>1 t\<^sub>2 \<tau>\<^sub>1 \<tau>\<^sub>2)
  then show ?case
    by (auto intro: has_type.intros)
next
  case (Abs \<F> t \<tau>\<^sub>1 \<tau>\<^sub>3 \<X>)
  show ?case
  proof (rule has_type.Abs)
    fix y
    assume "y |\<notin>| \<X>"
    show "has_type \<C> (\<F>(x \<mapsto> \<tau>\<^sub>2, y \<mapsto> \<tau>\<^sub>1)) (subst_bound 0 (Free y) t) \<tau>\<^sub>3"
    proof (cases "x = y")
      case True

      then have "\<F>(x \<mapsto> \<tau>\<^sub>2, y \<mapsto> \<tau>\<^sub>1) = \<F>(y \<mapsto> \<tau>\<^sub>1)"
        by simp

      then show ?thesis
        using Abs.hyps \<open>y |\<notin>| \<X>\<close> by metis
    next
      case False

      then have "\<F>(x \<mapsto> \<tau>\<^sub>2, y \<mapsto> \<tau>\<^sub>1) = \<F>(y \<mapsto> \<tau>\<^sub>1, x \<mapsto> \<tau>\<^sub>2)"
        by auto

      moreover have "x \<notin> dom (\<F>(y \<mapsto> \<tau>\<^sub>1))"
        using \<open>x \<notin> dom \<F>\<close> \<open>x \<noteq> y\<close> by simp

      ultimately show ?thesis
        using Abs.IH \<open>y |\<notin>| \<X>\<close> by metis
    qed
  qed
qed

lemma has_type_subst_free:
  fixes t :: "(('\<alpha>, '\<kappa>) ty, 'c, 'f) preterm"
  assumes inf_vars: "infinite (UNIV :: 'f set)"
  assumes "has_type \<C> \<F> t \<tau>\<^sub>1" and "finite (dom \<F>)" and "\<F> x = Some \<tau>\<^sub>2" and "has_type \<C> \<F> u \<tau>\<^sub>2"
  shows "has_type \<C> \<F> (subst_free x u t) \<tau>\<^sub>1"
  using assms(2-5)
proof (induction \<F> t \<tau>\<^sub>1 rule: has_type.induct)
  case (Const \<F> c \<tau>\<^sub>1s ts \<tau>\<^sub>3 \<alpha>s \<tau>\<^sub>2s)
  then show ?case
    by (simp add: has_type.Const list_all2_mono)
next
  case (Free \<F> f \<tau>)
  then show ?case
    by (auto intro: has_type.intros)
next
  case (App \<F> t\<^sub>1 t\<^sub>2 \<tau>\<^sub>1 \<tau>\<^sub>2)
  then show ?case
    by (auto intro: has_type.intros)
next
  case (Abs \<F> t \<tau>\<^sub>1 \<tau>\<^sub>3 \<X>)
  show ?case
    unfolding subst_free.simps
  proof (rule has_type.Abs)
    fix y
    assume y_in: "y |\<notin>| \<X> |\<union>| Abs_fset (dom \<F>)"

    moreover have "x \<in> dom \<F>"
      using Abs.prems by auto

    ultimately have "x \<noteq> y"
      using Abs.prems(1) Abs_fset_inverse by blast

    moreover have "locally_closed u"
      using Abs.prems by auto

    moreover have "has_type \<C> (\<F>(y \<mapsto> \<tau>\<^sub>1)) (subst_free x u (subst_bound 0 (Free y) t)) \<tau>\<^sub>3"
    proof (rule Abs.IH)
      show "y |\<notin>| \<X>"
        using y_in by simp
    next
      show "finite (dom (\<F>(y \<mapsto> \<tau>\<^sub>1)))"
        using Abs.prems by simp
    next
      show "(\<F>(y \<mapsto> \<tau>\<^sub>1)) x = Some \<tau>\<^sub>2"
        using Abs.prems \<open>x \<noteq> y\<close> by simp
    next
      have "y \<notin> dom \<F>"
        using y_in Abs.prems(1) Abs_fset_inverse by auto

      then show "has_type \<C> (\<F>(y \<mapsto> \<tau>\<^sub>1)) u \<tau>\<^sub>2"
        using Abs.prems has_type_weaken_funenv by metis
    qed

    ultimately show "has_type \<C> (\<F>(y \<mapsto> \<tau>\<^sub>1)) (subst_bound 0 (Free y) (subst_free x u t)) \<tau>\<^sub>3"
      using subst_free_commutes_with_subst_bound_Free[OF inf_vars] by metis
  qed
qed

end