theory LN_Lambda_Strong_Normalization
  imports
    LN_Lambda_Reduction
    LN_Lambda_Typing
begin

text \<open>Strong normalization of the well-typed fragment, via Tait/Girard reducibility.\<close>


section \<open>Strong normalization predicate\<close>

text \<open>\<open>SN t\<close> holds when every \<open>\<beta>\<close>-reduction sequence starting from \<open>t\<close> terminates. Rather than a
  bespoke predicate we reuse the accessible part \<^const>\<open>Wellfounded.accp\<close> of one-step reduction;
  \<open>SN\<close> is merely an abbreviation (no new constant), so all of \<^const>\<open>Wellfounded.accp\<close>'s library
  (well-founded induction, etc.) is available directly.\<close>

abbreviation SN :: "('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> bool" where
  "SN \<equiv> Wellfounded.accp beta_reduce\<inverse>\<inverse>"

lemma SN_I:
  assumes "\<And>u. beta_reduce t u \<Longrightarrow> SN u"
  shows "SN t"
proof (rule accpI)
  fix u
  assume "beta_reduce\<inverse>\<inverse> u t"
  then have "beta_reduce t u"
    by simp
  then show "SN u"
    by (rule assms)
qed

lemma SN_step:
  assumes "SN t" and "beta_reduce t u"
  shows "SN u"
proof -
  from assms(1) show ?thesis
  proof (rule accp.cases)
    fix x
    assume t_eq: "t = x"
      and reducts: "\<And>y. beta_reduce\<inverse>\<inverse> y x \<Longrightarrow> SN y"
    have "beta_reduce x u"
      using assms(2) t_eq by simp
    then show "SN u"
      by (simp add: reducts)
  qed
qed

lemma not_SN_if_beta_reduce_self:
  assumes loop: "beta_reduce t t"
  shows "\<not> SN t"
proof
  assume "SN t"
  then have "\<not> beta_reduce t t"
  proof (induction t rule: accp_induct_rule)
    case (1 s)
    then show ?case
      by (metis conversepI)
  qed
  with loop show False
    by contradiction
qed


section \<open>Degenerate behaviour over a finite variable type\<close>

text \<open>Over a finite variable type, some finite set contains every variable (see \<open>ex_fset_UNIV\<close>),
  which makes the cofinite premise of the \<open>Abs\<close> rule of \<^const>\<open>beta_reduce\<close> vacuously true: any
  two abstractions (with the same type annotation) are related by \<^const>\<open>beta_reduce\<close>.
  Consequently, every locally closed preterm that admits a reduction also reduces to itself---and
  is therefore not strongly normalizing---and likewise below \<^const>\<open>subst_bound\<close>.\<close>

lemma beta_reduce_Abs_Abs_if_finite_vars:
  fixes t t' :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes fin_vars: "finite (UNIV :: '\<V> set)"
  shows "beta_reduce (Abs \<tau> t) (Abs \<tau> t')"
proof -
  obtain \<X> :: "'\<V> fset" where "\<forall>x. x |\<in>| \<X>"
    using ex_fset_UNIV[OF fin_vars] by blast
  then show ?thesis
    by (auto intro: beta_reduce.Abs[where \<X> = \<X>])
qed

lemma beta_reduce_self_if_finite_vars:
  fixes t t' :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes fin_vars: "finite (UNIV :: '\<V> set)"
  assumes "beta_reduce t t'" and "locally_closed t"
  shows "beta_reduce t t"
  using assms(2,3)
proof (induction rule: beta_reduce.induct)
  case (beta t u \<tau>)
  then show ?case
    by (auto intro: beta_reduce.App_left beta_reduce_Abs_Abs_if_finite_vars[OF fin_vars])
next
  case (App_left t t' u)
  then show ?case
    by (auto intro: beta_reduce.App_left simp: locally_closed_App_iff)
next
  case (App_right t u u')
  then show ?case
    by (auto intro: beta_reduce.App_right simp: locally_closed_App_iff)
next
  case (Abs \<X> t t' \<tau>)
  show ?case
    by (rule beta_reduce_Abs_Abs_if_finite_vars[OF fin_vars])
next
  case (Const ts i t' c \<tau>s)
  then have "beta_reduce (ts ! i) (ts ! i)"
    by simp
  then show ?case
    using Const.hyps by (metis beta_reduce.Const list_update_id)
qed

lemma beta_reduce_subst_bound_self_if_finite_vars:
  fixes t t' :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes fin_vars: "finite (UNIV :: '\<V> set)"
  assumes "beta_reduce t t'"
  shows "beta_reduce (subst_bound n u t) (subst_bound n u t)"
  using assms(2)
proof (induction arbitrary: n rule: beta_reduce.induct)
  case (beta s v \<tau>)
  then show ?case
    unfolding subst_bound.simps
    by (auto intro: beta_reduce.App_left beta_reduce_Abs_Abs_if_finite_vars[OF fin_vars]
        locally_closed_subst_bound_if_finite_vars[OF fin_vars])
next
  case (App_left s s' v)
  then show ?case
    unfolding subst_bound.simps
    by (auto intro: beta_reduce.App_left locally_closed_subst_bound_if_finite_vars[OF fin_vars])
next
  case (App_right s v v')
  then show ?case
    unfolding subst_bound.simps
    by (auto intro: beta_reduce.App_right locally_closed_subst_bound_if_finite_vars[OF fin_vars])
next
  case (Abs \<X> s s' \<tau>)
  show ?case
    unfolding subst_bound.simps
    by (rule beta_reduce_Abs_Abs_if_finite_vars[OF fin_vars])
next
  case (Const ts i t' c \<tau>s)
  have "beta_reduce (ts ! i) (ts ! i)"
    using Const.hyps
    by (auto intro: beta_reduce_self_if_finite_vars[OF fin_vars])
  then have "beta_reduce (Const c \<tau>s ts) (Const c \<tau>s ts)"
    using Const.hyps by (metis beta_reduce.Const list_update_id)
  then show ?case
    by simp
qed



lemma SN_App_leftD:
  fixes t u :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes "SN (App t u)" and "locally_closed u"
  shows "SN t"
  using assms
proof (induction "App t u" arbitrary: t u rule: accp_induct_rule)
  case 1
  note IH = "1.hyps"(2)
  show ?case
  proof (rule accpI)
    fix t'
    assume "beta_reduce\<inverse>\<inverse> t' t"
    then have red: "beta_reduce t t'"
      by simp
    have app_red: "beta_reduce (App t u) (App t' u)"
      by (rule beta_reduce.App_left[OF red "1.prems"])
    have "beta_reduce\<inverse>\<inverse> (App t' u) (App t u)"
      using app_red by (rule conversepI)
    then show "SN t'"
      by (rule IH[OF _ "1.prems"])
  qed
qed

lemma SN_App_rightD:
  fixes t u :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes "SN (App t u)" and "locally_closed t"
  shows "SN u"
  using assms
proof (induction "App t u" arbitrary: t u rule: accp_induct_rule)
  case 1
  note IH = "1.hyps"(2)
  show ?case
  proof (rule accpI)
    fix u'
    assume "beta_reduce\<inverse>\<inverse> u' u"
    then have red: "beta_reduce u u'"
      by simp
    have app_red: "beta_reduce (App t u) (App t u')"
      by (rule beta_reduce.App_right[OF "1.prems" red])
    have "beta_reduce\<inverse>\<inverse> (App t u') (App t u)"
      using app_red by (rule conversepI)
    then show "SN u'"
      by (rule IH[OF _ "1.prems"])
  qed
qed

lemma SN_AppD:
  fixes t u :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes "locally_closed t" and "locally_closed u" and "SN (App t u)"
  shows "SN t \<and> SN u"
proof
  show "SN t"
    by (rule SN_App_leftD[OF assms(3,2)])
  show "SN u"
    by (rule SN_App_rightD[OF assms(3,1)])
qed

lemma SN_AbsD:
  fixes t :: "(_, _, '\<V>) preterm"
  assumes "SN (Abs \<tau> t)"
  shows "SN t"
proof (cases "infinite (UNIV :: '\<V> set)")
  case True
  have inf_vars: "infinite (UNIV :: '\<V> set)"
    by (rule True)
  show ?thesis
    using assms
  proof (induction "Abs \<tau> t" arbitrary: \<tau> t rule: accp_induct_rule)
    case 1
    note IH = "1.hyps"(2)
    show ?case
    proof (rule accpI)
      fix t'
      assume conv: "beta_reduce\<inverse>\<inverse> t' t"
      then have red: "beta_reduce t t'"
        by simp
      have abs_red: "beta_reduce (Abs \<tau> t) (Abs \<tau> t')"
      proof (rule beta_reduce.Abs[where \<X> = "{||}"])
        fix x
        show "beta_reduce (subst_bound 0 (Free x) t)
            (subst_bound 0 (Free x) t')"
          by (rule beta_reduce_subst_bound_subst_bound[OF inf_vars red locally_closed.Free])
      qed
      have "beta_reduce\<inverse>\<inverse> (Abs \<tau> t') (Abs \<tau> t)"
        using abs_red by (rule conversepI)
      then show "SN t'"
        by (rule IH)
    qed
  qed
next
  case False
  then have fin_vars: "finite (UNIV :: '\<V> set)"
    by simp
  have "\<not> SN (Abs \<tau> t)"
    by (rule not_SN_if_beta_reduce_self[OF beta_reduce_Abs_Abs_if_finite_vars[OF fin_vars]])
  with assms show ?thesis
    by contradiction
qed

lemma SN_ConstD:
  fixes ts :: "('\<tau>, '\<Sigma>, '\<V>) preterm list"
  assumes "locally_closed (Const c \<tau>s ts)"
  assumes "SN (Const c \<tau>s ts)"
  assumes "t \<in> set ts"
  shows "SN t"
proof (cases "infinite (UNIV :: '\<V> set)")
  case inf_vars: True
  have constD:
    "SN (Const c \<tau>s ts) \<Longrightarrow> locally_closed (Const c \<tau>s ts) \<Longrightarrow> t \<in> set ts \<Longrightarrow> SN t"
    for c :: '\<Sigma> and \<tau>s :: "'\<tau> list"
      and ts :: "('\<tau>, '\<Sigma>, '\<V>) preterm list" and t
  proof (induction "Const c \<tau>s ts" arbitrary: c \<tau>s ts t rule: accp_induct_rule)
    case 1
    note IH = "1.hyps"(2)
    show ?case
    proof (rule accpI)
      fix t'
      assume conv: "beta_reduce\<inverse>\<inverse> t' t"
      then have red: "beta_reduce t t'"
        by simp
      obtain i where i: "i < length ts" and ts_i: "ts ! i = t"
        using "1.prems"(2) by (meson in_set_conv_nth)
      have const_red: "beta_reduce (Const c \<tau>s ts) (Const c \<tau>s (ts[i := t']))"
      proof (rule beta_reduce.Const)
        show "\<forall>t \<in> set ts. locally_closed t"
          using "1.prems"(1) by simp
      next
        show "i < length ts" and "beta_reduce (ts ! i) t'"
          using i ts_i red by simp_all
      qed
      have lc_target: "locally_closed (Const c \<tau>s (ts[i := t']))"
        by (rule locally_closed_if_beta_reduce(2)[OF inf_vars const_red])
      have t'_in_target: "t' \<in> set (ts[i := t'])"
        using i by (simp add: set_update_memI)
      have conv_const: "beta_reduce\<inverse>\<inverse> (Const c \<tau>s (ts[i := t'])) (Const c \<tau>s ts)"
        using const_red by (rule conversepI)
      show "SN t'"
        using IH conv_const lc_target t'_in_target by blast
    qed
  qed
  show ?thesis
    using assms by (auto intro: constD)
next
  case False
  then have fin_vars: "finite (UNIV :: '\<V> set)"
    by simp
  have lc_t: "locally_closed t"
    using assms(1,3) by simp
  show ?thesis
  proof (cases "\<exists>t'. beta_reduce t t'")
    case True
    then obtain t' where "beta_reduce t t'" ..
    then have loop_t: "beta_reduce t t"
      by (rule beta_reduce_self_if_finite_vars[OF fin_vars _ lc_t])
    obtain i where "i < length ts" and "ts ! i = t"
      using assms(3) by (meson in_set_conv_nth)
    then have "beta_reduce (Const c \<tau>s ts) (Const c \<tau>s ts)"
      using assms(1) loop_t
      by (metis beta_reduce.Const list_update_id locally_closed_Const_iff)
    then have "\<not> SN (Const c \<tau>s ts)"
      by (rule not_SN_if_beta_reduce_self)
    with assms(2) show ?thesis
      by contradiction
  next
    case False
    then show ?thesis
      by (auto intro: SN_I)
  qed
qed

lemma SN_subst_bound_FreeD:
  fixes t :: "(_, _, '\<V>) preterm"
  assumes "SN (subst_bound n (Free x) t)"
  shows "SN t"
proof (cases "infinite (UNIV :: '\<V> set)")
  case inf_vars: True
  show ?thesis
    using assms
  proof (induction "subst_bound n (Free x) t" arbitrary: n x t rule: accp_induct_rule)
    case 1
    note IH = "1.hyps"(2)
    show ?case
    proof (rule accpI)
      fix t'
      assume conv: "beta_reduce\<inverse>\<inverse> t' t"
      then have red: "beta_reduce t t'"
        by simp
      have opened_red:
        "beta_reduce (subst_bound n (Free x) t) (subst_bound n (Free x) t')"
        by (rule beta_reduce_subst_bound_subst_bound[OF inf_vars red locally_closed.Free])
      have conv_opened:
        "beta_reduce\<inverse>\<inverse> (subst_bound n (Free x) t') (subst_bound n (Free x) t)"
        using opened_red by (rule conversepI)
      show "SN t'"
        using IH conv_opened by blast
    qed
  qed
next
  case False
  then have fin_vars: "finite (UNIV :: '\<V> set)"
    by simp
  show ?thesis
  proof (cases "\<exists>t'. beta_reduce t t'")
    case True
    then obtain t' where "beta_reduce t t'" ..
    then have "beta_reduce (subst_bound n (Free x) t) (subst_bound n (Free x) t)"
      by (rule beta_reduce_subst_bound_self_if_finite_vars[OF fin_vars])
    then have "\<not> SN (subst_bound n (Free x) t)"
      by (rule not_SN_if_beta_reduce_self)
    with assms show ?thesis
      by contradiction
  next
    case False
    then show ?thesis
      by (auto intro: SN_I)
  qed
qed
text \<open>Bridge to the goal: if every element of a set is strongly normalizing, then the reversed
  reduction relation is well-founded on that set.\<close>

lemma wfp_on_beta_reduce_if_SN:
  assumes "\<And>t. t \<in> A \<Longrightarrow> SN t"
  shows "wfp_on A beta_reduce\<inverse>\<inverse>"
proof -
  have "Wellfounded.accp (\<lambda>x y. beta_reduce y x \<and> x \<in> A \<and> y \<in> A) y"
    if "beta_reduce x y" and "y \<in> A" and "x \<in> A"
    for x y
    using assms(1)[OF \<open>y \<in> A\<close>, unfolded conversep_iff] that
    by (smt (verit, ccfv_SIG) accpI accp_induct)

  then have "wfp (\<lambda>x y. beta_reduce y x \<and> x \<in> A \<and> y \<in> A)"
    by (metis (no_types, lifting) accpI accp_wfpI)

  then show ?thesis
    unfolding conversep_iff wfp_on_iff_wfp[of A] .
qed


section \<open>Reducibility candidates\<close>

text \<open>A term is \<^emph>\<open>neutral\<close> when it is not an abstraction; applying it to an argument creates no
  redex at the root.\<close>

definition neutral :: "('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> bool" where
  "neutral t \<longleftrightarrow> \<not> is_Abs t"

text \<open>Reducibility \<open>Red_ty \<tau> t\<close> is defined by recursion on the type \<open>\<tau>\<close>. At a function type a term
  is reducible iff it is strongly normalizing and sends reducible, locally closed arguments to
  reducible results; at any other type reducibility is just strong normalization.\<close>

function Red_ty ::
  "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: type_signature) ty \<Rightarrow> (('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) ty, '\<Sigma>, '\<V>) preterm \<Rightarrow> bool" where
  "Red_ty (TyFun \<tau>\<^sub>1 \<tau>\<^sub>2) t \<longleftrightarrow> (SN t \<and> (\<forall>u. locally_closed u \<longrightarrow> Red_ty \<tau>\<^sub>1 u \<longrightarrow> Red_ty \<tau>\<^sub>2 (App t u)))" |
  "\<not> is_TyFun \<tau> \<Longrightarrow> Red_ty \<tau> t \<longleftrightarrow> SN t"
proof -
  \<comment> \<open>Pattern completeness\<close>
  show "\<And>P x. (\<And>\<tau>\<^sub>1 \<tau>\<^sub>2 t. x = (TyFun \<tau>\<^sub>1 \<tau>\<^sub>2, t) \<Longrightarrow> P) \<Longrightarrow> (\<And>\<tau> t. \<not> is_TyFun \<tau> \<Longrightarrow> x = (\<tau>, t) \<Longrightarrow> P) \<Longrightarrow> P"
    by (metis prod.exhaust)

  \<comment> \<open>The remaining subgoals are pattern compatibility.\<close>
qed auto
termination
proof (relation "measure (\<lambda>(\<tau>, t). size_ty (\<lambda>_. 0) (\<lambda>_. 0) \<tau>)")
  show "wf (measure (\<lambda>(\<tau>, t). size_ty (\<lambda>_. 0) (\<lambda>_. 0) \<tau>))"
    by simp
next
  fix \<tau>\<^sub>1 \<tau>\<^sub>2 t x
  assume "locally_closed x"
  then have "size_ty (\<lambda>_. 0) (\<lambda>_. 0) \<tau>\<^sub>1 < size_ty (\<lambda>_. 0) (\<lambda>_. 0) (TyFun \<tau>\<^sub>1 \<tau>\<^sub>2)"
    unfolding size_ty_TyFun
    by linarith
  then show "((\<tau>\<^sub>1, x), TyFun \<tau>\<^sub>1 \<tau>\<^sub>2, t) \<in> measure (\<lambda>(\<tau>, t). size_ty (\<lambda>_. 0) (\<lambda>_. 0) \<tau>)"
    by simp
next
  fix \<tau>\<^sub>1 \<tau>\<^sub>2 t x
  assume "locally_closed x" and "Red_ty \<tau>\<^sub>1 x" and "Red_ty_dom (\<tau>\<^sub>1, x)"
  then have "size_ty (\<lambda>_. 0) (\<lambda>_. 0) \<tau>\<^sub>2 < size_ty (\<lambda>_. 0) (\<lambda>_. 0) (TyFun \<tau>\<^sub>1 \<tau>\<^sub>2)"
    unfolding size_ty_TyFun
    by linarith
  then show "((\<tau>\<^sub>2, App t x), TyFun \<tau>\<^sub>1 \<tau>\<^sub>2, t) \<in> measure (\<lambda>(\<tau>, t). size_ty (\<lambda>_. 0) (\<lambda>_. 0) \<tau>)"
    by simp
qed

section \<open>Reducibility candidate properties (CR1--CR3)\<close>

lemma CR1: "Red_ty \<tau> t \<Longrightarrow> SN t"
  by (cases "is_TyFun \<tau>") auto

lemma CR2:
  assumes "Red_ty \<tau> t" and "beta_reduce t t'"
  shows "Red_ty \<tau> t'"
  using assms
proof (induction \<tau> t arbitrary: t' rule: Red_ty.induct)
  case (1 \<tau>\<^sub>1 \<tau>\<^sub>2 t)
  have "SN t'"
    using "1.prems" SN_step by (metis Red_ty.simps(1))
  moreover have "Red_ty \<tau>\<^sub>2 (App t' u)"
    if u: "locally_closed u" "Red_ty \<tau>\<^sub>1 u" for u
  proof -
    have "Red_ty \<tau>\<^sub>2 (App t u)"
      using "1.prems"(1) u by simp
    moreover have "beta_reduce (App t u) (App t' u)"
      using "1.prems"(2)
      by (metis App_left u(1))
    ultimately show ?thesis
      using "1.IH"(2)[OF u(1) u(2)] by blast
  qed
  ultimately show ?case
    by simp
next
  case (2 \<tau> t)
  then show ?case
    using SN_step by (metis Red_ty.simps(2))
qed

text \<open>Inverting a \<open>\<beta>\<close>-step out of an application with a \<^emph>\<open>neutral\<close> head: since the head is not an
  abstraction, no redex is created at the root, so the step happens in one of the two immediate
  subterms.\<close>

lemma beta_reduce_App_neutralD:
  assumes "beta_reduce (App t u) v" and "neutral t"
  shows "(\<exists>t'. v = App t' u \<and> beta_reduce t t') \<or> (\<exists>u'. v = App t u' \<and> beta_reduce u u')"
  using assms by (auto simp: neutral_def elim: beta_reduce.cases)

text \<open>Over a finite variable type, a locally closed, strongly normalizing preterm is \<open>\<beta>\<close>-normal
  (otherwise it would reduce to itself), and \<open>\<beta>\<close>-normal preterms are reducible at every type: an
  application of a \<open>\<beta>\<close>-normal preterm to a locally closed, reducible argument is itself \<open>\<beta>\<close>-normal
  because the head cannot be an abstraction (abstractions are never \<open>\<beta>\<close>-normal over a finite
  variable type) and the argument is \<open>\<beta>\<close>-normal as well.\<close>

lemma beta_normal_if_SN_if_finite_vars:
  fixes t :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes fin_vars: "finite (UNIV :: '\<V> set)"
  assumes "locally_closed t" and "SN t"
  shows "beta_normal t"
  unfolding beta_normal_def
  using beta_reduce_self_if_finite_vars[OF fin_vars _ assms(2)]
    not_SN_if_beta_reduce_self assms(3)
  by metis

lemma Red_ty_if_beta_normal_if_finite_vars:
  fixes t :: "(('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: type_signature) ty, '\<Sigma>, '\<V>) preterm"
  assumes fin_vars: "finite (UNIV :: '\<V> set)"
  assumes "beta_normal t"
  shows "Red_ty \<tau> t"
  using assms(2)
proof (induction \<tau> t rule: Red_ty.induct)
  case (1 \<tau>\<^sub>1 \<tau>\<^sub>2 t)
  have SN_t: "SN t"
    using "1.prems" unfolding beta_normal_def
    by (auto intro: SN_I)
  moreover have "Red_ty \<tau>\<^sub>2 (App t u)" if lc_u: "locally_closed u" and red_u: "Red_ty \<tau>\<^sub>1 u" for u
  proof (rule "1.IH"(2)[OF lc_u red_u])
    have "beta_normal u"
      by (rule beta_normal_if_SN_if_finite_vars[OF fin_vars lc_u CR1[OF red_u]])
    moreover have "\<not> is_Abs t"
      using "1.prems" beta_reduce_Abs_Abs_if_finite_vars[OF fin_vars]
      unfolding beta_normal_def
      by (metis preterm.collapse(5))
    ultimately show "beta_normal (App t u)"
      using "1.prems"
      unfolding beta_normal_def
      by (auto elim: beta_reduce.cases)
  qed
  ultimately show ?case
    by simp
next
  case (2 \<tau> t)
  then show ?case
    unfolding beta_normal_def
    by (auto intro: SN_I "2.hyps"[THEN Red_ty.simps(2)[THEN iffD2]])
qed

lemma CR3:
  fixes t :: "(_, _, '\<V>) preterm"
  assumes "neutral t" and "locally_closed t" and "\<And>t'. beta_reduce t t' \<Longrightarrow> Red_ty \<tau> t'"
  shows "Red_ty \<tau> t"
proof (cases "infinite (UNIV :: '\<V> set)")
  case False
  then have fin_vars: "finite (UNIV :: '\<V> set)"
    by simp
  show ?thesis
  proof (cases "\<exists>t'. beta_reduce t t'")
    case True
    then obtain t' where "beta_reduce t t'" ..
    then have "beta_reduce t t"
      by (rule beta_reduce_self_if_finite_vars[OF fin_vars _ assms(2)])
    then show ?thesis
      by (rule assms(3))
  next
    case False
    then show ?thesis
      by (intro Red_ty_if_beta_normal_if_finite_vars[OF fin_vars])
        (simp add: beta_normal_def)
  qed
next
  case inf_vars: True
  show ?thesis
  using assms
proof (induction \<tau> t rule: Red_ty.induct)
  case (1 \<tau>\<^sub>1 \<tau>\<^sub>2 t)
  note neutral_t = "1.prems"(1) and lc_t = "1.prems"(2) and reds_t = "1.prems"(3)
  note IH2 = "1.IH"(2)
  have SN_t: "SN t"
  proof (rule SN_I)
    fix y
    assume "beta_reduce t y"
    then have "Red_ty (TyFun \<tau>\<^sub>1 \<tau>\<^sub>2) y"
      by (rule reds_t)
    then show "SN y"
      by (rule CR1)
  qed
  have red_App: "Red_ty \<tau>\<^sub>2 (App t u)" if "locally_closed u" and "Red_ty \<tau>\<^sub>1 u" for u
  proof -
    have "SN u" using \<open>Red_ty \<tau>\<^sub>1 u\<close> by (rule CR1)
    then show ?thesis using \<open>locally_closed u\<close> \<open>Red_ty \<tau>\<^sub>1 u\<close>
    proof (induction u rule: accp_induct_rule)
      case (1 w)
      note IH_w = "1.IH"
      note lc_w = "1.prems"(1) and red_w = "1.prems"(2)
      show ?case
      proof (rule IH2[OF lc_w red_w])
        show "neutral (App t w)"
          by (simp add: neutral_def)
      next
        show "locally_closed (App t w)"
          using lc_t lc_w by (rule locally_closed.App)
      next
        fix v assume "beta_reduce (App t w) v"
        from beta_reduce_App_neutralD[OF this neutral_t] show "Red_ty \<tau>\<^sub>2 v"
        proof
          assume "\<exists>t'. v = App t' w \<and> beta_reduce t t'"
          then obtain t' where v: "v = App t' w" and "beta_reduce t t'"
            by blast
          have "Red_ty (TyFun \<tau>\<^sub>1 \<tau>\<^sub>2) t'"
            by (rule reds_t[OF \<open>beta_reduce t t'\<close>])
          then have "Red_ty \<tau>\<^sub>2 (App t' w)"
            using lc_w red_w by simp
          then show "Red_ty \<tau>\<^sub>2 v"
            by (simp add: v)
        next
          assume "\<exists>u'. v = App t u' \<and> beta_reduce w u'"
          then obtain w' where v: "v = App t w'" and "beta_reduce w w'"
            by blast
          have "locally_closed w'"
            by (rule locally_closed_if_beta_reduce[OF inf_vars \<open>beta_reduce w w'\<close>])
          moreover have "Red_ty \<tau>\<^sub>1 w'"
            by (rule CR2[OF red_w \<open>beta_reduce w w'\<close>])
          moreover have "beta_reduce\<inverse>\<inverse> w' w"
            using \<open>beta_reduce w w'\<close> by (rule conversepI)
          ultimately have "Red_ty \<tau>\<^sub>2 (App t w')"
            using IH_w by blast
          then show "Red_ty \<tau>\<^sub>2 v"
            by (simp add: v)
        qed
      qed
    qed
  qed
  show ?case
    using SN_t red_App by auto
next
  case (2 \<tau> t)
  have "SN t"
  proof (rule SN_I)
    fix y
    assume "beta_reduce t y"
    then have "Red_ty \<tau> y"
      by (rule "2.prems"(3))
    then show "SN y"
      by (rule CR1)
  qed
  then show ?case
    using "2.hyps" by simp
qed
qed

text \<open>In particular, free variables are reducible at every type (they are neutral and normal).\<close>

lemma SN_Free: "SN (Free x)"
  by (rule SN_I) (auto elim: beta_reduce.cases)

text \<open>A free variable is neutral, locally closed, and normal (no \<open>\<beta>\<close>-reduct), so \<open>CR3\<close>
  applies with a vacuous reduct hypothesis.\<close>

lemma Red_Free: "Red_ty \<tau> (Free x)"
proof (rule CR3)
  show "neutral (Free x)"
    by (simp add: neutral_def)
next
  show "locally_closed (Free x)"
    by (rule locally_closed.Free)
next
  show "\<And>t'. beta_reduce (Free x) t' \<Longrightarrow> Red_ty \<tau> t'"
    by (auto elim: beta_reduce.cases)
qed


section \<open>Reducibility of abstractions and constants\<close>

text \<open>Infinitely many variables suffice to choose one name fresh for a finite set of names
  and every term in a finite set.\<close>

lemma fresh_for_fset_and_terms:
  fixes \<T> :: "('\<tau>, '\<Sigma>, '\<V>) preterm fset"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  obtains x where "x |\<notin>| \<X>" and "\<And>t. t |\<in>| \<T> \<Longrightarrow> x \<notin> free_vars t"
proof -
  let ?A = "fset \<X> \<union> (\<Union>t\<in>fset \<T>. free_vars t)"
  have finite_A: "finite ?A"
    by (auto intro: finite_vars_term)
  from ex_new_if_finite[OF inf_vars finite_A]
  obtain x where x_notin: "x \<notin> ?A" ..
  show thesis
  proof (rule that[of x])
    show "x |\<notin>| \<X>"
      using x_notin by simp
  next
    fix t
    assume "t |\<in>| \<T>"
    with x_notin show "x \<notin> free_vars t"
      by auto
  qed
qed


text \<open>A reduction between openings by a fresh free variable can be transported to an opening
  by any locally closed term.\<close>

lemma beta_reduce_subst_bound_from_fresh:
  fixes t t' v :: "(_, _, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes fresh: "x \<notin> free_vars t" "x \<notin> free_vars t'"
  assumes opened_red:
    "beta_reduce (subst_bound n (Free x) t) (subst_bound n (Free x) t')"
  assumes "locally_closed v"
  shows "beta_reduce (subst_bound n v t) (subst_bound n v t')"
proof -
  have "beta_reduce
      (subst_free x v (subst_bound n (Free x) t))
      (subst_free x v (subst_bound n (Free x) t'))"
    by (rule beta_reduce_subst_free[OF inf_vars opened_red assms(5)])
  then show ?thesis
    by (simp add: subst_free_subst_bound_Free_eq_subst_bound fresh)
qed


text \<open>Strong normalization of a free-variable opening is inherited by an abstraction.\<close>

lemma SN_Abs:
  fixes t :: "(_, _, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes "SN (subst_bound 0 (Free x) t)"
  shows "SN (Abs \<tau> t)"
using assms(2)
proof (induction "subst_bound 0 (Free x) t" arbitrary: t rule: accp_induct_rule)
  case 1
  note IH = "1.hyps"(2)
  show ?case
  proof (rule accpI)
    fix v
    assume conv: "beta_reduce\<inverse>\<inverse> v (Abs \<tau> t)"
    then have red: "beta_reduce (Abs \<tau> t) v"
      by simp
    obtain t' \<X> where
      v: "v = Abs \<tau> t'" and
      opened_red: "\<And>y. y |\<notin>| \<X> \<Longrightarrow> beta_reduce (subst_bound 0 (Free y) t)
        (subst_bound 0 (Free y) t')"
      using red by (auto elim!: beta_reduce.cases)
    obtain y where
      y_fresh_\<X>: "y |\<notin>| \<X>" and
      fresh_terms: "\<And>s. s |\<in>| {|t, t'|} \<Longrightarrow> y \<notin> free_vars s"
      using fresh_for_fset_and_terms[OF inf_vars, where \<X> = \<X> and \<T> = "{|t, t'|}"] by blast
    have y_notin_t: "y \<notin> free_vars t"
      by (rule fresh_terms) simp
    have y_notin_t': "y \<notin> free_vars t'"
      by (rule fresh_terms) simp
    have red_x:
      "beta_reduce (subst_bound 0 (Free x) t) (subst_bound 0 (Free x) t')"
      by (rule beta_reduce_subst_bound_from_fresh[
            OF inf_vars y_notin_t y_notin_t'
              opened_red[OF y_fresh_\<X>] locally_closed.Free])
    have conv_x:
      "beta_reduce\<inverse>\<inverse> (subst_bound 0 (Free x) t') (subst_bound 0 (Free x) t)"
      using red_x by (rule conversepI)
    have "SN (Abs \<tau> t')"
      by (rule IH[OF conv_x])
    then show "SN v"
      by (simp add: v)
  qed
qed

text \<open>Inverting a \<open>\<beta>\<close>-step out of a redex \<open>(\<lambda>. t) u\<close>: either the redex is contracted, or the step is
  taken inside the body or the argument.\<close>

lemma beta_reduce_AppD:
  assumes "beta_reduce (App a b) v"
  obtains (redex) \<tau> s where "a = Abs \<tau> s" and "v = subst_bound 0 b s"
    | (left) a' where "v = App a' b" and "beta_reduce a a'"
    | (right) b' where "v = App a b'" and "beta_reduce b b'"
  using assms by (auto elim: beta_reduce.cases)

lemma beta_reduce_App_AbsD:
  assumes "beta_reduce (App (Abs \<tau>\<^sub>1 t) u) v"
  shows "v = subst_bound 0 u t
    \<or> (\<exists>t'. v = App (Abs \<tau>\<^sub>1 t') u \<and> (\<exists>\<X>. \<forall>x. x |\<notin>| \<X> \<longrightarrow> beta_reduce (subst_bound 0 (Free x) t) (subst_bound 0 (Free x) t')))
    \<or> (\<exists>u'. v = App (Abs \<tau>\<^sub>1 t) u' \<and> beta_reduce u u')"
  using assms
proof (cases rule: beta_reduce_AppD)
  case (redex \<tau> s)
  then show ?thesis by auto
next
  case (left a')
  from \<open>beta_reduce (Abs \<tau>\<^sub>1 t) a'\<close> obtain \<X> t'
    where "a' = Abs \<tau>\<^sub>1 t'" and
      "\<And>x. x |\<notin>| \<X> \<Longrightarrow> beta_reduce (subst_bound 0 (Free x) t) (subst_bound 0 (Free x) t')"
    by (auto elim!: beta_reduce.cases)
  then show ?thesis
    using \<open>v = App a' u\<close>
    by blast
next
  case (right b')
  then show ?thesis by blast
qed

text \<open>Core of the abstraction lemma: \<open>(\<lambda>. t) u\<close> is reducible whenever \<open>t\<close> and \<open>u\<close> are strongly
  normalizing, \<open>u\<close> is reducible, and every reducible instance of the body is reducible. Since the
  redex is neutral (an application), we invoke \<open>CR3\<close> and discharge its reducts by a nested
  induction on \<open>SN t\<close> (for reductions in the body) and \<open>SN u\<close> (for reductions in the argument).\<close>

lemma Red_Abs_aux:
  fixes t u :: "(_, _, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes "SN (subst_bound 0 (Free undefined) t)" and "SN u"
    and "body t" and "locally_closed u" and "Red_ty \<tau>\<^sub>1 u"
    and "\<And>v. locally_closed v \<Longrightarrow> Red_ty \<tau>\<^sub>1 v \<Longrightarrow> Red_ty \<tau>\<^sub>2 (subst_bound 0 v t)"
  shows "Red_ty \<tau>\<^sub>2 (App (Abs \<tau>\<^sub>1 t) u)"
  using assms(2-)
proof (induction "subst_bound 0 (Free undefined) t" arbitrary: t u rule: accp_induct_rule)
  case 1
  note outer_IH = "1.hyps"(2)
  note body_t = "1.prems"(2) and hyp_t = "1.prems"(5)
  from "1.prems"(1) show ?case
    using "1.prems"(3,4)
  proof (induction u rule: accp_induct_rule)
    case (1 u)
    note inner_IH = "1.IH"
    note lc_u = "1.prems"(1) and red_u = "1.prems"(2)
    show ?case
    proof (rule CR3)
      show "neutral (App (Abs \<tau>\<^sub>1 t) u)"
        by (simp add: neutral_def)
    next
      show "locally_closed (App (Abs \<tau>\<^sub>1 t) u)"
        using body_t lc_u
        by (simp add: locally_closed_App_iff locall_closed_Abs_iff_body)
    next
      fix w assume "beta_reduce (App (Abs \<tau>\<^sub>1 t) u) w"
      from beta_reduce_App_AbsD[OF this]
      consider (contract) "w = subst_bound 0 u t"
        | (body) t' \<X> where
            "w = App (Abs \<tau>\<^sub>1 t') u" and
            "\<And>x. x |\<notin>| \<X> \<Longrightarrow> beta_reduce (subst_bound 0 (Free x) t) (subst_bound 0 (Free x) t')"
        | (arg) u' where "w = App (Abs \<tau>\<^sub>1 t) u'" and "beta_reduce u u'"
        by blast
      then show "Red_ty \<tau>\<^sub>2 w"
      proof cases
        case contract
        then show ?thesis
          using hyp_t[OF lc_u red_u] by simp
      next
        case (body t')
        have SN_u: "SN u"
          using red_u by (rule CR1)
        have body_t': "body t'"
        proof -
          have abs_red: "beta_reduce (Abs \<tau>\<^sub>1 t) (Abs \<tau>\<^sub>1 t')"
          proof (rule beta_reduce.Abs[where \<X> = \<X>])
            fix x
            assume "x |\<notin>| \<X>"
            then show "beta_reduce (subst_bound 0 (Free x) t)
                (subst_bound 0 (Free x) t')"
              by (rule body(2))
          qed
          have "locally_closed (Abs \<tau>\<^sub>1 t')"
            by (rule locally_closed_if_beta_reduce[OF inf_vars abs_red])
          then show ?thesis
            by (simp add: locall_closed_Abs_iff_body)
        qed
        have opened_red_for:
          "beta_reduce (subst_bound 0 v t) (subst_bound 0 v t')"
          if "locally_closed v" for v
        proof -
          obtain y where y_fresh_\<X>: "y |\<notin>| \<X>"
            and fresh_terms: "\<And>s. s |\<in>| {|t, t'|} \<Longrightarrow> y \<notin> free_vars s"
            using fresh_for_fset_and_terms[OF inf_vars, where \<X> = \<X> and \<T> = "{|t, t'|}"] by blast
          have y_notin_t: "y \<notin> free_vars t"
            by (rule fresh_terms) simp
          have y_notin_t': "y \<notin> free_vars t'"
            by (rule fresh_terms) simp
          show ?thesis
            by (rule beta_reduce_subst_bound_from_fresh[
                  OF inf_vars y_notin_t y_notin_t'
                    body(2)[OF y_fresh_\<X>] that])
        qed
        have hyp_t': "Red_ty \<tau>\<^sub>2 (subst_bound 0 v t')"
          if "locally_closed v" and "Red_ty \<tau>\<^sub>1 v" for v
        proof -
          have "Red_ty \<tau>\<^sub>2 (subst_bound 0 v t)"
            by (rule hyp_t[OF that])
          moreover have "beta_reduce (subst_bound 0 v t) (subst_bound 0 v t')"
            by (rule opened_red_for[OF that(1)])
          ultimately show ?thesis
            by (rule CR2)
        qed
        have conv_open:
          "beta_reduce\<inverse>\<inverse> (subst_bound 0 (Free undefined) t')
            (subst_bound 0 (Free undefined) t)"
          using opened_red_for[OF locally_closed.Free]
          by (rule conversepI)
        have "Red_ty \<tau>\<^sub>2 (App (Abs \<tau>\<^sub>1 t') u)"
          by (rule outer_IH[OF conv_open SN_u body_t' lc_u red_u hyp_t'])
        then show ?thesis
          by (simp add: \<open>w = App (Abs \<tau>\<^sub>1 t') u\<close>)
      next
        case (arg u')
        have "locally_closed u'"
          by (rule locally_closed_if_beta_reduce[OF inf_vars \<open>beta_reduce u u'\<close>])
        moreover have "Red_ty \<tau>\<^sub>1 u'"
          using red_u \<open>beta_reduce u u'\<close> by (rule CR2)
        moreover have "beta_reduce\<inverse>\<inverse> u' u"
          using \<open>beta_reduce u u'\<close> by (rule conversepI)
        ultimately have "Red_ty \<tau>\<^sub>2 (App (Abs \<tau>\<^sub>1 t) u')"
          using inner_IH by blast
        then show ?thesis
          by (simp add: \<open>w = App (Abs \<tau>\<^sub>1 t) u'\<close>)
      qed
    qed
  qed
qed

lemma Red_Abs:
  fixes t :: "(_, _, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes "locally_closed (Abs \<tau>\<^sub>1 t)"
  assumes hyp: "\<And>u. locally_closed u \<Longrightarrow> Red_ty \<tau>\<^sub>1 u \<Longrightarrow> Red_ty \<tau>\<^sub>2 (subst_bound 0 u t)"
  shows "Red_ty (TyFun \<tau>\<^sub>1 \<tau>\<^sub>2) (Abs \<tau>\<^sub>1 t)"
proof -
  have body_t: "body t"
    using assms(2) by (simp add: locall_closed_Abs_iff_body)
  have SN_open: "SN (subst_bound 0 (Free undefined) t)"
    by (rule CR1[OF hyp[OF locally_closed.Free Red_Free]])
  have "SN (Abs \<tau>\<^sub>1 t)"
    using SN_open by (rule SN_Abs[OF inf_vars])
  moreover have "Red_ty \<tau>\<^sub>2 (App (Abs \<tau>\<^sub>1 t) u)"
    if "locally_closed u" and "Red_ty \<tau>\<^sub>1 u" for u
  proof (rule Red_Abs_aux[OF inf_vars])
    show "SN (subst_bound 0 (Free undefined) t)" by (rule SN_open)
    show "SN u" using that(2) by (rule CR1)
    show "body t" by (rule body_t)
    show "locally_closed u" by (rule that(1))
    show "Red_ty \<tau>\<^sub>1 u" by (rule that(2))
    show "\<And>v. locally_closed v \<Longrightarrow> Red_ty \<tau>\<^sub>1 v \<Longrightarrow> Red_ty \<tau>\<^sub>2 (subst_bound 0 v t)"
      by (rule hyp)
  qed
  ultimately show ?thesis
    by simp
qed

text \<open>Inverting a \<open>\<beta>\<close>-step out of a constant: exactly one parameter is reduced.\<close>

lemma beta_reduce_ConstD:
  assumes "beta_reduce (Const c \<tau>s ts) v"
  obtains i t' where "i < length ts" and "beta_reduce (ts ! i) t'"
    and "v = Const c \<tau>s (ts[i := t'])"
  using assms by (auto elim: beta_reduce.cases)

text \<open>A constant is strongly normalizing once all its parameters are (converse of \<open>SN_ConstD\<close>). The
  key \<open>cons\<close> step is a double induction: on the head (reductions in it) and on the constant built
  from the tail (reductions in the remaining parameters).\<close>

lemma SN_Const_cons:
  assumes "SN a" and "SN (Const c \<tau>s bs)"
  shows "SN (Const c \<tau>s (a # bs))"
  using assms
proof (induction a arbitrary: bs rule: accp_induct_rule)
  case (1 a)
  note IH_a = "1.IH"
  from "1.prems" show ?case
  proof (induction "Const c \<tau>s bs" arbitrary: bs rule: accp_induct_rule)
    case 1
    note SN_bs = "1.hyps"(1) and IH_bs = "1.hyps"(2)
    show ?case
    proof (rule accpI)
      fix v assume "beta_reduce\<inverse>\<inverse> v (Const c \<tau>s (a # bs))"
      then have "beta_reduce (Const c \<tau>s (a # bs)) v"
        by simp
      then obtain i t' where "i < length (a # bs)" and "beta_reduce ((a # bs) ! i) t'"
        and v_eq: "v = Const c \<tau>s ((a # bs)[i := t'])"
        by (elim beta_reduce_ConstD)
      then show "SN v"
      proof (cases i)
        case 0
        then have "beta_reduce a t'" and "v = Const c \<tau>s (t' # bs)"
          using \<open>beta_reduce ((a # bs) ! i) t'\<close> v_eq by simp_all
        have "beta_reduce\<inverse>\<inverse> t' a"
          using \<open>beta_reduce a t'\<close> by (rule conversepI)
        then have "SN (Const c \<tau>s (t' # bs))"
          by (rule IH_a[OF _ SN_bs])
        then show ?thesis
          using \<open>v = Const c \<tau>s (t' # bs)\<close> by simp
      next
        case (Suc j)
        have tail_red:
          "beta_reduce (Const c \<tau>s bs) (Const c \<tau>s (bs[j := t']))"
        proof (rule beta_reduce.Const)
          show "\<forall>t\<in>set bs. locally_closed t"
            using \<open>beta_reduce (Const c \<tau>s (a # bs)) v\<close> beta_reduce.cases by force
        next
          show "j < length bs" and "beta_reduce (bs ! j) t'"
            using Suc \<open>i < length (a # bs)\<close>
              \<open>beta_reduce ((a # bs) ! i) t'\<close> by simp_all
        qed
        have "beta_reduce\<inverse>\<inverse> (Const c \<tau>s (bs[j := t'])) (Const c \<tau>s bs)"
          using tail_red by (rule conversepI)
        then have "SN (Const c \<tau>s (a # bs[j := t']))"
          by (rule IH_bs)
        moreover have "v = Const c \<tau>s (a # bs[j := t'])"
          using Suc v_eq by simp
        ultimately show ?thesis
          by simp
      qed
    qed
  qed
qed

lemma SN_Const:
  "(\<And>t. t \<in> set ts \<Longrightarrow> SN t) \<Longrightarrow> SN (Const c \<tau>s ts)"
proof (induction ts)
  case Nil
  show ?case
    by (rule SN_I) (auto elim: beta_reduce.cases)
next
  case (Cons a bs)
  show ?case
  proof (rule SN_Const_cons)
    show "SN a"
      using Cons.prems by fastforce
    show "SN (Const c \<tau>s bs)"
    proof (rule Cons.IH)
      fix t assume "t \<in> set bs"
      then show "SN t"
        using Cons.prems by fastforce
    qed
  qed
qed

text \<open>Core of the constant lemma: a strongly normalizing, locally closed constant is reducible at any
  type. Since \<open>Const\<close> is neutral we invoke \<^text>\<open>CR3\<close>; each reduct reduces one parameter, so it is again
  a constant that is strongly normalizing and locally closed, hence reducible by the induction hypothesis.\<close>

lemma Red_Const_aux:
  fixes ts :: "(_, _, '\<V>) preterm list"
  assumes "SN (Const c \<tau>s ts)" and "locally_closed (Const c \<tau>s ts)"
  shows "Red_ty \<tau> (Const c \<tau>s ts)"
proof (cases "infinite (UNIV :: '\<V> set)")
  case inf_vars: True
  show ?thesis
    using assms
  proof (induction "Const c \<tau>s ts" arbitrary: ts rule: accp_induct_rule)
    case 1
    note IH = "1.hyps"(2)
    show ?case
    proof (rule CR3)
      show "neutral (Const c \<tau>s ts)"
        by (simp add: neutral_def)
    next
      show "locally_closed (Const c \<tau>s ts)"
        using "1.prems" .
    next
      fix v assume bv: "beta_reduce (Const c \<tau>s ts) v"
      then obtain i t' where "i < length ts" and "beta_reduce (ts ! i) t'"
        and v_eq: "v = Const c \<tau>s (ts[i := t'])"
        by (elim beta_reduce_ConstD)
      have "locally_closed v"
        by (rule locally_closed_if_beta_reduce[OF inf_vars bv])
      moreover have "beta_reduce\<inverse>\<inverse> v (Const c \<tau>s ts)"
        using bv by (rule conversepI)
      ultimately show "Red_ty \<tau> v"
        unfolding v_eq using IH by blast
    qed
  qed
next
  case False
  then have fin_vars: "finite (UNIV :: '\<V> set)"
    by simp
  have "beta_normal (Const c \<tau>s ts)"
    by (rule beta_normal_if_SN_if_finite_vars[OF fin_vars assms(2,1)])
  then show ?thesis
    by (rule Red_ty_if_beta_normal_if_finite_vars[OF fin_vars])
qed

lemma Red_Const:
  fixes ts :: "(_, _, '\<V>) preterm list"
  assumes "locally_closed (Const c \<tau>s ts)"
  assumes "\<forall>t \<in> set ts. SN t"
  shows "Red_ty \<tau> (Const c \<tau>s ts)"
proof (rule Red_Const_aux)
  show "SN (Const c \<tau>s ts)"
    using assms by (auto intro: SN_Const)
next
  show "locally_closed (Const c \<tau>s ts)"
    by (rule assms)
qed


section \<open>Parallel substitution of free variables\<close>

text \<open>Simultaneous substitution of the free (named) variables. Contrary to \<^const>\<open>subst_bound\<close>,
  this descends into the parameters of a constant, which may contain free variables.\<close>

fun msubst ::
  "('\<V> \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm) \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm" where
  "msubst \<theta> (Const c \<tau>s ts) = Const c \<tau>s (map (msubst \<theta>) ts)" |
  "msubst \<theta> (Free x) = \<theta> x" |
  "msubst \<theta> (Bound n) = Bound n" |
  "msubst \<theta> (App t\<^sub>1 t\<^sub>2) = App (msubst \<theta> t\<^sub>1) (msubst \<theta> t\<^sub>2)" |
  "msubst \<theta> (Abs \<tau> t) = Abs \<tau> (msubst \<theta> t)"

lemma msubst_Free: "msubst Free t = t"
  by (induction t) (simp_all add: map_idI)

lemma msubst_cong:
  "(\<And>z. z \<in> free_vars t \<Longrightarrow> \<theta> z = \<theta>' z) \<Longrightarrow> msubst \<theta> t = msubst \<theta>' t"
  by (induction t) (auto cong: map_cong)

text \<open>Opening a fresh variable and then substituting it equals substituting into the opened body
  (the key commutation lemma for the abstraction case of the fundamental theorem).\<close>

lemma msubst_subst_bound_Free:
  fixes t :: "(_, _, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes "x \<notin> free_vars t"
  assumes "\<And>y. locally_closed (\<theta> y)"
  shows "msubst (\<theta>(x := u)) (subst_bound n (Free x) t) = subst_bound n u (msubst \<theta> t)"
  using assms(2,3)
  by (induction t arbitrary: n)
    (auto intro!: msubst_cong cong: map_cong
      simp: subst_bound_ident_if_locally_closed[OF inf_vars])

text \<open>Parallel substitution of free variables preserves local closure.\<close>

lemma locally_closed_msubst:
  fixes t :: "(_, _, '\<V>) preterm"
  assumes lc_\<theta>: "\<And>y. locally_closed (\<theta> y)"
  assumes lc_t: "locally_closed t"
  shows "locally_closed (msubst \<theta> t)"
proof (cases "infinite (UNIV :: '\<V> set)")
  case True
  show ?thesis
    using lc_t lc_\<theta>
  proof (induction arbitrary: \<theta> rule: locally_closed.induct)
    case (Const c \<tau>s ts)
    show ?case
      unfolding msubst.simps
    proof (rule locally_closed.Const)
      show "list_all locally_closed (map (msubst \<theta>) ts)"
        using Const.IH Const.prems
        by (auto simp: list.pred_set)
    qed
  next
    case (Free x)
    then show ?case
      by simp
  next
    case (App t u)
    then show ?case
      by (auto intro: locally_closed.App)
  next
    case (Abs \<X> t \<tau>)
    show ?case
      unfolding msubst.simps
    proof (rule locally_closed.Abs[
          where \<X> = "free_vars_fset t |\<union>| \<X>"])
      fix x
      assume fresh: "x |\<notin>| free_vars_fset t |\<union>| \<X>"
      have fresh_\<X>: "x |\<notin>| \<X>"
        using fresh by simp
      have x_notin_t: "x \<notin> free_vars t"
        using fresh by (simp add: free_vars_fset_rep_eq)
      have lc_update: "\<And>y. locally_closed ((\<theta>(x := Free x)) y)"
      proof -
        fix y
        show "locally_closed ((\<theta>(x := Free x)) y)"
        proof (cases "y = x")
          case True
          then show ?thesis
            by (simp add: locally_closed.Free)
        next
          case False
          then show ?thesis
            using Abs.prems by simp
        qed
      qed
      have "locally_closed
          (msubst (\<theta>(x := Free x)) (subst_bound 0 (Free x) t))"
        by (rule Abs.IH[OF fresh_\<X> lc_update])
      then show "locally_closed (subst_bound 0 (Free x) (msubst \<theta> t))"
        by (simp add: msubst_subst_bound_Free[
              OF True x_notin_t Abs.prems])
    qed
  qed
next
  case False
  have finite_vars: "finite (UNIV :: '\<V> set)"
    using False by simp
  let ?\<X> = "the_inv fset (UNIV :: '\<V> set)"
  have fset_\<X>: "fset ?\<X> = UNIV"
    by (rule fset_to_fset[OF finite_vars])
  show ?thesis
    using lc_t
  proof (induction t)
    case (Const c \<tau>s ts)
    then show ?case
      by (auto intro: locally_closed.Const simp: list.pred_set)
  next
    case (Free x)
    then show ?case
      using lc_\<theta>[of x] by simp
  next
    case (App t u)
    then show ?case
      by (auto intro: locally_closed.App)
  next
    case (Abs \<Y> t \<tau>)
    show ?case
      unfolding msubst.simps
    proof (rule locally_closed.Abs[where \<X> = ?\<X>])
      fix x
      assume "x |\<notin>| ?\<X>"
      then show "locally_closed (subst_bound 0 (Free x) (msubst \<theta> t))"
        by (simp add: fset_\<X>)
    qed
  qed
qed



section \<open>Fundamental theorem and strong normalization\<close>

text \<open>Every well-typed term is reducible under any reducible, locally closed substitution of its
  free variables.\<close>

lemma fundamental:
  fixes t :: "(('vty, 'sty :: type_signature) ty, 'c, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes "has_type \<C> \<F> t \<tau>"
  assumes "\<And>x. locally_closed (\<theta> x)"
  assumes "\<And>x. Red_ty (\<F> x) (\<theta> x)"
  shows "Red_ty \<tau> (msubst \<theta> t)"
  using assms(2-4)
proof (induction arbitrary: \<theta> rule: has_type.induct)
  case (Const \<F> c \<tau>\<^sub>1s ts \<tau> \<alpha>s \<tau>\<^sub>2s \<tau>\<^sub>3 \<sigma>)
  have lc_args: "\<forall>s \<in> set ts. locally_closed (msubst \<theta> s)"
    using Const.IH
    by (induction rule: list_all2_induct)
       (auto intro: locally_closed_msubst Const.prems(1))
  have sn_args: "\<forall>s \<in> set ts. SN (msubst \<theta> s)"
    using Const.IH Const.prems
    by (induction rule: list_all2_induct) (auto, metis CR1)
  show ?case
    unfolding msubst.simps
  proof (rule Red_Const)
    show "locally_closed (Const c \<tau>\<^sub>1s (map (msubst \<theta>) ts))"
      using lc_args by simp
  next
    show "\<forall>s\<in>set (map (msubst \<theta>) ts). SN s"
      using sn_args by simp
  qed
next
  case (Free \<F> f \<tau>)
  then show ?case
    using Free.prems(2)[of f] by simp
next
  case (App \<F> t\<^sub>1 t\<^sub>2 \<tau>\<^sub>1 \<tau>\<^sub>2)
  have red_t\<^sub>1: "Red_ty (TyFun \<tau>\<^sub>1 \<tau>\<^sub>2) (msubst \<theta> t\<^sub>1)"
    by (rule App.IH(1)[OF App.prems])
  have red_t\<^sub>2: "Red_ty \<tau>\<^sub>1 (msubst \<theta> t\<^sub>2)"
    by (rule App.IH(2)[OF App.prems])
  have lc_t\<^sub>2: "locally_closed (msubst \<theta> t\<^sub>2)"
  proof (rule locally_closed_msubst)
    show "\<And>x. locally_closed (\<theta> x)"
      by (rule App.prems)
    show "locally_closed t\<^sub>2"
      by (rule locally_closed_if_has_type[OF App.hyps(2)])
  qed
  show ?case
    using red_t\<^sub>1 lc_t\<^sub>2 red_t\<^sub>2 by simp
next
  case (Abs \<F> t \<tau>\<^sub>1 \<tau>\<^sub>2 \<X>)
  have lc_abs: "locally_closed (Abs \<tau>\<^sub>1 t)"
  proof (rule locally_closed_if_has_type)
    show "has_type \<C> \<F> (Abs \<tau>\<^sub>1 t) (TyFun \<tau>\<^sub>1 \<tau>\<^sub>2)"
      by (rule has_type.Abs[where \<X> = \<X>]) (rule Abs.hyps)
  qed
  show ?case
    unfolding msubst.simps
  proof (rule Red_Abs[OF inf_vars])
    show "locally_closed (Abs \<tau>\<^sub>1 (msubst \<theta> t))"
      using locally_closed_msubst[OF Abs.prems(1) lc_abs] by simp
  next
    fix u :: "(('vty, 'sty) ty, 'c, '\<V>) preterm"
    assume lc_u: "locally_closed u" and red_u: "Red_ty \<tau>\<^sub>1 u"
    obtain x where fresh_x: "x |\<notin>| \<X>" and x_notin_t: "x \<notin> free_vars t"
      using fresh_for_fset_and_terms[OF inf_vars, where \<X> = \<X> and \<T> = "{|t|}"] by auto
    have red_open:
      "Red_ty \<tau>\<^sub>2 (msubst (\<theta>(x := u)) (subst_bound 0 (Free x) t))"
    proof (rule Abs.IH[OF fresh_x])
      show "\<And>y. locally_closed ((\<theta>(x := u)) y)"
        using Abs.prems(1) lc_u by simp
      show "\<And>y. Red_ty ((\<F>(x := \<tau>\<^sub>1)) y) ((\<theta>(x := u)) y)"
        using Abs.prems(2) red_u by simp
    qed
    show "Red_ty \<tau>\<^sub>2 (subst_bound 0 u (msubst \<theta> t))"
      using red_open
      by (simp add: msubst_subst_bound_Free[OF inf_vars x_notin_t Abs.prems(1)])
  qed
qed

lemma SN_if_has_type:
  fixes t :: "(_, _, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes ht: "has_type \<C> \<F> t \<tau>"
  shows "SN t"
proof -
  have red: "Red_ty \<tau> (msubst Free t)"
  proof (rule fundamental[OF inf_vars ht])
    show "\<And>x. locally_closed (Free x)"
      by (rule locally_closed.Free)
  next
    show "\<And>x. Red_ty (\<F> x) (Free x)"
      by (rule Red_Free)
  qed
  show "SN t"
    using CR1[OF red, unfolded msubst_Free] .
qed

proposition strong_normalization_of_typed_terms:
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  shows "wfp_on {t :: (_, _, '\<V>) preterm. \<exists>\<C> \<F> \<tau>. has_type \<C> \<F> t \<tau>} beta_reduce\<inverse>\<inverse>"
  by (rule wfp_on_beta_reduce_if_SN) (auto intro: SN_if_has_type[OF inf_vars])

text \<open>The assumption of infinitely many variables is not an artifact of the proof: over a finite
  variable type the cofinite premise of the \<open>Abs\<close> rule of \<^const>\<open>has_type\<close> is vacuously true, so
  every abstraction is well typed---including abstractions that reduce to themselves and are
  therefore not strongly normalizing. Hence \<open>SN_if_has_type\<close> and
  \<open>strong_normalization_of_typed_terms\<close> would be false without the assumption, and likewise for
  \<open>Red_Abs\<close>, \<open>Red_Abs_aux\<close>, \<open>SN_Abs\<close>, and \<open>fundamental\<close>, whose conclusions all require some
  abstraction to be strongly normalizing (or reducible, which implies strong normalization).\<close>

lemma ex_has_type_and_not_SN_if_finite_vars:
  assumes fin_vars: "finite (UNIV :: '\<V> set)"
  shows "\<exists>t :: (('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: type_signature) ty, '\<Sigma>, '\<V>) preterm.
    (\<exists>\<C> \<F> \<tau>. has_type \<C> \<F> t \<tau>) \<and> \<not> SN t"
proof -
  obtain \<X> :: "'\<V> fset" where "\<forall>x. x |\<in>| \<X>"
    using ex_fset_UNIV[OF fin_vars] by blast
  then have "has_type \<C> \<F> (Abs \<bool> (Bound 0)) (TyFun \<bool> \<bool>)"
    for \<C> :: "'\<Sigma> \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) const_ty" and \<F> :: "'\<V> \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) ty"
    by (auto intro: has_type.Abs[where \<X> = \<X>])
  moreover have "\<not> SN (Abs \<bool> (Bound 0) :: (('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) ty, '\<Sigma>, '\<V>) preterm)"
    by (rule not_SN_if_beta_reduce_self[OF beta_reduce_Abs_Abs_if_finite_vars[OF fin_vars]])
  ultimately show ?thesis
    by blast
qed

end