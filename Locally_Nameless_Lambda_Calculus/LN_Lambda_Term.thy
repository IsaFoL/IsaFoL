theory LN_Lambda_Term
  imports
    Main
    "HOL-Library.Uprod"
    "HOL-Library.Multiset"
    "HOL-Library.FSet"
    "HOL-ex.Sketch_and_Explore"
begin

declare foldl_inject[simp]

datatype (type_symbols: '\<tau>, const_symbols: '\<Sigma>, free_vars: '\<V>) preterm =
  is_Const: Const '\<Sigma> "'\<tau> list" "('\<tau>, '\<Sigma>, '\<V>) preterm list" |
  is_Free: Free '\<V> |
  is_Bound: Bound nat '\<tau> |
  is_App: App "('\<tau>, '\<Sigma>, '\<V>) preterm" "('\<tau>, '\<Sigma>, '\<V>) preterm" |
  is_Abs: Abs "'\<tau>" "('\<tau>, '\<Sigma>, '\<V>) preterm"

lemma finite_vars_term: "finite (free_vars t)"
  using preterm.set_finite(3) .


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

declare fset_of_list.rep_eq[termination_simp]

fun free_vars_fset :: "('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> '\<V> fset" where
  "free_vars_fset (Const _ _ ts) = ffUnion (free_vars_fset |`| fset_of_list ts)" |
  "free_vars_fset (Free x) = {|x|}" |
  "free_vars_fset (Bound _ _) = {||}" |
  "free_vars_fset (App t\<^sub>1 t\<^sub>2) = free_vars_fset t\<^sub>1 |\<union>| free_vars_fset t\<^sub>2" |
  "free_vars_fset (Abs _ t) = free_vars_fset t"

lemma free_vars_fset_rep_eq: "fset (free_vars_fset t) = free_vars t"
  by (induction t) (simp_all add: ffUnion.rep_eq fimage.rep_eq fset_of_list.rep_eq)


primrec open_bound ::
  "nat \<Rightarrow> '\<tau> \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm" where
  "open_bound n \<tau> u (Const c \<tau>s ts) = Const c \<tau>s ts" |
  "open_bound n \<tau> u (Free f) = Free f" |
  "open_bound n \<tau> u (Bound k \<sigma>) = (if k = n \<and> \<sigma> = \<tau> then u else Bound k \<sigma>)" |
  "open_bound n \<tau> u (App t\<^sub>1 t\<^sub>2) = App (open_bound n \<tau> u t\<^sub>1) (open_bound n \<tau> u t\<^sub>2)" |
  "open_bound n \<tau> u (Abs \<sigma> t) = Abs \<sigma> (open_bound (Suc n) \<tau> u t)"

lemma free_vars_open_bound_subset:
  "free_vars (open_bound n \<tau> u t) \<subseteq> free_vars t \<union> free_vars u"
  by (induction t arbitrary: n) auto

inductive locally_closed :: "('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> bool" where
  Const: "locally_closed (Const c \<tau>s ts)"
    if "list_all locally_closed ts" for c \<tau>s ts |
  Free: "locally_closed (Free f)" |
  App: "locally_closed (App t\<^sub>1 t\<^sub>2)"
    if "locally_closed t\<^sub>1" and "locally_closed t\<^sub>2" |
  Abs: "locally_closed (Abs \<tau> t)"
    if "\<And>x. x |\<notin>| \<X> \<Longrightarrow> locally_closed (open_bound 0 \<tau> (Free x) t)"

definition body where
  "body \<tau> t \<longleftrightarrow> (\<exists>\<X>. \<forall>x. x |\<notin>| \<X> \<longrightarrow> locally_closed (open_bound 0 \<tau> (Free x) t))"

text \<open>A structural, level-indexed notion of local closure: \<open>locally_closed_at k t\<close> holds when every
  dangling bound index of \<open>t\<close> is smaller than \<open>k\<close>. Constant parameters are required to be
  closed (level \<open>0\<close>), matching the fact that opening and free substitution treat them
  opaquely (they never descend into them); with the naive rule \<open>list_all (locally_closed_at k) ts\<close>
  the equivalence with \<^const>\<open>locally_closed\<close> below would fail.\<close>

inductive locally_closed_at :: "nat \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> bool" where
  Bound: "locally_closed_at k (Bound i \<tau>)" if "i < k" |
  Const: "locally_closed_at k (Const c \<tau>s ts)" if "list_all (locally_closed_at 0) ts" for k c \<tau>s ts |
  Free: "locally_closed_at k (Free f)" |
  App: "locally_closed_at k (App t\<^sub>1 t\<^sub>2)" if "locally_closed_at k t\<^sub>1" and "locally_closed_at k t\<^sub>2" |
  Abs: "locally_closed_at k (Abs \<tau> t)" if "locally_closed_at (Suc k) t"

lemma locally_closed_at_Bound_iff[simp]: "locally_closed_at k (Bound i \<tau>) \<longleftrightarrow> i < k"
  by (auto elim: locally_closed_at.cases intro: locally_closed_at.Bound)

lemma locally_closed_at_Free[simp]: "locally_closed_at k (Free f)"
  by (rule locally_closed_at.Free)

lemma locally_closed_App_iff: "locally_closed (App t\<^sub>1 t\<^sub>2) \<longleftrightarrow> locally_closed t\<^sub>1 \<and> locally_closed t\<^sub>2"
  by (auto elim: locally_closed.cases intro: locally_closed.App)

lemma locally_closed_at_App_iff[simp]:
  "locally_closed_at k (App t\<^sub>1 t\<^sub>2) \<longleftrightarrow> locally_closed_at k t\<^sub>1 \<and> locally_closed_at k t\<^sub>2"
  by (auto elim: locally_closed_at.cases intro: locally_closed_at.App)

lemma locally_closed_Const_iff[simp]:
  "locally_closed (Const \<kappa> \<tau>s ts) \<longleftrightarrow> (\<forall>t \<in> set ts. locally_closed t)"
  by (metis list.pred_set locally_closed.simps preterm.distinct(1,5) preterm.inject(1)
      preterm.simps(13))

lemma locall_closed_Abs_iff_body: "locally_closed (Abs \<tau> t) \<longleftrightarrow> body \<tau> t"
  unfolding locally_closed.simps[of "Abs _ _", simplified] body_def ..

lemma body_App_iff: "body \<tau> (App t\<^sub>1 t\<^sub>2) \<longleftrightarrow> body \<tau> t\<^sub>1 \<and> body \<tau> t\<^sub>2"
  unfolding body_def by (auto simp add: locally_closed_App_iff)

lemma locally_closed_at_Abs_iff[simp]:
  "locally_closed_at k (Abs \<tau> t) \<longleftrightarrow> locally_closed_at (Suc k) t"
  by (auto elim: locally_closed_at.cases intro: locally_closed_at.Abs)

lemma locally_closed_at_Const_iff[simp]:
  "locally_closed_at k (Const c \<tau>s ts) \<longleftrightarrow> (\<forall>t \<in> set ts. locally_closed_at 0 t)"
  by (auto elim: locally_closed_at.cases intro: locally_closed_at.Const simp: list.pred_set)

lemma locally_closed_at_Suc_if_open_bound_Free:
  "locally_closed_at k (open_bound k \<tau> (Free x) t) \<Longrightarrow> locally_closed_at (Suc k) t"
  by (induction t arbitrary: k) (auto split: if_splits)


lemma locally_closed_at_mono:
  assumes "locally_closed_at k t" and "k \<le> l"
  shows "locally_closed_at l t"
  using assms
  by (induction arbitrary: l rule: locally_closed_at.induct) (auto simp: list.pred_set)

primrec subst_free
  :: "'\<V> \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm" where
  "subst_free x u (Const c \<tau>s ts) = Const c \<tau>s ts"|
  "subst_free x u (Free y) = (if x = y then u else Free y)" |
  "subst_free x u (Bound k \<tau>) = Bound k \<tau>" |
  "subst_free x u (App t\<^sub>1 t\<^sub>2) = App (subst_free x u t\<^sub>1) (subst_free x u t\<^sub>2)" |
  "subst_free x u (Abs \<tau> t) = Abs \<tau> (subst_free x u t)"

lemma size_open_bound_Free[simp]: "size (open_bound n \<tau> (Free x) t) = size t"
  by (induction t arbitrary: n) simp_all

text \<open>Over a finite variable type, a cofinite binder premise may be vacuous.\<close>

lemma ex_fset_UNIV:
  assumes fin_vars: "finite (UNIV :: '\<V> set)"
  shows "\<exists>\<X> :: '\<V> fset. \<forall>x. x |\<in>| \<X>"
  by (metis fin_vars finite_list fset_of_list_elem UNIV_I)

lemma locally_closed_Abs_if_finite_vars:
  fixes t :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes fin_vars: "finite (UNIV :: '\<V> set)"
  shows "locally_closed (Abs \<tau> t)"
proof -
  obtain \<X> :: "'\<V> fset" where "\<forall>x. x |\<in>| \<X>"
    using ex_fset_UNIV[OF fin_vars] by blast
  then show ?thesis
    by (auto intro: locally_closed.Abs[where \<X> = \<X>])
qed

lemma body_if_finite_vars:
  fixes t :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes fin_vars: "finite (UNIV :: '\<V> set)"
  shows "body \<tau> t"
  unfolding body_def
  using ex_fset_UNIV[OF fin_vars] by blast


lemma locally_closed_open_bound_if_finite_vars:
  fixes t u :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes fin_vars: "finite (UNIV :: '\<V> set)"
    and lc: "locally_closed t"
  shows "locally_closed (open_bound n \<tau> u t)"
  using lc
  by (induction arbitrary: n rule: locally_closed.induct)
    (auto intro: locally_closed.intros
      simp: list.pred_set locally_closed_Abs_if_finite_vars[OF fin_vars])

lemma locally_closed_imp_locally_closed_at:
  fixes t :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
    and lc: "locally_closed t"
  shows "locally_closed_at 0 t"
  using lc
proof (induction rule: locally_closed.induct)
  case (Const c \<tau>s ts)
  then show ?case
    by (auto intro: locally_closed_at.Const simp: list.pred_set)
next
  case Free
  then show ?case by simp
next
  case App
  then show ?case by simp
next
  case (Abs \<X> \<tau> t)
  obtain x :: '\<V> where fresh: "x |\<notin>| \<X>"
    using inf_vars by (metis ex_new_if_finite finite_fset)
  have "locally_closed_at 0 (open_bound 0 \<tau> (Free x) t)"
    by (rule Abs.IH[OF fresh])
  then have "locally_closed_at (Suc 0) t"
    by (rule locally_closed_at_Suc_if_open_bound_Free)
  then show ?case by simp
qed

lemma open_bound_ident_if_locally_closed_at:
  assumes lc: "locally_closed_at k t" and "k \<le> n"
  shows "open_bound n \<tau> u t = t"
  using lc \<open>k \<le> n\<close>
  by (induction arbitrary: n rule: locally_closed_at.induct)
    (auto simp: list.pred_set)

lemma open_bound_ident_if_locally_closed:
  fixes t :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)" and lc: "locally_closed t"
  shows "open_bound n \<tau> u t = t"
  by (rule open_bound_ident_if_locally_closed_at[
        OF locally_closed_imp_locally_closed_at[OF inf_vars lc]]) simp

lemma subst_free_ident_if_not_in_vars[simp]:
  "x \<notin> free_vars t \<Longrightarrow> subst_free x u t = t"
  by (induction t) simp_all

lemma subst_open:
  fixes t :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
    and lc_u: "locally_closed u"
  shows "subst_free x u (open_bound k \<tau> v t) =
    open_bound k \<tau> (subst_free x u v) (subst_free x u t)"
  by (induction t arbitrary: k)
    (simp_all add: open_bound_ident_if_locally_closed[OF inf_vars lc_u])

lemma subst_free_commutes_with_open_bound_Free:
  fixes t :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
    and "x \<noteq> y" and "locally_closed u"
  shows "subst_free x u (open_bound n \<tau> (Free y) t) =
    open_bound n \<tau> (Free y) (subst_free x u t)"
  using subst_open[OF inf_vars \<open>locally_closed u\<close>, of x n \<tau> "Free y" t]
    \<open>x \<noteq> y\<close> by simp

lemma subst_free_open_bound_Free_eq_open_bound:
  assumes "x \<notin> free_vars t"
  shows "subst_free x u (open_bound n \<tau> (Free x) t) = open_bound n \<tau> u t"
  using assms by (induction t arbitrary: n) auto

lemma locally_closed_subst_free:
  fixes t u :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes lc_t: "locally_closed t" and lc_u: "locally_closed u"
  shows "locally_closed (subst_free x u t)"
proof (cases "infinite (UNIV :: '\<V> set)")
  case inf_vars: True
  show ?thesis
    using lc_t
  proof (induction t rule: locally_closed.induct)
    case (Const c \<tau>s ts)
    then show ?case
      by (auto intro: locally_closed.Const simp: list.pred_set)
  next
    case Free
    then show ?case
      using lc_u by (simp add: locally_closed.Free)
  next
    case App
    then show ?case
      by (simp add: locally_closed.App)
  next
    case (Abs \<X> \<tau> t)
    show ?case
      unfolding subst_free.simps
    proof (rule locally_closed.Abs[where \<X> = "finsert x \<X>"])
      fix y
      assume fresh: "y |\<notin>| finsert x \<X>"
      then have "x \<noteq> y" and "y |\<notin>| \<X>" by auto
      show "locally_closed (open_bound 0 \<tau> (Free y) (subst_free x u t))"
        using Abs.IH[OF \<open>y |\<notin>| \<X>\<close>]
        by (simp add: subst_free_commutes_with_open_bound_Free[
              OF inf_vars \<open>x \<noteq> y\<close> lc_u, symmetric])
    qed
  qed
next
  case False
  then have fin_vars: "finite (UNIV :: '\<V> set)" by simp
  show ?thesis
    using lc_t
    by (induction t rule: preterm.induct)
      (auto elim: locally_closed.cases intro: locally_closed.intros
        simp: list.pred_set locally_closed_Abs_if_finite_vars[OF fin_vars] lc_u)
qed

lemma body_subst_free:
  fixes t u :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes body: "body \<tau> t" and lc_u: "locally_closed u"
  shows "body \<tau> (subst_free x u t)"
proof -
  have "locally_closed (subst_free x u (Abs \<tau> t))"
    by (rule locally_closed_subst_free)
      (use body lc_u in \<open>simp_all add: locall_closed_Abs_iff_body\<close>)
  then show ?thesis
    by (simp add: locall_closed_Abs_iff_body)
qed

lemma locally_closed_open_bound:
  fixes t u :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
    and body: "body \<tau> t" and lc_u: "locally_closed u"
  shows "locally_closed (open_bound 0 \<tau> u t)"
proof -
  obtain \<X> :: "'\<V> fset" where opened:
      "\<And>x. x |\<notin>| \<X> \<Longrightarrow> locally_closed (open_bound 0 \<tau> (Free x) t)"
    using body unfolding body_def by blast
  obtain x :: '\<V> where fresh_\<X>: "x |\<notin>| \<X>" and fresh_t: "x \<notin> free_vars t"
    using fresh_for_fset_and_terms[OF inf_vars, where \<X> = \<X> and \<T> = "{|t|}"]
    by blast
  have "locally_closed (subst_free x u (open_bound 0 \<tau> (Free x) t))"
    by (rule locally_closed_subst_free[OF opened[OF fresh_\<X>] lc_u])
  then show ?thesis
    by (simp add: subst_free_open_bound_Free_eq_open_bound[OF fresh_t])
qed

lemma body_Abs_if_body:
  fixes t :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes body: "body \<tau> t"
  shows "body \<sigma> (Abs \<tau> t)"
proof (cases "infinite (UNIV :: '\<V> set)")
  case True
  have lc: "locally_closed (Abs \<tau> t)"
    using body by (simp add: locall_closed_Abs_iff_body)
  show ?thesis
    unfolding body_def
    using open_bound_ident_if_locally_closed[OF True lc]
    by (intro exI[of _ "{||}"]) (simp add: lc)
next
  case False
  then show ?thesis
    by (simp add: body_if_finite_vars)
qed

lemma open_bound_open_bound_idem[simp]:
  fixes t s :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)" and lc_s: "locally_closed s"
  shows "open_bound n \<tau> u (open_bound n \<tau> s t) = open_bound n \<tau> s t"
  by (induction t arbitrary: n)
    (simp_all add: open_bound_ident_if_locally_closed[OF inf_vars lc_s])

lemma open_bound_commute:
  fixes t s u :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
    and lc_s: "locally_closed s" and lc_u: "locally_closed u"
    and distinct: "(n\<^sub>u, \<tau>\<^sub>u) \<noteq> (n\<^sub>s, \<tau>\<^sub>s)"
  shows "open_bound n\<^sub>u \<tau>\<^sub>u u (open_bound n\<^sub>s \<tau>\<^sub>s s t) =
    open_bound n\<^sub>s \<tau>\<^sub>s s (open_bound n\<^sub>u \<tau>\<^sub>u u t)"
  using distinct
  by (induction t arbitrary: n\<^sub>u n\<^sub>s)
    (auto simp: open_bound_ident_if_locally_closed[OF inf_vars lc_s]
      open_bound_ident_if_locally_closed[OF inf_vars lc_u])


primrec shift_bound :: "nat \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm" where
  "shift_bound n (Const c \<tau>s ts) = Const c \<tau>s ts" |
  "shift_bound n (Free f) = Free f" |
  "shift_bound n (Bound k \<tau>) = Bound (if k < n then k else Suc k) \<tau>" |
  "shift_bound n (App t\<^sub>1 t\<^sub>2) = App (shift_bound n t\<^sub>1) (shift_bound n t\<^sub>2)" |
  "shift_bound n (Abs \<tau> t) = Abs \<tau> (shift_bound (Suc n) t)"

primrec head where
  "head (Const c \<tau>s ts) = Const c \<tau>s ts" |
  "head (Free x) = Free x" |
  "head (Bound n \<tau>) = Bound n \<tau>" |
  "head (App t\<^sub>1 t\<^sub>2) = head t\<^sub>1" |
  "head (Abs \<tau> t) = head t"



end