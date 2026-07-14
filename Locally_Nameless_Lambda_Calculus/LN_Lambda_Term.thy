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
  is_Bound: Bound nat |
  is_App: App "('\<tau>, '\<Sigma>, '\<V>) preterm" "('\<tau>, '\<Sigma>, '\<V>) preterm" |
  is_Abs: Abs "'\<tau>" "('\<tau>, '\<Sigma>, '\<V>) preterm"

lemma finite_vars_term: "finite (free_vars t)"
  by (induction t) simp_all

declare fset_of_list.rep_eq[termination_simp]

fun free_vars_fset :: "('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> '\<V> fset" where
  "free_vars_fset (Const _ _ ts) = ffUnion (free_vars_fset |`| fset_of_list ts)" |
  "free_vars_fset (Free x) = {|x|}" |
  "free_vars_fset (Bound _) = {||}" |
  "free_vars_fset (App t\<^sub>1 t\<^sub>2) = free_vars_fset t\<^sub>1 |\<union>| free_vars_fset t\<^sub>2" |
  "free_vars_fset (Abs _ t) = free_vars_fset t"

lemma free_vars_fset_rep_eq: "fset (free_vars_fset t) = free_vars t"
  by (induction t) (simp_all add: ffUnion.rep_eq fimage.rep_eq fset_of_list.rep_eq)

primrec subst_bound :: "nat \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm" where
  "subst_bound n t (Const c \<tau>s ts) = Const c \<tau>s ts"|
  "subst_bound n t (Free f) = Free f" |
  "subst_bound n t (Bound k) = (if k = n then t else Bound k)" |
  "subst_bound n t (App t\<^sub>1 t\<^sub>2) = App (subst_bound n t t\<^sub>1) (subst_bound n t t\<^sub>2)" |
  "subst_bound n t (Abs \<tau> t\<^sub>1) = Abs \<tau> (subst_bound (Suc n) t t\<^sub>1)"

lemma free_vars_subst_bound_subset: "free_vars (subst_bound n u t) \<subseteq> free_vars t \<union> free_vars u"
  by (induction t arbitrary: n) auto

inductive locally_closed :: "('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> bool" where
  Const: "locally_closed (Const c \<tau>s ts)"
    if "list_all locally_closed ts" for c \<tau>s ts |
  Free: "locally_closed (Free f)" |
  App: "locally_closed (App t\<^sub>1 t\<^sub>2)"
    if "locally_closed t\<^sub>1" and "locally_closed t\<^sub>2" |
  Abs: "locally_closed (Abs \<tau> t)"
    if "\<And>x. x |\<notin>| \<X> \<Longrightarrow> locally_closed (subst_bound 0 (Free x) t)"

definition body where
  "body t \<longleftrightarrow> (\<exists>\<X>. \<forall>x. x |\<notin>| \<X> \<longrightarrow> locally_closed (subst_bound 0 (Free x) t))"

text \<open>A structural, level-indexed notion of local closure: \<open>locally_closed_at k t\<close> holds when every
  dangling bound index of \<open>t\<close> is smaller than \<open>k\<close>. \<^bold>\<open>Note:\<close> constant parameters are required to be
  closed (level \<open>0\<close>), matching the fact that \<^const>\<open>subst_bound\<close> and \<open>subst_free\<close> treat them
  opaquely (they never descend into them); with the naive rule \<open>list_all (locally_closed_at k) ts\<close>
  the equivalence with \<^const>\<open>locally_closed\<close> below would fail.\<close>

inductive locally_closed_at :: "nat \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> bool" where
  Bound: "locally_closed_at k (Bound i)" if "i < k" |
  Const: "locally_closed_at k (Const c \<tau>s ts)" if "list_all (locally_closed_at 0) ts" for k c \<tau>s ts |
  Free: "locally_closed_at k (Free f)" |
  App: "locally_closed_at k (App t\<^sub>1 t\<^sub>2)" if "locally_closed_at k t\<^sub>1" and "locally_closed_at k t\<^sub>2" |
  Abs: "locally_closed_at k (Abs \<tau> t)" if "locally_closed_at (Suc k) t"

lemma locally_closed_at_Bound_iff[simp]: "locally_closed_at k (Bound i) \<longleftrightarrow> i < k"
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

lemma locall_closed_Abs_iff_body: "locally_closed (Abs \<tau> t) \<longleftrightarrow> body t"
  unfolding locally_closed.simps[of "Abs _ _", simplified] body_def ..

lemma body_App_iff: "body (App t\<^sub>1 t\<^sub>2) \<longleftrightarrow> body t\<^sub>1 \<and> body t\<^sub>2"
  unfolding body_def by (auto simp add: locally_closed_App_iff)

lemma locally_closed_at_Abs_iff[simp]:
  "locally_closed_at k (Abs \<tau> t) \<longleftrightarrow> locally_closed_at (Suc k) t"
  by (auto elim: locally_closed_at.cases intro: locally_closed_at.Abs)

lemma locally_closed_at_Const_iff[simp]:
  "locally_closed_at k (Const c \<tau>s ts) \<longleftrightarrow> (\<forall>t \<in> set ts. locally_closed_at 0 t)"
  by (auto elim: locally_closed_at.cases intro: locally_closed_at.Const simp: list.pred_set)

text \<open>Opening a fresh variable lowers the level by one, and vice versa (local closure ignores free
  variables, so no freshness side condition is needed).\<close>

lemma locally_closed_at_subst_bound_Free:
  "locally_closed_at (Suc k) t \<Longrightarrow> locally_closed_at k (subst_bound k (Free x) t)"
  by (induction t arbitrary: k) auto

lemma locally_closed_at_Suc_if_subst_bound_Free:
  "locally_closed_at k (subst_bound k (Free x) t) \<Longrightarrow> locally_closed_at (Suc k) t"
  by (induction t arbitrary: k) (auto split: if_splits)

primrec subst_free
  :: "'\<V> \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm" where
  "subst_free x u (Const c \<tau>s ts) = Const c \<tau>s ts"|
  "subst_free x u (Free y) = (if x = y then u else Free y)" |
  "subst_free x u (Bound k) = Bound k" |
  "subst_free x u (App t\<^sub>1 t\<^sub>2) = App (subst_free x u t\<^sub>1) (subst_free x u t\<^sub>2)" |
  "subst_free x u (Abs \<tau> t) = Abs \<tau> (subst_free x u t)"

lemma size_subst_bound_Free[simp]: "size (subst_bound n (Free x) t) = size t"
  by (induction t arbitrary: n) simp_all

text \<open>Over an infinite variable type, \<^const>\<open>locally_closed\<close> and \<^const>\<open>body\<close> coincide with
  \<^const>\<open>locally_closed_at\<close> at levels \<open>0\<close> and \<open>1\<close>. (Infinitely many variables are needed to rule out the
  spurious models of the cofinite \<^const>\<open>locally_closed\<close> over finite variable types.)\<close>

lemma locally_closed_iff_locally_closed_at:
  fixes t :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  shows "locally_closed t \<longleftrightarrow> locally_closed_at 0 t"
proof (induction t rule: measure_induct_rule[where f = size])
  case (less t)
  show ?case
  proof (cases t)
    case (Const c \<tau>s ts)
    have "size t' < size t" if "t' \<in> set ts" for t'
    proof -
      have "size t' \<le> size_list size ts"
        by (rule size_list_estimation'[OF that order_refl])
      then show ?thesis by (simp add: Const)
    qed
    then show ?thesis
      using less.IH by (auto simp: Const)
  next
    case (Free x)
    then show ?thesis by (simp add: locally_closed.Free)
  next
    case (Bound i)
    then show ?thesis by (simp add: locally_closed.simps[of "Bound _"])
  next
    case (App t\<^sub>1 t\<^sub>2)
    then show ?thesis
      using less.IH by (auto simp: locally_closed_App_iff)
  next
    case (Abs \<tau> s)
    have "body s \<longleftrightarrow> locally_closed_at (Suc 0) s"
    proof
      assume "body s"
      then obtain \<X> :: "'\<V> fset" where
        X: "\<And>x. x |\<notin>| \<X> \<Longrightarrow> locally_closed (subst_bound 0 (Free x) s)"
        unfolding body_def by blast
      obtain x :: '\<V> where "x |\<notin>| \<X>"
        using inf_vars by (metis ex_new_if_finite finite_fset)
      from X[OF this] have "locally_closed (subst_bound 0 (Free x) s)" .
      moreover have "size (subst_bound 0 (Free x) s) < size t"
        by (simp add: Abs)
      ultimately have "locally_closed_at 0 (subst_bound 0 (Free x) s)"
        using less.IH by blast
      then show "locally_closed_at (Suc 0) s"
        by (rule locally_closed_at_Suc_if_subst_bound_Free)
    next
      assume "locally_closed_at (Suc 0) s"
      have "locally_closed (subst_bound 0 (Free x) s)" for x
      proof -
        have "locally_closed_at 0 (subst_bound 0 (Free x) s)"
          using locally_closed_at_subst_bound_Free[OF \<open>locally_closed_at (Suc 0) s\<close>] by simp
        moreover have "size (subst_bound 0 (Free x) s) < size t"
          by (simp add: Abs)
        ultimately show ?thesis
          using less.IH by blast
      qed
      then show "body s"
        unfolding body_def by blast
    qed
    then show ?thesis
      by (simp add: Abs locall_closed_Abs_iff_body)
  qed
qed

lemma body_iff_locally_closed_at:
  fixes t :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  shows "body t \<longleftrightarrow> locally_closed_at (Suc 0) t"
  by (metis locally_closed_iff_locally_closed_at[OF inf_vars] locally_closed_at_Abs_iff
      locall_closed_Abs_iff_body)

lemma subst_bound_subst_bound_Free_idem[simp]:
  "subst_bound n u (subst_bound n (Free x) t) = subst_bound n (Free x) t"
  by (induction t arbitrary: n rule: preterm.induct) simp_all

lemma subst_free_ident_if_not_in_vars[simp]: "x \<notin> free_vars t \<Longrightarrow> subst_free x u t = t"
  by (induction t) simp_all

lemma subst_bound_idem_if_subst_bound_subst_bound_idem:
  "i \<noteq> j \<Longrightarrow>
  subst_bound i (Free u) (subst_bound j (Free v) t) = subst_bound j (Free v) t \<Longrightarrow>
  subst_bound i (Free u) t = t"
proof (induction t arbitrary: i j rule: preterm.induct)
  case (Bound x)
  then show ?case
    by auto
next
  case (Abs t)
  then show ?case
    unfolding subst_bound.simps preterm.inject
    by force
qed simp_all

lemma subst_bound_ident_if_locally_closed:
  fixes t :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes "locally_closed t"
  shows "subst_bound n u t = t"
  using \<open>locally_closed t\<close>
proof (induction t arbitrary: n u rule: locally_closed.induct)
  case (Const c \<tau>s ts)
  then show ?case by simp
next
  case (Free c)
  then show ?case by simp
next
  case (App t\<^sub>1 t\<^sub>2)
  then show ?case by simp
next
  case (Abs \<X> t)
  obtain x :: '\<V> where "x |\<notin>| \<X>"
    using inf_vars
    by (metis assms(1) finite_fset ex_new_if_finite)

  then have IH': "\<And>n u. subst_bound n u (subst_bound 0 (Free x) t) = subst_bound 0 (Free x) t"
    using Abs.IH by auto

  show ?case
    using subst_bound_idem_if_subst_bound_subst_bound_idem[of _ 0]
    by (metis IH' nat.distinct(1) subst_bound.simps(5) subst_bound_subst_bound_Free_idem)
qed


text \<open>Chargu\<eacute>raud's \<open>subst_open\<close>: substitution commutes with opening. His proof generalises to an
  arbitrary index and, in the \<^const>\<open>Free\<close> case, uses \<open>open_rec_lc\<close> (here
  \<open>subst_bound_ident_if_locally_closed\<close>) to see that opening does not affect the locally closed term
  \<open>u\<close>. That auxiliary needs \<open>infinite (UNIV :: '\<V> set)\<close> in this development (the \<open>Abs\<close> rule of
  \<^const>\<open>locally_closed\<close> is cofinite), which corresponds to Chargu\<eacute>raud's atoms being infinite; over a
  finite variable type \<^const>\<open>locally_closed\<close> can hold spuriously and the statement is refutable.\<close>

lemma subst_open:
  fixes t :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes "locally_closed u"
  shows "subst_free x u (subst_bound k v t) = subst_bound k (subst_free x u v) (subst_free x u t)"
  by (induction t arbitrary: k)
    (simp_all add: subst_bound_ident_if_locally_closed[OF inf_vars \<open>locally_closed u\<close>])

lemma subst_free_subst_bound_Free_eq_subst_bound:
  assumes "x \<notin> free_vars t"
  shows "subst_free x u (subst_bound n (Free x) t) = subst_bound n u t"
  using assms by (induction t arbitrary: n) auto

lemma subst_free_commutes_with_subst_bound_Free:
  fixes t :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes "x \<noteq> y" and "locally_closed u"
  shows "subst_free x u (subst_bound n (Free y) t) = subst_bound n (Free y) (subst_free x u t)"
proof (induction t arbitrary: n rule: preterm.induct)
  case (Const c \<tau>s ts)
  then show ?case
    by simp
next
  case (Free z)
  then show ?case
    unfolding subst_bound.simps
    by (cases "x = z")
      (simp_all add: subst_bound_ident_if_locally_closed[OF inf_vars \<open>locally_closed u\<close>])
next
  case (Bound i)
  then show ?case
    using \<open>x \<noteq> y\<close> by simp
next
  case (App t1 t2)
  then show ?case
    by simp
next
  case (Abs t)
  then show ?case
    by simp
qed

lemma locally_closed_subst_free:
  fixes t u :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes
    inf_vars: "infinite (UNIV :: '\<V> set)" and
    "locally_closed t" and "locally_closed u"
  shows "locally_closed (subst_free x u t)"
  using \<open>locally_closed t\<close>
proof (induction t rule: locally_closed.induct)
  case (Const c \<tau>s ts)
  show ?case
    unfolding subst_free.simps
  proof (rule locally_closed.Const)
    show "list_all locally_closed ts"
      using list.pred_mono_strong local.Const by auto
  qed
next
  case (Free f)
  then show ?case
    using \<open>locally_closed u\<close>
    by (simp add: locally_closed.Free)
next
  case (App t\<^sub>1 t\<^sub>2)
  then show ?case
    by (simp add: locally_closed.App)
next   
  case (Abs \<X> t)
  show ?case
    unfolding subst_free.simps
  proof (rule locally_closed.Abs)
    fix y :: '\<V>
    assume "y |\<notin>| finsert x \<X>"
    hence "x \<noteq> y" and "y |\<notin>| \<X>"
      by auto
    show "locally_closed (subst_bound 0 (Free y) (subst_free x u t))"
      unfolding subst_free_commutes_with_subst_bound_Free[OF inf_vars \<open>x \<noteq> y\<close> \<open>locally_closed u\<close>,
          symmetric]
      using Abs.IH[OF \<open>y |\<notin>| \<X>\<close>] .
  qed
qed

lemma body_subst_free:
  fixes t u :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes
    inf_vars: "infinite (UNIV :: '\<V> set)" and
    "body t" and "locally_closed u"
  shows "body (subst_free x u t)"
proof -
  have "locally_closed (subst_free x u (Abs \<tau> t))" for \<tau>
  proof (intro locally_closed_subst_free[OF inf_vars])
    show "locally_closed (Abs \<tau> t)"
      using \<open>body t\<close> by (simp add: locall_closed_Abs_iff_body)
  next
    show "locally_closed u"
      using \<open>locally_closed u\<close> .
  qed

  then show ?thesis
    by (simp add: locall_closed_Abs_iff_body)
qed

lemma body_Abs_if_body:
  fixes t :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  shows "body t \<Longrightarrow> body (Abs \<tau> t)"
proof (induction t)
  case (Const x1 x2a x3a)
  then show ?case
    by (simp add: body_def locall_closed_Abs_iff_body)
next
  case (Free x)
  then show ?case
    by (simp add: body_iff_locally_closed_at inf_vars)
next
  case (Bound x)
  then show ?case
    by (simp add: body_iff_locally_closed_at inf_vars)
next
  case (App t1 t2)
  then show ?case
    by (simp add: body_iff_locally_closed_at inf_vars)
next
  case (Abs x1 t)
  then show ?case
    by (metis body_def locall_closed_Abs_iff_body subst_bound_ident_if_locally_closed[OF inf_vars])
qed

lemma locally_closed_subst_bound:
  fixes t u :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes "body t" and "locally_closed u"
  shows "locally_closed (subst_bound 0 u t)"
proof -
  obtain \<X> :: "'\<V> fset" where
    lc_substb_0_t: "\<And>x. x |\<notin>| \<X> \<Longrightarrow> locally_closed (subst_bound 0 (Free x) t)"
    using \<open>body t\<close>
    by (metis body_def)

  obtain x :: '\<V> where "x \<notin> free_vars t" and "x \<notin> fset \<X>"
    by (metis Un_iff ex_new_if_finite finite_Un finite_fset finite_vars_term inf_vars)

  then obtain "subst_free x u (subst_bound 0 (Free x) t) = subst_bound 0 u t"
    using subst_free_subst_bound_Free_eq_subst_bound by metis

  moreover have "locally_closed (subst_free x u (subst_bound 0 (Free x) t))"
  proof (rule locally_closed_subst_free[OF inf_vars])
    show "locally_closed (subst_bound 0 (Free x) t)"
      using lc_substb_0_t[OF \<open>x \<notin> fset \<X>\<close>] .
  next
    show "locally_closed u"
      using \<open>locally_closed u\<close> .
  qed

  ultimately show ?thesis
    by metis
qed

lemma subst_bound_distrib:
  fixes t :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes "locally_closed s"
  shows "subst_bound n u (subst_bound n s t) = subst_bound n (subst_bound n u s) t"
  using assms
  using subst_bound_ident_if_locally_closed[OF inf_vars \<open>locally_closed s\<close>]
  by (induction t arbitrary: n rule: preterm.induct) simp_all

lemma subst_bound_subst_bound_idem[simp]:
  fixes t :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes "locally_closed s"
  shows "subst_bound n u (subst_bound n s t) = subst_bound n s t"
  unfolding subst_bound_distrib[OF assms]
  unfolding subst_bound_ident_if_locally_closed[OF assms]
  ..

lemma subst_bound_subst_bound:
  fixes t :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes "locally_closed s" and "locally_closed u" and "n\<^sub>u \<noteq> n\<^sub>s"
  shows "subst_bound n\<^sub>u u (subst_bound n\<^sub>s s t) = subst_bound n\<^sub>s s (subst_bound n\<^sub>u u t)"
  using assms
proof (induction t arbitrary: n\<^sub>u u n\<^sub>s s)
  case (Const \<kappa> \<tau>s ts)
  then show ?case
    using subst_bound_ident_if_locally_closed[OF inf_vars]
    by simp
next
  case (Free x)
  then show ?case
    by simp
next
  case (Bound x)
  then show ?case
    using \<open>n\<^sub>u \<noteq> n\<^sub>s\<close>
    by (simp_all add: subst_bound_ident_if_locally_closed)
next
  case (App t1 t2)
  then show ?case
    by simp
next
  case (Abs \<tau> t)
  then show ?case
    by simp
qed

primrec shift_bound :: "nat \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm" where
  "shift_bound n (Const c \<tau>s ts) = Const c \<tau>s ts" |
  "shift_bound n (Free f) = Free f" |
  "shift_bound n (Bound k) = Bound (if k < n then k else Suc k)" |
  "shift_bound n (App t\<^sub>1 t\<^sub>2) = App (shift_bound n t\<^sub>1) (shift_bound n t\<^sub>2)" |
  "shift_bound n (Abs \<tau> t) = Abs \<tau> (shift_bound (Suc n) t)"

primrec head where
  "head (Const c \<tau>s ts) = Const c \<tau>s ts" |
  "head (Free x) = Free x" |
  "head (Bound n) = Bound n" |
  "head (App t\<^sub>1 t\<^sub>2) = head t\<^sub>1" |
  "head (Abs \<tau> t) = head t"


(*

(* text \<open>Creating a context from a term by adding a hole at a specific position.\<close>
fun replace_at :: "nat list \<Rightarrow> _ \<Rightarrow> _" where
    "replace_at [] t u = u" |
    "replace_at (i # ps) (Fun f ts) =
    More f (take i ts) (ctxt_of_pos_term ps (ts!i)) (drop (Suc i) ts)"

abbreviation (input) "replace_at t p s \<equiv> (ctxt_of_pos_term p t)\<langle>s\<rangle>" *)

fun beta_reduce :: "('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm" where
  "beta_reduce (App (Abs \<tau> t\<^sub>1) t\<^sub>2) = subst_bound 0 t\<^sub>2 t\<^sub>1" |
  "beta_reduce t = t"

term beta_reduce

inductive is_\<beta>normal where
  "is_\<beta>normal"

primrec is_hnf_App where                                  
  "is_hnf_App (Const _ _ _) \<longleftrightarrow> True" |
  "is_hnf_App (Free _) \<longleftrightarrow> True" |
  "is_hnf_App (Bound _) \<longleftrightarrow> True" |
  "is_hnf_App (App t _) \<longleftrightarrow> is_hnf_App t" |
  "is_hnf_App (Abs _ _) \<longleftrightarrow> False"

primrec is_hnf where                                  
  "is_hnf (Const _ _ _) \<longleftrightarrow> True" |
  "is_hnf (Free _) \<longleftrightarrow> True" |
  "is_hnf (Bound _) \<longleftrightarrow> True" |
  "is_hnf (App t _) \<longleftrightarrow> is_hnf_App t" |
  "is_hnf (Abs _ t) \<longleftrightarrow> is_hnf t"

experiment begin

term "Const c\<^sub>1 [] []"

lemma "is_hnf (App (Const c\<^sub>1 [] []) (Const c\<^sub>2 [] []))"
  by simp

lemma "is_hnf (App (App (Const c\<^sub>1 [] []) (Const c\<^sub>2 [] [])) (Const c\<^sub>3 [] []))"
  by simp

lemma "is_hnf (App (Const c\<^sub>1 [] []) (App (Const c\<^sub>2 [] []) (Const c\<^sub>3 [] [])))"
  by simp

lemma "\<not> is_hnf (App (Abs \<tau> (Const c\<^sub>1 [] [])) (Const c\<^sub>2 [] []))"
  by simp

lemma "is_hnf (Abs \<tau> (App (Const c\<^sub>1 [] []) (Bound 0)))"
  by simp

lemma "is_hnf (Abs \<tau>\<^sub>1 (Abs \<tau>\<^sub>2 (App (App (Const c\<^sub>1 [] []) (Bound 1)) (Bound 0))))"
  by simp

end *)
 
(* lemma "is_hnf t \<Longrightarrow> beta_reduce t = t"
proof (induction t)
  case (App t\<^sub>1 t\<^sub>2)
  have "\<not> is_Abs t\<^sub>1"
    using \<open>is_hnf (App t\<^sub>1 t\<^sub>2)\<close>
    by (cases t\<^sub>1) simp_all
  then have "beta_reduce (App t\<^sub>1 t\<^sub>2) = (App (beta_reduce t\<^sub>1) t\<^sub>2)"
    by (cases t\<^sub>1) simp_all
  moreover have "beta_reduce t\<^sub>1 = t\<^sub>1"
    using App.IH
    by (metis App.prems \<open>\<not> is_Abs t\<^sub>1\<close>
        beta_reduce.simps(7,8) is_hnf.simps(1,4)
        is_hnf_App.simps(4) preterm.disc(25)
        preterm.exhaust_sel)
  ultimately show ?case
    by metis
qed simp_all *)

end