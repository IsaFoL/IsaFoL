theory LN_Lambda_Term
  imports
    Main
    "HOL-Library.Uprod"
    "HOL-Library.Multiset"
    "HOL-Library.FSet"
    "HOL-ex.Sketch_and_Explore"
begin

declare foldl_inject[simp]

datatype ('\<tau>, 'c, free_vars: 'f) preterm =
  is_Const: Const 'c "'\<tau> list" "('\<tau>, 'c, 'f) preterm list" |
  is_Free: Free 'f |
  is_Bound: Bound nat |
  is_App: App "('\<tau>, 'c, 'f) preterm" "('\<tau>, 'c, 'f) preterm" |
  is_Abs: Abs "'\<tau>" "('\<tau>, 'c, 'f) preterm"

lemma finite_vars_term: "finite (free_vars t)"
  by (induction t) simp_all

primrec subst_bound :: "nat \<Rightarrow> ('\<tau>, 'c, 'f) preterm \<Rightarrow> ('\<tau>, 'c, 'f) preterm \<Rightarrow> ('\<tau>, 'c, 'f) preterm" where
  "subst_bound n t (Const c \<tau>s ts) = Const c \<tau>s ts"|
  "subst_bound n t (Free f) = Free f" |
  "subst_bound n t (Bound k) = (if k = n then t else Bound k)" |
  "subst_bound n t (App t\<^sub>1 t\<^sub>2) = App (subst_bound n t t\<^sub>1) (subst_bound n t t\<^sub>2)" |
  "subst_bound n t (Abs \<tau> t\<^sub>1) = Abs \<tau> (subst_bound (Suc n) t t\<^sub>1)"

primrec subst_free
  :: "'f \<Rightarrow> ('\<tau>, 'c, 'f) preterm \<Rightarrow> ('\<tau>, 'c, 'f) preterm \<Rightarrow> ('\<tau>, 'c, 'f) preterm" where
  "subst_free x u (Const c \<tau>s ts) = Const c \<tau>s ts"|
  "subst_free x u (Free y) = (if x = y then u else Free y)" |
  "subst_free x u (Bound k) = Bound k" |
  "subst_free x u (App t\<^sub>1 t\<^sub>2) = App (subst_free x u t\<^sub>1) (subst_free x u t\<^sub>2)" |
  "subst_free x u (Abs \<tau> t) = Abs \<tau> (subst_free x u t)"

inductive locally_closed :: "('\<tau>, 'c, 'f) preterm \<Rightarrow> bool" where
  Const: "locally_closed (Const c \<tau>s ts)"
    if "list_all locally_closed ts" for c \<tau>s ts |
  Free: "locally_closed (Free f)" |
  App: "locally_closed (App t\<^sub>1 t\<^sub>2)"
    if "locally_closed t\<^sub>1" and "locally_closed t\<^sub>2" |
  Abs: "locally_closed (Abs \<tau> t)"
    if "\<And>x. x |\<notin>| \<X> \<Longrightarrow> locally_closed (subst_bound 0 (Free x) t)"

definition body where
  "body t \<longleftrightarrow> (\<exists>\<X>. \<forall>x. x |\<notin>| \<X> \<longrightarrow> locally_closed (subst_bound 0 (Free x) t))"

lemma locally_closed_App_iff: "locally_closed (App t\<^sub>1 t\<^sub>2) \<longleftrightarrow> locally_closed t\<^sub>1 \<and> locally_closed t\<^sub>2"
  by (auto elim: locally_closed.cases intro: locally_closed.App)

lemma locall_closed_Abs_iff_body: "locally_closed (Abs \<tau> t) \<longleftrightarrow> body t"
  unfolding locally_closed.simps[of "Abs _ _", simplified] body_def ..

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
    unfolding subst_bound.simps term.inject
    by force
qed simp_all

lemma subst_bound_ident_if_locally_closed:
  fixes t :: "('\<tau>, 'c, 'f) preterm"
  assumes inf_vars: "infinite (UNIV :: 'f set)"
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
  obtain x :: 'f where "x |\<notin>| \<X>"
    using inf_vars
    by (metis assms(1) finite_fset ex_new_if_finite)

  then have IH': "\<And>n u. subst_bound n u (subst_bound 0 (Free x) t) = subst_bound 0 (Free x) t"
    using Abs.IH by auto

  show ?case
    using subst_bound_idem_if_subst_bound_subst_bound_idem[of _ 0]
    by (metis IH' nat.distinct(1) subst_bound.simps(5) subst_bound_subst_bound_Free_idem)
qed

lemma subst_free_term_subst_bound_Free_eq_subst_bound_term:
  assumes "x \<notin> free_vars t"
  shows "subst_free x u (subst_bound n (Free x) t) = subst_bound n u t"
  using assms
proof (induction t arbitrary: n rule: preterm.induct)
  case (Const c \<tau>s ts)
  then show ?case
    by simp
next
  case (Free y)
  then have "x \<noteq> y"
    by simp
  then show ?case
    by simp
next
  case (Bound i)
  then show ?case
    by (auto split: if_split)
next
  case (App t1 t2)
  then show ?case
    by simp
next
  case (Abs \<tau> t)
  have "x \<notin> free_vars t"
    using Abs.prems by simp
  then have "\<And>n. subst_free x u (subst_bound n (Free x) t) = subst_bound n u t"
    using Abs.IH by simp
  then show ?case
    by simp
qed

lemma subst_free_commutes_with_subst_bound_Free:
  fixes t :: "('\<tau>, 'c, 'f) preterm"
  assumes inf_vars: "infinite (UNIV :: 'f set)"
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
  fixes t u :: "('\<tau>, 'c, 'f) preterm"
  assumes
    inf_vars: "infinite (UNIV :: 'f set)" and
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
    fix y :: 'f
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
  fixes t u :: "('\<tau>, 'c, 'f) preterm"
  assumes
    inf_vars: "infinite (UNIV :: 'f set)" and
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
  fixes t :: "('\<tau>, 'c, 'f) preterm"
  assumes inf_vars: "infinite (UNIV :: 'f set)"
  shows "body t \<Longrightarrow> body (Abs \<tau> t)"
  unfolding body_def
  apply (induction t)
      apply (simp_all add: locally_closed.intros)
    apply (metis Abs subst_bound.simps(3))
  using subst_bound_ident_if_locally_closed[OF inf_vars]
   apply (metis Abs subst_bound.simps(4,5))
  using subst_bound_ident_if_locally_closed[OF inf_vars]
  by (metis Abs subst_bound.simps(5))

lemma locally_closed_subst_bound:
  fixes t u :: "('\<tau>, 'c, 'f) preterm"
  assumes inf_vars: "infinite (UNIV :: 'f set)"
  assumes "body t" and "locally_closed u"
  shows "locally_closed (subst_bound 0 u t)"
proof -
  obtain \<X> :: "'f fset" where
    lc_substb_0_t: "\<And>x. x |\<notin>| \<X> \<Longrightarrow> locally_closed (subst_bound 0 (Free x) t)"
    using \<open>body t\<close>
    by (metis body_def)

  obtain x :: 'f where "x \<notin> free_vars t" and "x \<notin> fset \<X>"
    by (metis Un_iff ex_new_if_finite finite_Un finite_fset finite_vars_term inf_vars)

  then obtain "subst_free x u (subst_bound 0 (Free x) t) = subst_bound 0 u t"
    using subst_free_term_subst_bound_Free_eq_subst_bound_term by metis

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

primrec shift_bound :: "nat \<Rightarrow> ('\<tau>, 'c, 'f) preterm \<Rightarrow> ('\<tau>, 'c, 'f) preterm" where
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

primrec subterms where
  "subterms (Const c \<tau>s ts) = {#Const c \<tau>s ts#}" |
  "subterms (Free x) = {#Free x#}" |
  "subterms (Bound n) = {#Bound n#}" |
  "subterms (App t\<^sub>1 t\<^sub>2) = add_mset (App t\<^sub>1 t\<^sub>2) (subterms t\<^sub>1 + subterms t\<^sub>2)" |
  "subterms (Abs \<tau> t) = add_mset (Abs \<tau> t) (subterms t)"

fun beta_reduce where
  "beta_reduce (App (Abs \<tau> t\<^sub>1) t\<^sub>2) = subst_bound 0 t\<^sub>2 t\<^sub>1" |
  "beta_reduce (App t\<^sub>1 t\<^sub>2) = (App (beta_reduce t\<^sub>1) t\<^sub>2)" |
  "beta_reduce t = t"

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

end
 
lemma "is_hnf t \<Longrightarrow> beta_reduce t = t"
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
qed simp_all

end