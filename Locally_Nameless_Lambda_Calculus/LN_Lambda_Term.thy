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

primrec subst_free
  :: "'\<V> \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm" where
  "subst_free x u (Const c \<tau>s ts) = Const c \<tau>s ts"|
  "subst_free x u (Free y) = (if x = y then u else Free y)" |
  "subst_free x u (Bound k) = Bound k" |
  "subst_free x u (App t\<^sub>1 t\<^sub>2) = App (subst_free x u t\<^sub>1) (subst_free x u t\<^sub>2)" |
  "subst_free x u (Abs \<tau> t) = Abs \<tau> (subst_free x u t)"

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
  unfolding body_def
  apply (induction t)
      apply (simp_all add: locally_closed.intros)
    apply (metis Abs subst_bound.simps(3))
  using subst_bound_ident_if_locally_closed[OF inf_vars]
   apply (metis Abs subst_bound.simps(4,5))
  using subst_bound_ident_if_locally_closed[OF inf_vars]
  by (metis Abs subst_bound.simps(5))

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

primrec subterms where
  "subterms (Const c \<tau>s ts) = {#Const c \<tau>s ts#}" |
  "subterms (Free x) = {#Free x#}" |
  "subterms (Bound n) = {#Bound n#}" |
  "subterms (App t\<^sub>1 t\<^sub>2) = add_mset (App t\<^sub>1 t\<^sub>2) (subterms t\<^sub>1 + subterms t\<^sub>2)" |
  "subterms (Abs \<tau> t) = add_mset (Abs \<tau> t) (subterms t)"

fun strip_comb where
  "strip_comb xs (App f x) = strip_comb (x # xs) f" |
  "strip_comb xs f = (f, xs)"

abbreviation strip_comb' where
  "strip_comb' \<equiv> strip_comb []"

lemma "size (fst (strip_comb ts t)) \<le> size t"
proof (induction t arbitrary: ts)
  case (App t1 t2)
  have "size (fst (strip_comb (t2 # ts) t1)) \<le> Suc (size t1 + size t2)"
    using App.IH(1)[of "t2 # ts"] by presburger
  then show ?case
    by simp
qed simp_all

lemma snd_strip_comb_lt:
  assumes "x \<in> set (snd (strip_comb ts t))"
  shows "size x < size t \<or> x \<in> set ts"
  using assms
proof (induction t arbitrary: ts)
  case (App t1 t2)
  then show ?case
    by fastforce
qed simp_all

lemma snd_strip_comb_lt':
  assumes "strip_comb ts t = (f, xs)"
  assumes "x \<in> set xs"
  shows "size x < size t \<or> x \<in> set ts"
  using assms
proof (induction t arbitrary: ts)
  case (App t1 t2)
  then show ?case
    by fastforce
qed simp_all

lemma snd_strip_comb'_lt:
  assumes "x \<in> set (snd (strip_comb' t))"
  shows "size x < size t"
  using assms snd_strip_comb_lt[of x "[]" t]
  by simp

lemma FOO:
  "(f, xs) = strip_comb [t\<^sub>2] t\<^sub>1 \<Longrightarrow> (i, x) \<in> set (zip [0..<length xs] xs) \<Longrightarrow>
    size x < Suc (size t\<^sub>1 + size t\<^sub>2)"
proof (induction t\<^sub>1 arbitrary: f xs)
  case (App t\<^sub>11 t\<^sub>12)
  have "x \<in> set xs"
    by (meson App.prems(2) in_set_zipE)
  have "size x < size (App t\<^sub>11 t\<^sub>12) \<or> x \<in> set [t\<^sub>2]"
    using App.prems(1)
    using snd_strip_comb_lt'[OF _ \<open>x \<in> set xs\<close>, of "[t\<^sub>2]" "App t\<^sub>11 t\<^sub>12" f]
    by metis
  then show ?case
    by auto
qed simp_all

inductive is_subterm_of :: "('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> bool" where
  refl: "is_subterm_of t t" |
  Const: "is_subterm_of s (Const c \<tau>s ts)"
    if "\<exists>t \<in> set ts. is_subterm_of s t" |
  Abs: "is_subterm_of s (Abs \<tau> t)"
    if "is_subterm_of s t" |
  App: "is_subterm_of s (App t\<^sub>1 t\<^sub>2)"
    if "is_subterm_of s t\<^sub>1 \<or> is_subterm_of s t\<^sub>2"

definition is_proper_subterm_of :: "('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> bool" where
  "is_proper_subterm_of s t \<longleftrightarrow> is_subterm_of s t \<and> s \<noteq> t"

lemma is_subterm_of_trans:
  assumes "is_subterm_of t\<^sub>1 t\<^sub>2" and "is_subterm_of t\<^sub>2 t\<^sub>3"
  shows "is_subterm_of t\<^sub>1 t\<^sub>3"
  using assms(2,1)
proof (induction t\<^sub>2 t\<^sub>3 arbitrary: t\<^sub>1 rule: is_subterm_of.induct)
  case (refl t)
  then show ?case by assumption
next
  case (Const ts s c \<tau>s)
  then show ?case
    by (metis is_subterm_of.Const)
next
  case (Abs s t \<tau>)
  then show ?case
    by (metis is_subterm_of.Abs)
next
  case (App s t\<^sub>1' t\<^sub>2')
  then show ?case
    by (metis is_subterm_of.App)
qed

lemma size_lt_or_eq_if_is_subterm_of:
  "is_subterm_of s t \<Longrightarrow> s = t \<or> size s < size t"
proof (induction s t rule: is_subterm_of.induct)
  case (refl t)
  then show ?case by simp
next
  case (Const ts s c \<tau>s)
  then obtain t where "t \<in> set ts" and "size s \<le> size t"
    by fastforce
  hence "size s \<le> size_list size ts"
    using size_list_estimation' by fast
  then show ?case
    by simp
next
  case (Abs s \<tau> t)
  then show ?case by auto
next
  case (App s t\<^sub>1 t\<^sub>2)
  then show ?case by auto
qed

lemma is_subterm_of_antisym:
  fixes t\<^sub>1 t\<^sub>2 :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  shows "is_subterm_of t\<^sub>1 t\<^sub>2 \<Longrightarrow> is_subterm_of t\<^sub>2 t\<^sub>1 \<Longrightarrow> t\<^sub>1 = t\<^sub>2"
  using size_lt_or_eq_if_is_subterm_of[of t\<^sub>1 t\<^sub>2] size_lt_or_eq_if_is_subterm_of[of t\<^sub>2 t\<^sub>1]
  by auto

text \<open>The following interpretation has the side effect of registering the partial order so the
"order" method can use it.\<close>

global_interpretation is_subterm_of: order is_subterm_of is_proper_subterm_of
proof unfold_locales
  show "\<And>x y. is_subterm_of x y \<Longrightarrow> is_subterm_of y x \<Longrightarrow> x = y"
    using is_subterm_of_antisym .
next
  show "\<And>x. is_subterm_of x x"
    using is_subterm_of.refl .
next
  show "\<And>x y z. is_subterm_of x y \<Longrightarrow> is_subterm_of y z \<Longrightarrow> is_subterm_of x z"
    using is_subterm_of_trans .
next
  show "\<And>x y. is_proper_subterm_of x y = (is_subterm_of x y \<and> \<not> is_subterm_of y x)"
    by (metis is_proper_subterm_of_def is_subterm_of_antisym)
qed

hide_fact is_subterm_of.refl is_subterm_of_antisym is_subterm_of_trans

text \<open>Prefer the standard names @{thm is_subterm_of.order_antisym is_subterm_of.order_trans
  is_subterm_of.order_refl}.\<close>

lemma wfp_is_proper_subterm_of: "wfp is_proper_subterm_of"
proof (rule wfp_if_convertible_to_nat)
  fix x y :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assume "is_proper_subterm_of x y"
  thus "size x < size y"
    using size_lt_or_eq_if_is_subterm_of
    by (auto simp: is_proper_subterm_of_def)
qed

lemma is_subterm_of_fst_strip_comb: "is_subterm_of (fst (strip_comb xs t)) t"
  by (induction t rule: strip_comb.induct) (simp_all add: is_subterm_of.App)

lemma snd_strip_comb_in_list_or_substerm:
  "s \<in> set (snd (strip_comb xs t)) \<Longrightarrow> s \<in> set xs \<or> is_subterm_of s t"
proof (induction t rule: strip_comb.induct)
  case (1 xs f x)
  then show ?case
    using is_subterm_of.App by auto
qed simp_all

lemma strip_comb'_subterm_of:
  "s = fst (strip_comb' t) \<or> s \<in> set (snd (strip_comb' t)) \<Longrightarrow> is_subterm_of s t"
  by (metis empty_iff is_subterm_of_fst_strip_comb list.set(1) snd_strip_comb_in_list_or_substerm)

inductive is_orange_subterm_at where
  Nil: "is_orange_subterm_at u u []" |
  App: "is_orange_subterm_at v (App t\<^sub>1 t\<^sub>2) (i # p)"
    if "strip_comb' (App t\<^sub>1 t\<^sub>2) = (f, us)"
    and "i < length us"
    and "is_Const f \<or> is_Bound f"
    and "is_orange_subterm_at v (us ! i) p" |
  Abs: "is_orange_subterm_at v (Abs \<tau> t) (0 # p)"
if "is_orange_subterm_at v t p"

text \<open>Contrary to Definition 2.2 of the paper, our positions count starting at zero.\<close>

lemma subterm_if_orange_subterm:
  assumes "is_orange_subterm_at s t p"
  shows "is_subterm_of s t"
  using assms
proof (induction s t p rule: is_orange_subterm_at.induct)
  case (Nil u)
  then show ?case
    by (simp add: is_subterm_of.intros)
next
  case (App t\<^sub>1 t\<^sub>2 f us i v p)
  then show ?case
    by (metis is_subterm_of.dual_order.trans nth_mem snd_conv strip_comb'_subterm_of)
next
  case (Abs v t p \<tau>)
  then show ?case
    by (simp add: is_subterm_of.intros)
qed

(*
function positions where
  "positions (Const c \<tau>s ts) = {[]}" |
  "positions (Free x) = {[]}" |
  "positions (Bound n) = {[]}" |
  "positions (App t\<^sub>1 t\<^sub>2) =
    (let (f, xs) = strip_comb' (App t\<^sub>1 t\<^sub>2) in
     insert [] (\<Union> (set (map2 (\<lambda>i x. Cons (Suc i) ` positions x) (upt (0 :: nat) (length xs)) xs))))" |
  "positions (Abs \<tau> t) = insert [] {1 # p | p. p \<in> positions t}"
  by pat_completeness auto
termination by (lexicographic_order simp add: FOO)

function positions' where
  "positions' (Const c \<tau>s ts) = {[]}" |
  "positions' (Free x) = {[]}" |
  "positions' (Bound n) = {[]}" |
  "positions' (App t\<^sub>1 t\<^sub>2) =
    (let (f, xs) = strip_comb' (App t\<^sub>1 t\<^sub>2) in
     insert [] {Suc i # p | i p. i < length xs \<and> p \<in> positions' (xs ! i)})" |
  "positions' (Abs \<tau> t) = insert [] {1 # p | p. p \<in> positions' t}"
  by pat_completeness auto
termination
proof (relation "measure size")
  show "wf (measure size)"
    by simp
next
  fix t\<^sub>1 t\<^sub>2 x xa y xb xc xd
  show "x = strip_comb' (App t\<^sub>1 t\<^sub>2) \<Longrightarrow> (xa, y) = x \<Longrightarrow> (y ! xc, App t\<^sub>1 t\<^sub>2) \<in> measure size"
    unfolding in_measure
    sorry
  oops

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