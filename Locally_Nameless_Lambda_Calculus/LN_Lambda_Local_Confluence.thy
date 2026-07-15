theory LN_Lambda_Local_Confluence
  imports LN_Lambda_Reduction
begin

section \<open>Local confluence of \<open>\<beta>\<close>-reduction\<close>

text \<open>Proof sketch of local confluence (weak confluence) of \<^const>\<open>beta_reduce\<close>: any two one-step
  reducts of a preterm can be joined by finitely many reduction steps. Together with strong
  normalization of the well-typed fragment and Newman's lemma, this would yield confluence of that
  fragment.

  The proof is by rule induction on the first reduction and inversion of the second one. Its
  supporting lemmas establish:
  \<^item> substitutivity of the argument (\<open>beta_reduce_rtrancl_subst_free_arg\<close>), contracting the (possibly many)
    occurrences of a variable one after the other;
  \<^item> congruence of \<open>beta_reduce\<^sup>*\<^sup>*\<close> under \<^const>\<open>Abs\<close> (\<open>beta_reduce_rtrancl_Abs\<close>), using the
    variable-closing operation \<open>close_free\<close> and its interaction with opening and substitution;
  \<^item> congruence of \<open>beta_reduce\<^sup>*\<^sup>*\<close> under \<^const>\<open>Const\<close> (\<open>beta_reduce_rtrancl_Const\<close>), including
    the required list bookkeeping.\<close>


subsection \<open>Congruence rules for \<open>beta_reduce\<^sup>*\<^sup>*\<close>\<close>

lemma beta_reduce_rtrancl_App_left:
  fixes t t' u :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes "beta_reduce\<^sup>*\<^sup>* t t'" and "locally_closed u"
  shows "beta_reduce\<^sup>*\<^sup>* (App t u) (App t' u)"
  using assms(1)
proof (induction rule: rtranclp_induct)
  case base
  show ?case
    by (rule rtranclp.rtrancl_refl)
next
  case (step s s')
  then show ?case
    using assms(2)
    by (meson beta_reduce.App_left rtranclp.rtrancl_into_rtrancl)
qed

lemma beta_reduce_rtrancl_App_right:
  fixes t u u' :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes "beta_reduce\<^sup>*\<^sup>* u u'" and "locally_closed t"
  shows "beta_reduce\<^sup>*\<^sup>* (App t u) (App t u')"
  using assms(1)
proof (induction rule: rtranclp_induct)
  case base
  show ?case
    by (rule rtranclp.rtrancl_refl)
next
  case (step s s')
  then show ?case
    using assms(2)
    by (meson beta_reduce.App_right rtranclp.rtrancl_into_rtrancl)
qed

text \<open>To transport a reduction chain of an opened body back under its binder, we close a
  chosen fresh free variable at the corresponding de Bruijn index.\<close>

primrec close_free ::
  "nat \<Rightarrow> '\<tau> \<Rightarrow> '\<V> \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm" where
  "close_free n \<tau> x (Const c \<tau>s ts) = Const c \<tau>s ts"
| "close_free n \<tau> x (Free y \<tau>\<^sub>y) = (if x = y \<and> \<tau> = \<tau>\<^sub>y then Bound n \<tau> else Free y \<tau>\<^sub>y)"
| "close_free n \<tau> x (Bound k \<sigma>) = Bound k \<sigma>"
| "close_free n \<tau> x (App t u) =
    App (close_free n \<tau> x t) (close_free n \<tau> x u)"
| "close_free n \<tau> x (Abs \<sigma> t) = Abs \<sigma> (close_free (Suc n) \<tau> x t)"

lemma close_free_open_bound_Free_idem:
  assumes "x \<notin> free_vars t"
  shows "close_free n \<tau> x (open_bound n \<tau> (Free x \<tau>) t) = t"
  using assms by (induction t arbitrary: n) simp_all

lemma open_bound_Free_close_free_idem:
  assumes "locally_closed_at n t"
  shows "open_bound n \<tau> (Free x \<tau>) (close_free n \<tau> x t) = t"
  using assms by (induction t) simp_all

text \<open>Since \<^const>\<open>close_free\<close> only converts a \<open>Free x \<tau>\<close> node into a bound variable when its
  annotation matches the level being closed, while \<^const>\<open>subst_free\<close> matches on the name alone,
  the two only agree when every occurrence of \<open>x\<close> in the term carries the same annotation \<open>\<tau>\<close>.
  \<open>free_var_annot\<close> (defined below) collects those annotations, and is preserved (as a subset)
  along \<^const>\<open>beta_reduce\<close>, since reduction only ever duplicates or discards already-existing
  subterms.\<close>

primrec free_var_annot :: "'\<V> \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> '\<tau> set" where
  "free_var_annot x (Const c \<tau>s ts) = {}" |
  "free_var_annot x (Free y \<tau>) = (if x = y then {\<tau>} else {})" |
  "free_var_annot x (Bound k \<tau>) = {}" |
  "free_var_annot x (App t\<^sub>1 t\<^sub>2) = free_var_annot x t\<^sub>1 \<union> free_var_annot x t\<^sub>2" |
  "free_var_annot x (Abs \<tau> t) = free_var_annot x t"

lemma free_var_annot_empty_if_not_in_free_vars:
  "x \<notin> free_vars t \<Longrightarrow> free_var_annot x t = {}"
  by (induction t) auto

lemma free_var_annot_open_bound_Free_other[simp]:
  "x \<noteq> y \<Longrightarrow> free_var_annot x (open_bound n \<tau> (Free y \<tau>) t) = free_var_annot x t"
  by (induction t arbitrary: n) auto

lemma free_var_annot_open_bound_subset:
  "free_var_annot x (open_bound n \<tau> u t) \<subseteq> free_var_annot x t \<union> free_var_annot x u"
  by (induction t arbitrary: n) auto

lemma free_var_annot_beta_reduce_subset:
  fixes t t' :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
    and red: "beta_reduce t t'"
  shows "free_var_annot x t' \<subseteq> free_var_annot x t"
  using red
proof (induction rule: beta_reduce.induct)
  case (beta \<tau> b u)
  then show ?case
    using free_var_annot_open_bound_subset[of x 0 \<tau> u b] by simp
next
  case (App_left t t' u)
  then show ?case by auto
next
  case (App_right t u u')
  then show ?case by auto
next
  case (Abs \<X> \<tau> t t')
  obtain y where y_notin: "y |\<notin>| finsert x \<X>"
    using inf_vars by (metis ex_new_if_finite finite_fset)
  then have y_ne_x: "y \<noteq> x" and y_notin_\<X>: "y |\<notin>| \<X>"
    by auto
  have "free_var_annot x (open_bound 0 \<tau> (Free y \<tau>) t') \<subseteq> free_var_annot x (open_bound 0 \<tau> (Free y \<tau>) t)"
    using Abs.IH[OF y_notin_\<X>] .
  then show ?case
    by (simp add: free_var_annot_open_bound_Free_other[OF y_ne_x[symmetric]])
next
  case (Const ts i t' c \<tau>s)
  then show ?case by simp
qed

lemma free_var_annot_rtranclp_beta_reduce_subset:
  fixes t t' :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
    and reds: "beta_reduce\<^sup>*\<^sup>* t t'"
  shows "free_var_annot x t' \<subseteq> free_var_annot x t"
  using reds
proof (induction rule: rtranclp_induct)
  case base
  show ?case by simp
next
  case (step s s')
  show ?case
    using free_var_annot_beta_reduce_subset[OF inf_vars step.hyps(2)] step.IH
    by (rule subset_trans)
qed

lemma open_bound_close_free:
  assumes "x \<noteq> y" and "locally_closed_at n t" and "free_var_annot x t \<subseteq> {\<tau>}"
  shows "open_bound n \<tau> (Free y \<tau>) (close_free n \<tau> x t) =
    subst_free x (Free y \<tau>) t"
  using assms
  by (induction t arbitrary: n) (auto elim: locally_closed_at.cases simp: list.pred_set)

lemma beta_reduce_Abs_close_free:
  fixes s s' :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
    and red: "beta_reduce s s'"
    and consistent: "free_var_annot x s \<subseteq> {\<tau>}"
  shows "beta_reduce
    (Abs \<tau> (close_free 0 \<tau> x s)) (Abs \<tau> (close_free 0 \<tau> x s'))"
proof (rule beta_reduce.Abs[where \<X> = "{|x|}"])
  fix y
  assume "y |\<notin>| {|x|}"
  then have "x \<noteq> y" by simp
  have lc_s0: "locally_closed s" and lc_s0': "locally_closed s'"
    using locally_closed_if_beta_reduce[OF inf_vars red] by blast+
  have lc_s: "locally_closed_at 0 s"
    by (rule locally_closed_imp_locally_closed_at[OF inf_vars lc_s0])
  have lc_s': "locally_closed_at 0 s'"
    by (rule locally_closed_imp_locally_closed_at[OF inf_vars lc_s0'])
  have consistent': "free_var_annot x s' \<subseteq> {\<tau>}"
    using free_var_annot_beta_reduce_subset[OF inf_vars red] consistent by blast
  show "beta_reduce (open_bound 0 \<tau> (Free y \<tau>) (close_free 0 \<tau> x s))
      (open_bound 0 \<tau> (Free y \<tau>) (close_free 0 \<tau> x s'))"
    unfolding open_bound_close_free[OF \<open>x \<noteq> y\<close> lc_s consistent]
      open_bound_close_free[OF \<open>x \<noteq> y\<close> lc_s' consistent']
    by (rule beta_reduce_subst_free[OF inf_vars red locally_closed.Free])
qed

lemma beta_reduce_rtrancl_Abs_close_free:
  fixes s s' :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
    and reds: "beta_reduce\<^sup>*\<^sup>* s s'"
    and consistent: "free_var_annot x s \<subseteq> {\<tau>}"
  shows "beta_reduce\<^sup>*\<^sup>*
    (Abs \<tau> (close_free 0 \<tau> x s)) (Abs \<tau> (close_free 0 \<tau> x s'))"
  using reds
proof (induction rule: rtranclp_induct)
  case base
  show ?case by (rule rtranclp.rtrancl_refl)
next
  case (step s\<^sub>1 s\<^sub>2)
  have consistent\<^sub>1: "free_var_annot x s\<^sub>1 \<subseteq> {\<tau>}"
    using free_var_annot_rtranclp_beta_reduce_subset[OF inf_vars step.hyps(1)] consistent
    by blast
  show ?case
    using step.IH beta_reduce_Abs_close_free[OF inf_vars step.hyps(2) consistent\<^sub>1]
    by (rule rtranclp.rtrancl_into_rtrancl)
qed


lemma beta_reduce_rtrancl_Abs:
  fixes t t' :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes opened: "\<And>x. x |\<notin>| \<X> \<Longrightarrow> beta_reduce\<^sup>*\<^sup>*
    (open_bound 0 \<tau> (Free x \<tau>) t) (open_bound 0 \<tau> (Free x \<tau>) t')"
  shows "beta_reduce\<^sup>*\<^sup>* (Abs \<tau> t) (Abs \<tau> t')"
proof -
  obtain x where x_fresh_\<X>: "x |\<notin>| \<X>" and
    x_fresh: "\<And>s. s |\<in>| {|t, t'|} \<Longrightarrow> x \<notin> free_vars s"
    using fresh_for_fset_and_terms[OF inf_vars, where \<X> = \<X> and \<T> = "{|t, t'|}"] by blast
  have x_t: "x \<notin> free_vars t" and x_t': "x \<notin> free_vars t'"
    by (rule x_fresh; simp)+
  have consistent: "free_var_annot x (open_bound 0 \<tau> (Free x \<tau>) t) \<subseteq> {\<tau>}"
    using free_var_annot_open_bound_subset[of x 0 \<tau> "Free x \<tau>" t]
    by (simp add: free_var_annot_empty_if_not_in_free_vars[OF x_t])
  have "beta_reduce\<^sup>*\<^sup>*
      (Abs \<tau> (close_free 0 \<tau> x (open_bound 0 \<tau> (Free x \<tau>) t)))
      (Abs \<tau> (close_free 0 \<tau> x (open_bound 0 \<tau> (Free x \<tau>) t')))"
    by (rule beta_reduce_rtrancl_Abs_close_free[OF inf_vars opened[OF x_fresh_\<X>] consistent])
  then show ?thesis
    by (simp add: close_free_open_bound_Free_idem[OF x_t]
        close_free_open_bound_Free_idem[OF x_t'])
qed

text \<open>Lifting a reduction chain of a parameter into the constant requires maintaining local
  closure of the updated parameter list along the chain (via \<open>locally_closed_if_beta_reduce\<close>).\<close>

lemma beta_reduce_rtrancl_Const:
  fixes ts :: "('\<tau>, '\<Sigma>, '\<V>) preterm list"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes "\<forall>t \<in> set ts. locally_closed t" and "i < length ts" and "beta_reduce\<^sup>*\<^sup>* (ts ! i) t'"
  shows "beta_reduce\<^sup>*\<^sup>* (Const c \<tau>s ts) (Const c \<tau>s (ts[i := t']))"
proof -
  show ?thesis
    using assms(4)
  proof (induction rule: rtranclp_induct)
    case base
    show ?case
      using assms(3) by simp
  next
    case (step s s')
    have lc_s: "locally_closed s"
      by (rule locally_closed_if_beta_reduce(1)[OF inf_vars step.hyps(2)])
    have lc_updated: "\<forall>t \<in> set (ts[i := s]). locally_closed t"
      using assms(2,3) lc_s
      by (metis in_set_conv_nth length_list_update nth_list_update)
    have one_step:
      "beta_reduce (Const c \<tau>s (ts[i := s])) (Const c \<tau>s ((ts[i := s])[i := s']))"
    proof (rule beta_reduce.Const)
      show "\<forall>t \<in> set (ts[i := s]). locally_closed t"
        by (rule lc_updated)
      show "i < length (ts[i := s])" and "beta_reduce ((ts[i := s]) ! i) s'"
        using assms(3) step.hyps(2) by simp_all
    qed
    have "beta_reduce (Const c \<tau>s (ts[i := s])) (Const c \<tau>s (ts[i := s']))"
      using one_step assms(3) by simp
    then show ?case
      by (meson step.IH rtranclp.rtrancl_into_rtrancl)
  qed
qed


subsection \<open>Substitutivity of the argument\<close>

text \<open>The occurrences of \<open>x\<close> in \<open>t\<close> are contracted one after the other.  The
  annotation-correctness invariant ensures that the opening used in the \<open>Abs\<close> case agrees
  with the binder's type annotation.\<close>

text \<open>Substitution preserves reduction chains in locally closed terms.\<close>

lemma beta_reduce_rtrancl_subst_free_arg:
  fixes t u u' :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
    and lc_t: "locally_closed t"
    and red: "beta_reduce u u'"
  shows "beta_reduce\<^sup>*\<^sup>* (subst_free x u t) (subst_free x u' t)"
proof -
  have lc_u: "locally_closed u" and lc_u': "locally_closed u'"
    using locally_closed_if_beta_reduce[OF inf_vars red] by blast+
  show ?thesis
    using lc_t
  proof (induction arbitrary: x rule: locally_closed.induct)
    case (Const c \<tau>s ts)
    show ?case
      by simp
  next
    case (Free f)
    show ?case
    proof (cases "x = f")
      case True
      then show ?thesis
        using red by (simp add: r_into_rtranclp)
    next
      case False
      then show ?thesis by simp
    qed
  next
    case (App t1 t2)
    have lc_right: "locally_closed (subst_free x u t2)"
      by (rule locally_closed_subst_free[OF App.hyps(2) lc_u])
    have lc_left: "locally_closed (subst_free x u' t1)"
      by (rule locally_closed_subst_free[OF App.hyps(1) lc_u'])
    have left:
      "beta_reduce\<^sup>*\<^sup>* (App (subst_free x u t1) (subst_free x u t2))
        (App (subst_free x u' t1) (subst_free x u t2))"
      by (rule beta_reduce_rtrancl_App_left[OF App.IH(1) lc_right])
    have right:
      "beta_reduce\<^sup>*\<^sup>* (App (subst_free x u' t1) (subst_free x u t2))
        (App (subst_free x u' t1) (subst_free x u' t2))"
      by (rule beta_reduce_rtrancl_App_right[OF App.IH(2) lc_left])
    have "beta_reduce\<^sup>*\<^sup>* (App (subst_free x u t1) (subst_free x u t2))
        (App (subst_free x u' t1) (subst_free x u' t2))"
      using left right by (rule rtranclp_trans)
    then show ?case by simp
  next
    case (Abs \<X> \<tau> t)
    show ?case
      unfolding subst_free.simps
    proof (rule beta_reduce_rtrancl_Abs[OF inf_vars, where \<X> = "finsert x \<X>"])
      fix y
      assume y_fresh: "y |\<notin>| finsert x \<X>"
      then have x_ne_y: "x \<noteq> y" and y_fresh_\<X>: "y |\<notin>| \<X>"
        by auto
      have red_open:
        "beta_reduce\<^sup>*\<^sup>* (subst_free x u (open_bound 0 \<tau> (Free y \<tau>) t))
          (subst_free x u' (open_bound 0 \<tau> (Free y \<tau>) t))"
        by (rule Abs.IH[OF y_fresh_\<X>])
      show "beta_reduce\<^sup>*\<^sup>* (open_bound 0 \<tau> (Free y \<tau>) (subst_free x u t))
          (open_bound 0 \<tau> (Free y \<tau>) (subst_free x u' t))"
        using red_open
        by (simp add: subst_free_commutes_with_open_bound_Free[OF inf_vars x_ne_y lc_u]
            subst_free_commutes_with_open_bound_Free[OF inf_vars x_ne_y lc_u'])
    qed
  qed
qed

lemma beta_reduce_rtrancl_open_bound_arg:
  fixes b a a' :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
    and body: "body \<tau> b"
    and red: "beta_reduce a a'"
  shows "beta_reduce\<^sup>*\<^sup>* (open_bound 0 \<tau> a b) (open_bound 0 \<tau> a' b)"
proof -
  obtain \<X> :: "'\<V> fset" where opened_lc:
      "\<And>x. x |\<notin>| \<X> \<Longrightarrow> locally_closed (open_bound 0 \<tau> (Free x \<tau>) b)"
    using body unfolding body_def by blast
  obtain x where fresh_\<X>: "x |\<notin>| \<X>" and fresh_b: "x \<notin> free_vars b"
    using fresh_for_fset_and_terms[OF inf_vars, where \<X> = \<X> and \<T> = "{|b|}"]
    by blast
  have reds: "beta_reduce\<^sup>*\<^sup>* (subst_free x a (open_bound 0 \<tau> (Free x \<tau>) b))
      (subst_free x a' (open_bound 0 \<tau> (Free x \<tau>) b))"
    by (rule beta_reduce_rtrancl_subst_free_arg[
          OF inf_vars opened_lc[OF fresh_\<X>] red])
  then show ?thesis
    by (simp add: subst_free_open_bound_Free_eq_open_bound[OF fresh_b])
qed



subsection \<open>Local confluence\<close>

proposition local_confluence_beta_reduce:
  fixes t u\<^sub>1 u\<^sub>2 :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
    and red\<^sub>1: "beta_reduce t u\<^sub>1" and red\<^sub>2: "beta_reduce t u\<^sub>2"
  shows "\<exists>v. beta_reduce\<^sup>*\<^sup>* u\<^sub>1 v \<and> beta_reduce\<^sup>*\<^sup>* u\<^sub>2 v"
  using red\<^sub>1 red\<^sub>2
proof (induction arbitrary: u\<^sub>2 rule: beta_reduce.induct)
  case (beta \<tau> b a)
  from beta_reduce_App_AbsD[OF beta.prems]
  consider
    (contract) "u\<^sub>2 = open_bound 0 \<tau> a b"
    | (body_step) b' \<X> where "u\<^sub>2 = App (Abs \<tau> b') a" and
        "\<And>x. x |\<notin>| \<X> \<Longrightarrow>
          beta_reduce (open_bound 0 \<tau> (Free x \<tau>) b) (open_bound 0 \<tau> (Free x \<tau>) b')"
    | (arg_step) a' where "u\<^sub>2 = App (Abs \<tau> b) a'" and "beta_reduce a a'"
    by blast
  then show ?case
  proof cases
    case contract
    then show ?thesis
      by (metis rtranclp.rtrancl_refl)
  next
    case (body_step b' \<X>)
    have abs_red: "beta_reduce (Abs \<tau> b) (Abs \<tau> b')"
      by (rule beta_reduce.Abs[where \<X> = \<X>]) (rule body_step(2))
    have body_b': "body \<tau> b'"
      using locally_closed_if_beta_reduce(2)[OF inf_vars abs_red]
      by (simp add: locall_closed_Abs_iff_body)
    obtain y where y_fresh_\<X>: "y |\<notin>| \<X>" and
      y_fresh: "\<And>s. s |\<in>| {|b, b'|} \<Longrightarrow> y \<notin> free_vars s"
      using fresh_for_fset_and_terms[OF inf_vars, where \<X> = \<X> and \<T> = "{|b, b'|}"]
      by blast
    have opened_red:
        "beta_reduce (open_bound 0 \<tau> (Free y \<tau>) b) (open_bound 0 \<tau> (Free y \<tau>) b')"
      by (rule body_step(2)[OF y_fresh_\<X>])
    have step\<^sub>1: "beta_reduce (open_bound 0 \<tau> a b) (open_bound 0 \<tau> a b')"
    proof (rule beta_reduce_open_bound_from_fresh[
          OF inf_vars _ _ opened_red beta.hyps(2)])
      show "y \<notin> free_vars b" and "y \<notin> free_vars b'"
        by (rule y_fresh; simp)+
    qed
    have step\<^sub>2: "beta_reduce u\<^sub>2 (open_bound 0 \<tau> a b')"
      unfolding body_step(1)
      by (rule beta_reduce.beta[OF body_b' beta.hyps(2)])
    show ?thesis
      using step\<^sub>1 step\<^sub>2 by (meson r_into_rtranclp)
  next
    case (arg_step a')
    have lc_a': "locally_closed a'"
      by (rule locally_closed_if_beta_reduce(2)[OF inf_vars arg_step(2)])
    have reds\<^sub>1: "beta_reduce\<^sup>*\<^sup>* (open_bound 0 \<tau> a b) (open_bound 0 \<tau> a' b)"
      by (rule beta_reduce_rtrancl_open_bound_arg[
            OF inf_vars beta.hyps(1) arg_step(2)])
    have step\<^sub>2: "beta_reduce u\<^sub>2 (open_bound 0 \<tau> a' b)"
      unfolding arg_step(1)
      by (rule beta_reduce.beta[OF beta.hyps(1) lc_a'])
    show ?thesis
      using reds\<^sub>1 step\<^sub>2 by (meson r_into_rtranclp)
  qed
next
  case (App_left t t' u)
  from App_left.prems show ?case
  proof (cases rule: beta_reduce_AppD)
    case (redex \<tau> s)
    obtain \<X> s' where t'_eq: "t' = Abs \<tau> s'" and
      opened: "\<And>x. x |\<notin>| \<X> \<Longrightarrow>
        beta_reduce (open_bound 0 \<tau> (Free x \<tau>) s) (open_bound 0 \<tau> (Free x \<tau>) s')"
      using \<open>beta_reduce t t'\<close> unfolding redex(1)
      by (auto elim!: beta_reduce.cases)
    have body_s': "body \<tau> s'"
      using locally_closed_if_beta_reduce(2)[OF inf_vars \<open>beta_reduce t t'\<close>]
      unfolding t'_eq
      by (simp add: locall_closed_Abs_iff_body)
    obtain y where y_fresh_\<X>: "y |\<notin>| \<X>" and
      y_fresh: "\<And>r. r |\<in>| {|s, s'|} \<Longrightarrow> y \<notin> free_vars r"
      using fresh_for_fset_and_terms[OF inf_vars, where \<X> = \<X> and \<T> = "{|s, s'|}"]
      by blast
    have opened_red:
        "beta_reduce (open_bound 0 \<tau> (Free y \<tau>) s) (open_bound 0 \<tau> (Free y \<tau>) s')"
      by (rule opened[OF y_fresh_\<X>])
    have step\<^sub>1: "beta_reduce (App t' u) (open_bound 0 \<tau> u s')"
      unfolding t'_eq
      by (rule beta_reduce.beta[OF body_s' App_left.hyps(2)])
    have step\<^sub>2: "beta_reduce u\<^sub>2 (open_bound 0 \<tau> u s')"
      unfolding redex(2)
    proof (rule beta_reduce_open_bound_from_fresh[
          OF inf_vars _ _ opened_red App_left.hyps(2)])
      show "y \<notin> free_vars s" and "y \<notin> free_vars s'"
        by (rule y_fresh; simp)+
    qed
    show ?thesis
      using step\<^sub>1 step\<^sub>2 by (meson r_into_rtranclp)
  next
    case (left t'')
    obtain w where "beta_reduce\<^sup>*\<^sup>* t' w" and "beta_reduce\<^sup>*\<^sup>* t'' w"
      using App_left.IH[OF left(2)] by blast
    then have "beta_reduce\<^sup>*\<^sup>* (App t' u) (App w u)" and
        "beta_reduce\<^sup>*\<^sup>* (App t'' u) (App w u)"
      by (auto intro: beta_reduce_rtrancl_App_left[OF _ App_left.hyps(2)])
    then show ?thesis
      unfolding left(1) by blast
  next
    case (right u')
    have lc_t': "locally_closed t'"
      by (rule locally_closed_if_beta_reduce(2)[OF inf_vars App_left.hyps(1)])
    have lc_u': "locally_closed u'"
      by (rule locally_closed_if_beta_reduce(2)[OF inf_vars right(2)])
    have "beta_reduce (App t' u) (App t' u')"
      by (rule beta_reduce.App_right[OF lc_t' right(2)])
    moreover have "beta_reduce u\<^sub>2 (App t' u')"
      unfolding right(1)
      by (rule beta_reduce.App_left[OF App_left.hyps(1) lc_u'])
    ultimately show ?thesis
      by (meson r_into_rtranclp)
  qed
next
  case (App_right t u u')
  from App_right.prems show ?case
  proof (cases rule: beta_reduce_AppD)
    case (redex \<tau> s)
    have body_s: "body \<tau> s"
      using App_right.hyps(1) unfolding redex(1)
      by (simp add: locall_closed_Abs_iff_body)
    have lc_u': "locally_closed u'"
      by (rule locally_closed_if_beta_reduce(2)[OF inf_vars App_right.hyps(2)])
    have step\<^sub>1: "beta_reduce (App t u') (open_bound 0 \<tau> u' s)"
      unfolding redex(1)
      by (rule beta_reduce.beta[OF body_s lc_u'])
    have reds\<^sub>2: "beta_reduce\<^sup>*\<^sup>* u\<^sub>2 (open_bound 0 \<tau> u' s)"
      unfolding redex(2)
      by (rule beta_reduce_rtrancl_open_bound_arg[
            OF inf_vars body_s App_right.hyps(2)])
    show ?thesis
      using step\<^sub>1 reds\<^sub>2 by (meson r_into_rtranclp)
  next
    case (left t')
    have lc_t': "locally_closed t'"
      by (rule locally_closed_if_beta_reduce(2)[OF inf_vars left(2)])
    have lc_u': "locally_closed u'"
      by (rule locally_closed_if_beta_reduce(2)[OF inf_vars App_right.hyps(2)])
    have "beta_reduce (App t u') (App t' u')"
      by (rule beta_reduce.App_left[OF left(2) lc_u'])
    moreover have "beta_reduce u\<^sub>2 (App t' u')"
      unfolding left(1)
      by (rule beta_reduce.App_right[OF lc_t' App_right.hyps(2)])
    ultimately show ?thesis
      by (meson r_into_rtranclp)
  next
    case (right u'')
    obtain w where "beta_reduce\<^sup>*\<^sup>* u' w" and "beta_reduce\<^sup>*\<^sup>* u'' w"
      using App_right.IH[OF right(2)] by blast
    then have "beta_reduce\<^sup>*\<^sup>* (App t u') (App t w)" and
        "beta_reduce\<^sup>*\<^sup>* (App t u'') (App t w)"
      by (auto intro: beta_reduce_rtrancl_App_right[OF _ App_right.hyps(1)])
    then show ?thesis
      unfolding right(1) by blast
  qed
next
  case (Abs \<X> \<tau> b b')
  show ?case
  proof -
    obtain \<Y> b'' where u\<^sub>2_eq: "u\<^sub>2 = Abs \<tau> b''" and
      opened\<^sub>2: "\<And>x. x |\<notin>| \<Y> \<Longrightarrow>
        beta_reduce (open_bound 0 \<tau> (Free x \<tau>) b) (open_bound 0 \<tau> (Free x \<tau>) b'')"
      using Abs.prems by (cases rule: beta_reduce.cases) blast
    obtain x where x_fresh: "x |\<notin>| \<X> |\<union>| \<Y>" and
      x_not_free: "\<And>s. s |\<in>| {|b, b', b''|} \<Longrightarrow> x \<notin> free_vars s"
      using fresh_for_fset_and_terms[OF inf_vars, where \<X> = "\<X> |\<union>| \<Y>"
          and \<T> = "{|b, b', b''|}"] by blast
    have x_fresh_\<X>: "x |\<notin>| \<X>" and x_fresh_\<Y>: "x |\<notin>| \<Y>"
      using x_fresh by auto
    have x_b': "x \<notin> free_vars b'" and x_b'': "x \<notin> free_vars b''"
      by (rule x_not_free; simp)+
    obtain w where reds\<^sub>1:
        "beta_reduce\<^sup>*\<^sup>* (open_bound 0 \<tau> (Free x \<tau>) b') w" and
      reds\<^sub>2: "beta_reduce\<^sup>*\<^sup>* (open_bound 0 \<tau> (Free x \<tau>) b'') w"
      using Abs.IH[OF x_fresh_\<X> opened\<^sub>2[OF x_fresh_\<Y>]]
      by blast
    have consistent\<^sub>1: "free_var_annot x (open_bound 0 \<tau> (Free x \<tau>) b') \<subseteq> {\<tau>}"
      using free_var_annot_open_bound_subset[of x 0 \<tau> "Free x \<tau>" b']
      by (simp add: free_var_annot_empty_if_not_in_free_vars[OF x_b'])
    have consistent\<^sub>2: "free_var_annot x (open_bound 0 \<tau> (Free x \<tau>) b'') \<subseteq> {\<tau>}"
      using free_var_annot_open_bound_subset[of x 0 \<tau> "Free x \<tau>" b'']
      by (simp add: free_var_annot_empty_if_not_in_free_vars[OF x_b''])
    have closed\<^sub>1:
      "beta_reduce\<^sup>*\<^sup>* (Abs \<tau> b') (Abs \<tau> (close_free 0 \<tau> x w))"
      using beta_reduce_rtrancl_Abs_close_free[OF inf_vars reds\<^sub>1 consistent\<^sub>1]
      by (simp add: close_free_open_bound_Free_idem[OF x_b'])
    have closed\<^sub>2:
      "beta_reduce\<^sup>*\<^sup>* u\<^sub>2 (Abs \<tau> (close_free 0 \<tau> x w))"
      using beta_reduce_rtrancl_Abs_close_free[OF inf_vars reds\<^sub>2 consistent\<^sub>2]
      unfolding u\<^sub>2_eq
      by (simp add: close_free_open_bound_Free_idem[OF x_b''])
    show ?thesis
      using closed\<^sub>1 closed\<^sub>2 by blast
  qed
next
  case (Const ts i t\<^sub>1' c \<tau>s)
  obtain j t\<^sub>2' where j_lt: "j < length ts" and red\<^sub>2: "beta_reduce (ts ! j) t\<^sub>2'" and
    u\<^sub>2_eq: "u\<^sub>2 = Const c \<tau>s (ts[j := t\<^sub>2'])"
    using Const.prems by (elim beta_reduce_ConstD)
  show ?case
  proof (cases "i = j")
    case True
    have red\<^sub>2_i: "beta_reduce (ts ! i) t\<^sub>2'"
      using red\<^sub>2 True by simp
    obtain w where reds\<^sub>1: "beta_reduce\<^sup>*\<^sup>* t\<^sub>1' w" and
      reds\<^sub>2: "beta_reduce\<^sup>*\<^sup>* t\<^sub>2' w"
      using Const.IH[OF red\<^sub>2_i] by blast
    have lc_t\<^sub>1': "locally_closed t\<^sub>1'"
      by (rule locally_closed_if_beta_reduce(2)[OF inf_vars Const.hyps(3)])
    have lc_t\<^sub>2': "locally_closed t\<^sub>2'"
      by (rule locally_closed_if_beta_reduce(2)[OF inf_vars red\<^sub>2])
    have lc_ts\<^sub>1: "\<forall>t \<in> set (ts[i := t\<^sub>1']). locally_closed t"
      using Const.hyps(1,2) lc_t\<^sub>1'
      by (metis in_set_conv_nth length_list_update nth_list_update)
    have lc_ts\<^sub>2: "\<forall>t \<in> set (ts[i := t\<^sub>2']). locally_closed t"
      using Const.hyps(1,2) lc_t\<^sub>2'
      by (metis in_set_conv_nth length_list_update nth_list_update)
    have lifted\<^sub>1:
      "beta_reduce\<^sup>*\<^sup>* (Const c \<tau>s (ts[i := t\<^sub>1'])) (Const c \<tau>s (ts[i := w]))"
    proof -
      have raw:
        "beta_reduce\<^sup>*\<^sup>* (Const c \<tau>s (ts[i := t\<^sub>1']))
          (Const c \<tau>s ((ts[i := t\<^sub>1'])[i := w]))"
      proof (rule beta_reduce_rtrancl_Const[OF inf_vars lc_ts\<^sub>1])
        show "i < length (ts[i := t\<^sub>1'])"
          using Const.hyps(2) by simp
        show "beta_reduce\<^sup>*\<^sup>* ((ts[i := t\<^sub>1']) ! i) w"
          using Const.hyps(2) reds\<^sub>1 by simp
      qed
      show ?thesis
        using raw Const.hyps(2) by simp
    qed
    have lifted\<^sub>2:
      "beta_reduce\<^sup>*\<^sup>* u\<^sub>2 (Const c \<tau>s (ts[i := w]))"
    proof -
      have raw:
        "beta_reduce\<^sup>*\<^sup>* (Const c \<tau>s (ts[i := t\<^sub>2']))
          (Const c \<tau>s ((ts[i := t\<^sub>2'])[i := w]))"
      proof (rule beta_reduce_rtrancl_Const[OF inf_vars lc_ts\<^sub>2])
        show "i < length (ts[i := t\<^sub>2'])"
          using Const.hyps(2) by simp
        show "beta_reduce\<^sup>*\<^sup>* ((ts[i := t\<^sub>2']) ! i) w"
          using Const.hyps(2) reds\<^sub>2 by simp
      qed
      show ?thesis
        using raw u\<^sub>2_eq True Const.hyps(2) by simp
    qed
    show ?thesis
      using lifted\<^sub>1 lifted\<^sub>2 by blast
  next
    case False
    have lc_t\<^sub>1': "locally_closed t\<^sub>1'"
      by (rule locally_closed_if_beta_reduce(2)[OF inf_vars Const.hyps(3)])
    have lc_t\<^sub>2': "locally_closed t\<^sub>2'"
      by (rule locally_closed_if_beta_reduce(2)[OF inf_vars red\<^sub>2])
    have lc_ts\<^sub>1: "\<forall>t \<in> set (ts[i := t\<^sub>1']). locally_closed t"
      using Const.hyps(1,2) lc_t\<^sub>1'
      by (metis in_set_conv_nth length_list_update nth_list_update)
    have lc_ts\<^sub>2: "\<forall>t \<in> set (ts[j := t\<^sub>2']). locally_closed t"
      using Const.hyps(1) j_lt lc_t\<^sub>2'
      by (metis in_set_conv_nth length_list_update nth_list_update)
    have step\<^sub>1:
      "beta_reduce (Const c \<tau>s (ts[i := t\<^sub>1']))
        (Const c \<tau>s ((ts[i := t\<^sub>1'])[j := t\<^sub>2']))"
    proof (rule beta_reduce.Const)
      show "\<forall>t \<in> set (ts[i := t\<^sub>1']). locally_closed t"
        by (rule lc_ts\<^sub>1)
      show "j < length (ts[i := t\<^sub>1'])"
        using j_lt by simp
      show "beta_reduce ((ts[i := t\<^sub>1']) ! j) t\<^sub>2'"
        using red\<^sub>2 False j_lt Const.hyps(2) by simp
    qed
    have step\<^sub>2_raw:
      "beta_reduce (Const c \<tau>s (ts[j := t\<^sub>2']))
        (Const c \<tau>s ((ts[j := t\<^sub>2'])[i := t\<^sub>1']))"
    proof (rule beta_reduce.Const)
      show "\<forall>t \<in> set (ts[j := t\<^sub>2']). locally_closed t"
        by (rule lc_ts\<^sub>2)
      show "i < length (ts[j := t\<^sub>2'])"
        using Const.hyps(2) by simp
      show "beta_reduce ((ts[j := t\<^sub>2']) ! i) t\<^sub>1'"
        using Const.hyps(2,3) False j_lt by simp
    qed
    have step\<^sub>2:
      "beta_reduce u\<^sub>2 (Const c \<tau>s ((ts[i := t\<^sub>1'])[j := t\<^sub>2']))"
      using step\<^sub>2_raw u\<^sub>2_eq False
      by (simp add: list_update_swap)
    show ?thesis
      using step\<^sub>1 step\<^sub>2 by (meson r_into_rtranclp)
  qed
qed

end