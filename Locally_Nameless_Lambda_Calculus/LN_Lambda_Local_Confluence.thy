theory LN_Lambda_Local_Confluence
  imports LN_Lambda_Strong_Normalization
begin

section \<open>Local confluence of \<open>\<beta>\<close>-reduction\<close>

text \<open>Proof sketch of local confluence (weak confluence) of \<^const>\<open>beta_reduce\<close>: any two one-step
  reducts of a preterm can be joined by finitely many reduction steps. Together with strong
  normalization of the well-typed fragment and Newman's lemma, this would yield confluence of that
  fragment.

  The proof is by rule induction on the first reduction and inversion of the second one. The
  \<open>sorry\<close>-ed lemmas concentrate the missing infrastructure:
  \<^item> substitutivity of the argument (\<open>beta_reduces_subst_free_arg\<close>): reducing \<open>u\<close> to \<open>u'\<close> inside
    \<open>subst_free x u t\<close> requires contracting the (possibly many) occurrences of \<open>x\<close> one after the
    other;
  \<^item> congruence of \<^const>\<open>beta_reduces\<close> under \<^const>\<open>Abs\<close> (\<open>beta_reduces_Abs\<close>): transporting a
    reduction chain of an opened body back under the binder requires a variable-closing operation
    (\<open>close_var\<close>) and renaming lemmas that the development does not yet provide;
  \<^item> congruence of \<^const>\<open>beta_reduces\<close> under \<^const>\<open>Const\<close> (\<open>beta_reduces_Const\<close>) and the list
    bookkeeping of the \<open>Const\<close> case.\<close>


subsection \<open>Congruence rules for \<^const>\<open>beta_reduces\<close>\<close>

lemma beta_reduces_App_left:
  fixes t t' u :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes "beta_reduces t t'" and "locally_closed u"
  shows "beta_reduces (App t u) (App t' u)"
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

lemma beta_reduces_App_right:
  fixes t u u' :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes "beta_reduces u u'" and "locally_closed t"
  shows "beta_reduces (App t u) (App t u')"
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

text \<open>Transporting a reduction chain of the opened body back under the binder requires writing
  every intermediate term of the chain as an opening of some body, i.e. a variable-closing
  operation \<open>close_var\<close> together with renaming lemmas, which the development does not yet
  provide.\<close>

lemma beta_reduces_Abs:
  fixes t t' :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes "\<And>x. x |\<notin>| \<X> \<Longrightarrow> beta_reduces (subst_bound 0 (Free x) t) (subst_bound 0 (Free x) t')"
  shows "beta_reduces (Abs \<tau> t) (Abs \<tau> t')"
  sorry

text \<open>Lifting a reduction chain of a parameter into the constant requires maintaining local
  closure of the updated parameter list along the chain (via \<open>locally_closed_if_beta_reduce\<close>).\<close>

lemma beta_reduces_Const:
  fixes ts :: "('\<tau>, '\<Sigma>, '\<V>) preterm list"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes "\<forall>t \<in> set ts. locally_closed t" and "i < length ts" and "beta_reduces (ts ! i) t'"
  shows "beta_reduces (Const c \<tau>s ts) (Const c \<tau>s (ts[i := t']))"
  sorry


subsection \<open>Substitutivity of the argument\<close>

text \<open>The occurrences of \<open>x\<close> in \<open>t\<close> are contracted one after the other; the proof should be by
  induction on \<open>locally_closed t\<close>, with the \<open>Abs\<close> case requiring the commutation of
  \<^const>\<open>subst_free\<close> with opening (\<open>subst_free_commutes_with_subst_bound_Free\<close>) and the
  congruence rule \<open>beta_reduces_Abs\<close> above.\<close>

lemma beta_reduces_subst_free_arg:
  fixes t u u' :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes "locally_closed t" and "beta_reduce u u'"
  shows "beta_reduces (subst_free x u t) (subst_free x u' t)"
  sorry

lemma beta_reduces_subst_bound_arg:
  fixes b a a' :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes red: "beta_reduce a a'" and body_b: "body b"
  shows "beta_reduces (subst_bound 0 a b) (subst_bound 0 a' b)"
proof -
  obtain \<X> :: "'\<V> fset" where
    opened_lc: "\<And>x. x |\<notin>| \<X> \<Longrightarrow> locally_closed (subst_bound 0 (Free x) b)"
    using body_b unfolding body_def by blast
  obtain x where x_fresh_\<X>: "x |\<notin>| \<X>" and x_fresh: "\<And>s. s |\<in>| {|b|} \<Longrightarrow> x \<notin> free_vars s"
    using fresh_for_fset_and_terms[OF inf_vars, where \<X> = \<X> and \<T> = "{|b|}"] by blast
  have x_b: "x \<notin> free_vars b"
    by (rule x_fresh) simp
  have "beta_reduces (subst_free x a (subst_bound 0 (Free x) b))
      (subst_free x a' (subst_bound 0 (Free x) b))"
    by (rule beta_reduces_subst_free_arg[OF inf_vars opened_lc[OF x_fresh_\<X>] red])
  then show ?thesis
    unfolding subst_free_subst_bound_Free_eq_subst_bound[OF x_b] .
qed


subsection \<open>Local confluence\<close>

theorem local_confluence_beta_reduce:
  fixes t u\<^sub>1 u\<^sub>2 :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes "beta_reduce t u\<^sub>1" and "beta_reduce t u\<^sub>2"
  shows "\<exists>v. beta_reduces u\<^sub>1 v \<and> beta_reduces u\<^sub>2 v"
  using assms(2,3)
proof (induction arbitrary: u\<^sub>2 rule: beta_reduce.induct)
  case (beta b a \<tau>)
  from beta_reduce_App_AbsD[OF beta.prems]
  consider
    (contract) "u\<^sub>2 = subst_bound 0 a b"
    | (body_step) b' \<X> where "u\<^sub>2 = App (Abs \<tau> b') a" and
        "\<And>x. x |\<notin>| \<X> \<Longrightarrow> beta_reduce (subst_bound 0 (Free x) b) (subst_bound 0 (Free x) b')"
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
    have body_b': "body b'"
      using locally_closed_if_beta_reduce(2)[OF inf_vars abs_red]
      by (simp add: locall_closed_Abs_iff_body)
    obtain y where y_fresh_\<X>: "y |\<notin>| \<X>" and
      y_fresh: "\<And>s. s |\<in>| {|b, b'|} \<Longrightarrow> y \<notin> free_vars s"
      using fresh_for_fset_and_terms[OF inf_vars, where \<X> = \<X> and \<T> = "{|b, b'|}"] by blast
    have step\<^sub>1: "beta_reduce (subst_bound 0 a b) (subst_bound 0 a b')"
    proof (rule beta_reduce_subst_bound_from_fresh[OF inf_vars _ _ body_step(2)[OF y_fresh_\<X>]
          \<open>locally_closed a\<close>])
      show "y \<notin> free_vars b" and "y \<notin> free_vars b'"
        by (rule y_fresh; simp)+
    qed
    have step\<^sub>2: "beta_reduce u\<^sub>2 (subst_bound 0 a b')"
      unfolding body_step(1)
      by (rule beta_reduce.beta[OF body_b' \<open>locally_closed a\<close>])
    show ?thesis
      using step\<^sub>1 step\<^sub>2 by (meson r_into_rtranclp)
  next
    case (arg_step a')
    have lc_a': "locally_closed a'"
      by (rule locally_closed_if_beta_reduce(2)[OF inf_vars arg_step(2)])
    have reds\<^sub>1: "beta_reduces (subst_bound 0 a b) (subst_bound 0 a' b)"
      by (rule beta_reduces_subst_bound_arg[OF inf_vars arg_step(2) \<open>body b\<close>])
    have step\<^sub>2: "beta_reduce u\<^sub>2 (subst_bound 0 a' b)"
      unfolding arg_step(1)
      by (rule beta_reduce.beta[OF \<open>body b\<close> lc_a'])
    show ?thesis
      using reds\<^sub>1 step\<^sub>2 by (meson r_into_rtranclp)
  qed
next
  case (App_left t t' u)
  from App_left.prems show ?case
  proof (cases rule: beta_reduce_AppD)
    case (redex \<tau> s)
    obtain \<X> s' where t'_eq: "t' = Abs \<tau> s'" and
      opened: "\<And>x. x |\<notin>| \<X> \<Longrightarrow> beta_reduce (subst_bound 0 (Free x) s) (subst_bound 0 (Free x) s')"
      using \<open>beta_reduce t t'\<close> unfolding redex(1)
      by (auto elim!: beta_reduce.cases)
    have body_s': "body s'"
      using locally_closed_if_beta_reduce(2)[OF inf_vars \<open>beta_reduce t t'\<close>]
      unfolding t'_eq
      by (simp add: locall_closed_Abs_iff_body)
    obtain y where y_fresh_\<X>: "y |\<notin>| \<X>" and
      y_fresh: "\<And>r. r |\<in>| {|s, s'|} \<Longrightarrow> y \<notin> free_vars r"
      using fresh_for_fset_and_terms[OF inf_vars, where \<X> = \<X> and \<T> = "{|s, s'|}"] by blast
    have step\<^sub>1: "beta_reduce (App t' u) (subst_bound 0 u s')"
      unfolding t'_eq
      by (rule beta_reduce.beta[OF body_s' \<open>locally_closed u\<close>])
    have step\<^sub>2: "beta_reduce u\<^sub>2 (subst_bound 0 u s')"
      unfolding redex(2)
    proof (rule beta_reduce_subst_bound_from_fresh[OF inf_vars _ _ opened[OF y_fresh_\<X>]
          \<open>locally_closed u\<close>])
      show "y \<notin> free_vars s" and "y \<notin> free_vars s'"
        by (rule y_fresh; simp)+
    qed
    show ?thesis
      using step\<^sub>1 step\<^sub>2 by (meson r_into_rtranclp)
  next
    case (left t'')
    obtain w where "beta_reduces t' w" and "beta_reduces t'' w"
      using App_left.IH[OF left(2)] by blast
    then have "beta_reduces (App t' u) (App w u)" and "beta_reduces (App t'' u) (App w u)"
      by (auto intro: beta_reduces_App_left[OF _ \<open>locally_closed u\<close>])
    then show ?thesis
      unfolding left(1) by blast
  next
    case (right u')
    have lc_t': "locally_closed t'"
      by (rule locally_closed_if_beta_reduce(2)[OF inf_vars \<open>beta_reduce t t'\<close>])
    have lc_u': "locally_closed u'"
      by (rule locally_closed_if_beta_reduce(2)[OF inf_vars right(2)])
    have "beta_reduce (App t' u) (App t' u')"
      by (rule beta_reduce.App_right[OF lc_t' right(2)])
    moreover have "beta_reduce u\<^sub>2 (App t' u')"
      unfolding right(1)
      by (rule beta_reduce.App_left[OF \<open>beta_reduce t t'\<close> lc_u'])
    ultimately show ?thesis
      by (meson r_into_rtranclp)
  qed
next
  case (App_right t u u')
  from App_right.prems show ?case
  proof (cases rule: beta_reduce_AppD)
    case (redex \<tau> s)
    have body_s: "body s"
      using \<open>locally_closed t\<close> unfolding redex(1)
      by (simp add: locall_closed_Abs_iff_body)
    have lc_u': "locally_closed u'"
      by (rule locally_closed_if_beta_reduce(2)[OF inf_vars \<open>beta_reduce u u'\<close>])
    have step\<^sub>1: "beta_reduce (App t u') (subst_bound 0 u' s)"
      unfolding redex(1)
      by (rule beta_reduce.beta[OF body_s lc_u'])
    have reds\<^sub>2: "beta_reduces u\<^sub>2 (subst_bound 0 u' s)"
      unfolding redex(2)
      by (rule beta_reduces_subst_bound_arg[OF inf_vars \<open>beta_reduce u u'\<close> body_s])
    show ?thesis
      using step\<^sub>1 reds\<^sub>2 by (meson r_into_rtranclp)
  next
    case (left t')
    have lc_t': "locally_closed t'"
      by (rule locally_closed_if_beta_reduce(2)[OF inf_vars left(2)])
    have lc_u': "locally_closed u'"
      by (rule locally_closed_if_beta_reduce(2)[OF inf_vars \<open>beta_reduce u u'\<close>])
    have "beta_reduce (App t u') (App t' u')"
      by (rule beta_reduce.App_left[OF left(2) lc_u'])
    moreover have "beta_reduce u\<^sub>2 (App t' u')"
      unfolding left(1)
      by (rule beta_reduce.App_right[OF lc_t' \<open>beta_reduce u u'\<close>])
    ultimately show ?thesis
      by (meson r_into_rtranclp)
  next
    case (right u'')
    then show ?thesis
      by (meson App_right.IH App_right.hyps(1) beta_reduces_App_right)
  qed
next
  case (Abs \<X> b b' \<tau>)
  txt \<open>Both reductions act under the binder. The induction hypothesis joins the two opened bodies
    for any variable outside \<open>\<X>\<close>, but transporting the join back under \<open>Abs\<close> requires
    \<open>beta_reduces_Abs\<close> and hence the missing \<open>close_var\<close> infrastructure.\<close>
  show ?case
    sorry
next
  case (Const ts i t\<^sub>1' c \<tau>s)
  obtain j t\<^sub>2' where j_lt: "j < length ts" and red\<^sub>2: "beta_reduce (ts ! j) t\<^sub>2'" and
    u\<^sub>2_eq: "u\<^sub>2 = Const c \<tau>s (ts[j := t\<^sub>2'])"
    using Const.prems by (elim beta_reduce_ConstD)
  show ?case
  proof (cases "i = j")
    case True
    txt \<open>Same parameter: the induction hypothesis joins \<open>t\<^sub>1'\<close> and \<open>t\<^sub>2'\<close> at some \<open>w\<close>; join at
      \<open>Const c \<tau>s (ts[i := w])\<close>, lifting both chains with \<open>beta_reduces_Const\<close>. Local closure of
      the updated lists follows from \<open>locally_closed_if_beta_reduce\<close>.\<close>
    show ?thesis
      sorry
  next
    case False
    txt \<open>Distinct parameters: the two steps commute; join at
      \<open>Const c \<tau>s (ts[i := t\<^sub>1', j := t\<^sub>2'])\<close> in one step from each side.\<close>
    show ?thesis
      sorry
  qed
qed

end
