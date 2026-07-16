theory LNLC_Reduction
  imports LNLC_Term
begin

section \<open>One-step \<open>\<beta>\<close>-reduction\<close>

text \<open>One-step \<open>\<beta>\<close>-reduction on \<open>\<lambda>\<close>-preterms. The relation \<open>beta_reduce t u\<close>
  expresses that \<open>t\<close> \<open>\<beta>\<close>-reduces to \<open>u\<close> in exactly one step. The first rule is the
  \<open>\<beta>\<close>-rule proper; the remaining rules are congruence (compatibility) rules that allow the
  reduction to take place anywhere inside a term, including inside a constant's parameters.\<close>

inductive beta_reduce :: "('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> bool" where
  beta: "beta_reduce (App (Abs \<tau> t) u) (open_bound 0 \<tau> u t)"
    if "body \<tau> t" and "locally_closed u" |

  App_left: "beta_reduce (App t u) (App t' u)"
    if "beta_reduce t t'" and "locally_closed u" |

  App_right: "beta_reduce (App t u) (App t u')"
    if "locally_closed t" "beta_reduce u u'" |

  Abs: "beta_reduce (Abs \<tau> t) (Abs \<tau> t')"
    if "\<And>x. x |\<notin>| \<X> \<Longrightarrow> beta_reduce (open_bound 0 \<tau> (Free x \<tau>) t) (open_bound 0 \<tau> (Free x \<tau>) t')" |

  Const: "beta_reduce (Const c \<tau>s ts) (Const c \<tau>s (ts[i := t']))"
    if "\<forall>t \<in> set ts. locally_closed t" and "i < length ts" and "beta_reduce (ts ! i) t'"

text \<open>Full reduction is the reflexive-transitive closure \<open>beta_reduce\<^sup>*\<^sup>*\<close>. A preterm is in
  normal form when no further \<open>\<beta>\<close>-step is possible; reducing a preterm fully means following this
  closure until a \<open>beta_normal\<close> preterm is reached (if one exists---see the note on strong
  normalization below).\<close>

definition beta_normal :: "('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> bool" where
  "beta_normal t \<longleftrightarrow> (\<nexists>u. beta_reduce t u)"

lemma locally_closed_if_beta_reduce:
  fixes t t' :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes "beta_reduce t t'"
  shows "locally_closed t" "locally_closed t'"
  unfolding atomize_conj
  using assms(2)
proof (induction rule: beta_reduce.induct)
  case (beta t \<tau> u)
  then show ?case
    by (simp add: locally_closed_App_iff locall_closed_Abs_iff_body
        locally_closed_open_bound[OF inf_vars])
next
  case (App_left t t' u)
  then show ?case
    by (simp add: locally_closed_App_iff)
next
  case (App_right t u u')
  then show ?case
    by (simp add: locally_closed_App_iff)
next
  case (Abs \<X> \<tau> t t')
  show ?case
  proof
    show "locally_closed (Abs \<tau> t)"
    proof (rule locally_closed.Abs[where \<X> = \<X>])
      fix x
      assume "x |\<notin>| \<X>"
      then show "locally_closed (open_bound 0 \<tau> (Free x \<tau>) t)"
        using Abs.IH by blast
    qed
  next
    show "locally_closed (Abs \<tau> t')"
    proof (rule locally_closed.Abs[where \<X> = \<X>])
      fix x
      assume "x |\<notin>| \<X>"
      then show "locally_closed (open_bound 0 \<tau> (Free x \<tau>) t')"
        using Abs.IH by blast
    qed
  qed
next
  case (Const ts i t' c \<tau>s)
  then show ?case
    unfolding locally_closed_Const_iff
    using in_set_conv_nth length_list_update nth_list_update
    by (metis in_set_conv_nth length_list_update nth_list_update)
qed




subsection \<open>Inversion rules\<close>

text \<open>Inverting a \<open>\<beta>\<close>-step out of an application: either the application is a redex, or the step
  is taken in its left or right subterm.\<close>

lemma beta_reduce_AppD:
  assumes "beta_reduce (App a b) v"
  obtains (redex) \<tau> s where "a = Abs \<tau> s" and "v = open_bound 0 \<tau> b s"
    | (left) a' where "v = App a' b" and "beta_reduce a a'"
    | (right) b' where "v = App a b'" and "beta_reduce b b'"
  using assms by (auto elim: beta_reduce.cases)

lemma beta_reduce_App_AbsD:
  assumes "beta_reduce (App (Abs \<tau>\<^sub>1 t) u) v"
  shows "v = open_bound 0 \<tau>\<^sub>1 u t
    \<or> (\<exists>t'. v = App (Abs \<tau>\<^sub>1 t') u \<and> (\<exists>\<X>. \<forall>x. x |\<notin>| \<X> \<longrightarrow> beta_reduce (open_bound 0 \<tau>\<^sub>1 (Free x \<tau>\<^sub>1) t) (open_bound 0 \<tau>\<^sub>1 (Free x \<tau>\<^sub>1) t')))
    \<or> (\<exists>u'. v = App (Abs \<tau>\<^sub>1 t) u' \<and> beta_reduce u u')"
  using assms
proof (cases rule: beta_reduce_AppD)
  case (redex \<tau> s)
  then show ?thesis by auto
next
  case (left a')
  from \<open>beta_reduce (Abs \<tau>\<^sub>1 t) a'\<close> obtain \<X> t'
    where "a' = Abs \<tau>\<^sub>1 t'" and
      "\<And>x. x |\<notin>| \<X> \<Longrightarrow> beta_reduce (open_bound 0 \<tau>\<^sub>1 (Free x \<tau>\<^sub>1) t) (open_bound 0 \<tau>\<^sub>1 (Free x \<tau>\<^sub>1) t')"
    by (auto elim!: beta_reduce.cases)
  then show ?thesis
    using \<open>v = App a' u\<close>
    by blast
next
  case (right b')
  then show ?thesis by blast
qed

text \<open>Inverting a \<open>\<beta>\<close>-step out of a constant: exactly one parameter is reduced.\<close>

lemma beta_reduce_ConstD:
  assumes "beta_reduce (Const c \<tau>s ts) v"
  obtains i t' where "i < length ts" and "beta_reduce (ts ! i) t'"
    and "v = Const c \<tau>s (ts[i := t'])"
  using assms by (auto elim: beta_reduce.cases)

lemma beta_reduce_open_bound:
  fixes t :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
    and red: "beta_reduce t t'"
  shows "beta_reduce (open_bound n \<tau> u t) (open_bound n \<tau> u t')"
  using red locally_closed_if_beta_reduce[OF inf_vars red]
  by (simp add: open_bound_ident_if_locally_closed[OF inf_vars])

lemma beta_reduce_subst_free:
  fixes t u :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes red: "beta_reduce t t'"
  assumes lc_u: "locally_closed u"
  shows "beta_reduce (subst_free x u t) (subst_free x u t')"
  using red lc_u
proof (induction arbitrary: x u rule: beta_reduce.induct)
  case beta
  then show ?case
    by (auto intro: beta_reduce.beta
      simp: subst_open[OF inf_vars] body_subst_free locally_closed_subst_free)
next
  case App_left
  then show ?case
    by (auto intro: beta_reduce.App_left
      simp: locally_closed_subst_free)
next
  case App_right
  then show ?case
    by (auto intro: beta_reduce.App_right
      simp: locally_closed_subst_free)
next
  case (Abs \<X> \<tau> t t')
  show ?case
    unfolding subst_free.simps
  proof (rule beta_reduce.Abs[where \<X> = "finsert x \<X>"])
    fix y
    assume y_fresh: "y |\<notin>| finsert x \<X>"
    have x_ne_y: "x \<noteq> y" and y_fresh_\<X>: "y |\<notin>| \<X>"
      using y_fresh by auto
    have red_subst:
      "beta_reduce (subst_free x u (open_bound 0 \<tau> (Free y \<tau>) t))
        (subst_free x u (open_bound 0 \<tau> (Free y \<tau>) t'))"
      by (rule Abs.IH[OF y_fresh_\<X> Abs.prems])
    show "beta_reduce (open_bound 0 \<tau> (Free y \<tau>) (subst_free x u t))
        (open_bound 0 \<tau> (Free y \<tau>) (subst_free x u t'))"
      using red_subst
      by (simp add: subst_free_commutes_with_open_bound_Free[OF inf_vars x_ne_y Abs.prems])
  qed
next
  case Const
  then show ?case
    by (auto intro: beta_reduce.Const)
qed


text \<open>A reduction between openings by a fresh free variable can be transported to an opening
  by any locally closed term.\<close>

lemma beta_reduce_open_bound_from_fresh:
  fixes t t' v :: "(_, _, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes fresh: "x \<notin> free_vars t" "x \<notin> free_vars t'"
  assumes opened_red:
    "beta_reduce (open_bound n \<tau> (Free x \<tau>) t) (open_bound n \<tau> (Free x \<tau>) t')"
  assumes lc_v: "locally_closed v"
  shows "beta_reduce (open_bound n \<tau> v t) (open_bound n \<tau> v t')"
proof -
  have "beta_reduce
      (subst_free x v (open_bound n \<tau> (Free x \<tau>) t))
      (subst_free x v (open_bound n \<tau> (Free x \<tau>) t'))"
    by (rule beta_reduce_subst_free[OF inf_vars opened_red lc_v])
  then show ?thesis
    by (simp add: subst_free_open_bound_Free_eq_open_bound fresh)
qed


section \<open>\<^const>\<open>beta_reduce\<close> is NOT strongly normalizing\<close>

text \<open>A relation is strongly normalizing when it admits no infinite chain, i.e. every reduction
  sequence eventually reaches a normal form.\<close>

definition strongly_normalizing :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "strongly_normalizing r \<longleftrightarrow> (\<nexists>f. \<forall>i. r (f i) (f (Suc i)))"

text \<open>\<^bold>\<open>Important.\<close> On untyped \<open>\<lambda>\<close>-preterms, \<open>beta_reduce\<close> is \<^emph>\<open>not\<close> strongly
  normalizing, so the property requested cannot be proved as stated. The standard witness is the
  self-replicating term \<open>\<omega> = \<lambda>x. x x\<close>: the application \<open>\<omega> \<omega>\<close> \<open>\<beta>\<close>-reduces to itself, yielding an
  infinite reduction sequence. Strong normalization only holds once reduction is restricted to
  \<^emph>\<open>well-typed\<close> preterms (via the typing judgment \<open>has_type\<close> from theory \<open>LNLC_Typing\<close>);
  that is a substantial, separate development (Tait/Girard reducibility) and is left as future
  work.\<close>

definition omega :: "'\<tau> \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm" where
  "omega \<tau> = Abs \<tau> (App (Bound 0 \<tau>) (Bound 0 \<tau>))"

lemma beta_reduce_omega_omega:
  "beta_reduce (App (omega \<tau>) (omega \<tau>)) (App (omega \<tau>) (omega \<tau>))"
proof -
  have body: "body \<tau> (App (Bound 0 \<tau>) (Bound 0 \<tau>))"
    by (auto simp: body_def intro: locally_closed.intros)
  have lc: "locally_closed (omega \<tau>)"
    by (simp add: omega_def locall_closed_Abs_iff_body body)
  have "beta_reduce (App (omega \<tau>) (omega \<tau>))
      (open_bound 0 \<tau> (omega \<tau>) (App (Bound 0 \<tau>) (Bound 0 \<tau>)))"
    unfolding omega_def
    by (rule beta_reduce.beta[OF body]) (simp add: locall_closed_Abs_iff_body body)
  then show ?thesis
    by simp
qed

lemma not_strongly_normalizing_beta_reduce:
  "\<not> strongly_normalizing (beta_reduce :: ('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> _)"
  unfolding strongly_normalizing_def not_not
proof (intro exI[of _ "\<lambda>_. App (omega undefined) (omega undefined)"] allI)
  fix i
  show "beta_reduce ((\<lambda>_. App (omega undefined) (omega undefined)) i)
      ((\<lambda>_. App (omega undefined) (omega undefined)) (Suc i) :: ('\<tau>, '\<Sigma>, '\<V>) preterm)"
    by (simp add: beta_reduce_omega_omega)
qed

end
