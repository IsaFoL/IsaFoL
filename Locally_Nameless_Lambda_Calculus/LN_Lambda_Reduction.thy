theory LN_Lambda_Reduction
  imports LN_Lambda_Term
begin

section \<open>One-step \<open>\<beta>\<close>-reduction\<close>

text \<open>One-step \<open>\<beta>\<close>-reduction on \<open>\<lambda>\<close>-preterms. The relation \<open>beta_reduce t u\<close>
  expresses that \<open>t\<close> \<open>\<beta>\<close>-reduces to \<open>u\<close> in exactly one step. The first rule is the
  \<open>\<beta>\<close>-rule proper; the remaining rules are congruence (compatibility) rules that allow the
  reduction to take place anywhere inside a term, including inside a constant's parameters.\<close>

inductive beta_reduce :: "('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> bool" where
  beta: "beta_reduce (App (Abs \<tau> t) u) (subst_bound 0 u t)"
    if "body t" and "locally_closed u"|

  App_left: "beta_reduce (App t u) (App t' u)"
    if "beta_reduce t t'" and "locally_closed u" |

  App_right: "beta_reduce (App t u) (App t u')"
    if "locally_closed t" "beta_reduce u u'" |

  Abs: "beta_reduce (Abs \<tau> t) (Abs \<tau> t')"
    if "\<And>x. x |\<notin>| \<X> \<Longrightarrow> beta_reduce (subst_bound 0 (Free x) t) (subst_bound 0 (Free x) t')" |

  Const: "beta_reduce (Const c \<tau>s ts) (Const c \<tau>s (ts[i := t']))"
    if "\<forall>t \<in> set ts. locally_closed t" and "i < length ts" and "beta_reduce (ts ! i) t'"

text \<open>Full reduction is the reflexive-transitive closure. A preterm is in normal form when no
  further \<open>\<beta>\<close>-step is possible; reducing a preterm fully means following \<open>beta_reduces\<close>
  until a \<open>beta_normal\<close> preterm is reached (if one exists---see the note on strong
  normalization below).\<close>

abbreviation beta_reduces :: "('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> bool" where
  "beta_reduces \<equiv> beta_reduce\<^sup>*\<^sup>*"

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
        locally_closed_subst_bound[OF inf_vars])
next
  case (App_left t t' u)
  then show ?case
    by (simp add: locally_closed_App_iff)
next
  case (App_right t u u')
  then show ?case
    by (simp add: locally_closed_App_iff)
next
  case (Abs \<X> t t' \<tau>)
  then show ?case
    by (metis body_def locall_closed_Abs_iff_body)
next
  case (Const ts i t' c \<tau>s)
  then show ?case
    unfolding locally_closed_Const_iff
    using in_set_conv_nth length_list_update nth_list_update
    by (metis in_set_conv_nth length_list_update nth_list_update)
qed

lemma beta_reduce_subst_bound_subst_bound:
  fixes t :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes "beta_reduce t t'" and "locally_closed u"
  shows "beta_reduce (subst_bound n u t) (subst_bound n u t')"
  using assms(2)
proof (induction arbitrary: n rule: beta_reduce.induct)
  case (beta t u \<tau>)
  then show ?case
    by (metis beta_reduce.beta inf_vars locally_closed_if_beta_reduce(1,2)
        subst_bound_ident_if_locally_closed)
next
  case (App_left t t' u)
  then show ?case
    by (simp add: beta_reduce.App_left inf_vars subst_bound_ident_if_locally_closed)
next
  case (App_right t u u')
  then show ?case
    by (simp add: beta_reduce.App_right inf_vars subst_bound_ident_if_locally_closed)
next
  case (Abs \<X> t t' \<tau>)
  then show ?case
    by (metis beta_reduce.Abs inf_vars locally_closed_if_beta_reduce(1,2)
        subst_bound_ident_if_locally_closed)
next
  case (Const ts i t' c \<tau>s)
  then show ?case
    by (simp add: beta_reduce.Const)
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
  \<^emph>\<open>well-typed\<close> preterms (via the typing judgment \<open>has_type\<close> from theory \<open>LN_Lambda_Typing\<close>);
  that is a substantial, separate development (Tait/Girard reducibility) and is left as future
  work.\<close>

definition omega :: "'\<tau> \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm" where
  "omega \<tau> = Abs \<tau> (App (Bound 0) (Bound 0))"

lemma beta_reduce_omega_omega:
  "beta_reduce (App (omega \<tau>) (omega \<tau>)) (App (omega \<tau>) (omega \<tau>))"
proof -
  have step: "beta_reduce (App (omega \<tau>) (omega \<tau>))
      (subst_bound 0 (omega \<tau>) (App (Bound 0) (Bound 0)))"
    unfolding omega_def
    by (metis beta body_App_iff body_def locall_closed_Abs_iff_body locally_closed.Free
        subst_bound.simps(3))
  have "subst_bound 0 (omega \<tau>) (App (Bound 0) (Bound 0)) = App (omega \<tau>) (omega \<tau>)"
    by simp
  with step show ?thesis
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
