theory LN_Lambda_Reduction
  imports LN_Lambda_Term
begin

section \<open>One-step \<open>\<beta>\<close>-reduction\<close>

text \<open>One-step \<open>\<beta>\<close>-reduction on \<open>\<lambda>\<close>-preterms. The relation \<open>beta_reduce t u\<close>
  expresses that \<open>t\<close> \<open>\<beta>\<close>-reduces to \<open>u\<close> in exactly one step. The first rule is the
  \<open>\<beta>\<close>-rule proper; the remaining rules are congruence (compatibility) rules that allow the
  reduction to take place anywhere inside a term, including inside a constant's parameters.\<close>

inductive beta_reduce :: "('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> bool" where
  beta: "beta_reduce (App (Abs \<tau> t) u) (subst_bound 0 u t)" |
  App_left: "beta_reduce t t' \<Longrightarrow> beta_reduce (App t u) (App t' u)" |
  App_right: "beta_reduce u u' \<Longrightarrow> beta_reduce (App t u) (App t u')" |
  Abs: "beta_reduce t t' \<Longrightarrow> beta_reduce (Abs \<tau> t) (Abs \<tau> t')" |
  Const: "i < length ts \<Longrightarrow> beta_reduce (ts ! i) t' \<Longrightarrow>
    beta_reduce (Const c \<tau>s ts) (Const c \<tau>s (ts[i := t']))"

text \<open>Full reduction is the reflexive-transitive closure. A preterm is in normal form when no
  further \<open>\<beta>\<close>-step is possible; reducing a preterm fully means following \<open>beta_reduces\<close>
  until a \<open>beta_normal\<close> preterm is reached (if one exists---see the note on strong
  normalization below).\<close>

abbreviation beta_reduces :: "('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> bool" where
  "beta_reduces \<equiv> beta_reduce\<^sup>*\<^sup>*"

definition beta_normal :: "('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> bool" where
  "beta_normal t \<longleftrightarrow> (\<nexists>u. beta_reduce t u)"


section \<open>\<open>\<beta>\<close>-reduction is NOT strongly normalizing\<close>

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
    unfolding omega_def by (rule beta_reduce.beta)
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
