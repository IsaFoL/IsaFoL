theory LN_Lambda_Substitution
  imports
    LN_Lambda_Term
    "Abstract_Substitution.Substitution"
begin

section \<open>General Substitution on Preterms\<close>

text \<open>The paper's substitutions (\<open>\<rho>\<close>) map term variables \<open>x\<langle>\<tau>\<rangle>\<close> (a name paired with its type
  annotation) to \<open>\<lambda>\<close>-terms. \<^const>\<open>subst_free\<close> only replaces a single named variable and ignores
  its annotation, so it cannot serve as a substitution in the abstract sense (in particular it has
  no identity: reproducing \<open>Free x \<tau>\<close> under the identity substitution requires knowing \<open>\<tau>\<close>). Here
  we define a general substitution keyed on \<open>'\<V> \<times> '\<tau>\<close> pairs, faithful to the paper's \<open>x\<langle>\<tau>\<rangle>\<close>
  notation, and show it forms an @{locale substitution} in the sense of
  \<^theory>\<open>Abstract_Substitution.Substitution\<close> --- mirroring the treatment of type substitutions in
  theory \<open>LN_Lambda_Typing\<close>.

  As with \<^const>\<open>subst_free\<close> and \<^const>\<open>open_bound\<close>, a constant's parameters are treated
  opaquely: substitution never descends into them (see the note at \<open>free_var_types\<close> in theory
  \<open>LN_Lambda_Typing\<close>). This is what lets \<^const>\<open>subst_free\<close> be recovered as a special case of
  the general substitution below.\<close>

primrec subst_preterm ::
  "('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> ('\<V> \<times> '\<tau> \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm) \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm"
  (infixl "\<cdot>\<^sub>t" 69) where
  "subst_preterm (Const c \<tau>s ts) \<sigma> = Const c \<tau>s ts" |
  "subst_preterm (Free x \<tau>) \<sigma> = \<sigma> (x, \<tau>)" |
  "subst_preterm (Bound k \<tau>) \<sigma> = Bound k \<tau>" |
  "subst_preterm (App t\<^sub>1 t\<^sub>2) \<sigma> = App (subst_preterm t\<^sub>1 \<sigma>) (subst_preterm t\<^sub>2 \<sigma>)" |
  "subst_preterm (Abs \<tau> t) \<sigma> = Abs \<tau> (subst_preterm t \<sigma>)"

primrec free_typed_vars :: "('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> ('\<V> \<times> '\<tau>) set" where
  "free_typed_vars (Const c \<tau>s ts) = {}" |
  "free_typed_vars (Free x \<tau>) = {(x, \<tau>)}" |
  "free_typed_vars (Bound k \<tau>) = {}" |
  "free_typed_vars (App t\<^sub>1 t\<^sub>2) = free_typed_vars t\<^sub>1 \<union> free_typed_vars t\<^sub>2" |
  "free_typed_vars (Abs \<tau> t) = free_typed_vars t"

definition id_subst_preterm :: "'\<V> \<times> '\<tau> \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm" where
  "id_subst_preterm \<equiv> \<lambda>(x, \<tau>). Free x \<tau>"

lemma id_subst_preterm_simp[simp]: "id_subst_preterm (x, \<tau>) = Free x \<tau>"
  by (simp add: id_subst_preterm_def)

lemma subst_preterm_id_subst_preterm[simp]: "subst_preterm t id_subst_preterm = t"
  by (induction t) simp_all

definition comp_subst_preterm ::
  "('\<V> \<times> '\<tau> \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm) \<Rightarrow> ('\<V> \<times> '\<tau> \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm) \<Rightarrow>
    '\<V> \<times> '\<tau> \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm" where
  "comp_subst_preterm \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<equiv> \<lambda>v. subst_preterm (\<sigma>\<^sub>1 v) \<sigma>\<^sub>2"

lemma subst_preterm_comp_subst_preterm:
  "subst_preterm t (comp_subst_preterm \<sigma>\<^sub>1 \<sigma>\<^sub>2) = subst_preterm (subst_preterm t \<sigma>\<^sub>1) \<sigma>\<^sub>2"
  by (induction t) (simp_all add: comp_subst_preterm_def)

definition is_ground_preterm :: "('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> bool" where
  "is_ground_preterm t \<longleftrightarrow> free_typed_vars t = {}"

lemma subst_preterm_ident_if_is_ground_preterm:
  assumes "is_ground_preterm t"
  shows "subst_preterm t \<sigma> = t"
  using assms
  by (induction t) (simp_all add: is_ground_preterm_def)

global_interpretation comp_subst_preterm: monoid comp_subst_preterm id_subst_preterm
proof unfold_locales
  fix \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<sigma>\<^sub>3 :: "'\<V> \<times> '\<tau> \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm"
  show "comp_subst_preterm (comp_subst_preterm \<sigma>\<^sub>1 \<sigma>\<^sub>2) \<sigma>\<^sub>3 =
    comp_subst_preterm \<sigma>\<^sub>1 (comp_subst_preterm \<sigma>\<^sub>2 \<sigma>\<^sub>3)"
  proof (rule ext)
    fix v
    have "comp_subst_preterm (comp_subst_preterm \<sigma>\<^sub>1 \<sigma>\<^sub>2) \<sigma>\<^sub>3 v =
      subst_preterm (subst_preterm (\<sigma>\<^sub>1 v) \<sigma>\<^sub>2) \<sigma>\<^sub>3"
      by (simp add: comp_subst_preterm_def)
    also have "\<dots> = subst_preterm (\<sigma>\<^sub>1 v) (comp_subst_preterm \<sigma>\<^sub>2 \<sigma>\<^sub>3)"
      by (simp add: subst_preterm_comp_subst_preterm)
    also have "\<dots> = comp_subst_preterm \<sigma>\<^sub>1 (comp_subst_preterm \<sigma>\<^sub>2 \<sigma>\<^sub>3) v"
      by (simp add: comp_subst_preterm_def)
    finally show "comp_subst_preterm (comp_subst_preterm \<sigma>\<^sub>1 \<sigma>\<^sub>2) \<sigma>\<^sub>3 v =
      comp_subst_preterm \<sigma>\<^sub>1 (comp_subst_preterm \<sigma>\<^sub>2 \<sigma>\<^sub>3) v" .
  qed
next
  fix a :: "'\<V> \<times> '\<tau> \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm"
  show "comp_subst_preterm id_subst_preterm a = a"
  proof (rule ext)
    fix v :: "'\<V> \<times> '\<tau>"
    obtain x \<tau> where "v = (x, \<tau>)"
      by (cases v)
    then show "comp_subst_preterm id_subst_preterm a v = a v"
      by (simp add: comp_subst_preterm_def)
  qed
next
  show "\<And>a. comp_subst_preterm a id_subst_preterm = a"
    by (simp add: comp_subst_preterm_def)
qed

global_interpretation subst_preterm: substitution where
  comp_subst = comp_subst_preterm and
  id_subst = id_subst_preterm and
  subst = subst_preterm and
  is_ground = is_ground_preterm and
  apply_subst = "\<lambda>v \<sigma>. \<sigma> v" and
  vars = free_typed_vars
proof unfold_locales
  fix t :: "('\<tau>, '\<Sigma>, '\<V>) preterm" and \<sigma>\<^sub>1 \<sigma>\<^sub>2 :: "'\<V> \<times> '\<tau> \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm"
  show "subst_preterm t (comp_subst_preterm \<sigma>\<^sub>1 \<sigma>\<^sub>2) = subst_preterm (subst_preterm t \<sigma>\<^sub>1) \<sigma>\<^sub>2"
    by (rule subst_preterm_comp_subst_preterm)
next
  fix t :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  show "subst_preterm t id_subst_preterm = t"
    by simp
next
  fix t :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assume "is_ground_preterm t"
  then show "\<forall>\<sigma>. subst_preterm t \<sigma> = t"
    by (simp add: subst_preterm_ident_if_is_ground_preterm)
next
  fix t :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assume "is_ground_preterm t"
  then show "free_typed_vars t = {}"
    by (simp add: is_ground_preterm_def)
qed

text \<open>\<^const>\<open>subst_free\<close> is the special case of \<^const>\<open>subst_preterm\<close> that only touches
  occurrences of \<open>x\<close>, regardless of their annotation, and leaves every other free variable
  unchanged --- matching that \<^const>\<open>subst_free\<close> ignores the stored type annotation entirely.\<close>

lemma subst_free_eq_subst_preterm:
  "subst_free x u t = subst_preterm t (\<lambda>(y, \<tau>). if y = x then u else Free y \<tau>)"
  by (induction t) simp_all

end
