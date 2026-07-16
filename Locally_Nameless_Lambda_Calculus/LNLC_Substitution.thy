theory LNLC_Substitution
  imports
    LNLC_Term
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
  theory \<open>LNLC_Typing\<close>.\<close>

primrec subst_preterm ::
  "('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> ('\<V> \<times> '\<tau> \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm) \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm"
  (infixl "\<cdot>\<^sub>t" 69) where
  "subst_preterm (Const c \<tau>s ts) \<sigma> = Const c \<tau>s (map (\<lambda>t. subst_preterm t \<sigma>) ts)" |
  "subst_preterm (Free x \<tau>) \<sigma> = \<sigma> (x, \<tau>)" |
  "subst_preterm (Bound k \<tau>) \<sigma> = Bound k \<tau>" |
  "subst_preterm (App t\<^sub>1 t\<^sub>2) \<sigma> = App (subst_preterm t\<^sub>1 \<sigma>) (subst_preterm t\<^sub>2 \<sigma>)" |
  "subst_preterm (Abs \<tau> t) \<sigma> = Abs \<tau> (subst_preterm t \<sigma>)"

primrec free_typed_vars :: "('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> ('\<V> \<times> '\<tau>) set" where
  "free_typed_vars (Const c \<tau>s ts) = \<Union> (set (map free_typed_vars ts))" |
  "free_typed_vars (Free x \<tau>) = {(x, \<tau>)}" |
  "free_typed_vars (Bound k \<tau>) = {}" |
  "free_typed_vars (App t\<^sub>1 t\<^sub>2) = free_typed_vars t\<^sub>1 \<union> free_typed_vars t\<^sub>2" |
  "free_typed_vars (Abs \<tau> t) = free_typed_vars t"

text \<open>Unlike \<^const>\<open>subst_free\<close> and \<^const>\<open>open_bound\<close>, \<^const>\<open>subst_preterm\<close> \<^emph>\<open>does\<close> descend into
  a constant's parameters: the paper requires parameters to contain no free De Bruijn indices
  (they are locally closed), but they routinely contain free term variables, which a substitution
  must reach (see \<open>basic.tex\<close>, lines 653, 798, 874, 936, 984--985, 1305, 1346, 1801--1804, and
  1882--1884). This makes \<^const>\<open>subst_preterm\<close> genuinely more general than \<^const>\<open>subst_free\<close>: the
  latter (and \<open>close_free\<close> in theory \<open>LNLC_Local_Confluence\<close>, which it is tied to via
  \<open>open_bound_close_free\<close>) must stay opaque towards parameters, since \<open>close_free\<close> would otherwise
  be able to plant a free De Bruijn index inside a parameter, which the paper forbids. Since the
  specific variable a \<open>\<lambda>\<close>-abstraction binds never occurs inside a parameter, this opacity is
  harmless for \<^const>\<open>subst_free\<close>'s only use (working alongside \<^const>\<open>open_bound\<close>/\<open>close_free\<close>
  at binders), but it means \<^const>\<open>subst_free\<close> is \<^emph>\<open>not\<close> a special case of the general
  \<^const>\<open>subst_preterm\<close> defined here (they disagree whenever the substituted variable occurs
  inside a parameter).\<close>

definition id_subst_preterm :: "'\<V> \<times> '\<tau> \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm" where
  "id_subst_preterm \<equiv> \<lambda>(x, \<tau>). Free x \<tau>"

lemma id_subst_preterm_simp[simp]: "id_subst_preterm (x, \<tau>) = Free x \<tau>"
  by (simp add: id_subst_preterm_def)

lemma subst_preterm_id_subst_preterm[simp]: "subst_preterm t id_subst_preterm = t"
proof (induction t)
  case (Const c \<tau>s ts)
  then show ?case
    by (simp add: list.map_ident_strong)
next
  case (Free x \<tau>)
  then show ?case by simp
next
  case (Bound k \<tau>)
  then show ?case by simp
next
  case (App t\<^sub>1 t\<^sub>2)
  then show ?case by simp
next
  case (Abs \<tau> t)
  then show ?case by simp
qed

definition comp_subst_preterm ::
  "('\<V> \<times> '\<tau> \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm) \<Rightarrow> ('\<V> \<times> '\<tau> \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm) \<Rightarrow>
    '\<V> \<times> '\<tau> \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm" where
  "comp_subst_preterm \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<equiv> \<lambda>v. subst_preterm (\<sigma>\<^sub>1 v) \<sigma>\<^sub>2"

lemma subst_preterm_comp_subst_preterm:
  "subst_preterm t (comp_subst_preterm \<sigma>\<^sub>1 \<sigma>\<^sub>2) = subst_preterm (subst_preterm t \<sigma>\<^sub>1) \<sigma>\<^sub>2"
proof (induction t)
  case (Const c \<tau>s ts)
  have "map (\<lambda>t. subst_preterm t (comp_subst_preterm \<sigma>\<^sub>1 \<sigma>\<^sub>2)) ts =
      map (\<lambda>t. subst_preterm (subst_preterm t \<sigma>\<^sub>1) \<sigma>\<^sub>2) ts"
  proof (rule list.map_cong0)
    fix t'
    assume "t' \<in> set ts"
    then show "subst_preterm t' (comp_subst_preterm \<sigma>\<^sub>1 \<sigma>\<^sub>2) = subst_preterm (subst_preterm t' \<sigma>\<^sub>1) \<sigma>\<^sub>2"
      using Const.IH by blast
  qed
  then show ?case
    by (simp add: list.map_comp comp_def)
qed (simp_all add: comp_subst_preterm_def)

definition is_ground_preterm :: "('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> bool" where
  "is_ground_preterm t \<longleftrightarrow> free_typed_vars t = {}"

lemma subst_preterm_ident_if_is_ground_preterm:
  assumes "is_ground_preterm t"
  shows "subst_preterm t \<sigma> = t"
  using assms
proof (induction t)
  case (Const c \<tau>s ts)
  have "map (\<lambda>t. subst_preterm t \<sigma>) ts = ts"
  proof (rule list.map_ident_strong)
    fix t'
    assume t'_in: "t' \<in> set ts"
    then have "free_typed_vars t' \<subseteq> \<Union> (set (map free_typed_vars ts))"
      by auto
    then have "is_ground_preterm t'"
      using Const.prems by (simp add: is_ground_preterm_def)
    then show "subst_preterm t' \<sigma> = t'"
      using Const.IH t'_in by blast
  qed
  then show ?case
    by simp
next
  case (Free x \<tau>)
  then show ?case
    by (simp add: is_ground_preterm_def)
next
  case (Bound k \<tau>)
  then show ?case by simp
next
  case (App t\<^sub>1 t\<^sub>2)
  then show ?case
    by (simp add: is_ground_preterm_def)
next
  case (Abs \<tau> t)
  then show ?case
    by (simp add: is_ground_preterm_def)
qed

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

text \<open>\<^const>\<open>subst_free\<close> is \<^emph>\<open>not\<close> a special case of \<^const>\<open>subst_preterm\<close>: they disagree on any
  \<open>t\<close> where the substituted variable occurs inside a constant's parameter, since
  \<^const>\<open>subst_free\<close> is deliberately opaque there (see the note above the definition of
  \<^const>\<open>subst_preterm\<close>) while \<^const>\<open>subst_preterm\<close> descends into parameters. What does hold
  unconditionally is that \<^const>\<open>free_typed_vars\<close> agrees with the datatype-derived
  \<^const>\<open>free_vars\<close>, since both now descend into parameters uniformly.\<close>

lemma free_vars_eq_fst_image_free_typed_vars: "free_vars t = fst ` free_typed_vars t"
  by (induction t) (auto simp: image_Un)

end
