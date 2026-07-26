theory LNLC_Substitution
  imports
    LNLC_Typing
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

type_synonym ('\<tau>, '\<Sigma>, '\<V>) preterm_subst = "'\<V> \<times> '\<tau> \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm"
type_synonym ('\<Sigma>\<^sub>t\<^sub>y, '\<V>\<^sub>t\<^sub>y) ty_subst = "'\<V>\<^sub>t\<^sub>y \<Rightarrow> ('\<Sigma>\<^sub>t\<^sub>y, '\<V>\<^sub>t\<^sub>y) ty"
type_synonym ('\<Sigma>\<^sub>t\<^sub>y, '\<V>\<^sub>t\<^sub>y, '\<Sigma>, '\<V>) subst =
  "('\<Sigma>\<^sub>t\<^sub>y, '\<V>\<^sub>t\<^sub>y) ty_subst \<times> (('\<Sigma>\<^sub>t\<^sub>y, '\<V>\<^sub>t\<^sub>y) ty, '\<Sigma>, '\<V>) preterm_subst"

primrec subst_preterm ::
  "('\<Sigma>\<^sub>t\<^sub>y :: arity, '\<V>\<^sub>t\<^sub>y, '\<Sigma>, '\<V>) subst \<Rightarrow> (('\<Sigma>\<^sub>t\<^sub>y, '\<V>\<^sub>t\<^sub>y) ty, '\<Sigma>, '\<V>) preterm \<Rightarrow>
    (('\<Sigma>\<^sub>t\<^sub>y, '\<V>\<^sub>t\<^sub>y) ty, '\<Sigma>, '\<V>) preterm" where
  "subst_preterm \<sigma> (Const c \<tau>s ts) = Const c (map (subst_ty (fst \<sigma>)) \<tau>s) (map (subst_preterm \<sigma>) ts)" |
  "subst_preterm \<sigma> (Free x \<tau>) = snd \<sigma> (x, \<tau>)" |
  "subst_preterm \<sigma> (Bound k \<tau>) = Bound k (subst_ty (fst \<sigma>) \<tau>)" |
  "subst_preterm \<sigma> (App t\<^sub>1 t\<^sub>2) = App (subst_preterm \<sigma> t\<^sub>1) (subst_preterm \<sigma> t\<^sub>2)" |
  "subst_preterm \<sigma> (Abs \<tau> t) = Abs (subst_ty (fst \<sigma>) \<tau>) (subst_preterm \<sigma> t)"

abbreviation subst_preterm_alt (infixl "\<cdot>\<^sub>t\<^sub>e" 51) where
  "t \<cdot>\<^sub>t\<^sub>e \<sigma> \<equiv> subst_preterm \<sigma> t"

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

abbreviation id_subst_preterm :: "('\<Sigma>\<^sub>t\<^sub>y :: arity, '\<V>\<^sub>t\<^sub>y, '\<Sigma>, '\<V>) subst" where
  "id_subst_preterm \<equiv> (TyVar, \<lambda>(x, \<tau>). Free x \<tau>)"

lemma subst_preterm_id_subst_preterm_ident[simp]: "subst_preterm id_subst_preterm t = t"
  by (induction t) (simp_all add: list.map_ident_strong)

definition comp_subst_preterm ::
  "('\<Sigma>\<^sub>t\<^sub>y, '\<V>\<^sub>t\<^sub>y, '\<Sigma>, '\<V>) subst \<Rightarrow> ('\<Sigma>\<^sub>t\<^sub>y, '\<V>\<^sub>t\<^sub>y, '\<Sigma>, '\<V>) subst \<Rightarrow>
    ('\<Sigma>\<^sub>t\<^sub>y :: arity, '\<V>\<^sub>t\<^sub>y, '\<Sigma>, '\<V>) subst" where
  "comp_subst_preterm \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<equiv> (fst \<sigma>\<^sub>1 \<then>\<^sub>t\<^sub>y fst \<sigma>\<^sub>2, \<lambda>v. subst_preterm \<sigma>\<^sub>2 (snd \<sigma>\<^sub>1 v))"

notation comp_subst_preterm (infix "\<then>" 51)

lemma subst_preterm_comp_subst_preterm: "t \<cdot>\<^sub>t\<^sub>e (\<sigma>\<^sub>1 \<then> \<sigma>\<^sub>2) = t \<cdot>\<^sub>t\<^sub>e \<sigma>\<^sub>1 \<cdot>\<^sub>t\<^sub>e \<sigma>\<^sub>2"
  by (induction t) (auto simp: comp_subst_preterm_def)

definition is_ground_preterm :: "(('\<Sigma>\<^sub>t\<^sub>y :: arity, '\<V>\<^sub>t\<^sub>y) ty, '\<Sigma>, '\<V>) preterm \<Rightarrow> bool" where
  "is_ground_preterm t \<longleftrightarrow> (\<forall>\<tau> \<in> type_symbols t. free_vars_ty \<tau> = {}) \<and> free_typed_vars t = {}"

lemma subst_preterm_ident_if_is_ground_preterm:
  assumes "is_ground_preterm t"
  shows "subst_preterm \<sigma> t = t"
  using assms
proof (induction t)
  case (Const c \<tau>s ts)
  then show ?case
    by (auto simp: is_ground_preterm_def intro: list.map_ident_strong)
qed (simp_all add: is_ground_preterm_def)

global_interpretation comp_subst_preterm: monoid comp_subst_preterm id_subst_preterm
proof unfold_locales
  fix \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<sigma>\<^sub>3 :: "('\<Sigma>\<^sub>t\<^sub>y :: arity, '\<V>\<^sub>t\<^sub>y, '\<Sigma>, '\<V>) subst"
  show "(\<sigma>\<^sub>1 \<then> \<sigma>\<^sub>2) \<then> \<sigma>\<^sub>3 = \<sigma>\<^sub>1 \<then> (\<sigma>\<^sub>2 \<then> \<sigma>\<^sub>3)"
    by (metis (no_types, lifting) ext comp_subst_preterm_def
        comp_subst_ty.assoc[of "fst \<sigma>\<^sub>1" "fst \<sigma>\<^sub>2" "fst \<sigma>\<^sub>3"] prod.sel
        subst_preterm_comp_subst_preterm[of \<sigma>\<^sub>2 \<sigma>\<^sub>3 "snd \<sigma>\<^sub>1 _"])

  show "id_subst_preterm \<then> \<sigma>\<^sub>1 = \<sigma>\<^sub>1"
    by (simp add: comp_subst_preterm_def case_prod_beta)

  show "comp_subst_preterm \<sigma>\<^sub>1 id_subst_preterm = \<sigma>\<^sub>1"
    by (simp add: comp_subst_preterm_def)
qed

global_interpretation subst_preterm: substitution where
  comp_subst = comp_subst_preterm and
  id_subst = id_subst_preterm and
  subst = "\<lambda>t \<sigma>. subst_preterm \<sigma> t" and
  is_ground = is_ground_preterm and
  apply_subst = "\<lambda>v \<sigma>. snd \<sigma> v" and
  vars = free_typed_vars
proof unfold_locales
  fix t :: "(('\<Sigma>\<^sub>t\<^sub>y :: arity, '\<V>\<^sub>t\<^sub>y) ty, '\<Sigma>, '\<V>) preterm" and \<sigma>\<^sub>1 \<sigma>\<^sub>2 :: "('\<Sigma>\<^sub>t\<^sub>y :: arity, '\<V>\<^sub>t\<^sub>y, '\<Sigma>, '\<V>) subst"
  show "t \<cdot>\<^sub>t\<^sub>e (\<sigma>\<^sub>1 \<then> \<sigma>\<^sub>2) = t \<cdot>\<^sub>t\<^sub>e \<sigma>\<^sub>1 \<cdot>\<^sub>t\<^sub>e \<sigma>\<^sub>2"
    by (rule subst_preterm_comp_subst_preterm)

  show "t  \<cdot>\<^sub>t\<^sub>e id_subst_preterm = t"
    by simp

  show "is_ground_preterm t \<Longrightarrow> \<forall>\<sigma>. t \<cdot>\<^sub>t\<^sub>e \<sigma> = t"
    using subst_preterm_ident_if_is_ground_preterm ..

  show "is_ground_preterm t \<Longrightarrow> free_typed_vars t = {}"
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
