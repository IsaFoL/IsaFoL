theory LNLC_Signature
  imports
    LNLC_Typing
    "HOL-Library.Infinite_Typeclass"
begin

section \<open>Basic Properties of Typing\<close>

text \<open>Inversion rules for \<^const>\<open>has_type\<close>. Dangling De Bruijn indices are never well typed.\<close>

lemma not_has_type_Bound[simp]: "\<not> has_type \<C> (Bound n \<tau>) \<upsilon>"
  sorry

lemma has_type_Free_iff[simp]: "has_type \<C> (Free x \<tau>) \<upsilon> \<longleftrightarrow> \<upsilon> = \<tau>"
  sorry

lemma has_type_App_iff:
  "has_type \<C> (App t\<^sub>1 t\<^sub>2) \<upsilon> \<longleftrightarrow> (\<exists>\<tau>. has_type \<C> t\<^sub>1 (TyFun \<tau> \<upsilon>) \<and> has_type \<C> t\<^sub>2 \<tau>)"
  sorry

text \<open>The type annotations make typing context-free: every \<open>\<lambda>\<close>-preterm has at most one type
  (paper, Section~2.1.2: ``The type arguments carry enough information to enable typing of any
  \<open>\<lambda>\<close>-preterm without any context''). This requires infinitely many variables: over a finite
  variable type, the cofinite premise of rule \<open>has_type.Abs\<close> is vacuous and every abstraction
  \<open>Abs \<tau> t\<close> has every type \<open>TyFun \<tau> \<upsilon>\<close>.\<close>

lemma has_type_unique:
  fixes t :: "(('\<Sigma>\<^sub>t\<^sub>y :: type_signature, '\<V>\<^sub>t\<^sub>y) ty, '\<Sigma>, '\<V> :: infinite) lpreterm"
  assumes "has_type \<C> t \<tau>" and "has_type \<C> t \<upsilon>"
  shows "\<tau> = \<upsilon>"
  sorry


section \<open>Signatures\<close>

text \<open>A term signature (paper, Section~2.1.2) assigns a type declaration to every constant and must
  contain the logical symbols \<open>\<top>, \<bottom> :: \<bool>\<close>, \<open>\<not> :: \<bool> \<rightarrow> \<bool>\<close>,
  \<open>\<and>, \<or>, \<longrightarrow> :: \<bool> \<rightarrow> \<bool> \<rightarrow> \<bool>\<close>, and \<open>\<approx>, \<not>\<approx> :: \<Pi>\<alpha>. \<alpha> \<rightarrow> \<alpha> \<rightarrow> \<bool>\<close>. The calculus additionally
  requires the extensionality Skolem constant \<open>diff :: \<Pi>\<alpha> \<beta>. (\<alpha> \<rightarrow> \<beta>, \<alpha> \<rightarrow> \<beta>) \<Rightarrow> \<alpha>\<close>
  (Section~2.3), which takes two parameters.

  The names of these symbols are provided by the type class \<^class>\<open>term_signature\<close>; the locale
  below requires that the type declaration function \<open>\<C>\<close> assigns them their intended types. The
  bound type variables of the polymorphic declarations are arbitrary, hence the existential
  quantifiers. The paper treats the logical symbols as distinct symbols, which we require
  explicitly.\<close>

locale signature =
  fixes \<C> :: "'\<Sigma> :: term_signature \<Rightarrow> ('\<Sigma>\<^sub>t\<^sub>y :: type_signature, '\<V>\<^sub>t\<^sub>y) const_ty"
  assumes
    distinct_logical_consts:
      "distinct [True_tconst :: '\<Sigma>, False_tconst, Neg_tconst, Conj_tconst, Disj_tconst, Imp_tconst,
        Eq_tconst, Neq_tconst, Diff_tconst]" and
    True_const_ty: "\<C> True_tconst = ConstTy [] [] \<bool>" and
    False_const_ty: "\<C> False_tconst = ConstTy [] [] \<bool>" and
    Neg_const_ty: "\<C> Neg_tconst = ConstTy [] [] (TyFun \<bool> \<bool>)" and
    Conj_const_ty: "\<C> Conj_tconst = ConstTy [] [] (TyFun \<bool> (TyFun \<bool> \<bool>))" and
    Disj_const_ty: "\<C> Disj_tconst = ConstTy [] [] (TyFun \<bool> (TyFun \<bool> \<bool>))" and
    Imp_const_ty: "\<C> Imp_tconst = ConstTy [] [] (TyFun \<bool> (TyFun \<bool> \<bool>))" and
    Eq_const_ty: "\<exists>\<alpha>. \<C> Eq_tconst = ConstTy [\<alpha>] [] (TyFun (TyVar \<alpha>) (TyFun (TyVar \<alpha>) \<bool>))" and
    Neq_const_ty: "\<exists>\<alpha>. \<C> Neq_tconst = ConstTy [\<alpha>] [] (TyFun (TyVar \<alpha>) (TyFun (TyVar \<alpha>) \<bool>))" and
    Diff_const_ty: "\<exists>\<alpha> \<beta>. \<alpha> \<noteq> \<beta> \<and>
      \<C> Diff_tconst = ConstTy [\<alpha>, \<beta>] [TyFun (TyVar \<alpha>) (TyVar \<beta>), TyFun (TyVar \<alpha>) (TyVar \<beta>)] (TyVar \<alpha>)"
begin

text \<open>A \<open>\<lambda>\<close>-preterm is \<^emph>\<open>functional\<close> if its type is a function type and \<^emph>\<open>nonfunctional\<close>
  otherwise (paper, Section~2.1.2). We only apply the notion to well-typed \<open>\<lambda>\<close>-preterms.\<close>

definition functional :: "(('\<Sigma>\<^sub>t\<^sub>y, '\<V>\<^sub>t\<^sub>y) ty, '\<Sigma>, '\<V>) lpreterm \<Rightarrow> bool" where
  "functional t \<longleftrightarrow> (\<exists>\<tau> \<upsilon>. has_type \<C> t (TyFun \<tau> \<upsilon>))"

lemma functional_iff_is_TyFun:
  fixes t :: "(('\<Sigma>\<^sub>t\<^sub>y, '\<V>\<^sub>t\<^sub>y) ty, '\<Sigma>, '\<V> :: infinite) lpreterm"
  assumes "has_type \<C> t \<tau>"
  shows "functional t \<longleftrightarrow> is_TyFun \<tau>"
  sorry


subsection \<open>Typing of the Logical Symbols\<close>

lemma has_type_True: "has_type \<C> (Const True_tconst [] []) \<bool>"
  sorry

lemma has_type_False: "has_type \<C> (Const False_tconst [] []) \<bool>"
  sorry

lemma has_type_Neg: "has_type \<C> (Const Neg_tconst [] []) (TyFun \<bool> \<bool>)"
  sorry

lemma has_type_Conj: "has_type \<C> (Const Conj_tconst [] []) (TyFun \<bool> (TyFun \<bool> \<bool>))"
  sorry

lemma has_type_Disj: "has_type \<C> (Const Disj_tconst [] []) (TyFun \<bool> (TyFun \<bool> \<bool>))"
  sorry

lemma has_type_Imp: "has_type \<C> (Const Imp_tconst [] []) (TyFun \<bool> (TyFun \<bool> \<bool>))"
  sorry

lemma has_type_Eq: "has_type \<C> (Const Eq_tconst [\<tau>] []) (TyFun \<tau> (TyFun \<tau> \<bool>))"
  sorry

lemma has_type_Neq: "has_type \<C> (Const Neq_tconst [\<tau>] []) (TyFun \<tau> (TyFun \<tau> \<bool>))"
  sorry

lemma has_type_Diff:
  assumes "has_type \<C> s (TyFun \<tau> \<upsilon>)" and "has_type \<C> t (TyFun \<tau> \<upsilon>)"
  shows "has_type \<C> (Const Diff_tconst [\<tau>, \<upsilon>] [s, t]) \<tau>"
  sorry

end

end
