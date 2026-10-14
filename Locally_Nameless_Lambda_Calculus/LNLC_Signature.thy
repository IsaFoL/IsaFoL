theory LNLC_Signature
  imports
    LNLC_Typing
    "HOL-Library.Infinite_Typeclass"
begin

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

end

end
