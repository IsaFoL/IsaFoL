theory Ground_Ordering
  imports
    Isabelle_2024_Compatibility
    Ground_Clause
    Transitive_Closure_Extra
    Clausal_Calculus_Extra
    Min_Max_Least_Greatest_Multiset
    Term_Ordering_Lifting
begin

locale ground_ordering = term_ordering_lifting "(\<prec>\<^sub>t)"
  for
    less\<^sub>t :: "'f gterm \<Rightarrow> 'f gterm \<Rightarrow> bool" (infix "\<prec>\<^sub>t" 50) +
  assumes
    less\<^sub>t_compatible_with_gctxt[simp]: "\<And>c t t'. t \<prec>\<^sub>t t' \<Longrightarrow> c\<langle>t\<rangle>\<^sub>G \<prec>\<^sub>t c\<langle>t'\<rangle>\<^sub>G" and
    less\<^sub>t_if_subterm[simp]: "\<And>t c. c \<noteq> \<box> \<Longrightarrow> t \<prec>\<^sub>t c\<langle>t\<rangle>\<^sub>G"
begin

(*notation less\<^sub>c (infix "\<prec>\<^sub>c" 50) *)



(* TODO: Names *)
lemma lesseq_trm_if_subterm: "t \<preceq>\<^sub>t ctxt\<langle>t\<rangle>\<^sub>G"
  using less\<^sub>t_if_subterm
  by (metis gctxt_ident_iff_eq_GHole reflclp_iff)

lemma less\<^sub>t_compatible_with_gctxt':
  assumes "ctxt\<langle>t\<rangle>\<^sub>G \<prec>\<^sub>t ctxt\<langle>t'\<rangle>\<^sub>G"
  shows "t \<prec>\<^sub>t t'"
proof(rule ccontr)
  assume "\<not> t \<prec>\<^sub>t t'"
  hence "t' \<preceq>\<^sub>t t"
    by order

  show False
  proof(cases "t' = t")
    case True
    then have "ctxt\<langle>t\<rangle>\<^sub>G = ctxt\<langle>t'\<rangle>\<^sub>G"
      by blast
    then show False
      using assms by order
  next
    case False
    then have "t' \<prec>\<^sub>t t"
      using \<open>t' \<preceq>\<^sub>t t\<close> by order

    then have "ctxt\<langle>t'\<rangle>\<^sub>G \<prec>\<^sub>t ctxt\<langle>t\<rangle>\<^sub>G"
      using less\<^sub>t_compatible_with_gctxt by metis
      
    then show ?thesis
      using assms by order
  qed
qed

lemma less\<^sub>t_compatible_with_gctxt_iff: "ctxt\<langle>t\<rangle>\<^sub>G \<prec>\<^sub>t ctxt\<langle>t'\<rangle>\<^sub>G \<longleftrightarrow> t \<prec>\<^sub>t t'"
  using less\<^sub>t_compatible_with_gctxt less\<^sub>t_compatible_with_gctxt' 
  by blast

lemma context_less_term_lesseq:
  assumes 
    "\<And>t. ctxt\<langle>t\<rangle>\<^sub>G \<prec>\<^sub>t ctxt'\<langle>t\<rangle>\<^sub>G"
    "t \<preceq>\<^sub>t t'"
  shows "ctxt\<langle>t\<rangle>\<^sub>G \<prec>\<^sub>t ctxt'\<langle>t'\<rangle>\<^sub>G"
  using assms less\<^sub>t_compatible_with_gctxt
  by (metis reflclp_iff term_order.dual_order.strict_trans)

lemma context_lesseq_term_less:
  assumes 
    "\<And>t. ctxt\<langle>t\<rangle>\<^sub>G \<preceq>\<^sub>t ctxt'\<langle>t\<rangle>\<^sub>G"
    "t \<prec>\<^sub>t t'"
  shows "ctxt\<langle>t\<rangle>\<^sub>G \<prec>\<^sub>t ctxt'\<langle>t'\<rangle>\<^sub>G"
  using assms less\<^sub>t_compatible_with_gctxt term_order.dual_order.strict_trans1 
  by blast

end

end