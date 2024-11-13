theory Ground_Term_Order
  imports 
    Ground_Term_Extra
    Ground_Context
    Term_Order_Notation
    Restricted_Order
    Transitive_Closure_Extra
begin

locale context_compatibility_iff =
  fixes R
  assumes
    context_compatibility_iff [simp]: "\<And>c t t'. R c\<langle>t\<rangle>\<^sub>G c\<langle>t'\<rangle>\<^sub>G \<longleftrightarrow> R t t'"

locale context_compatibility =
  total_strict_order where less = less\<^sub>t
  for less\<^sub>t :: "'f gterm \<Rightarrow> 'f gterm \<Rightarrow> bool" +
  assumes
    context_compatibility [simp]: "\<And>c t t'. less\<^sub>t t t' \<Longrightarrow> less\<^sub>t c\<langle>t\<rangle>\<^sub>G c\<langle>t'\<rangle>\<^sub>G"
begin

(* TODO: Already here with t or just from Ground_Order on?*)
interpretation term_order_notation.

sublocale context_compatibility_iff "(\<prec>\<^sub>t)"
proof unfold_locales
  fix c t t'
  show "c\<langle>t\<rangle>\<^sub>G \<prec>\<^sub>t c\<langle>t'\<rangle>\<^sub>G \<longleftrightarrow> t \<prec>\<^sub>t t'"
  proof(intro iffI)
    assume less\<^sub>t_with_context: "c\<langle>t\<rangle>\<^sub>G \<prec>\<^sub>t c\<langle>t'\<rangle>\<^sub>G"

    show "t \<prec>\<^sub>t t'"
    proof(rule ccontr)
      assume "\<not> t \<prec>\<^sub>t t'"
      hence "t' \<preceq>\<^sub>t t"
        by order

      show False
      proof(cases "t' = t")
        case True

        then have "c\<langle>t\<rangle>\<^sub>G = c\<langle>t'\<rangle>\<^sub>G"
          by blast

        then show False
          using less\<^sub>t_with_context 
          by order
      next
        case False

        then have "t' \<prec>\<^sub>t t"
          using \<open>t' \<preceq>\<^sub>t t\<close> 
          by order

        then have "c\<langle>t'\<rangle>\<^sub>G \<prec>\<^sub>t c\<langle>t\<rangle>\<^sub>G"
          using context_compatibility 
          by metis

        then show ?thesis
          using less\<^sub>t_with_context 
          by order
      qed
    qed
  next
    show "t \<prec>\<^sub>t t' \<Longrightarrow> c\<langle>t\<rangle>\<^sub>G \<prec>\<^sub>t c\<langle>t'\<rangle>\<^sub>G"
      using context_compatibility.
  qed
qed

sublocale less_eq: context_compatibility_iff "(\<preceq>\<^sub>t)"
  using context_compatibility not_le
  by unfold_locales blast

end

locale subterm_property =
  strict_order where less = less\<^sub>t
  for less\<^sub>t :: "'f gterm \<Rightarrow> 'f gterm \<Rightarrow> bool" +
  assumes
    subterm_property [simp]: "\<And>t c. c \<noteq> \<box> \<Longrightarrow> less\<^sub>t t c\<langle>t\<rangle>\<^sub>G"
begin

interpretation term_order_notation.

lemma less_eq_subterm_property: "t \<preceq>\<^sub>t c\<langle>t\<rangle>\<^sub>G"
  using subterm_property
  by (metis gctxt_ident_iff_eq_GHole reflclp_iff)

end

locale ground_term_order = 
  wellfounded_strict_order less\<^sub>t + 
  total_strict_order less\<^sub>t +
  context_compatibility less\<^sub>t +
  subterm_property less\<^sub>t 
  for less\<^sub>t :: "'f gterm \<Rightarrow> 'f gterm \<Rightarrow> bool" 
begin

interpretation term_order_notation.

(* TODO: Names *)
lemma context_less_term_less_eq:
  assumes 
    "\<And>t. c\<langle>t\<rangle>\<^sub>G \<prec>\<^sub>t c'\<langle>t\<rangle>\<^sub>G"
    "t \<preceq>\<^sub>t t'"
  shows "c\<langle>t\<rangle>\<^sub>G \<prec>\<^sub>t c'\<langle>t'\<rangle>\<^sub>G"
  using assms context_compatibility
  by (metis reflclp_iff dual_order.strict_trans)

lemma context_less_eq_term_less:
  assumes 
    "\<And>t. c\<langle>t\<rangle>\<^sub>G \<preceq>\<^sub>t c'\<langle>t\<rangle>\<^sub>G"
    "t \<prec>\<^sub>t t'"
  shows "c\<langle>t\<rangle>\<^sub>G \<prec>\<^sub>t c'\<langle>t'\<rangle>\<^sub>G"
  using assms context_compatibility dual_order.strict_trans1 
  by blast

end

end
