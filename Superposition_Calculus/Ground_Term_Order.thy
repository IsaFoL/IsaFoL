theory Ground_Term_Order
  imports
    Ground_Context
    Context_Compatibility
    Term_Order_Notation
    Transitive_Closure_Extra
begin

locale context_compatible_ground_order = context_compatible_order where Fun = GFun

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
  context_compatible_ground_order less\<^sub>t +
  subterm_property less\<^sub>t 
  for less\<^sub>t :: "'f gterm \<Rightarrow> 'f gterm \<Rightarrow> bool" 
begin

interpretation term_order_notation.


end

end
