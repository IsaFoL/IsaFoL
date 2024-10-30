theory Ground_Ordering
  imports
    Ground_Clause
    Transitive_Closure_Extra
    Clausal_Calculus_Extra
    Min_Max_Least_Greatest.Min_Max_Least_Greatest_Multiset
    Term_Ordering_Lifting
begin

locale ground_ordering = term_ordering_lifting less_trm
  for
    less_trm :: "'f gterm \<Rightarrow> 'f gterm \<Rightarrow> bool" (infix "\<prec>\<^sub>t" 50) +
  assumes
    wfP_less_trm[intro]: "wfP (\<prec>\<^sub>t)" and
    totalp_less_trm[intro]: "totalp (\<prec>\<^sub>t)" and
    less_trm_compatible_with_gctxt[simp]: "\<And>ctxt t t'. t \<prec>\<^sub>t t' \<Longrightarrow> ctxt\<langle>t\<rangle>\<^sub>G \<prec>\<^sub>t ctxt\<langle>t'\<rangle>\<^sub>G" and
    less_trm_if_subterm[simp]: "\<And>t ctxt. ctxt \<noteq> \<box>\<^sub>G \<Longrightarrow> t \<prec>\<^sub>t ctxt\<langle>t\<rangle>\<^sub>G"
begin

abbreviation lesseq_trm (infix "\<preceq>\<^sub>t" 50) where
  "lesseq_trm \<equiv> (\<prec>\<^sub>t)\<^sup>=\<^sup>="

lemma lesseq_trm_if_subtermeq: "t \<preceq>\<^sub>t ctxt\<langle>t\<rangle>\<^sub>G"
  using less_trm_if_subterm
  by (metis gctxt_ident_iff_eq_GHole reflclp_iff)

abbreviation lesseq_lit (infix "\<preceq>\<^sub>l" 50) where
  "lesseq_lit \<equiv> (\<prec>\<^sub>l)\<^sup>=\<^sup>="

abbreviation lesseq_cls (infix "\<preceq>\<^sub>c" 50) where
  "lesseq_cls \<equiv> (\<prec>\<^sub>c)\<^sup>=\<^sup>="

lemma wfP_less_lit[simp]: "wfp (\<prec>\<^sub>l)"
  unfolding less_lit_def
  using wfP_less_trm wfP_multp wfP_if_convertible_to_wfP by meson

lemma wfP_less_cls[simp]: "wfp (\<prec>\<^sub>c)"
  using wfP_less_lit wfP_multp less_cls_def by metis


sublocale term_order: linorder lesseq_trm less_trm
proof unfold_locales
  show "\<And>x y. x \<preceq>\<^sub>t y \<or> y \<preceq>\<^sub>t x"
    by (metis reflclp_iff totalpD totalp_less_trm)
qed

sublocale literal_order: linorder lesseq_lit less_lit
proof unfold_locales
  have "totalp_on A (\<prec>\<^sub>l)" for A
  proof (rule totalp_onI)
    fix L1 L2 :: "'f gatom literal"
    assume "L1 \<noteq> L2"

    show "L1 \<prec>\<^sub>l L2 \<or> L2 \<prec>\<^sub>l L1"
      unfolding less_lit_def
    proof (rule totalp_multp[THEN totalpD])
      show "totalp (\<prec>\<^sub>t)"
        using totalp_less_trm .
    next
      show "transp (\<prec>\<^sub>t)"
        using transp_less_trm .
    next
      obtain x1 y1 x2 y2 :: "'f gterm" where
        "atm_of L1 = Upair x1 y1" and "atm_of L2 = Upair x2 y2"
        using uprod_exhaust by metis
      thus "mset_lit L1 \<noteq> mset_lit L2"
        using \<open>L1 \<noteq> L2\<close>
        by (cases L1; cases L2) (auto simp add: add_eq_conv_ex)
    qed
  qed
  thus "\<And>x y. x \<preceq>\<^sub>l y \<or> y \<preceq>\<^sub>l x"
    by (metis reflclp_iff totalpD)
qed

sublocale clause_order: linorder lesseq_cls less_cls
proof unfold_locales
  show "\<And>x y. x \<preceq>\<^sub>c y \<or> y \<preceq>\<^sub>c x"
    unfolding less_cls_def
    using totalp_multp[OF literal_order.totalp_on_less literal_order.transp_on_less]
    by (metis reflclp_iff totalpD)
qed

abbreviation is_maximal_lit :: "'f gatom literal \<Rightarrow> 'f gatom clause \<Rightarrow> bool" where
  "is_maximal_lit L M \<equiv> is_maximal_in_mset_wrt (\<prec>\<^sub>l) M L"

abbreviation is_strictly_maximal_lit :: "'f gatom literal \<Rightarrow> 'f gatom clause \<Rightarrow> bool" where
  "is_strictly_maximal_lit L M \<equiv> is_greatest_in_mset_wrt (\<prec>\<^sub>l) M L"

lemma less_trm_compatible_with_gctxt':
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
      using less_trm_compatible_with_gctxt by metis
      
    then show ?thesis
      using assms by order
  qed
qed

lemma less_trm_compatible_with_gctxt_iff: "ctxt\<langle>t\<rangle>\<^sub>G \<prec>\<^sub>t ctxt\<langle>t'\<rangle>\<^sub>G \<longleftrightarrow> t \<prec>\<^sub>t t'"
  using less_trm_compatible_with_gctxt less_trm_compatible_with_gctxt' 
  by blast

lemma context_less_term_lesseq:
  assumes 
    "\<And>t. ctxt\<langle>t\<rangle>\<^sub>G \<prec>\<^sub>t ctxt'\<langle>t\<rangle>\<^sub>G"
    "t \<preceq>\<^sub>t t'"
  shows "ctxt\<langle>t\<rangle>\<^sub>G \<prec>\<^sub>t ctxt'\<langle>t'\<rangle>\<^sub>G"
  using assms less_trm_compatible_with_gctxt
  by (metis reflclp_iff term_order.dual_order.strict_trans)

lemma context_lesseq_term_less:
  assumes 
    "\<And>t. ctxt\<langle>t\<rangle>\<^sub>G \<preceq>\<^sub>t ctxt'\<langle>t\<rangle>\<^sub>G"
    "t \<prec>\<^sub>t t'"
  shows "ctxt\<langle>t\<rangle>\<^sub>G \<prec>\<^sub>t ctxt'\<langle>t'\<rangle>\<^sub>G"
  using assms less_trm_compatible_with_gctxt term_order.dual_order.strict_trans1 
  by blast

end

end
