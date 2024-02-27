theory Ground_Ordering
  imports
    Regular_Tree_Relations.Ground_Ctxt
    Regular_Tree_Relations.Ground_Terms

    Ground_Clause
    Ground_Ctxt_Extra
    Transitive_Closure_Extra
    Clausal_Calculus_Extra
    Min_Max_Least_Greatest_Multiset
begin

locale ground_ordering =
  fixes
    less_trm :: "'f gterm \<Rightarrow> 'f gterm \<Rightarrow> bool" (infix "\<prec>\<^sub>t" 50)
  assumes
    transp_less_trm[intro]: "transp (\<prec>\<^sub>t)" and
    asymp_less_trm[intro]: "asymp (\<prec>\<^sub>t)" and
    wfP_less_trm[intro]: "wfP (\<prec>\<^sub>t)" and
    totalp_less_trm[intro]: "totalp (\<prec>\<^sub>t)" and
    less_trm_compatible_with_gctxt[simp]: "\<And>ctxt t t'. t \<prec>\<^sub>t t' \<Longrightarrow> ctxt\<langle>t\<rangle>\<^sub>G \<prec>\<^sub>t ctxt\<langle>t'\<rangle>\<^sub>G" and
    less_trm_if_subterm[simp]: "\<And>t ctxt. ctxt \<noteq> \<box>\<^sub>G \<Longrightarrow> t \<prec>\<^sub>t ctxt\<langle>t\<rangle>\<^sub>G"
begin

lemma irreflp_on_less_trm[simp]: "irreflp_on A (\<prec>\<^sub>t)"
  by (metis asympD asymp_less_trm irreflp_onI)

abbreviation lesseq_trm (infix "\<preceq>\<^sub>t" 50) where
  "lesseq_trm \<equiv> (\<prec>\<^sub>t)\<^sup>=\<^sup>="

lemma lesseq_trm_if_subtermeq: "t \<preceq>\<^sub>t ctxt\<langle>t\<rangle>\<^sub>G"
  using less_trm_if_subterm
  by (metis gctxt_ident_iff_eq_GHole reflclp_iff)

definition less_lit :: "'f atom literal \<Rightarrow> 'f atom literal \<Rightarrow> bool" (infix "\<prec>\<^sub>l" 50) where
  "less_lit L1 L2 \<equiv> multp (\<prec>\<^sub>t) (mset_lit L1) (mset_lit L2)"

abbreviation lesseq_lit (infix "\<preceq>\<^sub>l" 50) where
  "lesseq_lit \<equiv> (\<prec>\<^sub>l)\<^sup>=\<^sup>="

abbreviation less_cls ::
  "'f atom clause \<Rightarrow> 'f atom clause \<Rightarrow> bool" (infix "\<prec>\<^sub>c" 50) where
  "less_cls \<equiv> multp (\<prec>\<^sub>l)"

abbreviation lesseq_cls (infix "\<preceq>\<^sub>c" 50) where
  "lesseq_cls \<equiv> (\<prec>\<^sub>c)\<^sup>=\<^sup>="

lemma transp_on_less_lit[simp]: "transp_on A (\<prec>\<^sub>l)"
  by (smt (verit, ccfv_SIG) less_lit_def transpE transp_less_trm transp_multp transp_onI)

corollary transp_less_lit: "transp (\<prec>\<^sub>l)"
  by simp

lemma transp_less_cls[simp]: "transp (\<prec>\<^sub>c)"
  by (simp add: transp_multp)

lemma asymp_on_less_lit[simp]: "asymp_on A (\<prec>\<^sub>l)"
  by (metis asympD asymp_less_trm asymp_multp\<^sub>H\<^sub>O asymp_onI less_lit_def multp_eq_multp\<^sub>H\<^sub>O
      transp_less_trm)

corollary asymp_less_lit: "asymp (\<prec>\<^sub>l)"
  by simp

lemma asymp_less_cls[simp]: "asymp (\<prec>\<^sub>c)"
  by (simp add: asymp_multp\<^sub>H\<^sub>O multp_eq_multp\<^sub>H\<^sub>O)

lemma wfP_less_lit[simp]: "wfP (\<prec>\<^sub>l)"
  unfolding less_lit_def
  using wfP_less_trm wfP_multp wfP_if_convertible_to_wfP by meson

lemma wfP_less_cls[simp]: "wfP (\<prec>\<^sub>c)"
  using wfP_less_lit wfP_multp by blast

lemma totalp_on_less_lit[simp]: "totalp_on A (\<prec>\<^sub>l)"
proof (rule totalp_onI)
  fix L1 L2 :: "'f atom literal"
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

corollary totalp_less_lit: "totalp (\<prec>\<^sub>l)"
  by simp

lemma totalp_less_cls[simp]: "totalp (\<prec>\<^sub>c)"
proof (rule totalp_multp)
  show "totalp (\<prec>\<^sub>l)"
    by simp
next
  show "transp (\<prec>\<^sub>l)"
    by simp
qed

sublocale linorder_trm: linorder lesseq_trm less_trm
proof unfold_locales
  show "\<And>x y. (x \<prec>\<^sub>t y) = (x \<preceq>\<^sub>t y \<and> \<not> y \<preceq>\<^sub>t x)"
    by (metis asympD asymp_less_trm reflclp_iff)
next
  show "\<And>x. x \<preceq>\<^sub>t x"
    by simp
next
  show "\<And>x y z. x \<preceq>\<^sub>t y \<Longrightarrow> y \<preceq>\<^sub>t z \<Longrightarrow> x \<preceq>\<^sub>t z"
    by (meson transpE transp_less_trm transp_on_reflclp)
next
  show "\<And>x y. x \<preceq>\<^sub>t y \<Longrightarrow> y \<preceq>\<^sub>t x \<Longrightarrow> x = y"
    by (metis asympD asymp_less_trm reflclp_iff)
next
  show "\<And>x y. x \<preceq>\<^sub>t y \<or> y \<preceq>\<^sub>t x"
    by (metis reflclp_iff totalpD totalp_less_trm)
qed

sublocale linorder_lit: linorder lesseq_lit less_lit
proof unfold_locales
  show "\<And>x y. (x \<prec>\<^sub>l y) = (x \<preceq>\<^sub>l y \<and> \<not> y \<preceq>\<^sub>l x)"
    by (metis asympD asymp_less_lit reflclp_iff)
next
  show "\<And>x. x \<preceq>\<^sub>l x"
    by simp
next
  show "\<And>x y z. x \<preceq>\<^sub>l y \<Longrightarrow> y \<preceq>\<^sub>l z \<Longrightarrow> x \<preceq>\<^sub>l z"
    by (meson transpE transp_less_lit transp_on_reflclp)
next
  show "\<And>x y. x \<preceq>\<^sub>l y \<Longrightarrow> y \<preceq>\<^sub>l x \<Longrightarrow> x = y"
    by (metis asympD asymp_less_lit reflclp_iff)
next
  show "\<And>x y. x \<preceq>\<^sub>l y \<or> y \<preceq>\<^sub>l x"
    by (metis reflclp_iff totalpD totalp_less_lit)
qed

sublocale linorder_cls: linorder lesseq_cls less_cls
proof unfold_locales
  show "\<And>x y. (x \<prec>\<^sub>c y) = (x \<preceq>\<^sub>c y \<and> \<not> y \<preceq>\<^sub>c x)"
    by (metis asympD asymp_less_cls reflclp_iff)
next
  show "\<And>x. x \<preceq>\<^sub>c x"
    by simp
next
  show "\<And>x y z. x \<preceq>\<^sub>c y \<Longrightarrow> y \<preceq>\<^sub>c z \<Longrightarrow> x \<preceq>\<^sub>c z"
    by (meson transpE transp_less_cls transp_on_reflclp)
next
  show "\<And>x y. x \<preceq>\<^sub>c y \<Longrightarrow> y \<preceq>\<^sub>c x \<Longrightarrow> x = y"
    by (metis asympD asymp_less_cls reflclp_iff)
next
  show "\<And>x y. x \<preceq>\<^sub>c y \<or> y \<preceq>\<^sub>c x"
    by (metis reflclp_iff totalpD totalp_less_cls)
qed

abbreviation is_maximal_lit :: "'f atom literal \<Rightarrow> 'f atom clause \<Rightarrow> bool" where
  "is_maximal_lit L M \<equiv> is_maximal_in_mset_wrt (\<prec>\<^sub>l) M L"

abbreviation is_strictly_maximal_lit :: "'f atom literal \<Rightarrow> 'f atom clause \<Rightarrow> bool" where
  "is_strictly_maximal_lit L M \<equiv> is_greatest_in_mset_wrt (\<prec>\<^sub>l) M L"

end

end