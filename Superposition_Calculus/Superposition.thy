theory Superposition
  imports
    (* Theories from the Isabelle distribution *)
    Main

    (* Theories from the AFP *)
    "Ordered_Resolution_Prover.Abstract_Substitution"
    "Saturation_Framework.Calculus"
    "Saturation_Framework.Lifting_to_Non_Ground_Calculi"
    "Saturation_Framework_Extensions.Clausal_Calculus"
    "First_Order_Terms.Term"
    "Knuth_Bendix_Order.Subterm_and_Context"
    "Abstract-Rewriting.Abstract_Rewriting"

    (* Theories from CeTA *)
    "CR.Critical_Pairs"

    (* Theories from this formalization *)
    "Multiset_Extra"
    "Abstract_Substitution_Extra_First_Order_Term"
    "Unordered_Prod"
    "Term_Rewrite_System"
begin

no_notation subst_compose (infixl "\<circ>\<^sub>s" 75)
no_notation subst_apply_term (infixl "\<cdot>" 67)

hide_type Inference_System.inference
hide_const
  Inference_System.Infer
  Inference_System.prems_of
  Inference_System.concl_of
  Inference_System.main_prem_of


lemma reflclp_iff: "\<And>R x y. R\<^sup>=\<^sup>= x y \<longleftrightarrow> R x y \<or> x = y"
  by (metis sup2CI sup2E)


section \<open>HOL_Extra\<close>

lemma UniqI:
  assumes "\<And>x y. P x \<Longrightarrow> P y \<Longrightarrow> x = y"
  shows "\<exists>\<^sub>\<le>\<^sub>1x. P x"
  using assms
  by (simp add: Uniq_def)

lemma Uniq_prodI:
  assumes "\<And>x1 y1 x2 y2. P x1 y1 \<Longrightarrow> P x2 y2 \<Longrightarrow> (x1, y1) = (x2, y2)"
  shows "\<exists>\<^sub>\<le>\<^sub>1(x, y). P x y"
  using assms
  by (metis UniqI case_prodE)

lemma Uniq_mono_decr: "Q \<le> P \<Longrightarrow> Uniq Q \<ge> Uniq P"
  by (simp add: UniqI Uniq_D le_fun_def)

lemma Uniq_mono_decr': "(\<And>x. Q x \<Longrightarrow> P x) \<Longrightarrow> Uniq P \<Longrightarrow> Uniq Q"
  using Uniq_mono_decr
  by (auto simp: le_fun_def)

lemma Collect_eq_if_Uniq: "(\<exists>\<^sub>\<le>\<^sub>1x. P x) \<Longrightarrow> {x. P x} = {} \<or> (\<exists>x. {x. P x} = {x})"
  using Uniq_D by fastforce

lemma Collect_eq_if_Uniq_prod: "(\<exists>\<^sub>\<le>\<^sub>1(x, y). P x y) \<Longrightarrow> {(x, y). P x y} = {} \<or> (\<exists>x y. {(x, y). P x y} = {(x, y)})"
  using Collect_eq_if_Uniq by fastforce


section \<open>Abstract_Rewriting_Extra\<close>

lemma trans_join:
  assumes strongly_norm: "SN r" and confluent: "WCR r"
  shows "trans (r\<^sup>\<down>)"
proof -
  from confluent strongly_norm have "CR r"
    using Newman by metis
  hence "r\<^sup>\<leftrightarrow>\<^sup>* = r\<^sup>\<down>"
    using CR_imp_conversionIff_join by metis
  thus ?thesis
    using conversion_trans by metis
qed


section \<open>Abstract_Substitutions_Extra\<close>

lemma (in substitution_ops) subst_cls_cong:
  assumes "\<And>L. L \<in># C \<Longrightarrow> atm_of L \<cdot>a \<sigma> = atm_of L \<cdot>a \<tau>"
  shows "subst_cls C \<sigma> = subst_cls C \<tau>"
  unfolding subst_cls_def
proof (rule multiset.map_cong0)
  fix L assume "L \<in># C"
  with assms have "atm_of L \<cdot>a \<sigma> = atm_of L \<cdot>a \<tau>"
    by simp
  thus "L \<cdot>l \<sigma> = L \<cdot>l \<tau>"
    by (metis atm_of_subst_lit literal.expand literal.map_disc_iff subst_lit_def)
qed


section \<open>First_Order_Terms And Abstract_Substitution\<close>

notation subst_apply_term (infixl "\<cdot>t" 67)
notation subst_apply_ctxt (infixl "\<cdot>t\<^sub>c" 67)
notation subst_compose (infixl "\<odot>" 75)

type_synonym 't atom = "'t uprod"

definition subst_atm ::
  "('f, 'v) term atom \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) term atom" (infixl "\<cdot>a" 67)
where
  "subst_atm A \<sigma> = map_uprod (\<lambda>t. subst_apply_term t \<sigma>) A"

definition subst_lit ::
  "('f, 'v) term atom literal \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) term atom literal" (infixl "\<cdot>l" 67)
where
  "subst_lit L \<sigma> = map_literal (\<lambda>A. A \<cdot>a \<sigma>) L"

definition subst_cls ::
  "('f, 'v) term atom clause \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) term atom clause" (infixl "\<cdot>" 67)
where
  "subst_cls C \<sigma> = image_mset (\<lambda>L. L \<cdot>l \<sigma>) C"

definition vars_atm :: "('f, 'v) term atom \<Rightarrow> 'v set" where
  "vars_atm p = (\<Union>t \<in> set_uprod p. vars_term t)"

definition vars_lit :: "('f, 'v) term atom literal \<Rightarrow> 'v set" where
  "vars_lit L = vars_atm (atm_of L)"

definition vars_cls :: "('f, 'v) term atom clause \<Rightarrow> 'v set" where
  "vars_cls C = (\<Union>L \<in> set_mset C. vars_lit L)"

definition vars_cls_set :: "('f, 'v) term atom clause set \<Rightarrow> 'v set" where
  "vars_cls_set N = (\<Union>C \<in> N. vars_cls C)"

lemma vars_term_ctxt_apply_term[simp]: "vars_term c\<langle>t\<rangle> = vars_ctxt c \<union> vars_term t"
  by (induction c) auto

lemma vars_atm_make_uprod[simp]: "vars_atm (t\<^sub>1 \<approx> t\<^sub>2) = vars_term t\<^sub>1 \<union> vars_term t\<^sub>2"
  by (simp add: vars_atm_def)

lemma vars_lit_Pos[simp]: "vars_lit (Pos A) = vars_atm A"
  by (simp add: vars_lit_def)

lemma vars_lit_Neg[simp]: "vars_lit (Neg A) = vars_atm A"
  by (simp add: vars_lit_def)

lemma vars_cls_add_mset[simp]: "vars_cls (add_mset L C) = vars_lit L \<union> vars_cls C"
  by (simp add: vars_cls_def)

lemma vars_cls_plus[simp]: "vars_cls (C\<^sub>1 + C\<^sub>2) = vars_cls C\<^sub>1 \<union> vars_cls C\<^sub>2"
  by (simp add: vars_cls_def)

abbreviation is_ground_trm where
  "is_ground_trm t \<equiv> vars_term t = {}"

abbreviation is_ground_trm_ctxt where
  "is_ground_trm_ctxt c \<equiv> vars_ctxt c = {}"

abbreviation is_ground_atm where
  "is_ground_atm A \<equiv> vars_atm A = {}"

abbreviation is_ground_lit where
  "is_ground_lit L \<equiv> vars_lit L = {}"

abbreviation is_ground_cls where
  "is_ground_cls C \<equiv> vars_cls C = {}"

abbreviation is_ground_cls_set where
  "is_ground_cls_set N \<equiv> vars_cls_set N = {}"

lemma subst_trm_ident_if_is_ground_trm[simp]: "is_ground_trm t \<Longrightarrow> t \<cdot>t \<sigma> = t"
  by (simp add: subst_apply_term_ident)

lemma subst_trm_ctxt_ident_if_is_ground_trm_ctxt[simp]: "is_ground_trm_ctxt c \<Longrightarrow> c \<cdot>t\<^sub>c \<sigma> = c"
  by (induction c) (simp_all add: list.map_ident_strong)

lemma subst_atm_ident_if_is_ground_atm[simp]: "is_ground_atm A \<Longrightarrow> A \<cdot>a \<sigma> = A"
  by (simp add: subst_atm_def uprod.map_ident_strong vars_atm_def)

lemma subst_lit_ident_if_is_ground_lit[simp]: "is_ground_lit L \<Longrightarrow> L \<cdot>l \<sigma> = L"
  by (simp add: subst_lit_def literal.expand literal.map_sel(1) literal.map_sel(2) vars_lit_def)

lemma subst_cls_ident_if_is_ground_cls[simp]: "is_ground_cls C \<Longrightarrow> C \<cdot> \<sigma> = C"
  by (induction C) (simp_all add: subst_cls_def)

typedef ('f, 'v) gterm = \<open>{t :: ('f, 'v) term. is_ground_trm t}\<close>
  morphisms trm_gtrm gtrm_trm
proof -
  have "is_ground_trm (Fun undefined [])"
    by simp
  thus "\<exists>x. x \<in> {t. is_ground_trm t}"
    by blast
qed

definition lit_glit where
  "lit_glit = map_literal (map_uprod trm_gtrm)"

definition glit_lit where
  "glit_lit = map_literal (map_uprod gtrm_trm)"

definition gcls_cls where
  "gcls_cls \<equiv> image_mset glit_lit"

definition cls_gcls where
  "cls_gcls \<equiv> image_mset lit_glit"

lemma cls_gcls_empty_mset[simp]: "cls_gcls {#} = {#}"
  by (simp add: cls_gcls_def)

lemma lit_glit_inverse[simp]: "glit_lit (lit_glit L) = L"
  unfolding lit_glit_def glit_lit_def
  by (simp add: literal.map_comp uprod.map_comp comp_def trm_gtrm_inverse literal.map_ident_strong
      uprod.map_ident_strong)

lemma cls_gcls_inverse[simp]: "gcls_cls (cls_gcls C) = C"
  unfolding gcls_cls_def cls_gcls_def
  by simp

lemma vars_trm_gtrm[simp]: "vars_term (trm_gtrm t) = {}"
  using trm_gtrm by fastforce

lemma vars_lit_glit[simp]: "vars_lit (lit_glit L) = {}"
  unfolding lit_glit_def vars_lit_def
  by (smt (verit, ccfv_SIG) empty_iff equals0I imageE literal.map_sel(1) literal.map_sel(2)
      mem_simps(9) uprod.set_map vars_atm_def vars_trm_gtrm)

lemma vars_cls_gcls[simp]: "vars_cls (cls_gcls C) = {}"
  unfolding cls_gcls_def vars_cls_def
  by simp

lemma is_ground_lit_if_in_ground_cls[intro]:
  "L \<in># C \<Longrightarrow> is_ground_cls C \<Longrightarrow> is_ground_lit L"
  by (simp add: vars_cls_def)

lemma is_ground_atm_if_in_ground_lit[intro]:
  "A \<in> set_literal L \<Longrightarrow> is_ground_lit L \<Longrightarrow> is_ground_atm A"
  by (metis literal.set_cases vars_lit_Neg vars_lit_Pos)

lemma is_ground_term_if_in_ground_atm[intro]:
  "t \<in> set_uprod A \<Longrightarrow> is_ground_atm A \<Longrightarrow> is_ground_trm t"
  by (simp add: vars_atm_def)

lemma glit_lit_inverse[simp]: "is_ground_lit L \<Longrightarrow> lit_glit (glit_lit L) = L"
  unfolding lit_glit_def glit_lit_def
  by (auto simp: literal.map_comp uprod.map_comp comp_def lit_glit_def
      elim!: is_ground_term_if_in_ground_atm is_ground_atm_if_in_ground_lit
      intro!: literal.map_ident_strong uprod.map_ident_strong gtrm_trm_inverse)

lemma gcls_cls_inverse[simp]: "is_ground_cls C \<Longrightarrow> cls_gcls (gcls_cls C) = C"
  unfolding cls_gcls_def gcls_cls_def
  by (simp add: multiset.map_comp comp_def multiset.map_ident_strong is_ground_lit_if_in_ground_cls)


section \<open>Superposition Calculus\<close>

locale superposition_calculus =
  fixes
    less_trm :: "('f, string) term \<Rightarrow> ('f, string) term \<Rightarrow> bool" (infix "\<prec>\<^sub>t" 50) and
    select :: "('f, string) term atom clause \<Rightarrow> ('f, string) term atom clause"
  assumes
    transp_less_trm[simp]: "transp (\<prec>\<^sub>t)" and
    asymp_less_trm[simp]: "asymp (\<prec>\<^sub>t)" and
    wfP_less_trm[simp]: "wfP (\<prec>\<^sub>t)" and
    totalp_on_less_trm[simp]: "totalp_on {t. is_ground_trm t} (\<prec>\<^sub>t)" and
    less_trm_compatible_with_ctxt[simp]: "\<And>ctxt t t'. t \<prec>\<^sub>t t' \<Longrightarrow> ctxt\<langle>t\<rangle> \<prec>\<^sub>t ctxt\<langle>t'\<rangle>" and
    less_trm_subterm: "\<And>t t'. t \<lhd> t' \<Longrightarrow> t \<prec>\<^sub>t t'" and
    select_negative_lits: "\<And>C L. L \<in># select C \<Longrightarrow> is_neg L" and
    select_stable_under_renaming: "\<And>C \<rho>. term_subst.is_renaming \<rho> \<Longrightarrow> select (C \<cdot> \<rho>) = select C \<cdot> \<rho>"
begin

lemma irreflp_on_less_trm[simp]: "irreflp_on A (\<prec>\<^sub>t)"
  by (metis asympD asymp_less_trm irreflp_onI)

abbreviation lesseq_trm (infix "\<preceq>\<^sub>t" 50) where
  "lesseq_trm \<equiv> (\<prec>\<^sub>t)\<^sup>=\<^sup>="

primrec mset_lit :: "'a uprod literal \<Rightarrow> 'a multiset" where
  "mset_lit (Pos A) = mset_uprod A" |
  "mset_lit (Neg A) = mset_uprod A + mset_uprod A"

definition less_lit :: "('f, string) term atom literal \<Rightarrow> ('f, string) term atom literal \<Rightarrow> bool" (infix "\<prec>\<^sub>l" 50) where
  "less_lit L1 L2 \<equiv> multp (\<prec>\<^sub>t) (mset_lit L1) (mset_lit L2)"

abbreviation lesseq_lit (infix "\<preceq>\<^sub>l" 50) where
  "lesseq_lit \<equiv> (\<prec>\<^sub>l)\<^sup>=\<^sup>="

abbreviation less_cls :: "('f, string) term atom clause \<Rightarrow> ('f, string) term atom clause \<Rightarrow> bool" (infix "\<prec>\<^sub>c" 50) where
  "less_cls \<equiv> multp (\<prec>\<^sub>l)"

abbreviation lesseq_cls (infix "\<preceq>\<^sub>c" 50) where
  "lesseq_cls \<equiv> (\<prec>\<^sub>c)\<^sup>=\<^sup>="


lemma transp_less_lit[simp]: "transp (\<prec>\<^sub>l)"
  by (metis (no_types, lifting) less_lit_def transpD transpI transp_less_trm transp_multp)

lemma transp_less_cls[simp]: "transp (\<prec>\<^sub>c)"
  by (simp add: transp_multp)

lemma totalp_on_less_lit[simp]: "totalp_on {L. is_ground_lit L} (\<prec>\<^sub>l)"
proof (rule totalp_onI, unfold mem_Collect_eq)
  fix L1 L2 :: "('f, string) term atom literal"
  assume "is_ground_lit L1" and "is_ground_lit L2" and "L1 \<noteq> L2"
  
  let ?TT = "{T. \<forall>t \<in># T. is_ground_trm t}"

  show "L1 \<prec>\<^sub>l L2 \<or> L2 \<prec>\<^sub>l L1"
    unfolding less_lit_def
  proof (rule totalp_on_multp[THEN totalp_onD])
    show "totalp_on {t. is_ground_trm t} (\<prec>\<^sub>t)"
      using totalp_on_less_trm .
  next
    show "transp (\<prec>\<^sub>t)"
      using transp_less_trm .
  next
    show "\<And>M. M \<in> ?TT \<Longrightarrow> set_mset M \<subseteq> {t. is_ground_trm t}"
      by auto
  next
    show "mset_lit L1 \<in> ?TT"
      using \<open>is_ground_lit L1\<close>
      by (cases L1) (simp_all add: set_uprod_def vars_atm_def)
  next
    show "mset_lit L2 \<in> ?TT"
      using \<open>is_ground_lit L2\<close>
      by (cases L2) (simp_all add: set_uprod_def vars_atm_def)
  next
    obtain x1 y1 x2 y2 :: "('f, string) term" where
      "atm_of L1 = x1 \<approx> y1" and "atm_of L2 = x2 \<approx> y2"
      using ex_make_uprod by metis
    thus "mset_lit L1 \<noteq> mset_lit L2"
      using \<open>L1 \<noteq> L2\<close>
      by (cases L1; cases L2) (auto simp add: make_uprod_eq_make_uprod_iff add_eq_conv_ex)
  qed
qed

lemma totalp_on_less_cls[simp]: "totalp_on {C. is_ground_cls C} (\<prec>\<^sub>c)"
proof (rule totalp_on_multp)
  show "totalp_on {L. is_ground_lit L} (\<prec>\<^sub>l)"
    by simp
next
  show "transp (\<prec>\<^sub>l)"
    by simp
next
  show "\<And>M. M \<in> {C. is_ground_cls C} \<Longrightarrow> set_mset M \<subseteq> {L. is_ground_lit L}"
    by (metis (mono_tags, lifting) insert_DiffM mem_Collect_eq subsetI sup_eq_bot_iff
        vars_cls_add_mset)
qed

lemma wfP_less_lit[simp]: "wfP (\<prec>\<^sub>l)"
  unfolding less_lit_def
  using wfP_less_trm wfP_multp wfP_if_convertible_to_wfP by meson

lemma wfP_less_cls[simp]: "wfP (\<prec>\<^sub>c)"
  using wfP_less_lit wfP_multp by blast


subsection \<open>Rules\<close>

abbreviation is_maximal_lit where
  "is_maximal_lit \<equiv> is_maximal_wrt (\<prec>\<^sub>l)"

abbreviation is_strictly_maximal_lit where
  "is_strictly_maximal_lit \<equiv> is_maximal_wrt (\<preceq>\<^sub>l)"

inductive superposition ::
  "('f, string) term atom clause \<Rightarrow> ('f, string) term atom clause \<Rightarrow> ('f, string) term atom clause \<Rightarrow> bool"
where
  superpositionI: "
    term_subst.is_renaming \<rho>\<^sub>1 \<Longrightarrow>
    term_subst.is_renaming \<rho>\<^sub>2 \<Longrightarrow>
    vars_cls (P\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter> vars_cls (P\<^sub>2 \<cdot> \<rho>\<^sub>2) = {} \<Longrightarrow>
    P\<^sub>1 = add_mset L\<^sub>1 P\<^sub>1' \<Longrightarrow>
    P\<^sub>2 = add_mset L\<^sub>2 P\<^sub>2' \<Longrightarrow>
    \<P> \<in> {Pos, Neg} \<Longrightarrow>
    L\<^sub>1 = \<P> (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<approx> s\<^sub>1') \<Longrightarrow>
    L\<^sub>2 = Pos (t\<^sub>2 \<approx> t\<^sub>2') \<Longrightarrow>
    \<not> is_Var u\<^sub>1 \<Longrightarrow>
    term_subst.is_imgu \<mu> {{u\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}} \<Longrightarrow>
    \<not> (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<preceq>\<^sub>c P\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    (\<P> = Pos \<and> is_strictly_maximal_lit (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>)) \<or>
    (\<P> = Neg \<and> (select P\<^sub>1 = {#} \<and> is_maximal_lit (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>) \<or> L\<^sub>1 \<in># select P\<^sub>1)) \<Longrightarrow>
    is_strictly_maximal_lit (L\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu>) (P\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    \<not> (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu>) \<Longrightarrow>
    \<not> (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<preceq>\<^sub>t t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu>) \<Longrightarrow>
    C = add_mset (\<P> ((s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> \<approx> s\<^sub>1' \<cdot>t \<rho>\<^sub>1)) (P\<^sub>1' \<cdot> \<rho>\<^sub>1 + P\<^sub>2' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu> \<Longrightarrow>
    superposition P\<^sub>1 P\<^sub>2 C"

inductive eq_resolution :: "('f, string) term atom clause \<Rightarrow> ('f, string) term atom clause \<Rightarrow> bool" where
  eq_resolutionI: "
    P = add_mset L P' \<Longrightarrow>
    L = Neg (s\<^sub>1 \<approx> s\<^sub>2) \<Longrightarrow>
    term_subst.is_imgu \<mu> {{s\<^sub>1, s\<^sub>2}} \<Longrightarrow>
    select P = {#} \<and> is_maximal_lit (L \<cdot>l \<mu>) (P \<cdot> \<mu>) \<or> L \<in># select P \<Longrightarrow>
    C = P' \<cdot> \<mu> \<Longrightarrow>
    eq_resolution P C"

inductive eq_factoring :: "('f, string) term atom clause \<Rightarrow> ('f, string) term atom clause \<Rightarrow> bool" where
  eq_factoringI: "
    P = add_mset L\<^sub>1 (add_mset L\<^sub>2 P') \<Longrightarrow>
    L\<^sub>1 = Pos (s\<^sub>1 \<approx> s\<^sub>1') \<Longrightarrow>
    L\<^sub>2 = Pos (t\<^sub>2 \<approx> t\<^sub>2') \<Longrightarrow>
    select P = {#} \<and> is_maximal_lit (L\<^sub>1 \<cdot>l \<mu>) (P \<cdot> \<mu>) \<Longrightarrow>
    \<not> (s\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t s\<^sub>1' \<cdot>t \<mu>) \<Longrightarrow>
    term_subst.is_imgu \<mu> {{s\<^sub>1, t\<^sub>2}} \<Longrightarrow>
    C = add_mset (Pos (s\<^sub>1 \<approx> t\<^sub>2')) (add_mset (Neg (s\<^sub>1' \<approx> t\<^sub>2')) P') \<cdot> \<mu> \<Longrightarrow>
    eq_factoring P C"


lemma subst_lit_Pos: "Pos A \<cdot>l \<sigma> = Pos (A \<cdot>a \<sigma>)"
  by (simp add: subst_lit_def)

lemma subst_lit_Neg: "Neg A \<cdot>l \<sigma> = Neg (A \<cdot>a \<sigma>)"
  by (simp add: subst_lit_def)

lemma subst_cls_add_mset: "add_mset L C \<cdot> \<sigma> = add_mset (L \<cdot>l \<sigma>) (C \<cdot> \<sigma>)"
  by (simp add: subst_cls_def)

lemma subst_cls_plus: "(C\<^sub>1 + C\<^sub>2) \<cdot> \<sigma> = (C\<^sub>1 \<cdot> \<sigma>) + (C\<^sub>2 \<cdot> \<sigma>)"
  by (simp add: subst_cls_def)

lemma superposition_preserves_groundness:
  assumes
    step: "superposition P1 P2 C" and
    ground_P1: "is_ground_cls P1" and
    ground_P2: "is_ground_cls P2"
  shows "is_ground_cls C"
  using step
proof (cases P1 P2 C rule: superposition.cases)
  case (superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' \<P> s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)
  with ground_P1 ground_P2 have
    "is_ground_cls P\<^sub>1'" and "is_ground_cls P\<^sub>2'" and
    "is_ground_trm_ctxt s\<^sub>1" and "is_ground_trm u\<^sub>1" and "is_ground_trm s\<^sub>1'" and
    "is_ground_trm t\<^sub>2" and "is_ground_trm t\<^sub>2'"
    by auto
  thus ?thesis
    unfolding superpositionI
    using \<open>\<P> \<in> {Pos, Neg}\<close>
    by (auto simp: subst_cls_add_mset)
qed

lemma eq_resolution_preserves_groundness:
  assumes step: "eq_resolution P C" and ground_P: "is_ground_cls P"
  shows "is_ground_cls C"
  using step
proof (cases P C rule: eq_resolution.cases)
  case (eq_resolutionI L P' s\<^sub>1 s\<^sub>2 \<mu>)
  with ground_P have "is_ground_cls P'"
    by (simp add: vars_cls_def)
  thus ?thesis
    unfolding eq_resolutionI by simp
qed

lemma eq_factoring_preserves_groundness:
  assumes step: "eq_factoring P C" and ground_P: "is_ground_cls P"
  shows "is_ground_cls C"
  using step
proof (cases P C rule: eq_factoring.cases)
  case (eq_factoringI L\<^sub>1 L\<^sub>2 P' s\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)
  with ground_P have "is_ground_cls P'"
    "is_ground_trm s\<^sub>1" "is_ground_trm s\<^sub>1'"
    "is_ground_trm t\<^sub>2" "is_ground_trm t\<^sub>2'"
    by simp_all
  thus ?thesis
    unfolding eq_factoringI by simp
qed


subsection \<open>Ground Layer\<close>

definition gcls_cls where
  "gcls_cls \<equiv> map_clause (map_uprod gtrm_trm)"

definition cls_gcls where
  "cls_gcls \<equiv> map_clause (map_uprod trm_gtrm)"

lemma cls_gcls_empty_mset[simp]: "cls_gcls {#} = {#}"
  by (simp add: cls_gcls_def)

lemma cls_gcls_inverse[simp]: "gcls_cls (cls_gcls C) = C"
  unfolding gcls_cls_def cls_gcls_def
  by (simp add: multiset.map_comp literal.map_comp uprod.map_comp comp_def
      literal.map_ident_strong trm_gtrm_inverse uprod.map_ident_strong)

lemma is_ground_cls_gcls[simp]: "is_ground_cls (cls_gcls C)"
  unfolding cls_gcls_def
  apply (simp add: vars_cls_def vars_lit_def vars_atm_def)
  by (smt (verit) imageE literal.map_sel(1) literal.map_sel(2) mem_Collect_eq trm_gtrm
      uprod.set_map)

lemma is_ground_lit_if_in_ground_cls[intro]:
  "L \<in># C \<Longrightarrow> is_ground_cls C \<Longrightarrow> is_ground_lit L"
  by (simp add: vars_cls_def)

lemma is_ground_atm_if_in_ground_lit[intro]:
  "A \<in> set_literal L \<Longrightarrow> is_ground_lit L \<Longrightarrow> is_ground_atm A"
  by (metis literal.set_cases vars_lit_Neg vars_lit_Pos)

lemma is_ground_term_if_in_ground_atm[intro]:
  "t \<in> set_uprod A \<Longrightarrow> is_ground_atm A \<Longrightarrow> is_ground_trm t"
  by (simp add: vars_atm_def)

lemma gcls_cls_inverse[simp]: "is_ground_cls C \<Longrightarrow> cls_gcls (gcls_cls C) = C"
  unfolding cls_gcls_def gcls_cls_def
  by (auto simp: literal.map_comp uprod.map_comp comp_def
      elim!: is_ground_term_if_in_ground_atm is_ground_atm_if_in_ground_lit is_ground_lit_if_in_ground_cls
      intro!: multiset.map_ident_strong literal.map_ident_strong uprod.map_ident_strong gtrm_trm_inverse)

definition G_Inf :: "('f, string) gterm atom clause inference set" where
  "G_Inf \<equiv>
    {Infer [P\<^sub>2, P\<^sub>1] (gcls_cls C) | P\<^sub>2 P\<^sub>1 C. superposition (cls_gcls P\<^sub>1) (cls_gcls P\<^sub>2) C} \<union>
    {Infer [P] (gcls_cls C) | P C. eq_resolution (cls_gcls P) C} \<union>
    {Infer [P] (gcls_cls C) | P C. eq_factoring (cls_gcls P) C}"

abbreviation G_Bot :: "('f, string) gterm atom clause set" where
  "G_Bot \<equiv> {{#}}"

definition G_entails ::
  "('f, string) gterm atom clause set \<Rightarrow> ('f, string) gterm atom clause set \<Rightarrow> bool"
where
  "G_entails N\<^sub>1 N\<^sub>2 \<longleftrightarrow> (\<forall>(I :: (('f, string) Term.term \<times> ('f, string) Term.term) set).
    refl I \<longrightarrow> trans I \<longrightarrow> sym I \<longrightarrow> compatible_with_ctxt I \<longrightarrow>
    (\<lambda>(t\<^sub>1, t\<^sub>2). t\<^sub>1 \<approx> t\<^sub>2) ` I \<TTurnstile>s (cls_gcls ` N\<^sub>1) \<longrightarrow>
    (\<lambda>(t\<^sub>1, t\<^sub>2). t\<^sub>1 \<approx> t\<^sub>2) ` I \<TTurnstile>s (cls_gcls ` N\<^sub>2))"


subsubsection \<open>Correctness\<close>

lemma true_lit_uprod_iff_true_lit_prod[simp]:
  assumes "sym I"
  shows
    "(\<lambda>(t\<^sub>1, t\<^sub>2). t\<^sub>1 \<approx> t\<^sub>2) ` I \<TTurnstile>l Pos (t \<approx> t') \<longleftrightarrow> I \<TTurnstile>l Pos (t, t')"
    "(\<lambda>(t\<^sub>1, t\<^sub>2). t\<^sub>1 \<approx> t\<^sub>2) ` I \<TTurnstile>l Neg (t \<approx> t') \<longleftrightarrow> I \<TTurnstile>l Neg (t, t')"
  unfolding true_lit_simps atomize_conj
  using \<open>sym I\<close>[THEN symD]
  by (smt (z3) case_prod_unfold image_iff make_uprod_eq_make_uprod_iff pair_imageI prod.collapse)

lemma correctness_ground_superposition:
  assumes
    step: "superposition P1 P2 C" and
    ground_P1: "is_ground_cls P1" and
    ground_P2: "is_ground_cls P2"
  shows "G_entails {gcls_cls P1, gcls_cls P2} {gcls_cls C}"
  using step
proof (cases P1 P2 C rule: superposition.cases)
  case (superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' \<P> s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)
  with ground_P1 ground_P2 have
    "is_ground_atm (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<approx> s\<^sub>1')" and "is_ground_cls P\<^sub>1'" and
    "is_ground_atm (t\<^sub>2 \<approx> t\<^sub>2')" and "is_ground_cls P\<^sub>2'"
    by (metis insert_iff singletonD sup_eq_bot_iff vars_cls_add_mset vars_lit_Neg vars_lit_Pos)+
  hence
    "is_ground_trm s\<^sub>1\<langle>u\<^sub>1\<rangle>" and "is_ground_trm_ctxt s\<^sub>1" and "is_ground_trm u\<^sub>1" and
    "is_ground_trm s\<^sub>1'" and "is_ground_trm t\<^sub>2" and "is_ground_trm t\<^sub>2'"
    by simp_all
  hence "term_subst.is_ground_set {u\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}"
    by (simp add: term_subst.is_ground_set_def term_subst.is_ground_def)
  moreover have "term_subst.is_unifier \<mu> {u\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}"
    using \<open>term_subst.is_imgu \<mu> {{u\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}}\<close>
    by (simp add: term_subst.is_imgu_def term_subst.is_unifiers_def)
  ultimately have "u\<^sub>1 = t\<^sub>2"
    using term_subst.ball_eq_constant_if_unifier[of "{_}" \<mu>, simplified]
    using \<open>is_ground_trm t\<^sub>2\<close> \<open>is_ground_trm u\<^sub>1\<close> by auto

  have 1: "cls_gcls ` {gcls_cls P1, gcls_cls P2} = {P1, P2}"
    using ground_P1 ground_P2 by simp_all

  have 2: "cls_gcls ` {gcls_cls C} = {C}"
    using superposition_preserves_groundness[OF step ground_P1 ground_P2] by simp

  show ?thesis
    unfolding G_entails_def 1 2 true_clss_singleton
    unfolding true_clss_insert
  proof (intro allI impI, elim conjE)
    fix I :: "(('f, string) Term.term \<times> ('f, string) Term.term) set"

    let ?I' = "(\<lambda>(t\<^sub>1, t\<^sub>2). t\<^sub>1 \<approx> t\<^sub>2) ` I"

    assume "refl I" and "trans I" and "sym I" and "compatible_with_ctxt I" and
      "?I' \<TTurnstile> P1" and "?I' \<TTurnstile> P2"
    then obtain K1 K2 :: "('f, string) Term.term uprod literal" where
      "K1 \<in># P1" and "?I' \<TTurnstile>l K1" and "K2 \<in># P2" and "?I' \<TTurnstile>l K2"
      by (auto simp: true_cls_def)

    show "?I' \<TTurnstile> C"
    proof (cases "K1 = \<P> (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<approx> s\<^sub>1')")
      case K1_def: True
      hence "?I' \<TTurnstile>l \<P> (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<approx> s\<^sub>1')"
        using \<open>?I' \<TTurnstile>l K1\<close> by simp

      show ?thesis
      proof (cases "K2 = Pos (t\<^sub>2 \<approx> t\<^sub>2')")
        case K2_def: True
        hence "(t\<^sub>2, t\<^sub>2') \<in> I"
          using \<open>?I' \<TTurnstile>l K2\<close> true_lit_uprod_iff_true_lit_prod[OF \<open>sym I\<close>] by simp

        have ?thesis if "\<P> = Pos"
        proof -
          from that have "(s\<^sub>1\<langle>u\<^sub>1\<rangle>, s\<^sub>1') \<in> I"
            using \<open>?I' \<TTurnstile>l K1\<close> K1_def true_lit_uprod_iff_true_lit_prod[OF \<open>sym I\<close>] by simp
          hence "(s\<^sub>1\<langle>t\<^sub>2'\<rangle>, s\<^sub>1') \<in> I"
            unfolding \<open>u\<^sub>1 = t\<^sub>2\<close>
            using \<open>(t\<^sub>2, t\<^sub>2') \<in> I\<close>
            using \<open>compatible_with_ctxt I\<close> \<open>refl I\<close> \<open>sym I\<close> \<open>trans I\<close>
            by (meson compatible_with_ctxtD refl_onD1 symD trans_onD)
          hence "?I' \<TTurnstile>l Pos (s\<^sub>1\<langle>t\<^sub>2'\<rangle> \<approx> s\<^sub>1')"
            by blast
          thus ?thesis
            unfolding superpositionI that
            using \<open>is_ground_trm_ctxt s\<^sub>1\<close> \<open>is_ground_trm t\<^sub>2'\<close> \<open>is_ground_trm s\<^sub>1'\<close>
              \<open>is_ground_cls P\<^sub>1'\<close> \<open>is_ground_cls P\<^sub>2'\<close>
            by simp
        qed

        moreover have ?thesis if "\<P> = Neg"
        proof -
          from that have "(s\<^sub>1\<langle>u\<^sub>1\<rangle>, s\<^sub>1') \<notin> I"
            using \<open>?I' \<TTurnstile>l K1\<close> K1_def true_lit_uprod_iff_true_lit_prod[OF \<open>sym I\<close>] by simp
          hence "(s\<^sub>1\<langle>t\<^sub>2'\<rangle>, s\<^sub>1') \<notin> I"
            unfolding \<open>u\<^sub>1 = t\<^sub>2\<close>
            using \<open>(t\<^sub>2, t\<^sub>2') \<in> I\<close>
            using \<open>compatible_with_ctxt I\<close> \<open>trans I\<close>
            by (metis compatible_with_ctxtD transD)
          hence "?I' \<TTurnstile>l Neg (s\<^sub>1\<langle>t\<^sub>2'\<rangle> \<approx> s\<^sub>1')"
            by (meson \<open>sym I\<close> true_lit_simps(2) true_lit_uprod_iff_true_lit_prod(2))
          thus ?thesis
            unfolding superpositionI that
            using \<open>is_ground_trm_ctxt s\<^sub>1\<close> \<open>is_ground_trm t\<^sub>2'\<close> \<open>is_ground_trm s\<^sub>1'\<close>
              \<open>is_ground_cls P\<^sub>1'\<close> \<open>is_ground_cls P\<^sub>2'\<close>
            by simp
        qed

        ultimately show ?thesis
          using \<open>\<P> \<in> {Pos, Neg}\<close> by auto
      next
        case False
        hence "K2 \<in># P\<^sub>2'"
          using \<open>K2 \<in># P2\<close>
          unfolding superpositionI by simp
        hence "?I' \<TTurnstile> P\<^sub>2'"
          using \<open>?I' \<TTurnstile>l K2\<close> by blast
        thus ?thesis
          unfolding superpositionI
          using \<open>is_ground_cls P\<^sub>2'\<close>
          by (simp add: subst_cls_add_mset subst_cls_plus)
      qed
    next
      case False
      hence "K1 \<in># P\<^sub>1'"
        using \<open>K1 \<in># P1\<close>
        unfolding superpositionI by simp
      hence "?I' \<TTurnstile> P\<^sub>1'"
        using \<open>?I' \<TTurnstile>l K1\<close> by blast
      moreover have "\<And>\<sigma>. P\<^sub>1' \<cdot> \<sigma> = P\<^sub>1'"
        using ground_P1
        unfolding superpositionI by force
      ultimately show ?thesis
        unfolding superpositionI
        by (simp add: subst_cls_add_mset subst_cls_plus)
    qed
  qed
qed

lemma correctness_ground_eq_resolution:
  assumes step: "eq_resolution P C" and ground_P: "is_ground_cls P"
  shows "G_entails {gcls_cls P} {gcls_cls C}"
  using step
proof (cases P C rule: eq_resolution.cases)
  case (eq_resolutionI L P' t\<^sub>1 t\<^sub>2 \<mu>)
  with ground_P have "is_ground_atm (t\<^sub>1 \<approx> t\<^sub>2)"
    by simp
  hence "is_ground_trm t\<^sub>1" and "is_ground_trm t\<^sub>2"
    by simp_all
  hence "term_subst.is_ground_set {t\<^sub>1, t\<^sub>2}"
    by (simp add: term_subst.is_ground_set_def term_subst.is_ground_def)

  moreover from \<open>term_subst.is_imgu \<mu> {{t\<^sub>1, t\<^sub>2}}\<close> have "term_subst.is_unifier \<mu> {t\<^sub>1, t\<^sub>2}"
    by (simp add: term_subst.is_imgu_def term_subst.is_unifiers_def)

  ultimately have "t\<^sub>1 = t\<^sub>2"
    using term_subst.ball_eq_constant_if_unifier[of "{t\<^sub>2}" \<mu> t\<^sub>1] by simp

  have 1: "cls_gcls ` {gcls_cls P} = {P}"
    using ground_P by simp

  have 2: "cls_gcls ` {gcls_cls C} = {C}"
    using eq_resolution_preserves_groundness[OF step ground_P] by simp

  show ?thesis
    unfolding G_entails_def 1 2 true_clss_singleton
  proof (intro allI impI)
    fix I
    assume "refl I" and "(\<lambda>(t\<^sub>1, t\<^sub>2). t\<^sub>1 \<approx> t\<^sub>2) ` I \<TTurnstile> P"
    then obtain K where "K \<in># P" and "(\<lambda>(t\<^sub>1, t\<^sub>2). t\<^sub>1 \<approx> t\<^sub>2) ` I \<TTurnstile>l K"
      by (auto simp: true_cls_def)
    hence "K \<noteq> L"
      by (metis \<open>refl I\<close> \<open>t\<^sub>1 = t\<^sub>2\<close> local.eq_resolutionI(2) pair_imageI reflD true_lit_simps(2))
    hence "K \<in># P'"
      using \<open>K \<in># P\<close> \<open>P = add_mset L P'\<close> by simp
    hence "K \<in># P' \<cdot> \<mu>"
      using ground_P eq_resolutionI(1) by fastforce
    thus "(\<lambda>(t\<^sub>1, t\<^sub>2). t\<^sub>1 \<approx> t\<^sub>2) ` I \<TTurnstile> C"
      using \<open>C = P' \<cdot> \<mu>\<close> \<open>(\<lambda>(t\<^sub>1, t\<^sub>2). t\<^sub>1 \<approx> t\<^sub>2) ` I \<TTurnstile>l K\<close> by blast
  qed
qed

lemma correctness_ground_eq_factoring:
  assumes step: "eq_factoring P C" and ground_P: "is_ground_cls P"
  shows "G_entails {gcls_cls P} {gcls_cls C}"
  using step
proof (cases P C rule: eq_factoring.cases)
  case (eq_factoringI L\<^sub>1 L\<^sub>2 P' s\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)
  with ground_P have "is_ground_atm (s\<^sub>1 \<approx> s\<^sub>1')" and "is_ground_atm (t\<^sub>2 \<approx> t\<^sub>2')"
    by simp_all
  hence "is_ground_trm s\<^sub>1" and "is_ground_trm s\<^sub>1'" and "is_ground_trm t\<^sub>2" and "is_ground_trm t\<^sub>2'"
    by simp_all
  hence "term_subst.is_ground_set {s\<^sub>1, t\<^sub>2}"
    by (simp add: term_subst.is_ground_set_def term_subst.is_ground_def)
  moreover from \<open>term_subst.is_imgu \<mu> {{s\<^sub>1, t\<^sub>2}}\<close> have "term_subst.is_unifier \<mu> {s\<^sub>1, t\<^sub>2}"
    by (simp add: term_subst.is_imgu_def term_subst.is_unifiers_def)
  ultimately have "s\<^sub>1 = t\<^sub>2"
    using term_subst.ball_eq_constant_if_unifier[of "{t\<^sub>2}" \<mu> s\<^sub>1] by simp

  have 1: "cls_gcls ` {gcls_cls P} = {P}"
    using ground_P by simp

  have 2: "cls_gcls ` {gcls_cls C} = {C}"
    using eq_factoring_preserves_groundness[OF step ground_P] by simp

  show ?thesis
    unfolding G_entails_def 1 2 true_clss_singleton
  proof (intro allI impI)
    fix I :: "(('f, string) Term.term \<times> ('f, string) Term.term) set"

    let ?I' = "(\<lambda>(t\<^sub>1, t\<^sub>2). t\<^sub>1 \<approx> t\<^sub>2) ` I"

    assume "trans I" and "sym I" and "?I' \<TTurnstile> P"
    then obtain K :: "('f, string) Term.term uprod literal" where
      "K \<in># P" and "?I' \<TTurnstile>l K"
      by (auto simp: true_cls_def)

    show "?I' \<TTurnstile> C"
    proof (cases "K = L\<^sub>1 \<or> K = L\<^sub>2")
      case True
      hence "I \<TTurnstile>l Pos (t\<^sub>2, s\<^sub>1') \<or> I \<TTurnstile>l Pos (t\<^sub>2, t\<^sub>2')"
        unfolding eq_factoringI \<open>s\<^sub>1 = t\<^sub>2\<close>
        using \<open>?I' \<TTurnstile>l K\<close> true_lit_uprod_iff_true_lit_prod[OF \<open>sym I\<close>] by metis
      hence "I \<TTurnstile>l Pos (s\<^sub>1, t\<^sub>2') \<or> I \<TTurnstile>l Neg (s\<^sub>1', t\<^sub>2')"
      proof (elim disjE)
        assume "I \<TTurnstile>l Pos (t\<^sub>2, s\<^sub>1')"
        then show ?thesis
          unfolding \<open>s\<^sub>1 = t\<^sub>2\<close> true_lit_simps
          by (metis \<open>trans I\<close> transD)
      next
        assume "I \<TTurnstile>l Pos (t\<^sub>2, t\<^sub>2')"
        then show ?thesis
          using \<open>s\<^sub>1 = t\<^sub>2\<close> by simp
      qed
      hence "?I' \<TTurnstile>l Pos (s\<^sub>1 \<approx> t\<^sub>2') \<or> ?I' \<TTurnstile>l Neg (s\<^sub>1' \<approx> t\<^sub>2')"
        unfolding true_lit_uprod_iff_true_lit_prod[OF \<open>sym I\<close>] .
      hence "?I' \<TTurnstile>l Pos (s\<^sub>1 \<approx> t\<^sub>2') \<cdot>l \<mu> \<or> ?I' \<TTurnstile>l Neg (s\<^sub>1' \<approx> t\<^sub>2') \<cdot>l \<mu>"
        using \<open>is_ground_atm (s\<^sub>1 \<approx> s\<^sub>1')\<close> \<open>is_ground_atm (t\<^sub>2 \<approx> t\<^sub>2')\<close> by auto
      thus ?thesis
        unfolding eq_factoringI
        by (metis subst_cls_add_mset true_cls_add_mset)
    next
      case False
      hence "K \<in># P'"
        using \<open>K \<in># P\<close>
        unfolding eq_factoringI
        by auto
      hence "K \<in># C"
        using ground_P
        by (simp add: eq_factoringI(1,2,3,7))
      thus ?thesis
        using \<open>(\<lambda>(t\<^sub>1, t\<^sub>2). t\<^sub>1 \<approx> t\<^sub>2) ` I \<TTurnstile>l K\<close> by blast
    qed
  qed
qed

interpretation G: sound_inference_system G_Inf G_Bot G_entails
proof unfold_locales
  show "G_Bot \<noteq> {}"
    by simp
next
  show "\<And>B N. B \<in> G_Bot \<Longrightarrow> G_entails {B} N"
    by (simp add: G_entails_def)
next
  show "\<And>N2 N1. N2 \<subseteq> N1 \<Longrightarrow> G_entails N1 N2"
    by (auto simp: G_entails_def elim!: true_clss_mono[rotated])
next
  fix N1 N2 assume ball_G_entails: "\<forall>C \<in> N2. G_entails N1 {C}"
  show "G_entails N1 N2"
    unfolding G_entails_def
  proof (intro allI impI)
    fix I
    assume "refl I" and "trans I" and "sym I" and "compatible_with_ctxt I" and
      "(\<lambda>(x, y). x \<approx> y) ` I \<TTurnstile>s cls_gcls ` N1"
    hence "\<forall>C \<in> N2. (\<lambda>(x, y). x \<approx> y) ` I \<TTurnstile>s {cls_gcls C}"
      using ball_G_entails by (simp add: G_entails_def)
    then show "(\<lambda>(x, y). x \<approx> y) ` I \<TTurnstile>s cls_gcls ` N2"
      by (simp add: true_clss_def)
  qed
next
  show "\<And>N1 N2 N3. G_entails N1 N2 \<Longrightarrow> G_entails N2 N3 \<Longrightarrow> G_entails N1 N3"
    using G_entails_def by simp
next
  show "\<And>\<iota>. \<iota> \<in> G_Inf \<Longrightarrow> G_entails (set (prems_of \<iota>)) {concl_of \<iota>}"
    unfolding G_Inf_def
    using correctness_ground_superposition
    using correctness_ground_eq_resolution
    using correctness_ground_eq_factoring
    by (auto simp: G_entails_def)
qed


subsubsection \<open>Redundancy Criterion\<close>

lemma smaller_conclusion_ground_superposition:
  assumes
    step: "superposition P1 P2 C" and
    ground_P1: "is_ground_cls P1" and
    ground_P2: "is_ground_cls P2"
  shows "C \<prec>\<^sub>c P1"
  using step
proof (cases P1 P2 C rule: superposition.cases)
  case (superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' \<P> s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)
  with ground_P1 ground_P2 have
    "is_ground_atm (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<approx> s\<^sub>1')" and "is_ground_cls P\<^sub>1'" and
    "is_ground_atm (t\<^sub>2 \<approx> t\<^sub>2')" and "is_ground_cls P\<^sub>2'"
    by (metis insert_iff singletonD sup_eq_bot_iff vars_cls_add_mset vars_lit_Neg vars_lit_Pos)+
  hence
    "is_ground_trm s\<^sub>1\<langle>u\<^sub>1\<rangle>" and "is_ground_trm_ctxt s\<^sub>1" and "is_ground_trm u\<^sub>1" and
    "is_ground_trm s\<^sub>1'" and "is_ground_trm t\<^sub>2" and "is_ground_trm t\<^sub>2'"
    by simp_all
  hence "term_subst.is_ground_set {u\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}"
    by (simp add: term_subst.is_ground_set_def term_subst.is_ground_def)
  moreover have "term_subst.is_unifier \<mu> {u\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}"
    using \<open>term_subst.is_imgu \<mu> {{u\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}}\<close>
    by (simp add: term_subst.is_imgu_def term_subst.is_unifiers_def)
  ultimately have "u\<^sub>1 = t\<^sub>2"
    using term_subst.ball_eq_constant_if_unifier[of "{_}" \<mu>, simplified]
    using \<open>is_ground_trm t\<^sub>2\<close> \<open>is_ground_trm u\<^sub>1\<close> by auto

  have "P2 \<prec>\<^sub>c P1"
    using \<open>\<not> (P1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<preceq>\<^sub>c P2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>)\<close> ground_P1 ground_P2
    using totalp_on_less_cls[THEN totalp_onD] by auto

  have "s\<^sub>1' \<prec>\<^sub>t s\<^sub>1\<langle>u\<^sub>1\<rangle>"
    using \<open>\<not> s\<^sub>1\<langle>u\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu>\<close> \<open>is_ground_trm s\<^sub>1\<langle>u\<^sub>1\<rangle>\<close> \<open>is_ground_trm s\<^sub>1'\<close>
    using totalp_on_less_trm[THEN totalp_onD, simplified]
    by (metis reflclp_iff subst_trm_ident_if_is_ground_trm)

  have "t\<^sub>2' \<prec>\<^sub>t t\<^sub>2"
    by (metis (mono_tags) \<open>is_ground_trm t\<^sub>2'\<close> \<open>is_ground_trm u\<^sub>1\<close> \<open>u\<^sub>1 = t\<^sub>2\<close> superpositionI(15)
        mem_Collect_eq subst_trm_ident_if_is_ground_trm sup2I1 sup2I2 totalp_onD totalp_on_less_trm)

  have "P\<^sub>1' + add_mset (\<P> (s\<^sub>1\<langle>t\<^sub>2'\<rangle> \<approx> s\<^sub>1')) P\<^sub>2' \<prec>\<^sub>c P\<^sub>1' + {#\<P> (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<approx> s\<^sub>1')#}"
  proof (intro one_step_implies_multp ballI)
    fix K assume "K \<in># add_mset (\<P> (s\<^sub>1\<langle>t\<^sub>2'\<rangle> \<approx> s\<^sub>1')) P\<^sub>2'"

    moreover have "\<P> (s\<^sub>1\<langle>t\<^sub>2'\<rangle> \<approx> s\<^sub>1') \<prec>\<^sub>l \<P> (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<approx> s\<^sub>1')"
    proof -
      have "t\<^sub>2' \<prec>\<^sub>t u\<^sub>1"
        using \<open>t\<^sub>2' \<prec>\<^sub>t t\<^sub>2\<close> \<open>u\<^sub>1 = t\<^sub>2\<close> by simp
      hence "s\<^sub>1\<langle>t\<^sub>2'\<rangle> \<prec>\<^sub>t s\<^sub>1\<langle>u\<^sub>1\<rangle>"
        using less_trm_compatible_with_ctxt by simp
      hence "multp (\<prec>\<^sub>t) {#s\<^sub>1\<langle>t\<^sub>2'\<rangle>, s\<^sub>1'#} {#s\<^sub>1\<langle>u\<^sub>1\<rangle>, s\<^sub>1'#}"
        by (simp add: add_mset_commute multp_cancel_add_mset)

      have ?thesis if "\<P> = Pos"
        unfolding that less_lit_def
        using \<open>multp (\<prec>\<^sub>t) {#s\<^sub>1\<langle>t\<^sub>2'\<rangle>, s\<^sub>1'#} {#s\<^sub>1\<langle>u\<^sub>1\<rangle>, s\<^sub>1'#}\<close> by simp

      moreover have ?thesis if "\<P> = Neg"
        unfolding that less_lit_def
        using \<open>multp (\<prec>\<^sub>t) {#s\<^sub>1\<langle>t\<^sub>2'\<rangle>, s\<^sub>1'#} {#s\<^sub>1\<langle>u\<^sub>1\<rangle>, s\<^sub>1'#}\<close>
        using multp_double_doubleI by force

      ultimately show ?thesis
        using \<open>\<P> \<in> {Pos, Neg}\<close> by auto
    qed

    moreover have "\<forall>K \<in># P\<^sub>2'. K \<prec>\<^sub>l \<P> (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<approx> s\<^sub>1')"
    proof -
      have "is_strictly_maximal_lit (L\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu>) (P2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>)"
        using superpositionI by simp
      hence "is_strictly_maximal_lit L\<^sub>2 P2"
        using \<open>is_ground_atm (t\<^sub>2 \<approx> t\<^sub>2')\<close> ground_P2 superpositionI(8) by auto
      hence "\<forall>K \<in># P\<^sub>2'. \<not> Pos (t\<^sub>2 \<approx> t\<^sub>2') \<prec>\<^sub>l K \<and> Pos (t\<^sub>2 \<approx> t\<^sub>2') \<noteq> K"
        unfolding is_maximal_wrt_def superpositionI by simp
      hence "\<forall>K \<in># P\<^sub>2'. K \<prec>\<^sub>l Pos (t\<^sub>2 \<approx> t\<^sub>2')"
        using totalp_on_less_lit[THEN totalp_onD, unfolded mem_Collect_eq]
        by (metis (mono_tags, lifting) \<open>is_ground_atm (t\<^sub>2 \<approx> t\<^sub>2')\<close> \<open>is_ground_cls P\<^sub>2'\<close>
            is_ground_lit_if_in_ground_cls vars_lit_Pos)

      moreover have "Pos (t\<^sub>2 \<approx> t\<^sub>2') \<prec>\<^sub>l \<P> (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<approx> s\<^sub>1')"
        if "\<P> = Neg"
      proof -
        have "u\<^sub>1 \<preceq>\<^sub>t s\<^sub>1\<langle>u\<^sub>1\<rangle>"
          apply (cases s\<^sub>1)
          apply simp_all
          using ctxt_supt[THEN less_trm_subterm]
          by fastforce
        hence " multp (\<prec>\<^sub>t) {#t\<^sub>2, t\<^sub>2'#} {#s\<^sub>1\<langle>u\<^sub>1\<rangle>, s\<^sub>1', s\<^sub>1\<langle>u\<^sub>1\<rangle>, s\<^sub>1'#}"
          unfolding reflclp_iff
        proof (elim disjE)
          assume "u\<^sub>1 \<prec>\<^sub>t s\<^sub>1\<langle>u\<^sub>1\<rangle>"
          hence "t\<^sub>2 \<prec>\<^sub>t s\<^sub>1\<langle>u\<^sub>1\<rangle>"
            using \<open>u\<^sub>1 = t\<^sub>2\<close> by simp
          moreover hence "t\<^sub>2' \<prec>\<^sub>t s\<^sub>1\<langle>u\<^sub>1\<rangle>"
            by (meson \<open>t\<^sub>2' \<prec>\<^sub>t t\<^sub>2\<close> transpD transp_less_trm)
          ultimately show ?thesis
            by (auto intro: one_step_implies_multp[of _ _ _ "{#}", simplified])
        next
          assume "u\<^sub>1 = s\<^sub>1\<langle>u\<^sub>1\<rangle>"
          show ?thesis
            unfolding \<open>u\<^sub>1 = s\<^sub>1\<langle>u\<^sub>1\<rangle>\<close>[symmetric]
            unfolding \<open>u\<^sub>1 = t\<^sub>2\<close>
            using \<open>t\<^sub>2' \<prec>\<^sub>t t\<^sub>2\<close>
            by (smt (verit, ccfv_SIG) add.commute add_mset_add_single add_mset_commute bex_empty
                one_step_implies_multp set_mset_add_mset_insert set_mset_empty singletonD
                union_single_eq_member)
        qed
        thus "Pos (t\<^sub>2 \<approx> t\<^sub>2') \<prec>\<^sub>l \<P> (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<approx> s\<^sub>1')"
          using \<open>\<P> = Neg\<close>
          by (simp add: less_lit_def)
      qed

      moreover have "Pos (t\<^sub>2 \<approx> t\<^sub>2') \<preceq>\<^sub>l \<P> (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<approx> s\<^sub>1')"
        if "\<P> = Pos" and "is_maximal_lit (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (P1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>)"
      proof (cases "s\<^sub>1")
        case Hole
        show ?thesis
        proof (cases "t\<^sub>2' \<preceq>\<^sub>t s\<^sub>1'")
          case True
          hence "(multp (\<prec>\<^sub>t))\<^sup>=\<^sup>= {#t\<^sub>2, t\<^sub>2'#} {#s\<^sub>1\<langle>u\<^sub>1\<rangle>, s\<^sub>1'#}"
            unfolding Hole \<open>u\<^sub>1 = t\<^sub>2\<close>
            by (simp add: multp_cancel_add_mset)
          thus ?thesis
            using Hole \<open>u\<^sub>1 = t\<^sub>2\<close> \<open>\<P> = Pos\<close>
            by (auto simp: less_lit_def)
        next
          case False
          hence "s\<^sub>1' \<prec>\<^sub>t t\<^sub>2'"
            using \<open>is_ground_trm s\<^sub>1'\<close> \<open>is_ground_trm t\<^sub>2'\<close>
            by (metis (mono_tags, lifting) mem_Collect_eq reflclp_iff totalp_onD totalp_on_less_trm)
          hence "multp (\<prec>\<^sub>t) {#s\<^sub>1\<langle>u\<^sub>1\<rangle>, s\<^sub>1'#} {#t\<^sub>2, t\<^sub>2'#}"
            by (simp add: Hole \<open>u\<^sub>1 = t\<^sub>2\<close> multp_cancel_add_mset)
          hence "\<P> (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<approx> s\<^sub>1') \<prec>\<^sub>l Pos (t\<^sub>2 \<approx> t\<^sub>2')"
            using \<open>\<P> = Pos\<close>
            by (simp add: less_lit_def)
          moreover have "\<forall>K \<in># P\<^sub>1'. K \<preceq>\<^sub>l \<P> (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<approx> s\<^sub>1')"
            using that
            unfolding superpositionI is_maximal_wrt_def
            using \<open>is_ground_atm (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<approx> s\<^sub>1')\<close> \<open>is_ground_cls P\<^sub>1'\<close>
            apply (simp add: subst_cls_add_mset)
            by (metis (mono_tags, lifting) ground_P1 is_ground_lit_if_in_ground_cls
                superpositionI(4,7) mem_Collect_eq subst_lit_ident_if_is_ground_lit
                sup_bot.right_neutral totalp_on_def totalp_on_less_lit vars_cls_add_mset)
          ultimately have "\<forall>K \<in># P\<^sub>1'. K \<preceq>\<^sub>l Pos (t\<^sub>2 \<approx> t\<^sub>2')"
            using transp_less_lit
            by (metis (no_types, lifting) reflclp_iff transpD)
          hence "P1 \<prec>\<^sub>c P2"
            using \<open>\<P> (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<approx> s\<^sub>1') \<prec>\<^sub>l Pos (t\<^sub>2 \<approx> t\<^sub>2')\<close>
              one_step_implies_multp[of P2 P1 "(\<prec>\<^sub>l)" "{#}", simplified]
            unfolding superpositionI
            by (metis (no_types, lifting) \<open>\<forall>K\<in>#P\<^sub>1'. (\<prec>\<^sub>l)\<^sup>=\<^sup>= K (\<P> (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<approx> s\<^sub>1'))\<close> empty_iff insert_iff
                transp_less_lit reflclp_iff set_mset_add_mset_insert set_mset_empty transpD)
          hence False
            using \<open>\<not> (P1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<preceq>\<^sub>c P2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>)\<close> ground_P1 ground_P2 by simp
          thus ?thesis ..
        qed
      next
        case (More f ts1 ctxt ts2)
        hence "u\<^sub>1 \<lhd> s\<^sub>1\<langle>u\<^sub>1\<rangle>"
          by auto
        hence "u\<^sub>1 \<prec>\<^sub>t s\<^sub>1\<langle>u\<^sub>1\<rangle>"
          using less_trm_subterm by simp
        hence \<open>t\<^sub>2 \<prec>\<^sub>t s\<^sub>1\<langle>u\<^sub>1\<rangle>\<close>
          using \<open>u\<^sub>1 = t\<^sub>2\<close> by simp
        moreover hence "t\<^sub>2' \<prec>\<^sub>t s\<^sub>1\<langle>u\<^sub>1\<rangle>"
          using \<open>t\<^sub>2' \<prec>\<^sub>t t\<^sub>2\<close> transp_less_trm
          by (metis transpD)
        ultimately have "multp (\<prec>\<^sub>t) {#t\<^sub>2, t\<^sub>2'#} {#s\<^sub>1\<langle>u\<^sub>1\<rangle>, s\<^sub>1'#}"
          using one_step_implies_multp[of "{#s\<^sub>1\<langle>u\<^sub>1\<rangle>, s\<^sub>1'#}" "{#t\<^sub>2, t\<^sub>2'#}" "(\<prec>\<^sub>t)" "{#}"] by simp
        hence "Pos (t\<^sub>2 \<approx> t\<^sub>2') \<prec>\<^sub>l \<P> (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<approx> s\<^sub>1')"
          using \<open>\<P> = Pos\<close>
          by (simp add: less_lit_def)
        thus ?thesis
          by simp
      qed

      ultimately show ?thesis
        using superpositionI
        by (metis is_maximal_wrt_def local.transp_less_lit reflclp_iff transpD)
    qed

    ultimately show "\<exists>j \<in># {#\<P> (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<approx> s\<^sub>1')#}. K \<prec>\<^sub>l j"
      by auto
  qed simp

  moreover have "C = add_mset (\<P> (s\<^sub>1\<langle>t\<^sub>2'\<rangle> \<approx> s\<^sub>1')) (P\<^sub>1' + P\<^sub>2')"
    unfolding superpositionI
    using \<open>is_ground_cls P\<^sub>1'\<close> \<open>is_ground_cls P\<^sub>2'\<close> \<open>is_ground_trm s\<^sub>1'\<close> \<open>is_ground_trm t\<^sub>2'\<close>
      \<open>is_ground_trm_ctxt s\<^sub>1\<close> superpositionI(6)
    by auto

  moreover have "P1 = P\<^sub>1' + {#\<P> (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<approx> s\<^sub>1')#}"
    unfolding superpositionI by simp

  ultimately show ?thesis
    by simp
qed

lemma smaller_conclusion_ground_eq_resolution:
  assumes step: "eq_resolution P C" and ground_P: "is_ground_cls P"
  shows "C \<prec>\<^sub>c P"
  using step
proof (cases P C rule: eq_resolution.cases)
  case (eq_resolutionI L P' s\<^sub>1 s\<^sub>2 \<mu>)
  then show ?thesis
    using totalp_on_less_cls
    by (metis add.right_neutral add_mset_add_single empty_iff empty_not_add_mset ground_P
        one_step_implies_multp set_mset_empty subst_cls_ident_if_is_ground_cls sup_eq_bot_iff
        vars_cls_add_mset)
qed

lemma smaller_conclusion_ground_eq_factoring:
  assumes step: "eq_factoring P C" and ground_P: "is_ground_cls P"
  shows "C \<prec>\<^sub>c P"
  using step
proof (cases P C rule: eq_factoring.cases)
  case (eq_factoringI L\<^sub>1 L\<^sub>2 P' s\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)
  with ground_P have
    "is_ground_trm s\<^sub>1" and "is_ground_trm s\<^sub>1'" and "is_ground_trm t\<^sub>2" and "is_ground_trm t\<^sub>2'"
    by simp_all
  hence subst_ident: "s\<^sub>1 \<cdot>t \<sigma> = s\<^sub>1" "s\<^sub>1' \<cdot>t \<sigma> = s\<^sub>1'" "t\<^sub>2 \<cdot>t \<sigma> = t\<^sub>2" "t\<^sub>2' \<cdot>t \<sigma> = t\<^sub>2'" for \<sigma>
    by simp_all

  have "term_subst.is_unifier \<mu> {s\<^sub>1, t\<^sub>2}"
    using \<open>term_subst.is_imgu \<mu> {{s\<^sub>1, t\<^sub>2}}\<close>
    by (simp add: term_subst.is_imgu_def term_subst.is_unifiers_def)
  moreover have "term_subst.is_ground_set {s\<^sub>1, t\<^sub>2}"
    using \<open>is_ground_trm s\<^sub>1\<close> \<open>is_ground_trm t\<^sub>2\<close>
    by (simp add: term_subst.is_ground_set_def term_subst.is_ground_def)
  ultimately have "s\<^sub>1 = t\<^sub>2"
    using term_subst.ball_eq_constant_if_unifier[of "{_}", simplified] by auto
  hence "s\<^sub>1' \<prec>\<^sub>t t\<^sub>2"
    using \<open>\<not> s\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t s\<^sub>1' \<cdot>t \<mu>\<close> \<open>is_ground_trm s\<^sub>1\<close> \<open>is_ground_trm s\<^sub>1'\<close>
    using totalp_on_less_trm[THEN totalp_onD, unfolded mem_Collect_eq]
    by (auto simp: subst_ident)

  have "is_ground_atm (s\<^sub>1 \<approx> s\<^sub>1')"
    by (simp add: \<open>is_ground_trm s\<^sub>1'\<close> \<open>is_ground_trm s\<^sub>1\<close>)

  have "is_ground_atm (t\<^sub>2 \<approx> t\<^sub>2')"
    by (simp add: \<open>is_ground_trm t\<^sub>2'\<close> \<open>is_ground_trm t\<^sub>2\<close>)

  have "is_maximal_lit (L\<^sub>1 \<cdot>l \<mu>) (P \<cdot> \<mu>)"
    using eq_factoringI by simp
  hence "is_maximal_lit L\<^sub>1 P"
    using ground_P eq_factoringI(1) by force
  hence "\<forall>K \<in># add_mset (Pos (t\<^sub>2 \<approx> t\<^sub>2')) P'. \<not> Pos (s\<^sub>1 \<approx> s\<^sub>1') \<prec>\<^sub>l K"
    unfolding eq_factoringI
    by (simp add: is_maximal_wrt_def)
  hence "\<not> Pos (s\<^sub>1 \<approx> s\<^sub>1') \<prec>\<^sub>l Pos (t\<^sub>2 \<approx> t\<^sub>2')"
    by simp
  hence "Pos (t\<^sub>2 \<approx> t\<^sub>2') \<preceq>\<^sub>l Pos (s\<^sub>1 \<approx> s\<^sub>1')"
    using totalp_on_less_lit
    by (metis (mono_tags, lifting) \<open>is_ground_atm (s\<^sub>1 \<approx> s\<^sub>1')\<close> \<open>is_ground_atm (t\<^sub>2 \<approx> t\<^sub>2')\<close>
        mem_Collect_eq reflclp_iff totalp_onD vars_lit_Pos)
  hence "t\<^sub>2' \<preceq>\<^sub>t s\<^sub>1'"
    unfolding \<open>s\<^sub>1 = t\<^sub>2\<close>
    unfolding reflclp_iff
    by (metis irreflp_on_less_trm literal.inject(1) local.less_lit_def make_uprod_eq_make_uprod_iff
        mset_lit.simps(1) mset_uprod_make_uprod multp_cancel_add_mset multp_singleton_singleton
        transp_less_trm)

  from eq_factoringI have "C = add_mset (Neg (s\<^sub>1' \<approx> t\<^sub>2')) (add_mset (Pos (s\<^sub>1 \<approx> t\<^sub>2')) P')"
    using ground_P by fastforce

  moreover have "add_mset (Neg (s\<^sub>1' \<approx> t\<^sub>2')) (add_mset (Pos (s\<^sub>1 \<approx> t\<^sub>2')) P') \<prec>\<^sub>c P"
    unfolding eq_factoringI \<open>s\<^sub>1 = t\<^sub>2\<close>
  proof (intro one_step_implies_multp[of "{#_#}" "{#_#}", simplified])
    have "t\<^sub>2' \<prec>\<^sub>t t\<^sub>2"
      using \<open>s\<^sub>1' \<prec>\<^sub>t t\<^sub>2\<close> \<open>t\<^sub>2' \<preceq>\<^sub>t s\<^sub>1'\<close>
      by (metis reflclp_iff transpD transp_less_trm)
    hence "multp (\<prec>\<^sub>t) {#s\<^sub>1', t\<^sub>2', s\<^sub>1', t\<^sub>2'#} {#t\<^sub>2, s\<^sub>1'#}"
      using one_step_implies_multp[of _ _ _ "{#}", simplified]
      by (metis \<open>s\<^sub>1' \<prec>\<^sub>t t\<^sub>2\<close> diff_empty id_remove_1_mset_iff_notin insert_iff
          set_mset_add_mset_insert)
    thus "Neg (s\<^sub>1' \<approx> t\<^sub>2') \<prec>\<^sub>l Pos (t\<^sub>2 \<approx> s\<^sub>1')"
      by (simp add: less_lit_def)
  qed

  ultimately show ?thesis
    by simp
qed

interpretation G: calculus_with_finitary_standard_redundancy G_Inf G_Bot G_entails
  "\<lambda>C\<^sub>1 C\<^sub>2. cls_gcls C\<^sub>1 \<prec>\<^sub>c cls_gcls C\<^sub>2"
proof unfold_locales
  show "transp (\<lambda>C\<^sub>1 C\<^sub>2. cls_gcls C\<^sub>1 \<prec>\<^sub>c cls_gcls C\<^sub>2)"
    using transp_less_cls
    by (metis (no_types, lifting) transpD transpI)
next
  show "wfP (\<lambda>C\<^sub>1 C\<^sub>2. cls_gcls C\<^sub>1 \<prec>\<^sub>c cls_gcls C\<^sub>2)"
    using wfP_less_cls
    by (metis (no_types, lifting) wfP_if_convertible_to_wfP)
next
  show "\<And>\<iota>. \<iota> \<in> G_Inf \<Longrightarrow> prems_of \<iota> \<noteq> []"
    by (auto simp: G_Inf_def)
next
  fix \<iota>
  have "cls_gcls (concl_of \<iota>) \<prec>\<^sub>c cls_gcls (main_prem_of \<iota>)"
    if \<iota>_def: "\<iota> = Infer [P\<^sub>2, P\<^sub>1] (gcls_cls C)" and
      infer: "superposition (cls_gcls P\<^sub>1) (cls_gcls P\<^sub>2) C"
    for P\<^sub>2 P\<^sub>1 C
    unfolding \<iota>_def
    using smaller_conclusion_ground_superposition[OF infer]
    using superposition_preserves_groundness[OF infer]
    by force

  moreover have "cls_gcls (concl_of \<iota>) \<prec>\<^sub>c cls_gcls (main_prem_of \<iota>)"
    if \<iota>_def: "\<iota> = Infer [P] (gcls_cls C)" and
      infer: "eq_resolution (cls_gcls P) C"
    for P C
    unfolding \<iota>_def
    using smaller_conclusion_ground_eq_resolution[OF infer]
    using eq_resolution_preserves_groundness[OF infer]
    by force

  moreover have "cls_gcls (concl_of \<iota>) \<prec>\<^sub>c cls_gcls (main_prem_of \<iota>)"
    if \<iota>_def: "\<iota> = Infer [P] (gcls_cls C)" and
      infer: "eq_factoring (cls_gcls P) C"
    for P C
    unfolding \<iota>_def
    using smaller_conclusion_ground_eq_factoring[OF infer]
    using eq_factoring_preserves_groundness[OF infer]
    by force

  ultimately show "\<iota> \<in> G_Inf \<Longrightarrow> cls_gcls (concl_of \<iota>) \<prec>\<^sub>c cls_gcls (main_prem_of \<iota>)"
    unfolding G_Inf_def
    by fast
qed


subsubsection \<open>Refutational Completeness\<close>

primrec equations_entail_lit where
  "equations_entail_lit E (Pos A) \<longleftrightarrow> (\<exists>s t. A = s \<approx> t \<and> (s, t) \<in> (rstep E)\<^sup>\<down>)" |
  "equations_entail_lit E (Neg A) \<longleftrightarrow> (\<exists>s t. A = s \<approx> t \<and> (s, t) \<notin> (rstep E)\<^sup>\<down>)"

definition equations_entail_cls where
  "equations_entail_cls E C \<longleftrightarrow> (\<exists>L \<in># C. equations_entail_lit E L)"

lemma equations_entail_lit_iff:
  "equations_entail_lit E L \<longleftrightarrow> (\<lambda>(x, y). x \<approx> y) ` (rstep E)\<^sup>\<down> \<TTurnstile>l L"
proof (rule iffI)
  assume "equations_entail_lit E L"
  show "(\<lambda>(x, y). x \<approx> y) ` (rstep E)\<^sup>\<down> \<TTurnstile>l L"
  proof (cases L)
    case (Pos A)
    thus ?thesis
      using \<open>equations_entail_lit E L\<close> by auto
  next
    case (Neg A)
    thus ?thesis
      using \<open>equations_entail_lit E L\<close>
      by (metis equations_entail_lit.simps(2) sym_join true_lit_simps(2)
          true_lit_uprod_iff_true_lit_prod(2))
  qed
next
  assume "(\<lambda>(x, y). x \<approx> y) ` (rstep E)\<^sup>\<down> \<TTurnstile>l L"
  show "equations_entail_lit E L"
  proof (cases L)
    case (Pos A)
    then show ?thesis
      using \<open>(\<lambda>(x, y). x \<approx> y) ` (rstep E)\<^sup>\<down> \<TTurnstile>l L\<close>
      by auto
  next
    case (Neg A)
    thus ?thesis
      using \<open>(\<lambda>(x, y). x \<approx> y) ` (rstep E)\<^sup>\<down> \<TTurnstile>l L\<close>
      by (metis equations_entail_lit.simps(2) ex_make_uprod pair_imageI true_lit_simps(2))
  qed
qed

lemma equations_entail_cls_iff:
  "equations_entail_cls E C \<longleftrightarrow> (\<lambda>(x, y). x \<approx> y) ` (rstep E)\<^sup>\<down> \<TTurnstile> C"
  using equations_entail_lit_iff
  by (metis equations_entail_cls_def true_cls_def)

context
  fixes N :: "('f, string) term uprod clause set"
begin

function production :: "('f, string) term uprod clause \<Rightarrow> ('f, string) term rel" where
  "production C = {(s, t)| s t C'.
    C \<in> N \<and>
    C = add_mset (Pos (s \<approx> t)) C' \<and>
    select C = {#} \<and>
    is_strictly_maximal_lit (Pos (s \<approx> t)) C \<and>
    t \<prec>\<^sub>t s \<and>
    (let R\<^sub>C = (\<Union>D \<in> {D \<in> N. D \<prec>\<^sub>c C}. production D) in
    \<not> (\<lambda>(x, y). x \<approx> y) ` (rstep R\<^sub>C)\<^sup>\<down> \<TTurnstile> C \<and>
    \<not> (\<lambda>(x, y). x \<approx> y) ` (rstep (insert (s, t) R\<^sub>C))\<^sup>\<down> \<TTurnstile> C' \<and>
    s \<in> NF (rstep R\<^sub>C))}"
  by simp_all

termination production
proof (relation "{(x, y). x \<prec>\<^sub>c y}")
  show "wf {(x, y). x \<prec>\<^sub>c y}"
    using wfP_less_cls
    by (simp add: wfP_def)
next
  show "\<And>C D. D \<in> {D \<in> N. D \<prec>\<^sub>c C} \<Longrightarrow> (D, C) \<in> {(x, y). x \<prec>\<^sub>c y}"
    by simp
qed

declare production.simps [simp del]

end

lemma Uniq_striclty_maximal_lit_in_ground_cls:
  assumes "is_ground_cls C"
  shows "\<exists>\<^sub>\<le>\<^sub>1L. L \<in># C \<and> is_strictly_maximal_lit L C"
proof (rule Uniq_is_maximal_wrt_reflclp)
  have "set_mset C \<subseteq> {L. is_ground_lit L}"
    using \<open>is_ground_cls C\<close>
    by (meson Ball_Collect is_ground_lit_if_in_ground_cls)
  thus "totalp_on (set_mset C) (\<prec>\<^sub>l)"
    by (auto intro: totalp_on_subset totalp_on_less_lit)
qed

lemma production_eq_empty_or_singleton:
  assumes "is_ground_cls C"
  shows "production N C = {} \<or> (\<exists>s t. production N C = {(s, t)})"
proof -
  have "\<exists>\<^sub>\<le>\<^sub>1 (x, y). \<exists>C'.
    C = add_mset (Pos (x \<approx> y)) C' \<and> is_maximal_wrt (\<prec>\<^sub>l)\<^sup>=\<^sup>= (Pos (x \<approx> y)) C \<and> y \<prec>\<^sub>t x"
    apply (rule Uniq_prodI)
    apply (elim exE conjE)
    using Uniq_striclty_maximal_lit_in_ground_cls[OF \<open>is_ground_cls C\<close>, THEN Uniq_D,
        of "Pos (_ \<approx> _)" "Pos (_ \<approx> _)", unfolded literal.inject make_uprod_eq_make_uprod_iff]
    using totalp_on_less_trm
    by (metis asympD asymp_less_trm union_single_eq_member)
  hence Uniq_production: "\<exists>\<^sub>\<le>\<^sub>1 (x, y). \<exists>C'.
    C \<in> N \<and>
    C = add_mset (Pos (x \<approx> y)) C' \<and> select C = {#} \<and>
    is_maximal_wrt (\<prec>\<^sub>l)\<^sup>=\<^sup>= (Pos (x \<approx> y)) C \<and> y \<prec>\<^sub>t x \<and>
    (let R\<^sub>C = \<Union> (production N ` {D \<in> N. D \<prec>\<^sub>c C}) in
      \<not> (\<lambda>(x, y). x \<approx> y) ` (rstep R\<^sub>C)\<^sup>\<down> \<TTurnstile> C \<and>
      \<not> (\<lambda>(x, y). x \<approx> y) ` (rstep (insert (x, y) R\<^sub>C))\<^sup>\<down> \<TTurnstile> C' \<and>
      x \<in> NF (rstep R\<^sub>C))"
    using Uniq_mono_decr'
    by (smt (verit) Uniq_def Uniq_prodI case_prod_conv)
  show ?thesis
    unfolding production.simps[of N C]
    using Collect_eq_if_Uniq_prod[OF Uniq_production]
    by (smt (verit, best) Collect_cong Collect_empty_eq Uniq_def Uniq_production case_prod_conv
        insertCI mem_Collect_eq)
qed

definition equation where
  "equation \<equiv> production"

definition rewrite_sys where
  "rewrite_sys N C \<equiv> (\<Union>D \<in> {D \<in> N. D \<prec>\<^sub>c C}. equation N D)"


lemma mem_equationE:
  assumes rule_in: "rule \<in> equation N C"
  obtains l r C' where
    "C \<in> N" and
    "rule = (l, r)" and
    "C = add_mset (Pos (l \<approx> r)) C'" and
    "select C = {#}" and
    "is_strictly_maximal_lit (Pos (l \<approx> r)) C" and
    "r \<prec>\<^sub>t l" and
    "l \<in> NF (rstep (\<Union>D \<in> {D \<in> N. D \<prec>\<^sub>c C}. production N D))"
  using rule_in
  unfolding equation_def production.simps[of N C]
  by auto

lemma singleton_eq_CollectD: "{x} = {y. P y} \<Longrightarrow> P x"
  by blast

lemma subset_Union_mem_CollectI: "P x \<Longrightarrow> f x \<subseteq> (\<Union>y \<in> {z. P z}. f y)"
  by blast

lemma rewrite_sys_subset_if_less_cls: "C \<prec>\<^sub>c D \<Longrightarrow> rewrite_sys N C \<subseteq> rewrite_sys N D"
  by (smt (verit, best) UN_iff mem_Collect_eq rewrite_sys_def subsetI transpD transp_less_cls)

lemma less_trm_iff_less_cls_if_lhs_equation:
  assumes E\<^sub>C: "equation N C = {(s, t)}" and E\<^sub>D: "equation N D = {(u, v)}" and
    gr_C: "is_ground_cls C" and gr_D: "is_ground_cls D"
  shows "u \<prec>\<^sub>t s \<longleftrightarrow> D \<prec>\<^sub>c C"
proof -
  from E\<^sub>C obtain C' where
    "C \<in> N" and
    C_def: "C = add_mset (Pos (s \<approx> t)) C'" and
    "is_strictly_maximal_lit (Pos (s \<approx> t)) C" and
    "t \<prec>\<^sub>t s" and
    s_irreducible: "s \<in> NF (rstep (\<Union>C' \<in> {C' \<in> N. C' \<prec>\<^sub>c C}. production N C'))"
    by (auto simp: equation_def elim!: production.elims dest: singleton_eq_CollectD)
  with gr_C have "\<forall>L \<in># C'. L \<prec>\<^sub>l Pos (s \<approx> t)"
    unfolding is_maximal_wrt_def
    using totalp_on_less_lit[THEN totalp_onD, unfolded mem_Collect_eq]
    by (metis (no_types, opaque_lifting) add_mset_remove_trivial multi_member_split reflclp_iff
        sup_eq_bot_iff vars_cls_add_mset)

  from E\<^sub>D obtain D' where
    "D \<in> N" and
    D_def: "D = add_mset (Pos (u \<approx> v)) D'" and
    "is_strictly_maximal_lit (Pos (u \<approx> v)) D" and
    "v \<prec>\<^sub>t u"
    by (auto simp: equation_def elim: production.elims dest: singleton_eq_CollectD)
  with gr_D have "\<forall>L \<in># D'. L \<prec>\<^sub>l Pos (u \<approx> v)"
    unfolding is_maximal_wrt_def
    using totalp_on_less_lit[THEN totalp_onD, unfolded mem_Collect_eq]
    by (metis add_mset_remove_trivial is_ground_lit_if_in_ground_cls reflclp_iff sup_eq_bot_iff
        vars_cls_add_mset)

  show ?thesis
  proof (rule iffI)
    assume "u \<prec>\<^sub>t s"
    moreover hence "v \<prec>\<^sub>t s"
      using \<open>v \<prec>\<^sub>t u\<close>
      by (meson transpD transp_less_trm)
    ultimately have "multp (\<prec>\<^sub>t) {#u, v#} {#s, t#}"
      using one_step_implies_multp[of "{#s, t#}" "{#u, v#}" _ "{#}"] by simp
    hence "Pos (u \<approx> v) \<prec>\<^sub>l Pos (s \<approx> t)"
      by (simp add: less_lit_def)
    moreover hence "\<forall>L \<in># D'. L \<prec>\<^sub>l Pos (s \<approx> t)"
      using \<open>\<forall>L \<in># D'. L \<prec>\<^sub>l Pos (u \<approx> v)\<close>
      by (meson transp_less_lit transpD)
    ultimately show "D \<prec>\<^sub>c C"
      using one_step_implies_multp[of C D _ "{#}"]
      by (simp add: D_def C_def)
  next
    assume "D \<prec>\<^sub>c C"
    hence "equation N D \<subseteq> rewrite_sys N C"
      using \<open>D \<in> N\<close>
      by (auto simp: rewrite_sys_def)
    hence "s \<noteq> u"
      unfolding E\<^sub>D
      using s_irreducible
      by (auto simp: rewrite_sys_def equation_def)
    moreover have "\<not> (s \<prec>\<^sub>t u)"
    proof (rule notI)
      assume "s \<prec>\<^sub>t u"
      moreover hence "t \<prec>\<^sub>t u"
        using \<open>t \<prec>\<^sub>t s\<close>
        by (meson transpD transp_less_trm)
      ultimately have "multp (\<prec>\<^sub>t) {#s, t#} {#u, v#}"
        using one_step_implies_multp[of "{#u, v#}" "{#s, t#}" _ "{#}"] by simp
      hence "Pos (s \<approx> t) \<prec>\<^sub>l Pos (u \<approx> v)"
        by (simp add: less_lit_def)
      moreover hence "\<forall>L \<in># C'. L \<prec>\<^sub>l Pos (u \<approx> v)"
        using \<open>\<forall>L \<in># C'. L \<prec>\<^sub>l Pos (s \<approx> t)\<close>
        by (meson transp_less_lit transpD)
      ultimately have "C \<prec>\<^sub>c D"
        using one_step_implies_multp[of D C _ "{#}"]
        by (simp add: D_def C_def)
      thus False
        using \<open>D \<prec>\<^sub>c C\<close>
        by (meson irreflpD transpD transp_less_cls wfP_imp_irreflp wfP_less_cls)
    qed
    ultimately show "u \<prec>\<^sub>t s"
      using totalp_on_less_trm[THEN totalp_onD, unfolded mem_Collect_eq, of s u]
      using C_def D_def gr_C gr_D by auto
  qed
qed

lemma termination_rewrite_sys: "wf ((rewrite_sys N C)\<inverse>)"
proof (rule wf_if_convertible_to_wf)
  show "wf {(x, y). x \<prec>\<^sub>t y}"
    using wfP_less_trm
    by (simp add: wfP_def)
next
  fix t s
  assume "(t, s) \<in> (rewrite_sys N C)\<inverse>"
  hence "(s, t) \<in> rewrite_sys N C"
    by simp
  then obtain D where "D \<prec>\<^sub>c C" and "(s, t) \<in> equation N D"
    unfolding rewrite_sys_def by blast
  hence "t \<prec>\<^sub>t s"
    by (auto elim: mem_equationE)
  thus "(t, s) \<in> {(x, y). x \<prec>\<^sub>t y}"
    by (simp add: ) 
qed

lemma termination_Union_rewrite_sys: "wf ((\<Union>D \<in> N. rewrite_sys N D)\<inverse>)"
proof (rule wf_if_convertible_to_wf)
  show "wf {(x, y). x \<prec>\<^sub>t y}"
    using wfP_less_trm
    by (simp add: wfP_def)
next
  fix t s
  assume "(t, s) \<in> (\<Union>D \<in> N. rewrite_sys N D)\<inverse>"
  hence "(s, t) \<in> (\<Union>D \<in> N. rewrite_sys N D)"
    by simp
  then obtain C where "C \<in> N" "(s, t) \<in> rewrite_sys N C"
    by auto
  then obtain D where "D \<prec>\<^sub>c C" and "(s, t) \<in> equation N D"
    unfolding rewrite_sys_def by blast
  hence "t \<prec>\<^sub>t s"
    by (auto elim: mem_equationE)
  thus "(t, s) \<in> {(x, y). x \<prec>\<^sub>t y}"
    by (simp add: ) 
qed

lemma ground_rule_if_mem_equation:
  assumes ground_N: "is_ground_cls_set N" and rule_in: "rule \<in> equation N C"
  shows "is_ground_trm (fst rule) \<and> is_ground_trm (snd rule)"
proof -
  from rule_in obtain l r C' where
    "C \<in> N" and
    "C = add_mset (Pos (l \<approx> r)) C'" and
    "rule = (l, r)"
    by (auto elim: mem_equationE)
  moreover have "is_ground_cls C"
    using ground_N \<open>C \<in> N\<close>
    by (simp add: vars_cls_set_def)
  ultimately show ?thesis
    by simp
qed

lemma ground_rule_if_mem_rewrite_sys:
  assumes ground_N: "is_ground_cls_set N" and rule_in: "rule \<in> rewrite_sys N C"
  shows "is_ground_trm (fst rule) \<and> is_ground_trm (snd rule)"
proof -
  from rule_in obtain D where "D \<in> N" and "D \<prec>\<^sub>c C" and "rule \<in> equation N D"
    unfolding rewrite_sys_def by auto
  thus ?thesis
    using ground_rule_if_mem_equation[OF ground_N] by simp
qed

lemma ground_rule_if_in_Union_rewrite_sys:
  assumes ground_N: "is_ground_cls_set N" and rule_in: "rule \<in> (\<Union> (rewrite_sys N ` N))"
  shows "is_ground_trm (fst rule) \<and> is_ground_trm (snd rule)"
proof -
  from rule_in obtain C where
    "C \<in> N" and "rule \<in> rewrite_sys N C"
    by auto
  thus ?thesis
    using ground_rule_if_mem_rewrite_sys[OF ground_N] by simp
qed

lemma no_crit_pairs:
  assumes ground_N: "is_ground_cls_set N"
  shows "{(b, t1, t2) \<in> critical_pairs (\<Union> (rewrite_sys N ` N)) (\<Union> (rewrite_sys N ` N)). t1 \<noteq> t2} = {}"
proof (rule ccontr)
  assume "{(b, t1, t2).
    (b, t1, t2) \<in> critical_pairs (\<Union> (rewrite_sys N ` N)) (\<Union> (rewrite_sys N ` N)) \<and> t1 \<noteq> t2} \<noteq> {}"
  then obtain l1 r1 l2 r2 ctxt l1' \<mu>1 \<mu>2 where
    "(ctxt = \<box>, (ctxt \<cdot>t\<^sub>c \<mu>1)\<langle>r2 \<cdot>t \<mu>2\<rangle>, r1 \<cdot>t \<mu>1) \<in> critical_pairs (\<Union> (rewrite_sys N ` N)) (\<Union> (rewrite_sys N ` N))" and
    rule1_in: "(l1, r1) \<in> \<Union> (rewrite_sys N ` N)" and
    rule2_in: "(l2, r2) \<in> \<Union> (rewrite_sys N ` N)" and
    "l1 = ctxt\<langle>l1'\<rangle>" and
    "is_Fun l1'" and
    mgu_l1'_l2: "mgu_var_disjoint_string l1' l2 = Some (\<mu>1, \<mu>2)" and
    "(ctxt \<cdot>t\<^sub>c \<mu>1)\<langle>r2 \<cdot>t \<mu>2\<rangle> \<noteq> r1 \<cdot>t \<mu>1"
    unfolding critical_pairs_def mem_Collect_eq by blast

  from rule1_in rule2_in obtain C1 C2 where
    "C1 \<in> N" and rule1_in': "(l1, r1) \<in> rewrite_sys N C1" and
    "C2 \<in> N" and rule2_in': "(l2, r2) \<in> rewrite_sys N C2"
    by auto

  from rule1_in' rule2_in' obtain D1 D2 where
    "D1 \<in> N" and "D1 \<prec>\<^sub>c C1" and rule1_in'': "(l1, r1) \<in> equation N D1" and
    "D2 \<in> N" and "D2 \<prec>\<^sub>c C2" and rule2_in'': "(l2, r2) \<in> equation N D2"
    unfolding rewrite_sys_def
    by auto

  have ground_D1: "is_ground_cls D1" and ground_D2: "is_ground_cls D2"
    using \<open>D1 \<in> N\<close> \<open>D2 \<in> N\<close> ground_N
    by (simp_all add: vars_cls_set_def)

  from rule1_in'' obtain D1' where
    D1_def: "D1 = add_mset (Pos (l1 \<approx> r1)) D1'" and
    D1_max: "is_strictly_maximal_lit (Pos (l1 \<approx> r1)) D1" and
    "r1 \<prec>\<^sub>t l1" and
    l1_irreducible: "l1 \<in> NF (rstep (\<Union>D \<in> {D \<in> N. D \<prec>\<^sub>c D1}. production N D))"
    by (auto elim: mem_equationE)

  from rule2_in'' obtain D2' where
    D2_def: "D2 = add_mset (Pos (l2 \<approx> r2)) D2'" and
    D2_max: "is_strictly_maximal_lit (Pos (l2 \<approx> r2)) D2" and
    "r2 \<prec>\<^sub>t l2" and
    l2_irreducible: "l2 \<in> NF (rstep (\<Union>D \<in> {D \<in> N. D \<prec>\<^sub>c D2}. production N D))"
    by (auto elim: mem_equationE)

  have
    "is_ground_trm l1" and "is_ground_trm r1" and
    "is_ground_trm l2" and "is_ground_trm r2"
    using ground_rule_if_mem_rewrite_sys[OF ground_N rule1_in']
    using ground_rule_if_mem_rewrite_sys[OF ground_N rule2_in']
    by simp_all

  have "is_ground_trm_ctxt ctxt" and "is_ground_trm l1'"
    using \<open>is_ground_trm l1\<close> \<open>l1 = ctxt\<langle>l1'\<rangle>\<close> by force+

  have "l1' = l2"
    using mgu_l1'_l2 \<open>is_ground_trm l1'\<close> \<open>is_ground_trm l2\<close>
    by (metis mgu_var_disjoint_string_sound subst_trm_ident_if_is_ground_trm)

  have "equation N D1 = {(l1, r1)}"
    using rule1_in'' production_eq_empty_or_singleton[OF ground_D1]
    unfolding equation_def
    by fastforce

  have "equation N D2 = {(l2, r2)}"
    using rule2_in'' production_eq_empty_or_singleton[OF ground_D2]
    unfolding equation_def
    by fastforce

  moreover have "is_ground_cls D1" and "is_ground_cls D2"
    using \<open>D1 \<in> N\<close> \<open>D2 \<in> N\<close> ground_N
    by (simp_all add: vars_cls_set_def)

  show False
  proof (cases "ctxt = \<box>")
    case True
    hence "l1 = l2"
      using \<open>l1 = ctxt\<langle>l1'\<rangle>\<close> \<open>l1' = l2\<close>
      by simp
    hence "\<not> (l1 \<prec>\<^sub>t l2)" and "\<not> (l2 \<prec>\<^sub>t l1)"
      by (simp_all add: irreflpD)
    hence "\<not> (D1 \<prec>\<^sub>c D2)" and "\<not> (D2 \<prec>\<^sub>c D1)"
      using \<open>equation N D1 = {(l1, r1)}\<close> \<open>equation N D2 = {(l2, r2)}\<close>
        ground_D1 ground_D2 less_trm_iff_less_cls_if_lhs_equation
      by simp_all
    hence "D1 = D2"
      using ground_D1 ground_D2 totalp_on_less_cls[THEN totalp_onD, unfolded mem_Collect_eq]
      by metis
    hence "r1 = r2"
      using \<open>equation N D1 = {(l1, r1)}\<close> calculation by auto
    moreover have "r1 \<noteq> r2"
      using \<open>(ctxt \<cdot>t\<^sub>c \<mu>1)\<langle>r2 \<cdot>t \<mu>2\<rangle> \<noteq> r1 \<cdot>t \<mu>1\<close> \<open>is_ground_trm r1\<close> \<open>is_ground_trm r2\<close>
      unfolding \<open>ctxt = \<box>\<close>
      by simp
    ultimately show ?thesis
      by argo
  next
    case False
    hence "l2 \<prec>\<^sub>t l1"
      unfolding \<open>l1 = ctxt\<langle>l1'\<rangle>\<close> \<open>l1' = l2\<close>
      by (metis ctxt_supt less_trm_subterm)
    hence "D2 \<prec>\<^sub>c D1"
      using \<open>equation N D1 = {(l1, r1)}\<close> \<open>equation N D2 = {(l2, r2)}\<close>
        ground_D1 ground_D2 less_trm_iff_less_cls_if_lhs_equation
      by simp
    hence "equation N D2 \<subseteq> rewrite_sys N D1"
      unfolding rewrite_sys_def
      using \<open>D2 \<in> N\<close> by auto
    then show False
      unfolding \<open>equation N D2 = {(l2, r2)}\<close>
      unfolding rewrite_sys_def equation_def
      using l1_irreducible[unfolded \<open>l1 = ctxt\<langle>l1'\<rangle>\<close> \<open>l1' = l2\<close>]
      by (meson NF_iff_no_step insert_subset rstep_ctxt rstep_rule)
  qed
qed

lemma WCR_Union_rewrite_sys:
  assumes ground_N: "is_ground_cls_set N"
  shows "WCR (rstep (\<Union>D \<in> N. rewrite_sys N D))"
  unfolding critical_pair_lemma
proof (rule ballI)
  fix tuple
  assume tuple_in: "tuple \<in> critical_pairs (\<Union> (rewrite_sys N ` N)) (\<Union> (rewrite_sys N ` N))"
  then obtain b t1 t2 where tuple_def: "tuple = (b, t1, t2)"
    using prod_cases3 by blast

  moreover have "(t1, t2) \<in> (rstep (\<Union> (rewrite_sys N ` N)))\<^sup>\<down>" if "t1 = t2"
    using that by auto

  moreover have False if "t1 \<noteq> t2"
    using that tuple_def tuple_in no_crit_pairs[OF ground_N] by simp

  ultimately show "case tuple of (b, s, t) \<Rightarrow> (s, t) \<in> (rstep (\<Union> (rewrite_sys N ` N)))\<^sup>\<down>"
    by (cases "t1 = t2") simp_all
qed

lemma
  assumes
    ground_D: "is_ground_cls D" and
    ground_C: "is_ground_cls C" and
    "D \<preceq>\<^sub>c C" and
    E\<^sub>C_eq: "equation N C = {(s, t)}" and
    L_in: "L \<in># D" and
    L_atm: "atm_of L = (u \<approx> v)"
  shows
    lesseq_trm_if_pos: "is_pos L \<Longrightarrow> u \<preceq>\<^sub>t s" and
    less_trm_if_neg: "is_neg L \<Longrightarrow> u \<prec>\<^sub>t s"
proof -
  from E\<^sub>C_eq have "(s, t) \<in> equation N C"
    by simp
  then obtain C' where
    C_def: "C = add_mset (Pos (s \<approx> t)) C'" and
    C_max_lit: "is_strictly_maximal_lit (Pos (s \<approx> t)) C" and
    "t \<prec>\<^sub>t s"
    by (auto elim: mem_equationE)
  with ground_C have ground_s: "is_ground_trm s" and ground_t: "is_ground_trm t"
    by simp_all

  from ground_D L_in L_atm have ground_u: "is_ground_trm u"
    by (metis is_ground_lit_if_in_ground_cls sup_bot.neutr_eq_iff vars_atm_make_uprod vars_lit_def)

  from ground_C ground_D have "set_mset C \<union> set_mset D \<subseteq> {L. is_ground_lit L}"
    by (meson Ball_Collect Un_iff is_ground_lit_if_in_ground_cls)
  hence less_lit_tot_on_C_D[simp]: "totalp_on (set_mset C \<union> set_mset D) (\<prec>\<^sub>l)"
    using totalp_on_less_lit totalp_on_subset by blast

  have "Pos (s \<approx> t) \<prec>\<^sub>l L" if "is_pos L" and "\<not> u \<preceq>\<^sub>t s"
  proof -
    from that(2) have "s \<prec>\<^sub>t u"
      using ground_s ground_u totalp_on_less_trm[THEN totalp_onD, unfolded mem_Collect_eq] by auto
    hence "multp (\<prec>\<^sub>t) {#s, t#} {#u, v#}"
      using \<open>t \<prec>\<^sub>t s\<close>
      by (smt (verit, del_insts) add.right_neutral empty_iff insert_iff one_step_implies_multp
          set_mset_add_mset_insert set_mset_empty transpD transp_less_trm union_mset_add_mset_right)
    with that(1) show "Pos (s \<approx> t) \<prec>\<^sub>l L"
      using L_atm
      by (metis less_lit_def literal.collapse(1) mset_lit.simps(1) mset_uprod_make_uprod)
  qed

  moreover have "Pos (s \<approx> t) \<prec>\<^sub>l L" if "is_neg L" and "\<not> u \<prec>\<^sub>t s"
  proof -
    from that(2) have "s \<preceq>\<^sub>t u"
      using ground_s ground_u totalp_on_less_trm[THEN totalp_onD, unfolded mem_Collect_eq] by auto
    hence "multp (\<prec>\<^sub>t) {#s, t#} {#u, v, u, v#}"
      using \<open>t \<prec>\<^sub>t s\<close>
      by (smt (z3) add_mset_add_single add_mset_remove_trivial add_mset_remove_trivial_iff
          empty_not_add_mset insert_DiffM insert_noteq_member one_step_implies_multp reflclp_iff
          transp_def transp_less_trm union_mset_add_mset_left union_mset_add_mset_right)
    with that(1) show "Pos (s \<approx> t) \<prec>\<^sub>l L"
      using L_atm
      by (cases L) (simp_all add: less_lit_def)
  qed

  moreover have False if "Pos (s \<approx> t) \<prec>\<^sub>l L"
  proof -
    have "C \<prec>\<^sub>c D"
    proof (rule multp_if_maximal_less)
      show "Pos (s \<approx> t) \<in># C"
        by (simp add: C_def)
    next
      show "L \<in># D"
        using L_in by simp
    next
      show "is_maximal_lit (Pos (s \<approx> t)) C"
        using C_max_lit by simp
    next
      show "Pos (s \<approx> t) \<prec>\<^sub>l L"
        using that by simp
    qed simp_all
    with \<open>D \<preceq>\<^sub>c C\<close> show False
      by (metis asympD reflclp_iff wfP_imp_asymp wfP_less_cls)
  qed

  ultimately show "is_pos L \<Longrightarrow> u \<preceq>\<^sub>t s" and "is_neg L \<Longrightarrow> u \<prec>\<^sub>t s"
    by metis+
qed

lemma
  fixes N D
  defines "R\<^sub>D \<equiv> rewrite_sys N D"
  assumes D_in: "D \<in> N" and R\<^sub>D_entails_D: "(\<lambda>(x, y). x \<approx> y) ` (rstep R\<^sub>D)\<^sup>\<down> \<TTurnstile> D"
  shows "(\<lambda>(x, y). x \<approx> y) ` (rstep (\<Union>D \<in> N. rewrite_sys N D))\<^sup>\<down> \<TTurnstile> D"
proof -
  from R\<^sub>D_entails_D obtain L s t where
    L_in: "L \<in># D" and
    "L = Pos (s \<approx> t) \<and> (s, t) \<in> (rstep R\<^sub>D)\<^sup>\<down> \<or>
     L = Neg (s \<approx> t) \<and> (s, t) \<notin> (rstep R\<^sub>D)\<^sup>\<down>"
    unfolding true_cls_def true_lit_iff
    by (metis (no_types, opaque_lifting) ex_make_uprod image_iff prod.case surj_pair)
  then show ?thesis
  proof (elim disjE conjE)
    assume L_def: "L = Pos (s \<approx> t)" and "(s, t) \<in> (rstep R\<^sub>D)\<^sup>\<down>"
    have "R\<^sub>D \<subseteq> (\<Union>D \<in> N. rewrite_sys N D)"
      unfolding R\<^sub>D_def
      using D_in by blast
    hence "rstep R\<^sub>D \<subseteq> rstep (\<Union>D \<in> N. rewrite_sys N D)"
      using rstep_mono by blast
    hence "(s, t) \<in> (rstep (\<Union>D \<in> N. rewrite_sys N D))\<^sup>\<down>"
      using \<open>(s, t) \<in> (rstep R\<^sub>D)\<^sup>\<down>\<close>
      using join_mono by blast
    thus ?thesis
      unfolding true_cls_def true_lit_iff
      using L_in L_def by blast
  next
    assume L_def: "L = Neg (s \<approx> t)" and "(s, t) \<notin> (rstep R\<^sub>D)\<^sup>\<down>"
    have "(s, t) \<notin> (rstep (\<Union>D \<in> N. rewrite_sys N D))\<^sup>\<down>"
    proof (rule notI)
      assume "(s, t) \<in> (rstep (\<Union> (rewrite_sys N ` N)))\<^sup>\<down>"
      then obtain u where
        "(s, u) \<in> (rstep (\<Union> (rewrite_sys N ` N)))\<^sup>*" and
        "(t, u) \<in> (rstep (\<Union> (rewrite_sys N ` N)))\<^sup>*"
        by auto
      then show False
        sorry
    qed
    hence "(s \<approx> t) \<notin> (\<lambda>(x, y). x \<approx> y) ` (rstep (\<Union>D \<in> N. rewrite_sys N D))\<^sup>\<down>"
      by (meson sym_join true_lit_simps(1) true_lit_uprod_iff_true_lit_prod(1))
    thus ?thesis
      unfolding true_cls_def true_lit_iff
      using L_in L_def by blast
  qed
  oops
  

lemma
  assumes "D \<in> N" and "C \<in> N" and "D \<prec>\<^sub>c C" and "(\<lambda>(x, y). x \<approx> y) ` (rstep (rewrite_sys N D))\<^sup>\<down> \<TTurnstile> D"
  shows "(\<lambda>(x, y). x \<approx> y) ` (rstep (rewrite_sys N C))\<^sup>\<down> \<TTurnstile> D"
  oops

lemma model_construction:
  fixes
    N :: "('f, char list) gterm uprod clause set" and
    C :: "('f, char list) gterm uprod clause"
  defines
    "N\<^sub>\<G> \<equiv> cls_gcls ` N" and
    "C\<^sub>\<G> \<equiv> cls_gcls C" and
    "entails \<equiv> \<lambda>E C. (\<lambda>(x, y). x \<approx> y) ` (rstep E)\<^sup>\<down> \<TTurnstile> C"
  assumes "G.saturated N" and "{#} \<notin> N" and C_in: "C \<in> N"
  shows
    "equation N\<^sub>\<G> C\<^sub>\<G> = {} \<longleftrightarrow> entails (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>) C\<^sub>\<G>"
    "entails (\<Union>D\<^sub>\<G> \<in> N\<^sub>\<G>. rewrite_sys N\<^sub>\<G> D\<^sub>\<G>) C\<^sub>\<G>"
    "D\<^sub>\<G> \<in> N\<^sub>\<G> \<Longrightarrow> C\<^sub>\<G> \<prec>\<^sub>c D\<^sub>\<G> \<Longrightarrow> entails (rewrite_sys N\<^sub>\<G> D\<^sub>\<G>) C\<^sub>\<G>"
  unfolding atomize_conj atomize_imp
  using wfP_less_cls imageI[OF C_in, of cls_gcls, folded C\<^sub>\<G>_def N\<^sub>\<G>_def]
proof (induction C\<^sub>\<G> rule: wfP_induct_rule)
  case (less C\<^sub>\<G>)

  have i: "entails (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>) C\<^sub>\<G> \<longleftrightarrow> (equation N\<^sub>\<G> C\<^sub>\<G> = {})"
  proof (rule iffI)
    show "entails (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>) C\<^sub>\<G> \<Longrightarrow> equation N\<^sub>\<G> C\<^sub>\<G> = {}"
      unfolding entails_def rewrite_sys_def
      by (smt (z3) Collect_cong Collect_empty_eq equation_def production.elims)
  next
    show "equation N\<^sub>\<G> C\<^sub>\<G> = {} \<Longrightarrow> entails (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>) C\<^sub>\<G>"
      sorry
  qed

  moreover from i have iia: "entails (\<Union> (rewrite_sys N\<^sub>\<G> ` N\<^sub>\<G>)) C\<^sub>\<G>"
    sorry

  moreover from i have iib: "D\<^sub>\<G> \<in> N\<^sub>\<G> \<longrightarrow> C\<^sub>\<G> \<prec>\<^sub>c D\<^sub>\<G> \<longrightarrow> entails (rewrite_sys N\<^sub>\<G> D\<^sub>\<G>) C\<^sub>\<G>"
    sorry

  ultimately show ?case
    by simp
qed

lemma rstep_eq_rewrite_inside_ctxt_if_ground:
  assumes ground_r: "\<forall>rule \<in> r. is_ground_trm (fst rule) \<and> is_ground_trm (snd rule)"
  shows "rstep r = rewrite_inside_ctxt r"
proof (intro Set.equalityI Set.subsetI)
  fix rule assume rule_in: "rule \<in> rstep r"
  then obtain t1 t2 where rule_def: "rule = (t1, t2)"
    by fastforce

  show "rule \<in> rewrite_inside_ctxt r"
    using rule_in[unfolded rule_def]
    apply (rule rstep.cases)
    using assms
    by (metis (no_types, lifting) compatible_with_ctxtD compatible_with_ctxt_rewrite_inside_ctxt
        fst_conv rule_def snd_conv subsetD subset_rewrite_inside_ctxt subst_trm_ident_if_is_ground_trm)
next
  show "\<And>x. x \<in> rewrite_inside_ctxt r \<Longrightarrow> x \<in> rstep r"
    by (smt (verit, best) mem_Collect_eq rewrite_inside_ctxt_def rstep_ctxt subset_iff subset_rstep)
qed

interpretation G: statically_complete_calculus G_Bot G_Inf G_entails G.Red_I G.Red_F
proof unfold_locales
  fix B :: "('f, string) gterm uprod clause" and N :: "('f, string) gterm uprod clause set"
  assume "B \<in> G_Bot" and "G.saturated N"
  hence "B = {#}"
    by simp

  assume "G_entails N {B}"
  hence "{#} \<in> N"
    unfolding \<open>B = {#}\<close>
  proof (rule contrapos_pp)
    assume "{#} \<notin> N"

    have ground_N: "is_ground_cls_set (cls_gcls ` N)"
      by (simp add: vars_cls_set_def)

    define I :: "(('f, string) term \<times> ('f, string) term) set" where
      "I = (rstep (\<Union>D \<in> cls_gcls ` N. rewrite_sys (cls_gcls ` N) D))\<^sup>\<down>"

    show "\<not> G_entails N G_Bot"
      unfolding G_entails_def not_all not_imp
    proof (intro exI conjI)
      show "refl I"
        unfolding I_def
        by (simp add: joinI_right reflI)
    next
      show "trans I"
        unfolding I_def
      proof (rule trans_join)
        have ground_model: "\<forall>rule \<in> (\<Union>D \<in> cls_gcls ` N. rewrite_sys (cls_gcls ` N) D).
          is_ground_trm (fst rule) \<and> is_ground_trm (snd rule)"
          using ground_N
          by (meson ground_rule_if_in_Union_rewrite_sys)

        have "wf ((rewrite_inside_ctxt (\<Union>D \<in> cls_gcls ` N. rewrite_sys (cls_gcls ` N) D))\<inverse>)"
        proof (rule wf_converse_rewrite_inside_ctxt)
          fix s t
          assume "(s, t) \<in> (\<Union>D \<in> cls_gcls ` N. rewrite_sys (cls_gcls ` N) D)"
          then obtain C where "C \<in> cls_gcls ` N" "(s, t) \<in> rewrite_sys (cls_gcls ` N) C"
            by auto
          then obtain D where "D \<prec>\<^sub>c C" and "(s, t) \<in> equation (cls_gcls ` N) D"
            unfolding rewrite_sys_def by blast
          thus "t \<prec>\<^sub>t s"
            by (auto elim: mem_equationE)
        qed simp_all
        thus "SN (rstep (\<Union>D \<in> cls_gcls ` N. rewrite_sys (cls_gcls ` N) D))"
          unfolding rstep_eq_rewrite_inside_ctxt_if_ground[OF ground_model]
          using SN_iff_wf by metis
      next
        show "WCR (rstep (\<Union> (rewrite_sys (local.cls_gcls ` N) ` local.cls_gcls ` N)))"
          using WCR_Union_rewrite_sys[OF ground_N] by metis
      qed
    next
      show "sym I"
        unfolding I_def
        using sym_join by metis
    next
      show "compatible_with_ctxt I"
        unfolding I_def
        apply (rule compatible_with_ctxt_join)
        using compatible_with_ctxt_def by blast
    next
      show "(\<lambda>(x, y). x \<approx> y) ` I \<TTurnstile>s cls_gcls ` N"
        unfolding I_def
        using model_construction[OF \<open>G.saturated N\<close> \<open>{#} \<notin> N\<close>]
        by (simp add: true_clss_def)
    next
      show "\<not> (\<lambda>(x, y). x \<approx> y) ` I \<TTurnstile>s cls_gcls ` G_Bot"
        by simp
    qed
  qed
  thus "\<exists>B'\<in>G_Bot. B' \<in> N"
    by auto
qed

end


subsection \<open>First-Order Layer\<close>


abbreviation F_Inf :: "('f, string) term atom clause inference set" where
  "F_Inf \<equiv> {}"

abbreviation F_Bot :: "('f, string) term atom clause set" where
  "F_Bot \<equiv> {{#}}"

abbreviation F_entails :: "('f, string) term atom clause set \<Rightarrow> ('f, string) term atom clause set \<Rightarrow> bool" where
  "F_entails \<equiv> (\<TTurnstile>e)"

typedecl Q

definition \<G>_F :: "Q \<Rightarrow> ('f, string) term atom clause \<Rightarrow> ('f, 'v) gterm atom clause set" where
  "\<G>_F \<equiv> \<lambda>_ _. {}"

definition \<G>_I :: "Q \<Rightarrow> ('f, string) term atom clause inference \<Rightarrow> ('f, 'v) gterm atom clause inference set option" where
  "\<G>_I \<equiv> \<lambda>_ _. None"

definition Prec_F :: "('f, 'v) gterm atom clause \<Rightarrow> ('f, string) term atom clause \<Rightarrow> ('f, string) term atom clause \<Rightarrow> bool" where
  "Prec_F \<equiv> \<lambda>_ _ _. False"

interpretation F: lifting_intersection F_Inf G_Bot "UNIV :: Q set" "\<lambda>(_ :: Q). G_Inf"
  "\<lambda>(_ :: Q). G_entails" "\<lambda>(_ :: Q). G.Red_I" "\<lambda>(_ :: Q). G.Red_F" F_Bot \<G>_F \<G>_I Prec_F
proof unfold_locales
  show "UNIV \<noteq> {}"
    by simp
next
  show "\<forall>q\<in>UNIV. consequence_relation G_Bot G_entails"
    sorry
next
  show "\<forall>q\<in>UNIV. tiebreaker_lifting F_Bot F_Inf G_Bot G_entails G_Inf G.Red_I G.Red_F (\<G>_F q) (\<G>_I q) Prec_F"
    sorry
qed

interpretation F: sound_inference_system F_Inf F_Bot F.entails_\<G>
proof unfold_locales
  show "\<And>\<iota>. \<iota> \<in> F_Inf \<Longrightarrow> F.entails_\<G> (set (prems_of \<iota>)) {concl_of \<iota>}"
    unfolding F.entails_\<G>_def
    sorry
qed

interpretation F: statically_complete_calculus F_Bot F_Inf F.entails_\<G> F.Red_I_\<G> F.Red_F_\<G>
proof unfold_locales
  show "\<And>B N. B \<in> F_Bot \<Longrightarrow> F.saturated N \<Longrightarrow> F.entails_\<G> N {B} \<Longrightarrow> \<exists>B' \<in> F_Bot. B' \<in> N"
    sorry
qed

end

end