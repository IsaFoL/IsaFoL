theory Superposition
  imports
    (* Theories from the Isabelle distribution *)
    Main

    (* Theories from the AFP *)
    "Saturation_Framework.Calculus"
    "Saturation_Framework.Lifting_to_Non_Ground_Calculi"
    "Saturation_Framework_Extensions.Clausal_Calculus"
    "First_Order_Terms.Term"
    "Knuth_Bendix_Order.Subterm_and_Context"
    "Abstract-Rewriting.Abstract_Rewriting"

    (* Theories from CeTA *)
    "CR.Critical_Pairs"

    (* Theories from this formalization *)
    "Abstract_Rewriting_Extra"
    "Abstract_Substitution_Extra_First_Order_Term"
    "Multiset_Extra"
    "Term_Rewrite_System"
    "Term_Rewriting_Extra"
    "Transitive_Closure_Extra"
    "Unordered_Prod"
begin


no_notation subst_compose (infixl "\<circ>\<^sub>s" 75)
no_notation subst_apply_term (infixl "\<cdot>" 67)

hide_type Inference_System.inference
hide_const
  Inference_System.Infer
  Inference_System.prems_of
  Inference_System.concl_of
  Inference_System.main_prem_of


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

lemma Uniq_implies_ex1: "\<exists>\<^sub>\<le>\<^sub>1x. P x \<Longrightarrow> P y \<Longrightarrow> \<exists>!x. P x"
  by (iprover intro: ex1I dest: Uniq_D)

lemma Uniq_antimono: "Q \<le> P \<Longrightarrow> Uniq Q \<ge> Uniq P"
  unfolding le_fun_def le_bool_def
  by (rule impI) (simp only: Uniq_I Uniq_D)

lemma Uniq_antimono': "(\<And>x. Q x \<Longrightarrow> P x) \<Longrightarrow> Uniq P \<Longrightarrow> Uniq Q"
  by (fact Uniq_antimono[unfolded le_fun_def le_bool_def, rule_format])

lemma Collect_eq_if_Uniq: "(\<exists>\<^sub>\<le>\<^sub>1x. P x) \<Longrightarrow> {x. P x} = {} \<or> (\<exists>x. {x. P x} = {x})"
  using Uniq_D by fastforce

lemma Collect_eq_if_Uniq_prod: "(\<exists>\<^sub>\<le>\<^sub>1(x, y). P x y) \<Longrightarrow> {(x, y). P x y} = {} \<or> (\<exists>x y. {(x, y). P x y} = {(x, y)})"
  using Collect_eq_if_Uniq by fastforce


section \<open>Abstract_Rewriting_Extra\<close>

lemma compatible_with_ctxt_rstep: "compatible_with_ctxt (rstep r)"
  by (auto simp: compatible_with_ctxt_def)


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

lemma subst_atm_Var_ident[simp]: "A \<cdot>a Var = A"
  by (simp add: subst_atm_def uprod.map_ident)

lemma subst_lit_Var_ident[simp]: "L \<cdot>l Var = L"
  by (simp add: subst_lit_def literal.map_ident)

lemma subst_cls_Var_ident[simp]: "C \<cdot> Var = C"
  by (simp add: subst_cls_def multiset.map_ident)

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

term Abstract_Substitution_Extra_First_Order_Term.is_ground_trm

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

lemma is_ground_cls_if_in_ground_cls_set:
  "is_ground_cls_set N \<Longrightarrow> C \<in> N \<Longrightarrow> is_ground_cls C"
  by (simp add: vars_cls_set_def)

lemma subst_trm_ctxt_ident_if_is_ground_trm_ctxt[simp]: "is_ground_trm_ctxt c \<Longrightarrow> c \<cdot>t\<^sub>c \<sigma> = c"
  by (induction c) (simp_all add: list.map_ident_strong)

lemma subst_atm_ident_if_is_ground_atm[simp]: "is_ground_atm A \<Longrightarrow> A \<cdot>a \<sigma> = A"
  by (simp add: subst_atm_def uprod.map_ident_strong vars_atm_def)

lemma subst_lit_ident_if_is_ground_lit[simp]: "is_ground_lit L \<Longrightarrow> L \<cdot>l \<sigma> = L"
  by (simp add: subst_lit_def literal.expand literal.map_sel(1) literal.map_sel(2) vars_lit_def)

lemma subst_cls_ident_if_is_ground_cls[simp]: "is_ground_cls C \<Longrightarrow> C \<cdot> \<sigma> = C"
  by (induction C) (simp_all add: subst_cls_def)

lemma subst_lit_Pos: "Pos A \<cdot>l \<sigma> = Pos (A \<cdot>a \<sigma>)"
  by (simp add: subst_lit_def)

lemma subst_lit_Neg: "Neg A \<cdot>l \<sigma> = Neg (A \<cdot>a \<sigma>)"
  by (simp add: subst_lit_def)

lemma subst_cls_add_mset: "add_mset L C \<cdot> \<sigma> = add_mset (L \<cdot>l \<sigma>) (C \<cdot> \<sigma>)"
  by (simp add: subst_cls_def)

lemma subst_cls_plus: "(C\<^sub>1 + C\<^sub>2) \<cdot> \<sigma> = (C\<^sub>1 \<cdot> \<sigma>) + (C\<^sub>2 \<cdot> \<sigma>)"
  by (simp add: subst_cls_def)

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
        fst_conv rule_def snd_conv subsetD subset_rewrite_inside_ctxt term_subst.subst_ident_if_ground)
next
  show "\<And>x. x \<in> rewrite_inside_ctxt r \<Longrightarrow> x \<in> rstep r"
    by (smt (verit, best) mem_Collect_eq rewrite_inside_ctxt_def rstep_ctxt subset_iff subset_rstep)
qed

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
    transp_less_trm[intro]: "transp (\<prec>\<^sub>t)" and
    asymp_less_trm[intro]: "asymp (\<prec>\<^sub>t)" and
    wfP_less_trm[intro]: "wfP (\<prec>\<^sub>t)" and
    totalp_on_less_trm[intro]: "totalp_on {t. is_ground_trm t} (\<prec>\<^sub>t)" and
    (* less_trm_closed_unter_subst[simp]: "\<And>t t' \<sigma>. t \<prec>\<^sub>t t' \<Longrightarrow> t \<cdot>t \<sigma> \<prec>\<^sub>t t' \<cdot>t \<sigma>" and *)
    less_trm_compatible_with_ctxt[simp]: "\<And>ctxt t t'. t \<prec>\<^sub>t t' \<Longrightarrow> ctxt\<langle>t\<rangle> \<prec>\<^sub>t ctxt\<langle>t'\<rangle>" and
    less_trm_if_subterm[simp]: "\<And>t t'. t \<lhd> t' \<Longrightarrow> t \<prec>\<^sub>t t'" and
    select_subset: "\<And>C. select C \<subseteq># C" and
    select_negative_lits: "\<And>C L. L \<in># select C \<Longrightarrow> is_neg L" and
    select_stable_under_renaming: "\<And>C \<rho>. term_subst.is_renaming \<rho> \<Longrightarrow> select (C \<cdot> \<rho>) = select C \<cdot> \<rho>"
begin

lemma irreflp_on_less_trm[simp]: "irreflp_on A (\<prec>\<^sub>t)"
  by (metis asympD asymp_less_trm irreflp_onI)

abbreviation lesseq_trm (infix "\<preceq>\<^sub>t" 50) where
  "lesseq_trm \<equiv> (\<prec>\<^sub>t)\<^sup>=\<^sup>="

lemma lesseq_trm_if_subtermeq: "\<And>t t'. t \<unlhd> t' \<Longrightarrow> t \<preceq>\<^sub>t t'"
  by (metis less_trm_if_subterm reflclp_iff subterm.order.not_eq_order_implies_strict)

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

lemma asymp_less_lit[simp]: "asymp (\<prec>\<^sub>l)"
  by (metis asympD asympI asymp_less_trm asymp_multp\<^sub>H\<^sub>O less_lit_def multp_eq_multp\<^sub>H\<^sub>O transp_less_trm)

lemma asymp_less_cls[simp]: "asymp (\<prec>\<^sub>c)"
  by (simp add: asymp_multp\<^sub>H\<^sub>O multp_eq_multp\<^sub>H\<^sub>O)

lemma wfP_less_lit[simp]: "wfP (\<prec>\<^sub>l)"
  unfolding less_lit_def
  using wfP_less_trm wfP_multp wfP_if_convertible_to_wfP by meson

lemma wfP_less_cls[simp]: "wfP (\<prec>\<^sub>c)"
  using wfP_less_lit wfP_multp by blast

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


subsection \<open>Alternative Specification of the Superposition Rule\<close>

inductive pos_superposition ::
  "('f, string) term atom clause \<Rightarrow> ('f, string) term atom clause \<Rightarrow> ('f, string) term atom clause \<Rightarrow> bool"
where
  pos_superpositionI: "
    term_subst.is_renaming \<rho>\<^sub>1 \<Longrightarrow>
    term_subst.is_renaming \<rho>\<^sub>2 \<Longrightarrow>
    vars_cls (P\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter> vars_cls (P\<^sub>2 \<cdot> \<rho>\<^sub>2) = {} \<Longrightarrow>
    P\<^sub>1 = add_mset L\<^sub>1 P\<^sub>1' \<Longrightarrow>
    P\<^sub>2 = add_mset L\<^sub>2 P\<^sub>2' \<Longrightarrow>
    L\<^sub>1 = Pos (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<approx> s\<^sub>1') \<Longrightarrow>
    L\<^sub>2 = Pos (t\<^sub>2 \<approx> t\<^sub>2') \<Longrightarrow>
    \<not> is_Var u\<^sub>1 \<Longrightarrow>
    term_subst.is_imgu \<mu> {{u\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}} \<Longrightarrow>
    \<not> (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<preceq>\<^sub>c P\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    is_strictly_maximal_lit (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>) \<Longrightarrow>
    is_strictly_maximal_lit (L\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu>) (P\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    \<not> (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu>) \<Longrightarrow>
    \<not> (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<preceq>\<^sub>t t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu>) \<Longrightarrow>
    C = add_mset (Pos ((s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> \<approx> s\<^sub>1' \<cdot>t \<rho>\<^sub>1)) (P\<^sub>1' \<cdot> \<rho>\<^sub>1 + P\<^sub>2' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu> \<Longrightarrow>
    pos_superposition P\<^sub>1 P\<^sub>2 C"

lemma superposition_if_pos_superposition:
  assumes "pos_superposition P\<^sub>1 P\<^sub>2 C"
  shows "superposition P\<^sub>1 P\<^sub>2 C"
  using assms
proof (cases P\<^sub>1 P\<^sub>2 C rule: pos_superposition.cases)
  case (pos_superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)
  then show ?thesis
    using superpositionI
    by (metis insert_iff)
qed

inductive neg_superposition ::
  "('f, string) term atom clause \<Rightarrow> ('f, string) term atom clause \<Rightarrow> ('f, string) term atom clause \<Rightarrow> bool"
where
  neg_superpositionI: "
    term_subst.is_renaming \<rho>\<^sub>1 \<Longrightarrow>
    term_subst.is_renaming \<rho>\<^sub>2 \<Longrightarrow>
    vars_cls (P\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter> vars_cls (P\<^sub>2 \<cdot> \<rho>\<^sub>2) = {} \<Longrightarrow>
    P\<^sub>1 = add_mset L\<^sub>1 P\<^sub>1' \<Longrightarrow>
    P\<^sub>2 = add_mset L\<^sub>2 P\<^sub>2' \<Longrightarrow>
    L\<^sub>1 = Neg (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<approx> s\<^sub>1') \<Longrightarrow>
    L\<^sub>2 = Pos (t\<^sub>2 \<approx> t\<^sub>2') \<Longrightarrow>
    \<not> is_Var u\<^sub>1 \<Longrightarrow>
    term_subst.is_imgu \<mu> {{u\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}} \<Longrightarrow>
    \<not> (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<preceq>\<^sub>c P\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    select P\<^sub>1 = {#} \<and> is_maximal_lit (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>) \<or> L\<^sub>1 \<in># select P\<^sub>1 \<Longrightarrow>
    is_strictly_maximal_lit (L\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu>) (P\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    \<not> (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu>) \<Longrightarrow>
    \<not> (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<preceq>\<^sub>t t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu>) \<Longrightarrow>
    C = add_mset (Neg ((s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> \<approx> s\<^sub>1' \<cdot>t \<rho>\<^sub>1)) (P\<^sub>1' \<cdot> \<rho>\<^sub>1 + P\<^sub>2' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu> \<Longrightarrow>
    neg_superposition P\<^sub>1 P\<^sub>2 C"

lemma superposition_if_neg_superposition:
  assumes "neg_superposition P\<^sub>1 P\<^sub>2 C"
  shows "superposition P\<^sub>1 P\<^sub>2 C"
  using assms
proof (cases P\<^sub>1 P\<^sub>2 C rule: neg_superposition.cases)
  case (neg_superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)
  then show ?thesis
    using superpositionI
    by (metis insert_iff)
qed

lemma superposition_imp_pos_or_neg:
  assumes "superposition P\<^sub>1 P\<^sub>2 C"
  shows "pos_superposition P\<^sub>1 P\<^sub>2 C \<or> neg_superposition P\<^sub>1 P\<^sub>2 C"
  using assms
proof (cases P\<^sub>1 P\<^sub>2 C rule: superposition.cases)
  case (superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' \<P> s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)
  then show ?thesis
    using pos_superpositionI[of \<rho>\<^sub>1 \<rho>\<^sub>2 P\<^sub>1 P\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>]
    using neg_superpositionI[of \<rho>\<^sub>1 \<rho>\<^sub>2 P\<^sub>1 P\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>]
    by metis
qed

lemma superposition_iff_pos_or_neg:
  "superposition P\<^sub>1 P\<^sub>2 C \<longleftrightarrow> pos_superposition P\<^sub>1 P\<^sub>2 C \<or> neg_superposition P\<^sub>1 P\<^sub>2 C"
  using superposition_imp_pos_or_neg
    superposition_if_neg_superposition superposition_if_pos_superposition
  by metis

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

lemma uprod_mem_image_iff_prod_mem[simp]:
  assumes "sym I"
  shows "(t \<approx> t') \<in> (\<lambda>(t\<^sub>1, t\<^sub>2). t\<^sub>1 \<approx> t\<^sub>2) ` I \<longleftrightarrow> (t, t') \<in> I"
  using \<open>sym I\<close>[THEN symD]
  by (smt (z3) case_prod_unfold image_iff make_uprod_eq_make_uprod_iff pair_imageI prod.collapse)

lemma true_lit_uprod_iff_true_lit_prod[simp]:
  assumes "sym I"
  shows
    "(\<lambda>(t\<^sub>1, t\<^sub>2). t\<^sub>1 \<approx> t\<^sub>2) ` I \<TTurnstile>l Pos (t \<approx> t') \<longleftrightarrow> I \<TTurnstile>l Pos (t, t')"
    "(\<lambda>(t\<^sub>1, t\<^sub>2). t\<^sub>1 \<approx> t\<^sub>2) ` I \<TTurnstile>l Neg (t \<approx> t') \<longleftrightarrow> I \<TTurnstile>l Neg (t, t')"
  unfolding true_lit_simps uprod_mem_image_iff_prod_mem[OF \<open>sym I\<close>]
  by simp_all

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
    by (simp add: term_subst.is_ground_set_def)
  moreover have "term_subst.is_unifier \<mu> {u\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}"
    using \<open>term_subst.is_imgu \<mu> {{u\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}}\<close>
    by (simp add: term_subst.is_imgu_def term_subst.is_unifiers_def)
  ultimately have "u\<^sub>1 = t\<^sub>2"
    using term_subst.ball_eq_constant_if_unifier[of "{u\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}" _ \<mu>]
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
    by (simp add: term_subst.is_ground_set_def)

  moreover from \<open>term_subst.is_imgu \<mu> {{t\<^sub>1, t\<^sub>2}}\<close> have "term_subst.is_unifier \<mu> {t\<^sub>1, t\<^sub>2}"
    by (simp add: term_subst.is_imgu_def term_subst.is_unifiers_def)

  ultimately have "t\<^sub>1 = t\<^sub>2"
    using term_subst.ball_eq_constant_if_unifier[of "{t\<^sub>1, t\<^sub>2}" _ \<mu>] by simp

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
    by (simp add: term_subst.is_ground_set_def)
  moreover from \<open>term_subst.is_imgu \<mu> {{s\<^sub>1, t\<^sub>2}}\<close> have "term_subst.is_unifier \<mu> {s\<^sub>1, t\<^sub>2}"
    by (simp add: term_subst.is_imgu_def term_subst.is_unifiers_def)
  ultimately have "s\<^sub>1 = t\<^sub>2"
    using term_subst.ball_eq_constant_if_unifier[of "{s\<^sub>1, t\<^sub>2}" _ \<mu>] by simp

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
    by (simp add: term_subst.is_ground_set_def)
  moreover have "term_subst.is_unifier \<mu> {u\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}"
    using \<open>term_subst.is_imgu \<mu> {{u\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}}\<close>
    by (simp add: term_subst.is_imgu_def term_subst.is_unifiers_def)
  ultimately have "u\<^sub>1 = t\<^sub>2"
    using term_subst.ball_eq_constant_if_unifier[of "{u\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}" _ \<mu>]
    using \<open>is_ground_trm t\<^sub>2\<close> \<open>is_ground_trm u\<^sub>1\<close> by auto

  have "P2 \<prec>\<^sub>c P1"
    using \<open>\<not> (P1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<preceq>\<^sub>c P2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>)\<close> ground_P1 ground_P2
    using totalp_on_less_cls[THEN totalp_onD] by auto

  have "s\<^sub>1' \<prec>\<^sub>t s\<^sub>1\<langle>u\<^sub>1\<rangle>"
    using \<open>\<not> s\<^sub>1\<langle>u\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu>\<close> \<open>is_ground_trm s\<^sub>1\<langle>u\<^sub>1\<rangle>\<close> \<open>is_ground_trm s\<^sub>1'\<close>
    using totalp_on_less_trm[THEN totalp_onD, simplified]
    by (metis reflclp_iff term_subst.subst_ident_if_ground)

  have "t\<^sub>2' \<prec>\<^sub>t t\<^sub>2"
    by (metis (mono_tags) \<open>is_ground_trm t\<^sub>2'\<close> \<open>is_ground_trm u\<^sub>1\<close> \<open>u\<^sub>1 = t\<^sub>2\<close> superpositionI(15)
        mem_Collect_eq term_subst.subst_ident_if_ground sup2I1 sup2I2 totalp_onD totalp_on_less_trm)

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
        using transp_less_trm
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
          using ctxt_supt[THEN less_trm_if_subterm]
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
            using transp_less_trm
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
            using transp_less_trm
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
          using less_trm_if_subterm by simp
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
    by (simp add: term_subst.is_ground_set_def)
  ultimately have "s\<^sub>1 = t\<^sub>2"
    using term_subst.ball_eq_constant_if_unifier[of "{s\<^sub>1, t\<^sub>2}" _ \<mu>] by auto
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
    using Uniq_antimono'
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
    "\<not> (\<lambda>(x, y). x \<approx> y) ` (rstep (rewrite_sys N C))\<^sup>\<down> \<TTurnstile> C" and
    "\<not> (\<lambda>(x, y). x \<approx> y) ` (rstep (insert (l, r) (rewrite_sys N C)))\<^sup>\<down> \<TTurnstile> C'" and
    "l \<in> NF (rstep (rewrite_sys N C))"
  using rule_in
  unfolding equation_def production.simps[of N C] mem_Collect_eq Let_def rewrite_sys_def
  by (metis (no_types, lifting))

lemma ground_rule_if_mem_equation:
  assumes ground_C: "is_ground_cls C" and rule_in: "rule \<in> equation N C"
  shows "is_ground_trm (fst rule) \<and> is_ground_trm (snd rule)"
proof -
  from rule_in obtain l r C' where
    "C \<in> N" and
    "C = add_mset (Pos (l \<approx> r)) C'" and
    "rule = (l, r)"
    by (auto elim!: mem_equationE)
  with ground_C show ?thesis
    by simp
qed

lemma is_ground_trm_if_mem_equation[simp]:
  assumes ground_C: "is_ground_cls C" and rule_in: "(t1, t2) \<in> equation N C"
  shows "is_ground_trm t1" and "is_ground_trm t2"
  using assms by (auto dest: ground_rule_if_mem_equation)

lemma ground_rule_if_mem_Union_equation:
  assumes ground_N: "is_ground_cls_set N" and rule_in: "rule \<in> (\<Union>C \<in> N. equation N2 C)"
  shows "is_ground_trm (fst rule) \<and> is_ground_trm (snd rule)"
proof -
  from rule_in obtain D where "D \<in> N" and "rule \<in> equation N2 D"
    unfolding rewrite_sys_def by auto
  moreover from ground_N have "is_ground_cls D"
    using \<open>D \<in> N\<close> by (simp add: is_ground_cls_if_in_ground_cls_set)
  ultimately show ?thesis
    using ground_rule_if_mem_equation by simp
qed

lemma ground_rule_if_mem_rewrite_sys:
  assumes ground_N: "is_ground_cls_set N" and rule_in: "rule \<in> rewrite_sys N C"
  shows "is_ground_trm (fst rule) \<and> is_ground_trm (snd rule)"
  using assms ground_rule_if_mem_Union_equation
  unfolding rewrite_sys_def
  by blast

lemma rhs_lt_lhs_if_mem_rewrite_sys:
  assumes "(t1, t2) \<in> rewrite_sys N C"
  shows "t2 \<prec>\<^sub>t t1"
  using assms
  unfolding rewrite_sys_def
  by (smt (verit, best) UN_iff mem_equationE prod.inject)

lemma rhs_less_trm_lhs_if_mem_rstep_rewrite_sys:
  assumes ground_N: "is_ground_cls_set N" and rule_in: "(t1, t2) \<in> rstep (rewrite_sys N C)"
  shows "t2 \<prec>\<^sub>t t1"
  using rule_in
proof (cases t1 t2 rule: rstep.cases)
  case (rstep ctxt \<sigma> l r)
  thus ?thesis
    using rhs_lt_lhs_if_mem_rewrite_sys[of l r]
    using ground_rule_if_mem_rewrite_sys[OF ground_N, of "(l, r)"]
    by simp
qed

lemma rhs_lesseq_trm_lhs_if_mem_rtrancl_rstep_rewrite_sys:
  assumes ground_N: "is_ground_cls_set N" and rule_in: "(t1, t2) \<in> (rstep (rewrite_sys N C))\<^sup>*"
  shows "t2 \<preceq>\<^sub>t t1"
  using rule_in
proof (induction t2 rule: rtrancl_induct)
  case base
  show ?case
    by simp
next
  case (step t2 t3)
  from step.hyps have "t3 \<prec>\<^sub>t t2"
    using rhs_less_trm_lhs_if_mem_rstep_rewrite_sys[OF ground_N] by metis
  with step.IH show ?case
    using transp_less_trm
    by (metis reflclp_iff transpD)
qed

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

lemma no_crit_pairs:
  assumes ground_N: "is_ground_cls_set N"
  shows "{(b, t1, t2) \<in> critical_pairs (\<Union> (equation N2 ` N)) (\<Union> (equation N2 ` N)). t1 \<noteq> t2} = {}"
proof (rule ccontr)
  assume "{(b, t1, t2).
    (b, t1, t2) \<in> critical_pairs (\<Union> (equation N2 ` N)) (\<Union> (equation N2 ` N)) \<and> t1 \<noteq> t2} \<noteq> {}"
  then obtain l1 r1 l2 r2 ctxt l1' \<mu>1 \<mu>2 where
    "(ctxt = \<box>, (ctxt \<cdot>t\<^sub>c \<mu>1)\<langle>r2 \<cdot>t \<mu>2\<rangle>, r1 \<cdot>t \<mu>1) \<in>
      critical_pairs (\<Union> (equation N2 ` N)) (\<Union> (equation N2 ` N))" and
    rule1_in: "(l1, r1) \<in> \<Union> (equation N2 ` N)" and
    rule2_in: "(l2, r2) \<in> \<Union> (equation N2 ` N)" and
    "l1 = ctxt\<langle>l1'\<rangle>" and
    "is_Fun l1'" and
    mgu_l1'_l2: "mgu_var_disjoint_string l1' l2 = Some (\<mu>1, \<mu>2)" and
    "(ctxt \<cdot>t\<^sub>c \<mu>1)\<langle>r2 \<cdot>t \<mu>2\<rangle> \<noteq> r1 \<cdot>t \<mu>1"
    unfolding critical_pairs_def mem_Collect_eq by blast

  from rule1_in rule2_in obtain C1 C2 where
    "C1 \<in> N" and rule1_in': "(l1, r1) \<in> equation N2 C1" and
    "C2 \<in> N" and rule2_in': "(l2, r2) \<in> equation N2 C2"
    by auto

  have ground_C1: "is_ground_cls C1" and ground_C2: "is_ground_cls C2"
    using \<open>C1 \<in> N\<close> \<open>C2 \<in> N\<close> ground_N
    by (simp_all add: is_ground_cls_if_in_ground_cls_set)

  have
    "is_ground_trm l1" and "is_ground_trm r1" and
    "is_ground_trm l2" and "is_ground_trm r2"
    using ground_rule_if_mem_Union_equation[OF ground_N rule1_in]
    using ground_rule_if_mem_Union_equation[OF ground_N rule2_in]
    by simp_all

  from rule1_in' obtain C1' where
    C1_def: "C1 = add_mset (Pos (l1 \<approx> r1)) C1'" and
    C1_max: "is_strictly_maximal_lit (Pos (l1 \<approx> r1)) C1" and
    "r1 \<prec>\<^sub>t l1" and
    l1_irreducible: "l1 \<in> NF (rstep (rewrite_sys N2 C1))"
    by (auto elim: mem_equationE)

  from rule2_in' obtain C2' where
    C2_def: "C2 = add_mset (Pos (l2 \<approx> r2)) C2'" and
    C2_max: "is_strictly_maximal_lit (Pos (l2 \<approx> r2)) C2" and
    "r2 \<prec>\<^sub>t l2"
    by (auto elim: mem_equationE)

  have "is_ground_trm_ctxt ctxt" and "is_ground_trm l1'"
    using \<open>is_ground_trm l1\<close> \<open>l1 = ctxt\<langle>l1'\<rangle>\<close> by force+

  have "l1' = l2"
    using mgu_l1'_l2 \<open>is_ground_trm l1'\<close> \<open>is_ground_trm l2\<close>
    by (metis mgu_var_disjoint_string_sound term_subst.subst_ident_if_ground)

  have "equation N2 C1 = {(l1, r1)}"
    using rule1_in' production_eq_empty_or_singleton[OF ground_C1]
    unfolding equation_def
    by fastforce

  have "equation N2 C2 = {(l2, r2)}"
    using rule2_in' production_eq_empty_or_singleton[OF ground_C2]
    unfolding equation_def
    by fastforce

  show False
  proof (cases "ctxt = \<box>")
    case True
    hence "l1 = l2"
      using \<open>l1 = ctxt\<langle>l1'\<rangle>\<close> \<open>l1' = l2\<close>
      by simp
    hence "\<not> (l1 \<prec>\<^sub>t l2)" and "\<not> (l2 \<prec>\<^sub>t l1)"
      by (simp_all add: irreflpD)
    hence "\<not> (C1 \<prec>\<^sub>c C2)" and "\<not> (C2 \<prec>\<^sub>c C1)"
      using \<open>equation N2 C1 = {(l1, r1)}\<close> \<open>equation N2 C2 = {(l2, r2)}\<close>
        ground_C1 ground_C2 less_trm_iff_less_cls_if_lhs_equation
      by simp_all
    hence "C1 = C2"
      using ground_C1 ground_C2 totalp_on_less_cls[THEN totalp_onD, unfolded mem_Collect_eq]
      by metis
    hence "r1 = r2"
      using \<open>equation N2 C1 = {(l1, r1)}\<close> \<open>equation N2 C2 = {(l2, r2)}\<close> by simp
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
      by (metis ctxt_supt less_trm_if_subterm)
    hence "C2 \<prec>\<^sub>c C1"
      using \<open>equation N2 C1 = {(l1, r1)}\<close> \<open>equation N2 C2 = {(l2, r2)}\<close>
        ground_C1 ground_C2 less_trm_iff_less_cls_if_lhs_equation
      by simp
    hence "equation N2 C2 \<subseteq> rewrite_sys N2 C1"
      unfolding rewrite_sys_def
      using \<open>C2 \<in> N\<close>
      using mem_equationE by blast
    thus False
      unfolding \<open>equation N2 C2 = {(l2, r2)}\<close>
      using l1_irreducible[unfolded \<open>l1 = ctxt\<langle>l1'\<rangle>\<close> \<open>l1' = l2\<close>]
      by auto
  qed
qed

lemma WCR_Union_rewrite_sys:
  assumes ground_N: "is_ground_cls_set N"
  shows "WCR (rstep (\<Union>D \<in> N. equation N2 D))"
  unfolding critical_pair_lemma
proof (rule ballI)
  fix tuple
  assume tuple_in: "tuple \<in> critical_pairs (\<Union> (equation N2 ` N)) (\<Union> (equation N2 ` N))"
  then obtain b t1 t2 where tuple_def: "tuple = (b, t1, t2)"
    using prod_cases3 by blast

  moreover have "(t1, t2) \<in> (rstep (\<Union> (equation N2 ` N)))\<^sup>\<down>" if "t1 = t2"
    using that by auto

  moreover have False if "t1 \<noteq> t2"
    using that tuple_def tuple_in no_crit_pairs[OF ground_N] by simp

  ultimately show "case tuple of (b, s, t) \<Rightarrow> (s, t) \<in> (rstep (\<Union> (equation N2 ` N)))\<^sup>\<down>"
    by (cases "t1 = t2") simp_all
qed

lemma
  assumes
    ground_D: "is_ground_cls D" and
    ground_C: "is_ground_cls C" and
    "D \<preceq>\<^sub>c C" and
    E\<^sub>C_eq: "equation N C = {(s, t)}" and
    L_in: "L \<in># D" and
    topmost_trms_of_L: "mset_uprod (atm_of L) = {#u, v#}"
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

  from ground_D L_in topmost_trms_of_L have ground_u: "is_ground_trm u"
    by (metis is_ground_lit_if_in_ground_cls mset_uprod_inject mset_uprod_make_uprod sup_eq_bot_iff
        vars_atm_make_uprod vars_lit_def)

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
      using topmost_trms_of_L
      by (cases L) (simp_all add: less_lit_def)
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
      using topmost_trms_of_L
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

lemma partition_set_around_element:
  assumes tot: "totalp_on N R" and x_in: "x \<in> N"
  shows "N = {y \<in> N. R y x} \<union> {x} \<union> {y \<in> N. R x y}"
proof (intro Set.equalityI Set.subsetI)
  fix z assume "z \<in> N"
  hence "R z x \<or> z = x \<or> R x z"
    using tot[THEN totalp_onD] x_in by auto
  thus "z \<in> {y \<in> N. R y x} \<union> {x} \<union> {y \<in> N. R x y}" 
    using \<open>z \<in> N\<close> by auto
next
  fix z assume "z \<in> {y \<in> N. R y x} \<union> {x} \<union> {y \<in> N. R x y}"
  hence "z \<in> N \<or> z = x"
    by auto
  thus "z \<in> N"
    using x_in by auto
qed

lemma less_trm_const_lhs_if_mem_rstep:
  fixes t t1 t2 r
  assumes
    rule_in: "(t1, t2) \<in> rstep r" and
    ball_lt_lhs: "\<And>t1 t2. (t1, t2) \<in> r \<Longrightarrow> t \<prec>\<^sub>t t1" and
    ball_ground_lhs: "\<And>t1 t2. (t1, t2) \<in> r \<Longrightarrow> is_ground_trm t1"
  shows "t \<prec>\<^sub>t t1"
proof -
  from rule_in obtain ctxt t1' t2' \<sigma> where
    rule_in': "(t1', t2') \<in> r" and
    l_def: "t1 = ctxt\<langle>t1' \<cdot>t \<sigma>\<rangle>" and
    r_def: "t2 = ctxt\<langle>t2' \<cdot>t \<sigma>\<rangle>"
    by fast

  have "t \<prec>\<^sub>t t1' \<cdot>t \<sigma>"
    using ball_lt_lhs[OF rule_in'] ball_ground_lhs[OF rule_in'] by simp
  moreover have "t1' \<cdot>t \<sigma> \<preceq>\<^sub>t ctxt\<langle>t1' \<cdot>t \<sigma>\<rangle>"
    using ctxt_imp_supteq[THEN lesseq_trm_if_subtermeq] by simp_all
  ultimately show ?thesis
    unfolding l_def r_def
    by (metis (full_types) sup2E transpD transp_less_trm)
qed

lemma split_Union_equation:
  fixes
    N :: "('f, char list) term uprod clause set" and
    D :: "('f, char list) term uprod clause"
  assumes ground_N: "is_ground_cls_set N" and D_in: "D \<in> N"
  shows "(\<Union>C \<in> N. equation N C) =
    rewrite_sys N D \<union> equation N D \<union> (\<Union>C \<in> {C \<in> N. D \<prec>\<^sub>c C}. equation N C)"
proof -
  have "N = {C \<in> N. C \<prec>\<^sub>c D} \<union> {D} \<union> {C \<in> N. D \<prec>\<^sub>c C}"
  proof (rule partition_set_around_element)
    have "N \<subseteq> {C. is_ground_cls C}"
      using ground_N
      by (auto simp: is_ground_cls_if_in_ground_cls_set)
    thus "totalp_on N (\<prec>\<^sub>c)"
      using totalp_on_less_cls totalp_on_subset by metis
  next
    show "D \<in> N"
      using D_in by simp
  qed
  hence "(\<Union>C \<in> N. equation N C) =
      (\<Union>C \<in> {C \<in> N. C \<prec>\<^sub>c D}. equation N C) \<union> equation N D \<union> (\<Union>C \<in> {C \<in> N. D \<prec>\<^sub>c C}. equation N C)"
    by auto
  thus "(\<Union>C \<in> N. equation N C) =
    rewrite_sys N D \<union> equation N D \<union> (\<Union>C \<in> {C \<in> N. D \<prec>\<^sub>c C}. equation N C)"
    by (simp add: rewrite_sys_def)
qed

lemma split_Union_equation':
  fixes
    N :: "('f, char list) term uprod clause set" and
    D :: "('f, char list) term uprod clause"
  assumes ground_N: "is_ground_cls_set N" and D_in: "D \<in> N"
  shows "(\<Union>C \<in> N. equation N C) = rewrite_sys N D \<union> (\<Union>C \<in> {C \<in> N. D \<preceq>\<^sub>c C}. equation N C)"
  using split_Union_equation[OF ground_N D_in] D_in
  by auto

lemma split_rewrite_sys:
  assumes ground_N: "is_ground_cls_set N" and "C \<in> N" and D_in: "D \<in> N" and "D \<prec>\<^sub>c C"
  shows "rewrite_sys N C = rewrite_sys N D \<union> (\<Union>C' \<in> {C' \<in> N. D \<preceq>\<^sub>c C' \<and> C' \<prec>\<^sub>c C}. equation N C')"
proof -
  have "{D \<in> N. D \<prec>\<^sub>c C} =
        {y \<in> {D \<in> N. D \<prec>\<^sub>c C}. y \<prec>\<^sub>c D} \<union> {D} \<union> {y \<in> {D \<in> N. D \<prec>\<^sub>c C}. D \<prec>\<^sub>c y}"
  proof (rule partition_set_around_element)
    from ground_N have "{D \<in> N. D \<prec>\<^sub>c C} \<subseteq> {C. is_ground_cls C}"
      by (auto simp: is_ground_cls_if_in_ground_cls_set)
    thus "totalp_on {D \<in> N. D \<prec>\<^sub>c C} (\<prec>\<^sub>c)"
      using totalp_on_less_cls totalp_on_subset by blast
  next
    from D_in \<open>D \<prec>\<^sub>c C\<close> show "D \<in> {D \<in> N. D \<prec>\<^sub>c C}"
      by simp
  qed
  also have "\<dots> = {x \<in> N. x \<prec>\<^sub>c C \<and> x \<prec>\<^sub>c D} \<union> {D} \<union> {x \<in> N. D \<prec>\<^sub>c x \<and> x \<prec>\<^sub>c C}"
    by auto
  also have "\<dots> = {x \<in> N. x \<prec>\<^sub>c D} \<union> {D} \<union> {x \<in> N. D \<prec>\<^sub>c x \<and> x \<prec>\<^sub>c C}"
    using \<open>D \<prec>\<^sub>c C\<close> transp_less_cls
    by (metis (no_types, opaque_lifting) transpD)
  finally have Collect_N_lt_C: "{x \<in> N. x \<prec>\<^sub>c C} = {x \<in> N. x \<prec>\<^sub>c D} \<union> {x \<in> N. D \<preceq>\<^sub>c x \<and> x \<prec>\<^sub>c C}"
    by auto

  have "rewrite_sys N C = (\<Union>C' \<in> {D \<in> N. D \<prec>\<^sub>c C}. equation N C')"
    by (simp add: rewrite_sys_def)
  also have "\<dots> = (\<Union>C' \<in> {x \<in> N. x \<prec>\<^sub>c D}. equation N C') \<union> (\<Union>C' \<in> {x \<in> N. D \<preceq>\<^sub>c x \<and> x \<prec>\<^sub>c C}. equation N C')"
    unfolding Collect_N_lt_C by simp
  finally show "rewrite_sys N C = rewrite_sys N D \<union> \<Union> (equation N ` {C' \<in> N. D \<preceq>\<^sub>c C' \<and> C' \<prec>\<^sub>c C})"
    unfolding rewrite_sys_def by simp
qed

lemma mem_join_union_iff_mem_join_lhs': "(s, t) \<in> (R\<^sub>1 \<union> R\<^sub>2)\<^sup>\<down> \<longleftrightarrow> (s, t) \<in> R\<^sub>1\<^sup>\<down>"
  if
    ball_R\<^sub>1_rhs_lt_lhs: "\<And>t1 t2. (t1, t2) \<in> R\<^sub>1 \<Longrightarrow> t2 \<prec>\<^sub>t t1" and
    ball_R\<^sub>2_lt_lhs: "\<And>t1 t2. (t1, t2) \<in> R\<^sub>2 \<Longrightarrow> s \<prec>\<^sub>t t1 \<and> t \<prec>\<^sub>t t1"
  for C
proof -
  have ball_R\<^sub>1_rhs_lt_lhs': "(t1, t2) \<in> R\<^sub>1\<^sup>* \<Longrightarrow> t2 \<preceq>\<^sub>t t1" for t1 t2
  proof (induction t2 rule: rtrancl_induct)
    case base
    show ?case
      by simp
  next
    case (step y z)
    thus ?case
      using ball_R\<^sub>1_rhs_lt_lhs
      by (metis reflclp_iff transpD transp_less_trm)
  qed

  show ?thesis
  proof (rule mem_join_union_iff_mem_join_lhs)
    fix u assume "(s, u) \<in> R\<^sub>1\<^sup>*"
    hence "u \<preceq>\<^sub>t s"
      using ball_R\<^sub>1_rhs_lt_lhs' by simp

    show "u \<notin> Domain R\<^sub>2"
    proof (rule notI)
      assume "u \<in> Domain R\<^sub>2"
      then obtain u' where "(u, u') \<in> R\<^sub>2"
        by auto
      hence "s \<prec>\<^sub>t u"
        using ball_R\<^sub>2_lt_lhs by simp
      with \<open>u \<preceq>\<^sub>t s\<close> show False
        by (meson asympD asymp_less_trm strict_reflclp_conv)
    qed
  next
    fix u assume "(t, u) \<in> R\<^sub>1\<^sup>*"
    hence "u \<preceq>\<^sub>t t"
      using ball_R\<^sub>1_rhs_lt_lhs' by simp

    show "u \<notin> Domain R\<^sub>2"
    proof (rule notI)
      assume "u \<in> Domain R\<^sub>2"
      then obtain u' where "(u, u') \<in> R\<^sub>2"
        by auto
      hence "t \<prec>\<^sub>t u"
        using ball_R\<^sub>2_lt_lhs by simp
      with \<open>u \<preceq>\<^sub>t t\<close> show False
        by (meson asympD asymp_less_trm strict_reflclp_conv)
    qed
  qed
qed

lemma mem_join_union_iff_mem_join_lhs'':
  assumes
    Range_R\<^sub>1_lt_Domain_R\<^sub>2: "\<And>t1 t2. t1 \<in> Range R\<^sub>1 \<Longrightarrow> t2 \<in> Domain R\<^sub>2 \<Longrightarrow> t1 \<prec>\<^sub>t t2" and
    s_lt_Domain_R\<^sub>2: "\<And>t2. t2 \<in> Domain R\<^sub>2 \<Longrightarrow> s \<prec>\<^sub>t t2" and
    t_lt_Domain_R\<^sub>2: "\<And>t2. t2 \<in> Domain R\<^sub>2 \<Longrightarrow> t \<prec>\<^sub>t t2"
  shows "(s, t) \<in> (R\<^sub>1 \<union> R\<^sub>2)\<^sup>\<down> \<longleftrightarrow> (s, t) \<in> R\<^sub>1\<^sup>\<down>"
proof (rule mem_join_union_iff_mem_join_lhs)
  fix u assume "(s, u) \<in> R\<^sub>1\<^sup>*"
  hence "u = s \<or> u \<in> Range R\<^sub>1"
    by (meson Range.intros rtrancl.cases)
  thus "u \<notin> Domain R\<^sub>2"
    using Range_R\<^sub>1_lt_Domain_R\<^sub>2 s_lt_Domain_R\<^sub>2
    by (metis irreflpD irreflp_on_less_trm)
next
  fix u assume "(t, u) \<in> R\<^sub>1\<^sup>*"
  hence "u = t \<or> u \<in> Range R\<^sub>1"
    by (meson Range.intros rtrancl.cases)
  thus "u \<notin> Domain R\<^sub>2"
    using Range_R\<^sub>1_lt_Domain_R\<^sub>2 t_lt_Domain_R\<^sub>2
    by (metis irreflpD irreflp_on_less_trm)
qed

lemma lift_entailment_to_Union:
  fixes N D
  defines "R\<^sub>D \<equiv> rewrite_sys N D"
  assumes
    ground_N: "is_ground_cls_set N" and
    D_in: "D \<in> N" and
    R\<^sub>D_entails_D: "(\<lambda>(x, y). x \<approx> y) ` (rstep R\<^sub>D)\<^sup>\<down> \<TTurnstile> D"
  shows
    "(\<lambda>(x, y). x \<approx> y) ` (rstep (\<Union>D \<in> N. equation N D))\<^sup>\<down> \<TTurnstile> D" and
    "C \<in> N \<Longrightarrow> D \<prec>\<^sub>c C \<Longrightarrow> (\<lambda>(x, y). x \<approx> y) ` (rstep (rewrite_sys N C))\<^sup>\<down> \<TTurnstile> D"
proof -
  from ground_N D_in have ground_D: "is_ground_cls D"
    by (simp add: is_ground_cls_if_in_ground_cls_set)

  from R\<^sub>D_entails_D obtain L s t where
    L_in: "L \<in># D" and
    L_eq_disj_L_eq: "L = Pos (s \<approx> t) \<and> (s, t) \<in> (rstep R\<^sub>D)\<^sup>\<down> \<or>
     L = Neg (s \<approx> t) \<and> (s, t) \<notin> (rstep R\<^sub>D)\<^sup>\<down>"
    unfolding true_cls_def true_lit_iff
    by (metis (no_types, opaque_lifting) ex_make_uprod image_iff prod.case surj_pair)

  from L_eq_disj_L_eq show
    "(\<lambda>(x, y). x \<approx> y) ` (rstep (\<Union>D \<in> N. equation N D))\<^sup>\<down> \<TTurnstile> D" and
    "C \<in> N \<Longrightarrow> D \<prec>\<^sub>c C \<Longrightarrow> (\<lambda>(x, y). x \<approx> y) ` (rstep (rewrite_sys N C))\<^sup>\<down> \<TTurnstile> D"
    unfolding atomize_conj atomize_imp
  proof (elim disjE conjE)
    assume L_def: "L = Pos (s \<approx> t)" and "(s, t) \<in> (rstep R\<^sub>D)\<^sup>\<down>"
    have "R\<^sub>D \<subseteq> (\<Union>D \<in> N. equation N D)" and
      "\<forall>C. C \<in> N \<longrightarrow> D \<prec>\<^sub>c C \<longrightarrow> R\<^sub>D \<subseteq> rewrite_sys N C"
      unfolding R\<^sub>D_def rewrite_sys_def
      using D_in transp_less_cls[THEN transpD]
      by (auto intro: Collect_mono)
    hence "rstep R\<^sub>D \<subseteq> rstep (\<Union>D \<in> N. equation N D)" and
      "\<forall>C. C \<in> N \<longrightarrow> D \<prec>\<^sub>c C \<longrightarrow> rstep R\<^sub>D \<subseteq> rstep (rewrite_sys N C)"
      by (auto intro!: rstep_mono)
    hence "(s, t) \<in> (rstep (\<Union>D \<in> N. equation N D))\<^sup>\<down>" and
      "\<forall>C. C \<in> N \<longrightarrow> D \<prec>\<^sub>c C \<longrightarrow> (s, t) \<in> (rstep (rewrite_sys N C))\<^sup>\<down>"
      by (auto intro!: join_mono intro: set_mp[OF _ \<open>(s, t) \<in> (rstep R\<^sub>D)\<^sup>\<down>\<close>])
    thus "(\<lambda>(x, y). x \<approx> y) ` (rstep (\<Union> (equation N ` N)))\<^sup>\<down> \<TTurnstile> D \<and>
      (C \<in> N \<longrightarrow> D \<prec>\<^sub>c C \<longrightarrow> (\<lambda>(x, y). x \<approx> y) ` (rstep (rewrite_sys N C))\<^sup>\<down> \<TTurnstile> D)"
      unfolding true_cls_def true_lit_iff
      using L_in L_def by blast
  next
    have "(t1, t2) \<in> R\<^sub>D \<Longrightarrow> t2 \<prec>\<^sub>t t1" for t1 t2
      by (auto simp: R\<^sub>D_def rewrite_sys_def elim: mem_equationE)
    hence ball_R\<^sub>D_rhs_lt_lhs: "(t1, t2) \<in> rstep R\<^sub>D \<Longrightarrow> t2 \<prec>\<^sub>t t1" for t1 t2
      by (smt (verit) R\<^sub>D_def fst_conv ground_N ground_rule_if_mem_rewrite_sys
          less_trm_compatible_with_ctxt prod.collapse rstepE snd_conv
          term_subst.subst_ident_if_ground)

    assume L_def: "L = Neg (s \<approx> t)" and "(s, t) \<notin> (rstep R\<^sub>D)\<^sup>\<down>"

    have "(s, t) \<in> (rstep R\<^sub>D \<union> rstep (\<Union>C \<in> {C \<in> N. D \<preceq>\<^sub>c C}. equation N C))\<^sup>\<down> \<longleftrightarrow>
      (s, t) \<in> (rstep R\<^sub>D)\<^sup>\<down>"
    proof (rule mem_join_union_iff_mem_join_lhs')
      show "\<And>t1 t2. (t1, t2) \<in> rstep R\<^sub>D \<Longrightarrow> t2 \<prec>\<^sub>t t1"
        using ball_R\<^sub>D_rhs_lt_lhs by simp
    next
      have ball_Rinf_minus_lt_lhs: "s \<prec>\<^sub>t fst rule \<and> t \<prec>\<^sub>t fst rule"
        if rule_in: "rule \<in> (\<Union>C \<in> {C \<in> N. D \<preceq>\<^sub>c C}. equation N C)"
        for rule
      proof -
        from rule_in obtain C where
          "C \<in> N" and "D \<preceq>\<^sub>c C" and "rule \<in> equation N C"
          by auto

        from ground_N have ground_C: "is_ground_cls C"
          using \<open>C \<in> N\<close> by (simp add: is_ground_cls_if_in_ground_cls_set)

        have equation_C_eq: "equation N C = {(fst rule, snd rule)}"
          using \<open>rule \<in> equation N C\<close>
          unfolding equation_def
          using production_eq_empty_or_singleton[OF ground_C]
          by force

        show ?thesis
          using less_trm_if_neg[OF ground_D ground_C \<open>D \<preceq>\<^sub>c C\<close> equation_C_eq L_in]
          by (simp add: L_def)
      qed

      have ground_lhs_if_mem_Rinf_minus: "\<And>t1 t2.
        (t1, t2) \<in> (\<Union>C \<in> {C \<in> N. D \<preceq>\<^sub>c C}. equation N C) \<Longrightarrow> is_ground_trm t1"
        using ground_N ground_rule_if_mem_Union_equation by fastforce

      show "\<And>t1 t2. (t1, t2) \<in> rstep (\<Union> (equation N ` {C \<in> N. (\<prec>\<^sub>c)\<^sup>=\<^sup>= D C})) \<Longrightarrow>
        s \<prec>\<^sub>t t1 \<and> t \<prec>\<^sub>t t1"
        using less_trm_const_lhs_if_mem_rstep
        using ball_Rinf_minus_lt_lhs ground_lhs_if_mem_Rinf_minus
        by force
    qed

    moreover have
      "(s, t) \<in> (rstep R\<^sub>D \<union> rstep (\<Union>C' \<in> {C' \<in> N. D \<preceq>\<^sub>c C' \<and> C' \<prec>\<^sub>c C}. equation N C'))\<^sup>\<down> \<longleftrightarrow>
       (s, t) \<in> (rstep R\<^sub>D)\<^sup>\<down>"
      if "C \<in> N" and "D \<prec>\<^sub>c C"
      for C
    proof (rule mem_join_union_iff_mem_join_lhs')
      show "\<And>t1 t2. (t1, t2) \<in> rstep R\<^sub>D \<Longrightarrow> t2 \<prec>\<^sub>t t1"
        using ball_R\<^sub>D_rhs_lt_lhs by simp
    next
      have ball_lt_lhs: "s \<prec>\<^sub>t t1 \<and> t \<prec>\<^sub>t t1"
        if "C \<in> N" and "D \<prec>\<^sub>c C" and
          rule_in: "(t1, t2) \<in> (\<Union>C' \<in> {C' \<in> N. D \<preceq>\<^sub>c C' \<and> C' \<prec>\<^sub>c C}. equation N C')"
        for C t1 t2
      proof -
        from ground_N \<open>C \<in> N\<close> have ground_C: "is_ground_cls C"
          by (simp add: is_ground_cls_if_in_ground_cls_set)

        from rule_in obtain C' where
          "C' \<in> N" and "D \<preceq>\<^sub>c C'" and "C' \<prec>\<^sub>c C" and "(t1, t2) \<in> equation N C'"
          by (auto simp: rewrite_sys_def)

        from ground_N have ground_C': "is_ground_cls C'"
          using \<open>C' \<in> N\<close> by (simp add: is_ground_cls_if_in_ground_cls_set)

        have equation_C'_eq: "equation N C' = {(t1, t2)}"
          using \<open>(t1, t2) \<in> equation N C'\<close>
          unfolding equation_def
          using production_eq_empty_or_singleton[OF ground_C']
          by force

        show ?thesis
          using less_trm_if_neg[OF ground_D ground_C' \<open>D \<preceq>\<^sub>c C'\<close> equation_C'_eq L_in]
          by (simp add: L_def)
      qed

      have ground_lhs_if_mem: "\<And>t1 t2 C.
        (t1, t2) \<in> (\<Union>C' \<in> {C' \<in> N. D \<preceq>\<^sub>c C' \<and> C' \<prec>\<^sub>c C}. equation N C') \<Longrightarrow> is_ground_trm t1"
        using ground_N ground_rule_if_mem_Union_equation by fastforce

      show "\<And>t1 t2. (t1, t2) \<in> rstep (\<Union> (equation N ` {C' \<in> N. (\<prec>\<^sub>c)\<^sup>=\<^sup>= D C' \<and> C' \<prec>\<^sub>c C})) \<Longrightarrow>
        s \<prec>\<^sub>t t1 \<and> t \<prec>\<^sub>t t1"
        using less_trm_const_lhs_if_mem_rstep
        using ball_lt_lhs[OF that(1,2)] ground_lhs_if_mem
        by (metis (no_types, lifting))
    qed

    ultimately have "(s, t) \<notin> (rstep R\<^sub>D \<union> rstep (\<Union>C \<in> {C \<in> N. D \<preceq>\<^sub>c C}. equation N C))\<^sup>\<down>" and
      "\<forall>C. C \<in> N \<longrightarrow> D \<prec>\<^sub>c C \<longrightarrow>
        (s, t) \<notin> (rstep R\<^sub>D \<union> rstep (\<Union>C' \<in> {C' \<in> N. D \<preceq>\<^sub>c C' \<and> C' \<prec>\<^sub>c C}. equation N C'))\<^sup>\<down>"
      using \<open>(s, t) \<notin> (rstep R\<^sub>D)\<^sup>\<down>\<close> by simp_all
    hence "(s, t) \<notin> (rstep (\<Union>D \<in> N. equation N D))\<^sup>\<down>" and
      "\<forall>C. C \<in> N \<longrightarrow> D \<prec>\<^sub>c C \<longrightarrow> (s, t) \<notin> (rstep (rewrite_sys N C))\<^sup>\<down>"
      using split_Union_equation'[OF ground_N D_in, folded R\<^sub>D_def]
      using split_rewrite_sys[OF ground_N _ D_in, folded R\<^sub>D_def]
      by (simp_all add: rstep_union)
    hence "(s \<approx> t) \<notin> (\<lambda>(x, y). x \<approx> y) ` (rstep (\<Union>D \<in> N. equation N D))\<^sup>\<down>" and
      "\<forall>C. C \<in> N \<longrightarrow> D \<prec>\<^sub>c C \<longrightarrow> (s \<approx> t) \<notin> (\<lambda>(x, y). x \<approx> y) ` (rstep (rewrite_sys N C))\<^sup>\<down>"
      unfolding atomize_conj
      by (meson sym_join true_lit_simps(2) true_lit_uprod_iff_true_lit_prod(2))
    thus "(\<lambda>(x, y). x \<approx> y) ` (rstep (\<Union> (equation N ` N)))\<^sup>\<down> \<TTurnstile> D \<and>
    (C \<in> N \<longrightarrow> D \<prec>\<^sub>c C \<longrightarrow> (\<lambda>(x, y). x \<approx> y) ` (rstep (rewrite_sys N C))\<^sup>\<down> \<TTurnstile> D)"
      unfolding true_cls_def true_lit_iff
      using L_in L_def by metis
  qed
qed

lemma
  assumes
    ground_N: "is_ground_cls_set N" and
    productive: "equation N C = {(l, r)}"
  shows
    true_cls_if_productive_equation:
      "(\<lambda>(x, y). x \<approx> y) ` (rstep (\<Union>D \<in> N. equation N D))\<^sup>\<down> \<TTurnstile> C"
      "D \<in> N \<Longrightarrow> C \<prec>\<^sub>c D \<Longrightarrow> (\<lambda>(x, y). x \<approx> y) ` (rstep (rewrite_sys N D))\<^sup>\<down> \<TTurnstile> C" and
    false_cls_if_productive_equation:
      "\<not> (\<lambda>(x, y). x \<approx> y) ` (rstep (\<Union>D \<in> N. equation N D))\<^sup>\<down> \<TTurnstile> C - {#Pos (l \<approx> r)#}"
      "D \<in> N \<Longrightarrow> C \<prec>\<^sub>c D \<Longrightarrow> \<not> (\<lambda>(x, y). x \<approx> y) ` (rstep (rewrite_sys N D))\<^sup>\<down> \<TTurnstile> C - {#Pos (l \<approx> r)#}"
proof -
  from productive have "(l, r) \<in> equation N C"
    by simp
  then obtain C' where
    C_in: "C \<in> N" and
    C_def: "C = add_mset (Pos (l \<approx> r)) C'" and
    "select C = {#}" and
    "is_strictly_maximal_lit (Pos (l \<approx> r)) C" and
    "r \<prec>\<^sub>t l" and
    e: "\<not> (\<lambda>(x, y). x \<approx> y) ` (rstep (rewrite_sys N C))\<^sup>\<down> \<TTurnstile> C" and
    f: "\<not> (\<lambda>(x, y). x \<approx> y) ` (rstep (insert (l, r) (rewrite_sys N C)))\<^sup>\<down> \<TTurnstile> C'" and
    "l \<in> NF_trs (rewrite_sys N C)"
    by (rule mem_equationE) blast

  from ground_N have ground_C: "is_ground_cls C"
    using C_in
    by (simp add: is_ground_cls_if_in_ground_cls_set)

  have "(l, r) \<in> (rstep (\<Union>D \<in> N. equation N D))\<^sup>\<down>"
    using C_in \<open>(l, r) \<in> equation N C\<close> rstep_rule by blast
  thus "(\<lambda>(x, y). x \<approx> y) ` (rstep (\<Union>D \<in> N. equation N D))\<^sup>\<down> \<TTurnstile> C"
    using C_def by blast

  have "rstep (\<Union>D \<in> N. equation N D) =
        rstep (rewrite_sys N C \<union> equation N C \<union> (\<Union>D \<in> {D \<in> N. C \<prec>\<^sub>c D}. equation N D))"
    using split_Union_equation[OF ground_N C_in] by simp
  also have "\<dots> =
        rstep (rewrite_sys N C \<union> equation N C) \<union> rstep (\<Union>D \<in> {D \<in> N. C \<prec>\<^sub>c D}. equation N D)"
    by (simp add: rstep_union)
  finally have rstep_Union_equation_eq: "rstep (\<Union>D \<in> N. equation N D) =
        rstep (insert (l, r) (rewrite_sys N C)) \<union> rstep (\<Union>D \<in> {D \<in> N. C \<prec>\<^sub>c D}. equation N D)"
    unfolding productive by simp

  have mem_join_union_iff_mem_lhs:"(t1, t2) \<in> (rstep (insert (l, r) (rewrite_sys N C)) \<union>
    rstep (\<Union>D \<in> {D \<in> N. C \<prec>\<^sub>c D}. equation N D))\<^sup>\<down> \<longleftrightarrow>
    (t1, t2) \<in> (rstep (insert (l, r) (rewrite_sys N C)))\<^sup>\<down>"
    if "t1 \<preceq>\<^sub>t l" and "t2 \<preceq>\<^sub>t l"
    for t1 t2
  proof (rule mem_join_union_iff_mem_join_lhs')
    fix s1 s2 assume "(s1, s2) \<in> rstep (insert (l, r) (rewrite_sys N C))"

    moreover have "s2 \<prec>\<^sub>t s1" if "(s1, s2) \<in> rstep {(l, r)}"
    proof (rule rhs_lt_lhs_if_rule_in_rstep[OF that])
      show "\<And>s1 s2. (s1, s2) \<in> {(l, r)} \<Longrightarrow> s2 \<prec>\<^sub>t s1"
        using \<open>r \<prec>\<^sub>t l\<close> by simp
    next
      show "\<And>s1 s2 \<sigma>. (s1, s2) \<in> {(l, r)} \<Longrightarrow> s2 \<prec>\<^sub>t s1 \<Longrightarrow> s2 \<cdot>t \<sigma> \<prec>\<^sub>t s1 \<cdot>t \<sigma>"
        using ground_N C_in ground_rule_if_mem_equation[OF _ \<open>(l, r) \<in> equation N C\<close>]
        by (simp add: is_ground_cls_if_in_ground_cls_set)
    qed simp

    moreover have "s2 \<prec>\<^sub>t s1" if "(s1, s2) \<in> rstep (rewrite_sys N C)"
    proof (rule rhs_lt_lhs_if_rule_in_rstep[OF that])
      show "\<And>s1 s2. (s1, s2) \<in> rewrite_sys N C \<Longrightarrow> s2 \<prec>\<^sub>t s1"
        by (simp add: rhs_lt_lhs_if_mem_rewrite_sys)
    next
      show "\<And>s1 s2 \<sigma>. (s1, s2) \<in> rewrite_sys N C \<Longrightarrow> s2 \<prec>\<^sub>t s1 \<Longrightarrow> s2 \<cdot>t \<sigma> \<prec>\<^sub>t s1 \<cdot>t \<sigma>"
        using ground_N ground_rule_if_mem_rewrite_sys by auto
    qed simp

    ultimately show "s2 \<prec>\<^sub>t s1"
      by fast
  next
    have ball_lt_lhs: "t1 \<prec>\<^sub>t s1 \<and> t2 \<prec>\<^sub>t s1"
      if rule_in: "(s1, s2) \<in> (\<Union>D \<in> {D \<in> N. C \<prec>\<^sub>c D}. equation N D)"
      for s1 s2
    proof -
      from rule_in obtain D where
        "D \<in> N" and "C \<prec>\<^sub>c D" and "(s1, s2) \<in> equation N D"
        by (auto simp: rewrite_sys_def)

      from ground_N have ground_D: "is_ground_cls D"
        using \<open>D \<in> N\<close> by (simp add: is_ground_cls_if_in_ground_cls_set)

      have E\<^sub>D_eq: "equation N D = {(s1, s2)}"
        using \<open>(s1, s2) \<in> equation N D\<close>
        unfolding equation_def
        using production_eq_empty_or_singleton[OF ground_D]
        by force

      have "l \<prec>\<^sub>t s1"
        using \<open>C \<prec>\<^sub>c D\<close>
        using less_trm_iff_less_cls_if_lhs_equation[OF E\<^sub>D_eq productive ground_D ground_C]
        by metis

      with \<open>t1 \<preceq>\<^sub>t l\<close> \<open>t2 \<preceq>\<^sub>t l\<close> show ?thesis
        by (metis reflclp_iff transpD transp_less_trm)
    qed

    moreover have ground_lhs_if_mem: "\<And>t1 t2.
        (t1, t2) \<in> (\<Union>D \<in> {D \<in> N. C \<prec>\<^sub>c D}. equation N D) \<Longrightarrow> is_ground_trm t1"
      using ground_N ground_rule_if_mem_Union_equation by fastforce

    ultimately show "\<And>l r. (l, r) \<in> rstep (\<Union> (equation N ` {D \<in> N. C \<prec>\<^sub>c D})) \<Longrightarrow> t1 \<prec>\<^sub>t l \<and> t2 \<prec>\<^sub>t l"
      using rstep_Union_equation_eq
      using less_trm_const_lhs_if_mem_rstep
      by presburger
  qed

  have neg_concl1: "\<not> (\<lambda>(x, y). x \<approx> y) ` (rstep (\<Union>D \<in> N. equation N D))\<^sup>\<down> \<TTurnstile> C'"
    unfolding true_cls_def Set.bex_simps
  proof (intro ballI)
    fix L assume L_in: "L \<in># C'"
    hence "L \<in># C"
      by (simp add: C_def)

    obtain t1 t2 where
      atm_L_eq: "atm_of L = t1 \<approx> t2"
      by (metis ex_make_uprod)
    hence trms_of_L: "mset_uprod (atm_of L) = {#t1, t2#}"
      by (metis mset_uprod_make_uprod)
    hence "t1 \<preceq>\<^sub>t l" and "t2 \<preceq>\<^sub>t l"
      unfolding atomize_conj
      using less_trm_if_neg[OF ground_C ground_C reflclp_refl productive \<open>L \<in># C\<close>]
      using lesseq_trm_if_pos[OF ground_C ground_C reflclp_refl productive \<open>L \<in># C\<close>]
      by (metis (no_types, opaque_lifting) add_mset_commute sup2CI)

    have "(t1, t2) \<notin> (rstep (\<Union>D \<in> N. equation N D))\<^sup>\<down>" if L_def: "L = Pos (t1 \<approx> t2)"
    proof -
      from that have "(t1, t2) \<notin> (rstep (insert (l, r) (rewrite_sys N C)))\<^sup>\<down>"
        using f \<open>L \<in># C'\<close> by blast
      thus ?thesis
        using rstep_Union_equation_eq mem_join_union_iff_mem_lhs[OF \<open>t1 \<preceq>\<^sub>t l\<close> \<open>t2 \<preceq>\<^sub>t l\<close>]
        by simp
    qed

    moreover have "(t1, t2) \<in> (rstep (\<Union>D \<in> N. equation N D))\<^sup>\<down>" if L_def: "L = Neg (t1 \<approx> t2)"
    proof -
      from that have "(t1, t2) \<in> (rstep (insert (l, r) (rewrite_sys N C)))\<^sup>\<down>"
        using f \<open>L \<in># C'\<close>
        by (meson equations_entail_lit.simps(2) equations_entail_lit_iff true_cls_def)
      thus ?thesis
        using rstep_Union_equation_eq mem_join_union_iff_mem_lhs[OF \<open>t1 \<preceq>\<^sub>t l\<close> \<open>t2 \<preceq>\<^sub>t l\<close>] by simp
    qed

    ultimately show "\<not> (\<lambda>(x, y). x \<approx> y) ` (rstep (\<Union> (equation N ` N)))\<^sup>\<down> \<TTurnstile>l L"
      using atm_L_eq true_lit_uprod_iff_true_lit_prod[OF sym_join] true_lit_simps
      by (smt (verit, ccfv_SIG) literal.exhaust_sel)
  qed
  then show "\<not> (\<lambda>(x, y). x \<approx> y) ` (rstep (\<Union>D \<in> N. equation N D))\<^sup>\<down> \<TTurnstile> C - {#Pos (l \<approx> r)#}"
    by (simp add: C_def)

  assume "D \<in> N" and "C \<prec>\<^sub>c D"
  then have "(l, r) \<in> (rstep (rewrite_sys N D))\<^sup>\<down>"
    by (smt (verit, ccfv_threshold) C_in UN_iff \<open>(l, r) \<in> equation N C\<close> joinI_left mem_Collect_eq
        r_into_rtrancl rstep_rule rewrite_sys_def)
  thus "(\<lambda>(x, y). x \<approx> y) ` (rstep (rewrite_sys N D))\<^sup>\<down> \<TTurnstile> C"
    using C_def by blast

  from \<open>D \<in> N\<close> have "rewrite_sys N D \<subseteq> (\<Union>D \<in> N. equation N D)"
    by (auto simp: rewrite_sys_def)
  hence "rstep (rewrite_sys N D) \<subseteq> rstep (\<Union>D \<in> N. equation N D)"
    using rstep_mono by metis
  hence "(rstep (rewrite_sys N D))\<^sup>\<down> \<subseteq> (rstep (\<Union>D \<in> N. equation N D))\<^sup>\<down>"
    using join_mono by metis

  have "\<not> (\<lambda>(x, y). x \<approx> y) ` (rstep (rewrite_sys N D))\<^sup>\<down> \<TTurnstile> C'"
    unfolding true_cls_def Set.bex_simps
  proof (intro ballI)
    fix L assume L_in: "L \<in># C'"
    hence "L \<in># C"
      by (simp add: C_def)

    obtain t1 t2 where
      atm_L_eq: "atm_of L = t1 \<approx> t2"
      by (metis ex_make_uprod)
    hence trms_of_L: "mset_uprod (atm_of L) = {#t1, t2#}"
      by (metis mset_uprod_make_uprod)
    hence "t1 \<preceq>\<^sub>t l" and "t2 \<preceq>\<^sub>t l"
      unfolding atomize_conj
      using less_trm_if_neg[OF ground_C ground_C reflclp_refl productive \<open>L \<in># C\<close>]
      using lesseq_trm_if_pos[OF ground_C ground_C reflclp_refl productive \<open>L \<in># C\<close>]
      by (metis (no_types, opaque_lifting) add_mset_commute sup2CI)

    have "(t1, t2) \<notin> (rstep (rewrite_sys N D))\<^sup>\<down>" if L_def: "L = Pos (t1 \<approx> t2)"
    proof -
      from that have "(t1, t2) \<notin> (rstep (insert (l, r) (rewrite_sys N C)))\<^sup>\<down>"
        using f \<open>L \<in># C'\<close> by blast
      thus ?thesis
        using rstep_Union_equation_eq mem_join_union_iff_mem_lhs[OF \<open>t1 \<preceq>\<^sub>t l\<close> \<open>t2 \<preceq>\<^sub>t l\<close>]
        using \<open>(rstep (rewrite_sys N D))\<^sup>\<down> \<subseteq> (rstep (\<Union> (equation N ` N)))\<^sup>\<down>\<close> by auto
    qed

    moreover have "(t1, t2) \<in> (rstep (rewrite_sys N D))\<^sup>\<down>" if L_def: "L = Neg (t1 \<approx> t2)"
      using e
    proof (rule contrapos_np)
      assume "(t1, t2) \<notin> (rstep (rewrite_sys N D))\<^sup>\<down>"
      hence "(t1, t2) \<notin> (rstep (rewrite_sys N C))\<^sup>\<down>"
        using rewrite_sys_subset_if_less_cls[OF \<open>C \<prec>\<^sub>c D\<close>]
        by (meson join_mono rstep_mono subsetD)
      thus "(\<lambda>(x, y). x \<approx> y) ` (rstep (rewrite_sys N C))\<^sup>\<down> \<TTurnstile> C"
        using neg_literal_notin_imp_true_cls[of "t1 \<approx> t2" C "(\<lambda>(x, y). x \<approx> y) ` _\<^sup>\<down>"]
        unfolding uprod_mem_image_iff_prod_mem[OF sym_join]
        using L_def L_in C_def
        by simp
    qed

    ultimately show "\<not> (\<lambda>(x, y). x \<approx> y) ` (rstep (rewrite_sys N D))\<^sup>\<down> \<TTurnstile>l L"
      using atm_L_eq true_lit_uprod_iff_true_lit_prod[OF sym_join] true_lit_simps
      by (smt (verit, ccfv_SIG) literal.exhaust_sel)
  qed
  thus "\<not> (\<lambda>(x, y). x \<approx> y) ` (rstep (rewrite_sys N D))\<^sup>\<down> \<TTurnstile> C - {#Pos (l \<approx> r)#}"
    by (simp add: C_def)
qed

lemma from_neq_double_rtrancl_to_eqE:
  assumes "x \<noteq> y" and "(x, z) \<in> r\<^sup>*" and "(y, z) \<in> r\<^sup>*"
  obtains
    w where "(x, w) \<in> r" and "(w, z) \<in> r\<^sup>*" |
    w where "(y, w) \<in> r" and "(w, z) \<in> r\<^sup>*"
  using assms
  by (metis converse_rtranclE)


lemma ex_step_if_joinable:
  assumes "asymp R" "(x, z) \<in> r\<^sup>*" and "(y, z) \<in> r\<^sup>*"
  shows
    "R\<^sup>=\<^sup>= z y \<Longrightarrow> R y x \<Longrightarrow> \<exists>w. (x, w) \<in> r \<and> (w, z) \<in> r\<^sup>*"
    "R\<^sup>=\<^sup>= z x \<Longrightarrow> R x y \<Longrightarrow> \<exists>w. (y, w) \<in> r \<and> (w, z) \<in> r\<^sup>*"
  using assms
  by (metis asympD converse_rtranclE reflclp_iff)+

lemma trans_join_rstep_rewrite_sys: "trans ((rstep (rewrite_sys N C))\<^sup>\<down>)"
  if ground_N: "is_ground_cls_set N"
  for N C
proof (rule trans_join)
  have ground_model: "\<forall>rule \<in> rewrite_sys N C.
              is_ground_trm (fst rule) \<and> is_ground_trm (snd rule)"
    using ground_rule_if_mem_rewrite_sys[OF ground_N] by metis

  have "wf ((rewrite_inside_ctxt (rewrite_sys N C))\<inverse>)"
  proof (rule wf_converse_rewrite_inside_ctxt)
    fix s t
    assume "(s, t) \<in> rewrite_sys N C"
    then obtain D where "(s, t) \<in> equation N D"
      unfolding rewrite_sys_def by auto
    thus "t \<prec>\<^sub>t s"
      by (auto elim: mem_equationE)
  qed auto
  thus "SN (rstep (rewrite_sys N C))"
    by (simp only: SN_iff_wf rstep_eq_rewrite_inside_ctxt_if_ground[OF ground_model])
next
  show "WCR (rstep (rewrite_sys N C))"
    unfolding rewrite_sys_def
    using WCR_Union_rewrite_sys
    by (metis (mono_tags, lifting) SUP_bot_conv(1) ground_N mem_Collect_eq
        vars_cls_set_def)
qed

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
    "entails (\<Union>D\<^sub>\<G> \<in> N\<^sub>\<G>. equation N\<^sub>\<G> D\<^sub>\<G>) C\<^sub>\<G>"
    "D\<^sub>\<G> \<in> N\<^sub>\<G> \<Longrightarrow> C\<^sub>\<G> \<prec>\<^sub>c D\<^sub>\<G> \<Longrightarrow> entails (rewrite_sys N\<^sub>\<G> D\<^sub>\<G>) C\<^sub>\<G>"
  unfolding atomize_conj atomize_imp
  using wfP_less_cls imageI[OF C_in, of cls_gcls, folded C\<^sub>\<G>_def N\<^sub>\<G>_def]
proof (induction C\<^sub>\<G> arbitrary: D\<^sub>\<G> rule: wfP_induct_rule)
  case (less C\<^sub>\<G>)
  note IH = less.IH

  from \<open>{#} \<notin> N\<close> \<open>C\<^sub>\<G> \<in> N\<^sub>\<G>\<close> have "C\<^sub>\<G> \<noteq> {#}"
    by (metis N\<^sub>\<G>_def image_iff local.cls_gcls_empty_mset local.cls_gcls_inverse)

  have ground_N\<^sub>\<G>: "is_ground_cls_set N\<^sub>\<G>"
    unfolding N\<^sub>\<G>_def
    by (simp add: vars_cls_set_def)
  hence ground_C\<^sub>\<G>: "is_ground_cls C\<^sub>\<G>"
    using less.prems
    by (simp add: is_ground_cls_if_in_ground_cls_set)

  define I where
    "I = (rstep (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>))\<^sup>\<down>"

  have "refl I"
    by (simp only: I_def refl_join)

  have "trans I"
    unfolding I_def
    using trans_join_rstep_rewrite_sys[OF ground_N\<^sub>\<G>] by simp

  have "sym I"
    by (simp only: I_def sym_join)

  have "compatible_with_ctxt I"
    by (simp only: I_def compatible_with_ctxt_join compatible_with_ctxt_rstep)

  note I_interp = \<open>refl I\<close> \<open>trans I\<close> \<open>sym I\<close> \<open>compatible_with_ctxt I\<close>

  have i: "entails (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>) C\<^sub>\<G> \<longleftrightarrow> (equation N\<^sub>\<G> C\<^sub>\<G> = {})"
  proof (rule iffI)
    show "entails (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>) C\<^sub>\<G> \<Longrightarrow> equation N\<^sub>\<G> C\<^sub>\<G> = {}"
      unfolding entails_def rewrite_sys_def
      by (smt (z3) Collect_cong Collect_empty_eq equation_def production.elims)
  next
    assume "equation N\<^sub>\<G> C\<^sub>\<G> = {}"
    show "entails (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>) C\<^sub>\<G>"
    proof (cases "\<exists>A. Neg A \<in># C\<^sub>\<G> \<and> (Neg A \<in># select C\<^sub>\<G> \<or> select C\<^sub>\<G> = {#} \<and> is_maximal_lit (Neg A) C\<^sub>\<G>)")
      case ex_neg_lit_sel_or_max: True
      then obtain s s' where
        "Neg (s \<approx> s') \<in># C\<^sub>\<G>" and
        sel_or_max: "Neg (s \<approx> s') \<in># select C\<^sub>\<G> \<or> select C\<^sub>\<G> = {#} \<and> is_maximal_lit (Neg (s \<approx> s')) C\<^sub>\<G>"
        by (metis ex_make_uprod)
      then obtain C\<^sub>\<G>' where
        C\<^sub>\<G>_def: "C\<^sub>\<G> = add_mset (Neg (s \<approx> s')) C\<^sub>\<G>'"
        by (metis mset_add)
      hence ground_C\<^sub>\<G>': "is_ground_cls C\<^sub>\<G>'"
        using ground_C\<^sub>\<G> by simp

      show ?thesis
      proof (cases "(\<lambda>(x, y). x \<approx> y) ` (rstep (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>))\<^sup>\<down> \<TTurnstile>l Pos (s \<approx> s')")
        case True
        hence "(s, s') \<in> (rstep (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>))\<^sup>\<down>"
          by (meson sym_join true_lit_simps(1) true_lit_uprod_iff_true_lit_prod(1))

        have "s = s' \<or> s \<prec>\<^sub>t s' \<or> s' \<prec>\<^sub>t s"
          using totalp_on_less_trm
          by (metis (mono_tags, lifting) \<open>Neg (s \<approx> s') \<in># C\<^sub>\<G>\<close> ground_C\<^sub>\<G>
              is_ground_lit_if_in_ground_cls mem_Collect_eq sup_eq_bot_iff totalp_on_def
              vars_atm_make_uprod vars_lit_Neg)
        thus ?thesis
        proof (rule disjE)
          assume "s = s'"
          define \<iota> :: "('f, char list) gterm uprod clause inference" where
            "\<iota> = Infer [gcls_cls C\<^sub>\<G>] (gcls_cls C\<^sub>\<G>')"

          have "eq_resolution C\<^sub>\<G> C\<^sub>\<G>'"
          proof (rule eq_resolutionI)
            show "C\<^sub>\<G> = add_mset (Neg (s \<approx> s')) C\<^sub>\<G>'"
              by (simp add: C\<^sub>\<G>_def)
          next
            show "term_subst.is_imgu Var {{s, s'}}"
              by (simp add: \<open>s = s'\<close> term_subst.is_imgu_id_subst)
          next
            show "select C\<^sub>\<G> = {#} \<and> is_maximal_lit (Neg (s \<approx> s') \<cdot>l Var) (C\<^sub>\<G> \<cdot> Var) \<or> Neg (s \<approx> s') \<in># select C\<^sub>\<G>"
              using sel_or_max by force
          qed simp_all
          hence "\<iota> \<in> G_Inf"
            using ground_C\<^sub>\<G>
            by (auto simp: \<iota>_def G_Inf_def)

          moreover have "\<And>t. t \<in> set (prems_of \<iota>) \<Longrightarrow> t \<in> N"
            using \<open>C\<^sub>\<G> \<in> N\<^sub>\<G>\<close>
            by (auto simp add: \<iota>_def N\<^sub>\<G>_def)

          ultimately have "\<iota> \<in> G.Inf_from N"
            by (auto simp: G.Inf_from_def)
          hence "\<iota> \<in> G.Red_I N"
            using \<open>G.saturated N\<close>
            by (auto simp: G.saturated_def)
          then obtain DD where
            DD_subset: "DD \<subseteq> N" and
            "finite DD" and
            DD_entails_C\<^sub>\<G>': "G_entails DD {gcls_cls C\<^sub>\<G>'}" and
            ball_DD_lt_C\<^sub>\<G>: "\<forall>D\<in>DD. cls_gcls D \<prec>\<^sub>c C\<^sub>\<G>"
            unfolding G.Red_I_def G.redundant_infer_def
            using ground_C\<^sub>\<G>
            by (auto simp: \<iota>_def)

          moreover have "\<forall>D\<in>DD. entails (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>) (cls_gcls D)"
            using IH[THEN conjunct2, THEN conjunct2, rule_format, of _ C\<^sub>\<G>]
            using N\<^sub>\<G>_def \<open>C\<^sub>\<G> \<in> N\<^sub>\<G>\<close> DD_subset ball_DD_lt_C\<^sub>\<G>
            by blast

          ultimately have "entails (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>) C\<^sub>\<G>'"
            using I_interp DD_entails_C\<^sub>\<G>' ground_C\<^sub>\<G>'
            unfolding entails_def G_entails_def
            by (simp add: I_def true_clss_def)
          then show "entails (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>) C\<^sub>\<G>"
            using C\<^sub>\<G>_def entails_def by simp
        next
          from \<open>(s, s') \<in> (rstep (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>))\<^sup>\<down>\<close> obtain u where
            s_u: "(s, u) \<in> (rstep (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>))\<^sup>*" and
            s'_u: "(s', u) \<in> (rstep (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>))\<^sup>*"
            by auto
          moreover hence "u \<preceq>\<^sub>t s" and "u \<preceq>\<^sub>t s'"
            using rhs_lesseq_trm_lhs_if_mem_rtrancl_rstep_rewrite_sys[OF ground_N\<^sub>\<G>] by simp_all

          moreover assume "s \<prec>\<^sub>t s' \<or> s' \<prec>\<^sub>t s"

          ultimately obtain u\<^sub>0 where
            "s' \<prec>\<^sub>t s \<Longrightarrow> (s, u\<^sub>0) : rstep (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>)"
            "s \<prec>\<^sub>t s' \<Longrightarrow> (s', u\<^sub>0) : rstep (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>)" and
            "(u\<^sub>0, u) : (rstep (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>))\<^sup>*"
            using ex_step_if_joinable[OF _ s_u s'_u]
            by (metis asympD asymp_less_trm)
          then obtain ctxt t t' where
            s_eq_if: "s' \<prec>\<^sub>t s \<Longrightarrow> s = ctxt\<langle>t\<rangle>" and
            s'_eq_if: "s \<prec>\<^sub>t s' \<Longrightarrow> s' = ctxt\<langle>t\<rangle>" and
            "u\<^sub>0 = ctxt\<langle>t'\<rangle>" and
            "(t, t') \<in> rewrite_sys N\<^sub>\<G> C\<^sub>\<G>"
            by (smt (verit, ccfv_SIG) \<open>s \<prec>\<^sub>t s' \<or> s' \<prec>\<^sub>t s\<close> asympD asymp_less_trm fst_conv ground_N\<^sub>\<G>
                rstep.cases snd_conv term_subst.subst_ident_if_ground ground_rule_if_mem_rewrite_sys)
          then obtain D\<^sub>\<G> where
            "(t, t') \<in> equation N\<^sub>\<G> D\<^sub>\<G>" and "D\<^sub>\<G> \<in> N\<^sub>\<G>" and "D\<^sub>\<G> \<prec>\<^sub>c C\<^sub>\<G>"
            unfolding rewrite_sys_def by auto
          then obtain D\<^sub>\<G>' where
            D\<^sub>\<G>_def: "D\<^sub>\<G> = add_mset (Pos (t \<approx> t')) D\<^sub>\<G>'" and
            sel_D\<^sub>\<G>: "select D\<^sub>\<G> = {#}" and
            max_t_t': "is_strictly_maximal_lit (Pos (t \<approx> t')) D\<^sub>\<G>" and
            "t' \<prec>\<^sub>t t"
            by (elim mem_equationE) fast

          have ground_D\<^sub>\<G>: "is_ground_cls D\<^sub>\<G>"
            using \<open>D\<^sub>\<G> \<in> N\<^sub>\<G>\<close> N\<^sub>\<G>_def by fastforce

          have superI: "neg_superposition C\<^sub>\<G> D\<^sub>\<G> (add_mset (Neg (s\<^sub>1\<langle>t'\<rangle> \<approx> s\<^sub>1')) (C\<^sub>\<G>' + D\<^sub>\<G>'))"
            if "{s, s'} = {s\<^sub>1\<langle>t\<rangle>, s\<^sub>1'}" and "s\<^sub>1' \<prec>\<^sub>t s\<^sub>1\<langle>t\<rangle>"
            for s\<^sub>1 s\<^sub>1'
          proof (rule neg_superpositionI)
            show "vars_cls (C\<^sub>\<G> \<cdot> Var) \<inter> vars_cls (D\<^sub>\<G> \<cdot> Var) = {}"
              using ground_D\<^sub>\<G> ground_C\<^sub>\<G> by simp
          next
            show "C\<^sub>\<G> = add_mset (Neg (s \<approx> s')) C\<^sub>\<G>'"
              by (simp add: C\<^sub>\<G>_def)
          next
            show "D\<^sub>\<G> = add_mset (Pos (t \<approx> t')) D\<^sub>\<G>'"
              by (simp add: D\<^sub>\<G>_def)
          next
            show "is_Fun t"
              using ground_D\<^sub>\<G>
              by (auto simp: D\<^sub>\<G>_def)
          next
            show "\<not> (C\<^sub>\<G> \<cdot> Var \<cdot> Var) \<preceq>\<^sub>c (D\<^sub>\<G> \<cdot> Var \<cdot> Var)"
              using \<open>D\<^sub>\<G> \<prec>\<^sub>c C\<^sub>\<G>\<close> asymp_less_cls
              by (metis asympD reflclp_iff subst_cls_Var_ident)
          next
            show "select C\<^sub>\<G> = {#} \<and> is_maximal_lit (Neg (s \<approx> s') \<cdot>l Var \<cdot>l Var) (C\<^sub>\<G> \<cdot> Var \<cdot> Var) \<or>
              Neg (s \<approx> s') \<in># select C\<^sub>\<G>"
              using sel_or_max by auto
          next
            show "is_maximal_wrt (\<prec>\<^sub>l)\<^sup>=\<^sup>= (Pos (t \<approx> t') \<cdot>l Var \<cdot>l Var) (D\<^sub>\<G> \<cdot> Var \<cdot> Var)"
              using max_t_t'
              by (metis subst_cls_Var_ident subst_lit_Var_ident)
          next
            show "\<not> t \<cdot>t Var \<cdot>t Var \<preceq>\<^sub>t t' \<cdot>t Var \<cdot>t Var"
              using \<open>t' \<prec>\<^sub>t t\<close> asymp_less_trm
              by (metis (full_types) asympD subst_apply_term_empty sup2E)
          next
            from that(1) show "Neg (s \<approx> s') = Neg (s\<^sub>1\<langle>t\<rangle> \<approx> s\<^sub>1')"
              using make_uprod_eq_make_uprod_iff by fastforce
          next
            from that(2) show "\<not> s\<^sub>1\<langle>t\<rangle> \<cdot>t Var \<cdot>t Var \<preceq>\<^sub>t s\<^sub>1' \<cdot>t Var \<cdot>t Var"
              using asymp_less_trm
              by (metis (full_types) asympD subst_apply_term_empty sup2E)
          qed simp_all

          have "neg_superposition C\<^sub>\<G> D\<^sub>\<G> (add_mset (Neg (ctxt\<langle>t'\<rangle> \<approx> s')) (C\<^sub>\<G>' + D\<^sub>\<G>'))"
            if \<open>s' \<prec>\<^sub>t s\<close>
          proof (rule superI)
            from that show "{s, s'} = {ctxt\<langle>t\<rangle>, s'}"
              using s_eq_if by simp
          next
            from that show "s' \<prec>\<^sub>t ctxt\<langle>t\<rangle>"
              using s_eq_if by simp
          qed

          moreover have "neg_superposition C\<^sub>\<G>  D\<^sub>\<G> (add_mset (Neg (ctxt\<langle>t'\<rangle> \<approx> s)) (C\<^sub>\<G>' + D\<^sub>\<G>'))"
            if \<open>s \<prec>\<^sub>t s'\<close>
          proof (rule superI)
            from that show "{s, s'} = {ctxt\<langle>t\<rangle>, s}"
              using s'_eq_if by auto
          next
            from that show "s \<prec>\<^sub>t ctxt\<langle>t\<rangle>"
              using s'_eq_if by simp
          qed

          ultimately obtain C\<^sub>\<G>D\<^sub>\<G> where
            super: "neg_superposition C\<^sub>\<G>  D\<^sub>\<G> C\<^sub>\<G>D\<^sub>\<G>" and
            C\<^sub>\<G>D\<^sub>\<G>_eq1: "s' \<prec>\<^sub>t s \<Longrightarrow> C\<^sub>\<G>D\<^sub>\<G> = add_mset (Neg (ctxt\<langle>t'\<rangle> \<approx> s')) (C\<^sub>\<G>' + D\<^sub>\<G>')" and
            C\<^sub>\<G>D\<^sub>\<G>_eq2: "s \<prec>\<^sub>t s' \<Longrightarrow> C\<^sub>\<G>D\<^sub>\<G> = add_mset (Neg (ctxt\<langle>t'\<rangle> \<approx> s)) (C\<^sub>\<G>' + D\<^sub>\<G>')"
            using \<open>s \<prec>\<^sub>t s' \<or> s' \<prec>\<^sub>t s\<close> s'_eq_if s_eq_if by metis
          hence ground_C\<^sub>\<G>D\<^sub>\<G>: "is_ground_cls C\<^sub>\<G>D\<^sub>\<G>"
            using ground_C\<^sub>\<G> ground_D\<^sub>\<G> superposition_preserves_groundness
              superposition_if_neg_superposition
            by metis

          define \<iota> :: "('f, char list) gterm uprod clause inference" where
            "\<iota> = Infer [gcls_cls D\<^sub>\<G>, gcls_cls C\<^sub>\<G>] (gcls_cls C\<^sub>\<G>D\<^sub>\<G>)"

          have "\<iota> \<in> G_Inf"
            using ground_C\<^sub>\<G> ground_D\<^sub>\<G> super superposition_if_neg_superposition
            by (auto simp: \<iota>_def G_Inf_def)

          moreover have "\<And>t. t \<in> set (prems_of \<iota>) \<Longrightarrow> t \<in> N"
            using \<open>C\<^sub>\<G> \<in> N\<^sub>\<G>\<close> \<open>D\<^sub>\<G> \<in> N\<^sub>\<G>\<close>
            by (auto simp add: \<iota>_def N\<^sub>\<G>_def)

          ultimately have "\<iota> \<in> G.Inf_from N"
            by (auto simp: G.Inf_from_def)
          hence "\<iota> \<in> G.Red_I N"
            using \<open>G.saturated N\<close>
            by (auto simp: G.saturated_def)
          then obtain DD where
            DD_subset: "DD \<subseteq> N" and
            "finite DD" and
            DD_entails_C\<^sub>\<G>D\<^sub>\<G>: "G_entails (insert (gcls_cls D\<^sub>\<G>) DD) {gcls_cls C\<^sub>\<G>D\<^sub>\<G>}" and
            ball_DD_lt_C\<^sub>\<G>: "\<forall>D\<in>DD. cls_gcls D \<prec>\<^sub>c C\<^sub>\<G>"
            unfolding G.Red_I_def G.redundant_infer_def mem_Collect_eq
            using ground_C\<^sub>\<G>
            by (auto simp: \<iota>_def)

          moreover have "\<forall>D\<in> insert (gcls_cls D\<^sub>\<G>) DD. entails (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>) (cls_gcls D)"
            using IH[THEN conjunct2, THEN conjunct2, rule_format, of _ C\<^sub>\<G>]
            using N\<^sub>\<G>_def \<open>C\<^sub>\<G> \<in> N\<^sub>\<G>\<close> \<open>D\<^sub>\<G> \<in> N\<^sub>\<G>\<close> \<open>D\<^sub>\<G> \<prec>\<^sub>c C\<^sub>\<G>\<close> DD_subset ball_DD_lt_C\<^sub>\<G> ground_D\<^sub>\<G>
            by (metis imageI in_mono insert_iff local.gcls_cls_inverse)

          ultimately have "entails (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>) C\<^sub>\<G>D\<^sub>\<G>"
            using I_interp DD_entails_C\<^sub>\<G>D\<^sub>\<G> ground_C\<^sub>\<G>D\<^sub>\<G>
            unfolding entails_def G_entails_def
            by (simp add: I_def true_clss_def)

          moreover have "\<not> entails (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>) D\<^sub>\<G>'"
            unfolding entails_def
            using false_cls_if_productive_equation(2)[OF ground_N\<^sub>\<G> _ \<open>C\<^sub>\<G> \<in> N\<^sub>\<G>\<close> \<open>D\<^sub>\<G> \<prec>\<^sub>c C\<^sub>\<G>\<close>]
            by (metis D\<^sub>\<G>_def \<open>(t, t') \<in> equation N\<^sub>\<G> D\<^sub>\<G>\<close> add_mset_remove_trivial empty_iff
                equation_def ground_D\<^sub>\<G> production_eq_empty_or_singleton singletonD)

          moreover have "\<not> (\<lambda>(x, y). x \<approx> y) ` (rstep (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>))\<^sup>\<down> \<TTurnstile>l (Neg (ctxt\<langle>t'\<rangle> \<approx> s'))"
            if "s' \<prec>\<^sub>t s"
            using \<open>(u\<^sub>0, u) \<in> (rstep (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>))\<^sup>*\<close> \<open>u\<^sub>0 = ctxt\<langle>t'\<rangle>\<close> s'_u by blast

          moreover have "\<not> (\<lambda>(x, y). x \<approx> y) ` (rstep (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>))\<^sup>\<down> \<TTurnstile>l (Neg (ctxt\<langle>t'\<rangle> \<approx> s))"
            if "s \<prec>\<^sub>t s'"
            using \<open>(u\<^sub>0, u) \<in> (rstep (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>))\<^sup>*\<close> \<open>u\<^sub>0 = ctxt\<langle>t'\<rangle>\<close> s_u by blast

          ultimately show "entails (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>) C\<^sub>\<G>"
            unfolding entails_def C\<^sub>\<G>_def
            using \<open>s \<prec>\<^sub>t s' \<or> s' \<prec>\<^sub>t s\<close> C\<^sub>\<G>D\<^sub>\<G>_eq1 C\<^sub>\<G>D\<^sub>\<G>_eq2 by fast
        qed
      next
        case False
        thus ?thesis
          using \<open>Neg (s \<approx> s') \<in># C\<^sub>\<G>\<close>
          by (auto simp add: entails_def true_cls_def)
      qed
    next
      case False
      hence "select C\<^sub>\<G> = {#}"
        using select_subset select_negative_lits
        by (metis (no_types, opaque_lifting) Neg_atm_of_iff mset_subset_eqD multiset_nonemptyE)
        
      from False obtain A where Pos_A_in: "Pos A \<in># C\<^sub>\<G>" and max_Pos_A: "is_maximal_lit (Pos A) C\<^sub>\<G>"
        using ex_is_maximal_wrt_if_not_empty[OF
            transp_less_lit[THEN transp_on_subset, OF subset_UNIV]
            asymp_less_lit[THEN asymp_on_subset, OF subset_UNIV]
            \<open>C\<^sub>\<G> \<noteq> {#}\<close>]
        using select_subset select_negative_lits
        by (metis (no_types, opaque_lifting) literal.disc(1) literal.exhaust mset_subset_eqD
            multiset_nonemptyE)
      then obtain C\<^sub>\<G>' where C\<^sub>\<G>_eq: "C\<^sub>\<G> = add_mset (Pos A) C\<^sub>\<G>'"
        by (meson mset_add)

      have ground_A: "is_ground_atm A"
        by (metis Pos_A_in ground_C\<^sub>\<G> is_ground_lit_if_in_ground_cls vars_lit_Pos)
      hence "set_uprod A \<subseteq> {t. is_ground_trm t}"
        using is_ground_term_if_in_ground_atm by auto
      hence "totalp_on (set_uprod A) (\<prec>\<^sub>t)"
        using totalp_on_less_trm totalp_on_subset by blast
      then obtain s s' where A_def: "A = (s \<approx> s')" and "s' \<preceq>\<^sub>t s"
        using ex_ordered_make_uprod[of A "(\<prec>\<^sub>t)"]
        by (metis make_uprod_sym)

      hence ground_s: "is_ground_trm s" and ground_s': "is_ground_trm s'"
        using ground_A by auto

      show ?thesis
      proof (cases "(\<lambda>(x, y). x \<approx> y) ` (rstep (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>))\<^sup>\<down> \<TTurnstile> C\<^sub>\<G>' \<or> s = s'")
        case True
        then show ?thesis
          using \<open>equation N\<^sub>\<G> C\<^sub>\<G> = {}\<close>
          using A_def C\<^sub>\<G>_eq entails_def by blast
      next
        case False

        from False have "\<not> (\<lambda>(x, y). x \<approx> y) ` (rstep (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>))\<^sup>\<down> \<TTurnstile> C\<^sub>\<G>'"
          by simp

        from False have "s' \<prec>\<^sub>t s"
          using \<open>s' \<preceq>\<^sub>t s\<close> asymp_less_trm[THEN asympD] by auto

        then show ?thesis
        proof (cases "is_strictly_maximal_lit (Pos A) C\<^sub>\<G>")
          case strictly_maximal: True
          show ?thesis
          proof (cases "s \<in> NF (rstep (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>))")
            case s_irreducible: True
            hence e_or_f_doesnt_hold: "(\<lambda>(x, y). x \<approx> y) ` (rstep (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>))\<^sup>\<down> \<TTurnstile> C\<^sub>\<G> \<or>
              (\<lambda>(x, y). x \<approx> y) ` (rstep (insert (s, s') (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>)))\<^sup>\<down> \<TTurnstile> C\<^sub>\<G>'"
              using \<open>equation N\<^sub>\<G> C\<^sub>\<G> = {}\<close>[unfolded equation_def production.simps[of N\<^sub>\<G> C\<^sub>\<G>]]
              using \<open>C\<^sub>\<G> \<in> N\<^sub>\<G>\<close> C\<^sub>\<G>_eq \<open>select C\<^sub>\<G> = {#}\<close> strictly_maximal \<open>s' \<prec>\<^sub>t s\<close>
              unfolding A_def rewrite_sys_def equation_def
              by (smt (verit, best) Collect_empty_eq)
            show ?thesis
            proof (cases "(\<lambda>(x, y). x \<approx> y) ` (rstep (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>))\<^sup>\<down> \<TTurnstile> C\<^sub>\<G>")
              case e_doesnt_hold: True
              thus ?thesis
                by (simp add: entails_def)
            next
              case e_holds: False
              show ?thesis
              proof (cases "(\<lambda>(x, y). x \<approx> y) ` (rstep (insert (s, s') (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>)))\<^sup>\<down> \<TTurnstile> C\<^sub>\<G>'")
                case f_doesnt_hold: True
                then show ?thesis
                  using e_holds
                  sorry
              next
                case f_holds: False
                hence False
                  using e_or_f_doesnt_hold e_holds by metis
                thus ?thesis ..
              qed
            qed
          next
            case s_reducible: False
            hence "\<exists>ss. (s, ss) \<in> rstep (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>)"
              unfolding NF_def by auto
            then obtain ctxt t t' \<sigma> D\<^sub>\<G> where
              "D\<^sub>\<G> \<in> N\<^sub>\<G>" and
              "D\<^sub>\<G> \<prec>\<^sub>c C\<^sub>\<G>" and
              "(t, t') \<in> equation N\<^sub>\<G> D\<^sub>\<G>" and
              "s = ctxt\<langle>t \<cdot>t \<sigma>\<rangle>"
              by (auto simp: rewrite_sys_def)
            hence "s = ctxt\<langle>t\<rangle>"
              by (simp only:
                  is_ground_cls_if_in_ground_cls_set[OF ground_N\<^sub>\<G>, of D\<^sub>\<G>]
                  is_ground_trm_if_mem_equation(1)[of D\<^sub>\<G> t t' N\<^sub>\<G>]
                  term_subst.subst_ident_if_ground[of t \<sigma>])

            obtain D\<^sub>\<G>' where
              D\<^sub>\<G>_def: "D\<^sub>\<G> = add_mset (Pos (t \<approx> t')) D\<^sub>\<G>'" and
              "select D\<^sub>\<G> = {#}" and
              max_t_t': "is_maximal_wrt (\<prec>\<^sub>l)\<^sup>=\<^sup>= (Pos (t \<approx> t')) D\<^sub>\<G>" and
              "t' \<prec>\<^sub>t t"
              using \<open>(t, t') \<in> equation N\<^sub>\<G> D\<^sub>\<G>\<close>
              apply (elim mem_equationE)
              by simp

            have ground_D\<^sub>\<G>: "is_ground_cls D\<^sub>\<G>"
              using \<open>D\<^sub>\<G> \<in> N\<^sub>\<G>\<close> ground_N\<^sub>\<G> is_ground_cls_if_in_ground_cls_set by blast

            define \<iota> :: "('f, char list) gterm uprod clause inference" where
              "\<iota> = Infer [gcls_cls D\<^sub>\<G>, gcls_cls C\<^sub>\<G>]
                (gcls_cls ((add_mset (Pos (ctxt\<langle>t'\<rangle> \<approx> s')) (C\<^sub>\<G>' + D\<^sub>\<G>'))))"

            have super: "pos_superposition C\<^sub>\<G> D\<^sub>\<G> (add_mset (Pos (ctxt\<langle>t'\<rangle> \<approx> s')) (C\<^sub>\<G>' + D\<^sub>\<G>'))"
            proof (rule pos_superpositionI)
              show "vars_cls (C\<^sub>\<G> \<cdot> Var) \<inter> vars_cls (D\<^sub>\<G> \<cdot> Var) = {}"
                using ground_D\<^sub>\<G> ground_C\<^sub>\<G> by simp
            next
              show "C\<^sub>\<G> = add_mset (Pos (s \<approx> s')) C\<^sub>\<G>'"
                by (simp add: C\<^sub>\<G>_eq A_def)
            next
              show "D\<^sub>\<G> = add_mset (Pos (t \<approx> t')) D\<^sub>\<G>'"
                by (simp add: D\<^sub>\<G>_def)
            next
              show "is_Fun t"
                using ground_D\<^sub>\<G>
                by (auto simp: D\<^sub>\<G>_def)
            next
              show "\<not> (C\<^sub>\<G> \<cdot> Var \<cdot> Var) \<preceq>\<^sub>c (D\<^sub>\<G> \<cdot> Var \<cdot> Var)"
                using \<open>D\<^sub>\<G> \<prec>\<^sub>c C\<^sub>\<G>\<close> asymp_less_cls
                by (metis asympD reflclp_iff subst_cls_Var_ident)
            next
              show "is_maximal_wrt (\<prec>\<^sub>l)\<^sup>=\<^sup>= (Pos (s \<approx> s') \<cdot>l Var \<cdot>l Var) (C\<^sub>\<G> \<cdot> Var \<cdot> Var)"
                using A_def strictly_maximal by simp
            next
              show "is_maximal_wrt (\<prec>\<^sub>l)\<^sup>=\<^sup>= (Pos (t \<approx> t') \<cdot>l Var \<cdot>l Var) (D\<^sub>\<G> \<cdot> Var \<cdot> Var)"
                using max_t_t'
                by (metis subst_cls_Var_ident subst_lit_Var_ident)
            next
              show "\<not> t \<cdot>t Var \<cdot>t Var \<preceq>\<^sub>t t' \<cdot>t Var \<cdot>t Var"
                using \<open>t' \<prec>\<^sub>t t\<close> asymp_less_trm
                by (metis (full_types) asympD subst_apply_term_empty sup2E)
            next
              show "Pos (s \<approx> s') = Pos (ctxt\<langle>t\<rangle> \<approx> s')"
                by (simp only: \<open>s = ctxt\<langle>t\<rangle>\<close>)
            next
              show "\<not> ctxt\<langle>t\<rangle> \<cdot>t Var \<cdot>t Var \<preceq>\<^sub>t s' \<cdot>t Var \<cdot>t Var"
                using \<open>s = ctxt\<langle>t\<rangle>\<close> \<open>s' \<prec>\<^sub>t s\<close>  asymp_less_trm
                by (metis (full_types) asympD subst_apply_term_empty sup2E)
            qed simp_all
            hence "\<iota> \<in> G_Inf"
              using ground_C\<^sub>\<G> ground_D\<^sub>\<G> superposition_if_pos_superposition
              by (auto simp: \<iota>_def G_Inf_def)

            moreover have "\<And>t. t \<in> set (prems_of \<iota>) \<Longrightarrow> t \<in> N"
              using \<open>C\<^sub>\<G> \<in> N\<^sub>\<G>\<close> \<open>D\<^sub>\<G> \<in> N\<^sub>\<G>\<close>
              by (auto simp add: \<iota>_def N\<^sub>\<G>_def)

            ultimately have "\<iota> \<in> G.Inf_from N"
              by (auto simp: G.Inf_from_def)
            hence "\<iota> \<in> G.Red_I N"
              using \<open>G.saturated N\<close>
              by (auto simp: G.saturated_def)
            then obtain DD where
              DD_subset: "DD \<subseteq> N" and
              "finite DD" and
              DD_entails_concl: "G_entails (insert (gcls_cls D\<^sub>\<G>) DD)
                {gcls_cls ((add_mset (Pos (ctxt\<langle>t'\<rangle> \<approx> s')) (C\<^sub>\<G>' + D\<^sub>\<G>')))}" and
              ball_DD_lt_C\<^sub>\<G>: "\<forall>D\<in>DD. cls_gcls D \<prec>\<^sub>c C\<^sub>\<G>"
              unfolding G.Red_I_def G.redundant_infer_def mem_Collect_eq
              using ground_C\<^sub>\<G>
              by (auto simp: \<iota>_def)

            moreover have "\<forall>D\<in> insert (gcls_cls D\<^sub>\<G>) DD. entails (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>) (cls_gcls D)"
              using IH[THEN conjunct2, THEN conjunct2, rule_format, of _ C\<^sub>\<G>]
              using N\<^sub>\<G>_def \<open>C\<^sub>\<G> \<in> N\<^sub>\<G>\<close> \<open>D\<^sub>\<G> \<in> N\<^sub>\<G>\<close> \<open>D\<^sub>\<G> \<prec>\<^sub>c C\<^sub>\<G>\<close> DD_subset ball_DD_lt_C\<^sub>\<G> ground_D\<^sub>\<G>
              by (metis imageI in_mono insert_iff local.gcls_cls_inverse)

            moreover have "is_ground_cls (add_mset (Pos (ctxt\<langle>t'\<rangle> \<approx> s')) (C\<^sub>\<G>' + D\<^sub>\<G>'))"
              using superposition_preserves_groundness
              using super ground_C\<^sub>\<G> ground_D\<^sub>\<G> by blast

            ultimately have "entails (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>) (add_mset (Pos (ctxt\<langle>t'\<rangle> \<approx> s')) (C\<^sub>\<G>' + D\<^sub>\<G>'))"
              using I_interp DD_entails_concl
              unfolding entails_def G_entails_def
              by (simp add: I_def true_clss_def)

            moreover have "\<not> entails (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>) D\<^sub>\<G>'"
              unfolding entails_def
              using false_cls_if_productive_equation(2)[OF ground_N\<^sub>\<G> _ \<open>C\<^sub>\<G> \<in> N\<^sub>\<G>\<close> \<open>D\<^sub>\<G> \<prec>\<^sub>c C\<^sub>\<G>\<close>]
              by (metis D\<^sub>\<G>_def \<open>(t, t') \<in> equation N\<^sub>\<G> D\<^sub>\<G>\<close> add_mset_remove_trivial empty_iff
                  equation_def ground_D\<^sub>\<G> production_eq_empty_or_singleton singletonD)

            ultimately have "entails (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>) {#Pos (ctxt\<langle>t'\<rangle> \<approx> s')#}"
              unfolding entails_def
              using \<open>\<not> (\<lambda>(x, y). x \<approx> y) ` (rstep (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>))\<^sup>\<down> \<TTurnstile> C\<^sub>\<G>'\<close>
              by fastforce

            moreover have "(ctxt\<langle>t\<rangle>, ctxt\<langle>t'\<rangle>) \<in> rstep (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>)"
              using \<open>(t, t') \<in> equation N\<^sub>\<G> D\<^sub>\<G>\<close> \<open>D\<^sub>\<G> \<in> N\<^sub>\<G>\<close> \<open>D\<^sub>\<G> \<prec>\<^sub>c C\<^sub>\<G>\<close> rewrite_sys_def by auto

            ultimately have "entails (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>) {#Pos (ctxt\<langle>t\<rangle> \<approx> s')#}"
              unfolding entails_def true_cls_def
              apply simp
              unfolding uprod_mem_image_iff_prod_mem[OF sym_join]
              by (meson r_into_rtrancl rtrancl_join_join)
            thus ?thesis
              using A_def C\<^sub>\<G>_eq \<open>s = ctxt\<langle>t\<rangle>\<close> entails_def by fastforce
          qed
        next
          case False
          then obtain C\<^sub>\<G>' where C\<^sub>\<G>_def: "C\<^sub>\<G> = add_mset (Pos A) (add_mset (Pos A) C\<^sub>\<G>')"
            using Pos_A_in max_Pos_A lift_is_maximal_wrt_to_is_maximal_wrt_reflclp
            by (metis insert_DiffM)

          define \<iota> :: "('f, char list) gterm uprod clause inference" where
            "\<iota> = Infer [gcls_cls C\<^sub>\<G>]
              (gcls_cls (add_mset (Pos (s \<approx> s')) (add_mset (Neg (s' \<approx> s')) C\<^sub>\<G>')))"

          have eq_fact: "eq_factoring C\<^sub>\<G> (add_mset (Pos (s \<approx> s')) (add_mset (Neg (s' \<approx> s')) C\<^sub>\<G>'))"
          proof (rule eq_factoringI)
            show "C\<^sub>\<G> = add_mset (Pos A) (add_mset (Pos A) C\<^sub>\<G>')"
              by (simp add: C\<^sub>\<G>_def)
          next
            show "Pos A = Pos (s \<approx> s')"
              by (simp add: A_def)
          next
            show "Pos A = Pos (s \<approx> s')"
              by (simp add: A_def)
          next
            show "select C\<^sub>\<G> = {#} \<and> is_maximal_lit (Pos A \<cdot>l Var) (C\<^sub>\<G> \<cdot> Var)"
              using \<open>select C\<^sub>\<G> = {#}\<close> max_Pos_A ground_C\<^sub>\<G> Pos_A_in by simp
          next
            show "\<not> s \<cdot>t Var \<preceq>\<^sub>t s' \<cdot>t Var"
              using \<open>s' \<prec>\<^sub>t s\<close> asymp_less_trm
              by (auto dest: asympD)
          qed simp_all
          hence "\<iota> \<in> G_Inf"
            using ground_C\<^sub>\<G>
            by (auto simp: \<iota>_def G_Inf_def)

          moreover have "\<And>t. t \<in> set (prems_of \<iota>) \<Longrightarrow> t \<in> N"
            using \<open>C\<^sub>\<G> \<in> N\<^sub>\<G>\<close>
            by (auto simp add: \<iota>_def N\<^sub>\<G>_def)

          ultimately have "\<iota> \<in> G.Inf_from N"
            by (auto simp: G.Inf_from_def)
          hence "\<iota> \<in> G.Red_I N"
            using \<open>G.saturated N\<close>
            by (auto simp: G.saturated_def)
          then obtain DD where
            DD_subset: "DD \<subseteq> N" and
            "finite DD" and
            DD_entails_concl: "G_entails DD {gcls_cls (add_mset (Pos (s \<approx> s')) (add_mset (Neg (s' \<approx> s')) C\<^sub>\<G>'))}" and
            ball_DD_lt_C\<^sub>\<G>: "\<forall>D\<in>DD. cls_gcls D \<prec>\<^sub>c C\<^sub>\<G>"
            unfolding G.Red_I_def G.redundant_infer_def mem_Collect_eq
            using ground_C\<^sub>\<G>
            by (auto simp: \<iota>_def)

          moreover have "\<forall>D\<in>DD. entails (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>) (cls_gcls D)"
            using IH[THEN conjunct2, THEN conjunct2, rule_format, of _ C\<^sub>\<G>]
            using N\<^sub>\<G>_def \<open>C\<^sub>\<G> \<in> N\<^sub>\<G>\<close> DD_subset ball_DD_lt_C\<^sub>\<G>
            by blast

          moreover have "is_ground_cls (add_mset (Pos (s \<approx> s')) (add_mset (Neg (s' \<approx> s')) C\<^sub>\<G>'))"
            using eq_factoring_preserves_groundness
            using eq_fact ground_C\<^sub>\<G> by blast

          ultimately have "entails (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>)
            (add_mset (Pos (s \<approx> s')) (add_mset (Neg (s' \<approx> s')) C\<^sub>\<G>'))"
            using I_interp DD_entails_concl
            unfolding entails_def G_entails_def
            by (simp add: I_def true_clss_def)
          then show ?thesis
            by (simp add: entails_def A_def C\<^sub>\<G>_def joinI_right pair_imageI)
        qed
      qed
    qed
  qed

  moreover have iia: "entails (\<Union> (equation N\<^sub>\<G> ` N\<^sub>\<G>)) C\<^sub>\<G>"
    using production_eq_empty_or_singleton[OF ground_C\<^sub>\<G>, of N\<^sub>\<G>, folded equation_def]
  proof (elim disjE exE)
    assume "equation N\<^sub>\<G> C\<^sub>\<G> = {}"
    hence "entails (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>) C\<^sub>\<G>"
      unfolding i by simp
    thus ?thesis
      using lift_entailment_to_Union(1)[OF ground_N\<^sub>\<G> \<open>C\<^sub>\<G> \<in> N\<^sub>\<G>\<close>]
      by (simp add: entails_def)
  next
    fix l r assume "equation N\<^sub>\<G> C\<^sub>\<G> = {(l, r)}"
    thus ?thesis
      using true_cls_if_productive_equation(1)[OF ground_N\<^sub>\<G> \<open>equation N\<^sub>\<G> C\<^sub>\<G> = {(l, r)}\<close>]
      by (simp add: entails_def)
  qed

  moreover have iib: "entails (rewrite_sys N\<^sub>\<G> D\<^sub>\<G>) C\<^sub>\<G>" if "D\<^sub>\<G> \<in> N\<^sub>\<G>" and "C\<^sub>\<G> \<prec>\<^sub>c D\<^sub>\<G>"
    using production_eq_empty_or_singleton[OF ground_C\<^sub>\<G>, of N\<^sub>\<G>, folded equation_def]
  proof (elim disjE exE)
    assume "equation N\<^sub>\<G> C\<^sub>\<G> = {}"
    hence "entails (rewrite_sys N\<^sub>\<G> C\<^sub>\<G>) C\<^sub>\<G>"
      unfolding i by simp
    thus ?thesis
      using lift_entailment_to_Union(2)[OF ground_N\<^sub>\<G> \<open>C\<^sub>\<G> \<in> N\<^sub>\<G>\<close> _ that]
      by (simp add: entails_def)
  next
    fix l r assume "equation N\<^sub>\<G> C\<^sub>\<G> = {(l, r)}"
    thus ?thesis
      using true_cls_if_productive_equation(2)[OF ground_N\<^sub>\<G> \<open>equation N\<^sub>\<G> C\<^sub>\<G> = {(l, r)}\<close> that]
      by (simp add: entails_def)
  qed

  ultimately show ?case
    by simp
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
      "I = (rstep (\<Union>D \<in> cls_gcls ` N. equation (cls_gcls ` N) D))\<^sup>\<down>"

    show "\<not> G_entails N G_Bot"
      unfolding G_entails_def not_all not_imp
    proof (intro exI conjI)
      show "refl I"
        by (simp only: I_def refl_join)
    next
      show "trans I"
        unfolding I_def
      proof (rule trans_join)
        have ground_model: "\<forall>rule \<in> (\<Union>D \<in> cls_gcls ` N. equation (cls_gcls ` N) D).
          is_ground_trm (fst rule) \<and> is_ground_trm (snd rule)"
          using ground_rule_if_mem_Union_equation[OF ground_N] by metis

        have "wf ((rewrite_inside_ctxt (\<Union>D \<in> cls_gcls ` N. equation (cls_gcls ` N) D))\<inverse>)"
        proof (rule wf_converse_rewrite_inside_ctxt)
          fix s t
          assume "(s, t) \<in> (\<Union>D \<in> cls_gcls ` N. equation (cls_gcls ` N) D)"
          then obtain C where "C \<in> cls_gcls ` N" "(s, t) \<in> equation (cls_gcls ` N) C"
            by auto
          thus "t \<prec>\<^sub>t s"
            by (auto elim: mem_equationE)
        qed auto
        thus "SN (rstep (\<Union>D \<in> cls_gcls ` N. equation (cls_gcls ` N) D))"
          unfolding rstep_eq_rewrite_inside_ctxt_if_ground[OF ground_model]
          using SN_iff_wf by metis
      next
        show "WCR (rstep (\<Union> (equation (cls_gcls ` N) ` cls_gcls ` N)))"
          using WCR_Union_rewrite_sys[OF ground_N] by metis
      qed
    next
      show "sym I"
        by (simp only: I_def sym_join)
    next
      show "compatible_with_ctxt I"
        by (simp only: I_def compatible_with_ctxt_join compatible_with_ctxt_rstep)
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

definition Prec_F :: "('f, string) gterm atom clause \<Rightarrow> ('f, string) term atom clause \<Rightarrow> ('f, string) term atom clause \<Rightarrow> bool" where
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