theory Superposition
  imports
    Main
    "Ordered_Resolution_Prover.Abstract_Substitution"
    "Saturation_Framework.Calculus"
    "Saturation_Framework.Lifting_to_Non_Ground_Calculi"
    "Saturation_Framework_Extensions.Clausal_Calculus"
    "First_Order_Terms.Term"
    "Knuth_Bendix_Order.Subterm_and_Context"

    (* Theories from this formalization *)
    "Multiset_Extra"
    "Abstract_Substitution_Extra_First_Order_Term"
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


lemma reflclp_iff: "\<And>R x y. R\<^sup>=\<^sup>= x y \<longleftrightarrow> R x y \<or> x = y"
  by (metis sup2CI sup2E)


section \<open>Abstract Substitutions\<close>

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
  morphisms term_gterm gterm_term
proof -
  have "is_ground_trm (Fun undefined [])"
    by simp
  thus "\<exists>x. x \<in> {t. is_ground_trm t}"
    by blast
qed


section \<open>Superposition Calculus\<close>

locale superposition_calculus =
  fixes
    less_trm :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" (infix "\<prec>\<^sub>t" 50) and
    select :: "('f, 'v) term atom clause \<Rightarrow> ('f, 'v) term atom clause"
  assumes
    transp_less_trm[simp]: "transp (\<prec>\<^sub>t)" and
    asymp_less_trm[simp]: "asymp (\<prec>\<^sub>t)" and
    wfP_less_trm[simp]: "wfP (\<prec>\<^sub>t)" and
    totalp_on_less_trm[simp]: "totalp_on {t. is_ground_trm t} (\<prec>\<^sub>t)" and
    select_negative_lits: "\<And>C L. L \<in># select C \<Longrightarrow> is_neg L" and
    select_stable_under_renaming: "\<And>C \<rho>. term_subst.is_renaming \<rho> \<Longrightarrow> select (C \<cdot> \<rho>) = select C \<cdot> \<rho>"
begin

lemma irreflp_less_trm[simp]: "irreflp (\<prec>\<^sub>t)"
  by simp

abbreviation lesseq_trm (infix "\<preceq>\<^sub>t" 50) where
  "lesseq_trm \<equiv> (\<prec>\<^sub>t)\<^sup>=\<^sup>="

abbreviation less_atm :: "('f, 'v) term atom \<Rightarrow> ('f, 'v) term atom \<Rightarrow> bool" (infix "\<prec>\<^sub>a" 50) where
  "less_atm A\<^sub>1 A\<^sub>2 \<equiv> multp (\<prec>\<^sub>t) (mset_uprod A\<^sub>1) (mset_uprod A\<^sub>2)"

abbreviation lesseq_atm (infix "\<preceq>\<^sub>a" 50) where
  "lesseq_atm \<equiv> (\<prec>\<^sub>a)\<^sup>=\<^sup>="

abbreviation less_lit :: "('f, 'v) term atom literal \<Rightarrow> ('f, 'v) term atom literal \<Rightarrow> bool" (infix "\<prec>\<^sub>l" 50) where
  "less_lit \<equiv> Clausal_Logic.less_lit (\<prec>\<^sub>a)"

abbreviation lesseq_lit (infix "\<preceq>\<^sub>l" 50) where
  "lesseq_lit \<equiv> (\<prec>\<^sub>l)\<^sup>=\<^sup>="

abbreviation less_cls :: "('f, 'v) term atom clause \<Rightarrow> ('f, 'v) term atom clause \<Rightarrow> bool" (infix "\<prec>\<^sub>c" 50) where
  "less_cls \<equiv> multp (\<prec>\<^sub>l)"

abbreviation lesseq_cls (infix "\<preceq>\<^sub>c" 50) where
  "lesseq_cls \<equiv> (\<prec>\<^sub>c)\<^sup>=\<^sup>="


lemma transp_less_atm[simp]: "transp (\<prec>\<^sub>a)"
  using transp_less_trm transp_multp
  by (metis (no_types, lifting) transpD transpI)

lemma transp_less_lit[simp]: "transp (\<prec>\<^sub>l)"
  by (simp add: transp_less_lit)

lemma transp_less_cls[simp]: "transp (\<prec>\<^sub>c)"
  by (simp add: transp_multp)

lemma totalp_on_less_atm[simp]: "totalp_on {A. is_ground_atm A} (\<prec>\<^sub>a)"
proof (rule totalp_onI, unfold mem_Collect_eq)
  fix A1 A2 :: "('f, 'v) Term.term uprod"
  assume "is_ground_atm A1" and "is_ground_atm A2" and "A1 \<noteq> A2"

  let ?GT = "{T. \<forall>t \<in># T. is_ground_trm t}"

  show "A1 \<prec>\<^sub>a A2 \<or> A2 \<prec>\<^sub>a A1"
  proof (rule totalp_on_multp[OF totalp_on_less_trm transp_less_trm, THEN totalp_onD])
    show "\<And>M. M \<in> ?GT \<Longrightarrow> set_mset M \<subseteq> {t. is_ground_trm t}"
      by auto
  next
    show "mset_uprod A1 \<in> ?GT"
      using \<open>is_ground_atm A1\<close>
      by (simp add: vars_atm_def set_uprod_def)
  next
    show "mset_uprod A2 \<in> ?GT"
      using \<open>is_ground_atm A2\<close>
      by (simp add: vars_atm_def set_uprod_def)
  next
    show "mset_uprod A1 \<noteq> mset_uprod A2"
      using \<open>A1 \<noteq> A2\<close>
      by (simp add: mset_uprod_inject)
  qed
qed

lemma totalp_on_less_lit[simp]: "totalp_on {L. is_ground_lit L} (\<prec>\<^sub>l)"
  using totalp_on_less_atm
  by (smt (verit, del_insts) Neg_atm_of_iff le_boolE less_lit_def linorder_not_less
      literal.collapse(1) mem_Collect_eq totalp_on_def vars_lit_def)

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

lemma mset_uprod_make_uprod[simp]: "mset_uprod (t\<^sub>1 \<approx> t\<^sub>2) = {#t\<^sub>1, t\<^sub>2#}"
  using Abs_uprod_inverse[of "{#t\<^sub>1, t\<^sub>2#}", simplified]
  by (simp add: make_uprod_def)

lemma make_uprod_eq_make_uprod_iff: "t\<^sub>1 \<approx> s\<^sub>1 = t\<^sub>2 \<approx> s\<^sub>2 \<longleftrightarrow> t\<^sub>1 = t\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2 \<or> t\<^sub>1 = s\<^sub>2 \<and> s\<^sub>1 = t\<^sub>2"
  by (metis add_mset_eq_single add_mset_remove_trivial diff_union_swap2 insert_noteq_member
      make_uprod_sym mset_uprod_make_uprod)

lemma multp_subset_supersetI: "multp (\<prec>\<^sub>t) A B \<Longrightarrow> C \<subseteq># A \<Longrightarrow> B \<subseteq># D \<Longrightarrow> multp (\<prec>\<^sub>t) C D"
  by (metis subset_implies_multp subset_mset.antisym_conv2 transpE transp_less_trm transp_multp)

lemma multp_plus_plusI:
  assumes "transp R" "multp R A B"
  shows "multp R (A + A) (B + B)"
  using multp_repeat_mset_repeat_msetI[OF \<open>transp R\<close> \<open>multp R A B\<close>, of 2]
  by (simp add: numeral_Bit0)

(* lemma
  defines "lift \<equiv> \<lambda>L t\<^sub>1 s\<^sub>1. if is_pos L then {#t\<^sub>1, s\<^sub>1#} else {#t\<^sub>1, t\<^sub>1, s\<^sub>1, s\<^sub>1#}"
  assumes "atm_of L\<^sub>1 = t\<^sub>1 \<approx> s\<^sub>1" and "atm_of L\<^sub>2 = t\<^sub>2 \<approx> s\<^sub>2"
  shows "L\<^sub>1 \<prec>\<^sub>l L\<^sub>2 \<longleftrightarrow> multp (\<prec>\<^sub>t) (lift L\<^sub>1 t\<^sub>1 s\<^sub>1) (lift L\<^sub>2 t\<^sub>2 s\<^sub>2)"
  unfolding lift_def
  using assms(2,3)
  apply (cases L\<^sub>1; cases L\<^sub>2)
  apply simp_all
  apply auto
  apply (erule transp_multp[THEN transpD, OF transp_less_trm, of "{#t\<^sub>1, s\<^sub>1#}" "{#t\<^sub>2, s\<^sub>2#}" "{#t\<^sub>2, t\<^sub>2, s\<^sub>2, s\<^sub>2#}"])
  apply (simp add: subset_implies_multp)
  unfolding make_uprod_eq_make_uprod_iff
  apply (auto intro: subset_implies_multp) []
  defer
  defer
  apply (auto elim: multp_subset_supersetI) []
  apply (drule multp_plus_plusI[OF transp_less_trm])
  apply (simp add: add_mset_commute)
  defer
  apply simp
  sledgehammer *)
  
  


section \<open>Rules\<close>

abbreviation is_maximal_lit where
  "is_maximal_lit \<equiv> is_maximal_wrt (\<prec>\<^sub>l)"

abbreviation is_strictly_maximal_lit where
  "is_strictly_maximal_lit \<equiv> is_maximal_wrt (\<preceq>\<^sub>l)"

inductive superposition ::
  "('f, 'v) term atom clause \<Rightarrow> ('f, 'v) term atom clause \<Rightarrow> ('f, 'v) term atom clause \<Rightarrow> bool"
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
    select P\<^sub>1 = {#} \<and> is_strictly_maximal_lit (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>) \<or> L\<^sub>1 \<in># select P\<^sub>1 \<Longrightarrow>
    select P\<^sub>2 = {#} \<and> is_strictly_maximal_lit (L\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu>) (P\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    \<not> (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu>) \<Longrightarrow>
    \<not> (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<preceq>\<^sub>t t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu>) \<Longrightarrow>
    C = add_mset (\<P> ((s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2 \<cdot>t \<rho>\<^sub>2\<rangle> \<approx> s\<^sub>1' \<cdot>t \<rho>\<^sub>1)) (P\<^sub>1' \<cdot> \<rho>\<^sub>1 + P\<^sub>2' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu> \<Longrightarrow>
    superposition P\<^sub>1 P\<^sub>2 C"

inductive eq_resolution :: "('f, 'v) term atom clause \<Rightarrow> ('f, 'v) term atom clause \<Rightarrow> bool" where
  eq_resolutionI: "
    P = add_mset L P' \<Longrightarrow>
    L = Neg (s\<^sub>1 \<approx> s\<^sub>2) \<Longrightarrow>
    term_subst.is_imgu \<mu> {{s\<^sub>1, s\<^sub>2}} \<Longrightarrow>
    select P = {#} \<and> is_maximal_lit (L \<cdot>l \<mu>) (P \<cdot> \<mu>) \<or> L \<in># select P \<Longrightarrow>
    C = P' \<cdot> \<mu> \<Longrightarrow>
    eq_resolution P C"

inductive eq_factoring :: "('f, 'v) term atom clause \<Rightarrow> ('f, 'v) term atom clause \<Rightarrow> bool" where
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


section \<open>Ground Layer\<close>

definition gcls_cls where
  "gcls_cls \<equiv> map_clause (map_uprod gterm_term)"

definition cls_gcls where
  "cls_gcls \<equiv> map_clause (map_uprod term_gterm)"

lemma cls_gcls_empty_mset[simp]: "cls_gcls {#} = {#}"
  by (simp add: cls_gcls_def)

lemma cls_gcls_inverse[simp]: "gcls_cls (cls_gcls C) = C"
  unfolding gcls_cls_def cls_gcls_def
  by (simp add: multiset.map_comp literal.map_comp uprod.map_comp comp_def
      literal.map_ident_strong term_gterm_inverse uprod.map_ident_strong)

lemma is_ground_cls_gcls[simp]: "is_ground_cls (cls_gcls C)"
  unfolding cls_gcls_def
  apply (simp add: vars_cls_def vars_lit_def vars_atm_def)
  by (smt (verit) imageE literal.map_sel(1) literal.map_sel(2) mem_Collect_eq term_gterm
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
      intro!: multiset.map_ident_strong literal.map_ident_strong uprod.map_ident_strong gterm_term_inverse)

definition G_Inf :: "('f, 'v) gterm atom clause inference set" where
  "G_Inf \<equiv>
    {Infer [P\<^sub>2, P\<^sub>1] (gcls_cls C) | P\<^sub>2 P\<^sub>1 C. superposition (cls_gcls P\<^sub>1) (cls_gcls P\<^sub>2) C} \<union>
    {Infer [P] (gcls_cls C) | P C. eq_resolution (cls_gcls P) C} \<union>
    {Infer [P] (gcls_cls C) | P C. eq_factoring (cls_gcls P) C}"

abbreviation G_Bot :: "('f, 'v) gterm atom clause set" where
  "G_Bot \<equiv> {{#}}"

definition compatible_with_Fun :: "(('f, 'v) Term.term \<times> ('f, 'v) Term.term) set \<Rightarrow> bool" where
  "compatible_with_Fun I \<longleftrightarrow>
    (\<forall>f ts ts'. list_all2 (\<lambda>t t'. (t, t') \<in> I) ts ts' \<longrightarrow> (Fun f ts, Fun f ts') \<in> I)"

definition G_entails ::
  "('f, 'v) gterm atom clause set \<Rightarrow> ('f, 'v) gterm atom clause set \<Rightarrow> bool"
where
  "G_entails N\<^sub>1 N\<^sub>2 \<longleftrightarrow> (\<forall>(I :: (('f, 'v) Term.term \<times> ('f, 'v) Term.term) set).
    refl I \<longrightarrow> trans I \<longrightarrow> sym I \<longrightarrow> compatible_with_Fun I \<longrightarrow>
    (\<lambda>(t\<^sub>1, t\<^sub>2). t\<^sub>1 \<approx> t\<^sub>2) ` I \<TTurnstile>s (cls_gcls ` N\<^sub>1) \<longrightarrow>
    (\<lambda>(t\<^sub>1, t\<^sub>2). t\<^sub>1 \<approx> t\<^sub>2) ` I \<TTurnstile>s (cls_gcls ` N\<^sub>2))"


subsection \<open>Correctness\<close>

lemma true_lit_uprod_iff_true_lit_prod[simp]:
  assumes "sym I"
  shows
    "(\<lambda>(t\<^sub>1, t\<^sub>2). t\<^sub>1 \<approx> t\<^sub>2) ` I \<TTurnstile>l Pos (t \<approx> t') \<longleftrightarrow> I \<TTurnstile>l Pos (t, t')"
    "(\<lambda>(t\<^sub>1, t\<^sub>2). t\<^sub>1 \<approx> t\<^sub>2) ` I \<TTurnstile>l Neg (t \<approx> t') \<longleftrightarrow> I \<TTurnstile>l Neg (t, t')"
  unfolding true_lit_simps atomize_conj
  using \<open>sym I\<close>[THEN symD]
  by (smt (z3) case_prod_unfold image_iff make_uprod_eq_make_uprod_iff pair_imageI prod.collapse)

lemma correctness_ground_superposition:
  assumes step: "superposition P1 P2 C" and ground_P1: "is_ground_cls P1" and ground_P2: "is_ground_cls P2"
  shows "G_entails {gcls_cls P1, gcls_cls P2} {gcls_cls C}"
  using step
proof (cases P1 P2 C rule: superposition.cases)
  case (superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' \<P> s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)
  with ground_P1 ground_P2 have "is_ground_atm (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<approx> s\<^sub>1')" and "is_ground_atm (t\<^sub>2 \<approx> t\<^sub>2')"
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
    fix I :: "(('f, 'v) Term.term \<times> ('f, 'v) Term.term) set"

    let ?I' = "(\<lambda>(t\<^sub>1, t\<^sub>2). t\<^sub>1 \<approx> t\<^sub>2) ` I"

    assume "refl I" and "trans I" and "sym I" and "compatible_with_Fun I" and
      "?I' \<TTurnstile> P1" and "?I' \<TTurnstile> P2"
    then obtain K1 K2 :: "('f, 'v) Term.term uprod literal" where
      "K1 \<in># P1" and "?I' \<TTurnstile>l K1" and "K2 \<in># P2" and "?I' \<TTurnstile>l K2"
      by (auto simp: true_cls_def)

    show "?I' \<TTurnstile> C"
    proof (cases "K1 = \<P> (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<approx> s\<^sub>1')")
      case True
      then show ?thesis
        using ground_P1 ground_P2 \<open>?I' \<TTurnstile>l K1\<close>
        unfolding superpositionI \<open>u\<^sub>1 = t\<^sub>2\<close>
        using \<open>is_ground_trm_ctxt s\<^sub>1\<close> \<open>is_ground_trm s\<^sub>1'\<close> \<open>is_ground_trm t\<^sub>2\<close> by auto
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
    fix I :: "(('f, 'v) Term.term \<times> ('f, 'v) Term.term) set"

    let ?I' = "(\<lambda>(t\<^sub>1, t\<^sub>2). t\<^sub>1 \<approx> t\<^sub>2) ` I"

    assume "trans I" and "sym I" and "?I' \<TTurnstile> P"
    then obtain K :: "('f, 'v) Term.term uprod literal" where
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
    assume "refl I" and "trans I" and "sym I" and "compatible_with_Fun I" and
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
  hence "(t\<^sub>2 \<approx> t\<^sub>2') \<preceq>\<^sub>a (s\<^sub>1 \<approx> s\<^sub>1')"
    using totalp_on_less_atm[THEN totalp_onD, unfolded mem_Collect_eq,
        OF \<open>is_ground_atm (s\<^sub>1 \<approx> s\<^sub>1')\<close> \<open>is_ground_atm (t\<^sub>2 \<approx> t\<^sub>2')\<close>]
    by force
  hence "t\<^sub>2' \<preceq>\<^sub>t s\<^sub>1'"
    unfolding \<open>s\<^sub>1 = t\<^sub>2\<close>
    unfolding reflclp_iff
    apply (simp add: make_uprod_eq_make_uprod_sym_iff)
    apply safe
    unfolding multp_cancel_add_mset[OF transp_less_trm
        irreflp_on_subset[OF irreflp_less_trm subset_UNIV]]
    by (smt (verit, del_insts) multp_implies_one_step set_mset_add_mset_insert set_mset_empty
        single_is_union singletonD transp_less_trm union_single_eq_member)

  from eq_factoringI have "C = add_mset (Pos (s\<^sub>1 \<approx> t\<^sub>2')) (add_mset (Neg (s\<^sub>1' \<approx> t\<^sub>2')) P')"
    using ground_P by auto

  moreover have "add_mset (Neg (s\<^sub>1' \<approx> t\<^sub>2')) (add_mset (Pos (s\<^sub>1 \<approx> t\<^sub>2')) P') \<prec>\<^sub>c P"
    unfolding eq_factoringI \<open>s\<^sub>1 = t\<^sub>2\<close>
  proof (intro one_step_implies_multp[of "{#_#}" "{#_#}", simplified])
    have "t\<^sub>2' \<prec>\<^sub>t t\<^sub>2"
      using \<open>s\<^sub>1' \<prec>\<^sub>t t\<^sub>2\<close> \<open>t\<^sub>2' \<preceq>\<^sub>t s\<^sub>1'\<close>
      by (metis reflclp_iff transpD transp_less_trm)
    thus "Neg (s\<^sub>1' \<approx> t\<^sub>2') \<prec>\<^sub>l Pos (t\<^sub>2 \<approx> s\<^sub>1')"
      apply simp
      by (smt (verit) add_mset_add_single add_mset_commute multi_self_add_other_not_self
          one_step_implies_multp set_mset_add_mset_insert set_mset_empty singletonD
          union_single_eq_member)
  qed

  ultimately show ?thesis
    unfolding eq_factoringI
    by (simp add: add_mset_commute)
qed

interpretation G: calculus_with_finitary_standard_redundancy G_Inf G_Bot G_entails
  "\<lambda>C\<^sub>1 C\<^sub>2. cls_gcls C\<^sub>1 \<prec>\<^sub>c cls_gcls C\<^sub>2"
proof unfold_locales
  show "transp (\<lambda>C\<^sub>1 C\<^sub>2. cls_gcls C\<^sub>1 \<prec>\<^sub>c cls_gcls C\<^sub>2)"
    using transp_less_cls
    by (metis (no_types, lifting) transpD transpI)
next
  have "wfP (\<prec>\<^sub>a)"
    using wfP_less_trm wfP_multp
    by (metis (no_types, lifting) wfP_if_convertible_to_wfP)
  hence "wfP (\<prec>\<^sub>l)"
    using wfP_less_lit by blast
  hence "wfP (\<prec>\<^sub>c)"
    using wfP_multp by blast
  thus "wfP (\<lambda>C\<^sub>1 C\<^sub>2. cls_gcls C\<^sub>1 \<prec>\<^sub>c cls_gcls C\<^sub>2)"
    by (metis (no_types, lifting) wfP_if_convertible_to_wfP)
next
  show "\<And>\<iota>. \<iota> \<in> G_Inf \<Longrightarrow> prems_of \<iota> \<noteq> []"
    by (auto simp: G_Inf_def)
next
  show "\<And>\<iota>. \<iota> \<in> G_Inf \<Longrightarrow> cls_gcls (concl_of \<iota>) \<prec>\<^sub>c cls_gcls (main_prem_of \<iota>)"
    sorry
qed

interpretation G: statically_complete_calculus G_Bot G_Inf G_entails G.Red_I G.Red_F
proof unfold_locales
  show "\<And>B N. B \<in> G_Bot \<Longrightarrow> G.saturated N \<Longrightarrow> G_entails N {B} \<Longrightarrow> \<exists>B'\<in>G_Bot. B' \<in> N"
    sorry
qed


section \<open>First-Order Layer\<close>


abbreviation F_Inf :: "('f, 'v) term atom clause inference set" where
  "F_Inf \<equiv> {}"

abbreviation F_Bot :: "('f, 'v) term atom clause set" where
  "F_Bot \<equiv> {{#}}"

abbreviation F_entails :: "('f, 'v) term atom clause set \<Rightarrow> ('f, 'v) term atom clause set \<Rightarrow> bool" where
  "F_entails \<equiv> (\<TTurnstile>e)"

typedecl Q

definition \<G>_F :: "Q \<Rightarrow> ('f, 'v) term atom clause \<Rightarrow> ('f, 'v) term atom clause set" where
  "\<G>_F \<equiv> \<lambda>_ _. {}"

definition \<G>_I :: "Q \<Rightarrow> ('f, 'v) term atom clause inference \<Rightarrow> ('f, 'v) term atom clause inference set option" where
  "\<G>_I \<equiv> \<lambda>_ _. None"

definition Prec_F :: "('f, 'v) term atom clause \<Rightarrow> ('f, 'v) term atom clause \<Rightarrow> ('f, 'v) term atom clause \<Rightarrow> bool" where
  "Prec_F \<equiv> \<lambda>_ _ _. False"

interpretation F: lifting_intersection F_Inf G_Bot "UNIV :: Q set" "\<lambda>(_ :: Q). G_Inf"
  "\<lambda>(_ :: Q). G_entails" "\<lambda>(_ :: Q). G.Red_I" "\<lambda>(_ :: Q). G.Red_F" F_Bot \<G>_F \<G>_I Prec_F
proof unfold_locales
  show "UNIV \<noteq> {}"
    by simp
next
  show "\<forall>q\<in>UNIV. consequence_relation F_Bot F_entails"
    sorry
next
  show "\<forall>q\<in>UNIV. tiebreaker_lifting F_Bot F_Inf F_Bot F_entails F_Inf G.Red_I G.Red_F (\<G>_F q)
    (\<G>_I q) Prec_F"
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