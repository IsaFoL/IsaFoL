theory First_Order_Superposition
  imports
    First_Order_Terms.Term
    First_Order_Terms.Subterm_and_Context
    Saturation_Framework.Lifting_to_Non_Ground_Calculi

    Ground_Superposition
    Abstract_Substitution_Extra_First_Order_Term
begin

no_notation subst_compose (infixl "\<circ>\<^sub>s" 75)
no_notation subst_apply_term (infixl "\<cdot>" 67)

text \<open>Prefer @{thm [source] term_subst.subst_id_subst} to @{thm [source] subst_apply_term_empty}.\<close>
declare subst_apply_term_empty[no_atp]

section \<open>First_Order_Terms And Abstract_Substitution\<close>

notation subst_apply_term (infixl "\<cdot>t" 67)
notation subst_apply_ctxt (infixl "\<cdot>t\<^sub>c" 67)
notation subst_compose (infixl "\<odot>" 75)

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

definition lit_glit where
  "lit_glit = map_literal (map_uprod term_of_gterm)"

definition glit_lit where
  "glit_lit = map_literal (map_uprod gterm_of_term)"

definition gcls_cls where
  "gcls_cls \<equiv> image_mset glit_lit"

definition cls_gcls where
  "cls_gcls \<equiv> image_mset lit_glit"

lemma cls_gcls_empty_mset[simp]: "cls_gcls {#} = {#}"
  by (simp add: cls_gcls_def)

lemma gterm_of_term_ident_if_ground:
  "is_ground_trm t \<Longrightarrow> term_of_gterm (gterm_of_term t) = t"
  by (induct t) (auto intro: nth_equalityI)

lemma lit_glit_inverse[simp]: "glit_lit (lit_glit L) = L"
  unfolding lit_glit_def glit_lit_def
  by (simp add: literal.map_comp uprod.map_comp comp_def gterm_of_term_ident_if_ground literal.map_ident_strong
      uprod.map_ident_strong)

lemma cls_gcls_inverse[simp]: "gcls_cls (cls_gcls C) = C"
  unfolding gcls_cls_def cls_gcls_def
  by simp

lemma vars_lit_glit[simp]: "vars_lit (lit_glit L) = {}"
  unfolding lit_glit_def vars_lit_def
  by (smt (verit, ccfv_SIG) empty_iff equals0I imageE literal.map_sel(1) literal.map_sel(2)
      mem_simps(9) uprod.set_map vars_atm_def vars_term_of_gterm)

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
      intro!: literal.map_ident_strong uprod.map_ident_strong gterm_of_term_ident_if_ground)

lemma gcls_cls_inverse[simp]: "is_ground_cls C \<Longrightarrow> cls_gcls (gcls_cls C) = C"
  unfolding cls_gcls_def gcls_cls_def
  by (simp add: multiset.map_comp comp_def multiset.map_ident_strong is_ground_lit_if_in_ground_cls)

lemma is_ground_cls_gcls: "is_ground_cls (cls_gcls C)"
  by simp


section \<open>First-Order Layer\<close>

context
  fixes
    less_trm :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" (infix "\<prec>\<^sub>t" 50) and
    select :: "('f, 'v) term atom clause \<Rightarrow> ('f, 'v) term atom clause"
begin

text \<open>TODO: replace fixed @{term less_trm} and @{term ground_select} by actual definitions.\<close>

abbreviation lesseq_trm (infix "\<preceq>\<^sub>t" 50) where
  "lesseq_trm \<equiv> (\<prec>\<^sub>t)\<^sup>=\<^sup>="

definition less_lit ::
  "('f, 'v) term atom literal \<Rightarrow> ('f, 'v) term atom literal \<Rightarrow> bool" (infix "\<prec>\<^sub>l" 50) where
  "less_lit L1 L2 \<equiv> multp (\<prec>\<^sub>t) (mset_lit L1) (mset_lit L2)"

abbreviation lesseq_lit (infix "\<preceq>\<^sub>l" 50) where
  "lesseq_lit \<equiv> (\<prec>\<^sub>l)\<^sup>=\<^sup>="

abbreviation less_cls ::
  "('f, 'v) term atom clause \<Rightarrow> ('f, 'v) term atom clause \<Rightarrow> bool" (infix "\<prec>\<^sub>c" 50) where
  "less_cls \<equiv> multp (\<prec>\<^sub>l)"

abbreviation lesseq_cls (infix "\<preceq>\<^sub>c" 50) where
  "lesseq_cls \<equiv> (\<prec>\<^sub>c)\<^sup>=\<^sup>="

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
    (\<P> = Pos \<and> select P\<^sub>1 = {#} \<and> is_strictly_maximal_lit (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>)) \<or>
    (\<P> = Neg \<and> (select P\<^sub>1 = {#} \<and> is_maximal_lit (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>) \<or> L\<^sub>1 \<in># select P\<^sub>1)) \<Longrightarrow>
    select P\<^sub>2 = {#} \<Longrightarrow>
    is_strictly_maximal_lit (L\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu>) (P\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    \<not> (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu>) \<Longrightarrow>
    \<not> (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<preceq>\<^sub>t t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu>) \<Longrightarrow>
    C = add_mset (\<P> ((s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> \<approx> s\<^sub>1' \<cdot>t \<rho>\<^sub>1)) (P\<^sub>1' \<cdot> \<rho>\<^sub>1 + P\<^sub>2' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu> \<Longrightarrow>
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

(* lemma superposition_iff_ground_superposition:
  assumes ground_P1: "is_ground_cls P1" and ground_P2: "is_ground_cls P2"
  shows "superposition P1 P2 C \<longleftrightarrow> ground_superposition P1 P2 C"
proof (rule iffI)
  assume "superposition P1 P2 C"
  thus "ground_superposition P1 P2 C"
  proof (cases P1 P2 C rule: superposition.cases)
    case (superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' \<P> s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)
    from ground_P1 ground_P2 have
      "is_ground_lit L\<^sub>1" and "is_ground_cls P\<^sub>1'" and
      "is_ground_lit L\<^sub>2" and "is_ground_cls P\<^sub>2'"
      using \<open>P1 = add_mset L\<^sub>1 P\<^sub>1'\<close> \<open>P2 = add_mset L\<^sub>2 P\<^sub>2'\<close> by simp_all
    hence
      "is_ground_atm (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<approx> s\<^sub>1')" and
      "is_ground_atm (t\<^sub>2 \<approx> t\<^sub>2')"
      using \<open>\<P> \<in> {Pos, Neg}\<close> \<open>L\<^sub>1 = \<P> (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<approx> s\<^sub>1')\<close> \<open>L\<^sub>2 = Pos (t\<^sub>2 \<approx> t\<^sub>2')\<close> by auto
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

    show ?thesis
    proof (rule ground_superpositionI)
      show "P1 = add_mset L\<^sub>1 P\<^sub>1'"
        using \<open>P1 = add_mset L\<^sub>1 P\<^sub>1'\<close> .
    next
      show "P2 = add_mset L\<^sub>2 P\<^sub>2'"
        using \<open>P2 = add_mset L\<^sub>2 P\<^sub>2'\<close> .
    next
      show "\<P> \<in> {Pos, Neg}"
        using \<open>\<P> \<in> {Pos, Neg}\<close> .
    next
      show "L\<^sub>1 = \<P> (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<approx> s\<^sub>1')"
        using \<open>L\<^sub>1 = \<P> (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<approx> s\<^sub>1')\<close> .
    next
      show "L\<^sub>2 = Pos (u\<^sub>1 \<approx> t\<^sub>2')"
        using \<open>L\<^sub>2 = Pos (t\<^sub>2 \<approx> t\<^sub>2')\<close> \<open>u\<^sub>1 = t\<^sub>2\<close> by argo
    next
      from ground_P1 ground_P2 have "\<not> (P1 \<preceq>\<^sub>c P2)"
        using \<open>\<not> (P1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<preceq>\<^sub>c P2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>)\<close> by simp
      with ground_P1 ground_P2 show "P2 \<prec>\<^sub>c P1"
        by (metis (mono_tags, lifting) mem_Collect_eq reflclp_iff totalp_on_def totalp_on_less_cls)
    next
      from ground_P1 show "\<P> = Pos \<and> select P1 = {#} \<and> is_maximal_wrt (\<prec>\<^sub>l)\<^sup>=\<^sup>= L\<^sub>1 P1 \<or>
        \<P> = Neg \<and> (select P1 = {#} \<and> is_maximal_lit L\<^sub>1 P1 \<or> L\<^sub>1 \<in># select P1)"
        using \<open>\<P> = Pos \<and> select P1 = {#} \<and> is_maximal_wrt (\<prec>\<^sub>l)\<^sup>=\<^sup>= (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (P1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>) \<or>
          \<P> = Neg \<and> (select P1 = {#} \<and> is_maximal_lit (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (P1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>) \<or>
            L\<^sub>1 \<in># select P1)\<close>
        using \<open>is_ground_lit L\<^sub>1\<close> by simp
    next
      show "select P2 = {#}"
        using \<open>select P2 = {#}\<close> .
    next
      from ground_P2 show "is_maximal_wrt (\<prec>\<^sub>l)\<^sup>=\<^sup>= L\<^sub>2 P2"
        using \<open>is_maximal_wrt (\<prec>\<^sub>l)\<^sup>=\<^sup>= (L\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu>) (P2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>)\<close> \<open>is_ground_lit L\<^sub>2\<close> by simp
    next
      have "\<not> s\<^sub>1\<langle>u\<^sub>1\<rangle> \<preceq>\<^sub>t s\<^sub>1'"
        using \<open>is_ground_trm s\<^sub>1\<langle>u\<^sub>1\<rangle>\<close> \<open>is_ground_trm s\<^sub>1'\<close> \<open>\<not> s\<^sub>1\<langle>u\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu>\<close> by simp
      thus "s\<^sub>1' \<prec>\<^sub>t s\<^sub>1\<langle>u\<^sub>1\<rangle>"
        using \<open>is_ground_trm s\<^sub>1\<langle>u\<^sub>1\<rangle>\<close> \<open>is_ground_trm s\<^sub>1'\<close> totalp_less_trm
        by (metis (mono_tags, lifting) mem_Collect_eq sup2CI totalp_onD)
    next
      have "\<not> t\<^sub>2 \<preceq>\<^sub>t t\<^sub>2'"
        using \<open>is_ground_trm t\<^sub>2\<close> \<open>is_ground_trm t\<^sub>2'\<close> \<open>\<not> t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<preceq>\<^sub>t t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu>\<close> by simp
      thus "t\<^sub>2' \<prec>\<^sub>t u\<^sub>1"
        using \<open>is_ground_trm t\<^sub>2\<close> \<open>is_ground_trm t\<^sub>2'\<close> \<open>u\<^sub>1 = t\<^sub>2\<close> totalp_less_trm
        by (metis (mono_tags, lifting) CollectI reflclp_iff totalp_onD)
    next
      show "C = add_mset (\<P> (s\<^sub>1\<langle>t\<^sub>2'\<rangle> \<approx> s\<^sub>1')) (P\<^sub>1' + P\<^sub>2')"
        using \<open>C = add_mset (\<P> ((s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> \<approx> s\<^sub>1' \<cdot>t \<rho>\<^sub>1)) (P\<^sub>1' \<cdot> \<rho>\<^sub>1 + P\<^sub>2' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu>\<close>
          \<open>is_ground_trm_ctxt s\<^sub>1\<close> \<open>is_ground_trm t\<^sub>2'\<close> \<open>is_ground_trm s\<^sub>1'\<close> \<open>is_ground_cls P\<^sub>1'\<close>
          \<open>is_ground_cls P\<^sub>2'\<close> \<open>\<P> \<in> {Pos, Neg}\<close>
        by auto
    qed
  qed
next
  assume "ground_superposition P1 P2 C"
  thus "superposition P1 P2 C"
  proof (cases P1 P2 C rule: ground_superposition.cases)
    case (ground_superpositionI L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' \<P> s t s' t')
    with ground_P2 have "is_ground_trm t"
      by force
    show ?thesis
    proof (rule superpositionI)
      from ground_P1 ground_P2 show "vars_cls (P1 \<cdot> Var) \<inter> vars_cls (P2 \<cdot> Var) = {}"
        by simp
    next
      show "P1 = add_mset L\<^sub>1 P\<^sub>1'"
        using \<open>P1 = add_mset L\<^sub>1 P\<^sub>1'\<close> .
    next
      show "P2 = add_mset L\<^sub>2 P\<^sub>2'"
        using \<open>P2 = add_mset L\<^sub>2 P\<^sub>2'\<close> .
    next
      show "\<P> \<in> {Pos, Neg}"
        using \<open>\<P> \<in> {Pos, Neg}\<close> .
    next
      show "L\<^sub>1 = \<P> (s\<langle>t\<rangle> \<approx> s')"
        using \<open>L\<^sub>1 = \<P> (s\<langle>t\<rangle> \<approx> s')\<close> .
    next
      show "L\<^sub>2 = Pos (t \<approx> t')"
        using \<open>L\<^sub>2 = Pos (t \<approx> t')\<close> .
    next
      show "is_Fun t"
        using \<open>is_ground_trm t\<close> by auto
    next
      show "\<not> (P1 \<cdot> Var \<cdot> Var \<preceq>\<^sub>c P2 \<cdot> Var \<cdot> Var)"
        using \<open>P2 \<prec>\<^sub>c P1\<close>
        by (metis asympD asymp_less_cls strict_reflclp_conv subst_cls_Var_ident)
    next
      show "\<P> = Pos \<and> select P1 = {#} \<and> is_maximal_wrt (\<prec>\<^sub>l)\<^sup>=\<^sup>= (L\<^sub>1 \<cdot>l Var \<cdot>l Var) (P1 \<cdot> Var \<cdot> Var) \<or>
        \<P> = Neg \<and> (select P1 = {#} \<and> is_maximal_lit (L\<^sub>1 \<cdot>l Var \<cdot>l Var) (P1 \<cdot> Var \<cdot> Var) \<or>
          L\<^sub>1 \<in># select P1)"
        using \<open>\<P> = Pos \<and> select P1 = {#} \<and> is_maximal_wrt (\<prec>\<^sub>l)\<^sup>=\<^sup>= L\<^sub>1 P1 \<or>
          \<P> = Neg \<and> (select P1 = {#} \<and> is_maximal_lit L\<^sub>1 P1 \<or> L\<^sub>1 \<in># select P1)\<close>
        by simp
    next
      show "select P2 = {#}"
        using \<open>select P2 = {#}\<close> .
    next
      show "is_maximal_wrt (\<prec>\<^sub>l)\<^sup>=\<^sup>= (L\<^sub>2 \<cdot>l Var \<cdot>l Var) (P2 \<cdot> Var \<cdot> Var)"
        using \<open>is_maximal_wrt (\<prec>\<^sub>l)\<^sup>=\<^sup>= L\<^sub>2 P2\<close> by simp
    next
      show "\<not> s\<langle>t\<rangle> \<cdot>t Var \<cdot>t Var \<preceq>\<^sub>t s' \<cdot>t Var \<cdot>t Var"
        using \<open>s' \<prec>\<^sub>t s\<langle>t\<rangle>\<close>
        by (metis asympD asymp_less_trm strict_reflclp_conv term_subst.subst_id_subst)
    next
      show "\<not> t \<cdot>t Var \<cdot>t Var \<preceq>\<^sub>t t' \<cdot>t Var \<cdot>t Var"
        using \<open>t' \<prec>\<^sub>t t\<close>
        by (metis asympD asymp_less_trm strict_reflclp_conv term_subst.subst_id_subst)
    next
      show "C = add_mset (\<P> ((s \<cdot>t\<^sub>c Var)\<langle>t' \<cdot>t Var\<rangle> \<approx> s' \<cdot>t Var)) (P\<^sub>1' \<cdot> Var + P\<^sub>2' \<cdot> Var) \<cdot> Var"
        using \<open>C = add_mset (\<P> (s\<langle>t'\<rangle> \<approx> s')) (P\<^sub>1' + P\<^sub>2')\<close> by simp
    qed simp_all
  qed
qed

lemma eq_resolution_iff_ground_eq_resolution:
  assumes ground_P: "is_ground_cls P"
  shows "eq_resolution P C \<longleftrightarrow> ground_eq_resolution P C"
proof (rule iffI)
  assume "eq_resolution P C"
  thus "ground_eq_resolution P C"
  proof (cases P C rule: eq_resolution.cases)
    case (eq_resolutionI L P' t\<^sub>1 t\<^sub>2 \<mu>)
    with ground_P have "is_ground_lit L" and "is_ground_cls P'"
      by simp_all
    hence "is_ground_atm (t\<^sub>1 \<approx> t\<^sub>2)"
      using \<open>L = Neg (t\<^sub>1 \<approx> t\<^sub>2)\<close> by simp
    hence "is_ground_trm t\<^sub>1" and "is_ground_trm t\<^sub>2"
      by simp_all
    hence "term_subst.is_ground_set {t\<^sub>1, t\<^sub>2}"
      by (simp add: term_subst.is_ground_set_def)
    moreover from \<open>term_subst.is_imgu \<mu> {{t\<^sub>1, t\<^sub>2}}\<close> have "term_subst.is_unifier \<mu> {t\<^sub>1, t\<^sub>2}"
      by (simp add: term_subst.is_imgu_def term_subst.is_unifiers_def)
    ultimately have "t\<^sub>1 = t\<^sub>2"
      using term_subst.ball_eq_constant_if_unifier[of "{t\<^sub>1, t\<^sub>2}" _ \<mu>] by simp

    have "P' = C"
      using \<open>C = P' \<cdot> \<mu>\<close>
      by (simp add: \<open>is_ground_cls P'\<close>)

    show ?thesis
    proof (rule ground_eq_resolutionI)
      show "P = add_mset L C"
        using \<open>P = add_mset L P'\<close> \<open>P' = C\<close> by argo
    next
      show "L = Neg (t\<^sub>1 \<approx> t\<^sub>1)"
        using \<open>L = Neg (t\<^sub>1 \<approx> t\<^sub>2)\<close> \<open>t\<^sub>1 = t\<^sub>2\<close> by argo
    next
      from ground_P show "select P = {#} \<and> is_maximal_lit L P \<or> L \<in># select P"
        using \<open>select P = {#} \<and> is_maximal_lit (L \<cdot>l \<mu>) (P \<cdot> \<mu>) \<or> L \<in># select P\<close> \<open>is_ground_lit L\<close>
        by simp
    qed
  qed
next
  assume "ground_eq_resolution P C"
  thus "eq_resolution P C"
  proof (cases P C rule: ground_eq_resolution.cases)
    case (ground_eq_resolutionI L t)
    show ?thesis
    proof (rule eq_resolutionI)
      show "P = add_mset L C"
        using \<open>P = add_mset L C\<close> .
    next
      show "L = Neg (t \<approx> t)"
        using \<open>L = Neg (t \<approx> t)\<close> .
    next
      show "term_subst.is_imgu Var {{t, t}}"
        by simp
    next
      show "select P = {#} \<and> is_maximal_lit (L \<cdot>l Var) (P \<cdot> Var) \<or> L \<in># select P"
        using \<open>select P = {#} \<and> is_maximal_lit L P \<or> L \<in># select P\<close> by simp
    next
      show "C = C \<cdot> Var"
        by simp
    qed
  qed
qed

lemma eq_factoring_iff_ground_eq_factoring:
  assumes ground_P: "is_ground_cls P"
  shows "eq_factoring P C \<longleftrightarrow> ground_eq_factoring P C"
proof (rule iffI)
  assume "eq_factoring P C"
  thus "ground_eq_factoring P C"
  proof (cases P C rule: eq_factoring.cases)
    case (eq_factoringI L\<^sub>1 L\<^sub>2 P' s\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)
    with ground_P have "is_ground_lit L\<^sub>1" and "is_ground_lit L\<^sub>2" and "is_ground_cls P'"
      by simp_all
    hence "is_ground_atm (s\<^sub>1 \<approx> s\<^sub>1')" and "is_ground_atm (t\<^sub>2 \<approx> t\<^sub>2')"
      using eq_factoringI(2,3) by simp_all
    hence "is_ground_trm s\<^sub>1" and "is_ground_trm s\<^sub>1'" and "is_ground_trm t\<^sub>2" and "is_ground_trm t\<^sub>2'"
      by simp_all
    hence "term_subst.is_ground_set {s\<^sub>1, t\<^sub>2}"
      by (simp add: term_subst.is_ground_set_def)
    moreover from \<open>term_subst.is_imgu \<mu> {{s\<^sub>1, t\<^sub>2}}\<close> have "term_subst.is_unifier \<mu> {s\<^sub>1, t\<^sub>2}"
      by (simp add: term_subst.is_imgu_def term_subst.is_unifiers_def)
    ultimately have "s\<^sub>1 = t\<^sub>2"
      using term_subst.ball_eq_constant_if_unifier[of "{s\<^sub>1, t\<^sub>2}" _ \<mu>] by simp

    show ?thesis
    proof (rule ground_eq_factoringI)
      show "P = add_mset (Pos (s\<^sub>1 \<approx> s\<^sub>1')) (add_mset (Pos (t\<^sub>2 \<approx> t\<^sub>2')) P')"
        using eq_factoringI(1-3) by argo
    next
      show "Pos (s\<^sub>1 \<approx> s\<^sub>1') = Pos (s\<^sub>1 \<approx> s\<^sub>1')" ..
    next
      show "Pos (t\<^sub>2 \<approx> t\<^sub>2') = Pos (s\<^sub>1 \<approx> t\<^sub>2')"
        unfolding \<open>s\<^sub>1 = t\<^sub>2\<close> ..
    next
      show "select P = {#}"
        using \<open>select P = {#} \<and> is_maximal_lit (L\<^sub>1 \<cdot>l \<mu>) (P \<cdot> \<mu>)\<close> ..
    next
      from ground_P show "is_maximal_lit (Pos (s\<^sub>1 \<approx> s\<^sub>1')) P"
        using \<open>select P = {#} \<and> is_maximal_lit (L\<^sub>1 \<cdot>l \<mu>) (P \<cdot> \<mu>)\<close> \<open>is_ground_lit L\<^sub>1\<close>
          \<open>L\<^sub>1 = Pos (s\<^sub>1 \<approx> s\<^sub>1')\<close> by simp
    next
      have "\<not> s\<^sub>1 \<preceq>\<^sub>t s\<^sub>1'"
        using \<open>is_ground_trm s\<^sub>1\<close> \<open>is_ground_trm s\<^sub>1'\<close> \<open>\<not> s\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t s\<^sub>1' \<cdot>t \<mu>\<close> by simp
      thus "s\<^sub>1' \<prec>\<^sub>t s\<^sub>1"
        using \<open>is_ground_trm s\<^sub>1\<close> \<open>is_ground_trm s\<^sub>1'\<close> totalp_less_trm
        by (metis (mono_tags, lifting) mem_Collect_eq sup2I1 sup2I2 totalp_onD)
    next
      show "C = add_mset (Neg (s\<^sub>1' \<approx> t\<^sub>2')) (add_mset (Pos (s\<^sub>1 \<approx> t\<^sub>2')) P')"
        using \<open>C = add_mset (Pos (s\<^sub>1 \<approx> t\<^sub>2')) (add_mset (Neg (s\<^sub>1' \<approx> t\<^sub>2')) P') \<cdot> \<mu>\<close> \<open>s\<^sub>1 = t\<^sub>2\<close>
          \<open>is_ground_cls P'\<close> \<open>is_ground_trm s\<^sub>1'\<close> \<open>is_ground_trm t\<^sub>2'\<close> \<open>is_ground_trm t\<^sub>2\<close>
        by simp
    qed
  qed
next
  assume "ground_eq_factoring P C"
  thus "eq_factoring P C"
  proof (cases P C rule: ground_eq_factoring.cases)
    case (ground_eq_factoringI L\<^sub>1 L\<^sub>2 P' t t' t'')
    show ?thesis
    proof (rule eq_factoringI)
      show "P = add_mset L\<^sub>1 (add_mset L\<^sub>2 P')"
        using \<open>P = add_mset L\<^sub>1 (add_mset L\<^sub>2 P')\<close> .
    next
      show "L\<^sub>1 = Pos (t \<approx> t')"
        using \<open>L\<^sub>1 = Pos (t \<approx> t')\<close> .
    next
      show "L\<^sub>2 = Pos (t \<approx> t'')"
        using \<open>L\<^sub>2 = Pos (t \<approx> t'')\<close> .
    next
      show "term_subst.is_imgu Var {{t, t}}"
        by simp
    next
      show "select P = {#} \<and> is_maximal_lit (L\<^sub>1 \<cdot>l Var) (P \<cdot> Var)"
        using \<open>select P = {#}\<close> \<open>is_maximal_lit L\<^sub>1 P\<close> by simp
    next
      show "\<not> t \<cdot>t Var \<preceq>\<^sub>t t' \<cdot>t Var"
        using \<open>t' \<prec>\<^sub>t t\<close>
        using asympD by fastforce
    next
      show "C = add_mset (Pos (t \<approx> t'')) (add_mset (Neg (t' \<approx> t'')) P') \<cdot> Var"
        using \<open>C = add_mset (Neg (t' \<approx> t'')) (add_mset (Pos (t \<approx> t'')) P')\<close> by simp
    qed
  qed
qed *)

subsubsection \<open>Alternative Specification of the Superposition Rule\<close>

inductive pos_superposition ::
  "('f, 'v) term atom clause \<Rightarrow> ('f, 'v) term atom clause \<Rightarrow> ('f, 'v) term atom clause \<Rightarrow> bool"
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
    select P\<^sub>1 = {#} \<Longrightarrow>
    is_strictly_maximal_lit (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>) \<Longrightarrow>
    select P\<^sub>2 = {#} \<Longrightarrow>
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
  "('f, 'v) term atom clause \<Rightarrow> ('f, 'v) term atom clause \<Rightarrow> ('f, 'v) term atom clause \<Rightarrow> bool"
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
    select P\<^sub>2 = {#} \<Longrightarrow>
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

lemma superposition_iff_pos_or_neg:
  "superposition P\<^sub>1 P\<^sub>2 C \<longleftrightarrow> pos_superposition P\<^sub>1 P\<^sub>2 C \<or> neg_superposition P\<^sub>1 P\<^sub>2 C"
proof (rule iffI)
  assume "superposition P\<^sub>1 P\<^sub>2 C"
  thus "pos_superposition P\<^sub>1 P\<^sub>2 C \<or> neg_superposition P\<^sub>1 P\<^sub>2 C"
  proof (cases P\<^sub>1 P\<^sub>2 C rule: superposition.cases)
    case (superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' \<P> s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)
    then show ?thesis
      using pos_superpositionI[of \<rho>\<^sub>1 \<rho>\<^sub>2 P\<^sub>1 P\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>]
      using neg_superpositionI[of \<rho>\<^sub>1 \<rho>\<^sub>2 P\<^sub>1 P\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>]
      by metis
  qed
next
  assume "pos_superposition P\<^sub>1 P\<^sub>2 C \<or> neg_superposition P\<^sub>1 P\<^sub>2 C"
  thus "superposition P\<^sub>1 P\<^sub>2 C"
    using superposition_if_neg_superposition superposition_if_pos_superposition by metis
qed


subsection \<open>First-Order Layer\<close>

abbreviation F_Inf :: "('f, 'v) term atom clause inference set" where
  "F_Inf \<equiv> {}"

abbreviation F_Bot :: "('f, 'v) term atom clause set" where
  "F_Bot \<equiv> {{#}}"

abbreviation F_entails :: "('f, 'v) term atom clause set \<Rightarrow> ('f, 'v) term atom clause set \<Rightarrow> bool" where
  "F_entails \<equiv> (\<TTurnstile>e)"

typedecl Q

definition \<G>_F :: "Q \<Rightarrow> ('f, 'v) term atom clause \<Rightarrow> 'f gterm atom clause set" where
  "\<G>_F \<equiv> \<lambda>_ _. {}"

definition \<G>_I :: "Q \<Rightarrow> ('f, 'v) term atom clause inference \<Rightarrow> 'f gterm atom clause inference set option" where
  "\<G>_I \<equiv> \<lambda>_ _. None"

definition Prec_F :: "'f gterm atom clause \<Rightarrow> ('f, 'v) term atom clause \<Rightarrow> ('f, 'v) term atom clause \<Rightarrow> bool" where
  "Prec_F \<equiv> \<lambda>_ _ _. False"

(* 
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
qed *)

end

end