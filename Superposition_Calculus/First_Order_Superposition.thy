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

lemma map_uprod_inverse: "(\<And>x. f (g x) = x) \<Longrightarrow> (\<And>y. map_uprod f (map_uprod g y) = y)"
  by (simp add: uprod.map_comp uprod.map_ident_strong)

lemma map_literal_inverse: "(\<And>x. f (g x) = x) \<Longrightarrow> (\<And>y. map_literal f (map_literal g y) = y)"
  by (simp add: literal.map_comp literal.map_ident_strong)

lemma gterm_is_fun: "is_Fun (term_of_gterm t)"
  by(cases t) simp

lemma ground_imgu_equal: 
  assumes "is_ground_trm t\<^sub>1" and "is_ground_trm t\<^sub>2" and "term_subst.is_imgu \<mu> {{t\<^sub>1, t\<^sub>2}}"
  shows "t\<^sub>1 = t\<^sub>2"
  using assms
  unfolding basic_substitution_ops.is_imgu_def term_subst.is_ground_def term_subst.is_unifiers_def
  by (metis finite.emptyI finite.insertI insertCI term_subst.is_unifier_iff_if_finite)

lemma literals_distinct [simp]: "Neg \<noteq> Pos" "Pos \<noteq> Neg"
  by(metis literal.distinct(1))+

lemma mset_uprod_image_mset: "mset_uprod (map_uprod f p) = image_mset f (mset_uprod p)"
  using image_mset_add_mset image_mset_empty map_uprod_simps mset_uprod_Upair uprod_exhaust
proof-
  obtain x y where [simp]: "p = Upair x y"
    using uprod_exhaust by blast

  have "mset_uprod (map_uprod f p) = {# f x, f y #}"
    by simp

  then show "mset_uprod (map_uprod f p) = image_mset f (mset_uprod p)"
    by simp
qed
  
lemma mset_lit_image_mset: "mset_lit (map_literal (map_uprod f) l) = image_mset f (mset_lit l)"
  by(induction l) (simp_all add: mset_uprod_image_mset)

section \<open>First_Order_Terms And Abstract_Substitution\<close>

notation subst_apply_term (infixl "\<cdot>t" 67)
notation subst_apply_ctxt (infixl "\<cdot>t\<^sub>c" 67)
notation subst_compose (infixl "\<odot>" 75)

type_synonym ('f, 'v) atom = "('f, 'v) term uprod"

type_synonym 'f ground_atom = "'f Ground_Superposition.atom"

definition subst_atm ::
  "('f, 'v) atom \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) atom" (infixl "\<cdot>a" 67)
where
  "subst_atm A \<sigma> = map_uprod (\<lambda>t. subst_apply_term t \<sigma>) A"

definition subst_lit ::
  "('f, 'v) atom literal \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) atom literal" (infixl "\<cdot>l" 67)
where
  "subst_lit L \<sigma> = map_literal (\<lambda>A. A \<cdot>a \<sigma>) L"

definition subst_cls ::
  "('f, 'v) atom clause \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) atom clause" (infixl "\<cdot>" 67)
where
  "subst_cls C \<sigma> = image_mset (\<lambda>L. L \<cdot>l \<sigma>) C"

definition subst_cls_list :: 
  "('f, 'v) atom clause list \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) atom clause list" (infixl "\<cdot>cl" 67) where
  "Cs \<cdot>cl \<sigma> = map (\<lambda>A. A \<cdot> \<sigma>) Cs"

definition subst_cls_lists :: 
  "('f, 'v) atom clause list \<Rightarrow> ('f, 'v) subst list \<Rightarrow>('f, 'v) atom clause list" (infixl "\<cdot>\<cdot>cl" 67) 
where
  "Cs \<cdot>\<cdot>cl \<sigma>s = map2 (\<cdot>) Cs \<sigma>s"

definition vars_atm :: "('f, 'v) atom \<Rightarrow> 'v set" where
  "vars_atm p = (\<Union>t \<in> set_uprod p. vars_term t)"

definition vars_lit :: "('f, 'v) atom literal \<Rightarrow> 'v set" where
  "vars_lit L = vars_atm (atm_of L)"
                            
definition vars_cls :: "('f, 'v) atom clause \<Rightarrow> 'v set" where
  "vars_cls C = (\<Union>L \<in> set_mset C. vars_lit L)"

definition vars_cls_set :: "('f, 'v) atom clause set \<Rightarrow> 'v set" where
  "vars_cls_set N = (\<Union>C \<in> N. vars_cls C)"

lemma subst_atm_Var_ident[simp]: "A \<cdot>a Var = A"
  by (simp add: subst_atm_def uprod.map_ident)

lemma subst_lit_Var_ident[simp]: "L \<cdot>l Var = L"
  by (simp add: subst_lit_def literal.map_ident)

lemma subst_cls_Var_ident[simp]: "C \<cdot> Var = C"
  by (simp add: subst_cls_def multiset.map_ident)
  
lemma vars_lit_Pos[simp]: "vars_lit (Pos A) = vars_atm A"
  by (simp add: vars_lit_def)

lemma vars_lit_Neg[simp]: "vars_lit (Neg A) = vars_atm A"
  by (simp add: vars_lit_def)

lemma vars_atm_make_uprod[simp]: "vars_lit (t\<^sub>1 \<approx> t\<^sub>2) = vars_term t\<^sub>1 \<union> vars_term t\<^sub>2"
  unfolding vars_lit_def vars_atm_def
  by simp

lemma vars_cls_add_mset[simp]: "vars_cls (add_mset L C) = vars_lit L \<union> vars_cls C"
  by (simp add: vars_cls_def)

lemma vars_cls_plus[simp]: "vars_cls (C\<^sub>1 + C\<^sub>2) = vars_cls C\<^sub>1 \<union> vars_cls C\<^sub>2"
  by (simp add: vars_cls_def)

lemma atom_subst_compose: "atom \<cdot>a \<mu> \<odot> \<theta> = atom \<cdot>a \<mu> \<cdot>a \<theta>"
  unfolding subst_atm_def subst_subst_compose
  by (metis (no_types, lifting) map_uprod_simps uprod_exhaust)

lemma literal_subst_compose: "literal \<cdot>l \<mu> \<odot> \<theta> = literal \<cdot>l \<mu> \<cdot>l \<theta>"
  unfolding subst_lit_def atom_subst_compose
  by (smt (verit, del_insts) Pos_atm_of_iff literal.collapse(2) literal.simps(10) literal.simps(9))

lemma clause_subst_compose: "clause \<cdot> (\<mu> \<odot> \<theta>) = clause \<cdot> \<mu> \<cdot> \<theta>"
  unfolding subst_cls_def literal_subst_compose
  by simp

lemma ground_subst_composition: 
  "term_subst.is_ground_subst \<theta> \<Longrightarrow> term_subst.is_ground_subst (\<mu> \<odot> \<theta>)"
  by (simp add: term_subst.is_ground_subst_def)

abbreviation is_ground_ctxt where
  "is_ground_ctxt c \<equiv> vars_ctxt c = {}"

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

lemma is_ground_trm_iff_term_context_ground: "Term_Context.ground t = is_ground_trm t "
  by(induction t) auto

lemma is_ground_trm_ctxt_iff_ground_ctxt [simp]: "ground_ctxt c = is_ground_ctxt c"
  by (induction c) (auto simp: is_ground_trm_iff_term_context_ground)

lemma gterm_of_term_gctxt_of_ctxt:
  "is_ground_ctxt c \<Longrightarrow> is_ground_trm t \<Longrightarrow> (gctxt_of_ctxt c)\<langle>gterm_of_term t\<rangle>\<^sub>G = gterm_of_term c\<langle>t\<rangle>"
  using is_ground_trm_ctxt_iff_ground_ctxt
  by (metis ctxt_of_gctxt_apply_gterm gctxt_of_ctxt_inv)

lemma subst_trm_ctxt_ident_if_is_ground_ctxt[simp]: "is_ground_ctxt c \<Longrightarrow> c \<cdot>t\<^sub>c \<sigma> = c"
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

lemma is_ground_subst_is_ground_term: "term_subst.is_ground_subst \<theta> \<Longrightarrow> is_ground_trm (t \<cdot>t \<theta>)"
  unfolding term_subst.is_ground_subst_def
  by simp

lemma is_ground_subst_is_ground_atom: "term_subst.is_ground_subst \<theta> \<Longrightarrow> is_ground_atm (a \<cdot>a \<theta>)"
  unfolding vars_atm_def subst_atm_def
  using is_ground_subst_is_ground_term
  by (smt (verit, ccfv_threshold) Sup_bot_conv(1) imageE uprod.set_map)

lemma is_ground_subst_is_ground_literal: "term_subst.is_ground_subst \<theta> \<Longrightarrow> is_ground_lit (l \<cdot>l \<theta>)"
  unfolding subst_lit_def vars_lit_def
  using is_ground_subst_is_ground_atom
  by (metis literal.map_sel(1) literal.map_sel(2))

lemma is_ground_subst_is_ground_clause: "term_subst.is_ground_subst \<theta> \<Longrightarrow> is_ground_cls (P \<cdot> \<theta>)"
  unfolding subst_cls_def vars_cls_def
  using is_ground_subst_is_ground_literal
  by blast

lemma is_ground_subst_is_ground_context: 
  "term_subst.is_ground_subst \<theta> \<Longrightarrow> is_ground_ctxt (c \<cdot>t\<^sub>c \<theta>)"
  unfolding term_subst.is_ground_subst_def
  by (metis subst_apply_term_ctxt_apply_distrib sup_bot.right_neutral vars_term_ctxt_apply)

lemma is_imgu_equals: "term_subst.is_imgu \<mu> {{t\<^sub>1, t\<^sub>2}} \<Longrightarrow> t\<^sub>1 \<cdot>t \<mu> = t\<^sub>2 \<cdot>t \<mu>"
  unfolding term_subst.is_imgu_def term_subst.is_unifiers_def  
  using term_subst.is_unifier_iff_if_finite[of "{t\<^sub>1, t\<^sub>2}"  \<mu>]
  by blast

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
  by (induction t) (auto intro: nth_equalityI)

lemma context_ground_context: 
  "(ctxt_of_gctxt context)\<langle>term_of_gterm term\<rangle> = term_of_gterm context\<langle>term\<rangle>\<^sub>G"
  "is_ground_ctxt c \<Longrightarrow> term_of_gterm (gctxt_of_ctxt c)\<langle>t\<rangle>\<^sub>G = c\<langle>term_of_gterm t\<rangle>"
   apply (metis ctxt_of_gctxt_inv ground_ctxt_of_gctxt ground_gctxt_of_ctxt_apply_gterm)
   by (simp add: ground_gctxt_of_ctxt_apply_gterm)

lemma ground_term_with_ground_context: "is_ground_trm ((ctxt_of_gctxt context)\<langle>term_of_gterm term\<rangle>)"
  by simp

lemma ground_term_with_context:
  assumes "is_ground_trm c\<langle>t\<rangle>" 
  shows 
    "ground_ctxt c" (is "?is_ground_context")
    "is_ground_trm t" (is "?is_ground_term")
proof-
  show ?is_ground_context
    using assms gterm_of_term_ident_if_ground term_of_gterm_ctxt_apply_ground(1) by blast
  show ?is_ground_term
    using assms by auto
qed

lemma ground_term_in_ground_context: "is_ground_ctxt c \<Longrightarrow> is_ground_trm t \<Longrightarrow> is_ground_trm c\<langle>t\<rangle>"
  by simp

lemma lit_glit_inverse[simp]: "glit_lit (lit_glit L) = L"
  unfolding lit_glit_def glit_lit_def
  by (simp add: literal.map_comp uprod.map_comp comp_def gterm_of_term_ident_if_ground 
      literal.map_ident_strong uprod.map_ident_strong)

lemma cls_gcls_inverse[simp]: "gcls_cls (cls_gcls C) = C"
  unfolding gcls_cls_def cls_gcls_def
  by simp

lemma inj_lit_glit: "inj_on lit_glit X"
  by (metis inj_on_def lit_glit_inverse)

lemma inj_cls_gcls: "inj_on cls_gcls X"
  by (metis inj_on_def cls_gcls_inverse)

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

lemma is_ground_lit_if_in_cls_gcls[intro]: 
    "literal \<in># cls_gcls clause \<Longrightarrow> is_ground_lit literal"
  by (simp add: is_ground_lit_if_in_ground_cls)

lemma is_ground_atm_if_in_ground_lit[intro]:
  "A \<in> set_literal L \<Longrightarrow> is_ground_lit L \<Longrightarrow> is_ground_atm A"
  by (metis literal.set_cases vars_lit_Neg vars_lit_Pos)

lemma is_ground_term_if_in_ground_atm[intro]:
  "t \<in> set_uprod A \<Longrightarrow> is_ground_atm A \<Longrightarrow> is_ground_trm t"
  by (simp add: vars_atm_def)

lemma glit_lit_inverse[simp]: "is_ground_lit L \<Longrightarrow> lit_glit (glit_lit L) = L"
  using gterm_of_term_ident_if_ground is_ground_atm_if_in_ground_lit is_ground_term_if_in_ground_atm
  by (smt (verit, best) glit_lit_def lit_glit_inverse literal.inj_map_strong uprod.inj_map_strong 
        vars_lit_glit)
  
lemma gcls_cls_inverse[simp]: "is_ground_cls C \<Longrightarrow> cls_gcls (gcls_cls C) = C"
  unfolding cls_gcls_def gcls_cls_def
  by (simp add: multiset.map_comp comp_def multiset.map_ident_strong is_ground_lit_if_in_ground_cls)

lemma is_ground_cls_gcls: "is_ground_cls (cls_gcls C)"
  by simp

lemma lit_glit_cls_gcls: "L \<in># C \<longleftrightarrow> (lit_glit L) \<in># cls_gcls C" 
  by (metis cls_gcls_def cls_gcls_inverse gcls_cls_def image_eqI lit_glit_inverse multiset.set_map)

lemma glit_lit_with_context: 
  assumes "is_ground_ctxt s" and "is_ground_trm u" and "is_ground_trm t" 
  shows 
    "glit_lit (s\<langle>u\<rangle> \<approx> t) = (gctxt_of_ctxt s)\<langle>gterm_of_term u\<rangle>\<^sub>G \<approx> gterm_of_term t" (is "?Pos")
    "glit_lit (Neg (Upair s\<langle>u\<rangle> t)) 
      = Neg (Upair (gctxt_of_ctxt s)\<langle>gterm_of_term u\<rangle>\<^sub>G (gterm_of_term t))"  (is "?Neg")
proof-
  show ?Pos 
    using assms ctxt_of_gctxt_apply_gterm gctxt_of_ctxt_inv is_ground_trm_ctxt_iff_ground_ctxt
    by (metis glit_lit_def literal.simps(9) map_uprod_simps)
next
  show ?Neg
    using assms ctxt_of_gctxt_apply_gterm gctxt_of_ctxt_inv is_ground_trm_ctxt_iff_ground_ctxt
    by (metis glit_lit_def literal.simps(10) map_uprod_simps)
qed

lemma lit_glit_with_context: 
  "lit_glit (s\<langle>t\<rangle>\<^sub>G \<approx> s') =  (ctxt_of_gctxt s)\<langle>term_of_gterm t\<rangle> \<approx> (term_of_gterm s')"
  "lit_glit (Neg (Upair s\<langle>t\<rangle>\<^sub>G s')) =
     Neg (Upair (ctxt_of_gctxt s)\<langle>term_of_gterm t\<rangle> (term_of_gterm s'))"
  by (auto simp add: context_ground_context lit_glit_def)

lemma gcls_cls_plus [simp]: "gcls_cls (P\<^sub>1 + P\<^sub>2) = gcls_cls P\<^sub>1 + gcls_cls P\<^sub>2"
  by (simp add: gcls_cls_def)

lemma ground_terms_in_ground_atom [intro]: 
  "is_ground_atm (Upair t1 t2) \<longleftrightarrow> is_ground_trm t1 \<and> is_ground_trm t2"
  using vars_atm_make_uprod by fastforce

lemma is_ground_add_mset: "is_ground_cls (add_mset literal clause) \<longleftrightarrow> 
  is_ground_lit literal \<and> is_ground_cls clause"
  by simp

lemma convert_add_mset:
  assumes "cls_gcls clause = add_mset literal clause'" 
  shows "clause = add_mset (glit_lit literal) (gcls_cls clause')"
  using assms
  by (metis cls_gcls_inverse gcls_cls_def image_mset_add_mset)

section \<open>First-Order Layer\<close>

locale first_order_superposition_calculus =
  fixes
    less_term :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" (infix "\<prec>\<^sub>t" 50) and
    less_gterm :: "'f gterm \<Rightarrow> 'f gterm \<Rightarrow> bool" (infix "\<prec>\<^sub>t\<^sub>G" 50) and
    select :: "('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause"
  assumes 
    less_gterm_less_term: "\<And>t1 t2. t1 \<prec>\<^sub>t\<^sub>G t2 \<longleftrightarrow> term_of_gterm t1 \<prec>\<^sub>t term_of_gterm t2" and
    
    transp_less_term[intro]: "transp (\<prec>\<^sub>t)" and
    asymp_less_term[intro]: "asymp (\<prec>\<^sub>t)" and

    wfP_less_gterm[intro]: "wfP (\<prec>\<^sub>t\<^sub>G)" and
    totalp_less_gterm[intro]: "totalp (\<prec>\<^sub>t\<^sub>G)" and
    
    less_gterm_compatible_with_gctxt[simp]: "\<And>ctxt t t'. t \<prec>\<^sub>t\<^sub>G t' \<Longrightarrow> ctxt\<langle>t\<rangle>\<^sub>G \<prec>\<^sub>t\<^sub>G ctxt\<langle>t'\<rangle>\<^sub>G" and
    less_gterm_if_subterm[simp]: "\<And>t ctxt. ctxt \<noteq> \<box>\<^sub>G \<Longrightarrow> t \<prec>\<^sub>t\<^sub>G ctxt\<langle>t\<rangle>\<^sub>G" and

    less_term_grounding_substitution: 
      "\<And>t1 t2 (\<theta> :: 'v \<Rightarrow> ('f, 'v) Term.term). 
        is_ground_trm (t1 \<cdot>t \<theta>) \<Longrightarrow> 
        is_ground_trm (t2 \<cdot>t \<theta>) \<Longrightarrow> 
        t1 \<prec>\<^sub>t t2 \<Longrightarrow> 
        gterm_of_term (t1 \<cdot>t \<theta>) \<prec>\<^sub>t\<^sub>G gterm_of_term (t2 \<cdot>t \<theta>)" and
    
    select_subset: "\<And>C. select C \<subseteq># C" and
    select_negative_lits: "\<And>C L. L \<in># select C \<Longrightarrow> is_neg L" and

    select_stable: "\<And>C \<rho>. select (C \<cdot> \<rho>) = (select C) \<cdot> \<rho>" and

    ground_critical_pair_theorem: "\<And>(R :: 'f gterm rel). ground_critical_pair_theorem R"
begin

lemma select_ground_lit: "literal \<in># select (cls_gcls clause) \<Longrightarrow> is_ground_lit literal"
  by (meson is_ground_lit_if_in_cls_gcls mset_subset_eqD select_subset)

lemma transp_less_gterm [intro]: "transp (\<prec>\<^sub>t\<^sub>G)"
  using less_gterm_less_term transp_less_term transpE transpI
  by metis

lemma asymp_less_gterm [intro]: "asymp (\<prec>\<^sub>t\<^sub>G)"
  by (simp add: wfP_imp_asymp wfP_less_gterm)

lemma less_term_less_gterm: 
  assumes "is_ground_trm t1" and "is_ground_trm t2"
  shows "t1 \<prec>\<^sub>t t2 \<longleftrightarrow> gterm_of_term t1 \<prec>\<^sub>t\<^sub>G gterm_of_term t2"
  by (simp add: assms gterm_of_term_ident_if_ground less_gterm_less_term)

(* TODO: This probably does not work out \<rightarrow> p.9 *)
definition select\<^sub>G :: 
  "'f ground_atom clause \<Rightarrow> 'f ground_atom clause" 
where
  "select\<^sub>G clause \<equiv> gcls_cls (select (cls_gcls clause))"

lemma select\<^sub>G_subset: "select\<^sub>G C \<subseteq># C"
  by (metis cls_gcls_inverse gcls_cls_def image_mset_subseteq_mono select\<^sub>G_def select_subset)

lemma select\<^sub>G_negative_lits: "L \<in># select\<^sub>G C \<Longrightarrow> is_neg L" 
  using select_negative_lits
  unfolding select\<^sub>G_def
  by (metis cls_gcls_def gcls_cls_inverse image_mset_of_subset is_ground_cls_gcls lit_glit_def 
      literal.map_disc_iff select_subset lit_glit_cls_gcls)

abbreviation lesseq_term (infix "\<preceq>\<^sub>t" 50) where
  "lesseq_term \<equiv> (\<prec>\<^sub>t)\<^sup>=\<^sup>="

definition less_lit ::
  "('f, 'v) atom literal \<Rightarrow> ('f, 'v) atom literal \<Rightarrow> bool" (infix "\<prec>\<^sub>l" 50) where
  "less_lit L1 L2 \<equiv> multp (\<prec>\<^sub>t) (mset_lit L1) (mset_lit L2)"

abbreviation lesseq_lit (infix "\<preceq>\<^sub>l" 50) where
  "lesseq_lit \<equiv> (\<prec>\<^sub>l)\<^sup>=\<^sup>="

abbreviation less_cls ::
  "('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool" (infix "\<prec>\<^sub>c" 50) where
  "less_cls \<equiv> multp (\<prec>\<^sub>l)"

abbreviation lesseq_cls (infix "\<preceq>\<^sub>c" 50) where
  "lesseq_cls \<equiv> (\<prec>\<^sub>c)\<^sup>=\<^sup>="

abbreviation is_maximal_lit :: "('f, 'v) atom literal \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool" where
  "is_maximal_lit L M \<equiv> is_maximal_in_mset_wrt (\<prec>\<^sub>l) M L"

abbreviation is_strictly_maximal_lit :: 
  "('f, 'v) atom literal \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool" where
  "is_strictly_maximal_lit L M \<equiv> is_greatest_in_mset_wrt (\<prec>\<^sub>l) M L"

lemma not_less_eq_term: 
  assumes "is_ground_trm t\<^sub>1" and "is_ground_trm t\<^sub>2"
  shows "\<not> t\<^sub>2 \<preceq>\<^sub>t t\<^sub>1 \<longleftrightarrow> t\<^sub>1 \<prec>\<^sub>t t\<^sub>2"
  using assms 
  by (metis asympD asymp_less_term gterm_of_term_ident_if_ground less_term_less_gterm reflclp_iff 
        totalpD totalp_less_gterm)

lemma totalp_less_term[intro]: "totalp_on (term_of_gterm ` terms) (\<prec>\<^sub>t)"
  by (smt (verit, best) image_iff less_gterm_less_term totalpD totalp_less_gterm totalp_on_def)

lemma transp_less_lit [intro]: "transp (\<prec>\<^sub>l)"
  by (metis less_lit_def transp_def transp_less_term transp_multp)
                                                            
lemma asymp_less_lit [intro]: "asymp (\<prec>\<^sub>l)"
  by (metis asympD asympI asymp_less_term asymp_multp\<^sub>H\<^sub>O less_lit_def multp_eq_multp\<^sub>H\<^sub>O 
        transp_less_term)

lemma transp_less_cls [intro]: "transp (\<prec>\<^sub>c)"
  by (metis less_lit_def transp_def transp_less_term transp_multp)

lemma asymp_less_cls [intro]: "asymp (\<prec>\<^sub>c)"
  by (simp add: asymp_less_lit asymp_multp\<^sub>H\<^sub>O multp_eq_multp\<^sub>H\<^sub>O transp_less_lit)

interpretation G: ground_superposition_calculus "(\<prec>\<^sub>t\<^sub>G)" select\<^sub>G
  apply(unfold_locales)
  by(auto simp: select\<^sub>G_subset select\<^sub>G_negative_lits ground_critical_pair_theorem)

notation G.less_lit (infix "\<prec>\<^sub>l\<^sub>G" 50)
notation G.less_cls (infix "\<prec>\<^sub>c\<^sub>G" 50)

notation G.lesseq_trm (infix "\<preceq>\<^sub>t\<^sub>G" 50)
notation G.lesseq_lit (infix "\<preceq>\<^sub>l\<^sub>G" 50)
notation G.lesseq_cls (infix "\<preceq>\<^sub>c\<^sub>G" 50)

lemma mset_lit_glit: "mset_lit (lit_glit l) = image_mset term_of_gterm (mset_lit l)"
  unfolding lit_glit_def
  by(rule mset_lit_image_mset[of term_of_gterm])

lemma less_glit_iff_less_lit: "x \<prec>\<^sub>l\<^sub>G y \<longleftrightarrow> lit_glit x \<prec>\<^sub>l lit_glit y"
   using 
     multp_image_mset_image_msetI[OF _ transp_less_term]
     multp_image_mset_image_msetD[OF _ transp_less_term[THEN transp_on_subset] inj_term_of_gterm]
   unfolding less_lit_def G.less_lit_def less_gterm_less_term mset_lit_glit
   by blast

lemma is_maximal_glit_iff_is_maximal_lit: 
  "G.is_maximal_lit literal clause \<longleftrightarrow> is_maximal_lit (lit_glit literal) (cls_gcls clause)"
  unfolding 
    is_maximal_in_mset_wrt_iff[
      OF transp_less_lit[THEN transp_on_subset] asymp_less_lit[THEN asymp_on_subset],
      OF subset_UNIV subset_UNIV
    ]
    is_maximal_in_mset_wrt_iff[
      OF G.transp_less_lit[THEN transp_on_subset] G.asymp_less_lit[THEN asymp_on_subset],
      OF subset_UNIV subset_UNIV
    ] 
  using lit_glit_cls_gcls lit_glit_inverse lit_glit_cls_gcls less_glit_iff_less_lit
  by (smt (verit, best) cls_gcls_def imageE multiset.set_map)

lemma totalp_less_lit[intro]: "totalp_on (lit_glit ` literals) (\<prec>\<^sub>l)"
proof-
  have "totalp_on literals (\<lambda>L1 L2. multp (\<prec>\<^sub>t\<^sub>G) (mset_lit L1) (mset_lit L2))"
    using totalp_less_gterm G.less_lit_def G.totalp_on_less_lit by presburger

  then have "totalp_on literals 
    (\<lambda>L1 L2. multp (\<lambda>a b. term_of_gterm a \<prec>\<^sub>t term_of_gterm b) (mset_lit L1) (mset_lit L2))"
    using less_gterm_less_term
    by (metis (mono_tags, lifting) transp_less_gterm multp_mono_strong totalp_on_def)

  then show "totalp_on (lit_glit ` literals) (\<prec>\<^sub>l)"
    by (smt (verit, best) G.totalp_on_less_lit imageE less_glit_iff_less_lit totalpD totalp_onI)
qed

lemma not_less_eq_lit: 
  assumes "is_ground_lit l\<^sub>1" and "is_ground_lit l\<^sub>2"
  shows "\<not> l\<^sub>2 \<preceq>\<^sub>l l\<^sub>1 \<longleftrightarrow> l\<^sub>1 \<prec>\<^sub>l l\<^sub>2"
  using assms
  by (metis G.asymp_on_less_lit G.totalp_on_less_lit asympD glit_lit_inverse less_glit_iff_less_lit 
        reflclp_iff totalpD)

lemma less_cls_iff_less_gcls: "cls_gcls c1 \<prec>\<^sub>c cls_gcls c2 \<longleftrightarrow> c1 \<prec>\<^sub>c\<^sub>G c2"
  unfolding cls_gcls_def
  using
    less_glit_iff_less_lit
    multp_image_mset_image_msetD[OF _ transp_less_lit[THEN transp_on_subset] inj_lit_glit]
    multp_image_mset_image_msetI[OF _  transp_less_lit[THEN transp_on_subset]]
  by (smt transp_less_lit multp_mono_strong top_greatest transpE transpI)

lemma totalp_less_cls[intro]: "totalp_on (cls_gcls ` clauses) (\<prec>\<^sub>c)"
  by (smt G.totalp_less_cls image_iff less_cls_iff_less_gcls totalpD totalp_onI) 

lemma set_mset_cls_glcs_lit_glit: "set_mset (cls_gcls clause) = lit_glit ` (set_mset clause)"
  unfolding cls_gcls_def
  by simp

lemma is_strictly_maximal_lit_iff_is_strictly_maximal_glit:
  "is_strictly_maximal_lit (lit_glit L) (cls_gcls P) \<longleftrightarrow> G.is_strictly_maximal_lit L P"
  unfolding 
    is_greatest_in_mset_wrt_iff[
      OF G.transp_less_lit[THEN transp_on_subset] 
         G.asymp_less_lit[THEN asymp_on_subset] 
         G.totalp_less_lit[THEN totalp_on_subset],
      OF subset_UNIV subset_UNIV subset_UNIV
    ]
    is_greatest_in_mset_wrt_iff[
      OF transp_less_lit[THEN transp_on_subset] 
         asymp_less_lit[THEN asymp_on_subset] 
         totalp_less_lit[THEN totalp_on_subset],
      OF subset_UNIV subset_UNIV set_mset_cls_glcs_lit_glit[THEN equalityD1]
    ]
    less_glit_iff_less_lit
  using
    lit_glit_cls_gcls
  by (smt (verit, del_insts) cls_gcls_def add_mset_remove_trivial imageE image_mset_add_mset 
        multi_member_split multiset.set_map)

lemma not_less_eq_cls: 
  assumes "is_ground_cls c\<^sub>1" and "is_ground_cls c\<^sub>2"
  shows "\<not> c\<^sub>2 \<preceq>\<^sub>c c\<^sub>1 \<longleftrightarrow> c\<^sub>1 \<prec>\<^sub>c c\<^sub>2"
  using assms
  by (metis G.totalp_less_cls asympD asymp_less_cls gcls_cls_inverse less_cls_iff_less_gcls 
        reflclp_iff totalpD)

inductive superposition ::
  "('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool"
where
  superpositionI: 
   "term_subst.is_renaming \<rho>\<^sub>1 \<Longrightarrow>
    term_subst.is_renaming \<rho>\<^sub>2 \<Longrightarrow>
    vars_cls (P\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter> vars_cls (P\<^sub>2 \<cdot> \<rho>\<^sub>2) = {} \<Longrightarrow>
    P\<^sub>1 = add_mset L\<^sub>1 P\<^sub>1' \<Longrightarrow>
    P\<^sub>2 = add_mset L\<^sub>2 P\<^sub>2' \<Longrightarrow>
    \<P> \<in> {Pos, Neg} \<Longrightarrow>
    L\<^sub>1 = \<P> (Upair s\<^sub>1\<langle>u\<^sub>1\<rangle> s\<^sub>1') \<Longrightarrow>
    L\<^sub>2 = t\<^sub>2 \<approx> t\<^sub>2' \<Longrightarrow>
    \<not> is_Var u\<^sub>1 \<Longrightarrow>
    term_subst.is_imgu \<mu> {{u\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}} \<Longrightarrow>
    \<not> (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<preceq>\<^sub>c P\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    (\<P> = Pos \<and> select P\<^sub>1 = {#} \<and> is_strictly_maximal_lit (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>)) \<or>
    (\<P> = Neg \<and> (select P\<^sub>1 = {#} \<and> is_maximal_lit (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>) \<or> L\<^sub>1 \<in># select P\<^sub>1)) \<Longrightarrow>
    select P\<^sub>2 = {#} \<Longrightarrow>
    is_strictly_maximal_lit (L\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu>) (P\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    \<not> (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu>) \<Longrightarrow>
    \<not> (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<preceq>\<^sub>t t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu>) \<Longrightarrow>
    C = add_mset (\<P> (Upair (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> (s\<^sub>1' \<cdot>t \<rho>\<^sub>1))) (P\<^sub>1' \<cdot> \<rho>\<^sub>1 + P\<^sub>2' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu> \<Longrightarrow>
    superposition P\<^sub>1 P\<^sub>2 C"

inductive eq_resolution :: "('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool" where
  eq_resolutionI: "
    P = add_mset L P' \<Longrightarrow>
    L = Neg (Upair s\<^sub>1 s\<^sub>2) \<Longrightarrow>
    term_subst.is_imgu \<mu> {{s\<^sub>1, s\<^sub>2}} \<Longrightarrow>
    select P = {#} \<and> is_maximal_lit (L \<cdot>l \<mu>) (P \<cdot> \<mu>) \<or> L \<in># select P \<Longrightarrow>
    C = P' \<cdot> \<mu> \<Longrightarrow>
    eq_resolution P C"

inductive eq_factoring :: "('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool" where
  eq_factoringI: "
    P = add_mset L\<^sub>1 (add_mset L\<^sub>2 P') \<Longrightarrow>
    L\<^sub>1 = (s\<^sub>1 \<approx> s\<^sub>1') \<Longrightarrow>
    L\<^sub>2 = (t\<^sub>2 \<approx> t\<^sub>2') \<Longrightarrow>
    select P = {#} \<and> is_maximal_lit (L\<^sub>1 \<cdot>l \<mu>) (P \<cdot> \<mu>) \<Longrightarrow>
    \<not> (s\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t s\<^sub>1' \<cdot>t \<mu>) \<Longrightarrow>
    term_subst.is_imgu \<mu> {{s\<^sub>1, t\<^sub>2}} \<Longrightarrow>
    C = add_mset (s\<^sub>1 \<approx> t\<^sub>2') (add_mset (Neg (Upair s\<^sub>1' t\<^sub>2')) P') \<cdot> \<mu> \<Longrightarrow>
    eq_factoring P C"

lemma eq_resolution_iff_ground_eq_resolution:
  "eq_resolution (cls_gcls P) (cls_gcls C) \<longleftrightarrow> G.ground_eq_resolution P C" 
proof (rule iffI)
  assume "eq_resolution (cls_gcls P) (cls_gcls C)"
  thus "G.ground_eq_resolution P C"
  proof(cases rule: eq_resolution.cases)
    case (eq_resolutionI L P' t\<^sub>1 t\<^sub>2 \<mu>)
    
    then have "is_ground_cls P'"
      using is_ground_cls_gcls[of P]
      by fastforce
  
    then have P'_is_C: "P' = cls_gcls C"
      using subst_cls_ident_if_is_ground_cls eq_resolutionI(5) by simp

    have [intro]: "is_ground_lit L" "is_ground_trm t\<^sub>1" "is_ground_trm t\<^sub>2" 
      using eq_resolutionI is_ground_lit_if_in_cls_gcls[of L P] vars_atm_make_uprod
      by fastforce+

    then have "t\<^sub>1 = t\<^sub>2"
      using eq_resolutionI ground_imgu_equal[of t\<^sub>1  t\<^sub>2]
      by simp

    then have [simp]: "L \<cdot>l \<mu> = L"
      using eq_resolutionI is_ground_lit_if_in_ground_cls
      by (metis is_ground_cls_gcls subst_lit_ident_if_is_ground_lit union_single_eq_member)
     
    show ?thesis 
    proof (rule G.ground_eq_resolutionI)
      from eq_resolutionI show "P = add_mset (glit_lit L) C"
        by (metis P'_is_C cls_gcls_inverse gcls_cls_def image_mset_add_mset)
    next
      show "glit_lit L = Neg (Upair (gterm_of_term t\<^sub>1) (gterm_of_term t\<^sub>1))"
        using \<open>t\<^sub>1 = t\<^sub>2\<close>
        by (simp add: glit_lit_def eq_resolutionI)
    next
      show "(select\<^sub>G P = {#} \<and> G.is_maximal_lit (glit_lit L) P) \<or> glit_lit L \<in># select\<^sub>G P"
      proof(cases "select\<^sub>G P")
        case empty
        then show ?thesis 
          using 
            eq_resolutionI(4) 
            is_maximal_glit_iff_is_maximal_lit[of P "glit_lit L"] 
            glit_lit_inverse[OF \<open>is_ground_lit L\<close>]
          unfolding select\<^sub>G_def gcls_cls_def
          by simp
      next
        case add
        then show ?thesis
          using eq_resolutionI(4) add_mset_remove_trivial_If image_mset_add_mset insert_noteq_member
          unfolding gcls_cls_def select\<^sub>G_def
          by force
      qed
    qed
  qed
next
  assume "G.ground_eq_resolution P C"
  thus "eq_resolution (cls_gcls P) (cls_gcls C)"
   proof(cases P C rule: G.ground_eq_resolution.cases)
   case (ground_eq_resolutionI L t)
    show ?thesis
    proof (rule eq_resolutionI)
      show "cls_gcls P = add_mset (lit_glit L) (cls_gcls C)"
        using \<open>P = add_mset L C\<close> 
        unfolding cls_gcls_def
        by simp
    next
      show "lit_glit L = Neg (Upair (term_of_gterm t) (term_of_gterm t))"
        using \<open>L = Neg (Upair t t)\<close>
        unfolding lit_glit_def
        by simp
    next
      show "term_subst.is_imgu Var {{term_of_gterm t, term_of_gterm t}}"
        by simp
    next
      show "select (cls_gcls P) = {#} \<and> is_maximal_lit (lit_glit L \<cdot>l Var) (cls_gcls P \<cdot> Var) 
          \<or> lit_glit L \<in># select (cls_gcls P)"
        using 
          ground_eq_resolutionI(3) 
          is_maximal_glit_iff_is_maximal_lit
          is_ground_lit_if_in_cls_gcls 
          select_subset
        unfolding select\<^sub>G_def gcls_cls_def
        by fastforce
    next
      show "cls_gcls C = cls_gcls C \<cdot> Var"
        by simp
    qed
  qed
qed

lemma eq_factoring_iff_ground_eq_factoring:
  "eq_factoring (cls_gcls P) (cls_gcls C) \<longleftrightarrow> G.ground_eq_factoring P C"
proof (rule iffI)
  assume "eq_factoring (cls_gcls P) (cls_gcls C)"
  thus "G.ground_eq_factoring P C"
  proof(cases rule: eq_factoring.cases)
    case (eq_factoringI L\<^sub>1 L\<^sub>2 P' s\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)

    have is_ground_lit [intro]: "is_ground_lit L\<^sub>1"
      using eq_factoringI is_ground_cls_gcls vars_cls_add_mset 
      by (metis sup_eq_bot_iff)

    have is_ground_trm [intro]: 
      "is_ground_trm s\<^sub>1" 
      "is_ground_trm s\<^sub>1'" 
      "is_ground_trm t\<^sub>2"
      using eq_factoringI is_ground_cls_gcls vars_atm_make_uprod vars_cls_add_mset
      by (metis sup_eq_bot_iff)+

    then have "s\<^sub>1 = t\<^sub>2"
      using ground_imgu_equal local.eq_factoringI(6) by blast

    have ground_substs [simp]: "L\<^sub>1 \<cdot>l \<mu> = L\<^sub>1" "s\<^sub>1 \<cdot>t \<mu> = s\<^sub>1" "s\<^sub>1' \<cdot>t \<mu> = s\<^sub>1'"
      using eq_factoringI is_ground_trm is_ground_lit
      by simp_all

    show ?thesis 
    proof (rule G.ground_eq_factoringI)
      show "P = add_mset (glit_lit L\<^sub>1) (add_mset (glit_lit L\<^sub>2) (gcls_cls P'))"
        by (metis cls_gcls_inverse gcls_cls_def image_mset_add_mset eq_factoringI(1))
    next 
      show "glit_lit L\<^sub>1 = (gterm_of_term s\<^sub>1 \<approx> gterm_of_term s\<^sub>1')"
        by (simp add: glit_lit_def eq_factoringI(2))
    next
      show "glit_lit L\<^sub>2 = (gterm_of_term s\<^sub>1 \<approx> gterm_of_term t\<^sub>2')"
        by (simp add: \<open>s\<^sub>1 = t\<^sub>2\<close> glit_lit_def eq_factoringI(3))
    next
      show "select\<^sub>G P = {#}"
        by (simp add: gcls_cls_def eq_factoringI(4) select\<^sub>G_def)
    next 
      show "G.is_maximal_lit (glit_lit L\<^sub>1) P"
        using   
          eq_factoringI(4) 
          is_maximal_glit_iff_is_maximal_lit 
          glit_lit_inverse[OF \<open>is_ground_lit L\<^sub>1\<close>]
        by simp
    next
      show "gterm_of_term s\<^sub>1' \<prec>\<^sub>t\<^sub>G gterm_of_term s\<^sub>1"
        using eq_factoringI(5)  
          totalp_less_gterm 
          gterm_of_term_ident_if_ground[OF \<open>is_ground_trm s\<^sub>1'\<close>]
          gterm_of_term_ident_if_ground[OF \<open>is_ground_trm s\<^sub>1\<close>]
          less_gterm_less_term
          ground_substs
        by (metis reflclp_iff totalpD)
    next
      have [simp]: "add_mset (s\<^sub>1 \<approx> t\<^sub>2') (add_mset (Neg (Upair s\<^sub>1' t\<^sub>2')) P') \<cdot> \<mu>
          = add_mset (s\<^sub>1 \<approx> t\<^sub>2') (add_mset (Neg (Upair s\<^sub>1' t\<^sub>2')) P')"
        using is_ground_trm is_ground_cls_gcls eq_factoringI subst_cls_ident_if_is_ground_cls
        by (metis cls_gcls_def msed_map_invR vars_atm_make_uprod vars_cls_add_mset vars_lit_Neg 
              vars_lit_Pos)

      then show "C = 
            add_mset 
               (Neg (Upair (gterm_of_term s\<^sub>1') (gterm_of_term t\<^sub>2'))) 
               (add_mset (gterm_of_term s\<^sub>1 \<approx> gterm_of_term t\<^sub>2') 
               (gcls_cls P'))"
        unfolding cls_gcls_def 
        using eq_factoringI(7) glit_lit_def gcls_cls_def cls_gcls_inverse add_mset_commute
        by (metis image_mset_add_mset literal.simps(9, 10) map_uprod_simps)
    qed
  qed
next
  assume "G.ground_eq_factoring P C"
  thus "eq_factoring (cls_gcls P) (cls_gcls C)"
  proof(cases P C rule: G.ground_eq_factoring.cases)
    case (ground_eq_factoringI L\<^sub>1 L\<^sub>2 P' t t' t'')
    show ?thesis 
    proof(rule eq_factoringI)
      show "cls_gcls P = add_mset (lit_glit L\<^sub>1) (add_mset (lit_glit L\<^sub>2) (cls_gcls P'))"
        by (simp add: cls_gcls_def ground_eq_factoringI(1))
    next
      show "lit_glit L\<^sub>1 = term_of_gterm t \<approx> term_of_gterm t'"
        by (simp add: ground_eq_factoringI(2) lit_glit_def)
    next
      show "lit_glit L\<^sub>2 =  term_of_gterm t \<approx> term_of_gterm t''"
        by (simp add: ground_eq_factoringI(3) lit_glit_def)
    next
      show "select (cls_gcls P) = {#} \<and> is_maximal_lit (lit_glit L\<^sub>1 \<cdot>l Var) (cls_gcls P \<cdot> Var)"
        using  ground_eq_factoringI(4,5) is_maximal_glit_iff_is_maximal_lit
        unfolding select\<^sub>G_def gcls_cls_def
        by simp
    next
      show "\<not> term_of_gterm t \<cdot>t Var \<preceq>\<^sub>t term_of_gterm t' \<cdot>t Var" 
        using ground_eq_factoringI(6) asympD 
        unfolding less_gterm_less_term
        by force
    next   
      show "term_subst.is_imgu Var {{term_of_gterm t, term_of_gterm t}}"
        by simp
    next
      show "cls_gcls C = 
              add_mset 
                  (term_of_gterm t \<approx> term_of_gterm t'') 
                  (add_mset (Neg (Upair (term_of_gterm t') (term_of_gterm t''))) 
                  (cls_gcls P')) 
              \<cdot> Var"
        by (simp add: cls_gcls_def ground_eq_factoringI(7) lit_glit_def)
    qed
  qed
qed

lemma superposition_iff_ground_superposition:
   "superposition (cls_gcls P1) (cls_gcls P2) (cls_gcls C) \<longleftrightarrow> G.ground_superposition P1 P2 C"
proof(rule iffI)
  assume "superposition (cls_gcls P1) (cls_gcls P2) (cls_gcls C)"
  thus " G.ground_superposition P1 P2 C"
  proof(cases rule: superposition.cases)
    case (superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' \<P> s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)

    have \<P>_ground: "\<And>a. is_ground_atm a \<longleftrightarrow> is_ground_lit (\<P> a)" 
      using superpositionI(12) by fastforce

    have is_ground_L\<^sub>1 [intro]: "is_ground_lit L\<^sub>1"
      using superpositionI(4) is_ground_add_mset is_ground_cls_gcls
      by metis
      
    have is_ground_L\<^sub>2 [intro]: "is_ground_lit L\<^sub>2"
      using superpositionI(5) is_ground_lit_if_in_cls_gcls[of L\<^sub>2 P2] 
      by simp

    have is_ground_P\<^sub>1' [intro]: "is_ground_cls P\<^sub>1'"
      using superpositionI(4) is_ground_add_mset is_ground_cls_gcls 
      by metis

    have is_ground_P\<^sub>2' [intro]: "is_ground_cls P\<^sub>2'"
      using superpositionI(5) is_ground_add_mset is_ground_cls_gcls 
      by metis

    have is_ground_s\<^sub>1_u\<^sub>1 [intro]: "is_ground_trm s\<^sub>1\<langle>u\<^sub>1\<rangle>"
      using is_ground_L\<^sub>1 superpositionI(7) ground_terms_in_ground_atom[of "s\<^sub>1\<langle>u\<^sub>1\<rangle>" s\<^sub>1'] \<P>_ground
      by blast

    then have is_ground_s\<^sub>1 [intro]: "is_ground_ctxt s\<^sub>1"
      by simp
      
    have is_ground_u\<^sub>1 [intro]: "is_ground_trm u\<^sub>1"
      using is_ground_s\<^sub>1_u\<^sub>1 by auto
   
    have is_ground_s\<^sub>1' [intro]: "is_ground_trm s\<^sub>1'"
      using superpositionI(7) is_ground_L\<^sub>1 ground_terms_in_ground_atom \<P>_ground
      by metis

    have is_ground_t\<^sub>2 [intro]: "is_ground_trm t\<^sub>2"
      using superpositionI(8) is_ground_L\<^sub>2
      by (simp add: ground_terms_in_ground_atom)

    have is_ground_t\<^sub>2' [intro]: "is_ground_trm t\<^sub>2'"
      using superpositionI(8) is_ground_L\<^sub>2
      by (simp add: ground_terms_in_ground_atom)

    have "u\<^sub>1 = t\<^sub>2"
      using superpositionI(10) ground_imgu_equal is_ground_t\<^sub>2 is_ground_u\<^sub>1 by auto
    
    obtain \<P>' :: "'f gterm uprod \<Rightarrow> 'f gterm uprod literal"
      where \<P>': "\<P>' = (if \<P> = Pos then Pos else Neg)"
      by simp
                              
    show ?thesis
    proof (rule G.ground_superpositionI)
      show "P1 = add_mset (glit_lit L\<^sub>1) (gcls_cls P\<^sub>1')"
        using superpositionI(4) convert_add_mset
        by blast
    next
      show "P2 = add_mset (glit_lit L\<^sub>2) (gcls_cls P\<^sub>2')"
        using superpositionI(5) convert_add_mset
        by blast
    next
      show "P2 \<prec>\<^sub>c\<^sub>G P1"
        using 
          superpositionI(11) 
          not_less_eq_cls[of "cls_gcls P1" "cls_gcls P2"]
          less_cls_iff_less_gcls
        by auto
    next
      show "\<P>' \<in> {Pos, Neg}"
        using superpositionI(6) 
        by (simp add: \<P>')
    next 
      show "glit_lit L\<^sub>1 = \<P>' (Upair (gctxt_of_ctxt s\<^sub>1)\<langle>gterm_of_term u\<^sub>1\<rangle>\<^sub>G (gterm_of_term s\<^sub>1'))"
        using glit_lit_with_context[OF is_ground_s\<^sub>1 is_ground_u\<^sub>1 is_ground_s\<^sub>1'] superpositionI(7,12)
        unfolding \<P>'
        by presburger
    next
      show "glit_lit L\<^sub>2 = gterm_of_term u\<^sub>1 \<approx> gterm_of_term t\<^sub>2'"
        by (simp add: \<open>u\<^sub>1 = t\<^sub>2\<close> glit_lit_def superpositionI(8))
    next
      note is_ground_s\<^sub>1_u\<^sub>1 = ground_term_in_ground_context[OF is_ground_s\<^sub>1 is_ground_u\<^sub>1]
      
      show "gterm_of_term s\<^sub>1' \<prec>\<^sub>t\<^sub>G (gctxt_of_ctxt s\<^sub>1)\<langle>gterm_of_term u\<^sub>1\<rangle>\<^sub>G"
        using superpositionI(15) 
        unfolding 
          term_subst.subst_ident_if_ground[OF is_ground_s\<^sub>1_u\<^sub>1]
          term_subst.subst_ident_if_ground[OF is_ground_s\<^sub>1']
          not_less_eq_term[OF is_ground_s\<^sub>1' is_ground_s\<^sub>1_u\<^sub>1]
          less_gterm_less_term
          gterm_of_term_ident_if_ground[OF is_ground_s\<^sub>1']
          context_ground_context(2)[OF is_ground_s\<^sub>1]
          gterm_of_term_ident_if_ground[OF is_ground_u\<^sub>1].
    next
      show "gterm_of_term t\<^sub>2' \<prec>\<^sub>t\<^sub>G gterm_of_term u\<^sub>1"
        using superpositionI(16)
        unfolding 
          \<open>u\<^sub>1 = t\<^sub>2\<close>
          term_subst.subst_ident_if_ground[OF is_ground_t\<^sub>2] 
          term_subst.subst_ident_if_ground[OF is_ground_t\<^sub>2']
          not_less_eq_term[OF is_ground_t\<^sub>2' is_ground_t\<^sub>2] 
          less_term_less_gterm[OF is_ground_t\<^sub>2' is_ground_t\<^sub>2].
    next 
      have totalp_ground: "totalp_on (set_mset (cls_gcls P1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>)) (\<prec>\<^sub>l)"
        by (simp add: totalp_less_lit set_mset_cls_glcs_lit_glit)

      show "\<P>' = Pos \<and> select\<^sub>G P1 = {#} \<and> G.is_strictly_maximal_lit (glit_lit L\<^sub>1) P1 
          \<or> \<P>' = Neg 
              \<and> (select\<^sub>G P1 = {#} \<and> G.is_maximal_lit (glit_lit L\<^sub>1) P1 \<or> glit_lit L\<^sub>1 \<in># select\<^sub>G P1)"
      proof(cases "\<P>' = Pos")
        case True
        then show ?thesis
          using 
            superpositionI(12)
            is_strictly_maximal_lit_iff_is_strictly_maximal_glit[of P1 "glit_lit L\<^sub>1"]
          unfolding 
            \<P>' 
            select\<^sub>G_def 
            gcls_cls_def 
            subst_lit_ident_if_is_ground_lit[OF is_ground_L\<^sub>1] 
            glit_lit_inverse[OF is_ground_L\<^sub>1]
            subst_cls_ident_if_is_ground_cls[OF is_ground_cls_gcls]
          by (metis image_mset_empty literal.distinct(1))
      next
        case False
        then show ?thesis 
          using superpositionI(12)
          unfolding   
            \<P>' 
            select\<^sub>G_def 
            gcls_cls_def 
            subst_lit_ident_if_is_ground_lit[OF is_ground_L\<^sub>1] 
            subst_cls_ident_if_is_ground_cls[OF is_ground_cls_gcls]
            is_maximal_glit_iff_is_maximal_lit[
              of P1 "glit_lit L\<^sub>1", 
              unfolded glit_lit_inverse[OF is_ground_L\<^sub>1]
            ]
          by auto
      qed 
    next 
      show "select\<^sub>G P2 = {#}"
        by (simp add: gcls_cls_def superpositionI(13) select\<^sub>G_def)
    next 
      note is_strictly_maximal = is_strictly_maximal_lit_iff_is_strictly_maximal_glit[
          of P2 "glit_lit L\<^sub>2", 
          unfolded glit_lit_inverse[OF is_ground_L\<^sub>2]
      ]

      show "G.is_strictly_maximal_lit (glit_lit L\<^sub>2) P2"
        using superpositionI(14)
        unfolding 
          subst_lit_ident_if_is_ground_lit[OF is_ground_L\<^sub>2] 
          subst_cls_ident_if_is_ground_cls[OF is_ground_cls_gcls]
          is_strictly_maximal.
    next 
      note ground_context = ground_term_in_ground_context[OF is_ground_s\<^sub>1 is_ground_t\<^sub>2']

      then have "is_ground_atm (Upair s\<^sub>1\<langle>t\<^sub>2'\<rangle> s\<^sub>1')"
        using is_ground_s\<^sub>1' ground_terms_in_ground_atom
        by metis
     
      then have ground_cls: "is_ground_cls (add_mset (\<P> (Upair s\<^sub>1\<langle>t\<^sub>2'\<rangle> s\<^sub>1')) (P\<^sub>1' + P\<^sub>2'))"
        using superpositionI(12) is_ground_P\<^sub>1' is_ground_P\<^sub>2' \<P>_ground
        by simp

      show "C = add_mset 
                  (\<P>' (Upair (gctxt_of_ctxt s\<^sub>1)\<langle>gterm_of_term t\<^sub>2'\<rangle>\<^sub>G (gterm_of_term s\<^sub>1'))) 
                  (gcls_cls P\<^sub>1' + gcls_cls P\<^sub>2')"
        using 
          superpositionI(12, 17)
          glit_lit_with_context[OF is_ground_s\<^sub>1 is_ground_t\<^sub>2' is_ground_s\<^sub>1']
          convert_add_mset[of C  "\<P> (Upair s\<^sub>1\<langle>t\<^sub>2'\<rangle> s\<^sub>1')" "(P\<^sub>1' + P\<^sub>2')"]
        unfolding 
          \<P>' 
          subst_cls_ident_if_is_ground_cls[OF is_ground_P\<^sub>1']
          subst_cls_ident_if_is_ground_cls[OF is_ground_P\<^sub>2']
          term_subst.subst_ident_if_ground[OF is_ground_t\<^sub>2'] 
          term_subst.subst_ident_if_ground[OF is_ground_s\<^sub>1'] 
          subst_trm_ctxt_ident_if_is_ground_ctxt[OF is_ground_s\<^sub>1]
          subst_cls_ident_if_is_ground_cls[OF ground_cls]
        by auto
      qed
    qed
next
  assume "G.ground_superposition P1 P2 C"
  thus "superposition (cls_gcls P1) (cls_gcls P2) (cls_gcls C)"
  proof(cases rule: G.ground_superposition.cases)
    case (ground_superpositionI L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' \<P> s t s' t')

    obtain \<P>' :: "('f, 'v) term uprod \<Rightarrow> ('f, 'v) term uprod literal" 
      where \<P>': "\<P>' = (if \<P> = Pos then Pos else Neg)"
      by simp

    have \<P>'_pos_or_neg: "\<P>' = Neg \<or> \<P>' = Pos"
      using ground_superpositionI(4)
      unfolding \<P>' lit_glit_def
      by simp

    show ?thesis
    proof(rule superpositionI)
      show "term_subst.is_renaming Var"
        by simp
    next
      show "term_subst.is_renaming Var"
        by simp
    next
      show "vars_cls (cls_gcls P1 \<cdot> Var) \<inter> vars_cls (cls_gcls P2 \<cdot> Var) = {}"
        by simp
    next
      show "cls_gcls P1 = add_mset (lit_glit L\<^sub>1) (cls_gcls P\<^sub>1')"
        by (simp add: cls_gcls_def ground_superpositionI(1))
    next
      show "cls_gcls P2 = add_mset (lit_glit L\<^sub>2) (cls_gcls P\<^sub>2')"
        by (simp add: cls_gcls_def ground_superpositionI(2))
    next
      show "\<P>' \<in> {Pos, Neg}"
        using \<P>'_pos_or_neg by auto
    next
      show "lit_glit L\<^sub>1 = \<P>' (Upair (ctxt_of_gctxt s) \<langle>term_of_gterm t\<rangle> (term_of_gterm s'))"
        using ground_superpositionI(5, 9) lit_glit_with_context
        unfolding \<P>'
        by auto
    next
      show "lit_glit L\<^sub>2 = (term_of_gterm t) \<approx> (term_of_gterm t')"
        by (simp add: ground_superpositionI(6) lit_glit_def)
    next 
      show "is_Fun (term_of_gterm t)"
        by (rule gterm_is_fun)
    next
      show "term_subst.is_imgu Var {{term_of_gterm t \<cdot>t Var, term_of_gterm t \<cdot>t Var}}"
        by simp
    next
      show " \<not> (\<prec>\<^sub>c)\<^sup>=\<^sup>= (cls_gcls P1 \<cdot> Var \<cdot> Var) (cls_gcls P2 \<cdot> Var \<cdot> Var)"
        using ground_superpositionI(3)
        unfolding
          subst_cls_Var_ident
          not_less_eq_cls[OF is_ground_cls_gcls is_ground_cls_gcls]
          less_cls_iff_less_gcls.
    next 
      show 
          "\<P>' = Pos 
            \<and> select (cls_gcls P1) = {#} 
            \<and> is_strictly_maximal_lit (lit_glit L\<^sub>1 \<cdot>l Var \<cdot>l Var) (cls_gcls P1 \<cdot> Var \<cdot> Var) 
         \<or> \<P>' = Neg 
            \<and> (select (cls_gcls P1) = {#} 
            \<and> is_maximal_lit (lit_glit L\<^sub>1 \<cdot>l Var \<cdot>l Var) (cls_gcls P1 \<cdot> Var \<cdot> Var) 
            \<or> lit_glit L\<^sub>1 \<in># select (cls_gcls P1))"
        proof(cases "\<P> = Pos")
          case True
          with ground_superpositionI(9) show ?thesis
            unfolding \<P>' select\<^sub>G_def gcls_cls_def
            using literals_distinct is_strictly_maximal_lit_iff_is_strictly_maximal_glit
            by auto
        next
          case False
          with ground_superpositionI(9) show ?thesis
            unfolding \<P>' select\<^sub>G_def gcls_cls_def
            using literals_distinct is_maximal_glit_iff_is_maximal_lit select_ground_lit
            by auto
        qed
    next
      show "select (cls_gcls P2) = {#}"
        using ground_superpositionI(10)
        unfolding gcls_cls_def select\<^sub>G_def
        by simp
    next
      show "is_strictly_maximal_lit (lit_glit L\<^sub>2 \<cdot>l Var \<cdot>l Var) (cls_gcls P2 \<cdot> Var \<cdot> Var)"
        using ground_superpositionI(11) is_strictly_maximal_lit_iff_is_strictly_maximal_glit
        by simp
    next
      show "\<not> (ctxt_of_gctxt s)\<langle>term_of_gterm t\<rangle> \<cdot>t Var \<cdot>t Var \<preceq>\<^sub>t term_of_gterm s' \<cdot>t Var \<cdot>t Var"
        using ground_superpositionI(7)  
        unfolding 
          term_subst.subst_id_subst 
          not_less_eq_term[OF vars_term_of_gterm vars_term_of_gterm]
          less_gterm_less_term
          context_ground_context.
    next
      show "\<not> term_of_gterm t \<cdot>t Var \<cdot>t Var \<preceq>\<^sub>t term_of_gterm t' \<cdot>t Var \<cdot>t Var"
        using ground_superpositionI(8)
        unfolding 
          term_subst.subst_id_subst 
          not_less_eq_term[OF vars_term_of_gterm vars_term_of_gterm]
          less_gterm_less_term.
    next
      show "cls_gcls C = add_mset 
            (\<P>' (Upair (ctxt_of_gctxt s \<cdot>t\<^sub>c Var)\<langle>term_of_gterm t' \<cdot>t Var\<rangle> (term_of_gterm s' \<cdot>t Var))) 
              (cls_gcls P\<^sub>1' \<cdot> Var + cls_gcls P\<^sub>2' \<cdot> Var) \<cdot> Var"
      proof(cases "\<P>' = Pos")
        case True
        then show ?thesis
          using ground_superpositionI(12) 
          unfolding \<P>'
          by(auto simp: cls_gcls_def lit_glit_with_context(1) split: if_splits)
      next
        case False
        then have "\<P> = Neg"
          using ground_superpositionI(4)
          unfolding \<P>'
          by auto
     
        then show ?thesis
          using ground_superpositionI(12)
          unfolding \<P>'
          by(auto simp:  cls_gcls_def lit_glit_with_context(2) split: if_splits)
      qed
    qed  
  qed
qed

subsubsection \<open>Alternative Specification of the Superposition Rule\<close>

inductive pos_superposition ::
  "('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool"
where
  pos_superpositionI: "
    term_subst.is_renaming \<rho>\<^sub>1 \<Longrightarrow>
    term_subst.is_renaming \<rho>\<^sub>2 \<Longrightarrow>
    vars_cls (P\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter> vars_cls (P\<^sub>2 \<cdot> \<rho>\<^sub>2) = {} \<Longrightarrow>
    P\<^sub>1 = add_mset L\<^sub>1 P\<^sub>1' \<Longrightarrow>
    P\<^sub>2 = add_mset L\<^sub>2 P\<^sub>2' \<Longrightarrow>
    L\<^sub>1 = (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<approx> s\<^sub>1') \<Longrightarrow>
    L\<^sub>2 = (t\<^sub>2 \<approx> t\<^sub>2') \<Longrightarrow>
    \<not> is_Var u\<^sub>1 \<Longrightarrow>
    term_subst.is_imgu \<mu> {{u\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}} \<Longrightarrow>
    \<not> (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<preceq>\<^sub>c P\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    select P\<^sub>1 = {#} \<Longrightarrow>
    is_strictly_maximal_lit (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>) \<Longrightarrow>
    select P\<^sub>2 = {#} \<Longrightarrow>
    is_strictly_maximal_lit (L\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu>) (P\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    \<not> (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu>) \<Longrightarrow>
    \<not> (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<preceq>\<^sub>t t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu>) \<Longrightarrow>
    C = add_mset ((s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> \<approx> s\<^sub>1' \<cdot>t \<rho>\<^sub>1) (P\<^sub>1' \<cdot> \<rho>\<^sub>1 + P\<^sub>2' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu> \<Longrightarrow>
    pos_superposition P\<^sub>1 P\<^sub>2 C"

lemma superposition_if_pos_superposition:
  assumes "pos_superposition P\<^sub>1 P\<^sub>2 C"
  shows "superposition P\<^sub>1 P\<^sub>2 C"
  using assms
proof (cases P\<^sub>1 P\<^sub>2 C rule: pos_superposition.cases)
  case (pos_superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)
  then show ?thesis
    using superpositionI
    by simp
qed

inductive neg_superposition ::
  "('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool"
where
  neg_superpositionI: "
    term_subst.is_renaming \<rho>\<^sub>1 \<Longrightarrow>
    term_subst.is_renaming \<rho>\<^sub>2 \<Longrightarrow>
    vars_cls (P\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter> vars_cls (P\<^sub>2 \<cdot> \<rho>\<^sub>2) = {} \<Longrightarrow>
    P\<^sub>1 = add_mset L\<^sub>1 P\<^sub>1' \<Longrightarrow>
    P\<^sub>2 = add_mset L\<^sub>2 P\<^sub>2' \<Longrightarrow>
    L\<^sub>1 = Neg (Upair s\<^sub>1\<langle>u\<^sub>1\<rangle> s\<^sub>1') \<Longrightarrow>
    L\<^sub>2 = (t\<^sub>2 \<approx> t\<^sub>2') \<Longrightarrow>
    \<not> is_Var u\<^sub>1 \<Longrightarrow>
    term_subst.is_imgu \<mu> {{u\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}} \<Longrightarrow>
    \<not> (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<preceq>\<^sub>c P\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    select P\<^sub>1 = {#} \<and> is_maximal_lit (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>) \<or> L\<^sub>1 \<in># select P\<^sub>1 \<Longrightarrow>
    select P\<^sub>2 = {#} \<Longrightarrow>
    is_strictly_maximal_lit (L\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu>) (P\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    \<not> (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu>) \<Longrightarrow>
    \<not> (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<preceq>\<^sub>t t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu>) \<Longrightarrow>
    C = add_mset (Neg (Upair (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle>  (s\<^sub>1' \<cdot>t \<rho>\<^sub>1))) (P\<^sub>1' \<cdot> \<rho>\<^sub>1 + P\<^sub>2' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu> \<Longrightarrow>
    neg_superposition P\<^sub>1 P\<^sub>2 C"

lemma superposition_if_neg_superposition:
  assumes "neg_superposition P\<^sub>1 P\<^sub>2 C"
  shows "superposition P\<^sub>1 P\<^sub>2 C"
  using assms
proof (cases P\<^sub>1 P\<^sub>2 C rule: neg_superposition.cases)
  case (neg_superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)
  then show ?thesis
    using superpositionI
    by simp
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

definition F_Inf :: "('f, 'v) atom clause inference set" where
  "F_Inf \<equiv> 
    {Infer [P\<^sub>2, P\<^sub>1] C | P\<^sub>2 P\<^sub>1 C. superposition P\<^sub>1 P\<^sub>2 C} \<union>
    {Infer [P] C | P C. eq_resolution P C} \<union>
    {Infer [P] C | P C. eq_factoring P C}"

abbreviation F_Bot :: "('f, 'v) atom clause set" where
  "F_Bot \<equiv> {{#}}"

abbreviation true_cls_thick :: 
  "'f ground_atom interp \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool" (infix "\<TTurnstile>n" 50) where
  "I \<TTurnstile>n C \<equiv> \<forall>\<theta>. term_subst.is_ground_subst \<theta> \<longrightarrow> I \<TTurnstile> gcls_cls (C \<cdot> \<theta>)"

abbreviation true_clss_thick :: 
  "'f ground_atom interp \<Rightarrow> ('f, 'v) atom clause set \<Rightarrow> bool" (infix "\<TTurnstile>sn" 50) where
  "I \<TTurnstile>sn \<C> \<equiv> \<forall>C\<in> \<C>. I \<TTurnstile>n C"

definition F_entails :: "('f, 'v) atom clause set \<Rightarrow> ('f, 'v) atom clause set \<Rightarrow> bool" where
  "F_entails N\<^sub>1 N\<^sub>2 \<longleftrightarrow> (\<forall>(I :: 'f gterm rel). 
    refl I \<longrightarrow> trans I \<longrightarrow> sym I \<longrightarrow> compatible_with_gctxt I \<longrightarrow>
    (\<lambda>(t\<^sub>1, t\<^sub>2). Upair t\<^sub>1 t\<^sub>2) ` I \<TTurnstile>sn N\<^sub>1 \<longrightarrow>
    (\<lambda>(t\<^sub>1, t\<^sub>2). Upair t\<^sub>1 t\<^sub>2) ` I \<TTurnstile>sn N\<^sub>2)"
 
lemma correctness_eq_resolution:
  assumes
    step: "eq_resolution P C"
  shows "F_entails {P} {C}"
  using step
proof (cases P C rule: eq_resolution.cases)
  case (eq_resolutionI L P' s\<^sub>1 s\<^sub>2 \<mu>)
  have 
    "\<And>I \<theta>. \<lbrakk>
        refl I; 
        \<forall>\<sigma>. term_subst.is_ground_subst \<sigma> \<longrightarrow> (\<lambda>(x, y). Upair x y) ` I \<TTurnstile> gcls_cls (P \<cdot> \<sigma>); 
        term_subst.is_ground_subst \<theta>
     \<rbrakk> \<Longrightarrow> (\<lambda>(x, y). Upair x y) ` I \<TTurnstile> gcls_cls (C \<cdot> \<theta>)"
  proof-
    fix I :: "'f gterm rel" and \<theta> :: "'v \<Rightarrow> ('f, 'v) Term.term"
    let ?I = "(\<lambda>(x, y). Upair x y) ` I"
    let ?P = "gcls_cls (P \<cdot> \<mu> \<cdot> \<theta>)"
    let ?L = "glit_lit (L \<cdot>l \<mu> \<cdot>l \<theta>)"
    let ?P' = "gcls_cls (P' \<cdot> \<mu> \<cdot> \<theta>)"
    let ?s\<^sub>1 = "gterm_of_term (s\<^sub>1 \<cdot>t \<mu> \<cdot>t \<theta>)"
    let ?s\<^sub>2 = "gterm_of_term (s\<^sub>2 \<cdot>t \<mu> \<cdot>t \<theta>)"

     assume 
       ground_subst: "term_subst.is_ground_subst \<theta>" and 
       refl_I: "refl I" and 
       premise: "\<forall>\<sigma>. term_subst.is_ground_subst \<sigma> \<longrightarrow> ?I \<TTurnstile> gcls_cls (P \<cdot> \<sigma>)"

     have "?I \<TTurnstile> ?P"
       using 
         premise[rule_format, of "\<mu> \<odot> \<theta>", OF ground_subst_composition[OF ground_subst]]
         clause_subst_compose
       by metis
      
     then obtain L' where L'_in_P: "L' \<in># ?P" and I_models_L': "?I \<TTurnstile>l L'"
       by (auto simp: true_cls_def)

     have [simp]: "?P = add_mset ?L ?P'"
       by (simp add: gcls_cls_def local.eq_resolutionI(1) subst_cls_add_mset)

     have [simp]: "?L = (Neg (Upair ?s\<^sub>1 ?s\<^sub>2))"
       unfolding glit_lit_def eq_resolutionI(2)
       by (simp add: subst_atm_def subst_lit_Neg)
       
     have [simp]: "?s\<^sub>1 = ?s\<^sub>2"
       using is_imgu_equals[OF eq_resolutionI(3)] by simp
      
     have "is_neg ?L"
       by (simp add: glit_lit_def eq_resolutionI(2) subst_lit_Neg)

     show "?I \<TTurnstile> gcls_cls (C \<cdot> \<theta>)"
      proof(cases "L' = ?L")
       case True
   
       then have "?I \<TTurnstile>l (Neg (atm_of ?L))"
         using I_models_L' by simp
  
       moreover have "atm_of L' \<in> ?I"
         using True reflD[OF refl_I, of ?s\<^sub>1] by auto
  
       ultimately show ?thesis
         using True by blast
     next
       case False
       then have "L' \<in># gcls_cls (P' \<cdot> \<mu> \<cdot> \<theta>)"
         using L'_in_P by force
  
       then have "L' \<in># gcls_cls (C \<cdot> \<theta>)"
         unfolding eq_resolutionI.
  
       then show ?thesis
         using I_models_L' by blast
     qed
   qed

  then show ?thesis 
    unfolding true_clss_singleton F_entails_def 
    by simp
qed

lemma correctness_eq_factoring:
  assumes step: "eq_factoring P C"
  shows "F_entails {P} {C}"
  using step
proof (cases P C rule: eq_factoring.cases)
  case (eq_factoringI L\<^sub>1 L\<^sub>2 P' s\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)
  have 
    "\<And>I \<theta>. \<lbrakk>
        trans I; 
        sym I;
        \<forall>\<sigma>. term_subst.is_ground_subst \<sigma> \<longrightarrow> (\<lambda>(x, y). Upair x y) ` I \<TTurnstile> gcls_cls (P \<cdot> \<sigma>); 
        term_subst.is_ground_subst \<theta>
     \<rbrakk> \<Longrightarrow> (\<lambda>(x, y). Upair x y) ` I \<TTurnstile> gcls_cls (C \<cdot> \<theta>)"
  proof-
    fix I :: "'f gterm rel" and \<theta> :: "'v \<Rightarrow> ('f, 'v) Term.term"
    let ?I = "(\<lambda>(x, y). Upair x y) ` I"
    let ?P = "gcls_cls (P \<cdot> \<mu> \<cdot> \<theta>)"
    let ?P' = "gcls_cls (P' \<cdot> \<mu> \<cdot> \<theta>)"
    let ?L\<^sub>1 = "glit_lit (L\<^sub>1 \<cdot>l \<mu> \<cdot>l \<theta>)"
    let ?L\<^sub>2 = "glit_lit (L\<^sub>2 \<cdot>l \<mu> \<cdot>l \<theta>)"
    let ?s\<^sub>1 = "gterm_of_term (s\<^sub>1 \<cdot>t \<mu> \<cdot>t \<theta>)"
    let ?s\<^sub>1' = "gterm_of_term (s\<^sub>1' \<cdot>t \<mu> \<cdot>t \<theta>)"
    let ?t\<^sub>2 = "gterm_of_term (t\<^sub>2 \<cdot>t \<mu> \<cdot>t \<theta>)"
    let ?t\<^sub>2' = "gterm_of_term (t\<^sub>2' \<cdot>t \<mu> \<cdot>t \<theta>)"
    let ?C = "gcls_cls (C \<cdot> \<theta>)"

    assume 
      ground_subst: "term_subst.is_ground_subst \<theta>" and 
      trans_I: "trans I" and 
      sym_I: "sym I" and 
      premise: "\<forall>\<sigma>. term_subst.is_ground_subst \<sigma> \<longrightarrow> ?I \<TTurnstile> gcls_cls (P \<cdot> \<sigma>)"

    have "?I \<TTurnstile> ?P"
       using 
         premise[rule_format, of "\<mu> \<odot> \<theta>", OF ground_subst_composition[OF ground_subst]]
         clause_subst_compose
       by metis

    then obtain L' where L'_in_P: "L' \<in># ?P" and I_models_L': "?I \<TTurnstile>l L'"
      by (auto simp: true_cls_def)

    then have s\<^sub>1_equals_t\<^sub>2: "?t\<^sub>2 = ?s\<^sub>1"
      using is_imgu_equals[OF eq_factoringI(6)]
      by simp

    have L\<^sub>1: "?L\<^sub>1 = ?s\<^sub>1 \<approx> ?s\<^sub>1'"
      unfolding glit_lit_def eq_factoringI(2)
      by (simp add: subst_atm_def subst_lit_Pos)

    have L\<^sub>2: "?L\<^sub>2 = ?t\<^sub>2 \<approx> ?t\<^sub>2'"
      unfolding glit_lit_def eq_factoringI(3)
      by (simp add: subst_atm_def subst_lit_Pos)

    have C: "?C = add_mset (?s\<^sub>1 \<approx> ?t\<^sub>2') (add_mset (Neg (Upair ?s\<^sub>1' ?t\<^sub>2')) ?P')"
      unfolding eq_factoringI
      by (simp add: gcls_cls_def glit_lit_def subst_atm_def subst_cls_add_mset subst_lit_Neg 
            subst_lit_Pos)

    show "?I \<TTurnstile> ?C"
    proof(cases "L' = ?L\<^sub>1 \<or> L' = ?L\<^sub>2")
      case True
      then have "I \<TTurnstile>l Pos (?s\<^sub>1, ?s\<^sub>1') \<or> I \<TTurnstile>l Pos (?s\<^sub>1, ?t\<^sub>2')"
        using G.true_lit_uprod_iff_true_lit_prod[OF sym_I] I_models_L'
        by (metis L\<^sub>1 L\<^sub>2 s\<^sub>1_equals_t\<^sub>2)

      then have "I \<TTurnstile>l Pos (?s\<^sub>1, ?t\<^sub>2') \<or> I \<TTurnstile>l Neg (?s\<^sub>1', ?t\<^sub>2')"
        by (meson transD trans_I true_lit_simps(1) true_lit_simps(2))

      then have "?I \<TTurnstile>l ?s\<^sub>1 \<approx> ?t\<^sub>2' \<or> ?I \<TTurnstile>l Neg (Upair ?s\<^sub>1' ?t\<^sub>2')"
        unfolding G.true_lit_uprod_iff_true_lit_prod[OF sym_I].

      then show ?thesis
        unfolding C
        by (metis true_cls_add_mset)
    next
      case False
      then have "L' \<in># ?P'"
        using L'_in_P
        unfolding eq_factoringI
        by (simp add: gcls_cls_def subst_cls_add_mset)

      then have "L' \<in># gcls_cls (C \<cdot> \<theta>)"
        by (simp add: gcls_cls_def eq_factoringI(7) subst_cls_add_mset)

      then show ?thesis
        using I_models_L' by blast
    qed
  qed

  then show ?thesis
    unfolding true_clss_singleton F_entails_def 
    by simp
qed

lemma correctness_superposition:
  assumes
    step: "superposition P1 P2 C"
  shows "F_entails {P1, P2} {C}"
  using step
proof (cases P1 P2 C rule: superposition.cases)
  case (superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' \<P> s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)

  have 
    "\<And>I \<theta>. \<lbrakk>
        refl I;
        trans I; 
        sym I;
        compatible_with_gctxt I;
        \<forall>\<sigma>. term_subst.is_ground_subst \<sigma> \<longrightarrow> (\<lambda>(x, y). Upair x y) ` I \<TTurnstile> gcls_cls (P1 \<cdot> \<sigma>);
        \<forall>\<sigma>. term_subst.is_ground_subst \<sigma> \<longrightarrow> (\<lambda>(x, y). Upair x y) ` I \<TTurnstile> gcls_cls (P2 \<cdot> \<sigma>); 
        term_subst.is_ground_subst \<theta>
     \<rbrakk> \<Longrightarrow> (\<lambda>(x, y). Upair x y) ` I \<TTurnstile> gcls_cls (C \<cdot> \<theta>)"
  proof -
    fix I :: "'f gterm rel" and \<theta> :: "'v \<Rightarrow> ('f, 'v) Term.term"

    let ?I = "(\<lambda>(x, y). Upair x y) ` I"

    let ?P1 = "gcls_cls (P1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<cdot> \<theta>)"
    let ?P2 = "gcls_cls (P2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu> \<cdot> \<theta>)"

    let ?L\<^sub>1 = "glit_lit (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu> \<cdot>l \<theta>)"
    let ?L\<^sub>2 = "glit_lit (L\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu> \<cdot>l \<theta>)"

    let ?P\<^sub>1' = "gcls_cls (P\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<cdot> \<theta>)"
    let ?P\<^sub>2' = "gcls_cls (P\<^sub>2' \<cdot> \<rho>\<^sub>2 \<cdot> \<mu> \<cdot> \<theta>)"

    let ?s\<^sub>1 = "gctxt_of_ctxt (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<mu> \<cdot>t\<^sub>c \<theta>)"
    let ?s\<^sub>1' = "gterm_of_term (s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<theta>)"
    let ?t\<^sub>2 = "gterm_of_term (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<theta>)"
    let ?t\<^sub>2' = "gterm_of_term (t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<theta>)"
    let ?u\<^sub>1 = "gterm_of_term (u\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<theta>)"

    let ?\<P> = "if \<P> = Pos then Pos else Neg"

    let ?C = "gcls_cls (C \<cdot> \<theta>)"

    assume 
      ground_subst: "term_subst.is_ground_subst \<theta>" and 
      refl_I: "refl I" and 
      trans_I: "trans I" and 
      sym_I: "sym I" and 
      compatible_with_ground_context_I: "compatible_with_gctxt I" and
      premise1: "\<forall>\<sigma>. term_subst.is_ground_subst \<sigma> \<longrightarrow> ?I \<TTurnstile> gcls_cls (P1 \<cdot> \<sigma>)" and
      premise2: "\<forall>\<sigma>. term_subst.is_ground_subst \<sigma> \<longrightarrow> ?I \<TTurnstile> gcls_cls (P2 \<cdot> \<sigma>)"

    have "?I \<TTurnstile> ?P1"
      using 
         premise1[rule_format, of "\<rho>\<^sub>1 \<odot> \<mu> \<odot> \<theta>", OF ground_subst_composition[OF ground_subst]]
         clause_subst_compose
      by metis

    moreover have "?I \<TTurnstile> ?P2"
      using 
         premise2[rule_format, of "\<rho>\<^sub>2 \<odot> \<mu> \<odot> \<theta>", OF ground_subst_composition[OF ground_subst]]
         clause_subst_compose
      by metis

    ultimately obtain L\<^sub>1' L\<^sub>2' 
      where
        L\<^sub>1'_in_P1: "L\<^sub>1' \<in># ?P1" and 
        I_models_L\<^sub>1': "?I \<TTurnstile>l L\<^sub>1'" and
        L\<^sub>2'_in_P2: "L\<^sub>2' \<in># ?P2" and 
        I_models_L\<^sub>2': "?I \<TTurnstile>l L\<^sub>2'"
      by (auto simp: true_cls_def)

    have u\<^sub>1_equals_t\<^sub>2: "?t\<^sub>2 = ?u\<^sub>1"
      using is_imgu_equals[OF superpositionI(10)]
      by simp

    have s\<^sub>1_u\<^sub>1: "?s\<^sub>1\<langle>?u\<^sub>1\<rangle>\<^sub>G = gterm_of_term (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<mu> \<cdot>t\<^sub>c \<theta>)\<langle>u\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<theta>\<rangle>"
      using gterm_of_term_gctxt_of_ctxt[OF 
              is_ground_subst_is_ground_context[OF ground_subst] 
              is_ground_subst_is_ground_term[OF ground_subst]
            ]
      by simp

    have s\<^sub>1_t\<^sub>2': "(?s\<^sub>1)\<langle>?t\<^sub>2'\<rangle>\<^sub>G  = gterm_of_term (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<mu> \<cdot>t\<^sub>c \<theta>)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<theta>\<rangle>"
      using gterm_of_term_gctxt_of_ctxt[OF 
              is_ground_subst_is_ground_context[OF ground_subst] 
              is_ground_subst_is_ground_term[OF ground_subst]
            ]
      by simp
      
    have \<P>_pos_or_neg: "\<P> = Pos \<or> \<P> = Neg"
      using superpositionI(6) by blast

    then have L\<^sub>1: "?L\<^sub>1 = ?\<P> (Upair ?s\<^sub>1\<langle>?u\<^sub>1\<rangle>\<^sub>G ?s\<^sub>1')"
      unfolding superpositionI glit_lit_def 
      by(auto simp: subst_atm_def subst_lit_Pos subst_lit_Neg s\<^sub>1_u\<^sub>1)
    
    have C: "?C = add_mset (?\<P> (Upair (?s\<^sub>1)\<langle>?t\<^sub>2'\<rangle>\<^sub>G (?s\<^sub>1'))) (?P\<^sub>1' + ?P\<^sub>2')"
      using \<P>_pos_or_neg
      unfolding s\<^sub>1_t\<^sub>2' superpositionI
      apply(cases "\<P> = Pos")
      by (simp_all add: gcls_cls_def glit_lit_def subst_atm_def subst_cls_add_mset subst_cls_plus 
              subst_lit_Pos subst_lit_Neg)

    show "?I \<TTurnstile> ?C"
    proof (cases "L\<^sub>1' = ?L\<^sub>1")
      case L\<^sub>1'_def: True
      then have "?I \<TTurnstile>l ?L\<^sub>1"
        using superpositionI
        using I_models_L\<^sub>1' by blast

      show ?thesis
      proof (cases "L\<^sub>2' = ?L\<^sub>2")
        case L\<^sub>2'_def: True
        then have ts_in_I: "(?t\<^sub>2, ?t\<^sub>2') \<in> I"
          using I_models_L\<^sub>2' G.true_lit_uprod_iff_true_lit_prod[OF sym_I] superpositionI(8)
          by (simp add: glit_lit_def subst_atm_def subst_lit_Pos)

        have ?thesis if "\<P> = Pos"
        proof -
          from that have "(?s\<^sub>1\<langle>?t\<^sub>2\<rangle>\<^sub>G, ?s\<^sub>1') \<in> I"
            using I_models_L\<^sub>1' L\<^sub>1'_def L\<^sub>1 G.true_lit_uprod_iff_true_lit_prod[OF sym_I] u\<^sub>1_equals_t\<^sub>2
            unfolding superpositionI 
            by (smt (verit, best) true_lit_simps(1))

          then have "(?s\<^sub>1\<langle>?t\<^sub>2'\<rangle>\<^sub>G, ?s\<^sub>1') \<in> I"
            using ts_in_I compatible_with_ground_context_I refl_I sym_I trans_I
            by (meson compatible_with_gctxtD refl_onD1 symD trans_onD)
          
          then have "?I \<TTurnstile>l ?s\<^sub>1\<langle>?t\<^sub>2'\<rangle>\<^sub>G  \<approx> ?s\<^sub>1'"
            by blast

          then show ?thesis 
            unfolding C that
            by (smt (verit) true_cls_add_mset)
        qed

        moreover have ?thesis if "\<P> = Neg"
        proof -
          from that have "(?s\<^sub>1\<langle>?t\<^sub>2\<rangle>\<^sub>G, ?s\<^sub>1') \<notin> I"
            using I_models_L\<^sub>1' L\<^sub>1'_def L\<^sub>1 G.true_lit_uprod_iff_true_lit_prod[OF sym_I] u\<^sub>1_equals_t\<^sub>2
            unfolding superpositionI 
            by (smt (verit, ccfv_threshold) literals_distinct(2) true_lit_simps(2))
        
          then have "(?s\<^sub>1\<langle>?t\<^sub>2'\<rangle>\<^sub>G, ?s\<^sub>1') \<notin> I"
            using ts_in_I compatible_with_ground_context_I trans_I
            by (meson compatible_with_gctxtD transD)

          then have "?I \<TTurnstile>l Neg (Upair ?s\<^sub>1\<langle>?t\<^sub>2'\<rangle>\<^sub>G  ?s\<^sub>1')"
            by (meson G.true_lit_uprod_iff_true_lit_prod(2) sym_I true_lit_simps(2))

          then show ?thesis 
            unfolding C that
            by (smt (verit, best) literals_distinct(1) true_cls_add_mset)
        qed

        ultimately show ?thesis
          using \<P>_pos_or_neg by blast
      next
        case False
        then have "L\<^sub>2' \<in># ?P\<^sub>2'"
          using L\<^sub>2'_in_P2
          unfolding superpositionI
          by (simp add: gcls_cls_def subst_cls_add_mset)

        then have "?I \<TTurnstile> ?P\<^sub>2'"
          using I_models_L\<^sub>2' by blast

        then show ?thesis
          unfolding superpositionI
          by (simp add: gcls_cls_def subst_cls_add_mset subst_cls_plus)
      qed
    next
      case False
      then have "L\<^sub>1' \<in># ?P\<^sub>1'"
        using L\<^sub>1'_in_P1
        unfolding superpositionI 
        by (simp add: gcls_cls_def subst_cls_add_mset)

      then have "?I \<TTurnstile> ?P\<^sub>1'"
        using I_models_L\<^sub>1' by blast

      then show ?thesis 
        unfolding superpositionI
        by (simp add: gcls_cls_def subst_cls_add_mset subst_cls_plus)
    qed
  qed

  then show ?thesis 
    unfolding true_clss_singleton true_clss_insert F_entails_def
    by simp
qed

definition ginfer_infer :: 
  "('f, 'v) atom clause inference \<Rightarrow> 'f ground_atom clause inference" 
  where
  "ginfer_infer infer = Infer (map gcls_cls (prems_of infer)) (gcls_cls (concl_of infer))"

definition infer_ginfer :: 
  "'f ground_atom clause inference \<Rightarrow> ('f, 'v) atom clause inference" 
  where
  "infer_ginfer infer = Infer (map cls_gcls (prems_of infer)) (cls_gcls (concl_of infer))"

definition is_ground_subst_list :: "('f, 'v) subst list \<Rightarrow> bool" where
  "is_ground_subst_list \<sigma>s \<longleftrightarrow> (\<forall>\<sigma> \<in> set \<sigma>s. term_subst.is_ground_subst \<sigma>)"

definition \<G>_F :: 
  "('f, 'v) atom clause \<Rightarrow> 'f ground_atom clause set" 
  where
  "\<G>_F C \<equiv> { gcls_cls (C \<cdot> \<sigma>) | \<sigma>. term_subst.is_ground_subst \<sigma> }"

definition \<G>_I :: 
  "('f, 'v) atom clause inference \<Rightarrow> 'f ground_atom clause inference set option" 
  where
  "\<G>_I \<iota> = Some ({ginfer_infer (Infer (prems_of \<iota> \<cdot>\<cdot>cl \<rho>s) (concl_of \<iota> \<cdot> \<rho>)) |\<rho> \<rho>s.
     is_ground_subst_list \<rho>s \<and> term_subst.is_ground_subst \<rho>
     \<and> ginfer_infer (Infer (prems_of \<iota> \<cdot>\<cdot>cl \<rho>s) (concl_of \<iota> \<cdot> \<rho>)) \<in> G.G_Inf})"


definition Prec_F :: 
  "'f ground_atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool" 
  where
  "Prec_F \<equiv> \<lambda>_ _ _. False"

interpretation F: sound_inference_system F_Inf F_Bot F_entails
proof unfold_locales
  show "\<And>\<iota>. \<iota> \<in> F_Inf \<Longrightarrow> F_entails (set (prems_of \<iota>)) {concl_of \<iota>}"
    using 
      F_Inf_def 
      correctness_eq_factoring 
      correctness_eq_resolution 
      correctness_superposition
      F_entails_def
    by auto
next 
  show "F_Bot \<noteq> {}"
    by simp
next 
  have "\<And>\<theta> I. 
    term_subst.is_ground_subst \<theta> \<Longrightarrow> 
    (\<lambda>(x, y). Upair x y) ` I \<TTurnstile> gcls_cls ({#} \<cdot> \<theta>) \<Longrightarrow> False"
    by (metis cls_gcls_empty_mset cls_gcls_inverse image_mset_is_empty_iff subst_cls_def 
          true_cls_empty)

  then show "\<And>B N1. B \<in> F_Bot \<Longrightarrow> F_entails {B} N1"
    unfolding true_clss_singleton F_entails_def
    by fastforce
next
  show "\<And>N2 N1. N2 \<subseteq> N1 \<Longrightarrow> F_entails N1 N2"
    by (auto simp: F_entails_def elim!: true_clss_mono[rotated])
next
  show "\<And>N2 N1. \<forall>C\<in>N2. F_entails N1 {C} \<Longrightarrow> F_entails N1 N2"
    unfolding F_entails_def
    by blast
next
  show "\<And>N1 N2 N3. \<lbrakk>F_entails N1 N2; F_entails N2 N3\<rbrakk> \<Longrightarrow> F_entails N1 N3 "
    using F_entails_def 
    by (smt (verit, best))
qed
  
(* Q = gs(S) 
  q = T
*)

interpretation F: lifting_intersection F_Inf G.G_Bot "UNIV" "\<lambda> _. G.G_Inf"
  "\<lambda>_. G.G_entails" "\<lambda>_. G.Red_I" "\<lambda>_. G.Red_F" F_Bot "\<lambda>_.  \<G>_F" "\<lambda>_. \<G>_I" Prec_F
proof unfold_locales
  show "UNIV \<noteq> {}"
    by simp
next 
  have "consequence_relation G.G_Bot G.G_entails"
    apply unfold_locales
    apply auto
    using G.G_entails_def apply blast
    unfolding G.G_entails_def
    using subset_entailed apply auto
    by (simp add: true_clss_def)

  then show "\<forall>q\<in>UNIV. consequence_relation G.G_Bot G.G_entails"
    ..
next
  show  "\<forall>q\<in>UNIV. tiebreaker_lifting F_Bot F_Inf G.G_Bot G.G_entails G.G_Inf G.Red_I G.Red_F \<G>_F \<G>_I Prec_F"
    sorry
qed

(*
interpretation F: statically_complete_calculus F_Bot F_Inf "F.entails_\<G>" F.Red_I_\<G> F.Red_F_\<G>
proof unfold_locales
  show "\<And>B N. B \<in> F_Bot \<Longrightarrow> F.saturated N \<Longrightarrow> F.entails_\<G> N {B} \<Longrightarrow> \<exists>B' \<in> F_Bot. B' \<in> N"
    sorry
qed *)

end

end