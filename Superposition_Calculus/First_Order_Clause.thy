theory First_Order_Clause
  imports 
    (* TODO: Factor out Ground_Clause *)
    Ground_Superposition
    Abstract_Substitution_Extra_First_Order_Term
    Clausal_Calculus_Extra
    Term_Extra
begin

no_notation subst_compose (infixl "\<circ>\<^sub>s" 75)
no_notation subst_apply_term (infixl "\<cdot>" 67)

text \<open>Prefer @{thm [source] term_subst.subst_id_subst} to @{thm [source] subst_apply_term_empty}.\<close>
declare subst_apply_term_empty[no_atp]

section \<open>First_Order_Terms And Abstract_Substitution\<close>

notation subst_apply_term (infixl "\<cdot>t" 67)
notation subst_apply_ctxt (infixl "\<cdot>t\<^sub>c" 67)
notation subst_compose (infixl "\<odot>" 75)

type_synonym ('f, 'v) atom = "('f, 'v) term uprod"

(* 
  TODO:
  What would be the problem to simply restrict first order terms to get ground_terms?
  We could use a quotient_type?
*)
type_synonym 'f ground_atom = "'f Ground_Superposition.atom"

(* This is an example where type-classes would be nice, but the Isabelle ones are shitty...*)
definition subst_atom ::
  "('f, 'v) atom \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) atom" (infixl "\<cdot>a" 67)
where
  "subst_atom A \<sigma> = map_uprod (\<lambda>t. subst_apply_term t \<sigma>) A"

definition subst_literal ::
  "('f, 'v) atom literal \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) atom literal" (infixl "\<cdot>l" 67)
where
  "subst_literal literal \<sigma> = map_literal (\<lambda>atom. atom \<cdot>a \<sigma>) literal"

definition subst_clause ::
  "('f, 'v) atom clause \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) atom clause" (infixl "\<cdot>" 67)
where
  "subst_clause clause \<sigma> = image_mset (\<lambda>literal. literal \<cdot>l \<sigma>) clause"

lemma subst_atom_Var_ident[simp]: "atom \<cdot>a Var = atom"
  unfolding subst_atom_def
  by (simp add: uprod.map_ident)

lemma subst_literal_Var_ident[simp]: "literal \<cdot>l Var = literal"
  unfolding subst_literal_def
  by (simp add: literal.map_ident)

lemma subst_clause_Var_ident[simp]: "clause \<cdot> Var = clause"
  unfolding subst_clause_def
  by simp

(*
TODO: Needed?

definition subst_clauses ::
  "('f, 'v) atom clause list \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) atom clause list" (infixl "\<cdot>cl" 67) where
  "Cs \<cdot>cl \<sigma> = map (\<lambda>A. A \<cdot> \<sigma>) Cs"

definition subst_cls_lists :: 
  "('f, 'v) atom clause list \<Rightarrow> ('f, 'v) subst list \<Rightarrow>('f, 'v) atom clause list" (infixl "\<cdot>\<cdot>cl" 67) 
where
  "Cs \<cdot>\<cdot>cl \<sigma>s = map2 (\<cdot>) Cs \<sigma>s"
*)

(* This is an example where type-classes would be nice, but the Isabelle ones are shitty...*)
definition vars_atom :: "('f, 'v) atom \<Rightarrow> 'v set" where
  "vars_atom atom = (\<Union>term \<in> set_uprod atom. vars_term term)"

definition vars_literal :: "('f, 'v) atom literal \<Rightarrow> 'v set" where
  "vars_literal literal = vars_atom (atm_of literal)"
                            
definition vars_clause :: "('f, 'v) atom clause \<Rightarrow> 'v set" where
  "vars_clause clause = (\<Union>literal \<in> set_mset clause. vars_literal literal)"

definition vars_clause_set :: "('f, 'v) atom clause set \<Rightarrow> 'v set" where
  "vars_clause_set clauses = (\<Union>clause \<in> clauses. vars_clause clause)"
  
lemma vars_literal[simp]: 
  "vars_literal (Pos atom) = vars_atom atom"
  "vars_literal (Neg atom) = vars_atom atom"
  by (simp_all add: vars_literal_def)

lemma vars_literal_split[simp]: "vars_literal (term\<^sub>1 \<approx> term\<^sub>2) = vars_term term\<^sub>1 \<union> vars_term term\<^sub>2"
  unfolding vars_literal_def vars_atom_def
  by simp

lemma vars_clause_add_mset[simp]: 
  "vars_clause (add_mset literal clause) = vars_literal literal \<union> vars_clause clause"
  by (simp add: vars_clause_def)
                                              
lemma vars_clause_plus[simp]: 
  "vars_clause (clause\<^sub>1 + clause\<^sub>2) = vars_clause clause\<^sub>1 \<union> vars_clause clause\<^sub>2"
  by (simp add: vars_clause_def)

lemma atom_subst_compose [simp]: "atom \<cdot>a \<mu> \<odot> \<theta> = atom \<cdot>a \<mu> \<cdot>a \<theta>"
  unfolding subst_atom_def subst_subst_compose
  by (metis (no_types, lifting) map_uprod_simps uprod_exhaust)

lemma literal_subst_compose [simp]: "literal \<cdot>l \<mu> \<odot> \<theta> = literal \<cdot>l \<mu> \<cdot>l \<theta>"
  unfolding subst_literal_def 
  by(simp add: map_literal_comp) 

lemma clause_subst_compose [simp]: "clause \<cdot> \<mu> \<odot> \<theta> = clause \<cdot> \<mu> \<cdot> \<theta>"
  unfolding subst_clause_def
  by simp

lemma ground_subst_compose: 
  "term_subst.is_ground_subst \<theta> \<Longrightarrow> term_subst.is_ground_subst (\<mu> \<odot> \<theta>)"
  by (simp add: term_subst.is_ground_subst_def)

abbreviation is_ground_term where 
  "is_ground_term \<equiv> is_ground_trm"

hide_const is_ground_trm

abbreviation is_ground_context where
  "is_ground_context context \<equiv> vars_ctxt context = {}"

abbreviation is_ground_atom where
  "is_ground_atom atom \<equiv> vars_atom atom = {}"
                           
abbreviation is_ground_literal where
  "is_ground_literal literal \<equiv> vars_literal literal = {}"

abbreviation is_ground_clause where
  "is_ground_clause clause \<equiv> vars_clause clause = {}"

(*
TODO: Needed?

abbreviation is_ground_clause_set where
  "is_ground_clause_set N \<equiv> vars_clause_set N = {}"

lemma is_ground_clause_if_in_ground_clause_set:
  "is_ground_clause_set N \<Longrightarrow> C \<in> N \<Longrightarrow> is_ground_clause C"
  by (simp add: vars_clause_set_def)
 *)

lemma is_ground_term_iff_term_context_ground [simp]: 
  "Term_Context.ground term = is_ground_term term"
  by(induction "term") auto

lemma is_ground_term_ctxt_iff_ground_ctxt [simp]: 
  "ground_ctxt context = is_ground_context context"
  by (induction "context") simp_all

lemma gterm_of_term_gctxt_of_ctxt:
  assumes  "is_ground_context context" "is_ground_term term"
  shows "(gctxt_of_ctxt context)\<langle>gterm_of_term term\<rangle>\<^sub>G = gterm_of_term context\<langle>term\<rangle>"
  using assms
  by simp

lemma subst_ground_context_ident[simp]: "is_ground_context context \<Longrightarrow> context \<cdot>t\<^sub>c \<sigma> = context"
  by (induction "context") (simp_all add: list.map_ident_strong)

lemma subst_ground_atom_ident[simp]: "is_ground_atom atom \<Longrightarrow> atom \<cdot>a \<sigma> = atom"
  by (simp add: subst_atom_def uprod.map_ident_strong vars_atom_def)

lemma subst_ground_literal_ident[simp]: "is_ground_literal literal \<Longrightarrow> literal \<cdot>l \<sigma> = literal"
  unfolding subst_literal_def vars_literal_def 
  by (simp add: literal.expand literal.map_sel)

lemma subst_ground_clause_ident[simp]: "is_ground_clause clause \<Longrightarrow> clause \<cdot> \<sigma> = clause"
  unfolding subst_clause_def vars_clause_def
  by simp

lemma subst_literal: 
  "Pos A \<cdot>l \<sigma> = Pos (A \<cdot>a \<sigma>)"
  "Neg A \<cdot>l \<sigma> = Neg (A \<cdot>a \<sigma>)"
  unfolding subst_literal_def
  by simp_all

lemma subst_cls_add_mset: "add_mset L C \<cdot> \<sigma> = add_mset (L \<cdot>l \<sigma>) (C \<cdot> \<sigma>)"
  unfolding subst_clause_def
  by simp

lemma subst_cls_plus: "(C\<^sub>1 + C\<^sub>2) \<cdot> \<sigma> = (C\<^sub>1 \<cdot> \<sigma>) + (C\<^sub>2 \<cdot> \<sigma>)"
  unfolding subst_clause_def
  by simp

lemma is_ground_subst_is_ground_term: "term_subst.is_ground_subst \<theta> \<Longrightarrow> is_ground_term (t \<cdot>t \<theta>)"
  unfolding term_subst.is_ground_subst_def
  by simp

lemma is_ground_subst_is_ground_atom: "term_subst.is_ground_subst \<theta> \<Longrightarrow> is_ground_atom (a \<cdot>a \<theta>)"
  unfolding vars_atom_def subst_atom_def
  using is_ground_subst_is_ground_term
  by (smt (verit, ccfv_threshold) Sup_bot_conv(1) imageE uprod.set_map)

lemma is_ground_subst_is_ground_literal: "term_subst.is_ground_subst \<theta> \<Longrightarrow> is_ground_literal (l \<cdot>l \<theta>)"
  unfolding subst_literal_def vars_literal_def
  using is_ground_subst_is_ground_atom
  by (metis literal.map_sel(1) literal.map_sel(2))

lemma is_ground_subst_is_ground_clause: "term_subst.is_ground_subst \<theta> \<Longrightarrow> is_ground_clause (P \<cdot> \<theta>)"
  unfolding subst_clause_def vars_clause_def
  using is_ground_subst_is_ground_literal
  by blast

lemma is_ground_subst_is_ground_context: 
  "term_subst.is_ground_subst \<theta> \<Longrightarrow> is_ground_context (c \<cdot>t\<^sub>c \<theta>)"
  unfolding term_subst.is_ground_subst_def
  by (metis subst_apply_term_ctxt_apply_distrib sup_bot.right_neutral vars_term_ctxt_apply)

lemma is_imgu_equals: "term_subst.is_imgu \<mu> {{t\<^sub>1, t\<^sub>2}} \<Longrightarrow> t\<^sub>1 \<cdot>t \<mu> = t\<^sub>2 \<cdot>t \<mu>"
  unfolding term_subst.is_imgu_def term_subst.is_unifiers_def  
  using term_subst.is_unifier_iff_if_finite[of "{t\<^sub>1, t\<^sub>2}"  \<mu>]
  by blast

definition atom_gatom where
  "atom_gatom = map_uprod term_of_gterm"

definition gatom_atom where
  "gatom_atom = map_uprod gterm_of_term"

definition lit_glit where
  "lit_glit = map_literal atom_gatom"

definition glit_lit where
  "glit_lit = map_literal gatom_atom"

definition gcls_cls where
  "gcls_cls \<equiv> image_mset glit_lit"

definition cls_gcls where
  "cls_gcls \<equiv> image_mset lit_glit"

lemma cls_gcls_empty_mset[simp]: "cls_gcls {#} = {#}"
  by (simp add: cls_gcls_def)

lemma gterm_of_term_ident_if_ground:
  "is_ground_term t \<Longrightarrow> term_of_gterm (gterm_of_term t) = t"
  by (induction t) (auto intro: nth_equalityI)

lemma context_ground_context: 
  "(ctxt_of_gctxt context)\<langle>term_of_gterm term\<rangle> = term_of_gterm context\<langle>term\<rangle>\<^sub>G"
  "is_ground_context c \<Longrightarrow> term_of_gterm (gctxt_of_ctxt c)\<langle>t\<rangle>\<^sub>G = c\<langle>term_of_gterm t\<rangle>"
   apply (metis ctxt_of_gctxt_inv ground_ctxt_of_gctxt ground_gctxt_of_ctxt_apply_gterm)
   by (simp add: ground_gctxt_of_ctxt_apply_gterm)

lemma ground_term_with_ground_context: "is_ground_term ((ctxt_of_gctxt context)\<langle>term_of_gterm term\<rangle>)"
  by simp

lemma ground_term_with_context:
  assumes "is_ground_term c\<langle>t\<rangle>" 
  shows 
    "ground_ctxt c" (is "?is_ground_context")
    "is_ground_term t" (is "?is_ground_term")
proof-
  show ?is_ground_context
    using assms gterm_of_term_ident_if_ground term_of_gterm_ctxt_apply_ground(1) by blast
  show ?is_ground_term
    using assms by auto
qed

lemma ground_term_in_ground_context: "is_ground_context c \<Longrightarrow> is_ground_term t \<Longrightarrow> is_ground_term c\<langle>t\<rangle>"
  by simp

lemma atom_gatom_inverse[simp]: "gatom_atom (atom_gatom A) = A"
  unfolding gatom_atom_def atom_gatom_def
  by (simp add: map_uprod_inverse)

lemma lit_glit_inverse[simp]: "glit_lit (lit_glit L) = L"
  unfolding lit_glit_def glit_lit_def
  by (simp add: map_literal_inverse)

lemma cls_gcls_inverse[simp]: "gcls_cls (cls_gcls C) = C"
  unfolding gcls_cls_def cls_gcls_def
  by simp

lemma inj_atom_gatom: "inj_on atom_gatom X"
  by (metis inj_on_def atom_gatom_inverse)

lemma inj_lit_glit: "inj_on lit_glit X"
  by (metis inj_on_def lit_glit_inverse)

lemma inj_cls_gcls: "inj_on cls_gcls X"
  by (metis inj_on_def cls_gcls_inverse)

lemma vars_atom_gatom[simp]: "vars_atom (atom_gatom A) = {}"
  unfolding atom_gatom_def vars_atom_def
  by (simp add: uprod.set_map)

lemma vars_lit_glit[simp]: "vars_literal (lit_glit L) = {}"
  unfolding lit_glit_def vars_literal_def
  by (metis literal.map_sel(1) literal.map_sel(2) vars_atom_gatom)

lemma vars_cls_gcls[simp]: "vars_clause (cls_gcls C) = {}"
  unfolding cls_gcls_def vars_clause_def
  by simp

lemma is_ground_literal_if_in_ground_cls[intro]:
  "L \<in># C \<Longrightarrow> is_ground_clause C \<Longrightarrow> is_ground_literal L"
  by (simp add: vars_clause_def)

lemma is_ground_literal_if_in_cls_gcls[intro]: 
    "literal \<in># cls_gcls clause \<Longrightarrow> is_ground_literal literal"
  by (simp add: is_ground_literal_if_in_ground_cls)

lemma is_ground_atom_if_in_ground_lit[intro]:
  "A \<in> set_literal L \<Longrightarrow> is_ground_literal L \<Longrightarrow> is_ground_atom A"
  by (simp add: set_literal_atm_of vars_literal_def)

lemma is_ground_term_if_in_ground_atm[intro]:
  "t \<in> set_uprod A \<Longrightarrow> is_ground_atom A \<Longrightarrow> is_ground_term t"
  by (simp add: vars_atom_def)

lemma gatom_atom_inverse[simp]: "is_ground_atom A \<Longrightarrow> atom_gatom (gatom_atom A) = A"
  using gterm_of_term_ident_if_ground is_ground_term_if_in_ground_atm map_uprod_inverse
  unfolding gatom_atom_def
  by (smt (verit, ccfv_SIG) atom_gatom_def term_of_gterm_inv uprod.inj_map_strong vars_atom_gatom)

lemma glit_lit_inverse[simp]: "is_ground_literal L \<Longrightarrow> lit_glit (glit_lit L) = L"
  using gatom_atom_inverse is_ground_atom_if_in_ground_lit
  unfolding  glit_lit_def lit_glit_def vars_literal_def
  by (simp add: literal.expand literal.map_sel)

lemma gcls_cls_inverse[simp]: "is_ground_clause C \<Longrightarrow> cls_gcls (gcls_cls C) = C"
  unfolding cls_gcls_def gcls_cls_def
  by (simp add: multiset.map_comp comp_def multiset.map_ident_strong is_ground_literal_if_in_ground_cls)

lemma is_ground_clause_gcls: "is_ground_clause (cls_gcls C)"
  by simp

lemma lit_glit_cls_gcls: "L \<in># C \<longleftrightarrow> (lit_glit L) \<in># cls_gcls C" 
  by (metis cls_gcls_def cls_gcls_inverse gcls_cls_def image_eqI lit_glit_inverse multiset.set_map)

lemma gatom_atom_with_context: 
  assumes "is_ground_context s" and "is_ground_term u" and "is_ground_term t" 
  shows 
    "gatom_atom (Upair s\<langle>u\<rangle> t) = Upair (gctxt_of_ctxt s)\<langle>gterm_of_term u\<rangle>\<^sub>G  (gterm_of_term t)"
  using assms
  unfolding gatom_atom_def
  by (simp add: gterm_of_term_gctxt_of_ctxt)

lemma atom_gatom_with_context: 
  "atom_gatom (Upair s\<langle>t\<rangle>\<^sub>G s') = Upair (ctxt_of_gctxt s)\<langle>term_of_gterm t\<rangle> (term_of_gterm s')"
  unfolding atom_gatom_def
  by (simp add: context_ground_context(1))

lemma glit_lit_with_context: 
  assumes "is_ground_context s" and "is_ground_term u" and "is_ground_term t" 
  shows 
    "glit_lit (s\<langle>u\<rangle> \<approx> t) = (gctxt_of_ctxt s)\<langle>gterm_of_term u\<rangle>\<^sub>G \<approx> gterm_of_term t"
    "glit_lit (Neg (Upair s\<langle>u\<rangle> t))
       = Neg (Upair (gctxt_of_ctxt s)\<langle>gterm_of_term u\<rangle>\<^sub>G (gterm_of_term t))"
  using gatom_atom_with_context
  unfolding glit_lit_def
  using assms by simp_all

lemma lit_glit_with_context: 
  "lit_glit (s\<langle>t\<rangle>\<^sub>G \<approx> s') = (ctxt_of_gctxt s)\<langle>term_of_gterm t\<rangle> \<approx> (term_of_gterm s')"
  "lit_glit (Neg (Upair s\<langle>t\<rangle>\<^sub>G s')) =
     Neg (Upair (ctxt_of_gctxt s)\<langle>term_of_gterm t\<rangle> (term_of_gterm s'))"
  unfolding lit_glit_def
  using atom_gatom_with_context
  by auto

lemma gcls_cls_plus [simp]: "gcls_cls (P\<^sub>1 + P\<^sub>2) = gcls_cls P\<^sub>1 + gcls_cls P\<^sub>2"
  by (simp add: gcls_cls_def)

lemma ground_terms_in_ground_atom [intro]: 
  "is_ground_atom (Upair t1 t2) \<longleftrightarrow> is_ground_term t1 \<and> is_ground_term t2"
  using vars_literal_split by fastforce

lemma is_ground_add_mset: "is_ground_clause (add_mset literal clause) \<longleftrightarrow> 
  is_ground_literal literal \<and> is_ground_clause clause"
  by simp

lemma convert_add_mset:
  assumes "cls_gcls clause = add_mset literal clause'" 
  shows "clause = add_mset (glit_lit literal) (gcls_cls clause')"
  using assms
  by (metis cls_gcls_inverse gcls_cls_def image_mset_add_mset)


end
