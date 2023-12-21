theory First_Order_Clause
  imports 
    (* TODO: Factor out Ground_Clause *)
    Ground_Superposition
    Abstract_Substitution_Extra_First_Order_Term
    Clausal_Calculus_Extra
    Term_Extra
begin

(* TODO: Maybe split up file*)
(* TODO: Maybe rename subst to substitution*)

no_notation subst_compose (infixl "\<circ>\<^sub>s" 75)
no_notation subst_apply_term (infixl "\<cdot>" 67)

text \<open>Prefer @{thm [source] term_subst.subst_id_subst} to @{thm [source] subst_apply_term_empty}.\<close>
declare subst_apply_term_empty[no_atp]

section \<open>First_Order_Terms And Abstract_Substitution\<close>

notation subst_apply_term (infixl "\<cdot>t" 67)
notation subst_apply_ctxt (infixl "\<cdot>t\<^sub>c" 67)
notation subst_compose (infixl "\<odot>" 75)

(* Is there a way to define ground terms directly as a subset/subtype of non-ground terms? *)
type_synonym 'f ground_term = "'f gterm"

type_synonym 'f ground_context = "'f gctxt"
type_synonym ('f, 'v) "context" = "('f, 'v) ctxt"

type_synonym 'f ground_atom = "'f Ground_Superposition.atom"
type_synonym ('f, 'v) atom = "('f, 'v) term uprod"

(* This is an example where type-classes would be nice, but the Isabelle ones are shitty...*)
definition subst_atom ::
  "('f, 'v) atom \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) atom" (infixl "\<cdot>a" 67)
where
  "subst_atom A \<sigma> = map_uprod (\<lambda>t. subst_apply_term t \<sigma>) A"

definition subst_literal ::
  "('f, 'v) atom literal \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) atom literal" (infixl "\<cdot>l" 66)
where
  "subst_literal literal \<sigma> = map_literal (\<lambda>atom. atom \<cdot>a \<sigma>) literal"

definition subst_clause ::
  "('f, 'v) atom clause \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) atom clause" (infixl "\<cdot>" 67)
where
  "subst_clause clause \<sigma> = image_mset (\<lambda>literal. literal \<cdot>l \<sigma>) clause"

lemma subst_context_Var_ident[simp]: "context \<cdot>t\<^sub>c Var = context"
  by(induction "context") auto

lemma subst_atom_Var_ident[simp]: "atom \<cdot>a Var = atom"
  unfolding subst_atom_def
  by (simp add: uprod.map_ident)

lemma subst_literal_Var_ident[simp]: "literal \<cdot>l Var = literal"
  unfolding subst_literal_def
  by (simp add: literal.map_ident)

lemma subst_clause_Var_ident[simp]: "clause \<cdot> Var = clause"
  unfolding subst_clause_def
  by simp

lemma clause_subst_empty [simp]: "{#} \<cdot> \<theta> = {#}"  "clause \<cdot> \<theta> = {#} \<longleftrightarrow> clause = {#}"
  by (simp_all add: subst_clause_def)

lemma term_subst_atom_subst: "Upair (term\<^sub>1 \<cdot>t \<theta>) (term\<^sub>2 \<cdot>t \<theta>) = (Upair term\<^sub>1 term\<^sub>2) \<cdot>a \<theta>"
  unfolding subst_atom_def
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

lemmas upair_in_literal = literal.sel

(* This is an example where type-classes would be nice, but the Isabelle ones are shitty...*)
abbreviation vars_context :: "('f, 'v) context \<Rightarrow> 'v set" where
  "vars_context \<equiv> vars_ctxt"

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

lemma vars_literal_split[simp]: 
  "vars_literal (term\<^sub>1 \<approx> term\<^sub>2) = vars_term term\<^sub>1 \<union> vars_term term\<^sub>2"
  unfolding vars_literal_def vars_atom_def
  by simp

lemma vars_clause_add_mset[simp]: 
  "vars_clause (add_mset literal clause) = vars_literal literal \<union> vars_clause clause"
  by (simp add: vars_clause_def)
                                              
lemma vars_clause_plus[simp]: 
  "vars_clause (clause\<^sub>1 + clause\<^sub>2) = vars_clause clause\<^sub>1 \<union> vars_clause clause\<^sub>2"
  by (simp add: vars_clause_def)

lemmas term_subst_compose = subst_subst_compose
  
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
  assumes "term_subst.is_ground_subst \<theta>"
  shows "term_subst.is_ground_subst (\<mu> \<odot> \<theta>)"
  using assms
  unfolding term_subst.is_ground_subst_def
  by simp

abbreviation is_ground_term where 
  "is_ground_term \<equiv> is_ground_trm"

hide_const is_ground_trm

abbreviation is_ground_context where
  "is_ground_context context \<equiv> vars_context context = {}"

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

lemma is_ground_clause_empty [simp]: "is_ground_clause {#}"
  unfolding vars_clause_def
  by simp 

lemma is_ground_term_iff_term_context_ground [simp]: 
  "Term_Context.ground term = is_ground_term term"
  by(induction "term") auto

lemma is_ground_term_ctxt_iff_ground_ctxt [simp]: 
  "ground_ctxt context = is_ground_context context"
  by (induction "context") simp_all

lemma subst_ground_context [simp]: 
  assumes "is_ground_context context" 
  shows "context \<cdot>t\<^sub>c \<sigma> = context"
  using assms
  by (induction "context") (simp_all add: list.map_ident_strong)

lemma subst_ground_atom [simp]: 
  assumes "is_ground_atom atom" 
  shows "atom \<cdot>a \<sigma> = atom"
  using assms
  unfolding subst_atom_def vars_atom_def
  by (simp add: uprod.map_ident_strong)

lemma subst_ground_literal [simp]: 
  assumes "is_ground_literal literal" 
  shows "literal \<cdot>l \<sigma> = literal"
  using assms
  unfolding subst_literal_def vars_literal_def 
  by (simp add: literal.expand literal.map_sel)

lemma subst_ground_clause [simp]: 
  assumes "is_ground_clause clause"  
  shows "clause \<cdot> \<sigma> = clause"
  using assms
  unfolding subst_clause_def vars_clause_def
  by simp

lemma subst_atom: 
  "Upair term\<^sub>1 term\<^sub>2 \<cdot>a \<sigma> = Upair (term\<^sub>1 \<cdot>t \<sigma>) (term\<^sub>2 \<cdot>t \<sigma>)"
  unfolding subst_atom_def
  by simp_all

lemma subst_literal: 
  "Pos atom \<cdot>l \<sigma> = Pos (atom \<cdot>a \<sigma>)"
  "Neg atom \<cdot>l \<sigma> = Neg (atom \<cdot>a \<sigma>)"
  unfolding subst_literal_def
  by simp_all

lemma subst_clause_add_mset: 
  "add_mset literal clause \<cdot> \<sigma> = add_mset (literal \<cdot>l \<sigma>) (clause \<cdot> \<sigma>)"
  unfolding subst_clause_def
  by simp

lemma subst_clause_remove1_mset: 
  assumes "literal \<in># clause" 
  shows "remove1_mset literal clause \<cdot> \<sigma> = remove1_mset (literal \<cdot>l \<sigma>) (clause \<cdot> \<sigma>)"
  unfolding subst_clause_def image_mset_remove1_mset_if
  using assms
  by simp
  
lemma subst_clause_plus: 
  "(clause\<^sub>1 + clause\<^sub>2) \<cdot> \<sigma> = clause\<^sub>1 \<cdot> \<sigma> + clause\<^sub>2 \<cdot> \<sigma>"
  unfolding subst_clause_def
  by simp

lemma sub_ground_clause: 
  assumes "clause' \<subseteq># clause" "is_ground_clause clause "
  shows "is_ground_clause clause'"
  using assms
  by (simp add: mset_subset_eqD vars_clause_def)

lemma mset_mset_lit_subst: 
  "{# term \<cdot>t \<theta>. term \<in># mset_lit literal #} = mset_lit (literal \<cdot>l \<theta>)"
  unfolding subst_literal_def subst_atom_def
  by (cases literal) (auto simp: mset_uprod_image_mset)

lemma is_ground_subst_is_ground_term: 
  assumes "term_subst.is_ground_subst \<theta>" 
  shows "is_ground_term (term \<cdot>t \<theta>)"
  using assms
  unfolding term_subst.is_ground_subst_def
  by simp

lemma is_ground_subst_is_ground_atom: 
  assumes "term_subst.is_ground_subst \<theta>"  
  shows "is_ground_atom (atom \<cdot>a \<theta>)"
  unfolding vars_atom_def subst_atom_def uprod.set_map
  using is_ground_subst_is_ground_term[OF assms]
  by simp 

lemma is_ground_subst_is_ground_literal: 
  assumes "term_subst.is_ground_subst \<theta>"  
  shows "is_ground_literal (literal \<cdot>l \<theta>)"
  unfolding subst_literal_def vars_literal_def
  using is_ground_subst_is_ground_atom[OF assms]
  by (cases literal) simp_all
 
lemma is_ground_subst_is_ground_clause: 
  assumes "term_subst.is_ground_subst \<theta>"  
  shows "is_ground_clause (clause \<cdot> \<theta>)"
  unfolding subst_clause_def vars_clause_def
  using is_ground_subst_is_ground_literal[OF assms]
  by simp

lemma is_ground_subst_is_ground_context: 
  assumes "term_subst.is_ground_subst \<theta>" 
  shows "is_ground_context (context \<cdot>t\<^sub>c \<theta>)"
  using assms unfolding term_subst.is_ground_subst_def
  by (metis subst_apply_term_ctxt_apply_distrib sup_bot.right_neutral vars_term_ctxt_apply)

lemma term_in_literal_subst: 
  assumes "term \<in># mset_lit literal" 
  shows "term \<cdot>t \<theta> \<in># mset_lit (literal \<cdot>l \<theta>)"
  using assms
  unfolding subst_literal_def subst_atom_def
  by (cases literal) (auto simp: uprod.set_map)

lemma literal_in_clause_subst: 
  assumes "literal \<in># clause"  
  shows "literal \<cdot>l \<theta> \<in># clause \<cdot> \<theta>"
  using assms
  unfolding subst_clause_def
  by simp

lemma subst_polarity_stable: 
  shows 
    subst_neg_stable: "is_neg literal \<longleftrightarrow> is_neg (literal \<cdot>l \<theta>)" and
    subst_pos_stable: "is_pos literal \<longleftrightarrow> is_pos (literal \<cdot>l \<theta>)"
  by (simp_all add: subst_literal_def)
                                        
lemma is_imgu_equals: 
  assumes "term_subst.is_imgu \<mu> {{term\<^sub>1, term\<^sub>2}}" 
  shows "term\<^sub>1 \<cdot>t \<mu> = term\<^sub>2 \<cdot>t \<mu>"
  using assms term_subst.is_unifier_iff_if_finite[of "{term\<^sub>1, term\<^sub>2}"]
  unfolding term_subst.is_imgu_def term_subst.is_unifiers_def
  by blast
  
(* TODO: Could these be made less explicit somehow? *)
abbreviation to_term where
  "to_term \<equiv> term_of_gterm"

abbreviation to_ground_term where
  "to_ground_term \<equiv> gterm_of_term"

abbreviation to_context where
  "to_context \<equiv> ctxt_of_gctxt"

abbreviation to_ground_context where
  "to_ground_context \<equiv> gctxt_of_ctxt"

definition to_atom where
  "to_atom = map_uprod to_term"

definition to_ground_atom where
  "to_ground_atom = map_uprod to_ground_term"

definition to_literal where
  "to_literal = map_literal to_atom"

definition to_ground_literal where
  "to_ground_literal = map_literal to_ground_atom"

definition to_clause where
  "to_clause \<equiv> image_mset to_literal"

definition to_ground_clause where
  "to_ground_clause \<equiv> image_mset to_ground_literal"

lemma to_term_to_atom: "Upair (to_term term\<^sub>G\<^sub>1) (to_term term\<^sub>G\<^sub>2) = to_atom (Upair term\<^sub>G\<^sub>1 term\<^sub>G\<^sub>2)"
  by (simp add: to_atom_def)

lemma to_atom_to_literal: 
  "Neg (to_atom atom\<^sub>G) = to_literal (Neg atom\<^sub>G)"
  "Pos (to_atom atom\<^sub>G) = to_literal (Pos atom\<^sub>G)"  
  by (simp_all add: to_literal_def)

lemma to_clause_empty_mset [simp]: "to_clause {#} = {#}"
  by (simp add: to_clause_def)

lemma to_ground_clause_empty_mset [simp]: "to_ground_clause {#} = {#}"
  by (simp add: to_ground_clause_def)

lemmas ground_term_is_ground = vars_term_of_gterm

lemmas ground_context_is_ground = vars_ctxt_of_gctxt

lemma ground_term_with_context_is_ground1: 
  "is_ground_term (to_context context\<^sub>G)\<langle>to_term term\<^sub>G\<rangle>"
  by simp

lemma ground_term_with_context_is_ground2:
  assumes "is_ground_term context\<langle>term\<rangle>" 
  shows 
    "is_ground_context context" 
    "is_ground_term term"
  using assms by auto

lemma ground_term_with_context_is_ground3: 
  assumes "is_ground_context context" "is_ground_term term"
  shows "is_ground_term context\<langle>term\<rangle>"
  using assms
  by simp

lemmas ground_term_with_context_is_ground = 
  ground_term_with_context_is_ground1
  ground_term_with_context_is_ground2
  ground_term_with_context_is_ground3

lemma ground_atom_is_ground [simp]: "is_ground_atom (to_atom atom\<^sub>G)"
  unfolding to_atom_def vars_atom_def
  using ground_term_is_ground
  by (simp add: uprod.set_map)

lemma ground_literal_is_ground [simp]: "is_ground_literal (to_literal literal\<^sub>G)"
  unfolding to_literal_def vars_literal_def
  by (cases literal\<^sub>G) simp_all

lemma ground_clause_is_ground [simp]: "is_ground_clause (to_clause clause\<^sub>G)"
  unfolding to_clause_def vars_clause_def
  by simp

lemma to_literal_polarity_stable: 
  shows 
    to_literal_neg_stable: "is_neg literal\<^sub>G \<longleftrightarrow> is_neg (to_literal literal\<^sub>G)" and
    to_literal_stable: "is_pos literal\<^sub>G \<longleftrightarrow> is_pos (to_literal literal\<^sub>G)"
  by (simp_all add: to_literal_def)

lemmas to_term_inverse = term_of_gterm_inv

lemmas to_context_inverse = ctxt_of_gctxt_inv

lemma to_atom_inverse [simp]: 
  "to_ground_atom (to_atom atom) = atom"
  unfolding to_ground_atom_def to_atom_def
  by (simp add: map_uprod_inverse)

lemma to_literal_inverse [simp]: 
  "to_ground_literal (to_literal literal) = literal"
  unfolding to_literal_def to_ground_literal_def
  by (simp add: map_literal_inverse)

lemma to_clause_inverse [simp]: 
  "to_ground_clause (to_clause clause) = clause"
  unfolding to_ground_clause_def to_clause_def
  by simp

lemma ground_term_with_context1:
  assumes "is_ground_context context" "is_ground_term term"
  shows "(to_ground_context context)\<langle>to_ground_term term\<rangle>\<^sub>G = to_ground_term context\<langle>term\<rangle>"
  using assms
  by simp

lemma ground_term_with_context2:
  assumes "is_ground_context context"  
  shows "to_term (to_ground_context context)\<langle>term\<^sub>G\<rangle>\<^sub>G = context\<langle>to_term term\<^sub>G\<rangle>"
  using assms
  by (simp add: ground_gctxt_of_ctxt_apply_gterm)

lemma ground_term_with_context3: 
  "(to_context context\<^sub>G)\<langle>to_term term\<^sub>G\<rangle> = to_term context\<^sub>G\<langle>term\<^sub>G\<rangle>\<^sub>G"
  using ground_term_with_context2[OF ground_context_is_ground, symmetric]
  unfolding to_context_inverse.

lemmas ground_term_with_context =
  ground_term_with_context1
  ground_term_with_context2
  ground_term_with_context3

lemmas to_term_inj = inj_term_of_gterm

lemma to_ground_term_inj: "inj_on to_ground_term (to_term ` domain\<^sub>G)"
  using inj_on_def by fastforce

lemma to_atom_inj: "inj_on to_atom domain"
  unfolding inj_on_def
  by (metis to_atom_inverse)

lemma to_ground_atom_inj: "inj_on to_ground_atom (to_atom ` domain\<^sub>G)"
  unfolding inj_on_def
  by simp

lemma to_literal_inj: "inj_on to_literal domain"
  by (metis inj_on_def to_literal_inverse)

lemma to_ground_literal_inj: "inj_on to_ground_literal (to_literal ` domain\<^sub>G)"
  by (simp add: inj_on_def)

lemma to_clause_inj: "inj_on to_clause domain"
  by (metis inj_on_def to_clause_inverse)

lemma to_ground_clause_inj: "inj_on to_ground_clause (to_clause ` domain\<^sub>G)"
  by (simp add: inj_on_def)

lemma to_clause_add_mset: 
  "to_clause (add_mset literal\<^sub>G clause\<^sub>G) = add_mset (to_literal literal\<^sub>G) (to_clause clause\<^sub>G)"
  by (simp add: to_clause_def)

lemma set_mset_to_clause_to_literal: 
  "set_mset (to_clause clause) = to_literal ` (set_mset clause)"
  unfolding to_clause_def
  by simp

lemma remove1_mset_to_literal: 
  "remove1_mset (to_literal literal\<^sub>G) (to_clause clause\<^sub>G) 
   = to_clause (remove1_mset literal\<^sub>G clause\<^sub>G)"
  unfolding to_clause_def image_mset_remove1_mset[OF to_literal_inj]..

lemma ground_term_in_ground_atom [intro]:
  assumes "term \<in> set_uprod atom" "is_ground_atom atom"
  shows "is_ground_term term"
  using assms
  by (simp add: vars_atom_def)

lemma ground_terms_in_ground_atom1:
  assumes "is_ground_term term\<^sub>1" and "is_ground_term term\<^sub>2"
  shows "Upair (to_ground_term term\<^sub>1) (to_ground_term term\<^sub>2) = to_ground_atom (Upair term\<^sub>1 term\<^sub>2)"
  using assms
  by (simp add: to_ground_atom_def)

lemma ground_terms_in_ground_atom2 [intro]: 
  "is_ground_atom (Upair term\<^sub>1 term\<^sub>2) \<longleftrightarrow> is_ground_term term\<^sub>1 \<and> is_ground_term term\<^sub>2"
  using vars_literal_split by fastforce

lemmas ground_terms_in_ground_atom = 
  ground_terms_in_ground_atom1
  ground_terms_in_ground_atom2

lemma ground_atom_in_ground_literal1 [intro]:
  assumes "atom \<in> set_literal literal" "is_ground_literal literal" 
  shows "is_ground_atom atom"
  using assms
  by (simp add: set_literal_atm_of vars_literal_def)

lemma ground_atom_in_ground_literal2:
  shows "Pos (to_ground_atom atom) = to_ground_literal (Pos atom)" 
        "Neg (to_ground_atom atom) = to_ground_literal (Neg atom)" 
  by (simp_all add: to_ground_atom_def to_ground_literal_def)

lemmas ground_atom_in_ground_literal = 
  ground_atom_in_ground_literal1
  ground_atom_in_ground_literal2

lemma is_ground_atom_in_ground_literal [intro]:
  "is_ground_literal literal \<longleftrightarrow> is_ground_atom (atm_of literal)"
  by (simp add: vars_literal_def)  

lemma ground_term_in_ground_literal:
  assumes "is_ground_literal literal"  "term \<in># mset_lit literal"  
  shows "is_ground_term term"
  using assms
  by(cases literal) (auto simp: ground_term_in_ground_atom)

lemma ground_term_in_ground_literal_subst:
  assumes "is_ground_literal (literal \<cdot>l \<theta>)" "term \<in># mset_lit literal"  
  shows "is_ground_term (term \<cdot>t \<theta>)"
  using ground_term_in_ground_literal[OF assms(1) term_in_literal_subst[OF assms(2)]].

lemma ground_literal_in_ground_clause1:
  assumes "literal \<in># clause" "is_ground_clause clause" 
  shows "is_ground_literal literal"
  using assms
  by (simp add: vars_clause_def)

lemma ground_literal_in_ground_clause2: 
   "literal \<in># to_clause clause\<^sub>G \<Longrightarrow> is_ground_literal literal"
  by (simp add: ground_literal_in_ground_clause1)

lemma ground_literal_in_ground_clause3: 
  "literal\<^sub>G \<in># clause\<^sub>G \<longleftrightarrow> to_literal literal\<^sub>G \<in># to_clause clause\<^sub>G"
  using to_clause_inverse to_literal_inverse
  by (metis image_eqI multiset.set_map to_clause_def to_ground_clause_def)

lemma ground_literal_in_ground_clause4: 
  "(\<forall>literal \<in># to_clause clause\<^sub>G. P literal) \<longleftrightarrow> (\<forall>literal\<^sub>G \<in># clause\<^sub>G. P (to_literal literal\<^sub>G))"
  using ground_literal_in_ground_clause3 set_mset_to_clause_to_literal image_iff
  by metis

lemmas ground_literal_in_ground_clause = 
  ground_literal_in_ground_clause1
  ground_literal_in_ground_clause2
  ground_literal_in_ground_clause3
  ground_literal_in_ground_clause4

lemma ground_literal_in_ground_clause_subst:
  assumes "is_ground_clause (clause \<cdot> \<theta>)"  "literal \<in># clause"  
  shows "is_ground_literal (literal \<cdot>l \<theta>)"
  using assms
  unfolding subst_clause_def vars_clause_def
  by simp

lemma to_ground_term_inverse [simp]:
  assumes "is_ground_term term"  
  shows "to_term (to_ground_term term) = term"
  using assms
  by (cases "term") (simp_all add: map_idI)

lemma to_ground_atom_inverse [simp]: 
  assumes "is_ground_atom atom"  
  shows "to_atom (to_ground_atom atom) = atom"
  using assms to_ground_term_inverse ground_term_in_ground_atom map_uprod_inverse to_term_inverse
  unfolding to_ground_atom_def
  by (smt (verit, ccfv_SIG) to_atom_def uprod.inj_map_strong ground_atom_is_ground)

lemma to_ground_literal_inverse [simp]: 
  assumes "is_ground_literal literal"  
  shows "to_literal (to_ground_literal literal) = literal"
  using assms ground_atom_in_ground_literal(1)[THEN to_ground_atom_inverse]
  unfolding to_ground_literal_def to_literal_def vars_literal_def
  by (simp add: literal.expand literal.map_sel)

lemma to_ground_clause_inverse [simp]: 
  assumes "is_ground_clause clause"  
  shows "to_clause (to_ground_clause clause) = clause"
  using assms
  unfolding to_clause_def to_ground_clause_def multiset.map_comp comp_def
  by (simp add: ground_literal_in_ground_clause(1))

lemma to_ground_clause_plus [simp]: 
  "to_ground_clause (clause\<^sub>1 + clause\<^sub>2) = to_ground_clause clause\<^sub>1 + to_ground_clause clause\<^sub>2"
  by (simp add: to_ground_clause_def)

lemma to_clause_plus [simp]: 
  "to_clause (clause\<^sub>G\<^sub>1 + clause\<^sub>G\<^sub>2) = to_clause clause\<^sub>G\<^sub>1 + to_clause clause\<^sub>G\<^sub>2"
  by (simp add: to_clause_def)

lemma mset_to_literal: "mset_lit (to_literal l) = image_mset to_term (mset_lit l)"
  unfolding to_literal_def
  by (simp add: to_atom_def mset_lit_image_mset)

lemma is_ground_clause_add_mset [intro]: "is_ground_clause (add_mset literal clause) \<longleftrightarrow> 
  is_ground_literal literal \<and> is_ground_clause clause"
  by simp

lemma to_ground_clause_add_mset:
  assumes "to_clause clause = add_mset literal clause'" 
  shows "clause = add_mset (to_ground_literal literal) (to_ground_clause clause')"
  using assms
  by (metis to_clause_inverse to_ground_clause_def image_mset_add_mset)

lemma obtain_from_atom_subst: 
  assumes "atom \<cdot>a \<theta> = Upair term\<^sub>1' term\<^sub>2'"
  obtains term\<^sub>1 term\<^sub>2 
  where "atom = Upair term\<^sub>1 term\<^sub>2" "term\<^sub>1 \<cdot>t \<theta> = term\<^sub>1'" "term\<^sub>2 \<cdot>t \<theta> = term\<^sub>2'"
  using assms term_subst_atom_subst
  by (smt (z3) Upair_inject uprod_exhaust)

lemma obtain_from_pos_literal_subst: 
  assumes "literal \<cdot>l \<theta> = term\<^sub>1' \<approx> term\<^sub>2'"
  obtains term\<^sub>1 term\<^sub>2 
  where "literal = term\<^sub>1 \<approx> term\<^sub>2" "term\<^sub>1 \<cdot>t \<theta> = term\<^sub>1'" "term\<^sub>2 \<cdot>t \<theta> = term\<^sub>2'"
  using assms obtain_from_atom_subst subst_pos_stable
  by (metis is_pos_def literal.sel(1) subst_literal(1))

lemma obtain_from_neg_literal_subst: 
  assumes "literal \<cdot>l \<theta> = term\<^sub>1' !\<approx> term\<^sub>2'"
  obtains term\<^sub>1 term\<^sub>2 
  where "literal = term\<^sub>1 !\<approx> term\<^sub>2" "term\<^sub>1 \<cdot>t \<theta> = term\<^sub>1'" "term\<^sub>2 \<cdot>t \<theta> = term\<^sub>2'"
  using assms obtain_from_atom_subst subst_neg_stable
  by (metis literal.collapse(2) literal.disc(2) subst_literal(2) upair_in_literal(2))

lemmas obtain_from_literal_subst = obtain_from_pos_literal_subst obtain_from_neg_literal_subst

end
