theory First_Order_Clause
  imports 
    Ground_Clause
    Abstract_Substitution_Extra_First_Order_Term
    Clausal_Calculus_Extra
    Multiset_Extra
    Term_Rewrite_System
begin

(* TODO: Maybe split up file*)

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

type_synonym 'f ground_atom = "'f gatom"
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

lemma atom_subst_eq:
  assumes "\<And>x. x \<in> vars_atom atom \<Longrightarrow> \<sigma> x = \<tau> x"
  shows "atom \<cdot>a \<sigma> = atom \<cdot>a \<tau>"
  using term_subst_eq assms
  unfolding vars_atom_def subst_atom_def
  by (metis (no_types, lifting) UN_I uprod.map_cong0)

lemma literal_subst_eq:
  assumes "\<And>x. x \<in> vars_literal literal \<Longrightarrow> \<sigma> x = \<tau> x"
  shows "literal \<cdot>l \<sigma> = literal \<cdot>l \<tau>"
  using atom_subst_eq assms
  unfolding vars_literal_def subst_literal_def
  by (metis literal.map_cong set_literal_atm_of singletonD)

lemma clause_subst_eq:
  assumes "\<And>x. x \<in> vars_clause clause \<Longrightarrow> \<sigma> x = \<tau> x"
  shows "clause \<cdot> \<sigma> = clause \<cdot> \<tau>"
  using literal_subst_eq assms
  unfolding vars_clause_def subst_clause_def
  by (metis (mono_tags, lifting) UN_I multiset.map_cong0)

lemmas term_subst_compose = subst_subst_compose

lemmas context_subst_compose = ctxt_compose_subst_compose_distrib  
  
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

lemma is_ground_clause_empty [simp]: "is_ground_clause {#}"
  unfolding vars_clause_def
  by simp 

lemma is_ground_term_iff_term_context_ground: 
  "Term_Context.ground term = is_ground_term term"
  by(induction "term") auto

lemma is_ground_term_ctxt_iff_ground_ctxt: 
  "ground_ctxt context = is_ground_context context"
  by (induction "context") (simp_all add: is_ground_term_iff_term_context_ground)

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
  "atm_of (literal \<cdot>l \<theta>) = atm_of literal \<cdot>a \<theta>"
  unfolding subst_literal_def
  using literal.map_sel
  by auto

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

lemma term_subst_reduntant_upd [simp]:
  assumes "var \<notin> vars_term term"
  shows "term \<cdot>t \<theta>(var := update) = term \<cdot>t \<theta>"
  using eval_with_fresh_var[OF assms] 
  by fast
 
lemma atom_subst_reduntant_upd [simp]:
  assumes "var \<notin> vars_atom atom"
  shows "atom \<cdot>a \<theta>(var := update) = atom \<cdot>a \<theta>"
  using assms 
  unfolding vars_atom_def subst_atom_def
  by(cases atom) simp
 
lemma literal_subst_reduntant_upd [simp]:
  assumes "var \<notin> vars_literal literal"
  shows "literal \<cdot>l \<theta>(var := update) = literal \<cdot>l \<theta>"
  using assms 
  unfolding vars_literal_def subst_literal_def
  by(cases literal) simp_all

lemma clause_subst_reduntant_upd [simp]:
  assumes "var \<notin> vars_clause clause"
  shows "clause \<cdot> \<theta>(var := update) = clause \<cdot> \<theta>"
  using assms
  unfolding vars_clause_def subst_clause_def
  by auto
                                      
(* TODO: Could these be made less explicit somehow?
Something like:
locale conversion =
  fixes to :: "'a \<Rightarrow> 'b" and "from" :: "'b \<Rightarrow> 'a"
  assumes 
    inv: "\<And>x. from (to x) = x" and
    inj_to: "\<And>X. inj_on to X" and
    inj_from: "\<And>domain. inj_on from (to ` domain)"
?
 *)
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

lemma to_context_hole: "context\<^sub>G = \<box>\<^sub>G \<longleftrightarrow> to_context context\<^sub>G = \<box>"
  by(cases context\<^sub>G) simp_all

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
  by (simp add: is_ground_term_iff_term_context_ground)
 
lemma ground_term_with_context2:
  assumes "is_ground_context context"  
  shows "to_term (to_ground_context context)\<langle>term\<^sub>G\<rangle>\<^sub>G = context\<langle>to_term term\<^sub>G\<rangle>"
  using assms
  by (simp add: ground_gctxt_of_ctxt_apply_gterm is_ground_term_ctxt_iff_ground_ctxt)

lemma ground_term_with_context3: 
  "(to_context context\<^sub>G)\<langle>to_term term\<^sub>G\<rangle> = to_term context\<^sub>G\<langle>term\<^sub>G\<rangle>\<^sub>G"
  using ground_term_with_context2[OF ground_context_is_ground, symmetric]
  unfolding to_context_inverse.

lemmas ground_term_with_context =
  ground_term_with_context1
  ground_term_with_context2
  ground_term_with_context3

lemma ground_term_subst_upd [simp]:
  assumes "is_ground_term update" "is_ground_term (term \<cdot>t \<theta>)" 
  shows "is_ground_term (term \<cdot>t \<theta>(var := update))"
  using assms
  by (simp add: is_ground_iff)

lemma ground_atom_subst_upd [simp]:
  assumes "is_ground_term update" "is_ground_atom (atom \<cdot>a \<theta>)" 
  shows "is_ground_atom (atom \<cdot>a \<theta>(var := update))"
  using assms
  unfolding subst_atom_def vars_atom_def
  by(cases atom) simp
  
lemma ground_literal_subst_upd [simp]:
  assumes "is_ground_term update" "is_ground_literal (literal \<cdot>l \<theta>)" 
  shows "is_ground_literal (literal \<cdot>l \<theta>(var := update))"
  using assms
  unfolding subst_literal_def vars_literal_def
  by(cases literal) simp_all

lemma ground_clause_subst_upd [simp]:
  assumes "is_ground_term update" "is_ground_clause (clause \<cdot> \<theta>)" 
  shows "is_ground_clause (clause \<cdot> \<theta>(var := update))"
  using assms
  unfolding subst_clause_def vars_clause_def
  by auto

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
  by (cases "term") (simp_all add: map_idI is_ground_term_iff_term_context_ground)

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
  using assms
  unfolding subst_atom_def
  by(cases atom) auto

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

lemma subst_cannot_add_var:
  assumes "is_Var (term \<cdot>t \<theta>)"  
  shows "is_Var term"
  using assms
  unfolding is_Var_def
  by (meson subst_apply_eq_Var)

lemma var_in_term:
  assumes "var \<in> vars_term term"
  obtains "context" where "term = context\<langle>Var var\<rangle>"
  using assms
proof(induction "term")
  case Var
  then show ?case
    by (metis Term.term.simps(17) ctxt_apply_term.simps(1) singletonD)
next
  case (Fun f args)
  then obtain term' where "term' \<in> set args " "var \<in> vars_term term'"
    by (metis term.distinct(1) term.sel(4) term.set_cases(2))

  moreover then obtain args1 args2 where
    "args1 @ [term'] @ args2 = args"
    by (metis append_Cons append_Nil split_list)

  moreover then have "(More f args1 \<box> args2)\<langle>term'\<rangle> = Fun f args"
    by simp

  ultimately show ?case 
    using Fun(1)[of term']
    by (metis Fun.prems(1) append_Cons ctxt_apply_term.simps(2))
qed
 
lemma var_in_non_ground_term: 
  assumes "\<not> is_ground_term term"
  obtains "context" var where "term = context\<langle>var\<rangle>" "is_Var var"
proof-
  obtain var where "var \<in> vars_term term"
    using assms
    by blast

  moreover then obtain "context" where "term = context\<langle>Var var\<rangle>"
    using var_in_term
    by metis

  ultimately show ?thesis
    using that
    by blast
qed

lemma ground_subst_exists:
  obtains \<gamma> 
  where "term_subst.is_ground_subst \<gamma>"
proof-
  obtain t\<^sub>G :: "('b, 'a) Term.term" where "is_ground_term t\<^sub>G"
    by (meson ground_term_is_ground)

  then have "term_subst.is_ground_subst  (\<lambda>_. t\<^sub>G)"
    by (simp add: is_ground_iff term_subst.is_ground_subst_def)

  with that show ?thesis
    by blast
qed

lemma ground_subst_exstension_term:
  assumes "is_ground_term (term \<cdot>t \<theta>)"
  obtains \<gamma>  :: "('f, 'v) subst"
  where "term \<cdot>t \<theta> = term \<cdot>t \<gamma>" and "term_subst.is_ground_subst \<gamma>"
  using assms
proof-
  obtain \<gamma>' :: "'v \<Rightarrow> ('f, 'v) Term.term" where 
    \<gamma>': "term_subst.is_ground_subst \<gamma>'"
      using ground_subst_exists
      by blast

  define \<gamma> where 
    \<gamma>:  "\<gamma> = (\<lambda>var. if var \<in> vars_term term then \<theta> var else \<gamma>' var)"
  
  have "term_subst.is_ground_subst \<gamma>"
    using assms \<gamma>' 
    unfolding \<gamma> term_subst.is_ground_subst_def
     by (simp add: is_ground_iff)

  moreover have "term \<cdot>t \<theta> = term \<cdot>t \<gamma>"
    unfolding \<gamma>
    by (smt (verit, best) term_subst_eq)
    
  ultimately show ?thesis
    using that
    by blast
qed

lemma ground_subst_exstension_atom:
  assumes "is_ground_atom (atom \<cdot>a \<theta>)"
  obtains \<gamma>
  where "atom \<cdot>a \<theta> = atom \<cdot>a \<gamma>" and "term_subst.is_ground_subst \<gamma>"
  by (metis assms atom_subst_compose ground_subst_compose ground_subst_exists subst_ground_atom)

lemma ground_subst_exstension_literal:
  assumes "is_ground_literal (literal \<cdot>l \<theta>)"
  obtains \<gamma>
  where "literal \<cdot>l \<theta> = literal \<cdot>l \<gamma>" and "term_subst.is_ground_subst \<gamma>"
proof(cases literal)
  case (Pos a)
  then show ?thesis
    using assms that ground_subst_exstension_atom[of a  \<theta>]
    unfolding vars_literal_def subst_literal_def
    by auto
next
  case (Neg a)
  then show ?thesis 
    using assms that ground_subst_exstension_atom[of a  \<theta>]
    unfolding vars_literal_def subst_literal_def
    by auto
qed

lemma ground_subst_exstension_clause:
  assumes "is_ground_clause (clause \<cdot> \<theta>)"
  obtains \<gamma>
  where "clause \<cdot> \<theta> = clause \<cdot> \<gamma>" and "term_subst.is_ground_subst \<gamma>"
  by (metis assms clause_subst_compose ground_subst_compose ground_subst_exists subst_ground_clause)

lemma non_ground_arg: 
  assumes "\<not> is_ground_term (Fun f terms)"
  obtains "term"
  where "term \<in> set terms" "\<not> is_ground_term term"
  using assms that by fastforce

lemma non_ground_arg': 
  assumes "\<not> is_ground_term (Fun f terms)"
  obtains ts1 var ts2 
  where "terms = ts1 @ [var] @ ts2" "\<not> is_ground_term var"
  using non_ground_arg
  by (metis append.left_neutral append_Cons assms split_list)

subsection \<open>Interpretations\<close>

lemma vars_term_ms_count:
  assumes "is_ground_term term\<^sub>G"
  shows "size {#var' \<in># vars_term_ms context\<langle>Var var\<rangle>. var' = var#} = 
         Suc (size {#var' \<in># vars_term_ms context\<langle>term\<^sub>G\<rangle>. var' = var#})"
proof(induction "context")
  case Hole
  then show ?case
    using assms
    by (simp add: filter_mset_empty_conv)
next
  case (More f ts1 "context" ts2)
  then show ?case 
    by auto
qed

lemma interpretation_context_congruence:
  assumes 
    "trans I"
    "sym I"
    "compatible_with_gctxt I"
    "(t, t') \<in> I"
    "(ctxt\<langle>t\<rangle>\<^sub>G, t'') \<in> I"
  shows
    "(ctxt\<langle>t'\<rangle>\<^sub>G, t'') \<in> I"
  using assms compatible_with_gctxtD[OF assms(3, 4)]
  by (meson symE transD)

lemma interpretation_context_congruence':
  assumes 
    "trans I"
    "sym I"
    "compatible_with_gctxt I"
    "(t, t') \<in> I"
    "(ctxt\<langle>t\<rangle>\<^sub>G, t'') \<notin> I"
  shows
    "(ctxt\<langle>t'\<rangle>\<^sub>G, t'') \<notin> I"
  using assms
  by (metis interpretation_context_congruence symD)

lemma interpretation_term_congruence:
  fixes \<theta> :: "('a, 'b) subst"
  assumes 
    "trans I"
    "sym I"
    "compatible_with_gctxt I"
    "is_ground_term update" 
    "is_ground_term (Var var \<cdot>t \<theta>)" 
    "is_ground_term (term \<cdot>t \<theta>)" 
    "(to_ground_term (\<theta> var), to_ground_term update) \<in> I"
    "(to_ground_term (term \<cdot>t \<theta>(var := update)), term') \<in> I" 
  shows
    "(to_ground_term (term \<cdot>t \<theta>), term') \<in> I"
  using assms(6, 8)
proof(induction "size (filter_mset (\<lambda>var'. var' = var) (vars_term_ms term))" arbitrary: "term")
  case 0

  then have "var \<notin> vars_term term"
    by (metis (mono_tags, lifting) filter_mset_empty_conv set_mset_vars_term_ms size_eq_0_iff_empty)
  
  then have "term \<cdot>t \<theta>(var := update) = term \<cdot>t \<theta>"
    using term_subst_reduntant_upd 
    by fast
  
  with 0 show ?case
    by argo
next
  case (Suc n)

  then have "var \<in> vars_term term"
    by (metis (full_types) filter_mset_empty_conv nonempty_has_size set_mset_vars_term_ms 
          zero_less_Suc)
    
  then obtain "context" where 
    "term" [simp]: "term = context\<langle>Var var\<rangle>"
    by (meson var_in_term)

  have [simp]: "(to_ground_context (context \<cdot>t\<^sub>c \<theta>))\<langle>to_ground_term (\<theta> var)\<rangle>\<^sub>G = 
    to_ground_term (context\<langle>Var var\<rangle> \<cdot>t \<theta>)"
    using Suc.prems(1) by fastforce

  have context_update [simp]: 
    "(to_ground_context (context \<cdot>t\<^sub>c \<theta>))\<langle>to_ground_term update\<rangle>\<^sub>G = 
      to_ground_term (context\<langle>update\<rangle> \<cdot>t \<theta>)"
    using Suc.prems(1) assms(4)
    unfolding "term"
    by auto

  have "n = size {#var' \<in># vars_term_ms context\<langle>update\<rangle>. var' = var#}"
    using Suc(2) vars_term_ms_count[OF assms(4), of var "context"]
    by auto

  moreover have "is_ground_term (context\<langle>update\<rangle> \<cdot>t \<theta>)"
    using Suc.prems assms(4) by auto
    
  moreover have  "(to_ground_term (context\<langle>update\<rangle> \<cdot>t \<theta>(var := update)), term') \<in> I"
    using  Suc.prems(2) assms(4) by auto

  moreover have update: "(to_ground_term update, to_ground_term (\<theta> var)) \<in> I"
    using assms(7)
    by (meson assms(2) symE)

  moreover have "(to_ground_term (context\<langle>update\<rangle> \<cdot>t \<theta>), term') \<in> I"
    using Suc(1) calculation
    by blast

  ultimately have "((to_ground_context (context \<cdot>t\<^sub>c \<theta>))\<langle>to_ground_term (\<theta> var)\<rangle>\<^sub>G, term') \<in> I"
    using interpretation_context_congruence[OF assms(1, 2, 3)] context_update
    by presburger

  then show ?case 
    unfolding "term"
    by simp
qed
               
lemma interpretation_term_congruence':
  fixes \<theta> :: "('a, 'b) subst"
  assumes 
    "trans I"
    "sym I"
    "compatible_with_gctxt I"
    "is_ground_term update" 
    "is_ground_term (Var var \<cdot>t \<theta>)" 
    "is_ground_term (term \<cdot>t \<theta>)" 
    "(to_ground_term (\<theta> var), to_ground_term update) \<in> I"
    "(to_ground_term (term \<cdot>t \<theta>(var := update)), term') \<notin> I" 
  shows
    "(to_ground_term (term \<cdot>t \<theta>), term') \<notin> I"
proof
  assume "(to_ground_term (term \<cdot>t \<theta>), term') \<in> I"

  then show False
    using assms interpretation_term_congruence
    by (smt (verit, ccfv_SIG) eval_term.simps(1) fun_upd_same fun_upd_triv fun_upd_upd 
         ground_term_subst_upd symE)
qed

lemma interpretation_atom_congruence:
  fixes \<theta> :: "('a, 'b) subst"
  assumes 
    "trans I"
    "sym I"
    "compatible_with_gctxt I"
    "is_ground_term update" 
    "is_ground_term (Var var \<cdot>t \<theta>)" 
    "is_ground_term (term\<^sub>1 \<cdot>t \<theta>)" 
    "is_ground_term (term\<^sub>2 \<cdot>t \<theta>)" 
    "(to_ground_term (\<theta> var), to_ground_term update) \<in> I"
    "(to_ground_term (term\<^sub>1 \<cdot>t \<theta>(var := update)), to_ground_term (term\<^sub>2 \<cdot>t \<theta>(var := update))) \<in> I" 
  shows
    "(to_ground_term (term\<^sub>1 \<cdot>t \<theta>), to_ground_term (term\<^sub>2 \<cdot>t \<theta>)) \<in> I"
  using assms
  by (metis interpretation_term_congruence symE)
 
lemma interpretation_atom_congruence':
  fixes \<theta> :: "('a, 'b) subst"
  assumes 
    "trans I "
    "sym I"
    "compatible_with_gctxt I"
    "is_ground_term update" 
    "is_ground_term (Var var \<cdot>t \<theta>)" 
    "is_ground_term (a \<cdot>t \<theta>)" 
    "is_ground_term (b \<cdot>t \<theta>)" 
    "(to_ground_term (\<theta> var), to_ground_term update) \<in> I"
    "(to_ground_term (a \<cdot>t \<theta>(var := update)), to_ground_term (b \<cdot>t \<theta>(var := update)))\<notin> I" 
  shows
    "(to_ground_term (a \<cdot>t \<theta>), to_ground_term (b \<cdot>t \<theta>)) \<notin> I"
   using assms
   by (metis interpretation_term_congruence' symE)

lemma interpretation_literal_congruence:
  assumes 
    "trans I"
    "sym I"
    "compatible_with_gctxt I"
    "is_ground_term update" 
    "is_ground_term (Var var \<cdot>t \<theta>)" 
    "is_ground_literal (literal \<cdot>l \<theta>)"
    "upair ` I \<TTurnstile>l to_ground_term (Var var \<cdot>t \<theta>) \<approx> to_ground_term update"
    "upair ` I \<TTurnstile>l to_ground_literal (literal \<cdot>l \<theta>(var := update))"
  shows
    "upair ` I \<TTurnstile>l to_ground_literal (literal \<cdot>l \<theta>)"
proof(cases literal)
  case (Pos atom)

  have "to_ground_atom (atom \<cdot>a \<theta>) \<in> upair ` I"
  proof(cases atom)
    case (Upair term\<^sub>1 term\<^sub>2)  
    then have term_groundings: "is_ground_term (term\<^sub>1 \<cdot>t \<theta>)" "is_ground_term (term\<^sub>2 \<cdot>t \<theta>)"
      using Pos assms(6)
      by(auto simp: subst_atom ground_terms_in_ground_atom2 subst_literal)
    
    have "(to_ground_term (\<theta> var), to_ground_term update) \<in> I"
      using assms(2) assms(7) by auto

    moreover have 
      "(to_ground_term (term\<^sub>1 \<cdot>t \<theta>(var := update)), to_ground_term (term\<^sub>2 \<cdot>t \<theta>(var := update))) \<in> I"
      using assms(8) Pos Upair
      unfolding to_ground_literal_def to_ground_atom_def
      by(auto simp: subst_atom assms(2) subst_literal)
   
    ultimately show ?thesis
      using interpretation_atom_congruence[OF assms(1-5) term_groundings]
      by (simp add: Upair assms(2) subst_atom to_ground_atom_def)
  qed

  with Pos show ?thesis
    by (metis ground_atom_in_ground_literal(2) subst_literal(1) true_lit_simps(1))
next
  case (Neg atom)
  
  have "to_ground_atom (atom \<cdot>a \<theta>) \<notin> upair ` I"
  proof(cases atom)
    case (Upair term\<^sub>1 term\<^sub>2)  
    then have term_groundings: "is_ground_term (term\<^sub>1 \<cdot>t \<theta>)" "is_ground_term (term\<^sub>2 \<cdot>t \<theta>)"
      using Neg assms(6)
      by(auto simp: subst_atom ground_terms_in_ground_atom2 subst_literal(2))
    
    have "(to_ground_term (\<theta> var), to_ground_term update) \<in> I"
      using assms(2) assms(7) by auto

    moreover have 
      "(to_ground_term (term\<^sub>1 \<cdot>t \<theta>(var := update)), to_ground_term (term\<^sub>2 \<cdot>t \<theta>(var := update))) \<notin> I"
      using assms(8) Neg Upair
      unfolding to_ground_literal_def to_ground_atom_def
      by (simp add: assms(2) subst_literal(2) subst_atom)
   
    ultimately show ?thesis
      using interpretation_atom_congruence'[OF assms(1-5) term_groundings]
      by (simp add: Upair assms(2) subst_atom to_ground_atom_def)
  qed

  then show ?thesis
    by (metis Neg ground_atom_in_ground_literal2(2) subst_literal(2) true_lit_simps(2))
qed

lemma interpretation_clause_congruence:
  assumes 
    "trans I"
    "sym I"
    "compatible_with_gctxt I"
    "is_ground_term update" 
    "is_ground_term (Var var \<cdot>t \<theta>)" 
    "is_ground_clause (clause \<cdot> \<theta>)" 
    "upair ` I \<TTurnstile>l to_ground_term (Var var \<cdot>t \<theta>) \<approx> to_ground_term update"
    "upair ` I \<TTurnstile> to_ground_clause (clause \<cdot> \<theta>(var := update))"
  shows
    "upair ` I \<TTurnstile> to_ground_clause (clause \<cdot> \<theta>)"
  using assms
proof(induction "clause")
  case empty
  then show ?case 
    by auto
next
  case (add literal clause')

  have clause'_grounding: "is_ground_clause (clause' \<cdot> \<theta>)"
    by (metis add.prems(6) is_ground_clause_add_mset subst_clause_add_mset)
  
  show ?case
  proof(cases "upair ` I \<TTurnstile> to_ground_clause (clause' \<cdot> \<theta>(var := update))")
    case True
    show ?thesis 
      using add(1)[OF assms(1 - 5) clause'_grounding assms(7) True]
      by (simp add: subst_clause_add_mset to_ground_clause_def)
  next
    case False
    then have "upair ` I \<TTurnstile>l to_ground_literal (literal \<cdot>l \<theta>(var := update))"
      using add(9)
      by (metis image_mset_add_mset subst_clause_add_mset to_ground_clause_def true_cls_add_mset)

    then have "upair ` I \<TTurnstile>l to_ground_literal (literal \<cdot>l \<theta>)"
      using interpretation_literal_congruence[OF assms(1-5)] add.prems
      by (metis is_ground_clause_add_mset subst_clause_add_mset)

    then show ?thesis 
      by (simp add: subst_clause_add_mset to_ground_clause_def)
  qed
qed

end
