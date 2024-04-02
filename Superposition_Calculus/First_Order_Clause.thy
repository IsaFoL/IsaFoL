theory First_Order_Clause
  imports 
    Ground_Clause
    Substitution_First_Order_Term
    Clausal_Calculus_Extra
    Multiset_Extra
    Term_Rewrite_System
    Term_Ordering_Lifting
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


global_interpretation subst_context: basic_substitution where
  subst = subst_apply_ctxt and id_subst = Var and comp_subst = subst_compose and
  is_ground = is_ground_context
proof unfold_locales
  fix \<kappa>
  show "\<kappa> \<cdot>t\<^sub>c Var = \<kappa>"
    by (induction \<kappa>) auto
next
  show "\<And>\<kappa> \<sigma> \<tau>. \<kappa> \<cdot>t\<^sub>c \<sigma> \<odot> \<tau> = \<kappa> \<cdot>t\<^sub>c \<sigma> \<cdot>t\<^sub>c \<tau>"
    by simp
next
  fix \<kappa>
  show "is_ground_context \<kappa> \<Longrightarrow> \<forall>\<sigma>. \<kappa> \<cdot>t\<^sub>c \<sigma> = \<kappa>"
    by (induction \<kappa>) (simp_all add: list.map_ident_strong)
qed

global_interpretation subst_atom: basic_substitution where
  subst = subst_atom and id_subst = Var and comp_subst = subst_compose and
  is_ground = is_ground_atom
proof unfold_locales
  show "\<And>x. x \<cdot>a Var = x"
    by (simp add: subst_atom_def uprod.map_ident)
next
  show "\<And>x \<sigma> \<tau>. x \<cdot>a \<sigma> \<odot> \<tau> = x \<cdot>a \<sigma> \<cdot>a \<tau>"
    unfolding subst_atom_def subst_subst_compose
    by (metis (no_types, lifting) map_uprod_simps uprod_exhaust)
next
  show "\<And>x. is_ground_atom x \<Longrightarrow> \<forall>\<sigma>. x \<cdot>a \<sigma> = x"
    by (simp add: subst_atom_def uprod.map_ident_strong vars_atom_def)
qed

global_interpretation subst_literal: basic_substitution where
  subst = subst_literal and id_subst = Var and comp_subst = subst_compose and
  is_ground = is_ground_literal
proof unfold_locales
  show "\<And>x. x \<cdot>l Var = x"
    by (simp add: subst_literal_def literal.map_ident)
next
  show "\<And>x \<sigma> \<tau>. x \<cdot>l \<sigma> \<odot> \<tau> = x \<cdot>l \<sigma> \<cdot>l \<tau>"
    by (simp add: subst_literal_def map_literal_comp)
next
  show "\<And>x. is_ground_literal x \<Longrightarrow> \<forall>\<sigma>. x \<cdot>l \<sigma> = x"
    by (simp add: literal.expand literal.map_sel subst_literal_def vars_literal_def)
qed

global_interpretation subst_clause: basic_substitution where
  subst = subst_clause and id_subst = Var and comp_subst = subst_compose and
  is_ground = is_ground_clause
proof unfold_locales
  show "\<And>x. x \<cdot> Var = x"
    by (simp add: subst_clause_def)
next
  show "\<And>x \<sigma> \<tau>. x \<cdot> \<sigma> \<odot> \<tau> = x \<cdot> \<sigma> \<cdot> \<tau>"
    by (simp add: subst_clause_def)
next
  show "\<And>x. is_ground_clause x \<Longrightarrow> \<forall>\<sigma>. x \<cdot> \<sigma> = x"
    by (simp add: subst_clause_def vars_clause_def)
qed

text \<open>The following names are for backward compatibility\<close>

lemmas subst_context_Var_ident = subst_context.subst_id_subst
lemmas subst_atom_Var_ident = subst_atom.subst_id_subst
lemmas subst_literal_Var_ident = subst_literal.subst_id_subst
lemmas subst_clause_Var_ident = subst_clause.subst_id_subst

lemmas context_subst_compose = subst_context.subst_comp_subst
lemmas term_subst_compose = term_subst.subst_comp_subst
lemmas atom_subst_compose = subst_atom.subst_comp_subst
lemmas literal_subst_compose = subst_literal.subst_comp_subst
lemmas clause_subst_compose = subst_clause.subst_comp_subst

lemmas subst_ground_context = subst_context.subst_ident_if_ground
lemmas subst_ground_atom = subst_atom.subst_ident_if_ground
lemmas subst_ground_literal = subst_literal.subst_ident_if_ground
lemmas subst_ground_clause = subst_clause.subst_ident_if_ground

lemmas ground_subst_compose = term_subst.is_ground_subst_comp_right

lemma clause_subst_empty [simp]: "{#} \<cdot> \<sigma> = {#}" "clause \<cdot> \<sigma> = {#} \<longleftrightarrow> clause = {#}"
  by (simp_all add: subst_clause_def)

lemmas upair_in_literal = literal.sel

lemma finite_vars_atom [simp]:
  "finite (vars_atom atom)"
  unfolding vars_atom_def
  by simp

lemma finite_vars_literal [simp]:
  "finite (vars_literal literal)"
  unfolding vars_literal_def
  by simp

lemma finite_vars_clause [simp]:
  "finite (vars_clause clause)"
  unfolding vars_clause_def
  by auto

lemma vars_literal [simp]: 
  "vars_literal (Pos atom) = vars_atom atom"
  "vars_literal (Neg atom) = vars_atom atom"
  by (simp_all add: vars_literal_def)

lemma vars_literal_split [simp]: 
  "vars_literal (term\<^sub>1 \<approx> term\<^sub>2) = vars_term term\<^sub>1 \<union> vars_term term\<^sub>2"
  unfolding vars_literal_def vars_atom_def
  by simp

lemma vars_clause_add_mset [simp]: 
  "vars_clause (add_mset literal clause) = vars_literal literal \<union> vars_clause clause"
  by (simp add: vars_clause_def)

lemma vars_clause_plus [simp]: 
  "vars_clause (clause\<^sub>1 + clause\<^sub>2) = vars_clause clause\<^sub>1 \<union> vars_clause clause\<^sub>2"
  by (simp add: vars_clause_def)

lemma clause_submset_vars_clause_subset: 
  "clause\<^sub>1 \<subseteq># clause\<^sub>2 \<Longrightarrow> vars_clause clause\<^sub>1 \<subseteq> vars_clause clause\<^sub>2"
  by (metis subset_mset.add_diff_inverse sup_ge1 vars_clause_plus)

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

lemma is_ground_clause_empty [simp]: "is_ground_clause {#}"
  unfolding vars_clause_def
  by simp 

lemma is_ground_term_iff_term_context_ground: 
  "Term_Context.ground term = is_ground_term term"
  by(induction "term") auto

lemma is_ground_term_ctxt_iff_ground_ctxt: 
  "ground_ctxt context = is_ground_context context"
  by (induction "context") (simp_all add: is_ground_term_iff_term_context_ground)

lemma subst_atom: 
  "Upair term\<^sub>1 term\<^sub>2 \<cdot>a \<sigma> = Upair (term\<^sub>1 \<cdot>t \<sigma>) (term\<^sub>2 \<cdot>t \<sigma>)"
  unfolding subst_atom_def
  by simp_all

lemma subst_literal: 
  "Pos atom \<cdot>l \<sigma> = Pos (atom \<cdot>a \<sigma>)"
  "Neg atom \<cdot>l \<sigma> = Neg (atom \<cdot>a \<sigma>)"
  "atm_of (literal \<cdot>l \<sigma>) = atm_of literal \<cdot>a \<sigma>"
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
  "{# term \<cdot>t \<sigma>. term \<in># mset_lit literal #} = mset_lit (literal \<cdot>l \<sigma>)"
  unfolding subst_literal_def subst_atom_def
  by (cases literal) (auto simp: mset_uprod_image_mset)

lemma is_ground_subst_is_ground_term: 
  assumes "term_subst.is_ground_subst \<gamma>" 
  shows "is_ground_term (term \<cdot>t \<gamma>)"
  using assms
  unfolding term_subst.is_ground_subst_def
  by simp

lemma is_ground_subst_is_ground_atom: 
  assumes "term_subst.is_ground_subst \<gamma>"  
  shows "is_ground_atom (atom \<cdot>a \<gamma>)"
  unfolding vars_atom_def subst_atom_def uprod.set_map
  using is_ground_subst_is_ground_term[OF assms]
  by simp 

lemma is_ground_subst_is_ground_literal: 
  assumes "term_subst.is_ground_subst \<gamma>"  
  shows "is_ground_literal (literal \<cdot>l \<gamma>)"
  unfolding subst_literal_def vars_literal_def
  using is_ground_subst_is_ground_atom[OF assms]
  by (cases literal) simp_all

lemma is_ground_subst_is_ground_clause: 
  assumes "term_subst.is_ground_subst \<gamma>"  
  shows "is_ground_clause (clause \<cdot> \<gamma>)"
  unfolding subst_clause_def vars_clause_def
  using is_ground_subst_is_ground_literal[OF assms]
  by simp

lemma is_ground_subst_is_ground_context: 
  assumes "term_subst.is_ground_subst \<gamma>" 
  shows "is_ground_context (context \<cdot>t\<^sub>c \<gamma>)"
  using assms unfolding term_subst.is_ground_subst_def
  by (metis subst_apply_term_ctxt_apply_distrib sup_bot.right_neutral vars_term_ctxt_apply)

lemma term_in_literal_subst: 
  assumes "term \<in># mset_lit literal" 
  shows "term \<cdot>t \<sigma> \<in># mset_lit (literal \<cdot>l \<sigma>)"
  using assms
  unfolding subst_literal_def subst_atom_def
  by (cases literal) (auto simp: uprod.set_map)

lemma literal_in_clause_subst: 
  assumes "literal \<in># clause"  
  shows "literal \<cdot>l \<sigma> \<in># clause \<cdot> \<sigma>"
  using assms
  unfolding subst_clause_def
  by simp

lemma subst_polarity_stable: 
  shows 
    subst_neg_stable: "is_neg literal \<longleftrightarrow> is_neg (literal \<cdot>l \<sigma>)" and
    subst_pos_stable: "is_pos literal \<longleftrightarrow> is_pos (literal \<cdot>l \<sigma>)"
  by (simp_all add: subst_literal_def)

lemma term_subst_reduntant_upd [simp]:
  assumes "var \<notin> vars_term term"
  shows "term \<cdot>t \<sigma>(var := update) = term \<cdot>t \<sigma>"
  using eval_with_fresh_var[OF assms] 
  by fast

lemma atom_subst_reduntant_upd [simp]:
  assumes "var \<notin> vars_atom atom"
  shows "atom \<cdot>a \<sigma>(var := update) = atom \<cdot>a \<sigma>"
  using assms 
  unfolding vars_atom_def subst_atom_def
  by(cases atom) simp

lemma literal_subst_reduntant_upd [simp]:
  assumes "var \<notin> vars_literal literal"
  shows "literal \<cdot>l \<sigma>(var := update) = literal \<cdot>l \<sigma>"
  using assms 
  unfolding vars_literal_def subst_literal_def
  by(cases literal) simp_all

lemma clause_subst_reduntant_upd [simp]:
  assumes "var \<notin> vars_clause clause"
  shows "clause \<cdot> \<sigma>(var := update) = clause \<cdot> \<sigma>"
  using assms
  unfolding vars_clause_def subst_clause_def
  by auto

lemma term_subst_reduntant_if [simp]: 
  assumes "vars_term term \<subseteq> vars"
  shows "term \<cdot>t (\<lambda>var. if var \<in> vars then \<sigma> var else \<sigma>' var) = term \<cdot>t \<sigma>"
  using assms
  by(induction "term") auto

lemma term_subst_reduntant_if' [simp]: 
  assumes "vars_term term \<inter> vars = {}"  
  shows "term \<cdot>t (\<lambda>var. if var \<in> vars then \<sigma>' var else \<sigma> var) = term \<cdot>t \<sigma>"
  using assms
  by(induction "term") auto

lemma atom_subst_reduntant_if [simp]:
  assumes "vars_atom atom \<subseteq> vars"
  shows "atom \<cdot>a (\<lambda>var. if var \<in> vars then \<sigma> var else \<sigma>' var) = atom \<cdot>a \<sigma>"
  using assms
  unfolding subst_atom_def vars_atom_def
  by(cases atom) simp

lemma atom_subst_reduntant_if' [simp]:
  assumes "vars_atom atom \<inter> vars = {}"  
  shows "atom \<cdot>a (\<lambda>var. if var \<in> vars then \<sigma>' var else \<sigma> var) = atom \<cdot>a \<sigma>"
  using assms
  unfolding subst_atom_def vars_atom_def
  by(cases atom)(simp add: disjoint_iff)  

lemma literal_subst_reduntant_if [simp]: 
  assumes "vars_literal literal \<subseteq> vars"
  shows "literal \<cdot>l (\<lambda>var. if var \<in> vars then \<sigma> var else \<sigma>' var) = literal \<cdot>l \<sigma>"
  using assms
  unfolding subst_literal_def vars_literal_def
  by(cases literal) simp_all

lemma literal_subst_reduntant_if' [simp]:
  assumes "vars_literal literal \<inter> vars = {}"  
  shows "literal \<cdot>l (\<lambda>var. if var \<in> vars then \<sigma>' var else \<sigma> var) = literal \<cdot>l \<sigma>"
  using assms
  unfolding subst_literal_def vars_literal_def
  by(cases literal) simp_all

lemma clause_subst_reduntant_if [simp]: 
  assumes "vars_clause clause \<subseteq> vars"
  shows "clause \<cdot> (\<lambda>var. if var \<in> vars then \<sigma> var else \<sigma>' var) = clause \<cdot> \<sigma>"
  using assms
  unfolding subst_clause_def vars_clause_def 
  by(induction clause) simp_all

lemma clause_subst_reduntant_if' [simp]:
  assumes "vars_clause clause \<inter> vars = {}"  
  shows "clause \<cdot> (\<lambda>var. if var \<in> vars then \<sigma>' var else \<sigma> var) = clause \<cdot> \<sigma>"
  using assms
  unfolding subst_clause_def vars_clause_def 
  by(induction clause) (simp_all add: disjoint_iff)

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

(* Turn around and simp lemmas? *)
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
  assumes "is_ground_term update" "is_ground_term (term \<cdot>t \<gamma>)" 
  shows "is_ground_term (term \<cdot>t \<gamma>(var := update))"
  using assms
  by (simp add: is_ground_iff)

lemma ground_atom_subst_upd [simp]:
  assumes "is_ground_term update" "is_ground_atom (atom \<cdot>a \<gamma>)" 
  shows "is_ground_atom (atom \<cdot>a \<gamma>(var := update))"
  using assms
  unfolding subst_atom_def vars_atom_def
  by(cases atom) simp

lemma ground_literal_subst_upd [simp]:
  assumes "is_ground_term update" "is_ground_literal (literal \<cdot>l \<gamma>)" 
  shows "is_ground_literal (literal \<cdot>l \<gamma>(var := update))"
  using assms
  unfolding subst_literal_def vars_literal_def
  by(cases literal) simp_all

lemma ground_clause_subst_upd [simp]:
  assumes "is_ground_term update" "is_ground_clause (clause \<cdot> \<gamma>)" 
  shows "is_ground_clause (clause \<cdot> \<gamma>(var := update))"
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
  assumes "is_ground_literal (literal \<cdot>l \<gamma>)" "term \<in># mset_lit literal"  
  shows "is_ground_term (term \<cdot>t \<gamma>)"
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
  assumes "is_ground_clause (clause \<cdot> \<gamma>)"  "literal \<in># clause"  
  shows "is_ground_literal (literal \<cdot>l \<gamma>)"
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
  assumes "atom \<cdot>a \<sigma> = Upair term\<^sub>1' term\<^sub>2'"
  obtains term\<^sub>1 term\<^sub>2 
  where "atom = Upair term\<^sub>1 term\<^sub>2" "term\<^sub>1 \<cdot>t \<sigma> = term\<^sub>1'" "term\<^sub>2 \<cdot>t \<sigma> = term\<^sub>2'"
  using assms
  unfolding subst_atom_def
  by(cases atom) auto

lemma obtain_from_pos_literal_subst: 
  assumes "literal \<cdot>l \<sigma> = term\<^sub>1' \<approx> term\<^sub>2'"
  obtains term\<^sub>1 term\<^sub>2 
  where "literal = term\<^sub>1 \<approx> term\<^sub>2" "term\<^sub>1 \<cdot>t \<sigma> = term\<^sub>1'" "term\<^sub>2 \<cdot>t \<sigma> = term\<^sub>2'"
  using assms obtain_from_atom_subst subst_pos_stable
  by (metis is_pos_def literal.sel(1) subst_literal(1))

lemma obtain_from_neg_literal_subst: 
  assumes "literal \<cdot>l \<sigma> = term\<^sub>1' !\<approx> term\<^sub>2'"
  obtains term\<^sub>1 term\<^sub>2 
  where "literal = term\<^sub>1 !\<approx> term\<^sub>2" "term\<^sub>1 \<cdot>t \<sigma> = term\<^sub>1'" "term\<^sub>2 \<cdot>t \<sigma> = term\<^sub>2'"
  using assms obtain_from_atom_subst subst_neg_stable
  by (metis literal.collapse(2) literal.disc(2) subst_literal(2) upair_in_literal(2))

lemmas obtain_from_literal_subst = obtain_from_pos_literal_subst obtain_from_neg_literal_subst

lemma subst_cannot_add_var:
  assumes "is_Var (term \<cdot>t \<sigma>)"  
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

lemma obtain_ground_subst:
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
  assumes "is_ground_term (term \<cdot>t \<gamma>)"
  obtains \<gamma>'  :: "('f, 'v) subst"
  where "term \<cdot>t \<gamma> = term \<cdot>t \<gamma>'" and "term_subst.is_ground_subst \<gamma>'"
  using assms
proof-
  obtain \<gamma>'' :: "'v \<Rightarrow> ('f, 'v) Term.term" where 
    \<gamma>'': "term_subst.is_ground_subst \<gamma>''"
    using obtain_ground_subst
    by blast

  define \<gamma>' where 
    \<gamma>':  "\<gamma>' = (\<lambda>var. if var \<in> vars_term term then \<gamma> var else \<gamma>'' var)"

  have "term_subst.is_ground_subst \<gamma>'"
    using assms \<gamma>'' 
    unfolding \<gamma>' term_subst.is_ground_subst_def
    by (simp add: is_ground_iff)

  moreover have "term \<cdot>t \<gamma> = term \<cdot>t \<gamma>'"
    unfolding \<gamma>'
    by (smt (verit, best) term_subst_eq)

  ultimately show ?thesis
    using that
    by blast
qed

lemma ground_subst_exstension_atom:
  assumes "is_ground_atom (atom \<cdot>a \<gamma>)"
  obtains \<gamma>'
  where "atom \<cdot>a \<gamma> = atom \<cdot>a \<gamma>'" and "term_subst.is_ground_subst \<gamma>'"
  by (metis assms atom_subst_compose ground_subst_compose obtain_ground_subst subst_ground_atom)

lemma ground_subst_exstension_literal:
  assumes "is_ground_literal (literal \<cdot>l \<gamma>)"
  obtains \<gamma>'
  where "literal \<cdot>l \<gamma> = literal \<cdot>l \<gamma>'" and "term_subst.is_ground_subst \<gamma>'"
proof(cases literal)
  case (Pos a)
  then show ?thesis
    using assms that ground_subst_exstension_atom[of a \<gamma>]
    unfolding vars_literal_def subst_literal_def
    by auto
next
  case (Neg a)
  then show ?thesis 
    using assms that ground_subst_exstension_atom[of a \<gamma>]
    unfolding vars_literal_def subst_literal_def
    by auto
qed

lemma ground_subst_exstension_clause:
  assumes "is_ground_clause (clause \<cdot> \<gamma>)"
  obtains \<gamma>'
  where "clause \<cdot> \<gamma> = clause \<cdot> \<gamma>'" and "term_subst.is_ground_subst \<gamma>'"
  by (metis assms clause_subst_compose ground_subst_compose obtain_ground_subst subst_ground_clause)

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

context
  fixes I :: "('f gterm \<times> 'f gterm) set"
  assumes 
    trans: "trans I" and
    sym: "sym I" and
    compatible_with_gctxt: "compatible_with_gctxt I"
begin

lemma interpretation_context_congruence:
  assumes 
    "(t, t') \<in> I"
    "(ctxt\<langle>t\<rangle>\<^sub>G, t'') \<in> I"
  shows
    "(ctxt\<langle>t'\<rangle>\<^sub>G, t'') \<in> I"
  using 
    assms sym trans compatible_with_gctxt
    compatible_with_gctxtD symE transE 
  by meson

lemma interpretation_context_congruence':
  assumes 
    "(t, t') \<in> I"
    "(ctxt\<langle>t\<rangle>\<^sub>G, t'') \<notin> I"
  shows
    "(ctxt\<langle>t'\<rangle>\<^sub>G, t'') \<notin> I"
  using assms sym trans compatible_with_gctxt
  by (metis interpretation_context_congruence symD)

context
  fixes 
    \<gamma> :: "('f, 'v) subst" and
    update :: "('f, 'v) Term.term" and
    var :: 'v
  assumes
    update_is_ground: "is_ground_term update" and
    var_grounding: "is_ground_term (Var var \<cdot>t \<gamma>)" 
begin

lemma interpretation_term_congruence:
  assumes 
    term_grounding: "is_ground_term (term \<cdot>t \<gamma>)" and
    var_update: "(to_ground_term (\<gamma> var), to_ground_term update) \<in> I" and
    updated_term: "(to_ground_term (term \<cdot>t \<gamma>(var := update)), term') \<in> I" 
  shows 
    "(to_ground_term (term \<cdot>t \<gamma>), term') \<in> I"
  using assms
proof(induction "size (filter_mset (\<lambda>var'. var' = var) (vars_term_ms term))" arbitrary: "term")
  case 0

  then have "var \<notin> vars_term term"
    by (metis (mono_tags, lifting) filter_mset_empty_conv set_mset_vars_term_ms size_eq_0_iff_empty)

  then have "term \<cdot>t \<gamma>(var := update) = term \<cdot>t \<gamma>"
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

  have [simp]: "(to_ground_context (context \<cdot>t\<^sub>c \<gamma>))\<langle>to_ground_term (\<gamma> var)\<rangle>\<^sub>G = 
    to_ground_term (context\<langle>Var var\<rangle> \<cdot>t \<gamma>)"
    using Suc by fastforce

  have context_update [simp]: 
    "(to_ground_context (context \<cdot>t\<^sub>c \<gamma>))\<langle>to_ground_term update\<rangle>\<^sub>G = 
      to_ground_term (context\<langle>update\<rangle> \<cdot>t \<gamma>)"
    using Suc update_is_ground
    unfolding "term"
    by auto

  have "n = size {#var' \<in># vars_term_ms context\<langle>update\<rangle>. var' = var#}"
    using Suc vars_term_ms_count[OF update_is_ground, of var "context"]
    by auto

  moreover have "is_ground_term (context\<langle>update\<rangle> \<cdot>t \<gamma>)"
    using Suc.prems update_is_ground 
    by auto

  moreover have  "(to_ground_term (context\<langle>update\<rangle> \<cdot>t \<gamma>(var := update)), term') \<in> I"
    using Suc.prems update_is_ground
    by auto

  moreover have update: "(to_ground_term update, to_ground_term (\<gamma> var)) \<in> I"
    using var_update sym
    by (metis symD)

  moreover have "(to_ground_term (context\<langle>update\<rangle> \<cdot>t \<gamma>), term') \<in> I"
    using Suc calculation
    by blast

  ultimately have "((to_ground_context (context \<cdot>t\<^sub>c \<gamma>))\<langle>to_ground_term (\<gamma> var)\<rangle>\<^sub>G, term') \<in> I"
    using interpretation_context_congruence context_update
    by presburger

  then show ?case 
    unfolding "term"
    by simp
qed

lemma interpretation_term_congruence':
  assumes 
    term_grounding: "is_ground_term (term \<cdot>t \<gamma>)" and
    var_update: "(to_ground_term (\<gamma> var), to_ground_term update) \<in> I" and
    updated_term: "(to_ground_term (term \<cdot>t \<gamma>(var := update)), term') \<notin> I" 
  shows
    "(to_ground_term (term \<cdot>t \<gamma>), term') \<notin> I"
proof
  assume "(to_ground_term (term \<cdot>t \<gamma>), term') \<in> I"

  then show False
    using 
      First_Order_Clause.interpretation_term_congruence[OF 
        trans sym compatible_with_gctxt var_grounding
        ]
      assms 
      sym 
      update_is_ground 
    by (smt (verit) eval_term.simps fun_upd_same fun_upd_triv fun_upd_upd ground_term_subst_upd 
        symD)
qed

lemma interpretation_atom_congruence:
  assumes 
    "is_ground_term (term\<^sub>1 \<cdot>t \<gamma>)" 
    "is_ground_term (term\<^sub>2 \<cdot>t \<gamma>)" 
    "(to_ground_term (\<gamma> var), to_ground_term update) \<in> I"
    "(to_ground_term (term\<^sub>1 \<cdot>t \<gamma>(var := update)), to_ground_term (term\<^sub>2 \<cdot>t \<gamma>(var := update))) \<in> I" 
  shows
    "(to_ground_term (term\<^sub>1 \<cdot>t \<gamma>), to_ground_term (term\<^sub>2 \<cdot>t \<gamma>)) \<in> I"
  using assms
  by (metis interpretation_term_congruence sym symE)

lemma interpretation_atom_congruence':
  assumes 
    "is_ground_term (term\<^sub>1 \<cdot>t \<gamma>)" 
    "is_ground_term (term\<^sub>2 \<cdot>t \<gamma>)" 
    "(to_ground_term (\<gamma> var), to_ground_term update) \<in> I"
    "(to_ground_term (term\<^sub>1 \<cdot>t \<gamma>(var := update)), to_ground_term (term\<^sub>2 \<cdot>t \<gamma>(var := update))) \<notin> I" 
  shows
    "(to_ground_term (term\<^sub>1 \<cdot>t \<gamma>), to_ground_term (term\<^sub>2 \<cdot>t \<gamma>)) \<notin> I"
  using assms
  by (metis interpretation_term_congruence' sym symE)

lemma interpretation_literal_congruence:
  assumes
    "is_ground_literal (literal \<cdot>l \<gamma>)"
    "upair ` I \<TTurnstile>l to_ground_term (Var var \<cdot>t \<gamma>) \<approx> to_ground_term update"
    "upair ` I \<TTurnstile>l to_ground_literal (literal \<cdot>l \<gamma>(var := update))"
  shows
    "upair ` I \<TTurnstile>l to_ground_literal (literal \<cdot>l \<gamma>)"
proof(cases literal)
  case (Pos atom)

  have "to_ground_atom (atom \<cdot>a \<gamma>) \<in> upair ` I"
  proof(cases atom)
    case (Upair term\<^sub>1 term\<^sub>2)  
    then have term_groundings: "is_ground_term (term\<^sub>1 \<cdot>t \<gamma>)" "is_ground_term (term\<^sub>2 \<cdot>t \<gamma>)"
      using Pos assms
      by(auto simp: subst_atom ground_terms_in_ground_atom2 subst_literal)

    have "(to_ground_term (\<gamma> var), to_ground_term update) \<in> I"
      using sym assms by auto

    moreover have 
      "(to_ground_term (term\<^sub>1 \<cdot>t \<gamma>(var := update)), to_ground_term (term\<^sub>2 \<cdot>t \<gamma>(var := update))) \<in> I"
      using assms Pos Upair
      unfolding to_ground_literal_def to_ground_atom_def
      by(auto simp: subst_atom sym subst_literal)

    ultimately show ?thesis
      using interpretation_atom_congruence[OF term_groundings]
      by (simp add: Upair sym subst_atom to_ground_atom_def)
  qed

  with Pos show ?thesis
    by (metis ground_atom_in_ground_literal(2) subst_literal(1) true_lit_simps(1))
next
  case (Neg atom)

  have "to_ground_atom (atom \<cdot>a \<gamma>) \<notin> upair ` I"
  proof(cases atom)
    case (Upair term\<^sub>1 term\<^sub>2)  
    then have term_groundings: "is_ground_term (term\<^sub>1 \<cdot>t \<gamma>)" "is_ground_term (term\<^sub>2 \<cdot>t \<gamma>)"
      using Neg assms
      by(auto simp: subst_atom ground_terms_in_ground_atom2 subst_literal(2))

    have "(to_ground_term (\<gamma> var), to_ground_term update) \<in> I"
      using sym assms by auto

    moreover have 
      "(to_ground_term (term\<^sub>1 \<cdot>t \<gamma>(var := update)), to_ground_term (term\<^sub>2 \<cdot>t \<gamma>(var := update))) \<notin> I"
      using assms Neg Upair
      unfolding to_ground_literal_def to_ground_atom_def
      by (simp add: sym subst_literal(2) subst_atom)

    ultimately show ?thesis
      using interpretation_atom_congruence'[OF term_groundings]
      by (simp add: Upair sym subst_atom to_ground_atom_def)
  qed

  then show ?thesis
    by (metis Neg ground_atom_in_ground_literal2(2) subst_literal(2) true_lit_simps(2))
qed

lemma interpretation_clause_congruence:
  assumes
    "is_ground_clause (clause \<cdot> \<gamma>)" 
    "upair ` I \<TTurnstile>l to_ground_term (Var var \<cdot>t \<gamma>) \<approx> to_ground_term update"
    "upair ` I \<TTurnstile> to_ground_clause (clause \<cdot> \<gamma>(var := update))"
  shows
    "upair ` I \<TTurnstile> to_ground_clause (clause \<cdot> \<gamma>)"
  using assms
proof(induction "clause")
  case empty
  then show ?case 
    by auto
next
  case (add literal clause')

  have clause'_grounding: "is_ground_clause (clause' \<cdot> \<gamma>)"
    by (metis add.prems(1) is_ground_clause_add_mset subst_clause_add_mset)

  show ?case
  proof(cases "upair ` I \<TTurnstile> to_ground_clause (clause' \<cdot> \<gamma>(var := update))")
    case True
    show ?thesis 
      using add(1)[OF clause'_grounding assms(2) True]
      unfolding subst_clause_add_mset to_ground_clause_def
      by simp
  next
    case False
    then have "upair ` I \<TTurnstile>l to_ground_literal (literal \<cdot>l \<gamma>(var := update))"
      using add.prems
      by (metis image_mset_add_mset subst_clause_add_mset to_ground_clause_def true_cls_add_mset)

    then have "upair ` I \<TTurnstile>l to_ground_literal (literal \<cdot>l \<gamma>)"
      using interpretation_literal_congruence add.prems
      by (metis is_ground_clause_add_mset subst_clause_add_mset)

    then show ?thesis 
      by (simp add: subst_clause_add_mset to_ground_clause_def)
  qed
qed

end
end

subsection \<open>Renaming\<close>

(* TODO: these work also without inj *)

context 
  fixes \<rho> :: "('f, 'v) subst"
  assumes renaming: "term_subst.is_renaming \<rho>"
begin

lemma renaming_vars_term:  "Var ` vars_term (term \<cdot>t \<rho>) = \<rho> ` (vars_term term)" 
proof(induction "term")
  case Var
  with renaming show ?case
    unfolding term_subst_is_renaming_iff
    by (metis Term.term.simps(17) eval_term.simps(1) image_empty image_insert is_VarE)
next
  case (Fun f terms)

  have 
    "\<And>term x. \<lbrakk>term \<in> set terms; x \<in> vars_term (term \<cdot>t \<rho>)\<rbrakk> 
       \<Longrightarrow> Var x \<in> \<rho> ` \<Union> (vars_term ` set terms)"
    using Fun
    by (smt (verit, del_insts) UN_iff image_UN image_eqI)

  moreover have 
    "\<And>term x. \<lbrakk>term \<in> set terms; x \<in> vars_term term\<rbrakk>
       \<Longrightarrow> \<rho> x \<in> Var ` (\<Union>x' \<in> set terms. vars_term (x' \<cdot>t \<rho>))"
    using Fun
    by (smt (verit, del_insts) UN_iff image_UN image_eqI)

  ultimately show ?case
    by auto
qed

lemma renaming_vars_atom: "Var ` vars_atom (atom \<cdot>a \<rho>) = \<rho> ` vars_atom atom"
  unfolding vars_atom_def subst_atom_def 
  by(cases atom)(auto simp: image_Un renaming_vars_term)

lemma renaming_vars_literal: "Var ` vars_literal (literal \<cdot>l \<rho>) = \<rho> ` vars_literal literal"
  unfolding vars_literal_def subst_literal_def
  by(cases literal)(auto simp: renaming_vars_atom)

lemma renaming_vars_clause: "Var ` vars_clause (clause \<cdot> \<rho>) = \<rho> ` vars_clause clause"
  using renaming_vars_literal
  by(induction clause)(simp_all add: image_Un subst_clause_add_mset)

end

end
