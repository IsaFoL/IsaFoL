theory First_Order_Clause
  imports 
    Ground_Clause
    Abstract_Substitution.Substitution_First_Order_Term
    Abstract_Substitution.Variable_Substitution
    Clausal_Calculus_Extra
    Multiset_Extra
    Term_Rewrite_System
    Term_Ordering_Lifting
    "HOL-Eisbach.Eisbach"
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

named_theorems clause_simp
named_theorems clause_intro

lemma ball_set_uprod [clause_simp]: "(\<forall>t\<in>set_uprod (Upair t1 t2). P t) \<longleftrightarrow> P t1 \<and> P t2"
  by auto

lemmas clause_simp_more = subst_apply_term_ctxt_apply_distrib literal.sel vars_term_ctxt_apply

lemma literal_cases: "\<lbrakk>\<P> \<in> {Pos, Neg}; \<P> = Pos \<Longrightarrow> P; \<P> = Neg \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by blast

(* TODO: cases *)
method clause_simp uses (* cases*) simp intro =
  (*(-, (rule literal_cases[OF cases]))?,*)
  auto simp only: simp clause_simp clause_simp_more intro: intro clause_intro

method clause_auto uses simp intro = 
  (clause_simp simp: simp intro: intro)?,  
  (auto simp: simp intro intro)?, 
  (auto simp: simp clause_simp intro: intro clause_intro)?

type_synonym 'f ground_term = "'f gterm"

type_synonym 'f ground_context = "'f gctxt"
type_synonym ('f, 'v) "context" = "('f, 'v) ctxt"

type_synonym 'f ground_atom = "'f gatom"
type_synonym ('f, 'v) atom = "('f, 'v) term uprod"

definition subst_atom ::
  "('f, 'v) atom \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) atom" (infixl "\<cdot>a" 67)
  where
    "subst_atom atom \<sigma> = map_uprod (\<lambda>term. term \<cdot>t \<sigma>) atom"

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

global_interpretation "term": variable_substitution_set where
  subst = subst_apply_term and id_subst = Var and comp_subst = subst_compose and vars = vars_term
  using term_subst_eq
  by unfold_locales auto

global_interpretation "context": variable_substitution_lifting_set where
   lifted_subst = subst_apply_ctxt and lifted_vars = vars_context and id_subst = Var and 
   comp_subst = subst_compose and vars = vars_term and subst = subst_apply_term
proof unfold_locales
  fix \<kappa> :: "('f, 'v) context"
  show "\<kappa> \<cdot>t\<^sub>c Var = \<kappa>"
    by (induction \<kappa>) auto
next
  show "\<And>\<kappa> \<sigma> \<tau>. \<kappa> \<cdot>t\<^sub>c \<sigma> \<odot> \<tau> = \<kappa> \<cdot>t\<^sub>c \<sigma> \<cdot>t\<^sub>c \<tau>"
    by simp
next
  fix \<kappa> :: "('f, 'v) context"
  show "vars_context \<kappa> = {} \<Longrightarrow> \<forall>\<sigma>. \<kappa> \<cdot>t\<^sub>c \<sigma> = \<kappa>"
    by (induction \<kappa>) (simp_all add: list.map_ident_strong)
next 
  show "\<And>a \<sigma> \<tau>. (\<And>x. x \<in> vars_context a \<Longrightarrow> \<sigma> x = \<tau> x) \<Longrightarrow> a \<cdot>t\<^sub>c \<sigma> = a \<cdot>t\<^sub>c \<tau>"
    using ctxt_subst_eq.
next
  fix \<kappa> :: "('f, 'v) context"

  have "\<And>t. finite (vars_term \<kappa>\<langle>t\<rangle>)"
    using term.finite_vars by blast

  then show "finite (vars_context \<kappa>)"
    unfolding vars_term_ctxt_apply finite_Un
    by simp
next
  fix \<gamma> :: "('f,'v) subst"

  show "(\<forall>\<kappa>. vars_context (\<kappa> \<cdot>t\<^sub>c \<gamma>) = {}) = (\<forall>t. term.is_ground (t \<cdot>t \<gamma>))"
  proof(intro iffI allI equals0I)
    fix t x

    assume is_ground: "\<forall>\<kappa>. vars_context (\<kappa> \<cdot>t\<^sub>c \<gamma>) = {}" and vars: "x \<in> vars_term (t \<cdot>t \<gamma>)"

    have "\<And>f. vars_context (More f [t] Hole [] \<cdot>t\<^sub>c \<gamma>) = {}"
      using is_ground
      by presburger

    moreover have "\<And>f. x \<in> vars_context (More f [t] Hole [] \<cdot>t\<^sub>c \<gamma>)"
      using vars
      by simp
      
    ultimately show False
      by blast
  next
    fix \<kappa> x
    assume is_ground: "\<forall>t. term.is_ground (t \<cdot>t \<gamma>)" and vars: "x \<in> vars_context (\<kappa> \<cdot>t\<^sub>c \<gamma>)"

    have "\<And>t. term.is_ground (\<kappa>\<langle>t\<rangle> \<cdot>t \<gamma>)"
      using is_ground
      by presburger

    moreover have "\<And>t. x \<in> vars_term (\<kappa>\<langle>t\<rangle> \<cdot>t \<gamma>)"
      using vars
      by simp

    ultimately show False
      by blast
  qed
qed

lemma atom_is_ground_iff_ident_forall_subst:
  fixes atom :: "('f, 'v) atom"
  shows "vars_atom atom = {} \<longleftrightarrow> (\<forall>\<sigma>. atom \<cdot>a \<sigma> = atom)" 
proof (rule iffI)
  show "\<And>x. vars_atom x = {} \<Longrightarrow> \<forall>\<sigma>. x \<cdot>a \<sigma> = x"
    by (simp add: subst_atom_def uprod.map_ident_strong vars_atom_def)
next
  assume ident_forall_subst: "\<forall>\<sigma>. atom \<cdot>a \<sigma> = atom"

  have "term.is_ground t" if A_def: "atom = Upair t u" for t u :: "('f, 'v) term"
  proof (rule ccontr)
    assume is_not_ground_term: "\<not> term.is_ground t"
    define \<sigma> :: "'v \<Rightarrow> ('f, 'v) term" where
      "\<sigma> = (\<lambda>_. u)"

    have "t \<cdot>t \<sigma> = t \<and> u \<cdot>t \<sigma> = u \<or> t \<cdot>t \<sigma> = u \<and> u \<cdot>t \<sigma> = t"
      using ident_forall_subst by (simp add: A_def subst_atom_def)

    moreover have "\<not> (t \<cdot>t \<sigma> = t \<and> u \<cdot>t \<sigma> = u)"
      using ident_forall_subst is_ground_trm_iff_ident_forall_subst is_not_ground_term
      unfolding \<sigma>_def A_def Upair_inject subst_atom_def map_uprod_simps 
      by (metis equals0I eval_term.elims is_FunI is_Fun_num_funs_less leD num_funs_subst)

    moreover then have "\<not> (t \<cdot>t \<sigma> = u \<and> u \<cdot>t \<sigma> = t)"
      by (metis (no_types, opaque_lifting) \<sigma>_def subst_apply_eq_Var subst_compose_def
          term_subst.subst_comp_subst term_subst_eq_conv)

    ultimately show False
      by argo
  qed

  thus "vars_atom atom = {}"
    by (metis (no_types, opaque_lifting) Sup_empty Sup_insert Upair_inject map_uprod_simps
        set_uprod_simps sup.idem uprod.set_map uprod_exhaust vars_atom_def)
qed

global_interpretation atom: variable_substitution_lifting_set
  where lifted_subst = subst_atom and lifted_vars = vars_atom and id_subst = Var and 
        comp_subst = subst_compose and vars = vars_term and subst = subst_apply_term
proof unfold_locales
  show "\<And>x \<sigma> \<tau>. x \<cdot>a \<sigma> \<odot> \<tau> = x \<cdot>a \<sigma> \<cdot>a \<tau>"
    unfolding subst_atom_def subst_subst_compose
    by (metis (no_types, lifting) map_uprod_simps uprod_exhaust)
next 
  show "\<And>x. x \<cdot>a Var = x"
    by (simp add: subst_atom_def uprod.map_ident)
next
  show "\<And>x. vars_atom x = {} \<Longrightarrow> \<forall>\<sigma>. x \<cdot>a \<sigma> = x"
    using atom_is_ground_iff_ident_forall_subst by  metis
next
  show "\<And>a \<sigma> \<tau>. (\<And>x. x \<in> vars_atom a \<Longrightarrow> \<sigma> x = \<tau> x) \<Longrightarrow> a \<cdot>a \<sigma> = a \<cdot>a \<tau>"
    by (smt (verit, best) UN_I subst_atom_def term_subst_eq uprod.map_cong0 vars_atom_def)
next
  show "\<And>\<gamma>. (\<forall>x. vars_atom (x \<cdot>a \<gamma>) = {}) = (\<forall>x. term.is_ground (x \<cdot>t \<gamma>))"    
    unfolding vars_atom_def subst_atom_def
    apply auto
     apply (metis emptyE insert_iff map_uprod_simps set_uprod_simps)
    by (metis (no_types, lifting) ex_in_conv imageE uprod.set_map)
next
  show "\<And>a. finite (vars_atom a)"
    by (simp add: vars_atom_def)
qed

(* TODO: also for clause *)
lemma literal_is_ground_iff_ident_forall_subst:
  fixes literal :: "('f, 'v) atom literal"
  shows "vars_literal literal = {} \<longleftrightarrow> (\<forall>\<sigma>. literal \<cdot>l \<sigma> = literal)" 
proof(intro iffI)
  assume "vars_literal literal = {}"
  then show "\<forall>\<sigma>. literal \<cdot>l \<sigma> = literal"
    by (simp add: literal.expand literal.map_sel subst_literal_def vars_literal_def)
next
  assume "\<forall>\<sigma>. literal \<cdot>l \<sigma> = literal"
  then show "vars_literal literal = {}"
    using atom_is_ground_iff_ident_forall_subst
    unfolding subst_literal_def vars_literal_def
    by (metis literal.map_sel)
qed

global_interpretation literal: variable_substitution_lifting_set
  where lifted_subst = subst_literal and lifted_vars = vars_literal and id_subst = Var and 
    comp_subst = subst_compose and vars = vars_atom and subst = subst_atom
proof unfold_locales
  show "\<And>x. x \<cdot>l Var = x"
    by (simp add: subst_literal_def literal.map_ident)
next
  show "\<And>x \<sigma> \<tau>. x \<cdot>l \<sigma> \<odot> \<tau> = x \<cdot>l \<sigma> \<cdot>l \<tau>"
    by (simp add: subst_literal_def map_literal_comp)
next
  show "\<And>x. vars_literal x = {} \<Longrightarrow> \<forall>\<sigma>. x \<cdot>l \<sigma> = x"
    using literal_is_ground_iff_ident_forall_subst
    by blast
next
  show "\<And>a \<sigma> \<tau>. (\<And>x. x \<in> vars_literal a \<Longrightarrow> \<sigma> x = \<tau> x) \<Longrightarrow> a \<cdot>l \<sigma> = a \<cdot>l \<tau>"
    unfolding subst_literal_def vars_literal_def  
    by (metis atom.subst_eq empty_iff insert_iff literal.map_cong0 set_literal_atm_of)
next
  show "\<And>\<gamma>. (\<forall>x. vars_literal (x \<cdot>l \<gamma>) = {}) = (\<forall>x. atom.is_ground (x \<cdot>a \<gamma>))"
    by (metis literal.map(2) literal.map_sel literal.sel(2) subst_literal_def vars_literal_def)
next
  show "\<And>a. finite (vars_literal a)"
    by (simp add: vars_literal_def)
qed

(* TODO: also for clause set *)
global_interpretation clause: variable_substitution_lifting_set
  where lifted_subst = subst_clause and lifted_vars = vars_clause and id_subst = Var and 
    comp_subst = subst_compose and vars = vars_literal and subst = subst_literal
proof unfold_locales
  show "\<And>x. x \<cdot> Var = x"
    by (simp add: subst_clause_def)
next
  show "\<And>x \<sigma> \<tau>. x \<cdot> \<sigma> \<odot> \<tau> = x \<cdot> \<sigma> \<cdot> \<tau>"
    by (simp add: subst_clause_def)
next
  show "\<And>x. vars_clause x = {} \<Longrightarrow> \<forall>\<sigma>. x \<cdot> \<sigma> = x"
    by (simp add: subst_clause_def vars_clause_def)
next
  show "\<And>a \<sigma> \<tau>. (\<And>x. x \<in> vars_clause a \<Longrightarrow> \<sigma> x = \<tau> x) \<Longrightarrow> a \<cdot> \<sigma> = a \<cdot> \<tau>"
    unfolding vars_clause_def subst_clause_def
    using literal.subst_eq
    by (metis (mono_tags, lifting) UN_I image_mset_cong2)
next
  show "\<And>\<gamma>. (\<forall>x. vars_clause (x \<cdot> \<gamma>) = {}) = (\<forall>x. literal.is_ground (x \<cdot>l \<gamma>))"
    unfolding vars_clause_def subst_clause_def
    by (smt (z3) SUP_bot_conv(1) image_iff insert_iff set_image_mset set_mset_add_mset_insert)
next
  show "\<And>a. finite (vars_clause a)"
    by (simp add: vars_clause_def)
qed

lemma clause_subst_empty [clause_simp]: "{#} \<cdot> \<sigma> = {#}" "clause \<cdot> \<sigma> = {#} \<longleftrightarrow> clause = {#}"
  by (simp_all add: subst_clause_def)

lemma vars_atom [clause_simp]: 
  "vars_atom (Upair term\<^sub>1 term\<^sub>2) = vars_term term\<^sub>1 \<union> vars_term term\<^sub>2"
  by (simp_all add: vars_atom_def)

lemma vars_literal [clause_simp]: 
  "vars_literal (Pos atom) = vars_atom atom"
  "vars_literal (Neg atom) = vars_atom atom"
  "vars_literal ((if b then Pos else Neg) atom) = vars_atom atom"
  by (simp_all add: vars_literal_def)

lemma vars_clause_add_mset [clause_simp]: 
  "vars_clause (add_mset literal clause) = vars_literal literal \<union> vars_clause clause"
  by (simp add: vars_clause_def)

lemma vars_clause_plus [clause_simp]: 
  "vars_clause (clause\<^sub>1 + clause\<^sub>2) = vars_clause clause\<^sub>1 \<union> vars_clause clause\<^sub>2"
  by (simp add: vars_clause_def)

lemma clause_submset_vars_clause_subset [clause_intro]: 
  "clause\<^sub>1 \<subseteq># clause\<^sub>2 \<Longrightarrow> vars_clause clause\<^sub>1 \<subseteq> vars_clause clause\<^sub>2"
  by (metis subset_mset.add_diff_inverse sup_ge1 vars_clause_plus)

lemma empty_clause_is_ground [clause_simp]: "clause.is_ground {#}"
  unfolding vars_clause_def
  by simp 

lemma term_context_ground_iff_term_is_ground [clause_simp]:
  "Term_Context.ground term = term.is_ground term"
  by(induction "term") auto

lemma ground_ctxt_iff_context_is_ground [clause_simp]: 
  "ground_ctxt context = context.is_ground context"
  by(induction "context") clause_auto
 
lemma subst_atom [clause_simp]: 
  "Upair term\<^sub>1 term\<^sub>2 \<cdot>a \<sigma> = Upair (term\<^sub>1 \<cdot>t \<sigma>) (term\<^sub>2 \<cdot>t \<sigma>)"
  unfolding subst_atom_def
  by simp_all
  
lemma subst_literal [clause_simp]: 
  "Pos atom \<cdot>l \<sigma> = Pos (atom \<cdot>a \<sigma>)"
  "Neg atom \<cdot>l \<sigma> = Neg (atom \<cdot>a \<sigma>)"
  "atm_of (literal \<cdot>l \<sigma>) = atm_of literal \<cdot>a \<sigma>"
  unfolding subst_literal_def
  using literal.map_sel
  by auto

lemma subst_clause_add_mset [clause_simp]: 
  "add_mset literal clause \<cdot> \<sigma> = add_mset (literal \<cdot>l \<sigma>) (clause \<cdot> \<sigma>)"
  unfolding subst_clause_def
  by simp

lemma subst_clause_remove1_mset [clause_simp]: 
  assumes "literal \<in># clause" 
  shows "remove1_mset literal clause \<cdot> \<sigma> = remove1_mset (literal \<cdot>l \<sigma>) (clause \<cdot> \<sigma>)"
  unfolding subst_clause_def image_mset_remove1_mset_if
  using assms
  by simp

lemma subst_clause_plus [clause_simp]: 
  "(clause\<^sub>1 + clause\<^sub>2) \<cdot> \<sigma> = clause\<^sub>1 \<cdot> \<sigma> + clause\<^sub>2 \<cdot> \<sigma>"
  unfolding subst_clause_def
  by simp

lemma sub_ground_clause [clause_intro]: 
  assumes "clause' \<subseteq># clause" "clause.is_ground clause"
  shows "clause.is_ground clause'"
  using assms
  unfolding vars_clause_def
  by blast

lemma mset_mset_lit_subst [clause_simp]: 
  "{# term \<cdot>t \<sigma>. term \<in># mset_lit literal #} = mset_lit (literal \<cdot>l \<sigma>)"
  unfolding subst_literal_def subst_atom_def
  by (cases literal) (auto simp: mset_uprod_image_mset)

lemma term_in_literal_subst [clause_intro]: 
  assumes "term \<in># mset_lit literal" 
  shows "term \<cdot>t \<sigma> \<in># mset_lit (literal \<cdot>l \<sigma>)"
  using assms
  unfolding subst_literal_def subst_atom_def
  by (cases literal) (auto simp: uprod.set_map)

lemma literal_in_clause_subst [clause_intro]: 
  assumes "literal \<in># clause"  
  shows "literal \<cdot>l \<sigma> \<in># clause \<cdot> \<sigma>"
  using assms
  unfolding subst_clause_def
  by simp

lemma subst_polarity_stable: 
  shows 
    subst_neg_stable: "is_neg (literal \<cdot>l \<sigma>) \<longleftrightarrow> is_neg literal" and
    subst_pos_stable: "is_pos (literal \<cdot>l \<sigma>) \<longleftrightarrow> is_pos literal"
  by (simp_all add: subst_literal_def)

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

(*
This would be just confusing, right?

declare [[coercion_enabled]]
declare [[coercion to_ground_term]]
declare [[coercion to_ground_context]] 
*)

definition clause_groundings ::
  "('f, 'v) atom clause \<Rightarrow> 'f ground_atom clause set" where
  "clause_groundings clause = { to_ground_clause (clause \<cdot> \<gamma>) | \<gamma>. clause.is_ground (clause \<cdot> \<gamma>) }"

lemma to_atom_to_term [clause_simp]:
  "to_atom (Upair term\<^sub>G\<^sub>1 term\<^sub>G\<^sub>2) = Upair (to_term term\<^sub>G\<^sub>1) (to_term term\<^sub>G\<^sub>2)"
  by (simp add: to_atom_def)

lemma to_literal_to_atom [clause_simp]: 
  "to_literal (Neg atom\<^sub>G) = Neg (to_atom atom\<^sub>G)"
  "to_literal (Pos atom\<^sub>G) = Pos (to_atom atom\<^sub>G)"  
  by (simp_all add: to_literal_def)

lemma to_context_hole [clause_simp]: "to_context context\<^sub>G = \<box> \<longleftrightarrow> context\<^sub>G = \<box>\<^sub>G"
  by(cases context\<^sub>G) simp_all

lemma to_clause_empty_mset [clause_simp]: "to_clause {#} = {#}"
  by (simp add: to_clause_def)

lemma to_ground_clause_empty_mset [clause_simp]: "to_ground_clause {#} = {#}"
  by (simp add: to_ground_clause_def)

lemmas ground_term_is_ground [clause_intro] = vars_term_of_gterm

lemmas ground_context_is_ground [clause_intro] = vars_ctxt_of_gctxt

lemma term_with_context_is_ground [clause_simp]: 
  "term.is_ground context\<langle>term\<rangle> \<longleftrightarrow> context.is_ground context \<and> term.is_ground term"
  by simp

(* --- *)
lemma ground_atom_is_ground [simp]: "atom.is_ground (to_atom atom\<^sub>G)"
  unfolding to_atom_def vars_atom_def
  using ground_term_is_ground
  by (simp add: uprod.set_map)

lemma ground_literal_is_ground [simp]: "literal.is_ground (to_literal literal\<^sub>G)"
  unfolding to_literal_def vars_literal_def
  by (cases literal\<^sub>G) simp_all

lemma ground_clause_is_ground [simp]: "clause.is_ground (to_clause clause\<^sub>G)"
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
  assumes "context.is_ground context" "term.is_ground term"
  shows "(to_ground_context context)\<langle>to_ground_term term\<rangle>\<^sub>G = to_ground_term context\<langle>term\<rangle>"
  using assms
  by (simp add: term_context_ground_iff_term_is_ground)

lemma ground_term_with_context2:
  assumes "context.is_ground context"  
  shows "to_term (to_ground_context context)\<langle>term\<^sub>G\<rangle>\<^sub>G = context\<langle>to_term term\<^sub>G\<rangle>"
  using assms
  by (simp add: ground_ctxt_iff_context_is_ground ground_gctxt_of_ctxt_apply_gterm)

lemma ground_term_with_context3: 
  "(to_context context\<^sub>G)\<langle>to_term term\<^sub>G\<rangle> = to_term context\<^sub>G\<langle>term\<^sub>G\<rangle>\<^sub>G"
  using ground_term_with_context2[OF ground_context_is_ground, symmetric]
  unfolding to_context_inverse.

lemmas ground_term_with_context =
  ground_term_with_context1
  ground_term_with_context2
  ground_term_with_context3

lemma context_is_ground_context_compose1:
  assumes "context.is_ground (context \<circ>\<^sub>c context')"
  shows "context.is_ground context" "context.is_ground context'"
  using assms
  by(induction "context" context' rule: ctxt_compose.induct) auto

lemma context_is_ground_context_compose2:
  assumes "context.is_ground context" "context.is_ground context'" 
  shows "context.is_ground (context \<circ>\<^sub>c context')"
  using assms
  by (meson ground_ctxt_comp ground_ctxt_iff_context_is_ground)

lemmas context_is_ground_context_compose = 
  context_is_ground_context_compose1 
  context_is_ground_context_compose2

lemma ground_context_subst:
  assumes 
    "context.is_ground context\<^sub>G" 
    "context\<^sub>G = (context \<cdot>t\<^sub>c \<sigma>) \<circ>\<^sub>c context'"
  shows 
    "context\<^sub>G = context \<circ>\<^sub>c context' \<cdot>t\<^sub>c \<sigma>"
  using assms 
proof(induction "context")
  case Hole
  then show ?case
    by simp
next
  case More
  then show ?case
    using context_is_ground_context_compose1(2)
    by (metis subst_compose_ctxt_compose_distrib context.subst_ident_if_ground)
qed
   
lemma ground_term_subst_upd [simp]:
  assumes "term.is_ground update" "term.is_ground (term \<cdot>t \<gamma>)" 
  shows "term.is_ground (term \<cdot>t \<gamma>(var := update))"
  using assms
  by (simp add: is_ground_iff)

lemma ground_atom_subst_upd [simp]:
  assumes "term.is_ground update" "atom.is_ground (atom \<cdot>a \<gamma>)" 
  shows "atom.is_ground (atom \<cdot>a \<gamma>(var := update))"
  using assms
  unfolding subst_atom_def vars_atom_def
  by(cases atom) simp

lemma ground_literal_subst_upd [simp]:
  assumes "term.is_ground update" "literal.is_ground (literal \<cdot>l \<gamma>)" 
  shows "literal.is_ground (literal \<cdot>l \<gamma>(var := update))"
  using assms
  unfolding subst_literal_def vars_literal_def
  by(cases literal) simp_all

lemma ground_clause_subst_upd [simp]:
  assumes "term.is_ground update" "clause.is_ground (clause \<cdot> \<gamma>)" 
  shows "clause.is_ground (clause \<cdot> \<gamma>(var := update))"
  using assms
  unfolding subst_clause_def vars_clause_def
  by auto

lemmas to_term_inj = inj_term_of_gterm

(* TODO: *)
lemma "surj to_ground_term"
  unfolding surj_def
  by (metis to_term_inverse)

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

lemma to_clause_add_mset [clause_simp]: 
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

lemma ground_term_in_ground_atom [clause_simp]:
  assumes "term \<in> set_uprod atom" "atom.is_ground atom"
  shows "term.is_ground term"
  using assms
  by (simp add: vars_atom_def)

lemma ground_terms_in_ground_atom1:
  assumes "term.is_ground term\<^sub>1" and "term.is_ground term\<^sub>2"
  shows "Upair (to_ground_term term\<^sub>1) (to_ground_term term\<^sub>2) = to_ground_atom (Upair term\<^sub>1 term\<^sub>2)"
  using assms
  by (simp add: to_ground_atom_def)

lemma ground_terms_in_ground_atom2 [clause_simp]: 
  "atom.is_ground (Upair term\<^sub>1 term\<^sub>2) \<longleftrightarrow> term.is_ground term\<^sub>1 \<and> term.is_ground term\<^sub>2"
  by clause_simp

lemmas ground_terms_in_ground_atom = 
  ground_terms_in_ground_atom1
  ground_terms_in_ground_atom2

lemma ground_atom_in_ground_literal1 [intro]:
  assumes "atom \<in> set_literal literal" "literal.is_ground literal" 
  shows "atom.is_ground atom"
  using assms
  by (simp add: set_literal_atm_of vars_literal_def)

lemma ground_atom_in_ground_literal2:
  shows "Pos (to_ground_atom atom) = to_ground_literal (Pos atom)" 
    "Neg (to_ground_atom atom) = to_ground_literal (Neg atom)" 
  by (simp_all add: to_ground_atom_def to_ground_literal_def)

lemmas ground_atom_in_ground_literal = 
  ground_atom_in_ground_literal1
  ground_atom_in_ground_literal2

lemma atom_is_ground_in_ground_literal [intro]:
  "literal.is_ground literal \<longleftrightarrow> atom.is_ground (atm_of literal)"
  by (simp add: vars_literal_def)  

lemma ground_term_in_ground_literal:
  assumes "literal.is_ground literal"  "term \<in># mset_lit literal"  
  shows "term.is_ground term"
  using assms
  apply(cases literal)
   apply(clause_simp simp:  ground_term_in_ground_atom)
   apply (simp add: ground_term_in_ground_atom)
  by (simp add: ground_term_in_ground_atom)
  

lemma ground_term_in_ground_literal_subst:
  assumes "literal.is_ground (literal \<cdot>l \<gamma>)" "term \<in># mset_lit literal"  
  shows "term.is_ground (term \<cdot>t \<gamma>)"
  using ground_term_in_ground_literal[OF assms(1) term_in_literal_subst[OF assms(2)]].

lemma ground_literal_in_ground_clause1:
  assumes "literal \<in># clause" "clause.is_ground clause" 
  shows "literal.is_ground literal"
  using assms
  by (simp add: vars_clause_def)

lemma ground_literal_in_ground_clause2: 
  "literal \<in># to_clause clause\<^sub>G \<Longrightarrow> literal.is_ground literal"
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
  assumes "clause.is_ground (clause \<cdot> \<gamma>)"  "literal \<in># clause"  
  shows "literal.is_ground (literal \<cdot>l \<gamma>)"
  using assms
  unfolding subst_clause_def vars_clause_def
  by simp

lemma to_ground_term_inverse [simp]:
  assumes "term.is_ground term"  
  shows "to_term (to_ground_term term) = term"
  using assms
  by (cases "term") (simp_all add: map_idI term_context_ground_iff_term_is_ground)

lemma to_ground_atom_inverse [simp]: 
  assumes "atom.is_ground atom"  
  shows "to_atom (to_ground_atom atom) = atom"
  using assms to_ground_term_inverse ground_term_in_ground_atom map_uprod_inverse to_term_inverse
  unfolding to_ground_atom_def
  by (smt (verit, ccfv_SIG) to_atom_def uprod.inj_map_strong ground_atom_is_ground)

lemma to_ground_literal_inverse [simp]: 
  assumes "literal.is_ground literal"  
  shows "to_literal (to_ground_literal literal) = literal"
  using assms ground_atom_in_ground_literal(1)[THEN to_ground_atom_inverse]
  unfolding to_ground_literal_def to_literal_def vars_literal_def
  by (simp add: literal.expand literal.map_sel)

lemma to_ground_clause_inverse [simp]: 
  assumes "clause.is_ground clause"  
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

lemma clause_is_ground_add_mset [clause_simp]: "clause.is_ground (add_mset literal clause) \<longleftrightarrow> 
  literal.is_ground literal \<and> clause.is_ground clause"
  by clause_auto

lemma to_ground_clause_add_mset:
  assumes "to_clause clause = add_mset literal clause'" 
  shows "clause = add_mset (to_ground_literal literal) (to_ground_clause clause')"
  using assms
  by (metis to_clause_inverse to_ground_clause_def image_mset_add_mset)

lemma obtain_from_atom_subst [clause_intro]: 
  assumes "Upair term\<^sub>1' term\<^sub>2' = atom \<cdot>a \<sigma>"
  obtains term\<^sub>1 term\<^sub>2 
  where "atom = Upair term\<^sub>1 term\<^sub>2" "term\<^sub>1' = term\<^sub>1 \<cdot>t \<sigma>" "term\<^sub>2' = term\<^sub>2 \<cdot>t \<sigma>"
  using assms
  unfolding subst_atom_def
  by(cases atom) auto

lemma obtain_from_pos_literal_subst [clause_intro]: 
  assumes "literal \<cdot>l \<sigma> = term\<^sub>1' \<approx> term\<^sub>2'"
  obtains term\<^sub>1 term\<^sub>2 
  where "literal = term\<^sub>1 \<approx> term\<^sub>2" "term\<^sub>1' = term\<^sub>1 \<cdot>t \<sigma>" "term\<^sub>2' = term\<^sub>2 \<cdot>t \<sigma>"
  using assms obtain_from_atom_subst subst_pos_stable
  by (metis is_pos_def literal.sel(1) subst_literal(1))

lemma obtain_from_neg_literal_subst: 
  assumes "literal \<cdot>l \<sigma> = term\<^sub>1' !\<approx> term\<^sub>2'"
  obtains term\<^sub>1 term\<^sub>2 
  where "literal = term\<^sub>1 !\<approx> term\<^sub>2" "term\<^sub>1 \<cdot>t \<sigma> = term\<^sub>1'" "term\<^sub>2 \<cdot>t \<sigma> = term\<^sub>2'"
  using assms obtain_from_atom_subst subst_neg_stable
  by (metis literal.collapse(2) literal.disc(2) literal.sel(2) subst_literal(3))

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
  assumes "\<not> term.is_ground term"
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
  obtain t\<^sub>G :: "('b, 'a) Term.term" where "term.is_ground t\<^sub>G"
    by (meson ground_term_is_ground)

  then have "term_subst.is_ground_subst  (\<lambda>_. t\<^sub>G)"
    by (simp add: is_ground_iff term_subst.is_ground_subst_def)

  with that show ?thesis
    by blast
qed

lemma ground_subst_exstension_term:
  assumes "term.is_ground (term \<cdot>t \<gamma>)"
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
  assumes "atom.is_ground (atom \<cdot>a \<gamma>)"
  obtains \<gamma>'
  where "atom \<cdot>a \<gamma> = atom \<cdot>a \<gamma>'" and "term_subst.is_ground_subst \<gamma>'"
  by (metis assms atom.subst_comp_subst term_subst.is_ground_subst_comp_right obtain_ground_subst 
        atom.subst_ident_if_ground)

lemma ground_subst_exstension_literal:
  assumes "literal.is_ground (literal \<cdot>l \<gamma>)"
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
  assumes "clause.is_ground (clause \<cdot> \<gamma>)"
  obtains \<gamma>'
  where "clause \<cdot> \<gamma> = clause \<cdot> \<gamma>'" and "term_subst.is_ground_subst \<gamma>'"
  by (metis assms clause.subst_comp_subst term_subst.is_ground_subst_comp_right obtain_ground_subst 
      clause.subst_ident_if_ground)

lemma non_ground_arg: 
  assumes "\<not> term.is_ground (Fun f terms)"
  obtains "term"
  where "term \<in> set terms" "\<not> term.is_ground term"
  using assms that by fastforce

lemma non_ground_arg': 
  assumes "\<not> term.is_ground (Fun f terms)"
  obtains ts1 var ts2 
  where "terms = ts1 @ [var] @ ts2" "\<not> term.is_ground var"
  using non_ground_arg
  by (metis append.left_neutral append_Cons assms split_list)

subsection \<open>Interpretations\<close>

lemma vars_term_ms_count:
  assumes "term.is_ground term\<^sub>G"
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
    update_is_ground: "term.is_ground update" and
    var_grounding: "term.is_ground (Var var \<cdot>t \<gamma>)" 
begin

lemma interpretation_term_congruence:
  assumes 
    term_grounding: "term.is_ground (term \<cdot>t \<gamma>)" and
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
    using term.subst_reduntant_upd 
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

  moreover have "term.is_ground (context\<langle>update\<rangle> \<cdot>t \<gamma>)"
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
    term_grounding: "term.is_ground (term \<cdot>t \<gamma>)" and
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
    "term.is_ground (term\<^sub>1 \<cdot>t \<gamma>)" 
    "term.is_ground (term\<^sub>2 \<cdot>t \<gamma>)" 
    "(to_ground_term (\<gamma> var), to_ground_term update) \<in> I"
    "(to_ground_term (term\<^sub>1 \<cdot>t \<gamma>(var := update)), to_ground_term (term\<^sub>2 \<cdot>t \<gamma>(var := update))) \<in> I" 
  shows
    "(to_ground_term (term\<^sub>1 \<cdot>t \<gamma>), to_ground_term (term\<^sub>2 \<cdot>t \<gamma>)) \<in> I"
  using assms
  by (metis interpretation_term_congruence sym symE)

lemma interpretation_atom_congruence':
  assumes 
    "term.is_ground (term\<^sub>1 \<cdot>t \<gamma>)" 
    "term.is_ground (term\<^sub>2 \<cdot>t \<gamma>)" 
    "(to_ground_term (\<gamma> var), to_ground_term update) \<in> I"
    "(to_ground_term (term\<^sub>1 \<cdot>t \<gamma>(var := update)), to_ground_term (term\<^sub>2 \<cdot>t \<gamma>(var := update))) \<notin> I" 
  shows
    "(to_ground_term (term\<^sub>1 \<cdot>t \<gamma>), to_ground_term (term\<^sub>2 \<cdot>t \<gamma>)) \<notin> I"
  using assms
  by (metis interpretation_term_congruence' sym symE)

lemma interpretation_literal_congruence:
  assumes
    "literal.is_ground (literal \<cdot>l \<gamma>)"
    "upair ` I \<TTurnstile>l to_ground_term (Var var \<cdot>t \<gamma>) \<approx> to_ground_term update"
    "upair ` I \<TTurnstile>l to_ground_literal (literal \<cdot>l \<gamma>(var := update))"
  shows
    "upair ` I \<TTurnstile>l to_ground_literal (literal \<cdot>l \<gamma>)"
proof(cases literal)
  case (Pos atom)

  have "to_ground_atom (atom \<cdot>a \<gamma>) \<in> upair ` I"
  proof(cases atom)
    case (Upair term\<^sub>1 term\<^sub>2)  
    then have term_groundings: "term.is_ground (term\<^sub>1 \<cdot>t \<gamma>)" "term.is_ground (term\<^sub>2 \<cdot>t \<gamma>)"
      using Pos assms
      by clause_auto

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
    then have term_groundings: "term.is_ground (term\<^sub>1 \<cdot>t \<gamma>)" "term.is_ground (term\<^sub>2 \<cdot>t \<gamma>)"
      using Neg assms
      by clause_auto

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
    "clause.is_ground (clause \<cdot> \<gamma>)" 
    "upair ` I \<TTurnstile>l to_ground_term (Var var \<cdot>t \<gamma>) \<approx> to_ground_term update"
    "upair ` I \<TTurnstile> to_ground_clause (clause \<cdot> \<gamma>(var := update))"
  shows
    "upair ` I \<TTurnstile> to_ground_clause (clause \<cdot> \<gamma>)"
  using assms
proof(induction "clause")
  case empty
  then show ?case 
    by clause_simp
next
  case (add literal clause')

  have clause'_grounding: "clause.is_ground (clause' \<cdot> \<gamma>)"
    by (metis add.prems(1) clause_is_ground_add_mset subst_clause_add_mset)

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
      by (metis clause_is_ground_add_mset subst_clause_add_mset)

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
  by(induction clause)(clause_auto simp: image_Un)

lemma surj_the_inv: "surj (\<lambda>x. the_inv \<rho> (Var x))"
  by (metis is_Var_def renaming surj_def term_subst_is_renaming_iff the_inv_f_f)

end

lemma needed: "surj g \<Longrightarrow> infinite {x. f x = ty} \<Longrightarrow> infinite {x. f (g x) = ty}"
  by (smt (verit) UNIV_I finite_imageI image_iff mem_Collect_eq rev_finite_subset subset_eq)

lemma obtain_ground_fun:
  assumes "term.is_ground t"
  obtains f ts where "t = Fun f ts"
  using assms
  by(cases t) auto

lemma vars_term_subst: "vars_term (t \<cdot>t \<sigma>) \<subseteq> vars_term t \<union> range_vars \<sigma>"
  by (meson Diff_subset order_refl subset_trans sup.mono vars_term_subst_apply_term_subset)

lemma vars_term_imgu [clause_intro]:
  assumes "term_subst.is_imgu \<mu> {{s, s'}}"
  shows "vars_term (t \<cdot>t \<mu>) \<subseteq> vars_term t \<union> vars_term s \<union> vars_term s'"
  using range_vars_subset_if_is_imgu[OF assms] vars_term_subst
  by fastforce

lemma vars_context_imgu [clause_intro]:
  assumes "term_subst.is_imgu \<mu> {{s, s'}}"
  shows "vars_context (c \<cdot>t\<^sub>c \<mu>) \<subseteq> vars_context c \<union> vars_term s \<union> vars_term s'"
  using  vars_term_imgu[OF assms]
  by (smt (verit, ccfv_threshold) Un_iff subset_iff subst_apply_term_ctxt_apply_distrib vars_term_ctxt_apply)

lemma vars_atom_imgu [clause_intro]:
  assumes "term_subst.is_imgu \<mu> {{s, s'}}"
  shows "vars_atom (a \<cdot>a \<mu>) \<subseteq> vars_atom a \<union> vars_term s \<union> vars_term s'"
  using vars_term_imgu[OF assms]
  unfolding vars_atom_def subst_atom_def 
  by(cases a) auto

lemma vars_literal_imgu [clause_intro]:
  assumes "term_subst.is_imgu \<mu> {{s, s'}}"
  shows "vars_literal (l \<cdot>l \<mu>) \<subseteq> vars_literal l \<union> vars_term s \<union> vars_term s'"
  using vars_atom_imgu[OF assms]
  unfolding vars_literal_def subst_literal
  by blast

lemma vars_clause_imgu [clause_intro]:
  assumes "term_subst.is_imgu \<mu> {{s, s'}}"
  shows "vars_clause (c \<cdot> \<mu>) \<subseteq> vars_clause c \<union> vars_term s \<union> vars_term s'"
  using vars_literal_imgu[OF assms]
  unfolding vars_clause_def subst_clause_def
  by blast

end
