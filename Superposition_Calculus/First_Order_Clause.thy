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

lemmas clause_simp_term =
  subst_apply_term_ctxt_apply_distrib vars_term_ctxt_apply literal.sel

named_theorems clause_simp
named_theorems clause_intro

lemma ball_set_uprod [clause_simp]: "(\<forall>t\<in>set_uprod (Upair t\<^sub>1 t\<^sub>2). P t) \<longleftrightarrow> P t\<^sub>1 \<and> P t\<^sub>2"
  by auto

lemma infinite_terms [clause_intro]: "infinite (UNIV :: ('f, 'v) term set)"
proof-
  have "infinite (UNIV :: ('f, 'v) term list set)"
    using infinite_UNIV_listI.

  then have "\<And>f :: 'f. infinite ((Fun f) ` (UNIV :: ('f, 'v) term list set))"
    by (meson finite_imageD injI term.inject(2))

  then show "infinite (UNIV :: ('f, 'v) term set)"
    using infinite_super top_greatest by blast
qed

lemma literal_cases: "\<lbrakk>\<P> \<in> {Pos, Neg}; \<P> = Pos \<Longrightarrow> P; \<P> = Neg \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by blast

(* TODO: cases *)
method clause_simp uses (* cases*) simp intro =
  (*(-, (rule literal_cases[OF cases]))?,*)
  auto simp only: simp clause_simp clause_simp_term intro: intro clause_intro

method clause_auto uses simp intro = 
  (clause_simp simp: simp intro: intro)?,  
  (auto simp: simp intro intro)?, 
  (auto simp: simp clause_simp intro: intro clause_intro)?

type_synonym 'f ground_term = "'f gterm"

type_synonym 'f ground_context = "'f gctxt"
type_synonym ('f, 'v) "context" = "('f, 'v) ctxt"

type_synonym 'f ground_atom = "'f gatom"
type_synonym ('f, 'v) atom = "('f, 'v) term uprod"

(* Just for unified naming *)
locale vars = 
  fixes vars_def :: "'expression \<Rightarrow> 'variables" 
begin 

abbreviation "vars \<equiv> vars_def"

end

global_interpretation "term": vars where vars_def = vars_term.

global_interpretation "context": vars where vars_def = vars_ctxt.

(*
TODO: (automatically? )
definition vars_clause_set :: "('f, 'v) atom clause set \<Rightarrow> 'v set" where
  "vars_clause_set clauses = (\<Union>clause \<in> clauses. vars_clause clause)"
*)

global_interpretation
  "term": variable_substitution_base_set 
  where
    subst = subst_apply_term and id_subst = Var and comp_subst = subst_compose and 
    vars = term.vars +
  "term": finite_variables
  where 
    is_finite = finite and vars = term.vars +
  "term": all_subst_ident_iff_ground
  where
    is_ground = term.is_ground and subst = subst_apply_term and is_finite = finite and 
    contains = "(\<in>)"
proof unfold_locales 
  show "\<And>t \<sigma> \<tau>. (\<And>x. x \<in> term.vars t \<Longrightarrow> \<sigma> x = \<tau> x) \<Longrightarrow> t \<cdot>t \<sigma> = t \<cdot>t \<tau>"
    using term_subst_eq.
next
  show "\<And>t. finite (term.vars t)"
    by simp
next
  show "\<And>t. (term.vars t = {}) = (\<forall>\<sigma>. t \<cdot>t \<sigma> = t)"
    using is_ground_trm_iff_ident_forall_subst.
next
  (* TODO: type variables *)
  fix t :: "('e, 'f) term" and ts :: "('e, 'f) term set"

  assume "finite ts" "term.vars t \<noteq> {}"
  then show "\<exists>\<sigma>. t \<cdot>t \<sigma> \<noteq> t \<and> t \<cdot>t \<sigma> \<notin> ts"
  proof(induction t arbitrary: ts)
    case (Var x)

    obtain t' where t': "t' \<notin> ts" "is_Fun t'"
      using Var.prems(1) finite_list by blast

    define \<sigma> :: "('e, 'f) subst" where "\<And>x. \<sigma> x = t'"

    have "Var x \<cdot>t \<sigma> \<noteq> Var x"
      using t'
      unfolding \<sigma>_def
      by auto

    moreover have "Var x \<cdot>t \<sigma> \<notin> ts"
      using t'
      unfolding \<sigma>_def
      by simp

    ultimately show ?case
      using Var
      by blast
  next
    case (Fun f args)

    obtain a where a: "a \<in> set args" and a_vars: "term.vars a \<noteq> {}"
      using Fun.prems by fastforce

    then obtain \<sigma> where 
      \<sigma>: "a \<cdot>t \<sigma> \<noteq> a" and
      a_\<sigma>_not_in_args: "a \<cdot>t \<sigma> \<notin> \<Union> (set `  term.args ` ts)"
      by (metis Fun.IH Fun.prems(1) List.finite_set finite_UN finite_imageI)

    then have "Fun f args \<cdot>t \<sigma> \<noteq> Fun f args"
      by (metis a subsetI term.set_intros(4) term_subst.comp_subst.left.action_neutral 
          vars_term_subset_subst_eq)

    moreover have "Fun f args \<cdot>t \<sigma> \<notin> ts"
      using a a_\<sigma>_not_in_args
      by auto

    ultimately show ?case
      using Fun
      by blast
  qed
next
  show "\<And>\<gamma> t. (term.vars (t \<cdot>t \<gamma>) = {}) = (\<forall>x. x \<in> term.vars t \<longrightarrow> term.vars (\<gamma> x) = {})"
    by (meson is_ground_iff)
next
  show "\<exists>t. term.vars t = {}"
    by (meson vars_term_of_gterm)
qed

(* TODO: Use locale *)
lemma context_is_ground_iff_ident_forall_subst:
  fixes \<kappa> :: "('f, 'v) context"
  shows "context.vars \<kappa> = {} \<longleftrightarrow> (\<forall>\<sigma>. \<kappa> \<cdot>t\<^sub>c \<sigma> = \<kappa>)" 
proof (intro iffI)
  show "context.vars \<kappa> = {} \<Longrightarrow> \<forall>\<sigma>. \<kappa> \<cdot>t\<^sub>c \<sigma> = \<kappa>"
    by(induction \<kappa>) (simp_all add: list.map_ident_strong)
next
  assume "\<forall>\<sigma>. \<kappa> \<cdot>t\<^sub>c \<sigma> = \<kappa>"

  then have "\<And>t\<^sub>G. term.is_ground t\<^sub>G \<Longrightarrow> \<forall>\<sigma>. \<kappa>\<langle>t\<^sub>G\<rangle> \<cdot>t \<sigma> = \<kappa>\<langle>t\<^sub>G\<rangle>"
    by simp

  then have "\<And>t\<^sub>G. term.is_ground t\<^sub>G \<Longrightarrow> term.is_ground \<kappa>\<langle>t\<^sub>G\<rangle>"
    by (meson is_ground_trm_iff_ident_forall_subst)

  then show "context.vars \<kappa> = {}"
    by (metis sup.commute sup_bot_left vars_term_ctxt_apply vars_term_of_gterm)
qed

global_interpretation "context": variable_substitution_expansion_set where
   expanded_subst = subst_apply_ctxt and expanded_vars = context.vars and id_subst = Var and 
   comp_subst = subst_compose and vars = term.vars and subst = subst_apply_term
proof unfold_locales
  fix \<kappa> :: "('f, 'v) context"
  show "\<kappa> \<cdot>t\<^sub>c Var = \<kappa>"
    by (induction \<kappa>) auto
next
  show "\<And>\<kappa> \<sigma> \<tau>. \<kappa> \<cdot>t\<^sub>c \<sigma> \<odot> \<tau> = \<kappa> \<cdot>t\<^sub>c \<sigma> \<cdot>t\<^sub>c \<tau>"
    by simp
next
  show "\<And>\<kappa>. context.vars \<kappa> = {} \<Longrightarrow> \<forall>\<sigma>. \<kappa> \<cdot>t\<^sub>c \<sigma> = \<kappa>"
    by (simp add: context_is_ground_iff_ident_forall_subst)
next 
  show "\<And>a \<sigma> \<tau>. (\<And>x. x \<in> context.vars a \<Longrightarrow> \<sigma> x = \<tau> x) \<Longrightarrow> a \<cdot>t\<^sub>c \<sigma> = a \<cdot>t\<^sub>c \<tau>"
    using ctxt_subst_eq.
next
  fix \<gamma> :: "('f,'v) subst"

  show "(\<forall>\<kappa>. context.vars (\<kappa> \<cdot>t\<^sub>c \<gamma>) = {}) = (\<forall>t. term.is_ground (t \<cdot>t \<gamma>))"
  proof(intro iffI allI equals0I)
    fix t x

    assume is_ground: "\<forall>\<kappa>. context.vars (\<kappa> \<cdot>t\<^sub>c \<gamma>) = {}" and vars: "x \<in> term.vars (t \<cdot>t \<gamma>)"

    have "\<And>f. context.vars (More f [t] Hole [] \<cdot>t\<^sub>c \<gamma>) = {}"
      using is_ground
      by presburger

    moreover have "\<And>f. x \<in> context.vars (More f [t] Hole [] \<cdot>t\<^sub>c \<gamma>)"
      using vars
      by simp
      
    ultimately show False
      by blast
  next
    fix \<kappa> x
    assume is_ground: "\<forall>t. term.is_ground (t \<cdot>t \<gamma>)" and vars: "x \<in> context.vars (\<kappa> \<cdot>t\<^sub>c \<gamma>)"

    have "\<And>t. term.is_ground (\<kappa>\<langle>t\<rangle> \<cdot>t \<gamma>)"
      using is_ground
      by presburger

    moreover have "\<And>t. x \<in> term.vars (\<kappa>\<langle>t\<rangle> \<cdot>t \<gamma>)"
      using vars
      by simp

    ultimately show False
      by blast
  qed
next
  fix \<kappa> and \<gamma> :: "('f, 'v) subst"

  show "(context.vars (\<kappa> \<cdot>t\<^sub>c \<gamma>) = {}) = (\<forall>x. x \<in> context.vars \<kappa> \<longrightarrow> term.is_ground (\<gamma> x))"
    by(induction \<kappa>)(auto simp: term.is_ground_iff)
qed

global_interpretation "context": finite_variables where 
  is_finite = finite and vars = context.vars
proof unfold_locales 
  fix \<kappa> :: "('f, 'v) context"

  have "\<And>t. finite (term.vars \<kappa>\<langle>t\<rangle>)"
    using term.finite_vars by blast

  then show "finite (context.vars \<kappa>)"
    unfolding vars_term_ctxt_apply finite_Un
    by simp
qed



lemma Union_range_set_uprod: "\<Union> (range set_uprod) = UNIV"
  by (metis UNIV_I UNIV_eq_I UN_iff insert_iff set_uprod_simps)



lemma "\<Union> (range f) = UNIV \<longleftrightarrow> (\<forall>x. \<exists>y. x \<in> f y)"
  by auto

lemma Union_range_set_literal: "\<Union> (range set_literal) = UNIV"
  unfolding set_literal_atm_of   
  by (metis (no_types, lifting) UNIV_eq_I Union_iff literal.sel(2) image_insert insertI1 
      insert_UNIV)

lemma Union_range_set_mset: "\<Union> (range set_mset) = UNIV"
  by (metis UNIV_eq_I Union_iff multi_member_this rangeI)

lemma finite_set_literal: "\<And>l. finite (set_literal l)"
  unfolding set_literal_atm_of
  by simp

global_interpretation atom: mylifting
  where comp_subst = subst_compose and id_subst = Var and 
    base_subst = subst_apply_term and base_vars = term.vars and map = map_uprod and
    to_set = set_uprod and base'_subst = subst_apply_term and base'_vars = term.vars
  apply 
    unfold_locales 
   apply (auto simp: uprod.map_comp uprod.map_id uprod.set_map Union_range_set_uprod term.is_ground_iff
       intro: uprod.map_cong)
  using Union_range_set_uprod by auto

find_theorems name: atom.obtain

global_interpretation literal: mylifting
  where comp_subst = subst_compose and id_subst = Var and 
    base_subst = atom.subst and base_vars = atom.vars and map = map_literal and
    to_set = set_literal and base'_subst = subst_apply_term and base'_vars = term.vars
  apply
    unfold_locales 
  apply (auto simp: literal.map_comp literal.map_id literal.set_map Union_range_set_literal atom.is_ground_iff
      finite_set_literal intro: literal.map_cong)
  by (meson literal.set_intros(1))

global_interpretation clause: mylifting
  where comp_subst = subst_compose and id_subst = Var and 
    base_subst = literal.subst and base_vars = literal.vars and map = image_mset and
    to_set = set_mset and base'_subst = subst_apply_term and base'_vars = term.vars
  apply unfold_locales apply(auto simp: Union_range_set_mset literal.is_ground_iff)
  by (meson multi_member_last)

notation atom.subst (infixl "\<cdot>a" 67)
notation literal.subst (infixl "\<cdot>l" 66)
notation clause.subst (infixl "\<cdot>" 67)

(* TODO: Directly from "is_ground {#}" *)
lemma clause_subst_empty [clause_simp]: "{#} \<cdot> \<sigma> = {#}" "clause \<cdot> \<sigma> = {#} \<longleftrightarrow> clause = {#}"
  by (simp_all add: clause.subst_def)

lemma vars_atom [clause_simp]: 
  "atom.vars (Upair term\<^sub>1 term\<^sub>2) = term.vars term\<^sub>1 \<union> term.vars term\<^sub>2"
  by (simp_all add: atom.vars_def)

lemma vars_literal [clause_simp]: 
  "literal.vars (Pos atom) = atom.vars atom"
  "literal.vars (Neg atom) = atom.vars atom"
  "literal.vars ((if b then Pos else Neg) atom) = atom.vars atom"
  by (simp_all add: literal.vars_def)

(* TODO: Can these be generalized? *)
lemma vars_clause_add_mset [clause_simp]: 
  "clause.vars (add_mset literal clause) = literal.vars literal \<union> clause.vars clause"
  by (simp add: clause.vars_def)

lemma vars_clause_plus [clause_simp]: 
  "clause.vars (clause\<^sub>1 + clause\<^sub>2) = clause.vars clause\<^sub>1 \<union> clause.vars clause\<^sub>2"
  by (simp add: clause.vars_def)

lemma clause_submset_vars_clause_subset [clause_intro]: 
  "clause\<^sub>1 \<subseteq># clause\<^sub>2 \<Longrightarrow> clause.vars clause\<^sub>1 \<subseteq> clause.vars clause\<^sub>2"
  by (metis subset_mset.add_diff_inverse sup_ge1 vars_clause_plus)

lemma empty_clause_is_ground [clause_simp]: "clause.is_ground {#}"
  unfolding clause.vars_def
  by simp 

lemma term_context_ground_iff_term_is_ground [clause_simp]:
  "Term_Context.ground term = term.is_ground term"
  by(induction "term") auto

lemma ground_ctxt_iff_context_is_ground [clause_simp]: 
  "ground_ctxt context = context.is_ground context"
  by(induction "context") clause_auto
 
lemma subst_atom [clause_simp]: 
  "Upair term\<^sub>1 term\<^sub>2 \<cdot>a \<sigma> = Upair (term\<^sub>1 \<cdot>t \<sigma>) (term\<^sub>2 \<cdot>t \<sigma>)"
  unfolding atom.subst_def
  by simp_all
  
lemma subst_literal [clause_simp]: 
  "Pos atom \<cdot>l \<sigma> = Pos (atom \<cdot>a \<sigma>)"
  "Neg atom \<cdot>l \<sigma> = Neg (atom \<cdot>a \<sigma>)"
  "atm_of (literal \<cdot>l \<sigma>) = atm_of literal \<cdot>a \<sigma>"
  unfolding literal.subst_def
  using literal.map_sel
  by auto

(* TODO: Can these be generalized? *)
lemma subst_clause_add_mset [clause_simp]: 
  "add_mset literal clause \<cdot> \<sigma> = add_mset (literal \<cdot>l \<sigma>) (clause \<cdot> \<sigma>)"
  unfolding clause.subst_def
  by simp

lemma subst_clause_remove1_mset [clause_simp]: 
  assumes "literal \<in># clause" 
  shows "remove1_mset literal clause \<cdot> \<sigma> = remove1_mset (literal \<cdot>l \<sigma>) (clause \<cdot> \<sigma>)"
  unfolding clause.subst_def image_mset_remove1_mset_if
  using assms
  by simp

lemma subst_clause_plus [clause_simp]: 
  "(clause\<^sub>1 + clause\<^sub>2) \<cdot> \<sigma> = clause\<^sub>1 \<cdot> \<sigma> + clause\<^sub>2 \<cdot> \<sigma>"
  unfolding clause.subst_def
  by simp

lemma sub_ground_clause [clause_intro]: 
  assumes "clause' \<subseteq># clause" "clause.is_ground clause"
  shows "clause.is_ground clause'"
  using assms
  unfolding clause.vars_def
  by blast

lemma mset_mset_lit_subst [clause_simp]: 
  "{# term \<cdot>t \<sigma>. term \<in># mset_lit literal #} = mset_lit (literal \<cdot>l \<sigma>)"
  unfolding literal.subst_def atom.subst_def
  by (cases literal) (auto simp: mset_uprod_image_mset)

(* TODO: Use subst_in_to_set_subst *)
lemma term_in_literal_subst [clause_intro]: 
  assumes "term \<in># mset_lit literal" 
  shows "term \<cdot>t \<sigma> \<in># mset_lit (literal \<cdot>l \<sigma>)"
  using assms
  unfolding literal.subst_def atom.subst_def
  by (cases literal) (auto simp: uprod.set_map)

lemma literal_in_clause_subst [clause_intro]: 
  assumes "literal \<in># clause"  
  shows "literal \<cdot>l \<sigma> \<in># clause \<cdot> \<sigma>"
  using assms
  unfolding clause.subst_def
  by simp

lemma subst_polarity_stable: 
  shows 
    subst_neg_stable: "is_neg (literal \<cdot>l \<sigma>) \<longleftrightarrow> is_neg literal" and
    subst_pos_stable: "is_pos (literal \<cdot>l \<sigma>) \<longleftrightarrow> is_pos literal"
  by (simp_all add: literal.subst_def)

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

lemma ground_atom_is_ground [simp]: "atom.is_ground (to_atom atom\<^sub>G)"
  unfolding to_atom_def atom.vars_def
  using ground_term_is_ground
  by (simp add: uprod.set_map)

lemma ground_literal_is_ground [simp]: "literal.is_ground (to_literal literal\<^sub>G)"
  unfolding to_literal_def literal.vars_def
  by (cases literal\<^sub>G) simp_all

lemma ground_clause_is_ground [simp]: "clause.is_ground (to_clause clause\<^sub>G)"
  unfolding to_clause_def clause.vars_def
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
  unfolding atom.subst_def atom.vars_def
  by(cases atom) simp

lemma ground_literal_subst_upd [simp]:
  assumes "term.is_ground update" "literal.is_ground (literal \<cdot>l \<gamma>)" 
  shows "literal.is_ground (literal \<cdot>l \<gamma>(var := update))"
  using assms
  unfolding literal.subst_def literal.vars_def
  by(cases literal) simp_all

lemma ground_clause_subst_upd [simp]:
  assumes "term.is_ground update" "clause.is_ground (clause \<cdot> \<gamma>)" 
  shows "clause.is_ground (clause \<cdot> \<gamma>(var := update))"
  using clause.ground_subst_upd[OF assms].
  

lemmas to_term_inj = inj_term_of_gterm


  

(* TODO: *)
lemma surj_to_ground_term: "surj to_ground_term"
  unfolding surj_def
  by (metis to_term_inverse)

(*global_interpretation "term" : grounding
  where to_ground = to_ground_term and from_ground = to_term
  apply unfold_locales
  by (auto simp: surj_to_ground_term to_term_inj)*)

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
  by (simp add: atom.vars_def)

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
  by (simp add: literal.vars_def)

lemma ground_atom_in_ground_literal2:
  shows "Pos (to_ground_atom atom) = to_ground_literal (Pos atom)" 
    "Neg (to_ground_atom atom) = to_ground_literal (Neg atom)" 
  by (simp_all add: to_ground_atom_def to_ground_literal_def)

lemmas ground_atom_in_ground_literal = 
  ground_atom_in_ground_literal1
  ground_atom_in_ground_literal2

lemma atom_is_ground_in_ground_literal [intro]:
  "literal.is_ground literal \<longleftrightarrow> atom.is_ground (atm_of literal)"
  by (simp add: literal.vars_def set_literal_atm_of)

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
  by (simp add: clause.vars_def)

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
  unfolding clause.subst_def clause.vars_def
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
  unfolding to_ground_literal_def to_literal_def
  by (simp add: atom_is_ground_in_ground_literal literal.expand literal.map_sel)
 
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
  unfolding atom.subst_def
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

lemma var_is_not_ground: "is_Var t \<Longrightarrow> \<not>term.is_ground t"
  by (metis empty_iff term.set_sel(3))

lemma subst_cannot_add_var:
  assumes "is_Var (term \<cdot>t \<sigma>)"  
  shows "is_Var term"
  using assms term.subst_cannot_unground[OF var_is_not_ground] 
  by fastforce

lemma var_in_term:
  assumes "var \<in> term.vars term"
  obtains "context" where "term = context\<langle>Var var\<rangle>"
  using assms
proof(induction "term")
  case Var
  then show ?case
    by (metis Term.term.simps(17) ctxt_apply_term.simps(1) singletonD)
next
  case (Fun f args)
  then obtain term' where "term' \<in> set args " "var \<in> term.vars term'"
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
  obtain var where "var \<in> term.vars term"
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
    \<gamma>':  "\<gamma>' = (\<lambda>var. if var \<in> term.vars term then \<gamma> var else \<gamma>'' var)"

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
  using atom.ground_subst_extension[OF assms]
  by auto

lemma ground_subst_exstension_literal:
  assumes "literal.is_ground (literal \<cdot>l \<gamma>)"
  obtains \<gamma>'
  where "literal \<cdot>l \<gamma> = literal \<cdot>l \<gamma>'" and "term_subst.is_ground_subst \<gamma>'"
proof(cases literal)
  case (Pos a)
  then show ?thesis
    using assms that ground_subst_exstension_atom[of a \<gamma>]
    unfolding literal.vars_def literal.subst_def
    by auto
next
  case (Neg a)
  then show ?thesis 
    using assms that ground_subst_exstension_atom[of a \<gamma>]
    unfolding literal.vars_def literal.subst_def
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

  then have "var \<notin> term.vars term"
    by (metis (mono_tags, lifting) filter_mset_empty_conv set_mset_vars_term_ms size_eq_0_iff_empty)

  then have "term \<cdot>t \<gamma>(var := update) = term \<cdot>t \<gamma>"
    using term.subst_reduntant_upd 
    by fast

  with 0 show ?case
    by argo
next
  case (Suc n)

  then have "var \<in> term.vars term"
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
      by (metis (no_types, lifting) image_mset_add_mset subst_clause_add_mset to_ground_clause_def true_cls_add_mset)

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

lemma renaming_vars_term:  "Var ` term.vars (term \<cdot>t \<rho>) = \<rho> ` (term.vars term)" 
proof(induction "term")
  case Var
  with renaming show ?case
    unfolding term_subst_is_renaming_iff
    by (metis Term.term.simps(17) eval_term.simps(1) image_empty image_insert is_VarE)
next
  case (Fun f terms)

  have 
    "\<And>term x. \<lbrakk>term \<in> set terms; x \<in> term.vars (term \<cdot>t \<rho>)\<rbrakk> 
       \<Longrightarrow> Var x \<in> \<rho> ` \<Union> (term.vars ` set terms)"
    using Fun
    by (smt (verit, del_insts) UN_iff image_UN image_eqI)

  moreover have 
    "\<And>term x. \<lbrakk>term \<in> set terms; x \<in> term.vars term\<rbrakk>
       \<Longrightarrow> \<rho> x \<in> Var ` (\<Union>x' \<in> set terms. term.vars (x' \<cdot>t \<rho>))"
    using Fun
    by (smt (verit, del_insts) UN_iff image_UN image_eqI)

  ultimately show ?case
    by auto
qed

lemma renaming_vars_atom: "Var ` atom.vars (atom \<cdot>a \<rho>) = \<rho> ` atom.vars atom"
  unfolding atom.vars_def atom.subst_def 
  by(cases atom)(auto simp: image_Un renaming_vars_term)

lemma renaming_vars_literal: "Var ` literal.vars (literal \<cdot>l \<rho>) = \<rho> ` literal.vars literal"
  unfolding literal.vars_def literal.subst_def
  by(cases literal)(auto simp: renaming_vars_atom)

lemma renaming_vars_clause: "Var ` clause.vars (clause \<cdot> \<rho>) = \<rho> ` clause.vars clause"
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

lemma vars_term_subst: "term.vars (t \<cdot>t \<sigma>) \<subseteq> term.vars t \<union> range_vars \<sigma>"
  by (meson Diff_subset order_refl subset_trans sup.mono vars_term_subst_apply_term_subset)

lemma vars_term_imgu [clause_intro]:
  assumes "term_subst.is_imgu \<mu> {{s, s'}}"
  shows "term.vars (t \<cdot>t \<mu>) \<subseteq> term.vars t \<union> term.vars s \<union> term.vars s'"
  using range_vars_subset_if_is_imgu[OF assms] vars_term_subst
  by fastforce

lemma vars_context_imgu [clause_intro]:
  assumes "term_subst.is_imgu \<mu> {{s, s'}}"
  shows "context.vars (c \<cdot>t\<^sub>c \<mu>) \<subseteq> context.vars c \<union> term.vars s \<union> term.vars s'"
  using  vars_term_imgu[OF assms]
  by (smt (verit, ccfv_threshold) Un_iff subset_iff subst_apply_term_ctxt_apply_distrib vars_term_ctxt_apply)

lemma vars_atom_imgu [clause_intro]:
  assumes "term_subst.is_imgu \<mu> {{s, s'}}"
  shows "atom.vars (a \<cdot>a \<mu>) \<subseteq> atom.vars a \<union> term.vars s \<union> term.vars s'"
  using vars_term_imgu[OF assms]
  unfolding atom.vars_def atom.subst_def 
  by(cases a) auto

lemma vars_literal_imgu [clause_intro]:
  assumes "term_subst.is_imgu \<mu> {{s, s'}}"
  shows "literal.vars (l \<cdot>l \<mu>) \<subseteq> literal.vars l \<union> term.vars s \<union> term.vars s'"
  using vars_atom_imgu[OF assms]
  unfolding literal.vars_def literal.subst_def set_literal_atm_of
  by (metis (no_types, lifting) UN_insert ccSUP_empty literal.map_sel sup_bot.right_neutral)

lemma vars_clause_imgu [clause_intro]:
  assumes "term_subst.is_imgu \<mu> {{s, s'}}"
  shows "clause.vars (c \<cdot> \<mu>) \<subseteq> clause.vars c \<union> term.vars s \<union> term.vars s'"
  using vars_literal_imgu[OF assms]
  unfolding clause.vars_def clause.subst_def
  by blast

end
