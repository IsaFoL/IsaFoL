theory Nonground_Clause
  imports 
    Ground_Clause
    Nonground_Term
    Nonground_Context
    Functional_Substitution_Lifting
    Entailment_Lifting
    Clausal_Calculus_Extra
    Multiset_Extra
    "HOL-Eisbach.Eisbach"
    HOL_Extra
    Fold_Extra 
begin

section \<open>Nonground Clauses and Substitutions\<close>

type_synonym 'f ground_atom = "'f gatom"
type_synonym ('f, 'v) atom = "('f, 'v) term uprod"

named_theorems clause_simp
named_theorems clause_intro

declare 
  ball_set_uprod [clause_simp] and
  subst_apply_term_ctxt_apply_distrib [clause_simp] and
  vars_term_ctxt_apply [clause_simp] and
  literal.sel [clause_simp] and
  term_context_ground_iff_term_is_ground [clause_simp] and
  ground_ctxt_iff_context_is_ground [clause_simp] and
  infinite_terms [clause_intro]

lemma literal_cases: "\<lbrakk>\<P> \<in> {Pos, Neg}; \<P> = Pos \<Longrightarrow> P; \<P> = Neg \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by blast

(* TODO: cases + names *)
method clause_simp uses (* cases*) simp intro =
  (*(-, (rule literal_cases[OF cases]))?,*)
  auto simp only: simp clause_simp intro: intro clause_intro

method clause_auto uses simp intro = 
  (clause_simp simp: simp intro: intro)?,  
  (auto simp: simp intro intro)?, 
  (auto simp: simp clause_simp intro: intro clause_intro)?

locale clause_lifting =
  based_functional_substitution_lifting where 
  base_subst = "(\<cdot>t)" and base_vars = term.vars and id_subst = Var and comp_subst = "(\<odot>)" + 
  all_subst_ident_iff_ground_lifting where id_subst = Var and comp_subst = "(\<odot>)" +
  grounding_lifting where id_subst = Var and comp_subst = "(\<odot>)" +
  renaming_variables_lifting where id_subst = Var and comp_subst = "(\<odot>)" +
  variables_in_base_imgu_lifting where id_subst = Var and comp_subst = "(\<odot>)" and base_subst = "(\<cdot>t)" and base_vars = term.vars 

subsection \<open>Nonground Atoms\<close>

global_interpretation atom: clause_lifting where 
  sub_subst = "(\<cdot>t)" and  sub_vars = term.vars and map = map_uprod and to_set = set_uprod and 
  sub_to_ground = term.to_ground and sub_from_ground = term.from_ground and 
  to_ground_map = map_uprod and from_ground_map = map_uprod and ground_map = map_uprod and 
  to_set_ground = set_uprod
  by 
    unfold_locales 
    (auto 
      simp: uprod.map_comp uprod.map_id uprod.set_map exists_atom_for_term 
      term.is_grounding_iff_vars_grounded 
      intro: uprod.map_cong)

notation atom.subst (infixl "\<cdot>a" 67)

subsection \<open>Nonground Literals\<close>

global_interpretation literal: clause_lifting where 
  sub_subst = atom.subst and sub_vars = atom.vars and map = map_literal and 
  to_set = set_literal and sub_to_ground = atom.to_ground and 
  sub_from_ground = atom.from_ground and to_ground_map = map_literal and 
  from_ground_map = map_literal and ground_map = map_literal and to_set_ground = set_literal
  by
    unfold_locales 
    (auto 
      simp: literal.map_comp literal.map_id literal.set_map exists_literal_for_atom 
      atom.is_grounding_iff_vars_grounded finite_set_literal
      intro: literal.map_cong)

notation literal.subst (infixl "\<cdot>l" 66)

subsection \<open>Nonground Literals - Alternative\<close>

global_interpretation literal': clause_lifting where 
  sub_subst = "(\<cdot>t)" and sub_vars = term.vars and map = "\<lambda>f. map_literal (map_uprod f)" and 
  to_set = "\<lambda>l. set_mset (mset_lit l)" and sub_to_ground = term.to_ground and 
  sub_from_ground = term.from_ground and to_ground_map = "\<lambda>f. map_literal (map_uprod f) " and 
  from_ground_map = "\<lambda>f. map_literal (map_uprod f)" and 
  ground_map = "\<lambda>f. map_literal (map_uprod f) " and to_set_ground = "\<lambda>l. set_mset (mset_lit l)" 
rewrites 
  "\<And>l \<sigma>. literal'.subst l \<sigma> = literal.subst l \<sigma>" and
  "\<And>l. literal'.vars l = literal.vars l"
proof-
  (* TODO: Is there a way to do this without having to write this stuff again and again?! *)
  interpret clause_lifting term.vars "(\<cdot>t)" "\<lambda>f. map_literal (map_uprod f)" 
    "\<lambda>l. set_mset (mset_lit l)" term.to_ground term.from_ground "\<lambda>f. map_literal (map_uprod f)" 
    "\<lambda>f. map_literal (map_uprod f)" "\<lambda>f. map_literal (map_uprod f)" "\<lambda>l. set_mset (mset_lit l)"
    by unfold_locales
      (auto 
      simp: exists_literal_for_term mset_lit_image_mset map_literal_comp literal.map_id0 
      uprod.map_id0 term.is_grounding_iff_vars_grounded uprod.map_comp literal.map_ident_strong 
      uprod.map_ident
      cong: map_literal_map_uprod_cong)

  show "\<And>l \<sigma>. subst l \<sigma> = l \<cdot>l \<sigma>"
    unfolding subst_def literal.subst_def 
    by (simp add: atom.subst_def)

  show "\<And>l :: ('f, 'v) atom literal. vars l = literal.vars l"
  proof(unfold vars_def literal.vars_def)
    fix l :: "('f, 'v) atom literal"
    show "\<Union> (term.vars ` set_mset (mset_lit l)) = \<Union> (atom.vars ` set_literal l)"
      unfolding atom.vars_def
      by(cases l) simp_all
  qed

  show 
    "clause_lifting term.vars (\<cdot>t) (\<lambda>f. map_literal (map_uprod f)) (\<lambda>l. set_mset (mset_lit l)) 
      term.to_ground term.from_ground (\<lambda>f. map_literal (map_uprod f)) 
      (\<lambda>f. map_literal (map_uprod f)) (\<lambda>f. map_literal (map_uprod f)) (\<lambda>l. set_mset (mset_lit l))"
    by unfold_locales
qed
    
lemma mset_mset_lit_subst [clause_simp]: "{# t \<cdot>t \<sigma>. t \<in># mset_lit l #} = mset_lit (l \<cdot>l \<sigma>)"
  unfolding literal'.subst_def mset_lit_image_mset ..

subsection \<open>Nonground Clauses\<close>

global_interpretation clause: clause_lifting where 
  sub_subst = literal.subst and sub_vars = literal.vars and map = image_mset and 
  to_set = set_mset and sub_to_ground = literal.to_ground and 
  sub_from_ground = literal.from_ground and to_ground_map = image_mset and 
  from_ground_map = image_mset and ground_map = image_mset and to_set_ground = set_mset
  by 
    unfold_locales 
    (auto simp: exists_clause_for_literal literal.is_grounding_iff_vars_grounded)

notation clause.subst (infixl "\<cdot>" 67)

lemmas empty_clause_is_ground[clause_intro] = clause.empty_is_ground[OF set_mset_empty]

lemmas clause_subst_empty [clause_simp] = 
  clause.subst_ident_if_ground[OF empty_clause_is_ground]
  clause.subst_empty[OF set_mset_empty]

declare
  literal.to_set_is_ground [clause_simp]
  atom.to_set_is_ground [clause_simp]
  clause.to_set_is_ground [clause_simp]
  set_mset_set_uprod [clause_simp]
  mset_lit_set_literal [clause_simp]

declare 
  clause.subst_in_to_set_subst [clause_intro]
  literal'.subst_in_to_set_subst [clause_intro]

lemma vars_atom [clause_simp]: 
  "atom.vars (Upair t\<^sub>1 t\<^sub>2) = term.vars t\<^sub>1 \<union> term.vars t\<^sub>2"
  by (simp_all add: atom.vars_def)

lemma vars_literal [clause_simp]: 
  "literal.vars (Pos a) = atom.vars a"
  "literal.vars (Neg a) = atom.vars a"
  "literal.vars ((if b then Pos else Neg) a) = atom.vars a"
  by (simp_all add: literal.vars_def)

lemma subst_atom [clause_simp]: 
  "Upair t\<^sub>1 t\<^sub>2 \<cdot>a \<sigma> = Upair (t\<^sub>1 \<cdot>t \<sigma>) (t\<^sub>2 \<cdot>t \<sigma>)"
  unfolding atom.subst_def
  by simp_all

lemma subst_literal [clause_simp]: 
  "Pos a \<cdot>l \<sigma> = Pos (a \<cdot>a \<sigma>)"
  "Neg a \<cdot>l \<sigma> = Neg (a \<cdot>a \<sigma>)"
  "atm_of (l \<cdot>l \<sigma>) = atm_of l \<cdot>a \<sigma>"
  unfolding literal.subst_def
  using literal.map_sel
  by auto

(* TODO: Can these be generalized? *)
lemma vars_clause_add_mset [clause_simp]: 
  "clause.vars (add_mset l C) = literal.vars l \<union> clause.vars C"
  by (simp add: clause.vars_def)

lemma vars_clause_plus [clause_simp]: 
  "clause.vars (C\<^sub>1 + C\<^sub>2) = clause.vars C\<^sub>1 \<union> clause.vars C\<^sub>2"
  by (simp add: clause.vars_def)

lemma clause_submset_vars_clause_subset [clause_intro]: 
  "C\<^sub>1 \<subseteq># C\<^sub>2 \<Longrightarrow> clause.vars C\<^sub>1 \<subseteq> clause.vars C\<^sub>2"
  by (metis subset_mset.add_diff_inverse sup_ge1 vars_clause_plus)

lemma subst_clause_add_mset [clause_simp]: 
  "add_mset l C \<cdot> \<sigma> = add_mset (l \<cdot>l \<sigma>) (C \<cdot> \<sigma>)"
  unfolding clause.subst_def
  by simp

lemma subst_clause_plus [clause_simp]: "(C\<^sub>1 + C\<^sub>2) \<cdot> \<sigma> = C\<^sub>1 \<cdot> \<sigma> + C\<^sub>2 \<cdot> \<sigma>"
  unfolding clause.subst_def
  by simp

lemma clause_to_ground_plus [simp]: 
  "clause.to_ground (C\<^sub>1 + C\<^sub>2) = clause.to_ground C\<^sub>1 + clause.to_ground C\<^sub>2"
  by (simp add: clause.to_ground_def)

lemma clause_from_ground_plus [simp]: 
  "clause.from_ground (C\<^sub>G\<^sub>1 + C\<^sub>G\<^sub>2) = clause.from_ground C\<^sub>G\<^sub>1 + clause.from_ground C\<^sub>G\<^sub>2"
  by (simp add: clause.from_ground_def)

lemma subst_clause_remove1_mset [clause_simp]: 
  assumes "l \<in># C" 
  shows "remove1_mset l C \<cdot> \<sigma> = remove1_mset (l \<cdot>l \<sigma>) (C \<cdot> \<sigma>)"
  unfolding clause.subst_def image_mset_remove1_mset_if
  using assms
  by simp

lemma sub_ground_clause [clause_intro]: 
  assumes "C' \<subseteq># C" "clause.is_ground C"
  shows "clause.is_ground C'"
  using assms
  unfolding clause.vars_def
  by blast

lemma clause_from_ground_empty_mset [clause_simp]: "clause.from_ground {#} = {#}"
  by (simp add: clause.from_ground_def)

lemma clause_to_ground_empty_mset [clause_simp]: "clause.to_ground {#} = {#}"
  by (simp add: clause.to_ground_def)

abbreviation ctxt_apply_gterm (\<open>_\<langle>_\<rangle>\<^sub>T\<close> [1000, 0] 1000) where
  "C\<langle>s\<rangle>\<^sub>T \<equiv> GFun\<langle>C;s\<rangle>"

lemma ground_term_with_context1:
  assumes "context.is_ground c" "term.is_ground t"
  shows "(context.to_ground c)\<langle>term.to_ground t\<rangle>\<^sub>T = term.to_ground c\<langle>t\<rangle>"
  using assms
  apply(induction c)
   apply auto
  apply (simp add: context.to_ground_def)
  by (simp add: context.to_ground_def)

lemma ground_term_with_context2:
  assumes "context.is_ground c"  
  shows "term.from_ground (context.to_ground c)\<langle>t\<^sub>G\<rangle>\<^sub>T = c\<langle>term.from_ground t\<^sub>G\<rangle>"
  using assms
  by (metis ground_term_with_context1 sup_bot.right_neutral term.from_ground_inverse term.to_ground_inverse vars_term_ctxt_apply vars_term_of_gterm)

lemma ground_term_with_context3: 
  "(context.from_ground c\<^sub>G)\<langle>term.from_ground t\<^sub>G\<rangle> = term.from_ground c\<^sub>G\<langle>t\<^sub>G\<rangle>\<^sub>T"
  using ground_term_with_context2[OF context.ground_is_ground, symmetric]
  unfolding context.from_ground_inverse.

lemmas ground_term_with_context =
  ground_term_with_context1
  ground_term_with_context2
  ground_term_with_context3

lemma context_is_ground_context_compose1:
  assumes "context.is_ground (c \<circ>\<^sub>c c')"
  shows "context.is_ground c" "context.is_ground c'"
  using assms
  by(induction c) auto

lemma context_is_ground_context_compose2:
  assumes "context.is_ground c" "context.is_ground c'" 
  shows "context.is_ground (c \<circ>\<^sub>c c')"
  using assms
  by (meson ground_ctxt_comp ground_ctxt_iff_context_is_ground)

lemmas context_is_ground_context_compose = 
  context_is_ground_context_compose1 
  context_is_ground_context_compose2

lemma ground_context_subst:
  assumes 
    "context.is_ground c\<^sub>G" 
    "c\<^sub>G = (c \<cdot>t\<^sub>c \<sigma>) \<circ>\<^sub>c c'"
  shows 
    "c\<^sub>G = c \<circ>\<^sub>c c' \<cdot>t\<^sub>c \<sigma>"
  using assms 
proof(induction c)
  case Hole
  then show ?case
    by simp
next
  case More
  then show ?case
    using context_is_ground_context_compose1(2)
    by (metis subst_compose_ctxt_compose_distrib context.subst_ident_if_ground)
qed

lemma clause_from_ground_add_mset [clause_simp]: 
  "clause.from_ground (add_mset l\<^sub>G C\<^sub>G) = add_mset (literal.from_ground l\<^sub>G) (clause.from_ground C\<^sub>G)"
  by (simp add: clause.from_ground_def)

lemma remove1_mset_literal_from_ground: 
  "remove1_mset (literal.from_ground l\<^sub>G) (clause.from_ground C\<^sub>G)
   = clause.from_ground (remove1_mset l\<^sub>G C\<^sub>G)"
  unfolding clause.from_ground_def image_mset_remove1_mset[OF literal.inj_from_ground]..

lemma term_with_context_is_ground [clause_simp]: 
  "term.is_ground c\<langle>t\<rangle> \<longleftrightarrow> context.is_ground c \<and> term.is_ground t"
  by simp

lemma mset_literal_from_ground: 
  "mset_lit (literal.from_ground l) = image_mset term.from_ground (mset_lit l)"
  by (metis atom.from_ground_def literal.from_ground_def literal.map_cong0 mset_lit_image_mset)

lemma clause_is_ground_add_mset [clause_simp]: 
  "clause.is_ground (add_mset l C) \<longleftrightarrow> literal.is_ground l \<and> clause.is_ground C"
  by clause_auto

lemma clause_to_ground_add_mset:
  assumes "clause.from_ground C = add_mset l C'" 
  shows "C = add_mset (literal.to_ground l) (clause.to_ground C')"
  using assms
  by (metis clause.from_ground_inverse clause.to_ground_def image_mset_add_mset)

(* --------------------------- *)

lemma subst_polarity_stable: 
  shows 
    subst_neg_stable: "is_neg (l \<cdot>l \<sigma>) \<longleftrightarrow> is_neg l" and
    subst_pos_stable: "is_pos (l \<cdot>l \<sigma>) \<longleftrightarrow> is_pos l"
  by (simp_all add: literal.subst_def)

lemma atom_from_ground_term_from_ground [clause_simp]:
  "atom.from_ground (Upair t\<^sub>G\<^sub>1 t\<^sub>G\<^sub>2) = Upair (term.from_ground t\<^sub>G\<^sub>1) (term.from_ground t\<^sub>G\<^sub>2)"
  by (simp add: atom.from_ground_def)

lemma literal_from_ground_atom_from_ground [clause_simp]:
  "literal.from_ground (Neg a\<^sub>G) = Neg (atom.from_ground a\<^sub>G)"
  "literal.from_ground (Pos a\<^sub>G) = Pos (atom.from_ground a\<^sub>G)"  
  by (simp_all add: literal.from_ground_def)

lemma context_from_ground_hole [clause_simp]: 
  "context.from_ground c\<^sub>G = \<box> \<longleftrightarrow> c\<^sub>G = \<box>"
  by(cases c\<^sub>G) (simp_all add: context.from_ground_def)

lemma literal_from_ground_polarity_stable: 
  shows 
    literal_from_ground_neg_stable: "is_neg l\<^sub>G \<longleftrightarrow> is_neg (literal.from_ground l\<^sub>G)" and
    literal_from_ground_stable: "is_pos l\<^sub>G \<longleftrightarrow> is_pos (literal.from_ground l\<^sub>G)"
  by (simp_all add: literal.from_ground_def)

lemma term_to_ground_atom_to_ground:
  assumes "term.is_ground t\<^sub>1" and "term.is_ground t\<^sub>2"
  shows "Upair (term.to_ground t\<^sub>1) (term.to_ground t\<^sub>2) = atom.to_ground (Upair t\<^sub>1 t\<^sub>2)"
  using assms
  by (simp add: atom.to_ground_def)

lemma atom_is_ground_term_is_ground [clause_simp]: 
  "atom.is_ground (Upair t\<^sub>1 t\<^sub>2) \<longleftrightarrow> term.is_ground t\<^sub>1 \<and> term.is_ground t\<^sub>2"
  by clause_simp

lemma literal_to_ground_atom_to_ground [clause_simp]:
  "literal.to_ground (Pos a) = Pos (atom.to_ground a)" 
  "literal.to_ground (Neg a) = Neg (atom.to_ground a)" 
  by (simp_all add: literal.to_ground_def)

lemma literal_is_ground_atom_is_ground [intro]: 
  "literal.is_ground l \<longleftrightarrow> atom.is_ground (atm_of l)"
  by (simp add: literal.vars_def set_literal_atm_of)

lemma obtain_from_atom_subst [clause_intro]: 
  assumes "Upair t\<^sub>1' t\<^sub>2' = a \<cdot>a \<sigma>"
  obtains t\<^sub>1 t\<^sub>2 
  where "a = Upair t\<^sub>1 t\<^sub>2" "t\<^sub>1' = t\<^sub>1 \<cdot>t \<sigma>" "t\<^sub>2' = t\<^sub>2 \<cdot>t \<sigma>"
  using assms
  unfolding atom.subst_def 
  by(cases a) auto

lemma obtain_from_pos_literal_subst [clause_intro]: 
  assumes "l \<cdot>l \<sigma> = t\<^sub>1' \<approx> t\<^sub>2'"
  obtains t\<^sub>1 t\<^sub>2 
  where "l = t\<^sub>1 \<approx> t\<^sub>2" "t\<^sub>1' = t\<^sub>1 \<cdot>t \<sigma>" "t\<^sub>2' = t\<^sub>2 \<cdot>t \<sigma>"
  using assms obtain_from_atom_subst subst_pos_stable
  by (metis is_pos_def literal.sel(1) subst_literal(1))

lemma obtain_from_neg_literal_subst: 
  assumes "l \<cdot>l \<sigma> = t\<^sub>1' !\<approx> t\<^sub>2'"
  obtains t\<^sub>1 t\<^sub>2 
  where "l = t\<^sub>1 !\<approx> t\<^sub>2" "t\<^sub>1 \<cdot>t \<sigma> = t\<^sub>1'" "t\<^sub>2 \<cdot>t \<sigma> = t\<^sub>2'"
  using assms obtain_from_atom_subst subst_neg_stable
  by (metis literal.collapse(2) literal.disc(2) literal.sel(2) subst_literal(3))

lemmas obtain_from_literal_subst = obtain_from_pos_literal_subst obtain_from_neg_literal_subst

subsection \<open>Entailment\<close>

locale clause_entailment = term_entailment where I = I for I :: "('f gterm \<times> 'f gterm) interp"
begin

sublocale atom: symmetric_entailment 
  where comp_subst = "(\<odot>)" and id_subst = Var 
    and base_subst = "(\<cdot>t)" and base_vars = term.vars and subst = "(\<cdot>a)" and vars = atom.vars
    and base_to_ground = term.to_ground and base_from_ground = term.from_ground and I = I 
    and entails_def = "\<lambda>a. atom.to_ground a \<in> upair ` I"
proof unfold_locales  
  fix a :: "('f, 'v) atom" and  \<gamma> var update P
  assume
    "term.is_ground update"
    "term.is_ground (\<gamma> var)" 
    "(term.to_ground (\<gamma> var), term.to_ground update) \<in> I"
    "atom.is_ground (a \<cdot>a \<gamma>)"
    "(atom.to_ground (a \<cdot>a \<gamma>(var := update)) \<in> upair ` I)"

  then show "(atom.to_ground (a \<cdot>a \<gamma>) \<in> upair ` I)"
    unfolding atom.to_ground_def atom.subst_def atom.vars_def
    by(cases a) (auto simp add: sym term.simultaneous_congruence)

qed (simp_all add: local.sym atom.is_grounding_iff_vars_grounded)

sublocale literal: entailment_lifting_conj
  where comp_subst = "(\<odot>)" and id_subst = Var 
    and base_subst = "(\<cdot>t)" and base_vars = term.vars and sub_subst = "(\<cdot>a)" and sub_vars = atom.vars
    and base_to_ground = term.to_ground and base_from_ground = term.from_ground and I = I 
    and sub_entails = atom.entails and map = "map_literal" and to_set = "set_literal" 
    and is_negated = is_neg and entails_def = "\<lambda>l. upair ` I \<TTurnstile>l literal.to_ground l"
proof unfold_locales 
  fix l :: "('f, 'v) atom literal" 

  show "(upair ` I \<TTurnstile>l literal.to_ground l) = 
    (if is_neg l then Not else (\<lambda>x. x))
      (Finite_Set.fold (\<and>) True ((\<lambda>a. atom.to_ground a \<in> upair ` I) ` set_literal l))" 
    unfolding literal.vars_def literal.to_ground_def
    by(cases l)(auto)

qed (auto simp: sym subst_polarity_stable)

sublocale clause: entailment_lifting_disj
  where comp_subst = "(\<odot>)" and id_subst = Var 
    and base_subst = "(\<cdot>t)" and base_vars = term.vars 
    and base_to_ground = term.to_ground and base_from_ground = term.from_ground and I = I
    and sub_subst = "(\<cdot>l)" and sub_vars = literal.vars and sub_entails = literal.entails 
    and map = image_mset and to_set = set_mset and is_negated = "\<lambda>_. False" 
    and entails_def = "\<lambda>C. upair ` I \<TTurnstile> clause.to_ground C"
proof unfold_locales 
  fix C :: "('f, 'v) atom clause" 

  show "(upair ` I \<TTurnstile> clause.to_ground C) = 
    (if False then Not else (\<lambda>x. x)) (Finite_Set.fold (\<or>) False (literal.entails ` set_mset C))"
    unfolding clause.to_ground_def
    by(induction C) auto

qed (auto simp: sym clause.subst_empty)

end

lemma vars_term_subst: "term.vars (t \<cdot>t \<sigma>) \<subseteq> term.vars t \<union> range_vars \<sigma>"
  by (meson Diff_subset order_refl subset_trans sup.mono vars_term_subst_apply_term_subset)

lemma vars_term_imgu [clause_intro]:
  assumes "term_subst.is_imgu \<mu> {{s, s'}}"
  shows "term.vars (t \<cdot>t \<mu>) \<subseteq> term.vars t \<union> term.vars s \<union> term.vars s'"
  using range_vars_subset_if_is_imgu[OF assms] vars_term_subst
  by fastforce

lemma vars_term_imgu' [clause_intro]:
  assumes "term_subst.is_imgu \<mu> XX" "\<forall>X\<in>XX. finite X" "finite XX"
  shows "term.vars (t \<cdot>t \<mu>) \<subseteq> term.vars t \<union>  \<Union>(term.vars ` \<Union> XX)"
  using range_vars_subset_if_is_imgu[OF assms] vars_term_subst
  by (metis sup.absorb_iff1 sup.coboundedI2 sup_left_commute)

(* TODO: *)
lemma vars_context_imgu [clause_intro]:
  assumes "term_subst.is_imgu \<mu> {{s, s'}}"
  shows "context.vars (c \<cdot>t\<^sub>c \<mu>) \<subseteq> context.vars c \<union> term.vars s \<union> term.vars s'"
  using vars_term_imgu[OF assms, of "c\<langle>s\<rangle>"]
  by simp

lemma vars_atom_imgu [clause_intro]:
  assumes "term_subst.is_imgu \<mu> {{s, s'}}"
  shows "atom.vars (a \<cdot>a \<mu>) \<subseteq> atom.vars a \<union> term.vars s \<union> term.vars s'"
  using atom.variables_in_base_imgu[OF assms]
  by fast

lemma vars_literal_imgu [clause_intro]:
  assumes "term_subst.is_imgu \<mu> {{s, s'}}"
  shows "literal.vars (l \<cdot>l \<mu>) \<subseteq> literal.vars l \<union> term.vars s \<union> term.vars s'"
  using literal.variables_in_base_imgu[OF assms]
  by blast

lemma vars_clause_imgu [clause_intro]:
  assumes "term_subst.is_imgu \<mu> {{s, s'}}"
  shows "clause.vars (c \<cdot> \<mu>) \<subseteq> clause.vars c \<union> term.vars s \<union> term.vars s'"
  using clause.variables_in_base_imgu[OF assms]
  by blast

end
