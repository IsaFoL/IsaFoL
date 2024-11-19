theory Nonground_Clause
  imports 
    Ground_Clause
    Nonground_Term
    Nonground_Context (* TODO: Remove *)
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

(* TODO: Try to remove  *)
named_theorems clause_simp
named_theorems clause_intro

declare 
  ball_set_uprod [clause_simp] and
  subst_apply_term_ctxt_apply_distrib [clause_simp] and
  vars_term_ctxt_apply [clause_simp] and
  literal.sel [clause_simp] and
  term_context_ground_iff_term_is_ground [clause_simp] and
  ground_ctxt_iff_context_is_ground [clause_simp] and
  term_with_context_is_ground [clause_simp] and
  context_from_ground_hole [clause_simp] and
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


subsection \<open>Nonground Atoms\<close>

global_interpretation atom: lifting_from_term where 
  sub_subst = "(\<cdot>t)" and sub_vars = term.vars and map = map_uprod and to_set = set_uprod and 
  sub_to_ground = term.to_ground and sub_from_ground = term.from_ground and 
  to_ground_map = map_uprod and from_ground_map = map_uprod and ground_map = map_uprod and 
  to_set_ground = set_uprod
  by unfold_locales

notation atom.subst (infixl "\<cdot>a" 67)

subsection \<open>Nonground Literals\<close>

global_interpretation literal: lifting_from_term where 
  sub_subst = atom.subst and sub_vars = atom.vars and map = map_literal and 
  to_set = set_literal and sub_to_ground = atom.to_ground and 
  sub_from_ground = atom.from_ground and to_ground_map = map_literal and 
  from_ground_map = map_literal and ground_map = map_literal and to_set_ground = set_literal
  by unfold_locales

notation literal.subst (infixl "\<cdot>l" 66)

subsection \<open>Nonground Literals - Alternative\<close>

(* TODO: Names  *)
lemma alternative_literal [simp]:
  fixes l
  shows 
  "functional_substitution_lifting.subst (\<cdot>t) map_uprod_literal l \<sigma> = l \<cdot>l \<sigma>"
  "functional_substitution_lifting.vars term.vars uprod_literal_to_set l = literal.vars l"
  "grounding_lifting.from_ground term.from_ground map_uprod_literal l\<^sub>G = literal.from_ground l\<^sub>G"
  "grounding_lifting.to_ground term.to_ground map_uprod_literal l = literal.to_ground l"
proof -
  interpret lifting_from_term term.vars "(\<cdot>t)" map_uprod_literal uprod_literal_to_set term.to_ground 
    term.from_ground map_uprod_literal map_uprod_literal map_uprod_literal uprod_literal_to_set
    by unfold_locales

  fix l :: "('f, 'v) atom literal" and \<sigma>

  show "subst l \<sigma> = l \<cdot>l \<sigma>"
    unfolding subst_def literal.subst_def atom.subst_def
    by simp

  show "vars l = literal.vars l"
    unfolding atom.vars_def vars_def literal.vars_def
    by(cases l) simp_all

  fix l\<^sub>G:: "'f ground_atom literal"
  show "from_ground l\<^sub>G = literal.from_ground l\<^sub>G"
    unfolding from_ground_def literal.from_ground_def atom.from_ground_def..

  fix l :: "('f, 'v) atom literal"
  show "to_ground l = literal.to_ground l"
    unfolding to_ground_def literal.to_ground_def atom.to_ground_def..
qed

lemma literal'_subst_eq_literal_subst: "map_uprod_literal (\<lambda>sub. sub \<cdot>t \<sigma>) l = l \<cdot>l \<sigma>"
   unfolding subst_def literal.subst_def 
   by (simp add: atom.subst_def)

lemma literal'_vars_eq_literal_vars: "\<Union> (term.vars ` uprod_literal_to_set l) = literal.vars l"
  unfolding literal.vars_def atom.vars_def
  by(cases l) simp_all

lemma literal'_from_ground_eq_literal_from_ground: 
  "map_uprod_literal term.from_ground l\<^sub>G = literal.from_ground l\<^sub>G"
  unfolding literal.from_ground_def atom.from_ground_def ..

lemma literal'_to_ground_eq_literal_to_ground: 
  "map_uprod_literal term.to_ground l = literal.to_ground l"
  unfolding literal.to_ground_def atom.to_ground_def ..

global_interpretation literal': lifting_from_term where 
  sub_subst = "(\<cdot>t)" and sub_vars = term.vars and map = map_uprod_literal and 
  to_set = uprod_literal_to_set and sub_to_ground = term.to_ground and
  sub_from_ground = term.from_ground and to_ground_map = map_uprod_literal and 
  from_ground_map = map_uprod_literal and ground_map = map_uprod_literal and 
  to_set_ground = uprod_literal_to_set
rewrites 
  "\<And>l \<sigma>. literal'.subst l \<sigma> = literal.subst l \<sigma>" and
  "\<And>l. literal'.vars l = literal.vars l" and
  "\<And>l\<^sub>G. literal'.from_ground l\<^sub>G = literal.from_ground l\<^sub>G" and
  "\<And>l. literal'.to_ground l = literal.to_ground l"
  by unfold_locales simp_all

(* TODO: Delete? *)
lemma mset_mset_lit_subst [clause_simp]: "{# t \<cdot>t \<sigma>. t \<in># mset_lit l #} = mset_lit (l \<cdot>l \<sigma>)"
  unfolding literal.subst_def atom.subst_def mset_lit_image_mset
  by blast

subsection \<open>Nonground Clauses\<close>

global_interpretation clause: lifting_from_term where 
  sub_subst = literal.subst and sub_vars = literal.vars and map = image_mset and 
  to_set = set_mset and sub_to_ground = literal.to_ground and 
  sub_from_ground = literal.from_ground and to_ground_map = image_mset and 
  from_ground_map = image_mset and ground_map = image_mset and to_set_ground = set_mset
  by unfold_locales

(* TODO: Name *)
locale grounded_natural_monoid_functor = natural_monoid_grounding_lifting where 
  comp_subst = "(\<odot>)" and id_subst = Var  +
  natural_monoid_functor_functional_substitution_lifting where 
  comp_subst = "(\<odot>)" and id_subst = Var

global_interpretation clause: grounded_natural_monoid_functor where 
  to_set = set_mset and sub_to_ground = literal.to_ground and 
  sub_from_ground = literal.from_ground and sub_subst = literal.subst and 
  sub_vars = literal.vars and map = image_mset and to_ground_map = image_mset and 
  from_ground_map = image_mset and ground_map = image_mset and to_set_ground = set_mset and 
  plus = "(+)" and wrap = "\<lambda>l. {#l#}" and plus_ground = "(+)" and wrap_ground = "\<lambda>l. {#l#}" and
  add = add_mset and add_ground = add_mset
  by unfold_locales (auto simp: clause.to_ground_def clause.from_ground_def)

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
  clause.is_ground_add [clause_simp]
  clause.add_subst [clause_simp]
  clause.from_ground_add [clause_simp]
  clause.plus_subst [clause_simp]
  clause.vars_add [clause_simp]
  clause.vars_plus [clause_simp]

declare 
  clause.subst_in_to_set_subst [clause_intro]
  literal'.subst_in_to_set_subst [clause_intro]

(* TODO: Names *)
lemma vars_atom [clause_simp]: "atom.vars (Upair t\<^sub>1 t\<^sub>2) = term.vars t\<^sub>1 \<union> term.vars t\<^sub>2"
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

lemmas clause_submset_vars_clause_subset [clause_intro] = 
  clause.to_set_subset_vars_subset[OF set_mset_mono]

lemma subst_clause_remove1_mset [clause_simp]: 
  assumes "l \<in># C" 
  shows "remove1_mset l C \<cdot> \<sigma> = remove1_mset (l \<cdot>l \<sigma>) (C \<cdot> \<sigma>)"
  unfolding clause.subst_def image_mset_remove1_mset_if
  using assms
  by simp

lemmas sub_ground_clause = clause.to_set_subset_is_ground[OF set_mset_mono]

lemma clause_from_ground_empty_mset [clause_simp]: "clause.from_ground {#} = {#}"
  by (simp add: clause.from_ground_def)

lemma clause_to_ground_empty_mset [clause_simp]: "clause.to_ground {#} = {#}"
  by (simp add: clause.to_ground_def)

lemma remove1_mset_literal_from_ground: 
  "remove1_mset (literal.from_ground l\<^sub>G) (clause.from_ground C\<^sub>G)
   = clause.from_ground (remove1_mset l\<^sub>G C\<^sub>G)"
  unfolding clause.from_ground_def image_mset_remove1_mset[OF literal.inj_from_ground]..

lemma mset_literal_from_ground: 
  "mset_lit (literal.from_ground l) = image_mset term.from_ground (mset_lit l)"
  by (metis atom.from_ground_def literal.from_ground_def literal.map_cong0 mset_lit_image_mset)

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
  by(cases a) force

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

end
