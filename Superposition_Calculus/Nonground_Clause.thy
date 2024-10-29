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

global_interpretation atom: natural_functor where map = map_uprod and to_set = set_uprod
  by
    unfold_locales 
    (auto 
      simp: uprod.map_comp uprod.map_id uprod.set_map exists_atom_for_term 
      intro: uprod.map_cong)

global_interpretation atom: natural_functor_conversion where 
  map = map_uprod and to_set = set_uprod and map_to = map_uprod and map_from = map_uprod and 
  map' = map_uprod and to_set' = set_uprod
  by unfold_locales (auto simp: uprod.set_map uprod.map_comp uprod.map_id)

global_interpretation atom: lifting_from_term where 
  sub_subst = "(\<cdot>t)" and  sub_vars = term.vars and map = map_uprod and to_set = set_uprod and 
  sub_to_ground = term.to_ground and sub_from_ground = term.from_ground and 
  to_ground_map = map_uprod and from_ground_map = map_uprod and ground_map = map_uprod and 
  to_set_ground = set_uprod
  by unfold_locales (auto simp: term.is_grounding_iff_vars_grounded)

notation atom.subst (infixl "\<cdot>a" 67)

subsection \<open>Nonground Literals\<close>

global_interpretation literal: natural_functor where map = map_literal and to_set = set_literal
  by
    unfold_locales 
    (auto 
      simp: literal.map_comp literal.map_id literal.set_map exists_literal_for_atom 
      intro: literal.map_cong)

global_interpretation literal: natural_functor_conversion where 
  map = map_literal and to_set = set_literal and map_to = map_literal and map_from = map_literal and 
  map' = map_literal and to_set' = set_literal
  by unfold_locales 
    (auto simp: literal.set_map Clausal_Logic.literal.map_comp literal.map_id)

global_interpretation literal: lifting_from_term where 
  sub_subst = atom.subst and sub_vars = atom.vars and map = map_literal and 
  to_set = set_literal and sub_to_ground = atom.to_ground and 
  sub_from_ground = atom.from_ground and to_ground_map = map_literal and 
  from_ground_map = map_literal and ground_map = map_literal and to_set_ground = set_literal
  by
    unfold_locales 
    (auto simp: atom.is_grounding_iff_vars_grounded finite_set_literal)

notation literal.subst (infixl "\<cdot>l" 66)

subsection \<open>Nonground Literals - Alternative\<close>

abbreviation literal_to_term_set where "literal_to_term_set l \<equiv> set_mset (mset_lit l)"

abbreviation map_literal_term where "map_literal_term f \<equiv>  map_literal (map_uprod f)"

global_interpretation literal': natural_functor where 
  map = map_literal_term and to_set = literal_to_term_set
  by
    unfold_locales 
    (auto 
      simp: exists_literal_for_term mset_lit_image_mset map_literal_comp uprod.map_id0 
      uprod.map_comp literal.map_ident_strong
      intro: map_literal_map_uprod_cong)

global_interpretation literal': natural_functor_conversion where 
  map = map_literal_term and to_set = literal_to_term_set and map_to = map_literal_term and 
  map_from = map_literal_term and map' = map_literal_term and to_set' = literal_to_term_set
  by 
    unfold_locales 
    (auto simp: mset_lit_image_mset map_literal_comp uprod.map_id0 uprod.map_comp 
      literal.map_ident_strong)

global_interpretation literal': lifting_from_term where 
  sub_subst = "(\<cdot>t)" and sub_vars = term.vars and map = map_literal_term and 
  to_set = literal_to_term_set and sub_to_ground = term.to_ground and
  sub_from_ground = term.from_ground and to_ground_map = map_literal_term and 
  from_ground_map = map_literal_term and ground_map = map_literal_term and 
  to_set_ground = literal_to_term_set
rewrites 
  "\<And>l \<sigma>. literal'.subst l \<sigma> = literal.subst l \<sigma>" and
  "\<And>l. literal'.vars l = literal.vars l"
proof-
  (* TODO: Is there a way to do this without having to write this stuff again and again?! *)
  interpret lifting_from_term term.vars "(\<cdot>t)" map_literal_term literal_to_term_set term.to_ground 
    term.from_ground map_literal_term map_literal_term map_literal_term literal_to_term_set
    by unfold_locales
      (auto simp: term.is_grounding_iff_vars_grounded)

  fix l :: "('f, 'v) atom literal" and \<sigma>

  show "subst l \<sigma> = l \<cdot>l \<sigma>"
    unfolding subst_def literal.subst_def 
    by (simp add: atom.subst_def)

  show "vars l = literal.vars l"
    unfolding atom.vars_def vars_def literal.vars_def
    by(cases l) simp_all

  show "lifting_from_term term.vars (\<cdot>t) map_literal_term literal_to_term_set term.to_ground 
    term.from_ground map_literal_term map_literal_term map_literal_term literal_to_term_set"
    by unfold_locales
qed
    
lemma mset_mset_lit_subst [clause_simp]: "{# t \<cdot>t \<sigma>. t \<in># mset_lit l #} = mset_lit (l \<cdot>l \<sigma>)"
  unfolding literal'.subst_def mset_lit_image_mset ..

subsection \<open>Nonground Clauses\<close>

global_interpretation clause: natural_functor where map = image_mset and to_set = set_mset
  by unfold_locales (auto simp: exists_clause_for_literal)

global_interpretation clause: natural_functor_conversion where 
  map = image_mset and to_set = set_mset and map_to = image_mset and map_from = image_mset and 
  map' = image_mset and to_set' = set_mset
  by unfold_locales simp_all 

global_interpretation clause: lifting_from_term where 
  sub_subst = literal.subst and sub_vars = literal.vars and map = image_mset and 
  to_set = set_mset and sub_to_ground = literal.to_ground and 
  sub_from_ground = literal.from_ground and to_ground_map = image_mset and 
  from_ground_map = image_mset and ground_map = image_mset and to_set_ground = set_mset
  by unfold_locales (auto simp: literal.is_grounding_iff_vars_grounded)

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

lemma clause_from_ground_add_mset [clause_simp]: 
  "clause.from_ground (add_mset l\<^sub>G C\<^sub>G) = add_mset (literal.from_ground l\<^sub>G) (clause.from_ground C\<^sub>G)"
  by (simp add: clause.from_ground_def)

lemma remove1_mset_literal_from_ground: 
  "remove1_mset (literal.from_ground l\<^sub>G) (clause.from_ground C\<^sub>G)
   = clause.from_ground (remove1_mset l\<^sub>G C\<^sub>G)"
  unfolding clause.from_ground_def image_mset_remove1_mset[OF literal.inj_from_ground]..

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

end
