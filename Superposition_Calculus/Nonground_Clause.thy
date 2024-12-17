theory Nonground_Clause
  imports 
    Ground_Clause
    Nonground_Term
    Nonground_Context
    Clausal_Calculus_Extra
    Multiset_Extra
begin

(* TODO: These are clauses with equality *)
section \<open>Nonground Clauses and Substitutions\<close>

type_synonym 'f ground_atom = "'f gatom"
type_synonym ('f, 'v) atom = "('f, 'v) term uprod"

(* TODO: *)
lemma literal_cases: "\<lbrakk>\<P> \<in> {Pos, Neg}; \<P> = Pos \<Longrightarrow> P; \<P> = Neg \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by blast

locale natural_magma_lifting =
  natural_magma_grounding_lifting +
  natural_magma_functor_functional_substitution_lifting

locale nonground_clause = nonground_term_with_context
begin

subsection \<open>Nonground Atoms\<close>

sublocale atom: term_based_lifting where 
  sub_subst = "(\<cdot>t)" and sub_vars = term.vars and map = map_uprod and to_set = set_uprod and 
  sub_to_ground = term.to_ground and sub_from_ground = term.from_ground and 
  to_ground_map = map_uprod and from_ground_map = map_uprod and ground_map = map_uprod and 
  to_set_ground = set_uprod
  by unfold_locales

notation atom.subst (infixl "\<cdot>a" 67)

subsection \<open>Nonground Literals\<close>

sublocale literal: term_based_lifting where 
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
  interpret term_based_lifting where
    sub_vars = term.vars and sub_subst = "(\<cdot>t)" and map = map_uprod_literal and 
    to_set = uprod_literal_to_set and sub_to_ground = term.to_ground and 
    sub_from_ground = term.from_ground and to_ground_map = map_uprod_literal and 
    from_ground_map = map_uprod_literal and ground_map = map_uprod_literal and 
    to_set_ground = uprod_literal_to_set
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

lemma literal'_subst_eq_literal_subst: "map_uprod_literal (\<lambda>t. t \<cdot>t \<sigma>) l = l \<cdot>l \<sigma>"
  unfolding atom.subst_def literal.subst_def
  by auto

lemma literal'_vars_eq_literal_vars: "\<Union> (term.vars ` uprod_literal_to_set l) = literal.vars l"
  unfolding literal.vars_def atom.vars_def
  by(cases l) simp_all

lemma literal'_from_ground_eq_literal_from_ground: 
  "map_uprod_literal term.from_ground l\<^sub>G = literal.from_ground l\<^sub>G"
  unfolding literal.from_ground_def atom.from_ground_def ..

lemma literal'_to_ground_eq_literal_to_ground: 
  "map_uprod_literal term.to_ground l = literal.to_ground l"
  unfolding literal.to_ground_def atom.to_ground_def ..

sublocale literal': term_based_lifting where 
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

subsection \<open>Nonground Clauses\<close>

sublocale clause: term_based_lifting where 
  sub_subst = literal.subst and sub_vars = literal.vars and map = image_mset and 
  to_set = set_mset and sub_to_ground = literal.to_ground and 
  sub_from_ground = literal.from_ground and to_ground_map = image_mset and 
  from_ground_map = image_mset and ground_map = image_mset and to_set_ground = set_mset
  by unfold_locales

sublocale clause: natural_magma_lifting where 
  id_subst = Var and comp_subst = "(\<odot>)" and to_set = set_mset and 
  sub_to_ground = literal.to_ground and sub_from_ground = literal.from_ground and
  sub_subst = literal.subst and sub_vars = literal.vars and map = image_mset and 
  to_ground_map = image_mset and from_ground_map = image_mset and ground_map = image_mset and 
  to_set_ground = set_mset and plus = "(+)" and wrap = "\<lambda>l. {#l#}" and plus_ground = "(+)" and 
  wrap_ground = "\<lambda>l. {#l#}" and add = add_mset and add_ground = add_mset
  by unfold_locales (auto simp: clause.to_ground_def clause.from_ground_def)

notation clause.subst (infixl "\<cdot>" 67)

lemmas empty_clause_is_ground [simp] = clause.empty_is_ground[OF set_mset_empty]

lemmas clause_subst_empty [simp] = 
  clause.subst_ident_if_ground[OF empty_clause_is_ground]
  clause.subst_empty[OF set_mset_empty]

lemma clause_to_ground_empty [simp]: "clause.to_ground C = {#} \<longleftrightarrow> C = {#}"
  by (simp add: clause.to_ground_def)

lemma clause_from_ground_empty [simp]: "clause.from_ground C = {#} \<longleftrightarrow> C = {#}"
  by (simp add: clause.from_ground_def)

lemma vars_atom [simp]: "atom.vars (Upair t\<^sub>1 t\<^sub>2) = term.vars t\<^sub>1 \<union> term.vars t\<^sub>2"
  by (simp_all add: atom.vars_def)

lemma vars_literal [simp]: 
  "literal.vars (Pos a) = atom.vars a"
  "literal.vars (Neg a) = atom.vars a"
  "literal.vars ((if b then Pos else Neg) a) = atom.vars a"
  by (simp_all add: literal.vars_def)

lemma subst_atom [simp]: 
  "Upair t\<^sub>1 t\<^sub>2 \<cdot>a \<sigma> = Upair (t\<^sub>1 \<cdot>t \<sigma>) (t\<^sub>2 \<cdot>t \<sigma>)"
  unfolding atom.subst_def
  by simp_all

lemma subst_literal [simp]: 
  "Pos a \<cdot>l \<sigma> = Pos (a \<cdot>a \<sigma>)"
  "Neg a \<cdot>l \<sigma> = Neg (a \<cdot>a \<sigma>)"
  "atm_of (l \<cdot>l \<sigma>) = atm_of l \<cdot>a \<sigma>"
  unfolding literal.subst_def
  using literal.map_sel
  by auto

lemma subst_literal_if [simp]:
  "(if b then Pos else Neg) a \<cdot>l \<rho> = (if b then Pos else Neg) (a \<cdot>a \<rho>)"
  by simp

lemmas clause_submset_vars_clause_subset [intro] = 
  clause.to_set_subset_vars_subset[OF set_mset_mono]

lemma subst_clause_remove1_mset [simp]: 
  assumes "l \<in># C" 
  shows "remove1_mset l C \<cdot> \<sigma> = remove1_mset (l \<cdot>l \<sigma>) (C \<cdot> \<sigma>)"
  unfolding clause.subst_def image_mset_remove1_mset_if
  using assms
  by simp

lemmas sub_ground_clause = clause.to_set_subset_is_ground[OF set_mset_mono]

lemma clause_from_ground_empty_mset [simp]: "clause.from_ground {#} = {#}"
  by (simp add: clause.from_ground_def)

lemma clause_to_ground_empty_mset [simp]: "clause.to_ground {#} = {#}"
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
    subst_neg_stable [simp]: "is_neg (l \<cdot>l \<sigma>) \<longleftrightarrow> is_neg l" and
    subst_pos_stable [simp]: "is_pos (l \<cdot>l \<sigma>) \<longleftrightarrow> is_pos l"
  by (simp_all add: literal.subst_def)

declare literal.discI [intro]

lemma atom_from_ground_term_from_ground [simp]:
  "atom.from_ground (Upair t\<^sub>G\<^sub>1 t\<^sub>G\<^sub>2) = Upair (term.from_ground t\<^sub>G\<^sub>1) (term.from_ground t\<^sub>G\<^sub>2)"
  by (simp add: atom.from_ground_def)

lemma literal_from_ground_atom_from_ground [simp]:
  "literal.from_ground (Neg a\<^sub>G) = Neg (atom.from_ground a\<^sub>G)"
  "literal.from_ground (Pos a\<^sub>G) = Pos (atom.from_ground a\<^sub>G)"  
  by (simp_all add: literal.from_ground_def)

lemma literal_from_ground_polarity_stable [simp]: 
  shows 
    literal_from_ground_neg_stable: "is_neg (literal.from_ground l\<^sub>G) \<longleftrightarrow> is_neg l\<^sub>G" and
    literal_from_ground_stable: "is_pos (literal.from_ground l\<^sub>G) \<longleftrightarrow> is_pos l\<^sub>G"
  by (simp_all add: literal.from_ground_def)

lemma atom_to_ground_term_to_ground [simp]: 
  "atom.to_ground (Upair t\<^sub>1 t\<^sub>2) = Upair (term.to_ground t\<^sub>1) (term.to_ground t\<^sub>2)"
  by (simp add: atom.to_ground_def)

lemma atom_is_ground_term_is_ground [simp]: 
  "atom.is_ground (Upair t\<^sub>1 t\<^sub>2) \<longleftrightarrow> term.is_ground t\<^sub>1 \<and> term.is_ground t\<^sub>2"
  by simp

lemma literal_to_ground_atom_to_ground [simp]:
  "literal.to_ground (Pos a) = Pos (atom.to_ground a)" 
  "literal.to_ground (Neg a) = Neg (atom.to_ground a)" 
  by (simp_all add: literal.to_ground_def)

lemma literal_is_ground_atom_is_ground [intro]: 
  "literal.is_ground l \<longleftrightarrow> atom.is_ground (atm_of l)"
  by (simp add: literal.vars_def set_literal_atm_of)

lemmas clause_safe_unfolds = 
  atom_to_ground_term_to_ground
  literal_to_ground_atom_to_ground 
  atom_from_ground_term_from_ground
  literal_from_ground_atom_from_ground
  literal_from_ground_polarity_stable
  subst_atom
  subst_literal
  vars_atom
  vars_literal

lemma obtain_from_atom_subst: 
  assumes "Upair t\<^sub>1' t\<^sub>2' = a \<cdot>a \<sigma>"
  obtains t\<^sub>1 t\<^sub>2 
  where "a = Upair t\<^sub>1 t\<^sub>2" "t\<^sub>1' = t\<^sub>1 \<cdot>t \<sigma>" "t\<^sub>2' = t\<^sub>2 \<cdot>t \<sigma>"
  using assms
  unfolding atom.subst_def 
  by(cases a) force

lemma obtain_from_pos_literal_subst: 
  assumes "l \<cdot>l \<sigma> = t\<^sub>1' \<approx> t\<^sub>2'"
  obtains t\<^sub>1 t\<^sub>2 
  where "l = t\<^sub>1 \<approx> t\<^sub>2" "t\<^sub>1' = t\<^sub>1 \<cdot>t \<sigma>" "t\<^sub>2' = t\<^sub>2 \<cdot>t \<sigma>"
  using assms obtain_from_atom_subst subst_pos_stable
  by (metis is_pos_def literal.sel(1) subst_literal(3))

lemma obtain_from_neg_literal_subst: 
  assumes "l \<cdot>l \<sigma> = t\<^sub>1' !\<approx> t\<^sub>2'"
  obtains t\<^sub>1 t\<^sub>2 
  where "l = t\<^sub>1 !\<approx> t\<^sub>2" "t\<^sub>1 \<cdot>t \<sigma> = t\<^sub>1'" "t\<^sub>2 \<cdot>t \<sigma> = t\<^sub>2'"
  using assms obtain_from_atom_subst subst_neg_stable
  by (metis literal.collapse(2) literal.disc(2) literal.sel(2) subst_literal(3))

lemmas obtain_from_literal_subst = obtain_from_pos_literal_subst obtain_from_neg_literal_subst

end

end
