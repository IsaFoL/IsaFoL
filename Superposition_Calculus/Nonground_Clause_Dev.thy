theory Nonground_Clause_Dev
  imports
    First_Order_Clause.Nonground_Clause
begin

(* Work in progress: Clause without equations *)
(* TODO: Bring as much together with Nonground_Clause as possible  *)

locale nonground_clause' = nonground_term_with_context
begin

subsection \<open>Nonground Literals\<close>

sublocale literal: term_based_lifting where 
  sub_subst = "(\<cdot>t)" and sub_vars = term.vars and map = map_literal and 
  to_set = set_literal and sub_to_ground = term.to_ground and 
  sub_from_ground = term.from_ground and to_ground_map = map_literal and 
  from_ground_map = map_literal and ground_map = map_literal and to_set_ground = set_literal
  by unfold_locales

notation literal.subst (infixl "\<cdot>l" 66)

lemma vars_literal [simp]: 
  "literal.vars (Pos a) = term.vars a"
  "literal.vars (Neg a) = term.vars a"
  "literal.vars ((if b then Pos else Neg) a) = term.vars a"
  by (simp_all add: literal.vars_def)

lemma subst_literal [simp]: 
  "Pos a \<cdot>l \<sigma> = Pos (a \<cdot>t \<sigma>)"
  "Neg a \<cdot>l \<sigma> = Neg (a \<cdot>t \<sigma>)"
  "atm_of (l \<cdot>l \<sigma>) = atm_of l \<cdot>t \<sigma>"
  unfolding literal.subst_def
  using literal.map_sel
  by auto

lemma subst_literal_if [simp]:
  "(if b then Pos else Neg) a \<cdot>l \<rho> = (if b then Pos else Neg) (a \<cdot>t \<rho>)"
  by simp

lemma subst_polarity_stable: 
  shows 
    subst_neg_stable [simp]: "is_neg (l \<cdot>l \<sigma>) \<longleftrightarrow> is_neg l" and
    subst_pos_stable [simp]: "is_pos (l \<cdot>l \<sigma>) \<longleftrightarrow> is_pos l"
  by (simp_all add: literal.subst_def)

declare literal.discI [intro]

lemma literal_from_ground_atom_from_ground [simp]:
  "literal.from_ground (Neg a\<^sub>G) = Neg (term.from_ground a\<^sub>G)"
  "literal.from_ground (Pos a\<^sub>G) = Pos (term.from_ground a\<^sub>G)"  
  by (simp_all add: literal.from_ground_def)

lemma literal_from_ground_polarity_stable [simp]: 
  shows 
    neg_literal_from_ground_stable: "is_neg (literal.from_ground l\<^sub>G) \<longleftrightarrow> is_neg l\<^sub>G" and
    pos_literal_from_ground_stable: "is_pos (literal.from_ground l\<^sub>G) \<longleftrightarrow> is_pos l\<^sub>G"
  by (simp_all add: literal.from_ground_def)

lemma literal_to_ground_atom_to_ground [simp]:
  "literal.to_ground (Pos a) = Pos (term.to_ground a)" 
  "literal.to_ground (Neg a) = Neg (term.to_ground a)" 
  by (simp_all add: literal.to_ground_def)

lemma literal_is_ground_atom_is_ground [intro]: 
  "literal.is_ground l \<longleftrightarrow> term.is_ground (atm_of l)"
  by (simp add: literal.vars_def set_literal_atm_of)

lemma obtain_from_pos_literal_subst: 
  assumes "l \<cdot>l \<sigma> = Pos t'"
  obtains t 
  where "l = Pos t" "t' = t \<cdot>t \<sigma>" 
  using assms subst_pos_stable
  by (metis is_pos_def literal.sel(1) subst_literal(3))

lemma obtain_from_neg_literal_subst: 
  assumes "l \<cdot>l \<sigma> = Neg t'"
  obtains t
  where "l = Neg t" "t \<cdot>t \<sigma> = t'"
  using assms subst_neg_stable
  by (metis literal.collapse(2) literal.disc(2) literal.sel(2) subst_literal(3))

lemmas obtain_from_literal_subst = obtain_from_pos_literal_subst obtain_from_neg_literal_subst


subsection \<open>Nonground Clauses\<close>

sublocale clause: term_based_multiset_lifting where 
  sub_subst = literal.subst and sub_vars = literal.vars and sub_to_ground = literal.to_ground and 
  sub_from_ground = literal.from_ground
  by unfold_locales

notation clause.subst (infixl "\<cdot>" 67)

lemmas clause_submset_vars_clause_subset [intro] = 
  clause.to_set_subset_vars_subset[OF set_mset_mono]

lemmas sub_ground_clause = clause.to_set_subset_is_ground[OF set_mset_mono]

lemma subst_clause_remove1_mset [simp]: 
  assumes "l \<in># C" 
  shows "remove1_mset l C \<cdot> \<sigma> = remove1_mset (l \<cdot>l \<sigma>) (C \<cdot> \<sigma>)"
  unfolding clause.subst_def image_mset_remove1_mset_if
  using assms
  by simp

lemma clause_from_ground_remove1_mset [simp]: 
  "clause.from_ground (remove1_mset l\<^sub>G C\<^sub>G) =
    remove1_mset (literal.from_ground l\<^sub>G) (clause.from_ground C\<^sub>G)"
  unfolding clause.from_ground_def image_mset_remove1_mset[OF literal.inj_from_ground]..

lemmas clause_safe_unfolds =
  literal_to_ground_atom_to_ground   
  literal_from_ground_atom_from_ground
  literal_from_ground_polarity_stable
  subst_literal
  vars_literal

end

end
