theory Nonground_Selection_Function
  imports 
    Nonground_Clause
    Selection_Function
begin

type_synonym 'f ground_select = "'f ground_atom clause \<Rightarrow> 'f ground_atom clause"
type_synonym ('f, 'v) select = "('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause"

context nonground_clause
begin

definition is_select_grounding :: "('f, 'v) select \<Rightarrow> 'f ground_select \<Rightarrow> bool" where 
  "is_select_grounding select select\<^sub>G \<equiv> \<forall>C\<^sub>G. \<exists>C \<gamma>. 
    clause.is_ground (C \<cdot> \<gamma>) \<and> 
    C\<^sub>G = clause.to_ground (C \<cdot> \<gamma>) \<and>
    select\<^sub>G C\<^sub>G = clause.to_ground ((select C) \<cdot> \<gamma>)"

end

locale nonground_selection_function = 
  nonground_clause +
  selection_function select
  for select :: "('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause"
begin

abbreviation is_grounding :: "'f ground_select \<Rightarrow> bool" where
  "is_grounding select\<^sub>G \<equiv> is_select_grounding select select\<^sub>G"

definition select\<^sub>G\<^sub>s where
  "select\<^sub>G\<^sub>s = { select\<^sub>G. is_grounding select\<^sub>G }"

definition select\<^sub>G_simple where
  "select\<^sub>G_simple C = clause.to_ground (select (clause.from_ground C))"

lemma select\<^sub>G_simple: "is_grounding select\<^sub>G_simple"
  unfolding is_select_grounding_def select\<^sub>G_simple_def
  by (metis clause.from_ground_inverse clause.ground_is_ground clause.subst_id_subst)

lemma select_is_ground: 
  assumes "clause.is_ground C" 
  shows "clause.is_ground (select C)"
  using select_subset sub_ground_clause assms
  by metis

lemma is_ground_in_selection: 
  assumes "l \<in># select (clause.from_ground C)"  
  shows "literal.is_ground l"
  using assms clause.sub_in_ground_is_ground select_subset
  by blast

lemma ground_literal_in_selection: 
  assumes "clause.is_ground C" "l\<^sub>G \<in># clause.to_ground C"
  shows "literal.from_ground l\<^sub>G \<in># C"
  using assms 
  by (metis clause.to_ground_inverse clause.ground_sub_in_ground)

lemma select_ground_subst:
  assumes "clause.is_ground (C \<cdot> \<gamma>)"  
  shows "clause.is_ground (select C \<cdot> \<gamma>)" 
  using assms
  by (metis image_mset_subseteq_mono select_subset sub_ground_clause clause.subst_def)

lemma select_neg_subst: 
  assumes "l \<in># select C \<cdot> \<gamma>"  
  shows "is_neg l"
  using assms subst_neg_stable select_negative_literals
  unfolding clause.subst_def
  by blast

end

end
