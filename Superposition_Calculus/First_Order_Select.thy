theory First_Order_Select
  imports 
    Generic_Select 
    First_Order_Clause
begin

type_synonym 'f ground_select = "'f ground_atom clause \<Rightarrow> 'f ground_atom clause"
type_synonym ('f, 'v) select = "('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause"

definition is_select_grounding :: "('f, 'v) select \<Rightarrow> 'f ground_select \<Rightarrow> bool" where
  "is_select_grounding select select\<^sub>G = (\<forall>clause\<^sub>G. \<exists>clause \<theta>. 
        is_ground_clause (clause \<cdot> \<theta>)  \<and> 
        clause\<^sub>G = to_ground_clause (clause \<cdot> \<theta>) \<and> 
        select\<^sub>G clause\<^sub>G = to_ground_clause ((select clause) \<cdot> \<theta>))"

locale first_order_select = generic_select select
  for select :: "('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause"
begin

abbreviation is_grounding :: "'f ground_select \<Rightarrow> bool" where
  "is_grounding select\<^sub>G \<equiv> is_select_grounding select select\<^sub>G"

definition select\<^sub>G\<^sub>s where
  "select\<^sub>G\<^sub>s = { ground_select. is_grounding ground_select }"

definition select\<^sub>G_simple where
  "select\<^sub>G_simple clause = to_ground_clause (select (to_clause clause))"

lemma select\<^sub>G_simple: "is_grounding select\<^sub>G_simple"
  unfolding is_select_grounding_def select\<^sub>G_simple_def
  by (metis to_clause_inverse ground_clause_is_ground subst_clause_Var_ident)

lemma select_from_ground_clause1: 
  assumes "is_ground_clause clause" 
  shows "is_ground_clause (select clause)"
  using select_subset sub_ground_clause assms
  by metis

lemma select_from_ground_clause2: 
  assumes "literal \<in># select (to_clause clause)"  
  shows "is_ground_literal literal"
  using assms ground_literal_in_ground_clause(2) select_subset
  by blast

lemma select_from_ground_clause3: 
  assumes "is_ground_clause clause" "literal\<^sub>G \<in># to_ground_clause clause"
  shows "to_literal literal\<^sub>G \<in># clause"
  using assms 
  by (metis to_ground_clause_inverse ground_literal_in_ground_clause(3))

lemmas select_from_ground_clause =
  select_from_ground_clause1
  select_from_ground_clause2
  select_from_ground_clause3

lemma select_subst1:
  assumes "is_ground_clause (clause \<cdot> \<theta>)"  
  shows "is_ground_clause (select clause \<cdot> \<theta>)" 
  using assms
  by (metis image_mset_subseteq_mono select_subset sub_ground_clause subst_clause_def)
  
lemma select_subst2: 
  assumes "literal \<in># select clause \<cdot> \<theta>"  
  shows "is_neg literal"
  using assms subst_neg_stable select_negative_lits
  unfolding subst_clause_def
  by auto

lemmas select_subst = select_subst1 select_subst2

end

locale grounded_first_order_select = 
  first_order_select select for select +
  fixes select\<^sub>G 
  assumes select\<^sub>G: "is_select_grounding select select\<^sub>G"
begin
  
lemma select\<^sub>G_subset: "select\<^sub>G clause \<subseteq># clause"
  using select\<^sub>G 
  unfolding is_select_grounding_def
  by (metis select_subset to_ground_clause_def image_mset_subseteq_mono subst_clause_def)

lemma select\<^sub>G_negative:
  assumes "literal\<^sub>G \<in># select\<^sub>G clause\<^sub>G"
  shows "is_neg literal\<^sub>G"
proof -
  obtain clause \<theta> where 
    is_ground: "is_ground_clause (clause \<cdot> \<theta>)" and
    select\<^sub>G: "select\<^sub>G clause\<^sub>G = to_ground_clause (select clause \<cdot> \<theta>)"
    using select\<^sub>G
    unfolding is_select_grounding_def
    by blast

  show ?thesis
    using 
      select_from_ground_clause(3)[
          OF select_subst(1)[OF is_ground] assms[unfolded select\<^sub>G], 
          THEN select_subst(2)
      ]
    unfolding to_literal_def
    by simp
qed

sublocale ground: generic_select select\<^sub>G
  by unfold_locales (simp_all add: select\<^sub>G_subset select\<^sub>G_negative)

end

end
