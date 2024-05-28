theory First_Order_Select
  imports 
    Selection_Function
    First_Order_Clause
    First_Order_Type_System
    HOL_Extra
begin

type_synonym ('f, 'v, 'ty) typed_clause = "('f, 'v) atom clause \<times> ('v, 'ty) var_types"

type_synonym 'f ground_select = "'f ground_atom clause \<Rightarrow> 'f ground_atom clause"
type_synonym ('f, 'v) select = "('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause"

definition is_select_grounding :: "('f, 'v) select \<Rightarrow> 'f ground_select \<Rightarrow> bool" where 
  "\<And>select select\<^sub>G.
        is_select_grounding select select\<^sub>G = (\<forall>clause\<^sub>G. \<exists>clause \<gamma>.
        is_ground_clause (clause \<cdot> \<gamma>)  \<and> 
        clause\<^sub>G = to_ground_clause (clause \<cdot> \<gamma>) \<and> 
        select\<^sub>G clause\<^sub>G = to_ground_clause ((select clause) \<cdot> \<gamma>))"

(* TODO: Is  welltyped\<^sub>c \<F> (snd clause) (fst clause) needed? *)
definition clause_groundings :: "('f, 'ty) fun_types \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> 'f ground_atom clause set"  where
  "clause_groundings \<F> clause = { to_ground_clause (fst clause \<cdot> \<gamma>) | \<gamma>. 
    term_subst.is_ground_subst \<gamma> \<and> 
    welltyped\<^sub>c \<F> (snd clause) (fst clause) \<and> 
    welltyped\<^sub>\<sigma> \<F> (snd clause) \<gamma>
  }"

(* TODO: Factor out sth like select_subst_stable for a single premise and use that format 
  everywhere

 *)
abbreviation select_subst_stability_on where
  "\<And>select select\<^sub>G. select_subst_stability_on \<F> select select\<^sub>G premises \<equiv>
    \<forall>premise\<^sub>G \<in> \<Union> (clause_groundings \<F> ` premises). \<exists>(premise, \<V>) \<in> premises. \<exists>\<gamma>. 
      premise \<cdot> \<gamma> = to_clause premise\<^sub>G \<and> 
      select\<^sub>G (to_ground_clause (premise \<cdot> \<gamma>)) = to_ground_clause ((select premise) \<cdot> \<gamma>) \<and>
      welltyped\<^sub>c \<F> \<V> premise \<and> welltyped\<^sub>\<sigma> \<F> \<V> \<gamma> \<and> term_subst.is_ground_subst \<gamma>"

lemma obtain_subst_stable_on_select_grounding:
  fixes select :: "('f, 'v) select"
  obtains select\<^sub>G where 
    "select_subst_stability_on \<F> select select\<^sub>G premises"
    "is_select_grounding select select\<^sub>G"
proof-
  let ?premise_groundings = "\<Union>(clause_groundings \<F> ` premises)"

  have select\<^sub>G_exists_for_premises: 
    "\<forall>premise\<^sub>G \<in> ?premise_groundings. \<exists>select\<^sub>G \<gamma>. \<exists>(premise, \<V>) \<in> premises.
          premise \<cdot> \<gamma> = to_clause premise\<^sub>G 
        \<and> select\<^sub>G premise\<^sub>G = to_ground_clause ((select premise) \<cdot> \<gamma>) \<and>
        welltyped\<^sub>c \<F> \<V> premise \<and> welltyped\<^sub>\<sigma> \<F> \<V> \<gamma> \<and> term_subst.is_ground_subst \<gamma>"
    unfolding clause_groundings_def
    using is_ground_subst_is_ground_clause by fastforce

  obtain select\<^sub>G_on_premise_groundings where 
    select\<^sub>G_on_premise_groundings: "\<forall>premise\<^sub>G \<in>?premise_groundings. \<exists>(premise, \<V>) \<in> premises. \<exists>\<gamma>.
        premise \<cdot> \<gamma> = to_clause premise\<^sub>G 
      \<and> select\<^sub>G_on_premise_groundings (to_ground_clause (premise \<cdot> \<gamma>)) = 
          to_ground_clause ((select premise) \<cdot> \<gamma>) 
      \<and> welltyped\<^sub>c \<F> \<V> premise \<and> welltyped\<^sub>\<sigma> \<F> \<V> \<gamma> \<and> term_subst.is_ground_subst \<gamma>"
    using Ball_Ex_comm(1)[OF select\<^sub>G_exists_for_premises]
    apply auto
    by (smt (verit, best) prod.case_eq_if to_clause_inverse)

  define select\<^sub>G where
    "\<And>clause\<^sub>G. select\<^sub>G clause\<^sub>G = (
        if clause\<^sub>G  \<in> ?premise_groundings 
        then select\<^sub>G_on_premise_groundings clause\<^sub>G 
        else to_ground_clause (select (to_clause clause\<^sub>G))
    )"

  have grounding: "is_select_grounding select select\<^sub>G"
    unfolding is_select_grounding_def select\<^sub>G_def
    using select\<^sub>G_on_premise_groundings
    apply auto
     apply force
    by (metis ground_clause_is_ground subst_clause_Var_ident to_clause_inverse)

  show ?thesis
    using that[OF _ grounding] select\<^sub>G_on_premise_groundings
    unfolding select\<^sub>G_def 
    by fastforce
qed

locale first_order_select = select select
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
  assumes "is_ground_clause (clause \<cdot> \<gamma>)"  
  shows "is_ground_clause (select clause \<cdot> \<gamma>)" 
  using assms
  by (metis image_mset_subseteq_mono select_subset sub_ground_clause subst_clause_def)
  
lemma select_subst2: 
  assumes "literal \<in># select clause \<cdot> \<gamma>"  
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

abbreviation subst_stability_on where
  "subst_stability_on \<F> premises \<equiv> select_subst_stability_on \<F> select select\<^sub>G premises"
  
lemma select\<^sub>G_subset: "select\<^sub>G clause \<subseteq># clause"
  using select\<^sub>G 
  unfolding is_select_grounding_def
  by (metis select_subset to_ground_clause_def image_mset_subseteq_mono subst_clause_def)

lemma select\<^sub>G_negative:
  assumes "literal\<^sub>G \<in># select\<^sub>G clause\<^sub>G"
  shows "is_neg literal\<^sub>G"
proof -
  obtain clause \<gamma> where 
    is_ground: "is_ground_clause (clause \<cdot> \<gamma>)" and
    select\<^sub>G: "select\<^sub>G clause\<^sub>G = to_ground_clause (select clause \<cdot> \<gamma>)"
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

sublocale ground: select select\<^sub>G
  by unfold_locales (simp_all add: select\<^sub>G_subset select\<^sub>G_negative)

end

end
