theory Grounded_Superposition
  imports 
    Grounded_Selection_Function
    Superposition
    Ground_Superposition
begin

locale grounded_superposition_calculus =
  superposition_calculus where select = select and \<F> = \<F> +
  grounded_selection_function where select = select and \<F> = \<F>
  for
    select :: "('f, 'v :: infinite) select" and
    \<F> :: "('f, 'ty) fun_types"
begin

sublocale ground: ground_superposition_calculus where
  less\<^sub>t = "(\<prec>\<^sub>t\<^sub>G)" and select = select\<^sub>G
rewrites 
  "multiset_extension.multiset_extension (\<prec>\<^sub>t\<^sub>G) mset_lit = (\<prec>\<^sub>l\<^sub>G)" and 
  "multiset_extension.multiset_extension (\<prec>\<^sub>l\<^sub>G) (\<lambda>x. x) = (\<prec>\<^sub>c\<^sub>G)" and
  "\<And>l C. ground.is_maximal l C \<longleftrightarrow> is_maximal (literal.from_ground l) (clause.from_ground C)" and
  "\<And>l C. ground.is_strictly_maximal l C \<longleftrightarrow>
    is_strictly_maximal (literal.from_ground l) (clause.from_ground C)"
  by unfold_locales (auto simp: ground_critical_pair_theorem)

abbreviation is_inference_grounding_one_premise where 
  "is_inference_grounding_one_premise D C \<iota>\<^sub>G \<gamma> \<equiv>
     case (D, C) of ((D, \<V>'), (C, \<V>)) \<Rightarrow>
      clause.is_ground (D \<cdot> \<gamma>)
        \<and> clause.is_ground (C \<cdot> \<gamma>)
        \<and> \<iota>\<^sub>G = Infer [clause.to_ground (D \<cdot> \<gamma>)] (clause.to_ground (C \<cdot> \<gamma>))
        \<and> clause.is_welltyped \<V> D 
        \<and> is_welltyped_on (clause.vars C) \<V> \<gamma>
        \<and> clause.is_welltyped \<V> C
        \<and> \<V> = \<V>'
        \<and> infinite_variables_per_type \<V>"

abbreviation is_inference_grounding_two_premises where 
  "is_inference_grounding_two_premises D E C \<iota>\<^sub>G \<gamma> \<rho>\<^sub>1 \<rho>\<^sub>2 \<equiv> 
    case (D, E, C) of ((D, \<V>\<^sub>2), (E, \<V>\<^sub>1), (C, \<V>\<^sub>3)) \<Rightarrow>
          term_subst.is_renaming \<rho>\<^sub>1
        \<and> term_subst.is_renaming \<rho>\<^sub>2
        \<and> clause.vars (E \<cdot> \<rho>\<^sub>1) \<inter> clause.vars (D \<cdot> \<rho>\<^sub>2) = {}
        \<and> clause.is_ground (D \<cdot> \<rho>\<^sub>2 \<cdot> \<gamma>)
        \<and> clause.is_ground (E \<cdot> \<rho>\<^sub>1  \<cdot> \<gamma>)
        \<and> clause.is_ground (C \<cdot> \<gamma>)
        \<and> \<iota>\<^sub>G =
            Infer
              [clause.to_ground (D \<cdot> \<rho>\<^sub>2 \<cdot> \<gamma>), clause.to_ground (E \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>)] (clause.to_ground (C \<cdot> \<gamma>))
        \<and> clause.is_welltyped \<V>\<^sub>1 E
        \<and> clause.is_welltyped \<V>\<^sub>2 D
        \<and> is_welltyped_on (clause.vars C) \<V>\<^sub>3 \<gamma>
        \<and> clause.is_welltyped \<V>\<^sub>3 C
        \<and> infinite_variables_per_type \<V>\<^sub>1
        \<and> infinite_variables_per_type \<V>\<^sub>2 
        \<and> infinite_variables_per_type \<V>\<^sub>3"

abbreviation is_inference_grounding where
  "is_inference_grounding \<iota> \<iota>\<^sub>G \<gamma> \<rho>\<^sub>1 \<rho>\<^sub>2 \<equiv> 
  (case \<iota> of
      Infer [D] C \<Rightarrow> is_inference_grounding_one_premise D C \<iota>\<^sub>G \<gamma>
    | Infer [D, E] C \<Rightarrow> is_inference_grounding_two_premises D E C \<iota>\<^sub>G \<gamma> \<rho>\<^sub>1 \<rho>\<^sub>2
    | _ \<Rightarrow> False) 
  \<and> \<iota>\<^sub>G \<in> ground.G_Inf"

definition inference_groundings where 
  "inference_groundings \<iota> = { \<iota>\<^sub>G | \<iota>\<^sub>G \<gamma> \<rho>\<^sub>1 \<rho>\<^sub>2. is_inference_grounding \<iota> \<iota>\<^sub>G \<gamma> \<rho>\<^sub>1 \<rho>\<^sub>2 }"

lemma is_inference_grounding_inference_groundings: 
  "is_inference_grounding \<iota> \<iota>\<^sub>G \<gamma> \<rho>\<^sub>1 \<rho>\<^sub>2 \<Longrightarrow> \<iota>\<^sub>G \<in> inference_groundings \<iota>"
  unfolding inference_groundings_def
  by blast

lemma inference\<^sub>G_concl_in_clause_grounding: 
  assumes "\<iota>\<^sub>G \<in> inference_groundings \<iota>"
  shows "concl_of \<iota>\<^sub>G \<in> clause_groundings (concl_of \<iota>)"
proof-
  obtain "premises" C \<V> where
    \<iota>: "\<iota> = Infer premises (C, \<V>)" 
    using Calculus.inference.exhaust
    by (metis prod.collapse)

  show ?thesis
    using assms
    unfolding \<iota> inference_groundings_def clause_groundings_def
    by (cases "premises" rule: list_4_cases) auto
qed  

lemma inference\<^sub>G_red_in_clause_grounding_of_concl: 
  assumes "\<iota>\<^sub>G \<in> inference_groundings \<iota>"
  shows "\<iota>\<^sub>G \<in> ground.Red_I (clause_groundings (concl_of \<iota>))"
proof-
  from assms have "\<iota>\<^sub>G \<in> ground.G_Inf"
    unfolding inference_groundings_def
    by blast

  moreover have "concl_of \<iota>\<^sub>G \<in> clause_groundings (concl_of \<iota>)"
    using assms inference\<^sub>G_concl_in_clause_grounding
    by auto

  ultimately show "\<iota>\<^sub>G \<in> ground.Red_I (clause_groundings (concl_of \<iota>))"
    using ground.Red_I_of_Inf_to_N
    by blast
qed

sublocale lifting: 
  tiebreaker_lifting
    "\<bottom>\<^sub>F"
    inferences 
    ground.G_Bot
    ground.G_entails
    ground.G_Inf 
    ground.GRed_I
    ground.GRed_F 
    clause_groundings
    "Some \<circ> inference_groundings"
    typed_tiebreakers
proof(unfold_locales; (intro impI)?)

  show "\<bottom>\<^sub>F \<noteq> {}"
    using exists_infinite_variables_per_type[OF variables]
    by blast
next
  fix bottom
  assume "bottom \<in> \<bottom>\<^sub>F"

  then show "clause_groundings bottom \<noteq> {}"
    unfolding clause_groundings_def
    by auto
next
  fix bottom
  assume "bottom \<in> \<bottom>\<^sub>F"

  then show "clause_groundings bottom \<subseteq> ground.G_Bot"
    unfolding clause_groundings_def
    by auto
next
  fix C :: "('f, 'v, 'ty) typed_clause"

  assume "clause_groundings C \<inter> ground.G_Bot \<noteq> {}"

  moreover then have "fst C = {#}"
    unfolding clause_groundings_def
    by simp

  then have "C = ({#}, snd C)"
    by (metis split_pairs)

  ultimately show "C \<in> \<bottom>\<^sub>F"
    unfolding clause_groundings_def
    by blast
next
  fix \<iota> :: "('f, 'v, 'ty) typed_clause inference"

  show "the ((Some \<circ> inference_groundings) \<iota>) \<subseteq> ground.GRed_I (clause_groundings (concl_of \<iota>))"
    using inference\<^sub>G_red_in_clause_grounding_of_concl
    by auto
next
  fix C\<^sub>G
  show "po_on (typed_tiebreakers C\<^sub>G) UNIV"
    unfolding po_on_def
    by simp
next
  fix C\<^sub>G
  show "Restricted_Predicates.wfp_on (typed_tiebreakers C\<^sub>G) UNIV"
    using typed_tiebreakers.wfp
    by simp
qed


end

context superposition_calculus
begin

sublocale
  lifting_intersection
    inferences      
    "{{#}}"
    select\<^sub>G\<^sub>s
    "ground_superposition_calculus.G_Inf (\<prec>\<^sub>t\<^sub>G)"
    "\<lambda>_. ground_superposition_calculus.G_entails"
    "ground_superposition_calculus.GRed_I (\<prec>\<^sub>t\<^sub>G)"
    "\<lambda>_. ground_superposition_calculus.GRed_F (\<prec>\<^sub>t\<^sub>G)"
    "\<bottom>\<^sub>F"
    "\<lambda>_. clause_groundings" 
    "\<lambda>select\<^sub>G. Some \<circ> (grounded_superposition_calculus.inference_groundings (\<prec>\<^sub>t) select\<^sub>G \<F>)"
    typed_tiebreakers
proof(unfold_locales; (intro ballI)?)
  show "select\<^sub>G\<^sub>s \<noteq> {}"
    using select\<^sub>G_simple
    unfolding select\<^sub>G\<^sub>s_def 
    by blast
next 
  fix select\<^sub>G
  assume "select\<^sub>G \<in> select\<^sub>G\<^sub>s"
 
  then interpret grounded_superposition_calculus
    where select\<^sub>G = select\<^sub>G
    by unfold_locales (simp add: select\<^sub>G\<^sub>s_def)

  show "consequence_relation ground.G_Bot ground.G_entails"
    using ground.consequence_relation_axioms.
next
   fix select\<^sub>G
   assume "select\<^sub>G \<in> select\<^sub>G\<^sub>s"
 
   then interpret grounded_superposition_calculus
    where select\<^sub>G = select\<^sub>G
    by unfold_locales (simp add: select\<^sub>G\<^sub>s_def)

  show "tiebreaker_lifting
          \<bottom>\<^sub>F
          inferences
          ground.G_Bot
          ground.G_entails
          ground.G_Inf
          ground.GRed_I
          ground.GRed_F
          clause_groundings
          (Some \<circ> inference_groundings)
          typed_tiebreakers"
    by unfold_locales
qed

end

end
