theory Grounded_First_Order_Superposition
  imports 
    First_Order_Superposition
    Ground_Superposition_Completeness
begin

context ground_superposition_calculus
begin

abbreviation eq_resolution_inferences where
  "eq_resolution_inferences \<equiv>  {Infer [P] C | P C. ground_eq_resolution P C}"

abbreviation eq_factoring_inferences where
  "eq_factoring_inferences \<equiv>  {Infer [P] C | P C.  ground_eq_factoring P C}"

abbreviation superposition_inferences where
  "superposition_inferences \<equiv> {Infer [P2, P1] C | P1 P2 C. ground_superposition P2 P1 C}"

end

locale grounded_first_order_superposition_calculus =
  first_order_superposition_calculus select _ _ typeof_fun +
  grounded_first_order_select select
  for 
    select :: "('f, 'v) select" and
    typeof_fun :: "'f \<Rightarrow> 'ty list \<times> 'ty"
begin

sublocale ground: ground_superposition_calculus where
  less_trm = "(\<prec>\<^sub>t\<^sub>G)" and select = select\<^sub>G
  by unfold_locales (rule ground_critical_pair_theorem)

abbreviation is_inference_grounding where
  "is_inference_grounding \<iota> \<iota>\<^sub>G \<gamma> \<rho>\<^sub>1 \<rho>\<^sub>2 \<equiv>
    (case \<iota> of
        Infer [premise] conclusion \<Rightarrow>
          is_ground_clause (premise \<cdot> \<gamma>)
        \<and> is_ground_clause (conclusion \<cdot> \<gamma>)
        \<and> \<iota>\<^sub>G = Infer [to_ground_clause (premise \<cdot> \<gamma>)] (to_ground_clause (conclusion \<cdot> \<gamma>))
      | Infer [premise\<^sub>2, premise\<^sub>1] conclusion \<Rightarrow> 
          term_subst.is_renaming \<rho>\<^sub>1
        \<and> term_subst.is_renaming \<rho>\<^sub>2
        \<and> vars_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter> vars_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2) = {}
        \<and> is_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>)
        \<and> is_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<gamma>)
        \<and> is_ground_clause (conclusion \<cdot> \<gamma>)
        \<and> \<iota>\<^sub>G =
            Infer
              [to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<gamma>), to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>)]
              (to_ground_clause (conclusion \<cdot> \<gamma>))
      | _ \<Rightarrow> False
     )
  \<and> \<iota>\<^sub>G \<in> ground.G_Inf
  \<and> (\<forall>\<V>. welltyped\<^sub>\<sigma> typeof_fun \<V> \<gamma>)"

definition inference_groundings where 
  "inference_groundings \<iota> = { \<iota>\<^sub>G | \<iota>\<^sub>G \<gamma> \<rho>\<^sub>1 \<rho>\<^sub>2. is_inference_grounding \<iota> \<iota>\<^sub>G \<gamma> \<rho>\<^sub>1 \<rho>\<^sub>2 }"

lemma is_inference_grounding_inference_groundings: 
  "is_inference_grounding \<iota> \<iota>\<^sub>G \<gamma> \<rho>\<^sub>1 \<rho>\<^sub>2 \<Longrightarrow> \<iota>\<^sub>G \<in> inference_groundings \<iota>"
  unfolding inference_groundings_def
  by blast

lemma inference\<^sub>G_concl_in_clause_grounding: 
  assumes "\<iota>\<^sub>G \<in> inference_groundings \<iota>"
  shows "concl_of \<iota>\<^sub>G \<in> typed_clause_groundings typeof_fun (concl_of \<iota>)"
proof-
  obtain premises\<^sub>G conlcusion\<^sub>G where
    \<iota>\<^sub>G: "\<iota>\<^sub>G = Infer premises\<^sub>G conlcusion\<^sub>G"
    using Calculus.inference.exhaust by blast

  obtain "premises" conlcusion where
    \<iota>: "\<iota> = Infer premises conlcusion"
    using Calculus.inference.exhaust by blast

  obtain \<gamma> where 
    "is_ground_clause (conlcusion \<cdot> \<gamma>)"
    "conlcusion\<^sub>G = to_ground_clause (conlcusion \<cdot> \<gamma>)"
    "\<forall>\<V>. welltyped\<^sub>\<sigma> typeof_fun \<V> \<gamma>"
    using assms list_4_cases
    unfolding inference_groundings_def \<iota> \<iota>\<^sub>G Calculus.inference.case
    by(simp split: list.splits)(metis list_4_cases)

  then show ?thesis
    unfolding \<iota> \<iota>\<^sub>G typed_clause_groundings_def
    by auto
qed  

lemma inference\<^sub>G_red_in_clause_grounding_of_concl: 
  assumes "\<iota>\<^sub>G \<in> inference_groundings \<iota>"
  shows "\<iota>\<^sub>G \<in> ground.Red_I (typed_clause_groundings typeof_fun (concl_of \<iota>))"
proof-
  from assms have "\<iota>\<^sub>G \<in> ground.G_Inf"
    unfolding inference_groundings_def
    by blast

  moreover have "concl_of \<iota>\<^sub>G \<in> typed_clause_groundings typeof_fun  (concl_of \<iota>)"
    using assms inference\<^sub>G_concl_in_clause_grounding
    by auto

  ultimately show "\<iota>\<^sub>G \<in> ground.Red_I (typed_clause_groundings typeof_fun (concl_of \<iota>))"
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
          "typed_clause_groundings typeof_fun"
          "(Some \<circ> inference_groundings)"
          tiebreakers
proof unfold_locales
  show "\<bottom>\<^sub>F \<noteq> {}"
    by simp
next
  fix bottom
  assume "bottom \<in> \<bottom>\<^sub>F"

  then show "typed_clause_groundings typeof_fun bottom \<noteq> {}"
    unfolding typed_clause_groundings_def
    using welltyped\<^sub>\<sigma>_Var by auto
next
  fix bottom
  assume "bottom \<in> \<bottom>\<^sub>F"
  then show "typed_clause_groundings typeof_fun bottom \<subseteq> ground.G_Bot"
    unfolding typed_clause_groundings_def
     using welltyped\<^sub>\<sigma>_Var by auto
next
  fix clause
  show "typed_clause_groundings typeof_fun clause \<inter> ground.G_Bot \<noteq> {} \<longrightarrow> clause \<in> \<bottom>\<^sub>F"
    unfolding typed_clause_groundings_def to_ground_clause_def subst_clause_def
    by simp
next
  fix \<iota> :: "('f, 'v) atom clause inference"

  show "the ((Some \<circ> inference_groundings) \<iota>) \<subseteq> ground.GRed_I (typed_clause_groundings typeof_fun (concl_of \<iota>))"
    using inference\<^sub>G_red_in_clause_grounding_of_concl
    by auto
next
  show "\<And>clause\<^sub>G. po_on (tiebreakers clause\<^sub>G) UNIV"
    unfolding po_on_def
    using wellfounded_tiebreakers
    by simp
next
  show "\<And>clause\<^sub>G. wfp_on (tiebreakers clause\<^sub>G) UNIV"
    using wellfounded_tiebreakers
    by simp
qed

end

sublocale first_order_superposition_calculus \<subseteq>
  lifting_intersection
    inferences      
    "{{#}}"
    select\<^sub>G\<^sub>s
    "ground_superposition_calculus.G_Inf (\<prec>\<^sub>t\<^sub>G)"               
    "\<lambda>_. ground_superposition_calculus.G_entails" 
    "ground_superposition_calculus.GRed_I (\<prec>\<^sub>t\<^sub>G)" 
    "\<lambda>_. ground_superposition_calculus.GRed_F(\<prec>\<^sub>t\<^sub>G)" 
    "\<bottom>\<^sub>F"
    "\<lambda>_. typed_clause_groundings typeof_fun" 
    "\<lambda>select\<^sub>G. Some \<circ>
      (grounded_first_order_superposition_calculus.inference_groundings (\<prec>\<^sub>t) select\<^sub>G typeof_fun)"
    tiebreakers
proof(unfold_locales; (intro ballI)?)
  show "select\<^sub>G\<^sub>s \<noteq> {}"
    using select\<^sub>G_simple
    unfolding select\<^sub>G\<^sub>s_def 
    by blast
next 
  fix select\<^sub>G
  assume "select\<^sub>G \<in> select\<^sub>G\<^sub>s"
 
  then interpret grounded_first_order_superposition_calculus
    where select\<^sub>G = select\<^sub>G
    apply unfold_locales
    by(simp add: select\<^sub>G\<^sub>s_def)

  show "consequence_relation ground.G_Bot ground.G_entails"
    using ground.consequence_relation_axioms.
next
   fix select\<^sub>G
   assume "select\<^sub>G \<in> select\<^sub>G\<^sub>s"
 
   then interpret grounded_first_order_superposition_calculus
    where select\<^sub>G = select\<^sub>G
    apply unfold_locales
    by(simp add: select\<^sub>G\<^sub>s_def)

  show "tiebreaker_lifting
          \<bottom>\<^sub>F
          inferences 
          ground.G_Bot
          ground.G_entails
          ground.G_Inf 
          ground.GRed_I
          ground.GRed_F 
          (typed_clause_groundings typeof_fun)
          (Some \<circ> inference_groundings)
          tiebreakers"
    by unfold_locales
qed

end

    