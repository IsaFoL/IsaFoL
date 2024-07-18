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
    select :: "('f, 'v :: infinite) select" and
    typeof_fun :: "('f, 'ty) fun_types"
begin

sublocale ground: ground_superposition_calculus where
  less_trm = "(\<prec>\<^sub>t\<^sub>G)" and select = select\<^sub>G
  by unfold_locales (rule ground_critical_pair_theorem)

abbreviation is_inference_grounding where
  "is_inference_grounding \<iota> \<iota>\<^sub>G \<gamma> \<rho>\<^sub>1 \<rho>\<^sub>2 \<equiv>
    (case \<iota> of
        Infer [(premise, \<V>')] (conclusion, \<V>) \<Rightarrow>
           term_subst.is_ground_subst \<gamma>
        \<and> \<iota>\<^sub>G = Infer [to_ground_clause (premise \<cdot> \<gamma>)] (to_ground_clause (conclusion \<cdot> \<gamma>))
        \<and> welltyped\<^sub>c typeof_fun \<V> premise 
        \<and> welltyped\<^sub>\<sigma>_on (clause.vars conclusion) typeof_fun \<V> \<gamma>
        \<and> welltyped\<^sub>c typeof_fun \<V> conclusion
        \<and> \<V> = \<V>'
        \<and> all_types \<V>
      | Infer [(premise\<^sub>2, \<V>\<^sub>2), (premise\<^sub>1, \<V>\<^sub>1)] (conclusion, \<V>\<^sub>3) \<Rightarrow> 
          term_subst.is_renaming \<rho>\<^sub>1
        \<and> term_subst.is_renaming \<rho>\<^sub>2
        \<and> clause.vars (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter> clause.vars (premise\<^sub>2 \<cdot> \<rho>\<^sub>2) = {}
        \<and> term_subst.is_ground_subst \<gamma>
        \<and> \<iota>\<^sub>G =
            Infer
              [to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<gamma>), to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>)]
              (to_ground_clause (conclusion \<cdot> \<gamma>))
        \<and> welltyped\<^sub>c typeof_fun \<V>\<^sub>1 premise\<^sub>1
        \<and> welltyped\<^sub>c typeof_fun \<V>\<^sub>2 premise\<^sub>2
        \<and> welltyped\<^sub>\<sigma>_on (clause.vars conclusion) typeof_fun \<V>\<^sub>3 \<gamma>
        \<and> welltyped\<^sub>c typeof_fun \<V>\<^sub>3 conclusion
        \<and> all_types \<V>\<^sub>1 \<and> all_types \<V>\<^sub>2 \<and> all_types \<V>\<^sub>3
      | _ \<Rightarrow> False
     )
  \<and> \<iota>\<^sub>G \<in> ground.G_Inf"

definition inference_groundings where 
  "inference_groundings \<iota> = { \<iota>\<^sub>G | \<iota>\<^sub>G \<gamma> \<rho>\<^sub>1 \<rho>\<^sub>2. is_inference_grounding \<iota> \<iota>\<^sub>G \<gamma> \<rho>\<^sub>1 \<rho>\<^sub>2 }"

lemma is_inference_grounding_inference_groundings: 
  "is_inference_grounding \<iota> \<iota>\<^sub>G \<gamma> \<rho>\<^sub>1 \<rho>\<^sub>2  \<Longrightarrow> \<iota>\<^sub>G \<in> inference_groundings \<iota>"
  unfolding inference_groundings_def
  by blast

lemma inference\<^sub>G_concl_in_clause_grounding: 
  assumes "\<iota>\<^sub>G \<in> inference_groundings \<iota>"
  shows "concl_of \<iota>\<^sub>G \<in> clause_groundings typeof_fun (concl_of \<iota>)"
proof-
  obtain premises\<^sub>G conlcusion\<^sub>G where
    \<iota>\<^sub>G: "\<iota>\<^sub>G = Infer premises\<^sub>G conlcusion\<^sub>G"
    using Calculus.inference.exhaust by blast

  obtain "premises" "conclusion" \<V> where
    \<iota>: "\<iota> = Infer premises (conclusion, \<V>)"
    using Calculus.inference.exhaust
    by (metis prod.collapse)

  (* TODO: *)
  then obtain \<gamma> where
    "clause.is_ground (conclusion \<cdot> \<gamma>)"
    "conlcusion\<^sub>G = to_ground_clause (conclusion \<cdot> \<gamma>)"
    "welltyped\<^sub>c typeof_fun \<V> conclusion \<and> welltyped\<^sub>\<sigma>_on (clause.vars conclusion) typeof_fun \<V> \<gamma> \<and> term_subst.is_ground_subst \<gamma> \<and> all_types \<V>"
    using assms list_4_cases
    unfolding inference_groundings_def \<iota> \<iota>\<^sub>G Calculus.inference.case
    apply(auto split: list.splits)
    unfolding atom.is_ground_subst_iff[symmetric] literal.is_ground_subst_iff[symmetric] clause.is_ground_subst_iff[symmetric]
    by (metis clause.is_ground_subst_is_ground list_4_cases prod.exhaust_sel)

  then show ?thesis
    unfolding \<iota> \<iota>\<^sub>G clause_groundings_def
    by auto
qed  

lemma inference\<^sub>G_red_in_clause_grounding_of_concl: 
  assumes "\<iota>\<^sub>G \<in> inference_groundings \<iota>"
  shows "\<iota>\<^sub>G \<in> ground.Red_I (clause_groundings typeof_fun (concl_of \<iota>))"
proof-
  from assms have "\<iota>\<^sub>G \<in> ground.G_Inf"
    unfolding inference_groundings_def
    by blast

  moreover have "concl_of \<iota>\<^sub>G \<in> clause_groundings typeof_fun  (concl_of \<iota>)"
    using assms inference\<^sub>G_concl_in_clause_grounding
    by auto

  ultimately show "\<iota>\<^sub>G \<in> ground.Red_I (clause_groundings typeof_fun (concl_of \<iota>))"
    using ground.Red_I_of_Inf_to_N
    by blast
qed

lemma obtain_welltyped_ground_subst:
  obtains \<gamma> :: "('f, 'v) subst" and \<F>\<^sub>G :: "('f, 'ty) fun_types"
  where "welltyped\<^sub>\<sigma> typeof_fun \<V> \<gamma>" "term_subst.is_ground_subst \<gamma>"
proof-
 
  define \<gamma> :: "('f, 'v) subst" where
    "\<And>x. \<gamma> x \<equiv> Fun (SOME f. typeof_fun f = ([], \<V> x)) []"


  moreover have "welltyped\<^sub>\<sigma> typeof_fun \<V> \<gamma>"
    unfolding welltyped\<^sub>\<sigma>_def \<gamma>_def
    apply auto
    apply(rule welltyped.Fun)
    using function_symbols
     apply auto
    by (meson tfl_some)    

  moreover have "term_subst.is_ground_subst \<gamma>"
    unfolding term_subst.is_ground_subst_def \<gamma>_def
    by (smt (verit) Nil_is_map_conv equals0D eval_term.simps(2) is_ground_iff is_ground_trm_iff_ident_forall_subst)

  ultimately show ?thesis
    using that
    by blast
qed


lemma welltyped\<^sub>\<sigma>_on_empty: "welltyped\<^sub>\<sigma>_on {} \<F> \<V> \<sigma>"
  unfolding welltyped\<^sub>\<sigma>_on_def
  by simp  

sublocale lifting: 
    tiebreaker_lifting
          "\<bottom>\<^sub>F"
          inferences 
          ground.G_Bot
          ground.G_entails
          ground.G_Inf 
          ground.GRed_I
          ground.GRed_F 
          "clause_groundings typeof_fun"
          "(Some \<circ> inference_groundings)"
          typed_tiebreakers
proof unfold_locales
  show "\<bottom>\<^sub>F \<noteq> {}"
    using all_types'[OF variables]
    by blast
next
  fix bottom
  assume "bottom \<in> \<bottom>\<^sub>F"

  then show "clause_groundings typeof_fun bottom \<noteq> {}"
    unfolding clause_groundings_def
    using welltyped\<^sub>\<sigma>_Var
    apply(clause_auto simp: welltyped\<^sub>c_def welltyped\<^sub>\<sigma>_on_empty)
    using obtain_ground_subst
    by metis
next
  fix bottom
  assume "bottom \<in> \<bottom>\<^sub>F"
  then show "clause_groundings typeof_fun bottom \<subseteq> ground.G_Bot"
    unfolding clause_groundings_def
    by clause_auto
next
  fix clause
  show "clause_groundings typeof_fun clause \<inter> ground.G_Bot \<noteq> {} \<longrightarrow> clause \<in> \<bottom>\<^sub>F"
    unfolding clause_groundings_def to_ground_clause_def clause.subst_def
    apply auto
    by (metis prod.exhaust_sel)
next
  fix \<iota> :: "('f, 'v, 'ty) typed_clause inference"

  show "the ((Some \<circ> inference_groundings) \<iota>) \<subseteq> ground.GRed_I (clause_groundings typeof_fun (concl_of \<iota>))"
    using inference\<^sub>G_red_in_clause_grounding_of_concl
    by auto
next
  show "\<And>clause\<^sub>G. po_on (typed_tiebreakers clause\<^sub>G) UNIV"
    unfolding po_on_def
    using wellfounded_typed_tiebreakers
    by simp
next
  show "\<And>clause\<^sub>G. wfp_on (typed_tiebreakers clause\<^sub>G) UNIV"
    using wellfounded_typed_tiebreakers
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
    "\<lambda>_. clause_groundings typeof_fun" 
    "\<lambda>select\<^sub>G. Some \<circ>
      (grounded_first_order_superposition_calculus.inference_groundings (\<prec>\<^sub>t) select\<^sub>G typeof_fun)"
    typed_tiebreakers
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
          (clause_groundings typeof_fun)
          (Some \<circ> inference_groundings)
          typed_tiebreakers"
    by unfold_locales
qed

end

    