theory Grounded_First_Order_Superposition
  imports 
    First_Order_Superposition
    Ground_Superposition_Completeness (* TODO: Completeness needed? *)
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
  first_order_superposition_calculus where select = select and typeof_fun = typeof_fun +
  grounded_first_order_select where \<F> = typeof_fun and select = select 
  for
    select :: "('f, 'v :: infinite) select" and
    typeof_fun :: "('f, 'ty) fun_types"
begin

sublocale ground: ground_superposition_calculus where
  less\<^sub>t = "(\<prec>\<^sub>t\<^sub>G)" and select = select\<^sub>G
rewrites 
  "multiset_extension.multiset_extension (\<prec>\<^sub>t\<^sub>G) mset_lit  = (\<prec>\<^sub>l\<^sub>G)" and 
  "multiset_extension.multiset_extension (\<prec>\<^sub>l\<^sub>G) (\<lambda>x. x) = (\<prec>\<^sub>c\<^sub>G)" and
  "\<And>l C. ground.is_maximal l C \<longleftrightarrow> is_maximal (literal.from_ground l) (clause.from_ground C)" and
  "\<And>l C. ground.is_strictly_maximal l C \<longleftrightarrow>
    is_strictly_maximal (literal.from_ground l) (clause.from_ground C)"
  by unfold_locales (auto simp: ground_critical_pair_theorem)

abbreviation is_inference_grounding where
  "is_inference_grounding \<iota> \<iota>\<^sub>G \<gamma> \<rho>\<^sub>1 \<rho>\<^sub>2 \<equiv>
    (case \<iota> of
        Infer [(premise, \<V>')] (conclusion, \<V>) \<Rightarrow>
           term_subst.is_ground_subst \<gamma>
        \<and> \<iota>\<^sub>G = Infer [clause.to_ground (premise \<cdot> \<gamma>)] (clause.to_ground (conclusion \<cdot> \<gamma>))
        \<and> clause.is_welltyped \<V> premise 
        \<and> is_welltyped_on (clause.vars conclusion) \<V> \<gamma>
        \<and> clause.is_welltyped \<V> conclusion
        \<and> \<V> = \<V>'
        \<and> all_types \<V>
      | Infer [(premise\<^sub>2, \<V>\<^sub>2), (premise\<^sub>1, \<V>\<^sub>1)] (conclusion, \<V>\<^sub>3) \<Rightarrow> 
          term_subst.is_renaming \<rho>\<^sub>1
        \<and> term_subst.is_renaming \<rho>\<^sub>2
        \<and> clause.vars (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter> clause.vars (premise\<^sub>2 \<cdot> \<rho>\<^sub>2) = {}
        \<and> term_subst.is_ground_subst \<gamma>
        \<and> \<iota>\<^sub>G =
            Infer
              [clause.to_ground (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<gamma>), clause.to_ground (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>)]
              (clause.to_ground (conclusion \<cdot> \<gamma>))
        \<and> clause.is_welltyped \<V>\<^sub>1 premise\<^sub>1
        \<and> clause.is_welltyped \<V>\<^sub>2 premise\<^sub>2
        \<and> is_welltyped_on (clause.vars conclusion) \<V>\<^sub>3 \<gamma>
        \<and> clause.is_welltyped \<V>\<^sub>3 conclusion
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
  shows "concl_of \<iota>\<^sub>G \<in> clause_groundings (concl_of \<iota>)"
proof-
  obtain premises\<^sub>G conlcusion\<^sub>G where
    \<iota>\<^sub>G: "\<iota>\<^sub>G = Infer premises\<^sub>G conlcusion\<^sub>G"
    using Calculus.inference.exhaust by blast

  obtain "premises" "conclusion" \<V> where
    \<iota>: "\<iota> = Infer premises (conclusion, \<V>)"
    using Calculus.inference.exhaust
    by (metis prod.collapse)

  (* TODO: *)
  obtain \<gamma> where
    "clause.is_ground (conclusion \<cdot> \<gamma>)"
    "conlcusion\<^sub>G = clause.to_ground (conclusion \<cdot> \<gamma>)"
    "clause.is_welltyped \<V> conclusion \<and> is_welltyped_on (clause.vars conclusion) \<V> \<gamma> \<and> 
    term_subst.is_ground_subst \<gamma> \<and> all_types \<V>"
  proof-
    (* TODO! *)
    have "\<And>\<gamma> \<rho>\<^sub>1 \<rho>\<^sub>2.
       \<lbrakk>\<And>\<gamma>. \<lbrakk>clause.vars (conclusion \<cdot> \<gamma>) = {}; conlcusion\<^sub>G = clause.to_ground (conclusion \<cdot> \<gamma>);
              clause.is_welltyped \<V> conclusion \<and>
              is_welltyped_on (clause.vars conclusion) \<V> \<gamma> \<and>
              term_subst.is_ground_subst \<gamma> \<and> all_types \<V>\<rbrakk>
             \<Longrightarrow> thesis;
        Infer premises\<^sub>G conlcusion\<^sub>G \<in> ground.G_Inf;
        case premises of [] \<Rightarrow> False
        | [(premise, \<V>')] \<Rightarrow>
            term_subst.is_ground_subst \<gamma> \<and>
            Infer premises\<^sub>G conlcusion\<^sub>G =
            Infer [clause.to_ground (premise \<cdot> \<gamma>)] (clause.to_ground (conclusion \<cdot> \<gamma>)) \<and>
            clause.is_welltyped \<V> premise \<and>
            is_welltyped_on (clause.vars conclusion) \<V> \<gamma> \<and>
            clause.is_welltyped \<V> conclusion \<and> \<V> = \<V>' \<and> all_types \<V>
        | [(premise, \<V>'), (premise\<^sub>1, \<V>\<^sub>1)] \<Rightarrow>
            clause.is_renaming \<rho>\<^sub>1 \<and>
            clause.is_renaming \<rho>\<^sub>2 \<and>
            clause.vars (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter> clause.vars (premise \<cdot> \<rho>\<^sub>2) = {} \<and>
            term_subst.is_ground_subst \<gamma> \<and>
            Infer premises\<^sub>G conlcusion\<^sub>G =
            Infer [clause.to_ground (premise \<cdot> \<rho>\<^sub>2 \<cdot> \<gamma>), clause.to_ground (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>)]
             (clause.to_ground (conclusion \<cdot> \<gamma>)) \<and>
            clause.is_welltyped \<V>\<^sub>1 premise\<^sub>1 \<and>
            clause.is_welltyped \<V>' premise \<and>
            is_welltyped_on (clause.vars conclusion) \<V> \<gamma> \<and>
            clause.is_welltyped \<V> conclusion \<and>
            all_types \<V>\<^sub>1 \<and> all_types \<V>' \<and> all_types \<V>
        | (premise, \<V>') # (premise\<^sub>1, \<V>\<^sub>1) # a # lista \<Rightarrow> False\<rbrakk>
       \<Longrightarrow> thesis"
     (* TOOD: *)
      apply(auto simp: clause.is_ground_subst_is_ground split: list.splits)
      by (metis list_4_cases prod.exhaust_sel)

     then show ?thesis
      using that assms 
      unfolding inference_groundings_def \<iota> \<iota>\<^sub>G Calculus.inference.case
      by auto
  qed

  then show ?thesis
    unfolding \<iota> \<iota>\<^sub>G clause_groundings_def
    by auto
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

lemma obtain_welltyped_ground_subst:
  obtains \<gamma> :: "('f, 'v) subst" and \<F>\<^sub>G :: "('f, 'ty) fun_types"
  where "is_welltyped \<V> \<gamma>" "term_subst.is_ground_subst \<gamma>"
proof-
 
  define \<gamma> :: "('f, 'v) subst" where
    "\<And>x. \<gamma> x \<equiv> Fun (SOME f. typeof_fun f = ([], \<V> x)) []"


  moreover have "is_welltyped \<V> \<gamma>"
  proof-
    have "\<And>x. welltyped \<V>
          (Fun (SOME f. typeof_fun f = ([], \<V> x)) []) (\<V> x)"
      by (meson function_symbols list_all2_Nil someI_ex welltyped.Fun)

    then show ?thesis
      unfolding \<gamma>_def
      by auto
  qed

  moreover have "term_subst.is_ground_subst \<gamma>"
    unfolding term_subst.is_ground_subst_def \<gamma>_def
    by (smt (verit) Nil_is_map_conv equals0D eval_term.simps(2) is_ground_iff is_ground_trm_iff_ident_forall_subst)

  ultimately show ?thesis
    using that
    by blast
qed


lemma is_welltyped_on_empty: "is_welltyped_on {} \<V> \<sigma>"
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
          "clause_groundings"
          "(Some \<circ> inference_groundings)"
          typed_tiebreakers
proof unfold_locales
  show "\<bottom>\<^sub>F \<noteq> {}"
    using all_types'[OF variables]
    by blast
next
  fix bottom
  assume "bottom \<in> \<bottom>\<^sub>F"

  then show "clause_groundings bottom \<noteq> {}"
    unfolding clause_groundings_def
    using is_welltyped_id_subst
  proof -
    have "\<exists>f. is_welltyped_on (clause.vars {#}) (snd bottom) f \<and> 
          clause.is_welltyped (snd bottom) {#} \<and> 
          term_subst.is_ground_subst f"
      by (metis clause.is_welltyped_def emptyE empty_clause_is_ground set_mset_empty
          term.obtain_ground_subst)

    then show "{clause.to_ground (fst bottom \<cdot> f) |f. term_subst.is_ground_subst f 
        \<and> clause.is_welltyped (snd bottom) (fst bottom) 
        \<and> is_welltyped_on (clause.vars (fst bottom)) (snd bottom) f 
        \<and> all_types (snd bottom)} \<noteq> {}"
      using \<open>bottom \<in> \<bottom>\<^sub>F\<close>
      by fastforce
  qed
next
  fix bottom
  assume "bottom \<in> \<bottom>\<^sub>F"
  then show "clause_groundings bottom \<subseteq> ground.G_Bot"
    unfolding clause_groundings_def
    by clause_auto
next
  fix clause
  show "clause_groundings clause \<inter> ground.G_Bot \<noteq> {} \<longrightarrow> clause \<in> \<bottom>\<^sub>F"
    unfolding clause_groundings_def clause.to_ground_def clause.subst_def
    by (smt (verit) disjoint_insert(1) image_mset_is_empty_iff inf_bot_right mem_Collect_eq 
        prod.exhaust_sel)
next
  fix \<iota> :: "('f, 'v, 'ty) typed_clause inference"

  show "the ((Some \<circ> inference_groundings) \<iota>) \<subseteq> 
      ground.GRed_I (clause_groundings (concl_of \<iota>))"
    using inference\<^sub>G_red_in_clause_grounding_of_concl
    by auto
next
  show "\<And>clause\<^sub>G. po_on (typed_tiebreakers clause\<^sub>G) UNIV"
    unfolding po_on_def
    using wellfounded_typed_tiebreakers
    by simp
next
  show "\<And>clause\<^sub>G. Restricted_Predicates.wfp_on (typed_tiebreakers clause\<^sub>G) UNIV"
    using wellfounded_typed_tiebreakers
    by simp
qed

end

context first_order_superposition_calculus
begin

sublocale
  lifting_intersection
    inferences      
    "{{#}}"
    select\<^sub>G\<^sub>s
    "ground_superposition_calculus.G_Inf (\<prec>\<^sub>t\<^sub>G)"
    "\<lambda>_. ground_superposition_calculus.G_entails"
    "ground_superposition_calculus.GRed_I (\<prec>\<^sub>t\<^sub>G)"
    "\<lambda>_. ground_superposition_calculus.GRed_F(\<prec>\<^sub>t\<^sub>G)"
    "\<bottom>\<^sub>F"
    "\<lambda>_. clause_groundings" 
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
    by unfold_locales (simp add: select\<^sub>G\<^sub>s_def)

  show "consequence_relation ground.G_Bot ground.G_entails"
    using ground.consequence_relation_axioms.
next
   fix select\<^sub>G
   assume "select\<^sub>G \<in> select\<^sub>G\<^sub>s"
 
   then interpret grounded_first_order_superposition_calculus
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

    