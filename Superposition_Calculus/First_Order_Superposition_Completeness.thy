theory First_Order_Superposition_Completeness
  imports
    Ground_Superposition_Completeness
    Grounded_First_Order_Superposition
    "HOL-ex.Sketch_and_Explore"
begin

lemma welltyped\<^sub>\<sigma>_on_term:
  assumes "welltyped\<^sub>\<sigma>_on (term.vars term) \<F> \<V> \<gamma>"
  shows "welltyped \<F> \<V> term \<tau> \<longleftrightarrow> welltyped \<F> \<V> (term \<cdot>t \<gamma>) \<tau>"
  by (simp add: assms welltyped\<^sub>\<sigma>_on_welltyped)

context grounded_first_order_superposition_calculus
begin


lemma eq_resolution_lifting:
  fixes 
    premise\<^sub>G conclusion\<^sub>G :: "'f gatom clause" and 
    premise "conclusion" :: "('f, 'v) atom clause" and
    \<gamma> :: "('f, 'v) subst"
  defines 
    premise\<^sub>G [simp]: "premise\<^sub>G \<equiv> clause.to_ground (premise \<cdot> \<gamma>)" and
    conclusion\<^sub>G [simp]: "conclusion\<^sub>G \<equiv> clause.to_ground (conclusion \<cdot> \<gamma>)"
  assumes 
    premise_grounding: "clause.is_ground (premise \<cdot> \<gamma>)" and
    conclusion_grounding: "clause.is_ground (conclusion \<cdot> \<gamma>)" and
    select: "clause.from_ground (select\<^sub>G premise\<^sub>G) = (select premise) \<cdot> \<gamma>" and
    ground_eq_resolution: "ground.ground_eq_resolution premise\<^sub>G conclusion\<^sub>G" and
    typing: 
    "welltyped\<^sub>c typeof_fun \<V> premise"
    "term_subst.is_ground_subst \<gamma>"
    "welltyped\<^sub>\<sigma>_on (clause.vars premise) typeof_fun \<V> \<gamma>"
    "all_types \<V>"
  obtains conclusion' 
  where
    "eq_resolution (premise, \<V>) (conclusion', \<V>)"
    "Infer [premise\<^sub>G] conclusion\<^sub>G \<in> inference_groundings (Infer [(premise, \<V>)] (conclusion', \<V>))"
    "conclusion' \<cdot> \<gamma> = conclusion \<cdot> \<gamma>"
  using ground_eq_resolution
proof(cases premise\<^sub>G conclusion\<^sub>G rule: ground.ground_eq_resolution.cases)
  case (ground_eq_resolutionI literal\<^sub>G premise\<^sub>G' term\<^sub>G)

  have premise_not_empty: "premise \<noteq> {#}"
    using 
      ground_eq_resolutionI(1)
      empty_not_add_mset
      clause_subst_empty
    unfolding premise\<^sub>G
    by (metis clause_from_ground_empty_mset clause.from_ground_inverse)

  have "premise \<cdot> \<gamma> = clause.from_ground (add_mset literal\<^sub>G (clause.to_ground (conclusion \<cdot> \<gamma>)))"
    using 
      ground_eq_resolutionI(1)[THEN arg_cong, of clause.from_ground]
      clause.to_ground_inverse[OF premise_grounding]
      ground_eq_resolutionI(4)
    unfolding premise\<^sub>G conclusion\<^sub>G
    by metis

  also have "... = add_mset (literal.from_ground literal\<^sub>G) (conclusion \<cdot> \<gamma>)"
    unfolding clause_from_ground_add_mset
    by (simp add: conclusion_grounding)

  finally have premise_\<gamma>: "premise \<cdot> \<gamma> = add_mset (literal.from_ground literal\<^sub>G) (conclusion \<cdot> \<gamma>)".

  let ?select\<^sub>G_empty = "select\<^sub>G premise\<^sub>G = {#}"
  let ?select\<^sub>G_not_empty = "select\<^sub>G premise\<^sub>G \<noteq> {#}"

  obtain max_literal where max_literal: 
    "is_maximal\<^sub>l max_literal premise" 
    "is_maximal\<^sub>l (max_literal \<cdot>l \<gamma>) (premise \<cdot> \<gamma>)"
    using is_maximal\<^sub>l_ground_subst_stability[OF premise_not_empty premise_grounding]
    by blast

  moreover then have "max_literal \<in># premise"
    using maximal\<^sub>l_in_clause by fastforce

  moreover have max_literal_\<gamma>: "max_literal \<cdot>l \<gamma> = literal.from_ground (term\<^sub>G !\<approx> term\<^sub>G)"
    if ?select\<^sub>G_empty
  proof-
    have "ground.is_maximal_lit literal\<^sub>G premise\<^sub>G"
      using ground_eq_resolutionI(3) that maximal_lit_in_clause
      by (metis empty_iff set_mset_empty)

    then show ?thesis
      using max_literal(2) unique_maximal_in_ground_clause[OF premise_grounding] 
      unfolding 
        ground_eq_resolutionI(2) 
        is_maximal_lit_iff_is_maximal\<^sub>l 
        premise\<^sub>G 
        clause.to_ground_inverse[OF premise_grounding]
      by blast
  qed

  moreover obtain selected_literal where 
    "selected_literal \<cdot>l \<gamma> = literal.from_ground (term\<^sub>G !\<approx> term\<^sub>G)" and
    "is_maximal\<^sub>l selected_literal (select premise)" 
  if ?select\<^sub>G_not_empty
  proof-
    have "ground.is_maximal_lit literal\<^sub>G (select\<^sub>G premise\<^sub>G)" if ?select\<^sub>G_not_empty
      using ground_eq_resolutionI(3) that
      by blast

    then show ?thesis 
      using 
        that 
        select 
        unique_maximal_in_ground_clause[OF select_subst(1)[OF premise_grounding]]
        is_maximal\<^sub>l_ground_subst_stability[OF _ select_subst(1)[OF premise_grounding]]
      unfolding
        ground_eq_resolutionI(2) 
        premise\<^sub>G
        is_maximal_lit_iff_is_maximal\<^sub>l
      by (metis (full_types) clause_subst_empty(2) clause.from_ground_inverse clause_to_ground_empty_mset)
  qed

  moreover then have "selected_literal \<in># premise" if ?select\<^sub>G_not_empty
    by (meson that maximal\<^sub>l_in_clause mset_subset_eqD select_subset)

  ultimately obtain literal where
    literal_\<gamma>: "literal \<cdot>l \<gamma> = literal.from_ground (term\<^sub>G !\<approx> term\<^sub>G)" and
    literal_in_premise: "literal \<in># premise" and
    literal_selected: "?select\<^sub>G_not_empty \<Longrightarrow> is_maximal\<^sub>l literal (select premise)" and
    literal_max: "?select\<^sub>G_empty \<Longrightarrow> is_maximal\<^sub>l literal premise"
    by blast

  have literal_grounding: "literal.is_ground (literal \<cdot>l \<gamma>)"
    using literal_\<gamma>
    by simp

  from literal_\<gamma> obtain "term" term' where 
    literal: "literal = term !\<approx> term'"
    using subst_polarity_stable literal_from_ground_polarity_stable
    by (metis literal.collapse(2) literal.disc(2) uprod_exhaust)


  have literal\<^sub>G: 
    "literal.from_ground literal\<^sub>G = (term !\<approx> term') \<cdot>l \<gamma>" 
    "literal\<^sub>G = literal.to_ground ((term !\<approx> term') \<cdot>l \<gamma>)"
    using literal_\<gamma> literal ground_eq_resolutionI(2) 
    by simp_all

  obtain conclusion' where conclusion': "premise = add_mset literal conclusion'"
    using multi_member_split[OF literal_in_premise]
    by blast

  have "term \<cdot>t \<gamma> = term' \<cdot>t \<gamma>"
    using literal_\<gamma>
    unfolding literal subst_literal(2) atom.subst_def literal.from_ground_def atom.from_ground_def
    by simp

  moreover obtain \<tau> where "welltyped typeof_fun \<V> term \<tau>" "welltyped typeof_fun \<V> term' \<tau>"
    using typing(1) 
    unfolding conclusion' literal welltyped\<^sub>c_def welltyped\<^sub>l_def welltyped\<^sub>a_def
    by auto

  ultimately obtain \<mu> \<sigma> where \<mu>: 
    "term_subst.is_imgu \<mu> {{term, term'}}" 
    "\<gamma> = \<mu> \<odot> \<sigma>" 
    "welltyped_imgu' typeof_fun \<V> term term' \<mu>"
    using welltyped_imgu'_exists
    by meson

  have conclusion'_\<gamma>: "conclusion' \<cdot> \<gamma> = conclusion \<cdot> \<gamma>"
    using premise_\<gamma>
    unfolding conclusion' ground_eq_resolutionI(2) literal_\<gamma>[symmetric] subst_clause_add_mset
    by simp

  have eq_resolution: "eq_resolution (premise, \<V>) (conclusion' \<cdot> \<mu>, \<V>)"
  proof (rule eq_resolutionI)
    show "premise = add_mset literal conclusion'"
      using conclusion'.
  next 
    show "literal = term !\<approx> term'"
      using literal.    
  next
    show "term_subst.is_imgu \<mu> {{term, term'}}"
      using \<mu>(1).
  next
    show "select premise = {#} \<and> is_maximal\<^sub>l (literal \<cdot>l \<mu>) (premise \<cdot> \<mu>) 
       \<or>  is_maximal\<^sub>l (literal \<cdot>l \<mu>) ((select premise) \<cdot> \<mu>)"
    proof(cases ?select\<^sub>G_empty)
      case select\<^sub>G_empty: True

      then have "max_literal \<cdot>l \<gamma> = literal \<cdot>l \<gamma>"
        by (simp add: max_literal_\<gamma> literal_\<gamma>)

      then have literal_\<gamma>_is_maximal: "is_maximal\<^sub>l (literal \<cdot>l \<gamma>) (premise \<cdot> \<gamma>)"
        using max_literal(2) by simp

      have literal_\<mu>_in_premise: "literal \<cdot>l \<mu> \<in># premise \<cdot> \<mu>"
        by (simp add: clause.subst_in_to_set_subst literal_in_premise)

      have "is_maximal\<^sub>l (literal \<cdot>l \<mu>) (premise \<cdot> \<mu>)"
        using is_maximal\<^sub>l_ground_subst_stability'[OF 
            literal_\<mu>_in_premise 
            premise_grounding[unfolded \<mu>(2) clause.subst_comp_subst]
            literal_\<gamma>_is_maximal[unfolded \<mu>(2) clause.subst_comp_subst literal.subst_comp_subst]
            ].

      then show ?thesis
        using select select\<^sub>G_empty
        by clause_auto
    next
      case False

      have selected_grounding: "clause.is_ground (select premise \<cdot> \<mu> \<cdot> \<sigma>)"
        using select_subst(1)[OF premise_grounding]
        unfolding \<mu>(2) clause.subst_comp_subst.

      note selected_subst =
        literal_selected[OF False, THEN maximal\<^sub>l_in_clause, THEN clause.subst_in_to_set_subst]

      have "is_maximal\<^sub>l (literal \<cdot>l \<gamma>) (select premise \<cdot> \<gamma>)"
        using False ground_eq_resolutionI(3) 
        unfolding ground_eq_resolutionI(2) is_maximal_lit_iff_is_maximal\<^sub>l literal_\<gamma> select
        by presburger

      then have "is_maximal\<^sub>l (literal \<cdot>l \<mu>) (select premise \<cdot> \<mu>)"
        unfolding \<mu>(2) clause.subst_comp_subst literal.subst_comp_subst
        using is_maximal\<^sub>l_ground_subst_stability'[OF selected_subst selected_grounding]
        by argo

      with False show ?thesis
        by blast
    qed
  next 
    show "welltyped_imgu' typeof_fun \<V> term term' \<mu>"
      using \<mu>(3).
  next 
    show "conclusion' \<cdot> \<mu> = conclusion' \<cdot> \<mu>" ..
  qed

  have "term_subst.is_idem \<mu>"
    using \<mu>(1)
    by (simp add: term_subst.is_imgu_iff_is_idem_and_is_mgu)  

  then have \<mu>_\<gamma>: "\<mu> \<odot> \<gamma> = \<gamma>"
    unfolding \<mu>(2) term_subst.is_idem_def
    by (metis subst_compose_assoc)

  have vars_conclusion': "clause.vars (conclusion' \<cdot> \<mu>) \<subseteq> clause.vars premise"
    using vars_clause_imgu[OF \<mu>(1)] 
    unfolding conclusion' literal 
    by clause_auto

  have "conclusion' \<cdot> \<mu> \<cdot> \<gamma> = conclusion \<cdot> \<gamma>"
    using conclusion'_\<gamma>  
    unfolding clause.subst_comp_subst[symmetric] \<mu>_\<gamma>.

  moreover have
    "Infer [premise\<^sub>G] conclusion\<^sub>G \<in> inference_groundings (Infer [(premise, \<V>)] (conclusion' \<cdot> \<mu>, \<V>))"
    unfolding inference_groundings_def mem_Collect_eq
  proof -
    have "Infer [premise\<^sub>G] conclusion\<^sub>G \<in> ground.G_Inf"
      unfolding ground.G_Inf_def
      using ground_eq_resolution by blast

    then have "\<exists>\<rho>\<^sub>1 \<rho>\<^sub>2. is_inference_grounding
      (Infer [(premise, \<V>)] (conclusion' \<cdot> \<mu>, \<V>))
      (Infer [premise\<^sub>G] conclusion\<^sub>G) \<gamma> \<rho>\<^sub>1 \<rho>\<^sub>2"
      unfolding is_inference_grounding_def Calculus.inference.case list.case prod.case
      using typing
      by (smt (verit) calculation conclusion\<^sub>G eq_resolution eq_resolution_preserves_typing premise\<^sub>G
          vars_conclusion' welltyped\<^sub>\<sigma>_on_subset)

    thus "\<exists>\<iota>\<^sub>G \<gamma> \<rho>\<^sub>1 \<rho>\<^sub>2. Infer [premise\<^sub>G] conclusion\<^sub>G = \<iota>\<^sub>G \<and>
       is_inference_grounding (Infer [(premise, \<V>)] (conclusion' \<cdot> \<mu>, \<V>)) \<iota>\<^sub>G \<gamma> \<rho>\<^sub>1 \<rho>\<^sub>2"
      by iprover
  qed

  ultimately show ?thesis
    using that[OF eq_resolution]
    by blast
qed

lemma eq_factoring_lifting:
  fixes 
    premise\<^sub>G conclusion\<^sub>G :: "'f gatom clause" and 
    premise "conclusion" :: "('f, 'v) atom clause" and
    \<gamma> :: "('f, 'v) subst"
  defines 
    premise\<^sub>G [simp]: "premise\<^sub>G \<equiv> clause.to_ground (premise \<cdot> \<gamma>)" and
    conclusion\<^sub>G [simp]: "conclusion\<^sub>G \<equiv> clause.to_ground (conclusion \<cdot> \<gamma>)"
  assumes
    premise_grounding: "clause.is_ground (premise \<cdot> \<gamma>)" and
    conclusion_grounding: "clause.is_ground (conclusion \<cdot> \<gamma>)" and
    select: "clause.from_ground (select\<^sub>G premise\<^sub>G) = (select premise) \<cdot> \<gamma>" and
    ground_eq_factoring: "ground.ground_eq_factoring premise\<^sub>G conclusion\<^sub>G" and
    typing:
    "welltyped\<^sub>c typeof_fun \<V> premise"
    "term_subst.is_ground_subst \<gamma>"
    "welltyped\<^sub>\<sigma>_on (clause.vars premise) typeof_fun \<V> \<gamma>"
    "all_types \<V>"
  obtains conclusion' 
  where
    "eq_factoring (premise, \<V>) (conclusion', \<V>)"
    "Infer [premise\<^sub>G] conclusion\<^sub>G \<in> inference_groundings (Infer [(premise, \<V>)] (conclusion', \<V>))"
    "conclusion' \<cdot> \<gamma> = conclusion \<cdot> \<gamma>"
  using ground_eq_factoring
proof(cases premise\<^sub>G conclusion\<^sub>G rule: ground.ground_eq_factoring.cases)
  case (ground_eq_factoringI literal\<^sub>G\<^sub>1 literal\<^sub>G\<^sub>2 premise'\<^sub>G term\<^sub>G\<^sub>1 term\<^sub>G\<^sub>2 term\<^sub>G\<^sub>3)

  have premise_not_empty: "premise \<noteq> {#}"
    using ground_eq_factoringI(1) empty_not_add_mset clause_subst_empty premise\<^sub>G
    by (metis clause_from_ground_empty_mset clause.from_ground_inverse)

  have select_empty: "select premise = {#}"
    using ground_eq_factoringI(4) select clause_subst_empty
    by clause_auto

  have premise_\<gamma>: "premise \<cdot> \<gamma> = clause.from_ground (add_mset literal\<^sub>G\<^sub>1 (add_mset literal\<^sub>G\<^sub>2 premise'\<^sub>G))"
    using ground_eq_factoringI(1) premise\<^sub>G
    by (metis premise_grounding clause.to_ground_inverse)

  obtain literal\<^sub>1 where literal\<^sub>1_maximal: 
    "is_maximal\<^sub>l literal\<^sub>1 premise" 
    "is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<gamma>) (premise \<cdot> \<gamma>)"
    using is_maximal\<^sub>l_ground_subst_stability[OF premise_not_empty premise_grounding]
    by blast

  have max_ground_literal: "is_maximal\<^sub>l (literal.from_ground (term\<^sub>G\<^sub>1 \<approx> term\<^sub>G\<^sub>2)) (premise \<cdot> \<gamma>)"
    using ground_eq_factoringI(5)
    unfolding 
      is_maximal_lit_iff_is_maximal\<^sub>l 
      ground_eq_factoringI(2) 
      premise\<^sub>G 
      clause.to_ground_inverse[OF premise_grounding].

  have literal\<^sub>1_\<gamma>: "literal\<^sub>1 \<cdot>l \<gamma> = literal.from_ground literal\<^sub>G\<^sub>1"
    using 
      unique_maximal_in_ground_clause[OF premise_grounding literal\<^sub>1_maximal(2) max_ground_literal]
      ground_eq_factoringI(2)
    by blast

  then have "is_pos literal\<^sub>1"
    unfolding ground_eq_factoringI(2)
    using literal_from_ground_stable subst_pos_stable
    by (metis literal.disc(1))

  with literal\<^sub>1_\<gamma> obtain term\<^sub>1 term\<^sub>1' where 
    literal\<^sub>1_terms: "literal\<^sub>1 = term\<^sub>1 \<approx> term\<^sub>1'" and
    term\<^sub>G\<^sub>1_term\<^sub>1: "term.from_ground term\<^sub>G\<^sub>1 = term\<^sub>1 \<cdot>t \<gamma>"
    unfolding ground_eq_factoringI(2)
    by clause_simp
  
  obtain premise'' where premise'': "premise = add_mset literal\<^sub>1 premise''"
    using maximal\<^sub>l_in_clause[OF literal\<^sub>1_maximal(1)]
    by (meson multi_member_split)

  then have premise''_\<gamma>: "premise'' \<cdot> \<gamma> =  add_mset (literal.from_ground literal\<^sub>G\<^sub>2) (clause.from_ground premise'\<^sub>G)"
    using premise_\<gamma> 
    unfolding clause_from_ground_add_mset literal\<^sub>1_\<gamma>[symmetric]
    by (simp add: subst_clause_add_mset)

  then obtain literal\<^sub>2 where literal\<^sub>2:
    "literal\<^sub>2 \<cdot>l \<gamma> = literal.from_ground literal\<^sub>G\<^sub>2"
    "literal\<^sub>2 \<in># premise''"
    unfolding clause.subst_def
    using msed_map_invR by force

  then have "is_pos literal\<^sub>2"
    unfolding ground_eq_factoringI(3)
    using literal_from_ground_stable subst_pos_stable
    by (metis literal.disc(1))

  with literal\<^sub>2 obtain term\<^sub>2 term\<^sub>2' where 
    literal\<^sub>2_terms: "literal\<^sub>2 = term\<^sub>2 \<approx> term\<^sub>2'" and
    term\<^sub>G\<^sub>1_term\<^sub>2: "term.from_ground term\<^sub>G\<^sub>1 = term\<^sub>2 \<cdot>t \<gamma>"
    unfolding ground_eq_factoringI(3) 
    by clause_simp

  have term\<^sub>G\<^sub>2_term\<^sub>1': "term.from_ground term\<^sub>G\<^sub>2 = term\<^sub>1' \<cdot>t \<gamma>"
    using literal\<^sub>1_\<gamma> term\<^sub>G\<^sub>1_term\<^sub>1 
    unfolding 
      literal\<^sub>1_terms 
      ground_eq_factoringI(2)       
    apply clause_simp
    by auto

  have term\<^sub>G\<^sub>3_term\<^sub>2': "term.from_ground term\<^sub>G\<^sub>3 = term\<^sub>2' \<cdot>t \<gamma>"
    using literal\<^sub>2 term\<^sub>G\<^sub>1_term\<^sub>2
    unfolding 
      literal\<^sub>2_terms 
      ground_eq_factoringI(3) 
    by clause_auto

  obtain premise' where premise: "premise = add_mset literal\<^sub>1 (add_mset literal\<^sub>2 premise')" 
    using literal\<^sub>2(2) maximal\<^sub>l_in_clause[OF  literal\<^sub>1_maximal(1)] premise''
    by (metis multi_member_split)

  then have premise'_\<gamma>: "premise' \<cdot> \<gamma> = clause.from_ground premise'\<^sub>G"
    using premise''_\<gamma>  premise''
    unfolding literal\<^sub>2(1)[symmetric]
    by (simp add: subst_clause_add_mset)

  have term\<^sub>1_term\<^sub>2: "term\<^sub>1 \<cdot>t \<gamma> = term\<^sub>2 \<cdot>t \<gamma>"
    using term\<^sub>G\<^sub>1_term\<^sub>1 term\<^sub>G\<^sub>1_term\<^sub>2
    by argo

  moreover obtain \<tau> where "welltyped typeof_fun \<V> term\<^sub>1 \<tau>" "welltyped typeof_fun \<V> term\<^sub>2 \<tau>"
  proof-
    have "welltyped\<^sub>c typeof_fun \<V> (premise \<cdot> \<gamma>)"
      using typing
      using welltyped\<^sub>\<sigma>_on_welltyped\<^sub>c by blast

    then obtain \<tau> where "welltyped typeof_fun \<V> (term.from_ground term\<^sub>G\<^sub>1) \<tau>"
      unfolding premise_\<gamma>  ground_eq_factoringI 
      by clause_simp

    then have "welltyped typeof_fun \<V> (term\<^sub>1 \<cdot>t \<gamma>) \<tau>" "welltyped typeof_fun \<V> (term\<^sub>2 \<cdot>t \<gamma>) \<tau>"
      using term\<^sub>G\<^sub>1_term\<^sub>1 term\<^sub>G\<^sub>1_term\<^sub>2
      by metis+

    then have "welltyped typeof_fun \<V> term\<^sub>1 \<tau>" "welltyped typeof_fun \<V> term\<^sub>2 \<tau>"
      using typing(3) welltyped\<^sub>\<sigma>_on_term
      unfolding welltyped\<^sub>\<sigma>_on_def premise literal\<^sub>1_terms literal\<^sub>2_terms
      apply clause_simp 
      by (metis UnCI welltyped\<^sub>\<sigma>_on_def welltyped\<^sub>\<sigma>_on_term)+

    then show ?thesis
      using that
      by blast
  qed

  ultimately obtain \<mu> \<sigma> where \<mu>: 
    "term_subst.is_imgu \<mu> {{term\<^sub>1, term\<^sub>2}}" 
    "\<gamma> = \<mu> \<odot> \<sigma>" 
    "welltyped_imgu' typeof_fun \<V> term\<^sub>1 term\<^sub>2 \<mu>"
    using welltyped_imgu'_exists
    by meson

  let ?conclusion' = "add_mset (term\<^sub>1 \<approx> term\<^sub>2') (add_mset (term\<^sub>1' !\<approx> term\<^sub>2') premise')"

  have eq_factoring: "eq_factoring (premise, \<V>) (?conclusion' \<cdot> \<mu>, \<V>)"
  proof (rule eq_factoringI)
    show "premise = add_mset literal\<^sub>1 (add_mset literal\<^sub>2 premise')"
      using premise.
  next
    show "literal\<^sub>1 = term\<^sub>1 \<approx> term\<^sub>1'"
      using literal\<^sub>1_terms.
  next 
    show "literal\<^sub>2 = term\<^sub>2 \<approx> term\<^sub>2'"
      using literal\<^sub>2_terms.
  next 
    show  "select premise = {#}"
      using select_empty.
  next
    have literal\<^sub>1_\<mu>_in_premise: "literal\<^sub>1 \<cdot>l \<mu> \<in># premise \<cdot> \<mu>"
      using literal\<^sub>1_maximal(1) clause.subst_in_to_set_subst maximal\<^sub>l_in_clause by blast

    have "is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<mu>) (premise \<cdot> \<mu>)"
      using is_maximal\<^sub>l_ground_subst_stability'[OF 
          literal\<^sub>1_\<mu>_in_premise 
          premise_grounding[unfolded \<mu>(2) clause.subst_comp_subst]
          literal\<^sub>1_maximal(2)[unfolded \<mu>(2) clause.subst_comp_subst literal.subst_comp_subst]
          ].

    then show "is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<mu>) (premise \<cdot> \<mu>)"
      by blast
  next
    have term_groundings: "term.is_ground (term\<^sub>1' \<cdot>t \<mu> \<cdot>t \<sigma>)" "term.is_ground (term\<^sub>1 \<cdot>t \<mu> \<cdot>t \<sigma>)" 
      unfolding 
        term_subst.subst_comp_subst[symmetric] 
        \<mu>(2)[symmetric]
        term\<^sub>G\<^sub>1_term\<^sub>1[symmetric] 
        term\<^sub>G\<^sub>2_term\<^sub>1'[symmetric] 
      using term.ground_is_ground
      by simp_all

    have "term\<^sub>1' \<cdot>t \<mu> \<cdot>t \<sigma> \<prec>\<^sub>t term\<^sub>1 \<cdot>t \<mu> \<cdot>t \<sigma>"
      using ground_eq_factoringI(6)[unfolded 
          less\<^sub>t\<^sub>G_def 
          term\<^sub>G\<^sub>1_term\<^sub>1 
          term\<^sub>G\<^sub>2_term\<^sub>1'
          \<mu>(2) 
          term_subst.subst_comp_subst
          ].

    then show "\<not> term\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t term\<^sub>1' \<cdot>t \<mu>"
      using less\<^sub>t_less_eq\<^sub>t_ground_subst_stability[OF term_groundings]
      by blast
  next 
    show "term_subst.is_imgu \<mu> {{term\<^sub>1, term\<^sub>2}}"
      using \<mu>(1).
  next 
    show "welltyped_imgu' typeof_fun \<V> term\<^sub>1 term\<^sub>2 \<mu>"
      using \<mu>(3).
  next
    show "?conclusion' \<cdot> \<mu> = ?conclusion' \<cdot> \<mu>"
      ..
  qed

  have "term_subst.is_idem \<mu>"
    using \<mu>(1)
    by (simp add: term_subst.is_imgu_iff_is_idem_and_is_mgu)  

  then have \<mu>_\<gamma>: "\<mu> \<odot> \<gamma> = \<gamma>"
    unfolding \<mu>(2) term_subst.is_idem_def
    by (metis subst_compose_assoc)

  have vars_conclusion': "clause.vars (?conclusion' \<cdot> \<mu>) \<subseteq> clause.vars premise"
    using vars_clause_imgu[OF \<mu>(1)] vars_term_imgu[OF \<mu>(1)]
    unfolding premise literal\<^sub>1_terms literal\<^sub>2_terms
    by clause_auto

  have "conclusion \<cdot> \<gamma> = 
      add_mset (term.from_ground term\<^sub>G\<^sub>2 !\<approx> term.from_ground term\<^sub>G\<^sub>3) 
        (add_mset (term.from_ground term\<^sub>G\<^sub>1 \<approx> term.from_ground term\<^sub>G\<^sub>3) (clause.from_ground premise'\<^sub>G))"
    using ground_eq_factoringI(7) clause.to_ground_inverse[OF conclusion_grounding]
    unfolding atom_from_ground_term_from_ground[symmetric] 
      literal_from_ground_atom_from_ground[symmetric] clause_from_ground_add_mset[symmetric]
    by simp

  then have conclusion_\<gamma>: 
    "conclusion \<cdot> \<gamma> = add_mset (term\<^sub>1 \<approx> term\<^sub>2') (add_mset (term\<^sub>1' !\<approx> term\<^sub>2') premise') \<cdot> \<gamma>"
    unfolding 
      term\<^sub>G\<^sub>2_term\<^sub>1'
      term\<^sub>G\<^sub>3_term\<^sub>2'
      term\<^sub>G\<^sub>1_term\<^sub>1
      premise'_\<gamma>[symmetric]
    by(clause_simp simp: add_mset_commute)

  then have "?conclusion' \<cdot> \<mu> \<cdot> \<gamma> = conclusion \<cdot> \<gamma>"
    by (metis \<mu>_\<gamma> clause.subst_comp_subst)

  moreover have 
    "Infer [premise\<^sub>G] conclusion\<^sub>G \<in> inference_groundings (Infer [(premise, \<V>)] (?conclusion' \<cdot> \<mu>, \<V>))"
    unfolding inference_groundings_def mem_Collect_eq
  proof -
    have "Infer [premise\<^sub>G] conclusion\<^sub>G \<in> ground.G_Inf"
      unfolding ground.G_Inf_def
      using ground_eq_factoring conclusion_grounding premise_grounding 
      by blast

    then have "\<exists>\<rho>\<^sub>1 \<rho>\<^sub>2. is_inference_grounding
      (Infer [(premise, \<V>)] (?conclusion' \<cdot> \<mu>, \<V>))
      (Infer [premise\<^sub>G] conclusion\<^sub>G) \<gamma> \<rho>\<^sub>1 \<rho>\<^sub>2"
      unfolding is_inference_grounding_def Calculus.inference.case list.case prod.case
      using typing
      by (smt (verit) calculation conclusion\<^sub>G eq_factoring eq_factoring_preserves_typing premise\<^sub>G
          vars_conclusion' welltyped\<^sub>\<sigma>_on_subset)

    thus "\<exists>\<iota>\<^sub>G \<gamma> \<rho>\<^sub>1 \<rho>\<^sub>2. Infer [premise\<^sub>G] conclusion\<^sub>G = \<iota>\<^sub>G \<and>
      is_inference_grounding (Infer [(premise, \<V>)] (?conclusion' \<cdot> \<mu>, \<V>)) \<iota>\<^sub>G \<gamma> \<rho>\<^sub>1 \<rho>\<^sub>2"
      by iprover
  qed    

  ultimately show ?thesis
    using that[OF eq_factoring]
    by blast
qed



lemma if_subst_sth [clause_simp]: "(if b then Pos else Neg) atom \<cdot>l \<rho> = 
  (if b then Pos else Neg) (atom \<cdot>a \<rho>)"
  by clause_auto

lemma superposition_lifting:
  fixes 
    premise\<^sub>G\<^sub>1 premise\<^sub>G\<^sub>2 conclusion\<^sub>G :: "'f gatom clause" and 
    premise\<^sub>1 premise\<^sub>2 "conclusion" :: "('f, 'v) atom clause" and
    \<gamma> \<rho>\<^sub>1 \<rho>\<^sub>2 :: "('f, 'v) subst" and
    \<V>\<^sub>1 \<V>\<^sub>2
  defines 
    premise\<^sub>G\<^sub>1 [simp]: "premise\<^sub>G\<^sub>1 \<equiv> clause.to_ground (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>)" and
    premise\<^sub>G\<^sub>2 [simp]: "premise\<^sub>G\<^sub>2 \<equiv> clause.to_ground (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<gamma>)" and
    conclusion\<^sub>G [simp]: "conclusion\<^sub>G \<equiv> clause.to_ground (conclusion \<cdot> \<gamma>)" and
    premise_groundings [simp]: 
    "premise_groundings \<equiv> clause_groundings typeof_fun (premise\<^sub>1, \<V>\<^sub>1) \<union> 
      clause_groundings typeof_fun (premise\<^sub>2, \<V>\<^sub>2)" and
    \<iota>\<^sub>G [simp]: "\<iota>\<^sub>G \<equiv> Infer [premise\<^sub>G\<^sub>2, premise\<^sub>G\<^sub>1] conclusion\<^sub>G"
  assumes 
    renaming: 
    "term_subst.is_renaming \<rho>\<^sub>1" 
    "term_subst.is_renaming \<rho>\<^sub>2" 
    "clause.vars (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter> clause.vars (premise\<^sub>2 \<cdot> \<rho>\<^sub>2) = {}"  and
    premise\<^sub>1_grounding: "clause.is_ground (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>)" and
    premise\<^sub>2_grounding: "clause.is_ground (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<gamma>)" and
    conclusion_grounding: "clause.is_ground (conclusion \<cdot> \<gamma>)" and
    select: 
    "clause.from_ground (select\<^sub>G premise\<^sub>G\<^sub>1) = (select premise\<^sub>1) \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>"
    "clause.from_ground (select\<^sub>G premise\<^sub>G\<^sub>2) = (select premise\<^sub>2) \<cdot> \<rho>\<^sub>2 \<cdot> \<gamma>" and
    ground_superposition: "ground.ground_superposition premise\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>1 conclusion\<^sub>G" and
    non_redundant: "\<iota>\<^sub>G \<notin> ground.Red_I premise_groundings" and
    typing:
    "welltyped\<^sub>c typeof_fun \<V>\<^sub>1 premise\<^sub>1"
    "welltyped\<^sub>c typeof_fun \<V>\<^sub>2 premise\<^sub>2"
    "term_subst.is_ground_subst \<gamma>"
    "welltyped\<^sub>\<sigma>_on (clause.vars premise\<^sub>1) typeof_fun \<V>\<^sub>1 (\<rho>\<^sub>1 \<odot> \<gamma>)"
    "welltyped\<^sub>\<sigma>_on (clause.vars premise\<^sub>2) typeof_fun \<V>\<^sub>2 (\<rho>\<^sub>2 \<odot> \<gamma>)"
    "welltyped\<^sub>\<sigma>_on (clause.vars premise\<^sub>1) typeof_fun \<V>\<^sub>1 \<rho>\<^sub>1"
    "welltyped\<^sub>\<sigma>_on (clause.vars premise\<^sub>2) typeof_fun \<V>\<^sub>2 \<rho>\<^sub>2"
    "all_types \<V>\<^sub>1" "all_types \<V>\<^sub>2"
  obtains conclusion' \<V>\<^sub>3
  where
    "superposition (premise\<^sub>2, \<V>\<^sub>2) (premise\<^sub>1, \<V>\<^sub>1) (conclusion', \<V>\<^sub>3)"
    "\<iota>\<^sub>G \<in> inference_groundings (Infer [(premise\<^sub>2, \<V>\<^sub>2), (premise\<^sub>1, \<V>\<^sub>1)] (conclusion', \<V>\<^sub>3))"
    "conclusion' \<cdot> \<gamma> = conclusion \<cdot> \<gamma>"
  using ground_superposition
proof(cases premise\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>1 conclusion\<^sub>G rule: ground.ground_superposition.cases)
  case (ground_superpositionI 
      literal\<^sub>G\<^sub>1
      premise\<^sub>G\<^sub>1'
      literal\<^sub>G\<^sub>2
      premise\<^sub>G\<^sub>2'
      \<P>\<^sub>G
      context\<^sub>G
      term\<^sub>G\<^sub>1
      term\<^sub>G\<^sub>2
      term\<^sub>G\<^sub>3
      )

  have premise\<^sub>1_not_empty: "premise\<^sub>1 \<noteq> {#}"
    using ground_superpositionI(1) empty_not_add_mset clause_subst_empty premise\<^sub>G\<^sub>1
    by (metis clause_from_ground_empty_mset clause.from_ground_inverse)

  have premise\<^sub>2_not_empty: "premise\<^sub>2 \<noteq> {#}"
    using ground_superpositionI(2) empty_not_add_mset clause_subst_empty premise\<^sub>G\<^sub>2
    by (metis clause_from_ground_empty_mset clause.from_ground_inverse)

  have premise\<^sub>1_\<gamma>: "premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma> = clause.from_ground (add_mset literal\<^sub>G\<^sub>1 premise\<^sub>G\<^sub>1')"
    using ground_superpositionI(1) premise\<^sub>G\<^sub>1
    by (metis premise\<^sub>1_grounding clause.to_ground_inverse)

  have premise\<^sub>2_\<gamma>: "premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<gamma> = clause.from_ground (add_mset literal\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>2')"
    using ground_superpositionI(2) premise\<^sub>G\<^sub>2
    by (metis premise\<^sub>2_grounding clause.to_ground_inverse)

  let ?select\<^sub>G_empty = "select\<^sub>G (clause.to_ground (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>)) = {#}"
  let ?select\<^sub>G_not_empty = "select\<^sub>G (clause.to_ground (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>)) \<noteq> {#}"

  have pos_literal\<^sub>G\<^sub>1_is_strictly_maximal\<^sub>l: 
    "is_strictly_maximal\<^sub>l (literal.from_ground literal\<^sub>G\<^sub>1) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)" if "\<P>\<^sub>G = Pos"
    using ground_superpositionI(9) that
    unfolding is_strictly_maximal\<^sub>G\<^sub>l_iff_is_strictly_maximal\<^sub>l
    by(simp add: premise\<^sub>1_grounding)

  have neg_literal\<^sub>G\<^sub>1_is_maximal\<^sub>l: 
    "is_maximal\<^sub>l (literal.from_ground literal\<^sub>G\<^sub>1) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)" if ?select\<^sub>G_empty
    using 
      that
      ground_superpositionI(9)  
      is_maximal\<^sub>l_if_is_strictly_maximal\<^sub>l 
      is_maximal\<^sub>l_empty
      premise\<^sub>1_\<gamma>
    unfolding 
      is_maximal_lit_iff_is_maximal\<^sub>l 
      is_strictly_maximal\<^sub>G\<^sub>l_iff_is_strictly_maximal\<^sub>l
      ground_superpositionI(1)
    apply clause_auto
    by (metis premise\<^sub>1_\<gamma> clause_from_ground_empty_mset clause.from_ground_inverse)

  obtain pos_literal\<^sub>1 where
    "is_strictly_maximal\<^sub>l pos_literal\<^sub>1 premise\<^sub>1"
    "pos_literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma> = literal.from_ground literal\<^sub>G\<^sub>1" 
  if "\<P>\<^sub>G = Pos"
    using is_strictly_maximal\<^sub>l_ground_subst_stability[OF 
        premise\<^sub>1_grounding[folded clause.subst_comp_subst] 
        pos_literal\<^sub>G\<^sub>1_is_strictly_maximal\<^sub>l
        ]
    by blast

  moreover then have "pos_literal\<^sub>1 \<in># premise\<^sub>1" if "\<P>\<^sub>G = Pos"
    using that strictly_maximal\<^sub>l_in_clause by fastforce

  moreover obtain neg_max_literal\<^sub>1 where
    "is_maximal\<^sub>l neg_max_literal\<^sub>1 premise\<^sub>1"
    "neg_max_literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma> = literal.from_ground literal\<^sub>G\<^sub>1" 
  if "\<P>\<^sub>G = Neg" ?select\<^sub>G_empty
    using 
      is_maximal\<^sub>l_ground_subst_stability[OF 
        premise\<^sub>1_not_empty 
        premise\<^sub>1_grounding[folded clause.subst_comp_subst]
        ]
      neg_literal\<^sub>G\<^sub>1_is_maximal\<^sub>l
    by (metis (no_types, opaque_lifting) assms(9) clause.comp_subst.left.monoid_action_compatibility unique_maximal_in_ground_clause)

  moreover then have "neg_max_literal\<^sub>1 \<in># premise\<^sub>1" if "\<P>\<^sub>G = Neg" ?select\<^sub>G_empty
    using that maximal\<^sub>l_in_clause by fastforce

  moreover obtain neg_selected_literal\<^sub>1 where
    "is_maximal\<^sub>l neg_selected_literal\<^sub>1 (select premise\<^sub>1)"
    "neg_selected_literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma> = literal.from_ground literal\<^sub>G\<^sub>1" 
  if "\<P>\<^sub>G = Neg" ?select\<^sub>G_not_empty 
  proof-
    have "ground.is_maximal_lit literal\<^sub>G\<^sub>1 (select\<^sub>G premise\<^sub>G\<^sub>1)" if "\<P>\<^sub>G = Neg" ?select\<^sub>G_not_empty
      using ground_superpositionI(9) that
      by simp

    then show ?thesis
      using
        that 
        select(1) 
        unique_maximal_in_ground_clause
        is_maximal\<^sub>l_ground_subst_stability
      unfolding premise\<^sub>G\<^sub>1 is_maximal_lit_iff_is_maximal\<^sub>l
      by (metis (mono_tags, lifting) clause.comp_subst.monoid_action_compatibility 
          clause_subst_empty(2) clause.ground_is_ground image_mset_is_empty_iff 
          clause.from_ground_def)
  qed

  moreover then have "neg_selected_literal\<^sub>1 \<in># premise\<^sub>1" if "\<P>\<^sub>G = Neg" ?select\<^sub>G_not_empty 
    using that
    by (meson maximal\<^sub>l_in_clause mset_subset_eqD select_subset)

  ultimately obtain literal\<^sub>1 where
    literal\<^sub>1_\<gamma>: "literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma> = literal.from_ground literal\<^sub>G\<^sub>1" and
    literal\<^sub>1_in_premise\<^sub>1: "literal\<^sub>1 \<in># premise\<^sub>1" and
    literal\<^sub>1_is_strictly_maximal: "\<P>\<^sub>G = Pos \<Longrightarrow> is_strictly_maximal\<^sub>l literal\<^sub>1 premise\<^sub>1" and
    literal\<^sub>1_is_maximal: "\<P>\<^sub>G = Neg \<Longrightarrow> ?select\<^sub>G_empty \<Longrightarrow> is_maximal\<^sub>l literal\<^sub>1 premise\<^sub>1" and
    literal\<^sub>1_selected: "\<P>\<^sub>G = Neg \<Longrightarrow> ?select\<^sub>G_not_empty \<Longrightarrow> is_maximal\<^sub>l literal\<^sub>1 (select premise\<^sub>1)"
    by (metis ground_superpositionI(9) literals_distinct(1))

  then have literal\<^sub>1_grounding: "literal.is_ground (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma>)"
    by simp

  have literal\<^sub>G\<^sub>2_is_strictly_maximal\<^sub>l: 
    "is_strictly_maximal\<^sub>l (literal.from_ground literal\<^sub>G\<^sub>2) (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>)"
    using ground_superpositionI(11)
    unfolding is_strictly_maximal\<^sub>G\<^sub>l_iff_is_strictly_maximal\<^sub>l
    by (simp add: premise\<^sub>2_grounding)

  obtain literal\<^sub>2 where 
    literal\<^sub>2_strictly_maximal: "is_strictly_maximal\<^sub>l literal\<^sub>2 premise\<^sub>2" and
    literal\<^sub>2_\<gamma>: "literal\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<odot> \<gamma> = literal.from_ground literal\<^sub>G\<^sub>2"
    using is_strictly_maximal\<^sub>l_ground_subst_stability[OF 
        premise\<^sub>2_grounding[folded clause.subst_comp_subst] 
        literal\<^sub>G\<^sub>2_is_strictly_maximal\<^sub>l
        ].

  then have literal\<^sub>2_in_premise\<^sub>2: "literal\<^sub>2 \<in># premise\<^sub>2" 
    using strictly_maximal\<^sub>l_in_clause by blast

  have literal\<^sub>2_grounding: "literal.is_ground (literal\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<odot> \<gamma>)"
    using literal\<^sub>2_\<gamma> by simp

  obtain premise\<^sub>1' where premise\<^sub>1: "premise\<^sub>1 = add_mset literal\<^sub>1 premise\<^sub>1'"
    by (meson literal\<^sub>1_in_premise\<^sub>1 multi_member_split)

  then have premise\<^sub>1'_\<gamma>: "premise\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma> = clause.from_ground premise\<^sub>G\<^sub>1'"
    using premise\<^sub>1_\<gamma>  
    unfolding clause_from_ground_add_mset literal\<^sub>1_\<gamma>[symmetric]
    by (simp add: subst_clause_add_mset)

  obtain premise\<^sub>2' where premise\<^sub>2: "premise\<^sub>2 = add_mset literal\<^sub>2 premise\<^sub>2'"
    by (meson literal\<^sub>2_in_premise\<^sub>2 multi_member_split)

  then have premise\<^sub>2'_\<gamma>: "premise\<^sub>2' \<cdot> \<rho>\<^sub>2 \<cdot> \<gamma> = clause.from_ground premise\<^sub>G\<^sub>2'"
    using premise\<^sub>2_\<gamma>  
    unfolding clause_from_ground_add_mset literal\<^sub>2_\<gamma>[symmetric]
    by (simp add: subst_clause_add_mset)

  let ?\<P> = "if \<P>\<^sub>G = Pos then Pos else Neg"

  have [simp]: "\<P>\<^sub>G \<noteq> Pos \<longleftrightarrow> \<P>\<^sub>G = Neg"
    using ground_superpositionI(4) 
    by auto

  have "literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<gamma> = 
    ?\<P> (Upair (context.from_ground context\<^sub>G)\<langle>term.from_ground term\<^sub>G\<^sub>1\<rangle> (term.from_ground term\<^sub>G\<^sub>2))"
    using literal\<^sub>1_\<gamma>
    unfolding ground_superpositionI(5)
    by (simp add: literal_from_ground_atom_from_ground atom_from_ground_term_from_ground 
        ground_term_with_context(3))

  then obtain term\<^sub>1_with_context term\<^sub>1' where 
    literal\<^sub>1: "literal\<^sub>1 = ?\<P> (Upair term\<^sub>1_with_context term\<^sub>1')" and
    term\<^sub>1'_\<gamma>: "term\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma> = term.from_ground term\<^sub>G\<^sub>2" and
    term\<^sub>1_with_context_\<gamma>: 
      "term\<^sub>1_with_context \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma> = (context.from_ground context\<^sub>G)\<langle>term.from_ground term\<^sub>G\<^sub>1\<rangle>"
    by (smt (verit) obtain_from_literal_subst)

  from literal\<^sub>2_\<gamma> have "literal\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<gamma> = term.from_ground term\<^sub>G\<^sub>1 \<approx> term.from_ground term\<^sub>G\<^sub>3"
    unfolding ground_superpositionI(6) atom_from_ground_term_from_ground 
      literal_from_ground_atom_from_ground(2) literal.subst_comp_subst.

  then obtain term\<^sub>2 term\<^sub>2' where 
    literal\<^sub>2: "literal\<^sub>2 = term\<^sub>2 \<approx> term\<^sub>2'" and
    term\<^sub>2_\<gamma>: "term\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<gamma> = term.from_ground term\<^sub>G\<^sub>1" and     
    term\<^sub>2'_\<gamma>: "term\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<gamma> = term.from_ground term\<^sub>G\<^sub>3"
    using obtain_from_pos_literal_subst
    by metis

  let ?inference_into_var = "\<nexists>context\<^sub>1 term\<^sub>1. 
      term\<^sub>1_with_context = context\<^sub>1\<langle>term\<^sub>1\<rangle> \<and> 
      term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma> = term.from_ground term\<^sub>G\<^sub>1 \<and> 
      context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma> = context.from_ground context\<^sub>G \<and> 
      is_Fun term\<^sub>1"

  have inference_into_var_is_redundant: 
    "?inference_into_var \<Longrightarrow> ground.redundant_infer premise_groundings \<iota>\<^sub>G"
  proof-
    assume inference_into_var: ?inference_into_var

    obtain term\<^sub>x context\<^sub>x context\<^sub>x' where
      term\<^sub>1_with_context: "term\<^sub>1_with_context = context\<^sub>x\<langle>term\<^sub>x\<rangle>" and
      is_Var_term\<^sub>x: "is_Var term\<^sub>x" and
      "context.from_ground context\<^sub>G = (context\<^sub>x \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma>) \<circ>\<^sub>c context\<^sub>x'"
    proof-  
      from inference_into_var term\<^sub>1_with_context_\<gamma>
      have 
        "\<exists>term\<^sub>x context\<^sub>x context\<^sub>x'. 
        term\<^sub>1_with_context = context\<^sub>x\<langle>term\<^sub>x\<rangle> \<and> 
        is_Var term\<^sub>x \<and> 
        context.from_ground context\<^sub>G = (context\<^sub>x \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma>) \<circ>\<^sub>c context\<^sub>x'"
      proof(induction term\<^sub>1_with_context arbitrary: context\<^sub>G)
        case (Var x)
        show ?case
        proof(intro exI conjI)
          show
            "Var x = \<box>\<langle>Var x\<rangle>"
            "is_Var (Var x)"
            "context.from_ground context\<^sub>G = (\<box> \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma>) \<circ>\<^sub>c context.from_ground context\<^sub>G"
            by simp_all
        qed
      next
        case (Fun f terms)

        then have "context\<^sub>G \<noteq> GHole"
          by (metis Fun.prems(2) ctxt_apply_term.simps(1) ctxt_of_gctxt.simps(1) 
              subst_apply_ctxt.simps(1) term.discI(2))

        then obtain terms\<^sub>G\<^sub>1 context\<^sub>G' terms\<^sub>G\<^sub>2 where
          context\<^sub>G: "context\<^sub>G = GMore f terms\<^sub>G\<^sub>1 context\<^sub>G' terms\<^sub>G\<^sub>2"
          using Fun(3)
          by(cases context\<^sub>G) auto

        have terms_\<gamma>: 
          "map (\<lambda>term. term \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>) terms = 
            map term.from_ground terms\<^sub>G\<^sub>1 @ (context.from_ground context\<^sub>G')\<langle>term.from_ground term\<^sub>G\<^sub>1\<rangle> #
             map term.from_ground terms\<^sub>G\<^sub>2"
          using Fun(3)
          unfolding context\<^sub>G
          by(simp add: comp_def)

        then obtain terms\<^sub>1 "term" terms\<^sub>2 where 
          terms: "terms = terms\<^sub>1 @ term # terms\<^sub>2" and
          terms\<^sub>1_\<gamma>: "map (\<lambda>term. term \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>) terms\<^sub>1 = map term.from_ground terms\<^sub>G\<^sub>1" and
          terms\<^sub>2_\<gamma>: "map (\<lambda>term. term \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>) terms\<^sub>2 = map term.from_ground terms\<^sub>G\<^sub>2"     
          by (smt (z3) append_eq_map_conv map_eq_Cons_D)

        with terms_\<gamma> 
        have term_\<gamma>: "term \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma> = (context.from_ground context\<^sub>G')\<langle>term.from_ground term\<^sub>G\<^sub>1\<rangle>"
          by simp

        show ?case
        proof(cases "term.is_ground term")
          case True

          with term_\<gamma> 
          obtain term\<^sub>1 context\<^sub>1 where
            "term = context\<^sub>1\<langle>term\<^sub>1\<rangle>"
            "term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma> = term.from_ground term\<^sub>G\<^sub>1" 
            "context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma> = context.from_ground context\<^sub>G'" 
            "is_Fun term\<^sub>1"
            by (metis Term.ground_vars_term_empty context.ground_is_ground ground_subst_apply 
                term.ground_is_ground context.subst_ident_if_ground gterm_is_fun)

          moreover then have "Fun f terms = (More f terms\<^sub>1 context\<^sub>1 terms\<^sub>2)\<langle>term\<^sub>1\<rangle>"
            unfolding terms
            by auto

          ultimately have 
            "\<exists>context\<^sub>1 term\<^sub>1. 
            Fun f terms = context\<^sub>1\<langle>term\<^sub>1\<rangle> \<and> 
            term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma> = term.from_ground term\<^sub>G\<^sub>1 \<and> 
            context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma> = context.from_ground context\<^sub>G \<and> 
            is_Fun term\<^sub>1"
            by (auto
                intro: exI[of _ "More f terms\<^sub>1 context\<^sub>1 terms\<^sub>2"] exI[of _ term\<^sub>1] 
                simp: comp_def terms\<^sub>1_\<gamma> terms\<^sub>2_\<gamma> context\<^sub>G)

          then show ?thesis
            using Fun(2)
            by argo
        next
          case False
          moreover have "term \<in> set terms"
            using terms by auto

          moreover have 
            "\<nexists>context\<^sub>1 term\<^sub>1. term = context\<^sub>1\<langle>term\<^sub>1\<rangle> \<and> 
            term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma> = term.from_ground term\<^sub>G\<^sub>1 \<and> 
            context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma> = context.from_ground context\<^sub>G' \<and> 
            is_Fun term\<^sub>1"
          proof(rule notI)
            assume 
              "\<exists>context\<^sub>1 term\<^sub>1. 
              term = context\<^sub>1\<langle>term\<^sub>1\<rangle> \<and> 
              term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma> = term.from_ground term\<^sub>G\<^sub>1 \<and> 
              context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma> = context.from_ground context\<^sub>G' \<and> 
              is_Fun term\<^sub>1"

            then obtain context\<^sub>1 term\<^sub>1 where
              "term": "term = context\<^sub>1\<langle>term\<^sub>1\<rangle>"
              "term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma> = term.from_ground term\<^sub>G\<^sub>1"
              "context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma> = context.from_ground context\<^sub>G'"
              "is_Fun term\<^sub>1"
              by blast

            then have 
              "\<exists>context\<^sub>1 term\<^sub>1. 
              Fun f terms = context\<^sub>1\<langle>term\<^sub>1\<rangle> \<and> 
              term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma> = term.from_ground term\<^sub>G\<^sub>1 \<and> 
              context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma> = context.from_ground context\<^sub>G \<and> 
              is_Fun term\<^sub>1"
              by(auto 
                  intro: exI[of _ "(More f terms\<^sub>1 context\<^sub>1 terms\<^sub>2)"] exI[of _ term\<^sub>1] 
                  simp: "term" terms terms\<^sub>1_\<gamma> terms\<^sub>2_\<gamma> context\<^sub>G comp_def)

            then show False
              using Fun(2)
              by argo
          qed

          ultimately obtain term\<^sub>x context\<^sub>x context\<^sub>x' where
            "term = context\<^sub>x\<langle>term\<^sub>x\<rangle>"  
            "is_Var term\<^sub>x" 
            "context.from_ground context\<^sub>G' = (context\<^sub>x \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma>) \<circ>\<^sub>c context\<^sub>x'"
            using Fun(1) term_\<gamma> by blast

          then have 
            "Fun f terms = (More f terms\<^sub>1 context\<^sub>x terms\<^sub>2)\<langle>term\<^sub>x\<rangle>"
            "is_Var term\<^sub>x" 
            "context.from_ground context\<^sub>G = (More f terms\<^sub>1 context\<^sub>x terms\<^sub>2 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma>) \<circ>\<^sub>c context\<^sub>x'"
            by(auto simp: terms terms\<^sub>1_\<gamma> terms\<^sub>2_\<gamma> context\<^sub>G comp_def)

          then show ?thesis
            by blast
        qed
      qed

      then show ?thesis
        using that
        by blast
    qed

    then have context\<^sub>G: "context.from_ground context\<^sub>G = context\<^sub>x \<circ>\<^sub>c context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma>"
      using ground_context_subst[OF context.ground_is_ground] ctxt_compose_subst_compose_distrib
      by metis

    obtain \<tau>\<^sub>x where \<tau>\<^sub>x: "welltyped typeof_fun \<V>\<^sub>1 term\<^sub>x \<tau>\<^sub>x"
      using term\<^sub>1_with_context typing(1)
      unfolding premise\<^sub>1 welltyped\<^sub>c_def literal\<^sub>1 welltyped\<^sub>l_def welltyped\<^sub>a_def
      by (metis welltyped.simps is_Var_term\<^sub>x term.collapse(1))
 
    have \<iota>\<^sub>G_parts: 
      "set (side_prems_of \<iota>\<^sub>G) = {premise\<^sub>G\<^sub>2}" 
      "main_prem_of \<iota>\<^sub>G = premise\<^sub>G\<^sub>1"
      "concl_of \<iota>\<^sub>G = conclusion\<^sub>G"
      unfolding \<iota>\<^sub>G
      by simp_all

    from is_Var_term\<^sub>x 
    obtain var\<^sub>x where var\<^sub>x: "Var var\<^sub>x = term\<^sub>x \<cdot>t \<rho>\<^sub>1"
      using renaming(1)
      unfolding is_Var_def term_subst.is_renaming_def subst_compose_def
      by (metis eval_term.simps(1) subst_apply_eq_Var)

    have \<tau>\<^sub>x_var\<^sub>x: "welltyped typeof_fun \<V>\<^sub>1 (Var var\<^sub>x) \<tau>\<^sub>x"
      using \<tau>\<^sub>x typing(6)
      unfolding welltyped\<^sub>\<sigma>_on_def var\<^sub>x premise\<^sub>1 literal\<^sub>1 term\<^sub>1_with_context 
      by(clause_auto simp: welltyped\<^sub>\<sigma>_on_def welltyped\<^sub>\<sigma>_on_welltyped)

    show ?thesis
    proof(unfold ground.redundant_infer_def \<iota>\<^sub>G_parts, intro exI conjI)

      let ?update = "(context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma>)\<langle>term.from_ground term\<^sub>G\<^sub>3\<rangle>"

      define \<gamma>' where
        \<gamma>': "\<gamma>' \<equiv> \<gamma>(var\<^sub>x := ?update)"

      have update_grounding: "term.is_ground ?update"
      proof-
        have "context.is_ground ((context\<^sub>x \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma>) \<circ>\<^sub>c (context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma>))"
          using context.ground_is_ground[of context\<^sub>G] context\<^sub>G
          by fastforce

        then show ?thesis
          using context_is_ground_context_compose1(2)
          by auto
      qed
      let ?context\<^sub>x'_\<gamma> = "context.to_ground (context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma>)"

      note term_from_ground_context =
        ground_term_with_context1[OF _ term.ground_is_ground, unfolded term.from_ground_inverse]

      have term\<^sub>x_\<gamma>: "term.to_ground (term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>) = ?context\<^sub>x'_\<gamma>\<langle>term\<^sub>G\<^sub>1\<rangle>\<^sub>G"
        using term\<^sub>1_with_context_\<gamma> update_grounding 
        unfolding term\<^sub>1_with_context context\<^sub>G
        by(auto simp: term_from_ground_context)

      have term\<^sub>x_\<gamma>': "term.to_ground (term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>') = ?context\<^sub>x'_\<gamma>\<langle>term\<^sub>G\<^sub>3\<rangle>\<^sub>G"
        using update_grounding
        unfolding var\<^sub>x[symmetric] \<gamma>'
        by(auto simp: term_from_ground_context)

      have aux: "term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma> = (context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma>)\<langle>term.from_ground term\<^sub>G\<^sub>1\<rangle>"
        using term\<^sub>x_\<gamma>
        by (metis ground_term_with_context2 term_subst.is_ground_subst_is_ground 
            term_with_context_is_ground term.to_ground_inverse typing(3) update_grounding)

      have "welltyped\<^sub>c typeof_fun \<V>\<^sub>2 (clause.from_ground premise\<^sub>G\<^sub>2)"
        by (metis ground_superpositionI(2) premise\<^sub>2_\<gamma> 
            clause.comp_subst.left.monoid_action_compatibility typing(2) typing(5) 
            welltyped\<^sub>\<sigma>_on_welltyped\<^sub>c)

      then have "\<exists>\<tau>. welltyped typeof_fun \<V>\<^sub>2 (term.from_ground term\<^sub>G\<^sub>1) \<tau> \<and> 
          welltyped typeof_fun \<V>\<^sub>2 (term.from_ground term\<^sub>G\<^sub>3) \<tau>"
        unfolding ground_superpositionI 
        by clause_simp

      then have aux': "\<exists>\<tau>. welltyped typeof_fun \<V>\<^sub>1 (term.from_ground term\<^sub>G\<^sub>1) \<tau> \<and> 
          welltyped typeof_fun \<V>\<^sub>1 (term.from_ground term\<^sub>G\<^sub>3) \<tau>"
        by (meson term.ground_is_ground welltyped_is_ground)

      have "welltyped typeof_fun \<V>\<^sub>1 (term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>) \<tau>\<^sub>x"
      proof-

        have "
          \<lbrakk>\<forall>x\<in>context.vars context\<^sub>x \<union> term.vars term\<^sub>x \<union> term.vars term\<^sub>1' \<union> clause.vars premise\<^sub>1'.
            First_Order_Type_System.welltyped typeof_fun \<V>\<^sub>1 ((\<rho>\<^sub>1 \<odot> \<gamma>) x) (\<V>\<^sub>1 x);
            First_Order_Type_System.welltyped typeof_fun \<V>\<^sub>1 term\<^sub>x \<tau>\<^sub>x\<rbrakk>
            \<Longrightarrow> First_Order_Type_System.welltyped typeof_fun \<V>\<^sub>1 (term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>) \<tau>\<^sub>x"
          by (metis UnI2 sup.commute term_subst.subst_comp_subst welltyped\<^sub>\<sigma>_on_def welltyped\<^sub>\<sigma>_on_term)
        
        then show ?thesis
          using typing(4) \<tau>\<^sub>x
          unfolding welltyped\<^sub>\<sigma>_on_def var\<^sub>x premise\<^sub>1 literal\<^sub>1 term\<^sub>1_with_context 
          by clause_simp
      qed

      then have \<tau>\<^sub>x_update: "welltyped typeof_fun \<V>\<^sub>1 ?update \<tau>\<^sub>x"
        unfolding aux
        using aux'
        by (meson welltyped\<^sub>\<kappa>)

      let ?premise\<^sub>1_\<gamma>' = "clause.to_ground (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>')"
      have premise\<^sub>1_\<gamma>'_grounding: "clause.is_ground (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>')"
        using clause.ground_subst_upd[OF update_grounding premise\<^sub>1_grounding] 
        unfolding \<gamma>'
        by blast

      have \<gamma>'_ground: "term_subst.is_ground_subst (\<rho>\<^sub>1 \<odot> \<gamma>')"
        by (metis \<gamma>' term.ground_subst_upd term_subst.comp_subst.left.monoid_action_compatibility 
            term_subst.is_ground_subst_def typing(3) update_grounding)

      have \<gamma>'_wt: "welltyped\<^sub>\<sigma>_on (clause.vars premise\<^sub>1) typeof_fun \<V>\<^sub>1 (\<rho>\<^sub>1 \<odot> \<gamma>')"
        using welltyped\<^sub>\<sigma>_on_subst_upd[OF \<tau>\<^sub>x_var\<^sub>x \<tau>\<^sub>x_update typing(4)]
        unfolding \<gamma>' welltyped\<^sub>\<sigma>_on_def subst_compose
        using First_Order_Type_System.welltyped.simps \<tau>\<^sub>x \<tau>\<^sub>x_update eval_term.simps(1) 
          eval_with_fresh_var fun_upd_same is_Var_term\<^sub>x renaming(1) subst_compose_def 
          term.collapse(1) term.distinct(1) term.set_cases(2) term_subst_is_renaming_iff 
          the_inv_f_f typing(4) var\<^sub>x welltyped\<^sub>\<sigma>_on_def
        by (smt (verit, del_insts))
      
      show "{?premise\<^sub>1_\<gamma>'} \<subseteq> premise_groundings"
        using premise\<^sub>1_\<gamma>'_grounding typing \<gamma>'_wt \<gamma>'_ground
        unfolding clause.subst_comp_subst[symmetric] premise\<^sub>1 premise_groundings 
          clause_groundings_def
        by auto

      show "finite {?premise\<^sub>1_\<gamma>'}"
        by simp

      show "ground.G_entails ({?premise\<^sub>1_\<gamma>'} \<union> {premise\<^sub>G\<^sub>2}) {conclusion\<^sub>G}"
      proof(unfold ground.G_entails_def, intro allI impI)
        fix I :: "'f gterm rel"
        let ?I = "upair ` I"

        assume 
          refl: "refl I" and 
          trans: "trans I" and 
          sym: "sym I" and
          compatible_with_gctxt: "compatible_with_gctxt I" and
          premise: "?I \<TTurnstile>s {?premise\<^sub>1_\<gamma>'} \<union> {premise\<^sub>G\<^sub>2}"

        have var\<^sub>x_\<gamma>_ground: "term.is_ground (Var var\<^sub>x \<cdot>t \<gamma>)"
          using term\<^sub>1_with_context_\<gamma>
          unfolding term\<^sub>1_with_context var\<^sub>x
          by(clause_simp simp: term_subst.is_ground_subst_is_ground typing(3))    

        show "?I \<TTurnstile>s { conclusion\<^sub>G }"
        proof(cases "?I \<TTurnstile> premise\<^sub>G\<^sub>2'")
          case True
          then show ?thesis 
            unfolding ground_superpositionI(12)
            by auto
        next
          case False
          then have literal\<^sub>G\<^sub>2: "?I \<TTurnstile>l literal\<^sub>G\<^sub>2"
            using premise 
            unfolding ground_superpositionI(2)
            by blast

          then have "?I \<TTurnstile>l ?context\<^sub>x'_\<gamma>\<langle>term\<^sub>G\<^sub>1\<rangle>\<^sub>G \<approx> ?context\<^sub>x'_\<gamma>\<langle>term\<^sub>G\<^sub>3\<rangle>\<^sub>G"
            unfolding ground_superpositionI(6)
            using compatible_with_gctxt compatible_with_gctxt_def sym 
            by auto

          then have "?I \<TTurnstile>l term.to_ground (term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>) \<approx> term.to_ground (term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>')"
            using term\<^sub>x_\<gamma> term\<^sub>x_\<gamma>'
            by argo

          moreover then have "?I \<TTurnstile> ?premise\<^sub>1_\<gamma>'"
            using premise by fastforce

          ultimately have "?I \<TTurnstile> premise\<^sub>G\<^sub>1"
            using
              interpretation_clause_congruence[OF 
                trans sym compatible_with_gctxt update_grounding var\<^sub>x_\<gamma>_ground premise\<^sub>1_grounding
                ]
              var\<^sub>x
            unfolding \<gamma>'
            by simp

          then have "?I \<TTurnstile> add_mset (\<P>\<^sub>G (Upair context\<^sub>G\<langle>term\<^sub>G\<^sub>1\<rangle>\<^sub>G term\<^sub>G\<^sub>2)) premise\<^sub>G\<^sub>1'"
            using ground_superpositionI(1) ground_superpositionI(5) by auto

          then have "?I \<TTurnstile> add_mset (\<P>\<^sub>G (Upair context\<^sub>G\<langle>term\<^sub>G\<^sub>3\<rangle>\<^sub>G term\<^sub>G\<^sub>2)) premise\<^sub>G\<^sub>1'"
            using 
              literal\<^sub>G\<^sub>2
              interpretation_context_congruence[OF trans sym compatible_with_gctxt]
              interpretation_context_congruence'[OF trans sym compatible_with_gctxt]
              ground_superpositionI(4)
            unfolding ground_superpositionI(6)
            by(cases "\<P>\<^sub>G = Pos")(auto simp: sym)

          then show ?thesis 
            unfolding ground_superpositionI(12)
            by blast
        qed
      qed

      show "\<forall>clause\<^sub>G \<in> {?premise\<^sub>1_\<gamma>'}. clause\<^sub>G \<prec>\<^sub>c\<^sub>G premise\<^sub>G\<^sub>1"
      proof-
        have var\<^sub>x_\<gamma>: "\<gamma> var\<^sub>x = term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>"
          using var\<^sub>x
          by simp

        have context\<^sub>x_grounding: "context.is_ground (context\<^sub>x \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma>)"
          using context\<^sub>G
          unfolding subst_compose_ctxt_compose_distrib
          by (metis context.ground_is_ground context_is_ground_context_compose1(1))

        have term\<^sub>x_grounding: "term.is_ground (term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>)"
          using term\<^sub>1_with_context_\<gamma>
          unfolding term\<^sub>1_with_context
          by(clause_simp simp: term_subst.is_ground_subst_is_ground typing(3))

        have 
          "(context\<^sub>x \<circ>\<^sub>c context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma>)\<langle>term.from_ground term\<^sub>G\<^sub>3\<rangle> \<prec>\<^sub>t context\<^sub>x\<langle>term\<^sub>x\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>"
          using ground_superpositionI(8)
          unfolding 
            less\<^sub>t\<^sub>G_def 
            context\<^sub>G[symmetric] 
            term\<^sub>1_with_context[symmetric] 
            term\<^sub>1_with_context_\<gamma>
            less\<^sub>t_ground_context_compatible_iff[OF 
              context.ground_is_ground term.ground_is_ground term.ground_is_ground].

        then have update_smaller: "?update \<prec>\<^sub>t \<gamma> var\<^sub>x"
          unfolding 
            var\<^sub>x_\<gamma>
            subst_apply_term_ctxt_apply_distrib 
            subst_compose_ctxt_compose_distrib
            Subterm_and_Context.ctxt_ctxt_compose
          by(rule less\<^sub>t_ground_context_compatible'[OF 
                context\<^sub>x_grounding update_grounding term\<^sub>x_grounding])     

        have var\<^sub>x_in_literal\<^sub>1: "var\<^sub>x \<in> literal.vars (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1)"
          unfolding literal\<^sub>1 term\<^sub>1_with_context literal.vars_def atom.vars_def 
          using var\<^sub>x
          by(auto simp: subst_literal subst_atom)

        have literal\<^sub>1_smaller: "literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<gamma>' \<prec>\<^sub>l literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<gamma>"
          unfolding \<gamma>'
          using less\<^sub>l_subst_upd[OF 
              update_grounding 
              update_smaller 
              literal\<^sub>1_grounding[unfolded literal.subst_comp_subst] 
              var\<^sub>x_in_literal\<^sub>1
              ].

        have premise\<^sub>1'_grounding: "clause.is_ground (premise\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>)"
          using premise\<^sub>1'_\<gamma>
          by simp

        have premise\<^sub>1'_smaller: "premise\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>' \<preceq>\<^sub>c premise\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>"
          unfolding \<gamma>'
          using less\<^sub>c_subst_upd[of _ \<gamma>, OF update_grounding update_smaller premise\<^sub>1'_grounding]
          by(cases "var\<^sub>x \<in> clause.vars (premise\<^sub>1' \<cdot> \<rho>\<^sub>1)") simp_all

        have "?premise\<^sub>1_\<gamma>' \<prec>\<^sub>c\<^sub>G premise\<^sub>G\<^sub>1"
          using less\<^sub>c_add_mset[OF literal\<^sub>1_smaller premise\<^sub>1'_smaller]
          unfolding 
            less\<^sub>c\<^sub>G_less\<^sub>c 
            premise\<^sub>G\<^sub>1
            subst_clause_add_mset[symmetric]
            clause.to_ground_inverse[OF premise\<^sub>1_\<gamma>'_grounding]
            clause.to_ground_inverse[OF premise\<^sub>1_grounding]
          unfolding premise\<^sub>1.

        then show ?thesis
          by blast
      qed   
    qed
  qed

  obtain context\<^sub>1 term\<^sub>1 where 
    term\<^sub>1_with_context: "term\<^sub>1_with_context = context\<^sub>1\<langle>term\<^sub>1\<rangle>" and
    term\<^sub>1_\<gamma>: "term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma> = term.from_ground term\<^sub>G\<^sub>1" and
    context\<^sub>1_\<gamma>: "context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma> = context.from_ground context\<^sub>G" and
    term\<^sub>1_not_Var: "\<not> is_Var term\<^sub>1"
    using non_redundant ground_superposition inference_into_var_is_redundant 
    unfolding
      ground.Red_I_def 
      ground.G_Inf_def 
      premise_groundings 
      \<iota>\<^sub>G 
      conclusion\<^sub>G 
      ground_superpositionI(1, 2) 
      premise_groundings 
    by blast

  obtain term\<^sub>2'_with_context where 
    term\<^sub>2'_with_context_\<gamma>: 
      "term\<^sub>2'_with_context \<cdot>t \<gamma> = (context.from_ground context\<^sub>G)\<langle>term.from_ground term\<^sub>G\<^sub>3\<rangle>" and
    term\<^sub>2'_with_context: "term\<^sub>2'_with_context = (context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>term\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle>" 
    unfolding term\<^sub>2'_\<gamma>[symmetric] context\<^sub>1_\<gamma>[symmetric]
    by force

  define \<V>\<^sub>3 where 
    "\<And>x. \<V>\<^sub>3 x \<equiv>
        if x \<in> clause.vars (premise\<^sub>1 \<cdot> \<rho>\<^sub>1)
        then \<V>\<^sub>1 (the_inv \<rho>\<^sub>1 (Var x))
        else \<V>\<^sub>2 (the_inv \<rho>\<^sub>2 (Var x))"

  have wt_\<gamma>: 
    "welltyped\<^sub>\<sigma>_on (clause.vars (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) \<union> clause.vars (premise\<^sub>2 \<cdot> \<rho>\<^sub>2)) typeof_fun \<V>\<^sub>3 \<gamma>"
  proof(unfold welltyped\<^sub>\<sigma>_on_def, intro ballI)
    fix x
    assume x_in_vars: "x \<in> clause.vars (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) \<union> clause.vars (premise\<^sub>2 \<cdot> \<rho>\<^sub>2)"

    obtain f ts where \<gamma>_x: "\<gamma> x = Fun f ts"
      using obtain_ground_fun term_subst.is_ground_subst_is_ground[OF typing(3)]
      by (metis eval_term.simps(1))

    have "welltyped typeof_fun \<V>\<^sub>3 (\<gamma> x) (\<V>\<^sub>3 x)"
    proof(cases "x \<in> clause.vars (premise\<^sub>1 \<cdot> \<rho>\<^sub>1)")
      case True
      then have "Var x \<in> \<rho>\<^sub>1 ` clause.vars premise\<^sub>1"
        by (metis image_eqI renaming(1) renaming_vars_clause)

      then have y_in_vars: "the_inv \<rho>\<^sub>1 (Var x) \<in> clause.vars premise\<^sub>1"
        by (metis (no_types, lifting) image_iff renaming(1) term_subst_is_renaming_iff the_inv_f_f)

      define y where "y \<equiv> the_inv \<rho>\<^sub>1 (Var x)"

      have "term.is_ground (Var y \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>)"
        using term_subst.is_ground_subst_is_ground typing(3) by blast

      moreover have "welltyped typeof_fun \<V>\<^sub>1 (Var y \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>) (\<V>\<^sub>1 y)"
        using typing(4) y_in_vars
        unfolding welltyped\<^sub>\<sigma>_on_def y_def
        by (simp add: subst_compose)

      ultimately have "welltyped typeof_fun \<V>\<^sub>3 (Var y \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>) (\<V>\<^sub>1 y)"
        by (meson welltyped_is_ground)     

      moreover have "\<rho>\<^sub>1 (the_inv \<rho>\<^sub>1 (Var x)) = Var x"
        by (metis \<open>Var x \<in> \<rho>\<^sub>1 ` clause.vars premise\<^sub>1\<close> image_iff renaming(1) term_subst_is_renaming_iff the_inv_f_f)

      ultimately show ?thesis
        using True
        unfolding \<V>\<^sub>3_def y_def
        by simp
    next
      case False
      then have "Var x \<in> \<rho>\<^sub>2 ` clause.vars premise\<^sub>2"
        using x_in_vars
        by (metis Un_iff image_eqI renaming(2) renaming_vars_clause)

      then have y_in_vars: "the_inv \<rho>\<^sub>2 (Var x) \<in> clause.vars premise\<^sub>2"
        by (metis (no_types, lifting) image_iff renaming(2) term_subst_is_renaming_iff the_inv_f_f)

      define y where "y \<equiv> the_inv \<rho>\<^sub>2 (Var x)"

      have "term.is_ground (Var y \<cdot>t \<rho>\<^sub>2 \<cdot>t \<gamma>)"
        using term_subst.is_ground_subst_is_ground typing(3) by blast

      moreover have "welltyped typeof_fun \<V>\<^sub>2 (Var y \<cdot>t \<rho>\<^sub>2 \<cdot>t \<gamma>) (\<V>\<^sub>2 y)"
        using typing(5) y_in_vars
        unfolding welltyped\<^sub>\<sigma>_on_def y_def
        by (simp add: subst_compose)

      ultimately have "welltyped typeof_fun \<V>\<^sub>3 (Var y \<cdot>t \<rho>\<^sub>2 \<cdot>t \<gamma>) (\<V>\<^sub>2 y)"
        by (meson welltyped_is_ground)     

      moreover have "\<rho>\<^sub>2 (the_inv \<rho>\<^sub>2 (Var x)) = Var x"
        by (metis \<open>Var x \<in> \<rho>\<^sub>2 ` clause.vars premise\<^sub>2\<close> image_iff renaming(2) 
            term_subst_is_renaming_iff the_inv_f_f)

      ultimately show ?thesis
        using False
        unfolding \<V>\<^sub>3_def y_def
        by simp
    qed

    then show "welltyped typeof_fun \<V>\<^sub>3 (\<gamma> x) (\<V>\<^sub>3 x)"
      unfolding \<gamma>_x.
  qed

  have "term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma> = term\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<gamma>"
    unfolding term\<^sub>1_\<gamma> term\<^sub>2_\<gamma> ..

  moreover have 
    "\<exists>\<tau>. welltyped typeof_fun \<V>\<^sub>3 (term\<^sub>1 \<cdot>t \<rho>\<^sub>1) \<tau> \<and> welltyped typeof_fun \<V>\<^sub>3 (term\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<tau>"
  proof-
    have "welltyped\<^sub>c typeof_fun \<V>\<^sub>2 (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<gamma>)"
      using typing
      by (metis clause.subst_comp_subst welltyped\<^sub>\<sigma>_on_welltyped\<^sub>c)

    then obtain \<tau> where 
      "welltyped typeof_fun \<V>\<^sub>2 (term.from_ground term\<^sub>G\<^sub>1) \<tau>" 
      unfolding premise\<^sub>2_\<gamma> ground_superpositionI 
      by clause_simp

    then have 
      "welltyped typeof_fun \<V>\<^sub>3 (term.from_ground term\<^sub>G\<^sub>1) \<tau>" 
      using welltyped_is_ground
      by (metis term.ground_is_ground)+

    then have 
      "welltyped typeof_fun \<V>\<^sub>3 (term.from_ground term\<^sub>G\<^sub>1) \<tau>"
      by auto

    then have 
        "welltyped typeof_fun \<V>\<^sub>3 (term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>) \<tau>" "welltyped typeof_fun \<V>\<^sub>3 (term\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<gamma>) \<tau>"
      using term\<^sub>1_\<gamma> term\<^sub>2_\<gamma>
      by presburger+

    moreover have 
      "term.vars (term\<^sub>1 \<cdot>t \<rho>\<^sub>1) \<subseteq> clause.vars (premise\<^sub>1 \<cdot> \<rho>\<^sub>1)"
      "term.vars (term\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<subseteq> clause.vars (premise\<^sub>2 \<cdot> \<rho>\<^sub>2)"
      unfolding premise\<^sub>1 literal\<^sub>1 subst_clause_add_mset term\<^sub>1_with_context premise\<^sub>2 literal\<^sub>2
      by clause_simp

    ultimately have 
        "welltyped typeof_fun \<V>\<^sub>3 (term\<^sub>1 \<cdot>t \<rho>\<^sub>1) \<tau>" "welltyped typeof_fun \<V>\<^sub>3 (term\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<tau>"
      using wt_\<gamma>
      unfolding welltyped\<^sub>\<sigma>_on_def 
      by (meson sup_ge1 sup_ge2 welltyped\<^sub>\<sigma>_on_subset welltyped\<^sub>\<sigma>_on_term wt_\<gamma>)+

    then show ?thesis
      by blast
  qed

  ultimately obtain \<mu> \<sigma> where \<mu>: 
    "term_subst.is_imgu \<mu> {{term\<^sub>1 \<cdot>t \<rho>\<^sub>1, term\<^sub>2 \<cdot>t \<rho>\<^sub>2}}" 
    "\<gamma> = \<mu> \<odot> \<sigma>" 
    "welltyped_imgu' typeof_fun \<V>\<^sub>3 (term\<^sub>1 \<cdot>t \<rho>\<^sub>1) (term\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<mu>"
    using welltyped_imgu'_exists
    by (smt (verit, del_insts))

  define conclusion' where 
    conclusion': "conclusion' \<equiv>
      add_mset (?\<P> (Upair term\<^sub>2'_with_context (term\<^sub>1' \<cdot>t \<rho>\<^sub>1))) (premise\<^sub>1' \<cdot> \<rho>\<^sub>1 + premise\<^sub>2' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu>"

  show ?thesis
  proof(rule that)
    show "superposition (premise\<^sub>2, \<V>\<^sub>2) (premise\<^sub>1, \<V>\<^sub>1) (conclusion', \<V>\<^sub>3)"
    proof(rule superpositionI)
      show "term_subst.is_renaming \<rho>\<^sub>1"
        using renaming(1).
    next
      show "term_subst.is_renaming \<rho>\<^sub>2"
        using renaming(2).
    next 
      show "premise\<^sub>1 = add_mset literal\<^sub>1 premise\<^sub>1'"
        using premise\<^sub>1.
    next
      show "premise\<^sub>2 = add_mset literal\<^sub>2 premise\<^sub>2'"
        using premise\<^sub>2.
    next
      show "?\<P> \<in> {Pos, Neg}"
        by simp
    next
      show "literal\<^sub>1 = ?\<P> (Upair context\<^sub>1\<langle>term\<^sub>1\<rangle> term\<^sub>1')"
        unfolding literal\<^sub>1 term\<^sub>1_with_context..
    next
      show "literal\<^sub>2 = term\<^sub>2 \<approx> term\<^sub>2'"
        using literal\<^sub>2.
    next
      show "is_Fun term\<^sub>1"
        using term\<^sub>1_not_Var.
    next
      show "term_subst.is_imgu \<mu> {{term\<^sub>1 \<cdot>t \<rho>\<^sub>1, term\<^sub>2 \<cdot>t \<rho>\<^sub>2}}"
        using \<mu>(1).
    next
      note premises_clause_to_ground_inverse = assms(9, 10)[THEN clause.to_ground_inverse]  
      note premise_groundings = assms(10, 9)[unfolded \<mu>(2) clause.subst_comp_subst]

      have "premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu> \<cdot> \<sigma> \<prec>\<^sub>c premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<cdot> \<sigma>"
        using ground_superpositionI(3)
        unfolding premise\<^sub>G\<^sub>1 premise\<^sub>G\<^sub>2 less\<^sub>c\<^sub>G_less\<^sub>c premises_clause_to_ground_inverse 
        unfolding \<mu>(2) clause.subst_comp_subst
        by blast

      then show "\<not> premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<preceq>\<^sub>c premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>"
        using less\<^sub>c_less_eq\<^sub>c_ground_subst_stability[OF premise_groundings]
        by blast
    next
      show "?\<P> = Pos 
              \<and> select premise\<^sub>1 = {#} 
              \<and> is_strictly_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>) 
          \<or> ?\<P> = Neg 
              \<and> (select premise\<^sub>1 = {#} \<and> is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>) 
                 \<or> is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) ((select premise\<^sub>1) \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>))"
      proof(cases "?\<P> = Pos")
        case True
        moreover then have select_empty: "select premise\<^sub>1 = {#}"
          using clause_subst_empty select(1) ground_superpositionI(9) 
          by clause_auto

        moreover have "is_strictly_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu> \<cdot>l \<sigma>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<cdot> \<sigma>)"
          using True pos_literal\<^sub>G\<^sub>1_is_strictly_maximal\<^sub>l
          unfolding literal\<^sub>1_\<gamma>[symmetric] \<mu>(2)
          by force

        moreover then have "is_strictly_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>)"
          using 
            is_strictly_maximal\<^sub>l_ground_subst_stability'[OF
              _
              premise\<^sub>1_grounding[unfolded \<mu>(2) clause.subst_comp_subst]
              ]
            clause.subst_in_to_set_subst
            literal\<^sub>1_in_premise\<^sub>1
          by blast

        ultimately show ?thesis
          by auto
      next
        case \<P>_not_Pos: False
        then have \<P>\<^sub>G_Neg: "\<P>\<^sub>G = Neg"
          using ground_superpositionI(4)
          by fastforce

        show ?thesis
        proof(cases ?select\<^sub>G_empty)
          case select\<^sub>G_empty: True

          then have "select premise\<^sub>1 = {#}"
            using clause_subst_empty select(1) ground_superpositionI(9) \<P>\<^sub>G_Neg
            by clause_auto

          moreover have "is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu> \<cdot>l \<sigma>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<cdot> \<sigma>)"
            using neg_literal\<^sub>G\<^sub>1_is_maximal\<^sub>l[OF select\<^sub>G_empty]
            unfolding literal\<^sub>1_\<gamma>[symmetric] \<mu>(2)
            by simp

          moreover then have "is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>)"
            using 
              is_maximal\<^sub>l_ground_subst_stability'[OF 
                _  
                premise\<^sub>1_grounding[unfolded \<mu>(2) clause.subst_comp_subst]
                ]
              clause.subst_in_to_set_subst
              literal\<^sub>1_in_premise\<^sub>1
            by blast

          ultimately show ?thesis
            using \<P>\<^sub>G_Neg
            by simp
        next
          case select\<^sub>G_not_empty: False

          have selected_grounding: "clause.is_ground (select premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<cdot> \<sigma>)"
            using select_subst(1)[OF premise\<^sub>1_grounding] select(1)
            unfolding \<mu>(2) clause.subst_comp_subst
            by (metis clause.ground_is_ground)

          note selected_subst =
            literal\<^sub>1_selected[
              OF \<P>\<^sub>G_Neg select\<^sub>G_not_empty, 
              THEN maximal\<^sub>l_in_clause, 
              THEN clause.subst_in_to_set_subst] 

          have "is_maximal\<^sub>l (literal\<^sub>1  \<cdot>l \<rho>\<^sub>1 \<cdot>l \<gamma>) (select premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>)"  
            using select\<^sub>G_not_empty ground_superpositionI(9) \<P>\<^sub>G_Neg 
            unfolding is_maximal_lit_iff_is_maximal\<^sub>l literal\<^sub>1_\<gamma>[symmetric] select(1)
            by simp

          then have "is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) ((select premise\<^sub>1) \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>)"
            using is_maximal\<^sub>l_ground_subst_stability'[OF _ selected_grounding] selected_subst
            by (metis \<mu>(2) clause.subst_comp_subst literal.subst_comp_subst)

          with select\<^sub>G_not_empty \<P>\<^sub>G_Neg show ?thesis
            by simp
        qed
      qed
    next
      show "select premise\<^sub>2 = {#}"
        using ground_superpositionI(10) select(2)
        by clause_auto
    next 
      have "is_strictly_maximal\<^sub>l (literal\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu> \<cdot>l \<sigma>) (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu> \<cdot> \<sigma>)"
        using literal\<^sub>G\<^sub>2_is_strictly_maximal\<^sub>l
        unfolding literal\<^sub>2_\<gamma>[symmetric] \<mu>(2)
        by simp

      then show "is_strictly_maximal\<^sub>l (literal\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu>) (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>)"
        using 
          is_strictly_maximal\<^sub>l_ground_subst_stability'[OF 
            _  premise\<^sub>2_grounding[unfolded \<mu>(2) clause.subst_comp_subst]]
          literal\<^sub>2_in_premise\<^sub>2
          clause.subst_in_to_set_subst
        by blast
    next
      have term_groundings: 
        "term.is_ground (term\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<sigma>)" 
        "term.is_ground (context\<^sub>1\<langle>term\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<sigma>)" 
        unfolding 
          term\<^sub>1_with_context[symmetric]  
          term\<^sub>1_with_context_\<gamma>[unfolded \<mu>(2) term_subst.subst_comp_subst]
          term\<^sub>1'_\<gamma>[unfolded \<mu>(2) term_subst.subst_comp_subst]
        by simp_all

      have "term\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<sigma> \<prec>\<^sub>t context\<^sub>1\<langle>term\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<sigma>"
        using ground_superpositionI(7) 
        unfolding 
          term\<^sub>1'_\<gamma>[unfolded \<mu>(2) term_subst.subst_comp_subst]
          term\<^sub>1_with_context[symmetric]
          term\<^sub>1_with_context_\<gamma>[unfolded \<mu>(2) term_subst.subst_comp_subst]
          less\<^sub>t\<^sub>G_def
          ground_term_with_context(3).

      then show "\<not> context\<^sub>1\<langle>term\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t term\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu>"
        using less\<^sub>t_less_eq\<^sub>t_ground_subst_stability[OF term_groundings]
        by blast
    next
      have term_groundings: 
        "term.is_ground (term\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<sigma>)"
        "term.is_ground (term\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<sigma>)"
        unfolding
          term\<^sub>2_\<gamma>[unfolded \<mu>(2) term_subst.subst_comp_subst]
          term\<^sub>2'_\<gamma>[unfolded \<mu>(2) term_subst.subst_comp_subst]
        by simp_all

      have "term\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<sigma> \<prec>\<^sub>t term\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<sigma>"
        using ground_superpositionI(8)
        unfolding
          term\<^sub>2_\<gamma>[unfolded \<mu>(2) term_subst.subst_comp_subst]       
          term\<^sub>2'_\<gamma>[unfolded \<mu>(2) term_subst.subst_comp_subst]
          less\<^sub>t\<^sub>G_def.

      then show "\<not> term\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<preceq>\<^sub>t term\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu>"
        using less\<^sub>t_less_eq\<^sub>t_ground_subst_stability[OF term_groundings]
        by blast
    next
      show 
        "conclusion' = add_mset (?\<P> (Upair (context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>term\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> (term\<^sub>1' \<cdot>t \<rho>\<^sub>1))) 
          (premise\<^sub>1' \<cdot> \<rho>\<^sub>1 + premise\<^sub>2' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu>"
        unfolding term\<^sub>2'_with_context conclusion'..
      show "welltyped_imgu' typeof_fun \<V>\<^sub>3 (term\<^sub>1 \<cdot>t \<rho>\<^sub>1) (term\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<mu>"
        using \<mu>(3) by blast

      show "clause.vars (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter> clause.vars (premise\<^sub>2 \<cdot> \<rho>\<^sub>2) = {}"
        using renaming(3). 

      show "\<forall>x\<in>clause.vars (premise\<^sub>1 \<cdot> \<rho>\<^sub>1). \<V>\<^sub>1 (the_inv \<rho>\<^sub>1 (Var x)) = \<V>\<^sub>3 x"
        unfolding \<V>\<^sub>3_def
        by meson

      show "\<forall>x\<in>clause.vars (premise\<^sub>2 \<cdot> \<rho>\<^sub>2). \<V>\<^sub>2 (the_inv \<rho>\<^sub>2 (Var x)) = \<V>\<^sub>3 x"
        unfolding \<V>\<^sub>3_def
        using renaming(3)
        by (meson disjoint_iff)

      show "welltyped\<^sub>\<sigma>_on (clause.vars premise\<^sub>1) typeof_fun \<V>\<^sub>1 \<rho>\<^sub>1"
        using typing(6).

      show "welltyped\<^sub>\<sigma>_on (clause.vars premise\<^sub>2) typeof_fun \<V>\<^sub>2 \<rho>\<^sub>2"
        using typing(7).

      have "\<exists>\<tau>. welltyped typeof_fun \<V>\<^sub>2 term\<^sub>2 \<tau> \<and> welltyped typeof_fun \<V>\<^sub>2 term\<^sub>2' \<tau>"
        using typing(2)
        unfolding premise\<^sub>2 literal\<^sub>2 welltyped\<^sub>c_def welltyped\<^sub>l_def welltyped\<^sub>a_def
        by auto

      then show "\<And>\<tau> \<tau>'. \<lbrakk>has_type typeof_fun \<V>\<^sub>2 term\<^sub>2 \<tau>; has_type typeof_fun \<V>\<^sub>2 term\<^sub>2' \<tau>'\<rbrakk> \<Longrightarrow> \<tau> = \<tau>'"
        by (metis welltyped_right_unique has_type_welltyped right_uniqueD) 

      show "all_types \<V>\<^sub>1" "all_types \<V>\<^sub>2"
        using typing
        by auto
    qed

    have "term_subst.is_idem \<mu>"
      using \<mu>(1)
      by (simp add: term_subst.is_imgu_iff_is_idem_and_is_mgu)  

    then have \<mu>_\<gamma>: "\<mu> \<odot> \<gamma> = \<gamma>"
      unfolding \<mu>(2) term_subst.is_idem_def
      by (metis subst_compose_assoc)

    have conclusion'_\<gamma>: "conclusion' \<cdot> \<gamma> = conclusion \<cdot> \<gamma>"
    proof-
      have "conclusion \<cdot> \<gamma> = 
              add_mset (?\<P> (Upair (context.from_ground context\<^sub>G)\<langle>term.from_ground term\<^sub>G\<^sub>3\<rangle> (term.from_ground term\<^sub>G\<^sub>2))) 
                (clause.from_ground premise\<^sub>G\<^sub>1' + clause.from_ground premise\<^sub>G\<^sub>2')"
      proof-
        have "\<lbrakk>
          conclusion\<^sub>G = add_mset (context\<^sub>G\<langle>term\<^sub>G\<^sub>3\<rangle>\<^sub>G \<approx> term\<^sub>G\<^sub>2) (premise\<^sub>G\<^sub>1' + premise\<^sub>G\<^sub>2');
          clause.from_ground (clause.to_ground (conclusion \<cdot> \<gamma>)) = conclusion \<cdot> \<gamma>; \<P>\<^sub>G = Pos\<rbrakk>
          \<Longrightarrow> conclusion \<cdot> \<gamma> =
              add_mset
               ((if Pos = Pos then Pos else Neg)
                 (Upair (term.from_ground context\<^sub>G\<langle>term\<^sub>G\<^sub>3\<rangle>\<^sub>G) (term.from_ground term\<^sub>G\<^sub>2)))
               (clause.from_ground premise\<^sub>G\<^sub>1' + clause.from_ground premise\<^sub>G\<^sub>2')"
          by (simp add: literal_from_ground_atom_from_ground(2) clause_from_ground_add_mset 
              atom_from_ground_term_from_ground)

        moreover have "\<lbrakk>
          conclusion\<^sub>G = add_mset (context\<^sub>G\<langle>term\<^sub>G\<^sub>3\<rangle>\<^sub>G !\<approx> term\<^sub>G\<^sub>2) (premise\<^sub>G\<^sub>1' + premise\<^sub>G\<^sub>2');
          clause.from_ground (clause.to_ground (conclusion \<cdot> \<gamma>)) = conclusion \<cdot> \<gamma>; \<P>\<^sub>G = Neg\<rbrakk>
          \<Longrightarrow> conclusion \<cdot> \<gamma> =
              add_mset
               ((if Neg = Pos then Pos else Neg)
                 (Upair (term.from_ground context\<^sub>G\<langle>term\<^sub>G\<^sub>3\<rangle>\<^sub>G) (term.from_ground term\<^sub>G\<^sub>2)))
               (clause.from_ground premise\<^sub>G\<^sub>1' + clause.from_ground premise\<^sub>G\<^sub>2')"
          by (simp add: literal_from_ground_atom_from_ground(1) clause_from_ground_add_mset 
              atom_from_ground_term_from_ground)

        ultimately show ?thesis
          using ground_superpositionI(4, 12) clause.to_ground_inverse[OF conclusion_grounding] 
          unfolding ground_term_with_context(3) 
          by clause_simp
      qed
      
      then show ?thesis
        unfolding 
          conclusion'
          term\<^sub>2'_with_context_\<gamma>[symmetric]
          premise\<^sub>1'_\<gamma>[symmetric] 
          premise\<^sub>2'_\<gamma>[symmetric] 
          term\<^sub>1'_\<gamma>[symmetric]
          subst_clause_plus[symmetric] 
          subst_apply_term_ctxt_apply_distrib[symmetric]
          subst_atom[symmetric]
        unfolding
          clause.subst_comp_subst[symmetric]
          \<mu>_\<gamma>
        by(simp add: subst_clause_add_mset subst_literal)
    qed

    have vars_conclusion': 
      "clause.vars conclusion' \<subseteq> clause.vars (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) \<union> clause.vars (premise\<^sub>2 \<cdot> \<rho>\<^sub>2)"
    proof
      fix x 
      assume "x \<in> clause.vars conclusion'"

      then consider 
          (term\<^sub>2'_with_context) "x \<in> term.vars (term\<^sub>2'_with_context \<cdot>t \<mu>)" 
        | (term\<^sub>1')  "x \<in> term.vars (term\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu>)"  
        | (premise\<^sub>1')  "x \<in> clause.vars (premise\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>)"  
        | (premise\<^sub>2')  "x \<in> clause.vars (premise\<^sub>2' \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>)"  
        unfolding conclusion' subst_clause_add_mset subst_clause_plus subst_literal
        by clause_simp
  
      then show "x \<in> clause.vars (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) \<union> clause.vars (premise\<^sub>2 \<cdot> \<rho>\<^sub>2)"
      proof(cases)
        case t: term\<^sub>2'_with_context
        then show ?thesis 
          using vars_context_imgu[OF \<mu>(1)]  vars_term_imgu[OF \<mu>(1)]
          unfolding premise\<^sub>1 literal\<^sub>1 term\<^sub>1_with_context premise\<^sub>2 literal\<^sub>2 term\<^sub>2'_with_context
          apply clause_simp
          by blast
      next
        case term\<^sub>1'
        then show ?thesis
          using vars_term_imgu[OF \<mu>(1)]
          unfolding premise\<^sub>1 subst_clause_add_mset literal\<^sub>1 term\<^sub>1_with_context premise\<^sub>2 literal\<^sub>2
          by clause_simp
      next
        case premise\<^sub>1'
        then show ?thesis 
          using vars_clause_imgu[OF \<mu>(1)]
          unfolding premise\<^sub>1 subst_clause_add_mset literal\<^sub>1 term\<^sub>1_with_context premise\<^sub>2 literal\<^sub>2
          by clause_simp
       next
        case premise\<^sub>2'
        then show ?thesis 
          using vars_clause_imgu[OF \<mu>(1)]
          unfolding premise\<^sub>1 subst_clause_add_mset literal\<^sub>1 term\<^sub>1_with_context premise\<^sub>2 literal\<^sub>2
          by clause_simp
      qed
    qed

    have surjx: "surj (\<lambda>x. the_inv \<rho>\<^sub>2 (Var x))"
      using surj_the_inv[OF renaming(2)].

    have yy: 
      "\<And>P Q b ty. {x. (if b x then P x else Q x) = ty } = 
        {x. b x \<and> P x = ty} \<union> {x. \<not>b x \<and> Q x = ty}"
      by auto

    have qq: "\<And>ty. infinite {x. \<V>\<^sub>2 (the_inv \<rho>\<^sub>2 (Var x)) = ty}"
      using needed[OF surjx typing(9)[unfolded all_types_def, rule_format]].

    have zz: 
      "\<And>ty. {x. x \<notin> clause.vars (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) \<and> \<V>\<^sub>2 (the_inv \<rho>\<^sub>2 (Var x)) = ty} = 
            {x. \<V>\<^sub>2 (the_inv \<rho>\<^sub>2 (Var x)) = ty} - {x. x \<in> clause.vars (premise\<^sub>1 \<cdot> \<rho>\<^sub>1)}"
      by auto

    have "\<And>ty. infinite {x. x \<notin> clause.vars (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) \<and> \<V>\<^sub>2 (the_inv \<rho>\<^sub>2 (Var x)) = ty}"
      unfolding zz
      using qq
      by auto

    then have all_types_\<V>\<^sub>3: "all_types \<V>\<^sub>3"   
      unfolding \<V>\<^sub>3_def all_types_def  yy     
      by auto

    show "\<iota>\<^sub>G \<in> inference_groundings (Infer [(premise\<^sub>2, \<V>\<^sub>2), (premise\<^sub>1, \<V>\<^sub>1)] (conclusion', \<V>\<^sub>3))"
    proof-
      have " \<lbrakk>conclusion' \<cdot> \<gamma> = conclusion \<cdot> \<gamma>;
         ground.ground_superposition (clause.to_ground (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<gamma>))
          (clause.to_ground (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>)) (clause.to_ground (conclusion \<cdot> \<gamma>));
         welltyped\<^sub>\<sigma>_on (clause.vars conclusion') typeof_fun \<V>\<^sub>3 \<gamma>; all_types \<V>\<^sub>3\<rbrakk>
        \<Longrightarrow> First_Order_Type_System.welltyped\<^sub>c typeof_fun \<V>\<^sub>3 conclusion'"
        using \<open>superposition (premise\<^sub>2, \<V>\<^sub>2) (premise\<^sub>1, \<V>\<^sub>1) (conclusion', \<V>\<^sub>3)\<close> 
          superposition_preserves_typing typing(1) typing(2) by blast

      then have 
        "is_inference_grounding (Infer [(premise\<^sub>2, \<V>\<^sub>2), (premise\<^sub>1, \<V>\<^sub>1)] (conclusion', \<V>\<^sub>3)) \<iota>\<^sub>G \<gamma> \<rho>\<^sub>1 \<rho>\<^sub>2"
        using 
          conclusion'_\<gamma> ground_superposition 
          welltyped\<^sub>\<sigma>_on_subset[OF  wt_\<gamma> vars_conclusion'] 
          all_types_\<V>\<^sub>3
        unfolding is_inference_grounding_def
        unfolding ground.G_Inf_def \<iota>\<^sub>G
        by(auto simp: typing renaming premise\<^sub>1_grounding premise\<^sub>2_grounding conclusion_grounding)

      then show ?thesis
        using is_inference_grounding_inference_groundings
        by blast
    qed

    show "conclusion' \<cdot> \<gamma> = conclusion \<cdot> \<gamma>"
      using conclusion'_\<gamma>.
  qed
qed  

lemma eq_resolution_ground_instance: 
  assumes 
    "\<iota>\<^sub>G \<in> ground.eq_resolution_inferences"
    "\<iota>\<^sub>G \<in> ground.Inf_from_q select\<^sub>G (\<Union>(clause_groundings typeof_fun ` premises))"
    "subst_stability_on typeof_fun premises"
  obtains \<iota> where 
    "\<iota> \<in> Inf_from premises" 
    "\<iota>\<^sub>G \<in> inference_groundings \<iota>"
proof-
  obtain premise\<^sub>G conclusion\<^sub>G where 
    \<iota>\<^sub>G : "\<iota>\<^sub>G = Infer [premise\<^sub>G] conclusion\<^sub>G" and
    ground_eq_resolution: "ground.ground_eq_resolution premise\<^sub>G conclusion\<^sub>G"
    using assms(1)
    by blast

  have premise\<^sub>G_in_groundings: "premise\<^sub>G \<in> \<Union>(clause_groundings typeof_fun ` premises)"
    using assms(2)
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
    by simp

  obtain premise "conclusion" \<gamma> \<V> where
    "clause.from_ground premise\<^sub>G = premise \<cdot> \<gamma>" and
    "clause.from_ground conclusion\<^sub>G = conclusion \<cdot> \<gamma>" and
    select: "clause.from_ground (select\<^sub>G premise\<^sub>G) = select premise \<cdot> \<gamma>" and
    premise_in_premises: "(premise, \<V>) \<in> premises" and
    typing: "welltyped\<^sub>c typeof_fun \<V> premise"
    "term_subst.is_ground_subst \<gamma>"
    "welltyped\<^sub>\<sigma>_on (clause.vars premise) typeof_fun \<V> \<gamma>"
    "all_types \<V>"
  proof-
    have x: "\<And>a b. \<lbrakk>\<And>premise \<gamma> conclusion \<V>.
               \<lbrakk>clause.from_ground premise\<^sub>G = premise \<cdot> \<gamma>;
                clause.from_ground conclusion\<^sub>G = conclusion \<cdot> \<gamma>;
                clause.from_ground (select\<^sub>G premise\<^sub>G) = select premise \<cdot> \<gamma>; 
                (premise, \<V>) \<in> premises;
                First_Order_Type_System.welltyped\<^sub>c typeof_fun \<V> premise; 
                term_subst.is_ground_subst \<gamma>;
                welltyped\<^sub>\<sigma>_on (clause.vars premise) typeof_fun \<V> \<gamma>; all_types \<V>\<rbrakk>
               \<Longrightarrow> thesis;
            \<forall>y\<in>premises.
               \<forall>premise\<^sub>G\<in>clause_groundings typeof_fun y.
                  \<exists>x\<in>premises.
                     case x of
                     (premise, \<V>) \<Rightarrow>
                       \<exists>\<gamma>. premise \<cdot> \<gamma> = clause.from_ground premise\<^sub>G \<and>
                           select\<^sub>G (clause.to_ground (premise \<cdot> \<gamma>)) =
                           clause.to_ground (select premise \<cdot> \<gamma>) \<and>
                           First_Order_Type_System.welltyped\<^sub>c typeof_fun \<V> premise \<and>
                           welltyped\<^sub>\<sigma>_on (clause.vars premise) typeof_fun \<V> \<gamma> \<and>
                           term_subst.is_ground_subst \<gamma> \<and> all_types \<V>;
            Infer [premise\<^sub>G] conclusion\<^sub>G \<in> ground.G_Inf; (a, b) \<in> premises;
            premise\<^sub>G \<in> clause_groundings typeof_fun (a, b)\<rbrakk>
           \<Longrightarrow> thesis"
      by (smt (verit, del_insts) case_prodE clause.ground_is_ground select_subst1 
          clause.subst_ident_if_ground clause.from_ground_inverse clause.to_ground_inverse)

    then show ?thesis
      using assms(2, 3) premise\<^sub>G_in_groundings that
      unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
      by auto
  qed

  then have
    premise_grounding: "clause.is_ground (premise \<cdot> \<gamma>)" and
    premise\<^sub>G: "premise\<^sub>G = clause.to_ground (premise \<cdot> \<gamma>)" and
    conclusion_grounding: "clause.is_ground (conclusion \<cdot> \<gamma>)" and
    conclusion\<^sub>G: "conclusion\<^sub>G = clause.to_ground (conclusion \<cdot> \<gamma>)"
    using clause.ground_is_ground clause.from_ground_inverse
    by(smt(verit))+

  obtain conclusion' where
    eq_resolution: "eq_resolution (premise, \<V>) (conclusion', \<V>)" and
    \<iota>\<^sub>G: "\<iota>\<^sub>G = Infer [clause.to_ground (premise \<cdot> \<gamma>)] (clause.to_ground (conclusion' \<cdot> \<gamma>))" and
    inference_groundings: "\<iota>\<^sub>G \<in> inference_groundings (Infer [(premise, \<V>)] (conclusion', \<V>))" and  
    conclusion'_conclusion: "conclusion' \<cdot> \<gamma> = conclusion \<cdot> \<gamma>"
    using
      eq_resolution_lifting[OF 
        premise_grounding 
        conclusion_grounding 
        select[unfolded premise\<^sub>G] 
        ground_eq_resolution[unfolded premise\<^sub>G conclusion\<^sub>G]
        typing
        ]
    unfolding premise\<^sub>G conclusion\<^sub>G \<iota>\<^sub>G
    by metis

  let ?\<iota> = "Infer [(premise, \<V>)] (conclusion', \<V>)"

  show ?thesis
  proof(rule that)
    show "?\<iota> \<in> Inf_from premises"
      using premise_in_premises eq_resolution
      unfolding Inf_from_def inferences_def inference_system.Inf_from_def
      by auto

    show "\<iota>\<^sub>G \<in> inference_groundings ?\<iota>"
      using inference_groundings.
  qed
qed 

lemma eq_factoring_ground_instance: 
  assumes 
    "\<iota>\<^sub>G \<in> ground.eq_factoring_inferences"
    "\<iota>\<^sub>G \<in> ground.Inf_from_q select\<^sub>G (\<Union>(clause_groundings typeof_fun ` premises))"
    "subst_stability_on typeof_fun premises"
  obtains \<iota> where 
    "\<iota> \<in> Inf_from premises" 
    "\<iota>\<^sub>G \<in> inference_groundings \<iota>"
proof-
  obtain premise\<^sub>G conclusion\<^sub>G where 
    \<iota>\<^sub>G : "\<iota>\<^sub>G = Infer [premise\<^sub>G] conclusion\<^sub>G" and
    ground_eq_factoring: "ground.ground_eq_factoring premise\<^sub>G conclusion\<^sub>G"
    using assms(1)
    by blast

  have premise\<^sub>G_in_groundings: "premise\<^sub>G \<in> \<Union>(clause_groundings typeof_fun ` premises)"
    using assms(2)
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
    by simp

  obtain premise "conclusion" \<gamma> \<V> where
    "clause.from_ground premise\<^sub>G = premise \<cdot> \<gamma>" and
    "clause.from_ground conclusion\<^sub>G = conclusion \<cdot> \<gamma>" and
    select: "clause.from_ground (select\<^sub>G (clause.to_ground (premise \<cdot> \<gamma>))) = select premise \<cdot> \<gamma>" and
    premise_in_premises: "(premise, \<V>) \<in> premises" and
    typing:
    "welltyped\<^sub>c typeof_fun \<V> premise"
    "term_subst.is_ground_subst \<gamma>"
    "welltyped\<^sub>\<sigma>_on (clause.vars premise) typeof_fun \<V> \<gamma>"
    "all_types \<V>"
    using assms(2, 3) premise\<^sub>G_in_groundings
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
    by (smt (verit) clause.subst_ident_if_ground clause.ground_is_ground 
        old.prod.case old.prod.exhaust select_subst1 clause.to_ground_inverse)

  then have 
    premise_grounding: "clause.is_ground (premise \<cdot> \<gamma>)" and 
    premise\<^sub>G: "premise\<^sub>G = clause.to_ground (premise \<cdot> \<gamma>)" and 
    conclusion_grounding: "clause.is_ground (conclusion \<cdot> \<gamma>)" and
    conclusion\<^sub>G: "conclusion\<^sub>G = clause.to_ground (conclusion \<cdot> \<gamma>)"
    by (smt(verit) clause.ground_is_ground clause.from_ground_inverse)+

  obtain conclusion' where 
    eq_factoring: "eq_factoring (premise, \<V>) (conclusion', \<V>)" and
    inference_groundings: "\<iota>\<^sub>G \<in> inference_groundings (Infer [(premise, \<V>)] (conclusion', \<V>))" and  
    conclusion'_conclusion: "conclusion' \<cdot> \<gamma> = conclusion \<cdot> \<gamma>"
    using 
      eq_factoring_lifting[OF 
        premise_grounding 
        conclusion_grounding 
        select 
        ground_eq_factoring[unfolded premise\<^sub>G conclusion\<^sub>G]
        ]
      typing
    unfolding premise\<^sub>G conclusion\<^sub>G \<iota>\<^sub>G
    by metis

  let ?\<iota> = "Infer [(premise, \<V>)] (conclusion', \<V>)"

  show ?thesis
  proof(rule that)
    show "?\<iota> \<in> Inf_from premises"
      using premise_in_premises eq_factoring
      unfolding Inf_from_def inferences_def inference_system.Inf_from_def
      by auto

    show "\<iota>\<^sub>G \<in> inference_groundings ?\<iota>"
      using inference_groundings.
  qed
qed

lemma subst_compose_if: "\<sigma> \<odot> (\<lambda>var. if var \<in> range_vars' \<sigma> then \<sigma>\<^sub>1 var else \<sigma>\<^sub>2 var) = \<sigma> \<odot> \<sigma>\<^sub>1"
  unfolding subst_compose_def range_vars'_def
  using term_subst_eq_conv
  by fastforce

lemma subst_compose_if': 
  assumes "range_vars' \<sigma> \<inter> range_vars' \<sigma>' = {}"
  shows "\<sigma> \<odot> (\<lambda>var. if var \<in> range_vars' \<sigma>' then \<sigma>\<^sub>1 var else \<sigma>\<^sub>2 var) = \<sigma> \<odot> \<sigma>\<^sub>2"
proof-
  have "\<And>x. \<sigma> x \<cdot>t (\<lambda>var. if var \<in> range_vars' \<sigma>' then \<sigma>\<^sub>1 var else \<sigma>\<^sub>2 var) = \<sigma> x \<cdot>t \<sigma>\<^sub>2"
  proof-
    fix x
    have "\<And>xa. \<lbrakk>\<sigma> x = Var xa; xa \<in> range_vars' \<sigma>'\<rbrakk> \<Longrightarrow> \<sigma>\<^sub>1 xa = \<sigma>\<^sub>2 xa"
      by (metis IntI assms emptyE subst_compose_def term.set_intros(3) 
          term_subst.comp_subst.left.right_neutral vars_term_range_vars')
    moreover have "\<And>x1a x2 xa.
       \<lbrakk>\<sigma> x = Fun x1a x2; xa \<in> set x2\<rbrakk>
       \<Longrightarrow> xa \<cdot>t (\<lambda>var. if var \<in> range_vars' \<sigma>' then \<sigma>\<^sub>1 var else \<sigma>\<^sub>2 var) = xa \<cdot>t \<sigma>\<^sub>2"
      by (smt (verit, ccfv_threshold) UNIV_I UN_iff assms disjoint_iff image_iff range_vars'_def 
          term.set_intros(4) term_subst_eq_conv)

    ultimately show "\<sigma> x \<cdot>t (\<lambda>var. if var \<in> range_vars' \<sigma>' then \<sigma>\<^sub>1 var else \<sigma>\<^sub>2 var) = \<sigma> x \<cdot>t \<sigma>\<^sub>2"
      by(induction "\<sigma> x") auto
  qed

  then show ?thesis
    unfolding subst_compose_def    
    by presburger
qed

lemma is_ground_subst_if:
  assumes "term_subst.is_ground_subst \<gamma>\<^sub>1" "term_subst.is_ground_subst \<gamma>\<^sub>2"
  shows "term_subst.is_ground_subst (\<lambda>var. if b var then \<gamma>\<^sub>1 var else \<gamma>\<^sub>2 var)"
  using assms
  unfolding term_subst.is_ground_subst_def
  by (simp add: is_ground_iff)

lemma superposition_ground_instance: 
  assumes 
    "\<iota>\<^sub>G \<in> ground.superposition_inferences"
    "\<iota>\<^sub>G \<in> ground.Inf_from_q select\<^sub>G (\<Union> (clause_groundings typeof_fun ` premises))" 
    "\<iota>\<^sub>G \<notin> ground.GRed_I (\<Union> (clause_groundings typeof_fun ` premises))"
    "subst_stability_on typeof_fun premises"
  obtains \<iota> where 
    "\<iota> \<in> Inf_from premises" 
    "\<iota>\<^sub>G \<in> inference_groundings \<iota>"
proof-
  obtain premise\<^sub>G\<^sub>1 premise\<^sub>G\<^sub>2 conclusion\<^sub>G where 
    \<iota>\<^sub>G : "\<iota>\<^sub>G = Infer [premise\<^sub>G\<^sub>2, premise\<^sub>G\<^sub>1] conclusion\<^sub>G" and
    ground_superposition: "ground.ground_superposition premise\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>1 conclusion\<^sub>G"
    using assms(1)
    by blast

  have 
    premise\<^sub>G\<^sub>1_in_groundings: "premise\<^sub>G\<^sub>1 \<in> \<Union> (clause_groundings typeof_fun ` premises)" and  
    premise\<^sub>G\<^sub>2_in_groundings: "premise\<^sub>G\<^sub>2 \<in> \<Union> (clause_groundings typeof_fun ` premises)"
    using assms(2)
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
    by simp_all

  obtain premise\<^sub>1 \<V>\<^sub>1 premise\<^sub>2 \<V>\<^sub>2 \<gamma>\<^sub>1 \<gamma>\<^sub>2 where
    premise\<^sub>1_\<gamma>\<^sub>1: "premise\<^sub>1 \<cdot> \<gamma>\<^sub>1 = clause.from_ground premise\<^sub>G\<^sub>1" and
    premise\<^sub>2_\<gamma>\<^sub>2: "premise\<^sub>2 \<cdot> \<gamma>\<^sub>2 = clause.from_ground premise\<^sub>G\<^sub>2" and
    select: 
    "clause.from_ground (select\<^sub>G (clause.to_ground (premise\<^sub>1 \<cdot> \<gamma>\<^sub>1))) = select premise\<^sub>1 \<cdot> \<gamma>\<^sub>1"
    "clause.from_ground (select\<^sub>G (clause.to_ground (premise\<^sub>2 \<cdot> \<gamma>\<^sub>2))) = select premise\<^sub>2 \<cdot> \<gamma>\<^sub>2" and
    premise\<^sub>1_in_premises: "(premise\<^sub>1, \<V>\<^sub>1) \<in> premises" and
    premise\<^sub>2_in_premises: "(premise\<^sub>2, \<V>\<^sub>2) \<in> premises" and 
    wt: 
    "welltyped\<^sub>\<sigma>_on (clause.vars premise\<^sub>1) typeof_fun \<V>\<^sub>1 \<gamma>\<^sub>1"
    "welltyped\<^sub>\<sigma>_on (clause.vars premise\<^sub>2) typeof_fun \<V>\<^sub>2 \<gamma>\<^sub>2"
    "term_subst.is_ground_subst \<gamma>\<^sub>1"
    "term_subst.is_ground_subst \<gamma>\<^sub>2" 
    "welltyped\<^sub>c typeof_fun \<V>\<^sub>1 premise\<^sub>1"
    "welltyped\<^sub>c typeof_fun \<V>\<^sub>2 premise\<^sub>2"
    "all_types \<V>\<^sub>1" 
    "all_types \<V>\<^sub>2" 
    using assms(2, 4) premise\<^sub>G\<^sub>1_in_groundings premise\<^sub>G\<^sub>2_in_groundings
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def   
    by (smt (verit, ccfv_threshold) case_prod_conv clause.ground_is_ground select_subst1 
        surj_pair clause.to_ground_inverse)

  obtain \<rho>\<^sub>1 \<rho>\<^sub>2 :: "('f, 'v) subst" where
    renaming: 
    "term_subst.is_renaming \<rho>\<^sub>1" 
    "term_subst.is_renaming \<rho>\<^sub>2"
    "\<rho>\<^sub>1 ` (clause.vars premise\<^sub>1) \<inter> \<rho>\<^sub>2 ` (clause.vars premise\<^sub>2) = {}" and
    wt_\<rho>: 
    "welltyped\<^sub>\<sigma>_on (clause.vars premise\<^sub>1) typeof_fun \<V>\<^sub>1 \<rho>\<^sub>1"
    "welltyped\<^sub>\<sigma>_on (clause.vars premise\<^sub>2) typeof_fun \<V>\<^sub>2 \<rho>\<^sub>2"
    using welltyped_on_renaming_exists'[OF _ _ wt(7,8)[unfolded all_types_def, rule_format]] 
    by (metis clause.finite_vars(1))

  have renaming_distinct: "clause.vars (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter> clause.vars (premise\<^sub>2 \<cdot> \<rho>\<^sub>2) = {}"
    using renaming(3)
    unfolding renaming(1,2)[THEN renaming_vars_clause, symmetric]
    by blast

  from renaming obtain \<rho>\<^sub>1_inv \<rho>\<^sub>2_inv where
    \<rho>\<^sub>1_inv: "\<rho>\<^sub>1 \<odot> \<rho>\<^sub>1_inv = Var" and
    \<rho>\<^sub>2_inv: "\<rho>\<^sub>2 \<odot> \<rho>\<^sub>2_inv = Var"
    unfolding term_subst.is_renaming_def
    by blast

  have "select premise\<^sub>1 \<subseteq># premise\<^sub>1" "select premise\<^sub>2 \<subseteq># premise\<^sub>2"
    by (simp_all add: select_subset)

  then have select_subset: 
    "select premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<subseteq># premise\<^sub>1 \<cdot> \<rho>\<^sub>1" 
    "select premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<subseteq># premise\<^sub>2 \<cdot> \<rho>\<^sub>2"
    by (simp_all add: image_mset_subseteq_mono clause.subst_def)

  define \<gamma> where 
    \<gamma>: "\<And>var. \<gamma> var \<equiv>
          if var \<in> clause.vars (premise\<^sub>1 \<cdot> \<rho>\<^sub>1)
          then (\<rho>\<^sub>1_inv \<odot> \<gamma>\<^sub>1) var 
          else (\<rho>\<^sub>2_inv \<odot> \<gamma>\<^sub>2) var"

  have \<gamma>\<^sub>1: "\<forall>x\<in> clause.vars premise\<^sub>1. (\<rho>\<^sub>1 \<odot> \<gamma>) x = \<gamma>\<^sub>1 x"
  proof(intro ballI)
    fix x
    assume x_in_vars: "x \<in> clause.vars premise\<^sub>1"

    obtain y where y: "\<rho>\<^sub>1 x = Var y"
      by (meson is_Var_def renaming(1) term_subst_is_renaming_iff)

    then have "y \<in> clause.vars (premise\<^sub>1 \<cdot> \<rho>\<^sub>1)"
      using x_in_vars renaming(1) renaming_vars_clause by fastforce
    

    then have "\<gamma> y = \<rho>\<^sub>1_inv y \<cdot>t \<gamma>\<^sub>1"
      by (simp add: \<gamma> subst_compose)

    then show "(\<rho>\<^sub>1 \<odot> \<gamma>) x = \<gamma>\<^sub>1 x"
      by (metis y \<rho>\<^sub>1_inv eval_term.simps(1) subst_compose)
  qed

  have \<gamma>\<^sub>2: "\<forall>x\<in> clause.vars premise\<^sub>2. (\<rho>\<^sub>2 \<odot> \<gamma>) x = \<gamma>\<^sub>2 x"
  proof(intro ballI)
    fix x
    assume x_in_vars: "x \<in> clause.vars premise\<^sub>2"

    obtain y where y: "\<rho>\<^sub>2 x = Var y"
      by (meson is_Var_def renaming(2) term_subst_is_renaming_iff)

    then have "y \<in> clause.vars (premise\<^sub>2 \<cdot> \<rho>\<^sub>2)"
      using x_in_vars renaming(2) renaming_vars_clause by fastforce
    

    then have "\<gamma> y = \<rho>\<^sub>2_inv y \<cdot>t \<gamma>\<^sub>2"
      using \<gamma> renaming_distinct subst_compose by fastforce

    then show "(\<rho>\<^sub>2 \<odot> \<gamma>) x = \<gamma>\<^sub>2 x"
      by (metis y \<rho>\<^sub>2_inv eval_term.simps(1) subst_compose)
  qed

  have \<gamma>\<^sub>1_is_ground: "\<forall>x\<in>clause.vars premise\<^sub>1. term.is_ground (\<gamma>\<^sub>1 x)"
    by (metis Term.term.simps(17) insert_iff is_ground_iff term_subst.is_ground_subst_def wt(3))

  have \<gamma>\<^sub>2_is_ground: "\<forall>x\<in>clause.vars premise\<^sub>2. term.is_ground (\<gamma>\<^sub>2 x)"
    by (metis Term.term.simps(17) insert_iff is_ground_iff term_subst.is_ground_subst_def wt(4))

  have wt_\<gamma>:
    "welltyped\<^sub>\<sigma>_on (clause.vars premise\<^sub>1) typeof_fun \<V>\<^sub>1 (\<rho>\<^sub>1 \<odot> \<gamma>)"
    "welltyped\<^sub>\<sigma>_on (clause.vars premise\<^sub>2) typeof_fun \<V>\<^sub>2 (\<rho>\<^sub>2 \<odot> \<gamma>)"
    using wt(1,2) welltyped\<^sub>\<sigma>_on_subset welltyped\<^sub>\<sigma>_welltyped\<^sub>\<sigma>_on \<gamma>\<^sub>1 \<gamma>\<^sub>2
    unfolding welltyped\<^sub>\<sigma>_on_def 
    by auto    

  have "term_subst.is_ground_subst (\<rho>\<^sub>1_inv \<odot> \<gamma>\<^sub>1)" "term_subst.is_ground_subst (\<rho>\<^sub>2_inv \<odot> \<gamma>\<^sub>2)"
    using term_subst.is_ground_subst_comp_right wt by blast+

  then have is_ground_subst_\<gamma>: "term_subst.is_ground_subst \<gamma>"
    unfolding \<gamma>
    using is_ground_subst_if
    by fast

  have premise\<^sub>1_\<gamma>: "premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma> = clause.from_ground premise\<^sub>G\<^sub>1" 
  proof -
    have "premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<odot> (\<rho>\<^sub>1_inv \<odot> \<gamma>\<^sub>1) = clause.from_ground premise\<^sub>G\<^sub>1"
      by (metis \<rho>\<^sub>1_inv premise\<^sub>1_\<gamma>\<^sub>1 subst_monoid_mult.mult.left_neutral subst_monoid_mult.mult_assoc)

    then show ?thesis
      using \<gamma>\<^sub>1 premise\<^sub>1_\<gamma>\<^sub>1 clause.subst_eq by fastforce
  qed

  have premise\<^sub>2_\<gamma>: "premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<gamma> = clause.from_ground premise\<^sub>G\<^sub>2" 
  proof -
    have "premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<odot> (\<rho>\<^sub>2_inv \<odot> \<gamma>\<^sub>2) = clause.from_ground premise\<^sub>G\<^sub>2"
      by (metis \<rho>\<^sub>2_inv premise\<^sub>2_\<gamma>\<^sub>2 subst_monoid_mult.mult.left_neutral subst_monoid_mult.mult_assoc)

    then show ?thesis
      using \<gamma>\<^sub>2 premise\<^sub>2_\<gamma>\<^sub>2 clause.subst_eq by force
  qed

  have "premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma> = premise\<^sub>1 \<cdot> \<gamma>\<^sub>1"
    by (simp add: premise\<^sub>1_\<gamma> premise\<^sub>1_\<gamma>\<^sub>1)

  moreover have "select premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma> = select premise\<^sub>1 \<cdot> \<gamma>\<^sub>1"
  proof-
    have "clause.vars (select premise\<^sub>1 \<cdot> \<rho>\<^sub>1) \<subseteq> clause.vars (premise\<^sub>1 \<cdot> \<rho>\<^sub>1)"
      using select_subset(1) clause_submset_vars_clause_subset by blast

    then show ?thesis
      unfolding \<gamma> 
      by (smt (verit, best) \<rho>\<^sub>1_inv clause.subst_eq subsetD 
          clause.comp_subst.left.monoid_action_compatibility 
          term_subst.comp_subst.left.right_neutral)
  qed

  ultimately have select\<^sub>1: 
    "clause.from_ground (select\<^sub>G (clause.to_ground (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>))) = select premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>"
    using select(1)
    by argo
  
  have "premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<gamma> = premise\<^sub>2 \<cdot> \<gamma>\<^sub>2"
    by (simp add: premise\<^sub>2_\<gamma> premise\<^sub>2_\<gamma>\<^sub>2)

  moreover have "select premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<gamma> = select premise\<^sub>2 \<cdot> \<gamma>\<^sub>2"
   proof-
    have "clause.vars (select premise\<^sub>2 \<cdot> \<rho>\<^sub>2) \<subseteq> clause.vars (premise\<^sub>2 \<cdot> \<rho>\<^sub>2)"
      using select_subset(2) clause_submset_vars_clause_subset by blast

    then show ?thesis
      unfolding \<gamma> 
      by (smt (verit, best) \<gamma>\<^sub>2 \<gamma> \<open>select premise\<^sub>2 \<subseteq># premise\<^sub>2\<close> clause_submset_vars_clause_subset
          clause.subst_eq subset_iff clause.comp_subst.left.monoid_action_compatibility)
  qed

  ultimately have select\<^sub>2: 
    "clause.from_ground (select\<^sub>G (clause.to_ground (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<gamma>))) = select premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<gamma>"   
    using select(2) 
    by argo

  obtain "conclusion" where 
    conclusion_\<gamma>: "conclusion \<cdot> \<gamma> = clause.from_ground conclusion\<^sub>G"
    by (meson clause.ground_is_ground clause.subst_ident_if_ground)

  then have 
    premise\<^sub>1_grounding: "clause.is_ground (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>)" and 
    premise\<^sub>2_grounding: "clause.is_ground (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<gamma>)" and 
    premise\<^sub>G\<^sub>1: "premise\<^sub>G\<^sub>1 = clause.to_ground (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>)" and 
    premise\<^sub>G\<^sub>2: "premise\<^sub>G\<^sub>2 = clause.to_ground (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<gamma>)" and 
    conclusion_grounding: "clause.is_ground (conclusion \<cdot> \<gamma>)" and
    conclusion\<^sub>G: "conclusion\<^sub>G = clause.to_ground (conclusion \<cdot> \<gamma>)"
    by (simp_all add: premise\<^sub>1_\<gamma> premise\<^sub>2_\<gamma>)

  have "clause_groundings typeof_fun (premise\<^sub>1, \<V>\<^sub>1) \<union> clause_groundings typeof_fun (premise\<^sub>2, \<V>\<^sub>2)
     \<subseteq> \<Union> (clause_groundings typeof_fun ` premises)"
    using premise\<^sub>1_in_premises premise\<^sub>2_in_premises by blast

  then have \<iota>\<^sub>G_not_redunant:
    "\<iota>\<^sub>G \<notin> ground.GRed_I (clause_groundings typeof_fun (premise\<^sub>1, \<V>\<^sub>1) \<union> clause_groundings typeof_fun (premise\<^sub>2, \<V>\<^sub>2))"
    using assms(3) ground.Red_I_of_subset
    by blast

  then obtain conclusion' \<V>\<^sub>3 where 
    superposition: "superposition (premise\<^sub>2, \<V>\<^sub>2) (premise\<^sub>1, \<V>\<^sub>1) (conclusion', \<V>\<^sub>3)" and
    inference_groundings: 
      "\<iota>\<^sub>G \<in> inference_groundings (Infer [(premise\<^sub>2, \<V>\<^sub>2), (premise\<^sub>1, \<V>\<^sub>1)] (conclusion', \<V>\<^sub>3))" and  
    conclusion'_\<gamma>_conclusion_\<gamma>: "conclusion' \<cdot> \<gamma> = conclusion \<cdot> \<gamma>"
    using 
      superposition_lifting[OF 
        renaming(1,2)
        renaming_distinct
        premise\<^sub>1_grounding 
        premise\<^sub>2_grounding 
        conclusion_grounding
        select\<^sub>1
        select\<^sub>2
        ground_superposition[unfolded  premise\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>1 conclusion\<^sub>G]
        \<iota>\<^sub>G_not_redunant[unfolded \<iota>\<^sub>G premise\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>1 conclusion\<^sub>G]
        wt(5, 6)
        is_ground_subst_\<gamma>
        wt_\<gamma>
        wt_\<rho>
        wt(7, 8)
        ]
    unfolding \<iota>\<^sub>G conclusion\<^sub>G premise\<^sub>G\<^sub>1 premise\<^sub>G\<^sub>2 
    by blast

  let ?\<iota> = "Infer [(premise\<^sub>2, \<V>\<^sub>2), (premise\<^sub>1, \<V>\<^sub>1)] (conclusion', \<V>\<^sub>3)"

  show ?thesis
  proof(rule that)
    show "?\<iota> \<in> Inf_from premises"
      using premise\<^sub>1_in_premises premise\<^sub>2_in_premises superposition
      unfolding Inf_from_def inferences_def inference_system.Inf_from_def
      by auto

    show "\<iota>\<^sub>G \<in> inference_groundings ?\<iota>"
      using inference_groundings.
  qed
qed

lemma ground_instances: 
  assumes 
    "\<iota>\<^sub>G \<in> ground.Inf_from_q select\<^sub>G (\<Union> (clause_groundings typeof_fun ` premises))" 
    "\<iota>\<^sub>G \<notin> ground.Red_I (\<Union> (clause_groundings typeof_fun ` premises))"
    "subst_stability_on typeof_fun premises"
  obtains \<iota> where 
    "\<iota> \<in> Inf_from premises" 
    "\<iota>\<^sub>G \<in> inference_groundings \<iota>"
proof-
  have "\<iota>\<^sub>G \<in> ground.superposition_inferences \<or>
        \<iota>\<^sub>G \<in> ground.eq_resolution_inferences \<or>
        \<iota>\<^sub>G \<in> ground.eq_factoring_inferences"
    using assms(1)
    unfolding 
      ground.Inf_from_q_def 
      ground.Inf_from_def 
      ground.G_Inf_def 
      inference_system.Inf_from_def
    by fastforce

  then show ?thesis
  proof(elim disjE)
    assume "\<iota>\<^sub>G \<in> ground.superposition_inferences"
    then show ?thesis
      using that superposition_ground_instance assms
      by blast
  next
    assume "\<iota>\<^sub>G \<in> ground.eq_resolution_inferences"  
    then show ?thesis
      using that eq_resolution_ground_instance assms
      by blast
  next
    assume "\<iota>\<^sub>G \<in> ground.eq_factoring_inferences"
    then show ?thesis
      using that eq_factoring_ground_instance assms
      by blast
  qed
qed

end

context first_order_superposition_calculus
begin

lemma overapproximation:
  obtains select\<^sub>G where
    "ground_Inf_overapproximated select\<^sub>G premises"
    "is_grounding select\<^sub>G"
proof-
  obtain select\<^sub>G where   
    subst_stability: "select_subst_stability_on typeof_fun select select\<^sub>G premises" and
    "is_grounding select\<^sub>G" 
    using obtain_subst_stable_on_select_grounding
    by blast

  then interpret grounded_first_order_superposition_calculus
    where select\<^sub>G = select\<^sub>G
    by unfold_locales

  have overapproximation: "ground_Inf_overapproximated select\<^sub>G premises"
    using ground_instances[OF _ _ subst_stability]
    by auto

  show thesis
    using that[OF overapproximation select\<^sub>G].
qed

sublocale statically_complete_calculus "\<bottom>\<^sub>F" inferences entails_\<G> Red_I_\<G> Red_F_\<G>
proof(unfold static_empty_ord_inter_equiv_static_inter, 
    rule stat_ref_comp_to_non_ground_fam_inter, 
    rule ballI)
  fix select\<^sub>G
  assume "select\<^sub>G \<in> select\<^sub>G\<^sub>s"
  then interpret grounded_first_order_superposition_calculus
    where select\<^sub>G = select\<^sub>G
    by unfold_locales (simp add: select\<^sub>G\<^sub>s_def)

  show "statically_complete_calculus
          ground.G_Bot
          ground.G_Inf
          ground.G_entails
          ground.Red_I
          ground.Red_F"
    using ground.statically_complete_calculus_axioms.
next
  fix clauses

  have "\<And>clauses. \<exists>select\<^sub>G \<in> select\<^sub>G\<^sub>s. ground_Inf_overapproximated select\<^sub>G clauses" 
    using overapproximation
    unfolding select\<^sub>G\<^sub>s_def
    by (smt (verit, best) mem_Collect_eq)

  then show "empty_ord.saturated clauses \<Longrightarrow> 
    \<exists>select\<^sub>G \<in> select\<^sub>G\<^sub>s. ground_Inf_overapproximated select\<^sub>G clauses".
qed

end

end
