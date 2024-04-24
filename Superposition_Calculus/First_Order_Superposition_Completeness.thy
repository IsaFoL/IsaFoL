theory First_Order_Superposition_Completeness
  imports
    Ground_Superposition_Completeness
    Grounded_First_Order_Superposition
begin

context grounded_first_order_superposition_calculus
begin

lemma eq_resolution_lifting:
  fixes 
    premise\<^sub>G conclusion\<^sub>G :: "'f gatom clause" and 
    premise conclusion :: "('f, 'v) atom clause" and
    \<gamma> :: "('f, 'v) subst"
  defines 
    premise\<^sub>G [simp]: "premise\<^sub>G \<equiv> to_ground_clause (premise \<cdot> \<gamma>)" and
    conclusion\<^sub>G [simp]: "conclusion\<^sub>G \<equiv> to_ground_clause (conclusion \<cdot> \<gamma>)"
  assumes 
    premise_grounding: "is_ground_clause (premise \<cdot> \<gamma>)" and
    conclusion_grounding: "is_ground_clause (conclusion \<cdot> \<gamma>)" and
    select: "to_clause (select\<^sub>G premise\<^sub>G) = (select premise) \<cdot> \<gamma>" and
    ground_eq_resolution: "ground.ground_eq_resolution premise\<^sub>G conclusion\<^sub>G"
  obtains conclusion' 
  where
    "eq_resolution (premise, \<V>) (conclusion', \<V>)"
    "Infer [premise\<^sub>G] conclusion\<^sub>G \<in> inference_groundings (Infer [premise] conclusion')"
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
    by (metis to_clause_empty_mset to_clause_inverse)

  have "premise \<cdot> \<gamma> = to_clause (add_mset literal\<^sub>G (to_ground_clause (conclusion \<cdot> \<gamma>)))"
    using 
      ground_eq_resolutionI(1)[THEN arg_cong, of to_clause]
      to_ground_clause_inverse[OF premise_grounding]
      ground_eq_resolutionI(4)
    unfolding premise\<^sub>G conclusion\<^sub>G
    by metis

  also have "... = add_mset (to_literal literal\<^sub>G) (conclusion \<cdot> \<gamma>)"
    unfolding to_clause_add_mset
    by (simp add: conclusion_grounding)

  finally have premise_\<gamma>: "premise \<cdot> \<gamma> = add_mset (to_literal literal\<^sub>G) (conclusion \<cdot> \<gamma>)".

  let ?select\<^sub>G_empty = "select\<^sub>G premise\<^sub>G = {#}"
  let ?select\<^sub>G_not_empty = "select\<^sub>G premise\<^sub>G \<noteq> {#}"

  obtain max_literal where max_literal: 
    "is_maximal\<^sub>l max_literal premise" 
    "is_maximal\<^sub>l (max_literal \<cdot>l \<gamma>) (premise \<cdot> \<gamma>)"
    using is_maximal\<^sub>l_ground_subst_stability[OF premise_not_empty premise_grounding]
    by blast

  moreover then have "max_literal \<in># premise"
    using maximal\<^sub>l_in_clause by fastforce

  moreover have max_literal_\<gamma>: "max_literal \<cdot>l \<gamma> = to_literal (term\<^sub>G !\<approx> term\<^sub>G)"
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
        to_ground_clause_inverse[OF premise_grounding]
      by blast
  qed

  moreover obtain selected_literal where 
    "selected_literal \<cdot>l \<gamma> = to_literal (term\<^sub>G !\<approx> term\<^sub>G)" and
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
      by (metis clause_subst_empty(2) to_clause_inverse to_ground_clause_empty_mset)
  qed

  moreover then have "selected_literal \<in># premise" if ?select\<^sub>G_not_empty
    by (meson that maximal\<^sub>l_in_clause mset_subset_eqD select_subset)

  ultimately obtain literal where
    literal_\<gamma>: "literal \<cdot>l \<gamma> = to_literal (term\<^sub>G !\<approx> term\<^sub>G)" and
    literal_in_premise: "literal \<in># premise" and
    literal_selected: "?select\<^sub>G_not_empty \<Longrightarrow> is_maximal\<^sub>l literal (select premise)" and
    literal_max: "?select\<^sub>G_empty \<Longrightarrow> is_maximal\<^sub>l literal premise"
    by blast

  have literal_grounding: "is_ground_literal (literal \<cdot>l \<gamma>)"
    using literal_\<gamma> ground_literal_is_ground
    by simp

  from literal_\<gamma> obtain "term" term' where 
    literal: "literal = term !\<approx> term'"
    using subst_polarity_stable to_literal_polarity_stable
    by (metis literal.collapse(2) literal.disc(2) uprod_exhaust)

  have "term \<cdot>t \<gamma> = term' \<cdot>t \<gamma>"
    using literal_\<gamma>
    unfolding literal subst_literal(2) subst_atom_def to_literal_def to_atom_def
    by simp

  then obtain \<mu> \<sigma> where \<mu>: 
    "term_subst.is_imgu \<mu> {{term, term'}}" 
    "\<gamma> = \<mu> \<odot> \<sigma>" 
    "welltyped_imgu typeof_fun \<V> term term' \<mu>"
    using welltyped_imgu_exists
    by meson

  have literal\<^sub>G: 
    "to_literal literal\<^sub>G = (term !\<approx> term') \<cdot>l \<gamma>" 
    "literal\<^sub>G = to_ground_literal ((term !\<approx> term') \<cdot>l \<gamma>)"
    using literal_\<gamma> literal ground_eq_resolutionI(2) 
    by simp_all

  obtain conclusion' where conclusion': "premise = add_mset literal conclusion'"
    using multi_member_split[OF literal_in_premise]
    by blast

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
        by (simp add: literal_in_clause_subst literal_in_premise)

      have "is_maximal\<^sub>l (literal \<cdot>l \<mu>) (premise \<cdot> \<mu>)"
        using is_maximal\<^sub>l_ground_subst_stability'[OF 
            literal_\<mu>_in_premise 
            premise_grounding[unfolded \<mu>(2) clause_subst_compose]
            literal_\<gamma>_is_maximal[unfolded \<mu>(2) clause_subst_compose literal_subst_compose]
            ].

      then show ?thesis
        using select select\<^sub>G_empty
        by simp
    next
      case False

      have selected_grounding: "is_ground_clause (select premise \<cdot> \<mu> \<cdot> \<sigma>)"
        using select_subst(1)[OF premise_grounding]
        unfolding \<mu>(2) clause_subst_compose.

      note selected_subst =
        literal_selected[OF False, THEN maximal\<^sub>l_in_clause, THEN literal_in_clause_subst]

      have "is_maximal\<^sub>l (literal \<cdot>l \<gamma>) (select premise \<cdot> \<gamma>)"
        using False ground_eq_resolutionI(3) 
        unfolding ground_eq_resolutionI(2) is_maximal_lit_iff_is_maximal\<^sub>l literal_\<gamma> select
        by presburger

      then have "is_maximal\<^sub>l (literal \<cdot>l \<mu>) (select premise \<cdot> \<mu>)"
        unfolding \<mu>(2) clause_subst_compose literal_subst_compose
        using is_maximal\<^sub>l_ground_subst_stability'[OF selected_subst selected_grounding]
        by argo
        
      with False show ?thesis
        by blast
    qed
  next 
    show "welltyped_imgu typeof_fun \<V> term term' \<mu>"
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

  have "conclusion' \<cdot> \<mu> \<cdot> \<gamma> = conclusion \<cdot> \<gamma>"
    using conclusion'_\<gamma>  
    unfolding clause_subst_compose[symmetric] \<mu>_\<gamma>.

  moreover then have 
    "Infer [premise\<^sub>G] conclusion\<^sub>G \<in> inference_groundings (Infer [premise] (conclusion' \<cdot> \<mu>))"
    using ground_eq_resolution conclusion_grounding premise_grounding
    unfolding 
      clause_groundings_def 
      inference_groundings_def 
      ground.G_Inf_def 
      inferences_def 
      premise\<^sub>G
      conclusion\<^sub>G
    by auto

  ultimately show ?thesis
    using that[OF eq_resolution]
    by blast
qed

lemma eq_factoring_lifting:
  fixes 
    premise\<^sub>G conclusion\<^sub>G :: "'f gatom clause" and 
    premise conclusion :: "('f, 'v) atom clause" and
    \<gamma> :: "('f, 'v) subst"
  defines 
    premise\<^sub>G [simp]: "premise\<^sub>G \<equiv> to_ground_clause (premise \<cdot> \<gamma>)" and
    conclusion\<^sub>G [simp]: "conclusion\<^sub>G \<equiv> to_ground_clause (conclusion \<cdot> \<gamma>)"
  assumes
    premise_grounding: "is_ground_clause (premise \<cdot> \<gamma>)" and
    conclusion_grounding: "is_ground_clause (conclusion \<cdot> \<gamma>)" and
    select: "to_clause (select\<^sub>G premise\<^sub>G) = (select premise) \<cdot> \<gamma>" and
    ground_eq_factoring: "ground.ground_eq_factoring premise\<^sub>G conclusion\<^sub>G"
  obtains conclusion' 
  where
    "eq_factoring (premise, \<V>) (conclusion', \<V>)"
    "Infer [premise\<^sub>G] conclusion\<^sub>G \<in> inference_groundings (Infer [premise] conclusion')"
    "conclusion' \<cdot> \<gamma> = conclusion \<cdot> \<gamma>"
  using ground_eq_factoring
proof(cases premise\<^sub>G conclusion\<^sub>G rule: ground.ground_eq_factoring.cases)
  case (ground_eq_factoringI literal\<^sub>G\<^sub>1 literal\<^sub>G\<^sub>2 premise'\<^sub>G term\<^sub>G\<^sub>1 term\<^sub>G\<^sub>2 term\<^sub>G\<^sub>3)

  have premise_not_empty: "premise \<noteq> {#}"
    using ground_eq_factoringI(1) empty_not_add_mset clause_subst_empty premise\<^sub>G
    by (metis to_clause_empty_mset to_clause_inverse)

  have select_empty: "select premise = {#}"
    using ground_eq_factoringI(4) select clause_subst_empty
    by auto

  have premise_\<gamma>: "premise \<cdot> \<gamma> = to_clause (add_mset literal\<^sub>G\<^sub>1 (add_mset literal\<^sub>G\<^sub>2 premise'\<^sub>G))"
    using ground_eq_factoringI(1) premise\<^sub>G
    by (metis premise_grounding to_ground_clause_inverse)

  obtain literal\<^sub>1 where literal\<^sub>1_maximal: 
    "is_maximal\<^sub>l literal\<^sub>1 premise" 
    "is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<gamma>) (premise \<cdot> \<gamma>)"
    using is_maximal\<^sub>l_ground_subst_stability[OF premise_not_empty premise_grounding]
    by blast

  have max_ground_literal: "is_maximal\<^sub>l (to_literal (term\<^sub>G\<^sub>1 \<approx> term\<^sub>G\<^sub>2)) (premise \<cdot> \<gamma>)"
    using ground_eq_factoringI(5)
    unfolding 
      is_maximal_lit_iff_is_maximal\<^sub>l 
      ground_eq_factoringI(2) 
      premise\<^sub>G 
      to_ground_clause_inverse[OF premise_grounding].

  have literal\<^sub>1_\<gamma>: "literal\<^sub>1 \<cdot>l \<gamma> = to_literal literal\<^sub>G\<^sub>1"
    using 
      unique_maximal_in_ground_clause[OF premise_grounding literal\<^sub>1_maximal(2) max_ground_literal]
      ground_eq_factoringI(2)
    by blast

  then have "is_pos literal\<^sub>1"
    unfolding ground_eq_factoringI(2)
    using to_literal_stable subst_pos_stable
    by (metis literal.disc(1))

  with literal\<^sub>1_\<gamma> obtain term\<^sub>1 term\<^sub>1' where 
    literal\<^sub>1_terms: "literal\<^sub>1 = term\<^sub>1 \<approx> term\<^sub>1'" and
    term\<^sub>G\<^sub>1_term\<^sub>1: "to_term term\<^sub>G\<^sub>1 = term\<^sub>1 \<cdot>t \<gamma>"
    unfolding ground_eq_factoringI(2) to_atom_to_literal[symmetric] to_term_to_atom[symmetric]
    using obtain_from_pos_literal_subst[of literal\<^sub>1]
    by metis

  obtain premise'' where premise'': "premise = add_mset literal\<^sub>1 premise''"
    using maximal\<^sub>l_in_clause[OF literal\<^sub>1_maximal(1)]
    by (meson multi_member_split)

  then have premise''_\<gamma>: "premise'' \<cdot> \<gamma> =  add_mset (to_literal literal\<^sub>G\<^sub>2) (to_clause premise'\<^sub>G)"
    using premise_\<gamma> 
    unfolding to_clause_add_mset literal\<^sub>1_\<gamma>[symmetric]
    by (simp add: subst_clause_add_mset)

  then obtain literal\<^sub>2 where literal\<^sub>2:
    "literal\<^sub>2 \<cdot>l \<gamma> = to_literal literal\<^sub>G\<^sub>2"
    "literal\<^sub>2 \<in># premise''"
    unfolding subst_clause_def
    using msed_map_invR by force

  then have "is_pos literal\<^sub>2"
    unfolding ground_eq_factoringI(3)
    using to_literal_stable subst_pos_stable
    by (metis literal.disc(1))

  with literal\<^sub>2 obtain term\<^sub>2 term\<^sub>2' where 
    literal\<^sub>2_terms: "literal\<^sub>2 = term\<^sub>2 \<approx> term\<^sub>2'" and
    term\<^sub>G\<^sub>1_term\<^sub>2: "to_term term\<^sub>G\<^sub>1 = term\<^sub>2 \<cdot>t \<gamma>"
    unfolding ground_eq_factoringI(3) to_atom_to_literal[symmetric] to_term_to_atom[symmetric]
    using obtain_from_pos_literal_subst[of literal\<^sub>2]
    by metis

  have term\<^sub>1_term\<^sub>2: "term\<^sub>1 \<cdot>t \<gamma> = term\<^sub>2 \<cdot>t \<gamma>"
    using term\<^sub>G\<^sub>1_term\<^sub>1 term\<^sub>G\<^sub>1_term\<^sub>2
    by argo

  then obtain \<mu> \<sigma> where \<mu>: "term_subst.is_imgu \<mu> {{term\<^sub>1, term\<^sub>2}}" "\<gamma> = \<mu> \<odot> \<sigma>"
    using imgu_exists
    by blast

  have term\<^sub>G\<^sub>2_term\<^sub>1': "to_term term\<^sub>G\<^sub>2 = term\<^sub>1' \<cdot>t \<gamma>"
    using literal\<^sub>1_\<gamma> term\<^sub>G\<^sub>1_term\<^sub>1 
    unfolding 
      literal\<^sub>1_terms 
      ground_eq_factoringI(2) 
      to_literal_def 
      to_atom_def 
      subst_literal_def
      subst_atom_def 
    by auto

  have term\<^sub>G\<^sub>3_term\<^sub>2': "to_term term\<^sub>G\<^sub>3 = term\<^sub>2' \<cdot>t \<gamma>"
    using literal\<^sub>2 term\<^sub>G\<^sub>1_term\<^sub>2
    unfolding 
      literal\<^sub>2_terms 
      ground_eq_factoringI(3) 
      to_literal_def 
      to_atom_def 
      subst_literal_def
      subst_atom_def 
    by auto

  obtain premise' where premise: "premise = add_mset literal\<^sub>1 (add_mset literal\<^sub>2 premise')" 
    using literal\<^sub>2(2) maximal\<^sub>l_in_clause[OF  literal\<^sub>1_maximal(1)] premise''
    by (metis multi_member_split)

  then have premise'_\<gamma>: "premise' \<cdot> \<gamma> = to_clause premise'\<^sub>G"
    using premise''_\<gamma>  premise''
    unfolding literal\<^sub>2(1)[symmetric]
    by (simp add: subst_clause_add_mset)

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
      using literal\<^sub>1_maximal(1) literal_in_clause_subst maximal\<^sub>l_in_clause by blast

    have "is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<mu>) (premise \<cdot> \<mu>)"
      using is_maximal\<^sub>l_ground_subst_stability'[OF 
          literal\<^sub>1_\<mu>_in_premise 
          premise_grounding[unfolded \<mu>(2) clause_subst_compose]
          literal\<^sub>1_maximal(2)[unfolded \<mu>(2) clause_subst_compose literal_subst_compose]
          ].

    then show "is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<mu>) (premise \<cdot> \<mu>)"
      by blast
  next
    have term_groundings: "is_ground_term (term\<^sub>1' \<cdot>t \<mu> \<cdot>t \<sigma>)" "is_ground_term (term\<^sub>1 \<cdot>t \<mu> \<cdot>t \<sigma>)" 
      unfolding 
        term_subst_compose[symmetric] 
        \<mu>(2)[symmetric]
        term\<^sub>G\<^sub>1_term\<^sub>1[symmetric] 
        term\<^sub>G\<^sub>2_term\<^sub>1'[symmetric] 
      using ground_term_is_ground
      by simp_all

    have "term\<^sub>1' \<cdot>t \<mu> \<cdot>t \<sigma> \<prec>\<^sub>t term\<^sub>1 \<cdot>t \<mu> \<cdot>t \<sigma>"
      using ground_eq_factoringI(6)[unfolded 
          less\<^sub>t\<^sub>G_def 
          term\<^sub>G\<^sub>1_term\<^sub>1 
          term\<^sub>G\<^sub>2_term\<^sub>1'
          \<mu>(2) 
          term_subst_compose
          ].

    then show "\<not> term\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t term\<^sub>1' \<cdot>t \<mu>"
      using less\<^sub>t_less_eq\<^sub>t_ground_subst_stability[OF term_groundings]
      by blast
  next 
    show "term_subst.is_imgu \<mu> {{term\<^sub>1, term\<^sub>2}}"
      using \<mu>(1).
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

  have "conclusion \<cdot> \<gamma> = 
      add_mset (to_term term\<^sub>G\<^sub>2 !\<approx> to_term term\<^sub>G\<^sub>3) 
        (add_mset (to_term term\<^sub>G\<^sub>1 \<approx> to_term term\<^sub>G\<^sub>3) (to_clause premise'\<^sub>G))"
    using ground_eq_factoringI(7) to_ground_clause_inverse[OF conclusion_grounding]
    unfolding to_term_to_atom to_atom_to_literal to_clause_add_mset[symmetric]
    by simp

  then have conclusion_\<gamma>: 
    "conclusion \<cdot> \<gamma> = add_mset (term\<^sub>1 \<approx> term\<^sub>2') (add_mset (term\<^sub>1' !\<approx> term\<^sub>2') premise') \<cdot> \<gamma>"
    unfolding 
      term\<^sub>G\<^sub>2_term\<^sub>1'
      term\<^sub>G\<^sub>3_term\<^sub>2'
      term\<^sub>G\<^sub>1_term\<^sub>1
      premise'_\<gamma>[symmetric]
      subst_clause_add_mset[symmetric]
      subst_literal[symmetric]
      subst_atom[symmetric]
    by (simp add: add_mset_commute)

  then have "?conclusion' \<cdot> \<mu> \<cdot> \<gamma> = conclusion \<cdot> \<gamma>"
    by (metis \<mu>_\<gamma> clause_subst_compose)

  moreover then have 
    "Infer [premise\<^sub>G] conclusion\<^sub>G \<in> inference_groundings (Infer [premise] (?conclusion' \<cdot> \<mu>))"
    using ground_eq_factoring conclusion_grounding premise_grounding
    unfolding 
      clause_groundings_def 
      inference_groundings_def 
      ground.G_Inf_def 
      inferences_def 
      premise\<^sub>G
      conclusion\<^sub>G
    by auto

  ultimately show ?thesis
    using that[OF eq_factoring]
    by blast
qed

(* TODO: Try to split up proof *)
lemma superposition_lifting:
  fixes 
    premise\<^sub>G\<^sub>1 premise\<^sub>G\<^sub>2 conclusion\<^sub>G :: "'f gatom clause" and 
    premise\<^sub>1 premise\<^sub>2 conclusion :: "('f, 'v) atom clause" and
    \<gamma> \<rho>\<^sub>1 \<rho>\<^sub>2 :: "('f, 'v) subst"
  defines 
    premise\<^sub>G\<^sub>1 [simp]: "premise\<^sub>G\<^sub>1 \<equiv> to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>)" and
    premise\<^sub>G\<^sub>2 [simp]: "premise\<^sub>G\<^sub>2 \<equiv> to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<gamma>)" and
    conclusion\<^sub>G [simp]: "conclusion\<^sub>G \<equiv> to_ground_clause (conclusion \<cdot> \<gamma>)" and
    premise_groundings [simp]: 
    "premise_groundings \<equiv> clause_groundings premise\<^sub>1 \<union> clause_groundings premise\<^sub>2" and
    \<iota>\<^sub>G [simp]: "\<iota>\<^sub>G \<equiv> Infer [premise\<^sub>G\<^sub>2, premise\<^sub>G\<^sub>1] conclusion\<^sub>G"
  assumes 
    renaming: 
    "term_subst.is_renaming \<rho>\<^sub>1" 
    "term_subst.is_renaming \<rho>\<^sub>2" 
    "vars_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter> vars_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2) = {}" and
    premise\<^sub>1_grounding: "is_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>)" and
    premise\<^sub>2_grounding: "is_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<gamma>)" and
    conclusion_grounding: "is_ground_clause (conclusion \<cdot> \<gamma>)" and
    select: 
    "to_clause (select\<^sub>G premise\<^sub>G\<^sub>1) = (select premise\<^sub>1) \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>"
    "to_clause (select\<^sub>G premise\<^sub>G\<^sub>2) = (select premise\<^sub>2) \<cdot> \<rho>\<^sub>2 \<cdot> \<gamma>" and
    ground_superposition: "ground.ground_superposition premise\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>1 conclusion\<^sub>G" and
    non_redundant: "\<iota>\<^sub>G \<notin> ground.Red_I premise_groundings"
  obtains conclusion' 
  where
    "superposition (premise\<^sub>2, \<V>) (premise\<^sub>1, \<V>) (conclusion', \<V>)"
    "\<iota>\<^sub>G \<in> inference_groundings (Infer [premise\<^sub>2, premise\<^sub>1] conclusion')"
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
    by (metis to_clause_empty_mset to_clause_inverse)

  have premise\<^sub>2_not_empty: "premise\<^sub>2 \<noteq> {#}"
    using ground_superpositionI(2) empty_not_add_mset clause_subst_empty premise\<^sub>G\<^sub>2
    by (metis to_clause_empty_mset to_clause_inverse)

  have premise\<^sub>1_\<gamma>: "premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma> = to_clause (add_mset literal\<^sub>G\<^sub>1 premise\<^sub>G\<^sub>1')"
    using ground_superpositionI(1) premise\<^sub>G\<^sub>1
    by (metis premise\<^sub>1_grounding to_ground_clause_inverse)

  have premise\<^sub>2_\<gamma>: "premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<gamma> = to_clause (add_mset literal\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>2')"
    using ground_superpositionI(2) premise\<^sub>G\<^sub>2
    by (metis premise\<^sub>2_grounding to_ground_clause_inverse)

  let ?select\<^sub>G_empty = "select\<^sub>G (to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>)) = {#}"
  let ?select\<^sub>G_not_empty = "select\<^sub>G (to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>)) \<noteq> {#}"

  have pos_literal\<^sub>G\<^sub>1_is_strictly_maximal\<^sub>l: 
    "is_strictly_maximal\<^sub>l (to_literal literal\<^sub>G\<^sub>1) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)" if "\<P>\<^sub>G = Pos"
    using ground_superpositionI(9) that
    unfolding is_strictly_maximal\<^sub>G\<^sub>l_iff_is_strictly_maximal\<^sub>l
    by(simp add: premise\<^sub>1_grounding)

  have neg_literal\<^sub>G\<^sub>1_is_maximal\<^sub>l: 
    "is_maximal\<^sub>l (to_literal literal\<^sub>G\<^sub>1) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)" if ?select\<^sub>G_empty
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
    by auto

  obtain pos_literal\<^sub>1 where
    "is_strictly_maximal\<^sub>l pos_literal\<^sub>1 premise\<^sub>1"
    "pos_literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma> = to_literal literal\<^sub>G\<^sub>1" 
  if "\<P>\<^sub>G = Pos"
    using is_strictly_maximal\<^sub>l_ground_subst_stability[OF 
        premise\<^sub>1_grounding[folded clause_subst_compose] 
        pos_literal\<^sub>G\<^sub>1_is_strictly_maximal\<^sub>l
        ]
    by blast

  moreover then have "pos_literal\<^sub>1 \<in># premise\<^sub>1" if "\<P>\<^sub>G = Pos"
    using that strictly_maximal\<^sub>l_in_clause by fastforce

  moreover obtain neg_max_literal\<^sub>1 where
    "is_maximal\<^sub>l neg_max_literal\<^sub>1 premise\<^sub>1"
    "neg_max_literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma> = to_literal literal\<^sub>G\<^sub>1" 
  if "\<P>\<^sub>G = Neg" ?select\<^sub>G_empty
    using 
      is_maximal\<^sub>l_ground_subst_stability[OF 
        premise\<^sub>1_not_empty 
        premise\<^sub>1_grounding[folded clause_subst_compose]
        ]
      neg_literal\<^sub>G\<^sub>1_is_maximal\<^sub>l
    by (metis clause_subst_compose premise\<^sub>1_grounding unique_maximal_in_ground_clause)

  moreover then have "neg_max_literal\<^sub>1 \<in># premise\<^sub>1" if "\<P>\<^sub>G = Neg" ?select\<^sub>G_empty
    using that maximal\<^sub>l_in_clause by fastforce

  moreover obtain neg_selected_literal\<^sub>1 where
    "is_maximal\<^sub>l neg_selected_literal\<^sub>1 (select premise\<^sub>1)"
    "neg_selected_literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma> = to_literal literal\<^sub>G\<^sub>1" 
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
      by (metis (full_types) clause_subst_compose clause_subst_empty(2) ground_clause_is_ground 
          image_mset_is_empty_iff to_clause_def)
  qed

  moreover then have "neg_selected_literal\<^sub>1 \<in># premise\<^sub>1" if "\<P>\<^sub>G = Neg" ?select\<^sub>G_not_empty 
    using that
    by (meson maximal\<^sub>l_in_clause mset_subset_eqD select_subset)

  ultimately obtain literal\<^sub>1 where
    literal\<^sub>1_\<gamma>: "literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma> = to_literal literal\<^sub>G\<^sub>1" and
    literal\<^sub>1_in_premise\<^sub>1: "literal\<^sub>1 \<in># premise\<^sub>1" and
    literal\<^sub>1_is_strictly_maximal: "\<P>\<^sub>G = Pos \<Longrightarrow> is_strictly_maximal\<^sub>l literal\<^sub>1 premise\<^sub>1" and
    literal\<^sub>1_is_maximal: "\<P>\<^sub>G = Neg \<Longrightarrow> ?select\<^sub>G_empty \<Longrightarrow> is_maximal\<^sub>l literal\<^sub>1 premise\<^sub>1" and
    literal\<^sub>1_selected: "\<P>\<^sub>G = Neg \<Longrightarrow> ?select\<^sub>G_not_empty \<Longrightarrow> is_maximal\<^sub>l literal\<^sub>1 (select premise\<^sub>1)"
    by (metis ground_superpositionI(9) literals_distinct(1))

  then have literal\<^sub>1_grounding: "is_ground_literal (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma>)"
    by simp

  have literal\<^sub>G\<^sub>2_is_strictly_maximal\<^sub>l: 
    "is_strictly_maximal\<^sub>l (to_literal literal\<^sub>G\<^sub>2) (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>)"
    using ground_superpositionI(11)
    unfolding is_strictly_maximal\<^sub>G\<^sub>l_iff_is_strictly_maximal\<^sub>l
    by (simp add: premise\<^sub>2_grounding)

  obtain literal\<^sub>2 where 
    literal\<^sub>2_strictly_maximal: "is_strictly_maximal\<^sub>l literal\<^sub>2 premise\<^sub>2" and
    literal\<^sub>2_\<gamma>: "literal\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<odot> \<gamma> = to_literal literal\<^sub>G\<^sub>2"
    using is_strictly_maximal\<^sub>l_ground_subst_stability[OF 
        premise\<^sub>2_grounding[folded clause_subst_compose] 
        literal\<^sub>G\<^sub>2_is_strictly_maximal\<^sub>l
        ].

  then have literal\<^sub>2_in_premise\<^sub>2: "literal\<^sub>2 \<in># premise\<^sub>2" 
    using strictly_maximal\<^sub>l_in_clause by blast

  have literal\<^sub>2_grounding: "is_ground_literal (literal\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<odot> \<gamma>)"
    using literal\<^sub>2_\<gamma> by simp

  obtain premise\<^sub>1' where premise\<^sub>1: "premise\<^sub>1 = add_mset literal\<^sub>1 premise\<^sub>1'"
    by (meson literal\<^sub>1_in_premise\<^sub>1 multi_member_split)

  then have premise\<^sub>1'_\<gamma>: "premise\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma> = to_clause premise\<^sub>G\<^sub>1'"
    using premise\<^sub>1_\<gamma>  
    unfolding to_clause_add_mset literal\<^sub>1_\<gamma>[symmetric]
    by (simp add: subst_clause_add_mset)

  obtain premise\<^sub>2' where premise\<^sub>2: "premise\<^sub>2 = add_mset literal\<^sub>2 premise\<^sub>2'"
    by (meson literal\<^sub>2_in_premise\<^sub>2 multi_member_split)

  then have premise\<^sub>2'_\<gamma>: "premise\<^sub>2' \<cdot> \<rho>\<^sub>2 \<cdot> \<gamma> = to_clause premise\<^sub>G\<^sub>2'"
    using premise\<^sub>2_\<gamma>  
    unfolding to_clause_add_mset literal\<^sub>2_\<gamma>[symmetric]
    by (simp add: subst_clause_add_mset)

  let ?\<P> = "if \<P>\<^sub>G = Pos then Pos else Neg"

  have [simp]: "\<P>\<^sub>G \<noteq> Pos \<longleftrightarrow> \<P>\<^sub>G = Neg"
    using ground_superpositionI(4) 
    by auto

  have "literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<gamma> = ?\<P> (Upair (to_context context\<^sub>G)\<langle>to_term term\<^sub>G\<^sub>1\<rangle> (to_term term\<^sub>G\<^sub>2))"
    using literal\<^sub>1_\<gamma>
    unfolding ground_superpositionI(5)
    by (simp add: to_atom_to_literal to_term_to_atom ground_term_with_context(3))

  then obtain term\<^sub>1_with_context term\<^sub>1' where 
    literal\<^sub>1: "literal\<^sub>1 = ?\<P> (Upair term\<^sub>1_with_context term\<^sub>1')" and
    term\<^sub>1'_\<gamma>: "term\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma> = to_term term\<^sub>G\<^sub>2" and
    term\<^sub>1_with_context_\<gamma>: "term\<^sub>1_with_context \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma> = (to_context context\<^sub>G)\<langle>to_term term\<^sub>G\<^sub>1\<rangle>"
    by (smt (verit) obtain_from_literal_subst)

  from literal\<^sub>2_\<gamma> have "literal\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<gamma> = to_term term\<^sub>G\<^sub>1 \<approx> to_term term\<^sub>G\<^sub>3"
    unfolding ground_superpositionI(6) to_term_to_atom to_atom_to_literal(2) literal_subst_compose.

  then obtain term\<^sub>2 term\<^sub>2' where 
    literal\<^sub>2: "literal\<^sub>2 = term\<^sub>2 \<approx> term\<^sub>2'" and
    term\<^sub>2_\<gamma>: "term\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<gamma> = to_term term\<^sub>G\<^sub>1" and     
    term\<^sub>2'_\<gamma>: "term\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<gamma> = to_term term\<^sub>G\<^sub>3"
    using obtain_from_pos_literal_subst
    by metis

  let ?inference_into_var = "\<nexists>context\<^sub>1 term\<^sub>1. 
      term\<^sub>1_with_context = context\<^sub>1\<langle>term\<^sub>1\<rangle> \<and> 
      term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma> = to_term term\<^sub>G\<^sub>1 \<and> 
      context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma> = to_context context\<^sub>G \<and> 
      is_Fun term\<^sub>1"

  have inference_into_var_is_redundant: 
    "?inference_into_var \<Longrightarrow> ground.redundant_infer premise_groundings \<iota>\<^sub>G"
  proof-
    assume inference_into_var: ?inference_into_var

    obtain term\<^sub>x context\<^sub>x context\<^sub>x' where
      term\<^sub>1_with_context: "term\<^sub>1_with_context = context\<^sub>x\<langle>term\<^sub>x\<rangle>" and
      is_Var_term\<^sub>x: "is_Var term\<^sub>x" and
      "to_context context\<^sub>G = (context\<^sub>x \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma>) \<circ>\<^sub>c context\<^sub>x'"
    proof-  
      from inference_into_var term\<^sub>1_with_context_\<gamma> 
      have 
        "\<exists>term\<^sub>x context\<^sub>x context\<^sub>x'. 
        term\<^sub>1_with_context = context\<^sub>x\<langle>term\<^sub>x\<rangle> \<and> 
        is_Var term\<^sub>x \<and> 
        to_context context\<^sub>G = (context\<^sub>x \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma>) \<circ>\<^sub>c context\<^sub>x'"
      proof(induction term\<^sub>1_with_context arbitrary: context\<^sub>G)
        case (Var x)
        show ?case
        proof(intro exI conjI)
          show
            "Var x = \<box>\<langle>Var x\<rangle>"
            "is_Var (Var x)"
            "to_context context\<^sub>G = (\<box> \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma>) \<circ>\<^sub>c to_context context\<^sub>G"
            by simp_all
        qed
      next
        case (Fun f terms)

        then have "context\<^sub>G \<noteq> GHole"
          by (metis ctxt_apply_term.simps(1) ctxt_of_gctxt.simps(1) subst_apply_ctxt.simps(1) 
              term.disc(2))

        then obtain terms\<^sub>G\<^sub>1 context\<^sub>G' terms\<^sub>G\<^sub>2 where
          context\<^sub>G: "context\<^sub>G = GMore f terms\<^sub>G\<^sub>1 context\<^sub>G' terms\<^sub>G\<^sub>2"
          using Fun(3)
          by(cases context\<^sub>G) auto

        have terms_\<gamma>: 
          "map (\<lambda>term. term \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>) terms = 
            map to_term terms\<^sub>G\<^sub>1 @ (to_context context\<^sub>G')\<langle>to_term term\<^sub>G\<^sub>1\<rangle> # map to_term terms\<^sub>G\<^sub>2"
          using Fun(3)
          unfolding context\<^sub>G
          by(simp add: comp_def)

        then obtain terms\<^sub>1 "term" terms\<^sub>2 where 
          terms: "terms = terms\<^sub>1 @ term # terms\<^sub>2" and
          terms\<^sub>1_\<gamma>: "map (\<lambda>term. term \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>) terms\<^sub>1 = map to_term terms\<^sub>G\<^sub>1" and
          terms\<^sub>2_\<gamma>: "map (\<lambda>term. term \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>) terms\<^sub>2 = map to_term terms\<^sub>G\<^sub>2"     
          by (smt (z3) append_eq_map_conv map_eq_Cons_D)

        with terms_\<gamma> 
        have term_\<gamma>: "term \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma> = (to_context context\<^sub>G')\<langle>to_term term\<^sub>G\<^sub>1\<rangle>"
          by simp

        show ?case
        proof(cases "is_ground_term term")
          case True

          with term_\<gamma> 
          obtain term\<^sub>1 context\<^sub>1 where
            "term = context\<^sub>1\<langle>term\<^sub>1\<rangle>"
            "term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma> = to_term term\<^sub>G\<^sub>1" 
            "context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma> = to_context context\<^sub>G'" 
            "is_Fun term\<^sub>1"
            by (metis Term.ground_vars_term_empty ground_context_is_ground ground_subst_apply 
                ground_term_is_ground subst_ground_context gterm_is_fun)

          moreover then have "Fun f terms = (More f terms\<^sub>1 context\<^sub>1 terms\<^sub>2)\<langle>term\<^sub>1\<rangle>"
            unfolding terms
            by auto

          ultimately have 
            "\<exists>context\<^sub>1 term\<^sub>1. 
            Fun f terms = context\<^sub>1\<langle>term\<^sub>1\<rangle> \<and> 
            term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma> = to_term term\<^sub>G\<^sub>1 \<and> 
            context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma> = to_context context\<^sub>G \<and> 
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
            term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma> = to_term term\<^sub>G\<^sub>1 \<and> 
            context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma> = to_context context\<^sub>G' \<and> 
            is_Fun term\<^sub>1"
          proof(rule notI)
            assume 
              "\<exists>context\<^sub>1 term\<^sub>1. 
              term = context\<^sub>1\<langle>term\<^sub>1\<rangle> \<and> 
              term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma> = to_term term\<^sub>G\<^sub>1 \<and> 
              context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma> = to_context context\<^sub>G' \<and> 
              is_Fun term\<^sub>1"

            then obtain context\<^sub>1 term\<^sub>1 where
              "term": "term = context\<^sub>1\<langle>term\<^sub>1\<rangle>"
              "term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma> = to_term term\<^sub>G\<^sub>1"
              "context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma> = to_context context\<^sub>G'"
              "is_Fun term\<^sub>1"
              by blast

            then have 
              "\<exists>context\<^sub>1 term\<^sub>1. 
              Fun f terms = context\<^sub>1\<langle>term\<^sub>1\<rangle> \<and> 
              term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma> = to_term term\<^sub>G\<^sub>1 \<and> 
              context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma> = to_context context\<^sub>G \<and> 
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
            "to_context context\<^sub>G' = (context\<^sub>x \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma>) \<circ>\<^sub>c context\<^sub>x'"
            using Fun(1) term_\<gamma> by blast

          then have 
            "Fun f terms = (More f terms\<^sub>1 context\<^sub>x terms\<^sub>2)\<langle>term\<^sub>x\<rangle>"
            "is_Var term\<^sub>x" 
            "to_context context\<^sub>G = (More f terms\<^sub>1 context\<^sub>x terms\<^sub>2 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma>) \<circ>\<^sub>c context\<^sub>x'"
            by(auto simp: terms terms\<^sub>1_\<gamma> terms\<^sub>2_\<gamma> context\<^sub>G comp_def)

          then show ?thesis
            by blast
        qed
      qed

      then show ?thesis
        using that
        by blast
    qed

    then have context\<^sub>G: "to_context context\<^sub>G = context\<^sub>x \<circ>\<^sub>c context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma>"
      using ground_context_subst[OF ground_context_is_ground] ctxt_compose_subst_compose_distrib
      by metis

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

    show ?thesis
    proof(unfold ground.redundant_infer_def \<iota>\<^sub>G_parts, intro exI conjI)

      let ?update = "(context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma>)\<langle>to_term term\<^sub>G\<^sub>3\<rangle>"

      define \<gamma>' where
        \<gamma>': "\<gamma>' \<equiv> \<gamma>(var\<^sub>x := ?update)"

      have update_grounding: "is_ground_term ?update"
      proof-
        have "is_ground_context ((context\<^sub>x \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma>) \<circ>\<^sub>c (context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma>))"
          using ground_context_is_ground[of context\<^sub>G] context\<^sub>G
          by fastforce

        then show ?thesis
          using is_ground_context_context_compose1(2)
          by auto
      qed

      let ?premise\<^sub>1_\<gamma>' = "to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>')"
      have premise\<^sub>1_\<gamma>'_grounding: "is_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>')"
        using ground_clause_subst_upd[OF update_grounding premise\<^sub>1_grounding] 
        unfolding \<gamma>'
        by blast

      show "{?premise\<^sub>1_\<gamma>'} \<subseteq> premise_groundings"
        using premise\<^sub>1_\<gamma>'_grounding
        unfolding clause_groundings_def clause_subst_compose[symmetric] premise\<^sub>1 premise_groundings
        by blast

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

        let ?context\<^sub>x'_\<gamma> = "to_ground_context (context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma>)"
        note to_term_context =
          ground_term_with_context1[OF _ ground_term_is_ground, unfolded to_term_inverse]

        have term\<^sub>x_\<gamma>: "to_ground_term (term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>) = ?context\<^sub>x'_\<gamma>\<langle>term\<^sub>G\<^sub>1\<rangle>\<^sub>G"
          using term\<^sub>1_with_context_\<gamma> update_grounding 
          unfolding term\<^sub>1_with_context context\<^sub>G
          by(auto simp: to_term_context)

        have term\<^sub>x_\<gamma>': "to_ground_term (term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>') = ?context\<^sub>x'_\<gamma>\<langle>term\<^sub>G\<^sub>3\<rangle>\<^sub>G"
          using update_grounding
          unfolding var\<^sub>x[symmetric] \<gamma>'
          by(auto simp: to_term_context)

        have var\<^sub>x_\<gamma>_ground: "is_ground_term (Var var\<^sub>x \<cdot>t \<gamma>)"
          using term\<^sub>1_with_context_\<gamma>
          unfolding term\<^sub>1_with_context var\<^sub>x subst_apply_term_ctxt_apply_distrib
          by (metis ground_term_with_context_is_ground1 ground_term_with_context_is_ground(3))

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

          then have "?I \<TTurnstile>l to_ground_term (term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>) \<approx> to_ground_term (term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>')"
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

        have context\<^sub>x_grounding: "is_ground_context (context\<^sub>x \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma>)"
          using context\<^sub>G
          unfolding subst_compose_ctxt_compose_distrib
          by (metis ground_context_is_ground is_ground_context_context_compose1(1))

        have term\<^sub>x_grounding: "is_ground_term (term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>)"
          using term\<^sub>1_with_context_\<gamma>
          unfolding term\<^sub>1_with_context subst_apply_term_ctxt_apply_distrib
          by (metis ground_term_with_context_is_ground(1,3))

        have "(context\<^sub>x \<circ>\<^sub>c context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma>)\<langle>to_term term\<^sub>G\<^sub>3\<rangle> \<prec>\<^sub>t context\<^sub>x\<langle>term\<^sub>x\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>"
          using ground_superpositionI(8)
          unfolding 
            less\<^sub>t\<^sub>G_def 
            context\<^sub>G[symmetric] 
            term\<^sub>1_with_context[symmetric] 
            term\<^sub>1_with_context_\<gamma>
            less\<^sub>t_ground_context_compatible_iff[OF 
              ground_context_is_ground ground_term_is_ground ground_term_is_ground].

        then have update_smaller: "?update \<prec>\<^sub>t \<gamma> var\<^sub>x"
          unfolding 
            var\<^sub>x_\<gamma>
            subst_apply_term_ctxt_apply_distrib 
            subst_compose_ctxt_compose_distrib
            Subterm_and_Context.ctxt_ctxt_compose
          by(rule less\<^sub>t_ground_context_compatible'[OF 
                context\<^sub>x_grounding update_grounding term\<^sub>x_grounding])     

        have var\<^sub>x_in_literal\<^sub>1: "var\<^sub>x \<in> vars_literal (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1)"
          unfolding literal\<^sub>1 term\<^sub>1_with_context  vars_literal_def vars_atom_def 
          using var\<^sub>x
          by(auto simp: subst_literal subst_atom)

        have literal\<^sub>1_smaller: "literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<gamma>' \<prec>\<^sub>l literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<gamma>"
          unfolding \<gamma>'
          using less\<^sub>l_subst_upd[OF 
              update_grounding 
              update_smaller 
              literal\<^sub>1_grounding[unfolded literal_subst_compose] 
              var\<^sub>x_in_literal\<^sub>1
              ].

        have premise\<^sub>1'_grounding: "is_ground_clause (premise\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>)"
          using premise\<^sub>1'_\<gamma>
          by simp

        have premise\<^sub>1'_smaller: "premise\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>' \<preceq>\<^sub>c premise\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>"
          unfolding \<gamma>'
          using less\<^sub>c_subst_upd[of _ \<gamma>, OF update_grounding update_smaller premise\<^sub>1'_grounding]
          by(cases "var\<^sub>x \<in> vars_clause (premise\<^sub>1' \<cdot> \<rho>\<^sub>1)") simp_all

        have "?premise\<^sub>1_\<gamma>' \<prec>\<^sub>c\<^sub>G premise\<^sub>G\<^sub>1"
          using less\<^sub>c_add_mset[OF literal\<^sub>1_smaller premise\<^sub>1'_smaller]
          unfolding 
            less\<^sub>c\<^sub>G_less\<^sub>c 
            premise\<^sub>G\<^sub>1
            subst_clause_add_mset[symmetric]
            to_ground_clause_inverse[OF premise\<^sub>1_\<gamma>'_grounding]
            to_ground_clause_inverse[OF premise\<^sub>1_grounding]
          unfolding premise\<^sub>1.

        then show ?thesis
          by blast
      qed   
    qed
  qed

  obtain context\<^sub>1 term\<^sub>1 where 
    term\<^sub>1_with_context: "term\<^sub>1_with_context = context\<^sub>1\<langle>term\<^sub>1\<rangle>" and
    term\<^sub>1_\<gamma>: "term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma> = to_term term\<^sub>G\<^sub>1" and
    context\<^sub>1_\<gamma>: "context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma> = to_context context\<^sub>G" and
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
    term\<^sub>2'_with_context_\<gamma>: "term\<^sub>2'_with_context \<cdot>t \<gamma> = (to_context context\<^sub>G)\<langle>to_term term\<^sub>G\<^sub>3\<rangle>" and
    term\<^sub>2'_with_context: "term\<^sub>2'_with_context = (context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>term\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle>" 
    unfolding term\<^sub>2'_\<gamma>[symmetric] context\<^sub>1_\<gamma>[symmetric]
    by force

  have "term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma> = term\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<gamma>"
    unfolding term\<^sub>1_\<gamma> term\<^sub>2_\<gamma> ..

  then obtain \<mu> \<sigma> where
    \<mu>: "term_subst.is_imgu \<mu> {{term\<^sub>1 \<cdot>t \<rho>\<^sub>1, term\<^sub>2 \<cdot>t \<rho>\<^sub>2}}" "\<gamma> = \<mu> \<odot> \<sigma>"
    using imgu_exists
    by blast

  define conclusion' where 
    conclusion': "conclusion' \<equiv>
      add_mset (?\<P> (Upair term\<^sub>2'_with_context (term\<^sub>1' \<cdot>t \<rho>\<^sub>1))) (premise\<^sub>1' \<cdot> \<rho>\<^sub>1 + premise\<^sub>2' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu>"

  show ?thesis
  proof(rule that)
    show "superposition (premise\<^sub>2, \<V>) (premise\<^sub>1, \<V>) (conclusion', \<V>)"
    proof(rule superpositionI)
      show "term_subst.is_renaming \<rho>\<^sub>1"
        using renaming(1).
    next
      show "term_subst.is_renaming \<rho>\<^sub>2"
        using renaming(2).
    next 
      show "vars_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter> vars_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2) = {}"
        using renaming(3).
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
      note premises_to_ground_clause_inverse = assms(9, 10)[THEN to_ground_clause_inverse]  
      note premise_groundings = assms(10, 9)[unfolded \<mu>(2) clause_subst_compose]

      have "premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu> \<cdot> \<sigma> \<prec>\<^sub>c premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<cdot> \<sigma>"
        using ground_superpositionI(3)
        unfolding premise\<^sub>G\<^sub>1 premise\<^sub>G\<^sub>2 less\<^sub>c\<^sub>G_less\<^sub>c premises_to_ground_clause_inverse 
        unfolding \<mu>(2) clause_subst_compose.

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
          by(auto simp: subst_clause_def)

        moreover have "is_strictly_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu> \<cdot>l \<sigma>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<cdot> \<sigma>)"
          using True pos_literal\<^sub>G\<^sub>1_is_strictly_maximal\<^sub>l
          unfolding literal\<^sub>1_\<gamma>[symmetric] \<mu>(2)
          by force

        moreover then have "is_strictly_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>)"
          using 
            is_strictly_maximal\<^sub>l_ground_subst_stability'[OF
              _
              premise\<^sub>1_grounding[unfolded \<mu>(2) clause_subst_compose]
              ]
            literal_in_clause_subst
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
            by auto

          moreover have "is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu> \<cdot>l \<sigma>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<cdot> \<sigma>)"
            using neg_literal\<^sub>G\<^sub>1_is_maximal\<^sub>l[OF select\<^sub>G_empty]
            unfolding literal\<^sub>1_\<gamma>[symmetric] \<mu>(2)
            by simp

          moreover then have "is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>)"
            using 
              is_maximal\<^sub>l_ground_subst_stability'[OF 
                _  
                premise\<^sub>1_grounding[unfolded \<mu>(2) clause_subst_compose]
                ]
              literal_in_clause_subst
              literal\<^sub>1_in_premise\<^sub>1
            by blast

          ultimately show ?thesis
            using \<P>\<^sub>G_Neg
            by simp
        next
          case select\<^sub>G_not_empty: False

          have selected_grounding: "is_ground_clause (select premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<cdot> \<sigma>)"
            using select_subst(1)[OF premise\<^sub>1_grounding] select(1)
            unfolding \<mu>(2) clause_subst_compose
            by (metis ground_clause_is_ground)

          note selected_subst =
            literal\<^sub>1_selected[
              OF \<P>\<^sub>G_Neg select\<^sub>G_not_empty, 
              THEN maximal\<^sub>l_in_clause, 
              THEN literal_in_clause_subst] 

          have "is_maximal\<^sub>l (literal\<^sub>1  \<cdot>l \<rho>\<^sub>1 \<cdot>l \<gamma>) (select premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>)"  
            using select\<^sub>G_not_empty ground_superpositionI(9) \<P>\<^sub>G_Neg 
            unfolding is_maximal_lit_iff_is_maximal\<^sub>l literal\<^sub>1_\<gamma>[symmetric] select(1)
            by simp

          then have "is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) ((select premise\<^sub>1) \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>)"
            using is_maximal\<^sub>l_ground_subst_stability'[OF _ selected_grounding] selected_subst
            by (metis \<mu>(2) clause_subst_compose literal_subst_compose)

          with select\<^sub>G_not_empty \<P>\<^sub>G_Neg show ?thesis
            by simp
        qed
      qed
    next
      show "select premise\<^sub>2 = {#}"
        using clause_subst_empty ground_superpositionI(10) select(2)
        by auto
    next 
      have "is_strictly_maximal\<^sub>l (literal\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu> \<cdot>l \<sigma>) (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu> \<cdot> \<sigma>)"
        using literal\<^sub>G\<^sub>2_is_strictly_maximal\<^sub>l
        unfolding literal\<^sub>2_\<gamma>[symmetric] \<mu>(2)
        by simp

      then show "is_strictly_maximal\<^sub>l (literal\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu>) (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>)"
        using 
          is_strictly_maximal\<^sub>l_ground_subst_stability'[OF 
            _  premise\<^sub>2_grounding[unfolded \<mu>(2) clause_subst_compose]]
          literal\<^sub>2_in_premise\<^sub>2
          literal_in_clause_subst
        by blast
    next
      have term_groundings: 
        "is_ground_term (term\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<sigma>)" 
        "is_ground_term (context\<^sub>1\<langle>term\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<sigma>)" 
        unfolding 
          term\<^sub>1_with_context[symmetric]  
          term\<^sub>1_with_context_\<gamma>[unfolded \<mu>(2) term_subst_compose]
          term\<^sub>1'_\<gamma>[unfolded \<mu>(2) term_subst_compose]
        using ground_term_with_context_is_ground(1)
        by simp_all

      have "term\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<sigma> \<prec>\<^sub>t context\<^sub>1\<langle>term\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<sigma>"
        using ground_superpositionI(7) 
        unfolding 
          term\<^sub>1'_\<gamma>[unfolded \<mu>(2) term_subst_compose]
          term\<^sub>1_with_context[symmetric]
          term\<^sub>1_with_context_\<gamma>[unfolded \<mu>(2) term_subst_compose]
          less\<^sub>t\<^sub>G_def
          ground_term_with_context(3).

      then show "\<not> context\<^sub>1\<langle>term\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t term\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu>"
        using less\<^sub>t_less_eq\<^sub>t_ground_subst_stability[OF term_groundings]
        by blast
    next
      have term_groundings: 
        "is_ground_term (term\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<sigma>)"
        "is_ground_term (term\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<sigma>)"
        unfolding
          term\<^sub>2_\<gamma>[unfolded \<mu>(2) term_subst_compose]
          term\<^sub>2'_\<gamma>[unfolded \<mu>(2) term_subst_compose]
        by simp_all

      have "term\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<sigma> \<prec>\<^sub>t term\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<sigma>"
        using ground_superpositionI(8)
        unfolding
          term\<^sub>2_\<gamma>[unfolded \<mu>(2) term_subst_compose]       
          term\<^sub>2'_\<gamma>[unfolded \<mu>(2) term_subst_compose]
          less\<^sub>t\<^sub>G_def.

      then show "\<not> term\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<preceq>\<^sub>t term\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu>"
        using less\<^sub>t_less_eq\<^sub>t_ground_subst_stability[OF term_groundings]
        by blast
    next
      show 
        "conclusion' = add_mset (?\<P> (Upair (context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>term\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> (term\<^sub>1' \<cdot>t \<rho>\<^sub>1))) 
          (premise\<^sub>1' \<cdot> \<rho>\<^sub>1 + premise\<^sub>2' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu>"
        unfolding term\<^sub>2'_with_context conclusion'..
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
              add_mset (?\<P> (Upair (to_context context\<^sub>G)\<langle>to_term term\<^sub>G\<^sub>3\<rangle> (to_term term\<^sub>G\<^sub>2))) 
                (to_clause premise\<^sub>G\<^sub>1' + to_clause premise\<^sub>G\<^sub>2')"
        using ground_superpositionI(4, 12) to_ground_clause_inverse[OF conclusion_grounding] 
        unfolding ground_term_with_context(3) to_term_to_atom
        by(auto simp: to_atom_to_literal to_clause_add_mset)

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
          clause_subst_compose[symmetric]
          \<mu>_\<gamma>
        by(simp add: subst_clause_add_mset subst_literal)
    qed

    show "\<iota>\<^sub>G \<in> inference_groundings (Infer [premise\<^sub>2, premise\<^sub>1] conclusion')"
    proof-
      have "is_inference_grounding (Infer [premise\<^sub>2, premise\<^sub>1] conclusion') \<iota>\<^sub>G \<gamma> \<rho>\<^sub>1 \<rho>\<^sub>2"
        using conclusion'_\<gamma> ground_superposition
        unfolding ground.G_Inf_def \<iota>\<^sub>G
        by(auto simp: renaming premise\<^sub>1_grounding premise\<^sub>2_grounding conclusion_grounding)

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
    "\<iota>\<^sub>G \<in> ground.Inf_from_q select\<^sub>G (\<Union>(clause_groundings ` premises))"
    "subst_stability_on premises"
  obtains \<iota> where 
    "\<iota> \<in> Inf_from premises" 
    "\<iota>\<^sub>G \<in> inference_groundings \<iota>"
proof-
  obtain premise\<^sub>G conclusion\<^sub>G where 
    \<iota>\<^sub>G : "\<iota>\<^sub>G = Infer [premise\<^sub>G] conclusion\<^sub>G" and
    ground_eq_resolution: "ground.ground_eq_resolution premise\<^sub>G conclusion\<^sub>G"
    using assms(1)
    by blast

  have premise\<^sub>G_in_groundings: "premise\<^sub>G \<in> \<Union>(clause_groundings ` premises)"
    using assms(2)
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
    by simp

  obtain premise conclusion \<gamma> where
    "to_clause premise\<^sub>G = premise \<cdot> \<gamma>" and
    "to_clause conclusion\<^sub>G = conclusion \<cdot> \<gamma>" and
    select: "to_clause (select\<^sub>G premise\<^sub>G) = select premise \<cdot> \<gamma>" and
    premise_in_premises: "premise \<in> premises"
    using assms(2, 3) premise\<^sub>G_in_groundings
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
    by (metis (no_types, lifting) select_subst(1) ground_clause_is_ground subst_ground_clause 
          to_clause_inverse to_ground_clause_inverse)
    
  then have
    premise_grounding: "is_ground_clause (premise \<cdot> \<gamma>)" and
    premise\<^sub>G: "premise\<^sub>G = to_ground_clause (premise \<cdot> \<gamma>)" and
    conclusion_grounding: "is_ground_clause (conclusion \<cdot> \<gamma>)" and
    conclusion\<^sub>G: "conclusion\<^sub>G = to_ground_clause (conclusion \<cdot> \<gamma>)"
    using ground_clause_is_ground to_clause_inverse
    by(smt(verit))+

  obtain conclusion' \<V> where
    eq_resolution: "eq_resolution (premise, \<V>) (conclusion', \<V>)" and
    \<iota>\<^sub>G: "\<iota>\<^sub>G = Infer [to_ground_clause (premise \<cdot> \<gamma>)] (to_ground_clause (conclusion' \<cdot> \<gamma>))" and
    inference_groundings: "\<iota>\<^sub>G \<in> inference_groundings (Infer [premise] conclusion')" and  
    conclusion'_conclusion: "conclusion' \<cdot> \<gamma> = conclusion \<cdot> \<gamma>"
    using
      eq_resolution_lifting[OF 
        premise_grounding 
        conclusion_grounding 
        select[unfolded premise\<^sub>G] 
        ground_eq_resolution[unfolded premise\<^sub>G conclusion\<^sub>G]]
    unfolding premise\<^sub>G conclusion\<^sub>G \<iota>\<^sub>G
    by metis

  let ?\<iota> = "Infer [premise] conclusion'"

  show ?thesis
  proof(rule that)
    show "?\<iota> \<in> Inf_from premises"
      using premise_in_premises eq_resolution
      unfolding Inf_from_def inferences_def inference_system.Inf_from_def
      (* TODO *) 
      apply auto
      by (metis (no_types, opaque_lifting) fst_conv list.simps(8) list.simps(9))
      

    show "\<iota>\<^sub>G \<in> inference_groundings ?\<iota>"
      using inference_groundings.
  qed
qed 

lemma eq_factoring_ground_instance: 
  assumes 
    "\<iota>\<^sub>G \<in> ground.eq_factoring_inferences"
    "\<iota>\<^sub>G \<in> ground.Inf_from_q select\<^sub>G (\<Union>(clause_groundings ` premises))" 
    "subst_stability_on premises"
  obtains \<iota> where 
    "\<iota> \<in> Inf_from premises" 
    "\<iota>\<^sub>G \<in> inference_groundings \<iota>"
proof-
  obtain premise\<^sub>G conclusion\<^sub>G where 
    \<iota>\<^sub>G : "\<iota>\<^sub>G = Infer [premise\<^sub>G] conclusion\<^sub>G" and
    ground_eq_factoring: "ground.ground_eq_factoring premise\<^sub>G conclusion\<^sub>G"
    using assms(1)
    by blast

  have premise\<^sub>G_in_groundings: "premise\<^sub>G \<in> \<Union>(clause_groundings ` premises)"
    using assms(2)
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
    by simp

  obtain premise conclusion \<gamma> where
    "to_clause premise\<^sub>G = premise \<cdot> \<gamma>" and
    "to_clause conclusion\<^sub>G = conclusion \<cdot> \<gamma>" and
    select: "to_clause (select\<^sub>G (to_ground_clause (premise \<cdot> \<gamma>))) = select premise \<cdot> \<gamma>" and
    premise_in_premises: "premise \<in> premises"
    using assms(2, 3) premise\<^sub>G_in_groundings
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
    by (metis (no_types, opaque_lifting) ground_clause_is_ground select_subst1 subst_ground_clause 
          to_ground_clause_inverse)

  then have 
    premise_grounding: "is_ground_clause (premise \<cdot> \<gamma>)" and 
    premise\<^sub>G: "premise\<^sub>G = to_ground_clause (premise \<cdot> \<gamma>)" and 
    conclusion_grounding: "is_ground_clause (conclusion \<cdot> \<gamma>)" and
    conclusion\<^sub>G: "conclusion\<^sub>G = to_ground_clause (conclusion \<cdot> \<gamma>)"
    by (smt(verit) ground_clause_is_ground to_clause_inverse)+

  obtain conclusion' \<V> where 
    eq_factoring: "eq_factoring (premise, \<V>) (conclusion', \<V>)" and
    inference_groundings: "\<iota>\<^sub>G \<in> inference_groundings (Infer [premise] conclusion')" and  
    conclusion'_conclusion: "conclusion' \<cdot> \<gamma> = conclusion \<cdot> \<gamma>"
    using 
      eq_factoring_lifting[OF 
        premise_grounding 
        conclusion_grounding 
        select 
        ground_eq_factoring[unfolded premise\<^sub>G conclusion\<^sub>G]
        ]
    unfolding premise\<^sub>G conclusion\<^sub>G \<iota>\<^sub>G
    by metis

  let ?\<iota> = "Infer [premise] conclusion'"

  show ?thesis
  proof(rule that)
    show "?\<iota> \<in> Inf_from premises"
      using premise_in_premises eq_factoring
      unfolding Inf_from_def inferences_def inference_system.Inf_from_def
      apply auto
      by (metis (no_types, lifting) fst_conv list.simps(8) list.simps(9))

    show "\<iota>\<^sub>G \<in> inference_groundings ?\<iota>"
      using inference_groundings.
  qed
qed

lemma superposition_ground_instance: 
  assumes 
    "\<iota>\<^sub>G \<in> ground.superposition_inferences"
    "\<iota>\<^sub>G \<in> ground.Inf_from_q select\<^sub>G (\<Union> (clause_groundings ` premises))" 
    "\<iota>\<^sub>G \<notin> ground.GRed_I (\<Union> (clause_groundings ` premises))"
    "subst_stability_on premises"
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
    premise\<^sub>G\<^sub>1_in_groundings: "premise\<^sub>G\<^sub>1 \<in> \<Union> (clause_groundings ` premises)" and  
    premise\<^sub>G\<^sub>2_in_groundings: "premise\<^sub>G\<^sub>2 \<in> \<Union> (clause_groundings ` premises)"
    using assms(2)
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
    by simp_all

  obtain premise\<^sub>1 premise\<^sub>2 \<gamma>\<^sub>1 \<gamma>\<^sub>2 where
    premise\<^sub>1_\<gamma>\<^sub>1: "premise\<^sub>1 \<cdot> \<gamma>\<^sub>1 = to_clause premise\<^sub>G\<^sub>1" and
    premise\<^sub>2_\<gamma>\<^sub>2: "premise\<^sub>2 \<cdot> \<gamma>\<^sub>2 = to_clause premise\<^sub>G\<^sub>2" and
    select: 
      "to_clause (select\<^sub>G (to_ground_clause (premise\<^sub>1 \<cdot> \<gamma>\<^sub>1))) = select premise\<^sub>1 \<cdot> \<gamma>\<^sub>1"
      "to_clause (select\<^sub>G (to_ground_clause (premise\<^sub>2 \<cdot> \<gamma>\<^sub>2))) = select premise\<^sub>2 \<cdot> \<gamma>\<^sub>2" and
    premise\<^sub>1_in_premises: "premise\<^sub>1 \<in> premises" and
    premise\<^sub>2_in_premises: "premise\<^sub>2 \<in> premises"
    using assms(2, 4) premise\<^sub>G\<^sub>1_in_groundings premise\<^sub>G\<^sub>2_in_groundings
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
    by (metis (no_types, lifting) ground_clause_is_ground select_subst1 to_ground_clause_inverse)

  obtain \<rho>\<^sub>1 \<rho>\<^sub>2 where
    renaming: 
      "term_subst.is_renaming (\<rho>\<^sub>1 :: ('f, 'v) subst)" 
      "term_subst.is_renaming \<rho>\<^sub>2" and
      "\<rho>\<^sub>1 ` vars_clause premise\<^sub>1 \<inter> \<rho>\<^sub>2 ` vars_clause premise\<^sub>2 = {}"
    using clause_renaming_exists[of premise\<^sub>1 premise\<^sub>2]. 

  then have vars_distinct: "vars_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter> vars_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2) = {}"
    using renaming_vars_clause[symmetric]
    by (smt (verit, del_insts) disjoint_iff imageI)

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
    by (simp_all add: image_mset_subseteq_mono subst_clause_def)

  define \<gamma> where 
    \<gamma>: "\<And>var. \<gamma> var = (
          if var \<in> vars_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) 
          then (\<rho>\<^sub>1_inv \<odot> \<gamma>\<^sub>1) var 
          else (\<rho>\<^sub>2_inv \<odot> \<gamma>\<^sub>2) var
        )"

  have premise\<^sub>1_\<gamma>: "premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma> = to_clause premise\<^sub>G\<^sub>1" 
  proof -
    have "premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<odot> (\<rho>\<^sub>1_inv \<odot> \<gamma>\<^sub>1) = to_clause premise\<^sub>G\<^sub>1"
      by (metis \<rho>\<^sub>1_inv premise\<^sub>1_\<gamma>\<^sub>1 subst_monoid_mult.mult.left_neutral subst_monoid_mult.mult_assoc)

    then show ?thesis
      unfolding \<gamma>
      by simp
  qed

  have premise\<^sub>2_\<gamma>: "premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<gamma> = to_clause premise\<^sub>G\<^sub>2" 
  proof -
    have "premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<odot> (\<rho>\<^sub>2_inv \<odot> \<gamma>\<^sub>2) = to_clause premise\<^sub>G\<^sub>2"
      by (metis \<rho>\<^sub>2_inv premise\<^sub>2_\<gamma>\<^sub>2 subst_monoid_mult.mult.left_neutral subst_monoid_mult.mult_assoc)

    then show ?thesis
      unfolding \<gamma>
      by (simp add: inf_commute vars_distinct)
  qed

  have select\<^sub>1: "to_clause (select\<^sub>G (to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>))) = select premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>"
    using select(1) \<rho>\<^sub>1_inv
    unfolding \<gamma> clause_subst_reduntant_if[OF clause_submset_vars_clause_subset, OF select_subset(1)]
    by (smt (verit, ccfv_SIG) clause_subst_compose clause_subst_eq subst_clause_Var_ident)
   
  have select\<^sub>2: "to_clause (select\<^sub>G (to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<gamma>))) = select premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<gamma>"   
  proof -
    have "vars_clause (select premise\<^sub>2 \<cdot> \<rho>\<^sub>2) \<subseteq> vars_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2)"
      using clause_submset_vars_clause_subset[OF select_subset(2)].

    then have "vars_clause (select premise\<^sub>2 \<cdot> \<rho>\<^sub>2) \<inter> vars_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) = {}"
      using vars_distinct
      by blast

    moreover have "\<And>clause \<sigma>. clause \<cdot> \<rho>\<^sub>2 \<odot> (\<rho>\<^sub>2_inv \<odot> \<sigma>) = clause \<cdot> \<sigma>"
      by (metis \<rho>\<^sub>2_inv subst_monoid_mult.mult.left_neutral subst_monoid_mult.mult_assoc)

    ultimately show ?thesis
      unfolding \<gamma>
      by (simp add: inf_commute select(2) vars_distinct)
  qed
    
  obtain conclusion where 
    conclusion_\<gamma>: "conclusion \<cdot> \<gamma> = to_clause conclusion\<^sub>G"
    by (meson ground_clause_is_ground subst_ground_clause)

  then have 
    premise\<^sub>1_grounding: "is_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>)" and 
    premise\<^sub>2_grounding: "is_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<gamma>)" and 
    premise\<^sub>G\<^sub>1: "premise\<^sub>G\<^sub>1 = to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>)" and 
    premise\<^sub>G\<^sub>2: "premise\<^sub>G\<^sub>2 = to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<gamma>)" and 
    conclusion_grounding: "is_ground_clause (conclusion \<cdot> \<gamma>)" and
    conclusion\<^sub>G: "conclusion\<^sub>G = to_ground_clause (conclusion \<cdot> \<gamma>)"
    by (simp_all add: premise\<^sub>1_\<gamma> premise\<^sub>2_\<gamma>)

  have "clause_groundings premise\<^sub>1 \<union> clause_groundings premise\<^sub>2 \<subseteq> \<Union> (clause_groundings ` premises)"
    using premise\<^sub>1_in_premises premise\<^sub>2_in_premises by blast

  then have \<iota>\<^sub>G_not_redunant:
    "\<iota>\<^sub>G \<notin> ground.GRed_I (clause_groundings premise\<^sub>1 \<union> clause_groundings premise\<^sub>2)"
    using assms(3) ground.Red_I_of_subset
    by blast

  obtain conclusion' \<V> where 
    superposition: "superposition (premise\<^sub>2, \<V>) (premise\<^sub>1, \<V>) (conclusion', \<V>)" and
    inference_groundings: "\<iota>\<^sub>G \<in>  inference_groundings (Infer [premise\<^sub>2, premise\<^sub>1] conclusion')" and  
    conclusion'_\<gamma>_conclusion_\<gamma>: "conclusion' \<cdot> \<gamma> = conclusion \<cdot> \<gamma>"
    using superposition_lifting[OF 
        renaming 
        vars_distinct 
        premise\<^sub>1_grounding 
        premise\<^sub>2_grounding 
        conclusion_grounding
        select\<^sub>1
        select\<^sub>2
        ground_superposition[unfolded  premise\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>1 conclusion\<^sub>G]
        \<iota>\<^sub>G_not_redunant[unfolded \<iota>\<^sub>G premise\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>1 conclusion\<^sub>G]
       ]
    unfolding \<iota>\<^sub>G conclusion\<^sub>G premise\<^sub>G\<^sub>1 premise\<^sub>G\<^sub>2 .
   
  let ?\<iota> = "Infer [premise\<^sub>2, premise\<^sub>1] conclusion'"

  show ?thesis
  proof(rule that)
    show "?\<iota> \<in> Inf_from premises"
      using premise\<^sub>1_in_premises premise\<^sub>2_in_premises superposition
      unfolding Inf_from_def inferences_def inference_system.Inf_from_def
      apply auto
      by (metis (no_types, opaque_lifting) fst_conv list.simps(8) list.simps(9))

    show "\<iota>\<^sub>G \<in> inference_groundings ?\<iota>"
      using inference_groundings.
  qed
qed

lemma ground_instances: 
  assumes 
    "\<iota>\<^sub>G \<in> ground.Inf_from_q select\<^sub>G (\<Union> (clause_groundings ` premises))" 
    "\<iota>\<^sub>G \<notin> ground.Red_I (\<Union> (clause_groundings ` premises))"
    "subst_stability_on premises"
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
    subst_stability: "select_subst_stability_on select select\<^sub>G premises" and
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
