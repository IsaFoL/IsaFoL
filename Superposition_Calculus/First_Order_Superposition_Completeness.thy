theory First_Order_Superposition_Completeness
  imports
    Ground_Superposition_Completeness
    Ground_Superposition_Soundness
    Grounded_First_Order_Superposition
begin

context grounded_first_order_superposition_calculus
begin

lemma equality_resolution_lifting:
  assumes 
    premise\<^sub>G [simp]: "premise\<^sub>G = to_ground_clause (premise \<cdot> \<theta>)" and
    conclusion\<^sub>G [simp]: "conclusion\<^sub>G = to_ground_clause (conclusion \<cdot> \<theta>)" and
    premise_grounding [intro]: "is_ground_clause (premise \<cdot> \<theta>)" and
    conclusion_grounding [intro]: "is_ground_clause (conclusion \<cdot> \<theta>)" and
    select: "to_clause (select\<^sub>G premise\<^sub>G) = (select premise) \<cdot> \<theta>" and
    ground_eq_resolution:  "ground.ground_eq_resolution premise\<^sub>G conclusion\<^sub>G"
  obtains conclusion' 
  where
    "equality_resolution premise conclusion'"
    "Infer [premise\<^sub>G] conclusion\<^sub>G \<in> inference_groundings (Infer [premise] conclusion')"
    "conclusion' \<cdot> \<theta> = conclusion \<cdot> \<theta>"
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

  have "premise \<cdot> \<theta> = to_clause (add_mset literal\<^sub>G (to_ground_clause (conclusion \<cdot> \<theta>)))"
    using 
       ground_eq_resolutionI(1)[THEN arg_cong, of to_clause]
       to_ground_clause_inverse[OF premise_grounding]
    unfolding premise\<^sub>G
    using \<open>conclusion\<^sub>G = premise\<^sub>G'\<close> conclusion\<^sub>G
    by metis

  also have "... = add_mset (to_literal literal\<^sub>G) (conclusion \<cdot> \<theta>)"
    unfolding to_clause_add_mset
    by (simp add: conclusion_grounding)

  finally have premise': "premise \<cdot> \<theta> = add_mset (to_literal literal\<^sub>G) (conclusion \<cdot> \<theta>)".

  let ?select\<^sub>G_empty = "select\<^sub>G (to_ground_clause (premise \<cdot> \<theta>)) = {#}"
  let ?select\<^sub>G_not_empty = "select\<^sub>G (to_ground_clause (premise \<cdot> \<theta>)) \<noteq> {#}"

  obtain max_literal where max_literal: 
      "is_maximal\<^sub>l max_literal premise" 
      "is_maximal\<^sub>l (max_literal \<cdot>l \<theta>) (premise \<cdot> \<theta>)"
    using is_maximal\<^sub>l_ground_subst_stability[OF premise_not_empty premise_grounding]
    by blast
   
  moreover then have "max_literal \<in># premise"
    using maximal\<^sub>l_in_clause by fastforce

  moreover have max_literal_literal\<^sub>G: 
      "max_literal \<cdot>l \<theta> = to_literal (term\<^sub>G !\<approx> term\<^sub>G)"
  if ?select\<^sub>G_empty
    using ground_eq_resolutionI(3) max_literal unique_maximal_in_ground_clause
    unfolding ground_eq_resolutionI(2) is_maximal_lit_iff_is_maximal\<^sub>l premise\<^sub>G
    by (metis empty_not_add_mset maximal\<^sub>l_in_clause multi_member_split premise_grounding that to_clause_empty_mset to_ground_clause_inverse)

  moreover obtain selected_literal where 
    "selected_literal \<cdot>l \<theta> = to_literal (term\<^sub>G !\<approx> term\<^sub>G)" and
    "is_maximal\<^sub>l selected_literal (select premise)" 
  if ?select\<^sub>G_not_empty
    using ground_eq_resolutionI(3) select
    unfolding ground_eq_resolutionI(2) premise\<^sub>G
    by (metis clause_subst_empty(2) is_maximal\<^sub>l_ground_subst_stability is_maximal_lit_iff_is_maximal\<^sub>l premise_grounding select_subst1 to_clause_inverse to_ground_clause_empty_mset unique_maximal_in_ground_clause)
   
  moreover then have "?select\<^sub>G_not_empty \<Longrightarrow> selected_literal \<in># premise"
    by (meson maximal\<^sub>l_in_clause mset_subset_eqD select_subset)

  ultimately obtain literal where
    literal: "literal \<cdot>l \<theta> = to_literal (term\<^sub>G !\<approx> term\<^sub>G)" and
    literal_in_premise: "literal \<in># premise" and
    literal_selected: "?select\<^sub>G_not_empty \<Longrightarrow> is_maximal\<^sub>l literal (select premise)" and
    literal_max: "?select\<^sub>G_empty \<Longrightarrow> is_maximal\<^sub>l literal premise"
    by blast    

  have literal_grounding: "is_ground_literal (literal \<cdot>l \<theta>)"
    using literal ground_literal_is_ground
    by simp

  from literal obtain "term" term' where terms: "literal = term !\<approx> term'"
    using subst_polarity_stable to_literal_polarity_stable
    by (metis literal.collapse(2) literal.disc(2) uprod_exhaust)

  have term_term': "term \<cdot>t \<theta> = term' \<cdot>t \<theta>"
    using literal
    unfolding terms subst_literal(2) subst_atom_def to_literal_def to_atom_def
    by simp

  then obtain \<sigma> \<tau> where \<sigma>: "term_subst.is_imgu \<sigma> {{term, term'}}" "\<theta> = \<sigma> \<odot> \<tau>"
    using imgu_exists
    by blast

  have literal\<^sub>G: 
    "to_literal literal\<^sub>G = (term !\<approx> term') \<cdot>l \<theta>" 
    "literal\<^sub>G = to_ground_literal ((term !\<approx> term') \<cdot>l \<theta>)"
    using literal ground_eq_resolutionI(2)  terms 
    by simp_all

  obtain conclusion' where conclusion': "premise = add_mset literal conclusion'"
    using multi_member_split[OF literal_in_premise]
    by blast

  have conclusion'_\<theta>: "conclusion' \<cdot> \<theta> = conclusion \<cdot> \<theta>"
    using premise'
    unfolding conclusion' ground_eq_resolutionI(2) literal[symmetric] subst_clause_add_mset
    by simp
    
  have equality_resolution: "equality_resolution premise (conclusion' \<cdot> \<sigma>)"
  proof (rule equality_resolutionI)
     show "premise = add_mset literal conclusion'"
       using conclusion'.
  next 
    show "literal = term !\<approx> term'"
      using terms.    
  next
    show "term_subst.is_imgu \<sigma> {{term, term'}}"
      using \<sigma>(1).
  next
    show "select premise = {#} \<and> is_maximal\<^sub>l (literal \<cdot>l \<sigma>) (premise \<cdot> \<sigma>) 
       \<or>  is_maximal\<^sub>l literal (select premise)"
    proof(cases ?select\<^sub>G_empty)
      case select\<^sub>G_empty: True

      then have "max_literal \<cdot>l \<theta> = literal \<cdot>l \<theta>"
        by (simp add: max_literal_literal\<^sub>G literal)
        
      then have literal_\<theta>_is_maximal: "is_maximal\<^sub>l (literal \<cdot>l \<theta>) (premise \<cdot> \<theta>)"
        using max_literal(2) by simp
       
      have literal_\<sigma>_in_premise: "literal \<cdot>l \<sigma> \<in># premise \<cdot> \<sigma>"
        by (simp add: literal_in_clause_subst literal_in_premise)

      have "is_maximal\<^sub>l (literal \<cdot>l \<sigma>) (premise \<cdot> \<sigma>)"
        using is_maximal\<^sub>l_ground_subst_stability'[OF 
                literal_\<sigma>_in_premise 
                premise_grounding[unfolded \<sigma>(2) clause_subst_compose]
                literal_\<theta>_is_maximal[unfolded \<sigma>(2) clause_subst_compose literal_subst_compose]
              ].

     then show ?thesis
       using select select\<^sub>G_empty
       by simp
    next
      case False
      then show ?thesis
        using literal_selected by blast
    qed
  next 
    show "conclusion' \<cdot> \<sigma> = conclusion' \<cdot> \<sigma>" ..
  qed

  have "term_subst.is_idem \<sigma>"
    using \<sigma>(1)
    by (simp add: term_subst.is_imgu_iff_is_idem_and_is_mgu)  

  then have \<sigma>_\<theta>: "\<sigma> \<odot> \<theta> = \<theta>"
    unfolding \<sigma>(2) term_subst.is_idem_def
    by (metis subst_compose_assoc)

  have conclusion'_\<sigma>_\<theta> : "conclusion' \<cdot> \<sigma> \<cdot> \<theta> = conclusion \<cdot> \<theta>"
    using conclusion'_\<theta>  
    unfolding clause_subst_compose[symmetric] \<sigma>_\<theta>.
 
  have "to_ground_clause (conclusion \<cdot> \<theta>) \<in> clause_groundings (conclusion' \<cdot> \<sigma>)"
    unfolding clause_groundings_def conclusion'_\<sigma>_\<theta>
    by (smt (verit, ccfv_threshold) conclusion'_\<sigma>_\<theta> conclusion_grounding mem_Collect_eq)

  (* TODO *)
  with equality_resolution that show ?thesis
    unfolding clause_groundings_def inference_groundings_def ground.G_Inf_def inferences_def premise\<^sub>G
    using premise_grounding 
    apply auto
    by (metis conclusion'_\<sigma>_\<theta> conclusion_grounding ground_eq_resolution premise\<^sub>G conclusion\<^sub>G)
qed

lemma equality_factoring_lifting:
  assumes
    premise_grounding [intro]: "is_ground_clause (premise \<cdot> \<theta>)" and
    conclusion_grounding [intro]: "is_ground_clause (conclusion \<cdot> \<theta>)" and
    select: "to_clause (select\<^sub>G (to_ground_clause (premise \<cdot> \<theta>))) = (select premise) \<cdot> \<theta>" and
    ground_eq_factoring: 
      "ground.ground_eq_factoring
          (to_ground_clause (premise \<cdot> \<theta>)) 
          (to_ground_clause (conclusion \<cdot> \<theta>))"
  obtains conclusion' 
  where
      "equality_factoring premise (conclusion')"
      "Infer [to_ground_clause (premise \<cdot> \<theta>)]  (to_ground_clause (conclusion' \<cdot> \<theta>)) \<in> 
                inference_groundings (Infer [premise] conclusion')"
      "conclusion' \<cdot> \<theta> = conclusion \<cdot> \<theta>"
   using ground_eq_factoring
proof(cases "to_ground_clause (premise \<cdot> \<theta>)" "to_ground_clause (conclusion \<cdot> \<theta>)" 
      rule: ground.ground_eq_factoring.cases)
  case (ground_eq_factoringI literal\<^sub>G\<^sub>1 literal\<^sub>G\<^sub>2 premise'\<^sub>G term\<^sub>G\<^sub>1 term\<^sub>G\<^sub>2 term\<^sub>G\<^sub>3)

  have premise_not_empty: "premise \<noteq> {#}"
    using ground_eq_factoringI(1) empty_not_add_mset clause_subst_empty
    by (metis to_clause_empty_mset to_clause_inverse)
  
  have select_empty: "select premise = {#}"
    using ground_eq_factoringI(4) select clause_subst_empty
    by auto
  
  have premise_\<theta>: "premise \<cdot> \<theta> = to_clause (add_mset literal\<^sub>G\<^sub>1 (add_mset literal\<^sub>G\<^sub>2 premise'\<^sub>G))"
    using ground_eq_factoringI(1)
    by (metis premise_grounding to_ground_clause_inverse)
  
  obtain literal\<^sub>1 where literal\<^sub>1_maximal: 
    "is_maximal\<^sub>l literal\<^sub>1 premise" 
    "is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<theta>) (premise \<cdot> \<theta>)"
    using is_maximal\<^sub>l_ground_subst_stability[OF premise_not_empty premise_grounding]
    by blast

  note max_ground_literal = is_maximal_lit_iff_is_maximal\<^sub>l[
      THEN iffD1,
      OF ground_eq_factoringI(5), 
      unfolded ground_eq_factoringI(2) to_ground_clause_inverse[OF premise_grounding]
    ]

  have literal\<^sub>1: "literal\<^sub>1 \<cdot>l \<theta> = to_literal literal\<^sub>G\<^sub>1"
    using 
      unique_maximal_in_ground_clause[OF premise_grounding literal\<^sub>1_maximal(2) max_ground_literal]
      ground_eq_factoringI(2)
    by blast

  then have "\<exists>term\<^sub>1 term\<^sub>1'. literal\<^sub>1 = term\<^sub>1 \<approx> term\<^sub>1'"
    unfolding ground_eq_factoringI(2)  
    using to_literal_stable subst_pos_stable is_pos_def[symmetric]
    by (metis uprod_exhaust)
   
  with literal\<^sub>1 obtain term\<^sub>1 term\<^sub>1' where 
    literal\<^sub>1_terms: "literal\<^sub>1 = term\<^sub>1 \<approx> term\<^sub>1'" and
    term\<^sub>G\<^sub>1_term\<^sub>1: "to_term term\<^sub>G\<^sub>1 = term\<^sub>1 \<cdot>t \<theta>"
    unfolding ground_eq_factoringI(2) to_literal_def to_atom_def subst_literal_def subst_atom_def 
    by force 

  obtain premise'' where premise'': "premise = add_mset literal\<^sub>1 premise''"
    using maximal\<^sub>l_in_clause[OF literal\<^sub>1_maximal(1)]
    by (meson multi_member_split)

  then have premise''_\<theta>: "premise'' \<cdot> \<theta> =  add_mset (to_literal literal\<^sub>G\<^sub>2) (to_clause premise'\<^sub>G)"
    using premise_\<theta> 
    unfolding to_clause_add_mset literal\<^sub>1[symmetric]
    by (simp add: subst_clause_add_mset)

  then obtain literal\<^sub>2 where literal\<^sub>2:
    "literal\<^sub>2 \<cdot>l \<theta> = to_literal literal\<^sub>G\<^sub>2"
    "literal\<^sub>2 \<in># premise''"
    unfolding subst_clause_def
    using msed_map_invR by force

  then have "\<exists>term\<^sub>2 term\<^sub>2'. literal\<^sub>2 = term\<^sub>2 \<approx> term\<^sub>2'"
    unfolding ground_eq_factoringI(3)  
    using to_literal_stable subst_pos_stable is_pos_def[symmetric]
    by (metis uprod_exhaust)
   
  with literal\<^sub>2 obtain term\<^sub>2 term\<^sub>2' where 
    literal\<^sub>2_terms: "literal\<^sub>2 = term\<^sub>2 \<approx> term\<^sub>2'" and
    term\<^sub>G\<^sub>1_term\<^sub>2: "to_term term\<^sub>G\<^sub>1 = term\<^sub>2 \<cdot>t \<theta>"
    unfolding ground_eq_factoringI(3) to_literal_def to_atom_def subst_literal_def subst_atom_def 
    by force
 
  have term\<^sub>1_term\<^sub>2: "term\<^sub>1 \<cdot>t \<theta> = term\<^sub>2 \<cdot>t \<theta>"
    using term\<^sub>G\<^sub>1_term\<^sub>1 term\<^sub>G\<^sub>1_term\<^sub>2
    by argo

  then obtain \<sigma> \<tau> where \<sigma>: "term_subst.is_imgu \<sigma> {{term\<^sub>1, term\<^sub>2}}" "\<theta> = \<sigma> \<odot> \<tau>"
    using imgu_exists
    by blast

  have term\<^sub>G\<^sub>2_term\<^sub>1': "to_term term\<^sub>G\<^sub>2 = term\<^sub>1' \<cdot>t \<theta>"
    using literal\<^sub>1 term\<^sub>G\<^sub>1_term\<^sub>1 
    unfolding 
      literal\<^sub>1_terms 
      ground_eq_factoringI(2) 
      to_literal_def 
      to_atom_def 
      subst_literal_def
      subst_atom_def 
    by auto
   
  have term\<^sub>G\<^sub>3_term\<^sub>2': "to_term term\<^sub>G\<^sub>3 = term\<^sub>2' \<cdot>t \<theta>"
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

  then have premise'_\<theta>: "premise' \<cdot> \<theta> = to_clause premise'\<^sub>G"
    using premise''_\<theta>  premise''
    unfolding literal\<^sub>2(1)[symmetric]
    by (simp add: subst_clause_add_mset)
  
  let ?conclusion' = "add_mset (term\<^sub>1 \<approx> term\<^sub>2') (add_mset (term\<^sub>1' !\<approx> term\<^sub>2') premise')"

  have equality_factoring: "equality_factoring premise (?conclusion' \<cdot> \<sigma>)"
  proof (rule equality_factoringI)
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
    have literal\<^sub>1_\<sigma>_in_premise: "literal\<^sub>1 \<cdot>l \<sigma> \<in># premise \<cdot> \<sigma>"
      using literal\<^sub>1_maximal(1) literal_in_clause_subst maximal\<^sub>l_in_clause by blast

    have "is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<sigma>) (premise \<cdot> \<sigma>)"
    using is_maximal\<^sub>l_ground_subst_stability'[OF 
              literal\<^sub>1_\<sigma>_in_premise 
              premise_grounding[unfolded \<sigma>(2) clause_subst_compose]
              literal\<^sub>1_maximal(2)[unfolded \<sigma>(2) clause_subst_compose literal_subst_compose]
            ].

    then show "is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<sigma>) (premise \<cdot> \<sigma>)"
      by blast
  next
    have term_groundings: "is_ground_term (term\<^sub>1' \<cdot>t \<sigma> \<cdot>t \<tau>)" "is_ground_term (term\<^sub>1 \<cdot>t \<sigma> \<cdot>t \<tau>)" 
      unfolding 
        term_subst_compose[symmetric] 
        \<sigma>(2)[symmetric]
        term\<^sub>G\<^sub>1_term\<^sub>1[symmetric] 
        term\<^sub>G\<^sub>2_term\<^sub>1'[symmetric] 
      using ground_term_is_ground
      by simp_all

    have "term\<^sub>1' \<cdot>t \<sigma> \<cdot>t \<tau> \<prec>\<^sub>t term\<^sub>1 \<cdot>t \<sigma> \<cdot>t \<tau>"
      using ground_eq_factoringI(6)[unfolded 
          less\<^sub>t\<^sub>G_def 
          term\<^sub>G\<^sub>1_term\<^sub>1 
          term\<^sub>G\<^sub>2_term\<^sub>1'
          \<sigma>(2) 
          term_subst_compose
      ].

    then show "\<not> term\<^sub>1 \<cdot>t \<sigma> \<preceq>\<^sub>t term\<^sub>1' \<cdot>t \<sigma>"
      using less\<^sub>t_less_eq\<^sub>t_ground_subst_stability[OF term_groundings]
      by blast
 next 
    show "term_subst.is_imgu \<sigma> {{term\<^sub>1, term\<^sub>2}}"
      using \<sigma>(1).
  next 
    show "?conclusion' \<cdot> \<sigma> = ?conclusion' \<cdot> \<sigma>"
      ..
  qed

  have "term_subst.is_idem \<sigma>"
    using \<sigma>(1)
    by (simp add: term_subst.is_imgu_iff_is_idem_and_is_mgu)  

  then have \<sigma>_\<theta>: "\<sigma> \<odot> \<theta> = \<theta>"
    unfolding \<sigma>(2) term_subst.is_idem_def
    by (metis subst_compose_assoc)

  have "conclusion \<cdot> \<theta> = 
      add_mset (to_term term\<^sub>G\<^sub>2 !\<approx> to_term term\<^sub>G\<^sub>3) 
        (add_mset (to_term term\<^sub>G\<^sub>1 \<approx> to_term term\<^sub>G\<^sub>3) (to_clause premise'\<^sub>G))"
    using ground_eq_factoringI(7) to_ground_clause_inverse[OF conclusion_grounding]
    unfolding to_term_to_atom to_atom_to_literal to_clause_add_mset[symmetric]
    by simp

  then have conclusion_\<theta>: 
    "conclusion \<cdot> \<theta> = add_mset (term\<^sub>1 \<approx> term\<^sub>2') (add_mset (term\<^sub>1' !\<approx> term\<^sub>2') premise') \<cdot> \<theta>"
    unfolding 
      term\<^sub>G\<^sub>2_term\<^sub>1'
      term\<^sub>G\<^sub>3_term\<^sub>2'
      term\<^sub>G\<^sub>1_term\<^sub>1
      premise'_\<theta>[symmetric]
      subst_clause_add_mset[symmetric]
      subst_literal[symmetric]
      subst_atom[symmetric]
    by (simp add: add_mset_commute)

  then have "to_ground_clause (conclusion \<cdot> \<theta>) \<in> clause_groundings (?conclusion' \<cdot> \<sigma>)"
    unfolding clause_groundings_def 
    using \<sigma>(2) conclusion_\<theta> conclusion_grounding by auto

  (* TODO *)
  with equality_factoring that show ?thesis
    unfolding clause_groundings_def inference_groundings_def ground.G_Inf_def inferences_def
    using premise_grounding
    apply auto
    by (metis (no_types, lifting) \<sigma>_\<theta> clause_subst_compose conclusion_\<theta> conclusion_grounding ground_eq_factoring)
qed

lemma superposition_lifting:
  assumes 
    renaming: 
      "term_subst.is_renaming \<rho>\<^sub>1" 
      "term_subst.is_renaming \<rho>\<^sub>2" 
      "vars_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter> vars_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2) = {}" and
    premise\<^sub>1_grounding [intro]: "is_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)" and
    premise\<^sub>2_grounding [intro]: "is_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>)" and
    conclusion_grounding [intro]: "is_ground_clause (conclusion \<cdot> \<theta>)" and
    select: 
      "to_clause (select\<^sub>G (to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>))) = (select premise\<^sub>1) \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>"
      "to_clause (select\<^sub>G (to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>))) = (select premise\<^sub>2) \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>" and
    ground_superposition: 
      "ground.ground_superposition
          (to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>))
          (to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>))
          (to_ground_clause (conclusion \<cdot> \<theta>))" and
    non_redundant:
      "Infer [to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>), to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)] (to_ground_clause (conclusion \<cdot> \<theta>)) 
        \<notin> ground.Red_I (clause_groundings premise\<^sub>1 \<union> clause_groundings premise\<^sub>2)"
  obtains conclusion' 
  where "superposition premise\<^sub>2 premise\<^sub>1 conclusion'"
        "Infer [to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>), to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)] (to_ground_clause (conclusion' \<cdot> \<theta>)) 
                \<in> inference_groundings (Infer [premise\<^sub>2, premise\<^sub>1] conclusion')"
        "conclusion' \<cdot> \<theta> = conclusion \<cdot> \<theta>"
   using ground_superposition
proof(cases 
      "to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>)"
      "to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)"
      "to_ground_clause (conclusion \<cdot> \<theta>)"
      rule: ground.ground_superposition.cases)
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
    using ground_superpositionI(1) empty_not_add_mset clause_subst_empty
    by (metis to_clause_empty_mset to_clause_inverse)

  have premise\<^sub>2_not_empty: "premise\<^sub>2 \<noteq> {#}"
    using ground_superpositionI(2) empty_not_add_mset clause_subst_empty
    by (metis to_clause_empty_mset to_clause_inverse)

  have premise\<^sub>1_\<theta> : "premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta> = to_clause (add_mset literal\<^sub>G\<^sub>1 premise\<^sub>G\<^sub>1')"
    using ground_superpositionI(1)
    by (metis premise\<^sub>1_grounding to_ground_clause_inverse)

   have premise\<^sub>2_\<theta> : "premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta> = to_clause (add_mset literal\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>2')"
    using ground_superpositionI(2)
    by (metis premise\<^sub>2_grounding to_ground_clause_inverse)

  let ?select\<^sub>G_empty = "select\<^sub>G (to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)) = {#}"
  let ?select\<^sub>G_not_empty = "select\<^sub>G (to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)) \<noteq> {#}"

  have pos_literal\<^sub>G\<^sub>1_is_strictly_maximal\<^sub>l: 
    "\<P>\<^sub>G = Pos \<Longrightarrow> is_strictly_maximal\<^sub>l (to_literal literal\<^sub>G\<^sub>1) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<odot> \<theta>)"
    using ground_superpositionI(9)
    unfolding is_strictly_maximal\<^sub>G\<^sub>l_iff_is_strictly_maximal\<^sub>l
    by(simp add: premise\<^sub>1_grounding)

  have neg_literal\<^sub>G\<^sub>1_is_maximal\<^sub>l: 
    "\<P>\<^sub>G = Neg \<Longrightarrow> ?select\<^sub>G_empty \<Longrightarrow> is_maximal\<^sub>l (to_literal literal\<^sub>G\<^sub>1) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<odot> \<theta>)"
    using ground_superpositionI(9)
    unfolding is_maximal_lit_iff_is_maximal\<^sub>l
    by (metis clause_subst_compose diff_empty ground_superpositionI(1) id_remove_1_mset_iff_notin is_maximal\<^sub>l_if_is_strictly_maximal\<^sub>l is_maximal_lit_iff_is_maximal\<^sub>l maximal_lit_in_clause pos_literal\<^sub>G\<^sub>1_is_strictly_maximal\<^sub>l premise\<^sub>1_\<theta>)

  obtain pos_literal\<^sub>1 where
    "is_strictly_maximal\<^sub>l pos_literal\<^sub>1 premise\<^sub>1"
    "pos_literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<theta> = to_literal literal\<^sub>G\<^sub>1" 
  if "\<P>\<^sub>G = Pos"
    using is_strictly_maximal\<^sub>l_ground_subst_stability[OF 
            premise\<^sub>1_grounding[folded clause_subst_compose] 
            pos_literal\<^sub>G\<^sub>1_is_strictly_maximal\<^sub>l
          ]
    by blast

  moreover then have "\<P>\<^sub>G = Pos \<Longrightarrow> pos_literal\<^sub>1 \<in># premise\<^sub>1" 
    using strictly_maximal\<^sub>l_in_clause by fastforce

  moreover obtain neg_max_literal\<^sub>1 where
    "is_maximal\<^sub>l neg_max_literal\<^sub>1 premise\<^sub>1"
    "neg_max_literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<theta> = to_literal literal\<^sub>G\<^sub>1" 
  if "\<P>\<^sub>G = Neg" ?select\<^sub>G_empty
    using 
      is_maximal\<^sub>l_ground_subst_stability[OF 
        premise\<^sub>1_not_empty 
        premise\<^sub>1_grounding[folded clause_subst_compose]
      ]
      neg_literal\<^sub>G\<^sub>1_is_maximal\<^sub>l
    by (metis clause_subst_compose premise\<^sub>1_grounding unique_maximal_in_ground_clause)

  moreover then have "\<P>\<^sub>G = Neg \<Longrightarrow> ?select\<^sub>G_empty \<Longrightarrow> neg_max_literal\<^sub>1 \<in># premise\<^sub>1" 
    using maximal\<^sub>l_in_clause by fastforce

  moreover obtain neg_selected_literal\<^sub>1 where
    "is_maximal\<^sub>l neg_selected_literal\<^sub>1 (select premise\<^sub>1)"
    "neg_selected_literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<theta> = to_literal literal\<^sub>G\<^sub>1" 
  if "\<P>\<^sub>G = Neg" ?select\<^sub>G_not_empty 
    using ground_superpositionI(9) select(1)
    by (metis (no_types, opaque_lifting) clause_subst_compose clause_subst_empty(2) ground_clause_is_ground is_maximal\<^sub>l_ground_subst_stability is_maximal_lit_iff_is_maximal\<^sub>l to_clause_inverse to_ground_clause_empty_mset unique_maximal_in_ground_clause)

  moreover then have "\<P>\<^sub>G = Neg \<Longrightarrow> ?select\<^sub>G_not_empty \<Longrightarrow> neg_selected_literal\<^sub>1 \<in># premise\<^sub>1" 
    by (meson maximal\<^sub>l_in_clause mset_subset_eqD select_subset)

  ultimately obtain literal\<^sub>1 where
   literal\<^sub>1_\<theta>: "literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<theta> = to_literal literal\<^sub>G\<^sub>1" and
   literal\<^sub>1_in_premise\<^sub>1: "literal\<^sub>1 \<in># premise\<^sub>1" and
   literal\<^sub>1_is_strictly_maximal: "\<P>\<^sub>G = Pos \<Longrightarrow> is_strictly_maximal\<^sub>l literal\<^sub>1 premise\<^sub>1" and
   literal\<^sub>1_is_maximal: "\<P>\<^sub>G = Neg \<Longrightarrow> ?select\<^sub>G_empty \<Longrightarrow> is_maximal\<^sub>l literal\<^sub>1 premise\<^sub>1" and
   literal\<^sub>1_selected: "\<P>\<^sub>G = Neg \<Longrightarrow> ?select\<^sub>G_not_empty \<Longrightarrow> is_maximal\<^sub>l literal\<^sub>1 (select premise\<^sub>1)"
    by (metis ground_superpositionI(9) literals_distinct(1))

  then have literal\<^sub>1_grounding [intro]: "is_ground_literal (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<theta>)"
    by simp

  have literal\<^sub>G\<^sub>2_is_strictly_maximal\<^sub>l: 
    "is_strictly_maximal\<^sub>l (to_literal literal\<^sub>G\<^sub>2) (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<odot> \<theta>)"
    using ground_superpositionI(11)
    unfolding is_strictly_maximal\<^sub>G\<^sub>l_iff_is_strictly_maximal\<^sub>l
    by (simp add: premise\<^sub>2_grounding)

  obtain literal\<^sub>2 where 
    literal\<^sub>2_maximal: "is_strictly_maximal\<^sub>l literal\<^sub>2 premise\<^sub>2" and
    literal\<^sub>2_\<theta>: "literal\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<odot> \<theta> = to_literal literal\<^sub>G\<^sub>2"
    using is_strictly_maximal\<^sub>l_ground_subst_stability[OF 
            premise\<^sub>2_grounding[folded clause_subst_compose] 
            literal\<^sub>G\<^sub>2_is_strictly_maximal\<^sub>l
          ].

  then have literal\<^sub>2_in_premise\<^sub>2: "literal\<^sub>2 \<in># premise\<^sub>2" 
    using strictly_maximal\<^sub>l_in_clause by blast

  have literal\<^sub>2_grounding [intro]: "is_ground_literal (literal\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<odot> \<theta>)"
    using literal\<^sub>2_\<theta> by simp

  obtain premise\<^sub>1' where premise\<^sub>1: "premise\<^sub>1 = add_mset literal\<^sub>1 premise\<^sub>1'"
    by (meson literal\<^sub>1_in_premise\<^sub>1 multi_member_split)

  then have premise\<^sub>1'_\<theta>: "premise\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<theta> = to_clause premise\<^sub>G\<^sub>1'"
    using premise\<^sub>1_\<theta>  
    unfolding to_clause_add_mset literal\<^sub>1_\<theta>[symmetric]
    by (simp add: subst_clause_add_mset)

  obtain premise\<^sub>2' where premise\<^sub>2: "premise\<^sub>2 = add_mset literal\<^sub>2 premise\<^sub>2'"
    by (meson literal\<^sub>2_in_premise\<^sub>2 multi_member_split)

  then have premise\<^sub>2'_\<theta>: "premise\<^sub>2' \<cdot> \<rho>\<^sub>2 \<cdot> \<theta> = to_clause premise\<^sub>G\<^sub>2'"
    using premise\<^sub>2_\<theta>  
    unfolding to_clause_add_mset literal\<^sub>2_\<theta>[symmetric]
    by (simp add: subst_clause_add_mset)

  let ?\<P> = "if \<P>\<^sub>G = Pos then Pos else Neg"

  from literal\<^sub>1_\<theta> have literal\<^sub>1_\<theta>': 
    "literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<theta> = ?\<P> (Upair (to_context context\<^sub>G)\<langle>to_term term\<^sub>G\<^sub>1\<rangle> (to_term term\<^sub>G\<^sub>2))"
    using ground_superpositionI(4)
    unfolding ground_superpositionI(5)
    by (cases "\<P>\<^sub>G = Pos") 
       (simp_all add: 
          to_atom_to_literal[symmetric] 
          to_term_to_atom[symmetric] 
          ground_term_with_context(3)[symmetric]
        )

  then obtain term\<^sub>1_with_context term\<^sub>1' where 
    literal\<^sub>1: "literal\<^sub>1 = ?\<P> (Upair term\<^sub>1_with_context term\<^sub>1')" and
    term\<^sub>1'_\<theta>: "term\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>2" and
    term\<^sub>1_with_context_\<theta>: "term\<^sub>1_with_context \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = (to_context context\<^sub>G)\<langle>to_term term\<^sub>G\<^sub>1\<rangle>"
    by (smt (verit, ccfv_SIG) obtain_from_literal_subst)

  have "to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>) \<in> clause_groundings premise\<^sub>1"
    unfolding clause_groundings_def
    by (smt (verit, del_insts) clause_subst_compose mem_Collect_eq premise\<^sub>1_grounding)

  moreover have "to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>) \<in> clause_groundings premise\<^sub>2"
    unfolding clause_groundings_def
    by (smt (verit, del_insts) clause_subst_compose mem_Collect_eq premise\<^sub>2_grounding)

  moreover have conclusion_\<theta>\<^sub>G: "conclusion \<cdot> \<theta> = 
    add_mset (?\<P> (Upair (to_context context\<^sub>G)\<langle>to_term term\<^sub>G\<^sub>3\<rangle> (to_term term\<^sub>G\<^sub>2))) 
      (to_clause premise\<^sub>G\<^sub>1' + to_clause premise\<^sub>G\<^sub>2')"
    using ground_superpositionI(4, 12) to_ground_clause_inverse[OF conclusion_grounding] 
    unfolding ground_term_with_context(3) to_term_to_atom
    by(cases "\<P>\<^sub>G = Pos")(simp_all add: to_atom_to_literal to_clause_add_mset)

  from literal\<^sub>2_\<theta> have literal\<^sub>2_\<theta>': 
    "literal\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<theta> = to_term term\<^sub>G\<^sub>1 \<approx> to_term term\<^sub>G\<^sub>3"
    unfolding ground_superpositionI(6) to_term_to_atom to_atom_to_literal(2) literal_subst_compose.

  then obtain term\<^sub>2 term\<^sub>2' where 
    literal\<^sub>2: "literal\<^sub>2 = term\<^sub>2 \<approx> term\<^sub>2'" and
    term\<^sub>2_\<theta>: "term\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>1" and     
    term\<^sub>2'_\<theta>: "term\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>3"
   using obtain_from_pos_literal_subst
   by metis

  have special_case: "\<nexists>context\<^sub>1 term\<^sub>1. 
    term\<^sub>1_with_context = context\<^sub>1\<langle>term\<^sub>1\<rangle> \<and> 
    term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>1 \<and> 
    context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta> = to_context context\<^sub>G \<and> 
    is_Fun term\<^sub>1 \<Longrightarrow>
      ground.redundant_infer
         (clause_groundings (add_mset literal\<^sub>1 premise\<^sub>1') \<union> clause_groundings (add_mset literal\<^sub>2 premise\<^sub>2'))
         (Infer [add_mset literal\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>2', add_mset literal\<^sub>G\<^sub>1 premise\<^sub>G\<^sub>1'] 
                (add_mset  (\<P>\<^sub>G (Upair context\<^sub>G\<langle>term\<^sub>G\<^sub>3\<rangle>\<^sub>G  term\<^sub>G\<^sub>2)) (premise\<^sub>G\<^sub>1' + premise\<^sub>G\<^sub>2')))"
  proof-
    assume a: "\<nexists>context\<^sub>1 term\<^sub>1. 
      term\<^sub>1_with_context = context\<^sub>1\<langle>term\<^sub>1\<rangle> \<and> 
      term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>1 \<and> 
      context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta> = to_context context\<^sub>G \<and> 
      is_Fun term\<^sub>1"

    have term\<^sub>1_with_context_not_ground: "\<not> is_ground_term term\<^sub>1_with_context"
    proof
      assume "is_ground_term term\<^sub>1_with_context"

      then obtain term\<^sub>1 context\<^sub>1 where
        "term\<^sub>1_with_context = context\<^sub>1\<langle>term\<^sub>1\<rangle>"
        "term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>1" 
        "context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta> = to_context context\<^sub>G"
        "is_Fun term\<^sub>1"
        by (metis ground_context_is_ground ground_term_is_ground subst_ground_context term\<^sub>1_with_context_\<theta> term_subst.subst_ident_if_ground gterm_is_fun)
    
      with a show False
        by blast
    qed

    with a term\<^sub>1_with_context_\<theta> have "\<exists>term\<^sub>x context\<^sub>x context\<^sub>x'. 
      term\<^sub>1_with_context = context\<^sub>x\<langle>term\<^sub>x\<rangle> \<and> 
      is_Var term\<^sub>x \<and> 
      (context\<^sub>x \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta>) \<circ>\<^sub>c context\<^sub>x' = to_context context\<^sub>G"
     proof(induction term\<^sub>1_with_context arbitrary: context\<^sub>G)
       case (Var x)
       show ?case
         apply(rule exI[of _ "Var x"], rule exI[of _ Hole], rule exI[of _ "to_context context\<^sub>G"])
         by simp
      next
       case (Fun f terms)
       then have "context\<^sub>G \<noteq> GHole"
         by (metis ctxt_apply_term.simps(1) ctxt_of_gctxt.simps(1) subst_apply_ctxt.simps(1) term.disc(2))

       then obtain ss1 context\<^sub>G' ss2 where
        context\<^sub>G: "context\<^sub>G = GMore f ss1 context\<^sub>G' ss2"
         using Fun(3)
         by (smt (verit) ctxt_apply_term.simps(2) ctxt_of_gctxt.elims eval_term.simps(2) term.sel(2))

       have xx: "map ((\<lambda>s. s \<cdot>t \<theta>) \<circ> (\<lambda>s. s \<cdot>t \<rho>\<^sub>1)) terms = map to_term ss1 @ (to_context context\<^sub>G')\<langle>to_term term\<^sub>G\<^sub>1\<rangle> # map to_term ss2"
         using Fun(3)
         unfolding context\<^sub>G
         by auto

       then obtain ts1 "term" ts2 where 
          terms: "terms = ts1 @ term # ts2" and
          "map ((\<lambda>s. s \<cdot>t \<theta>) \<circ> (\<lambda>s. s \<cdot>t \<rho>\<^sub>1)) ts1 = map to_term ss1"
          "map ((\<lambda>s. s \<cdot>t \<theta>) \<circ> (\<lambda>s. s \<cdot>t \<rho>\<^sub>1)) ts2 = map to_term ss2"
         by (smt (z3) append_eq_map_conv map_eq_Cons_conv)
          
       with xx have yy: "term \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = (to_context context\<^sub>G')\<langle>to_term term\<^sub>G\<^sub>1\<rangle>"
         by simp

       show ?case
       proof(cases "is_ground_term term")
         case True
         with yy obtain term\<^sub>1 context\<^sub>1 where zz: 
            "term = context\<^sub>1\<langle>term\<^sub>1\<rangle>"
            "term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>1" "context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta> = to_context context\<^sub>G'" "is_Fun term\<^sub>1"
           by (metis Term.ground_vars_term_empty ground_context_is_ground ground_subst_apply ground_term_is_ground subst_ground_context gterm_is_fun)

         then have zzz: "Fun f terms = (More f ts1 context\<^sub>1 ts2)\<langle>term\<^sub>1\<rangle>"
           unfolding terms
           by auto

         have "\<exists>context\<^sub>1 term\<^sub>1. Fun f terms = context\<^sub>1\<langle>term\<^sub>1\<rangle> \<and> term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>1 \<and> context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta> = to_context context\<^sub>G \<and> is_Fun term\<^sub>1"
           apply(rule exI[of _ "(More f ts1 context\<^sub>1 ts2)"])
           apply(rule exI[of _ term\<^sub>1])
           using zz zzz
           by (auto simp add: \<open>map ((\<lambda>s. s \<cdot>t \<theta>) \<circ> (\<lambda>s. s \<cdot>t \<rho>\<^sub>1)) ts1 = map to_term ss1\<close> \<open>map ((\<lambda>s. s \<cdot>t \<theta>) \<circ> (\<lambda>s. s \<cdot>t \<rho>\<^sub>1)) ts2 = map to_term ss2\<close> context\<^sub>G)

         then show ?thesis
           using Fun(2)
           by blast
       next
         case False
         have zz: "term \<in> set terms"
           using terms by auto

         have zzz: "\<nexists>context\<^sub>1 term\<^sub>1. term = context\<^sub>1\<langle>term\<^sub>1\<rangle> \<and> term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>1 \<and> context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta> = to_context context\<^sub>G' \<and> is_Fun term\<^sub>1"
         proof
           assume "\<exists>context\<^sub>1 term\<^sub>1. term = context\<^sub>1\<langle>term\<^sub>1\<rangle> \<and> term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>1 \<and> context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta> = to_context context\<^sub>G' \<and> is_Fun term\<^sub>1"
  
           then obtain context\<^sub>1 term\<^sub>1 where
              "term": "term = context\<^sub>1\<langle>term\<^sub>1\<rangle>"
              "term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>1"
              "context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta> = to_context context\<^sub>G'"
              "is_Fun term\<^sub>1"
             by blast

          then have zzzz: "Fun f terms = (More f ts1 context\<^sub>1 ts2)\<langle>term\<^sub>1\<rangle>"
           unfolding terms
           by auto

         have "\<exists>context\<^sub>1 term\<^sub>1. Fun f terms = context\<^sub>1\<langle>term\<^sub>1\<rangle> \<and> term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>1 \<and> context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta> = to_context context\<^sub>G \<and> is_Fun term\<^sub>1"
           apply(rule exI[of _ "(More f ts1 context\<^sub>1 ts2)"])
           apply(rule exI[of _ term\<^sub>1])
           by(auto simp: "term" terms \<open>map ((\<lambda>s. s \<cdot>t \<theta>) \<circ> (\<lambda>s. s \<cdot>t \<rho>\<^sub>1)) ts1 = map to_term ss1\<close> \<open>map ((\<lambda>s. s \<cdot>t \<theta>) \<circ> (\<lambda>s. s \<cdot>t \<rho>\<^sub>1)) ts2 = map to_term ss2\<close> context\<^sub>G)
           

          then show False
            using Fun(2)
            by blast
        qed

        obtain term\<^sub>x context\<^sub>x context\<^sub>x' where 
          term\<^sub>x: 
          "term = context\<^sub>x\<langle>term\<^sub>x\<rangle>"  
          "is_Var term\<^sub>x" 
          "(context\<^sub>x \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta>) \<circ>\<^sub>c context\<^sub>x' = to_context context\<^sub>G'"
         using Fun(1)[OF zz zzz yy False] by blast

         show ?thesis
           apply(rule exI[of _ term\<^sub>x]) 
           apply(rule exI[of _ "(More f ts1 context\<^sub>x ts2)"])
           apply(rule exI[of _ context\<^sub>x'])
           by(auto simp: term\<^sub>x terms \<open>map ((\<lambda>s. s \<cdot>t \<theta>) \<circ> (\<lambda>s. s \<cdot>t \<rho>\<^sub>1)) ts1 = map to_term ss1\<close> \<open>map ((\<lambda>s. s \<cdot>t \<theta>) \<circ> (\<lambda>s. s \<cdot>t \<rho>\<^sub>1)) ts2 = map to_term ss2\<close> context\<^sub>G)
       qed
     qed
  
    then obtain term\<^sub>x context\<^sub>x context\<^sub>x' where
      context\<^sub>x: "term\<^sub>1_with_context = context\<^sub>x\<langle>term\<^sub>x\<rangle>"
      "is_Var term\<^sub>x"
      "(context\<^sub>x \<circ>\<^sub>c context\<^sub>x') \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta> = to_context context\<^sub>G"
      by (metis Subterm_and_Context.ctxt_ctxt_compose ground_context_is_ground ground_term_is_ground ground_term_with_context_is_ground2(2) subst_compose_ctxt_compose_distrib subst_ground_context sup_bot.right_neutral vars_term_ctxt_apply)

    then obtain var\<^sub>x where var\<^sub>x: "Var var\<^sub>x = term\<^sub>x \<cdot>t \<rho>\<^sub>1"
      by (metis eval_term.simps(1) is_Var_def renaming(1) subst_cannot_add_var subst_compose_def term_subst.is_renaming_def)

    obtain \<theta>' where \<theta>':
      "\<theta>' = \<theta>(var\<^sub>x := (context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta>)\<langle>to_term term\<^sub>G\<^sub>3\<rangle>)"
      by simp

    have update_grounding: "is_ground_term (context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta>)\<langle>to_term term\<^sub>G\<^sub>3\<rangle>"
      by (metis Subterm_and_Context.ctxt_ctxt_compose context\<^sub>x(3) ground_term_with_context_is_ground1 ground_term_with_context_is_ground2(2) subst_compose_ctxt_compose_distrib)

    have premise\<^sub>1_grounding': "is_ground_clause (add_mset literal\<^sub>1 premise\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)"
      using premise\<^sub>1 premise\<^sub>1_grounding by blast

    have \<theta>'_grounding: "is_ground_clause (add_mset literal\<^sub>1 premise\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>')"
      using ground_clause_subst_upd[OF update_grounding premise\<^sub>1_grounding']
      unfolding \<theta>'
      by blast
 
    let ?D = "to_ground_clause ((add_mset literal\<^sub>1 premise\<^sub>1') \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>')"
    let ?DD = "{ ?D }"

    have term\<^sub>x_\<theta>: "to_ground_term (term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta>) = (to_ground_context (context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta>))\<langle>term\<^sub>G\<^sub>1\<rangle>\<^sub>G"
      using term\<^sub>1_with_context_\<theta>
      unfolding context\<^sub>x(1)context\<^sub>x(3)[symmetric]
      apply auto
      by (metis ground_term_is_ground ground_term_with_context1 ground_term_with_context_is_ground2(1) update_grounding to_term_inverse)

    have term\<^sub>x_\<theta>': "to_ground_term (term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta>') = (to_ground_context (context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta>))\<langle>term\<^sub>G\<^sub>3\<rangle>\<^sub>G"
      unfolding \<theta>'
      by (metis eval_term.simps(1) fun_upd_same ground_term_is_ground ground_term_with_context1 ground_term_with_context_is_ground2(1) update_grounding to_term_inverse var\<^sub>x)

    have premise\<^sub>1_\<theta>_x: "add_mset literal\<^sub>1 premise\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<theta> =  add_mset (to_literal literal\<^sub>G\<^sub>1) (to_clause premise\<^sub>G\<^sub>1')"
      using premise\<^sub>1 premise\<^sub>1_\<theta> to_clause_add_mset by auto

    have entails: "\<And>I. refl I \<Longrightarrow>
         trans I \<Longrightarrow>
         sym I \<Longrightarrow>
         compatible_with_gctxt I \<Longrightarrow>
         (\<lambda>(x, y). Upair x y) ` I \<TTurnstile>s {add_mset literal\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>2', ?D} \<Longrightarrow>
         (\<lambda>(x, y). Upair x y) ` I \<TTurnstile>s {add_mset (\<P>\<^sub>G (Upair context\<^sub>G\<langle>term\<^sub>G\<^sub>3\<rangle>\<^sub>G term\<^sub>G\<^sub>2)) (premise\<^sub>G\<^sub>1' + premise\<^sub>G\<^sub>2')}"
    proof-
      fix I :: "'f gterm rel"
      let ?I = "(\<lambda>(x, y). Upair x y) ` I"
  
      assume 
        refl: "refl I" and 
        trans: "trans I" and 
        sym: "sym I" and
        compatible_with_gctxt: "compatible_with_gctxt I" and
        premise: "?I \<TTurnstile>s {add_mset literal\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>2', ?D}"

      have var\<^sub>x_\<theta>_ground: "is_ground_term (Var var\<^sub>x \<cdot>t \<theta>)"
        by (metis context\<^sub>x(1) ground_term_is_ground ground_term_with_context3 ground_term_with_context_is_ground2(2) subst_apply_term_ctxt_apply_distrib term\<^sub>1_with_context_\<theta> var\<^sub>x)
        
      show "?I \<TTurnstile>s {add_mset (\<P>\<^sub>G (Upair context\<^sub>G\<langle>term\<^sub>G\<^sub>3\<rangle>\<^sub>G term\<^sub>G\<^sub>2)) (premise\<^sub>G\<^sub>1' + premise\<^sub>G\<^sub>2')}"
      proof(cases "?I \<TTurnstile> premise\<^sub>G\<^sub>2'")
        case True
        then show ?thesis 
          by auto
      next
        let ?x =  "to_ground_context (context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta>)"
        case False
        then have literal\<^sub>G\<^sub>2: "?I \<TTurnstile>l literal\<^sub>G\<^sub>2"
          using premise by blast

        then have "?I \<TTurnstile>l ?x\<langle>term\<^sub>G\<^sub>1\<rangle>\<^sub>G \<approx> ?x\<langle>term\<^sub>G\<^sub>3\<rangle>\<^sub>G"
          unfolding ground_superpositionI(6)
          using compatible_with_gctxt compatible_with_gctxt_def sym by auto

        then have "?I \<TTurnstile>l to_ground_term (term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta>) \<approx> to_ground_term (term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta>')"
          using term\<^sub>x_\<theta> term\<^sub>x_\<theta>'
          by argo

        then have "?I \<TTurnstile> to_ground_clause (add_mset literal\<^sub>1 premise\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>')"
          using premise by fastforce

        then have "?I \<TTurnstile> to_ground_clause (add_mset literal\<^sub>1 premise\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)"
          using \<theta>'_grounding
          unfolding \<theta>'
          using interpretation_clause_congruence[OF trans sym compatible_with_gctxt update_grounding var\<^sub>x_\<theta>_ground]
          using \<open>(\<lambda>(x, y). Upair x y) ` I \<TTurnstile>l to_ground_term (term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta>) \<approx> to_ground_term (term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta>')\<close> \<theta>' premise\<^sub>1_grounding' var\<^sub>x by auto

       then have "?I \<TTurnstile> add_mset (\<P>\<^sub>G (Upair context\<^sub>G\<langle>term\<^sub>G\<^sub>1\<rangle>\<^sub>G term\<^sub>G\<^sub>2)) premise\<^sub>G\<^sub>1'"
         using ground_superpositionI(1) ground_superpositionI(5) premise\<^sub>1 by auto

       then have "?I \<TTurnstile> add_mset (\<P>\<^sub>G (Upair context\<^sub>G\<langle>term\<^sub>G\<^sub>3\<rangle>\<^sub>G term\<^sub>G\<^sub>2)) premise\<^sub>G\<^sub>1'"
         using literal\<^sub>G\<^sub>2
         unfolding ground_superpositionI(6)
         (* TODO: Only place where ground soundness is used *)
         by (smt (verit) False compatible_with_gctxt ground.G_entails_def
             ground.soundness_ground_superposition ground_superposition ground_superpositionI(1)
             ground_superpositionI(12) ground_superpositionI(2) ground_superpositionI(5) local.refl
             local.sym local.trans premise true_cls_union true_clss_insert union_commute
             union_mset_add_mset_right)
  
        then show ?thesis 
          by blast
      qed
 
    qed
  
    have var\<^sub>x_\<theta>: "\<theta> var\<^sub>x = term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta>"
      using var\<^sub>x
      by simp

    have smaller': "((context\<^sub>x \<circ>\<^sub>c context\<^sub>x') \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta>)\<langle>to_term term\<^sub>G\<^sub>3\<rangle> \<prec>\<^sub>t context\<^sub>x\<langle>term\<^sub>x\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta>"
      unfolding context\<^sub>x(3) context\<^sub>x(1)[symmetric]
      unfolding term\<^sub>1_with_context_\<theta>
      by (simp add: ground_superpositionI(8) less\<^sub>t_less\<^sub>t\<^sub>G)

    then have xx: "(context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta>)\<langle>to_term term\<^sub>G\<^sub>3\<rangle> \<prec>\<^sub>t \<theta> var\<^sub>x"
      unfolding var\<^sub>x_\<theta>
      using less\<^sub>t_ground_context_compatible'[of "context\<^sub>x \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta>" "(context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta>)\<langle>to_term term\<^sub>G\<^sub>3\<rangle>" "term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta>"]
      by (metis Subterm_and_Context.ctxt_ctxt_compose context\<^sub>x(1) ground_term_with_context_is_ground1 ground_term_with_context_is_ground2(1) ground_term_with_context_is_ground2(2) update_grounding subst_compose_ctxt_compose_distrib term\<^sub>1_with_context_\<theta> subst_apply_term_ctxt_apply_distrib)

    have xy: "var\<^sub>x \<in> vars_literal (literal\<^sub>1  \<cdot>l \<rho>\<^sub>1)"
      unfolding literal\<^sub>1 context\<^sub>x vars_literal_def vars_atom_def 
      using var\<^sub>x
      by(auto simp: subst_literal subst_atom)

    have "is_ground_literal (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<theta>)"
      using literal\<^sub>1_grounding by force
    
    then have smaller: "literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<theta>' \<prec>\<^sub>l literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<theta>"
      unfolding \<theta>'
      using less\<^sub>l_subst_upd[of _ \<theta>, OF update_grounding xx _ xy]
      by blast

    have premise\<^sub>1'_\<theta>_grounding: "is_ground_clause (premise\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)"
      using premise\<^sub>1'_\<theta>
      by simp

    have smaller_premise\<^sub>1': "premise\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>' \<preceq>\<^sub>c premise\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>"
      unfolding \<theta>'
      using 
        less\<^sub>c_subst_upd[of _ \<theta>, OF update_grounding xx premise\<^sub>1'_\<theta>_grounding]
      by (metis (no_types, lifting) clause_subst_eq fun_upd_other reflclp_iff)

    from \<theta>'_grounding have "?D \<in> clause_groundings (add_mset literal\<^sub>1 premise\<^sub>1')"
      unfolding clause_groundings_def clause_subst_compose[symmetric]
      by blast

    moreover have "?D \<prec>\<^sub>c\<^sub>G add_mset literal\<^sub>G\<^sub>1 premise\<^sub>G\<^sub>1'"
      unfolding less\<^sub>c\<^sub>G_less\<^sub>c to_ground_clause_inverse[OF \<theta>'_grounding] to_clause_add_mset
      unfolding literal\<^sub>1_\<theta>[symmetric]  subst_clause_add_mset premise\<^sub>1'_\<theta>[symmetric]
      using less\<^sub>c_add_mset[OF smaller smaller_premise\<^sub>1']
      by simp

    moreover have "ground.G_entails (insert (add_mset literal\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>2') ?DD) {add_mset (\<P>\<^sub>G (Upair context\<^sub>G\<langle>term\<^sub>G\<^sub>3\<rangle>\<^sub>G term\<^sub>G\<^sub>2)) (premise\<^sub>G\<^sub>1' + premise\<^sub>G\<^sub>2')}"
      unfolding ground.G_entails_def
      using entails
      by blast

    ultimately show ?thesis
      unfolding ground.redundant_infer_def
      by auto
  qed

  have z: "(to_ground_clause
             (add_mset ((if \<P>\<^sub>G = Pos then Pos else Neg) (Upair (to_context context\<^sub>G)\<langle>to_term term\<^sub>G\<^sub>3\<rangle> (to_term term\<^sub>G\<^sub>2))) (to_clause premise\<^sub>G\<^sub>1' + to_clause premise\<^sub>G\<^sub>2'))) = 
             (add_mset  (\<P>\<^sub>G (Upair context\<^sub>G\<langle>term\<^sub>G\<^sub>3\<rangle>\<^sub>G  term\<^sub>G\<^sub>2))) (premise\<^sub>G\<^sub>1' + premise\<^sub>G\<^sub>2')"
    by (smt (verit) ground_superpositionI(9) ground_term_with_context3 to_atom_to_literal(1) to_atom_to_literal(2) to_clause_add_mset to_clause_inverse to_clause_plus to_term_to_atom)  

  have x: "\<lbrakk>
     ground.ground_superposition (add_mset literal\<^sub>G\<^sub>1 premise\<^sub>G\<^sub>1') (add_mset literal\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>2')
      (to_ground_clause
        (add_mset ((if \<P>\<^sub>G = Pos then Pos else Neg) (Upair (to_context context\<^sub>G)\<langle>to_term term\<^sub>G\<^sub>3\<rangle> (to_term term\<^sub>G\<^sub>2))) (to_clause premise\<^sub>G\<^sub>1' + to_clause premise\<^sub>G\<^sub>2')));

     \<not> ground.redundant_infer (clause_groundings (add_mset literal\<^sub>1 premise\<^sub>1') \<union> clause_groundings (add_mset literal\<^sub>2 premise\<^sub>2'))
         (Infer [add_mset literal\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>2', add_mset literal\<^sub>G\<^sub>1 premise\<^sub>G\<^sub>1']
           (to_ground_clause
             (add_mset ((if \<P>\<^sub>G = Pos then Pos else Neg) (Upair (to_context context\<^sub>G)\<langle>to_term term\<^sub>G\<^sub>3\<rangle> (to_term term\<^sub>G\<^sub>2))) (to_clause premise\<^sub>G\<^sub>1' + to_clause premise\<^sub>G\<^sub>2'))))\<rbrakk>
    \<Longrightarrow> \<exists>context\<^sub>1 term\<^sub>1. term\<^sub>1_with_context = context\<^sub>1\<langle>term\<^sub>1\<rangle> \<and> context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta> = to_context context\<^sub>G \<and> term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>1 \<and> is_Fun term\<^sub>1"
    unfolding z
    using special_case
    by blast

  obtain context\<^sub>1 term\<^sub>1 where 
    term\<^sub>1_with_context: "term\<^sub>1_with_context = context\<^sub>1\<langle>term\<^sub>1\<rangle>" and
    term\<^sub>1_\<theta> : "term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>1" and
    context\<^sub>1_\<theta> : "context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta> = to_context context\<^sub>G" and
    term\<^sub>1_not_Var: "\<not> is_Var term\<^sub>1"
    using non_redundant ground_superposition
    unfolding premise\<^sub>1_\<theta>
    unfolding premise\<^sub>2_\<theta>
    unfolding conclusion_\<theta>\<^sub>G
    unfolding premise\<^sub>1 premise\<^sub>2
    apply auto
    unfolding ground.Red_I_def
    apply auto
    unfolding ground.G_Inf_def
     apply blast
    by (metis special_case z)
 
  obtain term\<^sub>2'_with_context where
    term\<^sub>2'_with_context: 
      "term\<^sub>2'_with_context \<cdot>t \<theta> = (to_context context\<^sub>G)\<langle>to_term term\<^sub>G\<^sub>3\<rangle>"
      "term\<^sub>2'_with_context = (context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>term\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle>" 
    unfolding term\<^sub>2'_\<theta>[symmetric]  context\<^sub>1_\<theta>[symmetric]
    by force

  have term_term': "term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = term\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<theta>"
    unfolding term\<^sub>1_\<theta> term\<^sub>2_\<theta>
    by(rule refl)

  then obtain \<sigma> \<tau> where \<sigma>: "term_subst.is_imgu \<sigma> {{term\<^sub>1 \<cdot>t \<rho>\<^sub>1, term\<^sub>2 \<cdot>t \<rho>\<^sub>2}}" "\<theta> = \<sigma> \<odot> \<tau>"
    using imgu_exists
    by blast

  let ?conclusion' = "add_mset (?\<P> (Upair (term\<^sub>2'_with_context) (term\<^sub>1' \<cdot>t \<rho>\<^sub>1))) 
        (premise\<^sub>1' \<cdot> \<rho>\<^sub>1 + premise\<^sub>2' \<cdot> \<rho>\<^sub>2) \<cdot> \<sigma>"

  have "term_subst.is_idem \<sigma>"
    using \<sigma>(1)
    by (simp add: term_subst.is_imgu_iff_is_idem_and_is_mgu)  

  then have \<sigma>_\<theta>: "\<sigma> \<odot> \<theta> = \<theta>"
    unfolding \<sigma>(2) term_subst.is_idem_def
    by (metis subst_compose_assoc)

  from conclusion_\<theta>\<^sub>G have conclusion_\<theta>: "conclusion \<cdot> \<theta> =  ?conclusion' \<cdot> \<theta>"
    unfolding 
      term\<^sub>2'_with_context[symmetric]
      premise\<^sub>1'_\<theta>[symmetric] 
      premise\<^sub>2'_\<theta>[symmetric] 
      term\<^sub>1'_\<theta>[symmetric]
      subst_clause_plus[symmetric] 
      subst_apply_term_ctxt_apply_distrib[symmetric]
      subst_atom[symmetric]
    apply(cases "\<P>\<^sub>G = Pos")
    using subst_clause_add_mset subst_literal \<sigma>_\<theta> clause_subst_compose
    by (smt (verit, del_insts))+

  have superposition: "superposition premise\<^sub>2 premise\<^sub>1 ?conclusion'"
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
    show  "?\<P> \<in> {Pos, Neg}"
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
    show "term_subst.is_imgu \<sigma> {{term\<^sub>1 \<cdot>t \<rho>\<^sub>1, term\<^sub>2 \<cdot>t \<rho>\<^sub>2}}"
      using \<sigma>(1).
  next
    note premises_to_ground_clause_inverse = assms(4, 5)[THEN to_ground_clause_inverse]  
    note premise_groundings = assms(5, 4)[unfolded \<sigma>(2) clause_subst_compose]
    
    have "premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<sigma> \<cdot> \<tau> \<prec>\<^sub>c premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<sigma> \<cdot> \<tau>"
      using ground_superpositionI(3)[
        unfolded less\<^sub>c\<^sub>G_less\<^sub>c premises_to_ground_clause_inverse, 
        unfolded \<sigma>(2) clause_subst_compose
        ].

    then show "\<not> premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<sigma> \<preceq>\<^sub>c premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<sigma>"
      using less\<^sub>c_less_eq\<^sub>c_ground_subst_stability[OF premise_groundings]
      by blast
  next
    show "?\<P> = Pos 
            \<and> select premise\<^sub>1 = {#} 
            \<and> is_strictly_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<sigma>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<sigma>) 
       \<or> ?\<P> = Neg 
            \<and> (select premise\<^sub>1 = {#} \<and> is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<sigma>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<sigma>) 
               \<or> is_maximal\<^sub>l literal\<^sub>1 (select premise\<^sub>1))"
    proof(cases "?\<P> = Pos")
      case True
      moreover then have select_empty: "select premise\<^sub>1 = {#}"
        using clause_subst_empty select(1) ground_superpositionI(9) 
        by(auto simp: subst_clause_def)

      moreover have "is_strictly_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<sigma> \<cdot>l \<tau>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<sigma> \<cdot> \<tau>)"
        using True pos_literal\<^sub>G\<^sub>1_is_strictly_maximal\<^sub>l
        unfolding literal\<^sub>1_\<theta>[symmetric] \<sigma>(2)
        by force

      moreover then have "is_strictly_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<sigma>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<sigma>)"
        using 
          is_strictly_maximal\<^sub>l_ground_subst_stability'[OF
            _
            premise\<^sub>1_grounding[unfolded \<sigma>(2) clause_subst_compose]
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

        moreover have "is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<sigma> \<cdot>l \<tau>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<sigma> \<cdot> \<tau>)"
          using neg_literal\<^sub>G\<^sub>1_is_maximal\<^sub>l[OF \<P>\<^sub>G_Neg select\<^sub>G_empty]
          unfolding literal\<^sub>1_\<theta>[symmetric] \<sigma>(2)
          by simp
          
        moreover then have "is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<sigma>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<sigma>)"
          using 
            is_maximal\<^sub>l_ground_subst_stability'[OF 
              _  
              premise\<^sub>1_grounding[unfolded \<sigma>(2) clause_subst_compose]
            ]
            literal_in_clause_subst
            literal\<^sub>1_in_premise\<^sub>1
          by blast

        ultimately show ?thesis
          using \<P>\<^sub>G_Neg
          by simp
      next
        case select\<^sub>G_not_empty: False
        have "is_maximal\<^sub>l literal\<^sub>1 (select premise\<^sub>1)"
          using literal\<^sub>1_selected[OF \<P>\<^sub>G_Neg select\<^sub>G_not_empty].
  
        with select\<^sub>G_not_empty \<P>\<^sub>G_Neg show ?thesis 
          by simp
      qed
    qed
  next
    show "select premise\<^sub>2 = {#}"
      using clause_subst_empty ground_superpositionI(10) select(2)
      by auto
  next 
    have "is_strictly_maximal\<^sub>l (literal\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<sigma> \<cdot>l \<tau>) (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<sigma> \<cdot> \<tau>)"
      using literal\<^sub>G\<^sub>2_is_strictly_maximal\<^sub>l
      unfolding literal\<^sub>2_\<theta>[symmetric]  \<sigma>(2)
      by simp

    then show "is_strictly_maximal\<^sub>l (literal\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<sigma>) (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<sigma>)"
      using 
        is_strictly_maximal\<^sub>l_ground_subst_stability'[OF 
          _  premise\<^sub>2_grounding[unfolded \<sigma>(2) clause_subst_compose]
        ]
        literal\<^sub>2_in_premise\<^sub>2 
        literal_in_clause_subst 
      by blast
  next
    have term_groundings: 
      "is_ground_term (term\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<sigma> \<cdot>t \<tau>)" 
      "is_ground_term (context\<^sub>1\<langle>term\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<sigma> \<cdot>t \<tau>)" 
      unfolding 
        term\<^sub>1_with_context[symmetric]  
        term\<^sub>1_with_context_\<theta>[unfolded \<sigma>(2) term_subst_compose]
        term\<^sub>1'_\<theta>[unfolded \<sigma>(2) term_subst_compose]
      using ground_term_with_context_is_ground(1)
      by simp_all

    have "term\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<sigma> \<cdot>t \<tau> \<prec>\<^sub>t context\<^sub>1\<langle>term\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<sigma> \<cdot>t \<tau>"
      using ground_superpositionI(7) 
      unfolding 
        term\<^sub>1'_\<theta>[unfolded \<sigma>(2) term_subst_compose]
        term\<^sub>1_with_context[symmetric]
        term\<^sub>1_with_context_\<theta>[unfolded \<sigma>(2) term_subst_compose]
        less\<^sub>t\<^sub>G_def
        ground_term_with_context(3).
     
    then show "\<not> context\<^sub>1\<langle>term\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<sigma> \<preceq>\<^sub>t term\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<sigma>"
      using less\<^sub>t_less_eq\<^sub>t_ground_subst_stability[OF term_groundings]
      by blast
  next
    have term_groundings: 
      "is_ground_term (term\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<sigma> \<cdot>t \<tau>)" 
      "is_ground_term (term\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<sigma> \<cdot>t \<tau>)" 
      unfolding 
        term\<^sub>2_\<theta>[unfolded \<sigma>(2) term_subst_compose]
        term\<^sub>2'_\<theta>[unfolded \<sigma>(2) term_subst_compose]
      by simp_all

    have "term\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<sigma> \<cdot>t \<tau> \<prec>\<^sub>t term\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<sigma> \<cdot>t \<tau>"
      using ground_superpositionI(8) 
      unfolding 
        term\<^sub>2_\<theta>[unfolded \<sigma>(2) term_subst_compose]             
        term\<^sub>2'_\<theta>[unfolded \<sigma>(2) term_subst_compose]
        less\<^sub>t\<^sub>G_def.

    then show "\<not> term\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<sigma> \<preceq>\<^sub>t term\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<sigma>"
      using less\<^sub>t_less_eq\<^sub>t_ground_subst_stability[OF term_groundings]
      by blast
  next
    show "?conclusion' =  add_mset
     ((if \<P>\<^sub>G = Pos then Pos else Neg) (Upair (context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>term\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> (term\<^sub>1' \<cdot>t \<rho>\<^sub>1)))
     (premise\<^sub>1' \<cdot> \<rho>\<^sub>1 + premise\<^sub>2' \<cdot> \<rho>\<^sub>2) \<cdot> \<sigma>"
      using term\<^sub>2'_with_context(2) by blast
  qed

  have "term_subst.is_idem \<sigma>"
    using \<sigma>(1)
    by (simp add: term_subst.is_imgu_iff_is_idem_and_is_mgu)  

  then have \<sigma>_\<theta>: "\<sigma> \<odot> \<theta> = \<theta>"
    unfolding \<sigma>(2) term_subst.is_idem_def
    by (metis subst_compose_assoc)

  have "to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>) \<in> clause_groundings premise\<^sub>1"
    unfolding clause_groundings_def
    by (smt (verit, del_insts) clause_subst_compose mem_Collect_eq premise\<^sub>1_grounding)

  moreover have "to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>) \<in> clause_groundings premise\<^sub>2"
    unfolding clause_groundings_def
    by (smt (verit, del_insts) clause_subst_compose mem_Collect_eq premise\<^sub>2_grounding)

  moreover have "conclusion \<cdot> \<theta> = 
    add_mset (?\<P> (Upair (to_context context\<^sub>G)\<langle>to_term term\<^sub>G\<^sub>3\<rangle> (to_term term\<^sub>G\<^sub>2))) 
      (to_clause premise\<^sub>G\<^sub>1' + to_clause premise\<^sub>G\<^sub>2')"
    using ground_superpositionI(4, 12) to_ground_clause_inverse[OF conclusion_grounding] 
    unfolding ground_term_with_context(3) to_term_to_atom
    by(cases "\<P>\<^sub>G = Pos")(simp_all add: to_atom_to_literal to_clause_add_mset)

  then have conclusion_\<theta>: "conclusion \<cdot> \<theta> =  ?conclusion' \<cdot> \<theta>"
    unfolding 
      term\<^sub>2'_with_context[symmetric]
      premise\<^sub>1'_\<theta>[symmetric] 
      premise\<^sub>2'_\<theta>[symmetric] 
      term\<^sub>1'_\<theta>[symmetric]
      subst_clause_plus[symmetric] 
      subst_apply_term_ctxt_apply_distrib[symmetric]
      subst_atom[symmetric]
    apply(cases "\<P>\<^sub>G = Pos")
    using subst_clause_add_mset subst_literal \<sigma>_\<theta> clause_subst_compose
    by (smt (verit))+
    
  have "to_ground_clause (conclusion \<cdot> \<theta>) \<in> clause_groundings ?conclusion'"
    unfolding clause_groundings_def
    by (smt (verit, best) conclusion_\<theta> conclusion_grounding mem_Collect_eq)

  (* TODO: *)
  ultimately show ?thesis
    using that
    unfolding clause_groundings_def inference_groundings_def ground.G_Inf_def inferences_def
    using superposition
    apply simp
    by (metis conclusion_\<theta> conclusion_grounding ground_superposition premise\<^sub>1_grounding premise\<^sub>2_grounding renaming)
qed

abbreviation subst_stability_on where
  "subst_stability_on premises \<equiv>
    \<forall>premise\<^sub>G \<in> \<Union> (clause_groundings ` premises). \<exists>premise \<in> premises. \<exists>\<theta>. 
          premise \<cdot> \<theta> = to_clause premise\<^sub>G 
        \<and> to_clause (select\<^sub>G (to_ground_clause (premise \<cdot> \<theta>))) = (select premise) \<cdot> \<theta>"

(* TODO: Probably it is easier to combine these with the above ones or have a generic way for 
    converting the formats
*)
lemma equality_resolution_ground_instance': 
  assumes 
    "\<iota>\<^sub>G \<in> ground.equality_resolution_inferences"
    "\<iota>\<^sub>G \<in> ground.Inf_from_q select\<^sub>G (\<Union> (clause_groundings ` premises))"
    "subst_stability_on premises"
  shows "\<exists>\<iota> \<in> Inf_from premises. \<iota>\<^sub>G \<in> inference_groundings \<iota>"
proof-
  obtain premise\<^sub>G conclusion\<^sub>G where 
    \<iota>\<^sub>G : "\<iota>\<^sub>G = Infer [premise\<^sub>G] conclusion\<^sub>G" and
    ground_eq_resolution: "ground.ground_eq_resolution premise\<^sub>G conclusion\<^sub>G"
    using assms(1)
    by blast

  have premise\<^sub>G_in_groundings: "premise\<^sub>G \<in>  \<Union> (clause_groundings ` premises)"
    using assms(2)
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
    by simp
  
  obtain premise conclusion \<theta> where
    "to_clause premise\<^sub>G = premise \<cdot> \<theta>" and
    "to_clause conclusion\<^sub>G = conclusion \<cdot> \<theta>" and
    select: "to_clause (select\<^sub>G premise\<^sub>G) = select premise \<cdot> \<theta>" and
    premise_in_premises: "premise \<in> premises"
    using assms(2, 3) premise\<^sub>G_in_groundings
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def 
    by (metis (no_types, opaque_lifting) ground_clause_is_ground subst_ground_clause to_clause_inverse)
    
  then have 
    premise_grounding: "is_ground_clause (premise \<cdot> \<theta>)" and 
    premise\<^sub>G: "premise\<^sub>G = to_ground_clause (premise \<cdot> \<theta>)" and 
    conclusion_grounding: "is_ground_clause (conclusion \<cdot> \<theta>)" and
    conclusion\<^sub>G: "conclusion\<^sub>G = to_ground_clause (conclusion \<cdot> \<theta>)"
    by (smt ground_clause_is_ground to_clause_inverse)+
   
  obtain conclusion' where 
    equality_resolution: "equality_resolution premise conclusion'" and
    inference_groundings: 
      "Infer [to_ground_clause (premise \<cdot> \<theta>)] (to_ground_clause (conclusion' \<cdot> \<theta>)) \<in> 
        inference_groundings (Infer [premise] conclusion')" and  
    conclusion'_conclusion: "conclusion' \<cdot> \<theta> = conclusion \<cdot> \<theta>"
    using 
      equality_resolution_lifting[OF
        premise\<^sub>G
        conclusion\<^sub>G
        premise_grounding 
        conclusion_grounding 
        select 
        ground_eq_resolution
      ]
    premise\<^sub>G
    conclusion\<^sub>G
    by metis

  let ?\<iota> = "Infer [premise] conclusion'"

  have "?\<iota> \<in> Inf_from premises"
    using premise_in_premises  equality_resolution
    unfolding Inf_from_def inferences_def inference_system.Inf_from_def
    by simp

  moreover have "\<iota>\<^sub>G \<in> inference_groundings ?\<iota>"
    unfolding \<iota>\<^sub>G premise\<^sub>G conclusion\<^sub>G conclusion'_conclusion[symmetric]
    by(rule inference_groundings)

  ultimately show ?thesis
    by blast
qed 

lemma equality_factoring_ground_instance': 
  assumes 
    "\<iota>\<^sub>G \<in> ground.equality_factoring_inferences"
    "\<iota>\<^sub>G \<in> ground.Inf_from_q select\<^sub>G (\<Union> (clause_groundings ` premises))" 
    "subst_stability_on premises"
  shows  "\<exists>\<iota> \<in> Inf_from premises. \<iota>\<^sub>G \<in> inference_groundings \<iota>"
proof-
  obtain premise\<^sub>G conclusion\<^sub>G where 
    \<iota>\<^sub>G : "\<iota>\<^sub>G = Infer [premise\<^sub>G] conclusion\<^sub>G" and
    ground_eq_factoring: "ground.ground_eq_factoring premise\<^sub>G conclusion\<^sub>G"
    using assms(1)
    by blast

  have premise\<^sub>G_in_groundings: "premise\<^sub>G \<in>  \<Union> (clause_groundings ` premises)"
    using assms(2)
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
    by simp
  
  obtain premise conclusion \<theta> where
    "to_clause premise\<^sub>G = premise \<cdot> \<theta>" and
    "to_clause conclusion\<^sub>G = conclusion \<cdot> \<theta>" and
    select: "to_clause (select\<^sub>G (to_ground_clause (premise \<cdot> \<theta>))) = select premise \<cdot> \<theta>" and
    premise_in_premises: "premise \<in> premises"
    using assms(2, 3) premise\<^sub>G_in_groundings
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
    by (metis (no_types, opaque_lifting) ground_clause_is_ground subst_ground_clause)
    
  then have 
    premise_grounding: "is_ground_clause (premise \<cdot> \<theta>)" and 
    premise\<^sub>G: "premise\<^sub>G = to_ground_clause (premise \<cdot> \<theta>)" and 
    conclusion_grounding: "is_ground_clause (conclusion \<cdot> \<theta>)" and
    conclusion\<^sub>G: "conclusion\<^sub>G = to_ground_clause (conclusion \<cdot> \<theta>)"
    by (smt ground_clause_is_ground to_clause_inverse)+
   
  obtain conclusion' where 
    equality_factoring: "equality_factoring premise conclusion'" and
    inference_groundings: 
      "Infer [to_ground_clause (premise \<cdot> \<theta>)] (to_ground_clause (conclusion' \<cdot> \<theta>)) \<in> 
        inference_groundings (Infer [premise] conclusion')" and  
    conclusion'_conclusion: "conclusion' \<cdot> \<theta> = conclusion \<cdot> \<theta>"
    using 
      equality_factoring_lifting[OF 
        premise_grounding 
        conclusion_grounding 
        select 
        ground_eq_factoring[unfolded premise\<^sub>G conclusion\<^sub>G]
      ]
    by blast

  let ?\<iota> = "Infer [premise] conclusion'"

  have "?\<iota> \<in> Inf_from premises"
    using premise_in_premises  equality_factoring
    unfolding Inf_from_def inferences_def inference_system.Inf_from_def
    by simp

  moreover have "\<iota>\<^sub>G \<in> inference_groundings ?\<iota>"
    unfolding \<iota>\<^sub>G premise\<^sub>G conclusion\<^sub>G conclusion'_conclusion[symmetric]
    by(rule inference_groundings)

  ultimately show ?thesis
    by blast
qed

lemma superposition_ground_instance': 
  assumes 
    "\<iota>\<^sub>G \<in> ground.superposition_inferences"
    "\<iota>\<^sub>G \<in> ground.Inf_from_q select\<^sub>G (\<Union> (clause_groundings ` premises))" 
    "\<iota>\<^sub>G \<notin> ground.GRed_I (\<Union> (clause_groundings ` premises))"
    "subst_stability_on premises"
   shows  "\<exists>\<iota> \<in> Inf_from premises. \<iota>\<^sub>G \<in> inference_groundings \<iota>"
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

  obtain premise\<^sub>1 premise\<^sub>2 \<theta>\<^sub>1 \<theta>\<^sub>2 where
    premise\<^sub>1_\<theta>\<^sub>1: "premise\<^sub>1 \<cdot> \<theta>\<^sub>1 = to_clause premise\<^sub>G\<^sub>1" and
    premise\<^sub>2_\<theta>\<^sub>2: "premise\<^sub>2 \<cdot> \<theta>\<^sub>2 = to_clause premise\<^sub>G\<^sub>2" and
    select': 
      "to_clause (select\<^sub>G (to_ground_clause (premise\<^sub>1 \<cdot> \<theta>\<^sub>1))) = select premise\<^sub>1 \<cdot> \<theta>\<^sub>1"
      "to_clause (select\<^sub>G (to_ground_clause (premise\<^sub>2 \<cdot> \<theta>\<^sub>2))) = select premise\<^sub>2 \<cdot> \<theta>\<^sub>2" and
    premise\<^sub>1_in_premises: "premise\<^sub>1 \<in> premises" and
    premise\<^sub>2_in_premises: "premise\<^sub>2 \<in> premises"
     using assms(2, 4) premise\<^sub>G\<^sub>1_in_groundings premise\<^sub>G\<^sub>2_in_groundings
     unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
     by (metis (no_types, lifting))

  obtain \<rho>\<^sub>1 \<rho>\<^sub>2 where
    renaming: 
      "term_subst.is_renaming (\<rho>\<^sub>1 :: ('f, 'v) subst)" 
      "term_subst.is_renaming \<rho>\<^sub>2" 
      "\<rho>\<^sub>1 ` vars_clause premise\<^sub>1 \<inter> \<rho>\<^sub>2 ` vars_clause premise\<^sub>2 = {}"
    using clause_renaming_exists[of premise\<^sub>1 premise\<^sub>2]. 

  (* TODO: *)
  then have vars_distinct: "vars_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter> vars_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2) = {}"
    using renaming_vars_clause[symmetric]
    by (smt (verit, del_insts) disjoint_iff imageI)

  from renaming obtain \<rho>\<^sub>1_inv \<rho>\<^sub>2_inv where
     \<rho>\<^sub>1_inv: "\<rho>\<^sub>1 \<odot> \<rho>\<^sub>1_inv = Var" and
     \<rho>\<^sub>2_inv: "\<rho>\<^sub>2 \<odot> \<rho>\<^sub>2_inv = Var"
    unfolding term_subst.is_renaming_def
    by blast

  have select_subset: "select premise\<^sub>1 \<subseteq># premise\<^sub>1" "select premise\<^sub>2 \<subseteq># premise\<^sub>2"
    by (simp_all add: select_subset)

  then have a: "select premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<subseteq># premise\<^sub>1 \<cdot> \<rho>\<^sub>1"  "select premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<subseteq># premise\<^sub>2 \<cdot> \<rho>\<^sub>2"
    by (simp_all add: image_mset_subseteq_mono subst_clause_def)

  have "vars_clause (select premise\<^sub>2 \<cdot> \<rho>\<^sub>2) \<subseteq> vars_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2)"
    using clause_submset_vars_clause_subset[OF a(2)].

  then have b: "vars_clause (select premise\<^sub>2 \<cdot> \<rho>\<^sub>2) \<inter> vars_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) = {}"
    using vars_distinct
    by blast

  obtain \<theta> where "\<theta> = (\<lambda>var. 
      if var \<in> vars_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) 
      then (\<rho>\<^sub>1_inv \<odot> \<theta>\<^sub>1) var 
      else (\<rho>\<^sub>2_inv \<odot> \<theta>\<^sub>2) var
    )"
    by simp

  then have 
    premise\<^sub>1_\<theta>: "premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta> = to_clause premise\<^sub>G\<^sub>1" and
    premise\<^sub>2_\<theta>: "premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta> = to_clause premise\<^sub>G\<^sub>2" and
    select: 
      "to_clause (select\<^sub>G (to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>))) = select premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>"
      "to_clause (select\<^sub>G (to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>))) = select premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>"
    using premise\<^sub>1_\<theta>\<^sub>1 premise\<^sub>2_\<theta>\<^sub>2 select' 
       apply auto

    using \<rho>\<^sub>1_inv \<rho>\<^sub>2_inv 
       apply (metis (mono_tags, lifting) clause_subst_compose subst_clause_Var_ident)
      apply (metis \<rho>\<^sub>2_inv clause_subst_compose clause_subst_reduntant_if' inf_commute subst_clause_Var_ident vars_distinct)
    apply (metis (no_types, lifting) \<rho>\<^sub>1_inv a(1) clause_submset_vars_clause_subset clause_subst_compose clause_subst_eq select'(1) subset_eq subst_clause_Var_ident)
    by (metis Int_iff \<rho>\<^sub>2_inv all_not_in_conv b clause_subst_compose clause_subst_reduntant_if' subst_clause_Var_ident to_clause_inverse vars_distinct)
   
  obtain conclusion where conclusion_\<theta>: "to_clause conclusion\<^sub>G = conclusion \<cdot> \<theta>"
    by (metis ground_clause_is_ground subst_ground_clause)
   
  then have 
    premise\<^sub>1_grounding: "is_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)" and 
    premise\<^sub>2_grounding: "is_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>)" and 
    premise\<^sub>G\<^sub>1: "premise\<^sub>G\<^sub>1 = to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)" and 
    premise\<^sub>G\<^sub>2: "premise\<^sub>G\<^sub>2 = to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>)" and 
    conclusion_grounding: "is_ground_clause (conclusion \<cdot> \<theta>)" and
    conclusion\<^sub>G: "conclusion\<^sub>G = to_ground_clause (conclusion \<cdot> \<theta>)"
    apply (simp_all add: premise\<^sub>1_\<theta> premise\<^sub>2_\<theta>)
    by (smt ground_clause_is_ground to_clause_inverse)+

  have "clause_groundings premise\<^sub>1 \<union> clause_groundings premise\<^sub>2 \<subseteq> \<Union> (clause_groundings ` premises)"
    using premise\<^sub>1_in_premises premise\<^sub>2_in_premises by blast

  then have Infer_not_GRed_I:
    "Infer [to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>), to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)]
      (to_ground_clause (conclusion \<cdot> \<theta>)) \<notin>
      ground.GRed_I (clause_groundings premise\<^sub>1 \<union> clause_groundings premise\<^sub>2)"
    using assms(3) ground.Red_I_of_subset
    unfolding \<iota>\<^sub>G  premise\<^sub>G\<^sub>1[symmetric] premise\<^sub>G\<^sub>2[symmetric] conclusion\<^sub>G[symmetric]
    by blast

  have "\<exists>conclusion'. superposition premise\<^sub>2 premise\<^sub>1 conclusion' \<and>
    Infer [to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>), to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)]
      (to_ground_clause (conclusion' \<cdot> \<theta>)) \<in> inference_groundings (Infer [premise\<^sub>2, premise\<^sub>1] conclusion') \<and>
    conclusion' \<cdot> \<theta> = conclusion \<cdot> \<theta>"
  proof (rule superposition_lifting)
    show "term_subst.is_renaming \<rho>\<^sub>1"
      using renaming by argo
  next
    show "term_subst.is_renaming \<rho>\<^sub>2"
      using renaming by argo
  next
    show "vars_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter> vars_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2) = {}"
      using vars_distinct .
  next
    show "is_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)"
      using premise\<^sub>1_grounding .
  next
    show "is_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>)"
      using premise\<^sub>2_grounding .
  next
    show "is_ground_clause (conclusion \<cdot> \<theta>)"
      using conclusion_grounding .
  next
    show "to_clause (select\<^sub>G (to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>))) = select premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>"
      using select by argo
  next
    show "to_clause (select\<^sub>G (to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>))) = select premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>"
      using select by argo
  next
    show "ground.ground_superposition
      (to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>))
      (to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>))
      (to_ground_clause (conclusion \<cdot> \<theta>))"
      using ground_superposition unfolding premise\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>1 conclusion\<^sub>G .
  next
    show "Infer [to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>), to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)]
     (to_ground_clause (conclusion \<cdot> \<theta>))
    \<notin> ground.GRed_I (clause_groundings premise\<^sub>1 \<union> clause_groundings premise\<^sub>2)"
      using Infer_not_GRed_I .
  qed(auto)

 then obtain conclusion' where 
    superposition: "superposition premise\<^sub>2 premise\<^sub>1 conclusion'" and
    inference_groundings: 
      "Infer [to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>), to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)]
        (to_ground_clause (conclusion' \<cdot> \<theta>)) \<in> 
        inference_groundings (Infer [premise\<^sub>2, premise\<^sub>1] conclusion')" and  
    conclusion'_conclusion: "conclusion' \<cdot> \<theta> = conclusion \<cdot> \<theta>"
   by metis

   let ?\<iota> = "Infer [premise\<^sub>2, premise\<^sub>1] conclusion'"

   have "?\<iota> \<in> Inf_from premises"
    using premise\<^sub>1_in_premises premise\<^sub>2_in_premises superposition
    unfolding Inf_from_def inferences_def inference_system.Inf_from_def
    by simp

  moreover have "\<iota>\<^sub>G \<in> inference_groundings ?\<iota>"
    unfolding \<iota>\<^sub>G premise\<^sub>G\<^sub>1 premise\<^sub>G\<^sub>2 conclusion\<^sub>G conclusion'_conclusion[symmetric]
    by(rule inference_groundings)


  ultimately show ?thesis
    by blast
qed

lemma ground_instances: 
  assumes 
    "\<iota> \<in> ground.Inf_from_q select\<^sub>G (\<Union> (clause_groundings ` premises))" 
    "\<iota> \<notin> ground.Red_I (\<Union> (clause_groundings ` premises))"
    "subst_stability_on premises"
  shows "\<exists>\<iota>'\<in>Inf_from premises. \<iota> \<in> inference_groundings \<iota>'"
proof-
  have "\<iota> \<in> ground.superposition_inferences \<or>
        \<iota> \<in> ground.equality_resolution_inferences \<or>
        \<iota> \<in> ground.equality_factoring_inferences"
    using assms(1)
    unfolding 
      ground.Inf_from_q_def 
      ground.Inf_from_def 
      ground.G_Inf_def 
      inference_system.Inf_from_def
    by auto

  then show ?thesis
    using 
      assms
      equality_resolution_ground_instance'
      equality_factoring_ground_instance'
      superposition_ground_instance'
    by presburger
qed

end

lemma for_all_elements_exists_f_implies_f_exists_for_all_elements: 
  "\<forall>x \<in> X. \<exists>f. P (f x) x \<Longrightarrow> \<exists>f. \<forall>x\<in> X. P (f x) x"
  by meson

lemma necessary_select\<^sub>G_exists:
  obtains select\<^sub>G where 
      "\<forall>premise\<^sub>G \<in> \<Union>(clause_groundings ` premises). \<exists>premise \<theta>. 
          premise \<cdot> \<theta> = to_clause premise\<^sub>G 
        \<and> select\<^sub>G premise\<^sub>G = to_ground_clause ((sel premise) \<cdot> \<theta>)
        \<and> premise \<in> premises" 
      "is_select_grounding sel select\<^sub>G"
proof-
  let ?premise_groundings = "\<Union>(clause_groundings ` premises)"
  
  have select\<^sub>G_exists_for_premises: "\<forall>premise\<^sub>G \<in> ?premise_groundings. \<exists>select\<^sub>G premise \<theta>.
          premise \<cdot> \<theta> = to_clause premise\<^sub>G 
        \<and> select\<^sub>G premise\<^sub>G = to_ground_clause ((sel premise) \<cdot> \<theta>)
        \<and> premise \<in> premises"
    unfolding clause_groundings_def
    by fastforce

  obtain select\<^sub>G_on_premise_groundings where 
    select\<^sub>G_on_premise_groundings: "\<forall>premise\<^sub>G \<in>?premise_groundings. \<exists>\<theta> premise. 
        premise \<cdot> \<theta> = to_clause premise\<^sub>G 
      \<and> select\<^sub>G_on_premise_groundings (to_ground_clause (premise \<cdot> \<theta>)) = 
          to_ground_clause ((sel premise) \<cdot> \<theta>)
      \<and> premise \<in> premises"
    using 
      for_all_elements_exists_f_implies_f_exists_for_all_elements[OF select\<^sub>G_exists_for_premises]
    by (metis (mono_tags, opaque_lifting) to_clause_inverse)
 
  define select\<^sub>G where
    select\<^sub>G_def: "\<And>clause\<^sub>G. select\<^sub>G clause\<^sub>G = (
        if clause\<^sub>G  \<in> ?premise_groundings 
        then select\<^sub>G_on_premise_groundings clause\<^sub>G 
        else to_ground_clause (sel (to_clause clause\<^sub>G))
    )"

  have "is_select_grounding sel select\<^sub>G"
    unfolding is_select_grounding_def select\<^sub>G_def
    using select\<^sub>G_on_premise_groundings
    by (metis ground_clause_is_ground subst_clause_Var_ident to_clause_inverse)
  
  then show ?thesis
    using select\<^sub>G_def select\<^sub>G_on_premise_groundings that 
    by (metis to_clause_inverse)
qed

lemma (in first_order_superposition_calculus) ground_instances:
  obtains select\<^sub>G where
    "ground_Inf_overapproximated select\<^sub>G premises"
    "is_grounding select\<^sub>G"
proof-
  obtain select\<^sub>G where   
      select\<^sub>G': "\<forall>premise\<^sub>G \<in> \<Union>(clause_groundings ` premises). \<exists>\<theta> premise. 
          premise \<cdot> \<theta> = to_clause premise\<^sub>G 
        \<and> to_clause (select\<^sub>G (to_ground_clause (premise \<cdot> \<theta>))) = (select premise) \<cdot> \<theta>
        \<and> premise \<in> premises" and
       "is_grounding select\<^sub>G" 
    using necessary_select\<^sub>G_exists
    by (metis (mono_tags, opaque_lifting) ground_clause_is_ground select_subst1 to_clause_inverse 
         to_ground_clause_inverse)

  then interpret grounded_first_order_superposition_calculus _ _ select\<^sub>G
    by unfold_locales

  from select\<^sub>G'(1) have "ground_Inf_overapproximated select\<^sub>G premises"
    using ground_instances  
    apply auto
    by blast

  with that select\<^sub>G show thesis
    by blast
qed

sublocale first_order_superposition_calculus \<subseteq> 
  statically_complete_calculus "\<bottom>\<^sub>F" inferences entails_\<G> Red_I_\<G> Red_F_\<G>
  unfolding static_empty_ord_inter_equiv_static_inter
proof(rule stat_ref_comp_to_non_ground_fam_inter, rule ballI)
  fix select\<^sub>G
  assume "select\<^sub>G \<in> select\<^sub>G\<^sub>s"
  then interpret grounded_first_order_superposition_calculus _ _ select\<^sub>G
    by unfold_locales (simp add: select\<^sub>G\<^sub>s_def)

  show "statically_complete_calculus 
          ground.G_Bot 
          ground.G_Inf 
          ground.G_entails 
          ground.Red_I 
          ground.Red_F"
    using ground.statically_complete_calculus_axioms 
    by blast
next
  have "\<And>N. \<exists>select\<^sub>G \<in> select\<^sub>G\<^sub>s. ground_Inf_overapproximated select\<^sub>G N" 
    using ground_instances
    by (smt (verit, ccfv_threshold) mem_Collect_eq select\<^sub>G\<^sub>s_def)
    
  then show "\<And>N. empty_ord.saturated N \<Longrightarrow> 
    \<exists>select\<^sub>G \<in> select\<^sub>G\<^sub>s. ground_Inf_overapproximated select\<^sub>G N".
qed 

end
