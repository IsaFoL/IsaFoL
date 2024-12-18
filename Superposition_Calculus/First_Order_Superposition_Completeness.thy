theory First_Order_Superposition_Completeness
  imports
    Ground_Superposition_Completeness
    Grounded_Superposition
    Nonground_Entailment
    Superposition_Welltypedness_Preservation
begin

context grounded_superposition_calculus
begin

lemma eq_resolution_lifting:
  fixes
    D\<^sub>G C\<^sub>G :: "'f ground_atom clause" and
    D C :: "('f, 'v) atom clause" and
    \<gamma> :: "('f, 'v) subst"
  defines
    D\<^sub>G [simp]: "D\<^sub>G \<equiv> clause.to_ground (D \<cdot> \<gamma>)" and
    C\<^sub>G [simp]: "C\<^sub>G \<equiv> clause.to_ground (C \<cdot> \<gamma>)"
  assumes
    ground_eq_resolution: "ground.eq_resolution D\<^sub>G C\<^sub>G" and
    D_grounding: "clause.is_ground (D \<cdot> \<gamma>)" and 
    C_grounding: "clause.is_ground (C \<cdot> \<gamma>)" and
    select: "clause.from_ground (select\<^sub>G D\<^sub>G) = (select D) \<cdot> \<gamma>" and
    D_is_welltyped: "clause.is_welltyped \<V> D" and
    \<gamma>_is_welltyped: "is_welltyped_on (clause.vars D) \<V> \<gamma>" and
    \<V>: "infinite_variables_per_type \<V>"
  obtains C'
  where
    "eq_resolution (D, \<V>) (C', \<V>)"
    "Infer [D\<^sub>G] C\<^sub>G \<in> inference_groundings (Infer [(D, \<V>)] (C', \<V>))"
    "C' \<cdot> \<gamma> = C \<cdot> \<gamma>"
  using ground_eq_resolution
proof(cases D\<^sub>G C\<^sub>G rule: ground.eq_resolution.cases)
  case ground_eq_resolutionI: (eq_resolutionI l\<^sub>G D\<^sub>G' t\<^sub>G)

  let ?select\<^sub>G_empty = "select\<^sub>G D\<^sub>G = {#}"
  let ?select\<^sub>G_not_empty = "select\<^sub>G D\<^sub>G \<noteq> {#}"

  obtain l where
    l_\<gamma>: "l \<cdot>l \<gamma> = term.from_ground t\<^sub>G !\<approx> term.from_ground t\<^sub>G" and
    l_in_D: "l \<in># D" and
    l_selected: "?select\<^sub>G_not_empty \<Longrightarrow> is_maximal l (select D)" and
    l_\<gamma>_selected: "?select\<^sub>G_not_empty \<Longrightarrow> is_maximal (l \<cdot>l \<gamma>) (select D \<cdot> \<gamma>)" and
    l_is_maximal: "?select\<^sub>G_empty \<Longrightarrow> is_maximal l D" and
    l_\<gamma>_is_maximal: "?select\<^sub>G_empty \<Longrightarrow> is_maximal (l \<cdot>l \<gamma>) (D \<cdot> \<gamma>)"
  proof-
    obtain max_l where 
     "is_maximal max_l D" and
      is_max_in_D_\<gamma>: "is_maximal (max_l \<cdot>l \<gamma>) (D \<cdot> \<gamma>)"
    proof-
      have "D \<noteq> {#}"
        using ground_eq_resolutionI(1)
        unfolding D\<^sub>G
        by auto

      then show ?thesis
        using that D_grounding obtain_maximal_literal
        by blast
    qed

    moreover then have "max_l \<in># D"
      unfolding is_maximal_def 
      by blast

    moreover have "max_l \<cdot>l \<gamma> = term.from_ground t\<^sub>G !\<approx> term.from_ground t\<^sub>G" if ?select\<^sub>G_empty
    proof-
      have "ground_is_maximal l\<^sub>G D\<^sub>G"
        using ground_eq_resolutionI(3) that
        unfolding is_maximal_def
        by simp

      then show ?thesis
        using unique_maximal_in_ground_clause[OF D_grounding is_max_in_D_\<gamma>] D_grounding
        unfolding ground_eq_resolutionI(2) D\<^sub>G
        by simp
    qed

    moreover obtain selected_l where 
      "selected_l \<cdot>l \<gamma> = term.from_ground t\<^sub>G !\<approx> term.from_ground t\<^sub>G" and
      "is_maximal selected_l (select D)"
      "is_maximal (selected_l \<cdot>l \<gamma>) (select D \<cdot> \<gamma>)"
    if ?select\<^sub>G_not_empty
    proof-
      have "is_maximal (term.from_ground t\<^sub>G !\<approx> term.from_ground t\<^sub>G) (select D \<cdot> \<gamma>)" 
        if ?select\<^sub>G_not_empty
        using ground_eq_resolutionI(3) that select
        unfolding ground_eq_resolutionI(2) D\<^sub>G
        by simp

      then show ?thesis
        using
          that
          obtain_maximal_literal[OF _ select_ground_subst[OF D_grounding]]
          unique_maximal_in_ground_clause[OF select_ground_subst[OF D_grounding]]
        by (metis is_maximal_empty clause_subst_empty)
    qed

    moreover then have "selected_l \<in># D" if ?select\<^sub>G_not_empty
      by (meson that maximal_in_clause mset_subset_eqD select_subset)

    ultimately show ?thesis
      using that
      by blast
  qed

  obtain C' where D: "D = add_mset l C'"
    using multi_member_split[OF l_in_D]
    by blast

  obtain t t' where l: "l = t !\<approx> t'"
    using l_\<gamma> obtain_from_neg_literal_subst
    by meson

  obtain \<mu> \<sigma> where \<gamma>: "\<gamma> = \<mu> \<odot> \<sigma>" and imgu: "welltyped_imgu \<V> t t' \<mu>"
  proof-
    have unified: "t \<cdot>t \<gamma> = t' \<cdot>t \<gamma>"
      using l_\<gamma>
      unfolding l
      by simp

    moreover obtain \<tau> where welltyped: "welltyped \<V> t \<tau>" "welltyped \<V> t' \<tau>"
      using D_is_welltyped
      unfolding D l
      by auto

    show ?thesis
      using welltyped_imgu_exists[OF unified welltyped] that
      by metis
  qed

  have eq_resolution: "eq_resolution (D, \<V>) (C' \<cdot> \<mu>, \<V>)"
  proof (rule eq_resolutionI, rule D, rule l, rule imgu)
    show "select D = {#} \<and> is_maximal (l \<cdot>l \<mu>) (D \<cdot> \<mu>) \<or> is_maximal (l \<cdot>l \<mu>) ((select D) \<cdot> \<mu>)"
    proof(cases ?select\<^sub>G_empty)
      case True

      moreover have "is_maximal (l \<cdot>l \<mu>) (D \<cdot> \<mu>)"
      proof-
        have "l \<cdot>l \<mu> \<in># D \<cdot> \<mu>"
          using l_in_D 
          by blast

        then show ?thesis
          using l_\<gamma>_is_maximal[OF True] is_maximal_if_grounding_is_maximal D_grounding
          unfolding \<gamma>
          by simp
      qed

      ultimately show ?thesis
        using select
        by simp
    next
      case False

      have "l \<cdot>l \<mu> \<in># select D \<cdot> \<mu>"
        using l_selected[OF False] maximal_in_clause
        by blast

      then have "is_maximal (l \<cdot>l \<mu>) (select D \<cdot> \<mu>)"
        using 
          select_ground_subst[OF D_grounding]
          l_\<gamma>_selected[OF False] 
          is_maximal_if_grounding_is_maximal 
        unfolding \<gamma>
        by auto

      then show ?thesis
        using select
        by blast
    qed
  qed simp

  have C_\<gamma>: "C \<cdot> \<gamma> = C' \<cdot> \<mu> \<cdot> \<gamma>"
  proof-
    have "term.is_idem \<mu>"
      using imgu 
      unfolding term_subst.is_imgu_iff_is_idem_and_is_mgu 
      by blast  

    then have \<mu>_\<gamma>: "\<mu> \<odot> \<gamma> = \<gamma>"
      unfolding \<gamma> term_subst.is_idem_def subst_compose_assoc[symmetric]
      by argo

    have "D \<cdot> \<gamma> = add_mset (l \<cdot>l \<gamma>) (C \<cdot> \<gamma>)"
    proof-
      have "clause.to_ground (D \<cdot> \<gamma>) = clause.to_ground (add_mset (l \<cdot>l \<gamma>) (C \<cdot> \<gamma>))"
        using ground_eq_resolutionI(1)
        unfolding D\<^sub>G ground_eq_resolutionI(2) l_\<gamma> ground_eq_resolutionI(4)[symmetric]
        by simp 

      moreover have "clause.is_ground (add_mset (l \<cdot>l \<gamma>) (C \<cdot> \<gamma>))"
        using C_grounding clause.to_set_is_ground_subst[OF l_in_D D_grounding]
        by simp

      ultimately show ?thesis
        using clause.to_ground_eq[OF D_grounding]
        by blast
    qed

    then have "C \<cdot> \<gamma> = C' \<cdot> \<gamma>"
      unfolding D
      by simp

    then show ?thesis
      unfolding clause.subst_comp_subst[symmetric] \<mu>_\<gamma>.
  qed
 
  moreover have "Infer [D\<^sub>G] C\<^sub>G \<in> inference_groundings (Infer [(D, \<V>)] (C' \<cdot> \<mu>, \<V>))"
  proof-

    have "is_inference_grounding_one_premise (D, \<V>) (C' \<cdot> \<mu>, \<V>) (Infer [D\<^sub>G] C\<^sub>G) \<gamma>"
    proof(unfold split, intro conjI; (rule D_grounding D_is_welltyped refl \<V>)?)
      show "clause.is_ground (C' \<cdot> \<mu> \<cdot> \<gamma>)"
        using C_grounding C_\<gamma> 
        by argo
    next
      show "Infer [D\<^sub>G] C\<^sub>G = Infer [clause.to_ground (D \<cdot> \<gamma>)] (clause.to_ground (C' \<cdot> \<mu> \<cdot> \<gamma>))"
        using C_\<gamma>
        by simp
    next
      have "clause.vars (C' \<cdot> \<mu>) \<subseteq> clause.vars D"
        using clause.variables_in_base_imgu imgu
        unfolding D l
        by auto

      then show "is_welltyped_on (clause.vars (C' \<cdot> \<mu>)) \<V> \<gamma>"
        using D_is_welltyped \<gamma>_is_welltyped
        by blast
    next
      show "clause.is_welltyped \<V> (C' \<cdot> \<mu>)"
        using D_is_welltyped eq_resolution eq_resolution_preserves_typing
        by blast
    qed

    moreover have "Infer [D\<^sub>G] C\<^sub>G \<in> ground.G_Inf"
      unfolding ground.G_Inf_def
      using ground_eq_resolution
      by blast

    ultimately show ?thesis
      unfolding inference_groundings_def
      by auto
  qed

  ultimately show ?thesis
    using that[OF eq_resolution]
    by presburger
qed

lemma eq_factoring_lifting:
  fixes 
    D\<^sub>G C\<^sub>G :: "'f ground_atom clause" and 
    D C :: "('f, 'v) atom clause" and
    \<gamma> :: "('f, 'v) subst"
  defines 
    D\<^sub>G [simp]: "D\<^sub>G \<equiv> clause.to_ground (D \<cdot> \<gamma>)" and
    C\<^sub>G [simp]: "C\<^sub>G \<equiv> clause.to_ground (C \<cdot> \<gamma>)"
  assumes
    ground_eq_factoring: "ground.eq_factoring D\<^sub>G C\<^sub>G" and
    D_grounding: "clause.is_ground (D \<cdot> \<gamma>)" and
    C_grounding: "clause.is_ground (C \<cdot> \<gamma>)" and
    select: "clause.from_ground (select\<^sub>G D\<^sub>G) = (select D) \<cdot> \<gamma>" and
    D_is_welltyped: "clause.is_welltyped \<V> D" and
    \<gamma>_is_welltyped: "is_welltyped_on (clause.vars D) \<V> \<gamma>" and
    \<V>: "infinite_variables_per_type \<V>"
  obtains C' 
  where
    "eq_factoring (D, \<V>) (C', \<V>)"
    "Infer [D\<^sub>G] C\<^sub>G \<in> inference_groundings (Infer [(D, \<V>)] (C', \<V>))"
    "C' \<cdot> \<gamma> = C \<cdot> \<gamma>"
  using ground_eq_factoring
proof(cases D\<^sub>G C\<^sub>G rule: ground.eq_factoring.cases)
  case ground_eq_factoringI: (eq_factoringI l\<^sub>G\<^sub>1 l\<^sub>G\<^sub>2 D\<^sub>G' t\<^sub>G\<^sub>1 t\<^sub>G\<^sub>2 t\<^sub>G\<^sub>3)

  have "D \<noteq> {#}"
    using ground_eq_factoringI(1)
    by auto

  then obtain l\<^sub>1 where 
    l\<^sub>1_is_maximal: "is_maximal l\<^sub>1 D" and
    l\<^sub>1_\<gamma>_is_maximal: "is_maximal (l\<^sub>1 \<cdot>l \<gamma>) (D \<cdot> \<gamma>)"
    using that obtain_maximal_literal D_grounding
    by blast

  obtain t\<^sub>1 t\<^sub>1' where
    l\<^sub>1: "l\<^sub>1 = t\<^sub>1 \<approx> t\<^sub>1'" and
    l\<^sub>1_\<gamma>: "l\<^sub>1 \<cdot>l \<gamma> = term.from_ground t\<^sub>G\<^sub>1 \<approx> term.from_ground t\<^sub>G\<^sub>2" and
    t\<^sub>1_\<gamma>: "t\<^sub>1 \<cdot>t \<gamma> = term.from_ground t\<^sub>G\<^sub>1" and
    t\<^sub>1'_\<gamma>: "t\<^sub>1' \<cdot>t \<gamma> = term.from_ground t\<^sub>G\<^sub>2"
  proof-
    have "is_maximal (literal.from_ground l\<^sub>G\<^sub>1) (D \<cdot> \<gamma>)"
      using ground_eq_factoringI(5)
      unfolding D\<^sub>G clause.to_ground_inverse[OF D_grounding].

    then have "l\<^sub>1 \<cdot>l \<gamma> = term.from_ground t\<^sub>G\<^sub>1 \<approx> term.from_ground t\<^sub>G\<^sub>2"
      unfolding  ground_eq_factoringI(2)
      using unique_maximal_in_ground_clause[OF D_grounding l\<^sub>1_\<gamma>_is_maximal]
      by simp

    then show ?thesis
      using that
      unfolding ground_eq_factoringI(2)
      by (metis obtain_from_pos_literal_subst)
  qed

  obtain l\<^sub>2 D' where 
    l\<^sub>2_\<gamma>: "l\<^sub>2 \<cdot>l \<gamma> = term.from_ground t\<^sub>G\<^sub>1 \<approx> term.from_ground t\<^sub>G\<^sub>3" and
    D: "D = add_mset l\<^sub>1 (add_mset l\<^sub>2 D')"
  proof-
    obtain D'' where D: "D = add_mset l\<^sub>1 D''"
      using maximal_in_clause[OF l\<^sub>1_is_maximal]
      by (meson multi_member_split)

    moreover have "D \<cdot> \<gamma> = clause.from_ground (add_mset l\<^sub>G\<^sub>1 (add_mset l\<^sub>G\<^sub>2 D\<^sub>G'))"
      using ground_eq_factoringI(1) D\<^sub>G
      by (metis D_grounding clause.to_ground_inverse)

    ultimately have "D'' \<cdot> \<gamma> =  add_mset (literal.from_ground l\<^sub>G\<^sub>2) (clause.from_ground D\<^sub>G')"
      using  l\<^sub>1_\<gamma>
      by (simp add: ground_eq_factoringI(2))

    then obtain l\<^sub>2 where "l\<^sub>2 \<cdot>l \<gamma> = term.from_ground t\<^sub>G\<^sub>1 \<approx> term.from_ground t\<^sub>G\<^sub>3" "l\<^sub>2 \<in># D''"
      unfolding clause.subst_def ground_eq_factoringI
      using msed_map_invR
      by force

    then show ?thesis
      using that
      unfolding D
      by (metis mset_add)
  qed

  then obtain t\<^sub>2 t\<^sub>2' where 
    l\<^sub>2: "l\<^sub>2 = t\<^sub>2 \<approx> t\<^sub>2'" and
    t\<^sub>2_\<gamma>: "t\<^sub>2 \<cdot>t \<gamma> = term.from_ground t\<^sub>G\<^sub>1" and
    t\<^sub>2'_\<gamma>: "t\<^sub>2' \<cdot>t \<gamma> = term.from_ground t\<^sub>G\<^sub>3"
    unfolding ground_eq_factoringI(3) 
    using obtain_from_pos_literal_subst
    by metis

  have D'_\<gamma>: "D' \<cdot> \<gamma> = clause.from_ground D\<^sub>G'" 
    using D D_grounding ground_eq_factoringI(1,2,3) l\<^sub>1_\<gamma> l\<^sub>2_\<gamma> 
    by force

  obtain \<mu> \<sigma> where \<gamma>: "\<gamma> = \<mu> \<odot> \<sigma>" and imgu: "welltyped_imgu \<V> t\<^sub>1 t\<^sub>2 \<mu>"
  proof-
    have unified: "t\<^sub>1 \<cdot>t \<gamma> = t\<^sub>2 \<cdot>t \<gamma>"
      unfolding t\<^sub>1_\<gamma> t\<^sub>2_\<gamma> ..

    then obtain \<tau> where "welltyped \<V> (t\<^sub>1 \<cdot>t \<gamma>) \<tau>" "welltyped \<V> (t\<^sub>2 \<cdot>t \<gamma>) \<tau>"
      using D_is_welltyped \<gamma>_is_welltyped
      unfolding D l\<^sub>1 l\<^sub>2
      by auto

    then have welltyped: "welltyped \<V> t\<^sub>1 \<tau>" "welltyped \<V> t\<^sub>2 \<tau>"
      using \<gamma>_is_welltyped
      unfolding D l\<^sub>1 l\<^sub>2
      by simp_all

    then show ?thesis
      using welltyped_imgu_exists[OF unified welltyped] that
      by metis
  qed

  let ?C' = "add_mset (t\<^sub>1 \<approx> t\<^sub>2') (add_mset (t\<^sub>1' !\<approx> t\<^sub>2') D')"

  have eq_factoring: "eq_factoring (D, \<V>) (?C' \<cdot> \<mu>, \<V>)"
  proof (rule eq_factoringI; (rule D l\<^sub>1 l\<^sub>2 imgu refl)?)
    show "select D = {#}"
      using ground_eq_factoringI(4) select
      by simp
  next
    have "l\<^sub>1 \<cdot>l \<mu> \<in># D \<cdot> \<mu>"
      using l\<^sub>1_is_maximal clause.subst_in_to_set_subst maximal_in_clause 
      by blast

    then show "is_maximal (l\<^sub>1 \<cdot>l \<mu>) (D \<cdot> \<mu>)"
      using is_maximal_if_grounding_is_maximal D_grounding l\<^sub>1_\<gamma>_is_maximal
      unfolding \<gamma>
      by auto
  next
    have groundings: "term.is_ground (t\<^sub>1' \<cdot>t \<mu> \<cdot>t \<sigma>)" "term.is_ground (t\<^sub>1 \<cdot>t \<mu> \<cdot>t \<sigma>)"
      using t\<^sub>1'_\<gamma> t\<^sub>1_\<gamma>
      unfolding \<gamma>
      by simp_all

    have "t\<^sub>1' \<cdot>t \<gamma> \<prec>\<^sub>t t\<^sub>1 \<cdot>t \<gamma>"
      using ground_eq_factoringI(6)
      unfolding t\<^sub>1'_\<gamma> t\<^sub>1_\<gamma> term.order.less\<^sub>G_def.

    then show "\<not> t\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t t\<^sub>1' \<cdot>t \<mu>"
      unfolding \<gamma> 
      using term.order.ground_less_not_less_eq[OF groundings]
      by simp
  qed

  have C_\<gamma>: "C \<cdot> \<gamma> = ?C' \<cdot> \<mu> \<cdot> \<gamma>"
  proof-
    have "term.is_idem \<mu>"
      using imgu 
      unfolding term_subst.is_imgu_iff_is_idem_and_is_mgu 
      by blast  

    then have \<mu>_\<gamma>: "\<mu> \<odot> \<gamma> = \<gamma>"
      unfolding \<gamma> term_subst.is_idem_def subst_compose_assoc[symmetric]
      by argo

    have "C \<cdot> \<gamma> = clause.from_ground (add_mset (t\<^sub>G\<^sub>2 !\<approx> t\<^sub>G\<^sub>3) (add_mset (t\<^sub>G\<^sub>1 \<approx> t\<^sub>G\<^sub>3) D\<^sub>G'))"
      using ground_eq_factoringI(7) clause.to_ground_eq[OF C_grounding clause.ground_is_ground]
      unfolding C\<^sub>G
      by (metis clause.from_ground_inverse)

    also have "... = ?C' \<cdot> \<gamma>"
      using t\<^sub>1_\<gamma> t\<^sub>1'_\<gamma> t\<^sub>2'_\<gamma> D'_\<gamma>
      by simp

    also have "... = ?C' \<cdot> \<mu> \<cdot> \<gamma>"
      unfolding clause.subst_comp_subst[symmetric] \<mu>_\<gamma> ..
      
    finally show ?thesis.
  qed

  moreover have "Infer [D\<^sub>G] C\<^sub>G \<in> inference_groundings (Infer [(D, \<V>)] (?C' \<cdot> \<mu>, \<V>))"
  proof-
    have "is_inference_grounding_one_premise (D, \<V>) (?C' \<cdot> \<mu>, \<V>) (Infer [D\<^sub>G] C\<^sub>G) \<gamma>"
    proof(unfold split, intro conjI; (rule D_grounding D_is_welltyped refl \<V>)?)
      show "clause.is_ground (?C' \<cdot> \<mu> \<cdot> \<gamma>)"
        using C_grounding C_\<gamma>
        by argo
    next
      show "Infer [D\<^sub>G] C\<^sub>G = Infer [clause.to_ground (D \<cdot> \<gamma>)] (clause.to_ground (?C' \<cdot> \<mu> \<cdot> \<gamma>))"
        using C_\<gamma>
        by simp
    next
      have imgu: "term.is_imgu \<mu> {{t\<^sub>1, t\<^sub>2}}"
        using imgu
        by blast

      have "clause.vars (?C' \<cdot> \<mu>) \<subseteq> clause.vars D"
        using clause.variables_in_base_imgu[OF imgu, of ?C']
        unfolding D l\<^sub>1 l\<^sub>2
        by auto

      then show "is_welltyped_on (clause.vars (?C' \<cdot> \<mu>)) \<V> \<gamma>"
        using D_is_welltyped \<gamma>_is_welltyped
        by blast
    next
      show "clause.is_welltyped \<V> (?C' \<cdot> \<mu>)"
        using D_is_welltyped eq_factoring eq_factoring_preserves_typing
        by blast
    qed

    moreover have "Infer [D\<^sub>G] C\<^sub>G \<in> ground.G_Inf"
      unfolding ground.G_Inf_def
      using ground_eq_factoring
      by blast

    ultimately show ?thesis
      unfolding inference_groundings_def
      by auto
  qed

  ultimately show ?thesis
    using that[OF eq_factoring]
    by presburger
qed

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
    "premise_groundings \<equiv> clause_groundings (premise\<^sub>1, \<V>\<^sub>1) \<union> clause_groundings (premise\<^sub>2, \<V>\<^sub>2)" and
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
    ground_superposition: "ground.superposition premise\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>1 conclusion\<^sub>G" and
    non_redundant: "\<iota>\<^sub>G \<notin> ground.Red_I premise_groundings" and
    typing:
    "clause.is_welltyped \<V>\<^sub>1 premise\<^sub>1"
    "clause.is_welltyped \<V>\<^sub>2 premise\<^sub>2"
    (*"term_subst.is_ground_subst \<gamma>"*)
    "is_welltyped_on (clause.vars premise\<^sub>1) \<V>\<^sub>1 (\<rho>\<^sub>1 \<odot> \<gamma>)"
    "is_welltyped_on (clause.vars premise\<^sub>2) \<V>\<^sub>2 (\<rho>\<^sub>2 \<odot> \<gamma>)"
    "is_welltyped_on (clause.vars premise\<^sub>1) \<V>\<^sub>1 \<rho>\<^sub>1"
    "is_welltyped_on (clause.vars premise\<^sub>2) \<V>\<^sub>2 \<rho>\<^sub>2"
    "infinite_variables_per_type \<V>\<^sub>1" "infinite_variables_per_type \<V>\<^sub>2"
  obtains conclusion' \<V>\<^sub>3
  where
    "superposition (premise\<^sub>2, \<V>\<^sub>2) (premise\<^sub>1, \<V>\<^sub>1) (conclusion', \<V>\<^sub>3)"
    "\<iota>\<^sub>G \<in> inference_groundings (Infer [(premise\<^sub>2, \<V>\<^sub>2), (premise\<^sub>1, \<V>\<^sub>1)] (conclusion', \<V>\<^sub>3))"
    "conclusion' \<cdot> \<gamma> = conclusion \<cdot> \<gamma>"
  using ground_superposition
proof(cases premise\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>1 conclusion\<^sub>G rule: ground.superposition.cases)
  case ground_superpositionI: (superpositionI 
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
    "is_strictly_maximal (literal.from_ground literal\<^sub>G\<^sub>1) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)" if "\<P>\<^sub>G = Pos"
    using ground_superpositionI(9) that
    by(simp add: premise\<^sub>1_grounding)

  have neg_literal\<^sub>G\<^sub>1_is_maximal\<^sub>l: 
    "is_maximal (literal.from_ground literal\<^sub>G\<^sub>1) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)" if ?select\<^sub>G_empty
    using
      that
      ground_superpositionI(9)  
      is_maximal_if_is_strictly_maximal 
      is_maximal_empty
      premise\<^sub>1_\<gamma>
    by auto

  obtain pos_literal\<^sub>1 where
    "is_strictly_maximal pos_literal\<^sub>1 premise\<^sub>1"
    "pos_literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma> = literal.from_ground literal\<^sub>G\<^sub>1" 
  if "\<P>\<^sub>G = Pos"
    using obtain_strictly_maximal_literal[OF 
        premise\<^sub>1_grounding[folded clause.subst_comp_subst] 
        pos_literal\<^sub>G\<^sub>1_is_strictly_maximal\<^sub>l
        ]
    by metis

  moreover then have "pos_literal\<^sub>1 \<in># premise\<^sub>1" if "\<P>\<^sub>G = Pos"
    using that strictly_maximal_in_clause by fastforce

  moreover obtain neg_max_literal\<^sub>1 where
    "is_maximal neg_max_literal\<^sub>1 premise\<^sub>1"
    "neg_max_literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma> = literal.from_ground literal\<^sub>G\<^sub>1" 
  if "\<P>\<^sub>G = Neg" ?select\<^sub>G_empty
    using 
      obtain_maximal_literal[OF 
        premise\<^sub>1_not_empty 
        premise\<^sub>1_grounding[folded clause.subst_comp_subst]
        ]
      neg_literal\<^sub>G\<^sub>1_is_maximal\<^sub>l
    by (metis (no_types, opaque_lifting) assms(9) clause.comp_subst.left.monoid_action_compatibility unique_maximal_in_ground_clause)

  moreover then have "neg_max_literal\<^sub>1 \<in># premise\<^sub>1" if "\<P>\<^sub>G = Neg" ?select\<^sub>G_empty
    using that maximal_in_clause by fastforce

  moreover obtain neg_selected_literal\<^sub>1 where
    "is_maximal neg_selected_literal\<^sub>1 (select premise\<^sub>1)"
    "neg_selected_literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma> = literal.from_ground literal\<^sub>G\<^sub>1" 
  if "\<P>\<^sub>G = Neg" ?select\<^sub>G_not_empty 
  proof-
    have "ground_is_maximal literal\<^sub>G\<^sub>1 (select\<^sub>G premise\<^sub>G\<^sub>1)" if "\<P>\<^sub>G = Neg" ?select\<^sub>G_not_empty
      using ground_superpositionI(9) that
      by simp

    then show ?thesis
      using
        that 
        select(1) 
        unique_maximal_in_ground_clause
        obtain_maximal_literal
      unfolding premise\<^sub>G\<^sub>1
      by (metis (mono_tags, lifting) clause.comp_subst.monoid_action_compatibility 
          clause_subst_empty(2) clause.ground_is_ground image_mset_is_empty_iff 
          clause.from_ground_def)
  qed

  moreover then have "neg_selected_literal\<^sub>1 \<in># premise\<^sub>1" if "\<P>\<^sub>G = Neg" ?select\<^sub>G_not_empty 
    using that
    by (meson maximal_in_clause mset_subset_eqD select_subset)

  ultimately obtain literal\<^sub>1 where
    literal\<^sub>1_\<gamma>: "literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma> = literal.from_ground literal\<^sub>G\<^sub>1" and
    literal\<^sub>1_in_premise\<^sub>1: "literal\<^sub>1 \<in># premise\<^sub>1" and
    literal\<^sub>1_is_strictly_maximal: "\<P>\<^sub>G = Pos \<Longrightarrow> is_strictly_maximal literal\<^sub>1 premise\<^sub>1" and
    literal\<^sub>1_is_maximal: "\<P>\<^sub>G = Neg \<Longrightarrow> ?select\<^sub>G_empty \<Longrightarrow> is_maximal literal\<^sub>1 premise\<^sub>1" and
    literal\<^sub>1_selected: "\<P>\<^sub>G = Neg \<Longrightarrow> ?select\<^sub>G_not_empty \<Longrightarrow> is_maximal literal\<^sub>1 (select premise\<^sub>1)"
    by (metis ground_superpositionI(9) literals_distinct(1))

  then have literal\<^sub>1_grounding: "literal.is_ground (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma>)"
    by simp

  have literal\<^sub>G\<^sub>2_is_strictly_maximal\<^sub>l: 
    "is_strictly_maximal (literal.from_ground literal\<^sub>G\<^sub>2) (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>)"
    using ground_superpositionI(11)
    by (simp add: premise\<^sub>2_grounding)

  obtain literal\<^sub>2 where 
    literal\<^sub>2_strictly_maximal: "is_strictly_maximal literal\<^sub>2 premise\<^sub>2" and
    literal\<^sub>2_\<gamma>: "literal\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<odot> \<gamma> = literal.from_ground literal\<^sub>G\<^sub>2"
    using obtain_strictly_maximal_literal[OF 
        premise\<^sub>2_grounding[folded clause.subst_comp_subst] 
        literal\<^sub>G\<^sub>2_is_strictly_maximal\<^sub>l
        ]
    by metis

  then have literal\<^sub>2_in_premise\<^sub>2: "literal\<^sub>2 \<in># premise\<^sub>2" 
    using strictly_maximal_in_clause by blast

  have literal\<^sub>2_grounding: "literal.is_ground (literal\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<odot> \<gamma>)"
    using literal\<^sub>2_\<gamma> by simp

  obtain premise\<^sub>1' where premise\<^sub>1: "premise\<^sub>1 = add_mset literal\<^sub>1 premise\<^sub>1'"
    by (meson literal\<^sub>1_in_premise\<^sub>1 multi_member_split)

  then have premise\<^sub>1'_\<gamma>: "premise\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma> = clause.from_ground premise\<^sub>G\<^sub>1'"
    using premise\<^sub>1_\<gamma>  
    unfolding clause.from_ground_add  literal\<^sub>1_\<gamma>[symmetric]
    by simp

  obtain premise\<^sub>2' where premise\<^sub>2: "premise\<^sub>2 = add_mset literal\<^sub>2 premise\<^sub>2'"
    by (meson literal\<^sub>2_in_premise\<^sub>2 multi_member_split)

  then have premise\<^sub>2'_\<gamma>: "premise\<^sub>2' \<cdot> \<rho>\<^sub>2 \<cdot> \<gamma> = clause.from_ground premise\<^sub>G\<^sub>2'"
    using premise\<^sub>2_\<gamma>  
    unfolding clause.from_ground_add literal\<^sub>2_\<gamma>[symmetric]
    by simp

  let ?\<P> = "if \<P>\<^sub>G = Pos then Pos else Neg"

  have [simp]: "\<P>\<^sub>G \<noteq> Pos \<longleftrightarrow> \<P>\<^sub>G = Neg"
    using ground_superpositionI(4) 
    by auto

  have "literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<gamma> = 
    ?\<P> (Upair (context.from_ground context\<^sub>G)\<langle>term.from_ground term\<^sub>G\<^sub>1\<rangle> (term.from_ground term\<^sub>G\<^sub>2))"
    using literal\<^sub>1_\<gamma>
    unfolding ground_superpositionI(5)
    by simp

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

        then have "context\<^sub>G \<noteq> Hole"
          by (metis Fun.prems(2) actxt.simps(8) context.context_from_ground_hole intp_actxt.simps(1) 
              is_FunI)

        then obtain terms\<^sub>G\<^sub>1 context\<^sub>G' terms\<^sub>G\<^sub>2 where
          context\<^sub>G: "context\<^sub>G = More f terms\<^sub>G\<^sub>1 context\<^sub>G' terms\<^sub>G\<^sub>2"
          using Fun(3)
          by(cases context\<^sub>G)(auto simp: context.from_ground_def)

        have terms_\<gamma>: 
          "map (\<lambda>term. term \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>) terms = 
            map term.from_ground terms\<^sub>G\<^sub>1 @ (context.from_ground context\<^sub>G')\<langle>term.from_ground term\<^sub>G\<^sub>1\<rangle> #
             map term.from_ground terms\<^sub>G\<^sub>2"
          using Fun(3) 
          unfolding context\<^sub>G context.from_ground_def
          (* TODO *)
          by (smt (verit, best) actxt.simps(9) eval_subst eval_term.simps(2) intp_actxt.simps(2) map_eq_conv term.inject(2))
        
        then obtain terms\<^sub>1 "term" terms\<^sub>2 where 
          terms: "terms = terms\<^sub>1 @ term # terms\<^sub>2" and
          terms\<^sub>1_\<gamma>: "map (\<lambda>term. term \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>) terms\<^sub>1 = map term.from_ground terms\<^sub>G\<^sub>1" and
          terms\<^sub>2_\<gamma>: "map (\<lambda>term. term \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>) terms\<^sub>2 = map term.from_ground terms\<^sub>G\<^sub>2"  
          unfolding context.from_ground_def
          (* TODO *)
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
             unfolding context.from_ground_def
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
              unfolding context.from_ground_def
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
            unfolding context.from_ground_def
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
      using context.ground_context_subst[OF context.ground_is_ground] ctxt_compose_subst_compose_distrib
      by metis

    obtain \<tau>\<^sub>x where \<tau>\<^sub>x: "welltyped \<V>\<^sub>1 term\<^sub>x \<tau>\<^sub>x"
      using term\<^sub>1_with_context typing(1)
      unfolding premise\<^sub>1 literal\<^sub>1
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
      by (metis eval_subst_def eval_term.simps(1) term.is_renaming_def renaming(1) 
          subst_apply_eq_Var)

    have \<tau>\<^sub>x_var\<^sub>x: "welltyped \<V>\<^sub>1 (Var var\<^sub>x) \<tau>\<^sub>x"
      using \<tau>\<^sub>x typing(5)
      unfolding var\<^sub>x premise\<^sub>1 literal\<^sub>1 term\<^sub>1_with_context
      by simp

    show ?thesis
    proof(unfold ground.redundant_infer_def \<iota>\<^sub>G_parts, intro exI conjI)

      let ?update = "(context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma>)\<langle>term.from_ground term\<^sub>G\<^sub>3\<rangle>"

      define \<gamma>' where
        \<gamma>': "\<gamma>' \<equiv> \<gamma>(var\<^sub>x := ?update)"

      have update_grounding: "term.is_ground ?update"
      proof-
        have "context.is_ground ((context\<^sub>x \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma>) \<circ>\<^sub>c (context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma>))"
          using context.ground_is_ground[of context\<^sub>G] context\<^sub>G
          by (metis subst_compose_ctxt_compose_distrib)

        then show ?thesis
          using context.context_is_ground_context_compose1(2)
          by auto
      qed
      let ?context\<^sub>x'_\<gamma> = "context.to_ground (context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma>)"

      (* TODO: *)
      have term\<^sub>x_\<gamma>: "term.to_ground (term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>) = ?context\<^sub>x'_\<gamma>\<langle>term\<^sub>G\<^sub>1\<rangle>\<^sub>G"
      proof-
        have "(context\<^sub>x \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma>)\<langle>term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>\<rangle> = 
          (context\<^sub>x \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma>) \<langle>(context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma>)\<langle>term.from_ground term\<^sub>G\<^sub>1\<rangle>\<rangle>"
          using term\<^sub>1_with_context_\<gamma> 
          unfolding term\<^sub>1_with_context context\<^sub>G
          by (metis ctxt_ctxt_compose eval_ctxt subst_compose_ctxt_compose_distrib)
        
        then show ?thesis
          using update_grounding 
          by (metis ctxt_eq context.term_to_ground_context_to_ground term.from_ground_inverse)
      qed

      have term\<^sub>x_\<gamma>': "term.to_ground (term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>') = ?context\<^sub>x'_\<gamma>\<langle>term\<^sub>G\<^sub>3\<rangle>\<^sub>G"
        using update_grounding
        unfolding var\<^sub>x[symmetric] \<gamma>'
        by auto

      have aux: "term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma> = (context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma>)\<langle>term.from_ground term\<^sub>G\<^sub>1\<rangle>"
        using term\<^sub>x_\<gamma>
        by (metis (mono_tags, lifting) context.ground_is_ground
            context.term_from_ground_context_to_ground
            context.term_with_context_is_ground subst_apply_term_ctxt_apply_distrib
            term.to_ground_inverse term\<^sub>1_with_context term\<^sub>1_with_context_\<gamma> update_grounding
            vars_term_of_gterm)

      have "clause.is_welltyped \<V>\<^sub>2 (clause.from_ground premise\<^sub>G\<^sub>2)"
        by (metis clause.comp_subst.monoid_action_compatibility clause.is_welltyped.subst_stability 
            clause.to_ground_inverse premise\<^sub>2_grounding premise\<^sub>G\<^sub>2 typing(2,4))

      then have 
        "\<exists>\<tau>. welltyped \<V>\<^sub>2 (term.from_ground term\<^sub>G\<^sub>1) \<tau> \<and> welltyped \<V>\<^sub>2 (term.from_ground term\<^sub>G\<^sub>3) \<tau>"
        unfolding ground_superpositionI 
        by simp

      then have aux': "\<exists>\<tau>. welltyped \<V>\<^sub>1 (term.from_ground term\<^sub>G\<^sub>1) \<tau> \<and> 
          welltyped \<V>\<^sub>1 (term.from_ground term\<^sub>G\<^sub>3) \<tau>"
        by (meson term.ground_is_ground welltyped.explicit_is_ground_typed)

      have "welltyped \<V>\<^sub>1 (term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>) \<tau>\<^sub>x"
      proof-

        have "
          \<lbrakk>\<forall>x\<in>context.vars context\<^sub>x \<union> term.vars term\<^sub>x \<union> term.vars term\<^sub>1' \<union> clause.vars premise\<^sub>1'.
            welltyped \<V>\<^sub>1 ((\<rho>\<^sub>1 \<odot> \<gamma>) x) (\<V>\<^sub>1 x);
            welltyped \<V>\<^sub>1 term\<^sub>x \<tau>\<^sub>x\<rbrakk>
            \<Longrightarrow> welltyped \<V>\<^sub>1 (term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>) \<tau>\<^sub>x"
          by (metis Un_iff term_subst.subst_comp_subst welltyped.explicit_subst_stability)
        
        then show ?thesis
          using typing(3) \<tau>\<^sub>x
          unfolding var\<^sub>x premise\<^sub>1 literal\<^sub>1 term\<^sub>1_with_context
          by simp
      qed

      then have \<tau>\<^sub>x_update: "welltyped \<V>\<^sub>1 ?update \<tau>\<^sub>x"
        unfolding aux
        using aux'
        by blast

      let ?premise\<^sub>1_\<gamma>' = "clause.to_ground (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>')"
      have premise\<^sub>1_\<gamma>'_grounding: "clause.is_ground (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>')"
        using clause.ground_subst_update[OF update_grounding premise\<^sub>1_grounding] 
        unfolding \<gamma>'
        by blast

      (*have \<gamma>'_ground: "term_subst.is_ground_subst (\<rho>\<^sub>1 \<odot> \<gamma>')"
        sledgehammer
        sorry*)
        (*by (metis \<gamma>' term.ground_subst_update term_subst.comp_subst.left.monoid_action_compatibility 
            term_subst.is_ground_subst_def typing(2) update_grounding)*)

      have \<gamma>'_wt: "is_welltyped_on (clause.vars premise\<^sub>1) \<V>\<^sub>1 (\<rho>\<^sub>1 \<odot> \<gamma>')"
        using welltyped.subst_update[OF \<tau>\<^sub>x_var\<^sub>x \<tau>\<^sub>x_update typing(3)]
        unfolding \<gamma>' subst_compose
        using welltyped.simps \<tau>\<^sub>x \<tau>\<^sub>x_update eval_term.simps(1) 
          eval_with_fresh_var fun_upd_same is_Var_term\<^sub>x renaming(1) subst_compose_def 
          term.collapse(1) term.distinct(1) term.set_cases(2) term_subst_is_renaming_iff 
          the_inv_f_f typing(3) var\<^sub>x
        by (smt (verit, del_insts))
      
      show "{?premise\<^sub>1_\<gamma>'} \<subseteq> premise_groundings"
        using premise\<^sub>1_\<gamma>'_grounding typing \<gamma>'_wt
        unfolding clause.subst_comp_subst[symmetric] premise\<^sub>1 premise_groundings 
          clause_groundings_def
        by (smt (verit, ccfv_threshold) Un_iff empty_iff fst_conv insert_iff mem_Collect_eq snd_conv subset_iff)

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

        interpret clause_entailment I
          by unfold_locales (rule trans sym compatible_with_gctxt)+

        have var\<^sub>x_\<gamma>_ground: "term.is_ground (\<gamma> var\<^sub>x)"
          using term\<^sub>1_with_context_\<gamma>
          unfolding term\<^sub>1_with_context var\<^sub>x
          by (metis aux eval_term.simps(1) nonground_context.term_with_context_is_ground
              term.ground_is_ground update_grounding var\<^sub>x)

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

          then have "(term.to_ground (\<gamma> var\<^sub>x), 
                      term.to_ground (context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma>)\<langle>term.from_ground term\<^sub>G\<^sub>3\<rangle>) \<in> I"
            unfolding \<gamma>'
            using var\<^sub>x
            by(auto simp: sym)
        
          moreover then have "?I \<TTurnstile> ?premise\<^sub>1_\<gamma>'"
            using premise by fastforce

          ultimately have "?I \<TTurnstile> premise\<^sub>G\<^sub>1"
            using
              clause.symmetric_congruence[of _ \<gamma>, 
                                          OF update_grounding var\<^sub>x_\<gamma>_ground _ premise\<^sub>1_grounding]
            unfolding \<gamma>' premise\<^sub>G\<^sub>1
            by blast

          then have "?I \<TTurnstile> add_mset (\<P>\<^sub>G (Upair context\<^sub>G\<langle>term\<^sub>G\<^sub>1\<rangle>\<^sub>G term\<^sub>G\<^sub>2)) premise\<^sub>G\<^sub>1'"
            using ground_superpositionI(1) ground_superpositionI(5) by auto

          then have "?I \<TTurnstile> add_mset (\<P>\<^sub>G (Upair context\<^sub>G\<langle>term\<^sub>G\<^sub>3\<rangle>\<^sub>G term\<^sub>G\<^sub>2)) premise\<^sub>G\<^sub>1'"
            using literal\<^sub>G\<^sub>2 symmetric_context_congruence ground_superpositionI(4)
            unfolding ground_superpositionI(6)
            apply(cases "\<P>\<^sub>G = Pos")
            (* TODO: Probably Upair_Extra was auto simp: sym *)
             apply(auto )
                   apply blast
                  apply(auto simp: sym)
            by (meson local.sym symD)+

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
          by (metis context.ground_is_ground context.context_is_ground_context_compose1(1))

        have term\<^sub>x_grounding: "term.is_ground (term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>)"
          using term\<^sub>1_with_context_\<gamma>
          unfolding term\<^sub>1_with_context
          by (metis aux nonground_context.term_with_context_is_ground term.ground_is_ground
              update_grounding)

        have 
          "(context\<^sub>x \<circ>\<^sub>c context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<gamma>)\<langle>term.from_ground term\<^sub>G\<^sub>3\<rangle> \<prec>\<^sub>t context\<^sub>x\<langle>term\<^sub>x\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>"
          using ground_superpositionI(8)
          unfolding 
            term.order.less\<^sub>G_def 
            context\<^sub>G[symmetric] 
            term\<^sub>1_with_context[symmetric] 
            term\<^sub>1_with_context_\<gamma>
          by (simp add: term.order.ground_context_compatibility)

        then have update_smaller: "?update \<prec>\<^sub>t \<gamma> var\<^sub>x"
          unfolding 
            var\<^sub>x_\<gamma>
            subst_apply_term_ctxt_apply_distrib 
            subst_compose_ctxt_compose_distrib
            Subterm_and_Context.ctxt_ctxt_compose
          using term.order.context_compatibility[OF 
              update_grounding term\<^sub>x_grounding context\<^sub>x_grounding]
          by simp   

        have var\<^sub>x_in_literal\<^sub>1: "var\<^sub>x \<in> literal.vars (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1)"
          unfolding literal\<^sub>1 term\<^sub>1_with_context literal.vars_def atom.vars_def 
          using var\<^sub>x
          by auto

        have literal\<^sub>1_smaller: "literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<gamma>' \<prec>\<^sub>l literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<gamma>"
          unfolding \<gamma>'
          using literal.order.subst_update_stability[OF 
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
          using clause.order.subst_update_stability[of _ \<gamma>, OF update_grounding update_smaller premise\<^sub>1'_grounding]
          by(cases "var\<^sub>x \<in> clause.vars (premise\<^sub>1' \<cdot> \<rho>\<^sub>1)") simp_all

        have "?premise\<^sub>1_\<gamma>' \<prec>\<^sub>c\<^sub>G premise\<^sub>G\<^sub>1"
          using less\<^sub>c_add_mset[OF literal\<^sub>1_smaller premise\<^sub>1'_smaller]
          unfolding 
            clause.order.less\<^sub>G_def 
            premise\<^sub>G\<^sub>1
            clause.add_subst[symmetric]
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
        then \<V>\<^sub>1 (inv \<rho>\<^sub>1 (Var x))
        else \<V>\<^sub>2 (inv \<rho>\<^sub>2 (Var x))"

  have wt_\<gamma>: 
    "is_welltyped_on (clause.vars (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) \<union> clause.vars (premise\<^sub>2 \<cdot> \<rho>\<^sub>2)) \<V>\<^sub>3 \<gamma>"
  proof(intro ballI)
    fix x
    assume x_in_vars: "x \<in> clause.vars (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) \<union> clause.vars (premise\<^sub>2 \<cdot> \<rho>\<^sub>2)"

    then have "term.is_ground (\<gamma> x)"
      using premise\<^sub>1_grounding premise\<^sub>2_grounding
      by (auto simp: clause.variable_grounding)

    then obtain f ts where \<gamma>_x: "\<gamma> x = Fun f ts"
      using term.obtain_ground_fun 
      by blast

    have "welltyped \<V>\<^sub>3 (\<gamma> x) (\<V>\<^sub>3 x)"
    proof(cases "x \<in> clause.vars (premise\<^sub>1 \<cdot> \<rho>\<^sub>1)")
      case True
      then have "Var x \<in> \<rho>\<^sub>1 ` clause.vars premise\<^sub>1"
        by (metis image_eqI renaming(1) clause.renaming_variables)

      then have y_in_vars: "inv \<rho>\<^sub>1 (Var x) \<in> clause.vars premise\<^sub>1"
        by (metis (no_types, lifting) image_iff renaming(1) term_subst_is_renaming_iff inv_f_f)

      define y where "y \<equiv> inv \<rho>\<^sub>1 (Var x)"

      have "term.is_ground (Var y \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>)"
        by (metis (no_types, lifting) clause.subst_comp_subst clause.variable_grounding
            eval_subst eval_term.simps(1) premise\<^sub>1_grounding y_def y_in_vars)

      moreover have "welltyped \<V>\<^sub>1 (Var y \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>) (\<V>\<^sub>1 y)"
        using typing(3) y_in_vars
        unfolding y_def
        by (simp add: subst_compose)

      ultimately have "welltyped \<V>\<^sub>3 (Var y \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>) (\<V>\<^sub>1 y)"
        by (meson welltyped.explicit_is_ground_typed)

      moreover have "\<rho>\<^sub>1 (inv \<rho>\<^sub>1 (Var x)) = Var x"
        by (metis \<open>Var x \<in> \<rho>\<^sub>1 ` clause.vars premise\<^sub>1\<close> image_iff renaming(1) term_subst_is_renaming_iff inv_f_f)

      ultimately show ?thesis
        using True
        unfolding \<V>\<^sub>3_def y_def
        by simp
    next
      case False
      then have "Var x \<in> \<rho>\<^sub>2 ` clause.vars premise\<^sub>2"
        using x_in_vars
        by (metis Un_iff image_eqI renaming(2) clause.renaming_variables)

      then have y_in_vars: "inv \<rho>\<^sub>2 (Var x) \<in> clause.vars premise\<^sub>2"
        by (metis (no_types, lifting) image_iff renaming(2) term_subst_is_renaming_iff inv_f_f)

      define y where "y \<equiv> inv \<rho>\<^sub>2 (Var x)"

      have "term.is_ground (Var y \<cdot>t \<rho>\<^sub>2 \<cdot>t \<gamma>)"
        by (metis (no_types, lifting) clause.comp_subst.left.monoid_action_compatibility
            clause.variable_grounding eval_subst eval_term.simps(1) premise\<^sub>2_grounding y_def
            y_in_vars)

      moreover have "welltyped \<V>\<^sub>2 (Var y \<cdot>t \<rho>\<^sub>2 \<cdot>t \<gamma>) (\<V>\<^sub>2 y)"
        using typing(4) y_in_vars
        unfolding y_def
        by (simp add: subst_compose)

      ultimately have "welltyped \<V>\<^sub>3 (Var y \<cdot>t \<rho>\<^sub>2 \<cdot>t \<gamma>) (\<V>\<^sub>2 y)"
        by (meson welltyped.explicit_is_ground_typed)     

      moreover have "\<rho>\<^sub>2 (inv \<rho>\<^sub>2 (Var x)) = Var x"
        by (metis \<open>Var x \<in> \<rho>\<^sub>2 ` clause.vars premise\<^sub>2\<close> image_iff renaming(2) 
            term_subst_is_renaming_iff inv_f_f)

      ultimately show ?thesis
        using False
        unfolding \<V>\<^sub>3_def y_def
        by simp
    qed

    then show "welltyped \<V>\<^sub>3 (\<gamma> x) (\<V>\<^sub>3 x)"
      unfolding \<gamma>_x.
  qed

  have "term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma> = term\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<gamma>"
    unfolding term\<^sub>1_\<gamma> term\<^sub>2_\<gamma> ..

  moreover have  "\<exists>\<tau>. welltyped \<V>\<^sub>3 (term\<^sub>1 \<cdot>t \<rho>\<^sub>1) \<tau> \<and> welltyped \<V>\<^sub>3 (term\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<tau>"
  proof-
    have "clause.is_welltyped  \<V>\<^sub>2 (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<gamma>)"
      using typing
      by (metis clause.comp_subst.monoid_action_compatibility clause.is_welltyped.subst_stability)

    then obtain \<tau> where 
      "welltyped \<V>\<^sub>2 (term.from_ground term\<^sub>G\<^sub>1) \<tau>" 
      unfolding premise\<^sub>2_\<gamma> ground_superpositionI
      by auto

    then have 
      "welltyped \<V>\<^sub>3 (term.from_ground term\<^sub>G\<^sub>1) \<tau>" 
      using welltyped.is_ground_typed
      by (meson term.ground_is_ground welltyped.explicit_is_ground_typed)

    then have "welltyped \<V>\<^sub>3 (term.from_ground term\<^sub>G\<^sub>1) \<tau>"
      by auto

    then have "welltyped \<V>\<^sub>3 (term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma>) \<tau>" "welltyped \<V>\<^sub>3 (term\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<gamma>) \<tau>"
      using term\<^sub>1_\<gamma> term\<^sub>2_\<gamma>
      by presburger+

    moreover have 
      "term.vars (term\<^sub>1 \<cdot>t \<rho>\<^sub>1) \<subseteq> clause.vars (premise\<^sub>1 \<cdot> \<rho>\<^sub>1)"
      "term.vars (term\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<subseteq> clause.vars (premise\<^sub>2 \<cdot> \<rho>\<^sub>2)"
      unfolding premise\<^sub>1 literal\<^sub>1 clause.add_subst term\<^sub>1_with_context premise\<^sub>2 literal\<^sub>2
      by auto

    ultimately have "welltyped \<V>\<^sub>3 (term\<^sub>1 \<cdot>t \<rho>\<^sub>1) \<tau>" "welltyped \<V>\<^sub>3 (term\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<tau>"
      using wt_\<gamma>
      by (simp_all add: subsetD)+ 

    then show ?thesis
      by blast
  qed

  ultimately obtain \<mu> \<sigma> where \<mu>: 
    "term_subst.is_imgu \<mu> {{term\<^sub>1 \<cdot>t \<rho>\<^sub>1, term\<^sub>2 \<cdot>t \<rho>\<^sub>2}}" 
    "\<gamma> = \<mu> \<odot> \<sigma>" 
    "welltyped_imgu \<V>\<^sub>3 (term\<^sub>1 \<cdot>t \<rho>\<^sub>1) (term\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<mu>"
    using welltyped_imgu_exists
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
        unfolding premise\<^sub>G\<^sub>1 premise\<^sub>G\<^sub>2 clause.order.less\<^sub>G_def premises_clause_to_ground_inverse 
        unfolding \<mu>(2) clause.subst_comp_subst 
        by blast

      then show "\<not> premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<preceq>\<^sub>c premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>"
        using clause.order.ground_less_not_less_eq[OF premise_groundings]
        by blast
    next
      show "?\<P> = Pos 
              \<and> select premise\<^sub>1 = {#} 
              \<and> is_strictly_maximal (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>) 
          \<or> ?\<P> = Neg 
              \<and> (select premise\<^sub>1 = {#} \<and> is_maximal (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>) 
                 \<or> is_maximal (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) ((select premise\<^sub>1) \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>))"
      proof(cases "?\<P> = Pos")
        case True
        moreover then have select_empty: "select premise\<^sub>1 = {#}"
          using clause_subst_empty select(1) ground_superpositionI(9) 
          by auto

        moreover have "is_strictly_maximal (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu> \<cdot>l \<sigma>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<cdot> \<sigma>)"
          using True pos_literal\<^sub>G\<^sub>1_is_strictly_maximal\<^sub>l
          unfolding literal\<^sub>1_\<gamma>[symmetric] \<mu>(2)
          by force

        moreover then have "is_strictly_maximal (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>)"
          using 
            is_strictly_maximal_if_grounding_is_strictly_maximal[OF
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
            by simp

          moreover have "is_maximal (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu> \<cdot>l \<sigma>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<cdot> \<sigma>)"
            using neg_literal\<^sub>G\<^sub>1_is_maximal\<^sub>l[OF select\<^sub>G_empty]
            unfolding literal\<^sub>1_\<gamma>[symmetric] \<mu>(2)
            by simp

          moreover then have "is_maximal (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>)"
            using 
              is_maximal_if_grounding_is_maximal[OF 
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
            using select_ground_subst[OF premise\<^sub>1_grounding] select(1)
            unfolding \<mu>(2) clause.subst_comp_subst
            by (metis clause.ground_is_ground)

          note selected_subst =
            literal\<^sub>1_selected[
              OF \<P>\<^sub>G_Neg select\<^sub>G_not_empty, 
              THEN maximal_in_clause, 
              THEN clause.subst_in_to_set_subst] 

          have "is_maximal (literal\<^sub>1  \<cdot>l \<rho>\<^sub>1 \<cdot>l \<gamma>) (select premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>)"  
            using select\<^sub>G_not_empty ground_superpositionI(9) \<P>\<^sub>G_Neg 
            unfolding literal\<^sub>1_\<gamma>[symmetric] select(1)
            by simp

          then have "is_maximal (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) ((select premise\<^sub>1) \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>)"
            using is_maximal_if_grounding_is_maximal[OF _ selected_grounding] selected_subst
            by (metis \<mu>(2) clause.subst_comp_subst literal.subst_comp_subst)

          with select\<^sub>G_not_empty \<P>\<^sub>G_Neg show ?thesis
            by simp
        qed
      qed
    next
      show "select premise\<^sub>2 = {#}"
        using ground_superpositionI(10) select(2)
        by simp
    next 
      have "is_strictly_maximal (literal\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu> \<cdot>l \<sigma>) (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu> \<cdot> \<sigma>)"
        using literal\<^sub>G\<^sub>2_is_strictly_maximal\<^sub>l
        unfolding literal\<^sub>2_\<gamma>[symmetric] \<mu>(2)
        by simp

      then show "is_strictly_maximal (literal\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu>) (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>)"
        using 
          is_strictly_maximal_if_grounding_is_strictly_maximal[OF 
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
          term.order.less\<^sub>G_def
          context.safe_unfolds.

      then show "\<not> context\<^sub>1\<langle>term\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t term\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu>"
        using term.order.ground_less_not_less_eq[OF term_groundings]
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
          term.order.less\<^sub>G_def.

      then show "\<not> term\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<preceq>\<^sub>t term\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu>"
        using term.order.ground_less_not_less_eq[OF term_groundings]
        by blast
    next
      show 
        "conclusion' = add_mset (?\<P> (Upair (context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>term\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> (term\<^sub>1' \<cdot>t \<rho>\<^sub>1))) 
          (premise\<^sub>1' \<cdot> \<rho>\<^sub>1 + premise\<^sub>2' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu>"
        unfolding term\<^sub>2'_with_context conclusion'..
      show "welltyped_imgu \<V>\<^sub>3 (term\<^sub>1 \<cdot>t \<rho>\<^sub>1) (term\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<mu>"
        using \<mu>(3) by blast

      show "clause.vars (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter> clause.vars (premise\<^sub>2 \<cdot> \<rho>\<^sub>2) = {}"
        using renaming(3). 

      show "\<forall>x\<in>clause.vars (premise\<^sub>1 \<cdot> \<rho>\<^sub>1). \<V>\<^sub>1 (inv \<rho>\<^sub>1 (Var x)) = \<V>\<^sub>3 x"
        unfolding \<V>\<^sub>3_def
        by meson

      show "\<forall>x\<in>clause.vars (premise\<^sub>2 \<cdot> \<rho>\<^sub>2). \<V>\<^sub>2 (inv \<rho>\<^sub>2 (Var x)) = \<V>\<^sub>3 x"
        unfolding \<V>\<^sub>3_def
        using renaming(3)
        by (meson disjoint_iff)

      show "is_welltyped_on (clause.vars premise\<^sub>1) \<V>\<^sub>1 \<rho>\<^sub>1"
        using typing(5).

      show "is_welltyped_on (clause.vars premise\<^sub>2) \<V>\<^sub>2 \<rho>\<^sub>2"
        using typing(6).

      have "\<exists>\<tau>. welltyped \<V>\<^sub>2 term\<^sub>2 \<tau> \<and> welltyped \<V>\<^sub>2 term\<^sub>2' \<tau>"
        using typing(2)
        unfolding premise\<^sub>2 literal\<^sub>2
        by auto

      then show "\<And>\<tau> \<tau>'. \<lbrakk>typed \<V>\<^sub>2 term\<^sub>2 \<tau>; typed \<V>\<^sub>2 term\<^sub>2' \<tau>'\<rbrakk> \<Longrightarrow> \<tau> = \<tau>'"
        using term.typed_if_welltyped by blast

      show "infinite_variables_per_type \<V>\<^sub>1" "infinite_variables_per_type \<V>\<^sub>2"
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
        using ground_superpositionI(4, 12) clause.to_ground_inverse[OF conclusion_grounding] 
        by auto
      
      then show ?thesis
        unfolding 
          conclusion'
          term\<^sub>2'_with_context_\<gamma>[symmetric]
          premise\<^sub>1'_\<gamma>[symmetric] 
          premise\<^sub>2'_\<gamma>[symmetric] 
          term\<^sub>1'_\<gamma>[symmetric]
          clause.plus_subst[symmetric] 
          subst_apply_term_ctxt_apply_distrib[symmetric]
          subst_atom[symmetric]
        unfolding
          clause.subst_comp_subst[symmetric]
          \<mu>_\<gamma>
        by simp
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
        unfolding conclusion' clause.add_subst clause.plus_subst subst_literal
        by auto
  
      then show "x \<in> clause.vars (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) \<union> clause.vars (premise\<^sub>2 \<cdot> \<rho>\<^sub>2)"
      proof(cases)
        case t: term\<^sub>2'_with_context
        then show ?thesis 
          using  context.variables_in_base_imgu[OF \<mu>(1)] term.variables_in_base_imgu[OF \<mu>(1)] 
          unfolding premise\<^sub>1 literal\<^sub>1 term\<^sub>1_with_context premise\<^sub>2 literal\<^sub>2  term\<^sub>2'_with_context
          (* TODO: *)
          apply auto
          by (smt (verit, ccfv_threshold) UnE in_mono t term\<^sub>2'_with_context
              vars_term_ctxt_apply)
      next
        case term\<^sub>1'
        then show ?thesis
          using term.variables_in_base_imgu[OF \<mu>(1)]
          unfolding premise\<^sub>1 clause.add_subst literal\<^sub>1 term\<^sub>1_with_context premise\<^sub>2 literal\<^sub>2
          by auto
      next
        case premise\<^sub>1'
        then show ?thesis 
          using clause.variables_in_base_imgu[OF \<mu>(1)]
          unfolding premise\<^sub>1 clause.add_subst literal\<^sub>1 term\<^sub>1_with_context premise\<^sub>2 literal\<^sub>2
          by auto
       next
        case premise\<^sub>2'
        then show ?thesis 
          using clause.variables_in_base_imgu[OF \<mu>(1)]
          unfolding premise\<^sub>1 clause.add_subst literal\<^sub>1 term\<^sub>1_with_context premise\<^sub>2 literal\<^sub>2
          by auto
      qed
    qed

    have surjx: "surj (\<lambda>x. inv \<rho>\<^sub>2 (Var x))"
      using term.surj_inv_renaming[OF renaming(2)].
                  
    have yy: 
      "\<And>P Q b ty. {x. (if b x then P x else Q x) = ty } = 
        {x. b x \<and> P x = ty} \<union> {x. \<not>b x \<and> Q x = ty}"
      by auto

    have qq: "\<And>ty. infinite {x. \<V>\<^sub>2 (inv \<rho>\<^sub>2 (Var x)) = ty}"
      using surj_infinite_set[OF surjx typing(8)[unfolded infinite_variables_per_type_def, rule_format]].

    have zz: 
      "\<And>ty. {x. x \<notin> clause.vars (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) \<and> \<V>\<^sub>2 (inv \<rho>\<^sub>2 (Var x)) = ty} = 
            {x. \<V>\<^sub>2 (inv \<rho>\<^sub>2 (Var x)) = ty} - {x. x \<in> clause.vars (premise\<^sub>1 \<cdot> \<rho>\<^sub>1)}"
      by auto

    have "\<And>ty. infinite {x. x \<notin> clause.vars (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) \<and> \<V>\<^sub>2 (inv \<rho>\<^sub>2 (Var x)) = ty}"
      unfolding zz
      using qq clause.finite_vars[of "premise\<^sub>1 \<cdot> \<rho>\<^sub>1"]
      by simp

    then have infinite_variables_per_type_\<V>\<^sub>3: "infinite_variables_per_type \<V>\<^sub>3"   
      unfolding \<V>\<^sub>3_def infinite_variables_per_type_def yy     
      by auto

    show "\<iota>\<^sub>G \<in> inference_groundings (Infer [(premise\<^sub>2, \<V>\<^sub>2), (premise\<^sub>1, \<V>\<^sub>1)] (conclusion', \<V>\<^sub>3))"
    proof-
      have " \<lbrakk>conclusion' \<cdot> \<gamma> = conclusion \<cdot> \<gamma>;
         ground.superposition (clause.to_ground (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<gamma>))
          (clause.to_ground (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>)) (clause.to_ground (conclusion \<cdot> \<gamma>));
         is_welltyped_on (clause.vars conclusion') \<V>\<^sub>3 \<gamma>; infinite_variables_per_type \<V>\<^sub>3\<rbrakk>
        \<Longrightarrow> clause.is_welltyped \<V>\<^sub>3 conclusion'"
        using \<open>superposition (premise\<^sub>2, \<V>\<^sub>2) (premise\<^sub>1, \<V>\<^sub>1) (conclusion', \<V>\<^sub>3)\<close> 
          superposition_preserves_typing typing(1) typing(2) by blast

      then have 
        "is_inference_grounding (Infer [(premise\<^sub>2, \<V>\<^sub>2), (premise\<^sub>1, \<V>\<^sub>1)] (conclusion', \<V>\<^sub>3)) \<iota>\<^sub>G \<gamma> \<rho>\<^sub>1 \<rho>\<^sub>2"
        using 
          conclusion'_\<gamma> ground_superposition 
          is_welltyped_on_subset[OF  wt_\<gamma> vars_conclusion'] 
          infinite_variables_per_type_\<V>\<^sub>3
          typing(1, 2)
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
    "\<iota>\<^sub>G \<in> ground.Inf_from_q select\<^sub>G (\<Union>(clause_groundings ` N))"
    "subst_stability_on N"
  obtains \<iota> where 
    "\<iota> \<in> Inf_from N" 
    "\<iota>\<^sub>G \<in> inference_groundings \<iota>"
proof-
  obtain D\<^sub>G C\<^sub>G where 
    \<iota>\<^sub>G : "\<iota>\<^sub>G = Infer [D\<^sub>G] C\<^sub>G" and
    ground_eq_resolution: "ground.eq_resolution D\<^sub>G C\<^sub>G"
    using assms(1)
    by blast

  have D\<^sub>G_in_groundings: "D\<^sub>G \<in> \<Union>(clause_groundings ` N)"
    using assms(2)
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
    by simp

  obtain D C \<gamma> \<V> where
    "clause.from_ground D\<^sub>G = D \<cdot> \<gamma>" and
    "clause.from_ground C\<^sub>G = C \<cdot> \<gamma>" and
    select: "clause.from_ground (select\<^sub>G D\<^sub>G) = select D \<cdot> \<gamma>" and
    D_in_N: "(D, \<V>) \<in> N" and
    D_is_welltyped: "clause.is_welltyped \<V> D" and
    \<gamma>_is_welltyped: "is_welltyped_on (clause.vars D) \<V> \<gamma>" and
    \<V>: "infinite_variables_per_type \<V>"
    using assms(2, 3) D\<^sub>G_in_groundings that
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def 
    apply (elim ballE)
    apply auto
    by (metis clause.all_subst_ident_if_ground clause.from_ground_inverse
        clause.ground_is_ground clause.obtain_grounding
        select_ground_subst)  

  then have
    D_grounding: "clause.is_ground (D \<cdot> \<gamma>)" and
    D\<^sub>G: "D\<^sub>G = clause.to_ground (D \<cdot> \<gamma>)" and
    C_grounding: "clause.is_ground (C \<cdot> \<gamma>)" and
    C\<^sub>G: "C\<^sub>G = clause.to_ground (C \<cdot> \<gamma>)"
    using clause.ground_is_ground clause.from_ground_inverse
    by(smt(verit))+

  obtain C' where
    eq_resolution: "eq_resolution (D, \<V>) (C', \<V>)" and
    \<iota>\<^sub>G: "\<iota>\<^sub>G = Infer [clause.to_ground (D \<cdot> \<gamma>)] (clause.to_ground (C' \<cdot> \<gamma>))" and
    inference_groundings: "\<iota>\<^sub>G \<in> inference_groundings (Infer [(D, \<V>)] (C', \<V>))" and  
    C'_C: "C' \<cdot> \<gamma> = C \<cdot> \<gamma>"
    using
      eq_resolution_lifting[OF 
        ground_eq_resolution[unfolded D\<^sub>G C\<^sub>G]
        D_grounding 
        C_grounding 
        select[unfolded D\<^sub>G] 
        D_is_welltyped
        \<gamma>_is_welltyped
        \<V>
        ]
    unfolding D\<^sub>G C\<^sub>G \<iota>\<^sub>G
    by metis

  let ?\<iota> = "Infer [(D, \<V>)] (C', \<V>)"

  show ?thesis
  proof(rule that)
    show "?\<iota> \<in> Inf_from N"
      using D_in_N eq_resolution
      unfolding Inf_from_def inferences_def inference_system.Inf_from_def
      by auto

    show "\<iota>\<^sub>G \<in> inference_groundings ?\<iota>"
      using inference_groundings.
  qed
qed 

lemma eq_factoring_ground_instance: 
  assumes 
    "\<iota>\<^sub>G \<in> ground.eq_factoring_inferences"
    "\<iota>\<^sub>G \<in> ground.Inf_from_q select\<^sub>G (\<Union>(clause_groundings ` N))"
    "subst_stability_on N"
  obtains \<iota> where 
    "\<iota> \<in> Inf_from N" 
    "\<iota>\<^sub>G \<in> inference_groundings \<iota>"
proof-
  obtain D\<^sub>G C\<^sub>G where 
    \<iota>\<^sub>G : "\<iota>\<^sub>G = Infer [D\<^sub>G] C\<^sub>G" and
    eq_factoring: "ground.eq_factoring D\<^sub>G C\<^sub>G"
    using assms(1)
    by blast

  have D\<^sub>G_in_groundings: "D\<^sub>G \<in> \<Union>(clause_groundings ` N)"
    using assms(2)
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
    by simp

  obtain D "C" \<gamma> \<V> where
    "clause.from_ground D\<^sub>G = D \<cdot> \<gamma>" and
    "clause.from_ground C\<^sub>G = C \<cdot> \<gamma>" and
    select: "clause.from_ground (select\<^sub>G (clause.to_ground (D \<cdot> \<gamma>))) = select D \<cdot> \<gamma>" and
    D_in_N: "(D, \<V>) \<in> N" and
    typing:
    "clause.is_welltyped \<V> D"
    (*"clause.is_ground (D \<cdot> \<gamma>)"  
    "clause.is_ground (C \<cdot> \<gamma>)"*)
    "is_welltyped_on (clause.vars D) \<V> \<gamma>"
    "infinite_variables_per_type \<V>"
    using assms(2, 3) D\<^sub>G_in_groundings
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
    (* TODO: *)
    apply(elim ballE)
     apply auto
    by (metis clause.from_ground_inverse clause.ground_is_ground
        clause.obtain_grounding clause.subst_ident_if_ground
        select_ground_subst)

  then have 
    D_grounding: "clause.is_ground (D \<cdot> \<gamma>)" and 
    D\<^sub>G: "D\<^sub>G = clause.to_ground (D \<cdot> \<gamma>)" and 
    C_grounding: "clause.is_ground (C \<cdot> \<gamma>)" and
    C\<^sub>G: "C\<^sub>G = clause.to_ground (C \<cdot> \<gamma>)"
    by (smt(verit) clause.ground_is_ground clause.from_ground_inverse)+

  obtain C' where 
    eq_factoring: "eq_factoring (D, \<V>) (C', \<V>)" and
    inference_groundings: "\<iota>\<^sub>G \<in> inference_groundings (Infer [(D, \<V>)] (C', \<V>))" and  
    C'_C: "C' \<cdot> \<gamma> = C \<cdot> \<gamma>"
    using 
      eq_factoring_lifting[OF 
        eq_factoring[unfolded D\<^sub>G C\<^sub>G]
        D_grounding 
        C_grounding 
        select
        ]
      typing
    unfolding D\<^sub>G C\<^sub>G \<iota>\<^sub>G
    by metis

  let ?\<iota> = "Infer [(D, \<V>)] (C', \<V>)"

  show ?thesis
  proof(rule that)
    show "?\<iota> \<in> Inf_from N"
      using D_in_N eq_factoring
      unfolding Inf_from_def inferences_def inference_system.Inf_from_def
      by auto

    show "\<iota>\<^sub>G \<in> inference_groundings ?\<iota>"
      using inference_groundings.
  qed
qed

(* TODO: Move *)
lemma is_ground_subst_if:
  assumes "term_subst.is_ground_subst \<gamma>\<^sub>1" "term_subst.is_ground_subst \<gamma>\<^sub>2"
  shows "term_subst.is_ground_subst (\<lambda>var. if b var then \<gamma>\<^sub>1 var else \<gamma>\<^sub>2 var)"
  using assms
  unfolding term_subst.is_ground_subst_def
  by (simp add: is_ground_iff)

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
    superposition: "ground.superposition premise\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>1 conclusion\<^sub>G"
    using assms(1)
    by blast

  have 
    premise\<^sub>G\<^sub>1_in_groundings: "premise\<^sub>G\<^sub>1 \<in> \<Union> (clause_groundings ` premises)" and  
    premise\<^sub>G\<^sub>2_in_groundings: "premise\<^sub>G\<^sub>2 \<in> \<Union> (clause_groundings ` premises)"
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
    "is_welltyped_on (clause.vars premise\<^sub>1) \<V>\<^sub>1 \<gamma>\<^sub>1"
    "is_welltyped_on (clause.vars premise\<^sub>2) \<V>\<^sub>2 \<gamma>\<^sub>2"
    (*"term_subst.is_ground_subst \<gamma>\<^sub>1"
    "term_subst.is_ground_subst \<gamma>\<^sub>2" *)
    "clause.is_welltyped \<V>\<^sub>1 premise\<^sub>1"
    "clause.is_welltyped \<V>\<^sub>2 premise\<^sub>2"
    "infinite_variables_per_type \<V>\<^sub>1" 
    "infinite_variables_per_type \<V>\<^sub>2" 
    using assms(2, 4) premise\<^sub>G\<^sub>1_in_groundings premise\<^sub>G\<^sub>2_in_groundings
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
    by (smt (verit) clause.from_ground_inverse clause.ground_is_ground clause.obtain_grounding select_ground_subst
        split_beta split_pairs)

  obtain \<rho>\<^sub>1 \<rho>\<^sub>2 :: "('f, 'v) subst" where
    renaming: 
    "term_subst.is_renaming \<rho>\<^sub>1" 
    "term_subst.is_renaming \<rho>\<^sub>2"
    "\<rho>\<^sub>1 ` (clause.vars premise\<^sub>1) \<inter> \<rho>\<^sub>2 ` (clause.vars premise\<^sub>2) = {}" and
    wt_\<rho>: 
    "is_welltyped_on (clause.vars premise\<^sub>1) \<V>\<^sub>1 \<rho>\<^sub>1"
    "is_welltyped_on (clause.vars premise\<^sub>2) \<V>\<^sub>2 \<rho>\<^sub>2"
    using welltyped.obtain_typed_renamings[OF infinite_UNIV _ _ wt(5,6)[unfolded infinite_variables_per_type_def, rule_format]] 
    by (metis clause.finite_vars(1))

  have renaming_distinct: "clause.vars (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter> clause.vars (premise\<^sub>2 \<cdot> \<rho>\<^sub>2) = {}"
    using renaming(3)
    unfolding renaming(1,2)[THEN clause.renaming_variables, symmetric]
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
      using x_in_vars renaming(1) clause.renaming_variables by fastforce
    

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
      using x_in_vars renaming(2) clause.renaming_variables by fastforce

    then have "\<gamma> y = \<rho>\<^sub>2_inv y \<cdot>t \<gamma>\<^sub>2"
      using \<gamma> renaming_distinct subst_compose by fastforce

    then show "(\<rho>\<^sub>2 \<odot> \<gamma>) x = \<gamma>\<^sub>2 x"
      by (metis y \<rho>\<^sub>2_inv eval_term.simps(1) subst_compose)
  qed

  have \<gamma>\<^sub>1_is_ground: "\<forall>x\<in>clause.vars premise\<^sub>1. term.is_ground (\<gamma>\<^sub>1 x)"
    by (metis clause.ground_is_ground clause.variable_grounding
        premise\<^sub>1_\<gamma>\<^sub>1)
    
  have \<gamma>\<^sub>2_is_ground: "\<forall>x\<in>clause.vars premise\<^sub>2. term.is_ground (\<gamma>\<^sub>2 x)"
    by (metis clause.ground_is_ground clause.variable_grounding
        premise\<^sub>2_\<gamma>\<^sub>2)

  have wt_\<gamma>:
    "is_welltyped_on (clause.vars premise\<^sub>1) \<V>\<^sub>1 (\<rho>\<^sub>1 \<odot> \<gamma>)"
    "is_welltyped_on (clause.vars premise\<^sub>2) \<V>\<^sub>2 (\<rho>\<^sub>2 \<odot> \<gamma>)"
    using wt(1,2) is_welltyped_on_subset \<gamma>\<^sub>1 \<gamma>\<^sub>2
    by auto    

  (*have "term_subst.is_ground_subst (\<rho>\<^sub>1_inv \<odot> \<gamma>\<^sub>1)" "term_subst.is_ground_subst (\<rho>\<^sub>2_inv \<odot> \<gamma>\<^sub>2)"
    using term_subst.is_ground_subst_comp_right wt by blast+

  then have is_ground_subst_\<gamma>: "term_subst.is_ground_subst \<gamma>"
    unfolding \<gamma>
    using is_ground_subst_if
    by fast*)

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
      using \<gamma>\<^sub>2 premise\<^sub>2_\<gamma>\<^sub>2 clause.subst_eq
      by fastforce
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

  have "clause_groundings (premise\<^sub>1, \<V>\<^sub>1) \<union> clause_groundings (premise\<^sub>2, \<V>\<^sub>2)
     \<subseteq> \<Union> (clause_groundings ` premises)"
    using premise\<^sub>1_in_premises premise\<^sub>2_in_premises by blast

  then have \<iota>\<^sub>G_not_redunant:
    "\<iota>\<^sub>G \<notin> ground.GRed_I (clause_groundings (premise\<^sub>1, \<V>\<^sub>1) \<union> clause_groundings (premise\<^sub>2, \<V>\<^sub>2))"
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
        superposition[unfolded  premise\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>1 conclusion\<^sub>G]
        \<iota>\<^sub>G_not_redunant[unfolded \<iota>\<^sub>G premise\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>1 conclusion\<^sub>G]
        wt(3, 4)
        wt_\<gamma>
        wt_\<rho>
        wt(5, 6)
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

context superposition_calculus
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

  then interpret grounded_superposition_calculus
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
  then interpret grounded_superposition_calculus
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
