theory Superposition_Completeness
  imports
    Ground_Superposition_Completeness
    Grounded_Superposition
    Nonground_Entailment
    Superposition_Welltypedness_Preservation
begin

section \<open>Completeness\<close>

context grounded_superposition_calculus
begin

subsection \<open>Liftings\<close>

lemma eq_resolution_lifting:
  fixes
    D\<^sub>G C\<^sub>G :: "'f ground_atom clause" and
    D C :: "('f, 'v) atom clause" and
    \<gamma> :: "('f, 'v) subst"
  defines
    [simp]: "D\<^sub>G \<equiv> clause.to_ground (D \<cdot> \<gamma>)" and
    [simp]: "C\<^sub>G \<equiv> clause.to_ground (C \<cdot> \<gamma>)"
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
        by auto

      then show ?thesis
        using that D_grounding obtain_maximal_literal
        by blast
    qed

    moreover then have "max_l \<in># D"
      unfolding is_maximal_def 
      by blast

    moreover have "max_l \<cdot>l \<gamma> = term.from_ground t\<^sub>G !\<approx> term.from_ground t\<^sub>G" if ?select\<^sub>G_empty
    proof(rule unique_maximal_in_ground_clause[OF D_grounding is_max_in_D_\<gamma>])
      have "ground_is_maximal l\<^sub>G D\<^sub>G"
        using ground_eq_resolutionI(3) that
        unfolding is_maximal_def
        by simp

      then show "is_maximal (term.from_ground t\<^sub>G !\<approx> term.from_ground t\<^sub>G) (D \<cdot> \<gamma>)"
        using D_grounding
        unfolding ground_eq_resolutionI(2)
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
        unfolding ground_eq_resolutionI(2)
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
      using obtain_welltyped_imgu[OF unified welltyped] that
      by metis
  qed

  show ?thesis
  proof(rule that)

    show eq_resolution: "eq_resolution (D, \<V>) (C' \<cdot> \<mu>, \<V>)"
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
    qed (rule refl)

    show C'_\<mu>_\<gamma>: "C' \<cdot> \<mu> \<cdot> \<gamma> = C \<cdot> \<gamma>"
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
          unfolding ground_eq_resolutionI(2) l_\<gamma> ground_eq_resolutionI(4)[symmetric]
          by simp 

        moreover have "clause.is_ground (add_mset (l \<cdot>l \<gamma>) (C \<cdot> \<gamma>))"
          using C_grounding clause.to_set_is_ground_subst[OF l_in_D D_grounding]
          by simp

        ultimately show ?thesis
          using clause.to_ground_eq[OF D_grounding]
          by blast
      qed

      then have "C' \<cdot> \<gamma> = C \<cdot> \<gamma>"
        unfolding D
        by simp

      then show ?thesis
        unfolding clause.subst_comp_subst[symmetric] \<mu>_\<gamma>.
    qed

    show "Infer [D\<^sub>G] C\<^sub>G \<in> inference_groundings (Infer [(D, \<V>)] (C' \<cdot> \<mu>, \<V>))"
    proof (rule is_inference_grounding_one_premise_inference_groundings)

      show "is_inference_grounding_one_premise (D, \<V>) (C' \<cdot> \<mu>, \<V>) (Infer [D\<^sub>G] C\<^sub>G) \<gamma>"
      proof(unfold split, intro conjI; (rule D_grounding D_is_welltyped refl \<V>)?)
        show "clause.is_ground (C' \<cdot> \<mu> \<cdot> \<gamma>)"
          using C_grounding C'_\<mu>_\<gamma>
          by argo
      next
        show "Infer [D\<^sub>G] C\<^sub>G = Infer [clause.to_ground (D \<cdot> \<gamma>)] (clause.to_ground (C' \<cdot> \<mu> \<cdot> \<gamma>))"
          using C'_\<mu>_\<gamma>
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

      show "Infer [D\<^sub>G] C\<^sub>G \<in> ground.G_Inf"
        unfolding ground.G_Inf_def
        using ground_eq_resolution
        by blast
    qed
  qed
qed

lemma eq_factoring_lifting:
  fixes 
    D\<^sub>G C\<^sub>G :: "'f ground_atom clause" and 
    D C :: "('f, 'v) atom clause" and
    \<gamma> :: "('f, 'v) subst"
  defines 
    [simp]: "D\<^sub>G \<equiv> clause.to_ground (D \<cdot> \<gamma>)" and
    [simp]: "C\<^sub>G \<equiv> clause.to_ground (C \<cdot> \<gamma>)"
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
      using ground_eq_factoringI(5) D_grounding
      by simp

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
      using ground_eq_factoringI(1) D\<^sub>G_def
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
      using obtain_welltyped_imgu[OF unified welltyped] that
      by metis
  qed

  let ?C'' = "add_mset (t\<^sub>1 \<approx> t\<^sub>2') (add_mset (t\<^sub>1' !\<approx> t\<^sub>2') D')"
  let ?C' = "?C'' \<cdot> \<mu>"

  show ?thesis
  proof(rule that)

    show eq_factoring: "eq_factoring (D, \<V>) (?C', \<V>)"
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

    show C'_\<gamma>: "?C' \<cdot> \<gamma> = C \<cdot> \<gamma>"
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
        unfolding C\<^sub>G_def
        by (metis clause.from_ground_inverse)

      also have "... = ?C'' \<cdot> \<gamma>"
        using t\<^sub>1_\<gamma> t\<^sub>1'_\<gamma> t\<^sub>2'_\<gamma> D'_\<gamma>
        by simp

      also have "... = ?C' \<cdot> \<gamma>"
        unfolding clause.subst_comp_subst[symmetric] \<mu>_\<gamma> ..

      finally show ?thesis ..
    qed

    show "Infer [D\<^sub>G] C\<^sub>G \<in> inference_groundings (Infer [(D, \<V>)] (?C', \<V>))"
    proof (rule is_inference_grounding_one_premise_inference_groundings)

      show "is_inference_grounding_one_premise (D, \<V>) (?C', \<V>) (Infer [D\<^sub>G] C\<^sub>G) \<gamma>"
      proof(unfold split, intro conjI; (rule D_grounding D_is_welltyped refl \<V>)?)
        show "clause.is_ground (?C' \<cdot> \<gamma>)"
          using C_grounding C'_\<gamma>
          by argo
      next
        show "Infer [D\<^sub>G] C\<^sub>G = Infer [clause.to_ground (D \<cdot> \<gamma>)] (clause.to_ground (?C' \<cdot> \<gamma>))"
          using C'_\<gamma>
          by simp
      next
        have imgu: "term.is_imgu \<mu> {{t\<^sub>1, t\<^sub>2}}"
          using imgu
          by blast

        have "clause.vars ?C' \<subseteq> clause.vars D"
          using clause.variables_in_base_imgu[OF imgu, of ?C'']
          unfolding D l\<^sub>1 l\<^sub>2
          by auto

        then show "is_welltyped_on (clause.vars ?C') \<V> \<gamma>"
          using D_is_welltyped \<gamma>_is_welltyped
          by blast
      next
        show "clause.is_welltyped \<V> ?C'"
          using D_is_welltyped eq_factoring eq_factoring_preserves_typing
          by blast
      qed

      show "Infer [D\<^sub>G] C\<^sub>G \<in> ground.G_Inf"
        unfolding ground.G_Inf_def
        using ground_eq_factoring
        by blast
    qed
  qed
qed

lemma superposition_lifting:
  fixes
    E\<^sub>G D\<^sub>G C\<^sub>G :: "'f ground_atom clause" and
    E D C :: "('f, 'v) atom clause" and
    \<gamma> \<rho>\<^sub>1 \<rho>\<^sub>2 :: "('f, 'v) subst" and
    \<V>\<^sub>1 \<V>\<^sub>2 :: "('v, 'ty) var_types"
  defines
    [simp]: "E\<^sub>G \<equiv> clause.to_ground (E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)" and
    [simp]: "D\<^sub>G \<equiv> clause.to_ground (D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>)" and
    [simp]: "C\<^sub>G \<equiv> clause.to_ground (C \<cdot> \<gamma>)" and
    [simp]: "N\<^sub>G \<equiv> clause_groundings (E, \<V>\<^sub>1) \<union> clause_groundings (D, \<V>\<^sub>2)" and
    [simp]: "\<iota>\<^sub>G \<equiv> Infer [D\<^sub>G, E\<^sub>G] C\<^sub>G"
  assumes
    ground_superposition: "ground.superposition D\<^sub>G E\<^sub>G C\<^sub>G" and
    \<rho>\<^sub>1: "term_subst.is_renaming \<rho>\<^sub>1" and
    \<rho>\<^sub>2: "term_subst.is_renaming \<rho>\<^sub>2" and
    rename_apart: "clause.vars (E \<cdot> \<rho>\<^sub>1) \<inter> clause.vars (D \<cdot> \<rho>\<^sub>2) = {}" and
    E_grounding: "clause.is_ground (E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)" and
    D_grounding: "clause.is_ground (D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>)" and
    C_grounding: "clause.is_ground (C \<cdot> \<gamma>)" and
    select_from_E: "clause.from_ground (select\<^sub>G E\<^sub>G) = (select E) \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>" and
    select_from_D: "clause.from_ground (select\<^sub>G D\<^sub>G) = (select D) \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>" and
    E_is_welltyped: "clause.is_welltyped \<V>\<^sub>1 E" and
    D_is_welltyped: "clause.is_welltyped \<V>\<^sub>2 D" and
    \<rho>\<^sub>1_\<gamma>_is_welltyped: "is_welltyped_on (clause.vars E) \<V>\<^sub>1 (\<rho>\<^sub>1 \<odot> \<gamma>)" and
    \<rho>\<^sub>2_\<gamma>_is_welltyped: "is_welltyped_on (clause.vars D) \<V>\<^sub>2 (\<rho>\<^sub>2 \<odot> \<gamma>)" and
    \<rho>\<^sub>1_is_welltyped: "is_welltyped_on (clause.vars E) \<V>\<^sub>1 \<rho>\<^sub>1" and
    \<rho>\<^sub>2_is_welltyped: "is_welltyped_on (clause.vars D) \<V>\<^sub>2 \<rho>\<^sub>2" and
    \<V>\<^sub>1: "infinite_variables_per_type \<V>\<^sub>1" and
    \<V>\<^sub>2: "infinite_variables_per_type \<V>\<^sub>2" and
    not_redundant: "\<iota>\<^sub>G \<notin> ground.Red_I N\<^sub>G"
  obtains C' \<V>\<^sub>3
  where
    "superposition (D, \<V>\<^sub>2) (E, \<V>\<^sub>1) (C', \<V>\<^sub>3)"
    "\<iota>\<^sub>G \<in> inference_groundings (Infer [(D, \<V>\<^sub>2), (E, \<V>\<^sub>1)] (C', \<V>\<^sub>3))"
    "C' \<cdot> \<gamma> = C \<cdot> \<gamma>"
  using ground_superposition
proof(cases D\<^sub>G E\<^sub>G C\<^sub>G rule: ground.superposition.cases)
  case ground_superpositionI: (superpositionI l\<^sub>G\<^sub>1 E\<^sub>G' l\<^sub>G\<^sub>2 D\<^sub>G' \<P>\<^sub>G c\<^sub>G t\<^sub>G\<^sub>1 t\<^sub>G\<^sub>2 t\<^sub>G\<^sub>3)

  have E_\<gamma>: "E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma> = clause.from_ground (add_mset l\<^sub>G\<^sub>1 E\<^sub>G')"
    using ground_superpositionI(1) 
    unfolding E\<^sub>G_def
    by (metis E_grounding clause.to_ground_inverse)

  have D_\<gamma>: "D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma> = clause.from_ground (add_mset l\<^sub>G\<^sub>2 D\<^sub>G')"
    using ground_superpositionI(2) D\<^sub>G_def
    by (metis D_grounding clause.to_ground_inverse)

  let ?select\<^sub>G_empty = "select\<^sub>G (clause.to_ground (E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)) = {#}"
  let ?select\<^sub>G_not_empty = "select\<^sub>G (clause.to_ground (E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)) \<noteq> {#}"

  obtain l\<^sub>1 where
    l\<^sub>1_\<gamma>: "l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma> = literal.from_ground l\<^sub>G\<^sub>1" and
    l\<^sub>1_is_strictly_maximal: "\<P>\<^sub>G = Pos \<Longrightarrow> is_strictly_maximal l\<^sub>1 E" and
    l\<^sub>1_is_maximal: "\<P>\<^sub>G = Neg \<Longrightarrow> ?select\<^sub>G_empty \<Longrightarrow> is_maximal l\<^sub>1 E" and
    l\<^sub>1_selected: "\<P>\<^sub>G = Neg \<Longrightarrow> ?select\<^sub>G_not_empty \<Longrightarrow> is_maximal l\<^sub>1 (select E)" and
    l\<^sub>1_in_E: "l\<^sub>1 \<in># E"
  proof-

    have E_not_empty: "E \<noteq> {#}"
      using ground_superpositionI(1) 
      by auto

    have "is_strictly_maximal (literal.from_ground l\<^sub>G\<^sub>1) (E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)" if "\<P>\<^sub>G = Pos"
      using ground_superpositionI(9) that E_grounding
      by simp

    then obtain positive_l\<^sub>1 where
      "is_strictly_maximal positive_l\<^sub>1 E"
      "positive_l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma> = literal.from_ground l\<^sub>G\<^sub>1" 
    if "\<P>\<^sub>G = Pos"
      using obtain_strictly_maximal_literal[OF E_grounding]
      by metis

    moreover then have "positive_l\<^sub>1 \<in># E" if "\<P>\<^sub>G = Pos"
      using that strictly_maximal_in_clause
      by blast

    moreover then have "is_maximal (literal.from_ground l\<^sub>G\<^sub>1) (E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)" if ?select\<^sub>G_empty
      using that ground_superpositionI(9) is_maximal_empty E_grounding
      by auto

    then obtain negative_maximal_l\<^sub>1 where
      "is_maximal negative_maximal_l\<^sub>1 E"
      "negative_maximal_l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma> = literal.from_ground l\<^sub>G\<^sub>1"
    if "\<P>\<^sub>G = Neg" ?select\<^sub>G_empty
      using
        obtain_maximal_literal[OF E_not_empty E_grounding[folded clause.subst_comp_subst]]
        unique_maximal_in_ground_clause[OF E_grounding[folded clause.subst_comp_subst]]
      by metis

    moreover then have "negative_maximal_l\<^sub>1 \<in># E" if "\<P>\<^sub>G = Neg" ?select\<^sub>G_empty
      using that maximal_in_clause
      by blast

    moreover have "ground_is_maximal l\<^sub>G\<^sub>1 (select\<^sub>G E\<^sub>G)" if "\<P>\<^sub>G = Neg" ?select\<^sub>G_not_empty
      using ground_superpositionI(9) that
      by simp

    then obtain negative_selected_l\<^sub>1 where
      "is_maximal negative_selected_l\<^sub>1 (select E)"
      "negative_selected_l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma> = literal.from_ground l\<^sub>G\<^sub>1" 
    if "\<P>\<^sub>G = Neg" ?select\<^sub>G_not_empty
      using 
        select_from_E
        unique_maximal_in_ground_clause
        obtain_maximal_literal
      unfolding E\<^sub>G_def
      by (metis (no_types, lifting) clause.ground_is_ground clause_from_ground_empty 
          clause_subst_empty)

    moreover then have "negative_selected_l\<^sub>1 \<in># E" if "\<P>\<^sub>G = Neg" ?select\<^sub>G_not_empty 
      using that
      by (meson maximal_in_clause mset_subset_eqD select_subset)

    ultimately show ?thesis
      using that ground_superpositionI(9)
      by (metis literals_distinct(1))
  qed

  obtain E' where E: "E = add_mset l\<^sub>1 E'"
    by (meson l\<^sub>1_in_E multi_member_split)

  then have E'_\<gamma>: "E' \<cdot> \<rho>\<^sub>1 \<odot> \<gamma> = clause.from_ground E\<^sub>G'"
    using l\<^sub>1_\<gamma> E_\<gamma>
    by auto

  let ?\<P> = "if \<P>\<^sub>G = Pos then Pos else Neg"

  have [simp]: "\<P>\<^sub>G \<noteq> Pos \<longleftrightarrow> \<P>\<^sub>G = Neg" "\<P>\<^sub>G \<noteq> Neg \<longleftrightarrow> \<P>\<^sub>G = Pos"
    using ground_superpositionI(4)
    by auto

  have [simp]: "\<And>a \<sigma>. ?\<P> a \<cdot>l \<sigma> = ?\<P> (a \<cdot>a \<sigma>)"
    by auto

  have [simp]: "\<And>\<V> a. literal.is_welltyped \<V> (?\<P> a) \<longleftrightarrow> atom.is_welltyped \<V> a"
    by(auto simp: literal_is_welltyped_iff_atm_of)

  have [simp]: "\<And>a. literal.vars (?\<P> a) = atom.vars a"
    by auto

  have l\<^sub>1_\<gamma>: 
    "l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma> = ?\<P> (Upair (context.from_ground c\<^sub>G)\<langle>term.from_ground t\<^sub>G\<^sub>1\<rangle> (term.from_ground t\<^sub>G\<^sub>2))"
    unfolding ground_superpositionI l\<^sub>1_\<gamma>
    by simp

  obtain c\<^sub>1 t\<^sub>1 t\<^sub>1' where 
    l\<^sub>1: "l\<^sub>1 = ?\<P> (Upair c\<^sub>1\<langle>t\<^sub>1\<rangle> t\<^sub>1')" and
    t\<^sub>1'_\<gamma>: "t\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<odot> \<gamma> = term.from_ground t\<^sub>G\<^sub>2" and
    t\<^sub>1_\<gamma>: "t\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<odot> \<gamma> = term.from_ground t\<^sub>G\<^sub>1" and
    c\<^sub>1_\<gamma>: "c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<odot> \<gamma> = context.from_ground c\<^sub>G" and
    t\<^sub>1_is_Fun: "is_Fun t\<^sub>1"
  proof-

    obtain c\<^sub>1_t\<^sub>1 t\<^sub>1' where 
      l\<^sub>1: "l\<^sub>1 = ?\<P> (Upair c\<^sub>1_t\<^sub>1 t\<^sub>1')" and
      t\<^sub>1'_\<gamma>: "t\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<odot> \<gamma> = term.from_ground t\<^sub>G\<^sub>2" and
      c\<^sub>1_t\<^sub>1_\<gamma>: "c\<^sub>1_t\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<odot> \<gamma> = (context.from_ground c\<^sub>G)\<langle>term.from_ground t\<^sub>G\<^sub>1\<rangle>"
      using l\<^sub>1_\<gamma>
      by (smt (verit) obtain_from_literal_subst)

    let ?inference_into_Fun =
      "\<exists>c\<^sub>1 t\<^sub>1. 
        c\<^sub>1_t\<^sub>1 = c\<^sub>1\<langle>t\<^sub>1\<rangle> \<and>
        t\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<odot> \<gamma> = term.from_ground t\<^sub>G\<^sub>1 \<and>
        c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<odot> \<gamma> = context.from_ground c\<^sub>G \<and>
        is_Fun t\<^sub>1"

    have "\<not> ?inference_into_Fun \<Longrightarrow> ground.redundant_infer N\<^sub>G \<iota>\<^sub>G"
    proof-
      assume "\<not> ?inference_into_Fun"

      with c\<^sub>1_t\<^sub>1_\<gamma>
      obtain t\<^sub>1 c\<^sub>1 c\<^sub>G' where
        c\<^sub>1_t\<^sub>1: "c\<^sub>1_t\<^sub>1 = c\<^sub>1\<langle>t\<^sub>1\<rangle>" and
        t\<^sub>1_is_Var: "is_Var t\<^sub>1" and
        c\<^sub>G: "c\<^sub>G = context.to_ground (c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<odot> \<gamma>) \<circ>\<^sub>c c\<^sub>G'"
      proof(induction c\<^sub>1_t\<^sub>1 arbitrary: c\<^sub>G thesis)
        case (Var x)

        show ?case
        proof(rule Var.prems)
          show "Var x = \<box>\<langle>Var x\<rangle>"
            by simp

          show "is_Var (Var x)"
            by simp

          show "c\<^sub>G = context.to_ground (\<box> \<cdot>t\<^sub>c \<rho>\<^sub>1 \<odot> \<gamma>) \<circ>\<^sub>c c\<^sub>G"
            by (simp add: context.to_ground_def)
        qed
      next
        case (Fun f ts)

        have "c\<^sub>G \<noteq> \<box>"
          using Fun.prems(2,3)
          unfolding context.from_ground_def
          by (metis actxt.simps(8) intp_actxt.simps(1) is_FunI)

        then obtain ts\<^sub>G\<^sub>1 c\<^sub>G' ts\<^sub>G\<^sub>2 where
          c\<^sub>G: "c\<^sub>G = More f ts\<^sub>G\<^sub>1 c\<^sub>G' ts\<^sub>G\<^sub>2"
          using Fun.prems
          by (cases c\<^sub>G) (auto simp: context.from_ground_def)

        have
          "map (\<lambda>t. t \<cdot>t \<rho>\<^sub>1 \<odot> \<gamma>) ts =
            map term.from_ground ts\<^sub>G\<^sub>1 @ (context.from_ground c\<^sub>G')\<langle>term.from_ground t\<^sub>G\<^sub>1\<rangle> # 
            map term.from_ground ts\<^sub>G\<^sub>2"
          using Fun(3)
          unfolding c\<^sub>G context.from_ground_def
          by simp

        moreover then obtain ts\<^sub>1 t ts\<^sub>2 where 
          ts: "ts = ts\<^sub>1 @ t # ts\<^sub>2" and
          ts\<^sub>1_\<gamma>: "map (\<lambda>term. term \<cdot>t \<rho>\<^sub>1 \<odot> \<gamma>) ts\<^sub>1 = map term.from_ground ts\<^sub>G\<^sub>1" and
          ts\<^sub>2_\<gamma>: "map (\<lambda>term. term \<cdot>t \<rho>\<^sub>1 \<odot> \<gamma>) ts\<^sub>2 = map term.from_ground ts\<^sub>G\<^sub>2"            
          by (smt append_eq_map_conv map_eq_Cons_D)

        ultimately have t_\<gamma>: "t \<cdot>t \<rho>\<^sub>1 \<odot> \<gamma> = (context.from_ground c\<^sub>G')\<langle>term.from_ground t\<^sub>G\<^sub>1\<rangle>"
          by simp

        obtain t\<^sub>1 c\<^sub>1 c\<^sub>G'' where 
          "t = c\<^sub>1\<langle>t\<^sub>1\<rangle>" and
          "is_Var t\<^sub>1" and
          "c\<^sub>G' = context.to_ground (c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<odot> \<gamma>) \<circ>\<^sub>c c\<^sub>G''"
        proof-
          have "t \<in> set ts"
            by (simp add: ts)

          moreover have
            "\<nexists>c\<^sub>1 t\<^sub>1. t = c\<^sub>1\<langle>t\<^sub>1\<rangle> \<and> 
                t\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<odot> \<gamma> = term.from_ground t\<^sub>G\<^sub>1 \<and> 
                c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<odot> \<gamma> = context.from_ground c\<^sub>G' \<and> 
                is_Fun t\<^sub>1"
          proof(rule notI, elim exE conjE)
            fix c\<^sub>1 t\<^sub>1
            assume 
              "t = c\<^sub>1\<langle>t\<^sub>1\<rangle>" 
              "t\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<odot> \<gamma> = term.from_ground t\<^sub>G\<^sub>1" 
              "c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<odot> \<gamma> = context.from_ground c\<^sub>G'" 
              "is_Fun t\<^sub>1"

            moreover then have 
              "Fun f ts = (More f ts\<^sub>1 c\<^sub>1 ts\<^sub>2)\<langle>t\<^sub>1\<rangle>" 
              "(More f ts\<^sub>1 c\<^sub>1 ts\<^sub>2) \<cdot>t\<^sub>c \<rho>\<^sub>1 \<odot> \<gamma> = context.from_ground c\<^sub>G"
              unfolding context.from_ground_def c\<^sub>G ts
              using ts\<^sub>1_\<gamma> ts\<^sub>2_\<gamma>
              by auto

            ultimately show False
              using Fun.prems(3)
              by blast
          qed

          ultimately show ?thesis
            using Fun(1) t_\<gamma> that
            by blast
        qed

        moreover then have
          "Fun f ts = (More f ts\<^sub>1 c\<^sub>1 ts\<^sub>2)\<langle>t\<^sub>1\<rangle>"
          "c\<^sub>G = context.to_ground (More f ts\<^sub>1 c\<^sub>1 ts\<^sub>2 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<odot> \<gamma>) \<circ>\<^sub>c c\<^sub>G''"
          using ts\<^sub>1_\<gamma> ts\<^sub>2_\<gamma>
          unfolding context.to_ground_def c\<^sub>G ts
          by auto

        ultimately show ?case
          using Fun.prems(1)
          by blast
      qed

      obtain x where t\<^sub>1_\<rho>\<^sub>1: "t\<^sub>1 \<cdot>t \<rho>\<^sub>1 = Var x"
        using t\<^sub>1_is_Var term.id_subst_rename[OF \<rho>\<^sub>1]
        unfolding is_Var_def
        by auto

      have \<iota>\<^sub>G_parts: 
        "set (side_prems_of \<iota>\<^sub>G) = {D\<^sub>G}" 
        "main_prem_of \<iota>\<^sub>G = E\<^sub>G"
        "concl_of \<iota>\<^sub>G = C\<^sub>G"
        by simp_all

      show ?thesis
      proof(rule ground.redundant_infer_singleton, unfold \<iota>\<^sub>G_parts, intro bexI conjI)

        let ?t\<^sub>G = "(context.from_ground c\<^sub>G')\<langle>term.from_ground t\<^sub>G\<^sub>3\<rangle>"

        define \<gamma>' where
          "\<gamma>' \<equiv> \<gamma>(x := ?t\<^sub>G)"

        let ?E\<^sub>G' = "clause.to_ground (E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>')"

        have t\<^sub>1_\<gamma>: "t\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<odot> \<gamma> = (context.from_ground c\<^sub>G')\<langle>term.from_ground t\<^sub>G\<^sub>1\<rangle>"
        proof -

          have "context.is_ground (c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<odot> \<gamma>)"
            using c\<^sub>1_t\<^sub>1_\<gamma>
            unfolding c\<^sub>1_t\<^sub>1 context.safe_unfolds
            by (metis context.ground_is_ground context.term_with_context_is_ground 
                term.ground_is_ground)

          then show ?thesis
            using c\<^sub>1_t\<^sub>1_\<gamma>
            unfolding c\<^sub>1_t\<^sub>1 c\<^sub>1_t\<^sub>1_\<gamma> c\<^sub>G
            by auto
        qed

        have t\<^sub>1_\<gamma>': "t\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<odot> \<gamma>' = (context.from_ground c\<^sub>G')\<langle>term.from_ground t\<^sub>G\<^sub>3\<rangle>"
          unfolding \<gamma>'_def
          using t\<^sub>1_\<rho>\<^sub>1
          by simp
         
        show "?E\<^sub>G' \<in> N\<^sub>G"
        proof-

          have "?E\<^sub>G' \<in> clause_groundings (E, \<V>\<^sub>1)"
          proof(unfold clause_groundings_def mem_Collect_eq fst_conv snd_conv, 
              intro exI conjI E_is_welltyped \<V>\<^sub>1, 
              rule refl)

            show "clause.is_ground (E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>')"
              unfolding \<gamma>'_def
              using E_grounding
              by simp

            show "is_welltyped_on (clause.vars E) \<V>\<^sub>1 (\<rho>\<^sub>1 \<odot> \<gamma>')"
            proof(intro is_welltyped_on_subst_compose \<rho>\<^sub>1_is_welltyped)
              
              have "welltyped \<V>\<^sub>1 ?t\<^sub>G (\<V>\<^sub>1 x)"
              proof-

                have "welltyped \<V>\<^sub>1 (context.from_ground c\<^sub>G')\<langle>term.from_ground t\<^sub>G\<^sub>1\<rangle> (\<V>\<^sub>1 x)"
                proof-

                  have "welltyped \<V>\<^sub>1 (t\<^sub>1 \<cdot>t \<rho>\<^sub>1) (\<V>\<^sub>1 x)"
                    using t\<^sub>1_\<rho>\<^sub>1
                    by auto

                  then have "welltyped \<V>\<^sub>1 (t\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<odot> \<gamma>) (\<V>\<^sub>1 x)"
                    using \<rho>\<^sub>1_is_welltyped \<rho>\<^sub>1_\<gamma>_is_welltyped
                    unfolding E c\<^sub>1_t\<^sub>1 l\<^sub>1 subst_compose_def
                    by simp

                  moreover have "context.is_ground (c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<odot> \<gamma>)"
                    using c\<^sub>1_t\<^sub>1_\<gamma> 
                    unfolding c\<^sub>1_t\<^sub>1 context.safe_unfolds
                    by (metis context.ground_is_ground context.term_with_context_is_ground 
                        term.ground_is_ground)

                  then have "t\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<odot> \<gamma> = (context.from_ground c\<^sub>G')\<langle>term.from_ground t\<^sub>G\<^sub>1\<rangle>"
                    using c\<^sub>1_t\<^sub>1_\<gamma>
                    unfolding c\<^sub>1_t\<^sub>1 c\<^sub>1_t\<^sub>1_\<gamma> c\<^sub>G
                    by auto

                  ultimately show ?thesis
                    by argo
                qed

                moreover obtain \<tau> where
                  "welltyped \<V>\<^sub>1 (term.from_ground t\<^sub>G\<^sub>1) \<tau>" 
                  "welltyped \<V>\<^sub>1 (term.from_ground t\<^sub>G\<^sub>3) \<tau>"
                proof-
                  have "clause.is_welltyped \<V>\<^sub>2 (clause.from_ground D\<^sub>G)"
                    using D_is_welltyped
                    unfolding
                      D\<^sub>G_def
                      clause.to_ground_inverse[OF D_grounding]
                      clause.is_welltyped.subst_stability[OF \<rho>\<^sub>2_\<gamma>_is_welltyped].

                  then obtain \<tau> where
                    "welltyped \<V>\<^sub>2 (term.from_ground t\<^sub>G\<^sub>1) \<tau>"
                    "welltyped \<V>\<^sub>2 (term.from_ground t\<^sub>G\<^sub>3) \<tau>"
                    unfolding ground_superpositionI
                    by auto

                  then show ?thesis
                    using that welltyped.explicit_replace_\<V>_iff[of _ \<V>\<^sub>2 \<V>\<^sub>1]
                    by simp
                qed

                 ultimately show ?thesis
                  by auto              
              qed

              moreover have "is_welltyped_on (\<Union> (term.vars ` \<rho>\<^sub>1 ` clause.vars E)) \<V>\<^sub>1 \<gamma>"
                by (intro is_welltyped_on_subst_compose_renaming \<rho>\<^sub>1_\<gamma>_is_welltyped
                    \<rho>\<^sub>1_is_welltyped \<rho>\<^sub>1)

              ultimately show "is_welltyped_on (\<Union> (term.vars ` \<rho>\<^sub>1 ` clause.vars E)) \<V>\<^sub>1 \<gamma>'"
                unfolding \<gamma>'_def
                by simp
            qed
          qed

          then show ?thesis
            by simp
        qed
     
        show "ground.G_entails {?E\<^sub>G', D\<^sub>G} {C\<^sub>G}"
        proof(unfold ground.G_entails_def, intro allI impI)
          fix I :: "'f gterm rel"
          let ?I = "upair ` I"

          assume 
            refl_I: "refl I" and 
            trans_I: "trans I" and 
            sym_I: "sym I" and
            compatible_with_gctxt_I: "compatible_with_gctxt I" and
            premise: "?I \<TTurnstile>s {?E\<^sub>G', D\<^sub>G}"

           then interpret clause_entailment I
             by unfold_locales

          have \<gamma>_x_is_ground: "term.is_ground (\<gamma> x)"
            using t\<^sub>1_\<gamma> t\<^sub>1_\<rho>\<^sub>1
            by auto

          show "?I \<TTurnstile>s {C\<^sub>G}"
          proof(cases "?I \<TTurnstile> D\<^sub>G'")
            case True

            then show ?thesis
              unfolding ground_superpositionI
              by auto
          next
            case False

            then have t\<^sub>G\<^sub>1_t\<^sub>G\<^sub>3: "Upair t\<^sub>G\<^sub>1 t\<^sub>G\<^sub>3 \<in> ?I"
              using premise sym
              unfolding ground_superpositionI
              by auto

            have "?I \<TTurnstile>l c\<^sub>G'\<langle>t\<^sub>G\<^sub>1\<rangle>\<^sub>G \<approx> c\<^sub>G'\<langle>t\<^sub>G\<^sub>3\<rangle>\<^sub>G"
              using upair_compatible_with_gctxtI[OF t\<^sub>G\<^sub>1_t\<^sub>G\<^sub>3]
              by auto

            then have "?I \<TTurnstile>l term.to_ground (t\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<odot> \<gamma>) \<approx> term.to_ground (t\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<odot> \<gamma>')"
              unfolding t\<^sub>1_\<gamma> t\<^sub>1_\<gamma>'
              by simp

            then have "(term.to_ground (\<gamma> x), c\<^sub>G'\<langle>t\<^sub>G\<^sub>3\<rangle>\<^sub>G) \<in> I"
              unfolding \<gamma>'_def
              using t\<^sub>1_\<rho>\<^sub>1
              by (auto simp: sym)

            moreover have "?I \<TTurnstile> ?E\<^sub>G'"
              using premise
              by simp

            ultimately have "?I \<TTurnstile> E\<^sub>G"
              unfolding \<gamma>'_def
              using
                clause.symmetric_congruence[of _ \<gamma>, OF _ \<gamma>_x_is_ground]
                E_grounding
              by simp

            then have "?I \<TTurnstile> add_mset (\<P>\<^sub>G (Upair c\<^sub>G\<langle>t\<^sub>G\<^sub>3\<rangle>\<^sub>G t\<^sub>G\<^sub>2)) E\<^sub>G'"
              unfolding ground_superpositionI
              using symmetric_literal_context_congruence[OF t\<^sub>G\<^sub>1_t\<^sub>G\<^sub>3]
              by (cases "\<P>\<^sub>G = Pos") simp_all

            then show ?thesis
              unfolding ground_superpositionI
              by blast
          qed
        qed

        show "?E\<^sub>G' \<prec>\<^sub>c\<^sub>G E\<^sub>G"
        proof-

          have "\<gamma> x = t\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<odot> \<gamma>"
            using t\<^sub>1_\<rho>\<^sub>1
            by simp

          then have t\<^sub>G_smaller: "?t\<^sub>G \<prec>\<^sub>t \<gamma> x"
            using ground_superpositionI(8)
            unfolding t\<^sub>1_\<gamma> term.order.less\<^sub>G_def
            by simp

          have "add_mset (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma>') (E' \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>') \<prec>\<^sub>c add_mset (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma>) (E' \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)"
          proof(rule less\<^sub>c_add_mset)

            have "x \<in> literal.vars (l\<^sub>1 \<cdot>l \<rho>\<^sub>1)"
              unfolding l\<^sub>1 c\<^sub>1_t\<^sub>1 literal.vars_def atom.vars_def 
              using t\<^sub>1_\<rho>\<^sub>1
              by auto

            moreover have "literal.is_ground (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma>)"
              using E_grounding
              unfolding E
              by simp

            ultimately show "l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma>' \<prec>\<^sub>l l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<gamma>"
              unfolding \<gamma>'_def
              using literal.order.subst_update_stability t\<^sub>G_smaller
              by simp
          next

            have "clause.is_ground (E' \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)"
              using E'_\<gamma>
              by simp

            then show "E' \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>' \<preceq>\<^sub>c E' \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>"
              unfolding \<gamma>'_def
              using clause.order.subst_update_stability t\<^sub>G_smaller
              by (cases "x \<in> clause.vars (E' \<cdot> \<rho>\<^sub>1)") simp_all
          qed

          then have "E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>' \<prec>\<^sub>c E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>"
            unfolding E
            by simp

          moreover have "clause.is_ground (E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>')"
            unfolding \<gamma>'_def
            using E_grounding
            by simp

          ultimately show ?thesis
            using E_grounding
            unfolding clause.order.less\<^sub>G_def
            by simp
        qed
      qed
    qed

    then show ?thesis
      using not_redundant ground_superposition that l\<^sub>1 t\<^sub>1'_\<gamma> c\<^sub>1_t\<^sub>1_\<gamma> 
      unfolding ground.Red_I_def ground.G_Inf_def
      by auto
  qed

  obtain l\<^sub>2 where 
    l\<^sub>2_\<gamma>: "l\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<odot> \<gamma> = literal.from_ground l\<^sub>G\<^sub>2" and
    l\<^sub>2_is_strictly_maximal: "is_strictly_maximal l\<^sub>2 D"
  proof-
    have "is_strictly_maximal (literal.from_ground l\<^sub>G\<^sub>2) (D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>)"
      using ground_superpositionI(11) D_grounding
      by simp

    then show ?thesis
      using obtain_strictly_maximal_literal[OF D_grounding] that
      by metis
  qed

  then have l\<^sub>2_in_D: "l\<^sub>2 \<in># D" 
    using strictly_maximal_in_clause 
    by blast

  from l\<^sub>2_\<gamma> have l\<^sub>2_\<gamma>: "l\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<odot> \<gamma> = term.from_ground t\<^sub>G\<^sub>1 \<approx> term.from_ground t\<^sub>G\<^sub>3"
    unfolding ground_superpositionI
    by simp

  then obtain t\<^sub>2 t\<^sub>2' where
    l\<^sub>2: "l\<^sub>2 = t\<^sub>2 \<approx> t\<^sub>2'" and
    t\<^sub>2_\<gamma>: "t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<odot> \<gamma> = term.from_ground t\<^sub>G\<^sub>1" and     
    t\<^sub>2'_\<gamma>: "t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<odot> \<gamma> = term.from_ground t\<^sub>G\<^sub>3"
    using obtain_from_pos_literal_subst
    by metis

  obtain D' where D: "D = add_mset l\<^sub>2 D'"
    by (meson l\<^sub>2_in_D multi_member_split)

  then have D'_\<gamma>: "D' \<cdot> \<rho>\<^sub>2 \<odot> \<gamma> = clause.from_ground D\<^sub>G'"
    using D_\<gamma> l\<^sub>2_\<gamma>
    unfolding ground_superpositionI
    by auto

  (* TODO: inv *) 
  define \<V>\<^sub>3 where 
    "\<And>x. \<V>\<^sub>3 x \<equiv>
        if x \<in> clause.vars (E \<cdot> \<rho>\<^sub>1)
        then \<V>\<^sub>1 (inv \<rho>\<^sub>1 (Var x))
        else \<V>\<^sub>2 (inv \<rho>\<^sub>2 (Var x))"

  have \<gamma>_is_welltyped: "is_welltyped_on (clause.vars (E \<cdot> \<rho>\<^sub>1) \<union> clause.vars (D \<cdot> \<rho>\<^sub>2)) \<V>\<^sub>3 \<gamma>"
  proof(unfold Set.ball_Un, intro conjI)

    show "is_welltyped_on (clause.vars (E \<cdot> \<rho>\<^sub>1)) \<V>\<^sub>3 \<gamma>"
      unfolding \<V>\<^sub>3_def
      using clause.is_welltyped.renaming_grounding[OF \<rho>\<^sub>1 \<rho>\<^sub>1_\<gamma>_is_welltyped E_grounding]
      by simp

  next
    have "\<forall>x\<in>clause.vars (D \<cdot> \<rho>\<^sub>2). \<V>\<^sub>3 x = \<V>\<^sub>2 (inv \<rho>\<^sub>2 (Var x))"
      unfolding \<V>\<^sub>3_def
      using rename_apart
      by auto

    then show "is_welltyped_on (clause.vars (D \<cdot> \<rho>\<^sub>2)) \<V>\<^sub>3 \<gamma>"
      unfolding \<V>\<^sub>3_def
      using clause.is_welltyped.renaming_grounding[OF \<rho>\<^sub>2 \<rho>\<^sub>2_\<gamma>_is_welltyped D_grounding]
      by simp
  qed

  obtain \<mu> \<sigma> where
    \<gamma>: "\<gamma> = \<mu> \<odot> \<sigma>" and
    imgu: "welltyped_imgu \<V>\<^sub>3 (t\<^sub>1 \<cdot>t \<rho>\<^sub>1) (t\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<mu>"
  proof-

    have unified: "t\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<gamma> = t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<gamma>"
      using t\<^sub>1_\<gamma> t\<^sub>2_\<gamma> 
      by simp

    obtain \<tau> where welltyped: "welltyped \<V>\<^sub>3 (t\<^sub>1 \<cdot>t \<rho>\<^sub>1) \<tau>" "welltyped \<V>\<^sub>3 (t\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<tau>"
    proof-
      have "clause.is_welltyped \<V>\<^sub>2 (D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>)"
        using \<rho>\<^sub>2_\<gamma>_is_welltyped D_is_welltyped
        by (metis clause.is_welltyped.subst_stability)

      then obtain \<tau> where 
        "welltyped \<V>\<^sub>2 (term.from_ground t\<^sub>G\<^sub>1) \<tau>" 
        unfolding D_\<gamma> ground_superpositionI
        by auto

      then have "welltyped \<V>\<^sub>3 (term.from_ground t\<^sub>G\<^sub>1) \<tau>" 
        using welltyped.is_ground_typed
        by (meson term.ground_is_ground welltyped.explicit_is_ground_typed)

      then have "welltyped \<V>\<^sub>3 (t\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<odot> \<gamma>) \<tau>" "welltyped \<V>\<^sub>3 (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<odot> \<gamma>) \<tau>"
        using t\<^sub>1_\<gamma> t\<^sub>2_\<gamma>
        by presburger+

      moreover have
        "term.vars (t\<^sub>1 \<cdot>t \<rho>\<^sub>1) \<subseteq> clause.vars (E \<cdot> \<rho>\<^sub>1)"
        "term.vars (t\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<subseteq> clause.vars (D \<cdot> \<rho>\<^sub>2)"
        unfolding E l\<^sub>1 clause.add_subst D l\<^sub>2
        by auto

      ultimately have "welltyped \<V>\<^sub>3 (t\<^sub>1 \<cdot>t \<rho>\<^sub>1) \<tau>" "welltyped \<V>\<^sub>3 (t\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<tau>"
        using \<gamma>_is_welltyped
        by (simp_all add: subsetD)

      then show ?thesis
        using that
        by blast
    qed

    show ?thesis
      using obtain_welltyped_imgu[OF unified welltyped] that
      by metis
  qed

  define C' where 
    C': "C' = add_mset (?\<P> (Upair (c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> (t\<^sub>1' \<cdot>t \<rho>\<^sub>1))) (E' \<cdot> \<rho>\<^sub>1 + D' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu>"

  show ?thesis
  proof(rule that)

    show superposition: "superposition (D, \<V>\<^sub>2) (E, \<V>\<^sub>1) (C', \<V>\<^sub>3)"
    proof(rule superpositionI, rule \<rho>\<^sub>1, rule \<rho>\<^sub>2; 
        ((rule E D l\<^sub>1 l\<^sub>2 t\<^sub>1_is_Fun imgu rename_apart \<rho>\<^sub>1_is_welltyped \<rho>\<^sub>2_is_welltyped \<V>\<^sub>1 \<V>\<^sub>2 C')+)?)

      show "?\<P> \<in> {Pos, Neg}"
        by simp
    next

      show "\<not> E \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<preceq>\<^sub>c D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>"
      proof(rule clause.order.ground_less_not_less_eq)

        show "clause.vars (D \<cdot> \<rho>\<^sub>2 \<odot> \<mu> \<cdot> \<sigma>) = {}"
          using D_grounding
          unfolding \<gamma>
          by simp

        show "clause.vars (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<cdot> \<sigma>) = {}"
          using E_grounding
          unfolding \<gamma>
          by simp

        show "D \<cdot> \<rho>\<^sub>2 \<odot> \<mu> \<cdot> \<sigma> \<prec>\<^sub>c E \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<cdot> \<sigma>"
          using ground_superpositionI(3) D_grounding E_grounding
          unfolding E\<^sub>G_def D\<^sub>G_def clause.order.less\<^sub>G_def \<gamma>
          by simp
      qed
    next
      have "select E = {#}" "is_strictly_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)" if "?\<P> = Pos"
      proof -

        show "select E = {#}"
          using that ground_superpositionI(9) select_from_E
          by fastforce

        show "is_strictly_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)"
        proof(rule is_strictly_maximal_if_grounding_is_strictly_maximal)

          show "l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu> \<in># E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>"
            using l\<^sub>1_in_E
            by blast

          show "clause.is_ground (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<cdot> \<sigma>)"
            using E_grounding[unfolded \<gamma>]
            by simp

          show "is_strictly_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu> \<cdot>l \<sigma>) (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<cdot> \<sigma>)"
            using that l\<^sub>1_\<gamma> E_\<gamma> ground_superpositionI(9)
            unfolding \<gamma> ground_superpositionI
            by fastforce
        qed
      qed

      moreover have "select E = {#}" "is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)" 
        if "?\<P> = Neg" ?select\<^sub>G_empty
      proof-
        show "select E = {#}"
          using clause_subst_empty select_from_E ground_superpositionI(9) that
          by simp
      next
        show "is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)"
        proof(rule is_maximal_if_grounding_is_maximal)

          show "l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu> \<in># E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>"
            using l\<^sub>1_in_E
            by blast
        next

          show "clause.is_ground (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<cdot> \<sigma>)"
            using E_grounding \<gamma> 
            by auto
        next

          show "is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu> \<cdot>l \<sigma>) (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<cdot> \<sigma>) "
            using l\<^sub>1_\<gamma> \<gamma> E_\<gamma> ground_superpositionI(5,9) is_maximal_empty that
            by auto
        qed
      qed

      moreover have "is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) ((select E) \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)" 
        if "?\<P> = Neg" "\<not>?select\<^sub>G_empty"
      proof(rule is_maximal_if_grounding_is_maximal)

        show "l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu> \<in># select E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>"
          using ground_superpositionI(9) l\<^sub>1_selected maximal_in_clause that 
          by auto
      next

        show "clause.is_ground (select E \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<cdot> \<sigma>)"
          using select_ground_subst[OF E_grounding]
          unfolding \<gamma>
          by simp
      next
        show "is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu> \<cdot>l \<sigma>) (select E \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<cdot> \<sigma>)"
          using \<gamma> ground_superpositionI(5,9) l\<^sub>1_\<gamma> that select_from_E 
          by fastforce
      qed

      ultimately show "?\<P> = Pos
              \<and> select E = {#}
              \<and> is_strictly_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)
          \<or> ?\<P> = Neg
              \<and> (select E = {#} \<and> is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)
                 \<or> is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) ((select E) \<cdot> \<rho>\<^sub>1 \<odot> \<mu>))"
        by meson
    next

      show "select D = {#}"
        using ground_superpositionI(10) select_from_D
        by simp
    next 

      show "is_strictly_maximal (l\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<odot> \<mu>) (D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>)"
      proof(rule is_strictly_maximal_if_grounding_is_strictly_maximal)

        show "l\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<odot> \<mu> \<in># D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>"
          using l\<^sub>2_in_D
          by blast
      next

        show "clause.is_ground (D \<cdot> \<rho>\<^sub>2 \<odot> \<mu> \<cdot> \<sigma>)"
          using D_grounding
          unfolding \<gamma>
          by simp
      next

        show "is_strictly_maximal (l\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<odot> \<mu> \<cdot>l \<sigma>) (D \<cdot> \<rho>\<^sub>2 \<odot> \<mu> \<cdot> \<sigma>)"
          using l\<^sub>2_\<gamma> \<gamma> D_\<gamma> ground_superpositionI(6,11) 
          by auto
      qed
    next

      show "\<not> c\<^sub>1\<langle>t\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<odot> \<mu> \<preceq>\<^sub>t t\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<odot> \<mu>"
      proof(rule term.order.ground_less_not_less_eq)

        show "term.is_ground (t\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<odot> \<mu> \<cdot>t \<sigma>)"
          using t\<^sub>1'_\<gamma> \<gamma>
          by simp
      next

        show "term.is_ground (c\<^sub>1\<langle>t\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<odot> \<mu> \<cdot>t \<sigma>)"
          using t\<^sub>1_\<gamma> c\<^sub>1_\<gamma> \<gamma>
          by simp
      next

        show "t\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<odot> \<mu> \<cdot>t \<sigma> \<prec>\<^sub>t c\<^sub>1\<langle>t\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<odot> \<mu> \<cdot>t \<sigma>"
          using ground_superpositionI(7) c\<^sub>1_\<gamma> t\<^sub>1'_\<gamma> t\<^sub>1_\<gamma>
          unfolding term.order.less\<^sub>G_def \<gamma>
          by auto
      qed
    next

      show "\<not> t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<odot> \<mu> \<preceq>\<^sub>t t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<odot> \<mu>"
      proof(rule term.order.ground_less_not_less_eq)

        show "term.is_ground (t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<odot> \<mu> \<cdot>t \<sigma>)"
          using t\<^sub>2'_\<gamma> \<gamma>
          by simp
      next

        show "term.is_ground (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<odot> \<mu> \<cdot>t \<sigma>)"
          using t\<^sub>2_\<gamma> \<gamma>
          by simp
      next

        show "t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<odot> \<mu> \<cdot>t \<sigma> \<prec>\<^sub>t t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<odot> \<mu> \<cdot>t \<sigma>"
          using ground_superpositionI(8) t\<^sub>2_\<gamma> t\<^sub>2'_\<gamma>
          unfolding \<gamma> term.order.less\<^sub>G_def
          by simp
      qed
    next

      show "\<forall>x\<in>clause.vars (E \<cdot> \<rho>\<^sub>1). \<V>\<^sub>1 (inv \<rho>\<^sub>1 (Var x)) = \<V>\<^sub>3 x"
        unfolding \<V>\<^sub>3_def
        by auto
    next

      show "\<forall>x\<in>clause.vars (D \<cdot> \<rho>\<^sub>2). \<V>\<^sub>2 (inv \<rho>\<^sub>2 (Var x)) = \<V>\<^sub>3 x"
        unfolding \<V>\<^sub>3_def
        using rename_apart
        by auto
    next

      have "\<exists>\<tau>. welltyped \<V>\<^sub>2 t\<^sub>2 \<tau> \<and> welltyped \<V>\<^sub>2 t\<^sub>2' \<tau>"
        using D_is_welltyped
        unfolding D l\<^sub>2
        by auto

      then show "\<And>\<tau> \<tau>'. \<lbrakk>typed \<V>\<^sub>2 t\<^sub>2 \<tau>; typed \<V>\<^sub>2 t\<^sub>2' \<tau>'\<rbrakk> \<Longrightarrow> \<tau> = \<tau>'"
        using term.typed_if_welltyped
        by blast
    qed

    show C'_\<gamma>: "C' \<cdot> \<gamma> = C \<cdot> \<gamma>"
    proof-

      have "term_subst.is_idem \<mu>"
        using imgu term.is_imgu_iff_is_idem_and_is_mgu 
        by blast

      then have \<mu>_\<gamma>: "\<mu> \<odot> \<gamma> = \<gamma>"
        unfolding \<gamma> term_subst.is_idem_def
        by (metis subst_compose_assoc)

      have "C \<cdot> \<gamma> = 
              add_mset 
                (?\<P> (Upair (context.from_ground c\<^sub>G)\<langle>term.from_ground t\<^sub>G\<^sub>3\<rangle> (term.from_ground t\<^sub>G\<^sub>2)))
                  (clause.from_ground E\<^sub>G' + clause.from_ground D\<^sub>G')"
        using ground_superpositionI(4, 12) clause.to_ground_inverse[OF C_grounding] 
        by auto

      then show ?thesis
        unfolding 
          C'
          E'_\<gamma>[symmetric] 
          D'_\<gamma>[symmetric] 
          t\<^sub>1'_\<gamma>[symmetric]
          t\<^sub>2'_\<gamma>[symmetric]
          c\<^sub>1_\<gamma>[symmetric]
          clause.subst_comp_subst[symmetric]
          \<mu>_\<gamma>
        by simp
    qed

    show "\<iota>\<^sub>G \<in> inference_groundings (Infer [(D, \<V>\<^sub>2), (E, \<V>\<^sub>1)] (C', \<V>\<^sub>3))"
    proof(rule is_inference_grounding_two_premises_inference_groundings)

      show "is_inference_grounding_two_premises (D, \<V>\<^sub>2) (E, \<V>\<^sub>1) (C', \<V>\<^sub>3) \<iota>\<^sub>G \<gamma> \<rho>\<^sub>1 \<rho>\<^sub>2"
      proof(unfold split, intro conjI; 
          (rule \<rho>\<^sub>1 \<rho>\<^sub>2 rename_apart D_grounding E_grounding D_is_welltyped E_is_welltyped refl \<V>\<^sub>1 
            \<V>\<^sub>2)?)

        show "clause.is_ground (C' \<cdot> \<gamma>)"
          using C_grounding C'_\<gamma>
          by argo
      next

        show "\<iota>\<^sub>G = Infer
                    [clause.to_ground (D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>), clause.to_ground (E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)]
                    (clause.to_ground (C' \<cdot> \<gamma>))"
          using C'_\<gamma>
          by simp
      next

        show "is_welltyped_on (clause.vars C') \<V>\<^sub>3 \<gamma>"
        proof(rule is_welltyped_on_subset[OF \<gamma>_is_welltyped])

          show "clause.vars C' \<subseteq> clause.vars (E \<cdot> \<rho>\<^sub>1) \<union> clause.vars (D \<cdot> \<rho>\<^sub>2)"
          proof (unfold subset_eq, intro ballI)
            fix x

            have is_imgu: "term.is_imgu \<mu> {{t\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}}"
              using imgu
              by blast

            assume "x \<in> clause.vars C'"

            then consider
              (t\<^sub>2') "x \<in> term.vars (t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<odot> \<mu>)" |
              (c\<^sub>1) "x \<in> context.vars (c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<odot> \<mu>)" |
              (t\<^sub>1') "x \<in> term.vars (t\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<odot> \<mu>)" |
              (E') "x \<in> clause.vars (E' \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)" |  
              (D') "x \<in> clause.vars (D' \<cdot> \<rho>\<^sub>2 \<odot> \<mu>)"  
              unfolding C'
              by auto

            then show "x \<in> clause.vars (E \<cdot> \<rho>\<^sub>1) \<union> clause.vars (D \<cdot> \<rho>\<^sub>2)"
            proof cases
              case t\<^sub>2'

              then show ?thesis 
                using term.variables_in_base_imgu[OF is_imgu] 
                unfolding E l\<^sub>1 D l\<^sub>2
                by auto
            next
              case c\<^sub>1

              then show ?thesis
                using context.variables_in_base_imgu[OF is_imgu] 
                unfolding E l\<^sub>1 D l\<^sub>2
                by force
            next
              case t\<^sub>1'

              then show ?thesis
                using term.variables_in_base_imgu[OF is_imgu]
                unfolding E clause.add_subst l\<^sub>1 D l\<^sub>2
                by auto
            next
              case E'

              then show ?thesis 
                using clause.variables_in_base_imgu[OF is_imgu]
                unfolding E l\<^sub>1 D l\<^sub>2
                by auto
            next
              case D'

              then show ?thesis 
                using clause.variables_in_base_imgu[OF is_imgu]
                unfolding E l\<^sub>1 D l\<^sub>2
                by auto
            qed
          qed
        qed
      next

        show "clause.is_welltyped \<V>\<^sub>3 C'"
          using superposition superposition_preserves_typing E_is_welltyped D_is_welltyped
          by blast
      next

        have "finite {x. x \<in> clause.vars (E \<cdot> \<rho>\<^sub>1)}"
          using clause.finite_vars
          by simp

        moreover {
          fix \<tau>

          have "infinite {x. \<V>\<^sub>2 (inv \<rho>\<^sub>2 (Var x)) = \<tau>}" 
          proof(rule surj_infinite_set[OF term.surj_inv_renaming, OF \<rho>\<^sub>2])

            show "infinite {x. \<V>\<^sub>2 x = \<tau>}"
              using \<V>\<^sub>2
              unfolding infinite_variables_per_type_def
              by blast
          qed
        }

        ultimately show "infinite_variables_per_type \<V>\<^sub>3"
          unfolding infinite_variables_per_type_def \<V>\<^sub>3_def if_distrib if_distribR Collect_if_eq 
            Collect_not_mem_conj_eq
          by auto
      qed
          
      show "\<iota>\<^sub>G \<in> ground.G_Inf"
        unfolding ground.G_Inf_def
        using ground_superposition
        by simp
    qed
  qed
qed

subsection \<open>Ground instances\<close>

context
  fixes \<iota>\<^sub>G N
  assumes 
    subst_stability: "subst_stability_on N" and
    \<iota>\<^sub>G_Inf_from: "\<iota>\<^sub>G \<in> ground.Inf_from_q select\<^sub>G (\<Union>(clause_groundings ` N))" 
begin

lemma single_premise_ground_instance:
  assumes 
    ground_inference: "\<iota>\<^sub>G \<in>  {Infer [D] C | D C. ground_inference D C}" and
    lifting: "\<And>D \<gamma> C \<V> thesis. \<lbrakk>
    ground_inference (clause.to_ground (D \<cdot> \<gamma>)) (clause.to_ground (C \<cdot> \<gamma>)); 
    clause.is_ground (D \<cdot> \<gamma>); 
    clause.is_ground (C \<cdot> \<gamma>);
    clause.from_ground (select\<^sub>G (clause.to_ground (D \<cdot> \<gamma>))) = select D \<cdot> \<gamma>; 
    clause.is_welltyped \<V> D; is_welltyped_on (clause.vars D) \<V> \<gamma>;
    infinite_variables_per_type \<V>;
    \<And>C'. \<lbrakk>
        inference (D, \<V>) (C', \<V>);
        Infer [clause.to_ground (D \<cdot> \<gamma>)] (clause.to_ground (C \<cdot> \<gamma>))
        \<in> inference_groundings (Infer [(D, \<V>)] (C', \<V>));
        C' \<cdot> \<gamma> = C \<cdot> \<gamma>\<rbrakk> \<Longrightarrow> thesis\<rbrakk>
       \<Longrightarrow> thesis" and
    inference_eq: "inference = eq_factoring \<or> inference = eq_resolution"
  obtains \<iota> where 
    "\<iota> \<in> Inf_from N" 
    "\<iota>\<^sub>G \<in> inference_groundings \<iota>"
proof-
  obtain D\<^sub>G C\<^sub>G where 
    \<iota>\<^sub>G: "\<iota>\<^sub>G = Infer [D\<^sub>G] C\<^sub>G" and
    ground_inference: "ground_inference D\<^sub>G C\<^sub>G"
    using ground_inference
    by blast

  have D\<^sub>G_in_groundings: "D\<^sub>G \<in> \<Union>(clause_groundings ` N)"
    using \<iota>\<^sub>G_Inf_from
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
    by simp

  obtain D \<gamma> \<V> where
    D_grounding: "clause.is_ground (D \<cdot> \<gamma>)" and
    D_is_welltyped: "clause.is_welltyped \<V> D" and
    \<gamma>_is_welltyped: "is_welltyped_on (clause.vars D) \<V> \<gamma>" and
    \<V>: "infinite_variables_per_type \<V>" and
    D_in_N: "(D, \<V>)\<in>N" and 
    "select\<^sub>G D\<^sub>G = clause.to_ground (select D \<cdot> \<gamma>)"
    "D \<cdot> \<gamma> = clause.from_ground D\<^sub>G"
    using subst_stability[rule_format, OF D\<^sub>G_in_groundings]
    by blast

  then have 
    D\<^sub>G: "D\<^sub>G = clause.to_ground (D \<cdot> \<gamma>)" and
    select: "clause.from_ground (select\<^sub>G D\<^sub>G) = select D \<cdot> \<gamma>"
    by (simp_all add: select_ground_subst)

  obtain C where 
    C\<^sub>G: "C\<^sub>G = clause.to_ground (C \<cdot> \<gamma>)" and 
    C_grounding: "clause.is_ground (C \<cdot> \<gamma>)"
    by (metis clause.all_subst_ident_iff_ground clause.from_ground_inverse 
        clause.ground_is_ground)

  obtain C' where 
    inference: "inference (D, \<V>) (C', \<V>)" and
    inference_groundings: "\<iota>\<^sub>G \<in> inference_groundings (Infer [(D, \<V>)] (C', \<V>))" and  
    C'_C: "C' \<cdot> \<gamma> = C \<cdot> \<gamma>"
    using
      lifting[OF 
        ground_inference[unfolded D\<^sub>G C\<^sub>G]
        D_grounding
        C_grounding
        select[unfolded D\<^sub>G]
        D_is_welltyped
        \<gamma>_is_welltyped
        \<V>]
    unfolding D\<^sub>G C\<^sub>G \<iota>\<^sub>G.

  let ?\<iota> = "Infer [(D, \<V>)] (C', \<V>)"

  show ?thesis
  proof(rule that[OF _ inference_groundings])

    show "?\<iota> \<in> Inf_from N"
      using D_in_N inference inference_eq
      unfolding Inf_from_def inferences_def inference_system.Inf_from_def
      by auto
  qed
qed

lemma eq_resolution_ground_instance: 
  assumes ground_eq_resolution: "\<iota>\<^sub>G \<in> ground.eq_resolution_inferences" 
  obtains \<iota> where             
    "\<iota> \<in> Inf_from N" 
    "\<iota>\<^sub>G \<in> inference_groundings \<iota>"
  using eq_resolution_lifting single_premise_ground_instance[OF ground_eq_resolution]
  by blast
  
lemma eq_factoring_ground_instance: 
  assumes ground_eq_factoring: "\<iota>\<^sub>G \<in> ground.eq_factoring_inferences" 
  obtains \<iota> where 
    "\<iota> \<in> Inf_from N" 
    "\<iota>\<^sub>G \<in> inference_groundings \<iota>"
  using eq_factoring_lifting single_premise_ground_instance[OF ground_eq_factoring]
  by blast

lemma superposition_ground_instance: 
  assumes 
    ground_superposition: "\<iota>\<^sub>G \<in> ground.superposition_inferences" and
    not_redundant: "\<iota>\<^sub>G \<notin> ground.GRed_I (\<Union> (clause_groundings ` N))"
  obtains \<iota> where 
    "\<iota> \<in> Inf_from N" 
    "\<iota>\<^sub>G \<in> inference_groundings \<iota>"
proof-
  obtain E\<^sub>G D\<^sub>G C\<^sub>G where 
    \<iota>\<^sub>G : "\<iota>\<^sub>G = Infer [D\<^sub>G, E\<^sub>G] C\<^sub>G" and
    ground_superposition: "ground.superposition D\<^sub>G E\<^sub>G C\<^sub>G"
    using assms(1)
    by blast

  have 
    E\<^sub>G_in_groundings: "E\<^sub>G \<in> \<Union> (clause_groundings ` N)" and  
    D\<^sub>G_in_groundings: "D\<^sub>G \<in> \<Union> (clause_groundings ` N)"
    using \<iota>\<^sub>G_Inf_from
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
    by simp_all

  obtain E \<V>\<^sub>1 \<gamma>\<^sub>1 where
    E_grounding: "clause.is_ground (E \<cdot> \<gamma>\<^sub>1)" and
    E_is_welltyped: "clause.is_welltyped \<V>\<^sub>1 E" and
    \<gamma>\<^sub>1_is_welltyped: "is_welltyped_on (clause.vars E) \<V>\<^sub>1 \<gamma>\<^sub>1" and
    \<V>\<^sub>1: "infinite_variables_per_type \<V>\<^sub>1" and
    E_in_N: "(E, \<V>\<^sub>1)\<in>N" and 
    "select\<^sub>G E\<^sub>G = clause.to_ground (select E \<cdot> \<gamma>\<^sub>1)"
    "E \<cdot> \<gamma>\<^sub>1 = clause.from_ground E\<^sub>G"
    using subst_stability[rule_format, OF E\<^sub>G_in_groundings]
    by blast

  then have 
    E\<^sub>G: "E\<^sub>G = clause.to_ground (E \<cdot> \<gamma>\<^sub>1)" and
    select_from_E: "clause.from_ground (select\<^sub>G E\<^sub>G) = select E \<cdot> \<gamma>\<^sub>1"
    by (simp_all add: select_ground_subst)

  obtain D \<V>\<^sub>2 \<gamma>\<^sub>2 where
    D_grounding: "clause.is_ground (D \<cdot> \<gamma>\<^sub>2)" and
    D_is_welltyped: "clause.is_welltyped \<V>\<^sub>2 D" and
    \<gamma>\<^sub>2_is_welltyped: "is_welltyped_on (clause.vars D) \<V>\<^sub>2 \<gamma>\<^sub>2" and
    \<V>\<^sub>2: "infinite_variables_per_type \<V>\<^sub>2" and
    D_in_N: "(D, \<V>\<^sub>2)\<in>N" and 
    "select\<^sub>G D\<^sub>G = clause.to_ground (select D \<cdot> \<gamma>\<^sub>2)"
    "D \<cdot> \<gamma>\<^sub>2 = clause.from_ground D\<^sub>G"
    using subst_stability[rule_format, OF D\<^sub>G_in_groundings] 
    by blast

  then have 
    D\<^sub>G: "D\<^sub>G = clause.to_ground (D \<cdot> \<gamma>\<^sub>2)" and
    select_from_D: "clause.from_ground (select\<^sub>G D\<^sub>G) = select D \<cdot> \<gamma>\<^sub>2"
    by (simp_all add: select_ground_subst)

  obtain \<rho>\<^sub>1 \<rho>\<^sub>2 :: "('f, 'v) subst" where
    \<rho>\<^sub>1: "term_subst.is_renaming \<rho>\<^sub>1" and
    \<rho>\<^sub>2: "term_subst.is_renaming \<rho>\<^sub>2" and
    rename_apart: "\<rho>\<^sub>1 ` (clause.vars E) \<inter> \<rho>\<^sub>2 ` (clause.vars D) = {}" and
    \<rho>\<^sub>1_is_welltyped: "is_welltyped_on (clause.vars E) \<V>\<^sub>1 \<rho>\<^sub>1" and
    \<rho>\<^sub>2_is_welltyped: "is_welltyped_on (clause.vars D) \<V>\<^sub>2 \<rho>\<^sub>2"
    using welltyped.obtain_typed_renamings[OF infinite_UNIV] 
    by (smt (verit, del_insts) \<V>\<^sub>1 \<V>\<^sub>2 clause.finite_vars infinite_variables_per_type_def)

  have rename_apart: "clause.vars (E \<cdot> \<rho>\<^sub>1) \<inter> clause.vars (D \<cdot> \<rho>\<^sub>2) = {}"
    using rename_apart clause.renaming_variables[OF \<rho>\<^sub>1] clause.renaming_variables[OF \<rho>\<^sub>2]
    by blast

  from \<rho>\<^sub>1 \<rho>\<^sub>2 obtain \<rho>\<^sub>1_inv \<rho>\<^sub>2_inv where
    \<rho>\<^sub>1_inv: "\<rho>\<^sub>1 \<odot> \<rho>\<^sub>1_inv = Var" and
    \<rho>\<^sub>2_inv: "\<rho>\<^sub>2 \<odot> \<rho>\<^sub>2_inv = Var"
    unfolding term_subst.is_renaming_def
    by blast

  define \<gamma> where 
     "\<And>x. \<gamma> x \<equiv>
       if x \<in> clause.vars (E \<cdot> \<rho>\<^sub>1)
       then (\<rho>\<^sub>1_inv \<odot> \<gamma>\<^sub>1) x
       else (\<rho>\<^sub>2_inv \<odot> \<gamma>\<^sub>2) x"

  have E_grounding: "clause.is_ground (E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)"
    using clause.subst_inv[OF \<rho>\<^sub>1_inv] E_grounding 
    unfolding \<gamma>_def
    by auto

  have E\<^sub>G: "E\<^sub>G = clause.to_ground (E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)"
    using clause.subst_inv[OF \<rho>\<^sub>1_inv] E\<^sub>G 
    unfolding \<gamma>_def
    by auto

  have D_grounding: "clause.is_ground (D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>)"
    using clause.subst_inv[OF \<rho>\<^sub>2_inv] D_grounding rename_apart
    unfolding \<gamma>_def
    by (simp add: inf.commute)

  have D\<^sub>G: "D\<^sub>G = clause.to_ground (D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>)"
    using clause.subst_inv[OF \<rho>\<^sub>2_inv] D\<^sub>G rename_apart
    unfolding \<gamma>_def
    by (simp add: inf.commute)

  have \<rho>\<^sub>1_\<gamma>_is_welltyped: "is_welltyped_on (clause.vars E) \<V>\<^sub>1 (\<rho>\<^sub>1 \<odot> \<gamma>)"
  proof-

    have "\<forall>x\<in>clause.vars E. (\<rho>\<^sub>1 \<odot> \<gamma>) x = \<gamma>\<^sub>1 x"
    proof(intro ballI)
      fix x
      assume x_in_vars: "x \<in> clause.vars E"

      obtain y where y: "\<rho>\<^sub>1 x = Var y"
        by (meson is_Var_def \<rho>\<^sub>1 term_subst_is_renaming_iff)

      then have "y \<in> clause.vars (E \<cdot> \<rho>\<^sub>1)"
        using x_in_vars \<rho>\<^sub>1 clause.renaming_variables 
        by fastforce

      then have "\<gamma> y = \<rho>\<^sub>1_inv y \<cdot>t \<gamma>\<^sub>1"
        by (simp add: \<gamma>_def subst_compose)

      then show "(\<rho>\<^sub>1 \<odot> \<gamma>) x = \<gamma>\<^sub>1 x"
        by (metis y \<rho>\<^sub>1_inv eval_term.simps(1) subst_compose)
    qed

    then show ?thesis
      using \<gamma>\<^sub>1_is_welltyped
      by auto
  qed

  have \<rho>\<^sub>2_\<gamma>_is_welltyped: "is_welltyped_on (clause.vars D) \<V>\<^sub>2 (\<rho>\<^sub>2 \<odot> \<gamma>)"
  proof -

    have "\<forall>x\<in> clause.vars D. (\<rho>\<^sub>2 \<odot> \<gamma>) x = \<gamma>\<^sub>2 x"
    proof(intro ballI)
      fix x
      assume x_in_vars: "x \<in> clause.vars D"

      obtain y where y: "\<rho>\<^sub>2 x = Var y"
        by (meson is_Var_def \<rho>\<^sub>2 term_subst_is_renaming_iff)

      then have "y \<in> clause.vars (D \<cdot> \<rho>\<^sub>2)"
        using x_in_vars \<rho>\<^sub>2 clause.renaming_variables 
        by fastforce

      then have "\<gamma> y = \<rho>\<^sub>2_inv y \<cdot>t \<gamma>\<^sub>2"
        using \<gamma>_def rename_apart subst_compose 
        by fastforce

      then show "(\<rho>\<^sub>2 \<odot> \<gamma>) x = \<gamma>\<^sub>2 x"
        by (metis y \<rho>\<^sub>2_inv eval_term.simps(1) subst_compose)
    qed

    then show ?thesis
      using \<gamma>\<^sub>2_is_welltyped
      by auto
  qed

  have select_from_E:
    "clause.from_ground (select\<^sub>G (clause.to_ground (E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>))) = select E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>"
  proof-
    have "E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma> = E \<cdot> \<gamma>\<^sub>1"
      using clause.subst_inv[OF \<rho>\<^sub>1_inv]
      unfolding \<gamma>_def
      by auto

    moreover have "select E \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma> = select E \<cdot> \<gamma>\<^sub>1"
    proof-
      have "select E \<cdot> \<rho>\<^sub>1 \<subseteq># E \<cdot> \<rho>\<^sub>1" 
        by (simp add: clause.subst_def image_mset_subseteq_mono select_subset)

      then have "clause.vars (select E \<cdot> \<rho>\<^sub>1) \<subseteq> clause.vars (E \<cdot> \<rho>\<^sub>1)"
        using clause_submset_vars_clause_subset
        by fast

      then show ?thesis
        unfolding \<gamma>_def
        by (simp add: \<rho>\<^sub>1_inv clause.subst_inv)
    qed

    ultimately show ?thesis
      using select_from_E
      unfolding E\<^sub>G
      by simp
  qed

  have select_from_D:
    "clause.from_ground (select\<^sub>G (clause.to_ground (D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>))) = select D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>"
  proof-   
    have "D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma> = D \<cdot> \<gamma>\<^sub>2"
      using clause.subst_inv[OF \<rho>\<^sub>2_inv] rename_apart
      unfolding \<gamma>_def
      by (simp add: inf.commute)

    moreover have "select D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma> = select D \<cdot> \<gamma>\<^sub>2"
    proof-
      have "select D \<cdot> \<rho>\<^sub>2 \<subseteq># D \<cdot> \<rho>\<^sub>2" 
        by (simp add: clause.subst_def image_mset_subseteq_mono select_subset)

      then have "clause.vars (select D \<cdot> \<rho>\<^sub>2) \<subseteq> clause.vars (D \<cdot> \<rho>\<^sub>2)"
        using clause_submset_vars_clause_subset
        by fast

      then have "clause.vars (E \<cdot> \<rho>\<^sub>1) \<inter> clause.vars (select D \<cdot> \<rho>\<^sub>2) = {}"
        using rename_apart
        by blast
    
      then show ?thesis
        using clause.subst_inv[OF \<rho>\<^sub>2_inv]
        unfolding \<gamma>_def
        by (simp add: inf.commute)
    qed

    ultimately show ?thesis
      using select_from_D
      unfolding D\<^sub>G
      by simp
  qed

  obtain C where
    C_grounding: "clause.is_ground (C \<cdot> \<gamma>)" and
    C\<^sub>G: "C\<^sub>G = clause.to_ground (C \<cdot> \<gamma>)"
    by (metis clause.all_subst_ident_if_ground clause.from_ground_inverse clause.ground_is_ground)

  have "clause_groundings (E, \<V>\<^sub>1) \<union> clause_groundings (D, \<V>\<^sub>2) \<subseteq> \<Union> (clause_groundings ` N)"
    using E_in_N D_in_N 
    by blast

  then have \<iota>\<^sub>G_not_redundant:
    "\<iota>\<^sub>G \<notin> ground.GRed_I (clause_groundings (E, \<V>\<^sub>1) \<union> clause_groundings (D, \<V>\<^sub>2))"
    using not_redundant ground.Red_I_of_subset
    by blast

  obtain C' \<V>\<^sub>3 where 
    superposition: "superposition (D, \<V>\<^sub>2) (E, \<V>\<^sub>1) (C', \<V>\<^sub>3)" and
    inference_groundings: "\<iota>\<^sub>G \<in> inference_groundings (Infer [(D, \<V>\<^sub>2), (E, \<V>\<^sub>1)] (C', \<V>\<^sub>3))" and  
    C'_\<gamma>_C_\<gamma>: "C' \<cdot> \<gamma> = C \<cdot> \<gamma>"
    using 
      superposition_lifting[OF 
        ground_superposition[unfolded D\<^sub>G E\<^sub>G C\<^sub>G]
        \<rho>\<^sub>1 \<rho>\<^sub>2
        rename_apart
        E_grounding D_grounding C_grounding
        select_from_E select_from_D
        E_is_welltyped D_is_welltyped
        \<rho>\<^sub>1_\<gamma>_is_welltyped \<rho>\<^sub>2_\<gamma>_is_welltyped
        \<rho>\<^sub>1_is_welltyped \<rho>\<^sub>2_is_welltyped
        \<V>\<^sub>1 \<V>\<^sub>2
        \<iota>\<^sub>G_not_redundant[unfolded \<iota>\<^sub>G D\<^sub>G E\<^sub>G C\<^sub>G]
        ]
    unfolding \<iota>\<^sub>G C\<^sub>G E\<^sub>G D\<^sub>G .

  let ?\<iota> = "Infer [(D, \<V>\<^sub>2), (E, \<V>\<^sub>1)] (C', \<V>\<^sub>3)"

  show ?thesis
  proof(rule that[OF _ inference_groundings])

    show "?\<iota> \<in> Inf_from N"
      using E_in_N D_in_N superposition
      unfolding Inf_from_def inferences_def inference_system.Inf_from_def
      by auto
  qed
qed

lemma ground_instances: 
  assumes not_redundant: "\<iota>\<^sub>G \<notin> ground.Red_I (\<Union> (clause_groundings ` N))"
  obtains \<iota> where 
    "\<iota> \<in> Inf_from N" 
    "\<iota>\<^sub>G \<in> inference_groundings \<iota>"
proof-
  consider 
    (superposition) "\<iota>\<^sub>G \<in> ground.superposition_inferences" |
    (eq_resolution) "\<iota>\<^sub>G \<in> ground.eq_resolution_inferences" |
    (eq_factoring) "\<iota>\<^sub>G \<in> ground.eq_factoring_inferences"
    using \<iota>\<^sub>G_Inf_from
    unfolding
      ground.Inf_from_q_def 
      ground.G_Inf_def
      inference_system.Inf_from_def
    by fastforce

  then show ?thesis
  proof cases
    case superposition

    then show ?thesis
      using that superposition_ground_instance not_redundant
      by blast
  next
    case eq_resolution

    then show ?thesis
      using that eq_resolution_ground_instance
      by blast
  next
    case eq_factoring

    then show ?thesis
      using that eq_factoring_ground_instance
      by blast
  qed
qed

end

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

  show thesis
  proof(rule that[OF _ select\<^sub>G])

    show "ground_Inf_overapproximated select\<^sub>G premises"
      using ground_instances[OF subst_stability]
      by auto
  qed
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

  show "\<And>N. \<exists>select\<^sub>G \<in> select\<^sub>G\<^sub>s. ground_Inf_overapproximated select\<^sub>G N" 
    using overapproximation
    unfolding select\<^sub>G\<^sub>s_def
    by (smt (verit, best) mem_Collect_eq)
qed

end

end
