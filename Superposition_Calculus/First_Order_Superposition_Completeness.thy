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
    qed simp

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
          unfolding D\<^sub>G ground_eq_resolutionI(2) l_\<gamma> ground_eq_resolutionI(4)[symmetric]
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
    proof-

      have "is_inference_grounding_one_premise (D, \<V>) (C' \<cdot> \<mu>, \<V>) (Infer [D\<^sub>G] C\<^sub>G) \<gamma>"
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

      moreover have "Infer [D\<^sub>G] C\<^sub>G \<in> ground.G_Inf"
        unfolding ground.G_Inf_def
        using ground_eq_resolution
        by blast

      ultimately show ?thesis
        unfolding inference_groundings_def
        by auto
    qed
  qed
qed

(* TODO: *)
lemma move_simp: "{x. if b x then P x else Q x } = 
        {x. b x \<and> P x } \<union> {x. \<not>b x \<and> Q x}"
  by auto

lemma zz: "{x. x \<notin> X \<and> P x} = {x. P x} - {x. x \<in> X}"
  by auto

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
        unfolding C\<^sub>G
        by (metis clause.from_ground_inverse)

      also have "... = ?C'' \<cdot> \<gamma>"
        using t\<^sub>1_\<gamma> t\<^sub>1'_\<gamma> t\<^sub>2'_\<gamma> D'_\<gamma>
        by simp

      also have "... = ?C' \<cdot> \<gamma>"
        unfolding clause.subst_comp_subst[symmetric] \<mu>_\<gamma> ..

      finally show ?thesis ..
    qed

    show "Infer [D\<^sub>G] C\<^sub>G \<in> inference_groundings (Infer [(D, \<V>)] (?C', \<V>))"
    proof-
      have "is_inference_grounding_one_premise (D, \<V>) (?C', \<V>) (Infer [D\<^sub>G] C\<^sub>G) \<gamma>"
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

      moreover have "Infer [D\<^sub>G] C\<^sub>G \<in> ground.G_Inf"
        unfolding ground.G_Inf_def
        using ground_eq_factoring
        by blast

      ultimately show ?thesis
        unfolding inference_groundings_def
        by auto
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
    E\<^sub>G [simp]: "E\<^sub>G \<equiv> clause.to_ground (E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)" and
    D\<^sub>G [simp]: "D\<^sub>G \<equiv> clause.to_ground (D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>)" and
    C\<^sub>G [simp]: "C\<^sub>G \<equiv> clause.to_ground (C \<cdot> \<gamma>)" and
    N\<^sub>G [simp]: "N\<^sub>G \<equiv> clause_groundings (E, \<V>\<^sub>1) \<union> clause_groundings (D, \<V>\<^sub>2)" and
    \<iota>\<^sub>G [simp]: "\<iota>\<^sub>G \<equiv> Infer [D\<^sub>G, E\<^sub>G] C\<^sub>G"
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
    non_redundant: "\<iota>\<^sub>G \<notin> ground.Red_I N\<^sub>G"
  obtains C' \<V>\<^sub>3
  where
    "superposition (D, \<V>\<^sub>2) (E, \<V>\<^sub>1) (C', \<V>\<^sub>3)"
    "\<iota>\<^sub>G \<in> inference_groundings (Infer [(D, \<V>\<^sub>2), (E, \<V>\<^sub>1)] (C', \<V>\<^sub>3))"
    "C' \<cdot> \<gamma> = C \<cdot> \<gamma>"
  using ground_superposition
proof(cases D\<^sub>G E\<^sub>G C\<^sub>G rule: ground.superposition.cases)
  case ground_superpositionI: (superpositionI l\<^sub>G\<^sub>1 E\<^sub>G' l\<^sub>G\<^sub>2 D\<^sub>G' \<P>\<^sub>G c\<^sub>G t\<^sub>G\<^sub>1 t\<^sub>G\<^sub>2 t\<^sub>G\<^sub>3)

  have E_\<gamma>: "E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma> = clause.from_ground (add_mset l\<^sub>G\<^sub>1 E\<^sub>G')"
    using ground_superpositionI(1) E\<^sub>G
    by (metis E_grounding clause.to_ground_inverse)

  have D_\<gamma>: "D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma> = clause.from_ground (add_mset l\<^sub>G\<^sub>2 D\<^sub>G')"
    using ground_superpositionI(2) D\<^sub>G
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
      unfolding E\<^sub>G
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
        unfolding \<iota>\<^sub>G
        by simp_all

      show ?thesis
      proof(unfold ground.redundant_infer_def \<iota>\<^sub>G_parts, intro exI conjI)

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
         
        show "{?E\<^sub>G'} \<subseteq> N\<^sub>G"
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
                      D\<^sub>G
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

        show "finite {?E\<^sub>G'}"
          by simp
     
        show "ground.G_entails ({?E\<^sub>G'} \<union> {D\<^sub>G}) {C\<^sub>G}"
        proof(unfold ground.G_entails_def, intro allI impI)
          fix I :: "'f gterm rel"
          let ?I = "upair ` I"

          assume 
            refl_I: "refl I" and 
            trans_I: "trans I" and 
            sym_I: "sym I" and
            compatible_with_gctxt_I: "compatible_with_gctxt I" and
            premise: "?I \<TTurnstile>s {?E\<^sub>G'} \<union> {D\<^sub>G}"

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
              unfolding \<gamma>'_def E\<^sub>G
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

        show "\<forall>E\<^sub>G' \<in> {?E\<^sub>G'}. E\<^sub>G' \<prec>\<^sub>c\<^sub>G E\<^sub>G"
        proof-

          have "\<gamma> x = t\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<odot> \<gamma>"
            using t\<^sub>1_\<rho>\<^sub>1
            by simp

          then have t\<^sub>G_smaller: "?t\<^sub>G \<prec>\<^sub>t \<gamma> x"
            using ground_superpositionI(8)
            unfolding t\<^sub>1_\<gamma> term.order.less\<^sub>G_def
            by simp

          have "?E\<^sub>G' \<prec>\<^sub>c\<^sub>G E\<^sub>G"
          proof -

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
              unfolding clause.order.less\<^sub>G_def E\<^sub>G
              by simp
          qed

          then show ?thesis
            by blast
        qed   
      qed

    qed

    then show ?thesis
      using non_redundant ground_superposition that l\<^sub>1 t\<^sub>1'_\<gamma> c\<^sub>1_t\<^sub>1_\<gamma> 
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
      using clause.is_welltyped.is_typed_on_renaming_grounding[OF \<rho>\<^sub>1 \<rho>\<^sub>1_\<gamma>_is_welltyped E_grounding]
      by simp

  next
    have "\<forall>x\<in>clause.vars (D \<cdot> \<rho>\<^sub>2). \<V>\<^sub>3 x = \<V>\<^sub>2 (inv \<rho>\<^sub>2 (Var x))"
      unfolding \<V>\<^sub>3_def
      using rename_apart
      by auto

    then show "is_welltyped_on (clause.vars (D \<cdot> \<rho>\<^sub>2)) \<V>\<^sub>3 \<gamma>"
      unfolding \<V>\<^sub>3_def
      using clause.is_welltyped.is_typed_on_renaming_grounding[OF \<rho>\<^sub>2 \<rho>\<^sub>2_\<gamma>_is_welltyped D_grounding]
      by simp
  qed

  obtain \<mu> \<sigma> where \<mu>: 
    "term_subst.is_imgu \<mu> {{t\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}}" 
    "\<gamma> = \<mu> \<odot> \<sigma>" 
    "welltyped_imgu \<V>\<^sub>3 (t\<^sub>1 \<cdot>t \<rho>\<^sub>1) (t\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<mu>"
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

      then have 
        "welltyped \<V>\<^sub>3 (term.from_ground t\<^sub>G\<^sub>1) \<tau>" 
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

  have (* TODO: Separate *)
    c\<^sub>1_t\<^sub>2'_\<gamma>: "(c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> \<cdot>t \<gamma> = (context.from_ground c\<^sub>G)\<langle>term.from_ground t\<^sub>G\<^sub>3\<rangle>"
    unfolding t\<^sub>2'_\<gamma>[symmetric] c\<^sub>1_\<gamma>[symmetric]
    by force

  

  

 

  define C' where 
    C': "C' \<equiv>
      add_mset (?\<P> (Upair (c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> (t\<^sub>1' \<cdot>t \<rho>\<^sub>1))) (E' \<cdot> \<rho>\<^sub>1 + D' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu>"

  show ?thesis
  proof(rule that)
    show "superposition (D, \<V>\<^sub>2) (E, \<V>\<^sub>1) (C', \<V>\<^sub>3)"
    proof(rule superpositionI)
      show "term_subst.is_renaming \<rho>\<^sub>1"
        using \<rho>\<^sub>1.
    next
      show "term_subst.is_renaming \<rho>\<^sub>2"
        using \<rho>\<^sub>2.
    next 
      show "E = add_mset l\<^sub>1 E'"
        using E.
    next
      show "D = add_mset l\<^sub>2 D'"
        using D.
    next
      show "?\<P> \<in> {Pos, Neg}"
        by simp
    next
      show "l\<^sub>1 = ?\<P> (Upair c\<^sub>1\<langle>t\<^sub>1\<rangle> t\<^sub>1')"
        unfolding l\<^sub>1 ..
    next
      show "l\<^sub>2 = t\<^sub>2 \<approx> t\<^sub>2'"
        using l\<^sub>2.
    next
      show "is_Fun t\<^sub>1"
        using t\<^sub>1_is_Fun.
    next
      show "term_subst.is_imgu \<mu> {{t\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}}"
        using \<mu>(1).
    next
      note premises_clause_to_ground_inverse = assms(10, 11)[THEN clause.to_ground_inverse]  
      note N\<^sub>G = assms(11, 10)[unfolded \<mu>(2) clause.subst_comp_subst]

      have "D \<cdot> \<rho>\<^sub>2 \<cdot> \<mu> \<cdot> \<sigma> \<prec>\<^sub>c E \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<cdot> \<sigma>"
        using ground_superpositionI(3) 
        unfolding E\<^sub>G D\<^sub>G clause.order.less\<^sub>G_def premises_clause_to_ground_inverse 
        unfolding \<mu>(2) clause.subst_comp_subst 
        by blast

      then show "\<not> E \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<preceq>\<^sub>c D \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>"
        using clause.order.ground_less_not_less_eq[OF N\<^sub>G]
        by blast
    next
      show "?\<P> = Pos 
              \<and> select E = {#} 
              \<and> is_strictly_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (E \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>) 
          \<or> ?\<P> = Neg 
              \<and> (select E = {#} \<and> is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (E \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>) 
                 \<or> is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) ((select E) \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>))"
      proof(cases "?\<P> = Pos")
        case True
        moreover then have select_empty: "select E = {#}"
          using clause_subst_empty(2) select_from_E ground_superpositionI(9) 
          by (metis clause_from_ground_empty_mset literals_distinct(1))

        moreover have "is_strictly_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu> \<cdot>l \<sigma>) (E \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<cdot> \<sigma>)"
          using True l\<^sub>1_\<gamma> \<mu>(2)
          by (smt (verit, ccfv_SIG) E_\<gamma> clause.subst_comp_subst clause_safe_unfolds(4,6) ground_superpositionI(1,5,9)
              literal.comp_subst.left.monoid_action_compatibility literals_distinct
              nonground_context.term_from_ground_context_from_ground)

        moreover then have "is_strictly_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (E \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>)"
          using 
            is_strictly_maximal_if_grounding_is_strictly_maximal[OF
              _
              E_grounding[unfolded \<mu>(2)]
              ]
            clause.subst_in_to_set_subst
            l\<^sub>1_in_E
          by (metis (no_types, lifting) \<mu>(2) assms(10) clause.subst_comp_subst
              is_strictly_maximal_if_grounding_is_strictly_maximal)

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

          then have "select E = {#}"
            using clause_subst_empty select_from_E ground_superpositionI(9) \<P>\<^sub>G_Neg
            by simp

          moreover have "is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu> \<cdot>l \<sigma>) (E \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<cdot> \<sigma>)"
            using l\<^sub>1_\<gamma> \<mu>(2)
            using E_\<gamma> ground_superpositionI(5,9) is_maximal_empty select\<^sub>G_empty by auto

          moreover then have "is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (E \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>)"
            using 
              is_maximal_if_grounding_is_maximal[OF 
                _  
                E_grounding[unfolded \<mu>(2)]
                ]
              clause.subst_in_to_set_subst
              l\<^sub>1_in_E
            by (metis (no_types, lifting) \<mu>(2) assms(10) clause.subst_comp_subst is_maximal_if_grounding_is_maximal)

          ultimately show ?thesis
            using \<P>\<^sub>G_Neg
            by auto
        next
          case select\<^sub>G_not_empty: False

          have selected_grounding: "clause.is_ground (select E \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<cdot> \<sigma>)"
            using select_ground_subst[OF E_grounding] select_from_E
            unfolding \<mu>(2) clause.subst_comp_subst
            by (metis clause.ground_is_ground)

          note selected_subst =
            l\<^sub>1_selected[
              OF \<P>\<^sub>G_Neg select\<^sub>G_not_empty, 
              THEN maximal_in_clause, 
              THEN clause.subst_in_to_set_subst] 

          have "is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<gamma>) (select E \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>)"  
            using select\<^sub>G_not_empty ground_superpositionI(9) \<P>\<^sub>G_Neg 
            using l\<^sub>1_\<gamma> select_from_E
            using E\<^sub>G \<open>(\<P>\<^sub>G \<noteq> Pos) = (\<P>\<^sub>G = Neg)\<close> ground_superpositionI(5) 
            by fastforce

          then have "is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) ((select E) \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>)"
            using is_maximal_if_grounding_is_maximal[OF _ selected_grounding] selected_subst
            by (metis \<mu>(2) clause.subst_comp_subst literal.subst_comp_subst)

          with select\<^sub>G_not_empty \<P>\<^sub>G_Neg show ?thesis
            by auto
        qed
      qed
    next
      show "select D = {#}"
        using ground_superpositionI(10) select_from_D
        by simp
    next 
      have "is_strictly_maximal (l\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu> \<cdot>l \<sigma>) (D \<cdot> \<rho>\<^sub>2 \<cdot> \<mu> \<cdot> \<sigma>)"
        using l\<^sub>2_\<gamma> \<mu>(2)
        using D_\<gamma> ground_superpositionI(11,6) by auto

      then show "is_strictly_maximal (l\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu>) (D \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>)"
        using 
          is_strictly_maximal_if_grounding_is_strictly_maximal[OF 
            _  D_grounding[unfolded \<mu>(2) clause.subst_comp_subst]]
          l\<^sub>2_in_D
          clause.subst_in_to_set_subst
        by blast
    next
      have term_groundings: 
        "term.is_ground (t\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<sigma>)" 
        "term.is_ground (c\<^sub>1\<langle>t\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<sigma>)" 
        using t\<^sub>1'_\<gamma> \<mu>(2) t\<^sub>1_\<gamma> c\<^sub>1_\<gamma>
        by simp_all

      have "t\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<sigma> \<prec>\<^sub>t c\<^sub>1\<langle>t\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<sigma>"
        using ground_superpositionI(7) c\<^sub>1_\<gamma>[unfolded \<mu>(2)]
        unfolding 
          t\<^sub>1'_\<gamma>[unfolded \<mu>(2) term_subst.subst_comp_subst]
          t\<^sub>1_\<gamma>[unfolded \<mu>(2) term_subst.subst_comp_subst]
          term.order.less\<^sub>G_def
          context.safe_unfolds
        by simp

      then show "\<not> c\<^sub>1\<langle>t\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t t\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu>"
        using term.order.ground_less_not_less_eq[OF term_groundings]
        by blast
    next
      have term_groundings: 
        "term.is_ground (t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<sigma>)"
        "term.is_ground (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<sigma>)"
        unfolding
          t\<^sub>2_\<gamma>[unfolded \<mu>(2) term_subst.subst_comp_subst]
          t\<^sub>2'_\<gamma>[unfolded \<mu>(2) term_subst.subst_comp_subst]
        by simp_all

      have "t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<sigma> \<prec>\<^sub>t t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<sigma>"
        using ground_superpositionI(8)
        unfolding
          t\<^sub>2_\<gamma>[unfolded \<mu>(2) term_subst.subst_comp_subst]       
          t\<^sub>2'_\<gamma>[unfolded \<mu>(2) term_subst.subst_comp_subst]
          term.order.less\<^sub>G_def.

      then show "\<not> t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<preceq>\<^sub>t t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu>"
        using term.order.ground_less_not_less_eq[OF term_groundings]
        by blast
    next
      show 
        "C' = add_mset (?\<P> (Upair (c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> (t\<^sub>1' \<cdot>t \<rho>\<^sub>1))) 
          (E' \<cdot> \<rho>\<^sub>1 + D' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu>"
        unfolding  C'..
      show "welltyped_imgu \<V>\<^sub>3 (t\<^sub>1 \<cdot>t \<rho>\<^sub>1) (t\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<mu>"
        using \<mu>(3) by blast

      show "clause.vars (E \<cdot> \<rho>\<^sub>1) \<inter> clause.vars (D \<cdot> \<rho>\<^sub>2) = {}"
        using rename_apart. 

      show "\<forall>x\<in>clause.vars (E \<cdot> \<rho>\<^sub>1). \<V>\<^sub>1 (inv \<rho>\<^sub>1 (Var x)) = \<V>\<^sub>3 x"
        unfolding \<V>\<^sub>3_def
        by meson

      show "\<forall>x\<in>clause.vars (D \<cdot> \<rho>\<^sub>2). \<V>\<^sub>2 (inv \<rho>\<^sub>2 (Var x)) = \<V>\<^sub>3 x"
        unfolding \<V>\<^sub>3_def
        using rename_apart
        by (meson disjoint_iff)

      show "is_welltyped_on (clause.vars E) \<V>\<^sub>1 \<rho>\<^sub>1"
        using \<rho>\<^sub>1_is_welltyped.

      show "is_welltyped_on (clause.vars D) \<V>\<^sub>2 \<rho>\<^sub>2"
        using \<rho>\<^sub>2_is_welltyped.

      have "\<exists>\<tau>. welltyped \<V>\<^sub>2 t\<^sub>2 \<tau> \<and> welltyped \<V>\<^sub>2 t\<^sub>2' \<tau>"
        using D_is_welltyped
        unfolding D l\<^sub>2
        by auto

      then show "\<And>\<tau> \<tau>'. \<lbrakk>typed \<V>\<^sub>2 t\<^sub>2 \<tau>; typed \<V>\<^sub>2 t\<^sub>2' \<tau>'\<rbrakk> \<Longrightarrow> \<tau> = \<tau>'"
        using term.typed_if_welltyped by blast

      show "infinite_variables_per_type \<V>\<^sub>1" "infinite_variables_per_type \<V>\<^sub>2"
        using \<V>\<^sub>1 \<V>\<^sub>2
        by auto
    qed

    have "term_subst.is_idem \<mu>"
      using \<mu>(1)
      by (simp add: term_subst.is_imgu_iff_is_idem_and_is_mgu)  

    then have \<mu>_\<gamma>: "\<mu> \<odot> \<gamma> = \<gamma>"
      unfolding \<mu>(2) term_subst.is_idem_def
      by (metis subst_compose_assoc)

    have C'_\<gamma>: "C' \<cdot> \<gamma> = C \<cdot> \<gamma>"
    proof-
      have "C \<cdot> \<gamma> = 
              add_mset (?\<P> (Upair (context.from_ground c\<^sub>G)\<langle>term.from_ground t\<^sub>G\<^sub>3\<rangle> (term.from_ground t\<^sub>G\<^sub>2))) 
                (clause.from_ground E\<^sub>G' + clause.from_ground D\<^sub>G')"
        using ground_superpositionI(4, 12) clause.to_ground_inverse[OF C_grounding] 
        by auto

      then show ?thesis
        unfolding 
          C'
          E'_\<gamma>[symmetric] 
          D'_\<gamma>[symmetric] 
          t\<^sub>1'_\<gamma>[symmetric]
          c\<^sub>1_t\<^sub>2'_\<gamma>[symmetric]
        unfolding
          clause.subst_comp_subst[symmetric]
          \<mu>_\<gamma>
        by simp
    qed

    have vars_C': 
      "clause.vars C' \<subseteq> clause.vars (E \<cdot> \<rho>\<^sub>1) \<union> clause.vars (D \<cdot> \<rho>\<^sub>2)"
    proof
      fix x 
      assume "x \<in> clause.vars C'"

      then consider 
        (term\<^sub>2'_with_context) "x \<in> term.vars ((c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> \<cdot>t \<mu>)" 
        | (term\<^sub>1')  "x \<in> term.vars (t\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu>)"  
        | (E')  "x \<in> clause.vars (E' \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>)"  
        | (D')  "x \<in> clause.vars (D' \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>)"  
        unfolding C' clause.add_subst clause.plus_subst subst_literal
        by auto

      then show "x \<in> clause.vars (E \<cdot> \<rho>\<^sub>1) \<union> clause.vars (D \<cdot> \<rho>\<^sub>2)"
      proof(cases)
        case t: term\<^sub>2'_with_context
        then show ?thesis 
          using  context.variables_in_base_imgu[OF \<mu>(1)] term.variables_in_base_imgu[OF \<mu>(1)] 
          unfolding E l\<^sub>1 D l\<^sub>2
            (* TODO: *)
          apply auto
          by (smt (verit, ccfv_threshold) UnE in_mono t vars_term_ctxt_apply)
      next
        case term\<^sub>1'
        then show ?thesis
          using term.variables_in_base_imgu[OF \<mu>(1)]
          unfolding E clause.add_subst l\<^sub>1 D l\<^sub>2
          by auto
      next
        case E'
        then show ?thesis 
          using clause.variables_in_base_imgu[OF \<mu>(1)]
          unfolding E l\<^sub>1 D l\<^sub>2
          by auto
      next
        case D'
        then show ?thesis 
          using clause.variables_in_base_imgu[OF \<mu>(1)]
          unfolding E l\<^sub>1 D l\<^sub>2
          by auto
      qed
    qed

    have surjx: "surj (\<lambda>x. inv \<rho>\<^sub>2 (Var x))"
      using term.surj_inv_renaming[OF \<rho>\<^sub>2].

    have infinite_variables_per_type_\<V>\<^sub>3: "infinite_variables_per_type \<V>\<^sub>3"
    proof(unfold infinite_variables_per_type_def \<V>\<^sub>3_def if_distrib if_distribR move_simp Finite_Set.infinite_Un zz, intro allI disjI2 Diff_infinite_finite)
      fix ty
      show "finite {x. x \<in> clause.vars (E \<cdot> \<rho>\<^sub>1)}"
        using clause.finite_vars[of "E \<cdot> \<rho>\<^sub>1"]
        by simp

      show "infinite {x. \<V>\<^sub>2 (inv \<rho>\<^sub>2 (Var x)) = ty}"
        using 
          surj_infinite_set[OF 
            surjx \<V>\<^sub>2[unfolded infinite_variables_per_type_def, rule_format]].
    qed

    show "\<iota>\<^sub>G \<in> inference_groundings (Infer [(D, \<V>\<^sub>2), (E, \<V>\<^sub>1)] (C', \<V>\<^sub>3))"
    proof-
      have " \<lbrakk>C' \<cdot> \<gamma> = C \<cdot> \<gamma>;
         ground.superposition (clause.to_ground (D \<cdot> \<rho>\<^sub>2 \<cdot> \<gamma>))
          (clause.to_ground (E \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma>)) (clause.to_ground (C \<cdot> \<gamma>));
         is_welltyped_on (clause.vars C') \<V>\<^sub>3 \<gamma>; infinite_variables_per_type \<V>\<^sub>3\<rbrakk>
        \<Longrightarrow> clause.is_welltyped \<V>\<^sub>3 C'"
        using \<open>superposition (D, \<V>\<^sub>2) (E, \<V>\<^sub>1) (C', \<V>\<^sub>3)\<close> 
          superposition_preserves_typing E_is_welltyped D_is_welltyped by blast

      then have 
        "is_inference_grounding (Infer [(D, \<V>\<^sub>2), (E, \<V>\<^sub>1)] (C', \<V>\<^sub>3)) \<iota>\<^sub>G \<gamma> \<rho>\<^sub>1 \<rho>\<^sub>2"
        using 
          C'_\<gamma> ground_superposition 
          is_welltyped_on_subset[OF \<gamma>_is_welltyped vars_C'] 
          infinite_variables_per_type_\<V>\<^sub>3
          E_is_welltyped
          D_is_welltyped
        unfolding ground.G_Inf_def \<iota>\<^sub>G
        using D_grounding E_grounding C_grounding
        by(auto simp: \<V>\<^sub>1 \<V>\<^sub>2 \<rho>\<^sub>1 \<rho>\<^sub>2 rename_apart)

      then show ?thesis
        using is_inference_grounding_inference_groundings
        by blast
    qed

    show "C' \<cdot> \<gamma> = C \<cdot> \<gamma>"
      using C'_\<gamma>.
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
  obtain E\<^sub>G D\<^sub>G C\<^sub>G where 
    \<iota>\<^sub>G : "\<iota>\<^sub>G = Infer [D\<^sub>G, E\<^sub>G] C\<^sub>G" and
    superposition: "ground.superposition D\<^sub>G E\<^sub>G C\<^sub>G"
    using assms(1)
    by blast

  have 
    E\<^sub>G_in_groundings: "E\<^sub>G \<in> \<Union> (clause_groundings ` premises)" and  
    D\<^sub>G_in_groundings: "D\<^sub>G \<in> \<Union> (clause_groundings ` premises)"
    using assms(2)
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
    by simp_all

  obtain E \<V>\<^sub>1 D \<V>\<^sub>2 \<gamma>\<^sub>1 \<gamma>\<^sub>2 where
    E_\<gamma>\<^sub>1: "E \<cdot> \<gamma>\<^sub>1 = clause.from_ground E\<^sub>G" and
    D_\<gamma>\<^sub>2: "D \<cdot> \<gamma>\<^sub>2 = clause.from_ground D\<^sub>G" and
    select: 
    "clause.from_ground (select\<^sub>G (clause.to_ground (E \<cdot> \<gamma>\<^sub>1))) = select E \<cdot> \<gamma>\<^sub>1"
    "clause.from_ground (select\<^sub>G (clause.to_ground (D \<cdot> \<gamma>\<^sub>2))) = select D \<cdot> \<gamma>\<^sub>2" and
    E_in_premises: "(E, \<V>\<^sub>1) \<in> premises" and
    D_in_premises: "(D, \<V>\<^sub>2) \<in> premises" and 
    wt: 
    "is_welltyped_on (clause.vars E) \<V>\<^sub>1 \<gamma>\<^sub>1"
    "is_welltyped_on (clause.vars D) \<V>\<^sub>2 \<gamma>\<^sub>2"
    (*"term_subst.is_ground_subst \<gamma>\<^sub>1"
    "term_subst.is_ground_subst \<gamma>\<^sub>2" *)
    "clause.is_welltyped \<V>\<^sub>1 E"
    "clause.is_welltyped \<V>\<^sub>2 D"
    "infinite_variables_per_type \<V>\<^sub>1" 
    "infinite_variables_per_type \<V>\<^sub>2" 
    using assms(2, 4) E\<^sub>G_in_groundings D\<^sub>G_in_groundings
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
    by (smt (verit) clause.from_ground_inverse clause.ground_is_ground clause.obtain_grounding select_ground_subst
        split_beta split_pairs)

  obtain \<rho>\<^sub>1 \<rho>\<^sub>2 :: "('f, 'v) subst" where
    renaming: 
    "term_subst.is_renaming \<rho>\<^sub>1" 
    "term_subst.is_renaming \<rho>\<^sub>2"
    "\<rho>\<^sub>1 ` (clause.vars E) \<inter> \<rho>\<^sub>2 ` (clause.vars D) = {}" and
    wt_\<rho>: 
    "is_welltyped_on (clause.vars E) \<V>\<^sub>1 \<rho>\<^sub>1"
    "is_welltyped_on (clause.vars D) \<V>\<^sub>2 \<rho>\<^sub>2"
    using welltyped.obtain_typed_renamings[OF infinite_UNIV _ _ wt(5,6)[unfolded infinite_variables_per_type_def, rule_format]] 
    by (metis clause.finite_vars(1))

  have renaming_distinct: "clause.vars (E \<cdot> \<rho>\<^sub>1) \<inter> clause.vars (D \<cdot> \<rho>\<^sub>2) = {}"
    using renaming(3)
    unfolding renaming(1,2)[THEN clause.renaming_variables, symmetric]
    by blast

  from renaming obtain \<rho>\<^sub>1_inv \<rho>\<^sub>2_inv where
    \<rho>\<^sub>1_inv: "\<rho>\<^sub>1 \<odot> \<rho>\<^sub>1_inv = Var" and
    \<rho>\<^sub>2_inv: "\<rho>\<^sub>2 \<odot> \<rho>\<^sub>2_inv = Var"
    unfolding term_subst.is_renaming_def
    by blast

  have "select E \<subseteq># E" "select D \<subseteq># D"
    by (simp_all add: select_subset)

  then have select_subset: 
    "select E \<cdot> \<rho>\<^sub>1 \<subseteq># E \<cdot> \<rho>\<^sub>1" 
    "select D \<cdot> \<rho>\<^sub>2 \<subseteq># D \<cdot> \<rho>\<^sub>2"
    by (simp_all add: image_mset_subseteq_mono clause.subst_def)

  define \<gamma> where 
    \<gamma>: "\<And>var. \<gamma> var \<equiv>
          if var \<in> clause.vars (E \<cdot> \<rho>\<^sub>1)
          then (\<rho>\<^sub>1_inv \<odot> \<gamma>\<^sub>1) var 
          else (\<rho>\<^sub>2_inv \<odot> \<gamma>\<^sub>2) var"

  have \<gamma>\<^sub>1: "\<forall>x\<in> clause.vars E. (\<rho>\<^sub>1 \<odot> \<gamma>) x = \<gamma>\<^sub>1 x"
  proof(intro ballI)
    fix x
    assume x_in_vars: "x \<in> clause.vars E"

    obtain y where y: "\<rho>\<^sub>1 x = Var y"
      by (meson is_Var_def renaming(1) term_subst_is_renaming_iff)

    then have "y \<in> clause.vars (E \<cdot> \<rho>\<^sub>1)"
      using x_in_vars renaming(1) clause.renaming_variables by fastforce


    then have "\<gamma> y = \<rho>\<^sub>1_inv y \<cdot>t \<gamma>\<^sub>1"
      by (simp add: \<gamma> subst_compose)

    then show "(\<rho>\<^sub>1 \<odot> \<gamma>) x = \<gamma>\<^sub>1 x"
      by (metis y \<rho>\<^sub>1_inv eval_term.simps(1) subst_compose)
  qed

  have \<gamma>\<^sub>2: "\<forall>x\<in> clause.vars D. (\<rho>\<^sub>2 \<odot> \<gamma>) x = \<gamma>\<^sub>2 x"
  proof(intro ballI)
    fix x
    assume x_in_vars: "x \<in> clause.vars D"

    obtain y where y: "\<rho>\<^sub>2 x = Var y"
      by (meson is_Var_def renaming(2) term_subst_is_renaming_iff)

    then have "y \<in> clause.vars (D \<cdot> \<rho>\<^sub>2)"
      using x_in_vars renaming(2) clause.renaming_variables by fastforce

    then have "\<gamma> y = \<rho>\<^sub>2_inv y \<cdot>t \<gamma>\<^sub>2"
      using \<gamma> renaming_distinct subst_compose by fastforce

    then show "(\<rho>\<^sub>2 \<odot> \<gamma>) x = \<gamma>\<^sub>2 x"
      by (metis y \<rho>\<^sub>2_inv eval_term.simps(1) subst_compose)
  qed

  have \<gamma>\<^sub>1_is_ground: "\<forall>x\<in>clause.vars E. term.is_ground (\<gamma>\<^sub>1 x)"
    by (metis clause.ground_is_ground clause.variable_grounding
        E_\<gamma>\<^sub>1)

  have \<gamma>\<^sub>2_is_ground: "\<forall>x\<in>clause.vars D. term.is_ground (\<gamma>\<^sub>2 x)"
    by (metis clause.ground_is_ground clause.variable_grounding
        D_\<gamma>\<^sub>2)

  have wt_\<gamma>:
    "is_welltyped_on (clause.vars E) \<V>\<^sub>1 (\<rho>\<^sub>1 \<odot> \<gamma>)"
    "is_welltyped_on (clause.vars D) \<V>\<^sub>2 (\<rho>\<^sub>2 \<odot> \<gamma>)"
    using wt(1,2) is_welltyped_on_subset \<gamma>\<^sub>1 \<gamma>\<^sub>2
    by auto    

(*have "term_subst.is_ground_subst (\<rho>\<^sub>1_inv \<odot> \<gamma>\<^sub>1)" "term_subst.is_ground_subst (\<rho>\<^sub>2_inv \<odot> \<gamma>\<^sub>2)"
    using term_subst.is_ground_subst_comp_right wt by blast+

  then have is_ground_subst_\<gamma>: "term_subst.is_ground_subst \<gamma>"
    unfolding \<gamma>
    using is_ground_subst_if
    by fast*)

  have E_\<gamma>: "E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma> = clause.from_ground E\<^sub>G" 
  proof -
    have "E \<cdot> \<rho>\<^sub>1 \<odot> (\<rho>\<^sub>1_inv \<odot> \<gamma>\<^sub>1) = clause.from_ground E\<^sub>G"
      by (metis \<rho>\<^sub>1_inv E_\<gamma>\<^sub>1 subst_monoid_mult.mult.left_neutral subst_monoid_mult.mult_assoc)

    then show ?thesis
      using \<gamma>\<^sub>1 E_\<gamma>\<^sub>1 clause.subst_eq by fastforce
  qed

  have D_\<gamma>: "D \<cdot> \<rho>\<^sub>2 \<odot>  \<gamma> = clause.from_ground D\<^sub>G" 
  proof -
    have "D \<cdot> \<rho>\<^sub>2 \<odot> (\<rho>\<^sub>2_inv \<odot> \<gamma>\<^sub>2) = clause.from_ground D\<^sub>G"
      by (metis \<rho>\<^sub>2_inv D_\<gamma>\<^sub>2 subst_monoid_mult.mult.left_neutral subst_monoid_mult.mult_assoc)

    then show ?thesis
      using \<gamma>\<^sub>2 D_\<gamma>\<^sub>2 clause.subst_eq
      by fastforce
  qed

  have "E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma> = E \<cdot> \<gamma>\<^sub>1"
    using E_\<gamma> E_\<gamma>\<^sub>1 
    by argo

  moreover have "select E \<cdot> \<rho>\<^sub>1 \<cdot> \<gamma> = select E \<cdot> \<gamma>\<^sub>1"
  proof-
    have "clause.vars (select E \<cdot> \<rho>\<^sub>1) \<subseteq> clause.vars (E \<cdot> \<rho>\<^sub>1)"
      using select_subset(1) clause_submset_vars_clause_subset by blast

    then show ?thesis
      unfolding \<gamma> 
      by (smt (verit, best) \<rho>\<^sub>1_inv clause.subst_eq subsetD 
          clause.comp_subst.left.monoid_action_compatibility 
          term_subst.comp_subst.left.right_neutral)
  qed

  ultimately have select\<^sub>1: 
    "clause.from_ground (select\<^sub>G (clause.to_ground (E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>))) = select E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>"
    using select(1)
    by auto

  have "D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma> = D \<cdot> \<gamma>\<^sub>2"
    using D_\<gamma> D_\<gamma>\<^sub>2
    by simp

  moreover have "select D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma> = select D \<cdot> \<gamma>\<^sub>2"
  proof-
    have "clause.vars (select D \<cdot> \<rho>\<^sub>2) \<subseteq> clause.vars (D \<cdot> \<rho>\<^sub>2)"
      using select_subset(2) clause_submset_vars_clause_subset by blast

    then show ?thesis
      unfolding \<gamma> 
      by (smt (verit, best) \<gamma>\<^sub>2 \<gamma> \<open>select D \<subseteq># D\<close> clause_submset_vars_clause_subset
          clause.subst_eq subset_iff clause.comp_subst.left.monoid_action_compatibility)
  qed

  ultimately have select\<^sub>2: 
    "clause.from_ground (select\<^sub>G (clause.to_ground (D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>))) = select D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>"   
    using select(2) 
    by argo

  obtain C where 
    C_\<gamma>: "C \<cdot> \<gamma> = clause.from_ground C\<^sub>G"
    by (meson clause.ground_is_ground clause.subst_ident_if_ground)

  then have 
    E_grounding: "clause.is_ground (E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)" and 
    D_grounding: "clause.is_ground (D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>)" and 
    E\<^sub>G: "E\<^sub>G = clause.to_ground (E \<cdot> \<rho>\<^sub>1 \<odot> \<gamma>)" and 
    D\<^sub>G: "D\<^sub>G = clause.to_ground (D \<cdot> \<rho>\<^sub>2 \<odot> \<gamma>)" and 
    C_grounding: "clause.is_ground (C \<cdot> \<gamma>)" and
    C\<^sub>G: "C\<^sub>G = clause.to_ground (C \<cdot> \<gamma>)"
    using E_\<gamma> D_\<gamma>
    by simp_all

  have "clause_groundings (E, \<V>\<^sub>1) \<union> clause_groundings (D, \<V>\<^sub>2)
     \<subseteq> \<Union> (clause_groundings ` premises)"
    using E_in_premises D_in_premises by blast

  then have \<iota>\<^sub>G_not_redunant:
    "\<iota>\<^sub>G \<notin> ground.GRed_I (clause_groundings (E, \<V>\<^sub>1) \<union> clause_groundings (D, \<V>\<^sub>2))"
    using assms(3) ground.Red_I_of_subset
    by blast

  then obtain C' \<V>\<^sub>3 where 
    superposition: "superposition (D, \<V>\<^sub>2) (E, \<V>\<^sub>1) (C', \<V>\<^sub>3)" and
    inference_groundings: 
    "\<iota>\<^sub>G \<in> inference_groundings (Infer [(D, \<V>\<^sub>2), (E, \<V>\<^sub>1)] (C', \<V>\<^sub>3))" and  
    C'_\<gamma>_C_\<gamma>: "C' \<cdot> \<gamma> = C \<cdot> \<gamma>"
    using 
      superposition_lifting[OF 
        superposition[unfolded  D\<^sub>G E\<^sub>G C\<^sub>G]
        renaming(1,2)
        renaming_distinct
        E_grounding 
        D_grounding 
        C_grounding
        select\<^sub>1
        select\<^sub>2
        wt(3, 4)
        wt_\<gamma>
        wt_\<rho>
        wt(5, 6)
        \<iota>\<^sub>G_not_redunant[unfolded \<iota>\<^sub>G D\<^sub>G E\<^sub>G C\<^sub>G]
        ]
    unfolding \<iota>\<^sub>G C\<^sub>G E\<^sub>G D\<^sub>G 
    by blast

  let ?\<iota> = "Infer [(D, \<V>\<^sub>2), (E, \<V>\<^sub>1)] (C', \<V>\<^sub>3)"

  show ?thesis
  proof(rule that)
    show "?\<iota> \<in> Inf_from premises"
      using E_in_premises D_in_premises superposition
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
