theory First_Order_Superposition_Soundness
  imports Grounded_Superposition
begin

(* TODO: Write about wrong displaying *)


subsection \<open>Soundness\<close>

context grounded_superposition_calculus
begin
  
(* TODO : Find rewrite to make both equal *)
abbreviation entails\<^sub>F (infix "\<TTurnstile>\<^sub>F" 50) where
  "entails\<^sub>F \<equiv> lifting.entails_\<G>"

lemma "entails_\<G> = lifting.entails_\<G>"
  unfolding entails_def
  using Q_nonempty
  by blast

lemma eq_resolution_sound:
  assumes eq_resolution: "eq_resolution D C"
  shows "{D} \<TTurnstile>\<^sub>F {C}"
  using eq_resolution
proof (cases D C rule: eq_resolution.cases)
  case (eq_resolutionI D l D' t t' \<mu> \<V> C)

  {
    fix I :: "'f ground_term rel" and \<gamma> :: "('f, 'v) subst"

    let ?I = "upair ` I"

    assume
      refl_I: "refl I" and
      entails_groundings: "\<forall>D\<^sub>G \<in> clause_groundings (D, \<V>). ?I \<TTurnstile> D\<^sub>G" and
      C_is_ground: "clause.is_ground (C \<cdot> \<gamma>)" and
      C_is_welltyped: "clause.is_welltyped \<V> C" and
      \<gamma>_is_welltyped: "is_welltyped_on (clause.vars C) \<V> \<gamma>" and
      \<V>: "infinite_variables_per_type \<V>"

    obtain \<gamma>' where
      \<gamma>'_is_ground_subst: "term_subst.is_ground_subst \<gamma>'" and
      \<gamma>'_is_welltyped: "is_welltyped \<V> \<gamma>'" and
      \<gamma>'_\<gamma>: "\<forall>x \<in> clause.vars C. \<gamma> x = \<gamma>' x"
      using 
        clause.is_welltyped.ground_subst_extension[OF
          types_inhabited C_is_ground \<gamma>_is_welltyped].

    let ?D = "clause.to_ground (D \<cdot> \<mu> \<cdot> \<gamma>')"
    let ?l = "literal.to_ground (l \<cdot>l \<mu> \<cdot>l \<gamma>')"
    let ?D' = "clause.to_ground (D' \<cdot> \<mu> \<cdot> \<gamma>')"
    let ?t = "term.to_ground (t \<cdot>t \<mu> \<cdot>t \<gamma>')"
    let ?t' = "term.to_ground (t' \<cdot>t \<mu> \<cdot>t \<gamma>')"

    have \<mu>_is_welltyped: "is_welltyped \<V> \<mu>"
      using eq_resolutionI
      by meson

    have "?D \<in> clause_groundings (D, \<V>)"
    proof(unfold clause_groundings_def mem_Collect_eq fst_conv snd_conv, intro exI conjI \<V>)
      show "clause.to_ground (D \<cdot> \<mu> \<cdot> \<gamma>') = clause.to_ground (D \<cdot> \<mu> \<odot> \<gamma>')"
        by simp
    next
      show "clause.is_ground (D \<cdot> \<mu> \<odot> \<gamma>')"
        using \<gamma>'_is_ground_subst clause.is_ground_subst_is_ground
        by auto
    next
      have "clause.is_welltyped \<V> D'"
        using C_is_welltyped \<mu>_is_welltyped
        unfolding eq_resolutionI
        by simp

      then show "clause.is_welltyped \<V> D"
        unfolding eq_resolutionI
        using eq_resolutionI(6)
        by auto
    next
      show "is_welltyped_on (clause.vars D) \<V> (\<mu> \<odot> \<gamma>')"
        using \<gamma>'_is_welltyped \<mu>_is_welltyped
        by (simp add: subst_compose_def)
    qed

    then have "?I \<TTurnstile> ?D"
      using entails_groundings
      by auto 

    then obtain l' where l'_in_D: "l' \<in># ?D" and I_models_l': "?I \<TTurnstile>l l'"
      by (auto simp: true_cls_def)

    have [simp]: "?D = add_mset ?l ?D'"
      unfolding eq_resolutionI
      by simp

    have [simp]: "?l = ?t !\<approx> ?t'"
      unfolding eq_resolutionI
      by simp

    have [simp]: "?t = ?t'"
      using term_subst.is_imgu_unifies'[OF eq_resolutionI(5)]
      by argo

    have "?I \<TTurnstile> clause.to_ground (C \<cdot> \<gamma>)"
    proof(cases "l' = ?l")
      case True

      moreover then have "atm_of l' \<in> ?I"
        using reflD[OF refl_I, of ?t]
        by auto

      ultimately show ?thesis
        using I_models_l'
        by auto
    next
      case False

      then have "l' \<in># clause.to_ground (C \<cdot> \<gamma>')"
        using l'_in_D
        unfolding eq_resolutionI
        by simp

      then show ?thesis
        using clause.subst_eq[OF \<gamma>'_\<gamma>[rule_format]] I_models_l'
        by auto
    qed
  }

  then show ?thesis
    unfolding
      ground.G_entails_def 
      true_clss_def 
      eq_resolutionI(1,2)
      clause_groundings_def
    by auto
qed

lemma eq_factoring_sound:
  assumes step: "eq_factoring D C"
  shows "{D} \<TTurnstile>\<^sub>F {C}"
  using step
proof (cases D C rule: eq_factoring.cases)
  case (eq_factoringI D l\<^sub>1 l\<^sub>2 D' t\<^sub>1 t\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu> \<V> C)

  {
    fix I :: "'f ground_term rel" and \<gamma> :: "('f, 'v) subst"

    let ?I = "upair ` I"

    assume
      trans_I: "trans I" and
      sym_I: "sym I" and
      entails_groundings: "\<forall>D\<^sub>G \<in> clause_groundings (D, \<V>). ?I \<TTurnstile> D\<^sub>G" and
      C_is_ground: "clause.is_ground (C \<cdot> \<gamma>)" and
      C_is_welltyped: "clause.is_welltyped \<V> C" and
      \<gamma>_is_welltyped: "is_welltyped_on (clause.vars C) \<V> \<gamma>" and
      \<V>: "infinite_variables_per_type \<V>"

    obtain \<gamma>' where
      \<gamma>'_is_ground_subst: "term_subst.is_ground_subst \<gamma>'" and
      \<gamma>'_is_welltyped: "is_welltyped \<V> \<gamma>'" and
      \<gamma>'_\<gamma>: "\<forall>x \<in> clause.vars C. \<gamma> x = \<gamma>' x"
      using 
        clause.is_welltyped.ground_subst_extension[OF
          types_inhabited C_is_ground \<gamma>_is_welltyped].

    let ?D = "clause.to_ground (D \<cdot> \<mu> \<cdot> \<gamma>')"
    let ?D' = "clause.to_ground (D' \<cdot> \<mu> \<cdot> \<gamma>')"
    let ?l\<^sub>1 = "literal.to_ground (l\<^sub>1 \<cdot>l \<mu> \<cdot>l \<gamma>')"
    let ?l\<^sub>2 = "literal.to_ground (l\<^sub>2 \<cdot>l \<mu> \<cdot>l \<gamma>')"
    let ?t\<^sub>1 = "term.to_ground (t\<^sub>1 \<cdot>t \<mu> \<cdot>t \<gamma>')"
    let ?t\<^sub>1' = "term.to_ground (t\<^sub>1' \<cdot>t \<mu> \<cdot>t \<gamma>')"
    let ?t\<^sub>2 = "term.to_ground (t\<^sub>2 \<cdot>t \<mu> \<cdot>t \<gamma>')"
    let ?t\<^sub>2' = "term.to_ground (t\<^sub>2' \<cdot>t \<mu> \<cdot>t \<gamma>')"
    let ?C = "clause.to_ground (C \<cdot> \<gamma>')"

    have \<mu>_is_welltyped: "is_welltyped \<V> \<mu>"
      using eq_factoringI(10)
      by blast

    have "?D \<in> clause_groundings (D, \<V>)"
    proof(unfold clause_groundings_def mem_Collect_eq fst_conv snd_conv, intro exI conjI \<V>)
      show "clause.to_ground (D \<cdot> \<mu> \<cdot> \<gamma>') = clause.to_ground (D \<cdot> \<mu> \<odot> \<gamma>')"
        by simp
    next
      show "clause.is_ground (D \<cdot> \<mu> \<odot> \<gamma>')"
        using \<gamma>'_is_ground_subst clause.is_ground_subst_is_ground
        by auto
    next
      have
        "clause.is_welltyped \<V> (D' \<cdot> \<mu>)"
        "literal.is_welltyped \<V> (t\<^sub>1 \<approx> t\<^sub>2')" 
        "literal.is_welltyped \<V> (t\<^sub>1' !\<approx> t\<^sub>2')"
        using C_is_welltyped \<mu>_is_welltyped
        unfolding eq_factoringI
        by auto

      then have
        "clause.is_welltyped \<V> D'"
        "literal.is_welltyped \<V> (t\<^sub>1 \<approx> t\<^sub>1')"
        "literal.is_welltyped \<V> (t\<^sub>2 \<approx> t\<^sub>2')"
        using eq_factoringI(10)
        by auto

      then show "clause.is_welltyped \<V> D"
        unfolding eq_factoringI
        by simp
    next
      show "is_welltyped_on (clause.vars D) \<V> (\<mu> \<odot> \<gamma>')"
        using \<mu>_is_welltyped \<gamma>'_is_welltyped
        by (simp add: subst_compose_def)
    qed

    then have "?I \<TTurnstile> ?D"
      using entails_groundings
      by blast

    then obtain l' where l'_in_D: "l' \<in># ?D" and I_models_l': "?I \<TTurnstile>l l'"
      by (auto simp: true_cls_def)

    have [simp]: "?t\<^sub>2 = ?t\<^sub>1"
      using term_subst.is_imgu_unifies'[OF eq_factoringI(9)]
      by argo

    have [simp]: "?l\<^sub>1 = ?t\<^sub>1 \<approx> ?t\<^sub>1'"
      unfolding eq_factoringI
      by simp

    have [simp]: "?l\<^sub>2 = ?t\<^sub>2 \<approx> ?t\<^sub>2'"
      unfolding eq_factoringI
      by simp

    have [simp]: "?C = add_mset (?t\<^sub>1 \<approx> ?t\<^sub>2') (add_mset (Neg (Upair ?t\<^sub>1' ?t\<^sub>2')) ?D')"
      unfolding eq_factoringI 
      by simp

    have "?I \<TTurnstile> clause.to_ground (C \<cdot> \<gamma>)"
    proof(cases "l' = ?l\<^sub>1 \<or> l' = ?l\<^sub>2")
      case True

      then have "?I \<TTurnstile>l ?t\<^sub>1 \<approx> ?t\<^sub>1' \<or> ?I \<TTurnstile>l ?t\<^sub>1 \<approx> ?t\<^sub>2'"
        using I_models_l' sym_I
        by(auto elim: symE)

      then have "?I \<TTurnstile>l ?t\<^sub>1 \<approx> ?t\<^sub>2' \<or> ?I \<TTurnstile>l ?t\<^sub>1' !\<approx> ?t\<^sub>2'"
        using sym_I trans_I
        by(auto dest: transD)

      then show ?thesis
        using clause.subst_eq[OF \<gamma>'_\<gamma>[rule_format]] sym_I
        by auto
    next
      case False

      then have "l' \<in># ?D'"
        using l'_in_D
        unfolding eq_factoringI
        by simp

      then have "l' \<in># clause.to_ground (C \<cdot> \<gamma>)"
        using clause.subst_eq[OF \<gamma>'_\<gamma>[rule_format]]
        by simp

      then show ?thesis
        using I_models_l' 
        by blast
    qed
  }

  then show ?thesis
    unfolding
      eq_factoringI(1, 2)
      ground.G_entails_def
      true_clss_def
      clause_groundings_def
    by auto
qed

lemma superposition_sound:
  assumes step: "superposition P2 P1 C"
  shows "{P1, P2} \<TTurnstile>\<^sub>F {C}"
  using step
proof (cases P2 P1 C rule: superposition.cases)
  case (superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 P\<^sub>1  P\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' \<P> s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu> \<V>\<^sub>3 \<V>\<^sub>1 \<V>\<^sub>2 C)

  have 
    "\<And>I \<gamma>. \<lbrakk>
        refl I;
        trans I; 
        sym I;
        compatible_with_gctxt I;
        \<forall>P\<^sub>G. (\<exists>\<gamma>'. P\<^sub>G = clause.to_ground (P\<^sub>1 \<cdot> \<gamma>') \<and> clause.is_ground (P\<^sub>1 \<cdot> \<gamma>') \<and> 
              clause.is_welltyped \<V>\<^sub>1 P\<^sub>1 \<and> is_welltyped_on (clause.vars P\<^sub>1) \<V>\<^sub>1 \<gamma>' \<and> 
              infinite_variables_per_type \<V>\<^sub>1) \<longrightarrow> upair ` I \<TTurnstile> P\<^sub>G;
        \<forall>P\<^sub>G. (\<exists>\<gamma>'. P\<^sub>G = clause.to_ground (P\<^sub>2 \<cdot> \<gamma>') \<and>  clause.is_ground (P\<^sub>2 \<cdot> \<gamma>') \<and> 
              clause.is_welltyped \<V>\<^sub>2 P\<^sub>2 \<and> is_welltyped_on (clause.vars P\<^sub>2) \<V>\<^sub>2 \<gamma>' \<and> 
              infinite_variables_per_type \<V>\<^sub>2) \<longrightarrow> upair ` I \<TTurnstile> P\<^sub>G;
        clause.is_ground (C \<cdot> \<gamma>); clause.is_welltyped \<V>\<^sub>3 C; 
        is_welltyped_on (clause.vars C) \<V>\<^sub>3 \<gamma>; infinite_variables_per_type \<V>\<^sub>3
     \<rbrakk> \<Longrightarrow> (\<lambda>(x, y). Upair x y) ` I \<TTurnstile> clause.to_ground (C \<cdot> \<gamma>)"
  proof -
    fix I :: "'f gterm rel" and \<gamma> :: "'v \<Rightarrow> ('f, 'v) Term.term"

    let ?I = "(\<lambda>(x, y). Upair x y) ` I"

    assume 
      refl_I: "refl I" and 
      trans_I: "trans I" and 
      sym_I: "sym I" and 
      compatible_with_ground_context_I: "compatible_with_gctxt I" and
      premise1: 
      "\<forall>P\<^sub>G. (\<exists>\<gamma>'. P\<^sub>G = clause.to_ground (P\<^sub>1 \<cdot> \<gamma>') \<and> clause.is_ground (P\<^sub>1 \<cdot> \<gamma>')
              \<and> clause.is_welltyped \<V>\<^sub>1 P\<^sub>1 \<and> is_welltyped_on (clause.vars P\<^sub>1) \<V>\<^sub>1 \<gamma>' 
              \<and> infinite_variables_per_type \<V>\<^sub>1) \<longrightarrow>?I \<TTurnstile> P\<^sub>G" and
      premise2: 
      "\<forall>P\<^sub>G. (\<exists>\<gamma>'. P\<^sub>G = clause.to_ground (P\<^sub>2 \<cdot> \<gamma>') \<and>  clause.is_ground (P\<^sub>2 \<cdot> \<gamma>')
              \<and> clause.is_welltyped \<V>\<^sub>2 P\<^sub>2 \<and> is_welltyped_on (clause.vars P\<^sub>2) \<V>\<^sub>2 \<gamma>'
              \<and> infinite_variables_per_type \<V>\<^sub>2) \<longrightarrow> ?I \<TTurnstile> P\<^sub>G" and 
      grounding: " clause.is_ground (C \<cdot> \<gamma>)" "clause.is_welltyped \<V>\<^sub>3 C" 
      "is_welltyped_on (clause.vars C) \<V>\<^sub>3 \<gamma>" "infinite_variables_per_type \<V>\<^sub>3"

    have grounding': "clause.is_ground (C \<cdot> \<gamma>)"
      using grounding
      by (simp add: clause.is_ground_subst_is_ground)

    obtain \<gamma>' where
      \<gamma>': "term_subst.is_ground_subst \<gamma>'" "is_welltyped \<V>\<^sub>3 \<gamma>'" 
      "\<forall>x \<in> clause.vars C. \<gamma> x = \<gamma>' x"
      using clause.is_welltyped.ground_subst_extension[OF types_inhabited grounding' grounding(3)].

    let ?P\<^sub>1 = "clause.to_ground (P\<^sub>1 \<cdot> \<rho>\<^sub>1\<cdot> \<mu> \<cdot> \<gamma>')"
    let ?P\<^sub>2 = "clause.to_ground (P\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu> \<cdot> \<gamma>')"

    let ?L\<^sub>1 = "literal.to_ground (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu> \<cdot>l \<gamma>')"
    let ?L\<^sub>2 = "literal.to_ground (L\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu> \<cdot>l \<gamma>')"

    let ?P\<^sub>1' = "clause.to_ground (P\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<cdot> \<gamma>')"
    let ?P\<^sub>2' = "clause.to_ground (P\<^sub>2' \<cdot> \<rho>\<^sub>2 \<cdot> \<mu> \<cdot> \<gamma>')"

    let ?s\<^sub>1 = "context.to_ground (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<mu> \<cdot>t\<^sub>c \<gamma>')"
    let ?s\<^sub>1' = "term.to_ground (s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<gamma>')"
    let ?t\<^sub>2 = "term.to_ground (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<gamma>')"
    let ?t\<^sub>2' = "term.to_ground (t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<gamma>')"
    let ?u\<^sub>1 = "term.to_ground (u\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<gamma>')"

    let ?\<P> = "if \<P> = Pos then Pos else Neg"

    let ?C = "clause.to_ground (C \<cdot> \<gamma>')"

    have ground_subst: 
      "term_subst.is_ground_subst (\<rho>\<^sub>1 \<odot> \<mu> \<odot> \<gamma>')" 
      "term_subst.is_ground_subst (\<rho>\<^sub>2 \<odot> \<mu> \<odot> \<gamma>')"
      "term_subst.is_ground_subst (\<mu> \<odot> \<gamma>')"
      using term_subst.is_ground_subst_comp_right[OF \<gamma>'(1)]
      by blast+

    have xx: "\<forall>x\<in>term.vars (t\<^sub>2 \<cdot>t \<rho>\<^sub>2). \<V>\<^sub>2 (inv \<rho>\<^sub>2 (Var x)) = \<V>\<^sub>3 x" 
      "\<forall>x\<in>term.vars (t\<^sub>2' \<cdot>t \<rho>\<^sub>2). \<V>\<^sub>2 (inv \<rho>\<^sub>2 (Var x)) = \<V>\<^sub>3 x"
      using superpositionI(16)
      by (simp_all add: clause.vars_def local.superpositionI(11) local.superpositionI(8) 
          subst_atom subst_literal(1) vars_atom vars_literal(1))

    have wt_t: "\<exists>\<tau>. welltyped \<V>\<^sub>3 (t\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<tau> \<and> welltyped \<V>\<^sub>3 (t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu>) \<tau>"
    proof-

      obtain \<tau> where "welltyped \<V>\<^sub>3 (t\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<tau>"
        using superpositionI(14) by blast

      moreover then have "welltyped \<V>\<^sub>2 t\<^sub>2 \<tau>"
        using superpositionI(5) welltyped.explicit_typed_renaming xx(1) by blast

      moreover obtain \<tau>' where "welltyped \<V>\<^sub>3 (t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu>) \<tau>'"
      proof-
        have "term.is_welltyped \<V>\<^sub>3 ((s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> \<cdot>t \<mu>)"
          using grounding(2) superpositionI(9)
          unfolding superpositionI subst_literal
          by(auto simp: subst_literal subst_atom)

        then show ?thesis
          using that
          by (metis eval_ctxt term.welltyped.subterm)
      qed

      moreover then have "welltyped \<V>\<^sub>3 (t\<^sub>2' \<cdot>t \<rho>\<^sub>2) \<tau>'"
        by (meson UNIV_I superpositionI(14) welltyped.explicit_subst_stability)

      moreover then have "welltyped \<V>\<^sub>2 t\<^sub>2' \<tau>'"
        using local.superpositionI(5) welltyped.explicit_typed_renaming xx(2)
        by blast

      ultimately show ?thesis
        using superpositionI(19)
        by (metis term.typed_if_welltyped)
    qed

    have wt_P\<^sub>1: "clause.is_welltyped \<V>\<^sub>1 P\<^sub>1" 
    proof-
      have xx: "\<forall>x\<in>clause.vars (P\<^sub>1' \<cdot> \<rho>\<^sub>1). \<V>\<^sub>1 (inv \<rho>\<^sub>1 (Var x)) = \<V>\<^sub>3 x"
        using superpositionI(15)
        unfolding superpositionI clause.add_subst
        by auto

      have wt_P\<^sub>1': "clause.is_welltyped \<V>\<^sub>1 P\<^sub>1'"
      proof-
        have "\<lbrakk>literal.is_welltyped \<V>\<^sub>3 (\<P> (Upair (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> (s\<^sub>1' \<cdot>t \<rho>\<^sub>1)) \<cdot>l \<mu>);
             clause.is_welltyped \<V>\<^sub>3 (P\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>);
             clause.is_welltyped \<V>\<^sub>3 (P\<^sub>2' \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>)\<rbrakk>
             \<Longrightarrow> clause.is_welltyped \<V>\<^sub>1 P\<^sub>1'"
          using 
            clause.is_welltyped.typed_renaming[OF superpositionI(4) xx] 
            superpositionI(14) 
            clause.is_welltyped.subst_stability
          by (metis UNIV_I)          

        then show ?thesis
          using grounding(2)
          unfolding superpositionI clause.add_subst clause.plus_subst clause.is_welltyped_add
            clause.is_welltyped_plus
          by auto
      qed

      from wt_t have x1:
        "\<exists>\<tau>. welltyped \<V>\<^sub>3 (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>u\<^sub>1 \<cdot>t \<rho>\<^sub>1\<rangle> \<tau> \<and> welltyped \<V>\<^sub>3 (s\<^sub>1' \<cdot>t \<rho>\<^sub>1) \<tau>"
      proof-
        have "\<exists>\<tau>. welltyped \<V>\<^sub>3 (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<mu>)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu>\<rangle> \<tau> \<and>
               welltyped \<V>\<^sub>3 (s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu>) \<tau>"
          using grounding(2) superpositionI(9, 14, 15) 
          unfolding superpositionI
          by auto

        then have "\<exists>\<tau>. welltyped \<V>\<^sub>3 (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<mu>)\<langle>u\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu>\<rangle> \<tau> \<and> welltyped \<V>\<^sub>3 (s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu>) \<tau>"
          by (metis (no_types, lifting) iso_tuple_UNIV_I local.superpositionI(14)
              term.welltyped.context_compatible welltyped.explicit_subst_stability
              wt_t)

        then show ?thesis
          by (metis UNIV_I superpositionI(14) subst_apply_term_ctxt_apply_distrib
              welltyped.explicit_subst_stability)
      qed

      then have "\<exists>\<tau>. welltyped \<V>\<^sub>1 s\<^sub>1\<langle>u\<^sub>1\<rangle> \<tau> \<and> welltyped \<V>\<^sub>1 s\<^sub>1' \<tau>"
      proof-
        have x1': " \<And>\<tau>. \<lbrakk>\<forall>x\<in>literal.vars ((s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>u\<^sub>1 \<cdot>t \<rho>\<^sub>1\<rangle> \<approx> s\<^sub>1' \<cdot>t \<rho>\<^sub>1) \<union> clause.vars (P\<^sub>1' \<cdot> \<rho>\<^sub>1).
             \<V>\<^sub>1 (inv \<rho>\<^sub>1 (Var x)) = \<V>\<^sub>3 x;
          \<And>t \<V> \<V>' \<tau>.
             \<forall>x\<in>term.vars (t \<cdot>t \<rho>\<^sub>1). \<V> (inv \<rho>\<^sub>1 (Var x)) = \<V>' x \<Longrightarrow>
             welltyped \<V> t \<tau> = welltyped \<V>' (t \<cdot>t \<rho>\<^sub>1) \<tau>;
          welltyped \<V>\<^sub>3 (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>u\<^sub>1 \<cdot>t \<rho>\<^sub>1\<rangle> \<tau>;
          welltyped \<V>\<^sub>3 (s\<^sub>1' \<cdot>t \<rho>\<^sub>1) \<tau>; \<P> = Pos\<rbrakk>
         \<Longrightarrow> \<exists>\<tau>. welltyped \<V>\<^sub>1 s\<^sub>1\<langle>u\<^sub>1\<rangle> \<tau> \<and>
                 welltyped \<V>\<^sub>1 s\<^sub>1' \<tau>"
          "\<And>\<tau>. \<lbrakk>\<forall>x\<in>literal.vars ((s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>u\<^sub>1 \<cdot>t \<rho>\<^sub>1\<rangle> !\<approx> s\<^sub>1' \<cdot>t \<rho>\<^sub>1) \<union> clause.vars (P\<^sub>1' \<cdot> \<rho>\<^sub>1).
             \<V>\<^sub>1 (inv \<rho>\<^sub>1 (Var x)) = \<V>\<^sub>3 x;
          \<And>t \<V> \<V>' \<tau>.
             \<forall>x\<in>term.vars (t \<cdot>t \<rho>\<^sub>1). \<V> (inv \<rho>\<^sub>1 (Var x)) = \<V>' x \<Longrightarrow>
             welltyped \<V> t \<tau> = welltyped \<V>' (t \<cdot>t \<rho>\<^sub>1) \<tau>;
             welltyped \<V>\<^sub>3 (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>u\<^sub>1 \<cdot>t \<rho>\<^sub>1\<rangle> \<tau>;
              welltyped \<V>\<^sub>3 (s\<^sub>1' \<cdot>t \<rho>\<^sub>1) \<tau>; \<P> = Neg\<rbrakk>
         \<Longrightarrow> \<exists>\<tau>. welltyped \<V>\<^sub>1 s\<^sub>1\<langle>u\<^sub>1\<rangle> \<tau> \<and>
                 welltyped \<V>\<^sub>1 s\<^sub>1' \<tau>"
        (* TODO: *)
           apply auto
          by (metis (mono_tags) Un_iff subst_apply_term_ctxt_apply_distrib vars_term_ctxt_apply)+

        with x1 show ?thesis
          using superpositionI(15)  superpositionI(9) welltyped.explicit_typed_renaming[OF superpositionI(4)] 
          unfolding superpositionI clause.add_subst clause.vars_add
          by auto
      qed

      then show ?thesis
        using grounding(2) superpositionI(9, 14) wt_P\<^sub>1'
        unfolding superpositionI
        by auto
    qed

    have wt_P\<^sub>2: "clause.is_welltyped \<V>\<^sub>2 P\<^sub>2"
    proof-
      have xx: "\<forall>x\<in>clause.vars (P\<^sub>2' \<cdot> \<rho>\<^sub>2). \<V>\<^sub>2 (inv \<rho>\<^sub>2 (Var x)) = \<V>\<^sub>3 x"
        using superpositionI(16) 
        unfolding superpositionI
        by simp

      have wt_P\<^sub>2': "clause.is_welltyped \<V>\<^sub>2 P\<^sub>2'"
        using grounding(2)
        unfolding superpositionI clause.plus_subst clause.is_welltyped_add clause.add_subst
          clause.is_welltyped_plus clause.is_welltyped.typed_renaming[OF superpositionI(5) xx] 
        using superpositionI(14) clause.is_welltyped.subst_stability  
        by (metis UNIV_I \<open>clause.is_welltyped \<V>\<^sub>3 (P\<^sub>2' \<cdot> \<rho>\<^sub>2) = clause.is_welltyped \<V>\<^sub>2 P\<^sub>2'\<close>)
       
      have tt: "\<exists>\<tau>. welltyped \<V>\<^sub>3 (t\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<tau> \<and> welltyped \<V>\<^sub>3 (t\<^sub>2' \<cdot>t \<rho>\<^sub>2) \<tau>"
        using wt_t
        by (meson UNIV_I superpositionI(14) welltyped.explicit_subst_stability)

      show ?thesis
      proof-
        have "\<exists>\<tau>. welltyped \<V>\<^sub>2 t\<^sub>2 \<tau> \<and> welltyped \<V>\<^sub>2 t\<^sub>2' \<tau>"
          using superpositionI(16) welltyped.explicit_typed_renaming[OF superpositionI(5)]
          unfolding superpositionI
          by (metis (no_types, lifting) Un_iff subst_atom clause.add_subst subst_literal(1) tt 
              vars_atom clause.vars_add vars_literal(1))

        with wt_P\<^sub>2' show ?thesis
          unfolding superpositionI
          by auto
      qed
    qed

    have wt_\<mu>_\<gamma>: "is_welltyped \<V>\<^sub>3 (\<mu> \<odot> \<gamma>')"
      by (metis UNIV_I \<gamma>'(2) superpositionI(14) welltyped.subst_compose
          welltyped.explicit_subst_stability)

    have wt_\<gamma>: "is_welltyped_on (clause.vars P\<^sub>1) \<V>\<^sub>1 (\<rho>\<^sub>1 \<odot> \<mu> \<odot> \<gamma>')" 
      "is_welltyped_on (clause.vars P\<^sub>2) \<V>\<^sub>2 (\<rho>\<^sub>2 \<odot>  \<mu> \<odot> \<gamma>')"
      using
        superpositionI(15, 16)
        welltyped.is_welltyped_renaming_ground_subst_weaker[OF superpositionI(4) wt_\<mu>_\<gamma> superpositionI(17) 
          ground_subst(3)]
        welltyped.is_welltyped_renaming_ground_subst_weaker[OF superpositionI(5) wt_\<mu>_\<gamma> superpositionI(18)
          ground_subst(3)]
      unfolding clause.vars_subst
      by (simp_all add: subst_compose_assoc)

    have "?I \<TTurnstile> ?P\<^sub>1"
      using premise1[rule_format, of ?P\<^sub>1, OF exI, of "\<rho>\<^sub>1 \<odot> \<mu> \<odot> \<gamma>'"] ground_subst wt_P\<^sub>1 wt_\<gamma> 
        superpositionI(27)
      by (metis clause.ground_subst_iff_base_ground_subst clause.is_ground_subst_is_ground
          clause.subst_comp_subst)

    moreover have "?I \<TTurnstile> ?P\<^sub>2"
      using premise2[rule_format, of ?P\<^sub>2, OF exI, of "\<rho>\<^sub>2 \<odot> \<mu> \<odot> \<gamma>'"] ground_subst wt_P\<^sub>2 wt_\<gamma> 
        superpositionI(28)
      by (metis clause.ground_subst_iff_base_ground_subst clause.is_ground_subst_is_ground
          clause.subst_comp_subst)

    ultimately obtain L\<^sub>1' L\<^sub>2' 
      where
        L\<^sub>1'_in_P1: "L\<^sub>1' \<in># ?P\<^sub>1" and 
        I_models_L\<^sub>1': "?I \<TTurnstile>l L\<^sub>1'" and
        L\<^sub>2'_in_P2: "L\<^sub>2' \<in># ?P\<^sub>2" and 
        I_models_L\<^sub>2': "?I \<TTurnstile>l L\<^sub>2'"
      by (auto simp: true_cls_def)

    have u\<^sub>1_equals_t\<^sub>2: "?t\<^sub>2 = ?u\<^sub>1"
      using term_subst.is_imgu_unifies'[OF superpositionI(13)]
      by argo

    have s\<^sub>1_u\<^sub>1: "?s\<^sub>1\<langle>?u\<^sub>1\<rangle>\<^sub>G = term.to_ground (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<mu> \<cdot>t\<^sub>c \<gamma>')\<langle>u\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<gamma>'\<rangle>"
      using context.ground_term_with_context(1)[OF
          context.is_ground_subst_is_ground
          term_subst.is_ground_subst_is_ground,
          OF ground_subst(1)[folded context.ground_subst_iff_base_ground_subst ] ground_subst(1) (* TODO *)
          ]
      by simp

    have s\<^sub>1_t\<^sub>2': "(?s\<^sub>1)\<langle>?t\<^sub>2'\<rangle>\<^sub>G  = term.to_ground (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<mu> \<cdot>t\<^sub>c \<gamma>')\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<gamma>'\<rangle>"
      using
        context.ground_term_with_context(1)[OF 
          context.is_ground_subst_is_ground
          term_subst.is_ground_subst_is_ground, 
          OF ground_subst(1)[folded context.ground_subst_iff_base_ground_subst ] ground_subst(2) (* TODO *)
          ]
      by auto

    have \<P>_pos_or_neg: "\<P> = Pos \<or> \<P> = Neg"
      using superpositionI(9) by blast

    then have L\<^sub>1: "?L\<^sub>1 = ?\<P> (Upair ?s\<^sub>1\<langle>?u\<^sub>1\<rangle>\<^sub>G ?s\<^sub>1')"
      using s\<^sub>1_u\<^sub>1
      unfolding superpositionI literal.to_ground_def atom.to_ground_def
      by auto

    have "literal.to_ground
         ((s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<mu> \<cdot>t\<^sub>c \<gamma>')\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<gamma>'\<rangle> \<approx> s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<gamma>') =
        term.to_ground (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<mu> \<cdot>t\<^sub>c \<gamma>')\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<gamma>'\<rangle> \<approx>
        term.to_ground (s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<gamma>')"
      by simp

    moreover have "literal.to_ground
         ((s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<mu> \<cdot>t\<^sub>c \<gamma>')\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<gamma>'\<rangle> !\<approx> s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<gamma>') =
        term.to_ground (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<mu> \<cdot>t\<^sub>c \<gamma>' )\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<gamma>'\<rangle> !\<approx>
        term.to_ground (s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<gamma>')"
      by simp

    ultimately have C: "?C = add_mset (?\<P> (Upair (?s\<^sub>1)\<langle>?t\<^sub>2'\<rangle>\<^sub>G (?s\<^sub>1'))) (?P\<^sub>1' + ?P\<^sub>2')"
      using \<P>_pos_or_neg
      unfolding
        s\<^sub>1_t\<^sub>2'
        superpositionI
        clause.to_ground_def
      by auto

    show "?I \<TTurnstile> clause.to_ground (C \<cdot> \<gamma>)"
    proof (cases "L\<^sub>1' = ?L\<^sub>1")
      case L\<^sub>1'_def: True
      then have "?I \<TTurnstile>l ?L\<^sub>1"
        using superpositionI
        using I_models_L\<^sub>1' by blast

      show ?thesis
      proof (cases "L\<^sub>2' = ?L\<^sub>2")
        case L\<^sub>2'_def: True

        then have ts_in_I: "(?t\<^sub>2, ?t\<^sub>2') \<in> I"
          using I_models_L\<^sub>2' true_lit_uprod_iff_true_lit_prod[OF sym_I] superpositionI(11)
          unfolding literal.to_ground_def  atom.to_ground_def  
          by (smt (verit) literal.simps(9) map_uprod_simps atom.subst_def subst_literal 
              true_lit_simps(1)) 

        have ?thesis if "\<P> = Pos"
        proof -
          from that have "(?s\<^sub>1\<langle>?t\<^sub>2\<rangle>\<^sub>G, ?s\<^sub>1') \<in> I"
            using I_models_L\<^sub>1' L\<^sub>1'_def L\<^sub>1 true_lit_uprod_iff_true_lit_prod[OF sym_I] u\<^sub>1_equals_t\<^sub>2
            unfolding superpositionI 
            by (smt (verit, best) true_lit_simps(1))

          then have "(?s\<^sub>1\<langle>?t\<^sub>2'\<rangle>\<^sub>G, ?s\<^sub>1') \<in> I"
            using ts_in_I compatible_with_ground_context_I refl_I sym_I trans_I
            by (meson compatible_with_gctxtD refl_onD1 symD trans_onD)

          then have "?I \<TTurnstile>l ?s\<^sub>1\<langle>?t\<^sub>2'\<rangle>\<^sub>G  \<approx> ?s\<^sub>1'"
            by blast

          then show ?thesis 
            unfolding C that
            by (smt (verit) C \<gamma>'(3) clause.subst_eq that true_cls_def union_single_eq_member)
        qed

        moreover have ?thesis if "\<P> = Neg"
        proof -
          from that have "(?s\<^sub>1\<langle>?t\<^sub>2\<rangle>\<^sub>G, ?s\<^sub>1') \<notin> I"
            using I_models_L\<^sub>1' L\<^sub>1'_def L\<^sub>1 true_lit_uprod_iff_true_lit_prod[OF sym_I] u\<^sub>1_equals_t\<^sub>2
            unfolding superpositionI 
            by (smt (verit, ccfv_threshold) literals_distinct(2) true_lit_simps(2))

          then have "(?s\<^sub>1\<langle>?t\<^sub>2'\<rangle>\<^sub>G, ?s\<^sub>1') \<notin> I"
            using ts_in_I compatible_with_ground_context_I trans_I
            by (meson compatible_with_gctxtD transD)

          then have "?I \<TTurnstile>l Neg (Upair ?s\<^sub>1\<langle>?t\<^sub>2'\<rangle>\<^sub>G  ?s\<^sub>1')"
            by (meson true_lit_uprod_iff_true_lit_prod(2) sym_I true_lit_simps(2))

          then show ?thesis 
            unfolding C that
            by (smt (verit, best) C \<gamma>'(3) calculation clause.subst_eq true_cls_def 
                union_single_eq_member)
        qed

        ultimately show ?thesis
          using \<P>_pos_or_neg by blast
      next
        case False
        then have "L\<^sub>2' \<in># ?P\<^sub>2'"
          using L\<^sub>2'_in_P2
          unfolding superpositionI
          by (simp add: clause.to_ground_def)

        then have "?I \<TTurnstile> ?P\<^sub>2'"
          using I_models_L\<^sub>2' by blast

        then show ?thesis
          unfolding superpositionI 
          by (smt (verit, ccfv_SIG) C \<gamma>'(3) clause.subst_eq local.superpositionI(26) true_cls_union
              union_mset_add_mset_left)
      qed
    next
      case False
      then have "L\<^sub>1' \<in># ?P\<^sub>1'"
        using L\<^sub>1'_in_P1
        unfolding superpositionI 
        by (simp add:  clause.to_ground_def)

      then have "?I \<TTurnstile> ?P\<^sub>1'"
        using I_models_L\<^sub>1' by blast

      then show ?thesis 
        unfolding superpositionI
        by (smt (verit, best) C \<gamma>'(3) clause.subst_eq local.superpositionI(26) true_cls_union 
            union_mset_add_mset_right)
    qed
  qed

  then show ?thesis 
    unfolding ground.G_entails_def clause_groundings_def true_clss_def superpositionI(1-3)
    by auto
qed

end

sublocale grounded_superposition_calculus \<subseteq> 
  sound_inference_system inferences "\<bottom>\<^sub>F" "(\<TTurnstile>\<^sub>F)"
proof unfold_locales
  fix \<iota>
  assume "\<iota> \<in> inferences"
  then show "set (prems_of \<iota>) \<TTurnstile>\<^sub>F {concl_of \<iota>}"
    using
      eq_factoring_sound
      eq_resolution_sound
      superposition_sound
    unfolding inferences_def ground.G_entails_def
    by auto
qed

sublocale superposition_calculus \<subseteq> sound_inference_system inferences "\<bottom>\<^sub>F" entails_\<G>
proof unfold_locales
  obtain select\<^sub>G where select\<^sub>G: "select\<^sub>G \<in> select\<^sub>G\<^sub>s"
    using Q_nonempty by blast

  then interpret grounded_superposition_calculus
    where select\<^sub>G = select\<^sub>G
    by unfold_locales (simp add: select\<^sub>G\<^sub>s_def)

  show "\<And>\<iota>. \<iota> \<in> inferences \<Longrightarrow> entails_\<G> (set (prems_of \<iota>)) {concl_of \<iota>}"
    using sound
    unfolding entails_def
    by blast
qed

end
