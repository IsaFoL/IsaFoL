theory First_Order_Superposition_Soundness
  imports Grounded_First_Order_Superposition

begin

subsection \<open>Soundness\<close>

context grounded_first_order_superposition_calculus
begin

abbreviation entails\<^sub>F (infix "\<TTurnstile>\<^sub>F" 50) where
  "entails\<^sub>F \<equiv> lifting.entails_\<G>"

lemma welltyped_extension:
  assumes "clause.is_ground (C \<cdot> \<gamma>)" "welltyped\<^sub>\<sigma>_on (clause.vars C) typeof_fun \<V> \<gamma>" 
  obtains \<gamma>'
  where 
    "term_subst.is_ground_subst \<gamma>'" 
    "welltyped\<^sub>\<sigma> typeof_fun \<V> \<gamma>'" 
    "\<forall>x \<in> clause.vars C. \<gamma> x = \<gamma>' x"
  using assms function_symbols
proof-
  define \<gamma>' where "\<And>x. \<gamma>' x \<equiv> 
    if x \<in> clause.vars C 
    then \<gamma> x else 
    Fun (SOME f. typeof_fun f = ([], \<V> x)) []"

  have "term_subst.is_ground_subst \<gamma>'"
    unfolding  term_subst.is_ground_subst_def
  proof(intro allI)
    fix t
    show "term.is_ground (t \<cdot>t \<gamma>')"
    proof(induction t)
      case (Var x)
      then show ?case
        using assms(1) 
        unfolding \<gamma>'_def  term_subst.is_ground_subst_def  is_ground_iff
        by(auto simp: clause.variable_grounding)
    next
      case Fun
      then show ?case
        by simp
    qed
  qed

  moreover have "welltyped\<^sub>\<sigma> typeof_fun \<V> \<gamma>'"
  proof-
    have "\<And>x. \<lbrakk>\<forall>x\<in>clause.vars C. First_Order_Type_System.welltyped typeof_fun \<V> (\<gamma> x) (\<V> x);
          \<And>\<tau>. \<exists>f. typeof_fun f = ([], \<tau>); x \<notin> clause.vars C\<rbrakk>
         \<Longrightarrow> First_Order_Type_System.welltyped typeof_fun \<V>
              (Fun (SOME f. typeof_fun f = ([], \<V> x)) []) (\<V> x)"
      by (meson First_Order_Type_System.welltyped.intros(2) list_all2_Nil someI_ex)

    then show ?thesis    
      using assms(2) function_symbols
      unfolding \<gamma>'_def welltyped\<^sub>\<sigma>_def welltyped\<^sub>\<sigma>_on_def
      by auto
  qed

  moreover have "\<forall>x \<in> clause.vars C. \<gamma> x = \<gamma>' x"
    unfolding \<gamma>'_def
    by auto

  ultimately show ?thesis
    using that
    by blast
qed

lemma vars_subst: "\<Union> (term.vars ` \<rho> ` term.vars t) = term.vars (t \<cdot>t \<rho>)"
  by(induction t) auto

lemma vars_subst\<^sub>a: "\<Union> (term.vars ` \<rho> ` atom.vars a) = atom.vars (a \<cdot>a \<rho>)"
  using vars_subst
  unfolding atom.vars_def atom.subst_def
  by (smt (verit) SUP_UNION Sup.SUP_cong UN_extend_simps(10) uprod.set_map)

lemma vars_subst\<^sub>l: "\<Union> (term.vars ` \<rho> ` literal.vars l) = literal.vars (l \<cdot>l \<rho>)"
  unfolding literal.vars_def literal.subst_def set_literal_atm_of
  by (metis (no_types, lifting) UN_insert Union_image_empty literal.map_sel vars_subst\<^sub>a)

lemma vars_subst\<^sub>c: "\<Union> (term.vars ` \<rho> ` clause.vars C) = clause.vars (C \<cdot> \<rho>)"
  using vars_subst\<^sub>l
  unfolding clause.vars_def clause.subst_def
  by fastforce

lemma eq_resolution_sound:
  assumes step: "eq_resolution P C"
  shows "{P} \<TTurnstile>\<^sub>F {C}"
  using step
proof (cases P C rule: eq_resolution.cases)
  case (eq_resolutionI P L P' s\<^sub>1 s\<^sub>2 \<mu> \<V> C)

  { 
    fix I :: "'f gterm rel" and \<gamma> :: "('f, 'v) subst"

    let ?I = "upair ` I"

    assume
      refl_I: "refl I" and 
      premise: 
      "\<forall>P\<^sub>G. (\<exists>\<gamma>'. P\<^sub>G = clause.to_ground (P \<cdot> \<gamma>') \<and> term_subst.is_ground_subst \<gamma>'
             \<and> welltyped\<^sub>c typeof_fun \<V> P \<and> welltyped\<^sub>\<sigma>_on (clause.vars P) typeof_fun \<V> \<gamma>') 
            \<longrightarrow> ?I \<TTurnstile> P\<^sub>G" and
      grounding: "term_subst.is_ground_subst \<gamma>" and
      wt: "welltyped\<^sub>c typeof_fun \<V> C" "welltyped\<^sub>\<sigma>_on (clause.vars C) typeof_fun \<V> \<gamma>"

    have grounding': "clause.is_ground (C \<cdot> \<gamma>)"
      using grounding
      by (simp add: clause.is_ground_subst_is_ground)

    obtain \<gamma>' where
      \<gamma>': "term_subst.is_ground_subst \<gamma>'" "welltyped\<^sub>\<sigma> typeof_fun \<V> \<gamma>'" 
      "\<forall>x \<in> clause.vars C. \<gamma> x = \<gamma>' x"
      using welltyped_extension[OF grounding' wt(2)].

    let ?P = "clause.to_ground (P \<cdot> \<mu> \<cdot> \<gamma>')"
    let ?L = "literal.to_ground (L \<cdot>l \<mu> \<cdot>l \<gamma>')"
    let ?P' = "clause.to_ground (P' \<cdot> \<mu> \<cdot> \<gamma>')"
    let ?s\<^sub>1 = "term.to_ground (s\<^sub>1 \<cdot>t \<mu> \<cdot>t \<gamma>')"
    let ?s\<^sub>2 = "term.to_ground (s\<^sub>2 \<cdot>t \<mu> \<cdot>t \<gamma>')"

    have "welltyped\<^sub>c typeof_fun \<V> (P' \<cdot> \<mu>)"
      using eq_resolutionI(8) wt(1)
      by blast

    moreover have welltyped_\<mu>: "welltyped\<^sub>\<sigma> typeof_fun \<V> \<mu>"
      using eq_resolutionI(6) wt(1)
      by auto

    ultimately have welltyped_P': "welltyped\<^sub>c typeof_fun \<V> P'"
      using welltyped\<^sub>\<sigma>_welltyped\<^sub>c
      by blast

    from welltyped_\<mu> have "welltyped\<^sub>\<sigma>_on (clause.vars C) typeof_fun \<V> (\<mu> \<odot> \<gamma>')"
      using \<gamma>'(2)
      by (simp add: subst_compose_def welltyped\<^sub>\<sigma>_def welltyped\<^sub>\<sigma>_on_def welltyped\<^sub>\<sigma>_welltyped)

    moreover have "welltyped\<^sub>c typeof_fun \<V> (add_mset (s\<^sub>1 !\<approx> s\<^sub>2) P')"
      using eq_resolutionI(6) welltyped_add_literal[OF welltyped_P'] wt(1)
      by auto

    ultimately have "?I \<TTurnstile> ?P"
      using premise[rule_format, of ?P, OF exI, of "\<mu> \<odot> \<gamma>'"] \<gamma>'(1) 
        term_subst.is_ground_subst_comp_right eq_resolutionI
      by (smt (verit, ccfv_threshold) \<gamma>'(2) clause.comp_subst.left.monoid_action_compatibility 
          subst_compose_def welltyped\<^sub>\<sigma>_def welltyped\<^sub>\<sigma>_on_def welltyped\<^sub>\<sigma>_welltyped)

    then obtain L' where L'_in_P: "L' \<in># ?P" and I_models_L': "?I \<TTurnstile>l L'"
      by (auto simp: true_cls_def)

    have [simp]: "?P = add_mset ?L ?P'"
      by (simp add: clause.to_ground_def eq_resolutionI(3) subst_clause_add_mset)

    have [simp]: "?L = (Neg (Upair ?s\<^sub>1 ?s\<^sub>2))"
      unfolding  eq_resolutionI(4) atom.to_ground_def literal.to_ground_def
      by clause_auto

    have [simp]: "?s\<^sub>1 = ?s\<^sub>2"
      using term_subst.subst_imgu_eq_subst_imgu[OF eq_resolutionI(5)] by simp

    have "is_neg ?L"
      by (simp add: literal.to_ground_def eq_resolutionI(4) subst_literal)

    have "?I \<TTurnstile> clause.to_ground (C \<cdot> \<gamma>)"
    proof(cases "L' = ?L")
      case True

      then have "?I \<TTurnstile>l (Neg (atm_of ?L))"
        using I_models_L' by simp

      moreover have "atm_of L' \<in> ?I"
        using True reflD[OF refl_I, of ?s\<^sub>1] by auto

      ultimately show ?thesis
        using True by blast
    next
      case False
      then have "L' \<in># clause.to_ground (P' \<cdot> \<mu> \<cdot> \<gamma>')"
        using L'_in_P by force

      then have "L' \<in># clause.to_ground (C \<cdot> \<gamma>')"
        unfolding eq_resolutionI.

      then show ?thesis
        using I_models_L' 
        by (metis \<gamma>'(3) clause.subst_eq true_cls_def)
    qed
  }

  then show ?thesis
    unfolding ground.G_entails_def true_clss_def clause_groundings_def
    using eq_resolutionI(1, 2) by auto
qed

lemma eq_factoring_sound:
  assumes step: "eq_factoring P C"
  shows "{P} \<TTurnstile>\<^sub>F {C}"
  using step
proof (cases P C rule: eq_factoring.cases)
  case (eq_factoringI P L\<^sub>1 L\<^sub>2 P' s\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu> \<V> C)

  have  
    "\<And>I \<gamma> \<F>\<^sub>G. \<lbrakk>
        trans I; 
        sym I;
        \<forall>P\<^sub>G. (\<exists>\<gamma>'. P\<^sub>G = clause.to_ground (P \<cdot> \<gamma>') \<and> term_subst.is_ground_subst \<gamma>'
              \<and> welltyped\<^sub>c typeof_fun \<V> P \<and> welltyped\<^sub>\<sigma>_on (clause.vars P) typeof_fun \<V> \<gamma>') 
            \<longrightarrow> upair ` I \<TTurnstile> P\<^sub>G; 
       term_subst.is_ground_subst \<gamma>;
       welltyped\<^sub>c typeof_fun \<V> C; welltyped\<^sub>\<sigma>_on (clause.vars C) typeof_fun \<V> \<gamma>
     \<rbrakk> \<Longrightarrow> upair  ` I \<TTurnstile> clause.to_ground (C \<cdot> \<gamma>)"
  proof-
    fix I :: "'f gterm rel" and \<gamma> :: "'v \<Rightarrow> ('f, 'v) Term.term"

    let ?I = "upair ` I"

    assume
      trans_I: "trans I" and 
      sym_I: "sym I" and 
      premise: 
      "\<forall>P\<^sub>G. (\<exists>\<gamma>'. P\<^sub>G = clause.to_ground (P \<cdot> \<gamma>') \<and> term_subst.is_ground_subst \<gamma>'
             \<and> welltyped\<^sub>c typeof_fun \<V> P \<and> welltyped\<^sub>\<sigma>_on (clause.vars P) typeof_fun \<V> \<gamma>') 
              \<longrightarrow> ?I \<TTurnstile> P\<^sub>G" and
      grounding: "term_subst.is_ground_subst \<gamma>" and
      wt: "welltyped\<^sub>c typeof_fun \<V> C" "welltyped\<^sub>\<sigma>_on (clause.vars C) typeof_fun \<V> \<gamma>"

    obtain \<gamma>' where
      \<gamma>': "term_subst.is_ground_subst \<gamma>'" "welltyped\<^sub>\<sigma> typeof_fun \<V> \<gamma>'" 
      "\<forall>x \<in> clause.vars C. \<gamma> x = \<gamma>' x"
      using welltyped_extension
      using grounding wt(2)
      by (smt (verit, ccfv_threshold) clause.ground_subst_iff_base_ground_subst 
          clause.is_ground_subst_is_ground)

    let ?P = "clause.to_ground (P \<cdot> \<mu> \<cdot> \<gamma>')"
    let ?P' = "clause.to_ground (P' \<cdot> \<mu> \<cdot> \<gamma>')"
    let ?L\<^sub>1 = "literal.to_ground (L\<^sub>1 \<cdot>l \<mu> \<cdot>l \<gamma>')"
    let ?L\<^sub>2 = "literal.to_ground (L\<^sub>2 \<cdot>l \<mu> \<cdot>l \<gamma>')"
    let ?s\<^sub>1 = "term.to_ground (s\<^sub>1 \<cdot>t \<mu> \<cdot>t \<gamma>')"
    let ?s\<^sub>1' = "term.to_ground (s\<^sub>1' \<cdot>t \<mu> \<cdot>t \<gamma>')"
    let ?t\<^sub>2 = "term.to_ground (t\<^sub>2 \<cdot>t \<mu> \<cdot>t \<gamma>')"
    let ?t\<^sub>2' = "term.to_ground (t\<^sub>2' \<cdot>t \<mu> \<cdot>t \<gamma>')"
    let ?C = "clause.to_ground (C \<cdot> \<gamma>')"

    have wt':
      "welltyped\<^sub>c typeof_fun \<V> (P' \<cdot> \<mu>)" 
      "welltyped\<^sub>l typeof_fun \<V> (s\<^sub>1 \<approx> t\<^sub>2' \<cdot>l \<mu>)" 
      "welltyped\<^sub>l typeof_fun \<V> (s\<^sub>1' !\<approx> t\<^sub>2' \<cdot>l \<mu>)"
      using wt(1)
      unfolding eq_factoringI(11) welltyped\<^sub>c_add_mset subst_clause_add_mset
      by auto

    moreover have welltyped_\<mu>: "welltyped\<^sub>\<sigma> typeof_fun \<V> \<mu>"
      using eq_factoringI(10) wt(1)
      by blast

    ultimately have welltyped_P': "welltyped\<^sub>c typeof_fun \<V> P'"
      using welltyped\<^sub>\<sigma>_welltyped\<^sub>c
      by blast

    have xx: "welltyped\<^sub>l typeof_fun \<V> (s\<^sub>1 \<approx> t\<^sub>2')" "welltyped\<^sub>l typeof_fun \<V> (s\<^sub>1' !\<approx> t\<^sub>2')"
      using wt'(2, 3) welltyped\<^sub>\<sigma>_welltyped\<^sub>l[OF welltyped_\<mu>]
      by auto

    then have welltyped_L\<^sub>1: "welltyped\<^sub>l typeof_fun \<V> (s\<^sub>1 \<approx> s\<^sub>1')"
      unfolding welltyped\<^sub>l_def welltyped\<^sub>a_def
      using right_uniqueD[OF welltyped_right_unique] 
      by (smt (verit, best) insert_iff set_uprod_simps literal.sel)

    have welltyped_L\<^sub>2: "welltyped\<^sub>l typeof_fun \<V> (t\<^sub>2 \<approx> t\<^sub>2')"
      using xx right_uniqueD[OF welltyped_right_unique] eq_factoringI(10) wt(1)
      unfolding welltyped\<^sub>l_def welltyped\<^sub>a_def
      by (smt (verit) insert_iff set_uprod_simps literal.sel(1))

    from welltyped_\<mu> have "welltyped\<^sub>\<sigma> typeof_fun \<V> (\<mu> \<odot> \<gamma>')"
      using wt(2) \<gamma>'
      by (simp add: subst_compose_def welltyped\<^sub>\<sigma>_def welltyped\<^sub>\<sigma>_welltyped)

    moreover have "welltyped\<^sub>c typeof_fun \<V> P"
      unfolding eq_factoringI welltyped\<^sub>c_add_mset
      using welltyped_P'  welltyped_L\<^sub>1 welltyped_L\<^sub>2
      by blast

    ultimately have "?I \<TTurnstile> ?P"
      using 
        premise[rule_format, of ?P, OF exI, of "\<mu> \<odot> \<gamma>'"] 
        term_subst.is_ground_subst_comp_right \<gamma>'(1)
      by (metis clause.subst_comp_subst welltyped\<^sub>\<sigma>_def welltyped\<^sub>\<sigma>_on_def)

    then obtain L' where L'_in_P: "L' \<in># ?P" and I_models_L': "?I \<TTurnstile>l L'"
      by (auto simp: true_cls_def)

    then have s\<^sub>1_equals_t\<^sub>2: "?t\<^sub>2 = ?s\<^sub>1"
      using term_subst.subst_imgu_eq_subst_imgu[OF eq_factoringI(9)]
      by simp

    have L\<^sub>1: "?L\<^sub>1 = ?s\<^sub>1 \<approx> ?s\<^sub>1'"
      unfolding literal.to_ground_def eq_factoringI(4) atom.to_ground_def
      by (simp add: atom.subst_def subst_literal)

    have L\<^sub>2: "?L\<^sub>2 = ?t\<^sub>2 \<approx> ?t\<^sub>2'"
      unfolding literal.to_ground_def eq_factoringI(5) atom.to_ground_def
      by (simp add: atom.subst_def subst_literal)

    have C: "?C = add_mset (?s\<^sub>1 \<approx> ?t\<^sub>2') (add_mset (Neg (Upair ?s\<^sub>1' ?t\<^sub>2')) ?P')"
      unfolding eq_factoringI 
      by (simp add: clause.to_ground_def literal.to_ground_def atom.subst_def subst_clause_add_mset 
          subst_literal atom.to_ground_def)

    show "?I \<TTurnstile> clause.to_ground (C \<cdot> \<gamma>)"
    proof(cases "L' = ?L\<^sub>1 \<or> L' = ?L\<^sub>2")
      case True

      then have "I \<TTurnstile>l Pos (?s\<^sub>1, ?s\<^sub>1') \<or> I \<TTurnstile>l Pos (?s\<^sub>1, ?t\<^sub>2')"
        using true_lit_uprod_iff_true_lit_prod[OF sym_I] I_models_L'
        by (metis L\<^sub>1 L\<^sub>2 s\<^sub>1_equals_t\<^sub>2)

      then have "I \<TTurnstile>l Pos (?s\<^sub>1, ?t\<^sub>2') \<or> I \<TTurnstile>l Neg (?s\<^sub>1', ?t\<^sub>2')"
        by (meson transD trans_I true_lit_simps(1) true_lit_simps(2))

      then have "?I \<TTurnstile>l ?s\<^sub>1 \<approx> ?t\<^sub>2' \<or> ?I \<TTurnstile>l Neg (Upair ?s\<^sub>1' ?t\<^sub>2')"
        unfolding true_lit_uprod_iff_true_lit_prod[OF sym_I].

      then show ?thesis
        using clause.subst_eq \<gamma>'(3) C
        by (smt (verit, best) true_cls_add_mset)
    next
      case False
      then have "L' \<in># ?P'"
        using L'_in_P
        unfolding eq_factoringI
        by (simp add: clause.to_ground_def subst_clause_add_mset)

      then have "L' \<in># clause.to_ground (C \<cdot> \<gamma>)"
        using clause.subst_eq \<gamma>'(3) C
        by fastforce

      then show ?thesis
        using I_models_L' by blast
    qed
  qed

  then show ?thesis
    unfolding ground.G_entails_def true_clss_def clause_groundings_def
    using eq_factoringI(1,2) by auto
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
        \<forall>P\<^sub>G. (\<exists>\<gamma>'. P\<^sub>G = clause.to_ground (P\<^sub>1 \<cdot> \<gamma>') \<and> term_subst.is_ground_subst \<gamma>' \<and> 
              welltyped\<^sub>c typeof_fun \<V>\<^sub>1 P\<^sub>1 \<and> welltyped\<^sub>\<sigma>_on (clause.vars P\<^sub>1) typeof_fun \<V>\<^sub>1 \<gamma>' \<and> 
              all_types \<V>\<^sub>1) \<longrightarrow> upair ` I \<TTurnstile> P\<^sub>G;
        \<forall>P\<^sub>G. (\<exists>\<gamma>'. P\<^sub>G = clause.to_ground (P\<^sub>2 \<cdot> \<gamma>') \<and> term_subst.is_ground_subst \<gamma>' \<and> 
              welltyped\<^sub>c typeof_fun \<V>\<^sub>2 P\<^sub>2 \<and> welltyped\<^sub>\<sigma>_on (clause.vars P\<^sub>2) typeof_fun \<V>\<^sub>2 \<gamma>' \<and> 
              all_types \<V>\<^sub>2) \<longrightarrow> upair ` I \<TTurnstile> P\<^sub>G;
        term_subst.is_ground_subst \<gamma>; welltyped\<^sub>c typeof_fun \<V>\<^sub>3 C; 
        welltyped\<^sub>\<sigma>_on (clause.vars C) typeof_fun \<V>\<^sub>3 \<gamma>; all_types \<V>\<^sub>3
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
      "\<forall>P\<^sub>G. (\<exists>\<gamma>'. P\<^sub>G = clause.to_ground (P\<^sub>1 \<cdot> \<gamma>') \<and> term_subst.is_ground_subst \<gamma>' 
              \<and> welltyped\<^sub>c typeof_fun \<V>\<^sub>1 P\<^sub>1 \<and> welltyped\<^sub>\<sigma>_on (clause.vars P\<^sub>1) typeof_fun \<V>\<^sub>1 \<gamma>' 
              \<and> all_types \<V>\<^sub>1) \<longrightarrow>?I \<TTurnstile> P\<^sub>G" and
      premise2: 
      "\<forall>P\<^sub>G. (\<exists>\<gamma>'. P\<^sub>G = clause.to_ground (P\<^sub>2 \<cdot> \<gamma>') \<and> term_subst.is_ground_subst \<gamma>' 
              \<and> welltyped\<^sub>c typeof_fun \<V>\<^sub>2 P\<^sub>2 \<and> welltyped\<^sub>\<sigma>_on (clause.vars P\<^sub>2) typeof_fun \<V>\<^sub>2 \<gamma>'
              \<and> all_types \<V>\<^sub>2) \<longrightarrow> ?I \<TTurnstile> P\<^sub>G" and 
      grounding: "term_subst.is_ground_subst \<gamma>" "welltyped\<^sub>c typeof_fun \<V>\<^sub>3 C" 
      "welltyped\<^sub>\<sigma>_on (clause.vars C) typeof_fun \<V>\<^sub>3 \<gamma>" "all_types \<V>\<^sub>3"

    have grounding': "clause.is_ground (C \<cdot> \<gamma>)"
      using grounding
      by (simp add: clause.is_ground_subst_is_ground)

    obtain \<gamma>' where
      \<gamma>': "term_subst.is_ground_subst \<gamma>'" "welltyped\<^sub>\<sigma> typeof_fun \<V>\<^sub>3 \<gamma>'" 
      "\<forall>x \<in> clause.vars C. \<gamma> x = \<gamma>' x"
      using welltyped_extension[OF grounding' grounding(3)].

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

    have xx: "\<forall>x\<in>term.vars (t\<^sub>2 \<cdot>t \<rho>\<^sub>2). \<V>\<^sub>2 (the_inv \<rho>\<^sub>2 (Var x)) = \<V>\<^sub>3 x" 
      "\<forall>x\<in>term.vars (t\<^sub>2' \<cdot>t \<rho>\<^sub>2). \<V>\<^sub>2 (the_inv \<rho>\<^sub>2 (Var x)) = \<V>\<^sub>3 x"
      using superpositionI(16)
      by (simp_all add: clause.vars_def local.superpositionI(11) local.superpositionI(8) 
          subst_atom subst_clause_add_mset subst_literal(1) vars_atom vars_literal(1))

    have wt_t: "\<exists>\<tau>. welltyped typeof_fun \<V>\<^sub>3 (t\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<tau> \<and> welltyped typeof_fun \<V>\<^sub>3 (t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu>) \<tau>"
    proof-
      have " \<And>\<tau> \<tau>'.
       \<lbrakk>\<And>\<tau> \<tau>'.
           \<lbrakk>has_type typeof_fun \<V>\<^sub>3 (t\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<tau>; has_type typeof_fun \<V>\<^sub>3 (t\<^sub>2' \<cdot>t \<rho>\<^sub>2) \<tau>'\<rbrakk> \<Longrightarrow> \<tau> = \<tau>';
        \<forall>L\<in>#(P\<^sub>1' \<cdot> \<rho>\<^sub>1 + P\<^sub>2' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu>.
           \<exists>\<tau>. \<forall>t\<in>set_uprod (atm_of L). First_Order_Type_System.welltyped typeof_fun \<V>\<^sub>3 t \<tau>;
        First_Order_Type_System.welltyped typeof_fun \<V>\<^sub>3 (u\<^sub>1 \<cdot>t \<rho>\<^sub>1) \<tau>;
        First_Order_Type_System.welltyped typeof_fun \<V>\<^sub>3 (t\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<tau>; welltyped\<^sub>\<sigma> typeof_fun \<V>\<^sub>3 \<mu>;
        \<P> = Pos;
        First_Order_Type_System.welltyped typeof_fun \<V>\<^sub>3
         (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<mu>)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu>\<rangle> \<tau>';
        First_Order_Type_System.welltyped typeof_fun \<V>\<^sub>3 (s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu>) \<tau>'\<rbrakk>
       \<Longrightarrow> \<exists>\<tau>. First_Order_Type_System.welltyped typeof_fun \<V>\<^sub>3 (t\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<tau> \<and>
               First_Order_Type_System.welltyped typeof_fun \<V>\<^sub>3 (t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu>) \<tau>"
        "\<And>\<tau> \<tau>'.
       \<lbrakk>\<And>\<tau> \<tau>'.
           \<lbrakk>has_type typeof_fun \<V>\<^sub>3 (t\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<tau>; has_type typeof_fun \<V>\<^sub>3 (t\<^sub>2' \<cdot>t \<rho>\<^sub>2) \<tau>'\<rbrakk> \<Longrightarrow> \<tau> = \<tau>';
        \<forall>L\<in>#(P\<^sub>1' \<cdot> \<rho>\<^sub>1 + P\<^sub>2' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu>.
           \<exists>\<tau>. \<forall>t\<in>set_uprod (atm_of L). First_Order_Type_System.welltyped typeof_fun \<V>\<^sub>3 t \<tau>;
        First_Order_Type_System.welltyped typeof_fun \<V>\<^sub>3 (u\<^sub>1 \<cdot>t \<rho>\<^sub>1) \<tau>;
        First_Order_Type_System.welltyped typeof_fun \<V>\<^sub>3 (t\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<tau>; welltyped\<^sub>\<sigma> typeof_fun \<V>\<^sub>3 \<mu>;
        \<P> = Neg;
        First_Order_Type_System.welltyped typeof_fun \<V>\<^sub>3 (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<mu>)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu>\<rangle> \<tau>';
        First_Order_Type_System.welltyped typeof_fun \<V>\<^sub>3 (s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu>) \<tau>'\<rbrakk>
       \<Longrightarrow> \<exists>\<tau>. First_Order_Type_System.welltyped typeof_fun \<V>\<^sub>3 (t\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<tau> \<and>
               First_Order_Type_System.welltyped typeof_fun \<V>\<^sub>3 (t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu>) \<tau>"
        by (metis welltyped\<^sub>\<kappa>' welltyped\<^sub>\<sigma>_welltyped welltyped_has_type)+

      then show ?thesis
        using grounding(2) superpositionI(9, 14, 19)
        unfolding superpositionI welltyped\<^sub>c_def welltyped\<^sub>l_def welltyped\<^sub>a_def subst_clause_add_mset
        unfolding xx[THEN has_type_renaming_weaker[OF superpositionI(5)]] 
        by(auto simp: welltyped\<^sub>\<kappa>' subst_literal subst_atom)
    qed

    have wt_P\<^sub>1: "welltyped\<^sub>c typeof_fun \<V>\<^sub>1 P\<^sub>1" 
    proof-
      have xx: "\<forall>x\<in>clause.vars (P\<^sub>1' \<cdot> \<rho>\<^sub>1). \<V>\<^sub>1 (the_inv \<rho>\<^sub>1 (Var x)) = \<V>\<^sub>3 x"
        using superpositionI(15)
        unfolding superpositionI subst_clause_add_mset
        by clause_simp

      have wt_P\<^sub>1': "welltyped\<^sub>c typeof_fun \<V>\<^sub>1 P\<^sub>1'"
      proof-
        have "\<lbrakk>welltyped\<^sub>l typeof_fun \<V>\<^sub>3 (\<P> (Upair (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> (s\<^sub>1' \<cdot>t \<rho>\<^sub>1)) \<cdot>l \<mu>);
             welltyped\<^sub>c typeof_fun \<V>\<^sub>3 (P\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>);
             welltyped\<^sub>c typeof_fun \<V>\<^sub>3 (P\<^sub>2' \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>)\<rbrakk>
             \<Longrightarrow> welltyped\<^sub>c typeof_fun \<V>\<^sub>1 P\<^sub>1'"
          unfolding welltyped\<^sub>c_renaming_weaker[OF superpositionI(4) xx] 
          using superpositionI(14) welltyped\<^sub>\<sigma>_welltyped\<^sub>c 
          by blast

        then show ?thesis
          using grounding(2)
          unfolding superpositionI subst_clause_add_mset subst_clause_plus welltyped\<^sub>c_add_mset 
            welltyped\<^sub>c_plus
          by auto
      qed

      from wt_t have x1:
        "\<exists>\<tau>. welltyped typeof_fun \<V>\<^sub>3 (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>u\<^sub>1 \<cdot>t \<rho>\<^sub>1\<rangle> \<tau> \<and> welltyped typeof_fun \<V>\<^sub>3 (s\<^sub>1' \<cdot>t \<rho>\<^sub>1) \<tau>"
      proof-
        have "\<exists>\<tau>. welltyped typeof_fun \<V>\<^sub>3 (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<mu>)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu>\<rangle> \<tau> \<and>
               welltyped typeof_fun \<V>\<^sub>3 (s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu>) \<tau>"
          using grounding(2) superpositionI(9, 14, 15) 
          unfolding superpositionI welltyped\<^sub>c_def welltyped\<^sub>l_def welltyped\<^sub>a_def
          by clause_auto

        then have "\<exists>\<tau>. welltyped typeof_fun \<V>\<^sub>3 (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<mu>)\<langle>u\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu>\<rangle> \<tau> \<and>
               welltyped typeof_fun \<V>\<^sub>3 (s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu>) \<tau>"
          by (meson local.superpositionI(14) welltyped\<^sub>\<kappa> welltyped\<^sub>\<sigma>_welltyped wt_t)

        then show ?thesis
          by (metis local.superpositionI(14) subst_apply_term_ctxt_apply_distrib 
              welltyped\<^sub>\<sigma>_welltyped)
      qed

      then have "\<exists>\<tau>. welltyped typeof_fun \<V>\<^sub>1 s\<^sub>1\<langle>u\<^sub>1\<rangle> \<tau> \<and> welltyped typeof_fun \<V>\<^sub>1 s\<^sub>1' \<tau>"
      proof-
        have x1': " \<And>\<tau>. \<lbrakk>\<forall>x\<in>literal.vars ((s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>u\<^sub>1 \<cdot>t \<rho>\<^sub>1\<rangle> \<approx> s\<^sub>1' \<cdot>t \<rho>\<^sub>1) \<union> clause.vars (P\<^sub>1' \<cdot> \<rho>\<^sub>1).
             \<V>\<^sub>1 (the_inv \<rho>\<^sub>1 (Var x)) = \<V>\<^sub>3 x;
          \<And>t \<V> \<V>' \<F> \<tau>.
             \<forall>x\<in>term.vars (t \<cdot>t \<rho>\<^sub>1). \<V> (the_inv \<rho>\<^sub>1 (Var x)) = \<V>' x \<Longrightarrow>
             First_Order_Type_System.welltyped \<F> \<V> t \<tau> =
             First_Order_Type_System.welltyped \<F> \<V>' (t \<cdot>t \<rho>\<^sub>1) \<tau>;
          First_Order_Type_System.welltyped typeof_fun \<V>\<^sub>3 (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>u\<^sub>1 \<cdot>t \<rho>\<^sub>1\<rangle> \<tau>;
          First_Order_Type_System.welltyped typeof_fun \<V>\<^sub>3 (s\<^sub>1' \<cdot>t \<rho>\<^sub>1) \<tau>; \<P> = Pos\<rbrakk>
         \<Longrightarrow> \<exists>\<tau>. First_Order_Type_System.welltyped typeof_fun \<V>\<^sub>1 s\<^sub>1\<langle>u\<^sub>1\<rangle> \<tau> \<and>
                 First_Order_Type_System.welltyped typeof_fun \<V>\<^sub>1 s\<^sub>1' \<tau>"
          "\<And>\<tau>. \<lbrakk>\<forall>x\<in>literal.vars ((s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>u\<^sub>1 \<cdot>t \<rho>\<^sub>1\<rangle> !\<approx> s\<^sub>1' \<cdot>t \<rho>\<^sub>1) \<union> clause.vars (P\<^sub>1' \<cdot> \<rho>\<^sub>1).
             \<V>\<^sub>1 (the_inv \<rho>\<^sub>1 (Var x)) = \<V>\<^sub>3 x;
          \<And>t \<V> \<V>' \<F> \<tau>.
             \<forall>x\<in>term.vars (t \<cdot>t \<rho>\<^sub>1). \<V> (the_inv \<rho>\<^sub>1 (Var x)) = \<V>' x \<Longrightarrow>
             First_Order_Type_System.welltyped \<F> \<V> t \<tau> =
             First_Order_Type_System.welltyped \<F> \<V>' (t \<cdot>t \<rho>\<^sub>1) \<tau>;
          First_Order_Type_System.welltyped typeof_fun \<V>\<^sub>3 (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>u\<^sub>1 \<cdot>t \<rho>\<^sub>1\<rangle> \<tau>;
          First_Order_Type_System.welltyped typeof_fun \<V>\<^sub>3 (s\<^sub>1' \<cdot>t \<rho>\<^sub>1) \<tau>; \<P> = Neg\<rbrakk>
         \<Longrightarrow> \<exists>\<tau>. First_Order_Type_System.welltyped typeof_fun \<V>\<^sub>1 s\<^sub>1\<langle>u\<^sub>1\<rangle> \<tau> \<and>
                 First_Order_Type_System.welltyped typeof_fun \<V>\<^sub>1 s\<^sub>1' \<tau>"
          by clause_simp (metis (mono_tags) Un_iff welltyped_renaming_weaker[OF superpositionI(4)] 
              subst_apply_term_ctxt_apply_distrib vars_term_ctxt_apply)+

        with x1 show ?thesis
          using superpositionI(15)  superpositionI(9) 
            welltyped_renaming_weaker[OF superpositionI(4)] 
          unfolding superpositionI subst_clause_add_mset vars_clause_add_mset
          by(auto simp: welltyped\<^sub>\<kappa>' subst_literal subst_atom)
      qed

      then show ?thesis
        using grounding(2) superpositionI(9, 14) wt_P\<^sub>1'
        unfolding superpositionI welltyped\<^sub>c_def welltyped\<^sub>l_def welltyped\<^sub>a_def subst_clause_add_mset 
          subst_clause_plus
        by auto
    qed

    have wt_P\<^sub>2: "welltyped\<^sub>c typeof_fun \<V>\<^sub>2 P\<^sub>2"
    proof-
      have xx: "\<forall>x\<in>clause.vars (P\<^sub>2' \<cdot> \<rho>\<^sub>2). \<V>\<^sub>2 (the_inv \<rho>\<^sub>2 (Var x)) = \<V>\<^sub>3 x"
        using superpositionI(16)
        unfolding superpositionI subst_clause_add_mset
        by clause_simp

      have wt_P\<^sub>2': "welltyped\<^sub>c typeof_fun \<V>\<^sub>2 P\<^sub>2'"
        using grounding(2)
        unfolding superpositionI subst_clause_add_mset subst_clause_plus welltyped\<^sub>c_add_mset 
          welltyped\<^sub>c_plus welltyped\<^sub>c_renaming_weaker[OF superpositionI(5) xx] 
        using superpositionI(14) welltyped\<^sub>\<sigma>_welltyped\<^sub>c by blast

      have tt: "\<exists>\<tau>. welltyped typeof_fun \<V>\<^sub>3 (t\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<tau> \<and> welltyped typeof_fun \<V>\<^sub>3 (t\<^sub>2' \<cdot>t \<rho>\<^sub>2) \<tau>"
        using wt_t
        by (meson superpositionI(14) welltyped\<^sub>\<sigma>_welltyped)

      show ?thesis
      proof-
        have "\<exists>\<tau>. welltyped typeof_fun \<V>\<^sub>2 t\<^sub>2 \<tau> \<and> welltyped typeof_fun \<V>\<^sub>2 t\<^sub>2' \<tau>"
          using superpositionI(16) welltyped_renaming_weaker[OF superpositionI(5)]
          unfolding superpositionI
          by (metis (no_types, lifting) Un_iff subst_atom subst_clause_add_mset subst_literal(1) tt 
              vars_atom vars_clause_add_mset vars_literal(1))

        with wt_P\<^sub>2' show ?thesis
          unfolding welltyped\<^sub>c_def welltyped\<^sub>l_def welltyped\<^sub>a_def  superpositionI
          by auto
      qed
    qed

    have wt_\<mu>_\<gamma>: "welltyped\<^sub>\<sigma> typeof_fun \<V>\<^sub>3 (\<mu> \<odot> \<gamma>')"
      by (metis \<gamma>'(2) local.superpositionI(14) subst_compose_def welltyped\<^sub>\<sigma>_def 
          welltyped\<^sub>\<sigma>_welltyped)

    have wt_\<gamma>: "welltyped\<^sub>\<sigma>_on  (clause.vars P\<^sub>1) typeof_fun \<V>\<^sub>1 (\<rho>\<^sub>1 \<odot> \<mu> \<odot> \<gamma>')" 
      "welltyped\<^sub>\<sigma>_on (clause.vars P\<^sub>2) typeof_fun \<V>\<^sub>2 (\<rho>\<^sub>2 \<odot>  \<mu> \<odot> \<gamma>')"
      using
        superpositionI(15, 16)
        welltyped\<^sub>\<sigma>_renaming_ground_subst_weaker[OF superpositionI(4) wt_\<mu>_\<gamma> superpositionI(17) 
          ground_subst(3)]
        welltyped\<^sub>\<sigma>_renaming_ground_subst_weaker[OF superpositionI(5) wt_\<mu>_\<gamma> superpositionI(18)
          ground_subst(3)]
      unfolding vars_subst\<^sub>c
      by (simp_all add: subst_compose_assoc)

    have "?I \<TTurnstile> ?P\<^sub>1"
      using premise1[rule_format, of ?P\<^sub>1, OF exI, of "\<rho>\<^sub>1 \<odot> \<mu> \<odot> \<gamma>'"] ground_subst wt_P\<^sub>1 wt_\<gamma> 
        superpositionI(27)
      by auto

    moreover have "?I \<TTurnstile> ?P\<^sub>2"
      using premise2[rule_format, of ?P\<^sub>2, OF exI, of "\<rho>\<^sub>2 \<odot> \<mu> \<odot> \<gamma>'"] ground_subst wt_P\<^sub>2 wt_\<gamma> 
        superpositionI(28)
      by auto

    ultimately obtain L\<^sub>1' L\<^sub>2' 
      where
        L\<^sub>1'_in_P1: "L\<^sub>1' \<in># ?P\<^sub>1" and 
        I_models_L\<^sub>1': "?I \<TTurnstile>l L\<^sub>1'" and
        L\<^sub>2'_in_P2: "L\<^sub>2' \<in># ?P\<^sub>2" and 
        I_models_L\<^sub>2': "?I \<TTurnstile>l L\<^sub>2'"
      by (auto simp: true_cls_def)

    have u\<^sub>1_equals_t\<^sub>2: "?t\<^sub>2 = ?u\<^sub>1"
      using term_subst.subst_imgu_eq_subst_imgu[OF superpositionI(13)]
      by argo

    have s\<^sub>1_u\<^sub>1: "?s\<^sub>1\<langle>?u\<^sub>1\<rangle>\<^sub>G = term.to_ground (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<mu> \<cdot>t\<^sub>c \<gamma>')\<langle>u\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<gamma>'\<rangle>"
      using 
        ground_term_with_context(1)[OF 
          context.is_ground_subst_is_ground
          term_subst.is_ground_subst_is_ground
          ]
        \<gamma>'(1)
      by auto

    have s\<^sub>1_t\<^sub>2': "(?s\<^sub>1)\<langle>?t\<^sub>2'\<rangle>\<^sub>G  = term.to_ground (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<mu> \<cdot>t\<^sub>c \<gamma>')\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<gamma>'\<rangle>"
      using 
        ground_term_with_context(1)[OF 
          context.is_ground_subst_is_ground
          term_subst.is_ground_subst_is_ground
          ]
        \<gamma>'(1) 
      by auto

    have \<P>_pos_or_neg: "\<P> = Pos \<or> \<P> = Neg"
      using superpositionI(9) by blast

    then have L\<^sub>1: "?L\<^sub>1 = ?\<P> (Upair ?s\<^sub>1\<langle>?u\<^sub>1\<rangle>\<^sub>G ?s\<^sub>1')"
      using s\<^sub>1_u\<^sub>1
      unfolding superpositionI literal.to_ground_def atom.to_ground_def
      by clause_auto   

    have "literal.to_ground
         ((s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<mu> \<cdot>t\<^sub>c \<gamma>')\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<gamma>'\<rangle> \<approx> s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<gamma>') =
        term.to_ground (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<mu> \<cdot>t\<^sub>c \<gamma>')\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<gamma>'\<rangle> \<approx>
        term.to_ground (s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<gamma>')"
      by (metis atom.to_ground_def ground_atom_in_ground_literal(1) map_uprod_simps)

    moreover have "literal.to_ground
         ((s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<mu> \<cdot>t\<^sub>c \<gamma>')\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<gamma>'\<rangle> !\<approx> s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<gamma>') =
        term.to_ground (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<mu> \<cdot>t\<^sub>c \<gamma>' )\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<gamma>'\<rangle> !\<approx>
        term.to_ground (s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<gamma>')"
      by (metis atom.to_ground_def ground_atom_in_ground_literal(2) map_uprod_simps)

    ultimately have C: "?C = add_mset (?\<P> (Upair (?s\<^sub>1)\<langle>?t\<^sub>2'\<rangle>\<^sub>G (?s\<^sub>1'))) (?P\<^sub>1' + ?P\<^sub>2')"
      using \<P>_pos_or_neg
      unfolding 
        s\<^sub>1_t\<^sub>2' 
        superpositionI 
        clause.to_ground_def 
        subst_clause_add_mset 
        subst_clause_plus 
      by (auto simp: subst_atom subst_literal)

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
          by (simp add:  clause.to_ground_def subst_clause_add_mset)

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
        by (simp add:  clause.to_ground_def  subst_clause_add_mset)

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

sublocale grounded_first_order_superposition_calculus \<subseteq> 
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

sublocale first_order_superposition_calculus \<subseteq> 
  sound_inference_system inferences "\<bottom>\<^sub>F" entails_\<G>
proof unfold_locales
  obtain select\<^sub>G where select\<^sub>G: "select\<^sub>G \<in> select\<^sub>G\<^sub>s"
    using Q_nonempty by blast

  then interpret grounded_first_order_superposition_calculus
    where select\<^sub>G = select\<^sub>G
    by unfold_locales (simp add: select\<^sub>G\<^sub>s_def)

  show "\<And>\<iota>. \<iota> \<in> inferences \<Longrightarrow> entails_\<G> (set (prems_of \<iota>)) {concl_of \<iota>}"
    using sound
    unfolding entails_def
    by blast
qed

end
