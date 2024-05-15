theory First_Order_Superposition_Soundness
  imports Grounded_First_Order_Superposition
    
begin

subsection \<open>Soundness\<close>

context grounded_first_order_superposition_calculus
begin

(* TODO : Find way to use this abbrev for both entails_\<G> *)
abbreviation entails\<^sub>F (infix "\<TTurnstile>\<^sub>F" 50) where
  "entails\<^sub>F \<equiv> lifting.entails_\<G>"

lemma eq_resolution_sound:
  assumes step: "eq_resolution P C"
  shows "{P} \<TTurnstile>\<^sub>F {C}"
  using step
proof (cases P C rule: eq_resolution.cases)
  case (eq_resolutionI P L P' s\<^sub>1 s\<^sub>2 \<mu> \<V> C)

  have 
    "\<And>I \<gamma> \<F>\<^sub>G. \<lbrakk>
        refl I; 
        \<forall>P\<^sub>G. (\<exists>\<gamma>'. P\<^sub>G = to_ground_clause (P \<cdot> \<gamma>') \<and> term_subst.is_ground_subst \<gamma>'
              \<and> welltyped\<^sub>c typeof_fun \<V> P \<and> (\<exists>\<F>\<^sub>G. welltyped\<^sub>\<sigma> \<F>\<^sub>G \<V> \<gamma>' \<and> typeof_fun \<subseteq>\<^sub>m \<F>\<^sub>G)) 
            \<longrightarrow> upair ` I \<TTurnstile> P\<^sub>G; 
       term_subst.is_ground_subst \<gamma>;
       welltyped\<^sub>c typeof_fun \<V> C; welltyped\<^sub>\<sigma> \<F>\<^sub>G \<V> \<gamma>; typeof_fun \<subseteq>\<^sub>m \<F>\<^sub>G
     \<rbrakk> \<Longrightarrow> upair  ` I \<TTurnstile> to_ground_clause (C \<cdot> \<gamma>)"
   proof-
    fix I :: "'f gterm rel" and \<gamma> :: "('f, 'v) subst" and \<F>\<^sub>G
    
    let ?I = "upair ` I"
    
    assume
     refl_I: "refl I" and 
     premise: 
      "\<forall>P\<^sub>G. (\<exists>\<gamma>'. P\<^sub>G = to_ground_clause (P \<cdot> \<gamma>') \<and> term_subst.is_ground_subst \<gamma>'
             \<and> welltyped\<^sub>c typeof_fun \<V> P \<and> (\<exists>\<F>\<^sub>G. welltyped\<^sub>\<sigma> \<F>\<^sub>G \<V> \<gamma>' \<and> typeof_fun \<subseteq>\<^sub>m \<F>\<^sub>G)) \<longrightarrow> ?I \<TTurnstile> P\<^sub>G" and
     grounding: "term_subst.is_ground_subst \<gamma>" and
     wt: "welltyped\<^sub>c typeof_fun \<V> C" "welltyped\<^sub>\<sigma> \<F>\<^sub>G \<V> \<gamma>" "typeof_fun \<subseteq>\<^sub>m \<F>\<^sub>G"

    let ?P = "to_ground_clause (P \<cdot> \<mu> \<cdot> \<gamma>)"
    let ?L = "to_ground_literal (L \<cdot>l \<mu> \<cdot>l \<gamma>)"
    let ?P' = "to_ground_clause (P' \<cdot> \<mu> \<cdot> \<gamma>)"
    let ?s\<^sub>1 = "to_ground_term (s\<^sub>1 \<cdot>t \<mu> \<cdot>t \<gamma>)"
    let ?s\<^sub>2 = "to_ground_term (s\<^sub>2 \<cdot>t \<mu> \<cdot>t \<gamma>)"

    have "welltyped\<^sub>c typeof_fun \<V> (P' \<cdot> \<mu>)"
      using eq_resolutionI(8) wt(1)
      by blast

    moreover have welltyped_\<mu>: "welltyped\<^sub>\<sigma> typeof_fun \<V> \<mu>"
      using eq_resolutionI(6)
      by auto

    ultimately have welltyped_P': "welltyped\<^sub>c typeof_fun \<V> P'"
      using welltyped\<^sub>\<sigma>_welltyped\<^sub>c
      by blast

    from welltyped_\<mu> have "welltyped\<^sub>\<sigma> \<F>\<^sub>G \<V> (\<mu> \<odot> \<gamma>)"
      using wt(2) welltyped\<^sub>\<sigma>_map_le[OF welltyped_\<mu> wt(3)]
      by (simp add: subst_compose_def welltyped\<^sub>\<sigma>_def welltyped\<^sub>\<sigma>_welltyped)

    moreover have "welltyped\<^sub>c typeof_fun \<V> (add_mset (s\<^sub>1 !\<approx> s\<^sub>2) P')"
      using eq_resolutionI(6) welltyped_add_literal[OF welltyped_P']
      by auto

    ultimately have "?I \<TTurnstile> ?P"
      using premise[rule_format, of ?P, OF exI, of "\<mu> \<odot> \<gamma>"] wt(1,3) grounding ground_subst_compose
      using eq_resolutionI
      by auto

    then obtain L' where L'_in_P: "L' \<in># ?P" and I_models_L': "?I \<TTurnstile>l L'"
       by (auto simp: true_cls_def)

     have [simp]: "?P = add_mset ?L ?P'"
       by (simp add: to_ground_clause_def eq_resolutionI(3) subst_clause_add_mset)

     have [simp]: "?L = (Neg (Upair ?s\<^sub>1 ?s\<^sub>2))"
       unfolding to_ground_literal_def eq_resolutionI(4) to_ground_atom_def
       by (simp add: subst_atom_def subst_literal)
       
     have [simp]: "?s\<^sub>1 = ?s\<^sub>2"
       using term_subst.subst_imgu_eq_subst_imgu[OF eq_resolutionI(5)] by simp
      
     have "is_neg ?L"
       by (simp add: to_ground_literal_def eq_resolutionI(4) subst_literal)

     show "?I \<TTurnstile> to_ground_clause (C \<cdot> \<gamma>)"
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
       then have "L' \<in># to_ground_clause (P' \<cdot> \<mu> \<cdot> \<gamma>)"
         using L'_in_P by force
  
       then have "L' \<in># to_ground_clause (C \<cdot> \<gamma>)"
         unfolding eq_resolutionI.
  
       then show ?thesis
         using I_models_L' 
         by blast
     qed
   qed
    
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
        \<forall>P\<^sub>G. (\<exists>\<gamma>'. P\<^sub>G = to_ground_clause (P \<cdot> \<gamma>') \<and> term_subst.is_ground_subst \<gamma>'
              \<and> welltyped\<^sub>c typeof_fun \<V> P \<and> (\<exists>\<F>\<^sub>G. welltyped\<^sub>\<sigma> \<F>\<^sub>G \<V> \<gamma>' \<and> typeof_fun \<subseteq>\<^sub>m \<F>\<^sub>G)) 
            \<longrightarrow> upair ` I \<TTurnstile> P\<^sub>G; 
       term_subst.is_ground_subst \<gamma>;
       welltyped\<^sub>c typeof_fun \<V> C; welltyped\<^sub>\<sigma> \<F>\<^sub>G \<V> \<gamma>; typeof_fun \<subseteq>\<^sub>m \<F>\<^sub>G
     \<rbrakk> \<Longrightarrow> upair  ` I \<TTurnstile> to_ground_clause (C \<cdot> \<gamma>)"
  proof-
    fix I :: "'f gterm rel" and \<gamma> :: "'v \<Rightarrow> ('f, 'v) Term.term" and \<F>\<^sub>G

    let ?I = "upair ` I"
    
    assume
     trans_I: "trans I" and 
     sym_I: "sym I" and 
     premise: 
       "\<forall>P\<^sub>G. (\<exists>\<gamma>'. P\<^sub>G = to_ground_clause (P \<cdot> \<gamma>') \<and> term_subst.is_ground_subst \<gamma>'
             \<and> welltyped\<^sub>c typeof_fun \<V> P \<and> (\<exists>\<F>\<^sub>G. welltyped\<^sub>\<sigma> \<F>\<^sub>G \<V> \<gamma>' \<and> typeof_fun \<subseteq>\<^sub>m \<F>\<^sub>G)) \<longrightarrow> ?I \<TTurnstile> P\<^sub>G" and
     grounding: "term_subst.is_ground_subst \<gamma>" and
     wt: "welltyped\<^sub>c typeof_fun \<V> C" "welltyped\<^sub>\<sigma> \<F>\<^sub>G \<V> \<gamma>" "typeof_fun \<subseteq>\<^sub>m \<F>\<^sub>G"

    let ?P = "to_ground_clause (P \<cdot> \<mu> \<cdot> \<gamma>)"
    let ?P' = "to_ground_clause (P' \<cdot> \<mu> \<cdot> \<gamma>)"
    let ?L\<^sub>1 = "to_ground_literal (L\<^sub>1 \<cdot>l \<mu> \<cdot>l \<gamma>)"
    let ?L\<^sub>2 = "to_ground_literal (L\<^sub>2 \<cdot>l \<mu> \<cdot>l \<gamma>)"
    let ?s\<^sub>1 = "to_ground_term (s\<^sub>1 \<cdot>t \<mu> \<cdot>t \<gamma>)"
    let ?s\<^sub>1' = "to_ground_term (s\<^sub>1' \<cdot>t \<mu> \<cdot>t \<gamma>)"
    let ?t\<^sub>2 = "to_ground_term (t\<^sub>2 \<cdot>t \<mu> \<cdot>t \<gamma>)"
    let ?t\<^sub>2' = "to_ground_term (t\<^sub>2' \<cdot>t \<mu> \<cdot>t \<gamma>)"
    let ?C = "to_ground_clause (C \<cdot> \<gamma>)"

    have wt':
      "welltyped\<^sub>c typeof_fun \<V> (P' \<cdot> \<mu>)" 
      "welltyped\<^sub>l typeof_fun \<V> (s\<^sub>1 \<approx> t\<^sub>2' \<cdot>l \<mu>)" 
      "welltyped\<^sub>l typeof_fun \<V> (s\<^sub>1' !\<approx> t\<^sub>2' \<cdot>l \<mu>)"
      using wt(1)
      unfolding eq_factoringI(11) welltyped\<^sub>c_add_mset subst_clause_add_mset
      by auto
      
    moreover have welltyped_\<mu>: "welltyped\<^sub>\<sigma> typeof_fun \<V> \<mu>"
      using eq_factoringI(10)
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
      by (smt (verit, best) insert_iff set_uprod_simps upair_in_literal(1) upair_in_literal(2))

    have welltyped_L\<^sub>2: "welltyped\<^sub>l typeof_fun \<V> (t\<^sub>2 \<approx> t\<^sub>2')"
      using xx right_uniqueD[OF welltyped_right_unique] eq_factoringI(10)
      unfolding welltyped\<^sub>l_def welltyped\<^sub>a_def
      by (smt (verit) insert_iff set_uprod_simps upair_in_literal(1))

    from welltyped_\<mu> have "welltyped\<^sub>\<sigma> \<F>\<^sub>G \<V> (\<mu> \<odot> \<gamma>)"
      using wt(2) welltyped\<^sub>\<sigma>_map_le[OF welltyped_\<mu> wt(3)]
      by (simp add: subst_compose_def welltyped\<^sub>\<sigma>_def welltyped\<^sub>\<sigma>_welltyped)

    moreover have "welltyped\<^sub>c typeof_fun \<V> P"
      unfolding eq_factoringI welltyped\<^sub>c_add_mset
      using welltyped_P'  welltyped_L\<^sub>1 welltyped_L\<^sub>2
      by blast

    ultimately have "?I \<TTurnstile> ?P"
      using 
        premise[rule_format, of ?P, OF exI, of "\<mu> \<odot> \<gamma>"] 
        wt(1,3) 
        ground_subst_compose grounding
      by auto
      
    then obtain L' where L'_in_P: "L' \<in># ?P" and I_models_L': "?I \<TTurnstile>l L'"
      by (auto simp: true_cls_def)

    then have s\<^sub>1_equals_t\<^sub>2: "?t\<^sub>2 = ?s\<^sub>1"
      using term_subst.subst_imgu_eq_subst_imgu[OF eq_factoringI(9)]
      by simp

    have L\<^sub>1: "?L\<^sub>1 = ?s\<^sub>1 \<approx> ?s\<^sub>1'"
      unfolding to_ground_literal_def eq_factoringI(4) to_ground_atom_def
      by (simp add: subst_atom_def subst_literal)

    have L\<^sub>2: "?L\<^sub>2 = ?t\<^sub>2 \<approx> ?t\<^sub>2'"
      unfolding to_ground_literal_def eq_factoringI(5) to_ground_atom_def
      by (simp add: subst_atom_def subst_literal)

    have C: "?C = add_mset (?s\<^sub>1 \<approx> ?t\<^sub>2') (add_mset (Neg (Upair ?s\<^sub>1' ?t\<^sub>2')) ?P')"
      unfolding eq_factoringI 
      by (simp add: to_ground_clause_def to_ground_literal_def subst_atom_def subst_clause_add_mset subst_literal
            to_ground_atom_def)

    show "?I \<TTurnstile> to_ground_clause (C \<cdot> \<gamma>)"
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
        unfolding C 
        by (metis true_cls_add_mset)
    next
      case False
      then have "L' \<in># ?P'"
        using L'_in_P
        unfolding eq_factoringI
        by (simp add: to_ground_clause_def subst_clause_add_mset)

      then have "L' \<in># to_ground_clause (C \<cdot> \<gamma>)"
        by (simp add: C)

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
  case (superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' \<P> s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)

  have 
    "\<And>I \<gamma>. \<lbrakk>
        refl I;
        trans I; 
        sym I;
        compatible_with_gctxt I;
        \<forall>P\<^sub>G. (\<exists>\<gamma>'. P\<^sub>G = to_ground_clause (P1 \<cdot> \<gamma>') \<and> is_ground_clause (P1 \<cdot> \<gamma>')) \<longrightarrow> upair ` I \<TTurnstile> P\<^sub>G;
        \<forall>P\<^sub>G. (\<exists>\<gamma>'. P\<^sub>G = to_ground_clause (P2 \<cdot> \<gamma>') \<and> is_ground_clause (P2 \<cdot> \<gamma>')) \<longrightarrow> upair ` I \<TTurnstile> P\<^sub>G;
        is_ground_clause (C \<cdot> \<gamma>)
     \<rbrakk> \<Longrightarrow> (\<lambda>(x, y). Upair x y) ` I \<TTurnstile> to_ground_clause (C \<cdot> \<gamma>)"
  proof -
    fix I :: "'f gterm rel" and \<gamma> :: "'v \<Rightarrow> ('f, 'v) Term.term"

    let ?I = "(\<lambda>(x, y). Upair x y) ` I"

    assume 
      refl_I: "refl I" and 
      trans_I: "trans I" and 
      sym_I: "sym I" and 
      compatible_with_ground_context_I: "compatible_with_gctxt I" and
      premise1: 
        "\<forall>P\<^sub>G. (\<exists>\<gamma>'. P\<^sub>G = to_ground_clause (P1 \<cdot> \<gamma>') \<and> is_ground_clause (P1 \<cdot> \<gamma>')) \<longrightarrow>?I \<TTurnstile> P\<^sub>G" and
      premise2: 
        "\<forall>P\<^sub>G. (\<exists>\<gamma>'. P\<^sub>G = to_ground_clause (P2 \<cdot> \<gamma>') \<and> is_ground_clause (P2 \<cdot> \<gamma>')) \<longrightarrow> ?I \<TTurnstile> P\<^sub>G" and 
      conclusion_grounding: "is_ground_clause (C \<cdot> \<gamma>)"

     obtain \<gamma>' :: "'v \<Rightarrow> ('f, 'v) Term.term" where 
       \<gamma>': "term_subst.is_ground_subst \<gamma>'" "C \<cdot> \<gamma> = C \<cdot> \<gamma>'"
       using ground_subst_exstension_clause[OF conclusion_grounding]
       by blast
      
     let ?P1 = "to_ground_clause (P1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<cdot> \<gamma>')"
     let ?P2 = "to_ground_clause (P2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu> \<cdot> \<gamma>')"
  
     let ?L\<^sub>1 = "to_ground_literal (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu> \<cdot>l \<gamma>')"
     let ?L\<^sub>2 = "to_ground_literal (L\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu> \<cdot>l \<gamma>')"
  
     let ?P\<^sub>1' = "to_ground_clause (P\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<cdot> \<gamma>')"
     let ?P\<^sub>2' = "to_ground_clause (P\<^sub>2' \<cdot> \<rho>\<^sub>2 \<cdot> \<mu> \<cdot> \<gamma>')"
  
     let ?s\<^sub>1 = "to_ground_context (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<mu> \<cdot>t\<^sub>c \<gamma>')"
     let ?s\<^sub>1' = "to_ground_term (s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<gamma>')"
     let ?t\<^sub>2 = "to_ground_term (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<gamma>')"
     let ?t\<^sub>2' = "to_ground_term (t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<gamma>')"
     let ?u\<^sub>1 = "to_ground_term (u\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<gamma>')"
  
     let ?\<P> = "if \<P> = Pos then Pos else Neg"
  
     let ?C = "to_ground_clause (C \<cdot> \<gamma>')"

     have "?I \<TTurnstile> ?P1"
       using premise1[rule_format, of ?P1, OF exI, of "\<rho>\<^sub>1 \<odot> \<mu> \<odot> \<gamma>'"] \<gamma>'
       by (simp add: is_ground_subst_is_ground_clause)

     moreover have "?I \<TTurnstile> ?P2"
       using premise2[rule_format, of ?P2, OF exI, of "\<rho>\<^sub>2 \<odot> \<mu> \<odot> \<gamma>'"] \<gamma>'
       by (simp add: is_ground_subst_is_ground_clause)

     ultimately obtain L\<^sub>1' L\<^sub>2' 
       where
         L\<^sub>1'_in_P1: "L\<^sub>1' \<in># ?P1" and 
         I_models_L\<^sub>1': "?I \<TTurnstile>l L\<^sub>1'" and
         L\<^sub>2'_in_P2: "L\<^sub>2' \<in># ?P2" and 
         I_models_L\<^sub>2': "?I \<TTurnstile>l L\<^sub>2'"
       by (auto simp: true_cls_def)

     have u\<^sub>1_equals_t\<^sub>2: "?t\<^sub>2 = ?u\<^sub>1"
       using term_subst.subst_imgu_eq_subst_imgu[OF superpositionI(10)]
       by simp

     have s\<^sub>1_u\<^sub>1: "?s\<^sub>1\<langle>?u\<^sub>1\<rangle>\<^sub>G = to_ground_term (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<mu> \<cdot>t\<^sub>c \<gamma>')\<langle>u\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<gamma>'\<rangle>"
       using ground_term_with_context(1)[OF 
              is_ground_subst_is_ground_context[OF \<gamma>'(1)] 
              is_ground_subst_is_ground_term[OF \<gamma>'(1)]
            ]
       by blast

    have s\<^sub>1_t\<^sub>2': "(?s\<^sub>1)\<langle>?t\<^sub>2'\<rangle>\<^sub>G  = to_ground_term (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<mu> \<cdot>t\<^sub>c \<gamma>')\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<gamma>'\<rangle>"
      using ground_term_with_context(1)[OF 
              is_ground_subst_is_ground_context[OF \<gamma>'(1)] 
              is_ground_subst_is_ground_term[OF \<gamma>'(1)]
            ]
      by blast
      
    have \<P>_pos_or_neg: "\<P> = Pos \<or> \<P> = Neg"
      using superpositionI(6) by blast

    then have L\<^sub>1: "?L\<^sub>1 = ?\<P> (Upair ?s\<^sub>1\<langle>?u\<^sub>1\<rangle>\<^sub>G ?s\<^sub>1')"
      unfolding superpositionI to_ground_literal_def to_ground_atom_def
      by (auto simp: s\<^sub>1_u\<^sub>1 subst_atom subst_literal)
     
    have C: "?C = add_mset (?\<P> (Upair (?s\<^sub>1)\<langle>?t\<^sub>2'\<rangle>\<^sub>G (?s\<^sub>1'))) (?P\<^sub>1' + ?P\<^sub>2')"
      using \<P>_pos_or_neg
      unfolding 
        s\<^sub>1_t\<^sub>2' 
        superpositionI 
        to_ground_clause_def 
        to_ground_literal_def 
        subst_atom_def 
        to_ground_atom_def
        subst_clause_add_mset 
        subst_clause_plus 
      by(auto simp: subst_atom subst_literal)

    show "?I \<TTurnstile> to_ground_clause (C \<cdot> \<gamma>)"
    proof (cases "L\<^sub>1' = ?L\<^sub>1")
      case L\<^sub>1'_def: True
      then have "?I \<TTurnstile>l ?L\<^sub>1"
        using superpositionI
        using I_models_L\<^sub>1' by blast

      show ?thesis
      proof (cases "L\<^sub>2' = ?L\<^sub>2")
        case L\<^sub>2'_def: True

        then have ts_in_I: "(?t\<^sub>2, ?t\<^sub>2') \<in> I"
          using I_models_L\<^sub>2' true_lit_uprod_iff_true_lit_prod[OF sym_I] superpositionI(8)
          unfolding to_ground_literal_def to_ground_atom_def 
          by (smt (verit) literal.simps(9) map_uprod_simps subst_atom_def subst_literal true_lit_simps(1)) 

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
            unfolding C that \<gamma>'
            by (smt (verit) true_cls_add_mset)
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
            unfolding C that \<gamma>'
            by (smt (verit, best) literals_distinct(1) true_cls_add_mset)
        qed

        ultimately show ?thesis
          using \<P>_pos_or_neg by blast
      next
        case False
        then have "L\<^sub>2' \<in># ?P\<^sub>2'"
          using L\<^sub>2'_in_P2
          unfolding superpositionI
          by (simp add: to_ground_clause_def subst_clause_add_mset)

        then have "?I \<TTurnstile> ?P\<^sub>2'"
          using I_models_L\<^sub>2' by blast

        then show ?thesis
          unfolding superpositionI 
          by (metis C \<gamma>'(2) local.superpositionI(19) true_cls_union union_mset_add_mset_left)
      qed
    next
      case False
      then have "L\<^sub>1' \<in># ?P\<^sub>1'"
        using L\<^sub>1'_in_P1
        unfolding superpositionI 
        by (simp add: to_ground_clause_def subst_clause_add_mset)

      then have "?I \<TTurnstile> ?P\<^sub>1'"
        using I_models_L\<^sub>1' by blast

      then show ?thesis 
        unfolding \<gamma>'(2)
        unfolding superpositionI
        by (simp add: to_ground_clause_def subst_clause_add_mset subst_clause_plus)
    qed
  qed

  then show ?thesis 
    unfolding ground.G_entails_def clause_groundings_def true_clss_def
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
proof-
  obtain select\<^sub>G where "select\<^sub>G \<in> select\<^sub>G\<^sub>s"
    using Q_nonempty by blast
    
  then interpret grounded_first_order_superposition_calculus
    where select\<^sub>G = select\<^sub>G
    by unfold_locales (simp add: select\<^sub>G\<^sub>s_def)

  show "sound_inference_system inferences {{#}} entails_\<G>"
    using sound_inference_system_axioms Q_nonempty[folded ex_in_conv]
    unfolding entails_def
    by simp
qed

end
