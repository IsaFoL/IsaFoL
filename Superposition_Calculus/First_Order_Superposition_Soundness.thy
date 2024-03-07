theory First_Order_Superposition_Soundness
  imports Grounded_First_Order_Superposition
begin

subsection \<open>Soundness\<close>

(* TODO: What do I use from the grounding and why? *)
context first_order_superposition_calculus
begin

lemma equality_resolution_sound:
  assumes step: "equality_resolution P C"
  shows "{P} \<TTurnstile>\<^sub>F {C}"
  using step
proof (cases P C rule: equality_resolution.cases)
  case (equality_resolutionI L P' s\<^sub>1 s\<^sub>2 \<mu>)
  have 
    "\<And>I \<theta>. \<lbrakk>
        refl I; 
        \<forall>\<sigma>. term_subst.is_ground_subst \<sigma> \<longrightarrow> (\<lambda>(x, y). Upair x y) ` I \<TTurnstile> to_ground_clause (P \<cdot> \<sigma>); 
        term_subst.is_ground_subst \<theta>
     \<rbrakk> \<Longrightarrow> (\<lambda>(x, y). Upair x y) ` I \<TTurnstile> to_ground_clause (C \<cdot> \<theta>)"
  proof-
    fix I :: "'f gterm rel" and \<theta> :: "'v \<Rightarrow> ('f, 'v) Term.term"
    let ?I = "(\<lambda>(x, y). Upair x y) ` I"
    let ?P = "to_ground_clause (P \<cdot> \<mu> \<cdot> \<theta>)"
    let ?L = "to_ground_literal (L \<cdot>l \<mu> \<cdot>l \<theta>)"
    let ?P' = "to_ground_clause (P' \<cdot> \<mu> \<cdot> \<theta>)"
    let ?s\<^sub>1 = "to_ground_term (s\<^sub>1 \<cdot>t \<mu> \<cdot>t \<theta>)"
    let ?s\<^sub>2 = "to_ground_term (s\<^sub>2 \<cdot>t \<mu> \<cdot>t \<theta>)"

     assume 
       ground_subst: "term_subst.is_ground_subst \<theta>" and 
       refl_I: "refl I" and 
       premise: "\<forall>\<sigma>. term_subst.is_ground_subst \<sigma> \<longrightarrow> ?I \<TTurnstile> to_ground_clause (P \<cdot> \<sigma>)"

     have "?I \<TTurnstile> ?P"
       using 
         premise[rule_format, of "\<mu> \<odot> \<theta>", OF ground_subst_compose[OF ground_subst]]
         clause_subst_compose
       by metis
      
     then obtain L' where L'_in_P: "L' \<in># ?P" and I_models_L': "?I \<TTurnstile>l L'"
       by (auto simp: true_cls_def)

     have [simp]: "?P = add_mset ?L ?P'"
       by (simp add: to_ground_clause_def local.equality_resolutionI(1) subst_clause_add_mset)

     have [simp]: "?L = (Neg (Upair ?s\<^sub>1 ?s\<^sub>2))"
       unfolding to_ground_literal_def equality_resolutionI(2) to_ground_atom_def
       by (simp add: subst_atom_def subst_literal)
       
     have [simp]: "?s\<^sub>1 = ?s\<^sub>2"
       using is_imgu_equals[OF equality_resolutionI(3)] by simp
      
     have "is_neg ?L"
       by (simp add: to_ground_literal_def equality_resolutionI(2) subst_literal)

     show "?I \<TTurnstile> to_ground_clause (C \<cdot> \<theta>)"
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
       then have "L' \<in># to_ground_clause (P' \<cdot> \<mu> \<cdot> \<theta>)"
         using L'_in_P by force
  
       then have "L' \<in># to_ground_clause (C \<cdot> \<theta>)"
         unfolding equality_resolutionI.
  
       then show ?thesis
         using I_models_L' by blast
     qed
   qed

  then show ?thesis 
    unfolding true_clss_singleton entails\<^sub>F_def 
    by simp
qed

lemma equality_factoring_sound:
  assumes step: "equality_factoring P C"
  shows "{P} \<TTurnstile>\<^sub>F {C}"
  using step
proof (cases P C rule: equality_factoring.cases)
  case (equality_factoringI L\<^sub>1 L\<^sub>2 P' s\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)
  have 
    "\<And>I \<theta>. \<lbrakk>
        trans I; 
        sym I;
        \<forall>\<sigma>. term_subst.is_ground_subst \<sigma> \<longrightarrow> (\<lambda>(x, y). Upair x y) ` I \<TTurnstile> to_ground_clause (P \<cdot> \<sigma>); 
        term_subst.is_ground_subst \<theta>
     \<rbrakk> \<Longrightarrow> (\<lambda>(x, y). Upair x y) ` I \<TTurnstile> to_ground_clause (C \<cdot> \<theta>)"
  proof-
    fix I :: "'f gterm rel" and \<theta> :: "'v \<Rightarrow> ('f, 'v) Term.term"
    let ?I = "(\<lambda>(x, y). Upair x y) ` I"
    let ?P = "to_ground_clause (P \<cdot> \<mu> \<cdot> \<theta>)"
    let ?P' = "to_ground_clause (P' \<cdot> \<mu> \<cdot> \<theta>)"
    let ?L\<^sub>1 = "to_ground_literal (L\<^sub>1 \<cdot>l \<mu> \<cdot>l \<theta>)"
    let ?L\<^sub>2 = "to_ground_literal (L\<^sub>2 \<cdot>l \<mu> \<cdot>l \<theta>)"
    let ?s\<^sub>1 = "to_ground_term (s\<^sub>1 \<cdot>t \<mu> \<cdot>t \<theta>)"
    let ?s\<^sub>1' = "to_ground_term (s\<^sub>1' \<cdot>t \<mu> \<cdot>t \<theta>)"
    let ?t\<^sub>2 = "to_ground_term (t\<^sub>2 \<cdot>t \<mu> \<cdot>t \<theta>)"
    let ?t\<^sub>2' = "to_ground_term (t\<^sub>2' \<cdot>t \<mu> \<cdot>t \<theta>)"
    let ?C = "to_ground_clause (C \<cdot> \<theta>)"

    assume 
      ground_subst: "term_subst.is_ground_subst \<theta>" and 
      trans_I: "trans I" and 
      sym_I: "sym I" and 
      premise: "\<forall>\<sigma>. term_subst.is_ground_subst \<sigma> \<longrightarrow> ?I \<TTurnstile> to_ground_clause (P \<cdot> \<sigma>)"

    have "?I \<TTurnstile> ?P"
       using 
         premise[rule_format, of "\<mu> \<odot> \<theta>", OF ground_subst_compose[OF ground_subst]]
         clause_subst_compose
       by metis

    then obtain L' where L'_in_P: "L' \<in># ?P" and I_models_L': "?I \<TTurnstile>l L'"
      by (auto simp: true_cls_def)

    then have s\<^sub>1_equals_t\<^sub>2: "?t\<^sub>2 = ?s\<^sub>1"
      using is_imgu_equals[OF equality_factoringI(6)]
      by simp

    have L\<^sub>1: "?L\<^sub>1 = ?s\<^sub>1 \<approx> ?s\<^sub>1'"
      unfolding to_ground_literal_def equality_factoringI(2) to_ground_atom_def
      by (simp add: subst_atom_def subst_literal)

    have L\<^sub>2: "?L\<^sub>2 = ?t\<^sub>2 \<approx> ?t\<^sub>2'"
      unfolding to_ground_literal_def equality_factoringI(3) to_ground_atom_def
      by (simp add: subst_atom_def subst_literal)

    have C: "?C = add_mset (?s\<^sub>1 \<approx> ?t\<^sub>2') (add_mset (Neg (Upair ?s\<^sub>1' ?t\<^sub>2')) ?P')"
      unfolding equality_factoringI 
      by (simp add: to_ground_clause_def to_ground_literal_def subst_atom_def subst_clause_add_mset subst_literal
            to_ground_atom_def)

    show "?I \<TTurnstile> ?C"
    proof(cases "L' = ?L\<^sub>1 \<or> L' = ?L\<^sub>2")
      case True
      interpret grounded_first_order_superposition_calculus _ _ select\<^sub>G_simple
        apply unfold_locales
        using select\<^sub>G_simple by blast

      from True have "I \<TTurnstile>l Pos (?s\<^sub>1, ?s\<^sub>1') \<or> I \<TTurnstile>l Pos (?s\<^sub>1, ?t\<^sub>2')"
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
        unfolding equality_factoringI
        by (simp add: to_ground_clause_def subst_clause_add_mset)

      then have "L' \<in># to_ground_clause (C \<cdot> \<theta>)"
        by (simp add: to_ground_clause_def equality_factoringI(7) subst_clause_add_mset)

      then show ?thesis
        using I_models_L' by blast
    qed
  qed

  then show ?thesis
    unfolding true_clss_singleton entails\<^sub>F_def 
    by simp
qed

lemma superposition_sound:
  assumes step: "superposition P1 P2 C"
  shows "{P1, P2} \<TTurnstile>\<^sub>F {C}"
  using step
proof (cases P1 P2 C rule: superposition.cases)
  case (superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' \<P> s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)

  have 
    "\<And>I \<theta>. \<lbrakk>
        refl I;
        trans I; 
        sym I;
        compatible_with_gctxt I;
        \<forall>\<sigma>. term_subst.is_ground_subst \<sigma> \<longrightarrow> (\<lambda>(x, y). Upair x y) ` I \<TTurnstile> to_ground_clause (P1 \<cdot> \<sigma>);
        \<forall>\<sigma>. term_subst.is_ground_subst \<sigma> \<longrightarrow> (\<lambda>(x, y). Upair x y) ` I \<TTurnstile> to_ground_clause (P2 \<cdot> \<sigma>); 
        term_subst.is_ground_subst \<theta>
     \<rbrakk> \<Longrightarrow> (\<lambda>(x, y). Upair x y) ` I \<TTurnstile> to_ground_clause (C \<cdot> \<theta>)"
  proof -
    fix I :: "'f gterm rel" and \<theta> :: "'v \<Rightarrow> ('f, 'v) Term.term"

    let ?I = "(\<lambda>(x, y). Upair x y) ` I"

    let ?P1 = "to_ground_clause (P1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<cdot> \<theta>)"
    let ?P2 = "to_ground_clause (P2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu> \<cdot> \<theta>)"

    let ?L\<^sub>1 = "to_ground_literal (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu> \<cdot>l \<theta>)"
    let ?L\<^sub>2 = "to_ground_literal (L\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu> \<cdot>l \<theta>)"

    let ?P\<^sub>1' = "to_ground_clause (P\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<cdot> \<theta>)"
    let ?P\<^sub>2' = "to_ground_clause (P\<^sub>2' \<cdot> \<rho>\<^sub>2 \<cdot> \<mu> \<cdot> \<theta>)"

    let ?s\<^sub>1 = "to_ground_context (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<mu> \<cdot>t\<^sub>c \<theta>)"
    let ?s\<^sub>1' = "to_ground_term (s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<theta>)"
    let ?t\<^sub>2 = "to_ground_term (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<theta>)"
    let ?t\<^sub>2' = "to_ground_term (t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<theta>)"
    let ?u\<^sub>1 = "to_ground_term (u\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<theta>)"

    let ?\<P> = "if \<P> = Pos then Pos else Neg"

    let ?C = "to_ground_clause (C \<cdot> \<theta>)"

    assume 
      ground_subst: "term_subst.is_ground_subst \<theta>" and 
      refl_I: "refl I" and 
      trans_I: "trans I" and 
      sym_I: "sym I" and 
      compatible_with_ground_context_I: "compatible_with_gctxt I" and
      premise1: "\<forall>\<sigma>. term_subst.is_ground_subst \<sigma> \<longrightarrow> ?I \<TTurnstile> to_ground_clause (P1 \<cdot> \<sigma>)" and
      premise2: "\<forall>\<sigma>. term_subst.is_ground_subst \<sigma> \<longrightarrow> ?I \<TTurnstile> to_ground_clause (P2 \<cdot> \<sigma>)"

    have "?I \<TTurnstile> ?P1"
      using 
         premise1[rule_format, of "\<rho>\<^sub>1 \<odot> \<mu> \<odot> \<theta>", OF ground_subst_compose[OF ground_subst]]
         clause_subst_compose
      by metis

    moreover have "?I \<TTurnstile> ?P2"
      using 
         premise2[rule_format, of "\<rho>\<^sub>2 \<odot> \<mu> \<odot> \<theta>", OF ground_subst_compose[OF ground_subst]]
         clause_subst_compose
      by metis

    ultimately obtain L\<^sub>1' L\<^sub>2' 
      where
        L\<^sub>1'_in_P1: "L\<^sub>1' \<in># ?P1" and 
        I_models_L\<^sub>1': "?I \<TTurnstile>l L\<^sub>1'" and
        L\<^sub>2'_in_P2: "L\<^sub>2' \<in># ?P2" and 
        I_models_L\<^sub>2': "?I \<TTurnstile>l L\<^sub>2'"
      by (auto simp: true_cls_def)

    have u\<^sub>1_equals_t\<^sub>2: "?t\<^sub>2 = ?u\<^sub>1"
      using is_imgu_equals[OF superpositionI(10)]
      by simp

    have s\<^sub>1_u\<^sub>1: "?s\<^sub>1\<langle>?u\<^sub>1\<rangle>\<^sub>G = to_ground_term (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<mu> \<cdot>t\<^sub>c \<theta>)\<langle>u\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<cdot>t \<theta>\<rangle>"
      using ground_term_with_context(1)[OF 
              is_ground_subst_is_ground_context[OF ground_subst] 
              is_ground_subst_is_ground_term[OF ground_subst]
            ]
      by blast

    have s\<^sub>1_t\<^sub>2': "(?s\<^sub>1)\<langle>?t\<^sub>2'\<rangle>\<^sub>G  = to_ground_term (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<mu> \<cdot>t\<^sub>c \<theta>)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<cdot>t \<theta>\<rangle>"
      using ground_term_with_context(1)[OF 
              is_ground_subst_is_ground_context[OF ground_subst] 
              is_ground_subst_is_ground_term[OF ground_subst]
            ]
      by blast
      
    have \<P>_pos_or_neg: "\<P> = Pos \<or> \<P> = Neg"
      using superpositionI(6) by blast

    then have L\<^sub>1: "?L\<^sub>1 = ?\<P> (Upair ?s\<^sub>1\<langle>?u\<^sub>1\<rangle>\<^sub>G ?s\<^sub>1')"
      unfolding superpositionI to_ground_literal_def to_ground_atom_def
      by (smt (verit, ccfv_threshold) ground_atom_in_ground_literal2(1) literal.simps(10) map_uprod_simps s\<^sub>1_u\<^sub>1 subst_apply_term_ctxt_apply_distrib subst_atom subst_literal(1) subst_literal(2) to_ground_atom_def to_ground_literal_def)
      (* Slow:  by(auto simp: subst_atom_def subst_literal s\<^sub>1_u\<^sub>1) *)
    
    have C: "?C = add_mset (?\<P> (Upair (?s\<^sub>1)\<langle>?t\<^sub>2'\<rangle>\<^sub>G (?s\<^sub>1'))) (?P\<^sub>1' + ?P\<^sub>2')"
      using \<P>_pos_or_neg
      unfolding s\<^sub>1_t\<^sub>2' superpositionI
      apply(cases "\<P> = Pos")
      by (simp_all add: to_ground_clause_def to_ground_literal_def subst_atom_def subst_clause_add_mset subst_clause_plus 
              subst_literal to_ground_atom_def)

    show "?I \<TTurnstile> ?C"
    proof (cases "L\<^sub>1' = ?L\<^sub>1")
      case L\<^sub>1'_def: True
      then have "?I \<TTurnstile>l ?L\<^sub>1"
        using superpositionI
        using I_models_L\<^sub>1' by blast

      show ?thesis
      proof (cases "L\<^sub>2' = ?L\<^sub>2")
        case L\<^sub>2'_def: True
        interpret grounded_first_order_superposition_calculus _ _ select\<^sub>G_simple
        apply unfold_locales
        using select\<^sub>G_simple by blast

        from L\<^sub>2'_def have ts_in_I: "(?t\<^sub>2, ?t\<^sub>2') \<in> I"
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
            unfolding C that
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
            unfolding C that
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
          by (simp add: to_ground_clause_def subst_clause_add_mset subst_clause_plus)
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
        unfolding superpositionI
        by (simp add: to_ground_clause_def subst_clause_add_mset subst_clause_plus)
    qed
  qed

  then show ?thesis 
    unfolding true_clss_singleton true_clss_insert entails\<^sub>F_def
    by simp
qed

end

sublocale first_order_superposition_calculus \<subseteq> sound_inference_system inferences "{{#}}" "(\<TTurnstile>\<^sub>F)"
proof unfold_locales
  show "\<And>\<iota>. \<iota> \<in> inferences \<Longrightarrow> set (prems_of \<iota>) \<TTurnstile>\<^sub>F {concl_of \<iota>}"
    using 
      inferences_def 
      equality_factoring_sound
      equality_resolution_sound
      superposition_sound
      entails\<^sub>F_def
    by auto
next 
  show "\<bottom>\<^sub>F \<noteq> {}"
    by simp
next 
  have "\<And>\<theta> I. 
    term_subst.is_ground_subst \<theta> \<Longrightarrow> 
    (\<lambda>(x, y). Upair x y) ` I \<TTurnstile> to_ground_clause ({#} \<cdot> \<theta>) \<Longrightarrow> False"
    by (metis to_clause_empty_mset to_clause_inverse image_mset_is_empty_iff subst_clause_def 
          true_cls_empty)

  then show "\<And>B N1. B \<in> \<bottom>\<^sub>F \<Longrightarrow> {B} \<TTurnstile>\<^sub>F N1"
    unfolding true_clss_singleton entails\<^sub>F_def
    by fastforce
next
  show "\<And>N2 N1. N2 \<subseteq> N1 \<Longrightarrow> N1 \<TTurnstile>\<^sub>F N2"
    by (auto simp: entails\<^sub>F_def elim!: true_clss_mono[rotated])
next
  show "\<And>N2 N1. \<forall>C\<in>N2. N1 \<TTurnstile>\<^sub>F {C} \<Longrightarrow> N1 \<TTurnstile>\<^sub>F N2"
    unfolding entails\<^sub>F_def
    by blast
next
  show "\<And>N1 N2 N3. \<lbrakk>N1 \<TTurnstile>\<^sub>F N2; N2 \<TTurnstile>\<^sub>F N3\<rbrakk> \<Longrightarrow> N1 \<TTurnstile>\<^sub>F N3 "
    using entails\<^sub>F_def 
    by (smt (verit, best))
qed

end
