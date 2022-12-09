theory Strategy_Minimal_Backtracking
  imports
    Simple_Clause_Learning
    Correct_Termination
    Non_Redundancy
    Termination
begin

context scl begin

definition ex_conflict where
  "ex_conflict C \<Gamma> \<longleftrightarrow> (\<exists>\<gamma>. is_ground_cls (C \<cdot> \<gamma>) \<and> trail_false_cls \<Gamma> (C \<cdot> \<gamma>))"

definition is_shortest_backtrack where
  "is_shortest_backtrack C \<Gamma> \<Gamma>\<^sub>0 \<longleftrightarrow> C \<noteq> {#} \<longrightarrow> suffix \<Gamma>\<^sub>0 \<Gamma> \<and> \<not> ex_conflict C \<Gamma>\<^sub>0 \<and>
    (\<forall>Kn. suffix (Kn # \<Gamma>\<^sub>0) \<Gamma> \<longrightarrow> ex_conflict C (Kn # \<Gamma>\<^sub>0))"

primrec shortest_backtrack where
  "shortest_backtrack C [] = []" |
  "shortest_backtrack C (Ln # \<Gamma>) =
    (if ex_conflict C (Ln # \<Gamma>) then
      shortest_backtrack C \<Gamma>
    else
      Ln # \<Gamma>)"

lemma suffix_shortest_backtrack: "suffix (shortest_backtrack C \<Gamma>) \<Gamma>"
  by (induction \<Gamma>) (simp_all add: suffix_Cons)

lemma ex_conflict_shortest_backtrack: "ex_conflict C (shortest_backtrack C \<Gamma>) \<longleftrightarrow> C = {#}"
  by (induction \<Gamma>) (auto simp add: ex_conflict_def)

lemma is_shortest_backtrack_shortest_backtrack:
  "C \<noteq> {#} \<Longrightarrow> is_shortest_backtrack C \<Gamma> (shortest_backtrack C \<Gamma>)"
proof (induction \<Gamma>)
  case Nil
  then show ?case 
    by (simp add: is_shortest_backtrack_def ex_conflict_def)
next
  case (Cons Kn \<Gamma>)
  then show ?case
    apply (simp del: )
    apply (rule conjI)
     apply (simp add: is_shortest_backtrack_def suffix_Cons)
    by (meson is_shortest_backtrack_def not_Cons_self2 suffix_ConsD suffix_appendD
        suffix_order.dual_order.antisym suffix_order.dual_order.refl)
qed

definition shortest_backtrack_strategy where
  "shortest_backtrack_strategy R N \<beta> S S' \<longleftrightarrow> R N \<beta> S S' \<and> (backtrack N \<beta> S S' \<longrightarrow>
    is_shortest_backtrack (fst (the (state_conflict S))) (state_trail S) (state_trail S'))"

lemma "shortest_backtrack_strategy scl N \<beta> S S' \<Longrightarrow> scl N \<beta> S S'"
  by (simp add: shortest_backtrack_strategy_def)

theorem correct_termination:
  fixes gnd_N and gnd_N_lt_\<beta>
  assumes
    no_more_step: "\<nexists>S'. shortest_backtrack_strategy scl N \<beta> S S'" and
    sound_S: "sound_state N \<beta> S" and
    invars: "trail_atoms_lt \<beta> S" "trail_propagated_wf (state_trail S)" "trail_lits_consistent S"
      "ground_false_closures S"
  defines
    "gnd_N \<equiv> grounding_of_clss (fset N)" and
    "gnd_N_lt_\<beta> \<equiv> {C \<in> gnd_N. \<forall>L \<in># C. atm_of L \<prec>\<^sub>B \<beta>}"
  shows "\<not> satisfiable gnd_N \<and> (\<exists>\<gamma>. state_conflict S = Some ({#}, \<gamma>)) \<or>
    satisfiable gnd_N_lt_\<beta> \<and> trail_true_clss (state_trail S) gnd_N_lt_\<beta>"
proof -
  obtain \<Gamma> U u where S_def: "S = (\<Gamma>, U, u)"
    using prod_cases3 by blast

  from sound_S have
    sound_\<Gamma>: "sound_trail N \<Gamma>"
    by (simp_all add: S_def sound_state_def)

  from \<open>ground_false_closures S\<close> have "ground_closures S"
    by (simp add: ground_false_closures_def)

  from no_more_step have no_new_conflict: "\<nexists>S'. conflict N \<beta> S S'"
    unfolding shortest_backtrack_strategy_def scl_def
    using backtrack_well_defined(3) by blast

  from no_more_step have no_new_propagate: "\<nexists>S'. propagate N \<beta> S S'"
    unfolding shortest_backtrack_strategy_def scl_def
    using backtrack_well_defined(1) by blast

  from no_more_step have
    no_new_decide: "(\<nexists>S'. decide N \<beta> S S') \<or> (\<exists>S' S''. decide N \<beta> S S' \<and> conflict N \<beta> S' S'')"
    unfolding shortest_backtrack_strategy_def scl_def
    using decide_well_defined(6) by blast

  from no_more_step have no_new_skip: "\<nexists>S'. skip N \<beta> S S'"
    unfolding shortest_backtrack_strategy_def scl_def
    using backtrack_well_defined(4) by blast

  from no_more_step have no_new_resolve: "\<nexists>S'. resolve N \<beta> S S'"
    unfolding shortest_backtrack_strategy_def scl_def
    using backtrack_well_defined(6) by blast

  have trail_consistent: "trail_consistent (state_trail S)"
    using \<open>trail_lits_consistent S\<close> by (simp add: trail_lits_consistent_def)

  show ?thesis
  proof (cases u)
    case u_def: None
    hence "state_conflict S = None"
      by (simp add: S_def)

    show ?thesis
      using no_new_decide
    proof (elim disjE exE conjE)
      assume no_new_decide: "\<nexists>S'. decide N \<beta> S S'"

      have tr_true: "trail_true_clss \<Gamma> gnd_N_lt_\<beta>"
        unfolding trail_true_clss_def gnd_N_lt_\<beta>_def gnd_N_def
      proof (rule ballI, unfold mem_Collect_eq, erule conjE)
        fix C assume C_in: "C \<in> grounding_of_clss (fset N)" and C_lt_\<beta>: "\<forall>L \<in># C. atm_of L \<prec>\<^sub>B \<beta>"

        from C_in have "is_ground_cls C"
          by (rule grounding_ground)

        from C_in obtain C' \<gamma> where C'_in: "C' |\<in>| N" and C_def: "C = C' \<cdot> \<gamma>"
          unfolding grounding_of_clss_def grounding_of_cls_def
          by (smt (verit, ccfv_threshold) UN_iff mem_Collect_eq notin_fset)

        from no_new_decide have \<Gamma>_defined_C: "trail_defined_cls \<Gamma> C"
        proof (rule contrapos_np)
          assume "\<not> trail_defined_cls \<Gamma> C"
          then obtain L where L_in: "L \<in># C" and "\<not> trail_defined_lit \<Gamma> L"
            using trail_defined_cls_def by blast
          then obtain L' where L'_in: "L' \<in># C'" and "L = L' \<cdot>l \<gamma>"
            using C_def Melem_subst_cls by blast

          have "decide N \<beta> (\<Gamma>, U, None) (trail_decide \<Gamma> (L' \<cdot>l \<gamma>), U, None)"
          proof (rule decideI)
            show "L' \<in> \<Union> (set_mset ` fset N)"
              using C'_in L'_in
              by (meson UN_I fmember.rep_eq)
          next
            show "is_ground_lit (L' \<cdot>l \<gamma>)"
              using L_in \<open>L = L' \<cdot>l \<gamma>\<close> \<open>is_ground_cls C\<close> is_ground_cls_def by blast
          next
            show "\<not> trail_defined_lit \<Gamma> (L' \<cdot>l \<gamma>)"
              using \<open>L = L' \<cdot>l \<gamma>\<close> \<open>\<not> trail_defined_lit \<Gamma> L\<close> by blast
          next
            show "atm_of L' \<cdot>a \<gamma> \<prec>\<^sub>B \<beta>"
              using \<open>L = L' \<cdot>l \<gamma>\<close> C_lt_\<beta> L_in by fastforce
          qed
          thus "\<exists>S'. decide N \<beta> S S'"
            by (auto simp add: S_def u_def)
        qed

        show "trail_true_cls \<Gamma> C"
          using \<Gamma>_defined_C[THEN trail_true_or_false_cls_if_defined]
        proof (elim disjE)
          show "trail_true_cls \<Gamma> C \<Longrightarrow> trail_true_cls \<Gamma> C"
            by assumption
        next
          assume "trail_false_cls \<Gamma> C"

          define \<rho> :: "'v \<Rightarrow> ('f, 'v) term" where
            "\<rho> = renaming_wrt (fset (N |\<union>| U |\<union>| clss_of_trail \<Gamma>))"

          define \<gamma>\<^sub>\<rho> where
            "\<gamma>\<^sub>\<rho> = rename_subst_domain \<rho> (restrict_subst_domain (vars_cls C') \<gamma>)"

          have "conflict N \<beta> (\<Gamma>, U, None) (\<Gamma>, U, Some (C', restrict_subst_domain (vars_cls C') \<gamma>))"
          proof (rule conflictI)
            show "C' |\<in>| N |\<union>| U"
              using C'_in by simp
          next
            show "is_ground_cls (C' \<cdot> restrict_subst_domain (vars_cls C') \<gamma>)"
              using \<open>is_ground_cls C\<close>[unfolded C_def]
              by (simp add: subst_cls_restrict_subst_domain)
          next
            show "trail_false_cls \<Gamma> (C' \<cdot> restrict_subst_domain (vars_cls C') \<gamma>)"
              using \<open>trail_false_cls \<Gamma> C\<close>[unfolded C_def]
              by (simp add: subst_cls_restrict_subst_domain)
          qed
          with no_new_conflict have False
            by (simp add: S_def u_def)
          thus "trail_true_cls \<Gamma> C" ..
        qed
      qed
      moreover have "satisfiable gnd_N_lt_\<beta>"
        unfolding true_clss_def gnd_N_lt_\<beta>_def
      proof (intro exI ballI, unfold mem_Collect_eq, elim conjE)
        fix C
        have "trail_consistent \<Gamma>"
          using S_def trail_consistent by auto
        show "C \<in> gnd_N \<Longrightarrow> \<forall>L \<in># C. atm_of L \<prec>\<^sub>B \<beta> \<Longrightarrow> trail_interp \<Gamma> \<TTurnstile> C"
          using tr_true[unfolded gnd_N_lt_\<beta>_def]
          using trail_interp_cls_if_trail_true[OF \<open>trail_consistent \<Gamma>\<close>]
          by (simp add: trail_true_clss_def)
      qed
      ultimately show ?thesis
        by (simp add: S_def)
    next
      fix S' S''
      assume deci: "decide N \<beta> S S'" and conf: "conflict N \<beta> S' S''"
      moreover have "trail_atoms_lt \<beta> S'"
        using decide_preserves_trail_atoms_lt[OF deci \<open>trail_atoms_lt \<beta> S\<close>] .
      ultimately have "\<exists>S\<^sub>4. propagate N \<beta> S S\<^sub>4"
        using propagate_if_conflict_follows_decide[OF _ no_new_conflict]
        by simp
      with no_new_propagate have False
        by blast
      thus ?thesis ..
    qed
  next
    case (Some Cl)
    then obtain C \<gamma>\<^sub>C where u_def: "u = Some (C, \<gamma>\<^sub>C)" by force

    from \<open>ground_false_closures S\<close> have \<Gamma>_false_C_\<gamma>\<^sub>C: "trail_false_cls \<Gamma> (C \<cdot> \<gamma>\<^sub>C)"
      by (simp add: S_def u_def ground_false_closures_def)

    show ?thesis
    proof (cases "C = {#}")
      case True
      hence "\<not> satisfiable gnd_N \<and> (\<exists>\<gamma>. state_conflict S = Some ({#}, \<gamma>))"
        using S_def u_def not_satisfiable_if_sound_state_conflict_bottom[OF sound_S]
        by (simp add: gnd_N_def)
      thus ?thesis by simp
    next
      case C_not_empty: False
      show ?thesis
      proof (cases \<Gamma>)
        case Nil
        with \<Gamma>_false_C_\<gamma>\<^sub>C have False
          using C_not_empty by simp
        thus ?thesis ..
      next
        case (Cons Ln \<Gamma>')
        then obtain K\<^sub>\<Gamma> n where \<Gamma>_def: "\<Gamma> = (K\<^sub>\<Gamma>, n) # \<Gamma>'"
          by fastforce

        show ?thesis
        proof (cases "- K\<^sub>\<Gamma> \<in># C \<cdot> \<gamma>\<^sub>C")
          case True \<comment> \<open>Literal cannot be skipped\<close>
          then obtain C' L where C_def: "C = add_mset L C'" and K_\<gamma>: "L \<cdot>l \<gamma>\<^sub>C = - K\<^sub>\<Gamma>"
            by (metis Melem_subst_cls multi_member_split)
          hence L_eq_uminus_K_\<gamma>: "K\<^sub>\<Gamma> = - (L \<cdot>l \<gamma>\<^sub>C)"
            by simp

          show ?thesis
          proof (cases n)
            case None \<comment> \<open>Conflict clause can be backtracked\<close>
            hence \<Gamma>_def: "\<Gamma> = trail_decide \<Gamma>' (- (L \<cdot>l \<gamma>\<^sub>C))"
              by (simp add: \<Gamma>_def L_eq_uminus_K_\<gamma> decide_lit_def)

            from suffix_shortest_backtrack[of "add_mset L C'" \<Gamma>'] obtain \<Gamma>'' where
              \<Gamma>'_def: "\<Gamma>' = \<Gamma>'' @ shortest_backtrack (add_mset L C') \<Gamma>'"
              using suffixE by blast

            define S' :: "('f, 'v) state" where
              "S' = (shortest_backtrack (add_mset L C') \<Gamma>', finsert (add_mset L C') U, None)"

            have "backtrack N \<beta> S S'"
              unfolding S_def[unfolded u_def C_def] S'_def
            proof (rule backtrackI[OF _ refl])
              show "\<Gamma> = trail_decide (\<Gamma>'' @ shortest_backtrack (add_mset L C') \<Gamma>') (- (L \<cdot>l \<gamma>\<^sub>C))"
                using \<Gamma>_def \<Gamma>'_def by simp
            next
              show "\<nexists>\<gamma>. is_ground_cls (add_mset L C' \<cdot> \<gamma>) \<and>
                trail_false_cls (shortest_backtrack (add_mset L C') \<Gamma>') (add_mset L C' \<cdot> \<gamma>)"
                using ex_conflict_shortest_backtrack[of "add_mset L C'", simplified]
                by (simp add: ex_conflict_def)
            qed
            moreover have "is_shortest_backtrack (fst (the (state_conflict S)))
              (state_trail S) (state_trail S')"
              unfolding S_def[unfolded u_def C_def] S'_def
              apply simp
              using is_shortest_backtrack_shortest_backtrack[of "add_mset L C'", simplified]
              by (metis C_def \<Gamma>_def \<Gamma>_false_C_\<gamma>\<^sub>C \<open>S = (\<Gamma>, U, Some (add_mset L C', \<gamma>\<^sub>C))\<close>
                  \<open>ground_closures S\<close> ex_conflict_def ground_closures_def is_shortest_backtrack_def
                  state_proj_simp(3) suffix_Cons)
            ultimately have "\<exists>S'. shortest_backtrack_strategy scl N \<beta> S S'"
              unfolding shortest_backtrack_strategy_def
              using scl_def by metis
            with no_more_step have False ..
            thus ?thesis ..
          next
            case Some \<comment> \<open>Literal can be resolved\<close>
            then obtain D K \<gamma>\<^sub>D where n_def: "n = Some (D, K, \<gamma>\<^sub>D)"
              by (metis prod_cases3)
            with \<open>trail_propagated_wf (state_trail S)\<close> have L_def: "K\<^sub>\<Gamma> = K \<cdot>l \<gamma>\<^sub>D"
              by (simp add: \<Gamma>_def S_def trail_propagated_wf_def)
            hence 1: "\<Gamma> = trail_propagate \<Gamma>' K D \<gamma>\<^sub>D"
              using \<Gamma>_def n_def
              by (simp add: propagate_lit_def)

            from \<open>ground_closures S\<close> have
              ground_conf: "is_ground_cls (add_mset L C' \<cdot> \<gamma>\<^sub>C)" and
              ground_prop: "is_ground_cls (add_mset K D \<cdot> \<gamma>\<^sub>D)"
              unfolding S_def ground_closures_def
              by (simp_all add: 1 C_def u_def ground_closures_def propagate_lit_def)

            define \<rho> :: "'v \<Rightarrow> ('f, 'v) Term.term" where
              "\<rho> = renaming_wrt {add_mset K D}"

            have ren_\<rho>: "is_renaming \<rho>"
              unfolding \<rho>_def
              by (rule is_renaming_renaming_wrt) simp
            hence "\<forall>x. is_Var (\<rho> x)" "inj \<rho>"
              by (simp_all add: is_renaming_iff)

            have disjoint_vars: "\<And>C. vars_cls (C \<cdot> \<rho>) \<inter> vars_cls (add_mset K D \<cdot> Var) = {}"
              by (simp add: \<rho>_def vars_cls_subst_renaming_disj)

            have 2: "K \<cdot>l \<gamma>\<^sub>D = - (L \<cdot>l \<gamma>\<^sub>C)"
              using K_\<gamma> L_def by fastforce

            let ?\<gamma>\<^sub>D' = "restrict_subst_domain (vars_cls (add_mset K D)) \<gamma>\<^sub>D"
    
            have "K \<cdot>l ?\<gamma>\<^sub>D' = K \<cdot>l \<gamma>\<^sub>D" and "D \<cdot> ?\<gamma>\<^sub>D' = D \<cdot> \<gamma>\<^sub>D"
              by (simp_all add: subst_lit_restrict_subst_domain subst_cls_restrict_subst_domain)
            hence "K \<cdot>l ?\<gamma>\<^sub>D' = - (L \<cdot>l \<gamma>\<^sub>C)" and ground_prop': "is_ground_cls (add_mset K D \<cdot> ?\<gamma>\<^sub>D')"
              using 2 ground_prop by simp_all
    
            have dom_\<gamma>\<^sub>D': "subst_domain ?\<gamma>\<^sub>D' \<subseteq> vars_cls (add_mset K D)"
              by simp
    
            let ?\<gamma> = "\<lambda>x.
              if x \<in> vars_cls (add_mset L C' \<cdot> \<rho>) then
                rename_subst_domain \<rho> \<gamma>\<^sub>C x
              else
                \<gamma>\<^sub>D x"
            have "L \<cdot>l \<rho> \<cdot>l ?\<gamma> = L \<cdot>l \<gamma>\<^sub>C" and "K \<cdot>l ?\<gamma> = K \<cdot>l \<gamma>\<^sub>D"
              using merge_of_renamed_groundings[OF ren_\<rho> is_renaming_id_subst disjoint_vars
                  ground_conf ground_prop is_grounding_merge_if_mem_then_else]
              unfolding rename_subst_domain_Var_lhs
              by simp_all

            then have "atm_of L \<cdot>a \<rho> \<cdot>a ?\<gamma> = atm_of K \<cdot>a ?\<gamma>"
              by (smt (verit, best) "2" atm_of_uminus subst_lit_id_subst atm_of_subst_lit)
            then obtain \<mu> where "Unification.mgu (atm_of L \<cdot>a \<rho>) (atm_of K) = Some \<mu>"
              using ex_mgu_if_subst_apply_term_eq_subst_apply_term
              by blast
            hence imgu_\<mu>: "is_imgu \<mu> {{atm_of L \<cdot>a \<rho>, atm_of K \<cdot>a Var}}"
              by (simp add: is_imgu_if_mgu_eq_Some)

            have "\<exists>S. resolve N \<beta> (\<Gamma>, U, Some (add_mset L C', \<gamma>\<^sub>C)) S"
              using resolveI[OF 1 2 ren_\<rho> is_renaming_id_subst disjoint_vars imgu_\<mu>
                  is_grounding_merge_if_mem_then_else] ..
            with no_new_resolve have False
              by (metis C_def S_def u_def)
            thus ?thesis ..
          qed
        next
          case False \<comment> \<open>Literal can be skipped\<close>
          hence "skip N \<beta> ((K\<^sub>\<Gamma>, n) # \<Gamma>', U, Some (C, \<gamma>\<^sub>C)) (\<Gamma>', U, Some (C, \<gamma>\<^sub>C))"
            by (rule skipI[of K\<^sub>\<Gamma> C \<gamma>\<^sub>C N \<beta> n \<Gamma>' U])
          with no_new_skip have False
            by (metis S_def \<Gamma>_def u_def)
          thus ?thesis ..
        qed
      qed
    qed
  qed
qed

theorem learned_clauses_in_shortest_backtracking_regular_runs:
  assumes
    run: "(shortest_backtrack_strategy regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S0" and
    conflict: "conflict N \<beta> S0 S1" and
    resolution: "(skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>+\<^sup>+ S1 Sn" and
    backtrack: "shortest_backtrack_strategy backtrack N \<beta> Sn Sn'" and
    "transp lt"
  defines
    "trail_ord \<equiv> multp (trail_less_ex lt (map fst (state_trail S1)))" and
    "U \<equiv> state_learned S1"
  shows "(shortest_backtrack_strategy regular_scl N \<beta>)\<^sup>+\<^sup>+ initial_state Sn' \<and>
    (\<exists>C \<gamma>. state_conflict Sn = Some (C, \<gamma>) \<and>
      C \<cdot> \<gamma> \<notin> grounding_of_clss (fset N \<union> fset U) \<and>
      set_mset (C \<cdot> \<gamma>) \<notin> set_mset ` grounding_of_clss (fset N \<union> fset U) \<and>
      \<not> redundant trail_ord (fset N \<union> fset U) C)"
  using learned_clauses_in_regular_runs
proof -
  from backtrack have backtrack': "backtrack N \<beta> Sn Sn'"
    by (simp add: shortest_backtrack_strategy_def)


  from run conflict have "(shortest_backtrack_strategy regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S1"
    by (metis (no_types, lifting) rtranclp.rtrancl_into_rtrancl scl.conflict_well_defined(6)
        regular_scl_if_conflict scl_axioms shortest_backtrack_strategy_def)
  also from resolution have reg_run_S1_Sn: "(shortest_backtrack_strategy regular_scl N \<beta>)\<^sup>+\<^sup>+ ... Sn"
  proof (induction Sn rule: tranclp_induct)
    case (base y)
    then show ?case
      by (metis backtrack_well_defined(6) factorize_well_defined(5) regular_scl_if_factorize
          regular_scl_if_resolve regular_scl_if_skip shortest_backtrack_strategy_def
          skip_well_defined(6) sup2E tranclp.r_into_trancl)
  next
    case (step y z)
    hence "(shortest_backtrack_strategy regular_scl N \<beta>) y z"
      by (metis backtrack_well_defined(6) factorize_well_defined(5) regular_scl_if_factorize
          regular_scl_if_resolve regular_scl_if_skip shortest_backtrack_strategy_def
          skip_well_defined(6) sup2E)
    with step.IH show ?case
      by force
  qed
  also have "(shortest_backtrack_strategy regular_scl N \<beta>)\<^sup>+\<^sup>+ ... Sn'"
  proof (rule tranclp.r_into_trancl)
    from backtrack' have "scl N \<beta> Sn Sn'"
      by (simp add: scl_def)
    with backtrack' have "reasonable_scl N \<beta> Sn Sn'"
      using reasonable_scl_def decide_well_defined(6) by blast
    with backtrack' have "regular_scl N \<beta> Sn Sn'"
      unfolding regular_scl_def
      by (smt (verit) conflict.simps option.simps(3) backtrack.cases state_conflict_simp)
    with backtrack show "shortest_backtrack_strategy regular_scl N \<beta> Sn Sn'"
      unfolding shortest_backtrack_strategy_def
      by simp
  qed
  finally have "(shortest_backtrack_strategy regular_scl N \<beta>)\<^sup>+\<^sup>+ initial_state Sn'" by assumption

  moreover have "(\<exists>C \<gamma>. state_conflict Sn = Some (C, \<gamma>) \<and>
           C \<cdot> \<gamma> \<notin> grounding_of_clss (fset N \<union> fset (state_learned S1)) \<and>
           set_mset (C \<cdot> \<gamma>) \<notin> set_mset ` grounding_of_clss (fset N \<union> fset (state_learned S1)) \<and>
           \<not> redundant (multp (trail_less_ex lt (map fst (state_trail S1))))
               (fset N \<union> fset (state_learned S1)) C)"
  proof (rule learned_clauses_in_regular_runs[THEN conjunct2])
    from run show "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S0"
      by (induction S0 rule: rtranclp_induct) (auto simp: shortest_backtrack_strategy_def)
  next
    from assms show "conflict N \<beta> S0 S1"
      by simp
  next
    from assms show "(skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>+\<^sup>+ S1 Sn"
      by simp
  next
    from assms show "backtrack N \<beta> Sn Sn'"
      by (simp add: shortest_backtrack_strategy_def)
  next
    from assms show "transp lt"
      by simp
  qed

  ultimately show ?thesis
    by (simp add: U_def trail_ord_def)
qed

theorem shortest_backtracking_regular_scl_terminates:
  fixes
    N :: "('f, 'v) Term.term clause fset" and
    \<beta> :: "('f, 'v) Term.term" and
    lt :: "('f, 'v) Term.term literal \<Rightarrow> ('f, 'v) Term.term literal \<Rightarrow> bool"
  defines
    "invars \<equiv> trail_atoms_lt \<beta> \<sqinter> trail_resolved_lits_pol \<sqinter> trail_lits_ground \<sqinter>
      trail_lits_from_clauses N \<sqinter> initial_lits_generalize_learned_trail_conflict N \<sqinter>
      ground_closures \<sqinter> ground_false_closures \<sqinter> sound_state N \<beta> \<sqinter>
      almost_no_conflict_with_trail N \<beta> \<sqinter>
      regular_conflict_resolution N \<beta>"
  assumes "transp lt"
  shows
    "wfP (\<lambda>S' S. shortest_backtrack_strategy regular_scl N \<beta> S S' \<and> invars S)" and
    "invars initial_state" and
    "\<And>S S'. shortest_backtrack_strategy regular_scl N \<beta> S S' \<Longrightarrow> invars S \<Longrightarrow> invars S'"
proof -
  show "invars initial_state"
    by (simp add: invars_def)
next
  have min_to_reg:
    "\<And>S S'. shortest_backtrack_strategy regular_scl N \<beta> S S' \<Longrightarrow> regular_scl N \<beta> S S'"
    by (simp add: shortest_backtrack_strategy_def)

  note rea_to_scl = scl_if_reasonable
  note reg_to_rea = reasonable_if_regular
  note min_to_scl = min_to_reg[THEN reg_to_rea[THEN rea_to_scl]]

  fix S S'
  assume "shortest_backtrack_strategy regular_scl N \<beta> S S'"
  thus "invars S \<Longrightarrow> invars S'"
    unfolding invars_def
    using
      min_to_scl[THEN scl_preserves_trail_atoms_lt]
      min_to_scl[THEN scl_preserves_trail_resolved_lits_pol]
      min_to_scl[THEN scl_preserves_trail_lits_ground]
      min_to_scl[THEN scl_preserves_trail_lits_from_clauses]
      min_to_scl[THEN scl_preserves_initial_lits_generalize_learned_trail_conflict]
      min_to_scl[THEN scl_preserves_ground_closures]
      min_to_scl[THEN scl_preserves_ground_false_closures]
      min_to_scl[THEN scl_preserves_sound_state]
      min_to_reg[THEN regular_scl_preserves_almost_no_conflict_with_trail]
      min_to_reg[THEN regular_scl_preserves_regular_conflict_resolution]
    by simp
next
  show "wfP (\<lambda>S' S. shortest_backtrack_strategy regular_scl N \<beta> S S' \<and> invars S)"
    using regular_scl_terminates(1)[OF \<open>transp lt\<close>, of N \<beta>, folded invars_def]
  proof (rule wfP_subset, unfold le_fun_def le_bool_def inf_fun_def, intro allI impI, elim conjE)
    fix S S'
    show "shortest_backtrack_strategy regular_scl N \<beta> S S' \<Longrightarrow> invars S \<Longrightarrow> regular_scl N \<beta> S S' \<and> invars S"
      by (simp add: shortest_backtrack_strategy_def)
  qed
qed

end

end