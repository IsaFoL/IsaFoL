theory Correct_Termination
  imports SCL_FOL
begin

context scl_fol_calculus begin

lemma not_satisfiable_if_sound_state_conflict_bottom:
  assumes sound_S: "sound_state N \<beta> S" and conflict_S: "state_conflict S = Some ({#}, \<gamma>)"
  shows "\<not> satisfiable (grounding_of_clss (fset N))"
proof -
  from sound_S conflict_S have "fset N \<TTurnstile>\<G>e {{#}}"
    unfolding sound_state_def state_conflict_def by auto
  thus ?thesis by simp
qed

lemma propagate_if_conflict_follows_decide:
  assumes
    trail_lt_\<beta>: "trail_atoms_lt \<beta> S\<^sub>2" and
    no_conf: "\<nexists>S\<^sub>1. conflict N \<beta> S\<^sub>0 S\<^sub>1" and deci: "decide N \<beta> S\<^sub>0 S\<^sub>2" and conf: "conflict N \<beta> S\<^sub>2 S\<^sub>3"
  shows "\<exists>S\<^sub>4. propagate N \<beta> S\<^sub>0 S\<^sub>4"
proof -
  from deci obtain L \<gamma> \<Gamma> U where
    S\<^sub>0_def: "S\<^sub>0 = (\<Gamma>, U, None)" and
    S\<^sub>2_def: "S\<^sub>2 = (trail_decide \<Gamma> (L \<cdot>l \<gamma>), U, None)" and
    "L \<in> \<Union> (set_mset ` fset N)" and
    "is_ground_lit (L \<cdot>l \<gamma>)" and
    "\<not> trail_defined_lit \<Gamma> (L \<cdot>l \<gamma>)" and
    "atm_of L \<cdot>a \<gamma> \<preceq>\<^sub>B \<beta>"
    by (elim decide.cases) blast
  
  from conf S\<^sub>2_def obtain D \<gamma>\<^sub>D where
    S\<^sub>3_def: "S\<^sub>3 = (trail_decide \<Gamma> (L \<cdot>l \<gamma>), U, Some (D, \<gamma>\<^sub>D))" and
    D_in: "D |\<in>| N |\<union>| U" and
    ground_D_\<sigma>: "is_ground_cls (D \<cdot> \<gamma>\<^sub>D)" and
    tr_\<Gamma>_L_false_D: "trail_false_cls (trail_decide \<Gamma> (L \<cdot>l \<gamma>)) (D \<cdot> \<gamma>\<^sub>D)"
    by (auto elim: conflict.cases)

  have "vars_cls D \<subseteq> subst_domain \<gamma>\<^sub>D"
    using ground_D_\<sigma> vars_cls_subset_subst_domain_if_grounding by blast

  moreover have "\<not> trail_false_cls \<Gamma> (D \<cdot> \<gamma>\<^sub>D)"
    using not_trail_false_ground_cls_if_no_conflict[OF no_conf] D_in
    by (simp add: S\<^sub>0_def ground_D_\<sigma>)

  ultimately have "- (L \<cdot>l \<gamma>) \<in># D \<cdot> \<gamma>\<^sub>D"
    using tr_\<Gamma>_L_false_D
    by (metis subtrail_falseI decide_lit_def)

  then obtain D' L' where D_def: "D = add_mset L' D'" and "- (L \<cdot>l \<gamma>) = L' \<cdot>l \<gamma>\<^sub>D"
    by (metis Melem_subst_cls multi_member_split)

  define C\<^sub>0 where
    "C\<^sub>0 = {#K \<in># D'. K \<cdot>l \<gamma>\<^sub>D \<noteq> L' \<cdot>l \<gamma>\<^sub>D#}"

  define C\<^sub>1 where
    "C\<^sub>1 = {#K \<in># D'. K \<cdot>l \<gamma>\<^sub>D = L' \<cdot>l \<gamma>\<^sub>D#}"

  have ball_atms_lt_\<beta>: "\<forall>K \<in># D \<cdot> \<gamma>\<^sub>D. atm_of K \<preceq>\<^sub>B \<beta>"
  proof (rule ballI)
    fix K assume "K \<in># D \<cdot> \<gamma>\<^sub>D"
    hence "K = L' \<cdot>l \<gamma>\<^sub>D \<or> (K \<in># D' \<cdot> \<gamma>\<^sub>D)"
      by (simp add: D_def)
    thus "atm_of K \<preceq>\<^sub>B \<beta>"
    proof (rule disjE)
      assume "K = L' \<cdot>l \<gamma>\<^sub>D"
      thus ?thesis
        using \<open>- (L \<cdot>l \<gamma>) = L' \<cdot>l \<gamma>\<^sub>D\<close> \<open>atm_of L \<cdot>a \<gamma> \<preceq>\<^sub>B \<beta>\<close>
        by (metis  atm_of_eq_uminus_if_lit_eq atm_of_subst_lit)
    next
      have trail_lt_\<beta>': "\<forall>A \<in> atm_of ` fst ` set (trail_decide \<Gamma> (L \<cdot>l \<gamma>)). A \<preceq>\<^sub>B \<beta>"
        using trail_lt_\<beta> by (simp add: trail_atoms_lt_def S\<^sub>2_def)

      assume K_in: "K \<in># D' \<cdot> \<gamma>\<^sub>D"
      hence "atm_of K \<in> atm_of ` fst ` set (trail_decide \<Gamma> (L \<cdot>l \<gamma>))"
        using tr_\<Gamma>_L_false_D[unfolded D_def]
        by (metis D_def \<open>K \<in># D \<cdot> \<gamma>\<^sub>D\<close> atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
            trail_false_cls_def trail_false_lit_def)
      moreover from trail_lt_\<beta> have "\<forall>A \<in> atm_of ` fst ` set (trail_decide \<Gamma> (L \<cdot>l \<gamma>)). A \<preceq>\<^sub>B \<beta>"
        by (simp add: trail_atoms_lt_def S\<^sub>2_def)
      ultimately show ?thesis
        by blast
    qed
  qed

  have tr_false_C\<^sub>1: "trail_false_cls \<Gamma> (C\<^sub>0 \<cdot> \<gamma>\<^sub>D)"
  proof (rule subtrail_falseI)
    show "trail_false_cls ((L \<cdot>l \<gamma>, None) # \<Gamma>) (C\<^sub>0 \<cdot> \<gamma>\<^sub>D)"
      unfolding C\<^sub>0_def trail_false_cls_def
      apply (rule ballI)
      apply (rule tr_\<Gamma>_L_false_D[unfolded D_def trail_false_cls_def decide_lit_def, rule_format])
      by auto
  next
    show "- (L \<cdot>l \<gamma>) \<notin># C\<^sub>0 \<cdot> \<gamma>\<^sub>D"
      unfolding C\<^sub>0_def
      using \<open>- (L \<cdot>l \<gamma>) = L' \<cdot>l \<gamma>\<^sub>D\<close> by fastforce
  qed

  have not_def_L'_\<rho>_\<sigma>\<^sub>\<rho>: "\<not> trail_defined_lit \<Gamma> (L' \<cdot>l \<gamma>\<^sub>D)"
    using \<open>\<not> trail_defined_lit \<Gamma> (L \<cdot>l \<gamma>)\<close>
    by (metis \<open>- (L \<cdot>l \<gamma>) = L' \<cdot>l \<gamma>\<^sub>D\<close> trail_defined_lit_iff_defined_uminus)

  obtain xs where "mset xs = add_mset L' C\<^sub>1"
    using ex_mset by auto
  hence set_xs_conv:
    "set xs = set_mset (add_mset L' C\<^sub>1)"
    by (metis set_mset_mset)

  have "unifiers (set (pairs (map atm_of xs))) \<noteq> {}"
  proof (rule not_empty_if_mem)
    have "set (pairs (map atm_of xs)) =
      atm_of ` set_mset (add_mset L' C\<^sub>1) \<times> atm_of ` set_mset (add_mset L' C\<^sub>1)"
      unfolding set_pairs list.set_map set_xs_conv by simp
    also have "\<dots> =
      atm_of ` insert L' (set_mset C\<^sub>1) \<times> atm_of ` insert L' (set_mset C\<^sub>1)"
      unfolding set_mset_add_mset_insert by simp
    also have "\<dots> =
      atm_of ` insert L' {K. K \<in># D' \<and> K \<cdot>l \<gamma>\<^sub>D = L' \<cdot>l \<gamma>\<^sub>D} \<times>
      atm_of ` insert L' {K. K \<in># D' \<and> K \<cdot>l \<gamma>\<^sub>D = L' \<cdot>l \<gamma>\<^sub>D}"
      unfolding C\<^sub>1_def set_mset_filter by simp
    finally have set_pairs_xs_simp: "set (pairs (map atm_of xs)) =
      atm_of ` insert L' {K. K \<in># D' \<and> K \<cdot>l \<gamma>\<^sub>D = L' \<cdot>l \<gamma>\<^sub>D} \<times>
      atm_of ` insert L' {K. K \<in># D' \<and> K \<cdot>l \<gamma>\<^sub>D = L' \<cdot>l \<gamma>\<^sub>D}"
      by assumption
      
    show "\<gamma>\<^sub>D \<in> unifiers (set (pairs (map atm_of xs)))"
      unfolding unifiers_def mem_Collect_eq
    proof (rule ballI)
      fix p assume p_in: "p \<in> set (pairs (map atm_of xs))"
      then obtain K1 K2 where p_def: "p = (atm_of K1, atm_of K2)" and
        "K1 = L' \<or> K1 \<in> {K. K \<in># D' \<and> K \<cdot>l \<gamma>\<^sub>D = L' \<cdot>l \<gamma>\<^sub>D}" and
        "K2 = L' \<or> K2 \<in> {K. K \<in># D' \<and> K \<cdot>l \<gamma>\<^sub>D = L' \<cdot>l \<gamma>\<^sub>D}"
        by (auto simp: set_pairs_xs_simp)
      hence "K1 \<cdot>l \<gamma>\<^sub>D = L' \<cdot>l \<gamma>\<^sub>D \<and> K2 \<cdot>l \<gamma>\<^sub>D = L' \<cdot>l \<gamma>\<^sub>D"
        by auto
      thus "fst p \<cdot>a \<gamma>\<^sub>D = snd p \<cdot>a \<gamma>\<^sub>D"
        unfolding p_def prod.sel
        by (metis atm_of_subst_lit)
    qed
  qed
  then obtain ys where
    unify_pairs: "unify (pairs (map atm_of xs)) [] = Some ys"
    using ex_unify_if_unifiers_not_empty[OF _ refl] by blast

  define \<mu> where
    "\<mu> = subst_of ys"

  have imgu_\<mu>: "is_imgu \<mu> {atm_of ` set_mset (add_mset L' C\<^sub>1)}"
  proof (intro is_imgu_if_mgu_sets[unfolded mgu_sets_def] exI conjI)
    show "set (map set [(map atm_of xs)]) = {atm_of ` set_mset (add_mset L' C\<^sub>1)}"
      by (simp add: set_xs_conv)
  next
    show "map_option subst_of (unify (concat (map pairs [map atm_of xs])) []) = Some \<mu>"
      by (simp add: unify_pairs \<mu>_def)
  qed

  show ?thesis
    using propagateI[OF D_in D_def, of \<gamma>\<^sub>D, unfolded subst_cls_comp_subst subst_lit_comp_subst,
      OF ground_D_\<sigma> ball_atms_lt_\<beta> C\<^sub>0_def C\<^sub>1_def tr_false_C\<^sub>1 not_def_L'_\<rho>_\<sigma>\<^sub>\<rho> imgu_\<mu>]   
    unfolding S\<^sub>0_def by blast
qed

theorem correct_termination:
  fixes gnd_N and gnd_N_lt_\<beta>
  assumes
    sound_S: "sound_state N \<beta> S" and
    invars: "trail_atoms_lt \<beta> S" "trail_propagated_wf (state_trail S)" "trail_lits_consistent S"
      "ground_false_closures S" and
    no_new_conflict: "\<nexists>S'. conflict N \<beta> S S'" and
    no_new_propagate: "\<nexists>S'. propagate N \<beta> S S'" and
    no_new_decide: "\<nexists>S'. decide N \<beta> S S' \<and> (\<nexists>S''. conflict N \<beta> S' S'')" and
    no_new_skip: "\<nexists>S'. skip N \<beta> S S'" and
    no_new_resolve: "\<nexists>S'. resolve N \<beta> S S'" and
    no_new_backtrack: "\<nexists>S'. backtrack N \<beta> S S' \<and>
      is_shortest_backtrack (fst (the (state_conflict S))) (state_trail S) (state_trail S')"
  defines
    "gnd_N \<equiv> grounding_of_clss (fset N)" and
    "gnd_N_lt_\<beta> \<equiv> {C \<in> gnd_N. \<forall>L \<in># C. atm_of L \<preceq>\<^sub>B \<beta>}"
  shows "\<not> satisfiable gnd_N \<and> (\<exists>\<gamma>. state_conflict S = Some ({#}, \<gamma>)) \<or>
    satisfiable gnd_N_lt_\<beta> \<and> trail_true_clss (state_trail S) gnd_N_lt_\<beta>"
proof -
  obtain \<Gamma> U u where S_def: "S = (\<Gamma>, U, u)"
    using prod_cases3 by blast

  from sound_S have sound_\<Gamma>: "sound_trail N \<Gamma>"
    by (simp_all add: S_def sound_state_def)

  from \<open>ground_false_closures S\<close> have "ground_closures S"
    by (simp add: ground_false_closures_def)

  have trail_consistent: "trail_consistent (state_trail S)"
    using \<open>trail_lits_consistent S\<close> by (simp add: trail_lits_consistent_def)

  show ?thesis
  proof (cases u)
    case u_def: None
    hence "state_conflict S = None"
      by (simp add: S_def)

    have tr_true: "trail_true_clss \<Gamma> gnd_N_lt_\<beta>"
      unfolding trail_true_clss_def gnd_N_lt_\<beta>_def gnd_N_def
    proof (rule ballI, unfold mem_Collect_eq, erule conjE)
      fix C assume C_in: "C \<in> grounding_of_clss (fset N)" and C_lt_\<beta>: "\<forall>L \<in># C. atm_of L \<preceq>\<^sub>B \<beta>"

      from C_in have "is_ground_cls C"
        by (rule grounding_ground)

      from C_in obtain C' \<gamma> where C'_in: "C' |\<in>| N" and C_def: "C = C' \<cdot> \<gamma>"
        unfolding grounding_of_clss_def grounding_of_cls_def
        by (smt (verit, ccfv_threshold) UN_iff mem_Collect_eq)

      from no_new_decide have \<Gamma>_defined_C: "trail_defined_cls \<Gamma> C"
      proof (rule contrapos_np)
        assume "\<not> trail_defined_cls \<Gamma> C"
        then obtain L where L_in: "L \<in># C" and "\<not> trail_defined_lit \<Gamma> L"
          using trail_defined_cls_def by blast
        then obtain L' where L'_in: "L' \<in># C'" and "L = L' \<cdot>l \<gamma>"
          using C_def Melem_subst_cls by blast

        have deci: "decide N \<beta> (\<Gamma>, U, None) (trail_decide \<Gamma> (L' \<cdot>l \<gamma>), U, None)"
        proof (rule decideI)
          show "L' \<in> \<Union> (set_mset ` fset N)"
            using C'_in L'_in
            by (meson UN_I)
        next
          show "is_ground_lit (L' \<cdot>l \<gamma>)"
            using L_in \<open>L = L' \<cdot>l \<gamma>\<close> \<open>is_ground_cls C\<close> is_ground_cls_def by blast
        next
          show "\<not> trail_defined_lit \<Gamma> (L' \<cdot>l \<gamma>)"
            using \<open>L = L' \<cdot>l \<gamma>\<close> \<open>\<not> trail_defined_lit \<Gamma> L\<close> by blast
        next
          show "atm_of L' \<cdot>a \<gamma> \<preceq>\<^sub>B \<beta>"
            using \<open>L = L' \<cdot>l \<gamma>\<close> C_lt_\<beta> L_in by fastforce
        qed

        moreover have "\<nexists>S''. conflict N \<beta> (trail_decide \<Gamma> (L' \<cdot>l \<gamma>), U, None) S''"
        proof (rule notI, elim exE)
          fix S''
          assume conf: "conflict N \<beta> (trail_decide \<Gamma> (L' \<cdot>l \<gamma>), U, None) S''"
          moreover have "trail_atoms_lt \<beta> (trail_decide \<Gamma> (L' \<cdot>l \<gamma>), U, None)"
            using decide_preserves_trail_atoms_lt[OF deci] \<open>trail_atoms_lt \<beta> S\<close>
            by (simp add: S_def u_def)
          ultimately have "\<exists>S\<^sub>4. propagate N \<beta> S S\<^sub>4"
            using propagate_if_conflict_follows_decide[OF _ no_new_conflict]
            using S_def deci u_def by blast
          with no_new_propagate show False
            by metis
        qed

        ultimately show "\<exists>S'. decide N \<beta> S S' \<and> (\<nexists>S''. conflict N \<beta> S' S'')"
          by (auto simp : S_def u_def)
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
      show "C \<in> gnd_N \<Longrightarrow> \<forall>L \<in># C. atm_of L \<preceq>\<^sub>B \<beta> \<Longrightarrow> trail_interp \<Gamma> \<TTurnstile> C"
        using tr_true[unfolded gnd_N_lt_\<beta>_def]
        using trail_interp_cls_if_trail_true[OF \<open>trail_consistent \<Gamma>\<close>]
        by (simp add: trail_true_clss_def)
    qed

    ultimately show ?thesis
      by (simp add: S_def)
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
      have False
      proof (cases \<Gamma>)
        case Nil
        with \<Gamma>_false_C_\<gamma>\<^sub>C show False
          using C_not_empty by simp
      next
        case (Cons Ln \<Gamma>')
        then obtain K\<^sub>\<Gamma> n where \<Gamma>_def: "\<Gamma> = (K\<^sub>\<Gamma>, n) # \<Gamma>'"
          by fastforce

        show False
        proof (cases "- K\<^sub>\<Gamma> \<in># C \<cdot> \<gamma>\<^sub>C")
          case True \<comment> \<open>Literal cannot be skipped\<close>
          then obtain C' L where C_def: "C = add_mset L C'" and K_\<gamma>: "L \<cdot>l \<gamma>\<^sub>C = - K\<^sub>\<Gamma>"
            by (metis Melem_subst_cls multi_member_split)
          hence L_eq_uminus_K_\<gamma>: "K\<^sub>\<Gamma> = - (L \<cdot>l \<gamma>\<^sub>C)"
            by simp

          show False
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
            ultimately show False
              using no_new_backtrack by metis
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
            with no_new_resolve show False
              by (metis C_def S_def u_def)
          qed
        next
          case False \<comment> \<open>Literal can be skipped\<close>
          hence "skip N \<beta> ((K\<^sub>\<Gamma>, n) # \<Gamma>', U, Some (C, \<gamma>\<^sub>C)) (\<Gamma>', U, Some (C, \<gamma>\<^sub>C))"
            by (rule skipI[of K\<^sub>\<Gamma> C \<gamma>\<^sub>C N \<beta> n \<Gamma>' U])
          with no_new_skip show False
            by (metis S_def \<Gamma>_def u_def)
        qed
      qed
      thus ?thesis ..
    qed
  qed
qed

corollary correct_termination_strategy:
  fixes gnd_N and gnd_N_lt_\<beta>
  assumes
    run: "(strategy N \<beta>)\<^sup>*\<^sup>* initial_state S" and
    no_step: "\<nexists>S'. strategy N \<beta> S S'" and
    strategy_restricted_by_min_back:
      "\<And>S S'. shortest_backtrack_strategy regular_scl N \<beta> S S' \<Longrightarrow> strategy N \<beta> S S'" and
    strategy_preserves_invars:
      "\<And>N \<beta> S S'. strategy N \<beta> S S' \<Longrightarrow> sound_state N \<beta> S \<Longrightarrow> sound_state N \<beta> S'"
      "\<And>N \<beta> S S'. strategy N \<beta> S S' \<Longrightarrow> trail_atoms_lt \<beta> S \<Longrightarrow> trail_atoms_lt \<beta> S'"
      "\<And>N \<beta> S S'. strategy N \<beta> S S' \<Longrightarrow> trail_propagated_or_decided' N \<beta> S \<Longrightarrow> trail_propagated_or_decided' N \<beta> S'"
      "\<And>N \<beta> S S'. strategy N \<beta> S S' \<Longrightarrow> trail_lits_consistent S \<Longrightarrow> trail_lits_consistent S'"
      "\<And>N \<beta> S S'. strategy N \<beta> S S' \<Longrightarrow> ground_false_closures S \<Longrightarrow> ground_false_closures S'"
  defines
    "gnd_N \<equiv> grounding_of_clss (fset N)" and
    "gnd_N_lt_\<beta> \<equiv> {C \<in> gnd_N. \<forall>L \<in># C. atm_of L \<preceq>\<^sub>B \<beta>}"
  shows "\<not> satisfiable gnd_N \<and> (\<exists>\<gamma>. state_conflict S = Some ({#}, \<gamma>)) \<or>
    satisfiable gnd_N_lt_\<beta> \<and> trail_true_clss (state_trail S) gnd_N_lt_\<beta>"
proof -
  from no_step have no_step': "\<nexists>S'. shortest_backtrack_strategy regular_scl N \<beta> S S'"
  proof (rule contrapos_nn)
    show "\<exists>S'. shortest_backtrack_strategy regular_scl N \<beta> S S' \<Longrightarrow> \<exists>S'. strategy N \<beta> S S'"
      using strategy_restricted_by_min_back by metis
  qed

  show ?thesis
  proof (rule correct_termination[of N \<beta> S, folded gnd_N_def, folded gnd_N_lt_\<beta>_def])
    from run show "sound_state N \<beta> S"
      by (induction S rule: rtranclp_induct) (auto intro: strategy_preserves_invars(1))
  next
    from run show "trail_atoms_lt \<beta> S"
      by (induction S rule: rtranclp_induct) (auto intro: strategy_preserves_invars(2))
  next
    from run have "trail_propagated_or_decided' N \<beta> S"
      by (induction S rule: rtranclp_induct) (auto intro: strategy_preserves_invars(3))
    thus "trail_propagated_wf (state_trail S)"
      by (simp add: trail_propagated_or_decided'_def
          trail_propagated_wf_if_trail_propagated_or_decided)
  next
    from run show "trail_lits_consistent S"
      by (induction S rule: rtranclp_induct) (auto intro: strategy_preserves_invars(4))
  next
    from run show "ground_false_closures S"
      by (induction S rule: rtranclp_induct) (auto intro: strategy_preserves_invars(5))
  next
    from no_step' show "\<nexists>S'. conflict N \<beta> S S'"
      unfolding shortest_backtrack_strategy_def regular_scl_def reasonable_scl_def scl_def
      using backtrack_well_defined(3) by blast
  next
    from no_step' show "\<nexists>S'. propagate N \<beta> S S'"
      unfolding shortest_backtrack_strategy_def regular_scl_def reasonable_scl_def scl_def
      using backtrack_well_defined(3) propagate_well_defined(1) propagate_well_defined(6) by blast
  next
    from no_step' show "\<nexists>S'. decide N \<beta> S S' \<and> (\<nexists>S''. conflict N \<beta> S' S'')"
      unfolding shortest_backtrack_strategy_def regular_scl_def reasonable_scl_def scl_def
      using backtrack_well_defined(2) backtrack_well_defined(3) by blast
  next
    from no_step' show "\<nexists>S'. skip N \<beta> S S'"
      unfolding shortest_backtrack_strategy_def regular_scl_def reasonable_scl_def scl_def
      using backtrack_well_defined(3) backtrack_well_defined(4) skip_well_defined(2) by blast
  next
    from no_step' show "\<nexists>S'. resolve N \<beta> S S'"
      unfolding shortest_backtrack_strategy_def regular_scl_def reasonable_scl_def scl_def
      using backtrack_well_defined(3) resolve_well_defined(2) resolve_well_defined(5) by blast
  next
    from no_step' show "\<nexists>S'. backtrack N \<beta> S S' \<and>
    is_shortest_backtrack (fst (the (state_conflict S))) (state_trail S) (state_trail S')"
      unfolding shortest_backtrack_strategy_def scl_def regular_scl_def reasonable_scl_def
      using backtrack_well_defined(2) backtrack_well_defined(3) by blast
  qed
qed

corollary correct_termination_scl_run:
  fixes gnd_N and gnd_N_lt_\<beta>
  assumes
    run: "(scl N \<beta>)\<^sup>*\<^sup>* initial_state S" and
    no_step: "\<nexists>S'. scl N \<beta> S S'"
  defines
    "gnd_N \<equiv> grounding_of_clss (fset N)" and
    "gnd_N_lt_\<beta> \<equiv> {C \<in> gnd_N. \<forall>L \<in># C. atm_of L \<preceq>\<^sub>B \<beta>}"
  shows "\<not> satisfiable gnd_N \<and> (\<exists>\<gamma>. state_conflict S = Some ({#}, \<gamma>)) \<or>
    satisfiable gnd_N_lt_\<beta> \<and> trail_true_clss (state_trail S) gnd_N_lt_\<beta>"
proof (rule correct_termination_strategy[of _ N \<beta>, folded gnd_N_def, folded gnd_N_lt_\<beta>_def])
  show "(scl N \<beta>)\<^sup>*\<^sup>* initial_state S"
    by (rule run)
next
  show "\<nexists>S'. scl N \<beta> S S'"
    by (rule no_step)
next
  show "\<And>S S'. shortest_backtrack_strategy regular_scl N \<beta> S S' \<Longrightarrow> scl N \<beta> S S'"
    by (simp add: regular_scl_if_shortest_backtrack_strategy scl_if_regular)
next
  show "\<And>N \<beta> S S'. scl N \<beta> S S' \<Longrightarrow> sound_state N \<beta> S \<Longrightarrow> sound_state N \<beta> S'"
    using scl_preserves_sound_state by simp
next
  show "\<And>N \<beta> S S'. scl N \<beta> S S' \<Longrightarrow> trail_atoms_lt \<beta> S \<Longrightarrow> trail_atoms_lt \<beta> S'"
    using scl_preserves_trail_atoms_lt by simp
next
  show "\<And>N \<beta> S S'. scl N \<beta> S S' \<Longrightarrow> trail_propagated_or_decided' N \<beta> S \<Longrightarrow>
    trail_propagated_or_decided' N \<beta> S'"
    using scl_preserves_trail_propagated_or_decided by simp
next
  show "\<And>N \<beta> S S'. scl N \<beta> S S' \<Longrightarrow> trail_lits_consistent S \<Longrightarrow> trail_lits_consistent S'"
    using scl_preserves_trail_lits_consistent by simp
next
  show "\<And>N \<beta> S S'. scl N \<beta> S S' \<Longrightarrow> ground_false_closures S \<Longrightarrow> ground_false_closures S'"
    using scl_preserves_ground_false_closures by simp
qed

corollary correct_termination_reasonable_scl_run:
  fixes gnd_N and gnd_N_lt_\<beta>
  assumes
    run: "(reasonable_scl N \<beta>)\<^sup>*\<^sup>* initial_state S" and
    no_step: "\<nexists>S'. reasonable_scl N \<beta> S S'"
  defines
    "gnd_N \<equiv> grounding_of_clss (fset N)" and
    "gnd_N_lt_\<beta> \<equiv> {C \<in> gnd_N. \<forall>L \<in># C. atm_of L \<preceq>\<^sub>B \<beta>}"
  shows "\<not> satisfiable gnd_N \<and> (\<exists>\<gamma>. state_conflict S = Some ({#}, \<gamma>)) \<or>
    satisfiable gnd_N_lt_\<beta> \<and> trail_true_clss (state_trail S) gnd_N_lt_\<beta>"
proof (rule correct_termination_strategy[of _ N \<beta>, folded gnd_N_def, folded gnd_N_lt_\<beta>_def])
  show "(reasonable_scl N \<beta>)\<^sup>*\<^sup>* initial_state S"
    by (rule run)
next
  show "\<nexists>S'. reasonable_scl N \<beta> S S'"
    by (rule no_step)
next
  show "\<And>S S'. shortest_backtrack_strategy regular_scl N \<beta> S S' \<Longrightarrow> reasonable_scl N \<beta> S S'"
    by (simp add: reasonable_if_regular regular_scl_if_shortest_backtrack_strategy)
next
  show "\<And>N \<beta> S S'. reasonable_scl N \<beta> S S' \<Longrightarrow> sound_state N \<beta> S \<Longrightarrow> sound_state N \<beta> S'"
    using scl_preserves_sound_state[OF scl_if_reasonable] by simp
next
  show "\<And>N \<beta> S S'. reasonable_scl N \<beta> S S' \<Longrightarrow> trail_atoms_lt \<beta> S \<Longrightarrow> trail_atoms_lt \<beta> S'"
    using scl_preserves_trail_atoms_lt[OF scl_if_reasonable] by simp
next
  show "\<And>N \<beta> S S'. reasonable_scl N \<beta> S S' \<Longrightarrow> trail_propagated_or_decided' N \<beta> S \<Longrightarrow>
    trail_propagated_or_decided' N \<beta> S'"
    using scl_preserves_trail_propagated_or_decided[OF scl_if_reasonable] by simp
next
  show "\<And>N \<beta> S S'. reasonable_scl N \<beta> S S' \<Longrightarrow> trail_lits_consistent S \<Longrightarrow> trail_lits_consistent S'"
    using scl_preserves_trail_lits_consistent[OF scl_if_reasonable] by simp
next
  show "\<And>N \<beta> S S'. reasonable_scl N \<beta> S S' \<Longrightarrow> ground_false_closures S \<Longrightarrow> ground_false_closures S'"
    using scl_preserves_ground_false_closures[OF scl_if_reasonable] by simp
qed

corollary correct_termination_regular_scl_run:
  fixes gnd_N and gnd_N_lt_\<beta>
  assumes
    run: "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S" and
    no_step: "\<nexists>S'. regular_scl N \<beta> S S'"
  defines
    "gnd_N \<equiv> grounding_of_clss (fset N)" and
    "gnd_N_lt_\<beta> \<equiv> {C \<in> gnd_N. \<forall>L \<in># C. atm_of L \<preceq>\<^sub>B \<beta>}"
  shows "\<not> satisfiable gnd_N \<and> (\<exists>\<gamma>. state_conflict S = Some ({#}, \<gamma>)) \<or>
    satisfiable gnd_N_lt_\<beta> \<and> trail_true_clss (state_trail S) gnd_N_lt_\<beta>"
proof (rule correct_termination_strategy[of _ N \<beta>, folded gnd_N_def, folded gnd_N_lt_\<beta>_def])
  show "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S"
    by (rule run)
next
  show "\<nexists>S'. regular_scl N \<beta> S S'"
    by (rule no_step)
next
  show "\<And>S S'. shortest_backtrack_strategy regular_scl N \<beta> S S' \<Longrightarrow> regular_scl N \<beta> S S'"
    by (simp add: reasonable_if_regular regular_scl_if_shortest_backtrack_strategy)
next
  show "\<And>N \<beta> S S'. regular_scl N \<beta> S S' \<Longrightarrow> sound_state N \<beta> S \<Longrightarrow> sound_state N \<beta> S'"
    using scl_preserves_sound_state[OF scl_if_regular] by simp
next
  show "\<And>N \<beta> S S'. regular_scl N \<beta> S S' \<Longrightarrow> trail_atoms_lt \<beta> S \<Longrightarrow> trail_atoms_lt \<beta> S'"
    using scl_preserves_trail_atoms_lt[OF scl_if_regular] by simp
next
  show "\<And>N \<beta> S S'. regular_scl N \<beta> S S' \<Longrightarrow> trail_propagated_or_decided' N \<beta> S \<Longrightarrow>
    trail_propagated_or_decided' N \<beta> S'"
    using scl_preserves_trail_propagated_or_decided[OF scl_if_regular] by simp
next
  show "\<And>N \<beta> S S'. regular_scl N \<beta> S S' \<Longrightarrow> trail_lits_consistent S \<Longrightarrow> trail_lits_consistent S'"
    using scl_preserves_trail_lits_consistent[OF scl_if_regular] by simp
next
  show "\<And>N \<beta> S S'. regular_scl N \<beta> S S' \<Longrightarrow> ground_false_closures S \<Longrightarrow> ground_false_closures S'"
    using scl_preserves_ground_false_closures[OF scl_if_regular] by simp
qed

corollary correct_termination_shortest_backtrack_strategy_regular_scl:
  fixes gnd_N and gnd_N_lt_\<beta>
  assumes
    run: "(shortest_backtrack_strategy regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S" and
    no_step: "\<nexists>S'. shortest_backtrack_strategy regular_scl N \<beta> S S'"
  defines
    "gnd_N \<equiv> grounding_of_clss (fset N)" and
    "gnd_N_lt_\<beta> \<equiv> {C \<in> gnd_N. \<forall>L \<in># C. atm_of L \<preceq>\<^sub>B \<beta>}"
  shows "\<not> satisfiable gnd_N \<and> (\<exists>\<gamma>. state_conflict S = Some ({#}, \<gamma>)) \<or>
    satisfiable gnd_N_lt_\<beta> \<and> trail_true_clss (state_trail S) gnd_N_lt_\<beta>"
proof (rule correct_termination_strategy[of _ N \<beta>, folded gnd_N_def, folded gnd_N_lt_\<beta>_def])
  show "(shortest_backtrack_strategy regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S"
    by (rule run)
next
  show "\<nexists>S'. shortest_backtrack_strategy regular_scl N \<beta> S S'"
    by (rule no_step)
next
  show "\<And>S S'. shortest_backtrack_strategy regular_scl N \<beta> S S' \<Longrightarrow> shortest_backtrack_strategy regular_scl N \<beta> S S'"
    by simp
next
  show "\<And>N \<beta> S S'. shortest_backtrack_strategy regular_scl N \<beta> S S' \<Longrightarrow> sound_state N \<beta> S \<Longrightarrow> sound_state N \<beta> S'"
    using scl_preserves_sound_state[OF scl_if_regular]
    by (auto simp: shortest_backtrack_strategy_def)
next
  show "\<And>N \<beta> S S'. shortest_backtrack_strategy regular_scl N \<beta> S S' \<Longrightarrow> trail_atoms_lt \<beta> S \<Longrightarrow> trail_atoms_lt \<beta> S'"
    using scl_preserves_trail_atoms_lt[OF scl_if_regular]
    by (auto simp: shortest_backtrack_strategy_def)
next
  show "\<And>N \<beta> S S'. shortest_backtrack_strategy regular_scl N \<beta> S S' \<Longrightarrow> trail_propagated_or_decided' N \<beta> S \<Longrightarrow>
    trail_propagated_or_decided' N \<beta> S'"
    using scl_preserves_trail_propagated_or_decided[OF scl_if_regular]
    by (auto simp: shortest_backtrack_strategy_def)
next
  show "\<And>N \<beta> S S'. shortest_backtrack_strategy regular_scl N \<beta> S S' \<Longrightarrow> trail_lits_consistent S \<Longrightarrow> trail_lits_consistent S'"
    using scl_preserves_trail_lits_consistent[OF scl_if_regular]
    by (auto simp: shortest_backtrack_strategy_def)
next
  show "\<And>N \<beta> S S'. shortest_backtrack_strategy regular_scl N \<beta> S S' \<Longrightarrow> ground_false_closures S \<Longrightarrow> ground_false_closures S'"
    using scl_preserves_ground_false_closures[OF scl_if_regular]
    by (auto simp: shortest_backtrack_strategy_def)
qed

corollary correct_termination_strategies:
  fixes gnd_N and gnd_N_lt_\<beta>
  assumes
    "(scl N \<beta>)\<^sup>*\<^sup>* initial_state S \<and> (\<nexists>S'. scl N \<beta> S S') \<or>
     (reasonable_scl N \<beta>)\<^sup>*\<^sup>* initial_state S \<and> (\<nexists>S'. reasonable_scl N \<beta> S S') \<or>
     (regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S \<and> (\<nexists>S'. regular_scl N \<beta> S S') \<or>
     (shortest_backtrack_strategy regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S \<and>
       (\<nexists>S'. shortest_backtrack_strategy regular_scl N \<beta> S S')"
  defines
    "gnd_N \<equiv> grounding_of_clss (fset N)" and
    "gnd_N_lt_\<beta> \<equiv> {C \<in> gnd_N. \<forall>L \<in># C. atm_of L \<preceq>\<^sub>B \<beta>}"
  shows "\<not> satisfiable gnd_N \<and> (\<exists>\<gamma>. state_conflict S = Some ({#}, \<gamma>)) \<or>
    satisfiable gnd_N_lt_\<beta> \<and> trail_true_clss (state_trail S) gnd_N_lt_\<beta>"
  unfolding gnd_N_def gnd_N_lt_\<beta>_def
  using assms(1)
    correct_termination_scl_run[of N \<beta> S]
    correct_termination_reasonable_scl_run[of N \<beta> S]
    correct_termination_regular_scl_run[of N \<beta> S]
    correct_termination_shortest_backtrack_strategy_regular_scl[of N \<beta> S]
  by argo

end

end