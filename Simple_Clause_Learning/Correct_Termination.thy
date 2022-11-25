theory Correct_Termination
  imports Simple_Clause_Learning
begin

context scl begin

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
    "atm_of L \<cdot>a \<gamma> \<prec>\<^sub>B \<beta>"
    by (elim decide.cases) blast
  
  from conf S\<^sub>2_def obtain D \<sigma> \<rho> \<sigma>\<^sub>\<rho> where
    S\<^sub>3_def: "S\<^sub>3 = (trail_decide \<Gamma> (L \<cdot>l \<gamma>), U, Some (D \<cdot> \<rho>, \<sigma>\<^sub>\<rho>))" and
    D_in: "D |\<in>| N |\<union>| U" and
    dom_\<sigma>_subset:"subst_domain \<sigma> \<subseteq> vars_cls D" and
    ground_D_\<sigma>: "is_ground_cls (D \<cdot> \<sigma>)" and
    tr_\<Gamma>_L_false_D: "trail_false_cls (trail_decide \<Gamma> (L \<cdot>l \<gamma>)) (D \<cdot> \<sigma>)" and
    ren_\<rho>: "is_renaming \<rho>" and
    vars_D_\<rho>_disjoint: "vars_cls (D \<cdot> \<rho>) \<inter> vars_clss
      (fset (N |\<union>| U |\<union>| clss_of_trail (trail_decide \<Gamma> (L \<cdot>l \<gamma>)))) = {}" and
    \<sigma>\<^sub>\<rho>_def: "\<sigma>\<^sub>\<rho> = rename_subst_domain \<rho> \<sigma>"
    by (auto elim: conflict.cases)

  have "vars_cls D \<subseteq> subst_domain \<sigma>"
    using ground_D_\<sigma> vars_cls_subset_subst_domain_if_grounding by blast
  hence "D \<cdot> \<rho> \<cdot> \<sigma>\<^sub>\<rho> = D \<cdot> \<sigma>"
    unfolding \<sigma>\<^sub>\<rho>_def using ren_\<rho> by (metis subst_renaming_subst_adapted)

  have gr_D_\<rho>_\<sigma>\<^sub>\<rho>: "is_ground_cls (D \<cdot> \<rho> \<cdot> \<sigma>\<^sub>\<rho>)"
    unfolding \<open>D \<cdot> \<rho> \<cdot> \<sigma>\<^sub>\<rho> = D \<cdot> \<sigma>\<close> by (rule ground_D_\<sigma>)

  have tr_false_D_\<rho>_\<sigma>\<^sub>\<rho>: "trail_false_cls (trail_decide \<Gamma> (L \<cdot>l \<gamma>)) (D \<cdot> \<rho> \<cdot> \<sigma>\<^sub>\<rho>)"
    unfolding \<open>D \<cdot> \<rho> \<cdot> \<sigma>\<^sub>\<rho> = D \<cdot> \<sigma>\<close> by (rule tr_\<Gamma>_L_false_D)

  moreover have "\<not> trail_false_cls \<Gamma> (D \<cdot> \<rho> \<cdot> \<sigma>\<^sub>\<rho>)"
    using not_trail_false_ground_cls_if_no_conflict[OF no_conf] D_in
    by (simp add: S\<^sub>0_def \<open>D \<cdot> \<rho> \<cdot> \<sigma>\<^sub>\<rho> = D \<cdot> \<sigma>\<close> ground_D_\<sigma>)

  ultimately have "- (L \<cdot>l \<gamma>) \<in># D \<cdot> \<rho> \<cdot> \<sigma>\<^sub>\<rho>"
    by (metis subtrail_falseI trail_decide_def)

  then obtain D' L' where D_def: "D = add_mset L' D'" and "- (L \<cdot>l \<gamma>) = L' \<cdot>l \<rho> \<cdot>l \<sigma>\<^sub>\<rho>"
    by (metis Melem_subst_cls multi_member_split)

  define C\<^sub>0 where
    "C\<^sub>0 = {#K \<in># D'. K \<cdot>l \<rho> \<cdot>l \<sigma>\<^sub>\<rho> \<noteq> L' \<cdot>l \<rho> \<cdot>l \<sigma>\<^sub>\<rho>#}"

  define C\<^sub>1 where
    "C\<^sub>1 = {#K \<in># D'. K \<cdot>l \<rho> \<cdot>l \<sigma>\<^sub>\<rho> = L' \<cdot>l \<rho> \<cdot>l \<sigma>\<^sub>\<rho>#}"

  have ball_atms_lt_\<beta>: "\<forall>K \<in># D \<cdot> \<rho> \<cdot> \<sigma>\<^sub>\<rho>. atm_of K \<prec>\<^sub>B \<beta>"
  proof (rule ballI)
    fix K assume "K \<in># D \<cdot> \<rho> \<cdot> \<sigma>\<^sub>\<rho>"
    hence "K = L' \<cdot>l \<rho> \<cdot>l \<sigma>\<^sub>\<rho> \<or> (K \<in># D' \<cdot> \<rho> \<cdot> \<sigma>\<^sub>\<rho>)"
      by (simp add: D_def)
    thus "atm_of K \<prec>\<^sub>B \<beta>"
    proof (rule disjE)
      assume "K = L' \<cdot>l \<rho> \<cdot>l \<sigma>\<^sub>\<rho>"
      thus ?thesis
        apply simp
        by (metis \<open>- (L \<cdot>l \<gamma>) = L' \<cdot>l \<rho> \<cdot>l \<sigma>\<^sub>\<rho>\<close> \<open>atm_of L \<cdot>a \<gamma> \<prec>\<^sub>B \<beta>\<close> atm_of_eq_uminus_if_lit_eq
            atm_of_subst_lit)
    next
      have trail_lt_\<beta>': "\<forall>atm \<in> atm_of ` fst ` set (trail_decide \<Gamma> (L \<cdot>l \<gamma>)). atm \<prec>\<^sub>B \<beta>"
        using trail_lt_\<beta> by (simp add: trail_atoms_lt_def S\<^sub>2_def)

      assume K_in: "K \<in># D' \<cdot> \<rho> \<cdot> \<sigma>\<^sub>\<rho>"
      hence "atm_of K \<in> atm_of ` fst ` set (trail_decide \<Gamma> (L \<cdot>l \<gamma>))"
        using tr_false_D_\<rho>_\<sigma>\<^sub>\<rho>[unfolded D_def]
        by (metis D_def \<open>K \<in># D \<cdot> \<rho> \<cdot> \<sigma>\<^sub>\<rho>\<close> atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
            trail_false_cls_def trail_false_lit_def)
      moreover from trail_lt_\<beta> have "\<forall>atm \<in> atm_of ` fst ` set (trail_decide \<Gamma> (L \<cdot>l \<gamma>)). atm \<prec>\<^sub>B \<beta>"
        by (simp add: trail_atoms_lt_def S\<^sub>2_def)
      ultimately show ?thesis
        by blast
    qed
  qed

  have tr_false_C\<^sub>1: "trail_false_cls \<Gamma> (C\<^sub>0 \<cdot> \<rho> \<cdot> \<sigma>\<^sub>\<rho>)"
  proof (rule subtrail_falseI)
    show "trail_false_cls ((L \<cdot>l \<gamma>, None) # \<Gamma>) (C\<^sub>0 \<cdot> \<rho> \<cdot> \<sigma>\<^sub>\<rho>)"
      unfolding C\<^sub>0_def trail_false_cls_def
      apply (rule ballI)
      apply (rule tr_false_D_\<rho>_\<sigma>\<^sub>\<rho>[unfolded D_def trail_false_cls_def trail_decide_def, rule_format])
      by auto
  next
    show "- (L \<cdot>l \<gamma>) \<notin># C\<^sub>0 \<cdot> \<rho> \<cdot> \<sigma>\<^sub>\<rho>"
      unfolding C\<^sub>0_def
      using \<open>- (L \<cdot>l \<gamma>) = L' \<cdot>l \<rho> \<cdot>l \<sigma>\<^sub>\<rho>\<close> by fastforce
  qed

  have not_def_L'_\<rho>_\<sigma>\<^sub>\<rho>: "\<not> trail_defined_lit \<Gamma> (L' \<cdot>l \<rho> \<cdot>l \<sigma>\<^sub>\<rho>)"
    using \<open>\<not> trail_defined_lit \<Gamma> (L \<cdot>l \<gamma>)\<close> \<open>D \<cdot> \<rho> \<cdot> \<sigma>\<^sub>\<rho> = D \<cdot> \<sigma>\<close>[unfolded D_def]
    by (metis \<open>- (L \<cdot>l \<gamma>) = L' \<cdot>l \<rho> \<cdot>l \<sigma>\<^sub>\<rho>\<close> trail_defined_lit_iff_defined_uminus)

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
      atm_of ` insert L' {K. K \<in># D' \<and> K \<cdot>l \<rho> \<cdot>l \<sigma>\<^sub>\<rho> = L' \<cdot>l \<rho> \<cdot>l \<sigma>\<^sub>\<rho>} \<times>
      atm_of ` insert L' {K. K \<in># D' \<and> K \<cdot>l \<rho> \<cdot>l \<sigma>\<^sub>\<rho> = L' \<cdot>l \<rho> \<cdot>l \<sigma>\<^sub>\<rho>}"
      unfolding C\<^sub>1_def set_mset_filter by simp
    finally have set_pairs_xs_simp: "set (pairs (map atm_of xs)) =
      atm_of ` insert L' {K. K \<in># D' \<and> K \<cdot>l \<rho> \<cdot>l \<sigma>\<^sub>\<rho> = L' \<cdot>l \<rho> \<cdot>l \<sigma>\<^sub>\<rho>} \<times>
      atm_of ` insert L' {K. K \<in># D' \<and> K \<cdot>l \<rho> \<cdot>l \<sigma>\<^sub>\<rho> = L' \<cdot>l \<rho> \<cdot>l \<sigma>\<^sub>\<rho>}"
      by assumption
      
    show "\<rho> \<odot> \<sigma>\<^sub>\<rho> \<in> unifiers (set (pairs (map atm_of xs)))"
      unfolding unifiers_def mem_Collect_eq
    proof (rule ballI)
      fix p assume p_in: "p \<in> set (pairs (map atm_of xs))"
      then obtain K1 K2 where p_def: "p = (atm_of K1, atm_of K2)" and
        "K1 = L' \<or> K1 \<in> {K. K \<in># D' \<and> K \<cdot>l \<rho> \<cdot>l \<sigma>\<^sub>\<rho> = L' \<cdot>l \<rho> \<cdot>l \<sigma>\<^sub>\<rho>}" and
        "K2 = L' \<or> K2 \<in> {K. K \<in># D' \<and> K \<cdot>l \<rho> \<cdot>l \<sigma>\<^sub>\<rho> = L' \<cdot>l \<rho> \<cdot>l \<sigma>\<^sub>\<rho>}"
        by (auto simp: set_pairs_xs_simp)
      hence "K1 \<cdot>l \<rho> \<cdot>l \<sigma>\<^sub>\<rho> = L' \<cdot>l \<rho> \<cdot>l \<sigma>\<^sub>\<rho> \<and> K2 \<cdot>l \<rho> \<cdot>l \<sigma>\<^sub>\<rho> = L' \<cdot>l \<rho> \<cdot>l \<sigma>\<^sub>\<rho>"
        by auto
      thus "fst p \<cdot>a (\<rho> \<odot> \<sigma>\<^sub>\<rho>) = snd p \<cdot>a (\<rho> \<odot> \<sigma>\<^sub>\<rho>)"
        unfolding p_def prod.sel subst_atm_comp_subst
        by (metis atm_of_subst_lit)
    qed
  qed
  then obtain ys where
    unify_pairs: "unify (pairs (map atm_of xs)) [] = Some ys"
    using ex_unify_if_unifiers_not_empty[OF _ refl] by blast

  define \<mu> where
    "\<mu> = subst_of ys"

  have mimgu_\<mu>: "is_mimgu \<mu> {atm_of ` set_mset (add_mset L' C\<^sub>1)}"
  proof (intro is_mimgu_if_mgu_sets[unfolded mgu_sets_def] exI conjI)
    show "set (map set [(map atm_of xs)]) = {atm_of ` set_mset (add_mset L' C\<^sub>1)}"
      by (simp add: set_xs_conv)
  next
    show "map_option subst_of (unify (concat (map pairs [map atm_of xs])) []) = Some \<mu>"
      by (simp add: unify_pairs \<mu>_def)
  qed

  have is_ren_wrt: "is_renaming (renaming_wrt (fset (N |\<union>| U |\<union>| clss_of_trail \<Gamma>)))"
    by (rule is_renaming_renaming_wrt) (rule finite_fset)

  have vars_cls_subst_renaming: "vars_cls (CC \<cdot> renaming_wrt NN) \<inter> vars_clss NN = {}"
    if "finite NN" for CC NN
    by (simp add: that vars_cls_subst_renaming_disj vars_clss_def)

  show ?thesis
    using propagateI[OF D_in D_def, of "\<rho> \<odot> \<sigma>\<^sub>\<rho>", unfolded subst_cls_comp_subst subst_lit_comp_subst,
      OF gr_D_\<rho>_\<sigma>\<^sub>\<rho> ball_atms_lt_\<beta> C\<^sub>0_def C\<^sub>1_def tr_false_C\<^sub>1 not_def_L'_\<rho>_\<sigma>\<^sub>\<rho> mimgu_\<mu> refl is_ren_wrt
      vars_cls_subst_renaming[OF finite_fset] refl]   
    unfolding S\<^sub>0_def by blast
qed

definition trail_propagated_wf where
  "trail_propagated_wf \<Gamma> \<longleftrightarrow> (\<forall>(L\<^sub>\<gamma>, n) \<in> set \<Gamma>.
    case n of
      None \<Rightarrow> True
    | Some (_, L, \<gamma>) \<Rightarrow> L\<^sub>\<gamma> = L \<cdot>l \<gamma>)"

lemma trail_propagated_wf_if_sound: "sound_trail N \<Gamma> \<Longrightarrow> trail_propagated_wf \<Gamma>"
proof (induction \<Gamma> rule: sound_trail.induct)
  case Nil
  then show ?case
    by (simp add: trail_propagated_wf_def)
next
  case (Cons u L \<Gamma>)
  then show ?case
    by (cases u) (auto simp add: trail_propagated_wf_def)
qed

theorem correct_termination:
  fixes gnd_N and gnd_N_lt_\<beta>
  assumes
    regular_run: "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S" and
    no_more_regular_step: "\<nexists>S'. regular_scl N \<beta> S S'"
  defines
    "gnd_N \<equiv> grounding_of_clss (fset N)" and
    "gnd_N_lt_\<beta> \<equiv> {C \<in> gnd_N. \<forall>L \<in># C. atm_of L \<prec>\<^sub>B \<beta>}"
  shows "\<not> satisfiable gnd_N \<and> (\<exists>\<gamma>. state_conflict S = Some ({#}, \<gamma>)) \<or>
    satisfiable gnd_N_lt_\<beta> \<and> trail_true_clss (state_trail S) gnd_N_lt_\<beta>"
proof -
  from regular_run have "(scl N \<beta>)\<^sup>*\<^sup>* initial_state S"
  proof (rule mono_rtranclp[rule_format, rotated])
    show "\<And>a b. regular_scl N \<beta> a b \<Longrightarrow> scl N \<beta> a b"
      by (rule scl_if_reasonable[OF reasonable_if_regular])
  qed
  hence mempty_not_in_learned_S: "{#} |\<notin>| state_learned S"
    by (induction S rule: rtranclp_induct) (simp_all add: scl_mempty_not_in_sate_learned)

  obtain \<Gamma> U u where S_def: "S = (\<Gamma>, U, u)"
    using prod_cases3 by blast

  have sound_S: "sound_state N \<beta> S"
    using regular_run_sound_state[OF regular_run] sound_initial_state by blast
  hence
    sound_\<Gamma>: "sound_trail N \<Gamma>" and
    "minimal_ground_closures S"
    by (simp_all add: S_def sound_state_def)

  from no_more_regular_step have no_new_conflict: "\<nexists>S'. conflict N \<beta> S S'"
    using regular_scl_def by blast

  from no_more_regular_step have no_new_propagate: "\<nexists>S'. propagate N \<beta> S S'"
    by (meson decide_well_defined(1) local.scl_def reasonable_scl_def regular_scl_def)

  from no_more_regular_step have
    no_reasonable_decide: "(\<nexists>S'. decide N \<beta> S S') \<or> (\<exists>S' S''. decide N \<beta> S S' \<and> conflict N \<beta> S' S'')"
    using local.scl_def reasonable_scl_def regular_scl_def by meson

  from sound_\<Gamma> have trail_propagate_wf: "trail_propagated_wf (state_trail S)"
    by (simp add: S_def trail_propagated_wf_if_sound)
  from regular_run have trail_consistent: "trail_lits_consistent S"
    by (induction S rule: rtranclp_induct)
      (simp_all add: scl_preserves_trail_lits_consistent[OF
          scl_if_reasonable[OF reasonable_if_regular]])
  hence trail_consistent: "trail_consistent (state_trail S)"
    by (simp add: trail_lits_consistent_def)

  show ?thesis
  proof (cases u)
    case u_def: None
    hence "state_conflict S = None"
      by (simp add: S_def)

    show ?thesis
      using no_reasonable_decide
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

          have "conflict N \<beta> (\<Gamma>, U, None) (\<Gamma>, U, Some (C' \<cdot> \<rho>, \<gamma>\<^sub>\<rho>))"
          proof (rule conflictI)
            show "C' |\<in>| N |\<union>| U"
              using C'_in by simp
          next
            show "subst_domain (restrict_subst_domain (vars_cls C') \<gamma>) \<subseteq> vars_cls C'"
              by (simp add: subst_domain_restrict_subst_domain)
          next
            show "is_ground_cls (C' \<cdot> restrict_subst_domain (vars_cls C') \<gamma>)"
              using \<open>is_ground_cls C\<close>[unfolded C_def]
              by (simp add: subst_cls_restrict_subst_domain_idem)
          next
            show "trail_false_cls \<Gamma> (C' \<cdot> restrict_subst_domain (vars_cls C') \<gamma>)"
              using \<open>trail_false_cls \<Gamma> C\<close>[unfolded C_def]
              by (simp add: subst_cls_restrict_subst_domain_idem)
          next
            show "is_renaming \<rho>"
              using \<rho>_def finite_fset is_renaming_renaming_wrt by metis
          next
            show "vars_cls (C' \<cdot> \<rho>) \<inter> vars_clss (fset (N |\<union>| U |\<union>| clss_of_trail \<Gamma>)) = {}"
              by (metis \<rho>_def finite_UN finite_fset finite_vars_cls vars_cls_subst_renaming_disj
                  vars_clss_def)
          qed (simp_all add: \<rho>_def \<gamma>\<^sub>\<rho>_def)
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
        by (rule decide_sound_state[OF deci sound_S, THEN trail_atoms_lt_if_sound_state])
      ultimately have "\<exists>S\<^sub>4. propagate N \<beta> S S\<^sub>4"
        using propagate_if_conflict_follows_decide[OF _ no_new_conflict]
        by simp
      with no_new_propagate have False
        by blast
      thus ?thesis ..
    qed
  next
    case (Some Cl)
    then obtain C \<gamma> where u_def: "u = Some (C, \<gamma>)" by force

    from sound_S have
      vars_conf_disjoint: "vars_cls C \<inter> (vars_clss (fset (N |\<union>| U |\<union>| clss_of_trail \<Gamma>))) = {}"
      by (simp add: S_def u_def sound_state_def conflict_disjoint_vars_def)

    from sound_S have domain_\<gamma>: "subst_domain \<gamma> \<subseteq> vars_cls C"
      by (simp add: S_def u_def sound_state_def minimal_ground_closures_def)

    from sound_S have \<Gamma>_false_C_\<gamma>: "trail_false_cls \<Gamma> (C \<cdot> \<gamma>)"
      by (simp add: S_def u_def sound_state_def)

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
        with \<Gamma>_false_C_\<gamma> have False
          using C_not_empty by simp
        thus ?thesis ..
      next
        case (Cons Ln \<Gamma>')
        then obtain L n where \<Gamma>_def: "\<Gamma> = (L, n) # \<Gamma>'"
          by fastforce

        from regular_run have mempty_not_in_N: "{#} |\<notin>| N"
          using C_not_empty mempty_not_in_initial_clauses_if_regular_run_reaches_non_empty_conflict
          unfolding S_def state_conflict_simp u_def option.inject
          by simp

        show ?thesis
        proof (cases "- L \<in># C \<cdot> \<gamma>")
          case True \<comment> \<open>Literal cannot be skipped\<close>
          then obtain C' K where C_def: "C = add_mset K C'" and K_\<gamma>: "K \<cdot>l \<gamma> = - L"
            by (metis Melem_subst_cls add.right_neutral multi_member_split
                union_mset_add_mset_right)
          hence L_eq_uminus_K_\<gamma>: "L = - (K \<cdot>l \<gamma>)"
            by simp

          show ?thesis
          proof (cases n)
            case None \<comment> \<open>Conflict clause can be backtracked\<close>
            hence \<Gamma>_def: "\<Gamma> = trail_decide \<Gamma>' (- (K \<cdot>l \<gamma>))"
              by (simp add: \<Gamma>_def L_eq_uminus_K_\<gamma> trail_decide_def)

            from \<Gamma>_def have \<Gamma>_def': "\<Gamma> = trail_decide (\<Gamma>' @ []) (- (K \<cdot>l \<gamma>))"
              by auto

            have no_new_new_conflict: "\<nexists>S'. conflict N \<beta> ([], finsert (add_mset K C') U, None) S'"
              apply simp
              apply (intro allI notI)
              apply (erule conflict.cases)
              apply simp
              using mempty_not_in_N mempty_not_in_learned_S[unfolded S_def, simplified]
              by (metis empty_not_add_mset finsertE not_trail_false_Nil(2) subst_cls_empty_iff)

            have "backtrack N \<beta> (\<Gamma>, U, Some (add_mset K C', \<gamma>)) ([], finsert (add_mset K C') U, None)"
              using backtrackI[OF \<Gamma>_def' no_new_new_conflict] by simp

            with no_more_regular_step have False
              unfolding regular_scl_def reasonable_scl_def scl_def
              using S_def[unfolded u_def C_def, symmetric]
              using backtrack_well_defined(2) by blast
            thus ?thesis ..
          next
            case Some \<comment> \<open>Literal can be resolved\<close>
            then obtain D L' \<sigma> where n_def: "n = Some (D, L', \<sigma>)"
              by (metis prod_cases3)
            with trail_propagate_wf have L_def: "L = L' \<cdot>l \<sigma>"
              by (simp add: \<Gamma>_def S_def trail_propagated_wf_def)
            hence 1: "\<Gamma> = trail_propagate \<Gamma>' L' D \<sigma> "
              using \<Gamma>_def n_def
              by (simp add: trail_propagate_def)

            from \<open>minimal_ground_closures S\<close> have
              domain_\<sigma>: "subst_domain \<sigma> \<subseteq> vars_cls (add_mset L' D)" and
              ground_L'_D_\<sigma>: "is_ground_cls (add_mset L' D \<cdot> \<sigma>)"
              by (simp_all add: S_def 1 trail_propagate_def minimal_ground_closures_def)

            define \<rho> :: "'v \<Rightarrow> ('f, 'v) Term.term" where
              "\<rho> = renaming_wrt (fset (N |\<union>| U |\<union>| clss_of_trail \<Gamma>))"

            have ren_\<rho>: "is_renaming \<rho>"
              using \<rho>_def finite_fset is_renaming_renaming_wrt by metis

            have vars_subst_\<rho>_disj:
              "\<And>C. vars_cls (C \<cdot> \<rho>) \<inter> vars_clss (fset (N |\<union>| U |\<union>| clss_of_trail \<Gamma>)) = {}"
              by (metis \<rho>_def finite_UN finite_fset finite_vars_cls vars_cls_subst_renaming_disj
                  vars_clss_def)

            have *: "vars_cls (add_mset L' D) \<inter> vars_cls (add_mset K C') = {}"
              using vars_conf_disjoint[unfolded C_def 1] by auto

            have 2: "L' \<cdot>l \<sigma> = - (K \<cdot>l \<gamma>)"
              using K_\<gamma> L_def by fastforce
            hence "atm_of L' \<cdot>a \<sigma> = atm_of K \<cdot>a \<gamma>"
              by (metis atm_of_subst_lit atm_of_uminus)
            hence "atm_of L' \<cdot>a (\<sigma> \<odot> \<gamma>) = atm_of K \<cdot>a (\<sigma> \<odot> \<gamma>)"
              unfolding subst_subst_compose
            proof (rule subst_subst_eq_subst_subst_if_subst_eq_substI(1))
              show "vars_lit L' \<inter> subst_domain \<gamma> = {}"
                using * domain_\<gamma> vars_conf_disjoint
                by (auto simp: C_def)
            next
              show "vars_lit K \<inter> subst_domain \<sigma> = {}"
                using * domain_\<sigma> vars_conf_disjoint by auto
            next
              have "range_vars \<sigma> = {}"
                by (rule range_vars_eq_empty_if_is_ground[OF ground_L'_D_\<sigma> domain_\<sigma>])
              thus "range_vars \<sigma> \<inter> subst_domain \<gamma> = {}"
                by simp
            qed
            then obtain \<mu> where "Unification.mgu (atm_of L') (atm_of K) = Some \<mu>"
              using ex_mgu_if_subst_apply_term_eq_subst_apply_term by blast
            hence 3: "is_mimgu \<mu> {{atm_of L', atm_of K}}"
              by (rule is_mimgu_if_mgu_eq_Some)

            have "resolve N \<beta> (\<Gamma>, U, Some (add_mset K C', \<gamma>)) (\<Gamma>, U, Some ((C' + D) \<cdot> \<mu> \<cdot> \<rho>,
              restrict_subst_domain (vars_cls ((C' + D) \<cdot> \<mu> \<cdot> \<rho>)) (inv_renaming \<rho> \<odot> \<gamma> \<odot> \<sigma>)))"
              using resolveI[OF 1 2 3 ren_\<rho> vars_subst_\<rho>_disj, of \<beta>] .
            with no_more_regular_step have False
              unfolding regular_scl_def reasonable_scl_def scl_def
              using S_def \<Gamma>_def C_def decide_well_defined(5) u_def
              by blast
            thus ?thesis ..
          qed
        next
          case False \<comment> \<open>Literal can be skipped\<close>
          hence "skip N \<beta> ((L, n) # \<Gamma>', U, Some (C, \<gamma>)) (\<Gamma>', U, Some (C, \<gamma>))"
            by (rule skipI[of L C \<gamma> N \<beta> n \<Gamma>' U])
          with no_more_regular_step have False
            by (metis S_def \<Gamma>_def local.scl_def reasonable_scl_def regular_scl_def
                skip_well_defined(2) u_def)
          thus ?thesis ..
        qed
      qed
    qed
  qed
qed

end

end