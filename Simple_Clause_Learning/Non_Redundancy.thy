theory Non_Redundancy
  imports
    Simple_Clause_Learning
    Trail_Induced_Ordering
    Initial_Literals_Generalize_Learned_Literals
begin

context scl begin


section \<open>Resolve in Regular Runs\<close>

lemma resolve_if_conflict_follows_propagate:
  assumes
    no_conf: "\<nexists>S\<^sub>1. conflict N \<beta> S\<^sub>0 S\<^sub>1" and
    propa: "propagate N \<beta> S\<^sub>0 S\<^sub>1" and
    conf: "conflict N \<beta> S\<^sub>1 S\<^sub>2"
  shows "\<exists>S\<^sub>3. resolve N \<beta> S\<^sub>2 S\<^sub>3"
  using propa
proof (cases N \<beta> S\<^sub>0 S\<^sub>1 rule: propagate.cases)
  case (propagateI C U L C' \<gamma> C\<^sub>0 C\<^sub>1 \<Gamma> \<mu> \<gamma>' \<rho> \<gamma>\<^sub>\<rho>')
  hence S\<^sub>0_def: "S\<^sub>0 = (\<Gamma>, U, None)"
    by simp

  from conf obtain \<gamma>\<^sub>D D \<rho>\<^sub>D where
    S\<^sub>2_def: "S\<^sub>2 = (trail_propagate \<Gamma> (L \<cdot>l \<mu> \<cdot>l \<rho>) (C\<^sub>0 \<cdot> \<mu> \<cdot> \<rho>) \<gamma>\<^sub>\<rho>', U,
      Some (D \<cdot> \<rho>\<^sub>D, rename_subst_domain \<rho>\<^sub>D \<gamma>\<^sub>D))" and
    D_in: "D |\<in>| N |\<union>| U" and
    dom_\<gamma>\<^sub>D: "subst_domain \<gamma>\<^sub>D \<subseteq> vars_cls D" and
    gr_D_\<gamma>\<^sub>D: "is_ground_cls (D \<cdot> \<gamma>\<^sub>D)" and
    tr_false_\<Gamma>_L_\<mu>: "trail_false_cls (trail_propagate \<Gamma> (L \<cdot>l \<mu> \<cdot>l \<rho>) (C\<^sub>0 \<cdot> \<mu> \<cdot> \<rho>) \<gamma>\<^sub>\<rho>') (D \<cdot> \<gamma>\<^sub>D)" and
    \<rho>\<^sub>D_def: "\<rho>\<^sub>D = renaming_wrt (fset (N |\<union>| U |\<union>|
      clss_of_trail (trail_propagate \<Gamma> (L \<cdot>l \<mu> \<cdot>l \<rho>) (C\<^sub>0 \<cdot> \<mu> \<cdot> \<rho>) \<gamma>\<^sub>\<rho>')))"
    by (elim conflict.cases) (unfold propagateI(1,2), blast)

  from no_conf have "\<not> trail_false_cls \<Gamma> (D \<cdot> \<gamma>\<^sub>D)"
    using gr_D_\<gamma>\<^sub>D D_in not_trail_false_ground_cls_if_no_conflict[of N \<beta> _ D \<gamma>\<^sub>D]
    using S\<^sub>0_def by force
  with tr_false_\<Gamma>_L_\<mu> have "- (L \<cdot>l \<mu> \<cdot>l \<rho> \<cdot>l \<gamma>\<^sub>\<rho>') \<in># D \<cdot> \<gamma>\<^sub>D"
    unfolding trail_propagate_def by (metis subtrail_falseI)
  then obtain D' L' where D_def: "D = add_mset L' D'" and "- (L \<cdot>l \<mu> \<cdot>l \<rho> \<cdot>l \<gamma>\<^sub>\<rho>') = L' \<cdot>l \<gamma>\<^sub>D"
    by (meson Melem_subst_cls multi_member_split)
  hence 1: "L \<cdot>l \<mu> \<cdot>l \<rho> \<cdot>l \<gamma>\<^sub>\<rho>' = - (L' \<cdot>l \<gamma>\<^sub>D)"
    by (metis uminus_of_uminus_id)

  moreover have L'_\<rho>\<^sub>D_adapt_\<gamma>\<^sub>D: "L' \<cdot>l \<rho>\<^sub>D \<cdot>l rename_subst_domain \<rho>\<^sub>D \<gamma>\<^sub>D = L' \<cdot>l \<gamma>\<^sub>D"
    by (metis D_def \<rho>\<^sub>D_def finite_fset gr_D_\<gamma>\<^sub>D le_sup_iff is_renaming_renaming_wrt
        subst_lit_renaming_subst_adapted vars_cls_add_mset
        vars_cls_subset_subst_domain_if_grounding)

  ultimately have 1: "L \<cdot>l \<mu> \<cdot>l \<rho> \<cdot>l \<gamma>\<^sub>\<rho>' = - (L' \<cdot>l \<rho>\<^sub>D \<cdot>l rename_subst_domain \<rho>\<^sub>D \<gamma>\<^sub>D)"
    by argo

  have "\<exists>\<mu>'. Unification.mgu (atm_of L \<cdot>a \<mu> \<cdot>a \<rho>) (atm_of L' \<cdot>a \<rho>\<^sub>D) = Some \<mu>'"
  proof (rule ex_mgu_if_subst_eq_subst_and_disj_vars)
    show "atm_of L \<cdot>a \<mu> \<cdot>a \<rho> \<cdot>a \<gamma>\<^sub>\<rho>' = atm_of L' \<cdot>a \<rho>\<^sub>D \<cdot>a rename_subst_domain \<rho>\<^sub>D \<gamma>\<^sub>D"
      using 1 by (metis atm_of_subst_lit atm_of_uminus)
  next
    have fin: "finite (\<Union> (vars_cls ` (fset (N |\<union>| U |\<union>|
      clss_of_trail (trail_propagate \<Gamma> (L \<cdot>l \<mu> \<cdot>l \<rho>) (C\<^sub>0 \<cdot> \<mu> \<cdot> \<rho>) \<gamma>\<^sub>\<rho>')))))"
      by auto
    hence "\<And>t. vars_term (t \<cdot>a \<rho>\<^sub>D) \<inter> (\<Union> (vars_cls ` (fset (N |\<union>| U |\<union>|
      clss_of_trail (trail_propagate \<Gamma> (L \<cdot>l \<mu> \<cdot>l \<rho>) (C\<^sub>0 \<cdot> \<mu> \<cdot> \<rho>) \<gamma>\<^sub>\<rho>'))))) = {}"
      unfolding \<rho>\<^sub>D_def by (rule vars_term_subst_term_Var_comp_renaming_disj)

    moreover have "vars_lit (L \<cdot>l \<mu> \<cdot>l \<rho>) \<subseteq> (\<Union> (vars_cls ` (fset (N |\<union>| U |\<union>|
      clss_of_trail (trail_propagate \<Gamma> (L \<cdot>l \<mu> \<cdot>l \<rho>) (C\<^sub>0 \<cdot> \<mu> \<cdot> \<rho>) \<gamma>\<^sub>\<rho>')))))"
      by force

    ultimately show "vars_term (atm_of L \<cdot>a \<mu> \<cdot>a \<rho>) \<inter> vars_term (atm_of L' \<cdot>a \<rho>\<^sub>D) = {}"
      by auto
  next
    have "\<And>x. x \<in> vars_term (atm_of L \<cdot>a \<mu> \<cdot>a \<rho>) \<Longrightarrow> vars_term (\<gamma>\<^sub>\<rho>' x) = {}"
      by (metis \<open>- (L \<cdot>l \<mu> \<cdot>l \<rho> \<cdot>l \<gamma>\<^sub>\<rho>') \<in># D \<cdot> \<gamma>\<^sub>D\<close> atm_of_uminus gr_D_\<gamma>\<^sub>D is_ground_atm_iff_vars_empty
          is_ground_atm_is_ground_on_var is_ground_cls_imp_is_ground_lit is_ground_lit_def
          atm_of_subst_lit)
    thus "(\<Union>x\<in>vars_term (atm_of L \<cdot>a \<mu> \<cdot>a \<rho>). if \<gamma>\<^sub>\<rho>' x = Var x then {} else vars_term (\<gamma>\<^sub>\<rho>' x)) \<inter>
      {x \<in> vars_term (atm_of L' \<cdot>a \<rho>\<^sub>D). rename_subst_domain \<rho>\<^sub>D \<gamma>\<^sub>D x \<noteq> Var x} = {}"
      by simp
  qed
  then obtain \<mu>' where 2: "is_mimgu \<mu>' {{atm_of (L \<cdot>l \<mu> \<cdot>l \<rho>), atm_of (L' \<cdot>l \<rho>\<^sub>D)}}"
    using is_mimgu_if_mgu_eq_Some by auto

  show ?thesis
    using resolveI[OF refl refl 1 2, of N \<beta> \<Gamma> "C\<^sub>0 \<cdot> \<mu> \<cdot> \<rho>" U "D' \<cdot> \<rho>\<^sub>D"]
    unfolding S\<^sub>2_def D_def by auto
qed

lemma factorize_preserves_resolvability:
  assumes reso: "resolve N \<beta> S\<^sub>1 S\<^sub>2" and fact: "factorize N \<beta> S\<^sub>1 S\<^sub>3" and
    invars: "trail_groundings (state_trail S\<^sub>1)" "conflict_disjoint_vars N S\<^sub>1"
  shows "\<exists>S\<^sub>4. resolve N \<beta> S\<^sub>3 S\<^sub>4"
  using reso
proof (cases N \<beta> S\<^sub>1 S\<^sub>2 rule: resolve.cases)
  case (resolveI \<Gamma> \<Gamma>' L C \<delta> \<rho> U D L' \<sigma> \<mu>)

  from fact obtain K K' \<mu>\<^sub>K \<sigma>' DD where
    S\<^sub>1_def: "S\<^sub>1 = (\<Gamma>, U, Some (DD + {#K, K'#}, \<sigma>))" and
    S\<^sub>3_def: "S\<^sub>3 = (\<Gamma>, U, Some ((DD + {#K#}) \<cdot> \<mu>\<^sub>K, \<sigma>'))" and
    "K \<cdot>l \<sigma> = K' \<cdot>l \<sigma>" and
    mimgu_\<mu>\<^sub>K: "is_mimgu \<mu>\<^sub>K {{atm_of K, atm_of K'}}" and
    \<sigma>'_def: "\<sigma>' = restrict_subst (vars_cls ((DD + {#K#}) \<cdot> \<mu>\<^sub>K)) \<sigma>"
    by (auto simp: \<open>S\<^sub>1 = (\<Gamma>, U, Some (D + {#L'#}, \<sigma>))\<close> elim: factorize.cases)

  have "add_mset L' D = add_mset K (add_mset K' DD)"
    using resolveI(1) S\<^sub>1_def by simp

  from mimgu_\<mu>\<^sub>K have "\<sigma> = \<mu>\<^sub>K \<odot> \<sigma>"
    using \<open>K \<cdot>l \<sigma> = K' \<cdot>l \<sigma>\<close>
    by (auto simp add: is_mimgu_def is_imgu_def is_unifiers_def is_unifier_alt
        intro!: subst_atm_of_eqI)

  have L_\<mu>\<^sub>K_\<sigma>'_simp: "L \<cdot>l \<mu>\<^sub>K \<cdot>l \<sigma>' = L \<cdot>l \<mu>\<^sub>K \<cdot>l \<sigma>" if L_in: "L \<in># add_mset K DD" for L
    unfolding \<sigma>'_def
    using L_in
    by (metis add_mset_add_single insert_DiffM subst_lit_restrict_subst_idem sup_ge1
        vars_cls_add_mset vars_lit_subst_subset_vars_cls_substI)

  have "L' \<cdot>l \<mu>\<^sub>K \<in># add_mset K DD \<cdot> \<mu>\<^sub>K"
  proof (cases "L' = K \<or> L' = K'")
    case True
    moreover have "K \<cdot>l \<mu>\<^sub>K = K' \<cdot>l \<mu>\<^sub>K"
      using mimgu_\<mu>\<^sub>K[unfolded is_mimgu_def, THEN conjunct1, unfolded is_imgu_def, THEN conjunct1,
          unfolded is_unifiers_def, simplified]
      by (metis (no_types, opaque_lifting) \<open>K \<cdot>l \<sigma> = K' \<cdot>l \<sigma>\<close> atm_of_subst_lit finite.emptyI
          finite.insertI insertCI is_unifier_subst_atm_eqI literal.expand subst_lit_is_neg)
    ultimately have "L' \<cdot>l \<mu>\<^sub>K = K \<cdot>l \<mu>\<^sub>K"
      by presburger
    thus ?thesis
      by simp
  next
    case False
    hence "L' \<in># DD"
      by (metis \<open>add_mset L' D = add_mset K (add_mset K' DD)\<close> insert_iff set_mset_add_mset_insert)
    thus ?thesis
      by auto
  qed
  then obtain DDD where "add_mset K DD \<cdot> \<mu>\<^sub>K = add_mset L' DDD \<cdot> \<mu>\<^sub>K"
    by (smt (verit, best) Melem_subst_cls mset_add subst_cls_add_mset)

  moreover have "L \<cdot>l \<delta> = - (L' \<cdot>l \<mu>\<^sub>K \<cdot>l \<sigma>')"
  proof -
    have "L' \<cdot>l \<mu>\<^sub>K \<cdot>l \<sigma>' = L' \<cdot>l \<mu>\<^sub>K \<cdot>l \<sigma>"
      using L_\<mu>\<^sub>K_\<sigma>'_simp
      by (metis Melem_subst_cls \<open>L' \<cdot>l \<mu>\<^sub>K \<in># add_mset K DD \<cdot> \<mu>\<^sub>K\<close>)
    also have "... = L' \<cdot>l \<sigma>"
      using \<open>\<sigma> = \<mu>\<^sub>K \<odot> \<sigma>\<close>
      by (metis subst_lit_comp_subst)
    finally show ?thesis
      using resolveI by simp
  qed

  moreover obtain \<mu>\<mu> where "is_mimgu \<mu>\<mu> {{atm_of L, atm_of L' \<cdot>a \<mu>\<^sub>K}}"
  proof -
    assume "\<And>\<mu>\<mu>. is_mimgu \<mu>\<mu> {{atm_of L, atm_of L' \<cdot>a \<mu>\<^sub>K}} \<Longrightarrow> thesis"
    moreover have "\<exists>\<mu>. Unification.mgu (atm_of L) (atm_of L' \<cdot>a \<mu>\<^sub>K) = Some \<mu>"
    proof (rule ex_mgu_if_subst_eq_subst_and_disj_vars)
      show "atm_of L \<cdot>a \<delta> = atm_of L' \<cdot>a \<mu>\<^sub>K \<cdot>a \<sigma>'"
        using \<open>L \<cdot>l \<delta> = - (L' \<cdot>l \<mu>\<^sub>K \<cdot>l \<sigma>')\<close>
        by (metis atm_of_subst_lit atm_of_uminus)
    next
      have "vars_lit L \<inter> vars_lit L' = {}"
        using invars(2)[unfolded resolveI]
        by (auto simp: conflict_disjoint_vars_def)

      have "vars_lit L \<inter> vars_cls (add_mset L' D) = {}"
        using invars(2)[unfolded resolveI]
        by (auto simp: conflict_disjoint_vars_def)

      moreover have "vars_term (atm_of L' \<cdot>a \<mu>\<^sub>K) \<subseteq> vars_cls (add_mset L' D)"
      proof -
        have "vars_lit K \<union> vars_lit K' \<subseteq> vars_cls (add_mset L' D)"
          by (simp add: \<open>add_mset L' D = add_mset K (add_mset K' DD)\<close> subsetI)

        moreover have "vars_lit L' \<subseteq> vars_cls (add_mset L' D)"
          using \<open>add_mset L' D = add_mset K (add_mset K' DD)\<close>
          by (metis Un_upper1 vars_cls_add_mset)

        ultimately show ?thesis
          using mimgu_\<mu>\<^sub>K[unfolded is_mimgu_def, THEN conjunct2, simplified]
            vars_term_subst_apply_term_subset
          by fastforce
      qed

      ultimately show "vars_lit L \<inter> vars_term (atm_of L' \<cdot>a \<mu>\<^sub>K) = {}"
        by auto
    next
      have "is_ground_cls (add_mset L C \<cdot> \<delta>)"
        using invars(1)[unfolded resolveI]
        by (simp add: trail_groundings_def trail_propagate_def)
      hence "is_ground_lit (L \<cdot>l \<delta>)"
        by (metis is_ground_cls_def subst_cls_add_mset union_single_eq_member)
      hence "\<forall>x\<in>vars_lit L. vars_term (\<delta> x) = {}"
        by (meson is_ground_atm_iff_vars_empty is_ground_lit_is_ground_on_var)
      hence "(\<Union>x\<in>vars_lit L. if \<delta> x = Var x then {} else vars_term (\<delta> x)) = {}"
        by force
      thus "(\<Union>x\<in>vars_lit L. if \<delta> x = Var x then {} else vars_term (\<delta> x)) \<inter>
        {x \<in> vars_term (atm_of L' \<cdot>a \<mu>\<^sub>K). \<sigma>' x \<noteq> Var x} = {}"
        by simp
    qed
    ultimately show ?thesis
      using is_mimgu_if_mgu_eq_Some by blast
  qed

  ultimately show ?thesis
    unfolding S\<^sub>3_def
    using resolve.resolveI[OF \<open>\<Gamma> = trail_propagate \<Gamma>' L C \<delta>\<close> refl,
        of "L' \<cdot>l \<mu>\<^sub>K" \<sigma>' _ N \<beta> U "DDD \<cdot> \<mu>\<^sub>K", simplified]
    by auto
qed

text \<open>The following lemma corresponds to Lemma 7 in the paper.\<close>

lemma no_backtrack_after_conflict_if:
  assumes conf: "conflict N \<beta> S1 S2" and trail_S2: "state_trail S1 = trail_propagate \<Gamma> L C \<gamma>"
  shows "\<nexists>S4. backtrack N \<beta> S2 S4"
proof -
  from trail_S2 conf have "state_trail S2 = trail_propagate \<Gamma> L C \<gamma>"
    unfolding conflict.simps by auto
  then show ?thesis
    unfolding backtrack.simps trail_propagate_def trail_decide_def
    by auto
qed

lemma skip_state_trail: "skip N \<beta> S S' \<Longrightarrow> suffix (state_trail S') (state_trail S)"
  by (auto simp: suffix_def elim: skip.cases)

lemma factorize_state_trail: "factorize N \<beta> S S' \<Longrightarrow> state_trail S' = state_trail S"
  by (auto elim: factorize.cases)

lemma resolve_state_trail: "resolve N \<beta> S S' \<Longrightarrow> state_trail S' = state_trail S"
  by (auto elim: resolve.cases)

lemma mempty_not_in_initial_clauses_if_run_leads_to_trail:
  assumes
    reg_run: "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S1" and
    trail_lit: "state_trail S1 = Lc # \<Gamma>"
  shows "{#} |\<notin>| N"
proof (rule notI)
  assume "{#} |\<in>| N"
  hence "conflict N \<beta> initial_state ([], {||}, Some ({#}, Var))"
    by (rule conflict_initial_state_if_mempty_in_intial_clauses)
  moreover hence "\<nexists>S'. local.scl N \<beta> ([], {||}, Some ({#}, Var)) S'"
    using no_more_step_if_conflict_mempty by simp
  ultimately show False
    using trail_lit
    by (metis (no_types, opaque_lifting) conflict_initial_state_only_with_mempty converse_rtranclpE
        list.discI prod.sel(1) reasonable_if_regular reg_run regular_scl_def scl_if_reasonable
        state_trail_def)
qed

(*
after conflict, one can apply factorize arbitrarily often,
but resolve must be applied at least once.

Prove this lemma!
conflict in reg run \<Longrightarrow> ALL following runs have the following shape:
  factorize* then resolve then (skip or factorize or resolve)*
*)

lemma conflict_with_literal_gets_resolved:
  assumes
    trail_lit: "state_trail S1 = Lc # \<Gamma>" and
    conf: "conflict N \<beta> S1 S2" and
    resolution: "(skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S2 Sn" and
    backtrack: "\<exists>Sn'. backtrack N \<beta> Sn Sn'" and
    mempty_not_in_init_clss: "{#} |\<notin>| N" and
    invars: "learned_nonempty S1" "trail_propagated_or_decided' N \<beta> S1" "no_conflict_after_decide' N \<beta> S1"
  shows "\<not> is_decision_lit Lc \<and> strict_suffix (state_trail Sn) (state_trail S1)"
proof -
  obtain S0 where propa: "propagate N \<beta> S0 S1"
    using mempty_not_in_init_clss before_reasonable_conflict[OF conf \<open>learned_nonempty S1\<close>
        \<open>trail_propagated_or_decided' N \<beta> S1\<close> \<open>no_conflict_after_decide' N \<beta> S1\<close>] by metis

  from trail_lit propa have "\<not> is_decision_lit Lc"
    by (auto simp: trail_propagate_def is_decision_lit_def elim!: propagate.cases)

  show ?thesis
  proof (rule conjI)
    show "\<not> is_decision_lit Lc"
      by (rule \<open>\<not> is_decision_lit Lc\<close>)
  next
    show "strict_suffix (state_trail Sn) (state_trail S1)"
      unfolding strict_suffix_def
    proof (rule conjI)
      from conf have "state_trail S2 = state_trail S1"
        by (auto elim: conflict.cases)
      moreover from resolution have "suffix (state_trail Sn) (state_trail S2)"
      proof (induction Sn rule: rtranclp_induct)
        case base
        thus ?case
          by simp
      next
        case (step y z)
        from step.hyps(2) have "suffix (state_trail z) (state_trail y)"
          by (auto simp: suffix_def factorize_state_trail resolve_state_trail
              dest: skip_state_trail)
        with step.IH show ?case
          by (auto simp: suffix_def)
      qed
      ultimately show "suffix (state_trail Sn) (state_trail S1)"
        by simp
    next
      from backtrack \<open>\<not> is_decision_lit Lc\<close> show "state_trail Sn \<noteq> state_trail S1"
        unfolding trail_lit
        by (auto simp: trail_decide_def is_decision_lit_def elim!: backtrack.cases)
    qed
  qed
qed


section \<open>Clause Redundancy\<close>

definition ground_redundant where
  "ground_redundant lt N C \<longleftrightarrow>
    is_ground_clss N \<and> is_ground_cls C \<and> {D \<in> N. lt\<^sup>=\<^sup>= D C} \<TTurnstile>e {C}"

definition redundant where
  "redundant lt N C \<longleftrightarrow>
    (\<forall>C' \<in> grounding_of_cls C. ground_redundant lt (grounding_of_clss N) C')"

lemma ground_redundant_mono_strong:
  "ground_redundant R N C \<Longrightarrow> (\<And>x. x \<in> N \<Longrightarrow> x \<noteq> C \<Longrightarrow> R x C \<Longrightarrow> S x C) \<Longrightarrow> ground_redundant S N C"
  unfolding ground_redundant_def
  apply (simp add: true_clss_def)
  by blast

lemma redundant_mono_strong:
  "redundant R N C \<Longrightarrow>
    (\<And>x y. x \<in> grounding_of_clss N \<Longrightarrow> y \<in> grounding_of_cls C \<Longrightarrow> x \<noteq> y \<Longrightarrow> R x y \<Longrightarrow> S x y) \<Longrightarrow>
  redundant S N C"
  by (auto simp: redundant_def
      intro: ground_redundant_mono_strong[of R "grounding_of_clss N" _ S])

lemma redundant_multp_if_redundant_strict_subset:
  "redundant (\<subset>#) N C \<Longrightarrow> redundant (multp (trail_less_ex lt Ls)) N C"
  by (auto intro: subset_implies_multp elim!: redundant_mono_strong)

lemma redundant_multp_if_redundant_subset:
  "redundant (\<subseteq>#) N C \<Longrightarrow> redundant (multp (trail_less_ex lt Ls)) N C"
  by (auto intro: subset_implies_multp elim!: redundant_mono_strong)

lemma not_bex_subset_mset_if_not_ground_redundant:
  assumes "is_ground_cls C" and "is_ground_clss N"
  shows "\<not> ground_redundant (\<subset>#) N C \<Longrightarrow> \<not> (\<exists>D \<in> N. D \<subseteq># C)"
  using assms unfolding ground_redundant_def
  apply (simp add: true_cls_def true_clss_def)
  apply (elim exE conjE)
  apply (rule ballI)
  subgoal premises prems for I D
    using prems(3)[rule_format, of D] prems(1,2,4-)
    apply simp
    by (meson mset_subset_eqD subset_mset.nless_le)
  done


section \<open>Trail-Induced Ordering\<close>

subsection \<open>Miscellaneous Lemmas\<close>

lemma pairwise_distinct_if_sound_trail:
  fixes \<Gamma>
  defines "Ls \<equiv> (map fst \<Gamma>)"
  shows "sound_trail N \<Gamma> \<Longrightarrow>
    \<forall>i < length Ls. \<forall>j < length Ls. i \<noteq> j \<longrightarrow> Ls ! i \<noteq> Ls ! j \<and> Ls ! i \<noteq> - (Ls ! j)"
  unfolding Ls_def
proof (induction \<Gamma> rule: sound_trail.induct)
  case Nil
  show ?case by simp
next
  case (Cons \<Gamma> L u)
  from Cons.hyps have L_distinct:
    "\<forall>x < length (map fst \<Gamma>). map fst \<Gamma> ! x \<noteq> L"
    "\<forall>x < length (map fst \<Gamma>). map fst \<Gamma> ! x \<noteq> - L"
    unfolding trail_defined_lit_def de_Morgan_disj
    unfolding image_set in_set_conv_nth not_ex de_Morgan_conj disj_not1
    by simp_all
  show ?case
    unfolding list.map prod.sel
  proof (intro allI impI)
    fix i j :: nat
    assume i_lt: "i < length (L # map fst \<Gamma>)" and j_lt: "j < length (L # map fst \<Gamma>)" and "i \<noteq> j"
    show
      "(L # map fst \<Gamma>) ! i \<noteq> (L # map fst \<Gamma>) ! j \<and>
       (L # map fst \<Gamma>) ! i \<noteq> - (L # map fst \<Gamma>) ! j"
    proof (cases i)
      case 0
      thus ?thesis
        using L_distinct \<open>i \<noteq> j\<close> \<open>j < length (L # map fst \<Gamma>)\<close>
        using gr0_conv_Suc by auto
    next
      case (Suc k)
      then show ?thesis
        apply simp
        using i_lt j_lt \<open>i \<noteq> j\<close> L_distinct Cons.IH[rule_format]
        using less_Suc_eq_0_disj by force
    qed
  qed
qed


subsection \<open>Strict Partial Order\<close>

lemma irreflp_trail_less_if_sound: "sound_trail N \<Gamma> \<Longrightarrow> irreflp (trail_less (map fst \<Gamma>))"
  using irreflp_trail_less[OF
      Clausal_Logic.uminus_not_id'
      Clausal_Logic.uminus_of_uminus_id
      pairwise_distinct_if_sound_trail]
  by assumption

lemma transp_trail_less_if_sound: "sound_trail N \<Gamma> \<Longrightarrow> transp (trail_less (map fst \<Gamma>))"
  using transp_trail_less[OF
      Clausal_Logic.uminus_not_id'
      Clausal_Logic.uminus_of_uminus_id
      pairwise_distinct_if_sound_trail]
  by assumption

lemma asymp_trail_less_if_sound: "sound_trail N \<Gamma> \<Longrightarrow> asymp (trail_less (map fst \<Gamma>))"
  using asymp_trail_less[OF
      Clausal_Logic.uminus_not_id'
      Clausal_Logic.uminus_of_uminus_id
      pairwise_distinct_if_sound_trail]
  by assumption


subsection \<open>Extension on All Literals\<close>

lemma transp_trail_less_ex_if_sound: "sound_trail N \<Gamma> \<Longrightarrow> transp lt \<Longrightarrow> transp (trail_less_ex lt (map fst \<Gamma>))"
  using transp_trail_less_ex[OF
      Clausal_Logic.uminus_not_id'
      Clausal_Logic.uminus_of_uminus_id
      pairwise_distinct_if_sound_trail]
  by assumption

lemma asymp_trail_less_ex_if_sound:
  "sound_trail N \<Gamma> \<Longrightarrow> asymp lt \<Longrightarrow> asymp (trail_less_ex lt (map fst \<Gamma>))"
  using asymp_trail_less_ex[OF
      Clausal_Logic.uminus_not_id'
      Clausal_Logic.uminus_of_uminus_id
      pairwise_distinct_if_sound_trail]
  by assumption


subsection \<open>Properties\<close>

lemma trail_defined_if_trail_less_ex:
  "trail_less_ex lt (map fst \<Gamma>) L K \<Longrightarrow> trail_defined_lit \<Gamma> K \<Longrightarrow> trail_defined_lit \<Gamma> L"
  by (metis (no_types, opaque_lifting) list.set_map trail_defined_lit_def trail_less_ex_def)

lemma trail_defined_cls_if_lt_defined:
  assumes sound_\<Gamma>: "sound_trail N \<Gamma>" and
    transp_lt: "transp lt" and
    C_lt_D: "multp (trail_less_ex lt (map fst \<Gamma>)) C D" and
    tr_def_D: "trail_defined_cls \<Gamma> D"
  shows "trail_defined_cls \<Gamma> C"
proof -
  have transp_tr_lt_ex: "transp (trail_less_ex lt (map fst \<Gamma>))"
    by (rule transp_trail_less_ex_if_sound[OF sound_\<Gamma> transp_lt])

  from multp_implies_one_step[OF transp_tr_lt_ex C_lt_D]
  obtain I J K where D_def: "D = I + J" and C_def: "C = I + K" and "J \<noteq> {#}" and
    *: "\<forall>k\<in>#K. \<exists>x\<in>#J. trail_less_ex lt (map fst \<Gamma>) k x"
    by auto

  show ?thesis
    unfolding trail_defined_cls_def
  proof (rule ballI)
    fix L assume L_in: "L \<in># C"
    show "trail_defined_lit \<Gamma> L"
    proof (cases "L \<in># I")
      case True
      then show ?thesis
        using tr_def_D D_def
        by (simp add: trail_defined_cls_def)
    next
      case False
      with C_def L_in have "L \<in># K" by fastforce
      then obtain L' where L'_in: "L'\<in>#J" and "trail_less_ex lt (map fst \<Gamma>) L L'"
        using * by blast
      moreover have "trail_defined_lit \<Gamma> L'"
        using tr_def_D D_def L'_in
        by (simp add: trail_defined_cls_def)
      ultimately show ?thesis
        by (auto intro: trail_defined_if_trail_less_ex)
    qed
  qed
qed


section \<open>Learned Clauses in Regular Runs\<close>

lemma regular_run_if_skip_factorize_resolve_run:
  assumes "(skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S S'"
  shows "(regular_scl N \<beta>)\<^sup>*\<^sup>* S S'"
  using assms
proof (induction S' rule: rtranclp_induct)
  case base
  show ?case by simp
next
  case (step S' S'')
  from step.hyps(2) have "scl N \<beta> S' S''"
    unfolding scl_def by blast
  with step.hyps(2) have "reasonable_scl N \<beta> S' S''"
    using reasonable_scl_def decide_well_defined(4) decide_well_defined(5) skip_well_defined(2)
    by blast
  moreover from step.hyps(2) have "\<not> Ex (conflict N \<beta> S')"
    apply simp
    by (smt (verit, best) conflict.cases factorize.simps option.distinct(1) resolve.simps skip.simps
        state_conflict_simp)
  ultimately have "regular_scl N \<beta> S' S''"
    by (simp add: regular_scl_def)
  with step.IH show ?case
    by simp
qed

lemma not_trail_true_and_false_lit:
  "sound_trail N \<Gamma> \<Longrightarrow> \<not> (trail_true_lit \<Gamma> L \<and> trail_false_lit \<Gamma> L)"
  apply (simp add: trail_true_lit_def trail_false_lit_def)
  by (metis (no_types, lifting) in_set_conv_nth list.set_map pairwise_distinct_if_sound_trail
      uminus_not_id')

lemma not_trail_true_and_false_cls: "sound_trail N \<Gamma> \<Longrightarrow> \<not> (trail_true_cls \<Gamma> C \<and> trail_false_cls \<Gamma> C)"
  using not_trail_true_and_false_lit
  by (metis trail_false_cls_def trail_true_cls_def)

theorem learned_clauses_in_regular_runs_invars:
  assumes
    sound_S0: "sound_state N \<beta> S0" and
    invars: "learned_nonempty S0" "conflict_disjoint_vars N S0"
      "trail_propagated_or_decided' N \<beta> S0" "no_conflict_after_decide' N \<beta> S0"
      "almost_no_conflict_with_trail N \<beta> S0" and
    conflict: "conflict N \<beta> S0 S1" and
    resolution: "(skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>+\<^sup>+ S1 Sn" and
    backtrack: "backtrack N \<beta> Sn Sn'" and
    "transp lt"
  defines
    "trail_ord \<equiv> multp (trail_less_ex lt (map fst (state_trail S1)))" and
    "U \<equiv> state_learned S1"
  shows "(\<exists>C \<gamma>. state_conflict Sn = Some (C, \<gamma>) \<and>
      C \<cdot> \<gamma> \<notin> grounding_of_clss (fset N \<union> fset U) \<and>
      set_mset (C \<cdot> \<gamma>) \<notin> set_mset ` grounding_of_clss (fset N \<union> fset U) \<and>
      \<not> redundant trail_ord (fset N \<union> fset U) C)"
proof -
  from conflict have "almost_no_conflict_with_trail N \<beta> S1"
    using \<open>almost_no_conflict_with_trail N \<beta> S0\<close>
    by (rule conflict_preserves_almost_no_conflict_with_trail)

  from conflict obtain C1 \<gamma>1 where conflict_S1: "state_conflict S1 = Some (C1, \<gamma>1)"
    by (smt (verit, best) conflict.simps state_conflict_simp)
  with backtrack obtain Cn \<gamma>n where conflict_Sn: "state_conflict Sn = Some (Cn, \<gamma>n)" and "Cn \<noteq> {#}"
    by (auto elim: backtrack.cases)
  with resolution conflict_S1 have "C1 \<noteq> {#}"
  proof (induction Sn arbitrary: C1 \<gamma>1 Cn \<gamma>n rule: tranclp_induct)
    case (base y)
    then show ?case
      by (auto elim: skip.cases factorize.cases resolve.cases)
  next
    case (step y z)
    from step.prems step.hyps obtain Cy \<gamma>y where
      conf_y: "state_conflict y = Some (Cy, \<gamma>y)" and "Cy \<noteq> {#}"
      by (auto elim: skip.cases factorize.cases resolve.cases)
    show ?case
      using step.IH[OF _ conf_y \<open>Cy \<noteq> {#}\<close>] step.prems
      by simp
  qed

  from conflict sound_S0 have sound_S1: "sound_state N \<beta> S1"
    by (simp add: conflict_sound_state)
  with resolution have sound_Sn: "sound_state N \<beta> Sn"
    by (induction rule: tranclp_induct)
      (auto intro: skip_sound_state factorize_sound_state resolve_sound_state)

  from conflict_Sn sound_Sn have "fset N \<TTurnstile>\<G>e {Cn}" and
    trail_Sn_false_Cn_\<gamma>n: "trail_false_cls (state_trail Sn) (Cn \<cdot> \<gamma>n)"
    by (auto simp add: sound_state_def)

  from conflict_S1 sound_S1 have trail_S1_false_C1_\<gamma>1: "trail_false_cls (state_trail S1) (C1 \<cdot> \<gamma>1)"
    by (auto simp add: sound_state_def)

  from resolution have "suffix (state_trail Sn) (state_trail S1) \<and>
    (\<exists>Cn \<gamma>n. state_conflict Sn = Some (Cn, \<gamma>n) \<and> trail_false_cls (state_trail S1) (Cn \<cdot> \<gamma>n))"
  proof (induction Sn rule: tranclp_induct)
    case (base S2)
    thus ?case
    proof (elim sup2E)
      assume "skip N \<beta> S1 S2"
      thus ?thesis
        using conflict_S1 skip.simps suffix_ConsI trail_S1_false_C1_\<gamma>1 by fastforce
    next
      assume "factorize N \<beta> S1 S2"
      moreover with sound_S1 have "sound_state N \<beta> S2"
        by (auto intro: factorize_sound_state)
      ultimately show ?thesis
        by (cases N \<beta> S1 S2 rule: factorize.cases) (simp add: sound_state_def)
    next
      assume "resolve N \<beta> S1 S2"
      moreover with sound_S1 have "sound_state N \<beta> S2"
        by (auto intro: resolve_sound_state)
      ultimately show ?thesis
        by (cases N \<beta> S1 S2 rule: resolve.cases) (simp add: sound_state_def)
    qed
  next
    case (step Sm Sm')
    from step.hyps(2) have "suffix (state_trail Sm') (state_trail Sm)"
      by (smt (verit) factorize.simps prod.sel(1) resolve.simps skip.simps state_trail_def
          suffix_ConsI suffix_order.eq_iff sup2E)
    with step.IH have "suffix (state_trail Sm') (state_trail S1)"
      by force

    from step.hyps(1) sound_S1 have sound_Sm: "sound_state N \<beta> Sm"
      by (induction rule: tranclp_induct)
        (auto intro: skip_sound_state factorize_sound_state resolve_sound_state)

    from step.IH obtain Cm \<gamma>m where
      conflict_Sm: "state_conflict Sm = Some (Cm, \<gamma>m)" and
      trail_false_Cm_\<gamma>m: "trail_false_cls (state_trail S1) (Cm \<cdot> \<gamma>m)"
      using step.prems step.hyps(2) \<open>suffix (state_trail Sm') (state_trail Sm)\<close>
      by auto

    from step.hyps(2) show ?case
    proof (elim sup2E)
      assume "skip N \<beta> Sm Sm'"
      thus ?thesis
        using \<open>suffix (state_trail Sm') (state_trail S1)\<close>
        using conflict_Sm skip.simps trail_false_Cm_\<gamma>m by auto
    next
      assume "factorize N \<beta> Sm Sm'"
      thus ?thesis
      proof (cases N \<beta> Sm Sm' rule: factorize.cases)
        case (factorizeI L \<sigma> L' \<mu> \<sigma>' D \<Gamma> U)
        with conflict_Sm have Cm_def: "Cm = D + {#L, L'#}" and \<gamma>m_def: "\<gamma>m = \<sigma>"
          by simp_all
        with factorizeI(3,4) have "trail_false_cls (state_trail S1) ((D + {#L#}) \<cdot> \<mu> \<cdot> \<sigma>)"
          apply -
          apply (rule trail_false_cls_subst_mgu_before_grounding[of _ _ L L'])
          using trail_false_Cm_\<gamma>m apply simp
           apply auto
          by (smt (verit, best) atm_of_subst_lit finite.emptyI finite.insertI insertE is_unifier_alt
              is_unifiers_def singletonD)
        with factorizeI(5) have "trail_false_cls (state_trail S1) ((D + {#L#}) \<cdot> \<mu> \<cdot> \<sigma>')"
          by (metis subsetI subst_cls_restrict_subst_idem)
        with factorizeI(2) show ?thesis
          using \<open>suffix (state_trail Sm') (state_trail S1)\<close>
          using state_conflict_simp by blast
      qed
    next
      assume "resolve N \<beta> Sm Sm'"
      thus ?thesis
      proof (cases N \<beta> Sm Sm' rule: resolve.cases)
        case (resolveI \<Gamma> \<Gamma>' L C \<delta> \<rho> U D L' \<sigma> \<mu>)
        have "is_renaming (renaming_wrt (fset (N |\<union>| U |\<union>| clss_of_trail \<Gamma> |\<union>| {|D + {#L'#}|})))"
          apply (rule is_renaming_renaming_wrt)
          using resolveI
          by (smt (verit, best) finite_fset sound_Sm sound_state_def state_learned_simp)
        with resolveI have is_renaming_\<rho>: "is_renaming \<rho>"
          by simp

        from resolveI conflict_Sm have Cm_def: "Cm = D + {#L'#}" and \<gamma>m_def: "\<gamma>m = \<sigma>"
          by simp_all
        hence tr_false_D_L'_\<sigma>: "trail_false_cls (state_trail S1) ((D + {#L'#}) \<cdot> \<sigma>)"
          using trail_false_Cm_\<gamma>m by simp

        from resolveI sound_Sm have
          "disjoint_vars_set (fset (N |\<union>| U |\<union>| clss_of_trail \<Gamma>))" and
          disj_N_U_\<Gamma>_D_L': "\<forall>C \<in> fset (N |\<union>| U |\<union>| clss_of_trail \<Gamma>). disjoint_vars (D + {#L'#}) C" and
          "is_ground_cls ((D + {#L'#}) \<cdot> \<sigma>)" and
          dom_\<sigma>: "subst_domain \<sigma> \<subseteq> vars_cls (D + {#L'#})" and
          "sound_trail N \<Gamma>"
          unfolding sound_state_def by simp_all

        have "vars_cls (D + {#L'#}) \<inter> vars_cls (C + {#L#}) = {}"
          apply(rule disj_N_U_\<Gamma>_D_L'[unfolded disjoint_vars_iff_inter_empty,
                rule_format, of "C + {#L#}"])
          by (simp add: resolveI(3))

        from resolveI have "atm_of (L \<cdot>l \<delta>) = atm_of (L' \<cdot>l \<sigma>)" by simp
        hence "(atm_of L) \<cdot>a \<delta> = (atm_of L') \<cdot>a \<sigma>" by simp

        have \<sigma>_\<delta>_in_unif: "\<sigma> \<odot> \<delta> \<in> unifiers {(atm_of L, atm_of L')}"
        proof (rule subst_compose_in_unifiersI(2))
          show "atm_of L \<cdot>a \<delta> = atm_of L' \<cdot>a \<sigma>"
            using resolveI by (metis atm_of_eq_uminus_if_lit_eq atm_of_subst_lit)
        next
          show "vars_lit L \<inter> subst_domain \<sigma> = {}"
            using dom_\<sigma> \<open>vars_cls (D + {#L'#}) \<inter> vars_cls (C + {#L#}) = {}\<close> by fastforce
        next
          have "subst_domain \<delta> \<subseteq> vars_cls C \<union> vars_lit L"
            using \<open>sound_trail N \<Gamma>\<close>
            unfolding sound_trail.simps[of N \<Gamma>]
            unfolding resolveI(3)
            by (simp add: trail_propagate_def)
          then show "vars_lit L' \<inter> subst_domain \<delta> = {}"
            using \<open>vars_cls (D + {#L'#}) \<inter> vars_cls (C + {#L#}) = {}\<close> by auto
        next
          have "range_vars \<sigma> = {}"
            unfolding range_vars_def UNION_empty_conv subst_range.simps
            using dom_\<sigma> \<open>is_ground_cls ((D + {#L'#}) \<cdot> \<sigma>)\<close> is_ground_cls_is_ground_on_var
              is_ground_atm_iff_vars_empty
            by fast
          thus "range_vars \<sigma> \<inter> subst_domain \<delta> = {}"
            by simp
        qed

        from resolveI \<open>sound_trail N \<Gamma>\<close> have "trail_false_cls \<Gamma>' (C \<cdot> \<delta>)"
          by (auto simp: trail_propagate_def elim: sound_trail.cases)

        from resolveI have "suffix \<Gamma>' (state_trail S1)"
          using \<open>suffix (state_trail Sm') (state_trail S1)\<close>
          by (metis (no_types, lifting) state_trail_simp suffix_order.trans suffix_trail_propagate)

        have "trail_false_cls (state_trail S1) ((D + C) \<cdot> \<mu> \<cdot> \<sigma> \<cdot> \<delta>)"
        proof (rule trail_false_cls_plus_subst_mgu_before_groundings[
              of "state_trail S1" D L' \<sigma> _ C \<delta> L \<mu>, OF tr_false_D_L'_\<sigma> \<open>trail_false_cls \<Gamma>' (C \<cdot> \<delta>)\<close>
                \<open>suffix \<Gamma>' (state_trail S1)\<close> \<open>is_ground_cls ((D + {#L'#}) \<cdot> \<sigma>)\<close>
                \<open>vars_cls (D + {#L'#}) \<inter> vars_cls (C + {#L#}) = {}\<close>
                \<open>subst_domain \<sigma> \<subseteq> vars_cls (D + {#L'#})\<close>])
          from resolveI show "is_imgu \<mu> {{atm_of L, atm_of L'}}"
            by auto
        next
          have "\<forall>A \<in> {atm_of L, atm_of L'}. \<forall>B \<in> {atm_of L, atm_of L'}. A \<cdot>a (\<sigma> \<odot> \<delta>) = B \<cdot>a (\<sigma> \<odot> \<delta>)"
            using \<sigma>_\<delta>_in_unif by fastforce
          hence "is_unifier (\<sigma> \<odot> \<delta>) {atm_of L, atm_of L'}"
            using is_unifier_alt[of "{atm_of L, atm_of L'}" "\<sigma> \<odot> \<delta>"]
            by blast
          thus "is_unifiers (\<sigma> \<odot> \<delta>) {{atm_of L, atm_of L'}}"
            using is_unifiers_def by blast
        qed
        then have "trail_false_cls (state_trail S1) ((D + C) \<cdot> \<mu> \<cdot> \<rho> \<cdot>
          restrict_subst (vars_cls ((D + C) \<cdot> \<mu> \<cdot> \<rho>)) (inv_renaming' \<rho> \<odot> \<sigma> \<odot> \<delta>))"
          unfolding subst_cls_restrict_subst_idem[OF subset_refl]
          unfolding subst_cls_comp_subst subst_cls_renaming_inv_renaming_idem[OF is_renaming_\<rho>]
          by assumption
        then show ?thesis
          using \<open>suffix (state_trail Sm') (state_trail S1)\<close>
          using resolveI by simp
      qed
    qed
  qed

  with conflict_Sn have
    "suffix (state_trail Sn) (state_trail S1)" and
    tr_false_S1_Cn_\<gamma>n: "trail_false_cls (state_trail S1) (Cn \<cdot> \<gamma>n)"
    by auto

  from sound_Sn conflict_Sn have Cn_\<gamma>n_in: "Cn \<cdot> \<gamma>n \<in> grounding_of_cls Cn"
    unfolding sound_state_def
    using grounding_of_cls_ground grounding_of_subst_cls_subset
    by fastforce

  from sound_S1 have sound_trail_S1: "sound_trail N (state_trail S1)"
    by (auto simp add: sound_state_def)
  hence tr_consistent_S1: "trail_consistent (state_trail S1)"
    by (rule trail_consistent_if_sound)

  have "\<forall>L\<in>#Cn \<cdot> \<gamma>n. trail_defined_lit (state_trail S1) L"
    using tr_false_S1_Cn_\<gamma>n trail_defined_lit_iff_true_or_false trail_false_cls_def by blast
  hence "trail_interp (state_trail S1) \<TTurnstile> Cn \<cdot> \<gamma>n \<longleftrightarrow> trail_true_cls (state_trail S1) (Cn \<cdot> \<gamma>n)"
    using tr_consistent_S1 trail_true_cls_iff_trail_interp_entails by auto
  hence not_trail_S1_entails_Cn_\<gamma>n: "\<not> trail_interp (state_trail S1) \<TTurnstile>s {Cn \<cdot> \<gamma>n}"
    using tr_false_S1_Cn_\<gamma>n not_trail_true_and_false_cls[OF sound_trail_S1] by auto

  have "trail_defined_cls (state_trail S1) (Cn \<cdot> \<gamma>n)"
    using \<open>\<forall>L\<in>#Cn \<cdot> \<gamma>n. trail_defined_lit (state_trail S1) L\<close> trail_defined_cls_def by blast

  have "{#} |\<notin>| N"
    by (rule mempty_not_in_initial_clauses_if_non_empty_regular_conflict[OF conflict_S1 \<open>C1 \<noteq> {#}\<close>
          \<open>almost_no_conflict_with_trail N \<beta> S1\<close> sound_S1])
  then obtain S where "propagate N \<beta> S S0"
    using before_reasonable_conflict[OF conflict \<open>learned_nonempty S0\<close>
        \<open>trail_propagated_or_decided' N \<beta> S0\<close> \<open>no_conflict_after_decide' N \<beta> S0\<close>]
    by auto

  have "state_learned S = state_learned S0"
    using \<open>propagate N \<beta> S S0\<close> by (auto simp add: propagate.simps)
  also from conflict have "... = state_learned S1"
    by (auto simp add: conflict.simps)
  finally have "state_learned S = state_learned S1"
    by assumption

  have "state_conflict S = None"
    using \<open>propagate N \<beta> S S0\<close> by (auto simp add: propagate.simps)

  from conflict have "state_trail S1 = state_trail S0"
    by (smt (verit) conflict.cases state_trail_simp)

  obtain L C \<gamma> where trail_S0_eq: "state_trail S0 = trail_propagate (state_trail S) L C \<gamma>"
    using \<open>propagate N \<beta> S S0\<close> unfolding propagate.simps by auto

  with backtrack have "strict_suffix (state_trail Sn) (state_trail S0)"
    using conflict_with_literal_gets_resolved[OF _ conflict resolution[THEN tranclp_into_rtranclp] _
        \<open>{#} |\<notin>| N\<close> \<open>learned_nonempty S0\<close> \<open>trail_propagated_or_decided' N \<beta> S0\<close>
        \<open>no_conflict_after_decide' N \<beta> S0\<close>]
    by (metis (no_types, lifting) trail_propagate_def)
  hence "suffix (state_trail Sn) (state_trail S)"
    unfolding trail_S0_eq trail_propagate_def
    by (metis suffix_Cons suffix_order.le_less suffix_order.less_irrefl)

  moreover have "\<not> trail_defined_lit (state_trail S) (L \<cdot>l \<gamma>)"
  proof -
    have  "trail_consistent (state_trail S0)"
      using \<open>state_trail S1 = state_trail S0\<close> \<open>trail_consistent (state_trail S1)\<close> by simp
    thus ?thesis
      by (smt (verit, best) Pair_inject list.distinct(1) list.inject trail_S0_eq
          trail_consistent.cases trail_propagate_def)
  qed

  ultimately have "\<not> trail_defined_lit (state_trail Sn) (L \<cdot>l \<gamma>)"
    by (metis trail_defined_lit_def trail_false_lit_def trail_false_lit_if_trail_false_suffix
        uminus_of_uminus_id)

  moreover have "trail_false_cls (state_trail Sn) (Cn \<cdot> \<gamma>n)"
    using sound_Sn conflict_Sn by (auto simp add: sound_state_def)

  ultimately have "L \<cdot>l \<gamma> \<notin># Cn \<cdot> \<gamma>n \<and> - (L \<cdot>l \<gamma>) \<notin># Cn \<cdot> \<gamma>n"
    unfolding trail_false_cls_def trail_false_lit_def trail_defined_lit_def
    by (metis uminus_of_uminus_id)

  have no_conf_at_S: "\<nexists>S'. conflict N \<beta> S S'"
  proof (rule nex_conflict_if_no_conflict_with_trail'')
    show "state_conflict S = None"
      using \<open>propagate N \<beta> S S0\<close> by (auto elim: propagate.cases)
  next
    show "{#} |\<notin>| N"
      by (rule \<open>{#} |\<notin>| N\<close>)
  next
    show "learned_nonempty S"
      using \<open>learned_nonempty S0\<close> \<open>state_learned S = state_learned S0\<close>
      by (simp add: learned_nonempty_def)
  next
    show "no_conflict_with_trail N \<beta> (state_learned S) (state_trail S)"
      using \<open>almost_no_conflict_with_trail N \<beta> S0\<close>
      using \<open>propagate N \<beta> S S0\<close>
      by (auto simp: almost_no_conflict_with_trail_def \<open>state_learned S = state_learned S0\<close>
          trail_propagate_def is_decision_lit_def elim!: propagate.cases)
  qed

  have conf_at_S_if: "\<exists>S'. conflict N \<beta> S S'"
    if D_in: "D \<in> grounding_of_clss (fset N \<union> fset U)" and
      tr_false_D: "trail_false_cls (state_trail S) D"
    for D
    using ex_conflict_if_trail_false_cls[OF tr_false_D D_in]
    unfolding U_def \<open>state_learned S = state_learned S1\<close>[symmetric]
      \<open>state_conflict S = None\<close>[symmetric]
    by simp

  have not_gr_red_Cn_\<gamma>n:
    "\<not> ground_redundant trail_ord (grounding_of_clss (fset N \<union> fset U)) (Cn \<cdot> \<gamma>n)"
  proof (rule notI)
    define gnds_le_Cn_\<gamma>n where
      "gnds_le_Cn_\<gamma>n = {D \<in> grounding_of_clss (fset N \<union> fset U). trail_ord\<^sup>=\<^sup>= D (Cn \<cdot> \<gamma>n)}"

    assume "ground_redundant trail_ord (grounding_of_clss (fset N \<union> fset U)) (Cn \<cdot> \<gamma>n)"
    hence "gnds_le_Cn_\<gamma>n \<TTurnstile>e {Cn \<cdot> \<gamma>n}"
      unfolding ground_redundant_def gnds_le_Cn_\<gamma>n_def by simp
    hence "\<not> trail_interp (state_trail S1) \<TTurnstile>s gnds_le_Cn_\<gamma>n"
      using not_trail_S1_entails_Cn_\<gamma>n by auto
    then obtain D where D_in: "D \<in> gnds_le_Cn_\<gamma>n" and "\<not> trail_interp (state_trail S1) \<TTurnstile> D"
      by (auto simp: true_clss_def)

    from D_in have
      D_in: "D \<in> grounding_of_clss (fset N \<union> fset U)" and
      D_le_Cn_\<gamma>n: "trail_ord\<^sup>=\<^sup>= D (Cn \<cdot> \<gamma>n)"
      unfolding gnds_le_Cn_\<gamma>n_def by simp_all

    from D_le_Cn_\<gamma>n have "trail_defined_cls (state_trail S1) D"
      unfolding Lattices.sup_apply Boolean_Algebras.sup_bool_def
    proof (elim disjE)
      assume multp_D_Cn_\<gamma>n: "trail_ord D (Cn \<cdot> \<gamma>n)"
      show "trail_defined_cls (state_trail S1) D"
        using \<open>sound_trail N (state_trail S1)\<close> multp_D_Cn_\<gamma>n
          \<open>trail_defined_cls (state_trail S1) (Cn \<cdot> \<gamma>n)\<close> \<open>transp lt\<close>
        by (auto simp add: trail_ord_def intro: trail_defined_cls_if_lt_defined)
    next
      assume "D = Cn \<cdot> \<gamma>n"
      then show "trail_defined_cls (state_trail S1) D"
        using \<open>trail_defined_cls (state_trail S1) (Cn \<cdot> \<gamma>n)\<close> by simp
    qed
    hence "trail_false_cls (state_trail S1) D"
      using \<open>\<not> trail_interp (state_trail S1) \<TTurnstile> D\<close>
      using \<open>trail_consistent (state_trail S1)\<close> trail_interp_cls_if_trail_true
        trail_true_or_false_cls_if_defined by blast

    from D_le_Cn_\<gamma>n have "L \<cdot>l \<gamma> \<notin># D \<and> - (L \<cdot>l \<gamma>) \<notin># D"
    proof (rule sup2E)
      show "D = Cn \<cdot> \<gamma>n \<Longrightarrow> ?thesis"
        using \<open>L \<cdot>l \<gamma> \<notin># Cn \<cdot> \<gamma>n \<and> - (L \<cdot>l \<gamma>) \<notin># Cn \<cdot> \<gamma>n\<close> by argo
    next
      assume "trail_ord D (Cn \<cdot> \<gamma>n)"
      hence D_lt_Cn_\<gamma>n': "multp (trail_less (map fst (state_trail S1))) D (Cn \<cdot> \<gamma>n)"
        unfolding trail_ord_def
      proof (rule multp_mono_strong)
        from \<open>transp lt\<close> show "transp (trail_less_ex lt (map fst (state_trail S1)))"
          by (rule transp_trail_less_ex_if_sound[OF \<open>sound_trail N (state_trail S1)\<close>])
      next
        show "\<And>x y. x \<in># D \<Longrightarrow> y \<in># Cn \<cdot> \<gamma>n \<Longrightarrow> trail_less_ex lt (map fst (state_trail S1)) x y \<Longrightarrow>
           trail_less (map fst (state_trail S1)) x y"
          using \<open>\<forall>L\<in>#Cn \<cdot> \<gamma>n. trail_defined_lit (state_trail S1) L\<close>
          by (metis (no_types, opaque_lifting) image_set trail_defined_lit_def trail_less_ex_def)
      qed

      have "\<forall>K\<in>#Cn \<cdot> \<gamma>n. - K \<in> fst ` set (state_trail S1)"
        by (rule \<open>trail_false_cls (state_trail S1) (Cn \<cdot> \<gamma>n)\<close>[unfolded trail_false_cls_def
              trail_false_lit_def])
      hence "\<forall>K\<in>#Cn \<cdot> \<gamma>n. - K \<in> insert (L \<cdot>l \<gamma>) (fst ` set (state_trail S))"
        unfolding \<open>state_trail S1 = state_trail S0\<close>
          \<open>state_trail S0 = trail_propagate (state_trail S) L C \<gamma>\<close>
          trail_propagate_def list.set image_insert prod.sel
        by simp
      hence *: "\<forall>K\<in>#Cn \<cdot> \<gamma>n. - K \<in> fst ` set (state_trail S)"
        by (metis \<open>L \<cdot>l \<gamma> \<notin># Cn \<cdot> \<gamma>n \<and> - (L \<cdot>l \<gamma>) \<notin># Cn \<cdot> \<gamma>n\<close> insert_iff uminus_lit_swap)
      have **: "\<forall>K \<in># Cn \<cdot> \<gamma>n. trail_less (map fst (state_trail S1)) K (L \<cdot>l \<gamma>)"
        unfolding \<open>state_trail S1 = state_trail S0\<close>
          \<open>state_trail S0 = trail_propagate (state_trail S) L C \<gamma>\<close>
          trail_propagate_def prod.sel list.map
      proof (rule ballI)
        fix K assume "K \<in># Cn \<cdot> \<gamma>n"
        have "trail_less_comp_id (L \<cdot>l \<gamma> # map fst (state_trail S)) K (L \<cdot>l \<gamma>)"
          unfolding trail_less_comp_id_def
          using *[rule_format, OF \<open>K \<in># Cn \<cdot> \<gamma>n\<close>]
          by (smt (verit, best) image_set in_set_conv_nth length_Cons less_Suc_eq_0_disj nth_Cons'
              nth_Cons_Suc uminus_lit_swap)
        thus "trail_less (L \<cdot>l \<gamma> # map fst (state_trail S)) K (L \<cdot>l \<gamma>)"
          by (simp add: trail_less_def)
      qed
      
      moreover have "trail_less (map fst (state_trail S1)) (L \<cdot>l \<gamma>) (- (L \<cdot>l \<gamma>))"
        unfolding \<open>state_trail S1 = state_trail S0\<close>
          \<open>state_trail S0 = trail_propagate (state_trail S) L C \<gamma>\<close>
          trail_propagate_def list.map prod.sel
        by (rule trail_less_comp_rightI) simp

      ultimately have ***: "\<forall>K \<in># Cn \<cdot> \<gamma>n. trail_less (map fst (state_trail S1)) K (- (L \<cdot>l \<gamma>))"
        using transp_trail_less_if_sound[OF sound_trail_S1, THEN transpD] by blast

      have "\<not> (L \<cdot>l \<gamma> \<in># D \<or> - (L \<cdot>l \<gamma>) \<in># D)"
      proof (rule notI)
        obtain I J K where
          "Cn \<cdot> \<gamma>n = I + J" and D_def: "D = I + K" and "J \<noteq> {#}" and
          "\<forall>k\<in>#K. \<exists>x\<in>#J. trail_less (map fst (state_trail S1)) k x"
          using multp_implies_one_step[OF transp_trail_less_if_sound[OF sound_trail_S1] D_lt_Cn_\<gamma>n']
          by auto
        assume "L \<cdot>l \<gamma> \<in># D \<or> - (L \<cdot>l \<gamma>) \<in># D"
        then show False
          unfolding D_def Multiset.union_iff
        proof (elim disjE)
          show "L \<cdot>l \<gamma> \<in># I \<Longrightarrow> False"
            using \<open>L \<cdot>l \<gamma> \<notin># Cn \<cdot> \<gamma>n \<and> - (L \<cdot>l \<gamma>) \<notin># Cn \<cdot> \<gamma>n\<close> \<open>Cn \<cdot> \<gamma>n = I + J\<close> by simp
        next
          show "- (L \<cdot>l \<gamma>) \<in># I \<Longrightarrow> False"
            using \<open>L \<cdot>l \<gamma> \<notin># Cn \<cdot> \<gamma>n \<and> - (L \<cdot>l \<gamma>) \<notin># Cn \<cdot> \<gamma>n\<close> \<open>Cn \<cdot> \<gamma>n = I + J\<close> by simp
        next
          show "L \<cdot>l \<gamma> \<in># K \<Longrightarrow> False"
            using \<open>L \<cdot>l \<gamma> \<notin># Cn \<cdot> \<gamma>n \<and> - (L \<cdot>l \<gamma>) \<notin># Cn \<cdot> \<gamma>n\<close>[THEN conjunct1]
              **[unfolded \<open>Cn \<cdot> \<gamma>n = I + J\<close>] \<open>\<forall>k\<in>#K. \<exists>x\<in>#J. trail_less (map fst (state_trail S1)) k x\<close>
            by (metis (no_types, lifting) D_def Un_insert_right
                \<open>\<not> trail_interp (state_trail S1) \<TTurnstile> D\<close>
                \<open>state_trail S0 = trail_propagate (state_trail S) L C \<gamma>\<close>
                \<open>state_trail S1 = state_trail S0\<close> \<open>trail_consistent (state_trail S1)\<close> image_insert
                insert_iff list.set(2) mk_disjoint_insert prod.sel(1) set_mset_union
                trail_interp_cls_if_trail_true trail_propagate_def trail_true_cls_def
                trail_true_lit_def)
        next
          assume "- (L \<cdot>l \<gamma>) \<in># K"
          then obtain j where
            j_in: "j \<in># J" and
            uminus_L_\<gamma>_lt_j: "trail_less (map fst (state_trail S1)) (- (L \<cdot>l \<gamma>)) j"
            using \<open>\<forall>k\<in>#K. \<exists>x\<in>#J. trail_less (map fst (state_trail S1)) k x\<close> by auto

          from j_in have
            "trail_less (map fst (state_trail S1)) j (- (L \<cdot>l \<gamma>))"
            using *** by (auto simp: \<open>Cn \<cdot> \<gamma>n = I + J\<close>)
          with uminus_L_\<gamma>_lt_j show "False"
            using asymp_trail_less_if_sound[OF sound_trail_S1, THEN asympD]
            by blast
        qed
      qed
      thus ?thesis by simp
    qed
    hence "trail_false_cls (state_trail S) D"
      using D_in \<open>trail_false_cls (state_trail S1) D\<close>
      unfolding \<open>state_trail S1 = state_trail S0\<close>
        \<open>state_trail S0 = trail_propagate (state_trail S) L C \<gamma>\<close>
      by (simp add: trail_propagate_def subtrail_falseI)
    thus False
      using no_conf_at_S conf_at_S_if[OF D_in] by metis
  qed
  hence "\<not> redundant trail_ord (fset N \<union> fset U) Cn"
    unfolding redundant_def
    using Cn_\<gamma>n_in by auto

  moreover have "Cn \<cdot> \<gamma>n \<notin> grounding_of_clss (fset N \<union> fset U)"
  proof -
    have "is_ground_cls (Cn \<cdot> \<gamma>n)"
      using Cn_\<gamma>n_in is_ground_cls_if_in_grounding_of_cls by blast

    moreover have "is_ground_clss (grounding_of_clss (fset N \<union> fset U))"
      by simp

    ultimately have "\<not> ({D \<in> grounding_of_clss (fset N \<union> fset U). trail_ord\<^sup>=\<^sup>= D (Cn \<cdot> \<gamma>n)} \<TTurnstile>e {Cn \<cdot> \<gamma>n})"
      using not_gr_red_Cn_\<gamma>n
      by (simp add: ground_redundant_def)
    thus ?thesis
      by (auto simp add: true_clss_def)
  qed

  moreover have "set_mset (Cn \<cdot> \<gamma>n) \<notin> set_mset ` grounding_of_clss (fset N \<union> fset U)"
  proof (rule notI)
    assume "set_mset (Cn \<cdot> \<gamma>n) \<in> set_mset ` grounding_of_clss (fset N \<union> fset U)"
    then obtain D where
      D_in: "D \<in> grounding_of_clss (fset N \<union> fset U)" and
      set_mset_eq_D_Cn_\<gamma>n: "set_mset D = set_mset (Cn \<cdot> \<gamma>n)"
      by (auto simp add: image_iff)

    have "\<not> trail_interp (state_trail S1) \<TTurnstile> D"
      unfolding true_cls_iff_set_mset_eq[OF set_mset_eq_D_Cn_\<gamma>n]
      using not_trail_S1_entails_Cn_\<gamma>n
      by simp

    have "trail_defined_cls (state_trail S1) D"
      using \<open>\<forall>L\<in>#Cn \<cdot> \<gamma>n. trail_defined_lit (state_trail S1) L\<close>
      unfolding set_mset_eq_D_Cn_\<gamma>n[symmetric]
      by (simp add: trail_defined_cls_def)
    hence "trail_false_cls (state_trail S1) D"
      using \<open>\<not> trail_interp (state_trail S1) \<TTurnstile> D\<close>
      using tr_consistent_S1 trail_interp_cls_if_trail_true trail_true_or_false_cls_if_defined
      by blast

    have "L \<cdot>l \<gamma> \<notin># D \<and> - (L \<cdot>l \<gamma>) \<notin># D"
      using \<open>L \<cdot>l \<gamma> \<notin># Cn \<cdot> \<gamma>n \<and> - (L \<cdot>l \<gamma>) \<notin># Cn \<cdot> \<gamma>n\<close>
      unfolding set_mset_eq_D_Cn_\<gamma>n[symmetric]
      by assumption
    hence "trail_false_cls (state_trail S) D"
      using D_in \<open>trail_false_cls (state_trail S1) D\<close>
      unfolding \<open>state_trail S1 = state_trail S0\<close>
        \<open>state_trail S0 = trail_propagate (state_trail S) L C \<gamma>\<close>
      by (simp add: trail_propagate_def subtrail_falseI)
    thus False
      using no_conf_at_S conf_at_S_if[OF D_in] by metis
  qed

  ultimately show ?thesis
    using conflict_Sn by simp
qed

theorem learned_clauses_in_regular_runs:
  assumes
    disj_vars_N: "disjoint_vars_set (fset N)" and
    regular_run: "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S0" and
    conflict: "conflict N \<beta> S0 S1" and
    resolution: "(skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>+\<^sup>+ S1 Sn" and
    backtrack: "backtrack N \<beta> Sn Sn'" and
    "transp lt"
  defines
    "trail_ord \<equiv> multp (trail_less_ex lt (map fst (state_trail S1)))" and
    "U \<equiv> state_learned S1"
  shows "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state Sn' \<and>
    (\<exists>C \<gamma>. state_conflict Sn = Some (C, \<gamma>) \<and>
      C \<cdot> \<gamma> \<notin> grounding_of_clss (fset N \<union> fset U) \<and>
      set_mset (C \<cdot> \<gamma>) \<notin> set_mset ` grounding_of_clss (fset N \<union> fset U) \<and>
      \<not> redundant trail_ord (fset N \<union> fset U) C)"
proof -
  from disj_vars_N have "sound_state N \<beta> initial_state"
    by (rule sound_initial_state)
  with regular_run have sound_S0: "sound_state N \<beta> S0"
    by (rule regular_run_sound_state)

  from regular_run have "learned_nonempty S0"
    by (induction S0 rule: rtranclp_induct)
      (auto intro: scl_preserves_learned_nonempty reasonable_if_regular scl_if_reasonable)

  from regular_run have "conflict_disjoint_vars N S0" and "trail_propagated_or_decided' N \<beta> S0"
    by (induction S0 rule: rtranclp_induct)
      (auto intro: scl_preserves_conflict_disjoint_vars scl_preserves_trail_propagated_or_decided
        reasonable_if_regular scl_if_reasonable)

  from regular_run have "no_conflict_after_decide' N \<beta> S0"
    by (induction S0 rule: rtranclp_induct)
      (auto intro: reasonable_scl_preserves_no_conflict_after_decide' reasonable_if_regular)

  from regular_run have "almost_no_conflict_with_trail N \<beta> S0"
    by (induction S0 rule: rtranclp_induct)
     (simp_all add: regular_scl_preserves_almost_no_conflict_with_trail)

  from regular_run conflict have "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S1"
    by (meson regular_scl_def rtranclp.simps)
  also from resolution have reg_run_S1_Sn: "(regular_scl N \<beta>)\<^sup>*\<^sup>* ... Sn"
    using regular_run_if_skip_factorize_resolve_run tranclp_into_rtranclp by metis
  also have "(regular_scl N \<beta>)\<^sup>*\<^sup>* ... Sn'"
  proof (rule r_into_rtranclp)
    from backtrack have "scl N \<beta> Sn Sn'"
      by (simp add: scl_def)
    with backtrack have "reasonable_scl N \<beta> Sn Sn'"
      using reasonable_scl_def decide_well_defined(6) by blast
    with backtrack show "regular_scl N \<beta> Sn Sn'"
      unfolding regular_scl_def
      by (smt (verit) conflict.simps option.simps(3) backtrack.cases state_conflict_simp)
  qed
  finally have "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state Sn'" by assumption
  thus ?thesis
    using learned_clauses_in_regular_runs_invars[OF sound_S0 \<open>learned_nonempty S0\<close>
        \<open>conflict_disjoint_vars N S0\<close> \<open>trail_propagated_or_decided' N \<beta> S0\<close>
        \<open>no_conflict_after_decide' N \<beta> S0\<close> \<open>almost_no_conflict_with_trail N \<beta> S0\<close>
        conflict resolution backtrack \<open>transp lt\<close>, folded trail_ord_def U_def]
    by argo
qed

corollary learned_clauses_in_regular_runs_static_order:
  assumes
    disj_vars_N: "disjoint_vars_set (fset N)" and
    regular_run: "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S0" and
    conflict: "conflict N \<beta> S0 S1" and
    resolution: "(skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>+\<^sup>+ S1 Sn" and
    backtrack: "backtrack N \<beta> Sn Sn'" and
    "transp lt"
  defines
    "trail_ord \<equiv> multp (trail_less_ex lt (map fst (state_trail S1)))" and
    "U \<equiv> state_learned S1"
  shows "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state Sn' \<and>
    (\<exists>C \<gamma>. state_conflict Sn = Some (C, \<gamma>) \<and> \<not> redundant (\<subset>#) (fset N \<union> fset U) C)"
  using learned_clauses_in_regular_runs[OF assms(1-6)]
  using U_def redundant_multp_if_redundant_strict_subset by blast

end

end