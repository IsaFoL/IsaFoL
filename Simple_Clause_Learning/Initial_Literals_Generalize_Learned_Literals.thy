theory Initial_Literals_Generalize_Learned_Literals
  imports Simple_Clause_Learning
begin

context scl begin

definition clss_lits_generalize_clss_lits where
  "clss_lits_generalize_clss_lits N U \<longleftrightarrow>
    (\<forall>L \<in> \<Union>(set_mset ` U). \<exists>K \<in> \<Union>(set_mset ` N). generalizes_lit K L)"

lemma clss_lits_generalize_clss_lits_if_superset[simp]:
  assumes "N1 \<supseteq> N2"
  shows "clss_lits_generalize_clss_lits N1 N2"
proof (unfold clss_lits_generalize_clss_lits_def, rule ballI)
  fix L
  assume "L \<in> \<Union>(set_mset ` N2)"
  show "\<exists>K \<in> \<Union>(set_mset ` N1). generalizes_lit K L"
    unfolding generalizes_lit_def
  proof (intro bexI exI conjI)
    show "L \<in> \<Union>(set_mset ` N1)"
      using \<open>L \<in> \<Union>(set_mset ` N2)\<close> \<open>N1 \<supseteq> N2\<close> by blast
  next
    show "L \<cdot>l Var = L"
      by simp
  qed
qed 

lemma clss_lits_generalize_clss_lits_refl[simp]: "clss_lits_generalize_clss_lits N N"
  using clss_lits_generalize_clss_lits_if_superset by simp

lemma clss_lits_generalize_clss_lits_insert: "clss_lits_generalize_clss_lits N (insert C U) \<longleftrightarrow>
  clss_lits_generalize_clss_lits N {C} \<and> clss_lits_generalize_clss_lits N U"
  unfolding clss_lits_generalize_clss_lits_def by blast

lemma clss_lits_generalize_clss_lits_rename_clause:
  "C \<in> N \<Longrightarrow> finite M \<Longrightarrow> clss_lits_generalize_clss_lits N {rename_clause M C}"
  unfolding clss_lits_generalize_clss_lits_def
  apply simp
  by (metis Melem_subst_cls generalizes_lit_def rename_clause_def)

lemma clss_lits_generalize_clss_lits_trans:
  assumes
    "clss_lits_generalize_clss_lits N1 N2" and
    "clss_lits_generalize_clss_lits N2 N3"
  shows "clss_lits_generalize_clss_lits N1 N3"
proof (unfold clss_lits_generalize_clss_lits_def, rule ballI)
  fix L3
  assume "L3 \<in> \<Union> (set_mset ` N3)"
  then obtain L2 \<sigma>2 where "L2 \<in> \<Union> (set_mset ` N2)" and "L2 \<cdot>l \<sigma>2 = L3"
    using assms(2)[unfolded clss_lits_generalize_clss_lits_def] generalizes_lit_def by meson
  then obtain L1 \<sigma>1 where "L1 \<in> \<Union> (set_mset ` N1)" and "L1 \<cdot>l \<sigma>1 = L2"
    using assms(1)[unfolded clss_lits_generalize_clss_lits_def] generalizes_lit_def by meson
  
  thus "\<exists>K\<in>\<Union> (set_mset ` N1). generalizes_lit K L3"
    unfolding generalizes_lit_def
  proof (intro bexI exI conjI)
    show "L1 \<cdot>l (\<sigma>1 \<odot> \<sigma>2) = L3"
      by (simp add: \<open>L1 \<cdot>l \<sigma>1 = L2\<close> \<open>L2 \<cdot>l \<sigma>2 = L3\<close>)
  qed simp_all
qed

definition initial_lits_generalized_learned_lits where
  "initial_lits_generalized_learned_lits N S \<longleftrightarrow> finite N \<and> finite (state_learned S) \<and>
    clss_lits_generalize_clss_lits N (state_learned S \<union> clss_of_trail (state_trail S) \<union>
      (case state_conflict S of None \<Rightarrow> {} | Some (C, _) \<Rightarrow> {C}))"

lemma initial_lits_generalized_learned_lits_initial_state:
  "finite N \<Longrightarrow> initial_lits_generalized_learned_lits N initial_state"
  unfolding initial_lits_generalized_learned_lits_def by simp

lemma propagate_initial_lits_generalized_learned_lits:
  "propagate N S S' \<Longrightarrow> initial_lits_generalized_learned_lits N S \<Longrightarrow>
    initial_lits_generalized_learned_lits N S'"
proof (induction S S' rule: propagate.induct)
  case (propagateI C U C'' L \<Gamma> \<gamma>)

  from propagateI.prems have
    fin: "finite N" "finite U" and
    N_superset_lits: "clss_lits_generalize_clss_lits N (U \<union> clss_of_trail \<Gamma>)"
    unfolding initial_lits_generalized_learned_lits_def by simp_all

  from propagateI.hyps have C_in: "C \<in> N \<union> U" by simp
  from propagateI.hyps have rename_C: "C'' + {#L#} = rename_clause (N \<union> U \<union> clss_of_trail \<Gamma>) C"
    by simp

  moreover have "clss_lits_generalize_clss_lits N (U \<union> clss_of_trail (trail_propagate \<Gamma> L C'' \<gamma>))"
  proof -
    from C_in have "clss_lits_generalize_clss_lits N {rename_clause (N \<union> U \<union> clss_of_trail \<Gamma>) C}"
    proof (unfold Un_iff, elim disjE)
      assume "C \<in> N "
      thus ?thesis
        using fin by (auto intro: clss_lits_generalize_clss_lits_rename_clause)
    next
      assume "C \<in> U"
      thus ?thesis
        using fin
        by (auto intro!: clss_lits_generalize_clss_lits_trans[OF N_superset_lits]
            intro: clss_lits_generalize_clss_lits_rename_clause)
    qed
    hence "clss_lits_generalize_clss_lits N {add_mset L C''}"
      unfolding rename_C[simplified] by assumption
    thus ?thesis
      using N_superset_lits
      using clss_lits_generalize_clss_lits_insert[of N "add_mset L C''" "U \<union> clss_of_trail \<Gamma>"]
      by simp
  qed

  ultimately show ?case
    unfolding initial_lits_generalized_learned_lits_def using fin by simp
qed

lemma decide_initial_lits_generalized_learned_lits:
  "decide N S S' \<Longrightarrow> initial_lits_generalized_learned_lits N S \<Longrightarrow>
    initial_lits_generalized_learned_lits N S'"
proof (induction S S' rule: decide.induct)
  case (decideI L \<Gamma> U)
  thus ?case
    by (simp add: initial_lits_generalized_learned_lits_def)
qed

lemma conflict_initial_lits_generalized_learned_lits:
  "conflict N S S' \<Longrightarrow> initial_lits_generalized_learned_lits N S \<Longrightarrow>
    initial_lits_generalized_learned_lits N S'"
proof (induction S S' rule: conflict.induct)
  case (conflictI D U D' \<Gamma> \<sigma>)
  moreover have "clss_lits_generalize_clss_lits N {rename_clause (N \<union> U \<union> clss_of_trail \<Gamma>) D}"
    using \<open>D \<in> N \<union> U\<close>
  proof (elim Set.UnE)
    assume "D \<in> N"
    then show ?thesis
      using clss_lits_generalize_clss_lits_rename_clause
      by (metis finite_UnI finite_clss_of_trail initial_lits_generalized_learned_lits_def local.conflictI(6)
          state_learned_simp)
  next
    assume "D \<in> U"
    then show ?thesis
      using clss_lits_generalize_clss_lits_rename_clause
      by (smt (verit) UnCI clss_lits_generalize_clss_lits_trans finite_UnI finite_clss_of_trail
          initial_lits_generalized_learned_lits_def local.conflictI(6) state_learned_simp)
  qed
  ultimately show ?case
    unfolding initial_lits_generalized_learned_lits_def
    using clss_lits_generalize_clss_lits_insert by auto
qed

lemma clss_lits_generalize_clss_lits_subset:
  "clss_lits_generalize_clss_lits N U1 \<Longrightarrow> U2 \<subseteq> U1 \<Longrightarrow> clss_lits_generalize_clss_lits N U2"
  unfolding clss_lits_generalize_clss_lits_def by blast

lemma skip_initial_lits_generalized_learned_lits:
  "skip N S S' \<Longrightarrow> initial_lits_generalized_learned_lits N S \<Longrightarrow>
    initial_lits_generalized_learned_lits N S'"
proof (induction S S' rule: skip.induct)
  case (skipI L D \<sigma> Cl \<Gamma> U)
  then show ?case
    unfolding initial_lits_generalized_learned_lits_def
    unfolding state_learned_simp state_conflict_simp state_trail_simp option.case prod.case
    unfolding clss_of_trail_Cons[of _ \<Gamma>]
    by (auto elim: clss_lits_generalize_clss_lits_subset)
qed

lemma clss_lits_generalize_clss_lits_subst_clss:
  assumes
    N_lits_alpha_superset: "clss_lits_generalize_clss_lits N1 N2"
  shows "clss_lits_generalize_clss_lits N1 (N2 \<cdot>cs \<sigma>)"
  unfolding clss_lits_generalize_clss_lits_def
proof (rule ballI)
  fix L assume "L \<in> \<Union>(set_mset ` (N2 \<cdot>cs \<sigma>))"
  hence "\<exists>L\<^sub>2. L\<^sub>2 \<in> \<Union>(set_mset ` N2) \<and> L = L\<^sub>2 \<cdot>l \<sigma>"
    by (smt (verit) Melem_subst_cls UN_iff image_iff subst_clss_def)
  then obtain L\<^sub>2 where "L\<^sub>2 \<in> \<Union>(set_mset ` N2)" and L_def: "L = L\<^sub>2 \<cdot>l \<sigma>" by auto
  then obtain L\<^sub>1 \<sigma>\<^sub>1 where "L\<^sub>1 \<in> \<Union>(set_mset ` N1)" and "L\<^sub>1 \<cdot>l \<sigma>\<^sub>1 = L\<^sub>2"
    using N_lits_alpha_superset[unfolded clss_lits_generalize_clss_lits_def, rule_format, of L\<^sub>2]
    by (auto simp: generalizes_lit_def)

  show "\<exists>K\<in>\<Union> (set_mset ` N1). generalizes_lit K L"
    unfolding generalizes_lit_def
  proof (intro bexI exI)
    show "L\<^sub>1 \<in> \<Union>(set_mset ` N1)"
      by (rule \<open>L\<^sub>1 \<in> \<Union>(set_mset ` N1)\<close>)
  next
    show "L\<^sub>1 \<cdot>l (\<sigma>\<^sub>1 \<odot> \<sigma>) = L"
      unfolding L_def \<open>L\<^sub>1 \<cdot>l \<sigma>\<^sub>1 = L\<^sub>2\<close>[symmetric] by simp
  qed
qed

lemma clss_lits_generalize_clss_lits_singleton_subst_cls:
  shows "clss_lits_generalize_clss_lits N {C} \<Longrightarrow> clss_lits_generalize_clss_lits N {C \<cdot> \<sigma>}"
  by (rule clss_lits_generalize_clss_lits_subst_clss[of N "{C}" \<sigma>, simplified])

lemma clss_lits_generalize_clss_lits_subst_cls:
  assumes
    N_lits_alpha_superset: "clss_lits_generalize_clss_lits N {add_mset L1 (add_mset L2 C)}"
  shows "clss_lits_generalize_clss_lits N {add_mset (L1 \<cdot>l \<sigma>) (C \<cdot> \<sigma>)}"
proof (rule clss_lits_generalize_clss_lits_trans)
  show "clss_lits_generalize_clss_lits N {add_mset L1 (add_mset L2 C) \<cdot> \<sigma>}"
    by (rule clss_lits_generalize_clss_lits_singleton_subst_cls[of N _ \<sigma>, OF N_lits_alpha_superset])
next
  show "clss_lits_generalize_clss_lits {add_mset L1 (add_mset L2 C) \<cdot> \<sigma>} {add_mset (L1 \<cdot>l \<sigma>) (C \<cdot> \<sigma>)}"
    apply (simp add: clss_lits_generalize_clss_lits_def generalizes_lit_def)
    using subst_lit_id_subst by blast
qed

lemma factorize_initial_lits_generalized_learned_lits:
  "factorize N S S' \<Longrightarrow> initial_lits_generalized_learned_lits N S \<Longrightarrow>
    initial_lits_generalized_learned_lits N S'"
proof (induction S S' rule: factorize.induct)
  case (factorizeI L \<sigma> L' \<mu> \<sigma>' D \<Gamma> U)
  moreover have "clss_lits_generalize_clss_lits N {add_mset (L \<cdot>l \<mu>) (D \<cdot> \<mu>)}"
    using factorizeI
    unfolding initial_lits_generalized_learned_lits_def
    apply simp
    using clss_lits_generalize_clss_lits_subst_cls
    using clss_lits_generalize_clss_lits_insert by blast
  ultimately show ?case
    unfolding initial_lits_generalized_learned_lits_def
    apply simp
    using clss_lits_generalize_clss_lits_insert by blast
qed

lemma resolve_initial_lits_generalized_learned_lits:
  "resolve N S S' \<Longrightarrow> initial_lits_generalized_learned_lits N S \<Longrightarrow>
    initial_lits_generalized_learned_lits N S'"
proof (induction S S' rule: resolve.induct)
  case (resolveI \<Gamma> \<Gamma>' L C \<delta> \<rho> U D L' \<sigma> \<mu>)
  moreover have "clss_lits_generalize_clss_lits N {(D + C) \<cdot> \<mu> \<cdot> \<rho>}"
  proof -
    from resolveI.prems have
      "finite N" "finite U" and
      N_lits_sup: "clss_lits_generalize_clss_lits N (U \<union> clss_of_trail \<Gamma> \<union> {D + {#L'#}})"
      unfolding initial_lits_generalized_learned_lits_def
      by simp_all

    have "clss_lits_generalize_clss_lits N {D \<cdot> \<mu> \<cdot> \<rho>}"
    proof -
      from N_lits_sup have "clss_lits_generalize_clss_lits N {D + {#L'#}}"
        using clss_lits_generalize_clss_lits_insert by auto
      hence "clss_lits_generalize_clss_lits N {D}"
        by (simp add: clss_lits_generalize_clss_lits_def)
      thus ?thesis
        by (auto intro: clss_lits_generalize_clss_lits_singleton_subst_cls)
    qed
    moreover have "clss_lits_generalize_clss_lits N {C \<cdot> \<mu> \<cdot> \<rho>}"
    proof -
      from N_lits_sup have "clss_lits_generalize_clss_lits N (clss_of_trail \<Gamma>)"
        by (metis Un_insert_right clss_lits_generalize_clss_lits_if_superset
            clss_lits_generalize_clss_lits_insert clss_lits_generalize_clss_lits_trans
            sup.cobounded2 sup_bot.right_neutral)
      hence "clss_lits_generalize_clss_lits N {add_mset L C}"
        unfolding resolveI.hyps
        using clss_lits_generalize_clss_lits_insert by auto
      hence "clss_lits_generalize_clss_lits N {C}"
        by (simp add: clss_lits_generalize_clss_lits_def)
      thus ?thesis
        by (auto intro: clss_lits_generalize_clss_lits_singleton_subst_cls)
    qed
    ultimately show ?thesis
      by (auto simp add: clss_lits_generalize_clss_lits_def)
  qed
  ultimately show ?case
    unfolding initial_lits_generalized_learned_lits_def
    unfolding state_trail_simp state_learned_simp state_conflict_simp
    unfolding option.case prod.case
    by (metis Un_insert_right clss_lits_generalize_clss_lits_insert)
qed

lemma backtrack_initial_lits_generalized_learned_lits:
  "backtrack N S S' \<Longrightarrow> initial_lits_generalized_learned_lits N S \<Longrightarrow>
    initial_lits_generalized_learned_lits N S'"
proof (induction S S' rule: backtrack.induct)
  case (backtrackI \<Gamma> D \<sigma> L U)
  then show ?case
    unfolding initial_lits_generalized_learned_lits_def
    apply simp
    by (smt (verit, best) Un_assoc Un_commute Un_insert_left
        clss_lits_generalize_clss_lits_if_superset clss_lits_generalize_clss_lits_trans
        clss_of_trail_trail_decide_subset sup.absorb_iff1 sup.right_idem)
qed

abbreviation lits_of_clss where
  "lits_of_clss N \<equiv> \<Union>(set_mset ` N)"

abbreviation grounding_lits_of_clss where
  "grounding_lits_of_clss N \<equiv> {L \<cdot>l \<gamma> | L \<gamma>. L \<in> lits_of_clss N \<and> is_ground_lit (L \<cdot>l \<gamma>)}"

corollary
  assumes "initial_lits_generalized_learned_lits N S"
  shows "grounding_lits_of_clss (state_learned S) \<subseteq> grounding_lits_of_clss N"
  (is "?lhs \<subseteq> ?rhs")
proof (rule subsetI)
  from assms(1) have N_lits_sup: "clss_lits_generalize_clss_lits N (state_learned S)"
    unfolding initial_lits_generalized_learned_lits_def 
    by (meson Un_upper1 clss_lits_generalize_clss_lits_if_superset clss_lits_generalize_clss_lits_trans)

  fix L
  assume "L \<in> ?lhs"
  then obtain L' \<gamma> where
    L_def: "L = L' \<cdot>l \<gamma>" and
    "L' \<in> \<Union> (set_mset ` state_learned S)" and
    "is_ground_lit (L' \<cdot>l \<gamma>)"
    by auto

  then obtain L\<^sub>N \<sigma>\<^sub>N where "L\<^sub>N \<in> \<Union>(set_mset ` N)" and "L\<^sub>N \<cdot>l \<sigma>\<^sub>N = L'"
    using N_lits_sup[unfolded clss_lits_generalize_clss_lits_def, rule_format, of L']
      generalizes_lit_def
    by blast

  then show "L \<in> ?rhs"
    unfolding mem_Collect_eq
    using \<open>is_ground_lit (L' \<cdot>l \<gamma>)\<close>
    unfolding L_def \<open>L\<^sub>N \<cdot>l \<sigma>\<^sub>N = L'\<close>[symmetric]
    by (metis subst_lit_comp_subst)
qed

end

end