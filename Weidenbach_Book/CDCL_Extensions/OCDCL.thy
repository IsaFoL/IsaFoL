theory OCDCL
  imports CDCL_W_Optimal_Model
begin

subsubsection \<open>Alternative versions\<close>

text \<open>We instantiate our more general rules with exactly the rule from Christoph's OCDCL with either
versions of improve.\<close>


subsubsection \<open>Weights\<close>

text \<open>This one is the version of the weight functions used by Christoph Weidenbach.
  However, we have decided to not instantiate tho calculus with this weight function,
  because it only a slight restriction.
\<close>
locale ocdcl_weight_WB =
  fixes
    \<nu> :: \<open>'v literal \<Rightarrow> nat\<close>
begin

definition \<rho> :: \<open>'v clause \<Rightarrow> nat\<close> where
  \<open>\<rho> M = (\<Sum>A \<in># M. \<nu> A)\<close>

sublocale ocdcl_weight \<rho>
  by (unfold_locales)
    (auto simp: \<rho>_def sum_image_mset_mono)

end


subsubsection \<open>Calculus with simple Improve rule\<close>

context conflict_driven_clause_learning\<^sub>W_optimal_weight
begin
text \<open>To make sure that the paper version of the correct, we restrict the previous calculus to exactly
  the rules that are on paper.\<close>
inductive pruning :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> where
pruning_rule:
  \<open>pruning S T\<close>
  if
    \<open>\<And>M'. total_over_m (set_mset (mset (map lit_of (trail S) @ M'))) (set_mset (init_clss S)) \<Longrightarrow>
       distinct_mset (atm_of `# mset (map lit_of (trail S) @ M')) \<Longrightarrow>
       consistent_interp (set_mset (mset (map lit_of (trail S) @ M'))) \<Longrightarrow>
       \<rho>' (weight S) \<le> Found (\<rho> (mset (map lit_of (trail S) @ M')))\<close>
    \<open>conflicting S = None\<close>
    \<open>T \<sim> update_conflicting (Some (negate_ann_lits (trail S))) S\<close>

inductive oconflict_opt :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S T :: 'st where
oconflict_opt_rule:
  \<open>oconflict_opt S T\<close>
  if
    \<open>Found (\<rho> (lit_of `# mset (trail S))) \<ge> \<rho>' (weight S)\<close>
    \<open>conflicting S = None\<close>
    \<open>T \<sim> update_conflicting (Some (negate_ann_lits (trail S))) S\<close>

inductive improve :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S T :: 'st where
improve_rule:
  \<open>improve S T\<close>
  if
    \<open>total_over_m (lits_of_l (trail S)) (set_mset (init_clss S))\<close>
    \<open>Found (\<rho> (lit_of `# mset (trail S))) < \<rho>' (weight S)\<close>
    \<open>trail S \<Turnstile>asm init_clss S\<close>
    \<open>conflicting S = None\<close>
    \<open>T \<sim> update_weight_information (trail S) S\<close>

text \<open>This is the basic version of the calculus:\<close>
inductive ocdcl\<^sub>w :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> for S :: 'st where (* \htmllink{ocdcl-def} *)
ocdcl_conflict: "conflict S S' \<Longrightarrow> ocdcl\<^sub>w S S'" |
ocdcl_propagate: "propagate S S' \<Longrightarrow> ocdcl\<^sub>w S S'" |
ocdcl_improve: "improve S S' \<Longrightarrow> ocdcl\<^sub>w S S'" |
ocdcl_conflict_opt: "oconflict_opt S S' \<Longrightarrow> ocdcl\<^sub>w S S'" |
ocdcl_other': "ocdcl\<^sub>W_o S S' \<Longrightarrow> ocdcl\<^sub>w S S'" |
ocdcl_pruning: "pruning S S' \<Longrightarrow> ocdcl\<^sub>w S S'"

inductive ocdcl\<^sub>w_stgy :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> for S :: 'st where (* \htmllink{ocdcl-strategy-def} *)
ocdcl\<^sub>w_conflict: "conflict S S' \<Longrightarrow> ocdcl\<^sub>w_stgy S S'" |
ocdcl\<^sub>w_propagate: "propagate S S' \<Longrightarrow> ocdcl\<^sub>w_stgy S S'" |
ocdcl\<^sub>w_improve: "improve S S' \<Longrightarrow> ocdcl\<^sub>w_stgy S S'" |
ocdcl\<^sub>w_conflict_opt: "conflict_opt S S' \<Longrightarrow> ocdcl\<^sub>w_stgy S S'" |
ocdcl\<^sub>w_other': "ocdcl\<^sub>W_o S S' \<Longrightarrow> no_confl_prop_impr S \<Longrightarrow> ocdcl\<^sub>w_stgy S S'"

lemma pruning_conflict_opt:
  assumes ocdcl_pruning: \<open>pruning S T\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>conflict_opt S T\<close>
proof -
  have le:
    \<open>\<And>M'. total_over_m (set_mset (mset (map lit_of (trail S) @ M')))
          (set_mset (init_clss S)) \<Longrightarrow>
         distinct_mset (atm_of `# mset (map lit_of (trail S) @ M')) \<Longrightarrow>
         consistent_interp (set_mset (mset (map lit_of (trail S) @ M'))) \<Longrightarrow>
         \<rho>' (weight S) \<le> Found (\<rho> (mset (map lit_of (trail S) @ M')))\<close>
    using ocdcl_pruning by (auto simp: pruning.simps)
  have alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (abs_state S)\<close> and
    lev: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (abs_state S)\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  have incl: \<open>atms_of (mset (map lit_of (trail S))) \<subseteq> atms_of_mm (init_clss S)\<close>
    using alien unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
    by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state lits_of_def image_image atms_of_def)
  have dist: \<open>distinct (map lit_of (trail S))\<close> and
    cons: \<open>consistent_interp (set (map lit_of (trail S)))\<close>
    using lev unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state lits_of_def image_image atms_of_def
      dest: no_dup_map_lit_of)
  have \<open>negate_ann_lits (trail S) \<in># conflicting_clss S\<close>
    unfolding negate_ann_lits_pNeg_lit_of comp_def mset_map[symmetric]
    apply (rule pruned_clause_in_conflicting_clss)
    subgoal using le by fast
    subgoal using incl by fast
    subgoal using dist by fast
    subgoal using cons by fast
    done
  then show \<open>conflict_opt S T\<close>
    apply (rule conflict_opt.intros)
    subgoal using ocdcl_pruning by (auto simp: pruning.simps)
    subgoal using ocdcl_pruning by (auto simp: pruning.simps)
    done
qed

lemma ocdcl_conflict_opt_conflict_opt:
  assumes ocdcl_pruning: \<open>oconflict_opt S T\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>conflict_opt S T\<close>
proof -
  have alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (abs_state S)\<close> and
    lev: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (abs_state S)\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  have incl: \<open>atms_of (lit_of `# mset (trail S)) \<subseteq> atms_of_mm (init_clss S)\<close>
    using alien unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
    by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state lits_of_def image_image atms_of_def)
  have dist: \<open>distinct_mset (lit_of `# mset (trail S))\<close> and
    cons: \<open>consistent_interp (set (map lit_of (trail S)))\<close> and
    tauto: \<open>\<not>tautology (lit_of `# mset (trail S))\<close>
    using lev unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state lits_of_def image_image atms_of_def
      dest: no_dup_map_lit_of no_dup_distinct no_dup_not_tautology)
  have \<open>lit_of `# mset (trail S) \<in> simple_clss (atms_of_mm (init_clss S))\<close>
    using dist incl tauto by (auto simp: simple_clss_def)
  then have simple: \<open>(lit_of `# mset (trail S))
    \<in> {a. a \<in># mset_set (simple_clss (atms_of_mm (init_clss S))) \<and>
          \<rho>' (weight S) \<le> Found (\<rho> a)}\<close>
    using ocdcl_pruning by (auto simp: simple_clss_finite oconflict_opt.simps)
  have \<open>negate_ann_lits (trail S) \<in># conflicting_clss S\<close>
    unfolding negate_ann_lits_pNeg_lit_of comp_def conflicting_clss_def
    by (rule too_heavy_clauses_conflicting_clauses)
      (use simple in \<open>auto simp: too_heavy_clauses_def oconflict_opt.simps\<close>)
  then show \<open>conflict_opt S T\<close>
    apply (rule conflict_opt.intros)
    subgoal using ocdcl_pruning by (auto simp: oconflict_opt.simps)
    subgoal using ocdcl_pruning by (auto simp: oconflict_opt.simps)
    done
qed


lemma improve_improvep:
  assumes imp: \<open>improve S T\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>improvep S T\<close>
proof -
  have alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (abs_state S)\<close> and
    lev: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (abs_state S)\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  have incl: \<open>atms_of (lit_of `# mset (trail S)) \<subseteq> atms_of_mm (init_clss S)\<close>
    using alien unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
    by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state lits_of_def image_image atms_of_def)
  have dist: \<open>distinct_mset (lit_of `# mset (trail S))\<close> and
    cons: \<open>consistent_interp (set (map lit_of (trail S)))\<close> and
    tauto: \<open>\<not>tautology (lit_of `# mset (trail S))\<close> and
    nd: \<open>no_dup (trail S)\<close>
    using lev unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state lits_of_def image_image atms_of_def
      dest: no_dup_map_lit_of no_dup_distinct no_dup_not_tautology)
  have \<open>lit_of `# mset (trail S) \<in> simple_clss (atms_of_mm (init_clss S))\<close>
    using dist incl tauto by (auto simp: simple_clss_def)
  have tot': \<open>total_over_m (lits_of_l (trail S)) (set_mset (init_clss S))\<close> and
    confl: \<open>conflicting S = None\<close> and
    T: \<open>T \<sim> update_weight_information (trail S) S\<close>
    using imp nd by (auto simp: is_improving_int_def improve.simps)
  have M': \<open>\<rho> (lit_of `# mset M') = \<rho> (lit_of `# mset (trail S))\<close>
    if \<open>total_over_m (lits_of_l M') (set_mset (init_clss S))\<close> and
      incl: \<open>mset (trail S) \<subseteq># mset M'\<close> and
      \<open>lit_of `# mset M' \<in> simple_clss (atms_of_mm (init_clss S))\<close>
      for M'
    proof -
      have [simp]: \<open>lits_of_l M' = set_mset (lit_of `# mset M')\<close>
        by (auto simp: lits_of_def)
      obtain A where A: \<open>mset M' = A + mset (trail S)\<close>
        using incl by (auto simp: mset_subset_eq_exists_conv)
      have M': \<open>lits_of_l M' = lit_of ` set_mset A \<union> lits_of_l (trail S)\<close>
        unfolding lits_of_def
        by (metis A image_Un set_mset_mset set_mset_union)
      have \<open>mset M' = mset (trail S)\<close>
        using that tot' unfolding A total_over_m_alt_def
          apply (case_tac A)
        apply (auto simp: A simple_clss_def distinct_mset_add M' image_Un
            tautology_union mset_inter_empty_set_mset atms_of_def atms_of_s_def
            atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set image_image
            tautology_add_mset)
          by (metis (no_types, lifting) atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
          lits_of_def subsetCE)
      then show ?thesis
        by auto
    qed

  have \<open>lit_of `# mset (trail S) \<in> simple_clss (atms_of_mm (init_clss S))\<close>
    using tauto dist incl by (auto simp: simple_clss_def)
  then have improving: \<open>is_improving (trail S) (trail S) S\<close> and
    \<open>total_over_m (lits_of_l (trail S)) (set_mset (init_clss S))\<close>
    using imp nd by (auto simp: is_improving_int_def improve.simps intro: M')

  show \<open>improvep S T\<close>
    by (rule improvep.intros[OF improving confl T])
qed

lemma ocdcl\<^sub>w_cdcl_bnb:
  assumes \<open>ocdcl\<^sub>w S T\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>cdcl_bnb S T\<close>
  using assms by (cases) (auto intro: cdcl_bnb.intros dest: pruning_conflict_opt
    ocdcl_conflict_opt_conflict_opt improve_improvep)


lemma ocdcl\<^sub>w_stgy_cdcl_bnb_stgy:
  assumes \<open>ocdcl\<^sub>w_stgy S T\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>cdcl_bnb_stgy S T\<close>
  using assms by (cases)
    (auto intro: cdcl_bnb_stgy.intros dest: pruning_conflict_opt improve_improvep)

lemma rtranclp_ocdcl\<^sub>w_stgy_rtranclp_cdcl_bnb_stgy:
  assumes \<open>ocdcl\<^sub>w_stgy\<^sup>*\<^sup>* S T\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>cdcl_bnb_stgy\<^sup>*\<^sup>* S T\<close>
  using assms
  by (induction rule: rtranclp_induct)
    (auto dest: rtranclp_cdcl_bnb_stgy_all_struct_inv[OF rtranclp_cdcl_bnb_stgy_cdcl_bnb]
      ocdcl\<^sub>w_stgy_cdcl_bnb_stgy)

lemma no_step_ocdcl\<^sub>w_no_step_cdcl_bnb:
  assumes \<open>no_step ocdcl\<^sub>w S\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>no_step cdcl_bnb S\<close>
proof -
  have
    nsc: \<open>no_step conflict S\<close> and
    nsp: \<open>no_step propagate S\<close> and
    nsi: \<open>no_step improve S\<close> and
    nsco: \<open>no_step oconflict_opt S\<close> and
    nso: \<open>no_step ocdcl\<^sub>W_o S\<close>and
    nspr: \<open>no_step pruning S\<close>
    using assms(1) by (auto simp: cdcl_bnb.simps ocdcl\<^sub>w.simps)
  have alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (abs_state S)\<close> and
    lev: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (abs_state S)\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  have incl: \<open>atms_of (lit_of `# mset (trail S)) \<subseteq> atms_of_mm (init_clss S)\<close>
    using alien unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
    by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state lits_of_def image_image atms_of_def)
  have dist: \<open>distinct_mset (lit_of `# mset (trail S))\<close> and
    cons: \<open>consistent_interp (set (map lit_of (trail S)))\<close> and
    tauto: \<open>\<not>tautology (lit_of `# mset (trail S))\<close> and
    n_d: \<open>no_dup (trail S)\<close>
    using lev unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state lits_of_def image_image atms_of_def
      dest: no_dup_map_lit_of no_dup_distinct no_dup_not_tautology)

  have nsip: False if imp: \<open>improvep S S'\<close> for S'
  proof -
    obtain M' where
      [simp]: \<open>conflicting S = None\<close> and
      is_improving:
        \<open>\<And>M'. total_over_m (lits_of_l M') (set_mset (init_clss S)) \<longrightarrow>
              mset (trail S) \<subseteq># mset M' \<longrightarrow>
              lit_of `# mset M' \<in> simple_clss (atms_of_mm (init_clss S)) \<longrightarrow>
              \<rho> (lit_of `# mset M') = \<rho> (lit_of `# mset (trail S))\<close> and
      S': \<open>S' \<sim> update_weight_information M' S\<close>
      using imp by (auto simp: improvep.simps is_improving_int_def)
    have 1: \<open>\<not> \<rho>' (weight S) \<le> Found (\<rho> (lit_of `# mset (trail S)))\<close>
      using nsco
      by (auto simp: is_improving_int_def oconflict_opt.simps)
    have 2: \<open>total_over_m (lits_of_l (trail S)) (set_mset (init_clss S))\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then obtain A where
        \<open>A \<in> atms_of_mm (init_clss S)\<close> and
        \<open>A \<notin> atms_of_s (lits_of_l (trail S))\<close>
        by (auto simp: total_over_m_def total_over_set_def)
      then show \<open>False\<close>
        using decide_rule[of S \<open>Pos A\<close>, OF _ _ _ state_eq_ref] nso
        by (auto simp: Decided_Propagated_in_iff_in_lits_of_l ocdcl\<^sub>W_o.simps)
    qed
    have 3: \<open>trail S \<Turnstile>asm init_clss S\<close>
      unfolding true_annots_def
    proof clarify
      fix C
      assume C: \<open>C \<in># init_clss S\<close>
      have \<open>total_over_m (lits_of_l (trail S)) {C}\<close>
        using 2 C by (auto dest!: multi_member_split)
      moreover have \<open>\<not> trail S \<Turnstile>as CNot C\<close>
        using C nsc conflict_rule[of S C, OF _ _ _ state_eq_ref]
        by (auto simp: clauses_def dest!: multi_member_split)
      ultimately show \<open>trail S \<Turnstile>a C\<close>
        using total_not_CNot[of \<open>lits_of_l (trail S)\<close> C] unfolding true_annots_true_cls true_annot_def
        by auto
    qed
    have 4: \<open>lit_of `# mset (trail S) \<in> simple_clss (atms_of_mm (init_clss S))\<close>
      using tauto cons incl dist by (auto simp: simple_clss_def)
    have \<open>improve S (update_weight_information (trail S) S)\<close>
      by (rule improve.intros[OF 2 _ 3]) (use 1 2 in auto)
    then show False
      using nsi by auto
  qed
  moreover have False if \<open>conflict_opt S S'\<close> for S'
  proof -
    have [simp]: \<open>conflicting S = None\<close>
      using that by (auto simp: conflict_opt.simps)
    have 1: \<open>\<not> \<rho>' (weight S) \<le> Found (\<rho> (lit_of `# mset (trail S)))\<close>
      using nsco
      by (auto simp: is_improving_int_def oconflict_opt.simps)
    have 2: \<open>total_over_m (lits_of_l (trail S)) (set_mset (init_clss S))\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then obtain A where
        \<open>A \<in> atms_of_mm (init_clss S)\<close> and
        \<open>A \<notin> atms_of_s (lits_of_l (trail S))\<close>
        by (auto simp: total_over_m_def total_over_set_def)
      then show \<open>False\<close>
        using decide_rule[of S \<open>Pos A\<close>, OF _ _ _ state_eq_ref] nso
        by (auto simp: Decided_Propagated_in_iff_in_lits_of_l ocdcl\<^sub>W_o.simps)
      qed
    have 3: \<open>trail S \<Turnstile>asm init_clss S\<close>
      unfolding true_annots_def
    proof clarify
      fix C
      assume C: \<open>C \<in># init_clss S\<close>
      have \<open>total_over_m (lits_of_l (trail S)) {C}\<close>
        using 2 C by (auto dest!: multi_member_split)
      moreover have \<open>\<not> trail S \<Turnstile>as CNot C\<close>
        using C nsc conflict_rule[of S C, OF _ _ _ state_eq_ref]
        by (auto simp: clauses_def dest!: multi_member_split)
      ultimately show \<open>trail S \<Turnstile>a C\<close>
        using total_not_CNot[of \<open>lits_of_l (trail S)\<close> C] unfolding true_annots_true_cls true_annot_def
        by auto
    qed
    have 4: \<open>lit_of `# mset (trail S) \<in> simple_clss (atms_of_mm (init_clss S))\<close>
      using tauto cons incl dist by (auto simp: simple_clss_def)

    have [intro]: \<open>\<rho> (lit_of `# mset M') = \<rho> (lit_of `# mset (trail S))\<close>
      if
        \<open>lit_of `# mset (trail S) \<in> simple_clss (atms_of_mm (init_clss S))\<close> and
        \<open>atms_of (lit_of `# mset (trail S)) \<subseteq> atms_of_mm (init_clss S)\<close> and
        \<open>no_dup (trail S)\<close> and
        \<open>total_over_m (lits_of_l M') (set_mset (init_clss S))\<close> and
        incl: \<open>mset (trail S) \<subseteq># mset M'\<close> and
        \<open>lit_of `# mset M' \<in> simple_clss (atms_of_mm (init_clss S))\<close>
      for M' :: \<open>('v literal, 'v literal, 'v literal multiset) annotated_lit list\<close>
    proof -
      have [simp]: \<open>lits_of_l M' = set_mset (lit_of `# mset M')\<close>
        by (auto simp: lits_of_def)
      obtain A where A: \<open>mset M' = A + mset (trail S)\<close>
        using incl by (auto simp: mset_subset_eq_exists_conv)
      have M': \<open>lits_of_l M' = lit_of ` set_mset A \<union> lits_of_l (trail S)\<close>
        unfolding lits_of_def
        by (metis A image_Un set_mset_mset set_mset_union)
      have \<open>mset M' = mset (trail S)\<close>
        using that 2 unfolding A total_over_m_alt_def
        apply (case_tac A)
        apply (auto simp: A simple_clss_def distinct_mset_add M' image_Un
            tautology_union mset_inter_empty_set_mset atms_of_def atms_of_s_def
            atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set image_image
            tautology_add_mset)
        by (metis (no_types, lifting) atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
            lits_of_def subsetCE)
      then show ?thesis
        using 2 by auto
    qed
    have imp: \<open>is_improving (trail S) (trail S) S\<close>
      using 1 2 3 4 incl n_d unfolding is_improving_int_def
      by (auto simp:  oconflict_opt.simps)

    show \<open>False\<close>
      using trail_is_improving_Ex_improve[of S, OF _ imp] nsip
      by auto
  qed
  ultimately show ?thesis
    using nsc nsp nsi nsco nso nsp nspr
    by (auto simp: cdcl_bnb.simps)
qed

lemma all_struct_init_state_distinct_iff:
  \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state (init_state N)) \<longleftrightarrow>
  distinct_mset_mset N\<close>
  unfolding init_state.simps[symmetric]
  by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
      cdcl\<^sub>W_restart_mset.no_strange_atm_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_alt_def
      abs_state_def cdcl\<^sub>W_restart_mset_state)

lemma no_step_ocdcl\<^sub>w_stgy_no_step_cdcl_bnb_stgy:
  assumes \<open>no_step ocdcl\<^sub>w_stgy S\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>no_step cdcl_bnb_stgy S\<close>
  using assms no_step_ocdcl\<^sub>w_no_step_cdcl_bnb[of S]
  by (auto simp: ocdcl\<^sub>w_stgy.simps ocdcl\<^sub>w.simps cdcl_bnb.simps cdcl_bnb_stgy.simps
    dest: ocdcl_conflict_opt_conflict_opt pruning_conflict_opt)

lemma full_ocdcl\<^sub>w_stgy_full_cdcl_bnb_stgy:
  assumes \<open>full ocdcl\<^sub>w_stgy S T\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>full cdcl_bnb_stgy S T\<close>
  using assms rtranclp_ocdcl\<^sub>w_stgy_rtranclp_cdcl_bnb_stgy[of S T]
    no_step_ocdcl\<^sub>w_stgy_no_step_cdcl_bnb_stgy[of T]
  unfolding full_def
  by (auto dest: rtranclp_cdcl_bnb_stgy_all_struct_inv[OF rtranclp_cdcl_bnb_stgy_cdcl_bnb])

corollary full_ocdcl\<^sub>w_stgy_no_conflicting_clause_from_init_state: (* \htmllink{ocdcl-correctness} *)
  assumes
    st: \<open>full ocdcl\<^sub>w_stgy (init_state N) T\<close> and
    dist: \<open>distinct_mset_mset N\<close>
  shows
    \<open>weight T = None \<Longrightarrow> unsatisfiable (set_mset N)\<close> and
    \<open>weight T \<noteq> None \<Longrightarrow> model_on (set_mset (the (weight T))) N \<and> set_mset (the (weight T)) \<Turnstile>sm N \<and>
       distinct_mset (the (weight T))\<close> and
    \<open>distinct_mset I \<Longrightarrow> consistent_interp (set_mset I) \<Longrightarrow> atms_of I = atms_of_mm N \<Longrightarrow>
      set_mset I \<Turnstile>sm N \<Longrightarrow> Found (\<rho> I) \<ge> \<rho>' (weight T)\<close>
  using full_cdcl_bnb_stgy_no_conflicting_clause_from_init_state[of N T,
    OF full_ocdcl\<^sub>w_stgy_full_cdcl_bnb_stgy[OF st] dist] dist
  by (auto simp: all_struct_init_state_distinct_iff model_on_def
    dest: multi_member_split)


lemma wf_ocdcl\<^sub>w:  (* \htmllink{ocdcl-improve-termination} *)
  \<open>wf {(T, S). cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)
     \<and> ocdcl\<^sub>w S T}\<close>
  by (rule wf_subset[OF wf_cdcl_bnb2]) (auto dest: ocdcl\<^sub>w_cdcl_bnb)


subsubsection \<open>Calculus with generalised Improve rule\<close>

text \<open>Now a version with the more general improve rule:\<close>
inductive ocdcl\<^sub>w_p :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> for S :: 'st where
ocdcl_conflict: "conflict S S' \<Longrightarrow> ocdcl\<^sub>w_p S S'" |
ocdcl_propagate: "propagate S S' \<Longrightarrow> ocdcl\<^sub>w_p S S'" |
ocdcl_improve: "improvep S S' \<Longrightarrow> ocdcl\<^sub>w_p S S'" |
ocdcl_conflict_opt: "oconflict_opt S S' \<Longrightarrow> ocdcl\<^sub>w_p S S'" |
ocdcl_other': "ocdcl\<^sub>W_o S S' \<Longrightarrow> ocdcl\<^sub>w_p S S'" |
ocdcl_pruning: "pruning S S' \<Longrightarrow> ocdcl\<^sub>w_p S S'"

inductive ocdcl\<^sub>w_p_stgy :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> for S :: 'st where
ocdcl\<^sub>w_p_conflict: "conflict S S' \<Longrightarrow> ocdcl\<^sub>w_p_stgy S S'" |
ocdcl\<^sub>w_p_propagate: "propagate S S' \<Longrightarrow> ocdcl\<^sub>w_p_stgy S S'" |
ocdcl\<^sub>w_p_improve: "improvep S S' \<Longrightarrow> ocdcl\<^sub>w_p_stgy S S'" |
ocdcl\<^sub>w_p_conflict_opt: "conflict_opt S S' \<Longrightarrow> ocdcl\<^sub>w_p_stgy S S'"|
ocdcl\<^sub>w_p_pruning: "pruning S S' \<Longrightarrow> ocdcl\<^sub>w_p_stgy S S'" |
ocdcl\<^sub>w_p_other': "ocdcl\<^sub>W_o S S' \<Longrightarrow> no_confl_prop_impr S \<Longrightarrow> ocdcl\<^sub>w_p_stgy S S'"

lemma ocdcl\<^sub>w_p_cdcl_bnb:
  assumes \<open>ocdcl\<^sub>w_p S T\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>cdcl_bnb S T\<close>
  using assms by (cases) (auto intro: cdcl_bnb.intros dest: pruning_conflict_opt
    ocdcl_conflict_opt_conflict_opt)


lemma ocdcl\<^sub>w_p_stgy_cdcl_bnb_stgy:
  assumes \<open>ocdcl\<^sub>w_p_stgy S T\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>cdcl_bnb_stgy S T\<close>
  using assms by (cases) (auto intro: cdcl_bnb_stgy.intros dest: pruning_conflict_opt)

lemma rtranclp_ocdcl\<^sub>w_p_stgy_rtranclp_cdcl_bnb_stgy:
  assumes \<open>ocdcl\<^sub>w_p_stgy\<^sup>*\<^sup>* S T\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>cdcl_bnb_stgy\<^sup>*\<^sup>* S T\<close>
  using assms
  by (induction rule: rtranclp_induct)
    (auto dest: rtranclp_cdcl_bnb_stgy_all_struct_inv[OF rtranclp_cdcl_bnb_stgy_cdcl_bnb]
      ocdcl\<^sub>w_p_stgy_cdcl_bnb_stgy)

lemma no_step_ocdcl\<^sub>w_p_no_step_cdcl_bnb:
  assumes \<open>no_step ocdcl\<^sub>w_p S\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>no_step cdcl_bnb S\<close>
proof -
  have
    nsc: \<open>no_step conflict S\<close> and
    nsp: \<open>no_step propagate S\<close> and
    nsi: \<open>no_step improvep S\<close> and
    nsco: \<open>no_step oconflict_opt S\<close> and
    nso: \<open>no_step ocdcl\<^sub>W_o S\<close>and
    nspr: \<open>no_step pruning S\<close>
    using assms(1) by (auto simp: cdcl_bnb.simps ocdcl\<^sub>w_p.simps)
  have alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (abs_state S)\<close> and
    lev: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (abs_state S)\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  have incl: \<open>atms_of (lit_of `# mset (trail S)) \<subseteq> atms_of_mm (init_clss S)\<close>
    using alien unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
    by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state lits_of_def image_image atms_of_def)
  have dist: \<open>distinct_mset (lit_of `# mset (trail S))\<close> and
    cons: \<open>consistent_interp (set (map lit_of (trail S)))\<close> and
    tauto: \<open>\<not>tautology (lit_of `# mset (trail S))\<close> and
    n_d: \<open>no_dup (trail S)\<close>
    using lev unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state lits_of_def image_image atms_of_def
      dest: no_dup_map_lit_of no_dup_distinct no_dup_not_tautology)

  have False if \<open>conflict_opt S S'\<close> for S'
  proof -
    have [simp]: \<open>conflicting S = None\<close>
      using that by (auto simp: conflict_opt.simps)
    have 1: \<open>\<not> \<rho>' (weight S) \<le> Found (\<rho> (lit_of `# mset (trail S)))\<close>
      using nsco
      by (auto simp: is_improving_int_def oconflict_opt.simps)
    have 2: \<open>total_over_m (lits_of_l (trail S)) (set_mset (init_clss S))\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then obtain A where
        \<open>A \<in> atms_of_mm (init_clss S)\<close> and
        \<open>A \<notin> atms_of_s (lits_of_l (trail S))\<close>
        by (auto simp: total_over_m_def total_over_set_def)
      then show \<open>False\<close>
        using decide_rule[of S \<open>Pos A\<close>, OF _ _ _ state_eq_ref] nso
        by (auto simp: Decided_Propagated_in_iff_in_lits_of_l ocdcl\<^sub>W_o.simps)
      qed
    have 3: \<open>trail S \<Turnstile>asm init_clss S\<close>
      unfolding true_annots_def
    proof clarify
      fix C
      assume C: \<open>C \<in># init_clss S\<close>
      have \<open>total_over_m (lits_of_l (trail S)) {C}\<close>
        using 2 C by (auto dest!: multi_member_split)
      moreover have \<open>\<not> trail S \<Turnstile>as CNot C\<close>
        using C nsc conflict_rule[of S C, OF _ _ _ state_eq_ref]
        by (auto simp: clauses_def dest!: multi_member_split)
      ultimately show \<open>trail S \<Turnstile>a C\<close>
        using total_not_CNot[of \<open>lits_of_l (trail S)\<close> C] unfolding true_annots_true_cls true_annot_def
        by auto
    qed
    have 4: \<open>lit_of `# mset (trail S) \<in> simple_clss (atms_of_mm (init_clss S))\<close>
      using tauto cons incl dist by (auto simp: simple_clss_def)

    have [intro]: \<open>\<rho> (lit_of `# mset M') = \<rho> (lit_of `# mset (trail S))\<close>
      if
        \<open>lit_of `# mset (trail S) \<in> simple_clss (atms_of_mm (init_clss S))\<close> and
        \<open>atms_of (lit_of `# mset (trail S)) \<subseteq> atms_of_mm (init_clss S)\<close> and
        \<open>no_dup (trail S)\<close> and
        \<open>total_over_m (lits_of_l M') (set_mset (init_clss S))\<close> and
        incl: \<open>mset (trail S) \<subseteq># mset M'\<close> and
        \<open>lit_of `# mset M' \<in> simple_clss (atms_of_mm (init_clss S))\<close>
      for M' :: \<open>('v literal, 'v literal, 'v literal multiset) annotated_lit list\<close>
    proof -
      have [simp]: \<open>lits_of_l M' = set_mset (lit_of `# mset M')\<close>
        by (auto simp: lits_of_def)
      obtain A where A: \<open>mset M' = A + mset (trail S)\<close>
        using incl by (auto simp: mset_subset_eq_exists_conv)
      have M': \<open>lits_of_l M' = lit_of ` set_mset A \<union> lits_of_l (trail S)\<close>
        unfolding lits_of_def
        by (metis A image_Un set_mset_mset set_mset_union)
      have \<open>mset M' = mset (trail S)\<close>
        using that 2 unfolding A total_over_m_alt_def
          apply (case_tac A)
        apply (auto simp: A simple_clss_def distinct_mset_add M' image_Un
            tautology_union mset_inter_empty_set_mset atms_of_def atms_of_s_def
            atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set image_image
            tautology_add_mset)
          by (metis (no_types, lifting) atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
          lits_of_def subsetCE)
      then show ?thesis
        using 2 by auto
    qed
    have imp: \<open>is_improving (trail S) (trail S) S\<close>
      using 1 2 3 4 incl n_d unfolding is_improving_int_def
      by (auto simp:  oconflict_opt.simps)

    show \<open>False\<close>
      using trail_is_improving_Ex_improve[of S, OF _ imp] nsi by auto
  qed
  then show ?thesis
    using nsc nsp nsi nsco nso nsp nspr
    by (auto simp: cdcl_bnb.simps)
qed

lemma no_step_ocdcl\<^sub>w_p_stgy_no_step_cdcl_bnb_stgy:
  assumes \<open>no_step ocdcl\<^sub>w_p_stgy S\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>no_step cdcl_bnb_stgy S\<close>
  using assms no_step_ocdcl\<^sub>w_p_no_step_cdcl_bnb[of S]
  by (auto simp: ocdcl\<^sub>w_p_stgy.simps ocdcl\<^sub>w_p.simps
    cdcl_bnb.simps cdcl_bnb_stgy.simps)

lemma full_ocdcl\<^sub>w_p_stgy_full_cdcl_bnb_stgy:
  assumes \<open>full ocdcl\<^sub>w_p_stgy S T\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>full cdcl_bnb_stgy S T\<close>
  using assms rtranclp_ocdcl\<^sub>w_p_stgy_rtranclp_cdcl_bnb_stgy[of S T]
    no_step_ocdcl\<^sub>w_p_stgy_no_step_cdcl_bnb_stgy[of T]
  unfolding full_def
  by (auto dest: rtranclp_cdcl_bnb_stgy_all_struct_inv[OF rtranclp_cdcl_bnb_stgy_cdcl_bnb])

corollary full_ocdcl\<^sub>w_p_stgy_no_conflicting_clause_from_init_state: (* \htmllink{ocdcl-improvep-correctness} *)
  assumes
    st: \<open>full ocdcl\<^sub>w_p_stgy (init_state N) T\<close> and
    dist: \<open>distinct_mset_mset N\<close>
  shows
    \<open>weight T = None \<Longrightarrow> unsatisfiable (set_mset N)\<close> and
    \<open>weight T \<noteq> None \<Longrightarrow> model_on (set_mset (the (weight T))) N \<and> set_mset (the (weight T)) \<Turnstile>sm N \<and>
       distinct_mset (the (weight T))\<close> and
    \<open>distinct_mset I \<Longrightarrow> consistent_interp (set_mset I) \<Longrightarrow> atms_of I = atms_of_mm N \<Longrightarrow>
      set_mset I \<Turnstile>sm N \<Longrightarrow> Found (\<rho> I) \<ge> \<rho>' (weight T)\<close>
  using full_cdcl_bnb_stgy_no_conflicting_clause_from_init_state[of N T,
    OF full_ocdcl\<^sub>w_p_stgy_full_cdcl_bnb_stgy[OF st] dist] dist
  by (auto simp: all_struct_init_state_distinct_iff model_on_def
    dest: multi_member_split)


lemma cdcl_bnb_stgy_no_smaller_propa:
  \<open>cdcl_bnb_stgy S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S) \<Longrightarrow>
    no_smaller_propa S \<Longrightarrow> no_smaller_propa T\<close>
  apply (induction rule: cdcl_bnb_stgy.induct)
  subgoal
    by (auto simp: no_smaller_propa_def propagated_cons_eq_append_decide_cons
        conflict.simps propagate.simps improvep.simps conflict_opt.simps
        ocdcl\<^sub>W_o.simps no_smaller_propa_tl cdcl_bnb_bj.simps
        elim!: rulesE)
  subgoal
    by (auto simp: no_smaller_propa_def propagated_cons_eq_append_decide_cons
        conflict.simps propagate.simps improvep.simps conflict_opt.simps
        ocdcl\<^sub>W_o.simps no_smaller_propa_tl cdcl_bnb_bj.simps
        elim!: rulesE)
  subgoal
    by (auto simp: no_smaller_propa_def propagated_cons_eq_append_decide_cons
        conflict.simps propagate.simps improvep.simps conflict_opt.simps
        ocdcl\<^sub>W_o.simps no_smaller_propa_tl cdcl_bnb_bj.simps
        elim!: rulesE)
  subgoal
    by (auto simp: no_smaller_propa_def propagated_cons_eq_append_decide_cons
        conflict.simps propagate.simps improvep.simps conflict_opt.simps
        ocdcl\<^sub>W_o.simps no_smaller_propa_tl cdcl_bnb_bj.simps
        elim!: rulesE)
  subgoal for T
    apply (cases rule: ocdcl\<^sub>W_o.cases, assumption; thin_tac \<open>ocdcl\<^sub>W_o S T\<close>)
    subgoal
      using decide_no_smaller_step[of S T] unfolding no_confl_prop_impr.simps by auto
    subgoal
      apply (cases rule: cdcl_bnb_bj.cases, assumption; thin_tac \<open>cdcl_bnb_bj S T\<close>)
      subgoal
        by (use no_smaller_propa_tl[of S T] in \<open>auto elim: rulesE\<close>)
      subgoal
        by (use no_smaller_propa_tl[of S T] in \<open>auto elim: rulesE\<close>)
      subgoal
        using backtrackg_no_smaller_propa[OF obacktrack_backtrackg, of S T]
        unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
        by (auto elim: obacktrackE)
      done
    done
  done

lemma rtranclp_cdcl_bnb_stgy_no_smaller_propa:
  \<open>cdcl_bnb_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S) \<Longrightarrow>
    no_smaller_propa S \<Longrightarrow> no_smaller_propa T\<close>
  by (induction rule: rtranclp_induct)
    (use rtranclp_cdcl_bnb_stgy_all_struct_inv
        rtranclp_cdcl_bnb_stgy_cdcl_bnb in \<open>force intro: cdcl_bnb_stgy_no_smaller_propa\<close>)+

lemma wf_ocdcl\<^sub>w_p:  (* \htmllink{ocdcl-improvep-termination} *)
  \<open>wf {(T, S). cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)
     \<and> ocdcl\<^sub>w_p S T}\<close>
  by (rule wf_subset[OF wf_cdcl_bnb2]) (auto dest: ocdcl\<^sub>w_p_cdcl_bnb)

end

end