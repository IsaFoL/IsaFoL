theory CDCL_W_Termination
imports CDCL_W
begin

context conflict_driven_clause_learning\<^sub>W
begin

subsection \<open>Termination\<close>

subsubsection \<open>No Relearning of a clause\<close>

text \<open>
  Because of the conflict minimisation, this version is less clear than the version without:
  instead of extracting the clause from the conflicting clause, we must take it from the clause
  used to backjump; i.e., the annotation of the first literal of the trail.

  We also prove below that no learned clause is subsumed by a (smaller) clause in the clause set. 
\<close>
lemma cdcl\<^sub>W_stgy_no_relearned_clause:
  assumes
    cdcl: \<open>backtrack S T\<close> and
    inv: \<open>cdcl\<^sub>W_all_struct_inv S\<close> and
    smaller: \<open>no_smaller_propa S\<close>
  shows
    \<open>mark_of (hd_trail T) \<notin># clauses S\<close>
proof (rule ccontr)
  assume n_dist: \<open>\<not> ?thesis\<close>
  obtain K L :: "'v literal" and
    M1 M2 :: "('v, 'v clause) ann_lit list" and i :: nat and D D' where
    confl_S: "conflicting S = Some (add_mset L D)" and
    decomp: "(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S))" and
    lev_L: "get_level (trail S) L = backtrack_lvl S" and
    max_D_L: "get_level (trail S) L = get_maximum_level (trail S) (add_mset L D')" and
    i: "get_maximum_level (trail S) D' \<equiv> i" and
    lev_K: "get_level (trail S) K = i + 1" and
    T: "T \<sim> cons_trail (Propagated L (add_mset L D'))
        (reduce_trail_to M1
          (add_learned_cls (add_mset L D')
            (update_conflicting None S)))" and
    D_D': \<open>D' \<subseteq># D\<close> and
    \<open>clauses S \<Turnstile>pm add_mset L D'\<close>
    using cdcl by (auto elim!: rulesE)

  obtain M2' where M2': \<open>trail S = (M2' @ M2) @ Decided K # M1\<close>
    using decomp by auto
  have inv_T: \<open>cdcl\<^sub>W_all_struct_inv T\<close>
    using cdcl cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv inv W_other backtrack bj
      cdcl\<^sub>W_all_struct_inv_inv cdcl\<^sub>W_cdcl\<^sub>W_restart by blast

  have M1_D': \<open>M1 \<Turnstile>as CNot D'\<close>
    using backtrack_M1_CNot_D'[of S D' \<open>i\<close> K M1 M2 L \<open>add_mset L D\<close> T
        \<open>Propagated L (add_mset L D')\<close>] inv confl_S decomp i T D_D' lev_K lev_L max_D_L
    unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_conflicting_def
    by (auto simp: subset_mset_trans_add_mset)
  have \<open>undefined_lit M1 L\<close>
    using inv_T T decomp unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def
    by (auto simp: defined_lit_map)
  moreover have \<open>D' + {#L#} \<in># clauses S\<close>
    using n_dist T by (auto simp: clauses_def)
  ultimately show False
    using smaller M1_D' unfolding no_smaller_propa_def M2' by blast
qed

lemma cdcl\<^sub>W_stgy_no_relearned_larger_clause:
  assumes
    cdcl: \<open>backtrack S T\<close> and
    inv: \<open>cdcl\<^sub>W_all_struct_inv S\<close> and
    smaller: \<open>no_smaller_propa S\<close> and
    smaller_conf: \<open>no_smaller_confl S\<close> and
    E_subset: \<open>E \<subset># mark_of (hd_trail T)\<close>
  shows \<open>E \<notin># clauses S\<close>
proof (rule ccontr)
  assume n_dist: \<open>\<not> ?thesis\<close>
  obtain K L :: "'v literal" and
    M1 M2 :: "('v, 'v clause) ann_lit list" and i :: nat and D D' where
    confl_S: "conflicting S = Some (add_mset L D)" and
    decomp: "(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S))" and
    lev_L: "get_level (trail S) L = backtrack_lvl S" and
    max_D_L: "get_level (trail S) L = get_maximum_level (trail S) (add_mset L D')" and
    i: "get_maximum_level (trail S) D' \<equiv> i" and
    lev_K: "get_level (trail S) K = i + 1" and
    T: "T \<sim> cons_trail (Propagated L (add_mset L D'))
        (reduce_trail_to M1
          (add_learned_cls (add_mset L D')
            (update_conflicting None S)))" and
    D_D': \<open>D' \<subseteq># D\<close> and
    \<open>clauses S \<Turnstile>pm add_mset L D'\<close>
    using cdcl by (auto elim!: rulesE)

  obtain M2' where M2': \<open>trail S = (M2' @ M2) @ Decided K # M1\<close>
    using decomp by auto
  have inv_T: \<open>cdcl\<^sub>W_all_struct_inv T\<close>
    using cdcl cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv inv W_other backtrack bj
      cdcl\<^sub>W_all_struct_inv_inv cdcl\<^sub>W_cdcl\<^sub>W_restart by blast
  have \<open>distinct_mset (add_mset L D')\<close>
    using inv_T T unfolding cdcl\<^sub>W_all_struct_inv_def distinct_cdcl\<^sub>W_state_def
    by auto
  then have dist_E: \<open>distinct_mset E\<close>
    using distinct_mset_mono_strict[OF E_subset] T by auto

  have M1_D': \<open>M1 \<Turnstile>as CNot D'\<close>
    using backtrack_M1_CNot_D'[of S D' \<open>i\<close> K M1 M2 L \<open>add_mset L D\<close> T
        \<open>Propagated L (add_mset L D')\<close>] inv confl_S decomp i T D_D' lev_K lev_L max_D_L
    unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_conflicting_def
    by (auto simp: subset_mset_trans_add_mset)
  have undef_L: \<open>undefined_lit M1 L\<close>
    using inv_T T decomp unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def
    by (auto simp: defined_lit_map)

  show False
  proof (cases \<open>L \<in># E\<close>)
    case True
    then obtain E' where
      E: \<open>E = add_mset L E'\<close>
      by (auto dest: multi_member_split)
    then have \<open>distinct_mset E'\<close> and \<open>L \<notin># E'\<close> and E'_E': \<open>E' \<subseteq># D'\<close>
      using dist_E T E_subset by auto
    then have M1_E': \<open>M1 \<Turnstile>as CNot E'\<close>
      using M1_D' T unfolding true_annots_true_cls_def_iff_negation_in_model
      by (auto dest: multi_member_split[of _ E] mset_subset_eq_insertD)
    have propa:  \<open>\<And>M' K M L D. trail S = M' @ Decided K # M \<Longrightarrow>
      D + {#L#} \<in># clauses S \<Longrightarrow> undefined_lit M L \<Longrightarrow> \<not> M \<Turnstile>as CNot D\<close>
      using smaller unfolding no_smaller_propa_def by blast
    show False
      using M1_E' propa[of \<open>M2' @ M2\<close> K M1 E', OF M2' _ undef_L] n_dist unfolding E
      by auto
  next
    case False
    then have \<open>E \<subseteq># D'\<close>
      using E_subset T by (auto simp: subset_add_mset_notin_subset)
    then have M1_E: \<open>M1 \<Turnstile>as CNot E\<close>
      using M1_D' T dist_E E_subset unfolding  true_annots_true_cls_def_iff_negation_in_model
      by (auto dest: multi_member_split[of _ E] mset_subset_eq_insertD)
    have confl:  \<open>\<And>M' K M L D. trail S = M' @ Decided K # M \<Longrightarrow>
      D \<in># clauses S \<Longrightarrow> \<not> M \<Turnstile>as CNot D\<close>
      using smaller_conf unfolding no_smaller_confl_def by blast
    show False
      using confl[of \<open>M2' @ M2\<close> K M1 E, OF M2'] n_dist M1_E
      by auto
  qed
qed

lemma cdcl\<^sub>W_stgy_no_relearned_highest_subres_clause:
  assumes
    cdcl: \<open>backtrack S T\<close> and
    inv: \<open>cdcl\<^sub>W_all_struct_inv S\<close> and
    smaller: \<open>no_smaller_propa S\<close> and
    smaller_conf: \<open>no_smaller_confl S\<close> and
    E_subset: \<open>mark_of (hd_trail T) = add_mset (lit_of (hd_trail T)) E\<close>
  shows \<open>add_mset (- lit_of (hd_trail T)) E \<notin># clauses S\<close>
proof (rule ccontr)
  assume n_dist: \<open>\<not> ?thesis\<close>
  obtain K L :: "'v literal" and
    M1 M2 :: "('v, 'v clause) ann_lit list" and i :: nat and D D' where
    confl_S: "conflicting S = Some (add_mset L D)" and
    decomp: "(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S))" and
    lev_L: "get_level (trail S) L = backtrack_lvl S" and
    max_D_L: "get_level (trail S) L = get_maximum_level (trail S) (add_mset L D')" and
    i: "get_maximum_level (trail S) D' \<equiv> i" and
    lev_K: "get_level (trail S) K = i + 1" and
    T: "T \<sim> cons_trail (Propagated L (add_mset L D'))
        (reduce_trail_to M1
          (add_learned_cls (add_mset L D')
            (update_conflicting None S)))" and
    D_D': \<open>D' \<subseteq># D\<close> and
    \<open>clauses S \<Turnstile>pm add_mset L D'\<close>
    using cdcl by (auto elim!: rulesE)

  obtain M2' where M2': \<open>trail S = (M2' @ M2) @ Decided K # M1\<close>
    using decomp by auto
  have inv_T: \<open>cdcl\<^sub>W_all_struct_inv T\<close>
    using cdcl cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv inv W_other backtrack bj
      cdcl\<^sub>W_all_struct_inv_inv cdcl\<^sub>W_cdcl\<^sub>W_restart by blast
  have \<open>distinct_mset (add_mset L D')\<close>
    using inv_T T unfolding cdcl\<^sub>W_all_struct_inv_def distinct_cdcl\<^sub>W_state_def
    by auto

  have M1_D': \<open>M1 \<Turnstile>as CNot D'\<close>
    using backtrack_M1_CNot_D'[of S D' \<open>i\<close> K M1 M2 L \<open>add_mset L D\<close> T
        \<open>Propagated L (add_mset L D')\<close>] inv confl_S decomp i T D_D' lev_K lev_L max_D_L
    unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_conflicting_def
    by (auto simp: subset_mset_trans_add_mset)
  have undef_L: \<open>undefined_lit M1 L\<close>
    using inv_T T decomp unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def
    by (auto simp: defined_lit_map)
  then have undef_uL: \<open>undefined_lit M1 (-L)\<close>
    by auto
  have propa:  \<open>\<And>M' K M L D. trail S = M' @ Decided K # M \<Longrightarrow>
    D + {#L#} \<in># clauses S \<Longrightarrow> undefined_lit M L \<Longrightarrow> \<not> M \<Turnstile>as CNot D\<close>
    using smaller unfolding no_smaller_propa_def by blast
  have E[simp]: \<open>E = D'\<close>
    using E_subset T by (auto dest: multi_member_split)
  have propa:  \<open>\<And>M' K M L D. trail S = M' @ Decided K # M \<Longrightarrow>
    D + {#L#} \<in># clauses S \<Longrightarrow> undefined_lit M L \<Longrightarrow> \<not> M \<Turnstile>as CNot D\<close>
    using smaller unfolding no_smaller_propa_def by blast
  show False
    using T M1_D' propa[of \<open>M2' @ M2\<close> K M1 D', OF M2' _ undef_uL] n_dist unfolding E
    by auto
qed


lemma cdcl\<^sub>W_stgy_distinct_mset:
  assumes
    cdcl: \<open>cdcl\<^sub>W_stgy S T\<close> and
    inv: "cdcl\<^sub>W_all_struct_inv S" and
    smaller: \<open>no_smaller_propa S\<close> and
    dist: \<open>distinct_mset (clauses S)\<close>
  shows
    \<open>distinct_mset (clauses T)\<close>
proof (rule ccontr)
  assume n_dist: \<open>\<not> distinct_mset (clauses T)\<close>
  then have \<open>backtrack S T\<close>
    using cdcl dist by (auto simp: cdcl\<^sub>W_stgy.simps cdcl\<^sub>W_o.simps cdcl\<^sub>W_bj.simps
        elim: propagateE conflictE decideE skipE resolveE)
  then show False
    using n_dist cdcl\<^sub>W_stgy_no_relearned_clause[of S T] dist
    by (auto simp: inv smaller elim!: rulesE)
qed

text \<open>
  This is a more restrictive version of the previous theorem, but is a better bound for an
  implementation that does not do duplication removal (esp. as part of preprocessing).
\<close>
lemma cdcl\<^sub>W_stgy_learned_distinct_mset:
  assumes
    cdcl: \<open>cdcl\<^sub>W_stgy S T\<close> and
    inv: "cdcl\<^sub>W_all_struct_inv S" and
    smaller: \<open>no_smaller_propa S\<close> and
    dist: \<open>distinct_mset (learned_clss S + remdups_mset (init_clss S))\<close>
  shows
    \<open>distinct_mset (learned_clss T + remdups_mset (init_clss T))\<close>
proof (rule ccontr)
  assume n_dist: \<open>\<not> ?thesis\<close>
  then have \<open>backtrack S T\<close>
    using cdcl dist by (auto simp: cdcl\<^sub>W_stgy.simps cdcl\<^sub>W_o.simps cdcl\<^sub>W_bj.simps
        elim: propagateE conflictE decideE skipE resolveE)
  then show False
    using n_dist cdcl\<^sub>W_stgy_no_relearned_clause[of S T] dist
    by (auto simp: inv smaller clauses_def elim!: rulesE)
qed

lemma rtranclp_cdcl\<^sub>W_stgy_distinct_mset_clauses:
  assumes
    st: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* R S" and
    invR: "cdcl\<^sub>W_all_struct_inv R" and
    dist: "distinct_mset (clauses R)" and
    no_smaller: \<open>no_smaller_propa R\<close>
  shows "distinct_mset (clauses S)"
  using assms by (induction rule: rtranclp_induct)
    (auto simp: cdcl\<^sub>W_stgy_distinct_mset rtranclp_cdcl\<^sub>W_stgy_no_smaller_propa
      rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv)


lemma rtranclp_cdcl\<^sub>W_stgy_distinct_mset_learned_clauses:
  assumes
    st: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* R S" and
    invR: "cdcl\<^sub>W_all_struct_inv R" and
    dist: "distinct_mset (learned_clss R + remdups_mset (init_clss R))" and
    no_smaller: \<open>no_smaller_propa R\<close>
  shows "distinct_mset (learned_clss S + remdups_mset (init_clss S))"
  using assms by (induction rule: rtranclp_induct)
    (auto simp: cdcl\<^sub>W_stgy_learned_distinct_mset rtranclp_cdcl\<^sub>W_stgy_no_smaller_propa
      rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv)

lemma cdcl\<^sub>W_stgy_distinct_mset_clauses:
  assumes
    st: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) S" and
    no_duplicate_clause: "distinct_mset N" and
    no_duplicate_in_clause: "distinct_mset_mset N"
  shows "distinct_mset (clauses S)"
  using rtranclp_cdcl\<^sub>W_stgy_distinct_mset_clauses[OF st] assms
  by (auto simp: cdcl\<^sub>W_all_struct_inv_def distinct_cdcl\<^sub>W_state_def no_smaller_propa_def)

lemma cdcl\<^sub>W_stgy_learned_distinct_mset_new:
  assumes
    cdcl: \<open>cdcl\<^sub>W_stgy S T\<close> and
    inv: "cdcl\<^sub>W_all_struct_inv S" and
    smaller: \<open>no_smaller_propa S\<close> and
    dist: \<open>distinct_mset (learned_clss S - A)\<close>
  shows \<open>distinct_mset (learned_clss T - A)\<close>
proof (rule ccontr)
  have [iff]: \<open>distinct_mset (add_mset C (learned_clss S) - A) \<longleftrightarrow>
     C \<notin># (learned_clss S) - A\<close> for C
    using dist distinct_mset_add_mset[of C \<open>learned_clss S - A\<close>]
  proof -
    have f1: "learned_clss S - A = remove1_mset C (add_mset C (learned_clss S) - A)"
      by (metis Multiset.diff_right_commute add_mset_remove_trivial)
    have "remove1_mset C (add_mset C (learned_clss S) - A) = add_mset C (learned_clss S) - A \<longrightarrow>
        distinct_mset (add_mset C (learned_clss S) - A)"
      by (metis (no_types) Multiset.diff_right_commute add_mset_remove_trivial dist)
    then have "\<not> distinct_mset (add_mset C (learned_clss S - A)) \<or>
        distinct_mset (add_mset C (learned_clss S) - A) \<noteq> (C \<in># learned_clss S - A)"
      by (metis (full_types) Multiset.diff_right_commute
          distinct_mset_add_mset[of C \<open>learned_clss S - A\<close>] add_mset_remove_trivial
          diff_single_trivial insert_DiffM)
    then show ?thesis
      using f1 by (metis (full_types) distinct_mset_add_mset[of C \<open>learned_clss S - A\<close>]
          diff_single_trivial dist insert_DiffM)
  qed

  assume n_dist: \<open>\<not> ?thesis\<close>
  then have \<open>backtrack S T\<close>
    using cdcl dist by (auto simp: cdcl\<^sub>W_stgy.simps cdcl\<^sub>W_o.simps cdcl\<^sub>W_bj.simps
        elim: propagateE conflictE decideE skipE resolveE)
  then show False
    using n_dist cdcl\<^sub>W_stgy_no_relearned_clause[of S T]
    by (auto simp: inv smaller clauses_def elim!: rulesE
        dest!: in_diffD)
qed

lemma rtranclp_cdcl\<^sub>W_stgy_distinct_mset_clauses_new_abs:
  assumes
    st: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* R S" and
    invR: "cdcl\<^sub>W_all_struct_inv R" and
    no_smaller: \<open>no_smaller_propa R\<close> and
    \<open>distinct_mset (learned_clss R - A)\<close>
  shows "distinct_mset (learned_clss S - A)"
  using assms by (induction rule: rtranclp_induct)
    (auto simp: cdcl\<^sub>W_stgy_distinct_mset rtranclp_cdcl\<^sub>W_stgy_no_smaller_propa
      rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv
      cdcl\<^sub>W_stgy_learned_distinct_mset_new)

lemma rtranclp_cdcl\<^sub>W_stgy_distinct_mset_clauses_new:
  assumes
    st: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* R S" and
    invR: "cdcl\<^sub>W_all_struct_inv R" and
    no_smaller: \<open>no_smaller_propa R\<close>
  shows "distinct_mset (learned_clss S - learned_clss R)"
  using assms by (rule rtranclp_cdcl\<^sub>W_stgy_distinct_mset_clauses_new_abs) auto


subsubsection \<open>Decrease of a Measure\<close>

fun cdcl\<^sub>W_restart_measure where
"cdcl\<^sub>W_restart_measure S =
  [(3::nat) ^ (card (atms_of_mm (init_clss S))) - card (set_mset (learned_clss S)),
    if conflicting S = None then 1 else 0,
    if conflicting S = None then card (atms_of_mm (init_clss S)) - length (trail S)
    else length (trail S)
    ]"

lemma length_model_le_vars:
  assumes
    "no_strange_atm S" and
    no_d: "no_dup (trail S)" and
    "finite (atms_of_mm (init_clss S))"
  shows "length (trail S) \<le> card (atms_of_mm (init_clss S))"
proof -
  obtain M N U k D where S: "state S = (M, N, U, k, D)" by (cases "state S", auto)
  have "finite (atm_of ` lits_of_l (trail S))"
    using assms(1,3) unfolding S by (auto simp add: finite_subset)
  have "length (trail S) = card (atm_of ` lits_of_l (trail S))"
    using no_dup_length_eq_card_atm_of_lits_of_l no_d by blast
  then show ?thesis using assms(1) unfolding no_strange_atm_def
  by (auto simp add: assms(3) card_mono)
qed

lemma length_model_le_vars_all_inv:
  assumes "cdcl\<^sub>W_all_struct_inv S"
  shows "length (trail S) \<le> card (atms_of_mm (init_clss S))"
  using assms length_model_le_vars[of S] unfolding cdcl\<^sub>W_all_struct_inv_def
  by (auto simp: cdcl\<^sub>W_M_level_inv_decomp)

lemma learned_clss_less_upper_bound:
  fixes S :: 'st
  assumes
    "distinct_cdcl\<^sub>W_state S" and
    "\<forall>s \<in># learned_clss S. \<not>tautology s"
  shows "card(set_mset (learned_clss S)) \<le> 3 ^ card (atms_of_mm (learned_clss S))"
proof -
  have "set_mset (learned_clss S) \<subseteq> simple_clss (atms_of_mm (learned_clss S))"
    apply (rule simplified_in_simple_clss)
    using assms unfolding distinct_cdcl\<^sub>W_state_def by auto
  then have "card(set_mset (learned_clss S))
    \<le> card (simple_clss (atms_of_mm (learned_clss S)))"
    by (simp add: simple_clss_finite card_mono)
  then show ?thesis
    by (meson atms_of_ms_finite simple_clss_card finite_set_mset order_trans)
qed


lemma cdcl\<^sub>W_restart_measure_decreasing:
  fixes S :: 'st
  assumes
    "cdcl\<^sub>W_restart S S'" and
    no_restart:
      "\<not>(learned_clss S \<subseteq># learned_clss S' \<and> [] = trail S' \<and> conflicting S' = None)"
    (*no restart*) and
    no_forget: "learned_clss S \<subseteq># learned_clss S'" (*no forget*) and
    no_relearn: "\<And>S'. backtrack S S' \<Longrightarrow> mark_of (hd_trail S') \<notin># learned_clss S"
      and
    alien: "no_strange_atm S" and
    M_level: "cdcl\<^sub>W_M_level_inv S" and
    no_taut: "\<forall>s \<in># learned_clss S. \<not>tautology s" and
    no_dup: "distinct_cdcl\<^sub>W_state S" and
    confl: "cdcl\<^sub>W_conflicting S"
  shows "(cdcl\<^sub>W_restart_measure S', cdcl\<^sub>W_restart_measure S) \<in> lexn less_than 3"
  using assms(1) assms(2,3)
proof (induct rule: cdcl\<^sub>W_restart_all_induct)
  case (propagate C L) note conf = this(1) and undef = this(5) and T = this(6)
  have propa: "propagate S (cons_trail (Propagated L C) S)"
    using propagate_rule[OF propagate.hyps(1,2)] propagate.hyps by auto
  then have no_dup': "no_dup (Propagated L C # trail S)"
    using M_level cdcl\<^sub>W_M_level_inv_decomp(2) undef defined_lit_map by auto

  let ?N = "init_clss S"
  have "no_strange_atm (cons_trail (Propagated L C) S)"
    using alien cdcl\<^sub>W_restart.propagate cdcl\<^sub>W_restart_no_strange_atm_inv propa M_level by blast
  then have "atm_of ` lits_of_l (Propagated L C # trail S)
    \<subseteq> atms_of_mm (init_clss S)"
    using undef unfolding no_strange_atm_def by auto
  then have "card (atm_of ` lits_of_l (Propagated L C # trail S))
    \<le> card (atms_of_mm (init_clss S))"
    by (meson atms_of_ms_finite card_mono finite_set_mset)
  then have "length (Propagated L C # trail S) \<le> card (atms_of_mm ?N)"
    using no_dup_length_eq_card_atm_of_lits_of_l no_dup' by fastforce
  then have H: "card (atms_of_mm (init_clss S)) - length (trail S)
    = Suc (card (atms_of_mm (init_clss S)) - Suc (length (trail S)))"
    by simp
  show ?case using conf T undef by (auto simp: H lexn3_conv)
next
  case (decide L) note conf = this(1) and undef = this(2) and T = this(4)
  moreover {
    have dec: "decide S (cons_trail (Decided L) S)"
      using decide_rule decide.hyps by force
    then have "cdcl\<^sub>W_restart S (cons_trail (Decided L) S)"
      using cdcl\<^sub>W_restart.simps cdcl\<^sub>W_o.intros by blast } note cdcl\<^sub>W_restart = this
  moreover {
    have lev: "cdcl\<^sub>W_M_level_inv (cons_trail (Decided L) S)"
      using cdcl\<^sub>W_restart M_level cdcl\<^sub>W_restart_consistent_inv[OF cdcl\<^sub>W_restart] by auto
    then have no_dup: "no_dup (Decided L # trail S)"
      using undef unfolding cdcl\<^sub>W_M_level_inv_def by auto
    have "no_strange_atm (cons_trail (Decided L) S)"
      using M_level alien calculation(4) cdcl\<^sub>W_restart_no_strange_atm_inv by blast
    then have "length (Decided L # (trail S))
      \<le> card (atms_of_mm (init_clss S))"
      using no_dup undef
      length_model_le_vars[of "cons_trail (Decided L) S"]
      by fastforce }
  ultimately show ?case using conf by (simp add: lexn3_conv)
next
  case (skip L C' M D) note tr = this(1) and conf = this(2) and T = this(5)
  show ?case using conf T by (simp add: tr lexn3_conv)
next
  case conflict
  then show ?case by (simp add: lexn3_conv)
next
  case resolve
  then show ?case using finite by (simp add: lexn3_conv)
next
  case (backtrack L D K i M1 M2 T D') note conf = this(1) and decomp = this(3) and D_D' = this(7)
    and T = this(9)
  let ?D' = \<open>add_mset L D'\<close>
  have bt: "backtrack S T"
    using backtrack_rule[OF backtrack.hyps] by auto
  have "?D' \<notin># learned_clss S"
    using no_relearn[OF bt] conf T by auto
  then have card_T:
    "card (set_mset ({#?D'#} + learned_clss S)) = Suc (card (set_mset (learned_clss S)))"
    by simp
  have "distinct_cdcl\<^sub>W_state T"
    using bt M_level distinct_cdcl\<^sub>W_state_inv no_dup other cdcl\<^sub>W_o.intros cdcl\<^sub>W_bj.intros by blast
  moreover have "\<forall>s\<in>#learned_clss T. \<not> tautology s"
    using learned_clss_are_not_tautologies[OF cdcl\<^sub>W_restart.other[OF cdcl\<^sub>W_o.bj[OF
      cdcl\<^sub>W_bj.backtrack[OF bt]]]] M_level no_taut confl by auto
  ultimately have "card (set_mset (learned_clss T)) \<le> 3 ^ card (atms_of_mm (learned_clss T))"
      by (auto simp: learned_clss_less_upper_bound)
    then have H: "card (set_mset ({#?D'#} + learned_clss S))
      \<le> 3 ^ card (atms_of_mm ({#?D'#} + learned_clss S))"
      using T decomp M_level by (simp add: cdcl\<^sub>W_M_level_inv_decomp)
  moreover
    have "atms_of_mm ({#?D'#} + learned_clss S) \<subseteq> atms_of_mm (init_clss S)"
      using alien conf atms_of_subset_mset_mono[OF D_D'] unfolding no_strange_atm_def
      by auto
    then have card_f: "card (atms_of_mm ({#?D'#} + learned_clss S))
      \<le> card (atms_of_mm (init_clss S))"
      by (meson atms_of_ms_finite card_mono finite_set_mset)
    then have "(3::nat) ^ card (atms_of_mm ({#?D'#} + learned_clss S))
      \<le> 3 ^ card (atms_of_mm (init_clss S))" by simp
  ultimately have "(3::nat) ^ card (atms_of_mm (init_clss S))
    \<ge> card (set_mset ({#?D'#} + learned_clss S))"
    using le_trans by blast
  then show ?case using decomp diff_less_mono2 card_T T M_level
    by (auto simp: cdcl\<^sub>W_M_level_inv_decomp lexn3_conv)
next
  case restart
  then show ?case using alien by auto
next
  case (forget C T) note no_forget = this(9)
  then have "C \<in># learned_clss S" and "C \<notin># learned_clss T"
    using forget.hyps by auto
  then have "\<not> learned_clss S \<subseteq># learned_clss T"
     by (auto simp add: mset_subset_eqD)
  then show ?case using no_forget by blast
qed

lemma cdcl\<^sub>W_stgy_step_decreasing:
  fixes S T :: 'st
  assumes
    cdcl: \<open>cdcl\<^sub>W_stgy S T\<close> and
    struct_inv: \<open>cdcl\<^sub>W_all_struct_inv S\<close> and
    smaller: \<open>no_smaller_propa S\<close>
  shows "(cdcl\<^sub>W_restart_measure T, cdcl\<^sub>W_restart_measure S) \<in> lexn less_than 3"
proof (rule cdcl\<^sub>W_restart_measure_decreasing)
  show \<open>cdcl\<^sub>W_restart S T\<close>
    using cdcl cdcl\<^sub>W_cdcl\<^sub>W_restart cdcl\<^sub>W_stgy_cdcl\<^sub>W by blast
  show \<open>\<not> (learned_clss S \<subseteq># learned_clss T \<and> [] = trail T \<and> conflicting T = None)\<close>
    using cdcl by (cases rule: cdcl\<^sub>W_stgy_cases) (auto elim!: rulesE)
  show \<open>learned_clss S \<subseteq># learned_clss T\<close>
    using cdcl by (cases rule: cdcl\<^sub>W_stgy_cases) (auto elim!: rulesE)
  show \<open>mark_of (hd_trail S') \<notin># learned_clss S\<close> if \<open>backtrack S S'\<close> for S'
    using cdcl\<^sub>W_stgy_no_relearned_clause[of S S'] cdcl\<^sub>W_stgy_no_smaller_propa[of S S']
      cdcl struct_inv smaller that unfolding clauses_def
    by (auto elim!: rulesE)
  show \<open>no_strange_atm S\<close> and \<open>cdcl\<^sub>W_M_level_inv S\<close> and \<open>distinct_cdcl\<^sub>W_state S\<close> and
    \<open>cdcl\<^sub>W_conflicting S\<close> and \<open>\<forall>s\<in>#learned_clss S. \<not> tautology s\<close>
    using struct_inv unfolding cdcl\<^sub>W_all_struct_inv_def by blast+
qed

lemma empty_trail_no_smaller_propa: \<open>trail R = [] \<Longrightarrow> no_smaller_propa R\<close>
  by (simp add: no_smaller_propa_def)

text \<open>Roughly corresponds to \cwref{theo:prop:cdcltermlc}{theorem 2.9.15 page 86}
  but using a different bound (the bound is below)\<close>
lemma tranclp_cdcl\<^sub>W_stgy_decreasing:
  fixes R S T :: 'st
  assumes "cdcl\<^sub>W_stgy\<^sup>+\<^sup>+ R S" and
  tr: "trail R = []" and
  "cdcl\<^sub>W_all_struct_inv R"
  shows "(cdcl\<^sub>W_restart_measure S, cdcl\<^sub>W_restart_measure R) \<in> lexn less_than 3"
  using assms
  apply induction
   using empty_trail_no_smaller_propa cdcl\<^sub>W_stgy_no_relearned_clause cdcl\<^sub>W_stgy_step_decreasing
    apply blast
  using tranclp_into_rtranclp[of cdcl\<^sub>W_stgy R] lexn_transI[OF trans_less_than, of 3]
    rtranclp_cdcl\<^sub>W_stgy_no_smaller_propa unfolding trans_def
  by (meson cdcl\<^sub>W_stgy_step_decreasing empty_trail_no_smaller_propa
      rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv)

lemma tranclp_cdcl\<^sub>W_stgy_S0_decreasing:
  fixes R S T :: 'st
  assumes
    pl: "cdcl\<^sub>W_stgy\<^sup>+\<^sup>+ (init_state N) S" and
    no_dup: "distinct_mset_mset N"
  shows "(cdcl\<^sub>W_restart_measure S, cdcl\<^sub>W_restart_measure (init_state N)) \<in> lexn less_than 3"
proof -
  have "cdcl\<^sub>W_all_struct_inv (init_state N)"
    using no_dup unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  then show ?thesis using pl tranclp_cdcl\<^sub>W_stgy_decreasing init_state_trail by blast
qed

lemma wf_tranclp_cdcl\<^sub>W_stgy:
  "wf {(S::'st, init_state N)| S N. distinct_mset_mset N \<and> cdcl\<^sub>W_stgy\<^sup>+\<^sup>+ (init_state N) S}"
  apply (rule wf_wf_if_measure'_notation2[of "lexn less_than 3" _ _ cdcl\<^sub>W_restart_measure])
   apply (simp add: wf wf_lexn)
  using tranclp_cdcl\<^sub>W_stgy_S0_decreasing by blast

text \<open>The following theorems is deeply linked with the strategy: It shows that a decision alone
cannot lead to a conflict. This is obvious but I expect this to be a major part of the proof that
the number of learnt clause cannot be larger that \<^term>\<open>2^n\<close>.\<close>
lemma no_conflict_after_decide:
  assumes
    dec: \<open>decide S T\<close> and
    inv: \<open>cdcl\<^sub>W_all_struct_inv T\<close> and
    smaller: \<open>no_smaller_propa T\<close> and
    smaller_confl: \<open>no_smaller_confl T\<close>
  shows \<open>\<not>conflict T U\<close>
proof (rule ccontr)
  assume \<open>\<not> ?thesis\<close>
  then obtain D where
    D: \<open>D \<in># clauses T\<close> and
    confl: \<open>trail T \<Turnstile>as CNot D\<close>
    by (auto simp: conflict.simps)
  obtain L where
    \<open>conflicting S = None\<close> and
    undef: \<open>undefined_lit (trail S) L\<close> and
    \<open>atm_of L \<in> atms_of_mm (init_clss S)\<close> and
    T: \<open>T \<sim> cons_trail (Decided L) S\<close>
    using dec by (auto simp: decide.simps)
  have dist: \<open>distinct_mset D\<close>
    using inv D unfolding cdcl\<^sub>W_all_struct_inv_def distinct_cdcl\<^sub>W_state_def
    by (auto dest!: multi_member_split simp: clauses_def)
  have L_D: \<open>L \<notin># D\<close>
    using confl undef T
    by (auto dest!: multi_member_split simp: Decided_Propagated_in_iff_in_lits_of_l)
    
  show False
  proof (cases \<open>-L \<in># D\<close>)
    case True
    have H: \<open>trail T = M' @ Decided K # M \<Longrightarrow>
      D + {#L#} \<in># clauses T \<Longrightarrow> undefined_lit M L \<Longrightarrow> \<not> M \<Turnstile>as CNot D\<close>
      for M K M' D L
      using smaller unfolding no_smaller_propa_def
      by auto
    have \<open>trail S \<Turnstile>as CNot (remove1_mset (-L) D)\<close>
      using true_annots_CNot_lit_of_notin_skip[of \<open>Decided L\<close> \<open>trail S\<close> \<open>remove1_mset (-L) D\<close>] T True
        dist confl L_D
      by (auto dest: multi_member_split)
    then show False
      using True H[of \<open>Nil\<close> L \<open>trail S\<close> \<open>remove1_mset (-L) D\<close> \<open>-L\<close>] T D confl undef
      by auto
  next
    case False
    have H: \<open>trail T = M' @ Decided K # M \<Longrightarrow>
      D \<in># clauses T \<Longrightarrow> \<not> M \<Turnstile>as CNot D\<close>
      for M K M' D
      using smaller_confl unfolding no_smaller_confl_def
      by auto
    have \<open>trail S \<Turnstile>as CNot D\<close>
      using true_annots_CNot_lit_of_notin_skip[of \<open>Decided L\<close> \<open>trail S\<close> D] T False
        dist confl L_D
      by (auto dest: multi_member_split)
    then show False
      using False H[of \<open>Nil\<close> L \<open>trail S\<close> D] T D confl undef
      by auto
  qed
qed

abbreviation list_weight_propa_trail :: \<open> ('v literal, 'v literal, 'v literal multiset) annotated_lit list \<Rightarrow> bool list\<close> where
\<open>list_weight_propa_trail M \<equiv> map is_proped M\<close>

definition comp_list_weight_propa_trail :: \<open>nat \<Rightarrow>  ('v literal, 'v literal, 'v literal multiset) annotated_lit list \<Rightarrow> bool list\<close> where
\<open>comp_list_weight_propa_trail b M \<equiv> replicate (b - length M) False @ list_weight_propa_trail M\<close>

lemma comp_list_weight_propa_trail_append[simp]:
  \<open>comp_list_weight_propa_trail b (M @ M') =
     comp_list_weight_propa_trail (b - length M') M @ list_weight_propa_trail M'\<close>
  by (auto simp: comp_list_weight_propa_trail_def)

lemma comp_list_weight_propa_trail_append_single[simp]:
  \<open>comp_list_weight_propa_trail b (M @ [K]) =
    comp_list_weight_propa_trail (b - 1) M @ [is_proped K]\<close>
  by (auto simp: comp_list_weight_propa_trail_def)

lemma comp_list_weight_propa_trail_cons[simp]:
  \<open>comp_list_weight_propa_trail b (K # M') =
    comp_list_weight_propa_trail (b - Suc (length M')) [] @ is_proped K # list_weight_propa_trail M'\<close>
  by (auto simp: comp_list_weight_propa_trail_def)

fun of_list_weight :: \<open>bool list \<Rightarrow> nat\<close> where
  \<open>of_list_weight [] = 0\<close>
| \<open>of_list_weight (b # xs) = (if b then 1 else 0) + 2 * of_list_weight xs\<close>

lemma of_list_weight_append[simp]:
  \<open>of_list_weight (a @ b) = of_list_weight a + 2^(length a) * of_list_weight b\<close>
  by (induction a) auto

lemma of_list_weight_append_single[simp]:
  \<open>of_list_weight (a @ [b]) = of_list_weight a + 2^(length a) * (if b then 1 else 0)\<close>
  using of_list_weight_append[of \<open>a\<close> \<open>[b]\<close>]
  by (auto simp del: of_list_weight_append)

lemma of_list_weight_replicate_False[simp]: \<open>of_list_weight (replicate n False) = 0\<close>
  by (induction n) auto

lemma of_list_weight_replicate_True[simp]: \<open>of_list_weight (replicate n True) = 2^n - 1\<close>
  apply (induction n)
  subgoal by auto
  subgoal for m
    using power_gt1_lemma[of \<open>2 :: nat\<close>]
    by (auto simp add: algebra_simps Suc_diff_Suc)
  done

lemma of_list_weight_le: \<open>of_list_weight xs \<le> 2^(length xs) - 1\<close>
proof -
  have \<open>of_list_weight xs \<le> of_list_weight (replicate (length xs) True)\<close>
    by (induction xs) auto
  then show \<open>?thesis\<close>
    by auto
qed

lemma of_list_weight_lt: \<open>of_list_weight xs < 2^(length xs)\<close>
  using of_list_weight_le[of xs]  by (metis One_nat_def Suc_le_lessD
    Suc_le_mono Suc_pred of_list_weight_le zero_less_numeral zero_less_power)

lemma [simp]: \<open>of_list_weight (comp_list_weight_propa_trail n []) = 0\<close>
  by (auto simp: comp_list_weight_propa_trail_def)

abbreviation propa_weight
  :: \<open>nat \<Rightarrow> ('v literal, 'v literal, 'v literal multiset) annotated_lit list \<Rightarrow> nat\<close>
where
  \<open>propa_weight n M \<equiv> of_list_weight (comp_list_weight_propa_trail n M)\<close>

lemma length_comp_list_weight_propa_trail[simp]: \<open>length (comp_list_weight_propa_trail a M) = max (length M) a\<close>
  by (auto simp: comp_list_weight_propa_trail_def)
  
lemma (in -)pow2_times_n:
  \<open>Suc a \<le> n \<Longrightarrow> 2 * 2^(n - Suc a) = (2::nat)^ (n - a)\<close>
  \<open>Suc a \<le> n \<Longrightarrow> 2^(n - Suc a) * 2 = (2::nat)^ (n - a)\<close>
  \<open>Suc a \<le> n \<Longrightarrow> 2^(n - Suc a) * b * 2 = (2::nat)^ (n - a) * b\<close>
  \<open>Suc a \<le> n \<Longrightarrow> 2^(n - Suc a) * (b * 2) = (2::nat)^ (n - a) * b\<close>
  \<open>Suc a \<le> n \<Longrightarrow> 2^(n - Suc a) * (2 * b) = (2::nat)^ (n - a) * b\<close>
  \<open>Suc a \<le> n \<Longrightarrow> 2 * b * 2^(n - Suc a) = (2::nat)^ (n - a) * b\<close>
  \<open>Suc a \<le> n \<Longrightarrow> 2 * (b * 2^(n - Suc a)) = (2::nat)^ (n - a) * b\<close>
  apply (simp_all add: Suc_diff_Suc semiring_normalization_rules(27))
  using Suc_diff_le by fastforce+
  
lemma decide_propa_weight:
  \<open>decide S T \<Longrightarrow> n \<ge> length (trail T) \<Longrightarrow> propa_weight n (trail S) \<le> propa_weight n (trail T)\<close>
  by (auto elim!: decideE simp: comp_list_weight_propa_trail_def
    algebra_simps pow2_times_n)

lemma propagate_propa_weight:
  \<open>propagate S T \<Longrightarrow> n \<ge> length (trail T) \<Longrightarrow> propa_weight n (trail S) < propa_weight n (trail T)\<close>
  by (auto elim!: propagateE simp: comp_list_weight_propa_trail_def
    algebra_simps pow2_times_n)

(*TODO Move*)
lemma (in -) power_ex_decomp:
  assumes \<open>(R^^n) S T\<close>
  shows
    \<open>\<exists>f. f 0 = S \<and> f n = T \<and> (\<forall>i. i < n \<longrightarrow> R (f i) (f (Suc i)))\<close>
  using assms
proof (induction n arbitrary: T)
  case 0
  then show \<open>?case\<close> by auto
next
  case (Suc n) note IH = this(1) and R = this(2)
  from R obtain T' where
    ST: \<open>(R^^n) S T'\<close> and
    T'T: \<open>R T' T\<close>
    by auto
  obtain f where
    [simp]: \<open>f 0 = S\<close> and
    [simp]: \<open>f n = T'\<close> and
    H: \<open>\<And>i. i < n \<Longrightarrow> R (f i) (f (Suc i))\<close>
    using IH[OF ST] by fast
  let ?f = \<open>f(Suc n := T)\<close>
  show ?case
    by (rule exI[of _ ?f])
      (use H ST T'T in auto)
qed

text \<open>
  The theorem below corresponds the bound of \cwref{theo:prop:cdcltermlc}{theorem 2.9.15 page 86}.
  In the current version there is no proof of the bound.

  The following proof contains an immense amount of stupid bookkeeping. The proof itself
  is rather easy and Isabelle makes it extra-complicated.

  Let's consider the sequence \<^text>\<open>S \<rightarrow> ... \<rightarrow> T\<close>.
  The bookkeping part:
    \<^enum> We decompose it into its components \<^text>\<open>f 0 \<rightarrow> f 1 \<rightarrow> ... \<rightarrow> f n\<close>.
    \<^enum> Then we extract the backjumps out of it, which are at position \<^text>\<open>nth_nj 0\<close>,
      \<^text>\<open>nth_nj 1\<close>, ...
    \<^enum> Then we extract the conflicts out of it, which are at position \<^text>\<open>nth_confl 0\<close>,
      \<^text>\<open>nth_confl 1\<close>, ...

  Then the simple part:
    \<^enum> each backtrack increases \<^term>\<open>propa_weight\<close>
    \<^enum> but \<^term>\<open>propa_weight\<close> is bounded by \<^term>\<open>2 ^ (card (atms_of_mm (init_clss S)))\<close>
  Therefore, we get the bound.

  Comments on the proof:
  \<^item> The main problem of the proof is the number of inductions in the bookkeeping part.
  \<^item> The proof is actually by contradiction to make sure that enough backtrack step exists. This could
    probably be avoided, but without change in the proof.

  Comments on the bound:
  \<^item> The proof is very very crude: Any propagation also decreases the bound. The lemma
    @{thm no_conflict_after_decide} above shows that a decision cannot lead immediately to a
    conflict.
  \<^item> TODO: can a backtrack could be immediately followed by another conflict
    (if there are several conflicts for the initial backtrack)? If not the bound can be divided by
    two.
\<close>
lemma cdcl_pow2_n_learned_clauses:
  assumes
    cdcl: \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S T\<close> and
    confl: \<open>conflicting S = None\<close> and
    inv: \<open>cdcl\<^sub>W_all_struct_inv S\<close>
  shows \<open>size (learned_clss T) \<le> size (learned_clss S) + 2 ^ (card (atms_of_mm (init_clss S)))\<close>
    (is \<open>_ \<le> _ + ?b\<close>)
proof (rule ccontr)
  assume ge: \<open>\<not> ?thesis\<close>
  let ?m = \<open>card (atms_of_mm (init_clss S))\<close>
  obtain n :: nat where
    n: \<open>(cdcl\<^sub>W_stgy^^n) S T\<close>
    using cdcl unfolding rtranclp_power by fast
  then obtain f :: \<open>nat \<Rightarrow> 'st\<close> where
    f: \<open>\<And>i. i < n \<Longrightarrow> cdcl\<^sub>W_stgy (f i) (f (Suc i))\<close> and
    [simp]: \<open>f 0 = S\<close> and
    [simp]: \<open>f n = T\<close>
    using power_ex_decomp[OF n]
    by auto
  
  have cdcl_st_k: \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S (f k)\<close> if \<open>k \<le> n\<close> for k
    using that
    apply (induction k)
    subgoal by auto
    subgoal for k using f[of k] by (auto)
    done
  let ?g = \<open>\<lambda>i. size (learned_clss (f i))\<close>
  have \<open>?g 0 = size (learned_clss S)\<close>
    by auto
  have g_n: \<open>?g n > ?g 0 + 2 ^ (card (atms_of_mm (init_clss S)))\<close>
    using ge by auto
  have g: \<open>?g (Suc i) = ?g i \<or> (?g (Suc i) = Suc (?g i) \<and> backtrack (f i) (f (Suc i)))\<close> if \<open>i < n\<close> for i
    using f[OF that]
    by (cases rule: cdcl\<^sub>W_stgy.cases)
      (auto elim: propagateE conflictE decideE backtrackE skipE resolveE
        simp: cdcl\<^sub>W_o.simps cdcl\<^sub>W_bj.simps)
  have g_le: \<open>?g i \<le> i + ?g 0\<close> if \<open>i \<le> n\<close> for i
    using that
    apply (induction i)
    subgoal by auto
    subgoal for i
      using g[of i]
      by auto
    done
  from this[of n] have n_ge_m: \<open>n > ?b\<close>
    using g_n ge by auto
  then have n0: \<open>n > 0\<close>
    using not_add_less1 by fastforce
  define nth_bj where
    \<open>nth_bj = rec_nat 0 (\<lambda>_ j. (LEAST i. i > j \<and> i < n \<and> backtrack (f i) (f (Suc i))))\<close>
  have [simp]: \<open>nth_bj 0 = 0\<close>
    by (auto simp: nth_bj_def)
  have nth_bj_Suc: \<open>nth_bj (Suc i) = (LEAST x. nth_bj i < x \<and> x < n \<and> backtrack (f x) (f (Suc x)))\<close> for i
    by (auto simp: nth_bj_def)

  have between_nth_bj_not_bt:
    \<open>\<not>backtrack (f k) (f (Suc k))\<close>
    if \<open>k < n\<close> \<open>k > nth_bj i\<close> \<open>k < nth_bj (Suc i) \<close> for k i
    using not_less_Least[of k \<open>\<lambda>x. nth_bj i < x \<and> x < n \<and> backtrack (f x) (f (Suc x))\<close>] that
    unfolding nth_bj_Suc[symmetric]
    by auto
  
  have g_nth_bj_eq:
    \<open>?g (Suc k) = ?g k\<close>
    if \<open>k < n\<close> \<open>k > nth_bj i\<close> \<open>k < nth_bj (Suc i)\<close> for k i
    using between_nth_bj_not_bt[OF that(1-3)] f[of k, OF that(1)]
    by (auto elim: propagateE conflictE decideE backtrackE skipE resolveE
        simp: cdcl\<^sub>W_o.simps cdcl\<^sub>W_bj.simps cdcl\<^sub>W_stgy.simps)
  have g_nth_bj_eq2:
    \<open>?g (Suc k) = ?g (Suc (nth_bj i))\<close>
    if \<open>k < n\<close> \<open>k > nth_bj i\<close> \<open>k < nth_bj (Suc i)\<close> for k i
    using that
    apply (induction k)
    subgoal by blast
    subgoal for k
      using g_nth_bj_eq less_antisym by fastforce
    done
  have [simp]: \<open>?g (Suc 0) = ?g 0\<close>
    using confl f[of 0] n0
    by (auto elim: propagateE conflictE decideE backtrackE skipE resolveE
        simp: cdcl\<^sub>W_o.simps cdcl\<^sub>W_bj.simps cdcl\<^sub>W_stgy.simps)
  have \<open>(?g (nth_bj i) = size (learned_clss S) + (i - 1)) \<and>
    nth_bj i < n \<and>
    nth_bj i \<ge> i \<and>
    (i > 0 \<longrightarrow> backtrack (f (nth_bj i)) (f (Suc (nth_bj i)))) \<and>
    (i > 0 \<longrightarrow> ?g (Suc (nth_bj i)) = size (learned_clss S) + i) \<and>
    (i > 0 \<longrightarrow> nth_bj i > nth_bj (i-1))\<close>
    if \<open>i \<le> ?b+1\<close>
    for i
    using that
  proof (induction i)
    case 0
    then show ?case using n0 by auto
  next
    case (Suc i)
    then have IH: \<open>?g (nth_bj i) = size (learned_clss S) + (i - 1)\<close>
        \<open>0 < i \<longrightarrow> backtrack (f (nth_bj i)) (f (Suc (nth_bj i)))\<close>
	\<open>0 < i \<longrightarrow> ?g (Suc (nth_bj i))  = size (learned_clss S) + i\<close> and
      i_le_m: \<open>Suc i \<le> ?b+1\<close> and
      le_n: \<open>nth_bj i < n\<close> and
      gei: \<open>nth_bj i \<ge> i\<close>
      by auto
    have ex_larger: \<open>\<exists>x>nth_bj i. x < n \<and> backtrack (f x) (f (Suc x))\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then have [simp]: \<open>n>x \<Longrightarrow> x>nth_bj i \<Longrightarrow> ?g (Suc x) = ?g x\<close> for x
        using g[of x] n_ge_m
	by auto
      have eq1: \<open>nth_bj i < Suc x \<Longrightarrow> \<not> nth_bj i < x \<Longrightarrow> x = nth_bj i\<close> and
         eq2: \<open>nth_bj i < x \<Longrightarrow> \<not> nth_bj i < x - Suc 0 \<Longrightarrow> nth_bj i = x - Suc 0\<close>
	 for x
        by simp_all
      have ex_larger: \<open>n>x \<Longrightarrow> x>nth_bj i \<Longrightarrow> ?g (Suc x) = ?g (Suc (nth_bj i))\<close> for x
        apply (induction x)
	subgoal by auto
	subgoal for x
	  by (cases \<open>nth_bj i < x\<close>) (auto dest: eq1)
	done
      from this[of \<open>n-1\<close>] have g_n_nth_bj: \<open>?g n = ?g (Suc (nth_bj i))\<close>
        using n_ge_m i_le_m le_n
	by (cases \<open>nth_bj i < n - Suc 0\<close>)
          (auto dest: eq2)
      then have \<open>size (learned_clss (f (Suc (nth_bj i)))) < size (learned_clss T)\<close>
        using g_n i_le_m n_ge_m g_le[of \<open>Suc (nth_bj i)\<close>] le_n ge
	   \<open>?g (nth_bj i) = size (learned_clss S) + (i - 1)\<close>
	using Suc.IH by auto
      then show False
        using g_n i_le_m n_ge_m g_le[of \<open>Suc (nth_bj i)\<close>] g_n_nth_bj by auto
    qed

    from LeastI_ex[OF ex_larger]
    have bt: \<open>backtrack (f (nth_bj (Suc i))) (f (Suc (nth_bj (Suc i))))\<close> and
      le: \<open>nth_bj (Suc i) < n\<close> and
      nth_mono: \<open>nth_bj i < nth_bj (Suc i)\<close>
      unfolding nth_bj_Suc[symmetric]
      by auto
    
    have g_nth_Suc_g_Suc_nth: \<open>?g (nth_bj (Suc i)) = ?g (Suc (nth_bj i))\<close>
      using g_nth_bj_eq2[of \<open>nth_bj (Suc i) - 1\<close> i] le nth_mono
      apply auto (*TODO proof*)
      by (metis Suc_pred gr0I less_Suc0 less_Suc_eq less_imp_diff_less)
    have H1: \<open>size (learned_clss (f (Suc (nth_bj (Suc i))))) =
       1 + size (learned_clss (f (nth_bj (Suc i))))\<close> if \<open>i = 0\<close>
      using bt unfolding that
      by (auto simp: that elim: backtrackE) 
    have ?case if \<open>i > 0\<close>
      using IH that nth_mono le bt gei
      by (auto elim: backtrackE simp: g_nth_Suc_g_Suc_nth)
    moreover have ?case if \<open>i = 0\<close>
      using le bt gei nth_mono IH g_nth_bj_eq2[of \<open>nth_bj (Suc i) - 1\<close> i]
        g_nth_Suc_g_Suc_nth
      apply (intro conjI)
      subgoal by (simp add: that)
      subgoal by (auto simp: that elim: backtrackE)
      subgoal by (auto simp: that elim: backtrackE)
      subgoal Hk by (auto simp: that elim: backtrackE)
      subgoal using H1 by (auto simp: that elim: backtrackE)
      subgoal using nth_mono by auto
      done
    ultimately show ?case by blast
  qed
  then have
    \<open>(?g (nth_bj i) = size (learned_clss S) + (i - 1))\<close> and
    nth_bj_le: \<open>nth_bj i < n\<close> and
    nth_bj_ge: \<open>nth_bj i \<ge> i\<close> and
    bt_nth_bj: \<open>i > 0 \<Longrightarrow> backtrack (f (nth_bj i)) (f (Suc (nth_bj i)))\<close> and
    \<open>i > 0 \<Longrightarrow> ?g (Suc (nth_bj i)) = size (learned_clss S) + i\<close> and
    nth_bj_mono: \<open>i > 0 \<Longrightarrow> nth_bj (i - 1) < nth_bj i\<close>
    if \<open>i \<le> ?b+1\<close>
    for i
    using that by blast+
  have
    confl_None: \<open>conflicting (f (Suc (nth_bj i))) = None\<close> and
    confl_nth_bj: \<open>conflicting (f (nth_bj i)) \<noteq> None\<close>
    if \<open>i \<le> ?b+1\<close> \<open>i > 0\<close>
    for i
    using bt_nth_bj[OF that] by (auto simp: backtrack.simps)

  have conflicting_still_conflicting:
    \<open>conflicting (f k) \<noteq> None \<longrightarrow> conflicting (f (Suc k)) \<noteq> None\<close>
    if \<open>k < n\<close> \<open>k > nth_bj i\<close> \<open>k < nth_bj (Suc i)\<close> for k i
    using between_nth_bj_not_bt[OF that] f[OF that(1)]
    by (auto elim: propagateE conflictE decideE backtrackE skipE resolveE
        simp: cdcl\<^sub>W_o.simps cdcl\<^sub>W_bj.simps cdcl\<^sub>W_stgy.simps)

  define nth_confl where
    \<open>nth_confl n \<equiv> LEAST i. i > nth_bj n \<and> i < nth_bj (Suc n) \<and> conflict (f i) (f (Suc i))\<close> for n
  have \<open>\<exists>i>nth_bj a. i < nth_bj (Suc a) \<and> conflict (f i) (f (Suc i))\<close>
    if a_n: \<open>a \<le> ?b\<close> \<open>a > 0\<close>
    for a
  proof (rule ccontr)
    assume H: \<open>\<not> ?thesis\<close>
    have \<open>conflicting (f (nth_bj a + Suc i)) = None\<close>
      if \<open>nth_bj a + Suc i \<le> nth_bj (Suc a)\<close> for i :: nat
      using that
      apply (induction i)
      subgoal
        using confl_None[of a] a_n n_ge_m by auto
      subgoal for i
        apply (cases \<open>Suc (nth_bj a + i) < n\<close>)
        using f[of \<open>nth_bj a + Suc i\<close>] H
        apply (auto elim: propagateE conflictE decideE backtrackE skipE resolveE
          simp: cdcl\<^sub>W_o.simps cdcl\<^sub>W_bj.simps cdcl\<^sub>W_stgy.simps)[]
	using nth_bj_le[of \<open>Suc a\<close>] a_n(1) by auto
      done
    from this[of \<open>nth_bj (Suc a) - 1 - nth_bj a\<close>] a_n
    show False
      using nth_bj_mono[of \<open>Suc a\<close>] a_n nth_bj_le[of \<open>Suc a\<close>] confl_nth_bj[of \<open>Suc a\<close>]
      by auto
  qed
  from LeastI_ex[OF this] have nth_bj_le_nth_confl: \<open>nth_bj a < nth_confl a\<close> and
    nth_confl: \<open>conflict (f (nth_confl a)) (f (Suc (nth_confl a)))\<close> and
    nth_confl_le_nth_bj_Suc: \<open>nth_confl a < nth_bj (Suc a)\<close>
    if a_n: \<open>a \<le> ?b\<close> \<open>a > 0\<close>
    for a
    using that unfolding nth_confl_def[symmetric]
    by blast+
  have nth_confl_conflicting: \<open>conflicting (f (Suc (nth_confl a))) \<noteq> None\<close>
    if a_n: \<open>a \<le> ?b\<close> \<open>a > 0\<close>
    for a
    using nth_confl[OF a_n]
    by (auto simp: conflict.simps)
  have no_conflict_before_nth_confl: \<open>\<not>conflict (f k) (f (Suc k))\<close>
    if \<open>k > nth_bj a\<close> and
      \<open>k < nth_confl a\<close> and
      a_n: \<open>a \<le> ?b\<close> \<open>a > 0\<close>
    for k a
    using not_less_Least[of k \<open>\<lambda>i. i > nth_bj a \<and> i < nth_bj (Suc a) \<and> conflict (f i) (f (Suc i))\<close>] that
    nth_confl_le_nth_bj_Suc[of a]
    unfolding nth_confl_def[symmetric]
    by auto
  have conflicting_after_nth_confl: \<open>conflicting (f (Suc (nth_confl a) + k)) \<noteq> None\<close>
    if a_n: \<open>a \<le> ?b\<close> \<open>a > 0\<close> and
      k: \<open>Suc (nth_confl a) + k < nth_bj (Suc a)\<close>
    for a k
    using k
    apply (induction k)
    subgoal using nth_confl_conflicting[OF a_n] by simp
    subgoal for k
      using conflicting_still_conflicting[of \<open>Suc (nth_confl a + k)\<close> a] a_n
        nth_bj_le[of a] nth_bj_le_nth_confl[of a]
      apply (cases \<open>Suc (nth_confl a + k) < n\<close>)
      apply auto
       by (metis (no_types, lifting) Suc_le_lessD add.commute le_less less_trans_Suc nth_bj_le
         plus_1_eq_Suc power_Suc)
    done
  have conflicting_before_nth_confl: \<open>conflicting (f (Suc (nth_bj a) + k)) = None\<close>
    if a_n: \<open>a \<le> ?b\<close> \<open>a > 0\<close> and
      k: \<open>Suc (nth_bj a) + k < nth_confl a\<close>
    for a k
    using k
    apply (induction k)
    subgoal using confl_None[of a] a_n by simp
    subgoal for k
      using f[of \<open>Suc (nth_bj a) + k\<close>] no_conflict_before_nth_confl[of a \<open>Suc (nth_bj a) + k\<close>] a_n
        nth_confl_le_nth_bj_Suc[of a] nth_bj_le[of \<open>Suc a\<close>]
      apply (cases \<open>Suc (nth_bj a + k) < n\<close>)
      apply (auto elim!: propagateE conflictE decideE backtrackE skipE resolveE
          simp: cdcl\<^sub>W_o.simps cdcl\<^sub>W_bj.simps cdcl\<^sub>W_stgy.simps)[]
      by linarith
    done
  have
    ex_trail_decomp: \<open>\<exists>M. trail (f (Suc (nth_confl a))) = M @ trail (f (Suc (nth_confl a + k)))\<close>
    if a_n: \<open>a \<le> ?b\<close> \<open>a > 0\<close> and
      k: \<open>Suc (nth_confl a) + k \<le> nth_bj (Suc a)\<close>
    for a k
    using k
  proof (induction k)
    case 0
    then show \<open>?case\<close> by auto
  next
    case (Suc k)
    moreover have \<open>nth_confl a + k < n\<close>
      proof -
	have "nth_bj (Suc a) < n"
	  by (rule nth_bj_le) (use a_n(1) in simp)
	then show ?thesis
	  using Suc.prems by linarith
      qed
    moreover have \<open>\<exists>Ma. M @ trail (f (Suc (nth_confl a + k))) =
            Ma @ tl (trail (f (Suc (nth_confl a + k))))\<close> for M
      by (cases \<open>trail (f (Suc (nth_confl a + k)))\<close>) auto
    ultimately show ?case
      using f[of \<open>Suc (nth_confl a + k)\<close>] conflicting_after_nth_confl[of a \<open>k\<close>, OF a_n] Suc
        between_nth_bj_not_bt[of \<open>Suc (nth_confl a + k)\<close> \<open>a\<close>]
	nth_bj_le_nth_confl[of a, OF a_n]
      apply (cases \<open>Suc (nth_confl a + k) < n\<close>)
      subgoal
        by (auto elim!: propagateE conflictE decideE skipE resolveE
          simp: cdcl\<^sub>W_o.simps cdcl\<^sub>W_bj.simps cdcl\<^sub>W_stgy.simps)[]
      subgoal
        by (metis (no_types, lifting) Suc_leD Suc_lessI a_n(1) add.commute add_Suc
	  add_mono_thms_linordered_semiring(1) le_numeral_extra(4) not_le nth_bj_le plus_1_eq_Suc)
      done
  qed
  have propa_weight_decreasing_confl:
    \<open>propa_weight n (trail (f (Suc (nth_bj (Suc a))))) > propa_weight n (trail (f (nth_confl a)))\<close>
    if a_n: \<open>a \<le> ?b\<close> \<open>a > 0\<close> and
      n: \<open>n \<ge> length (trail (f (nth_confl a)))\<close>
    for a n
  proof -
    have pw0: \<open>propa_weight n (trail (f (Suc (nth_confl a)))) =
      propa_weight n (trail (f (nth_confl a)))\<close> and
      [simp]: \<open>trail (f (Suc (nth_confl a))) = trail (f (nth_confl a))\<close>
      using nth_confl[OF a_n] by (auto elim!: conflictE)
    have H: \<open>nth_bj (Suc a) = Suc (nth_confl a) \<or> nth_bj (Suc a) \<ge> Suc (Suc (nth_confl a))\<close>
      using nth_bj_le_nth_confl[of a, OF a_n]
      using a_n(1) nth_confl_le_nth_bj_Suc that(2) by force

    from ex_trail_decomp[of a \<open>nth_bj (Suc a) - (1+nth_confl a)\<close>, OF a_n]
    obtain M where
      M: \<open>trail (f (Suc (nth_confl a))) = M @ trail (f (nth_bj (Suc a)))\<close>
      apply -
      apply (rule disjE[OF H])
      subgoal
        by auto
      subgoal
        using nth_bj_le_nth_confl[of a, OF a_n] nth_bj_ge[of \<open>Suc a\<close>] a_n
	by (auto simp add: numeral_2_eq_2)
      done
    obtain K M1 M2 D D' L where
      decomp: \<open>(Decided K # M1, M2)
         \<in> set (get_all_ann_decomposition (trail (f (nth_bj (Suc a)))))\<close> and
      \<open>get_maximum_level (trail (f (nth_bj (Suc a)))) (add_mset L D') =
       backtrack_lvl (f (nth_bj (Suc a)))\<close> and
      \<open>get_level (trail (f (nth_bj (Suc a)))) L = backtrack_lvl (f (nth_bj (Suc a)))\<close> and
      \<open>get_level (trail (f (nth_bj (Suc a)))) K =
       Suc (get_maximum_level (trail (f (nth_bj (Suc a)))) D')\<close> and
      \<open>D' \<subseteq># D\<close> and
      \<open>clauses (f (nth_bj (Suc a))) \<Turnstile>pm add_mset L D'\<close> and
      st_Suc: \<open>f (Suc (nth_bj (Suc a))) \<sim>
       cons_trail (Propagated L (add_mset L D'))
        (reduce_trail_to M1
          (add_learned_cls (add_mset L D')
            (update_conflicting None (f (nth_bj (Suc a))))))\<close>
      using bt_nth_bj[of \<open>Suc a\<close>] a_n
      by (auto elim!: backtrackE)
    obtain M3 where
      tr: \<open>trail (f (nth_bj (Suc a))) = M3 @ M2 @ Decided K # M1\<close>
      using decomp by auto
    define M2' where
      \<open>M2' = M3 @ M2\<close>
    then have
      tr: \<open>trail (f (nth_bj (Suc a))) = M2' @ Decided K # M1\<close>
      using tr by auto
    define M' where
      \<open>M' = M @ M2'\<close>
    then have tr2: \<open>trail (f (nth_confl a)) = M' @ Decided K # M1\<close>
      using tr M n
      by auto
    have [simp]: \<open>max (length M) (n - Suc (length M1 + (length M2')))
      = (n - Suc (length M1 + (length M2')))\<close>
      using tr M st_Suc n by auto
    have [simp]: \<open>2 *
      (of_list_weight (list_weight_propa_trail M1) *
       (2 ^ length M2' *
        (2 ^ (n - Suc (length M1 + length M2'))))) =
	 of_list_weight (list_weight_propa_trail M1) * 2 ^ (n - length M1)\<close>
	 using tr M n by (auto simp: algebra_simps field_simps pow2_times_n 
	   comm_semiring_1_class.semiring_normalization_rules(26))
    have n_ge: \<open>Suc (length M + (length M2' + length M1)) \<le> n\<close>
      using n st_Suc tr M by auto
    have WTF: \<open>a < b \<Longrightarrow> b \<le> c \<Longrightarrow> a < c\<close> and
      WTF': \<open>a \<le> b \<Longrightarrow> b < c \<Longrightarrow> a < c\<close> for a b c :: nat
      by auto

    have 3: \<open>propa_weight (n - Suc (length M1 + (length M2'))) M
      \<le> 2^(n - Suc (length M1 + length M2')) - 1\<close>
      using of_list_weight_le
      apply auto
      by (metis \<open>max (length M) (n - Suc (length M1 + (length M2'))) = n - Suc (length M1 + (length M2'))\<close>
        length_comp_list_weight_propa_trail)
    have 1: \<open>of_list_weight (list_weight_propa_trail M2') *
      2 ^ (n - Suc (length M1 + length M2')) < Suc (if M2' = [] then 0
        else 2 ^ (n - Suc (length M1)) - 2 ^ (n - Suc (length M1 + length M2')))\<close>
      apply (cases \<open>M2' = []\<close>)
      subgoal by auto
      subgoal
	apply (rule WTF')
	  apply (rule Nat.mult_le_mono1[of \<open>of_list_weight (list_weight_propa_trail M2')\<close>,
	  OF of_list_weight_le[of \<open>(list_weight_propa_trail M2')\<close>]])
	using of_list_weight_le[of \<open>(list_weight_propa_trail M2')\<close>] n M tr
	by (auto simp add: comm_semiring_1_class.semiring_normalization_rules(26)
	  algebra_simps)
      done
    have WTF2:
      \<open>a \<le> a' \<Longrightarrow> b < b' \<Longrightarrow> a + b < a' + b'\<close> for a b c a' b' c' :: nat
      by auto

    have \<open>propa_weight (n - Suc (length M1 + length M2')) M +
    of_list_weight (list_weight_propa_trail M2') *
    2 ^ (n - Suc (length M1 + length M2'))
    < 2 ^ (n - Suc (length M1))\<close>
      apply (rule WTF)
      apply (rule WTF2[OF 3 1])
      using n_ge[unfolded nat_le_iff_add] by (auto simp: ac_simps algebra_simps)
    then have \<open>propa_weight n (trail (f (nth_confl a))) < propa_weight n (trail (f (Suc (nth_bj (Suc a)))))\<close>
      using tr2 M st_Suc n tr
      by (auto simp: pow2_times_n algebra_simps
        comm_semiring_1_class.semiring_normalization_rules(26))
    then show \<open>?thesis\<close>
      using pw0 by auto
  qed
  have length_trail_le_m: \<open>length (trail (f k)) < ?m + 1\<close>
    if \<open>k \<le> n\<close>
    for k
  proof -
    have \<open>cdcl\<^sub>W_all_struct_inv (f k)\<close>
      using cdcl_st_k[OF that] inv rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv by blast
    then have \<open>cdcl\<^sub>W_M_level_inv (f k)\<close> and \<open>no_strange_atm (f k)\<close>
      unfolding cdcl\<^sub>W_all_struct_inv_def by blast+
    then have \<open>no_dup (trail (f k))\<close> and
      incl: \<open>atm_of ` lits_of_l (trail (f k)) \<subseteq> atms_of_mm (init_clss (f k))\<close>
      unfolding cdcl\<^sub>W_M_level_inv_def no_strange_atm_def
      by auto
    have eq: \<open>(atms_of_mm (init_clss (f k))) = (atms_of_mm (init_clss S))\<close>
      using rtranclp_cdcl\<^sub>W_stgy_no_more_init_clss[OF cdcl_st_k[OF that]]
      by auto
    have \<open>length (trail (f k)) = card (atm_of ` lits_of_l (trail (f k)))\<close>
      using \<open>no_dup (trail (f k))\<close> no_dup_length_eq_card_atm_of_lits_of_l by blast
    also have \<open>card (atm_of ` lits_of_l (trail (f k))) \<le> ?m\<close>
      using card_mono[OF _ incl] eq by auto
    finally show ?thesis
      by linarith
  qed
  have propa_weight_decreasing_propa:
    \<open>propa_weight ?m (trail (f (nth_confl a))) \<ge> propa_weight ?m (trail (f (Suc (nth_bj a))))\<close>
    if a_n: \<open>a \<le> ?b\<close> \<open>a > 0\<close>
    for a
  proof -
    have ppa: \<open>propa_weight ?m (trail (f (Suc (nth_bj a) + Suc k)))
      \<ge> propa_weight ?m (trail (f (Suc (nth_bj a) + k)))\<close>
      if \<open>k < nth_confl a - Suc (nth_bj a)\<close>
      for k
    proof -
      have \<open>Suc (nth_bj a + k) < n\<close> and \<open>Suc (nth_bj a + k) < nth_confl a\<close>
        using that nth_bj_le_nth_confl[OF a_n] nth_confl_le_nth_bj_Suc[OF a_n]
	  nth_bj_le[of \<open>Suc a\<close>] a_n
	by auto
      then show ?thesis
        using f[of \<open>(Suc (nth_bj a) + k)\<close>] conflicting_before_nth_confl[OF a_n, of \<open>k\<close>]
	no_conflict_before_nth_confl[OF _ _ a_n, of \<open>Suc (nth_bj a) + k\<close>] that
	length_trail_le_m[of \<open>Suc (Suc (nth_bj a) + k)\<close>]
        by (auto elim!: skipE resolveE backtrackE
            simp: cdcl\<^sub>W_o.simps cdcl\<^sub>W_bj.simps cdcl\<^sub>W_stgy.simps
	    dest!: propagate_propa_weight[of _ _ ?m]
	      decide_propa_weight[of _ _ ?m])
    qed
    have WTF3: \<open>(Suc (nth_bj a + (nth_confl a - Suc (nth_bj a)))) = nth_confl a\<close>
      using a_n(1) nth_bj_le_nth_confl that(2) by fastforce
    have \<open>propa_weight ?m (trail (f (Suc (nth_bj a) + k)))
      \<ge> propa_weight ?m (trail (f (Suc (nth_bj a))))\<close>
      if \<open>k \<le> nth_confl a - Suc (nth_bj a)\<close>
      for k
      using that
      apply (induction k)
      subgoal by auto
      subgoal for k using ppa[of k]
        apply (cases \<open>k < nth_confl a - Suc (nth_bj a)\<close>)
	subgoal by auto
	subgoal by linarith
      done
      done
    from this[of \<open>nth_confl a - (Suc (nth_bj a))\<close>]
    show ?thesis
      by (auto simp: WTF3)
  qed 
  have propa_weight_decreasing_confl:
    \<open>propa_weight ?m (trail (f (Suc (nth_bj a))))
      < propa_weight ?m (trail (f (Suc (nth_bj (Suc a)))))\<close>
    if a_n: \<open>a \<le> ?b\<close> \<open>a > 0\<close>
    for a
  proof -
    have WTF: \<open>b < c \<Longrightarrow> a \<le> b \<Longrightarrow> a < c\<close> for a b c  :: nat by linarith
    have \<open>nth_confl a < n\<close>
      by (metis Suc_le_mono a_n(1) add.commute add_lessD1 less_imp_le nat_le_iff_add
        nth_bj_le nth_confl_le_nth_bj_Suc plus_1_eq_Suc that(2))
 
    show ?thesis
      apply (rule WTF)
        apply (rule propa_weight_decreasing_confl[OF a_n, of ?m])
	subgoal using length_trail_le_m[of \<open>nth_confl a\<close>] \<open>nth_confl a < n\<close> by auto
       apply (rule propa_weight_decreasing_propa[OF a_n])
      done
  qed
  have weight1: \<open>propa_weight ?m (trail (f (Suc (nth_bj 1)))) \<ge> 1\<close>
    using bt_nth_bj[of 1]
    by (auto simp: elim!: backtrackE intro!: trans_le_add1)
  have \<open>propa_weight ?m (trail (f (Suc (nth_bj (Suc a))))) \<ge>
       propa_weight ?m (trail (f (Suc (nth_bj 1)))) + a\<close>
    if a_n: \<open>a \<le> ?b\<close>
    for a :: nat
    using that
    apply (induction a)
    subgoal by auto
    subgoal for a
      using propa_weight_decreasing_confl[of \<open>Suc a\<close>]
      by auto
    done
  from this[of \<open>?b\<close>] have \<open>propa_weight ?m (trail (f (Suc (nth_bj (Suc (?b)))))) \<ge> 1 + ?b\<close>
    using weight1 by auto
  moreover have
    \<open>max (length (trail (f (Suc (nth_bj (Suc ?b)))))) ?m = ?m\<close>
    using length_trail_le_m[of \<open>(Suc (nth_bj (Suc ?b)))\<close>] Suc_leI nth_bj_le
    nth_bj_le[of \<open>Suc (?b)\<close>] by (auto simp: max_def)
  ultimately show \<open>False\<close>
    using of_list_weight_le[of \<open>comp_list_weight_propa_trail ?m (trail (f (Suc (nth_bj (Suc ?b)))))\<close>]
    by (simp del: state_eq_init_clss state_eq_trail)
qed

text \<open>Application of the previous theorem to an initial state:\<close>
corollary cdcl_pow2_n_learned_clauses2:
  assumes
    cdcl: \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) T\<close> and
    inv: \<open>cdcl\<^sub>W_all_struct_inv (init_state N)\<close>
  shows \<open>size (learned_clss T) \<le> 2 ^ (card (atms_of_mm N))\<close>
  using assms cdcl_pow2_n_learned_clauses[of \<open>init_state N\<close> T]
  by auto

end

end
