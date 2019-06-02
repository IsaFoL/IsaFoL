theory Watched_Literals_Watch_List_Enumeration
  imports Watched_Literals_List_Enumeration Watched_Literals.Watched_Literals_Watch_List
begin

definition find_decomp_target_wl :: \<open>nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> ('v twl_st_wl \<times> 'v literal) nres\<close> where
  \<open>find_decomp_target_wl =  (\<lambda>i S.
    SPEC(\<lambda>(T, K). \<exists>M2 M1. equality_except_trail_wl S T \<and> get_trail_wl T = M1 \<and>
       (Decided K # M1, M2) \<in> set (get_all_ann_decomposition (get_trail_wl S)) \<and>
          get_level (get_trail_wl S) K = i))\<close>

fun propagate_unit_and_add_wl :: \<open>'v literal \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>propagate_unit_and_add_wl K (M, N, D, NE, UE, Q, W) =
      (Propagated (-K) 0 # M, N, None, add_mset {#-K#} NE, UE, {#K#}, W)\<close>

definition negate_mode_bj_unit_wl   :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
\<open>negate_mode_bj_unit_wl = (\<lambda>S. do {
    (S, K) \<leftarrow> find_decomp_target_wl 1 S;
    ASSERT(K \<in># all_lits_of_mm (clause `# twl_clause_of `# ran_mf (get_clauses_wl S) +
           get_unit_clauses_wl S));
    RETURN (propagate_unit_and_add_wl K S)
  })\<close>

abbreviation find_decomp_target_wl_ref where
  \<open>find_decomp_target_wl_ref S \<equiv>
     {((T, K), (T', K')). (T, T') \<in> {(T, T'). (T, T') \<in> state_wl_l None \<and> correct_watching T} \<and>
        (K , K') \<in> Id \<and>
        K \<in># all_lits_of_mm (clause `# twl_clause_of `# ran_mf (get_clauses_wl T) +
           get_unit_clauses_wl T) \<and>
        K \<in># all_lits_of_mm (clause `# twl_clause_of `# ran_mf (get_clauses_wl T) +
           get_unit_init_clss_wl T) \<and> equality_except_trail_wl S T \<and>
        atms_of (DECO_clause (get_trail_wl S)) \<subseteq> atms_of_mm (clause `# twl_clause_of `# ran_mf (get_clauses_wl T) +
          get_unit_init_clss_wl T) \<and> distinct_mset (DECO_clause (get_trail_wl S)) \<and>
        correct_watching T}\<close>

lemma DECO_clause_nil[simp]: \<open>DECO_clause [] = {#}\<close>
  by (auto simp: DECO_clause_def)

lemma in_DECO_clauseD: \<open>x \<in># DECO_clause M \<Longrightarrow> -x \<in> lits_of_l M\<close>
  by (auto simp: DECO_clause_def lits_of_def)

lemma in_atms_of_DECO_clauseD: \<open>x \<in> atms_of (DECO_clause M) \<Longrightarrow> x \<in> atm_of ` (lits_of_l M)\<close>
  by (auto simp: DECO_clause_def lits_of_def atms_of_def)

lemma no_dup_distinct_mset_DECO_clause:
  assumes \<open>no_dup M\<close>
  shows \<open>distinct_mset (DECO_clause M)\<close>
proof -
  have \<open>distinct (map lit_of (filter is_decided M))\<close>
    using no_dup_map_lit_of[OF assms] distinct_map_filter by blast
  moreover have \<open>?thesis \<longleftrightarrow> distinct (map lit_of (filter is_decided M))\<close>
    unfolding DECO_clause_def image_mset.compositionality[symmetric]
    apply (subst distinct_image_mset_inj)
    subgoal by (auto simp: inj_on_def)
    subgoal by (auto simp flip: mset_filter
      distinct_mset_mset_distinct simp del: mset_filter)
    done
  ultimately show ?thesis by blast
qed

lemma find_decomp_target_wl_find_decomp_target_l:
  assumes
    SS': \<open>(S, S') \<in> {(S, S''). (S, S'') \<in> state_wl_l None \<and> correct_watching S}\<close> and
    inv: \<open>\<exists>S'' b. (S', S'') \<in> twl_st_l b \<and> twl_struct_invs S''\<close> and
    [simp]: \<open>a = a'\<close>
  shows \<open>find_decomp_target_wl a S \<le>
     \<Down> (find_decomp_target_wl_ref S) (find_decomp_target a' S')\<close>
    (is \<open>_ \<le> \<Down> ?negate _\<close>)
proof -
  let ?y0 = \<open>\<lambda>S S'. (\<lambda>(M, Oth). (get_trail_wl S, Oth)) S'\<close>
  have K: \<open>\<And>K. K \<in> lits_of_l (get_trail_wl S) \<Longrightarrow>
     K \<in># all_lits_of_mm (clause `# twl_clause_of `# ran_mf (get_clauses_wl S) +
          get_unit_init_clss_wl S)\<close> (is \<open>\<And>K. ?HK K \<Longrightarrow> ?K K\<close>) and
    DECO:
      \<open>atms_of (DECO_clause (get_trail_wl S)) \<subseteq> atms_of_mm (clause `# twl_clause_of `# ran_mf (get_clauses_wl S) +
          get_unit_init_clss_wl S)\<close> (is ?DECO) and
    distinct_DECO:
      \<open>distinct_mset (DECO_clause (get_trail_wl S))\<close> (is ?dist_DECO)
  proof -
    obtain b S'' where
      S'_S'': \<open>(S', S'') \<in> twl_st_l b\<close> and
      struct: \<open>twl_struct_invs S''\<close>
      using inv unfolding negate_mode_bj_unit_l_inv_def by blast
    then have no_alien: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S'')\<close>
      using struct unfolding twl_struct_invs_def by fast
    then have no_alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of S'')\<close> and
      M_lev: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of S'')\<close>
      unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast+
    moreover have \<open>atms_of_mm (get_all_init_clss S'') =
          atms_of_mm (mset `# (ran_mf (get_clauses_wl S)) + get_unit_init_clss_wl S)\<close>
      apply (subst all_clss_lf_ran_m[symmetric])
      using no_alien
      using S'_S'' SS' unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
      by (cases S; cases S'; cases b)
        (auto simp: mset_take_mset_drop_mset' cdcl\<^sub>W_restart_mset_state
        in_all_lits_of_mm_ain_atms_of_iff twl_st_l_def state_wl_l_def)
    ultimately show \<open>\<And>K. ?HK K \<Longrightarrow> ?K K\<close>
      using S'_S'' SS' unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
      by (auto 5 5 simp: twl_st_l twl_st mset_take_mset_drop_mset'
        in_all_lits_of_mm_ain_atms_of_iff get_unit_clauses_wl_alt_def)
    then show ?DECO
      using S'_S'' SS' unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
      by (auto simp: twl_st_l twl_st mset_take_mset_drop_mset'
        in_all_lits_of_mm_ain_atms_of_iff get_unit_clauses_wl_alt_def
        dest: in_atms_of_DECO_clauseD)

    show ?dist_DECO
      by (rule no_dup_distinct_mset_DECO_clause)
       (use M_lev S'_S'' SS' in \<open>auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def twl_st\<close>)
  qed

  show ?thesis
    using SS'
    unfolding find_decomp_target_wl_def find_decomp_target_def apply -
    apply (rule RES_refine)
    apply (rule_tac x=\<open>(?y0 (fst s) S', snd s)\<close> in bexI)
    subgoal
      using K DECO distinct_DECO
      by (cases S; cases S')
       (force simp: state_wl_l_def correct_watching.simps clause_to_update_def
          mset_take_mset_drop_mset' all_lits_of_mm_union
          dest!: get_all_ann_decomposition_exists_prepend)+
    subgoal
      by (cases S; cases S')
        (auto simp: state_wl_l_def correct_watching.simps clause_to_update_def)
    done
qed

lemma negate_mode_bj_unit_wl_negate_mode_bj_unit_l:
  fixes S :: \<open>'v twl_st_wl\<close> and S' :: \<open>'v twl_st_l\<close>
  assumes \<open>count_decided (get_trail_wl S) = 1\<close> and
    SS': \<open>(S, S') \<in> {(S, S'). (S, S') \<in> state_wl_l None \<and> correct_watching S}\<close>
  shows
    \<open>negate_mode_bj_unit_wl S \<le> \<Down>{(S, S'). (S, S') \<in> state_wl_l None \<and> correct_watching S}
       (negate_mode_bj_unit_l S')\<close>
       (is \<open>_ \<le> \<Down> ?R _\<close>)
proof -
  have 2: \<open>(propagate_unit_and_add_wl x2a x1a, propagate_unit_and_add_l x2 x1)
        \<in> {(S, S''). (S, S'') \<in> state_wl_l None \<and> correct_watching S}\<close>
    if
      \<open>(x, x') \<in> find_decomp_target_wl_ref S\<close> and
      \<open>x' = (x1, x2)\<close> and
      \<open>x = (x1a, x2a)\<close>
    for x2a x1a x2 x1 and x :: \<open>'v twl_st_wl \<times> 'v literal\<close> and x' :: \<open>'v twl_st_l \<times> 'v literal\<close>
  proof -
    show ?thesis
      using that
      by (cases x1a; cases x1)
        (auto, auto simp: state_wl_l_def correct_watching.simps clause_to_update_def
          all_lits_of_mm_add_mset
          all_lits_of_m_add_mset all_lits_of_mm_union mset_take_mset_drop_mset'
          dest: in_all_lits_of_mm_uminusD)
  qed

  show ?thesis
    using SS' unfolding negate_mode_bj_unit_wl_def negate_mode_bj_unit_l_def
    apply (refine_rcg find_decomp_target_wl_find_decomp_target_l 2)
    subgoal unfolding negate_mode_bj_unit_l_inv_def by blast
    subgoal unfolding negate_mode_bj_unit_l_inv_def by blast
    subgoal by blast
    apply assumption+
    done
qed

definition propagate_nonunit_and_add_wl_pre
  :: \<open>'v literal \<Rightarrow> 'v clause_l \<Rightarrow> nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>propagate_nonunit_and_add_wl_pre K C i S \<longleftrightarrow>
     length C \<ge> 2 \<and> i > 0 \<and> i \<notin># dom_m (get_clauses_wl S) \<and>
     atms_of (mset C) \<subseteq> atms_of_mm (clause `# twl_clause_of `# ran_mf (get_clauses_wl S) +
          get_unit_init_clss_wl S)\<close>

fun propagate_nonunit_and_add_wl
  :: \<open>'v literal \<Rightarrow> 'v clause_l \<Rightarrow> nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close>
where
  \<open>propagate_nonunit_and_add_wl K C i (M, N, D, NE, UE, Q, W) = do {
      ASSERT(propagate_nonunit_and_add_wl_pre K C i (M, N, D, NE, UE, Q, W));
      let b = (length C = 2);
      let W = W(C!0 := W (C!0) @ [(i, C!1, b)]);
      let W = W(C!1 := W (C!1) @ [(i, C!0, b)]);
      RETURN (Propagated (-K) i # M, fmupd i (C, True) N, None,
      NE, UE, {#K#}, W)
    }\<close>

lemma twl_st_l_splitD:
  \<open>(\<And>M N D NE UE Q W. f (M, N, D, NE, UE, Q, W) = P M N D NE UE Q W) \<Longrightarrow>
   f S = P (get_trail_l S) (get_clauses_l S) (get_conflict_l S) (get_unit_init_clauses_l S)
    (get_unit_learned_clauses_l S) (clauses_to_update_l S) (literals_to_update_l S)\<close>
  by (cases S) auto

lemma twl_st_wl_splitD:
  \<open>(\<And>M N D NE UE Q W. f (M, N, D, NE, UE, Q, W) = P M N D NE UE Q W) \<Longrightarrow>
   f S = P (get_trail_wl S) (get_clauses_wl S) (get_conflict_wl S) (get_unit_init_clss_wl S)
    (get_unit_learned_clss_wl S) (literals_to_update_wl S) (get_watched_wl S)\<close>
  by (cases S) auto

definition negate_mode_bj_nonunit_wl_inv where
\<open>negate_mode_bj_nonunit_wl_inv S \<longleftrightarrow>
   (\<exists>S'' b. (S, S'') \<in> state_wl_l b \<and> negate_mode_bj_nonunit_l_inv S'' \<and> correct_watching S)\<close>

definition negate_mode_bj_nonunit_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
\<open>negate_mode_bj_nonunit_wl = (\<lambda>S. do {
    ASSERT(negate_mode_bj_nonunit_wl_inv S);
    let C = DECO_clause_l (get_trail_wl S);
    (S, K) \<leftarrow> find_decomp_target_wl (count_decided (get_trail_wl S)) S;
    i \<leftarrow> get_fresh_index_wl (get_clauses_wl S) (get_unit_clauses_wl S) (get_watched_wl S);
    propagate_nonunit_and_add_wl K C i S
  })\<close>


lemmas propagate_nonunit_and_add_wl_def =
   twl_st_wl_splitD[of \<open>propagate_nonunit_and_add_wl _ _ _\<close>, OF propagate_nonunit_and_add_wl.simps]

lemmas propagate_nonunit_and_add_l_def =
   twl_st_l_splitD[of \<open>propagate_nonunit_and_add_l _ _ _\<close>, OF propagate_nonunit_and_add_l.simps,
  rule_format]

lemma atms_of_subset_in_atms_ofI:
  \<open>atms_of C \<subseteq> atms_of_ms N \<Longrightarrow> L \<in># C \<Longrightarrow> atm_of L \<in> atms_of_ms N\<close>
  by (auto dest!: multi_member_split)

lemma in_DECO_clause_l_in_DECO_clause_iff:
  \<open>x \<in> set (DECO_clause_l M) \<longleftrightarrow> x \<in># (DECO_clause M)\<close>
  by (metis DECO_clause_l_DECO_clause set_mset_mset)

lemma distinct_DECO_clause_l:
  \<open>no_dup M \<Longrightarrow> distinct (DECO_clause_l M)\<close>
  by (auto simp: DECO_clause_l_def distinct_map inj_on_def
      dest!: no_dup_map_lit_of)

lemma propagate_nonunit_and_add_wl_propagate_nonunit_and_add_l:
  assumes
    SS': \<open>(S, S') \<in> state_wl_l None\<close> and
    inv: \<open>negate_mode_bj_nonunit_wl_inv S\<close> and
    TK: \<open>(TK, TK') \<in> find_decomp_target_wl_ref S\<close> and
    [simp]: \<open>TK' = (T, K)\<close> and
    [simp]: \<open>TK = (T', K')\<close> and
    ij: \<open>(i, j) \<in> {(i, j). i = j \<and> i \<notin># dom_m (get_clauses_wl T') \<and> i > 0 \<and>
       (\<forall>L \<in># all_lits_of_mm (mset `# ran_mf (get_clauses_wl T') + get_unit_clauses_wl T') .
          i \<notin> fst ` set (watched_by T' L))}\<close>
  shows \<open>propagate_nonunit_and_add_wl K' (DECO_clause_l (get_trail_wl S)) i T'
         \<le> SPEC (\<lambda>c. (c, propagate_nonunit_and_add_l K
                          (DECO_clause_l (get_trail_l S')) j T)
                     \<in> {(S, S'').
                        (S, S'') \<in> state_wl_l None \<and> correct_watching S})\<close>
proof -
  have [simp]: \<open>i = j\<close> and j: \<open>j \<notin># dom_m (get_clauses_wl T')\<close>
    using ij by auto
  have [simp]: \<open>DECO_clause_l (get_trail_l S') = DECO_clause_l (get_trail_wl S)\<close>
    using SS' by auto
  obtain T U b b' where
    ST: \<open>(S, T) \<in> state_wl_l b\<close> and
    corr: \<open>correct_watching S\<close> and
    TU: \<open>(T, U) \<in> twl_st_l b'\<close> and
    \<open>twl_list_invs T\<close> and
    ge1: \<open>1 < count_decided (get_trail_l T)\<close> and
    st: \<open>twl_struct_invs U\<close> and
    \<open>twl_stgy_invs U\<close> and
    \<open>get_conflict_l T = None\<close>
    using inv unfolding negate_mode_bj_nonunit_wl_inv_def negate_mode_bj_nonunit_l_inv_def apply -
    by blast
  have \<open>length (DECO_clause_l (get_trail_wl S)) > 1\<close>
    using ST ge1 by auto
  then have 1: \<open>DECO_clause_l (get_trail_wl S) =
        DECO_clause_l (get_trail_wl S) ! 0 #
           DECO_clause_l (get_trail_wl S) ! Suc 0 # drop 2 (DECO_clause_l (get_trail_wl S))\<close>
    by (cases \<open>DECO_clause_l (get_trail_wl S)\<close>; cases \<open>tl (DECO_clause_l (get_trail_wl S))\<close>)
      auto
  have \<open>no_dup (trail (state\<^sub>W_of U))\<close>
    using st unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by fast
  then have neq: False if \<open>DECO_clause_l (get_trail_wl S) ! 0 = DECO_clause_l (get_trail_wl S) ! Suc 0\<close>
    using that
    apply (subst (asm) nth_eq_iff_index_eq)
    using ge1 ST TU by (auto simp: twl_st twl_st_l twl_st_wl distinct_DECO_clause_l)

  show ?thesis
    using TK j corr ge1 ST
    apply (simp only: propagate_nonunit_and_add_wl_def
       propagate_nonunit_and_add_l_def Let_def
       assert_bind_spec_conv)
    apply (intro conjI)
    subgoal using j ij TK unfolding propagate_nonunit_and_add_wl_pre_def by auto
    subgoal
      unfolding RETURN_def less_eq_nres.simps mem_Collect_eq prod.simps singleton_iff
      apply (subst subset_iff)
      unfolding RETURN_def less_eq_nres.simps mem_Collect_eq prod.simps singleton_iff
      apply (intro conjI impI allI)
      subgoal by (auto simp: state_wl_l_def)
      subgoal
        apply (simp only: )
        apply (subst 1)
        apply (subst One_nat_def[symmetric])+
        apply (subst fun_upd_other)
        subgoal
          using SS' length_DECO_clause_l[of \<open>get_trail_wl S\<close>]
          by (cases \<open>DECO_clause_l (get_trail_wl S)\<close>; cases \<open>tl (DECO_clause_l (get_trail_wl S))\<close>)
            (auto simp: DECO_clause_l_DECO_clause[symmetric] twl_st_l twl_st
            simp del: DECO_clause_l_DECO_clause)
        apply (rule correct_watching_learn[THEN iffD2])
        apply (rule atms_of_subset_in_atms_ofI[of \<open>DECO_clause (get_trail_wl S)\<close>])
        subgoal by (auto simp add: mset_take_mset_drop_mset' get_unit_clauses_wl_alt_def
          DECO_clause_l_DECO_clause[symmetric]
           simp del: DECO_clause_l_DECO_clause)
        subgoal by (solves \<open>auto simp add: mset_take_mset_drop_mset'
          DECO_clause_l_DECO_clause[symmetric]
           simp del: DECO_clause_l_DECO_clause\<close>)
        subgoal apply (use in \<open>auto simp add: mset_take_mset_drop_mset' DECO_clause_l_DECO_clause[symmetric]
           simp del: DECO_clause_l_DECO_clause\<close>)
          by (metis (no_types, lifting) "1" UnE add_mset_commute image_eqI mset.simps(2)
              set_mset_mset subsetCE union_single_eq_member)
        subgoal \<comment> \<open>TODO Proof\<close>
         apply (auto simp: mset_take_mset_drop_mset' in_DECO_clause_l_in_DECO_clause_iff
           dest!: in_set_dropD)
           by (metis UnE atms_of_ms_union atms_of_subset_in_atms_ofI)
        subgoal by simp
        subgoal using corr ij
          by (cases S; cases T; cases T')
            (auto simp: equality_except_trail_wl.simps state_wl_l_def correct_watching.simps
             clause_to_update_def)
        subgoal using corr neq
          by (cases S; cases T; cases T')
           (auto simp: equality_except_trail_wl.simps state_wl_l_def correct_watching.simps
             clause_to_update_def)
        subgoal
          by (subst 1) auto
        subgoal using corr
          by (cases S; cases T; cases T')
           (auto simp: equality_except_trail_wl.simps state_wl_l_def correct_watching.simps
             clause_to_update_def)
        done
      done
    done
  qed

lemma watched_by_alt_def:
  \<open>watched_by T L = get_watched_wl T L\<close>
  by (cases T) auto

lemma negate_mode_bj_nonunit_wl_negate_mode_bj_nonunit_l:
  fixes S :: \<open>'v twl_st_wl\<close> and S' :: \<open>'v twl_st_l\<close>
  assumes
    SS': \<open>(S, S') \<in> {(S, S''). (S, S'') \<in> state_wl_l None \<and> correct_watching S}\<close>
  shows
    \<open>negate_mode_bj_nonunit_wl S \<le> \<Down>{(S, S''). (S, S'') \<in> state_wl_l None \<and> correct_watching S}
       (negate_mode_bj_nonunit_l S')\<close>
proof -
  have fresh: \<open>get_fresh_index_wl (get_clauses_wl T) (get_unit_clauses_wl T) (get_watched_wl T)
    \<le> \<Down> {(i, j). i = j \<and> i \<notin># dom_m (get_clauses_wl T) \<and> i > 0 \<and>
       (\<forall>L \<in># all_lits_of_mm (mset `# ran_mf (get_clauses_wl T) + get_unit_clauses_wl T) .
          i \<notin> fst ` set (watched_by T L))}
        (get_fresh_index (get_clauses_l T'))\<close>
    if \<open>(TK, TK') \<in> find_decomp_target_wl_ref S\<close> and
      \<open>TK = (T, K)\<close> and
      \<open>TK' =(T', K')\<close>
    for T T' K K' TK TK'
    using that by (auto simp: get_fresh_index_def equality_except_trail_wl_get_clauses_wl
        get_fresh_index_wl_def watched_by_alt_def
      intro!: RES_refine)
  show ?thesis
    using SS'
    unfolding negate_mode_bj_nonunit_wl_def negate_mode_bj_nonunit_l_def
    apply (refine_rcg find_decomp_target_wl_find_decomp_target_l fresh
      propagate_nonunit_and_add_wl_propagate_nonunit_and_add_l)
    subgoal
       using SS' unfolding negate_mode_bj_unit_l_inv_def negate_mode_bj_nonunit_wl_inv_def
       by blast
    subgoal
       using SS' unfolding negate_mode_bj_nonunit_l_inv_def by blast
    subgoal using SS' by (auto simp add: twl_st_wl)
    apply assumption+
    apply (auto simp add: equality_except_trail_wl_get_clauses_wl)
    done
qed

definition negate_mode_restart_nonunit_wl_inv :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
\<open>negate_mode_restart_nonunit_wl_inv S \<longleftrightarrow>
  (\<exists>S' b. (S, S') \<in> state_wl_l b \<and> negate_mode_restart_nonunit_l_inv S' \<and> correct_watching S)\<close>

definition restart_nonunit_and_add_wl_inv where
  \<open>restart_nonunit_and_add_wl_inv C i S \<longleftrightarrow>
     length C \<ge> 2 \<and> correct_watching S \<and>
      atms_of (mset C) \<subseteq> atms_of_mm (clause `# twl_clause_of `# ran_mf (get_clauses_wl S) +
          get_unit_init_clss_wl S)\<close>

fun restart_nonunit_and_add_wl :: \<open>'v clause_l \<Rightarrow> nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>restart_nonunit_and_add_wl C i (M, N, D, NE, UE, Q, W) = do {
      ASSERT(restart_nonunit_and_add_wl_inv C i (M, N, D, NE, UE, Q, W));
     let b = (length C = 2);
      let W = W(C!0 := W (C!0) @ [(i, C!1, b)]);
      let W = W(C!1 := W (C!1) @ [(i, C!0, b)]);
      RETURN (M, fmupd i (C, True) N, None, NE, UE, {#}, W)
  }\<close>

definition negate_mode_restart_nonunit_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
\<open>negate_mode_restart_nonunit_wl = (\<lambda>S. do {
    ASSERT(negate_mode_restart_nonunit_wl_inv S);
    let C = DECO_clause_l (get_trail_wl S);
    i \<leftarrow> SPEC(\<lambda>i. i < count_decided (get_trail_wl S));
    (S, K) \<leftarrow> find_decomp_target_wl i S;
    i \<leftarrow> get_fresh_index_wl (get_clauses_wl S) (get_unit_clauses_wl S) (get_watched_wl S);
    restart_nonunit_and_add_wl C i S
  })\<close>


definition negate_mode_wl_inv where
  \<open>negate_mode_wl_inv S \<longleftrightarrow>
     (\<exists>S' b. (S, S') \<in> state_wl_l b \<and> negate_mode_l_inv S' \<and> correct_watching S)\<close>

definition negate_mode_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>negate_mode_wl S = do {
    ASSERT(negate_mode_wl_inv S);
    if count_decided (get_trail_wl S) = 1
    then negate_mode_bj_unit_wl S
    else do {
      b \<leftarrow> SPEC(\<lambda>_. True);
      if b then negate_mode_bj_nonunit_wl S else negate_mode_restart_nonunit_wl S
    }
  }\<close>

lemma correct_watching_learn_no_propa:
  assumes
    L1: \<open>atm_of L1 \<in> atms_of_mm (mset `# ran_mf N + NE)\<close> and
    L2: \<open>atm_of L2 \<in> atms_of_mm (mset `# ran_mf N + NE)\<close> and
    UW: \<open>atms_of (mset UW) \<subseteq> atms_of_mm (mset `# ran_mf N + NE)\<close> and
    \<open>L1 \<noteq> L2\<close> and
    i_dom: \<open>i \<notin># dom_m N\<close> and
    \<open>\<And>L. L \<in># all_lits_of_mm (mset `# ran_mf N + (NE + UE)) \<Longrightarrow> i \<notin> fst ` set (W L)\<close> and
    \<open>b \<longleftrightarrow>  length (L1 # L2 # UW) = 2\<close>
  shows
  \<open>correct_watching (M, fmupd i (L1 # L2 # UW, b') N,
    D, NE, UE, Q, W (L1 := W L1 @ [(i, L2, b)], L2 := W L2 @ [(i, L1, b)])) \<longleftrightarrow>
  correct_watching (M, N, D, NE, UE, Q, W)\<close>
  apply (subst correct_watching_learn[OF assms(1-3, 5-6), symmetric])
  unfolding correct_watching.simps clause_to_update_def
  by (auto simp: assms)

lemma restart_nonunit_and_add_wl_restart_nonunit_and_add_l:
  assumes
    SS': \<open>(S, S') \<in> {(S, S'). (S, S') \<in> state_wl_l None \<and> correct_watching S}\<close> and
    l_inv: \<open>negate_mode_restart_nonunit_l_inv S'\<close> and
    inv: \<open>negate_mode_restart_nonunit_wl_inv S\<close> and
    \<open>(m, n) \<in> nat_rel\<close> and
    \<open>m \<in> {i. i < count_decided (get_trail_wl S)}\<close> and
    \<open>n \<in> {i. i < count_decided (get_trail_l S')}\<close> and
    TK: \<open>(TK, TK') \<in> find_decomp_target_wl_ref S\<close> and
    [simp]: \<open>TK' = (T, K)\<close> and
    [simp]: \<open>TK = (T', K')\<close> and
    ij: \<open>(i, j) \<in> {(i, j). i = j \<and> i \<notin># dom_m (get_clauses_wl T') \<and> i > 0 \<and>
       (\<forall>L \<in># all_lits_of_mm (mset `# ran_mf (get_clauses_wl T') + get_unit_clauses_wl T') .
          i \<notin> fst ` set (watched_by T' L))}\<close>
  shows \<open>restart_nonunit_and_add_wl (DECO_clause_l (get_trail_wl S)) i T'
         \<le> SPEC (\<lambda>c. (c, restart_nonunit_and_add_l
                          (DECO_clause_l (get_trail_l S')) j T)
                     \<in> {(S, S'').
                        (S, S'') \<in> state_wl_l None \<and> correct_watching S})\<close>
proof -
  have [simp]: \<open>i = j\<close>
    using ij by auto
  have le: \<open>length (DECO_clause_l (get_trail_wl S)) > 1\<close>
    using SS' l_inv unfolding negate_mode_restart_nonunit_l_inv_def by auto
  then have 1: \<open>DECO_clause_l (get_trail_wl S) =
        DECO_clause_l (get_trail_wl S) ! 0 #
           DECO_clause_l (get_trail_wl S) ! Suc 0 # drop 2 (DECO_clause_l (get_trail_wl S))\<close>
    by (cases \<open>DECO_clause_l (get_trail_wl S)\<close>; cases \<open>tl (DECO_clause_l (get_trail_wl S))\<close>)
      auto
  obtain T U b b' where
      ST: \<open>(S, T) \<in> state_wl_l b\<close> and
      \<open>no_dup (trail (state\<^sub>W_of U))\<close> and
      TU: \<open>(T, U) \<in> twl_st_l b'\<close>
    using inv unfolding negate_mode_restart_nonunit_wl_inv_def negate_mode_restart_nonunit_l_inv_def
    unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by fast
  then have neq: False if \<open>DECO_clause_l (get_trail_wl S) ! 0 = DECO_clause_l (get_trail_wl S) ! Suc 0\<close>
    using that
    apply (subst (asm) nth_eq_iff_index_eq)
    using le ST TU by (auto simp: twl_st twl_st_l twl_st_wl distinct_DECO_clause_l)

  show ?thesis
    apply (simp only:  twl_st_wl_splitD[of \<open>restart_nonunit_and_add_wl _ _\<close>,
        OF restart_nonunit_and_add_wl.simps]
       twl_st_l_splitD[of \<open>restart_nonunit_and_add_l _ _\<close>,
        OF restart_nonunit_and_add_l.simps] Let_def
       assert_bind_spec_conv)
    apply (intro conjI)
    subgoal
      using TK SS' l_inv unfolding negate_mode_restart_nonunit_l_inv_def
         restart_nonunit_and_add_wl_inv_def
      by (cases T') auto
    subgoal
      unfolding RETURN_def less_eq_nres.simps mem_Collect_eq prod.simps singleton_iff
      apply (subst subset_iff)
      unfolding RETURN_def less_eq_nres.simps mem_Collect_eq prod.simps singleton_iff
      apply (intro conjI impI allI)
      subgoal using TK SS' by (auto simp: state_wl_l_def)
      subgoal
        apply (simp only: )
        apply (subst 1)
        apply (subst One_nat_def[symmetric])+
        apply (subst fun_upd_other)
        subgoal
          using SS' length_DECO_clause_l[of \<open>get_trail_wl S\<close>] le TK
          by (cases \<open>DECO_clause_l (get_trail_wl S)\<close>; cases \<open>tl (DECO_clause_l (get_trail_wl S))\<close>)
            (auto simp: DECO_clause_l_DECO_clause[symmetric] twl_st_l twl_st
            simp del: DECO_clause_l_DECO_clause)
        apply (rule correct_watching_learn_no_propa[THEN iffD2])
        apply (rule atms_of_subset_in_atms_ofI[of \<open>DECO_clause (get_trail_wl S)\<close>])
        subgoal using TK by (solves \<open>auto simp add: mset_take_mset_drop_mset'\<close>)
        subgoal using TK le by (solves \<open>auto simp add: mset_take_mset_drop_mset'
          DECO_clause_l_DECO_clause[symmetric]
           simp del: DECO_clause_l_DECO_clause\<close>)
        subgoal apply (use TK le in \<open>auto simp add: mset_take_mset_drop_mset' DECO_clause_l_DECO_clause[symmetric]
           simp del: DECO_clause_l_DECO_clause\<close>)
           apply (smt "1" UnE add_mset_add_single image_eqI mset.simps(2) set_mset_mset subsetCE
              union_iff union_single_eq_member)
           done
        subgoal \<comment> \<open>TODO Proof\<close>
          using TK le apply (auto simp: mset_take_mset_drop_mset' in_DECO_clause_l_in_DECO_clause_iff
           dest!: in_set_dropD)
           by (metis UnE atms_of_ms_union atms_of_subset_in_atms_ofI)
        subgoal using SS' TK neq by (auto simp add: equality_except_trail_wl_get_clauses_wl)
        subgoal using inv TK SS' ij unfolding negate_mode_restart_nonunit_wl_inv_def
          by (cases S; cases T; cases T')
           (auto simp: state_wl_l_def correct_watching.simps
             clause_to_update_def)
        subgoal using inv TK SS' ij unfolding negate_mode_restart_nonunit_wl_inv_def
          by (cases S; cases T; cases T')
            (auto simp: state_wl_l_def correct_watching.simps
             clause_to_update_def)
        subgoal by (subst 1) auto
        subgoal using inv TK SS' unfolding negate_mode_restart_nonunit_wl_inv_def
          by (cases S; cases T; cases T')
            (auto simp: state_wl_l_def correct_watching.simps
             clause_to_update_def)
        done
      done
    done
qed

lemma negate_mode_restart_nonunit_wl_negate_mode_restart_nonunit_l:
  fixes S :: \<open>'v twl_st_wl\<close> and S' :: \<open>'v twl_st_l\<close>
  assumes
    SS': \<open>(S, S') \<in> {(S, S''). (S, S'') \<in> state_wl_l None \<and> correct_watching S}\<close>
  shows
    \<open>negate_mode_restart_nonunit_wl S \<le>
      \<Down> {(S, S''). (S, S'') \<in> state_wl_l None \<and> correct_watching S}
       (negate_mode_restart_nonunit_l S')\<close>
proof -
  have fresh: \<open>get_fresh_index_wl (get_clauses_wl T) (get_unit_clauses_wl T) (get_watched_wl T)
    \<le> \<Down> {(i, j). i = j \<and> i \<notin># dom_m (get_clauses_wl T) \<and> i > 0 \<and>
       (\<forall>L \<in># all_lits_of_mm (mset `# ran_mf (get_clauses_wl T) + get_unit_clauses_wl T) .
          i \<notin> fst ` set (watched_by T L))}
        (get_fresh_index (get_clauses_l T'))\<close>
    if \<open>(TK, TK') \<in> find_decomp_target_wl_ref S\<close> and
      \<open>TK = (T, K)\<close> and
      \<open>TK' =(T', K')\<close>
    for T T' K K' TK TK'
    using that by (auto simp: get_fresh_index_def equality_except_trail_wl_get_clauses_wl
        get_fresh_index_wl_def watched_by_alt_def
      intro!: RES_refine)
  show ?thesis
    unfolding negate_mode_restart_nonunit_wl_def negate_mode_restart_nonunit_l_def
    apply (refine_rcg find_decomp_target_wl_find_decomp_target_l fresh
      restart_nonunit_and_add_wl_restart_nonunit_and_add_l)
    subgoal using SS' unfolding negate_mode_restart_nonunit_wl_inv_def by blast
    subgoal using SS' by auto
    subgoal using SS' by simp
    subgoal unfolding negate_mode_restart_nonunit_l_inv_def by blast
    subgoal using SS' by fast
    apply assumption+
    apply (rule SS')
    apply assumption+
    done
qed

lemma negate_mode_wl_negate_mode_l:
  fixes S :: \<open>'v twl_st_wl\<close> and S' :: \<open>'v twl_st_l\<close>
  assumes
    SS': \<open>(S, S') \<in> {(S, S''). (S, S'') \<in> state_wl_l None \<and> correct_watching S}\<close> and
    confl: \<open>get_conflict_wl S = None\<close>
  shows
    \<open>negate_mode_wl S \<le>
      \<Down> {(S, S''). (S, S'') \<in> state_wl_l None \<and> correct_watching S}
       (negate_mode_l S')\<close>
proof -
  show ?thesis
    using SS'
    unfolding negate_mode_wl_def negate_mode_l_def
    apply (refine_vcg negate_mode_bj_nonunit_wl_negate_mode_bj_nonunit_l
      negate_mode_bj_unit_wl_negate_mode_bj_unit_l
      negate_mode_restart_nonunit_wl_negate_mode_restart_nonunit_l)
    subgoal unfolding negate_mode_wl_inv_def by blast
    subgoal by auto
    subgoal by auto
    done
qed

context
  fixes P :: \<open>'v literal set \<Rightarrow> bool\<close>
begin

definition cdcl_twl_enum_inv_wl :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
  \<open>cdcl_twl_enum_inv_wl S \<longleftrightarrow>
    (\<exists>S'. (S, S') \<in> state_wl_l None \<and> cdcl_twl_enum_inv_l S') \<and>
       correct_watching S\<close>

definition cdcl_twl_enum_wl :: \<open>'v twl_st_wl \<Rightarrow> bool nres\<close> where
  \<open>cdcl_twl_enum_wl S = do {
     S \<leftarrow> cdcl_twl_stgy_prog_wl S;
     S \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_enum_inv_wl\<^esup>
       (\<lambda>S. get_conflict_wl S = None \<and> count_decided(get_trail_wl S) > 0 \<and>
            \<not>P (lits_of_l (get_trail_wl S)))
       (\<lambda>S. do {
             S \<leftarrow> negate_mode_wl S;
             cdcl_twl_stgy_prog_wl S
           })
       S;
     if get_conflict_wl S = None
     then RETURN (if count_decided(get_trail_wl S) = 0 then P (lits_of_l (get_trail_wl S)) else True)
     else RETURN (False)
    }\<close>

lemma cdcl_twl_enum_wl_cdcl_twl_enum_l:
  assumes
    SS': \<open>(S, S') \<in> state_wl_l None\<close> and
    corr: \<open>correct_watching S\<close>
  shows
    \<open>cdcl_twl_enum_wl S \<le> \<Down> bool_rel
       (cdcl_twl_enum_l P S')\<close>
  unfolding cdcl_twl_enum_wl_def cdcl_twl_enum_l_def
  apply (refine_vcg cdcl_twl_stgy_prog_wl_spec'[unfolded fref_param1, THEN fref_to_Down]
    negate_mode_wl_negate_mode_l)
  subgoal by fast
  subgoal using SS' corr by auto
  subgoal using corr unfolding cdcl_twl_enum_inv_wl_def by blast
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  done

end

end