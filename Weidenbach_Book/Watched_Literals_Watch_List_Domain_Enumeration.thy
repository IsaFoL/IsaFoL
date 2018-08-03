theory Watched_Literals_Watch_List_Domain_Enumeration
  imports Watched_Literals_Watch_List_Enumeration Watched_Literals.Watched_Literals_Watch_List_Domain
begin

context isasat_input_ops
begin

fun propagate_unit_and_add_wl_D
  :: \<open>nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close>
where
  \<open>propagate_unit_and_add_wl_D K (M, N, D, NE, UE, Q, W) = do {
      ASSERT(-K \<in># \<L>\<^sub>a\<^sub>l\<^sub>l);
      RETURN (Propagated (-K) 0 # M, N, None, add_mset {#-K#} NE, UE, {#K#}, W)
    }\<close>

definition negate_mode_bj_unit_wl_D
  :: \<open>nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close>
where
\<open>negate_mode_bj_unit_wl_D = (\<lambda>S. do {
    (S, K) \<leftarrow> find_decomp_target_wl 1 S;
    ASSERT(K \<in># \<L>\<^sub>a\<^sub>l\<^sub>l);
    propagate_unit_and_add_wl_D K S
  })\<close>

abbreviation find_decomp_target_wl_D_ref
  :: \<open>nat twl_st_wl \<Rightarrow> ((nat twl_st_wl \<times> nat literal) \<times> (nat twl_st_wl \<times> nat literal)) set\<close> where
  \<open>find_decomp_target_wl_D_ref S \<equiv>
     {((T, K), (T', K')). (T, T') \<in> Id \<and> (K, K') \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n T \<and>
        equality_except_trail_wl T S}\<close>

lemma find_decomp_target_wl_D_find_decomp_target_wl:
  fixes S S' :: \<open>nat twl_st_wl\<close>
  assumes
    SS': \<open>(S, S') \<in> {(S, S''). (S, S'') \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S}\<close> and \<open>(a, a') \<in> Id\<close>
  shows
    \<open>find_decomp_target_wl a S \<le> \<Down>(find_decomp_target_wl_D_ref S) (find_decomp_target_wl a' S')\<close>
  using assms unfolding find_decomp_target_wl_def
  by (cases S') (auto intro!: RES_refine simp: literals_are_\<L>\<^sub>i\<^sub>n_def blits_in_\<L>\<^sub>i\<^sub>n_def)

lemma is_\<L>\<^sub>a\<^sub>l\<^sub>l_add_mset_already_in:
  \<open>x \<in># N \<Longrightarrow> is_\<L>\<^sub>a\<^sub>l\<^sub>l (add_mset x N) \<longleftrightarrow>  is_\<L>\<^sub>a\<^sub>l\<^sub>l N\<close>
  using is_\<L>\<^sub>a\<^sub>l\<^sub>l_def by auto

lemma negate_mode_bj_unit_wl_D_negate_mode_bj_unit_wl:
  fixes S S' :: \<open>nat twl_st_wl\<close>
  assumes
    SS': \<open>(S, S') \<in> {(S, S''). (S, S'') \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S}\<close>
  shows
    \<open>negate_mode_bj_unit_wl_D S \<le> \<Down> {(S, S''). (S, S'') \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S}
       (negate_mode_bj_unit_wl S')\<close>
  unfolding negate_mode_bj_unit_wl_D_def negate_mode_bj_unit_wl_def
  using assms
  apply (refine_vcg find_decomp_target_wl_D_find_decomp_target_wl)
  apply (auto simp: mset_take_mset_drop_mset' uminus_\<A>\<^sub>i\<^sub>n_iff all_lits_of_mm_add_mset
     all_lits_of_m_add_mset in_all_lits_of_mm_uminus_iff literals_are_\<L>\<^sub>i\<^sub>n_def blits_in_\<L>\<^sub>i\<^sub>n_def
      intro!: is_\<L>\<^sub>a\<^sub>l\<^sub>l_add_mset_already_in[THEN iffD2] dest:(* in_all_lits_of_mm_uminusD *))
  using is_\<L>\<^sub>a\<^sub>l\<^sub>l_def by blast

definition negate_mode_bj_nonunit_wl_D_inv:: \<open>nat twl_st_wl \<Rightarrow> bool\<close> where
\<open>negate_mode_bj_nonunit_wl_D_inv S \<longleftrightarrow>
   (negate_mode_bj_nonunit_wl_inv S \<and> literals_are_\<L>\<^sub>i\<^sub>n S)\<close>

definition negate_mode_bj_nonunit_wl_D
  :: \<open>nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close> where
\<open>negate_mode_bj_nonunit_wl_D = (\<lambda>S. do {
    ASSERT(negate_mode_bj_nonunit_wl_D_inv S);
    let C = DECO_clause_l (get_trail_wl S);
    (S, K) \<leftarrow> find_decomp_target_wl (count_decided (get_trail_wl S)) S;
    i \<leftarrow> get_fresh_index_wl (get_clauses_wl S) (get_unit_clauses_wl S) (get_watched_wl S);
    propagate_nonunit_and_add_wl K C i S
  })\<close>

lemma is_\<L>\<^sub>a\<^sub>l\<^sub>l_add_all_lits_of_m:
  \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l (all_lits_of_mm B) \<Longrightarrow> atms_of A \<subseteq> atms_of_mm B \<Longrightarrow> is_\<L>\<^sub>a\<^sub>l\<^sub>l (all_lits_of_m A + all_lits_of_mm B)\<close>
  unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_def
  by (auto simp: in_all_lits_of_m_ain_atms_of_iff in_all_lits_of_mm_ain_atms_of_iff)

lemma literals_are_\<L>\<^sub>i\<^sub>n_propagate_nonunit_and_add_wl:
  assumes
    lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n T'\<close> and
    le: \<open>2 \<le> count_decided (get_trail_wl S')\<close> and
    i': \<open>i' \<notin># dom_m (get_clauses_wl T')\<close> and
    atms: \<open>atms_of (DECO_clause (get_trail_wl S'))
     \<subseteq> atms_of_ms ((\<lambda>x. mset (fst x)) ` set_mset (ran_m (get_clauses_wl T'))) \<union>
        atms_of_mm (get_unit_init_clss_wl T')\<close>
  shows \<open>literals_are_\<L>\<^sub>i\<^sub>n
          (M',
           fmupd i' (DECO_clause_l (get_trail_wl S'), b) (get_clauses_wl T'), None,
           get_unit_init_clss_wl T', get_unit_learned_clss_wl T', Q, (get_watched_wl T')
           (DECO_clause_l (get_trail_wl S') ! 0 :=
              get_watched_wl T' (DECO_clause_l (get_trail_wl S') ! 0) @
              [(i', DECO_clause_l (get_trail_wl S') ! Suc 0)],
          DECO_clause_l (get_trail_wl S') ! Suc 0 :=
            get_watched_wl T' (DECO_clause_l (get_trail_wl S') ! Suc 0) @
            [(i', DECO_clause_l (get_trail_wl S') ! 0)]))\<close>
  (is \<open>literals_are_\<L>\<^sub>i\<^sub>n ?S\<close>) and
  \<open>DECO_clause_l (get_trail_wl S') ! 0 = DECO_clause_l (get_trail_wl S') ! Suc 0 \<Longrightarrow>
    literals_are_\<L>\<^sub>i\<^sub>n
     (M',
      fmupd i' (DECO_clause_l (get_trail_wl S'), True) (get_clauses_wl T'), None, get_unit_init_clss_wl T',
      get_unit_learned_clss_wl T', Q, (get_watched_wl T')
      (DECO_clause_l (get_trail_wl S') ! 0 :=
         get_watched_wl T' (DECO_clause_l (get_trail_wl S') ! 0) @
         [(i', DECO_clause_l (get_trail_wl S') ! 0), (i', DECO_clause_l (get_trail_wl S') ! 0)]))\<close>
  (is \<open>?eq \<Longrightarrow> literals_are_\<L>\<^sub>i\<^sub>n ?S'\<close>)
proof -
  have lall: \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l (all_lits_of_mm ((\<lambda>C. mset (fst C)) `# ran_m (get_clauses_wl T')
        + get_unit_clauses_wl T'))\<close> and
    blits: \<open>blits_in_\<L>\<^sub>i\<^sub>n T'\<close>
    using lits unfolding literals_are_\<L>\<^sub>i\<^sub>n_def
    by fast+
  have \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l (all_lits_of_mm ((\<lambda>C. mset (fst C)) `# ran_m (get_clauses_wl ?S)
        + get_unit_clauses_wl ?S))\<close>
    using i' atms
    by (auto simp: ran_m_mapsto_upd_notin all_lits_of_mm_add_mset
        intro!: is_\<L>\<^sub>a\<^sub>l\<^sub>l_add_all_lits_of_m[unfolded get_unit_clauses_wl_alt_def]
        lall[unfolded get_unit_clauses_wl_alt_def])
  moreover have blits: \<open>blits_in_\<L>\<^sub>i\<^sub>n ?S\<close>
    using blits i' atms le lall unfolding length_DECO_clause_l[symmetric] is_\<L>\<^sub>a\<^sub>l\<^sub>l_def
    by (cases \<open>DECO_clause_l (get_trail_wl S')\<close>; cases \<open>tl (DECO_clause_l (get_trail_wl S'))\<close>)
      (auto simp: ran_m_mapsto_upd_notin all_lits_of_mm_add_mset blits_in_\<L>\<^sub>i\<^sub>n_def
        in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n DECO_clause_l_DECO_clause[symmetric] Ball_def
        in_all_lits_of_mm_ain_atms_of_iff all_conj_distrib
        watched_by_alt_def get_unit_clauses_wl_alt_def
        simp del: DECO_clause_l_DECO_clause)
  ultimately show \<open>literals_are_\<L>\<^sub>i\<^sub>n ?S\<close>
    unfolding literals_are_\<L>\<^sub>i\<^sub>n_def by blast


  have \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l (all_lits_of_mm ((\<lambda>C. mset (fst C)) `# ran_m (get_clauses_wl ?S')
        + get_unit_clauses_wl ?S'))\<close>
    using i' atms
    by (auto simp: ran_m_mapsto_upd_notin all_lits_of_mm_add_mset
        intro!: is_\<L>\<^sub>a\<^sub>l\<^sub>l_add_all_lits_of_m[unfolded get_unit_clauses_wl_alt_def]
        lall[unfolded get_unit_clauses_wl_alt_def])
  moreover have blits: \<open>?eq \<Longrightarrow> blits_in_\<L>\<^sub>i\<^sub>n ?S'\<close>
    using blits i' atms le lall unfolding length_DECO_clause_l[symmetric] is_\<L>\<^sub>a\<^sub>l\<^sub>l_def
    by (cases \<open>DECO_clause_l (get_trail_wl S')\<close>)
      (auto simp: ran_m_mapsto_upd_notin all_lits_of_mm_add_mset blits_in_\<L>\<^sub>i\<^sub>n_def
        in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n DECO_clause_l_DECO_clause[symmetric] Ball_def
        in_all_lits_of_mm_ain_atms_of_iff all_conj_distrib
        watched_by_alt_def get_unit_clauses_wl_alt_def
        simp del: DECO_clause_l_DECO_clause)
  ultimately show \<open>?eq \<Longrightarrow> literals_are_\<L>\<^sub>i\<^sub>n ?S'\<close>
    unfolding literals_are_\<L>\<^sub>i\<^sub>n_def by blast
qed


lemma propagate_nonunit_and_add_wl_propagate_nonunit_and_add_wl:
  assumes
    TK: \<open>(TK, TK') \<in> {((S, K), (S'', K'')). (K, K'') \<in> Id \<and> (S, S'') \<in> Id
      \<and> literals_are_\<L>\<^sub>i\<^sub>n S}\<close> and
    [simp]: \<open>TK = (T, K)\<close> and
    [simp]: \<open>TK' = (T', K')\<close> and
    \<open>(i, i') \<in> Id\<close> and
    \<open>literals_are_\<L>\<^sub>i\<^sub>n T\<close> and
    \<open>(S, S') \<in> {(S, S''). (S, S'') \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S}\<close>
  shows \<open>propagate_nonunit_and_add_wl K (DECO_clause_l (get_trail_wl S)) i T
         \<le> \<Down> {(S, S''). (S, S'') \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S}
             (propagate_nonunit_and_add_wl K' (DECO_clause_l (get_trail_wl S')) i' T')\<close>
  using assms unfolding propagate_nonunit_and_add_wl_def
  by refine_vcg
    (auto simp: ran_m_mapsto_upd_notin all_lits_of_mm_add_mset
    propagate_nonunit_and_add_wl_pre_def mset_take_mset_drop_mset'
    get_unit_clauses_wl_alt_def
    intro!: is_\<L>\<^sub>a\<^sub>l\<^sub>l_add_all_lits_of_m
   intro!: literals_are_\<L>\<^sub>i\<^sub>n_propagate_nonunit_and_add_wl)

lemma negate_mode_bj_nonunit_wl_D_negate_mode_bj_nonunit_wl:
  fixes S S' :: \<open>nat twl_st_wl\<close>
  assumes
    SS': \<open>(S, S') \<in> {(S, S''). (S, S'') \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S}\<close>
     (is \<open>_ \<in> ?input\<close>)
  shows
    \<open>negate_mode_bj_nonunit_wl_D S \<le> \<Down>{(S, S''). (S, S'') \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S}
       (negate_mode_bj_nonunit_wl S')\<close>
proof -
  have find_deomp: \<open>find_decomp_target_wl (count_decided (get_trail_wl S)) S
    \<le> \<Down> {((S, K), (S'', K'')). (K, K'') \<in> Id \<and> (S, S'') \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S}
      (find_decomp_target_wl (count_decided (get_trail_wl S')) S')\<close>
      (is \<open>_ \<le> \<Down> ?find_d _\<close>)
    using SS' unfolding find_decomp_target_wl_def
    by (cases S') (auto simp: literals_are_\<L>\<^sub>i\<^sub>n_def blits_in_\<L>\<^sub>i\<^sub>n_def intro!: RES_refine)
  have fresh: \<open>get_fresh_index_wl (get_clauses_wl T) (get_unit_clauses_wl T) (get_watched_wl T)
    \<le> \<Down> {(i, j). i = j \<and> i \<notin># dom_m (get_clauses_wl T) \<and> i > 0 \<and>
       (\<forall>L \<in># all_lits_of_mm (mset `# ran_mf (get_clauses_wl T) + get_unit_clauses_wl T) .
          i \<notin> fst ` set (watched_by T L))}
        (get_fresh_index_wl (get_clauses_wl T') (get_unit_clauses_wl T') (get_watched_wl T'))\<close>
    if \<open>(TK, TK') \<in> ?find_d\<close> and
      \<open>TK = (T, K)\<close> and
      \<open>TK' =(T', K')\<close>
    for T T' K K' TK TK'
    using that by (auto simp: get_fresh_index_def equality_except_trail_wl_get_clauses_wl
        get_fresh_index_wl_def watched_by_alt_def
      intro!: RES_refine)
  show ?thesis
    unfolding negate_mode_bj_nonunit_wl_D_def negate_mode_bj_nonunit_wl_def
    apply (refine_vcg propagate_nonunit_and_add_wl_propagate_nonunit_and_add_wl fresh find_deomp)
    subgoal using SS' unfolding negate_mode_bj_nonunit_wl_D_inv_def by blast
    apply assumption+
    subgoal by auto
    subgoal by auto
    subgoal using assms by fast
    done
qed

definition negate_mode_restart_nonunit_wl_D_inv
 :: \<open>nat twl_st_wl \<Rightarrow> bool\<close>
where
  \<open>negate_mode_restart_nonunit_wl_D_inv S \<longleftrightarrow>
    (negate_mode_restart_nonunit_wl_inv S \<and>  literals_are_\<L>\<^sub>i\<^sub>n S)\<close>

definition restart_nonunit_and_add_wl_D_inv
  :: \<open>nat clause_l \<Rightarrow> nat \<Rightarrow> nat twl_st_wl \<Rightarrow> bool\<close>where
  \<open>restart_nonunit_and_add_wl_D_inv C i S \<longleftrightarrow>
     restart_nonunit_and_add_wl_inv C i S \<and> literals_are_\<L>\<^sub>i\<^sub>n S\<close>

fun restart_nonunit_and_add_wl_D
  :: \<open>nat clause_l \<Rightarrow> nat \<Rightarrow> nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close>
where
  \<open>restart_nonunit_and_add_wl_D C i (M, N, D, NE, UE, Q, W) = do {
      ASSERT(restart_nonunit_and_add_wl_D_inv C i (M, N, D, NE, UE, Q, W));
      let W = W(C!0 := W (C!0) @ [(i, C!1)]);
      let W = W(C!1 := W (C!1) @ [(i, C!0)]);
      RETURN (M, fmupd i (C, True) N, None, NE, UE, {#}, W)
  }\<close>

definition negate_mode_restart_nonunit_wl_D
  :: \<open>nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close>
where
  \<open>negate_mode_restart_nonunit_wl_D = (\<lambda>S. do {
    ASSERT(negate_mode_restart_nonunit_wl_D_inv S);
    let C = DECO_clause_l (get_trail_wl S);
    i \<leftarrow> SPEC(\<lambda>i. i < count_decided (get_trail_wl S));
    (S, K) \<leftarrow> find_decomp_target_wl i S;
    i \<leftarrow> get_fresh_index_wl (get_clauses_wl S) (get_unit_clauses_wl S) (get_watched_wl S);
    restart_nonunit_and_add_wl_D C i S
  })\<close>


definition negate_mode_wl_D_inv :: \<open>nat twl_st_wl \<Rightarrow> bool\<close> where
  \<open>negate_mode_wl_D_inv S \<longleftrightarrow>
  (negate_mode_wl_inv S \<and> literals_are_\<L>\<^sub>i\<^sub>n S)\<close>

definition negate_mode_wl_D :: \<open>nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close> where
  \<open>negate_mode_wl_D S = do {
    ASSERT(negate_mode_wl_D_inv S);
    if count_decided (get_trail_wl S) = 1
    then negate_mode_bj_unit_wl_D S
    else do {
      b \<leftarrow> SPEC(\<lambda>_. True);
      if b then negate_mode_bj_nonunit_wl_D S else negate_mode_restart_nonunit_wl_D S
    }
  }\<close>


lemma restart_nonunit_and_add_wl_D_restart_nonunit_and_add_wl:
  assumes
    SS': \<open>(S, S') \<in> {(S, S''). (S, S'') \<in> Id \<and>  literals_are_\<L>\<^sub>i\<^sub>n S}\<close> and
    inv: \<open>negate_mode_restart_nonunit_wl_inv S\<close> and
    \<open>(m, n) \<in> nat_rel\<close> and
    \<open>m \<in> {i. i < count_decided (get_trail_wl S)}\<close> and
    \<open>n \<in> {i. i < count_decided (get_trail_wl S')}\<close> and
    TK: \<open>(TK, TK') \<in> find_decomp_target_wl_D_ref S\<close> and
    [simp]: \<open>TK = (T, K)\<close> and
    [simp]: \<open>TK' = (T', K')\<close> and
    ij: \<open>(i, i') \<in> {(i, j). i = j \<and> i \<notin># dom_m (get_clauses_wl S)}\<close>
  shows \<open>restart_nonunit_and_add_wl_D (DECO_clause_l (get_trail_wl S)) i T
         \<le> \<Down>{(S, S''). (S, S'') \<in> Id \<and>  literals_are_\<L>\<^sub>i\<^sub>n S}
            (restart_nonunit_and_add_wl (DECO_clause_l (get_trail_wl S')) i' T')\<close>
proof -
  have [simp]: \<open>i = i'\<close> and j: \<open>i' \<notin># dom_m (get_clauses_wl S)\<close>
    using ij by auto
  show ?thesis
    apply (cases T; cases T')
    apply (simp only: restart_nonunit_and_add_wl_D.simps
      restart_nonunit_and_add_wl.simps)
    apply refine_vcg
    subgoal using TK SS' ij unfolding restart_nonunit_and_add_wl_D_inv_def
      by auto
    subgoal using TK SS' j literals_are_\<L>\<^sub>i\<^sub>n_propagate_nonunit_and_add_wl[of T S' i]
      unfolding restart_nonunit_and_add_wl_inv_def
      by (auto simp: ran_m_mapsto_upd_notin all_lits_of_mm_add_mset
       restart_nonunit_and_add_wl_D_inv_def mset_take_mset_drop_mset'
        restart_nonunit_and_add_wl_inv_def
        equality_except_trail_wl_get_clauses_wl[symmetric]
        intro!: is_\<L>\<^sub>a\<^sub>l\<^sub>l_add_all_lits_of_m )
    done
qed

lemma negate_mode_restart_nonunit_wl_D_negate_mode_restart_nonunit_wl:
  fixes S S' :: \<open>nat twl_st_wl\<close>
  assumes
    SS': \<open>(S, S') \<in> {(S, S''). (S, S'') \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S}\<close>
  shows
    \<open>negate_mode_restart_nonunit_wl_D S \<le>
      \<Down> {(S, S''). (S, S'') \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S}
       (negate_mode_restart_nonunit_wl S')\<close>
proof -
  have fresh: \<open>get_fresh_index_wl (get_clauses_wl T) (get_unit_clauses_wl T) (get_watched_wl T)
    \<le> \<Down> {(i, j). i = j \<and> i \<notin># dom_m (get_clauses_wl T) \<and> i > 0 \<and>
       (\<forall>L \<in># all_lits_of_mm (mset `# ran_mf (get_clauses_wl T) + get_unit_clauses_wl T) .
          i \<notin> fst ` set (watched_by T L))}
        (get_fresh_index_wl (get_clauses_wl T') (get_unit_clauses_wl T') (get_watched_wl T'))\<close>
    if \<open>(TK, TK') \<in> find_decomp_target_wl_D_ref S\<close> and
      \<open>TK = (T, K)\<close> and
      \<open>TK' =(T', K')\<close>
    for T T' K K' TK TK'
    using that by (auto simp: get_fresh_index_def equality_except_trail_wl_get_clauses_wl
        get_fresh_index_wl_def watched_by_alt_def
      intro!: RES_refine)
  show ?thesis
    unfolding negate_mode_restart_nonunit_wl_def negate_mode_restart_nonunit_wl_D_def
    apply (refine_rcg find_decomp_target_wl_D_find_decomp_target_wl fresh
      restart_nonunit_and_add_wl_D_restart_nonunit_and_add_wl)
    subgoal using SS' unfolding negate_mode_restart_nonunit_wl_D_inv_def by blast
    subgoal using SS' by auto
    subgoal using SS' by auto
    apply assumption+
    subgoal using SS' by auto
    subgoal using SS' by fast
    apply assumption+
    subgoal for i ia x x' x1 x2 x1a x2a ib ic
      using SS' by (cases S'; cases x1) auto
    done
qed

lemma negate_mode_wl_D_negate_mode_wl:
  fixes S S' :: \<open>nat twl_st_wl\<close>
  assumes
    SS': \<open>(S, S') \<in> {(S, S''). (S, S'') \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S}\<close> and
    confl: \<open>get_conflict_wl S = None\<close>
  shows
    \<open>negate_mode_wl_D S \<le>
      \<Down>  {(S, S''). (S, S'') \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S}
       (negate_mode_wl S')\<close>
proof -
  show ?thesis
    using SS'
    unfolding negate_mode_wl_def negate_mode_wl_D_def
    apply (refine_vcg negate_mode_bj_nonunit_wl_negate_mode_bj_nonunit_l
      negate_mode_bj_unit_wl_D_negate_mode_bj_unit_wl
      negate_mode_bj_nonunit_wl_D_negate_mode_bj_nonunit_wl
      negate_mode_restart_nonunit_wl_D_negate_mode_restart_nonunit_wl)
    subgoal unfolding negate_mode_wl_D_inv_def by blast
    subgoal by auto
    subgoal by auto
    done
qed

end \<comment> \<open>end of @{locale isasat_input_ops}\<close>

context isasat_input_bounded_nempty
begin

context
  fixes P :: \<open>nat literal set \<Rightarrow> bool\<close>
begin

definition cdcl_twl_enum_inv_wl_D :: \<open>nat twl_st_wl \<Rightarrow> bool\<close> where
  \<open>cdcl_twl_enum_inv_wl_D S \<longleftrightarrow>
    cdcl_twl_enum_inv_wl S \<and> literals_are_\<L>\<^sub>i\<^sub>n S\<close>

definition cdcl_twl_enum_wl_D :: \<open>nat twl_st_wl \<Rightarrow> bool nres\<close> where
  \<open>cdcl_twl_enum_wl_D S = do {
     S \<leftarrow> cdcl_twl_stgy_prog_wl_D S;
     S \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_enum_inv_wl_D\<^esup>
       (\<lambda>S. get_conflict_wl S = None \<and> count_decided(get_trail_wl S) > 0 \<and>
            \<not>P (lits_of_l (get_trail_wl S)))
       (\<lambda>S. do {
             S \<leftarrow> negate_mode_wl_D S;
             cdcl_twl_stgy_prog_wl_D S
           })
       S;
     if get_conflict_wl S = None
     then RETURN (if count_decided(get_trail_wl S) = 0 then P (lits_of_l (get_trail_wl S)) else True)
     else RETURN (False)
  }\<close>

lemma cdcl_twl_enum_wl_D_cdcl_twl_enum_wl:
  assumes
    SS': \<open>(S, S') \<in> {(S, S''). (S, S'') \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S}\<close>
  shows
    \<open>cdcl_twl_enum_wl_D S \<le> \<Down> bool_rel (cdcl_twl_enum_wl P S')\<close>
  unfolding cdcl_twl_enum_wl_D_def cdcl_twl_enum_wl_def
  apply (refine_vcg cdcl_twl_stgy_prog_wl_D_spec'[unfolded fref_param1, THEN fref_to_Down]
    negate_mode_wl_D_negate_mode_wl)
  subgoal by fast
  subgoal using SS' by auto
  subgoal unfolding cdcl_twl_enum_inv_wl_D_def by blast
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  done

end \<comment> \<open>end of context with \<^term>\<open>P\<close>\<close>

end  \<comment> \<open>end of @{locale isasat_input_bounded_nempty}\<close>

end
