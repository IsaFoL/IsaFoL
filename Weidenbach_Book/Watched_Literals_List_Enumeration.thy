theory Watched_Literals_List_Enumeration
  imports Watched_Literals_Algorithm_Enumeration Watched_Literals.Watched_Literals_List
begin

lemma convert_lits_l_DECO_clause[simp]:
  \<open>(S, S') \<in> convert_lits_l M N \<Longrightarrow> DECO_clause S' = DECO_clause S\<close>
  by (auto simp: DECO_clause_def uminus_lit_of_image_mset)
    (auto simp:
    mset_filter[symmetric] convert_lits_l_filter_decided mset_map[symmetric]
    simp del: mset_map)

lemma convert_lits_l_TWL_DECO_clause[simp]:
  \<open>(S, S') \<in> convert_lits_l M N \<Longrightarrow> TWL_DECO_clause S' = TWL_DECO_clause S\<close>
  by (auto simp: TWL_DECO_clause_def uminus_lit_of_image_mset)
    (auto simp: take_map[symmetric] drop_map[symmetric]
    mset_filter[symmetric] convert_lits_l_filter_decided mset_map[symmetric]
    simp del: mset_map)

lemma [twl_st_l]:
  \<open>(S, S') \<in> twl_st_l b \<Longrightarrow> DECO_clause (get_trail S') = DECO_clause (get_trail_l S)\<close>
  by (auto simp: twl_st_l_def convert_lits_l_DECO_clause)

lemma [twl_st_l]:
  \<open>(S, S') \<in> twl_st_l b \<Longrightarrow> TWL_DECO_clause (get_trail S') = TWL_DECO_clause (get_trail_l S)\<close>
  by (auto simp: twl_st_l_def convert_lits_l_DECO_clause)

lemma DECO_clause_simp[simp]:
  \<open>DECO_clause (A @ B) = DECO_clause A + DECO_clause B\<close>
  \<open>DECO_clause (Decided K # A) = add_mset (-K) (DECO_clause A)\<close>
  \<open>DECO_clause (Propagated K C # A) = DECO_clause A\<close>
  \<open>(\<And>K. K \<in> set A \<Longrightarrow> \<not>is_decided K) \<Longrightarrow> DECO_clause A = {#}\<close>
  by (auto simp: DECO_clause_def filter_mset_empty_conv)

definition find_decomp_target :: \<open>nat \<Rightarrow> 'v twl_st_l \<Rightarrow> ('v twl_st_l \<times> 'v literal) nres\<close> where
  \<open>find_decomp_target =  (\<lambda>i S.
    SPEC(\<lambda>(T, K). \<exists>M2 M1. equality_except_trail S T \<and> get_trail_l T = M1 \<and>
       (Decided K # M1, M2) \<in> set (get_all_ann_decomposition (get_trail_l S)) \<and>
          get_level (get_trail_l S) K = i))\<close>

fun propagate_unit_and_add :: \<open>'v literal \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st\<close> where
  \<open>propagate_unit_and_add K (M, N, U, D, NE, UE, WS, Q) =
      (Propagated (-K) {#-K#} # M, N, U, None, add_mset {#-K#} NE, UE, {#}, {#K#})\<close>

fun propagate_unit_and_add_l :: \<open>'v literal \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l\<close> where
  \<open>propagate_unit_and_add_l K (M, N, D, NE, UE, WS, Q) =
      (Propagated (-K) 0 # M, N, None, add_mset {#-K#} NE, UE, {#}, {#K#})\<close>

definition negate_mode_bj_unit_l_inv :: \<open>'v twl_st_l \<Rightarrow> bool\<close> where
  \<open>negate_mode_bj_unit_l_inv S \<longleftrightarrow>
     (\<exists>(S'::'v twl_st) b. (S, S') \<in> twl_st_l b \<and> twl_list_invs S \<and> twl_stgy_invs S' \<and>
        twl_struct_invs S' \<and> get_conflict_l S = None)\<close>

definition negate_mode_bj_unit_l   :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
\<open>negate_mode_bj_unit_l = (\<lambda>S. do {
    ASSERT(negate_mode_bj_unit_l_inv S);
    (S, K) \<leftarrow> find_decomp_target 1 S;
    RETURN (propagate_unit_and_add_l K S)
  })\<close>


lemma negate_mode_bj_unit_l:
  fixes S :: \<open>'v twl_st_l\<close> and S' :: \<open>'v twl_st\<close>
  assumes \<open>count_decided (get_trail_l S) = 1\<close> and
    SS': \<open>(S, S') \<in> twl_st_l b\<close> and
    struct_invs: \<open>twl_struct_invs S'\<close> and
    add_inv: \<open>twl_list_invs S\<close> and
    stgy_inv: \<open>twl_stgy_invs S'\<close> and
    confl: \<open>get_conflict_l S = None\<close>
  shows
    \<open>negate_mode_bj_unit_l S \<le> \<Down>{(S, S''). (S, S'') \<in> twl_st_l None \<and> twl_list_invs S \<and>
        clauses_to_update_l S = {#}}
       (SPEC (negate_model_and_add_twl S'))\<close>
proof -
    have H: \<open>\<exists>y\<in>Collect (negate_model_and_add_twl S').
            (propagate_unit_and_add_l x2 x1, y)
            \<in> {(S, S''). (S, S'') \<in> twl_st_l None \<and> twl_list_invs S \<and> clauses_to_update_l S = {#}}\<close>
    if
        count_dec: \<open>count_decided (get_trail_l S) = 1\<close> and
        S_S': \<open>(S, S') \<in> twl_st_l b\<close> and
        \<open>twl_struct_invs S'\<close> and
        \<open>twl_list_invs S\<close> and
        \<open>twl_stgy_invs S'\<close> and
        x_S: \<open>x \<in> {(T, K).
            \<exists>M2 M1.
                equality_except_trail S T \<and>
                get_trail_l T = M1 \<and>
                (Decided K # M1, M2)
                \<in> set (get_all_ann_decomposition (get_trail_l S)) \<and>
                get_level (get_trail_l S) K = 1}\<close> and
        x: \<open>x = (x1, x2)\<close>
    for x :: \<open>'v twl_st_l \<times> 'v literal\<close> and x1 :: \<open>'v twl_st_l\<close> and x2 :: \<open>'v literal\<close>
    proof -
      let ?y0 = \<open>(\<lambda>(M, Oth). (drop (length M - length (get_trail_l x1)) (get_trail S'), Oth)) S'\<close>
      let ?y1 = \<open>propagate_unit_and_add x2 ?y0\<close>
      obtain M1 M2 where
        S_x1: \<open>equality_except_trail S x1\<close> and
        tr_M1: \<open>get_trail_l x1 = M1\<close> and
        decomp: \<open>(Decided x2 # M1, M2) \<in> set (get_all_ann_decomposition (get_trail_l S))\<close> and
        lev_x2: \<open>get_level (get_trail_l S) x2 = 1\<close>
        using x_S unfolding x by blast
      obtain M2' where
        decomp': \<open>(Decided x2 # drop (length (get_trail S') - length M1) (get_trail S'), M2')
           \<in> set (get_all_ann_decomposition (get_trail S'))\<close> and
        conv: \<open>(get_trail_l S, get_trail S') \<in> convert_lits_l (get_clauses_l S)
          (get_unit_clauses_l S)\<close> and
        conv_M1: \<open>(M1, drop (length (get_trail S') - length M1) (get_trail S'))
             \<in> convert_lits_l (get_clauses_l S) (get_unit_clauses_l S)\<close>
        using convert_lits_l_decomp_ex[OF decomp, of \<open>get_trail S'\<close> \<open>get_clauses_l S\<close>
          \<open>get_unit_clauses_l S\<close>] S_S'
        by (auto simp: twl_st_l_def)
      have x2_DECO: \<open>{#-x2#} = DECO_clause (get_trail S')\<close>
        using decomp count_dec S_S'
        by (auto simp:  twl_st_l filter_mset_empty_conv count_decided_0_iff
            dest!: get_all_ann_decomposition_exists_prepend)
      have M1_drop: \<open>drop (length (get_trail_l S) - length M1) (get_trail_l S) = M1\<close>
        using decomp by auto
      have \<open>(propagate_unit_and_add_l x2 x1, ?y1)
        \<in> {(S, S''). (S, S'') \<in> twl_st_l None \<and> twl_list_invs S \<and>
        clauses_to_update_l S = {#}}\<close>
        using S_S' S_x1 tr_M1 decomp decomp' lev_x2 add_inv conv_M1 unfolding x
        apply (cases x1; cases S')
        by (auto simp: twl_st_l_def twl_list_invs_def convert_lit.simps split: option.splits
          intro: convert_lits_l_extend_mono)
      moreover have \<open>negate_model_and_add_twl S' ?y1\<close>
        using S_S' confl lev_x2 count_dec tr_M1 S_x1 decomp decomp' M1_drop
        unfolding x
        by (cases x1)
          (auto simp: twl_st_l_def x2_DECO simp del: convert_lits_l_DECO_clause
            intro!: negate_model_and_add_twl.bj_unit[of _ _ ]
            split: option.splits)
      ultimately show ?thesis
        apply -
        by (rule bexI[of _ ?y1]) fast+
    qed

  show ?thesis
    using assms
    unfolding negate_mode_bj_unit_l_def find_decomp_target_def
    apply (refine_rcg)
    subgoal unfolding negate_mode_bj_unit_l_inv_def by fast
    subgoal
      by (subst RETURN_RES_refine_iff) (rule H; assumption)
    done
qed


definition DECO_clause_l :: \<open>('v, 'a) ann_lits \<Rightarrow>  'v clause_l\<close> where
  \<open>DECO_clause_l M = map (uminus o lit_of) (filter is_decided M)\<close>


fun propagate_nonunit_and_add :: \<open>'v literal \<Rightarrow> 'v literal multiset twl_clause \<Rightarrow>  'v twl_st \<Rightarrow> 'v twl_st\<close> where
  \<open>propagate_nonunit_and_add K C (M, N, U, D, NE, UE, WS, Q) = do {
      (Propagated (-K) (clause C) # M, add_mset C N, U, None,
       NE, UE, {#}, {#K#})
    }\<close>

fun propagate_nonunit_and_add_l :: \<open>'v literal \<Rightarrow> 'v clause_l \<Rightarrow> nat \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l\<close> where
  \<open>propagate_nonunit_and_add_l K C i (M, N, D, NE, UE, WS, Q) = do {
      (Propagated (-K) i # M, fmupd i (C, True) N, None,
      NE, UE, {#}, {#K#})
    }\<close>

definition negate_mode_bj_nonunit_l_inv where
\<open>negate_mode_bj_nonunit_l_inv S \<longleftrightarrow>
   (\<exists>S'' b. (S, S'') \<in> twl_st_l b \<and> twl_list_invs S \<and> count_decided (get_trail_l S) > 1 \<and>
      twl_struct_invs S'' \<and>  twl_stgy_invs S'' \<and> get_conflict_l S = None)\<close>

definition negate_mode_bj_nonunit_l :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
\<open>negate_mode_bj_nonunit_l = (\<lambda>S. do {
    ASSERT(negate_mode_bj_nonunit_l_inv S);
    let C = DECO_clause_l (get_trail_l S);
    (S, K) \<leftarrow> find_decomp_target (count_decided (get_trail_l S)) S;
    i \<leftarrow> get_fresh_index (get_clauses_l S);
    RETURN (propagate_nonunit_and_add_l K C i S)
  })\<close>

lemma DECO_clause_l_DECO_clause[simp]:
 \<open>mset (DECO_clause_l M1) = DECO_clause M1\<close>
  by (induction M1) (auto simp: DECO_clause_l_def DECO_clause_def convert_lits_l_def)

lemma TWL_DECO_clause_alt_def:
  \<open>TWL_DECO_clause M1 =
    TWL_Clause (mset (watched_l (DECO_clause_l M1)))
          (mset (unwatched_l (DECO_clause_l M1)))\<close>
  unfolding TWL_DECO_clause_def convert_lits_l_def
  by (auto simp: TWL_DECO_clause_def convert_lits_l_def filter_map take_map drop_map
    DECO_clause_l_def)

lemma length_DECO_clause_l[simp]:
  \<open>length (DECO_clause_l M) = count_decided M\<close>
  unfolding DECO_clause_l_def count_decided_def by auto

lemma negate_mode_bj_nonunit_l:
  fixes S :: \<open>'v twl_st_l\<close> and S' :: \<open>'v twl_st\<close>
  assumes
    count_dec: \<open>count_decided (get_trail_l S) > 1\<close> and
    SS': \<open>(S, S') \<in> twl_st_l b\<close> and
    struct_invs: \<open>twl_struct_invs S'\<close> and
    add_inv: \<open>twl_list_invs S\<close> and
    stgy_inv: \<open>twl_stgy_invs S'\<close> and
    confl: \<open>get_conflict_l S = None\<close>
  shows
    \<open>negate_mode_bj_nonunit_l S \<le> \<Down>{(S, S''). (S, S'') \<in> twl_st_l None \<and> twl_list_invs S \<and>
        clauses_to_update_l S = {#}}
       (SPEC (negate_model_and_add_twl S'))\<close>
proof -
  have H: \<open>RETURN (propagate_nonunit_and_add_l x2 (DECO_clause_l (get_trail_l S)) i x1)
        \<le> \<Down> {(S, S''). (S, S'') \<in> twl_st_l None \<and> twl_list_invs S \<and>
        clauses_to_update_l S = {#}}
          (SPEC (negate_model_and_add_twl S'))\<close>
    if
      x_S: \<open>x \<in> {(T, K).
            \<exists>M2 M1.
              equality_except_trail S T \<and>
              get_trail_l T = M1 \<and>
              (Decided K # M1, M2) \<in> set (get_all_ann_decomposition (get_trail_l S)) \<and>
              get_level (get_trail_l S) K = count_decided (get_trail_l S)}\<close> and
      x: \<open>x = (x1, x2)\<close> and
      i: \<open>i \<in> {i. 0 < i \<and> i \<notin># dom_m (get_clauses_l x1)}\<close>
    for x :: \<open>'v twl_st_l \<times> 'v literal\<close> and
       x1 :: \<open>'v twl_st_l\<close> and x2 :: \<open>'v literal\<close> and i :: \<open>nat\<close>
  proof -
    obtain M N U D NE UE Q where
      x1: \<open>x1 = (M, N, U, D, NE, UE, Q)\<close>
      by (cases x1)

    obtain M1 M2 where
      S_x1: \<open>equality_except_trail S x1\<close> and
      tr_M1: \<open>get_trail_l x1 = M1\<close> and
      decomp: \<open>(Decided x2 # M1, M2) \<in> set (get_all_ann_decomposition (get_trail_l S))\<close> and
      lev_K: \<open>get_level (get_trail_l S) x2 = count_decided (get_trail_l S)\<close>
      using x_S unfolding x by blast
    let ?y0 = \<open>(\<lambda>(M, Oth). (drop (length M - length (get_trail_l x1)) (get_trail S'), Oth)) S'\<close>
    let ?y1 = \<open>propagate_nonunit_and_add x2 (TWL_DECO_clause (get_trail S')) ?y0\<close>
    obtain M3 where
      M3: \<open>get_trail_l S = M3 @ M2 @ Decided x2 # M1\<close>
      using decomp by blast
    have confl': \<open>get_conflict S' = None\<close> and
      trail_S': \<open>(get_trail_l S, get_trail S') \<in> convert_lits_l (get_clauses_l S) (get_unit_clauses_l S)\<close>
      using confl SS' by (auto simp: twl_st_l_def)
    have \<open>no_dup (trail (state\<^sub>W_of S'))\<close>
      using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
      by fast
    then have \<open>no_dup (get_trail_l S)\<close>
      using SS' by (auto simp: twl_st twl_st_l)
    then have [simp]: \<open>count_decided M3 = 0\<close> \<open>count_decided M2 = 0\<close>
      \<open>filter is_decided M3 = []\<close>
      \<open>filter is_decided M2 = []\<close>
      using lev_K
      by (auto simp: M3 count_decided_0_iff)
    obtain M2' where
      decomp': \<open>(Decided x2 # drop (length (get_trail S') - length M1) (get_trail S'), M2')
          \<in> set (get_all_ann_decomposition (get_trail S'))\<close> and
      conv: \<open>(get_trail_l S, get_trail S') \<in> convert_lits_l (get_clauses_l S)
        (get_unit_clauses_l S)\<close> and
      conv_M1: \<open>(M1, drop (length (get_trail S') - length M1) (get_trail S'))
            \<in> convert_lits_l (get_clauses_l S) (get_unit_clauses_l S)\<close>
      using convert_lits_l_decomp_ex[OF decomp, of \<open>get_trail S'\<close> \<open>get_clauses_l S\<close>
        \<open>get_unit_clauses_l S\<close>] SS'
      by (auto simp: twl_st_l_def)
    have M1_drop: \<open>drop (length (get_trail_l S) - length M1) (get_trail_l S) = M1\<close>
      using decomp by auto
    moreover have \<open>- x2 \<in> set (watched_l (DECO_clause_l (get_trail_l S)))\<close>
      using S_x1 tr_M1 SS' i decomp add_inv lev_K M3
      by (auto simp: DECO_clause_l_def)
    moreover have \<open>DECO_clause_l (get_trail_l S) ! 0 = -x2\<close>
      by (auto simp: M3 DECO_clause_l_def)
    moreover have \<open>Propagated L i \<notin> set M1\<close> for L
      using add_inv i S_x1 M3 unfolding twl_list_invs_def
      by (cases S; cases x1) auto
    ultimately have \<open>(propagate_nonunit_and_add_l x2 (DECO_clause_l (get_trail_l S)) i x1, ?y1) \<in>
        {(S, S''). (S, S'') \<in> twl_st_l None \<and> twl_list_invs S \<and> clauses_to_update_l S = {#}}\<close>
      using S_x1 tr_M1 SS' i add_inv decomp conv_M1 M1_drop
      by (cases S; cases S')
       (auto simp add: x1 twl_st_l_def twl_list_invs_def init_clss_l_mapsto_upd_notin
          TWL_DECO_clause_alt_def[symmetric] learned_clss_l_mapsto_upd_notin_irrelev
          convert_lit.simps
          intro!: convert_lits_l_extend_mono[of _ _ N \<open>D + NE\<close>])
    moreover have \<open>?y1 \<in> Collect (negate_model_and_add_twl S')\<close>
      using S_x1 tr_M1 i add_inv decomp confl confl' count_dec lev_K decomp' S_x1 SS'
      by (cases S; cases S')
        (auto simp: x1  twl_st_l_def
        intro!: negate_model_and_add_twl.bj_nonunit[of _ _ M2'])
    ultimately have \<open>\<exists>y\<in>Collect (negate_model_and_add_twl S').
        (propagate_nonunit_and_add_l x2 (DECO_clause_l (get_trail_l S)) i x1, y)
      \<in> {(S, S''). (S, S'') \<in> twl_st_l None \<and> twl_list_invs S \<and>
        clauses_to_update_l S = {#}}\<close>
      apply -
      apply (rule bexI[of _ ?y1])
      apply fast+
      done
    then show ?thesis
      unfolding x1
      apply (subst RETURN_RES_refine_iff)
      by fast
  qed
  have \<open>negate_mode_bj_nonunit_l_inv S\<close>
    using assms unfolding negate_mode_bj_nonunit_l_inv_def by blast
  then show ?thesis
    unfolding negate_mode_bj_nonunit_l_def find_decomp_target_def get_fresh_index_def
    apply refine_vcg
    apply (rule H; assumption)
    done
qed



fun restart_nonunit_and_add :: \<open>'v literal multiset twl_clause \<Rightarrow>  'v twl_st \<Rightarrow> 'v twl_st\<close> where
  \<open>restart_nonunit_and_add C (M, N, U, D, NE, UE, WS, Q) = do {
      (M, add_mset C N, U, None, NE, UE, {#}, {#})
    }\<close>

fun restart_nonunit_and_add_l :: \<open>'v clause_l \<Rightarrow> nat \<Rightarrow> 'v twl_st_l \<Rightarrow> 'v twl_st_l\<close> where
  \<open>restart_nonunit_and_add_l C i (M, N, D, NE, UE, WS, Q) = do {
      (M, fmupd i (C, True) N, None, NE, UE, {#}, {#})
    }\<close>

definition negate_mode_restart_nonunit_l_inv :: \<open>'v twl_st_l \<Rightarrow> bool\<close> where
\<open>negate_mode_restart_nonunit_l_inv S \<longleftrightarrow>
  (\<exists>S' b. (S, S') \<in> twl_st_l b \<and> twl_struct_invs S' \<and> twl_list_invs S \<and> twl_stgy_invs S' \<and>
     count_decided (get_trail_l S) > 1 \<and> get_conflict_l S = None)\<close>

definition negate_mode_restart_nonunit_l :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
\<open>negate_mode_restart_nonunit_l = (\<lambda>S. do {
    ASSERT(negate_mode_restart_nonunit_l_inv S);
    let C = DECO_clause_l (get_trail_l S);
    i \<leftarrow> SPEC(\<lambda>i. i < count_decided (get_trail_l S));
    (S, K) \<leftarrow> find_decomp_target i S;
    i \<leftarrow> get_fresh_index (get_clauses_l S);
    RETURN (restart_nonunit_and_add_l C i S)
  })\<close>

lemma negate_mode_restart_nonunit_l:
  fixes S :: \<open>'v twl_st_l\<close> and S' :: \<open>'v twl_st\<close>
  assumes
    count_dec: \<open>count_decided (get_trail_l S) > 1\<close> and
    SS': \<open>(S, S') \<in> twl_st_l b\<close> and
    struct_invs: \<open>twl_struct_invs S'\<close> and
    add_inv: \<open>twl_list_invs S\<close> and
    stgy_inv: \<open>twl_stgy_invs S'\<close> and
    confl: \<open>get_conflict_l S = None\<close>
  shows
    \<open>negate_mode_restart_nonunit_l S \<le> \<Down>{(S, S''). (S, S'') \<in> twl_st_l None \<and> twl_list_invs S \<and>
        clauses_to_update_l S = {#}}
       (SPEC (negate_model_and_add_twl S'))\<close>
proof -
  have H: \<open>RETURN (restart_nonunit_and_add_l (DECO_clause_l (get_trail_l S)) i x1)
        \<le> \<Down> {(S, S''). (S, S'') \<in> twl_st_l None \<and> twl_list_invs S \<and>
        clauses_to_update_l S = {#}}
          (SPEC (negate_model_and_add_twl S'))\<close>
    if
      j: \<open>j \<in> {i. i < count_decided (get_trail_l S)}\<close> and
      x_S: \<open>x \<in> {(T, K).
            \<exists>M2 M1.
              equality_except_trail S T \<and>
              get_trail_l T = M1 \<and>
              (Decided K # M1, M2) \<in> set (get_all_ann_decomposition (get_trail_l S)) \<and>
              get_level (get_trail_l S) K = j}\<close> and
      x: \<open>x = (x1, x2)\<close> and
      i: \<open>i \<in> {i. 0 < i \<and> i \<notin># dom_m (get_clauses_l x1)}\<close>
    for x :: \<open>'v twl_st_l \<times> 'v literal\<close> and
       x1 :: \<open>'v twl_st_l\<close> and x2 :: \<open>'v literal\<close> and i j :: \<open>nat\<close>
  proof -
    obtain M N U D NE UE Q where
      x1: \<open>x1 = (M, N, U, D, NE, UE, Q)\<close>
      by (cases x1)

    obtain M1 M2 where
      S_x1: \<open>equality_except_trail S x1\<close> and
      tr_M1: \<open>get_trail_l x1 = M1\<close> and
      decomp: \<open>(Decided x2 # M1, M2) \<in> set (get_all_ann_decomposition (get_trail_l S))\<close> and
      lev_K: \<open>get_level (get_trail_l S) x2 = j\<close>
      using x_S unfolding x by blast
    let ?y0 = \<open>(\<lambda>(M, Oth). (drop (length (get_trail S') - length M1) (get_trail S'), Oth)) S'\<close>
    let ?y1 = \<open>restart_nonunit_and_add (TWL_DECO_clause (get_trail S')) ?y0\<close>

    obtain M3 where
      M3: \<open>get_trail_l S = M3 @ M2 @ Decided x2 # M1\<close>
      using decomp by blast
    have \<open>M = M1\<close>
      using S_x1 SS' decomp tr_M1 unfolding x1
      by (cases S; cases S') auto
    have confl': \<open>get_conflict S' = None\<close> and
      trail_S': \<open>(get_trail_l S, get_trail S') \<in> convert_lits_l (get_clauses_l S) (get_unit_clauses_l S)\<close>
      using confl SS' by (auto simp: twl_st_l)
    have \<open>no_dup (trail (state\<^sub>W_of S'))\<close>
      using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
      by fast
    then have \<open>no_dup (get_trail_l S)\<close>
      using SS' by (auto simp: twl_st twl_st_l)
    obtain M2' where
      decomp': \<open>(Decided x2 # drop (length (get_trail S') - length M1) (get_trail S'), M2')
          \<in> set (get_all_ann_decomposition (get_trail S'))\<close> and
      conv: \<open>(get_trail_l S, get_trail S') \<in> convert_lits_l (get_clauses_l S)
        (get_unit_clauses_l S)\<close> and
      conv_M1: \<open>(M1, drop (length (get_trail S') - length M1) (get_trail S'))
            \<in> convert_lits_l (get_clauses_l S) (get_unit_clauses_l S)\<close>
      using convert_lits_l_decomp_ex[OF decomp, of \<open>get_trail S'\<close> \<open>get_clauses_l S\<close>
        \<open>get_unit_clauses_l S\<close>] SS'
      by (auto simp: twl_st_l_def)
    have M1_drop: \<open>drop (length (get_trail_l S) - length M1) (get_trail_l S) = M1\<close>
      using decomp by auto

    moreover have \<open>Propagated L i \<notin> set M1\<close> for L
      using add_inv i S_x1 M3 unfolding twl_list_invs_def
      by (cases S; cases x1) auto
    ultimately have \<open>(restart_nonunit_and_add_l (DECO_clause_l (get_trail_l S)) i x1, ?y1) \<in>
        {(S, S''). (S, S'') \<in> twl_st_l None \<and> twl_list_invs S \<and>
        clauses_to_update_l S = {#}}\<close>
      using S_x1 tr_M1 SS' i add_inv decomp conv_M1 decomp'
      by (cases S; cases S')
       (auto simp: x1 twl_st_l_def twl_list_invs_def init_clss_l_mapsto_upd_notin
          TWL_DECO_clause_alt_def[symmetric] learned_clss_l_mapsto_upd_notin_irrelev
          dest: get_all_ann_decomposition_exists_prepend
          intro!: convert_lits_l_extend_mono[of _ _ N \<open>D+NE\<close>])
    moreover {
      have \<open>get_level (get_trail_l S) x2 < count_decided (get_trail_l S)\<close>
        using lev_K j by auto
      then have \<open>?y1 \<in> Collect (negate_model_and_add_twl S')\<close>
        using S_x1 tr_M1 i add_inv decomp' confl confl' count_dec lev_K SS'
        by (cases S; cases S')
         (auto simp: x1  twl_st_l_def
          intro!: negate_model_and_add_twl.restart_nonunit[of x2 _ \<open>M2'\<close>])
    }
    ultimately have \<open>\<exists>y\<in>Collect (negate_model_and_add_twl S').
        (restart_nonunit_and_add_l (DECO_clause_l (get_trail_l S)) i x1, y)
      \<in> {(S, S''). (S, S'') \<in> twl_st_l None \<and> twl_list_invs S \<and>
        clauses_to_update_l S = {#}}\<close>
      apply -
      apply (rule bexI[of _ ?y1])
      apply fast+
      done
    then show ?thesis
      unfolding x1
      apply (subst RETURN_RES_refine_iff)
      by fast
  qed
  show ?thesis
    unfolding negate_mode_restart_nonunit_l_def find_decomp_target_def get_fresh_index_def
    apply refine_vcg
    subgoal
      using assms unfolding negate_mode_restart_nonunit_l_inv_def by fast
    subgoal
      supply [[unify_trace_failure]]
      apply (rule H; assumption)
      done
    done
qed

definition negate_mode_l_inv where
  \<open>negate_mode_l_inv S \<longleftrightarrow>
     (\<exists>S' b. (S, S') \<in> twl_st_l b \<and> twl_struct_invs S' \<and> twl_list_invs S \<and> twl_stgy_invs S' \<and>
       get_conflict_l S = None \<and> count_decided (get_trail_l S) \<noteq> 0)\<close>

definition negate_mode_l :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
  \<open>negate_mode_l S = do {
    ASSERT(negate_mode_l_inv S);
    if count_decided (get_trail_l S) = 1
    then negate_mode_bj_unit_l S
    else do {
      b \<leftarrow> SPEC(\<lambda>_. True);
      if b then negate_mode_bj_nonunit_l S else negate_mode_restart_nonunit_l S
    }
  }\<close>

lemma negate_mode_l:
  fixes S :: \<open>'v twl_st_l\<close> and S' :: \<open>'v twl_st\<close>
  assumes
    SS': \<open>(S, S') \<in> twl_st_l b\<close> and
    struct_invs: \<open>twl_struct_invs S'\<close> and
    add_inv: \<open>twl_list_invs S\<close> and
    stgy_inv: \<open>twl_stgy_invs S'\<close> and
    confl: \<open>get_conflict_l S = None\<close> and
    \<open>count_decided (get_trail_l S) \<noteq> 0\<close>
  shows
    \<open>negate_mode_l S \<le> \<Down>{(S, S''). (S, S'') \<in> twl_st_l None \<and> twl_list_invs S \<and>
        clauses_to_update_l S = {#}}
       (SPEC (negate_model_and_add_twl S'))\<close>
   unfolding negate_mode_l_def
   apply (refine_vcg negate_mode_restart_nonunit_l[OF _ SS'] negate_mode_bj_unit_l[OF _ SS']
      negate_mode_bj_nonunit_l[OF _ SS'] lhs_step_If)
    subgoal using assms unfolding negate_mode_l_inv_def by fast
    subgoal using assms by fast
    subgoal using assms by fast
    subgoal using assms by fast
    subgoal using assms by fast
    subgoal using assms by simp
    subgoal using assms by fast
    subgoal using assms by fast
    subgoal using assms by fast
    subgoal using assms by fast
    subgoal using assms by simp
    subgoal using assms by fast
    subgoal using assms by fast
    subgoal using assms by fast
    subgoal using assms by fast
    done

context
  fixes P :: \<open>'v literal set \<Rightarrow> bool\<close>
begin

definition cdcl_twl_enum_inv_l :: \<open>'v twl_st_l \<Rightarrow> bool\<close> where
  \<open>cdcl_twl_enum_inv_l S \<longleftrightarrow>
    (\<exists>S'. (S, S') \<in> twl_st_l None \<and> cdcl_twl_enum_inv S') \<and>
       twl_list_invs S\<close>

definition cdcl_twl_enum_l :: \<open>'v twl_st_l \<Rightarrow> bool nres\<close> where
  \<open>cdcl_twl_enum_l S = do {
     S \<leftarrow> cdcl_twl_stgy_prog_l S;
     S \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_enum_inv_l\<^esup>
       (\<lambda>S. get_conflict_l S = None \<and> count_decided(get_trail_l S) > 0 \<and>
            \<not>P (lits_of_l (get_trail_l S)))
       (\<lambda>S. do {
             S \<leftarrow> negate_mode_l S;
             cdcl_twl_stgy_prog_l S
           })
       S;
     if get_conflict_l S = None
     then RETURN (if count_decided(get_trail_l S) = 0 then P (lits_of_l (get_trail_l S)) else True)
     else RETURN (False)
    }\<close>


lemma negate_model_and_add_twl_resultD:
  \<open>negate_model_and_add_twl S T \<Longrightarrow>
    clauses_to_update T = {#} \<and> get_conflict T = None\<close>
  by (auto simp: negate_model_and_add_twl.simps)

lemma cdcl_twl_enum_l:
  fixes S :: \<open>'v twl_st_l\<close> and S' :: \<open>'v twl_st\<close>
  assumes
    SS': \<open>(S, S') \<in> twl_st_l None\<close> and
    struct_invs: \<open>twl_struct_invs S'\<close> and
    add_inv: \<open>twl_list_invs S\<close> and
    stgy_inv: \<open>twl_stgy_invs S'\<close> and
    confl: \<open>get_conflict_l S = None\<close> and
    \<open>count_decided (get_trail_l S) \<noteq> 0\<close> and
    \<open>clauses_to_update_l S = {#}\<close>
  shows
    \<open>cdcl_twl_enum_l S \<le> \<Down> bool_rel
       (cdcl_twl_enum P S')\<close>
  unfolding cdcl_twl_enum_l_def cdcl_twl_enum_def
  apply (refine_vcg cdcl_twl_stgy_prog_l_spec_final' negate_mode_l)
  subgoal
     using assms unfolding cdcl_twl_stgy_prog_l_pre_def
     by fast
  apply assumption
  subgoal for S S' U U'
     using assms unfolding cdcl_twl_enum_inv_l_def
     apply -
     apply (intro conjI)
     apply (rule exI[of _ U'])
     by auto
  subgoal by (auto simp: twl_st_l)
  apply auto[]
  subgoal unfolding cdcl_twl_enum_inv_def by auto
  subgoal by fast
  subgoal by (auto simp: twl_st_l cdcl_twl_enum_inv_def)
  subgoal by (auto simp: twl_st_l)
  subgoal by (auto simp: twl_st_l)
  subgoal for S S' T T' U U'
    by (rule cdcl_twl_stgy_prog_l_spec_final'[THEN order.trans])
      (auto simp: twl_st twl_st_l cdcl_twl_stgy_prog_l_pre_def cdcl_twl_enum_inv_def
      intro: negate_model_and_add_twl_twl_struct_invs
        negate_model_and_add_twl_twl_stgy_invs conc_fun_R_mono
      dest: negate_model_and_add_twl_resultD)
  subgoal by (auto simp: twl_st_l)
  subgoal by (auto simp: twl_st_l)
  done

end

end