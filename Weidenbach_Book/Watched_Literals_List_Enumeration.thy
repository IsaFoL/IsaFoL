theory Watched_Literals_List_Enumeration
  imports Watched_Literals_Algorithm_Enumeration Watched_Literals_List
begin


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

definition negate_mode_bj_unit_l   :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
\<open>negate_mode_bj_unit_l = (\<lambda>S. do {
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
    \<open>negate_mode_bj_unit_l S \<le> \<Down>{(S, S''). (S, S'') \<in> twl_st_l None \<and> twl_list_invs S}
       (SPEC (negate_model_and_add_twl S'))\<close>
proof -
    have H: \<open>\<exists>y\<in>Collect (negate_model_and_add_twl S').
            (propagate_unit_and_add_l x2 x1, y)
            \<in> {(S, S''). (S, S'') \<in> twl_st_l None \<and> twl_list_invs S}\<close>
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
      let ?y0 = \<open>(\<lambda>(M, Oth). (convert_lits_l (get_clauses_l x1) (get_trail_l x1), Oth)) S'\<close>
      let ?y1 = \<open>propagate_unit_and_add x2 ?y0\<close>
      obtain M1 M2 where
        S_x1: \<open>equality_except_trail S x1\<close> and
        tr_M1: \<open>get_trail_l x1 = M1\<close> and
        decomp: \<open>(Decided x2 # M1, M2) \<in> set (get_all_ann_decomposition (get_trail_l S))\<close> and
        lev_x2: \<open>get_level (get_trail_l S) x2 = 1\<close>
        using x_S unfolding x by blast
      have x2_DECO: \<open>{#-x2#} = DECO_clause (get_trail S')\<close>
        using decomp count_dec S_S'
        by (auto simp: DECO_clause_def twl_st_l filter_mset_empty_conv count_decided_0_iff
            convert_lits_l_def
            dest!: get_all_ann_decomposition_exists_prepend)
      have \<open>(propagate_unit_and_add_l x2 x1, ?y1)
        \<in> {(S, S''). (S, S'') \<in> twl_st_l None \<and> twl_list_invs S}\<close>
        using S_S' S_x1 tr_M1 decomp lev_x2 add_inv unfolding x
        by (cases x1; cases S')
          (auto simp: twl_st_l_def twl_list_invs_def split: option.splits)
      moreover have \<open>negate_model_and_add_twl S' ?y1\<close>
        using S_S' confl lev_x2 count_dec tr_M1 S_x1
        imageI[OF decomp, of \<open>\<lambda>(M, M'). (convert_lits_l (get_clauses_l x1) M,
            convert_lits_l (get_clauses_l x1) M')\<close>]
        unfolding x
        apply (cases x1)
        by (force simp: twl_st_l_def x2_DECO get_all_ann_decomposition_convert_lits_l
          intro!: negate_model_and_add_twl.bj_unit[of _ _ \<open>convert_lits_l (get_clauses_l x1) M2\<close>]
          split: option.splits)
      ultimately show ?thesis
        apply -
        by (rule bexI[of _ ?y1]) fast+
    qed

  show ?thesis
    using assms
    unfolding negate_mode_bj_unit_l_def find_decomp_target_def
    apply (refine_rcg)
    apply (subst RETURN_RES_refine_iff)
    apply (rule H; assumption)
    done
qed

end