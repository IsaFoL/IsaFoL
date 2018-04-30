theory Watched_Literals_Watch_List_Enumeration
  imports Watched_Literals_List_Enumeration Watched_Literals_Watch_List
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
           get_unit_init_clss_wl S));
    RETURN (propagate_unit_and_add_wl K S)
  })\<close>

(* TODO Move *)
lemma in_all_lits_of_mm_uminusD: \<open>x2 \<in># all_lits_of_mm N \<Longrightarrow> -x2 \<in># all_lits_of_mm N\<close>
  by (auto simp: all_lits_of_mm_def)
(* End Move *)

lemma find_decomp_target_wl_find_decomp_target_l:
  assumes
    SS': \<open>(S, S') \<in> state_wl_l None\<close> and
    inv: \<open>negate_mode_bj_unit_l_inv S'\<close> and
    corr: \<open>correct_watching S\<close> and
    [simp]: \<open>a = a'\<close>
  shows \<open>find_decomp_target_wl a S \<le>
     \<Down> {((S, K), (S', K')). (S, S') \<in> {(S, S'). (S, S') \<in> state_wl_l None \<and> correct_watching S} \<and>
        (K , K') \<in> Id \<and> K \<in># all_lits_of_mm (clause `# twl_clause_of `# ran_mf (get_clauses_wl S) +
          get_unit_init_clss_wl S)}
    (find_decomp_target a' S')\<close>
    (is \<open>_ \<le> \<Down> ?negate _\<close>)
proof -
  let ?y0 = \<open>\<lambda>S S'. (\<lambda>(M, Oth). (get_trail_wl S, Oth)) S'\<close>
  have K: \<open>K \<in># all_lits_of_mm (clause `# twl_clause_of `# ran_mf (get_clauses_wl S) +
          get_unit_init_clss_wl S)\<close>
    if K: \<open>K \<in> lits_of_l (get_trail_wl S)\<close>
    for K
  proof -
    obtain b S'' where
      S'_S'': \<open>(S', S'') \<in> twl_st_l b\<close> and
      struct: \<open>twl_struct_invs S''\<close>
      using inv unfolding negate_mode_bj_unit_l_inv_def by blast
    then have no_alien: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of S'')\<close>
      using struct unfolding twl_struct_invs_def by fast
    then have no_alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of S'')\<close>
      unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast
    moreover have \<open>atms_of_mm (get_all_init_clss S'') =
          atms_of_mm (mset `# (ran_mf (get_clauses_wl S)) + get_unit_init_clss_wl S)\<close>
      apply (subst all_clss_lf_ran_m[symmetric])
      using no_alien 
      using S'_S'' SS' K unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
      by (cases S; cases S'; cases b)
        (auto simp: mset_take_mset_drop_mset' cdcl\<^sub>W_restart_mset_state
        in_all_lits_of_mm_ain_atms_of_iff twl_st_l_def state_wl_l_def)
    ultimately show ?thesis
      using S'_S'' SS' K unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
      by (auto simp: twl_st_l twl_st mset_take_mset_drop_mset'
        in_all_lits_of_mm_ain_atms_of_iff)
  qed
  show ?thesis
    using SS' corr
    unfolding find_decomp_target_wl_def find_decomp_target_def apply -
    apply (rule RES_refine)
    apply (rule_tac x=\<open>(?y0 (fst s) S', snd s)\<close> in bexI)
    subgoal
      using K
      by (cases S; cases S')
        (auto simp: state_wl_l_def correct_watching.simps clause_to_update_def
        mset_take_mset_drop_mset')
    subgoal
      by (cases S; cases S')
        (auto simp: state_wl_l_def correct_watching.simps clause_to_update_def)
    done
qed

lemma negate_mode_bj_unit_l:
  fixes S :: \<open>'v twl_st_wl\<close> and S' :: \<open>'v twl_st_l\<close>
  assumes \<open>count_decided (get_trail_wl S) = 1\<close> and
    SS': \<open>(S, S') \<in> state_wl_l None\<close> and
    confl: \<open>get_conflict_wl S = None\<close> and
    corr: \<open>correct_watching S\<close>
  shows
    \<open>negate_mode_bj_unit_wl S \<le> \<Down>{(S, S'). (S, S') \<in> state_wl_l None \<and> correct_watching S}
       (negate_mode_bj_unit_l S')\<close>
       (is \<open>_ \<le> \<Down> ?R _\<close>)
proof -
  have 2: \<open>(propagate_unit_and_add_wl x2a x1a, propagate_unit_and_add_l x2 x1)
        \<in> {(S, S''). (S, S'') \<in> state_wl_l None \<and> correct_watching S}\<close>
    if 
      \<open>(x, x') \<in> {((S, K), (S', K')). (S, S') \<in> {(S, S'). (S, S') \<in> state_wl_l None \<and> correct_watching S} \<and>
        (K , K') \<in> Id \<and> K \<in># all_lits_of_mm (clause `# twl_clause_of `# ran_mf (get_clauses_wl S) +
          get_unit_init_clss_wl S)}\<close> and
      \<open>x' = (x1, x2)\<close> and
      \<open>x = (x1a, x2a)\<close>
    for x2a x1a x2 x1 and x :: \<open>'v twl_st_wl \<times> 'v literal\<close> and x' :: \<open>'v twl_st_l \<times> 'v literal\<close>
  proof -
    show ?thesis
      using that
      by (cases x1a; cases x1)
        (auto simp: state_wl_l_def correct_watching.simps clause_to_update_def
          all_lits_of_mm_add_mset
          all_lits_of_m_add_mset all_lits_of_mm_union mset_take_mset_drop_mset'
          dest: in_all_lits_of_mm_uminusD)
  qed

  show ?thesis
    using SS' corr unfolding negate_mode_bj_unit_wl_def negate_mode_bj_unit_l_def
    by (refine_rcg find_decomp_target_wl_find_decomp_target_l 2) auto
qed

fun propagate_nonunit_and_add_wl
  :: \<open>'v literal \<Rightarrow> 'v clause_l \<Rightarrow> nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close>
where
  \<open>propagate_nonunit_and_add_wl K C i (M, N, D, NE, UE, Q, W) = do {
      ASSERT(length C \<ge> 2);
      let W = W(C!0 := W (C!0) @ [i]);
      let W = W(C!1 := W (C!1) @ [i]);
      RETURN (Propagated (-K) i # M, fmupd i (C, True) N, None,
      NE, UE, {#K#}, W)
    }\<close>


definition negate_mode_bj_nonunit_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
\<open>negate_mode_bj_nonunit_wl = (\<lambda>S. do {
    let C = DECO_clause_l (get_trail_wl S);
    (S, K) \<leftarrow> find_decomp_target_wl (count_decided (get_trail_wl S)) S;
    i \<leftarrow> get_fresh_index (get_clauses_wl S);
    propagate_nonunit_and_add_wl K C i S
  })\<close>


lemma negate_mode_bj_nonunit_l:
  fixes S :: \<open>'v twl_st_wl\<close> and S' :: \<open>'v twl_st_l\<close>
  assumes \<open>count_decided (get_trail_wl S) = 1\<close> and
    SS': \<open>(S, S') \<in> state_wl_l None\<close> and
    confl: \<open>get_conflict_wl S = None\<close> and
    corr: \<open>correct_watching S\<close>
  shows
    \<open>negate_mode_bj_nonunit_wl S \<le> \<Down>{(S, S''). (S, S'') \<in> state_wl_l None \<and> correct_watching S}
       (negate_mode_bj_nonunit_l S')\<close>
proof -

  show ?thesis
    using corr SS'
    unfolding negate_mode_bj_nonunit_wl_def negate_mode_bj_nonunit_l_def
    apply (refine_rcg find_decomp_target_wl_find_decomp_target_l)
    subgoal 
      unfolding negate_mode_bj_nonunit_l_inv_def negate_mode_bj_unit_l_inv_def
    using SS' by (auto simp: )
end