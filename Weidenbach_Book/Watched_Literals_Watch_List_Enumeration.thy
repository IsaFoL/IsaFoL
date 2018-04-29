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

definition negate_mode_bj_unit_wl   :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
\<open>negate_mode_bj_unit_wl = (\<lambda>S. do {
    (S, K) \<leftarrow> find_decomp_target 1 S;
    RETURN (propagate_unit_and_add_l K S)
  })\<close>


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

end