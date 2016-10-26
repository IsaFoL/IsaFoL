theory CDCL_Two_Watched_Literals_List_Simple_Code
  imports CDCL_Two_Watched_Literals_List DPLL_CDCL_W_Implementation
begin

definition backtrack_list' :: "'v twl_st_list \<Rightarrow> 'v twl_st_list nres" where
  \<open>backtrack_list' S\<^sub>0 =
    do {
      let (M, N, U, D, NP, UP, WS, Q) = S\<^sub>0 in
      do {
        ASSERT(M \<noteq> []);
        let L = lit_of (hd M);
        ASSERT(get_level M L = count_decided M);
        ASSERT(\<exists>K M1 M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
          get_level M K = get_maximum_level M (mset (the D) - {#-L#}) + 1);
        let j = snd (the (find_level_decomp M (the D) [] (count_decided M)));
        let M1 = tl (the (bt_cut j M));

        if length (the D) > 1
        then do {
          let L' = the (find (\<lambda>L'.  get_level M L' = get_maximum_level M (mset (the D) - {#-L#})) (the D));
          RETURN (Propagated (-L) (length N) # M1,
            N @ [[-L, L'] @ (remove1 (-L) (remove1 L' (the D)))], U,
            None, NP, UP, WS, {#L#})
        }
        else do {
          RETURN (Propagated (-L) 0 # M1, N, U, None, NP, add_mset (mset (the D)) UP, WS, {#L#})
        }
      }
    }
  \<close>

lemma
  assumes
    \<open>get_conflict_list S \<noteq> None \<and> get_conflict_list S \<noteq> Some [] \<and>
       working_queue_list S = {#} \<and> pending_list S = {#} \<and> additional_WS_invs S \<and>
       no_step cdcl\<^sub>W_restart_mset.skip (convert_to_state (twl_st_of S)) \<and>
       no_step cdcl\<^sub>W_restart_mset.resolve (convert_to_state (twl_st_of S)) \<and>
       twl_struct_invs (twl_st_of S) \<and> twl_stgy_invs (twl_st_of S)\<close>
  shows \<open>(backtrack_list', backtrack_list) \<in> 
    {(S', S). S' = S \<and> get_conflict_list S \<noteq> None \<and> get_conflict_list S \<noteq> Some [] \<and>
       working_queue_list S = {#} \<and> pending_list S = {#} \<and> additional_WS_invs S \<and>
       no_step cdcl\<^sub>W_restart_mset.skip (convert_to_state (twl_st_of S)) \<and>
       no_step cdcl\<^sub>W_restart_mset.resolve (convert_to_state (twl_st_of S)) \<and>
       twl_struct_invs (twl_st_of S) \<and> twl_stgy_invs (twl_st_of S)} \<rightarrow> {(S', S). S' = S}\<close>
  unfolding backtrack_list_def backtrack_list'_def
    apply (rewrite at \<open>let _ = snd _ in _\<close> Let_def)
  apply refine_rcg
  apply (case_tac a')
  apply (refine_vcg ASSERT_same_eq_conv[THEN iffD2])
sorry
end