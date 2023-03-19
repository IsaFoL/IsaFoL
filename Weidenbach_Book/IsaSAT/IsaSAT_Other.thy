theory IsaSAT_Other
  imports IsaSAT_Conflict_Analysis IsaSAT_Backtrack IsaSAT_Decide
    IsaSAT_Other_Defs
begin
chapter \<open>Combining Together: the Other Rules\<close>

lemma cdcl_twl_o_prog_wl_D_heur_cdcl_twl_o_prog_wl_D:
  \<open>(cdcl_twl_o_prog_wl_D_heur, cdcl_twl_o_prog_wl) \<in>
   {(S, T). (S, T) \<in> twl_st_heur \<and> length (get_clauses_wl_heur S) = r \<and> learned_clss_count S = u} \<rightarrow>\<^sub>f
     \<langle>bool_rel \<times>\<^sub>f {(S, T). (S, T) \<in> twl_st_heur \<and>
        length (get_clauses_wl_heur S) \<le> r + MAX_HEADER_SIZE+1 + unat32_max div 2  \<and> 
           learned_clss_count S \<le> Suc u}\<rangle>nres_rel\<close>
proof -
  have H: \<open>(x, y) \<in> {(S, T).
               (S, T) \<in> twl_st_heur \<and>
               length (get_clauses_wl_heur S) =
               length (get_clauses_wl_heur x)} \<Longrightarrow>
           (x, y)
           \<in> {(S, T).
               (S, T) \<in> twl_st_heur_conflict_ana \<and>
               length (get_clauses_wl_heur S) =
               length (get_clauses_wl_heur x)}\<close> for x y
    by (auto simp: twl_st_heur_state_simp twl_st_heur_twl_st_heur_conflict_ana)
   have H2: \<open>(x, y) \<in> {(S, T).
     (S, T) \<in> twl_st_heur \<and>
     length (get_clauses_wl_heur S) = r \<and> learned_clss_count S = u} \<Longrightarrow>
          (x, y) \<in> twl_st_heur_conflict_ana' r (get_learned_count x)\<close> for x y
     by (auto simp: twl_st_heur_state_simp twl_st_heur_twl_st_heur_conflict_ana)
   have H3: \<open>(x, y)
     \<in> {(S, T).
     (S, T) \<in> twl_st_heur \<and>
     length (get_clauses_wl_heur S) = r \<and> learned_clss_count S = u} \<Longrightarrow>
     (x, y) \<in> {(S, T). (S, T) \<in> twl_st_heur''' r \<and> learned_clss_count S = u}\<close> for x y
     by auto
 have UUa: \<open>(U, Ua)
       \<in> {(S, T).
          (S, T) \<in> twl_st_heur \<and>
          length (get_clauses_wl_heur S) \<le> 3 + 1 + r + unat32_max div 2 \<and>
          learned_clss_count S \<le> Suc u} \<Longrightarrow>
       (U,  Ua)
       \<in> {(S, Tb).
          (S, Tb) \<in> twl_st_heur \<and>
     length (get_clauses_wl_heur S) \<le> 3 + 1 + r + unat32_max div 2 \<and> learned_clss_count S \<le> Suc u}\<close> for U Ua
   by auto
  show ?thesis
    unfolding cdcl_twl_o_prog_wl_D_heur_def cdcl_twl_o_prog_wl_def
      get_conflict_wl_is_None
    apply (intro frefI nres_relI)
    apply (refine_vcg
        decide_wl_or_skip_D_heur_decide_wl_or_skip_D[where r=r and u=u, THEN fref_to_Down, THEN order_trans]
        skip_and_resolve_loop_wl_D_heur_skip_and_resolve_loop_wl_D[where r=r, THEN fref_to_Down]
        backtrack_wl_D_nlit_backtrack_wl_D[where r=r and u=u, THEN fref_to_Down]
        isasat_current_status_id[THEN fref_to_Down, THEN order_trans])
    subgoal
      by (auto simp: twl_st_heur_state_simp
          get_conflict_wl_is_None_heur_get_conflict_wl_is_None[THEN fref_to_Down_unRET_Id])
    apply (rule H3; assumption)
    subgoal by (rule conc_fun_R_mono) auto
    subgoal by (auto simp: twl_st_heur_state_simp twl_st_heur_count_decided_st_alt_def)
    apply (rule H2; assumption)
    subgoal by (auto simp: twl_st_heur_state_simp twl_st_heur_twl_st_heur_conflict_ana)
    subgoal by (auto simp: twl_st_heur_state_simp)
    subgoal by (auto simp: twl_st_heur_state_simp dest!: get_learned_count_learned_clss_countD2)
    apply (rule UUa; assumption)
    subgoal by (auto simp: conc_fun_RES RETURN_def learned_clss_count_def)
    subgoal by (auto simp: twl_st_heur_state_simp)
    done
qed

lemma cdcl_twl_o_prog_wl_D_heur_cdcl_twl_o_prog_wl_D2:
  \<open>(cdcl_twl_o_prog_wl_D_heur, cdcl_twl_o_prog_wl) \<in>
   {(S, T). (S, T) \<in> twl_st_heur} \<rightarrow>\<^sub>f
     \<langle>bool_rel \<times>\<^sub>f {(S, T). (S, T) \<in> twl_st_heur}\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (rule cdcl_twl_o_prog_wl_D_heur_cdcl_twl_o_prog_wl_D[THEN fref_to_Down, THEN order_trans])
  apply (auto intro!: conc_fun_R_mono)
  done

end
