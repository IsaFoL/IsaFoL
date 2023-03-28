theory IsaSAT_CDCL
  imports IsaSAT_Propagate_Conflict IsaSAT_Other IsaSAT_Show
    IsaSAT_CDCL_Defs
begin



paragraph \<open>Combining Together: Full Strategy\<close>

lemma cdcl_twl_stgy_prog_wl_D_heur_cdcl_twl_stgy_prog_wl_D:
  \<open>(cdcl_twl_stgy_prog_wl_D_heur, cdcl_twl_stgy_prog_wl) \<in> twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle>nres_rel\<close>
proof -
  have H[refine0]: \<open>(x, y) \<in> {(S, T).
               (S, T) \<in> twl_st_heur \<and>
               length (get_clauses_wl_heur S) =
               length (get_clauses_wl_heur x)} \<Longrightarrow>
           (x, y)
           \<in> {(S, T).
               (S, T) \<in> twl_st_heur \<and> get_learned_count S = get_learned_count x}\<close> for x y
    by (auto simp: twl_st_heur_state_simp twl_st_heur_twl_st_heur_conflict_ana)
  show ?thesis
    unfolding cdcl_twl_stgy_prog_wl_D_heur_def cdcl_twl_stgy_prog_wl_def
    apply (intro frefI nres_relI)
    subgoal for x y
    apply (refine_vcg
        unit_propagation_outer_loop_wl_D_heur_unit_propagation_outer_loop_wl_D'[THEN twl_st_heur''D_twl_st_heurD, THEN fref_to_Down]
        cdcl_twl_o_prog_wl_D_heur_cdcl_twl_o_prog_wl_D2[THEN fref_to_Down])
    subgoal by (auto simp: twl_st_heur_state_simp)
    subgoal by (auto simp: twl_st_heur_state_simp twl_st_heur'_def)
    subgoal by (auto simp: twl_st_heur'_def)
    subgoal by (auto simp: twl_st_heur_state_simp)
    subgoal by (auto simp: twl_st_heur_state_simp)
    done
    done
qed



lemma cdcl_twl_stgy_prog_early_wl_heur_cdcl_twl_stgy_prog_early_wl_D:
  assumes r: \<open>r \<le> snat64_max\<close>
  shows \<open>(cdcl_twl_stgy_prog_bounded_wl_heur, cdcl_twl_stgy_prog_early_wl) \<in>
    {(S,T). (S, T) \<in> twl_st_heur''' r} \<rightarrow>\<^sub>f
    \<langle>bool_rel \<times>\<^sub>r  twl_st_heur\<rangle>nres_rel\<close>
proof -
  have A[refine0]: \<open>RETURN (isasat_fast x) \<le> \<Down>
      {(b, b'). b = b' \<and> (b = (isasat_fast x))} (RES UNIV)\<close>
    for x
    by (auto intro: RETURN_RES_refine)
  have twl_st_heur'': \<open>(x1e, x1b) \<in> twl_st_heur \<Longrightarrow>
    (x1e, x1b)
    \<in> twl_st_heur''
        (dom_m (get_clauses_wl x1b))
        (length (get_clauses_wl_heur x1e))
        (get_learned_count x1e)\<close>
    for x1e x1b
    by (auto simp: twl_st_heur'_def)
  have twl_st_heur''': \<open>(x1e, x1b) \<in> twl_st_heur'' \<D> r lcount \<Longrightarrow>
    (x1e, x1b)
    \<in> {(S, Taa).
          (S, Taa) \<in> twl_st_heur \<and>
          length (get_clauses_wl_heur S) = r \<and>
          learned_clss_count S = (\<lambda>(a,b,c,d,e). a + b + c + d+e) (lcount)}\<close>
    for x1e x1b r \<D> lcount
    by (auto simp: twl_st_heur'_def learned_clss_count_def clss_size_lcountUEk_def
      clss_size_lcountUE_def clss_size_lcountU0_def clss_size_lcount_def clss_size_lcountUS_def
      split: prod.splits)
  have H: \<open>SPEC (\<lambda>_::bool. True) = RES UNIV\<close> by auto
  show ?thesis
    supply[[goals_limit=1]] isasat_fast_length_leD[dest] twl_st_heur'_def[simp]
    unfolding cdcl_twl_stgy_prog_bounded_wl_heur_def
      cdcl_twl_stgy_prog_early_wl_def H
    apply (intro frefI nres_relI)
    apply (refine_rcg
        cdcl_twl_o_prog_wl_D_heur_cdcl_twl_o_prog_wl_D[THEN fref_to_Down]
        unit_propagation_outer_loop_wl_D_heur_unit_propagation_outer_loop_wl_D'[THEN fref_to_Down]
        WHILEIT_refine[where R = \<open>{((ebrk, brk, T), (ebrk', brk', T')).
	    (ebrk = ebrk') \<and> (brk = brk') \<and> (T, T')  \<in> twl_st_heur \<and>
	      (ebrk \<longrightarrow> isasat_fast T) \<and> (length (get_clauses_wl_heur T) \<le> snat64_max)}\<close>])
    subgoal using r by auto
    subgoal by fast
    subgoal by auto
    apply (rule twl_st_heur''; auto; fail)
    subgoal by (auto simp: isasat_fast_def dest: get_learned_count_learned_clss_countD)
    apply (rule twl_st_heur'''; assumption)
    subgoal
      apply clarsimp
      by (auto simp: isasat_fast_def snat64_max_def unat32_max_def
      dest: )
    subgoal by auto
    done
qed

end
