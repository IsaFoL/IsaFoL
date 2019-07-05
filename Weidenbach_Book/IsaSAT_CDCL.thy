theory IsaSAT_CDCL
  imports IsaSAT_Propagate_Conflict IsaSAT_Conflict_Analysis IsaSAT_Backtrack
    IsaSAT_Decide IsaSAT_Show
begin

paragraph \<open>Combining Together: the Other Rules\<close>

definition cdcl_twl_o_prog_wl_D_heur
 :: \<open>twl_st_wl_heur \<Rightarrow> (bool \<times> twl_st_wl_heur) nres\<close>
where
  \<open>cdcl_twl_o_prog_wl_D_heur S =
    do {
      if get_conflict_wl_is_None_heur S
      then decide_wl_or_skip_D_heur S
      else do {
        if count_decided_st_heur S > 0
        then do {
          T \<leftarrow> skip_and_resolve_loop_wl_D_heur S;
          ASSERT(length (get_clauses_wl_heur S) = length (get_clauses_wl_heur T));
          U \<leftarrow> backtrack_wl_D_nlit_heur T;
          U \<leftarrow> isasat_current_status U; \<comment> \<open>Print some information every once in a while\<close>
          RETURN (False, U)
        }
        else RETURN (True, S)
      }
    }
  \<close>

lemma twl_st_heur''D_twl_st_heurD:
  assumes H: \<open>(\<And>\<D> r. f \<in> twl_st_heur'' \<D> r \<rightarrow>\<^sub>f \<langle>twl_st_heur'' \<D> r\<rangle> nres_rel)\<close>
  shows \<open>f \<in> twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle> nres_rel\<close>  (is \<open>_ \<in> ?A B\<close>)
proof -
  obtain f1 f2 where f: \<open>f = (f1, f2)\<close>
    by (cases f) auto
  show ?thesis
    unfolding f
    apply (simp only: fref_def twl_st_heur'_def nres_rel_def in_pair_collect_simp)
    apply (intro conjI impI allI)
    subgoal for x y
      using assms[of \<open>dom_m (get_clauses_wl y)\<close>  \<open>length (get_clauses_wl_heur x)\<close>,
        unfolded twl_st_heur'_def nres_rel_def in_pair_collect_simp f,
        rule_format] unfolding f
      apply (simp only: fref_def twl_st_heur'_def nres_rel_def in_pair_collect_simp)
      apply (drule spec[of _ x])
      apply (drule spec[of _ y])
      apply simp
      apply (rule "weaken_\<Down>'"[of _ \<open>twl_st_heur'' (dom_m (get_clauses_wl y))
         (length (get_clauses_wl_heur x))\<close>])
      apply (fastforce simp: twl_st_heur'_def)+
      done
    done
qed


lemma twl_st_heur'''D_twl_st_heurD:
  assumes H: \<open>(\<And>r. f \<in> twl_st_heur''' r \<rightarrow>\<^sub>f \<langle>twl_st_heur''' r\<rangle> nres_rel)\<close>
  shows \<open>f \<in> twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle> nres_rel\<close>  (is \<open>_ \<in> ?A B\<close>)
proof -
  obtain f1 f2 where f: \<open>f = (f1, f2)\<close>
    by (cases f) auto
  show ?thesis
    unfolding f
    apply (simp only: fref_def twl_st_heur'_def nres_rel_def in_pair_collect_simp)
    apply (intro conjI impI allI)
    subgoal for x y
      using assms[of \<open>length (get_clauses_wl_heur x)\<close>,
        unfolded twl_st_heur'_def nres_rel_def in_pair_collect_simp f,
        rule_format] unfolding f
      apply (simp only: fref_def twl_st_heur'_def nres_rel_def in_pair_collect_simp)
      apply (drule spec[of _ x])
      apply (drule spec[of _ y])
      apply simp
      apply (rule "weaken_\<Down>'"[of _ \<open>twl_st_heur''' (length (get_clauses_wl_heur x))\<close>])
      apply (fastforce simp: twl_st_heur'_def)+
      done
    done
qed


lemma twl_st_heur'''D_twl_st_heurD_prod:
  assumes H: \<open>(\<And>r. f \<in> twl_st_heur''' r \<rightarrow>\<^sub>f \<langle>A \<times>\<^sub>r twl_st_heur''' r\<rangle> nres_rel)\<close>
  shows \<open>f \<in> twl_st_heur \<rightarrow>\<^sub>f \<langle>A \<times>\<^sub>r twl_st_heur\<rangle> nres_rel\<close>  (is \<open>_ \<in> ?A B\<close>)
proof -
  obtain f1 f2 where f: \<open>f = (f1, f2)\<close>
    by (cases f) auto
  show ?thesis
    unfolding f
    apply (simp only: fref_def twl_st_heur'_def nres_rel_def in_pair_collect_simp)
    apply (intro conjI impI allI)
    subgoal for x y
      using assms[of \<open>length (get_clauses_wl_heur x)\<close>,
        unfolded twl_st_heur'_def nres_rel_def in_pair_collect_simp f,
        rule_format] unfolding f
      apply (simp only: fref_def twl_st_heur'_def nres_rel_def in_pair_collect_simp)
      apply (drule spec[of _ x])
      apply (drule spec[of _ y])
      apply simp
      apply (rule "weaken_\<Down>'"[of _ \<open>A \<times>\<^sub>r twl_st_heur''' (length (get_clauses_wl_heur x))\<close>])
      apply (fastforce simp: twl_st_heur'_def)+
      done
    done
qed

lemma cdcl_twl_o_prog_wl_D_heur_cdcl_twl_o_prog_wl_D:
  \<open>(cdcl_twl_o_prog_wl_D_heur, cdcl_twl_o_prog_wl_D) \<in>
   {(S, T). (S, T) \<in> twl_st_heur \<and> length (get_clauses_wl_heur S) = r} \<rightarrow>\<^sub>f
     \<langle>bool_rel \<times>\<^sub>f {(S, T). (S, T) \<in> twl_st_heur \<and>
        length (get_clauses_wl_heur S) \<le> r + 6 + uint32_max div 2}\<rangle>nres_rel\<close>
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
  show ?thesis
    unfolding cdcl_twl_o_prog_wl_D_heur_def cdcl_twl_o_prog_wl_D_def
      get_conflict_wl_is_None
    apply (intro frefI nres_relI)
    apply (refine_vcg
        decide_wl_or_skip_D_heur_decide_wl_or_skip_D[where r=r, THEN fref_to_Down, THEN order_trans]
        skip_and_resolve_loop_wl_D_heur_skip_and_resolve_loop_wl_D[where r=r, THEN fref_to_Down]
        backtrack_wl_D_nlit_backtrack_wl_D[where r=r, THEN fref_to_Down]
        isasat_current_status_id[THEN fref_to_Down, THEN order_trans])
    subgoal
      by (auto simp: twl_st_heur_state_simp
          get_conflict_wl_is_None_heur_get_conflict_wl_is_None[THEN fref_to_Down_unRET_Id])
    apply (assumption)
    subgoal by (rule conc_fun_R_mono) auto
    subgoal by (auto simp: twl_st_heur_state_simp twl_st_heur_count_decided_st_alt_def)
    subgoal by (auto simp: twl_st_heur_state_simp twl_st_heur_twl_st_heur_conflict_ana)
    subgoal by (auto simp: twl_st_heur_state_simp)
    apply assumption
    subgoal by (auto simp: conc_fun_RES RETURN_def)
    subgoal by (auto simp: twl_st_heur_state_simp)
    done
qed

lemma cdcl_twl_o_prog_wl_D_heur_cdcl_twl_o_prog_wl_D2:
  \<open>(cdcl_twl_o_prog_wl_D_heur, cdcl_twl_o_prog_wl_D) \<in>
   {(S, T). (S, T) \<in> twl_st_heur} \<rightarrow>\<^sub>f
     \<langle>bool_rel \<times>\<^sub>f {(S, T). (S, T) \<in> twl_st_heur}\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (rule cdcl_twl_o_prog_wl_D_heur_cdcl_twl_o_prog_wl_D[THEN fref_to_Down, THEN order_trans])
  apply (auto intro!: conc_fun_R_mono)
  done


paragraph \<open>Combining Together: Full Strategy\<close>

definition  cdcl_twl_stgy_prog_wl_D_heur
   :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>
where
  \<open>cdcl_twl_stgy_prog_wl_D_heur S\<^sub>0 =
  do {
    do {
        (brk, T) \<leftarrow> WHILE\<^sub>T
        (\<lambda>(brk, _). \<not>brk)
        (\<lambda>(brk, S).
        do {
          T \<leftarrow> unit_propagation_outer_loop_wl_D_heur S;
          cdcl_twl_o_prog_wl_D_heur T
        })
        (False, S\<^sub>0);
      RETURN T
    }
  }
  \<close>

theorem unit_propagation_outer_loop_wl_D_heur_unit_propagation_outer_loop_wl_D:
  \<open>(unit_propagation_outer_loop_wl_D_heur, unit_propagation_outer_loop_wl_D) \<in>
    twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle> nres_rel\<close>
  using twl_st_heur''D_twl_st_heurD[OF
     unit_propagation_outer_loop_wl_D_heur_unit_propagation_outer_loop_wl_D']
  .

lemma cdcl_twl_stgy_prog_wl_D_heur_cdcl_twl_stgy_prog_wl_D:
  \<open>(cdcl_twl_stgy_prog_wl_D_heur, cdcl_twl_stgy_prog_wl_D) \<in> twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle>nres_rel\<close>
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
  show ?thesis
    unfolding cdcl_twl_stgy_prog_wl_D_heur_def cdcl_twl_stgy_prog_wl_D_def
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


definition cdcl_twl_stgy_prog_break_wl_D_heur :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>
where
  \<open>cdcl_twl_stgy_prog_break_wl_D_heur S\<^sub>0 =
  do {
    b \<leftarrow> RETURN (isasat_fast S\<^sub>0);
    (b, brk, T) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(b, brk, T). True\<^esup>
        (\<lambda>(b, brk, _). b \<and> \<not>brk)
        (\<lambda>(b, brk, S).
        do {
          ASSERT(isasat_fast S);
          T \<leftarrow> unit_propagation_outer_loop_wl_D_heur S;
          ASSERT(isasat_fast T);
          (brk, T) \<leftarrow> cdcl_twl_o_prog_wl_D_heur T;
          b \<leftarrow> RETURN (isasat_fast T);
          RETURN(b, brk, T)
        })
        (b, False, S\<^sub>0);
    if brk then RETURN T
    else cdcl_twl_stgy_prog_wl_D_heur T
  }\<close>


definition cdcl_twl_stgy_prog_bounded_wl_heur :: \<open>twl_st_wl_heur \<Rightarrow> (bool \<times> twl_st_wl_heur) nres\<close>
where
  \<open>cdcl_twl_stgy_prog_bounded_wl_heur S\<^sub>0 =
  do {
    b \<leftarrow> RETURN (isasat_fast S\<^sub>0);
    (b, brk, T) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(b, brk, T). True\<^esup>
        (\<lambda>(b, brk, _). b \<and> \<not>brk)
        (\<lambda>(b, brk, S).
        do {
          ASSERT(isasat_fast S);
          T \<leftarrow> unit_propagation_outer_loop_wl_D_heur S;
          ASSERT(isasat_fast T);
          (brk, T) \<leftarrow> cdcl_twl_o_prog_wl_D_heur T;
          b \<leftarrow> RETURN (isasat_fast T);
          RETURN(b, brk, T)
        })
        (b, False, S\<^sub>0);
    RETURN (brk, T)
  }\<close>


lemma cdcl_twl_stgy_restart_prog_early_wl_heur_cdcl_twl_stgy_restart_prog_early_wl_D:
  assumes r: \<open>r \<le> sint64_max\<close>
  shows \<open>(cdcl_twl_stgy_prog_bounded_wl_heur, cdcl_twl_stgy_prog_early_wl_D) \<in>
   twl_st_heur''' r \<rightarrow>\<^sub>f \<langle>bool_rel \<times>\<^sub>r twl_st_heur\<rangle>nres_rel\<close>
proof -
  have A[refine0]: \<open>RETURN (isasat_fast x) \<le> \<Down>
      {(b, b'). b = b' \<and> (b = (isasat_fast x))} (RES UNIV)\<close>
    for x
    by (auto intro: RETURN_RES_refine)
  have twl_st_heur'': \<open>(x1e, x1b) \<in> twl_st_heur \<Longrightarrow>
    (x1e, x1b)
    \<in> twl_st_heur''
        (dom_m (get_clauses_wl x1b))
        (length (get_clauses_wl_heur x1e))\<close>
    for x1e x1b
    by (auto simp: twl_st_heur'_def)
  have twl_st_heur''': \<open>(x1e, x1b) \<in> twl_st_heur'' \<D> r \<Longrightarrow>
    (x1e, x1b)
    \<in> twl_st_heur''' r\<close>
    for x1e x1b r \<D>
    by (auto simp: twl_st_heur'_def)
  have H: \<open>SPEC (\<lambda>_::bool. True) = RES UNIV\<close> by auto
  show ?thesis
    supply[[goals_limit=1]] isasat_fast_length_leD[dest] twl_st_heur'_def[simp]
    unfolding cdcl_twl_stgy_prog_bounded_wl_heur_def
      cdcl_twl_stgy_prog_early_wl_D_def H
    apply (intro frefI nres_relI)
    apply (refine_rcg
        cdcl_twl_o_prog_wl_D_heur_cdcl_twl_o_prog_wl_D[THEN fref_to_Down]
        unit_propagation_outer_loop_wl_D_heur_unit_propagation_outer_loop_wl_D'[THEN fref_to_Down]
        WHILEIT_refine[where R = \<open>{((ebrk, brk, T), (ebrk', brk', T')).
	    (ebrk = ebrk') \<and> (brk = brk') \<and> (T, T')  \<in> twl_st_heur \<and>
	      (ebrk \<longrightarrow> isasat_fast T) \<and> length (get_clauses_wl_heur T) \<le> sint64_max}\<close>])
    subgoal using r by auto
    subgoal by fast
    subgoal by auto
    apply (rule twl_st_heur''; auto; fail)
    subgoal by (auto simp: isasat_fast_def)
    apply (rule twl_st_heur'''; assumption)
    subgoal by (auto simp: isasat_fast_def sint64_max_def uint32_max_def)
    subgoal by auto
    done
qed

end
