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
        if count_decided_st_heur S > zero_uint32_nat
        then do {
          T \<leftarrow> skip_and_resolve_loop_wl_D_heur S;
          ASSERT(length (get_clauses_wl_heur S) = length (get_clauses_wl_heur T));
          U \<leftarrow> backtrack_wl_D_nlit_heur T;
          RETURN (False, U)
        }
        else RETURN (True, S)
      }
    }
  \<close>

lemma cdcl_twl_o_prog_wl_D_heur_alt_def:
  \<open>cdcl_twl_o_prog_wl_D_heur S =
    do {
      if get_conflict_wl_is_None_heur S
      then decide_wl_or_skip_D_heur S
      else do {
        if count_decided_st_heur S > zero_uint32_nat
        then do {
          T \<leftarrow> skip_and_resolve_loop_wl_D_heur S;
          ASSERT(length (get_clauses_wl_heur S) = length (get_clauses_wl_heur T));
          U \<leftarrow> backtrack_wl_D_nlit_heur T;
          _ \<leftarrow> isasat_current_status U; \<comment> \<open>Print some information every once in a while\<close>
          RETURN (False, U)
        }
        else RETURN (True, S)
      }
    }
  \<close>
  unfolding cdcl_twl_o_prog_wl_D_heur_def isasat_current_status_def
  by auto

(*TODO Move*)
declare backtrack_wl_D_fast_code.refine[sepref_fr_rules]
  backtrack_wl_D_code.refine[sepref_fr_rules]

sepref_register get_conflict_wl_is_None decide_wl_or_skip_D_heur skip_and_resolve_loop_wl_D_heur
  backtrack_wl_D_nlit_heur isasat_current_status count_decided_st_heur get_conflict_wl_is_None_heur

sepref_register cdcl_twl_o_prog_wl_D

sepref_definition cdcl_twl_o_prog_wl_D_code
  is \<open>cdcl_twl_o_prog_wl_D_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a bool_assn *a isasat_unbounded_assn\<close>
  unfolding cdcl_twl_o_prog_wl_D_heur_alt_def PR_CONST_def
  unfolding get_conflict_wl_is_None get_conflict_wl_is_None_heur_alt_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref

sepref_definition cdcl_twl_o_prog_wl_D_fast_code
  is \<open>cdcl_twl_o_prog_wl_D_heur\<close>
  :: \<open>[isasat_fast]\<^sub>a
      isasat_bounded_assn\<^sup>d \<rightarrow> bool_assn *a isasat_bounded_assn\<close>
  unfolding cdcl_twl_o_prog_wl_D_heur_alt_def PR_CONST_def
  unfolding get_conflict_wl_is_None get_conflict_wl_is_None_heur_alt_def[symmetric]
  supply [[goals_limit = 1]] isasat_fast_def[simp]
  by sepref

declare cdcl_twl_o_prog_wl_D_code.refine[sepref_fr_rules]
  cdcl_twl_o_prog_wl_D_fast_code.refine[sepref_fr_rules]

lemma twl_st_heur_count_decided_st_alt_def:
  fixes S :: twl_st_wl_heur
  shows \<open>(S, T) \<in> twl_st_heur \<Longrightarrow> count_decided_st_heur S = count_decided (get_trail_wl T)\<close>
  unfolding count_decided_st_def twl_st_heur_def trail_pol_def
  by (cases S) (auto simp: count_decided_st_heur_def)

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
        unfolded ref_def twl_st_heur'_def nres_rel_def in_pair_collect_simp f,
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
        unfolded ref_def twl_st_heur'_def nres_rel_def in_pair_collect_simp f,
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
        unfolded ref_def twl_st_heur'_def nres_rel_def in_pair_collect_simp f,
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
  \<open>(cdcl_twl_o_prog_wl_D_heur, cdcl_twl_o_prog_wl_D) \<in> twl_st_heur \<rightarrow>\<^sub>f
     \<langle>bool_rel \<times>\<^sub>f twl_st_heur\<rangle>nres_rel\<close>
proof -
  have [refine0]: \<open>(x, y) \<in> twl_st_heur \<Longrightarrow>
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
        decide_wl_or_skip_D_heur_decide_wl_or_skip_D[THEN twl_st_heur'''D_twl_st_heurD_prod,
             THEN fref_to_Down]
        skip_and_resolve_loop_wl_D_heur_skip_and_resolve_loop_wl_D[THEN fref_to_Down]
        backtrack_wl_D_nlit_backtrack_wl_D[THEN fref_to_Down])
    subgoal
      by (auto simp: twl_st_heur_state_simp
          get_conflict_wl_is_None_heur_get_conflict_wl_is_None[THEN fref_to_Down_unRET_Id])
    subgoal by (auto simp: twl_st_heur_state_simp twl_st_heur_count_decided_st_alt_def)
    subgoal by (auto simp: twl_st_heur_state_simp twl_st_heur_twl_st_heur_conflict_ana)
    subgoal by (auto simp: twl_st_heur_state_simp)
    subgoal by (auto simp: twl_st_heur_state_simp)
    subgoal by (auto simp: twl_st_heur_state_simp)
    done
qed


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
  unfolding cdcl_twl_stgy_prog_wl_D_heur_def cdcl_twl_stgy_prog_wl_D_def
  apply (intro frefI nres_relI)
  apply (refine_vcg
      unit_propagation_outer_loop_wl_D_heur_unit_propagation_outer_loop_wl_D[THEN fref_to_Down]
      cdcl_twl_o_prog_wl_D_heur_cdcl_twl_o_prog_wl_D[THEN fref_to_Down])
  subgoal by (auto simp: twl_st_heur_state_simp)
  subgoal by (auto simp: twl_st_heur_state_simp)
  subgoal by (auto simp: twl_st_heur_state_simp)
  subgoal by (auto simp: twl_st_heur_state_simp)
  done

sepref_register cdcl_twl_stgy_prog_wl_D unit_propagation_outer_loop_wl_D_heur
  cdcl_twl_o_prog_wl_D_heur

sepref_definition cdcl_twl_stgy_prog_wl_D_code
  is \<open>cdcl_twl_stgy_prog_wl_D_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  unfolding cdcl_twl_stgy_prog_wl_D_heur_def PR_CONST_def
  supply [[goals_limit = 1]]
  by sepref

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


export_code cdcl_twl_stgy_prog_wl_D_code in SML_imp module_name SAT_Solver
  file "code/CDCL_Cached_Array_Trail.sml"


end
