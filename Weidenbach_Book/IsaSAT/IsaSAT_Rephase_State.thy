theory IsaSAT_Rephase_State
  imports IsaSAT_Rephase IsaSAT_Setup IsaSAT_Show
begin

definition rephase_heur_stats :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> restart_heuristics \<Rightarrow> restart_heuristics nres\<close> where
  \<open>rephase_heur_stats = (\<lambda>end_of_phase b (fast_ema, slow_ema, restart_info, wasted, \<phi>, relu).
    do {
      \<phi> \<leftarrow> phase_rephase end_of_phase b \<phi>;
      RETURN (fast_ema, slow_ema, restart_info, wasted, \<phi>, relu)
   })\<close>


definition rephase_heur :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> isasat_restart_heuristics \<Rightarrow> isasat_restart_heuristics nres\<close> where
  \<open>rephase_heur = (\<lambda>end_of_phase b heur.
  do {
  \<phi> \<leftarrow> rephase_heur_stats end_of_phase b (get_content heur);
  RETURN (Restart_Heuristics \<phi>)
  })\<close>


lemma rephase_heur_spec:
  \<open>heuristic_rel \<A> heur \<Longrightarrow> rephase_heur end_of_phase b heur \<le>  \<Down>Id (SPEC(heuristic_rel \<A>))\<close>
  unfolding rephase_heur_def rephase_heur_stats_def
  apply (refine_vcg phase_rephase_spec[THEN order_trans])
  apply (auto simp: heuristic_rel_def heuristic_rel_stats_def)
  done

definition rephase_heur_st :: \<open>isasat \<Rightarrow> isasat nres\<close> where
  \<open>rephase_heur_st = (\<lambda>S. do {
      let lcount = get_global_conflict_count S;
      let heur = get_heur S;
      let stats = get_stats_heur S;
      let b = current_restart_phase heur;
      heur \<leftarrow> rephase_heur lcount b heur;
      let _ = isasat_print_progress (current_phase_letter (current_rephasing_phase heur))
                  b stats (get_learned_count S);
      RETURN (set_heur_wl_heur heur S)
   })\<close>

lemma rephase_heur_st_spec:
  \<open>(S, S') \<in> twl_st_heur \<Longrightarrow> rephase_heur_st S \<le> SPEC(\<lambda>S. (S, S') \<in> twl_st_heur)\<close>
  unfolding rephase_heur_st_def
  apply (cases S')
  apply (refine_vcg rephase_heur_spec[THEN order_trans, of \<open>all_atms_st S'\<close>])
  apply (simp_all add:  twl_st_heur_def all_atms_st_def)
  done

definition save_rephase_heur_stats :: \<open>64 word \<Rightarrow> restart_heuristics \<Rightarrow> restart_heuristics nres\<close> where
  \<open>save_rephase_heur_stats = (\<lambda>n (fast_ema, slow_ema, restart_info, wasted, \<phi>, relu).
    do {
      \<phi> \<leftarrow> phase_save_phase n \<phi>;
      RETURN (fast_ema, slow_ema, restart_info, wasted, \<phi>, relu)
  })\<close>

definition save_rephase_heur :: \<open>64 word \<Rightarrow> isasat_restart_heuristics \<Rightarrow> isasat_restart_heuristics nres\<close> where
  \<open>save_rephase_heur = (\<lambda>n heur.
  do {
  \<phi> \<leftarrow> save_rephase_heur_stats n (get_content heur);
  RETURN (Constructor \<phi>)
  })\<close>

lemma save_phase_heur_spec:
  \<open>heuristic_rel \<A> heur \<Longrightarrow> save_rephase_heur n heur \<le>  \<Down>Id (SPEC(heuristic_rel \<A>))\<close>
  unfolding save_rephase_heur_def save_rephase_heur_stats_def
  apply (refine_vcg phase_save_phase_spec[THEN order_trans])
  apply (auto simp: heuristic_rel_def heuristic_rel_stats_def)
  done


definition save_phase_st :: \<open>isasat \<Rightarrow> isasat nres\<close> where
  \<open>save_phase_st = (\<lambda>S. do {
      let stats = get_stats_heur S;
      let n = no_conflict_until stats;
      let heur = get_heur S;
      heur \<leftarrow> save_rephase_heur n heur;
      RETURN (set_heur_wl_heur heur S)
   })\<close>

lemma save_phase_st_spec:
  \<open>(S, S') \<in> twl_st_heur \<Longrightarrow> save_phase_st S \<le> SPEC(\<lambda>S. (S, S') \<in> twl_st_heur)\<close>
  unfolding save_phase_st_def
  apply (cases S')
  apply (refine_vcg save_phase_heur_spec[THEN order_trans, of \<open>all_atms_st S'\<close>])
  apply (simp_all add:  twl_st_heur_def isa_length_trail_pre all_atms_st_def flip: all_lits_st_alt_def)
  done

end