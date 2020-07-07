theory IsaSAT_Rephase_State
  imports IsaSAT_Rephase IsaSAT_Setup IsaSAT_Show
begin

definition rephase_heur :: \<open>64 word \<Rightarrow> restart_heuristics \<Rightarrow> restart_heuristics nres\<close> where
  \<open>rephase_heur = (\<lambda>b (fast_ema, slow_ema, restart_info, wasted, \<phi>).
    do {
      \<phi> \<leftarrow> phase_rephase b \<phi>;
      RETURN (fast_ema, slow_ema, restart_info, wasted, \<phi>)
   })\<close>

lemma rephase_heur_spec:
  \<open>heuristic_rel \<A> heur \<Longrightarrow> rephase_heur b heur \<le>  \<Down>Id (SPEC(heuristic_rel \<A>))\<close>
  unfolding rephase_heur_def
  apply (refine_vcg phase_rephase_spec[THEN order_trans])
  apply (auto simp: heuristic_rel_def)
  done

definition rephase_heur_st :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>rephase_heur_st = (\<lambda>(M', arena, D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
       vdom, avdom, lcount, opts, old_arena). do {
      let b = current_restart_phase heur;
      heur \<leftarrow> rephase_heur b heur;
      let _ = isasat_print_progress (current_rephasing_phase heur) b stats lcount;
      RETURN (M', arena, D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
       vdom, avdom, lcount, opts, old_arena)
   })\<close>

lemma rephase_heur_st_spec:
  \<open>(S, S') \<in> twl_st_heur \<Longrightarrow> rephase_heur_st S \<le> SPEC(\<lambda>S. (S, S') \<in> twl_st_heur)\<close>
  unfolding rephase_heur_st_def
  apply (cases S')
  apply (refine_vcg rephase_heur_spec[THEN order_trans, of \<open>all_atms_st S'\<close>])
  apply (simp_all add:  twl_st_heur_def)
  done

definition save_rephase_heur :: \<open>nat \<Rightarrow> restart_heuristics \<Rightarrow> restart_heuristics nres\<close> where
  \<open>save_rephase_heur = (\<lambda>n (fast_ema, slow_ema, restart_info, wasted, \<phi>).
    do {
      \<phi> \<leftarrow> phase_save_phase n \<phi>;
      RETURN (fast_ema, slow_ema, restart_info, wasted, \<phi>)
   })\<close>

lemma save_phase_heur_spec:
  \<open>heuristic_rel \<A> heur \<Longrightarrow> save_rephase_heur n heur \<le>  \<Down>Id (SPEC(heuristic_rel \<A>))\<close>
  unfolding save_rephase_heur_def
  apply (refine_vcg phase_save_phase_spec[THEN order_trans])
  apply (auto simp: heuristic_rel_def)
  done


definition save_phase_st :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>save_phase_st = (\<lambda>(M', arena, D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
       vdom, avdom, lcount, opts, old_arena). do {
      ASSERT(isa_length_trail_pre M');
      let n = isa_length_trail M';
      heur \<leftarrow> save_rephase_heur n heur;
      RETURN (M', arena, D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
       vdom, avdom, lcount, opts, old_arena)
   })\<close>

lemma save_phase_st_spec:
  \<open>(S, S') \<in> twl_st_heur \<Longrightarrow> save_phase_st S \<le> SPEC(\<lambda>S. (S, S') \<in> twl_st_heur)\<close>
  unfolding save_phase_st_def
  apply (cases S')
  apply (refine_vcg save_phase_heur_spec[THEN order_trans, of \<open>all_atms_st S'\<close>])
  apply (simp_all add:  twl_st_heur_def isa_length_trail_pre)
  apply (rule isa_length_trail_pre)
  apply blast
  done

end