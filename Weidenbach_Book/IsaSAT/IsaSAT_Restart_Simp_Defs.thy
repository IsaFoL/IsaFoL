theory IsaSAT_Restart_Simp_Defs
  imports IsaSAT_Restart_Heuristics_Defs IsaSAT_Other_Defs IsaSAT_Propagate_Conflict_Defs IsaSAT_Restart_Inprocessing_Defs
    Watched_Literals.Watched_Literals_Watch_List_Reduce
begin

chapter \<open>Full CDCL with Restarts\<close>


definition cdcl_twl_stgy_restart_abs_wl_heur_inv where
  \<open>cdcl_twl_stgy_restart_abs_wl_heur_inv S\<^sub>0 = (\<lambda>(brk, T, last_GC, last_Rephase).
    (\<exists>S\<^sub>0' T'. (S\<^sub>0, S\<^sub>0') \<in> twl_st_heur \<and> (T, T') \<in> twl_st_heur_loop \<and>
      (\<not>brk \<longrightarrow> cdcl_twl_stgy_restart_abs_wl_inv S\<^sub>0' (brk, T', last_GC, last_Rephase))))\<close>

definition cdcl_twl_stgy_restart_abs_wl_heur_inv2 where
  \<open>cdcl_twl_stgy_restart_abs_wl_heur_inv2 S\<^sub>0 = (\<lambda>(brk, T, last_GC, last_Rephase).
    (\<exists>S\<^sub>0' T'. (S\<^sub>0, S\<^sub>0') \<in> twl_st_heur_loop \<and> (T, T') \<in> twl_st_heur_loop \<and>
      (\<not>brk\<longrightarrow>cdcl_twl_stgy_restart_abs_wl_inv S\<^sub>0' (brk, T', last_GC, last_Rephase))))\<close>

text \<open>It would be better to add a backtrack to level 0 before instead of delaying the restart.\<close>
definition update_all_phases :: \<open>isasat \<Rightarrow> (isasat) nres\<close> where
  \<open>update_all_phases = (\<lambda>S. do {
     if (isa_count_decided_st S = 0) then do {
       let lcount = get_global_conflict_count S;
       end_of_restart_phase \<leftarrow> RETURN (end_of_restart_phase_st S);
       S \<leftarrow> (if end_of_restart_phase > lcount then RETURN S else update_restart_phases S);
       S \<leftarrow> (if end_of_rephasing_phase_st S > lcount then RETURN S else rephase_heur_st S);
       RETURN S
    }
    else RETURN S
  })\<close>

definition isasat_fast_slow :: \<open>isasat \<Rightarrow> isasat nres\<close> where
   [simp]: \<open>isasat_fast_slow S = RETURN S\<close>

definition cdcl_twl_stgy_restart_prog_early_wl_heur
   :: \<open>isasat \<Rightarrow> isasat nres\<close>
where
  \<open>cdcl_twl_stgy_restart_prog_early_wl_heur S\<^sub>0 = do {
    ebrk \<leftarrow> RETURN (\<not>isasat_fast S\<^sub>0);
    (ebrk, brk, T, n) \<leftarrow>
       WHILE\<^sub>T\<^bsup>\<lambda>(ebrk, brk, T, last_GC, last_Restart, n).
       cdcl_twl_stgy_restart_abs_wl_heur_inv S\<^sub>0 (brk, T, last_GC, last_Restart, n) \<and>
        (\<not>ebrk \<longrightarrow>isasat_fast T) \<and> length (get_clauses_wl_heur T) \<le> uint64_max\<^esup>
      (\<lambda>(ebrk, brk, _). \<not>brk \<and> \<not>ebrk)
      (\<lambda>(ebrk, brk, S, last_GC, last_Restart, n).
      do {
        ASSERT(\<not>brk \<and> \<not>ebrk);
        ASSERT(length (get_clauses_wl_heur S) \<le> uint64_max);
        T \<leftarrow> unit_propagation_outer_loop_wl_D_heur S;
        ASSERT(length (get_clauses_wl_heur T) \<le> uint64_max);
        ASSERT(length (get_clauses_wl_heur T) = length (get_clauses_wl_heur S));
        (brk, T) \<leftarrow> cdcl_twl_o_prog_wl_D_heur T;
        ASSERT(length (get_clauses_wl_heur T) \<le> uint64_max);
        (T, n) \<leftarrow> restart_prog_wl_D_heur T last_GC last_Restart n brk;
	ebrk \<leftarrow> RETURN (\<not>isasat_fast T);
        RETURN (ebrk, brk \<or> \<not>get_conflict_wl_is_None_heur T, T, n)
      })
      (ebrk, False, S\<^sub>0::isasat, learned_clss_count S\<^sub>0, learned_clss_count S\<^sub>0,  0);
    ASSERT(length (get_clauses_wl_heur T) \<le> uint64_max \<and>
        get_old_arena T = []);
    if \<not>brk then do {
       T \<leftarrow> isasat_fast_slow T;
       (brk, T, _) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_restart_abs_wl_heur_inv2 T\<^esup>
	         (\<lambda>(brk, _). \<not>brk)
	         (\<lambda>(brk, S, last_GC, last_Restart, n).
	         do {
	           T \<leftarrow> unit_propagation_outer_loop_wl_D_heur S;
	           (brk, T) \<leftarrow> cdcl_twl_o_prog_wl_D_heur T;
	           (T, last_GC, last_Restart, n) \<leftarrow> restart_prog_wl_D_heur T last_GC last_Restart n brk;
	           RETURN (brk \<or> \<not>get_conflict_wl_is_None_heur T, T, last_GC, last_Restart, n)
	         })
	         (False, T, n);
       RETURN T
    }
    else isasat_fast_slow T
  }\<close>

definition cdcl_twl_stgy_restart_prog_bounded_wl_heur
   :: \<open>isasat \<Rightarrow> (bool \<times> isasat) nres\<close>
where
  \<open>cdcl_twl_stgy_restart_prog_bounded_wl_heur S\<^sub>0 = do {
    ebrk \<leftarrow> RETURN (\<not>isasat_fast S\<^sub>0);
    (ebrk, brk, T, n) \<leftarrow>
     WHILE\<^sub>T\<^bsup>\<lambda>(ebrk, brk, T, last_GC, last_Restart, n). cdcl_twl_stgy_restart_abs_wl_heur_inv S\<^sub>0 (brk, T, last_GC, last_Restart, n) \<and>
        (\<not>ebrk \<longrightarrow>isasat_fast T \<and> n < uint64_max) \<and>
        (\<not>ebrk \<longrightarrow>length (get_clauses_wl_heur T) \<le> sint64_max)\<^esup>
      (\<lambda>(ebrk, brk, _). \<not>brk \<and> \<not>ebrk)
      (\<lambda>(ebrk, brk, S, last_GC, last_Restart, n).
      do {
        ASSERT(\<not>brk \<and> \<not>ebrk);
        ASSERT(isasat_fast S);
        T \<leftarrow> unit_propagation_outer_loop_wl_D_heur S;
        ASSERT(isasat_fast T);
        (brk, T) \<leftarrow> cdcl_twl_o_prog_wl_D_heur T;
        ASSERT(isasat_fast_relaxed2 T n);
        (T, last_GC, last_Restart, n) \<leftarrow> restart_prog_wl_D_heur T last_GC last_Restart n brk;
        T \<leftarrow> update_all_phases T;
        ASSERT(isasat_fast_relaxed T);
	      ebrk \<leftarrow> RETURN (\<not>(isasat_fast T \<and> n < uint64_max));
        RETURN (ebrk, brk \<or> \<not>get_conflict_wl_is_None_heur T, T, last_GC, last_Restart, n)
      })
      (ebrk, False, S\<^sub>0::isasat, learned_clss_count S\<^sub>0, learned_clss_count S\<^sub>0, 0);
    RETURN (ebrk, T)
  }\<close>


definition cdcl_twl_stgy_restart_prog_wl_heur
   :: \<open>isasat \<Rightarrow> isasat nres\<close>
where
  \<open>cdcl_twl_stgy_restart_prog_wl_heur S\<^sub>0 = do {
    (brk, T, _) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_restart_abs_wl_heur_inv S\<^sub>0\<^esup>
      (\<lambda>(brk, _). \<not>brk)
      (\<lambda>(brk, S, last_GC, last_Rephase, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop_wl_D_heur S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog_wl_D_heur T;
        (T, last_GC, last_Rephase, n) \<leftarrow> restart_prog_wl_D_heur T last_GC last_Rephase n brk;
        RETURN (brk \<or> \<not>get_conflict_wl_is_None_heur T, T, last_GC, last_Rephase, n)
      })
      (False, S\<^sub>0::isasat, learned_clss_count S\<^sub>0, learned_clss_count S\<^sub>0, 0);
    RETURN T
  }\<close>

end