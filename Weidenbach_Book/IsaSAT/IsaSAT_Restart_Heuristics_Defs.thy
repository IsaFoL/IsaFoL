theory IsaSAT_Restart_Heuristics_Defs
imports
  IsaSAT_Restart_Reduce_Defs IsaSAT_Restart_Inprocessing
begin

text \<open>

  For simplification in our proofs, our inprocessing contains both inprocessing (currently:
  deduplication of binary clauses) and removal of unit clauses. We leave the concrete schedule
  to the inprocessing function.
\<close>
definition should_inprocess_or_unit_reduce_st :: \<open>isasat \<Rightarrow> bool \<Rightarrow> bool\<close> where
  \<open>should_inprocess_or_unit_reduce_st S should_GC \<longleftrightarrow>
      (should_GC \<and> units_since_last_GC_st S > 0) \<or>
      should_inprocess_st S \<or>
      GC_units_required S\<close>

definition restart_required_heur :: \<open>isasat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 8 word nres\<close> where
  \<open>restart_required_heur S last_GC last_Restart n = do {
    ASSERT(learned_clss_count S \<ge> last_Restart);
    ASSERT(learned_clss_count S \<ge> last_GC);
    let opt_red = opts_reduction_st S;
    let opt_res = opts_restart_st S;
    let curr_phase = get_restart_phase S;
    let can_res = (learned_clss_count S > last_Restart);
    let can_GC = (learned_clss_count S - last_GC> n);
    let fully_proped = is_fully_propagated_heur_st S;
    let should_reduce = (opt_red \<and> upper_restart_bound_reached S \<and> can_GC);
    should_GC \<leftarrow> GC_required_heur S n;
    let should_inprocess = should_inprocess_or_unit_reduce_st S should_GC;

    if (\<not>can_res \<and> \<not>can_GC) \<or> \<not>opt_res \<or> \<not>opt_red \<or> \<not>fully_proped then RETURN FLAG_no_restart
    else if curr_phase = STABLE_MODE
    then do {
      if should_reduce
      then if should_inprocess
      then RETURN FLAG_Inprocess_restart
      else if should_GC then RETURN FLAG_GC_restart else RETURN FLAG_Reduce_restart
      else if heuristic_reluctant_triggered2_st S \<and> can_res
        then RETURN FLAG_restart
        else RETURN FLAG_no_restart
    }
    else do {
      let sema = ema_get_value (get_slow_ema_heur S);
      let limit = (opts_restart_coeff1_st S) * (shiftr (sema) 4);
      let fema = ema_get_value (get_fast_ema_heur S);
      let ccount = get_conflict_count_since_last_restart_heur S;
      let min_reached = (ccount > opts_minimum_between_restart_st S);
      let level = count_decided_st_heur S;
      let should_restart = ((opt_res) \<and>
         limit > fema \<and> min_reached \<and> can_res \<and>
        level > 2 \<and> \<^cancel>\<open>This comment from Marijn Heule seems not to help:
           \<^term>\<open>level < max_restart_decision_lvl\<close>\<close>
        of_nat level > (shiftr fema 32));
      if should_reduce
        then if should_inprocess
        then RETURN FLAG_Inprocess_restart
        else if should_GC
        then RETURN FLAG_GC_restart
        else RETURN FLAG_Reduce_restart
      else if should_restart
      then RETURN FLAG_restart
      else RETURN FLAG_no_restart
     }
   }\<close>


(*TODO Move clean: cdcl_twl_local_restart_wl_spec0 vs cdcl_twl_local_restart_wl_spec is mess*)


definition cdcl_twl_full_restart_wl_D_GC_heur_prog where
\<open>cdcl_twl_full_restart_wl_D_GC_heur_prog S0 = do {
    _ \<leftarrow> RETURN (IsaSAT_Profile.start_GC);
    S \<leftarrow> do {
      if count_decided_st_heur S0 > 0
      then do {
        S \<leftarrow> find_decomp_wl_st_int 0 S0;
        empty_Q (empty_US_heur S)
      } else RETURN (empty_US_heur S0)
    };
    ASSERT(length (get_clauses_wl_heur S) = length (get_clauses_wl_heur S0));
    ASSERT(learned_clss_count S \<le> learned_clss_count S0);
    T \<leftarrow> remove_one_annot_true_clause_imp_wl_D_heur S;
    ASSERT(length (get_clauses_wl_heur T) = length (get_clauses_wl_heur S0));
    ASSERT(learned_clss_count T \<le> learned_clss_count S0);
    U \<leftarrow> mark_to_delete_clauses_GC_wl_D_heur T;
    ASSERT(length (get_clauses_wl_heur U) = length (get_clauses_wl_heur S0));
    ASSERT(learned_clss_count U \<le> learned_clss_count S0);
    V \<leftarrow> isasat_GC_clauses_wl_D False U;
    _ \<leftarrow> RETURN (IsaSAT_Profile.stop_GC);
    RETURN (clss_size_resetUS0_st V)
  }\<close>


definition cdcl_twl_full_restart_wl_D_inprocess_heur_prog where
\<open>cdcl_twl_full_restart_wl_D_inprocess_heur_prog S0 = do {
    _ \<leftarrow> RETURN (IsaSAT_Profile.start_reduce);
    S \<leftarrow> do {
      if count_decided_st_heur S0 > 0
      then do {
        S \<leftarrow> find_decomp_wl_st_int 0 S0;
        empty_Q (empty_US_heur S)
      } else RETURN (empty_US_heur S0)
    };
    ASSERT(length (get_clauses_wl_heur S) = length (get_clauses_wl_heur S0));
    ASSERT(learned_clss_count S \<le> learned_clss_count S0);
    T \<leftarrow> remove_one_annot_true_clause_imp_wl_D_heur S;
    _ \<leftarrow> RETURN (IsaSAT_Profile.stop_reduce);
    ASSERT(length (get_clauses_wl_heur T) = length (get_clauses_wl_heur S0));
        ASSERT(learned_clss_count T \<le> learned_clss_count S0);
    _ \<leftarrow> RETURN (IsaSAT_Profile.start_binary_simp);
    T \<leftarrow> isa_mark_duplicated_binary_clauses_as_garbage_wl2 T;
    _ \<leftarrow> RETURN (IsaSAT_Profile.stop_binary_simp);
    ASSERT(length (get_clauses_wl_heur T) = length (get_clauses_wl_heur S0));
        ASSERT(learned_clss_count T \<le> learned_clss_count S0);
    _ \<leftarrow> RETURN (IsaSAT_Profile.start_subsumption);
    T \<leftarrow> isa_forward_subsumption_all T;
    _ \<leftarrow> RETURN (IsaSAT_Profile.stop_subsumption);
    ASSERT(length (get_clauses_wl_heur T) = length (get_clauses_wl_heur S0));
        ASSERT(learned_clss_count T \<le> learned_clss_count S0);
    _ \<leftarrow> RETURN (IsaSAT_Profile.start_pure_literal);
    T \<leftarrow> isa_pure_literal_elimination_wl T;
    _ \<leftarrow> RETURN (IsaSAT_Profile.stop_pure_literal);
    ASSERT(length (get_clauses_wl_heur T) = length (get_clauses_wl_heur S0));
    ASSERT(learned_clss_count T \<le> learned_clss_count S0);
    _ \<leftarrow> RETURN (IsaSAT_Profile.start_reduce);
    T \<leftarrow> isa_simplify_clauses_with_units_st_wl2 T;
    _ \<leftarrow> RETURN (IsaSAT_Profile.stop_reduce);
    ASSERT(length (get_clauses_wl_heur T) = length (get_clauses_wl_heur S0));
    ASSERT(learned_clss_count T \<le> learned_clss_count S0);
    if \<not>get_conflict_wl_is_None_heur T then RETURN T
    else do {
      _ \<leftarrow> RETURN (IsaSAT_Profile.start_GC);
      U \<leftarrow> mark_to_delete_clauses_GC_wl_D_heur T;
      ASSERT(length (get_clauses_wl_heur U) = length (get_clauses_wl_heur S0));
      ASSERT(learned_clss_count U \<le> learned_clss_count S0);
      V \<leftarrow> isasat_GC_clauses_wl_D True U;
      _ \<leftarrow> RETURN (IsaSAT_Profile.stop_GC);
      RETURN (clss_size_resetUS0_st V)
    }
  }\<close>


definition restart_prog_wl_D_heur
  :: \<open>isasat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> (isasat \<times> nat \<times> nat \<times> nat) nres\<close>
where
  \<open>restart_prog_wl_D_heur S last_GC last_Restart n brk = do {
   if brk then RETURN (S, last_GC, last_Restart, n)
   else do {
      b \<leftarrow> restart_required_heur S last_GC last_Restart n;
      if b = FLAG_restart
      then do {
         T \<leftarrow> cdcl_twl_restart_wl_heur S;
         ASSERT(learned_clss_count T \<le> learned_clss_count S);
         RETURN (T, last_GC, learned_clss_count T, n)
      }
      else if b \<noteq> FLAG_no_restart
      then if b \<noteq> FLAG_Inprocess_restart then do {
         if b = FLAG_Reduce_restart
         then do {
           T \<leftarrow> cdcl_twl_mark_clauses_to_delete S;
           ASSERT(learned_clss_count T \<le> learned_clss_count S);
           RETURN (T, learned_clss_count T, learned_clss_count T, n+1)
         }
         else do {
           T \<leftarrow> cdcl_twl_full_restart_wl_D_GC_heur_prog S;
           ASSERT(learned_clss_count T \<le> learned_clss_count S);
           RETURN (T, learned_clss_count T, learned_clss_count T, n+1)
         }
     } else do {
         T \<leftarrow> cdcl_twl_full_restart_wl_D_inprocess_heur_prog S;
         ASSERT(learned_clss_count T \<le> learned_clss_count S);
         RETURN (T, learned_clss_count T, learned_clss_count T, n+1)
     }
      else RETURN (S, last_GC, last_Restart, n)
    }
  }\<close>

end