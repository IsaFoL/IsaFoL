theory IsaSAT_Defs
  imports IsaSAT_CDCL_Defs IsaSAT_Restart_Simp_Defs IsaSAT_Initialisation
begin

chapter \<open>Full IsaSAT\<close>

text \<open>
  We now combine all the previous definitions to prove correctness of the complete SAT
  solver:
  \<^enum> We initialise the arena part of the state;
  \<^enum> Then depending on the options and the number of clauses, we either use the
    bounded version or the unbounded version. Once have if decided which one,
    we initiale the watch lists;
  \<^enum> After that, we can run the CDCL part of the SAT solver;
  \<^enum> Finally, we extract the trail from the state.

  Remark that the statistics and the options are unchecked: the number of propagations
  might overflows (but they do not impact the correctness of the whole solver). Similar
  restriction applies on the options: setting the options might not do what you expect to
  happen, but the result will still be correct.
\<close>


definition extract_model_of_state_heur where
  \<open>extract_model_of_state_heur U = Some (fst (get_trail_wl_heur U))\<close>


definition convert_state where
  \<open>convert_state _ S = S\<close>

definition learned_clss_count_init :: \<open>twl_st_wl_heur_init \<Rightarrow> nat\<close> where
  \<open>learned_clss_count_init S = clss_size_lcount (get_learned_count_init S) +
    clss_size_lcountUE (get_learned_count_init S) + 
    clss_size_lcountUEk (get_learned_count_init S) + clss_size_lcountUS (get_learned_count_init S) +
    clss_size_lcountU0 (get_learned_count_init S)\<close>

definition isasat_fast_init :: \<open>twl_st_wl_heur_init \<Rightarrow> bool\<close> where
  \<open>isasat_fast_init S \<longleftrightarrow>
      (length (get_clauses_wl_heur_init S) \<le> sint64_max - (uint32_max div 2 + MAX_HEADER_SIZE+1) \<and>
       learned_clss_count_init S < uint64_max)\<close>

definition empty_init_code :: \<open>bool \<times> _ list \<times> isasat_stats\<close> where
  \<open>empty_init_code = (True, [], empty_stats)\<close>

definition empty_conflict_code :: \<open>(bool \<times> _ list \<times> isasat_stats) nres\<close> where
  \<open>empty_conflict_code = do{
     let M0 = [];
     RETURN (False, M0, empty_stats)}\<close>

definition extract_model_of_state_stat :: \<open>isasat \<Rightarrow> bool \<times> nat literal list \<times> isasat_stats\<close> where
  \<open>extract_model_of_state_stat U =
     (False, (fst (get_trail_wl_heur U)), (get_stats_heur U))\<close>

definition extract_state_stat :: \<open>isasat \<Rightarrow> bool \<times> nat literal list \<times> isasat_stats\<close> where
  \<open>extract_state_stat U =
     (True, [], (get_stats_heur U))\<close>

definition empty_conflict :: \<open>nat literal list option\<close> where
  \<open>empty_conflict = Some []\<close>

definition IsaSAT_bounded_heur :: \<open>opts \<Rightarrow> nat clause_l list \<Rightarrow> (bool \<times> (bool \<times> nat literal list \<times> isasat_stats)) nres\<close> where
  \<open>IsaSAT_bounded_heur opts CS = do{
    _ \<leftarrow> RETURN (IsaSAT_Profile.start_initialisation);
    ASSERT(isasat_input_bounded (mset_set (extract_atms_clss CS {})));
    ASSERT(\<forall>C\<in>set CS. \<forall>L\<in>set C. nat_of_lit L \<le> uint32_max);
    let \<A>\<^sub>i\<^sub>n' = mset_set (extract_atms_clss CS {});
    ASSERT(isasat_input_bounded \<A>\<^sub>i\<^sub>n');
    ASSERT(distinct_mset \<A>\<^sub>i\<^sub>n');
    let \<A>\<^sub>i\<^sub>n'' = virtual_copy \<A>\<^sub>i\<^sub>n';
    let b = opts_unbounded_mode opts;
    S \<leftarrow> init_state_wl_heur_fast \<A>\<^sub>i\<^sub>n';
    (T::twl_st_wl_heur_init) \<leftarrow> init_dt_wl_heur_b CS S;
    let T = convert_state \<A>\<^sub>i\<^sub>n'' T;
    _ \<leftarrow> RETURN (IsaSAT_Profile.stop_initialisation);
    if isasat_fast_init T \<and> \<not>is_failed_heur_init T
    then do {
      if \<not>get_conflict_wl_is_None_heur_init T
      then RETURN (False, empty_init_code)
      else if CS = [] then do {stat \<leftarrow> empty_conflict_code; RETURN (False, stat)}
      else do {
        _ \<leftarrow> RETURN (IsaSAT_Profile.start_initialisation);
        ASSERT(\<A>\<^sub>i\<^sub>n'' \<noteq> {#});
        ASSERT(isasat_input_bounded_nempty \<A>\<^sub>i\<^sub>n'');
        _ \<leftarrow> isasat_information_banner T;
        ASSERT(rewatch_heur_st_fast_pre T);
        T \<leftarrow> rewatch_heur_st_init T;
        ASSERT(isasat_fast_init T);
        T \<leftarrow> finalise_init_code opts (T::twl_st_wl_heur_init);
        _ \<leftarrow> RETURN (IsaSAT_Profile.stop_initialisation);
        ASSERT(isasat_fast T);
        (b, U) \<leftarrow> cdcl_twl_stgy_restart_prog_bounded_wl_heur T;
        RETURN (b, if \<not>b \<and> get_conflict_wl_is_None_heur U then extract_model_of_state_stat U
          else extract_state_stat U)
      }
    }
    else RETURN (True, empty_init_code)
  }\<close>


end