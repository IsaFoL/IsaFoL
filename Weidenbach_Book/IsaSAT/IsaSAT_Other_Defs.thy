theory IsaSAT_Other_Defs
imports IsaSAT_Conflict_Analysis_Defs IsaSAT_Backtrack_Defs IsaSAT_Decide_Defs
begin
chapter \<open>Combining Together: the Other Rules\<close>

definition cdcl_twl_o_prog_wl_D_heur
 :: \<open>isasat \<Rightarrow> (bool \<times> isasat) nres\<close>
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
          ASSERT(get_learned_count S = get_learned_count T);
          U \<leftarrow> backtrack_wl_D_nlit_heur T;
          U \<leftarrow> isasat_current_status U; \<comment> \<open>Print some information every once in a while\<close>
          RETURN (False, U)
        }
        else RETURN (True, S)
      }
    }
  \<close>

end