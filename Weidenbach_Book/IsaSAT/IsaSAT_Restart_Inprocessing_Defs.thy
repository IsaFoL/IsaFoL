(*TODO Rename to IsaSAT_Inprocessing*)
theory IsaSAT_Restart_Inprocessing_Defs
  imports IsaSAT_Setup
    IsaSAT_Simplify_Units_Defs
    Watched_Literals.Watched_Literals_Watch_List_Inprocessing
    More_Refinement_Libs.WB_More_Refinement_Loops
    IsaSAT_Restart_Defs
    IsaSAT_Simplify_Binaries_Defs
    IsaSAT_Simplify_Pure_Literals_Defs
    IsaSAT_Simplify_Forward_Subsumption_Defs
begin

definition isa_pure_literal_elimination_round_wl where
  \<open>isa_pure_literal_elimination_round_wl S\<^sub>0 = do {
    ASSERT (isa_pure_literal_elimination_round_wl_pre S\<^sub>0);
    S \<leftarrow> isa_simplify_clauses_with_units_st_wl2 S\<^sub>0;
    ASSERT (length (get_clauses_wl_heur S) = length (get_clauses_wl_heur S\<^sub>0));
    ASSERT (learned_clss_count S \<le> learned_clss_count S\<^sub>0);
    if get_conflict_wl_is_None_heur S
    then do {
     let S = incr_purelit_rounds_st S;
     (abort, occs) \<leftarrow> isa_pure_literal_count_occs_wl (S);
      if \<not>abort then isa_pure_literal_deletion_wl occs S
      else RETURN (0, S)}
    else RETURN (0, S)
}\<close>



definition isa_pure_literal_elimination_wl_pre :: \<open>_\<close> where
  \<open>isa_pure_literal_elimination_wl_pre S = (\<exists>T u r.
    (S, T) \<in> twl_st_heur_restart_ana' r u \<and> pure_literal_elimination_wl_pre T)\<close>

definition isa_pure_literal_elimination_wl_inv :: \<open>_\<close> where
  \<open>isa_pure_literal_elimination_wl_inv S max_rounds = (\<lambda>(T,m,abort). \<exists>S' T' u r.
  (S, S') \<in> twl_st_heur_restart_ana' r u \<and>
  (T, T') \<in> twl_st_heur_restart_ana' r u \<and> pure_literal_elimination_wl_inv S' max_rounds (T', m, abort))\<close>

definition isa_pure_literal_elimination_wl :: \<open>isasat \<Rightarrow> isasat nres\<close> where
  \<open>isa_pure_literal_elimination_wl S\<^sub>0 = do {
    ASSERT (isa_pure_literal_elimination_wl_pre S\<^sub>0);
     max_rounds \<leftarrow> RETURN (3::nat);
    (S, _, _) \<leftarrow> WHILE\<^sub>T\<^bsup>isa_pure_literal_elimination_wl_inv S\<^sub>0 max_rounds\<^esup> (\<lambda>(S, m, abort). m < max_rounds \<and> \<not>abort)
     (\<lambda>(S, m, abort). do {
         ASSERT (m \<le> max_rounds);
         ASSERT (length (get_clauses_wl_heur S) = length (get_clauses_wl_heur S\<^sub>0));
         ASSERT (learned_clss_count S \<le> learned_clss_count S\<^sub>0);
         (elim, S) \<leftarrow> isa_pure_literal_elimination_round_wl S;
         abort \<leftarrow> RETURN (elim > 0);
         RETURN (S, m+1, abort)
       })
    (S\<^sub>0, 0, False);
   RETURN (schedule_next_pure_lits_st S)
  }\<close>

definition isa_pure_literal_eliminate :: \<open>isasat \<Rightarrow> isasat nres\<close> where
  \<open>isa_pure_literal_eliminate S = do {
    let b = should_eliminate_pure_st S;
    if b then isa_pure_literal_elimination_wl S else RETURN S
}\<close>

end