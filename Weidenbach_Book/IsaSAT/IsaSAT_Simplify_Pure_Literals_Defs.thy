theory IsaSAT_Simplify_Pure_Literals_Defs
  imports IsaSAT_Setup
    IsaSAT_Restart_Defs
begin
  definition isa_pure_literal_count_occs_clause_wl_invs :: \<open>_\<close> where
  \<open>isa_pure_literal_count_occs_clause_wl_invs C S occs =
  (\<lambda>(i, occs2, remaining). \<exists>S' r u occs' occs2'. (S, S') \<in> twl_st_heur_restart_ana' r u \<and>
    (occs, occs') \<in> \<langle>bool_rel\<rangle>map_fun_rel (D\<^sub>0 (all_init_atms_st S')) \<and>
    (occs2, occs2') \<in> \<langle>bool_rel\<rangle>map_fun_rel (D\<^sub>0 (all_init_atms_st S')) \<and>
    pure_literal_count_occs_clause_wl_invs C S' occs' (i, occs2'))\<close>

definition isa_pure_literal_count_occs_clause_wl_pre :: \<open>_\<close> where
  \<open>isa_pure_literal_count_occs_clause_wl_pre C S occs =
  (\<exists>S' r u occs'. (S, S') \<in> twl_st_heur_restart_ana' r u \<and>
    (occs, occs') \<in> \<langle>bool_rel\<rangle>map_fun_rel (D\<^sub>0 (all_init_atms_st S')) \<and>
    pure_literal_count_occs_clause_wl_pre C S' occs')\<close>

definition isa_pure_literal_count_occs_clause_wl :: \<open>nat \<Rightarrow> isasat \<Rightarrow> _ \<Rightarrow> 64 word \<Rightarrow> _\<close> where
  \<open>isa_pure_literal_count_occs_clause_wl C S occs remaining = do {
    ASSERT (isa_pure_literal_count_occs_clause_wl_pre C S occs);
    m \<leftarrow> mop_arena_length_st S C;
    (i, occs, _) \<leftarrow> WHILE\<^sub>T\<^bsup>isa_pure_literal_count_occs_clause_wl_invs C S occs\<^esup> (\<lambda>(i, occs, remaining). i < m)
      (\<lambda>(i, occs, remaining). do {
        ASSERT (i < m);
        L \<leftarrow> mop_access_lit_in_clauses_heur S C i;
        ASSERT (nat_of_lit L < length occs);
        ASSERT (nat_of_lit (-L) < length occs);
        let remaining = (if \<not>occs!(nat_of_lit L) \<and> occs ! (nat_of_lit (-L)) then remaining-1 else remaining);
        let occs = occs [nat_of_lit L := True];
        RETURN (i+1, occs, remaining)
      })
      (0, occs, remaining);
   RETURN (occs, remaining)
 }\<close>

definition isa_pure_literal_count_occs_wl :: \<open>isasat \<Rightarrow> _\<close> where
  \<open>isa_pure_literal_count_occs_wl S = do {
  let xs = get_avdom S @ get_ivdom S;
  let m = length (xs);
  let remaining = ((of_nat (length (get_watched_wl_heur S)) :: 64 word) >> 1) - units_since_beginning_st S;
  let abort = (remaining \<le> 0);
  let occs = replicate (length (get_watched_wl_heur S)) False;
  ASSERT (m \<le> length (get_clauses_wl_heur S) - 2);
  (_, occs, abort) \<leftarrow> WHILE\<^sub>T(\<lambda>(i, occs, remaining). i < m \<and> remaining > 0)
      (\<lambda>(i, occs, remaining). do {
        ASSERT (i \<le> length (get_clauses_wl_heur S) - 2);
        ASSERT ((i < length (get_avdom S) \<longrightarrow> access_avdom_at_pre S i) \<and>
           (i \<ge> length (get_avdom S) \<longrightarrow> access_ivdom_at_pre S (i - length_avdom S)));
        let C = (get_avdom S @ get_ivdom S) ! i;
        E \<leftarrow> mop_arena_status (get_clauses_wl_heur S) C;
        if (E = IRRED) then do {
          (occs, remaining) \<leftarrow> isa_pure_literal_count_occs_clause_wl C S occs remaining;
          let abort = (remaining \<le> 0);
          RETURN (i+1, occs, remaining)
        } else RETURN  (i+1, occs, remaining)
      })
      (0, occs, remaining);
   RETURN (abort \<le> 0, occs)
  }\<close>


definition isa_pure_literal_elimination_round_wl_pre where
  \<open>isa_pure_literal_elimination_round_wl_pre S \<longleftrightarrow>
  (\<exists>T r u. (S, T) \<in> twl_st_heur_restart_ana' r u \<and> pure_literal_elimination_round_wl_pre T)\<close>

definition isa_pure_literal_deletion_wl_pre :: \<open>_\<close> where
  \<open>isa_pure_literal_deletion_wl_pre S \<longleftrightarrow>
  (\<exists>T r u. (S, T) \<in> twl_st_heur_restart_ana' r u \<and> pure_literal_deletion_wl_pre T)\<close>


definition isa_propagate_pure_bt_wl
  :: \<open>nat literal \<Rightarrow> isasat \<Rightarrow> isasat nres\<close>
  where
    \<open>isa_propagate_pure_bt_wl = (\<lambda>L S. do {
      let M = get_trail_wl_heur S;
      let stats = get_stats_heur S;
      ASSERT(0 \<noteq> DECISION_REASON);
      ASSERT(cons_trail_Propagated_tr_pre ((L, 0::nat), M));
      M \<leftarrow> cons_trail_Propagated_tr (L) 0 M;
      let stats = incr_units_since_last_GC (incr_uset (incr_purelit_elim stats));
      let S = set_stats_wl_heur stats S;
      let S = set_trail_wl_heur M S;
      RETURN S})
\<close>



definition isa_pure_literal_deletion_wl_raw :: \<open>bool list \<Rightarrow> isasat \<Rightarrow> (64 word \<times> isasat) nres\<close> where
  \<open>isa_pure_literal_deletion_wl_raw occs S\<^sub>0 = (do {
    ASSERT (isa_pure_literal_deletion_wl_pre S\<^sub>0);
    (eliminated, S) \<leftarrow> iterate_over_VMTF
      (\<lambda>A (eliminated, T). do {
         ASSERT (get_vmtf_heur_array S\<^sub>0 = get_vmtf_heur_array T);
         ASSERT (nat_of_lit (Pos A) < length occs);
         ASSERT (nat_of_lit (Neg A) < length occs);
         let L = (if occs ! (nat_of_lit (Pos A)) \<and> \<not> occs ! (nat_of_lit (Neg A))
                  then Pos A else Neg A);
         ASSERT (nat_of_lit (-L) < length occs);
         val \<leftarrow> mop_polarity_pol (get_trail_wl_heur T) L;
         if \<not>occs ! (nat_of_lit (-L)) \<and> val = None
         then do {S \<leftarrow> isa_propagate_pure_bt_wl L T;
          ASSERT (get_vmtf_heur_array S\<^sub>0 = get_vmtf_heur_array S);
          RETURN (eliminated + 1, S)}
        else RETURN (eliminated, T)
      })
     (\<lambda>(_, S). get_vmtf_heur_array S\<^sub>0 = (get_vmtf_heur_array S))
     (get_vmtf_heur_array S\<^sub>0, Some (get_vmtf_heur_fst S\<^sub>0)) (0 :: 64 word, S\<^sub>0);
   RETURN (eliminated, S)
})\<close>

definition isa_pure_literal_deletion_wl :: \<open>bool list \<Rightarrow> isasat \<Rightarrow> (64 word \<times> isasat) nres\<close> where
  \<open>isa_pure_literal_deletion_wl occs S\<^sub>0 = (do {
  ASSERT (isa_pure_literal_deletion_wl_pre S\<^sub>0);
  (_, eliminated, S) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(n, _, S). get_vmtf_heur_array S\<^sub>0 = get_vmtf_heur_array S\<^esup> (\<lambda>(n, x). n \<noteq> None)
    (\<lambda>(n, eliminated, T). do {
       ASSERT (n \<noteq> None);
       let A = the n;
       ASSERT (A < length (get_vmtf_heur_array S\<^sub>0));
       ASSERT (A \<le> unat32_max div 2);
       ASSERT (get_vmtf_heur_array S\<^sub>0 = get_vmtf_heur_array T);
       ASSERT (nat_of_lit (Pos A) < length occs);
       ASSERT (nat_of_lit (Neg A) < length occs);
       let L = (if occs ! nat_of_lit (Pos A) \<and> \<not> occs ! nat_of_lit (Neg A) then Pos A else Neg A);
       ASSERT (nat_of_lit (- L) < length occs);
       val \<leftarrow> mop_polarity_pol (get_trail_wl_heur T) L;
       if \<not> occs ! nat_of_lit (- L) \<and> val = None then do {
          S \<leftarrow> isa_propagate_pure_bt_wl L T;
          ASSERT (get_vmtf_heur_array S\<^sub>0 = get_vmtf_heur_array S);
          RETURN (get_next (get_vmtf_heur_array S ! A),eliminated + 1, S)
       }
       else RETURN (get_next (get_vmtf_heur_array T ! A),eliminated, T)
     })
    (Some (get_vmtf_heur_fst S\<^sub>0), 0, S\<^sub>0);
  RETURN (eliminated, S)
})\<close>


end