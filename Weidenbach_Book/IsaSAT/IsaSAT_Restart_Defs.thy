theory IsaSAT_Restart_Defs
  imports
    Watched_Literals.WB_Sort Watched_Literals.Watched_Literals_Watch_List_Simp IsaSAT_Rephase_State
    IsaSAT_Setup IsaSAT_VMTF IsaSAT_Sorting IsaSAT_Proofs
begin

lemma unbounded_id: \<open>unbounded (id :: nat \<Rightarrow> nat)\<close>
  by (auto simp: bounded_def) presburger

global_interpretation twl_restart_ops id
  by unfold_locales

global_interpretation twl_restart id
  by standard (rule unbounded_id)



definition twl_st_heur_restart :: \<open>(isasat \<times> nat twl_st_wl) set\<close> where
[unfolded Let_def]: \<open>twl_st_heur_restart =
  {(S,T).
  let M' = get_trail_wl_heur S; N' = get_clauses_wl_heur S; D' = get_conflict_wl_heur S;
    W' = get_watched_wl_heur S; j = literals_to_update_wl_heur S; outl = get_outlearned_heur S;
    cach = get_conflict_cach S; clvls = get_count_max_lvls_heur S;
    vm = get_vmtf_heur S;
    vdom = get_aivdom S; heur = get_heur S; old_arena = get_old_arena S;
    lcount = get_learned_count S; occs = get_occs S in
    let M = get_trail_wl T; N = get_clauses_wl T;  D = get_conflict_wl T;
      Q = literals_to_update_wl T;
      W = get_watched_wl T; N0 = get_init_clauses0_wl T; U0 = get_learned_clauses0_wl T;
      NS = get_subsumed_init_clauses_wl T; US = get_subsumed_learned_clauses_wl T;
      NEk = get_kept_unit_init_clss_wl T; UEk = get_kept_unit_learned_clss_wl T;
      NE = get_unkept_unit_init_clss_wl T; UE = get_unkept_unit_learned_clss_wl T in
    (M', M) \<in> trail_pol (all_init_atms N (NE+NEk+NS+N0)) \<and>
    valid_arena N' N (set (get_vdom_aivdom vdom)) \<and>
    (D', D) \<in> option_lookup_clause_rel (all_init_atms N (NE+NEk+NS+N0)) \<and>
    (D = None \<longrightarrow> j \<le> length M) \<and>
    Q = uminus `# lit_of `# mset (drop j (rev M)) \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 (all_init_atms N (NE+NEk+NS+N0))) \<and>
    vm \<in> isa_vmtf (all_init_atms N (NE+NEk+NS+N0)) M \<and>
    no_dup M \<and>
    clvls \<in> counts_maximum_level M D \<and>
    cach_refinement_empty (all_init_atms N (NE+NEk+NS+N0)) cach \<and>
    out_learned M D outl \<and>
    clss_size_corr_restart N NE {#} NEk UEk NS {#} N0 {#} lcount \<and>
    vdom_m (all_init_atms N (NE+NEk+NS+N0)) W N \<subseteq> set (get_vdom_aivdom vdom) \<and>
    aivdom_inv_dec vdom (dom_m N) \<and>
    isasat_input_bounded (all_init_atms N (NE+NEk+NS+N0)) \<and>
    isasat_input_nempty (all_init_atms N (NE+NEk+NS+N0)) \<and>
    old_arena = [] \<and>
      heuristic_rel (all_init_atms N (NE+NEk+NS+N0)) heur \<and>
    (occs, empty_occs_list (all_init_atms N (NE+NEk+NS+N0))) \<in> occurrence_list_ref
  }\<close>


abbreviation twl_st_heur'''' where
  \<open>twl_st_heur'''' r \<equiv> {(S, T). (S, T) \<in> twl_st_heur \<and> length (get_clauses_wl_heur S) \<le> r}\<close>

abbreviation twl_st_heur''''uu where
  \<open>twl_st_heur''''uu r u \<equiv> {(S, T). (S, T) \<in> twl_st_heur \<and> length (get_clauses_wl_heur S) \<le> r \<and>
    learned_clss_count S \<le> u}\<close>

abbreviation twl_st_heur_restart''' where
  \<open>twl_st_heur_restart''' r \<equiv>
    {(S, T). (S, T) \<in> twl_st_heur_restart \<and> length (get_clauses_wl_heur S) = r}\<close>

abbreviation twl_st_heur_restart'''' where
  \<open>twl_st_heur_restart'''' r \<equiv>
    {(S, T). (S, T) \<in> twl_st_heur_restart \<and> length (get_clauses_wl_heur S) \<le> r}\<close>

definition twl_st_heur_restart_ana :: \<open>nat \<Rightarrow> (isasat \<times> nat twl_st_wl) set\<close> where
\<open>twl_st_heur_restart_ana r =
  {(S, T). (S, T) \<in> twl_st_heur_restart \<and> length (get_clauses_wl_heur S) = r}\<close>

abbreviation twl_st_heur_restart_ana' :: \<open>_\<close> where
  \<open>twl_st_heur_restart_ana' r u \<equiv>
    {(S, T). (S, T) \<in> twl_st_heur_restart_ana r \<and> learned_clss_count S \<le> u}\<close>

definition empty_Q :: \<open>isasat \<Rightarrow> isasat nres\<close> where
  \<open>empty_Q = (\<lambda>S. do{
  j \<leftarrow> mop_isa_length_trail (get_trail_wl_heur S);
  RETURN (set_heur_wl_heur (restart_info_restart_done_heur (get_heur S)) (set_literals_to_update_wl_heur j S))
  })\<close>

definition remove_all_annot_true_clause_one_imp_heur
  :: \<open>nat \<times> clss_size \<times> arena \<Rightarrow> (clss_size \<times> arena) nres\<close>
where
\<open>remove_all_annot_true_clause_one_imp_heur = (\<lambda>(C, j, N). do {
      case arena_status N C of
        DELETED \<Rightarrow> RETURN (j, N)
      | IRRED \<Rightarrow> RETURN (j, extra_information_mark_to_delete N C)
      | LEARNED \<Rightarrow> RETURN (clss_size_decr_lcount j, extra_information_mark_to_delete N C)
  })\<close>

definition number_clss_to_keep :: \<open>isasat \<Rightarrow> nat nres\<close> where
  \<open>number_clss_to_keep = (\<lambda>S.
    RES UNIV)\<close>

definition number_clss_to_keep_impl :: \<open>isasat \<Rightarrow> nat nres\<close> where
  \<open>number_clss_to_keep_impl = (\<lambda>S.
    RETURN (length_tvdom_aivdom (get_aivdom S) >> 2))\<close>

(* TODO Missing : The sorting function + definition of l should depend on the number of initial
  clauses *)
definition (in -) MINIMUM_DELETION_LBD :: nat where
  \<open>MINIMUM_DELETION_LBD = 3\<close>

definition trail_update_reason_at :: \<open>_ \<Rightarrow> _ \<Rightarrow> trail_pol \<Rightarrow> _\<close> where
  \<open>trail_update_reason_at \<equiv> (\<lambda>L C (M, val, lvls, reason, k). (M, val, lvls, reason[atm_of L := C], k))\<close>

abbreviation trail_get_reason :: \<open>trail_pol \<Rightarrow> _\<close> where
  \<open>trail_get_reason \<equiv> (\<lambda>(M, val, lvls, reason, k). reason)\<close>

definition replace_reason_in_trail :: \<open>nat literal \<Rightarrow> _\<close> where
  \<open>replace_reason_in_trail L C = (\<lambda>M. do {
    ASSERT(atm_of L < length (trail_get_reason M));
    RETURN (trail_update_reason_at L 0 M)
  })\<close>

definition isasat_replace_annot_in_trail
  :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> isasat \<Rightarrow> isasat nres\<close>
  where
  \<open>isasat_replace_annot_in_trail L C = (\<lambda>S. do {
    let lcount = clss_size_resetUS0 (get_learned_count S);
    M \<leftarrow> replace_reason_in_trail L C (get_trail_wl_heur S);
    RETURN (set_trail_wl_heur M (set_learned_count_wl_heur lcount S))
  })\<close>

definition remove_one_annot_true_clause_one_imp_wl_D_heur
  :: \<open>nat \<Rightarrow> isasat \<Rightarrow> (nat \<times> isasat) nres\<close>
where
\<open>remove_one_annot_true_clause_one_imp_wl_D_heur = (\<lambda>i S\<^sub>0. do {
      (L, C) \<leftarrow> do {
        L \<leftarrow> isa_trail_nth (get_trail_wl_heur S\<^sub>0) i;
	C \<leftarrow> get_the_propagation_reason_pol (get_trail_wl_heur S\<^sub>0) L;
	RETURN (L, C)};
      ASSERT(C \<noteq> None \<and> i + 1 \<le> Suc (uint32_max div 2));
      if the C = 0 then RETURN (i+1, S\<^sub>0)
      else do {
        ASSERT(C \<noteq> None);
        S \<leftarrow> isasat_replace_annot_in_trail L (the C) S\<^sub>0;
        log_del_clause_heur S (the C);
	ASSERT(mark_garbage_pre (get_clauses_wl_heur S, the C) \<and> arena_is_valid_clause_vdom (get_clauses_wl_heur S) (the C) \<and> learned_clss_count S \<le> learned_clss_count S\<^sub>0);
        S \<leftarrow> mark_garbage_heur4 (the C) S;
        \<comment> \<open>\<^text>\<open>S \<leftarrow> remove_all_annot_true_clause_imp_wl_D_heur L S;\<close>\<close>
        RETURN (i+1, S)
      }
  })\<close>

definition cdcl_twl_full_restart_wl_D_GC_prog_heur_post :: \<open>isasat \<Rightarrow> isasat \<Rightarrow> bool\<close> where
\<open>cdcl_twl_full_restart_wl_D_GC_prog_heur_post S T \<longleftrightarrow>
  (\<exists>S' T'. (S, S') \<in> twl_st_heur_restart \<and> (T, T') \<in> twl_st_heur_restart \<and>
    cdcl_twl_full_restart_wl_GC_prog_post S' T')\<close>

definition remove_one_annot_true_clause_imp_wl_D_heur_inv
  :: \<open>isasat \<Rightarrow> (nat \<times> isasat) \<Rightarrow> bool\<close> where
  \<open>remove_one_annot_true_clause_imp_wl_D_heur_inv S = (\<lambda>(i, T).
    (\<exists>S' T'. (S, S') \<in> twl_st_heur_restart \<and> (T, T') \<in> twl_st_heur_restart \<and>
     remove_one_annot_true_clause_imp_wl_inv S' (i, T') \<and>
     learned_clss_count T \<le> learned_clss_count S))\<close>

definition empty_US  :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>empty_US = (\<lambda>(M', N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W).
  (M', N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W))\<close>




definition remove_one_annot_true_clause_imp_wl_D_heur :: \<open>isasat \<Rightarrow> isasat nres\<close>
where
\<open>remove_one_annot_true_clause_imp_wl_D_heur = (\<lambda>S. do {
    ASSERT((isa_length_trail_pre o get_trail_wl_heur) S);
    k \<leftarrow> (if count_decided_st_heur S = 0
      then RETURN (isa_length_trail (get_trail_wl_heur S))
      else get_pos_of_level_in_trail_imp (get_trail_wl_heur S) 0);
    (_, S) \<leftarrow> WHILE\<^sub>T\<^bsup>remove_one_annot_true_clause_imp_wl_D_heur_inv S\<^esup>
      (\<lambda>(i, S). i < k)
      (\<lambda>(i, S). remove_one_annot_true_clause_one_imp_wl_D_heur i S)
      (0, S);
    RETURN (empty_US_heur S)
  })\<close>

definition GC_units_required :: \<open>isasat \<Rightarrow> bool\<close> where
  \<open>GC_units_required T \<longleftrightarrow> units_since_last_GC_st T \<ge> get_GC_units_opt T\<close>


definition FLAG_no_restart :: \<open>8 word\<close> where
  \<open>FLAG_no_restart = 0\<close>

definition FLAG_restart :: \<open>8 word\<close> where
  \<open>FLAG_restart = 1\<close>

definition FLAG_Reduce_restart :: \<open>8 word\<close> where
  \<open>FLAG_Reduce_restart = 3\<close>

definition FLAG_GC_restart :: \<open>8 word\<close> where
  \<open>FLAG_GC_restart = 2\<close>

definition FLAG_Inprocess_restart :: \<open>8 word\<close> where
  \<open>FLAG_Inprocess_restart = 4\<close>


definition max_restart_decision_lvl :: nat where
  \<open>max_restart_decision_lvl = 300\<close>

definition max_restart_decision_lvl_code :: \<open>32 word\<close> where
  \<open>max_restart_decision_lvl_code = 300\<close>

definition GC_required_heur :: \<open>isasat \<Rightarrow> nat \<Rightarrow> bool nres\<close> where
  \<open>GC_required_heur S n = do {
    n \<leftarrow> RETURN (full_arena_length_st S);
    wasted \<leftarrow> RETURN (wasted_bytes_st S);
    RETURN (3*wasted > ((of_nat n)>>2))
 }\<close>

definition minimum_number_between_restarts :: \<open>64 word\<close> where
  \<open>minimum_number_between_restarts = 50\<close>

definition upper_restart_bound_reached :: \<open>isasat \<Rightarrow> bool\<close> where
  \<open>upper_restart_bound_reached = (\<lambda>S. get_global_conflict_count S \<ge> next_reduce_schedule_st S)\<close>

definition should_subsume_st :: \<open>isasat \<Rightarrow> bool\<close> where
  \<open>should_subsume_st S \<longleftrightarrow> get_subsumption_opts S \<and>
      (get_global_conflict_count S > next_subsume_schedule_st S)\<close>

definition should_eliminate_pure_st :: \<open>isasat \<Rightarrow> bool\<close> where
  \<open>should_eliminate_pure_st S \<longleftrightarrow>
      (get_global_conflict_count S > next_inprocessing_schedule_st S)\<close>

definition should_inprocess_st :: \<open>isasat \<Rightarrow> bool\<close> where
  \<open>should_inprocess_st S \<longleftrightarrow>
      (should_subsume_st S \<or> should_eliminate_pure_st S)\<close>

definition iterate_over_VMTFC where
  \<open>iterate_over_VMTFC = (\<lambda>f (I :: 'a \<Rightarrow> bool) P (ns :: (nat, nat) vmtf_node list, n) x. do {
      (_, x) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(n, x). I x\<^esup>
        (\<lambda>(n, x). n \<noteq> None \<and> P x)
        (\<lambda>(n, x). do {
          ASSERT(n \<noteq> None);
          let A = the n;
          ASSERT(A < length ns);
          ASSERT(A \<le> uint32_max div 2);
          x \<leftarrow> f A x;
          RETURN (get_next ((ns ! A)), x)
        })
        (n, x);
      RETURN x
    })\<close>

definition iterate_over_VMTF :: \<open>_\<close> where
  iterate_over_VMTF_alt_def: \<open>iterate_over_VMTF f I  = iterate_over_VMTFC f I (\<lambda>_. True)\<close>

definition arena_header_size :: \<open>arena \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>arena_header_size arena C =
  (if arena_length arena C > 4 then MAX_HEADER_SIZE else MIN_HEADER_SIZE)\<close>

definition update_restart_phases :: \<open>isasat \<Rightarrow> isasat nres\<close> where
  \<open>update_restart_phases = (\<lambda>S. do {
     let heur = get_heur S;
     heur \<leftarrow> RETURN (incr_restart_phase heur);
     heur \<leftarrow> RETURN (incr_restart_phase_end heur);
     heur \<leftarrow> RETURN (if current_restart_phase heur = STABLE_MODE then heuristic_reluctant_enable heur else heuristic_reluctant_disable heur);
     RETURN (set_heur_wl_heur heur S)
  })\<close>


(*TODO used: in Restart_Reduce_Defs only?*)
definition restart_abs_wl_heur_pre  :: \<open>isasat \<Rightarrow> bool \<Rightarrow> bool\<close> where
  \<open>restart_abs_wl_heur_pre S brk  \<longleftrightarrow> (\<exists>T last_GC last_Restart. (S, T) \<in> twl_st_heur \<and> restart_abs_wl_pre T last_GC last_Restart brk)\<close>

lemma valid_arena_header_size:
  \<open>valid_arena arena N vdom \<Longrightarrow> C \<in># dom_m N \<Longrightarrow> arena_header_size arena C = header_size (N \<propto> C)\<close>
  by (auto simp: arena_header_size_def header_size_def arena_lifting)


definition rewatch_heur_st_pre :: \<open>isasat \<Rightarrow> bool\<close> where
  \<open>rewatch_heur_st_pre S \<longleftrightarrow> (\<forall>i < length (get_tvdom S). get_tvdom S ! i \<le> sint64_max)\<close>

lemma isasat_GC_clauses_wl_D_rewatch_pre:
  assumes
    \<open>length (get_clauses_wl_heur x) \<le> sint64_max\<close> and
    \<open>length (get_clauses_wl_heur xc) \<le> length (get_clauses_wl_heur x)\<close> and
    \<open>\<forall>i \<in> set (get_tvdom xc). i \<le> length (get_clauses_wl_heur x)\<close>
  shows \<open>rewatch_heur_st_pre xc\<close>
  using assms
  unfolding rewatch_heur_st_pre_def all_set_conv_all_nth
  by auto

end