theory IsaSAT_Simplify_Forward_Subsumption_Defs
  imports IsaSAT_Setup
    IsaSAT_Occurence_List
    IsaSAT_Restart
    IsaSAT_LBD
begin

section \<open>Forward subsumption\<close>

subsection \<open>Algorithm\<close>

text \<open>We first refine the algorithm to use occurence lists, while keeping as many things as possible
  abstract (like the candidate selection or the selection of the literal with the least number
  of occurrences). We also include the marking structure (at least abstractly, because why not)

  For simplicity, we keep the occurrence list outside of the state (unlike the current solver where
  this is part of the state.)\<close>

definition valid_occs where \<open>valid_occs occs vdom \<longleftrightarrow> cocc_content_set occs \<subseteq> set (get_vdom_aivdom vdom) \<and>
  distinct_mset (cocc_content occs)\<close>

text \<open>This version is equivalent to \<^term>\<open>twl_st_heur_restart\<close>, without any information on the occurrence list.\<close>
definition twl_st_heur_restart_occs :: \<open>(isasat \<times> nat twl_st_wl) set\<close> where
[unfolded Let_def]: \<open>twl_st_heur_restart_occs =
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
    vm \<in> bump_heur (all_init_atms N (NE+NEk+NS+N0)) M \<and>
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
    valid_occs occs vdom
  }\<close>

abbreviation twl_st_heur_restart_occs' :: \<open>_\<close> where
  \<open>twl_st_heur_restart_occs' r u \<equiv>
    {(S, T). (S, T) \<in> twl_st_heur_restart_occs \<and> length (get_clauses_wl_heur S) = r \<and> learned_clss_count S \<le> u}\<close>


definition subsume_clauses_match2_pre :: \<open>nat \<Rightarrow> nat \<Rightarrow> _ \<Rightarrow> clause_hash \<Rightarrow> bool\<close> where
  \<open>subsume_clauses_match2_pre C C' N D  \<longleftrightarrow>
  subsume_clauses_match_pre C C' (get_clauses_wl N) \<and>
  snd D = mset (get_clauses_wl N \<propto> C')\<close>

definition subsume_clauses_match2 :: \<open>nat \<Rightarrow> nat \<Rightarrow> _ \<Rightarrow> clause_hash \<Rightarrow> nat subsumption nres\<close> where
  \<open>subsume_clauses_match2 C C' N D = do {
  ASSERT (subsume_clauses_match2_pre C C' N D);
  let n = length (get_clauses_wl N \<propto> C);
  (i, st) \<leftarrow> WHILE\<^sub>T\<^bsup> \<lambda>(i,s). try_to_subsume C' C ((get_clauses_wl N)(C \<hookrightarrow> take i (get_clauses_wl N \<propto> C))) s\<^esup> (\<lambda>(i, st). i < n\<and> st \<noteq> NONE)
    (\<lambda>(i, st). do {
      L \<leftarrow> mop_clauses_at (get_clauses_wl N) C i;
      lin \<leftarrow> mop_ch_in L D;
      if lin
      then RETURN (i+1, st)
     else do {
      lin \<leftarrow> mop_ch_in (-L) D;
      if lin
      then if is_subsumed st
      then RETURN (i+1, STRENGTHENED_BY L C)
      else RETURN (i+1, NONE)
      else RETURN (i+1, NONE)
    }})
     (0, SUBSUMED_BY C);
  RETURN st
  }\<close>

definition push_to_occs_list2_pre :: \<open>_\<close> where
  \<open>push_to_occs_list2_pre C S occs \<longleftrightarrow>
  (C \<in># dom_m (get_clauses_wl S) \<and> length (get_clauses_wl S \<propto> C) \<ge> 2 \<and> fst occs = set_mset (all_init_atms_st S) \<and>
    atm_of ` set (get_clauses_wl S \<propto> C) \<subseteq> set_mset (all_init_atms_st S) \<and>
    C \<notin># all_occurrences (mset_set (fst occs)) occs)\<close>

definition push_to_occs_list2 where
  \<open>push_to_occs_list2 C S occs = do {
     ASSERT (push_to_occs_list2_pre C S occs);
     L \<leftarrow> SPEC (\<lambda>L. L \<in># mset (get_clauses_wl S \<propto> C));
     mop_occ_list_append C occs L
  }\<close>

definition maybe_push_to_occs_list2 where
  \<open>maybe_push_to_occs_list2 C S occs = do {
     ASSERT (push_to_occs_list2_pre C S occs);
     b \<leftarrow> SPEC (\<lambda>_. True);
     if b then do {
       L \<leftarrow> SPEC (\<lambda>L. L \<in># mset (get_clauses_wl S \<propto> C));
       mop_occ_list_append C occs L
    } else RETURN occs
  }\<close>

definition isa_is_candidate_forward_subsumption where
  \<open>isa_is_candidate_forward_subsumption S C = do {
    ASSERT(arena_act_pre (get_clauses_wl_heur S) C);
    lbd \<leftarrow> mop_arena_lbd (get_clauses_wl_heur S) C;
    sze \<leftarrow> mop_arena_length (get_clauses_wl_heur S) C;
    status \<leftarrow> mop_arena_status (get_clauses_wl_heur S) C;
    ASSERT (sze \<le> length (get_clauses_wl_heur S));
    (_, added) \<leftarrow> WHILE\<^sub>T (\<lambda>(i, added). i < sze \<and> added \<le> 2)
       (\<lambda>(i, added). do {
           ASSERT (i < sze);
           L \<leftarrow> mop_arena_lit2 (get_clauses_wl_heur S) C i;
           is_added \<leftarrow> mop_is_marked_added_heur (get_heur S) (atm_of L);
           RETURN (i+1, added + (if is_added then 1 else 0))
    }) (0, 0 :: 64 word);
    let (lbd_limit, size_limit) = get_lsize_limit_stats_st S;
    let can_del =
       sze \<noteq> 2 \<and> (status = LEARNED \<longrightarrow> lbd \<le> lbd_limit \<and> sze \<le> size_limit) \<and> (added \<ge> 2);
    RETURN can_del
  }\<close>

definition find_best_subsumption_candidate where
  \<open>find_best_subsumption_candidate C S = do {
    L \<leftarrow> mop_arena_lit2 (get_clauses_wl_heur S) C 0;
    ASSERT (nat_of_lit L < length (get_occs S));
    score \<leftarrow> mop_cocc_list_length (get_occs S) L;
    n \<leftarrow> mop_arena_length_st S C;
   (i,score,L) \<leftarrow> WHILE\<^sub>T (\<lambda>(i,score,L). i < n)
     (\<lambda>(i,score,L). do {
       ASSERT (Suc i \<le> unat32_max);
       new_L \<leftarrow> mop_arena_lit2 (get_clauses_wl_heur S) C i;
       ASSERT (nat_of_lit L < length (get_occs S));
       new_score \<leftarrow> mop_cocc_list_length (get_occs S) L;
       if new_score < score then RETURN (i+1, new_score, new_L) else RETURN (i+1, score, L)
    })
    (1, score, L);
    RETURN L
  }\<close>

definition isa_push_to_occs_list_st where
  \<open>isa_push_to_occs_list_st C S = do {
     L \<leftarrow> find_best_subsumption_candidate C S;
     ASSERT (length (get_occs S ! nat_of_lit L) < length (get_clauses_wl_heur S));
     occs \<leftarrow> mop_cocc_list_append C (get_occs S) L;
     RETURN (set_occs_wl_heur occs S)
  }\<close>


definition find_best_subsumption_candidate_and_push where
  \<open>find_best_subsumption_candidate_and_push C S = do {
    L \<leftarrow> mop_arena_lit2 (get_clauses_wl_heur S) C 0;
    ASSERT (nat_of_lit L < length (get_occs S));
    score \<leftarrow> mop_cocc_list_length (get_occs S) L;
    n \<leftarrow> mop_arena_length_st S C;
   (i,score,L,push) \<leftarrow> WHILE\<^sub>T (\<lambda>(i,score,L,push). i < n \<and> push)
     (\<lambda>(i,score,L,push). do {
       ASSERT (Suc i \<le> unat32_max);
       new_L \<leftarrow> mop_arena_lit2 (get_clauses_wl_heur S) C i;
       ASSERT (nat_of_lit L < length (get_occs S));
       new_score \<leftarrow> mop_cocc_list_length (get_occs S) L;
       b \<leftarrow> mop_is_marked_added_heur (get_heur S) (atm_of L);
       if new_score < score then RETURN (i+1, new_score, new_L,b) else RETURN (i+1, score, L,b)
    })
    (1, score, L, True);
    RETURN (L, push)
  }\<close>

definition isa_maybe_push_to_occs_list_st where
  \<open>isa_maybe_push_to_occs_list_st C S = do {
     (L, push) \<leftarrow> find_best_subsumption_candidate_and_push C S;
     if push then do {
       let L = L;
       ASSERT (length (get_occs S ! nat_of_lit L) < length (get_clauses_wl_heur S));
       occs \<leftarrow> mop_cocc_list_append C (get_occs S) L;
       RETURN (set_occs_wl_heur occs S)
     } else RETURN S
  }\<close>

definition forward_subsumption_one_wl2_pre :: \<open>nat \<Rightarrow> nat multiset \<Rightarrow> nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> bool\<close> where
  \<open>forward_subsumption_one_wl2_pre = (\<lambda>C cands L S.
  forward_subsumption_one_wl_pre C cands S \<and> L \<in># all_init_lits_of_wl S)\<close>

definition isa_forward_subsumption_one_wl_pre :: \<open>_\<close> where
  \<open>isa_forward_subsumption_one_wl_pre C L S \<longleftrightarrow>
  (\<exists>T r u cands. (S,T)\<in>twl_st_heur_restart_occs' r u \<and> forward_subsumption_one_wl2_pre C cands L T) \<close>

definition forward_subsumption_one_wl2_inv :: \<open>'v twl_st_wl \<Rightarrow> nat \<Rightarrow> nat multiset \<Rightarrow> nat list \<Rightarrow>
  nat \<times> 'v subsumption \<Rightarrow> bool\<close> where
  \<open>forward_subsumption_one_wl2_inv = (\<lambda>S C cands ys (i, x). forward_subsumption_one_wl_inv S C (mset ys) (mset (drop i ys), x))\<close>

definition isa_forward_subsumption_one_wl2_inv :: \<open>isasat \<Rightarrow> nat \<Rightarrow> nat literal \<Rightarrow>
  nat \<times> nat subsumption \<Rightarrow> bool\<close> where
  \<open>isa_forward_subsumption_one_wl2_inv = (\<lambda>S C L (ix).
  (\<exists>T r u cands. (S,T)\<in>twl_st_heur_restart_occs' r u \<and>
    forward_subsumption_one_wl2_inv T C cands (get_occs S ! nat_of_lit L) (ix)))\<close>

definition isa_subsume_clauses_match2_pre :: \<open>_\<close> where
  \<open>isa_subsume_clauses_match2_pre C C' S D \<longleftrightarrow> (
  \<exists>T r u D'. (S,T)\<in>twl_st_heur_restart_occs' r u \<and> subsume_clauses_match2_pre C C' T D' \<and>
    (D,D') \<in> clause_hash) \<close>

definition isa_subsume_clauses_match2 :: \<open>nat \<Rightarrow> nat \<Rightarrow> isasat \<Rightarrow> bool list \<Rightarrow> nat subsumption nres\<close> where
  \<open>isa_subsume_clauses_match2 C' C N D = do {
  ASSERT (isa_subsume_clauses_match2_pre C' C N D);
  n \<leftarrow> mop_arena_length_st N C';
  ASSERT (n \<le> length (get_clauses_wl_heur N));
  (i, st) \<leftarrow> WHILE\<^sub>T\<^bsup> \<lambda>(i,s). True\<^esup> (\<lambda>(i, st). i < n\<and> st \<noteq> NONE)
    (\<lambda>(i, st). do {
      ASSERT (i < n);
      L \<leftarrow> mop_arena_lit2 (get_clauses_wl_heur N) C' i;
      lin \<leftarrow> mop_cch_in L D;
      if lin
      then RETURN (i+1, st)
      else do {
      lin \<leftarrow> mop_cch_in (-L) D;
      if lin
      then if is_subsumed st
      then do {RETURN (i+1, STRENGTHENED_BY L C')}
      else do {RETURN (i+1, NONE)}
      else do {RETURN (i+1, NONE)}
    }})
     (0, SUBSUMED_BY C');
  RETURN st
  }\<close>

definition isa_subsume_or_strengthen_wl_pre :: \<open>_\<close> where
  \<open>isa_subsume_or_strengthen_wl_pre C s S \<longleftrightarrow>
   (\<exists>T r u.  (S,T)\<in>twl_st_heur_restart_occs' r u \<and> subsume_or_strengthen_wl_pre C s T)\<close>


definition remove_lit_from_clause where
  \<open>remove_lit_from_clause N C L = do {
    n \<leftarrow> mop_arena_length N C;
   (i, j, N) \<leftarrow> WHILE\<^sub>T (\<lambda>(i, j, N). j < n)
     (\<lambda>(i, j, N). do {
       ASSERT (i < n);
       ASSERT (j < n);
       K \<leftarrow> mop_arena_lit2 N C j;
       if K \<noteq> L then do {
         N \<leftarrow> mop_arena_swap C i j N;
         RETURN (i+1, j+1, N)}
      else RETURN (i, j+1, N)
    }) (0, 0, N);
   N \<leftarrow> mop_arena_shorten C i N;
   N \<leftarrow> update_lbd_shrunk_clause C N;
   RETURN N
  }\<close>

definition remove_lit_from_clause_st :: \<open>_\<close> where
  \<open>remove_lit_from_clause_st T C L = do {
    N \<leftarrow> remove_lit_from_clause (get_clauses_wl_heur T) C L;
    RETURN (set_clauses_wl_heur N T)
}\<close>
(*
TODO the wasted bits should be incremented in the deletion functions
TODO rename the mark_garbage_heurX functions with proper name like below
*)
definition mark_garbage_heur_as_subsumed :: \<open>nat \<Rightarrow> isasat \<Rightarrow> isasat nres\<close> where
  \<open>mark_garbage_heur_as_subsumed C S = (do{
    let N' = get_clauses_wl_heur S;
    ASSERT (arena_is_valid_clause_vdom N' C);
    _ \<leftarrow> log_del_clause_heur S C;
    let st = arena_status N' C = IRRED;
    ASSERT (mark_garbage_pre (N', C));
    let N' = extra_information_mark_to_delete (N') C;
    size \<leftarrow> mop_arena_length (get_clauses_wl_heur S) C;
    let lcount = get_learned_count S;
    ASSERT(\<not>st \<longrightarrow> clss_size_lcount lcount \<ge> 1);
    let lcount = (if st then lcount else (clss_size_decr_lcount lcount));
    let stats = get_stats_heur S;
    let stats = (if st then decr_irred_clss stats else stats);
    let S = set_clauses_wl_heur N' S;
    let S = set_learned_count_wl_heur lcount S;
    let S = set_stats_wl_heur stats S;
    let S = incr_wasted_st (of_nat size) S;
    RETURN S
  })\<close>

definition isa_strengthen_clause_wl2 where
  \<open>isa_strengthen_clause_wl2 C C' L S = do {
    m \<leftarrow> mop_arena_length (get_clauses_wl_heur S) C;
    n \<leftarrow> mop_arena_length (get_clauses_wl_heur S) C';
    st1 \<leftarrow> mop_arena_status (get_clauses_wl_heur S) C;
    st2 \<leftarrow> mop_arena_status (get_clauses_wl_heur S) C';
    S \<leftarrow> remove_lit_from_clause_st S C (-L);
    _ \<leftarrow> log_new_clause_heur S C;
    let _ = mark_clause_for_unit_as_changed 0;
    if m = n
    then do {
      S \<leftarrow> RETURN S;
      S \<leftarrow> (if st1 = LEARNED \<and> st2 = IRRED then mop_arena_promote_st S C else RETURN S);
      S \<leftarrow> mark_garbage_heur_as_subsumed C' S;
       RETURN (set_stats_wl_heur (incr_forward_strengethening (get_stats_heur S)) S)
    }
    else
     RETURN (set_stats_wl_heur (incr_forward_strengethening (get_stats_heur S)) S)
  }\<close>

definition incr_forward_subsumed_st  :: \<open>_\<close> where
  \<open>incr_forward_subsumed_st S = (set_stats_wl_heur (incr_forward_subsumed (get_stats_heur S)) S)\<close>

definition incr_forward_tried_st  :: \<open>_\<close> where
  \<open>incr_forward_tried_st S = (set_stats_wl_heur (incr_forward_tried (get_stats_heur S)) S)\<close>

definition incr_forward_rounds_st  :: \<open>_\<close> where
  \<open>incr_forward_rounds_st S = (set_stats_wl_heur (incr_forward_rounds (get_stats_heur S)) S)\<close>

definition incr_forward_strengthened_st  :: \<open>_\<close> where
  \<open>incr_forward_strengthened_st S = (set_stats_wl_heur (incr_forward_strengethening (get_stats_heur S)) S)\<close>

definition isa_subsume_or_strengthen_wl :: \<open>nat \<Rightarrow> nat subsumption \<Rightarrow> isasat \<Rightarrow> isasat nres\<close> where
  \<open>isa_subsume_or_strengthen_wl = (\<lambda>C s S. do {
   ASSERT(isa_subsume_or_strengthen_wl_pre C s S);
   (case s of
     NONE \<Rightarrow> RETURN S
  | SUBSUMED_BY C' \<Rightarrow> do {
     st1 \<leftarrow> mop_arena_status (get_clauses_wl_heur S) C;
     st2 \<leftarrow> mop_arena_status (get_clauses_wl_heur S) C';
     S \<leftarrow> mark_garbage_heur2 C S;
     let _ = mark_clause_for_unit_as_changed 0;
     S \<leftarrow> (if st1 = IRRED \<and> st2 = LEARNED then mop_arena_promote_st S C' else RETURN S);
     let S = (set_stats_wl_heur (incr_forward_subsumed (get_stats_heur S)) S);
     RETURN S
  }
   | STRENGTHENED_BY L C' \<Rightarrow> isa_strengthen_clause_wl2 C C' L S)
  })\<close>

definition mop_cch_remove_one where
  \<open>mop_cch_remove_one L D = do {
     ASSERT (nat_of_lit L < length D);
     RETURN (D[nat_of_lit L := False])
  } \<close>

definition mop_cch_remove_all_clauses where
  \<open>mop_cch_remove_all_clauses S C D = do {
     n \<leftarrow> mop_arena_length (get_clauses_wl_heur S) C;
     (_, D) \<leftarrow> WHILE\<^sub>T (\<lambda>(i, D). i < n)
       (\<lambda>(i, D). do {ASSERT (i < length (get_clauses_wl_heur S)); L \<leftarrow> mop_arena_lit2 (get_clauses_wl_heur S) C i; D \<leftarrow> mop_cch_remove_one L D; RETURN (i+1, D)})
      (0, D);
    RETURN D
  } \<close>

definition isa_forward_subsumption_one_wl :: \<open>nat \<Rightarrow> bool list \<Rightarrow> nat literal \<Rightarrow> isasat \<Rightarrow> (isasat \<times> nat subsumption \<times> bool list) nres\<close> where
  \<open>isa_forward_subsumption_one_wl = (\<lambda>C D L S. do {
  ASSERT (isa_forward_subsumption_one_wl_pre C L S);
  ASSERT (nat_of_lit L < length (get_occs S));
  n \<leftarrow> mop_cocc_list_length (get_occs S) L;
  (i, s) \<leftarrow>
    WHILE\<^sub>T\<^bsup> isa_forward_subsumption_one_wl2_inv S C L \<^esup> (\<lambda>(i, s). i < n \<and> s = NONE)
    (\<lambda>(i, s). do {
      ASSERT (i < n);
      C' \<leftarrow> mop_cocc_list_at (get_occs S) L i;
      status \<leftarrow> mop_arena_status (get_clauses_wl_heur S) C';
      if status = DELETED
      then RETURN (i+1, s)
      else do  {
        s \<leftarrow> isa_subsume_clauses_match2 C' C S D;
       RETURN (i+1, s)
      }
    })
        (0, NONE);
  D \<leftarrow> (if s \<noteq> NONE then mop_cch_remove_all_clauses S C D else RETURN D);
  S \<leftarrow> (if is_strengthened s then isa_maybe_push_to_occs_list_st C S else RETURN S);
  S \<leftarrow> isa_subsume_or_strengthen_wl C s S;
  
  let S = set_stats_wl_heur (incr_forward_subchecks_by (of_nat i) (get_stats_heur S)) S;
  RETURN (S, s, D)
  })\<close>

definition try_to_forward_subsume_wl2_pre :: \<open>_\<close> where
  \<open>try_to_forward_subsume_wl2_pre C cands shrunken S \<longleftrightarrow>
    distinct_mset cands \<and>
    try_to_forward_subsume_wl_pre C cands S\<close>

definition isa_try_to_forward_subsume_wl_pre :: \<open>_\<close> where
  \<open>isa_try_to_forward_subsume_wl_pre C shrunken S \<longleftrightarrow>
  (\<exists>T r u cands occs'. (S,T)\<in>twl_st_heur_restart_occs' r u \<and>  (get_occs S, occs') \<in> occurrence_list_ref \<and>
  try_to_forward_subsume_wl2_pre C cands (mset shrunken) T)\<close>

definition try_to_forward_subsume_wl2_inv :: \<open>_\<close> where
  \<open>try_to_forward_subsume_wl2_inv S cands  C = (\<lambda>(i, changed, break, occs, D, T).
  try_to_forward_subsume_wl_inv S cands C (i, break, T) \<and>
  (\<not>changed \<longrightarrow> (D, mset (get_clauses_wl T \<propto> C)) \<in> clause_hash_ref (all_init_atms_st T)) \<and>
  (changed \<longrightarrow> (D, {#}) \<in> clause_hash_ref (all_init_atms_st T)))\<close>


definition isa_try_to_forward_subsume_wl_inv :: \<open>isasat \<Rightarrow> nat \<Rightarrow> nat \<times> nat subsumption \<times> bool \<times> bool list \<times> isasat \<Rightarrow> bool\<close> where
  \<open>isa_try_to_forward_subsume_wl_inv S C = (\<lambda>(i, changed, break, D, T).
  (\<exists>S' T' cands occs' D'. (S,S')\<in>twl_st_heur_restart_occs' (length (get_clauses_wl_heur S)) (learned_clss_count S) \<and>
    (T,T')\<in>twl_st_heur_restart_occs' (length (get_clauses_wl_heur S)) (learned_clss_count S)\<and>
  (get_occs T, occs') \<in> occurrence_list_ref \<and>
  (D,D') \<in>clause_hash \<and>
  try_to_forward_subsume_wl2_inv S' cands C (i, changed \<noteq> NONE, break, occs', D', T')))\<close>

  (*TODO: Missing ticks*)
definition isa_try_to_forward_subsume_wl2_break :: \<open>isasat \<Rightarrow> bool nres\<close> where
  \<open>isa_try_to_forward_subsume_wl2_break S = RETURN (forward_subchecks (get_stats_heur S) \<ge> forward_budget (get_stats_heur S))\<close>

definition isa_try_to_forward_subsume_wl2 :: \<open>nat \<Rightarrow> bool list \<Rightarrow> nat list \<Rightarrow> isasat \<Rightarrow> (bool list \<times> nat list \<times> isasat) nres\<close> where
  \<open>isa_try_to_forward_subsume_wl2 C D shrunken S = do {
  ASSERT (isa_try_to_forward_subsume_wl_pre C shrunken S);
  n \<leftarrow> mop_arena_length_st S C;
  ASSERT (n \<le> Suc (unat32_max div 2));
  let n = 2 * n;
  ebreak \<leftarrow> isa_try_to_forward_subsume_wl2_break S;
  (_, changed, _, D, S) \<leftarrow> WHILE\<^sub>T\<^bsup> isa_try_to_forward_subsume_wl_inv S C\<^esup>
    (\<lambda>(i, changed, break, D, S). \<not>break \<and> i < n)
    (\<lambda>(i, changed, break, D, S). do {
      ASSERT (i < n);
      L \<leftarrow> mop_arena_lit2 (get_clauses_wl_heur S) C (i div 2);
      let L = (if i mod 2 = 0 then L else - L);
      (S, subs, D) \<leftarrow> isa_forward_subsumption_one_wl C D L S;
      ebreak \<leftarrow> isa_try_to_forward_subsume_wl2_break S;
      RETURN (i+1, subs, (subs \<noteq> NONE) \<or> ebreak, D, S)
    })
  (0, NONE, ebreak, D, S);
  D \<leftarrow> (if changed = NONE then mop_cch_remove_all_clauses S C D else RETURN D);
  let _ = (if changed = NONE then mark_clause_for_unit_as_unchanged 0 else ());
  ASSERT (Suc (length shrunken) \<le> length (get_tvdom S));
  let add_to_shunken = (is_strengthened changed);
  let shrunken = (if add_to_shunken then shrunken @ [C] else shrunken);
  RETURN (D, shrunken, S)
  }\<close>
definition isa_forward_subsumption_pre_all :: \<open>_\<close> where
  \<open>isa_forward_subsumption_pre_all  S \<longleftrightarrow>
  (\<exists>T r u. (S,T)\<in>twl_st_heur_restart_ana' r u \<and> forward_subsumption_all_wl_pre T)\<close>

definition correct_occurence_list where
  \<open>correct_occurence_list S occs cands n \<longleftrightarrow>
  distinct_mset cands \<and>
  all_occurrences (all_init_atms_st S) occs \<inter># cands = {#} \<and>
  (\<forall>C\<in># all_occurrences (all_init_atms_st S) occs. C \<in># dom_m (get_clauses_wl S) \<longrightarrow> length (get_clauses_wl S \<propto> C) \<le> n)\<and>
  (\<forall>C\<in># all_occurrences (all_init_atms_st S) occs. C \<in># dom_m (get_clauses_wl S) \<longrightarrow>
    (\<forall>L\<in>set (get_clauses_wl S \<propto> C). undefined_lit (get_trail_wl S) L)) \<and>
  fst occs = set_mset (all_init_atms_st S)\<close>

definition populate_occs_inv where
  \<open>populate_occs_inv S xs = (\<lambda>(i, occs, cands).
  all_occurrences (all_init_atms_st S) occs + mset cands \<subseteq># mset (take i xs) \<inter># dom_m (get_clauses_wl S) \<and>
  distinct cands \<and> fst occs = set_mset (all_init_atms_st S) \<and> 
  correct_occurence_list S occs (mset (drop i xs)) 2 \<and>
  all_occurrences (all_init_atms_st S) occs \<inter># mset cands = {#} \<and>
  (\<forall>C\<in># all_occurrences (all_init_atms_st S) occs. C \<in># dom_m (get_clauses_wl S) \<and>
    (\<forall>L\<in>set (get_clauses_wl S \<propto> C). undefined_lit (get_trail_wl S) L) \<and> length (get_clauses_wl S \<propto> C) = 2) \<and>
  (\<forall>C\<in>set cands. C \<in># dom_m (get_clauses_wl S) \<and>  length (get_clauses_wl S \<propto> C) > 2 \<and> (\<forall>L\<in>set (get_clauses_wl S \<propto> C). undefined_lit (get_trail_wl S) L)))\<close>

definition isa_populate_occs_inv where
  \<open>isa_populate_occs_inv S xs = (\<lambda>(i, U).
  (\<exists>T U' occs. (S,T)\<in>twl_st_heur_restart_occs' (length (get_clauses_wl_heur S)) (learned_clss_count S) \<and> (get_occs U, occs) \<in> occurrence_list_ref \<and>
    (U,U')\<in>twl_st_heur_restart_occs' (length (get_clauses_wl_heur S)) (learned_clss_count S) \<and> populate_occs_inv T xs (i, occs, get_tvdom U)))\<close>

definition isa_all_lit_clause_unset_pre :: \<open>_\<close> where
  \<open>isa_all_lit_clause_unset_pre C S \<longleftrightarrow> (\<exists>T r u. (S,T)\<in>twl_st_heur_restart_occs' r u \<and> forward_subsumption_all_wl_pre T \<and> C\<in>set (get_vdom S)) \<close>

definition isa_all_lit_clause_unset where
  \<open>isa_all_lit_clause_unset C S = do {
  ASSERT (isa_all_lit_clause_unset_pre C S);
  not_garbage \<leftarrow> mop_clause_not_marked_to_delete_heur S C;
  if \<not>not_garbage then RETURN False
  else do {
    n \<leftarrow> mop_arena_length_st S C;
    (i, unset, added) \<leftarrow> WHILE\<^sub>T (\<lambda>(i, unset, _). unset \<and> i < n)
    (\<lambda>(i, unset, added). do {
      ASSERT (i+1 \<le> Suc (unat32_max div 2));
      ASSERT(Suc i \<le> unat32_max);
      L \<leftarrow> mop_arena_lit2 (get_clauses_wl_heur S) C i;
      val \<leftarrow> mop_polarity_pol (get_trail_wl_heur S) L;
      is_added \<leftarrow> mop_is_marked_added_heur_st S (atm_of L);
      RETURN (i+1, val = None, if is_added then added + 1 else added)
    }) (0, True, 0::64 word);
    let a = (added \<ge> 2);
    RETURN (unset \<and> a)
  }
  }\<close>



definition forward_subsumption_all_wl2_inv :: \<open>nat twl_st_wl \<Rightarrow> nat list \<Rightarrow> nat \<times> _ \<times> _ \<times> nat twl_st_wl \<times> nat \<times> nat multiset \<Rightarrow> bool\<close> where
  \<open>forward_subsumption_all_wl2_inv = (\<lambda>S xs (i, occs, D, s, n, shrunken).
  (D, {#}) \<in> clause_hash_ref (all_init_atms_st s) \<and> shrunken \<subseteq># mset (take i xs) \<and>
  forward_subsumption_all_wl_inv S (mset xs) (mset (drop i xs), s))
  \<close>



definition sort_cands_by_length where
  \<open>sort_cands_by_length S = do {
  let tvdom = get_tvdom S;
  let avdom = get_avdom S;
  let ivdom = get_ivdom S;
  let vdom = get_vdom S;
  ASSERT (\<forall>i\<in>set tvdom. arena_is_valid_clause_idx (get_clauses_wl_heur S) i);
  tvdom \<leftarrow> SPEC (\<lambda>cands'. mset cands' = mset tvdom \<and>
    sorted_wrt (\<lambda>a b. arena_length (get_clauses_wl_heur S) a \<le> arena_length (get_clauses_wl_heur S) b) cands');
  RETURN (set_aivdom_wl_heur (AIvdom (vdom, avdom, ivdom, tvdom)) S)
}\<close>

definition push_to_tvdom_st :: \<open>nat \<Rightarrow> isasat \<Rightarrow> isasat nres\<close> where
  \<open>push_to_tvdom_st C S = do {
    ASSERT (length (get_vdom S) \<le> length (get_clauses_wl_heur S));
    ASSERT (length (get_tvdom S) < length (get_clauses_wl_heur S));
    let av = get_aivdom S; let av = push_to_tvdom C av;
    RETURN (set_aivdom_wl_heur av S)
  }\<close>

definition empty_tvdom_st :: \<open>isasat \<Rightarrow> isasat nres\<close> where
  \<open>empty_tvdom_st S = do {
    let aivdom = get_aivdom S;
    let aivdom = empty_tvdom aivdom;
    RETURN (set_aivdom_wl_heur aivdom S)
  }\<close>

text \<open>Using \<^term>\<open>empty_tvdom_st\<close> is mostly laziness: It should actually already be empty, but 
re-cleaning is not costing much anyhow.\<close>
definition isa_populate_occs :: \<open>isasat \<Rightarrow> _ nres\<close> where
  \<open>isa_populate_occs S = do {
    ASSERT (length (get_avdom_aivdom (get_aivdom S) @ get_ivdom_aivdom (get_aivdom S))  \<le> length (get_clauses_wl_heur S));
    let xs = get_avdom_aivdom (get_aivdom S) @ get_ivdom_aivdom (get_aivdom S);
    let m = size (get_avdom_aivdom (get_aivdom S));
    let n = size xs;
    let occs = get_occs S;
    ASSERT (n \<le> length (get_clauses_wl_heur S));
    T \<leftarrow> empty_tvdom_st S;
    (xs,  S) \<leftarrow> WHILE\<^sub>T\<^bsup>isa_populate_occs_inv S xs\<^esup> (\<lambda>(i, S). i < n)
    (\<lambda>(i, S). do {
      ASSERT (i < n);
      ASSERT (Suc i \<le> length (get_avdom_aivdom (get_aivdom S) @ get_ivdom_aivdom (get_aivdom S)));
      ASSERT (i < m \<longrightarrow> access_avdom_at_pre S i);
      ASSERT (i \<ge> m \<longrightarrow> access_ivdom_at_pre S (i - m));
      let C = (if i < m then get_avdom_aivdom (get_aivdom S) ! i else get_ivdom_aivdom (get_aivdom S) ! (i-m));
      ASSERT (C \<in> set (get_vdom S));
      all_undef \<leftarrow> isa_all_lit_clause_unset C S;
      if \<not>all_undef then
        RETURN (i+1, S)
      else do {
        n \<leftarrow> mop_arena_length_st S C;
        if n = 2 then do {
          S \<leftarrow> isa_push_to_occs_list_st C S;
          RETURN (i+1, S)
        }
        else  do {
          cand \<leftarrow> isa_is_candidate_forward_subsumption S C;
          if cand then do {S \<leftarrow> push_to_tvdom_st C S; RETURN (i+1, S)}
          else RETURN (i+1, S)
          }
        }
            }
      )
      (0, T);
     T \<leftarrow> sort_cands_by_length S;
     RETURN T
  }\<close>

definition mop_cch_add_all_clause :: \<open>_\<close> where
  \<open>mop_cch_add_all_clause S C D = do {
    n \<leftarrow> mop_arena_length_st S C;
    ASSERT (n \<le> length (get_clauses_wl_heur S));
    (_, D) \<leftarrow> WHILE\<^sub>T (\<lambda>(i, D). i < n)
    (\<lambda>(i,D). do {
      ASSERT (i < n);
      L \<leftarrow> mop_arena_lit2 (get_clauses_wl_heur S) C i;
      let _ = mark_literal_for_unit_deletion L;
      D \<leftarrow> mop_cch_add L D;
      RETURN (i+1, D)
      }) (0, D);
    RETURN D
}\<close>

definition mop_ch_add_all_clause :: \<open>_\<close> where
  \<open>mop_ch_add_all_clause S C D = do {
    ASSERT (C \<in># dom_m (get_clauses_wl S));
    let n = length (get_clauses_wl S \<propto> C);
    (_, D) \<leftarrow> WHILE\<^sub>T (\<lambda>(i, D). i < n)
    (\<lambda>(i,D). do {
      L \<leftarrow> mop_clauses_at (get_clauses_wl S) C i;
      D \<leftarrow> mop_ch_add L D;
      RETURN (i+1, D)
      }) (0, D);
    RETURN D
}\<close>

definition empty_occs_st :: \<open>isasat \<Rightarrow> isasat nres\<close> where
  \<open>empty_occs_st S = do {
    let D = get_occs S;
    let D = replicate (length D) [];
    RETURN (set_occs_wl_heur D S)
  }\<close>

definition empty_occs2 where
  \<open>empty_occs2 occs\<^sub>0 = do {
  let n = length occs\<^sub>0;
  (_, occs)\<leftarrow> WHILE\<^sub>T (\<lambda>(i,occs). i < n)
  (\<lambda>(i,occs). do {
     ASSERT (i < n \<and> length occs = length occs\<^sub>0);
     RETURN (i+1, occs[i := take 0 (occs ! i)])
  }) (0, occs\<^sub>0);
  RETURN occs
  }\<close>

definition isa_forward_reset_added_and_stats where
  \<open>isa_forward_reset_added_and_stats S = 
  (let S = (set_stats_wl_heur (incr_forward_rounds (get_stats_heur S)) S) in
  set_heur_wl_heur (reset_added_heur (get_heur S)) S)\<close>

definition empty_occs2_st :: \<open>isasat \<Rightarrow> isasat nres\<close> where
  \<open>empty_occs2_st S = do {
    let D = get_occs S;
    D \<leftarrow> empty_occs2 D;
    RETURN (set_occs_wl_heur D S)
  }\<close>

definition forward_subsumption_finalize :: \<open>nat list \<Rightarrow> isasat \<Rightarrow> isasat nres\<close> where
  \<open>forward_subsumption_finalize shrunken S = do {
    let S = isa_forward_reset_added_and_stats (schedule_next_subsume_st ((1 + stats_forward_rounds_st S) * 10000) S);
    _ \<leftarrow> isasat_current_progress 115 S;
    (_, S) \<leftarrow> WHILE\<^sub>T(\<lambda>(i,S). i < length shrunken) (\<lambda>(i,S). do {
      ASSERT (i < length shrunken);
      let C = shrunken ! i;
      not_garbage \<leftarrow> mop_clause_not_marked_to_delete_heur S C;
      S \<leftarrow> (if not_garbage then mark_added_clause_heur2 S C else RETURN S);
      RETURN (i+1, S)
    }) (0, S);
    empty_occs2_st S
  }\<close>

definition subsumemineff :: \<open>64 word\<close> where
  \<open>subsumemineff = 1000000›

definition subsumemaxeff :: \<open>64 word\<close> where
  \<open>subsumemaxeff = 1000000›
  
definition isa_forward_set_budget where
  \<open>isa_forward_set_budget S = do {
     let stats = get_stats_heur S;
     let delta = stats_propagations stats;
     let delta = (if delta < subsumemineff then subsumemineff else delta);
     let delta = (if delta > subsumemaxeff then subsumemaxeff else delta);
     let budget = delta + forward_budget stats;
     let stats = set_forward_budget budget stats;
     RETURN (set_stats_wl_heur stats S)
  }\<close>
definition isa_forward_subsumption_all_wl_inv :: \<open>_\<close> where
  \<open>isa_forward_subsumption_all_wl_inv R\<^sub>0 S =
  (\<lambda>(i, D, shrunken, T). \<exists>R\<^sub>0' S' T' D' occs' n. (R\<^sub>0, R\<^sub>0')\<in>twl_st_heur_restart_occs' (length (get_clauses_wl_heur R\<^sub>0)) (learned_clss_count R\<^sub>0) \<and>
  (S, S')\<in>twl_st_heur_restart_occs' (length (get_clauses_wl_heur R\<^sub>0)) (learned_clss_count R\<^sub>0) \<and>
  (T,T')\<in>twl_st_heur_restart_occs' (length (get_clauses_wl_heur R\<^sub>0)) (learned_clss_count R\<^sub>0) \<and> (get_occs T, occs') \<in> occurrence_list_ref \<and>
  (D, D') \<in> clause_hash \<and>
    forward_subsumption_all_wl2_inv S' (get_tvdom S) (i, occs', D', T', n, mset shrunken)) \<close>

definition isa_forward_subsumption_all :: \<open>_ \<Rightarrow> _ nres\<close> where
  \<open>isa_forward_subsumption_all = (\<lambda>S\<^sub>0. do {
  ASSERT (isa_forward_subsumption_pre_all S\<^sub>0);
  S \<leftarrow> isa_forward_set_budget S\<^sub>0;
  ASSERT (isasat_fast_relaxed S\<^sub>0 \<longrightarrow> isasat_fast_relaxed S);
  S \<leftarrow> isa_populate_occs S;
  ASSERT (isasat_fast_relaxed S\<^sub>0 \<longrightarrow> isasat_fast_relaxed S);
  let m = length (get_tvdom S);
  D \<leftarrow> mop_cch_create (length (get_watched_wl_heur S));
  let shrunken = [];
  (_, D, shrunken, S) \<leftarrow>
    WHILE\<^sub>T\<^bsup> isa_forward_subsumption_all_wl_inv S\<^sub>0 S \<^esup> (\<lambda>(i, D, shrunken, S). i < m \<and> get_conflict_wl_is_None_heur S)
    (\<lambda>(i, D, shrunken, S). do {
       ASSERT (i < m);
       ASSERT (access_tvdom_at_pre S i);
       let C = get_tvdom S!i;
       D \<leftarrow> mop_cch_add_all_clause S C D;
       (D, shrunken, T) \<leftarrow> isa_try_to_forward_subsume_wl2 C D shrunken S;
       RETURN (i+1, D, shrunken, incr_forward_tried_st T)
    })
    (0, D, shrunken, S);
  ASSERT (\<forall>C\<in>set shrunken. C \<in> set (get_vdom S));
  forward_subsumption_finalize shrunken S
  }
)\<close>

definition isa_forward_subsume :: \<open>isasat \<Rightarrow> isasat nres\<close> where
  \<open>isa_forward_subsume S = do {
    let b = should_subsume_st S;
    if b then isa_forward_subsumption_all S else RETURN S
  }\<close>

end