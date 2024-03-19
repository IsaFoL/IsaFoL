theory IsaSAT_Restart_Reduce_Defs
  imports IsaSAT_Restart_Defs
    IsaSAT_Bump_Heuristics
begin

text \<open>
  We first fix the function that proves termination. We don't take the ``smallest'' function
  possible (other possibilites that are growing slower include \<^term>\<open>\<lambda>(n::nat). n >> 50\<close>).
\<close>

definition (in -) find_local_restart_target_level_int_inv where
  \<open>find_local_restart_target_level_int_inv bmp cs =
     (\<lambda>(brk, i). i \<le> length cs \<and> length cs < unat32_max)\<close>

(*TODO fix*)
definition find_local_restart_target_level_int
   :: \<open>trail_pol \<Rightarrow> bump_heuristics \<Rightarrow> nat nres\<close>
where
  \<open>find_local_restart_target_level_int =
     (\<lambda>(M, xs, lvls, reasons, k, cs, zeored) bmp. do {
     let m = current_vmtf_array_nxt_score bmp;
     (brk, i) \<leftarrow> WHILE\<^sub>T\<^bsup>find_local_restart_target_level_int_inv bmp cs\<^esup>
        (\<lambda>(brk, i). \<not>brk \<and> i < length cs)
        (\<lambda>(brk, i). do {
           ASSERT (i < length cs);
           let t = (cs  ! i);
	   ASSERT(t < length M);
	   let L = atm_of (M ! t);
           u \<leftarrow> access_focused_vmtf_array bmp L;
           let brk = stamp u < m;
           RETURN (brk, if brk then i else i+1)
         })
        (False, 0);
    RETURN i
   })\<close>


text \<open>\<^term>\<open>find_decomp_wl_st_int\<close> is the wrong function here, because unlike in the backtrack case,
  we also have to update the queue of literals to update. This is done in the function \<^term>\<open>empty_Q\<close>.
\<close>

definition find_local_restart_target_level_st :: \<open>isasat \<Rightarrow> nat nres\<close> where
  \<open>find_local_restart_target_level_st S = do {
    find_local_restart_target_level_int (get_trail_wl_heur S) (get_vmtf_heur S)
  }\<close>

definition cdcl_twl_local_restart_wl_D_heur
   :: \<open>isasat \<Rightarrow> isasat nres\<close>
where
  \<open>cdcl_twl_local_restart_wl_D_heur = (\<lambda>S. do {
      ASSERT(restart_abs_wl_heur_pre S False);
      lvl \<leftarrow> find_local_restart_target_level_st S;
      b \<leftarrow> RETURN (lvl = count_decided_st_heur S);
      if b
      then RETURN S
      else do {
        S \<leftarrow> find_decomp_wl_st_int lvl S;
        S \<leftarrow> empty_Q S;
        incr_restart_stat S
      }
   }
  )\<close>

definition reorder_vdom_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>reorder_vdom_wl S = do {
    ASSERT (mark_to_delete_clauses_wl_pre S);
    RETURN S
  }\<close>

definition sort_clauses_by_score :: \<open>arena \<Rightarrow> isasat_aivdom \<Rightarrow> isasat_aivdom nres\<close> where
  \<open>sort_clauses_by_score arena vdom = do {
      ASSERT(\<forall>i\<in>set (get_vdom_aivdom vdom). valid_sort_clause_score_pre_at arena i);
      ASSERT(\<forall>i\<in>set (get_avdom_aivdom vdom). valid_sort_clause_score_pre_at arena i);
      ASSERT(\<forall>i\<in>set (get_tvdom_aivdom vdom). valid_sort_clause_score_pre_at arena i);
  SPEC(\<lambda>vdom'. mset (get_vdom_aivdom vdom) = mset (get_vdom_aivdom vdom') \<and>
      mset (get_avdom_aivdom vdom) = mset (get_avdom_aivdom vdom') \<and>
      mset (get_ivdom_aivdom vdom) = mset (get_ivdom_aivdom vdom') \<and>
      mset (get_tvdom_aivdom vdom) = mset (get_tvdom_aivdom vdom'))
  }\<close>

definition (in -) quicksort_clauses_by_score_avdom :: \<open>arena \<Rightarrow> vdom \<Rightarrow> vdom nres\<close> where
  \<open>quicksort_clauses_by_score_avdom arena =
     (full_quicksort_ref clause_score_ordering (clause_score_extract arena))\<close>
 
definition remove_deleted_clauses_from_avdom_inv :: \<open>_\<close> where
  \<open>remove_deleted_clauses_from_avdom_inv N avdom0 = (\<lambda>(i, j, avdom). i \<le> j \<and> j \<le> length (get_avdom_aivdom avdom0) \<and> length (get_avdom_aivdom avdom) = length (get_avdom_aivdom avdom0) \<and>
    mset (take i (get_avdom_aivdom avdom) @ drop j (get_avdom_aivdom avdom)) \<subseteq># mset (get_avdom_aivdom avdom0) \<and>
    mset (take i (get_avdom_aivdom avdom) @ drop j (get_avdom_aivdom avdom)) \<inter># dom_m N = mset (get_avdom_aivdom avdom0) \<inter># dom_m N \<and>
    get_vdom_aivdom avdom = get_vdom_aivdom avdom0 \<and>
    get_ivdom_aivdom avdom = get_ivdom_aivdom avdom0 \<and>
    distinct (get_tvdom_aivdom avdom) \<and>
  set (get_tvdom_aivdom avdom) \<subseteq> set (take i (get_avdom_aivdom avdom)) \<and>
  length (get_tvdom_aivdom avdom) \<le> i \<and>
   (\<forall>C \<in> set (get_tvdom_aivdom avdom). C \<in># dom_m N \<and> \<not>irred N C \<and> length (N \<propto> C) \<noteq> 2))\<close>

definition is_candidate_for_removal where
  \<open>is_candidate_for_removal C N = do {
    ASSERT (C \<in># dom_m N);
    SPEC (\<lambda>b :: bool. b \<longrightarrow> \<not>irred N C \<and> length (N \<propto> C) \<noteq> 2)
  }\<close>

definition remove_deleted_clauses_from_avdom :: \<open>_\<close> where
\<open>remove_deleted_clauses_from_avdom N avdom0 = do {
  let n = length (get_avdom_aivdom avdom0);
  let avdom0' = get_avdom_aivdom avdom0;
  (i, j, avdom) \<leftarrow> WHILE\<^sub>T\<^bsup> remove_deleted_clauses_from_avdom_inv N avdom0\<^esup>
    (\<lambda>(i, j, avdom). j < n)
    (\<lambda>(i, j, avdom). do {
      ASSERT(j < length (get_avdom_aivdom avdom));
      if (get_avdom_aivdom avdom ! j) \<in># dom_m N then do {
        let C = get_avdom_aivdom avdom ! j;
        let avdom = swap_avdom_aivdom avdom i j;
        should_push \<leftarrow> is_candidate_for_removal C N;
        if should_push then RETURN (i+1, j+1, push_to_tvdom C avdom)
        else RETURN (i+1, j+1, avdom)
      }
     else RETURN (i, j+1, avdom)
    })
    (0, 0, empty_tvdom avdom0);
  ASSERT(i \<le> length (get_avdom_aivdom avdom));
  RETURN (take_avdom_aivdom i avdom)
}\<close>


definition isa_is_candidate_for_removal where
  \<open>isa_is_candidate_for_removal M C arena = do {
    ASSERT(arena_act_pre arena C);
    L \<leftarrow> mop_arena_lit arena C;
    lbd \<leftarrow> mop_arena_lbd arena C;
    length \<leftarrow> mop_arena_length arena C;
    status \<leftarrow> mop_arena_status arena C;
    used \<leftarrow> mop_marked_as_used arena C;
    D \<leftarrow> get_the_propagation_reason_pol M L;
    let can_del =
      lbd > MINIMUM_DELETION_LBD \<and>
      status = LEARNED \<and>
      length \<noteq> 2 \<and>
      used = 0 \<and>
      (D \<noteq> Some C);
    RETURN can_del
  }\<close>


definition isa_gather_candidates_for_reduction :: \<open>trail_pol \<Rightarrow> arena \<Rightarrow> _ \<Rightarrow> (arena \<times> _) nres\<close> where
\<open>isa_gather_candidates_for_reduction M arena avdom0 = do {
  ASSERT(length (get_avdom_aivdom avdom0) \<le> length arena);
  ASSERT(length (get_avdom_aivdom avdom0) \<le> length (get_vdom_aivdom avdom0));
  let n = length (get_avdom_aivdom avdom0);
  (arena, i, j, avdom) \<leftarrow> WHILE\<^sub>T\<^bsup> \<lambda>(_, i, j, _). i \<le> j \<and> j \<le> n\<^esup>
    (\<lambda>(arena, i, j, avdom). j < n)
    (\<lambda>(arena, i, j, avdom). do {
      ASSERT(j < n);
      ASSERT(arena_is_valid_clause_vdom arena (get_avdom_aivdom avdom!j) \<and> j < length (get_avdom_aivdom avdom) \<and> i < length (get_avdom_aivdom avdom));
     ASSERT (length (get_tvdom_aivdom avdom) \<le> i);
     if arena_status arena (get_avdom_aivdom avdom ! j) \<noteq> DELETED then do{
        ASSERT(arena_act_pre arena (get_avdom_aivdom avdom ! j));
        should_push \<leftarrow> isa_is_candidate_for_removal M (get_avdom_aivdom avdom ! j) arena;
        let arena = mark_unused arena (get_avdom_aivdom avdom ! j);
       if should_push then  RETURN (arena, i+1, j+1, push_to_tvdom (get_avdom_aivdom avdom ! j) (swap_avdom_aivdom avdom i j))
       else RETURN (arena, i+1, j+1, swap_avdom_aivdom avdom i j)
      }
      else RETURN (arena, i, j+1, avdom)
    }) (arena, 0, 0, empty_tvdom avdom0);
  ASSERT(i \<le> length (get_avdom_aivdom avdom));
  RETURN (arena, take_avdom_aivdom i avdom)
}\<close>

definition (in -) sort_vdom_heur :: \<open>isasat \<Rightarrow> isasat nres\<close> where
  \<open>sort_vdom_heur = (\<lambda>S. do {
    let vdom = get_aivdom S;
    let M' = get_trail_wl_heur S;
    let arena = get_clauses_wl_heur S;
    ASSERT(length (get_avdom_aivdom vdom) \<le> length arena);
    ASSERT(length (get_vdom_aivdom vdom) \<le> length arena);
    (arena', vdom) \<leftarrow> isa_gather_candidates_for_reduction M' arena vdom;
    ASSERT(valid_sort_clause_score_pre arena (get_vdom_aivdom vdom));
    ASSERT(EQ (length arena) (length arena'));
    ASSERT(length (get_avdom_aivdom vdom) \<le> length arena);
    vdom \<leftarrow> sort_clauses_by_score arena' vdom;
    RETURN (set_clauses_wl_heur arena' (set_aivdom_wl_heur vdom S))
    })\<close>

definition partition_main_clause where
  \<open>partition_main_clause arena = partition_main clause_score_ordering (clause_score_extract arena)\<close>

definition partition_clause where
  \<open>partition_clause arena = partition_between_ref clause_score_ordering  (clause_score_extract arena)\<close>


definition mark_to_delete_clauses_wl_D_heur_pre :: \<open>isasat \<Rightarrow> bool\<close> where
  \<open>mark_to_delete_clauses_wl_D_heur_pre S \<longleftrightarrow>
  (\<exists>S'. (S, S') \<in> twl_st_heur_restart \<and> mark_to_delete_clauses_wl_pre S')\<close>

definition find_largest_lbd_and_size
  :: \<open>nat \<Rightarrow> isasat \<Rightarrow> (nat \<times> nat) nres\<close>
where
\<open>find_largest_lbd_and_size  = (\<lambda>l S. do {
    ASSERT(length (get_tvdom S) \<le> length (get_clauses_wl_heur S));
    (i, lbd, sze) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i, _ :: nat, _::nat). i \<le> length (get_tvdom S)\<^esup>
      (\<lambda>(i, lbd, sze). i < l \<and> i < length (get_tvdom S))
      (\<lambda>(i, lbd, sze). do {
        ASSERT(i < length (get_tvdom S));
        ASSERT(access_tvdom_at_pre S i);
        let C = get_tvdom S ! i;
        ASSERT(clause_not_marked_to_delete_heur_pre (S, C));
        b \<leftarrow> mop_clause_not_marked_to_delete_heur S C;
        if \<not>b then RETURN (i+1, lbd, sze)
        else do {
          lbd2 \<leftarrow> mop_arena_lbd_st S C;
          sze' \<leftarrow> mop_arena_length_st S C;
          RETURN (i+1, max lbd (lbd2), max sze sze')
        }
      })
      (0, 0 :: nat , 0 :: nat);
    RETURN (lbd, sze)
  })\<close>

definition mark_to_delete_clauses_wl_D_heur
  :: \<open>isasat \<Rightarrow> isasat nres\<close>
where
\<open>mark_to_delete_clauses_wl_D_heur  = (\<lambda>S0. do {
    ASSERT(mark_to_delete_clauses_wl_D_heur_pre S0);
    S \<leftarrow> sort_vdom_heur S0;
    l \<leftarrow> number_clss_to_keep S;
    (lbd, sze) \<leftarrow> find_largest_lbd_and_size l S;
    ASSERT(length (get_tvdom S) \<le> length (get_clauses_wl_heur S0));
    (i, T) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>_. True\<^esup>
      (\<lambda>(i, S). i < length (get_tvdom S))
      (\<lambda>(i, T). do {
        ASSERT(i < length (get_tvdom T));
        ASSERT(access_tvdom_at_pre T i);
        let C = get_tvdom T ! i;
        ASSERT(clause_not_marked_to_delete_heur_pre (T, C));
        b \<leftarrow> mop_clause_not_marked_to_delete_heur T C;
        if \<not>b then RETURN (i, delete_index_vdom_heur i T)
        else do {
          ASSERT(access_lit_in_clauses_heur_pre ((T, C), 0));
          ASSERT(length (get_clauses_wl_heur T) \<le> length (get_clauses_wl_heur S0));
          ASSERT(length (get_tvdom T) \<le> length (get_clauses_wl_heur T));
          L \<leftarrow> mop_access_lit_in_clauses_heur T C 0;
          D \<leftarrow> get_the_propagation_reason_pol (get_trail_wl_heur T) L;
          length \<leftarrow> mop_arena_length (get_clauses_wl_heur T) C;
          let can_del = (D \<noteq> Some C) \<and>
             length \<noteq> 2;
          if can_del
          then
            do {
              wasted \<leftarrow> mop_arena_length_st T C;
              _ \<leftarrow> log_del_clause_heur T C;
              T \<leftarrow> mop_mark_garbage_heur3 C i (incr_wasted_st (of_nat wasted) T);
              RETURN (i, T)
            }
          else do {
            RETURN (i+1, T)
	  }
        }
      })
      (l, S);
    ASSERT(length (get_tvdom T) \<le> length (get_clauses_wl_heur S0));
    incr_reduction_stat (set_stats_size_limit_st lbd sze T)
  })\<close>



definition mark_to_delete_clauses_GC_wl_D_heur_pre :: \<open>isasat \<Rightarrow> bool\<close> where
  \<open>mark_to_delete_clauses_GC_wl_D_heur_pre S \<longleftrightarrow>
  (\<exists>S'. (S, S') \<in> twl_st_heur_restart \<and> mark_to_delete_clauses_GC_wl_pre S')\<close>

text \<open>
  The duplication is unfortunate. The only difference is the precondition.
\<close>
definition mark_to_delete_clauses_GC_wl_D_heur
  :: \<open>isasat \<Rightarrow> isasat nres\<close>
where
\<open>mark_to_delete_clauses_GC_wl_D_heur  = (\<lambda>S0. do {
    ASSERT(mark_to_delete_clauses_GC_wl_D_heur_pre S0);
    S \<leftarrow> sort_vdom_heur S0;
    l \<leftarrow> number_clss_to_keep S;
    (lbd, sze) \<leftarrow> find_largest_lbd_and_size l S;
    ASSERT(length (get_tvdom S) \<le> length (get_clauses_wl_heur S0));
    (i, T) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>_. True\<^esup>
      (\<lambda>(i, S). i < length (get_tvdom S))
      (\<lambda>(i, T). do {
        ASSERT(i < length (get_tvdom T));
        ASSERT(access_tvdom_at_pre T i);
        let C = get_tvdom T ! i;
        ASSERT(clause_not_marked_to_delete_heur_pre (T, C));
        b \<leftarrow> mop_clause_not_marked_to_delete_heur T C;
        if \<not>b then RETURN (i, delete_index_vdom_heur i T)
        else do {
          ASSERT(access_lit_in_clauses_heur_pre ((T, C), 0));
          ASSERT(length (get_clauses_wl_heur T) \<le> length (get_clauses_wl_heur S0));
          ASSERT(length (get_tvdom T) \<le> length (get_clauses_wl_heur T));
          length \<leftarrow> mop_arena_length (get_clauses_wl_heur T) C;
          let can_del = length \<noteq> 2;
          if can_del
          then
            do {
              wasted \<leftarrow> mop_arena_length_st T C;
              _ \<leftarrow> log_del_clause_heur T C;
              T \<leftarrow> mop_mark_garbage_heur3 C i (incr_wasted_st (of_nat wasted) T);
              RETURN (i, T)
            }
          else do {
            RETURN (i+1, T)
	  }
        }
      })
      (l, S);
    ASSERT(length (get_tvdom T) \<le> length (get_clauses_wl_heur S0));
    incr_restart_stat (set_stats_size_limit_st lbd sze T)
  })\<close>


text \<open>Approximatively @{term \<open>sqrt(p)\<close>} is @{term \<open>2^((word_log2 p) >> 1)\<close>}\<close>
definition schedule_next_reduction_st :: \<open>isasat \<Rightarrow> isasat\<close> where
  \<open>schedule_next_reduction_st S =
   (let (delta :: 64 word) = 1 + 2 << (word_log2 (max 1 (get_reductions_count S)) >> 1);
      delta = delta * opts_reduceint_st S;
      irred = (get_irredundant_count_st S) >> 10;
      extra = if irred < 10 then 1 else of_nat (word_log2 (irred)) >> 1;
      delta = extra * delta in
  schedule_next_reduce_st delta S)\<close>

definition cdcl_twl_mark_clauses_to_delete where
  \<open>cdcl_twl_mark_clauses_to_delete S = do {
  _ \<leftarrow> ASSERT (mark_to_delete_clauses_wl_D_heur_pre S);
  _ \<leftarrow> RETURN (IsaSAT_Profile.start_reduce);
  T \<leftarrow> mark_to_delete_clauses_wl_D_heur S;
  _ \<leftarrow> RETURN (IsaSAT_Profile.stop_reduce);
  RETURN (schedule_next_reduction_st (clss_size_resetUS0_st T))
  }\<close>

(*TODO deduplicate*)
definition cdcl_twl_restart_wl_heur where
\<open>cdcl_twl_restart_wl_heur S = do {
    cdcl_twl_local_restart_wl_D_heur S
  }\<close>

definition isasat_GC_clauses_prog_copy_wl_entry
  :: \<open>arena \<Rightarrow> (nat watcher) list list \<Rightarrow> nat literal \<Rightarrow>
         (arena \<times> isasat_aivdom) \<Rightarrow> (arena \<times> (arena \<times> isasat_aivdom)) nres\<close>
where
\<open>isasat_GC_clauses_prog_copy_wl_entry = (\<lambda>N0 W A (N', aivdom). do {
    ASSERT(nat_of_lit A < length W);
    ASSERT(length (W ! nat_of_lit A) \<le> length N0);
    let le = length (W ! nat_of_lit A);
    (i, N, N', aivdom) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(i, N, N', aivdom). i < le)
      (\<lambda>(i, N, (N', aivdom)). do {
        ASSERT(i < length (W ! nat_of_lit A));
        let C = fst (W ! nat_of_lit A ! i);
        ASSERT(arena_is_valid_clause_vdom N C);
        let st = arena_status N C;
        if st \<noteq> DELETED then do {
          ASSERT(arena_is_valid_clause_idx N C);
          ASSERT(length N' +
            (if arena_length N C > 4 then MAX_HEADER_SIZE else MIN_HEADER_SIZE) +
            arena_length N C \<le> length N0);
          ASSERT(length N = length N0);
           ASSERT(length (get_vdom_aivdom aivdom) < length N0);
          ASSERT(length (get_avdom_aivdom aivdom) < length N0);
          ASSERT(length (get_ivdom_aivdom aivdom) < length N0);
          ASSERT(length (get_tvdom_aivdom aivdom) < length N0);
          let D = length N' + (if arena_length N C > 4 then MAX_HEADER_SIZE else MIN_HEADER_SIZE);
          N' \<leftarrow> fm_mv_clause_to_new_arena C N N';
          ASSERT(mark_garbage_pre (N, C));
	  RETURN (i+1, extra_information_mark_to_delete N C, N',
             (if st = LEARNED then add_learned_clause_aivdom_strong D aivdom else add_init_clause_aivdom_strong D aivdom))
        } else RETURN (i+1, N, (N', aivdom))
      }) (0, N0, (N', aivdom));
    RETURN (N, (N', aivdom))
  })\<close>

definition isasat_GC_clauses_prog_single_wl
  :: \<open>arena \<Rightarrow>  (arena \<times> isasat_aivdom) \<Rightarrow> (nat watcher) list list \<Rightarrow> nat \<Rightarrow>
        (arena \<times> (arena \<times> isasat_aivdom) \<times> (nat watcher) list list) nres\<close>
where
\<open>isasat_GC_clauses_prog_single_wl = (\<lambda>N0 N' WS A. do {
    let L = Pos A; \<^cancel>\<open>use phase saving instead\<close>
    ASSERT(nat_of_lit L < length WS);
    ASSERT(nat_of_lit (-L) < length WS);
    (N, (N', aivdom)) \<leftarrow> isasat_GC_clauses_prog_copy_wl_entry N0 WS L N';
    let WS = WS[nat_of_lit L := []];
    ASSERT(length N = length N0);
    (N, N') \<leftarrow> isasat_GC_clauses_prog_copy_wl_entry N WS (-L) (N', aivdom);
    let WS = WS[nat_of_lit (-L) := []];
    RETURN (N, N', WS)
  })\<close>

definition isasat_GC_clauses_prog_wl2 where
  \<open>isasat_GC_clauses_prog_wl2 \<equiv> (\<lambda>(ns :: bump_heuristics) x0. do {
      (_, x) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(n, x). length (fst x) = length (fst x0)\<^esup>
        (\<lambda>(n, _). n \<noteq> None)
        (\<lambda>(n, x). do {
          ASSERT(n \<noteq> None);
          let A = the n;
          ASSERT (A < length_bumped_vmtf_array ns);
          ASSERT(A \<le> unat32_max div 2);
          x \<leftarrow> (\<lambda>(arena\<^sub>o, arena, W). isasat_GC_clauses_prog_single_wl arena\<^sub>o arena W A) x;
          n \<leftarrow>  access_focused_vmtf_array ns A;
          RETURN (get_next n, x)
        })
        (Some (bumped_vmtf_array_fst ns), x0);
      RETURN x
    })\<close>

definition isasat_GC_clauses_prog_wl :: \<open>isasat \<Rightarrow> isasat nres\<close> where
  \<open>isasat_GC_clauses_prog_wl = (\<lambda>S. do {
    let vm = get_vmtf_heur S;
    let N' = get_clauses_wl_heur S;
    let W' = get_watched_wl_heur S;
    let vdom = get_aivdom S;
    let old_arena = get_old_arena S;
    ASSERT(old_arena = []);
    (N, (N', vdom), WS) \<leftarrow> isasat_GC_clauses_prog_wl2 vm
        (N', (old_arena, empty_aivdom vdom), W');
    let S = set_watched_wl_heur WS S;
    let S = set_clauses_wl_heur N' S;
    let S = set_old_arena_wl_heur (take 0 N) S;
    let S = set_vmtf_wl_heur vm S;
    let S = set_stats_wl_heur (incr_GC (get_stats_heur S)) S;
    let S = set_aivdom_wl_heur vdom S;
    let heur = get_heur S;
    let heur = heuristic_reluctant_untrigger (set_zero_wasted heur);
    let S = set_heur_wl_heur heur S;
    RETURN S
  })\<close>

definition isasat_GC_clauses_pre_wl_D :: \<open>isasat \<Rightarrow> bool\<close> where
\<open>isasat_GC_clauses_pre_wl_D S \<longleftrightarrow> (
  \<exists>T. (S, T) \<in> twl_st_heur_restart \<and> cdcl_GC_clauses_pre_wl T
  )\<close>

definition isasat_GC_clauses_wl_D :: \<open>bool \<Rightarrow> isasat \<Rightarrow> isasat nres\<close> where
\<open>isasat_GC_clauses_wl_D = (\<lambda>inprocessing S. do {
  ASSERT(isasat_GC_clauses_pre_wl_D S);
  let b = True;
  if b then do {
    T \<leftarrow> isasat_GC_clauses_prog_wl S;
    ASSERT(length (get_clauses_wl_heur T) \<le> length (get_clauses_wl_heur S));
    ASSERT(\<forall>i \<in> set (get_tvdom T). i < length (get_clauses_wl_heur S));
    U \<leftarrow> rewatch_heur_and_reorder_st (empty_US_heur T);
    RETURN U
  }
  else RETURN S})\<close>

end