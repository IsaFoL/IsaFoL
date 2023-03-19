theory IsaSAT_Inner_Propagation_Defs
  imports IsaSAT_Setup IsaSAT_Bump_Heuristics
     IsaSAT_Clauses IsaSAT_VMTF IsaSAT_LBD
begin


definition find_non_false_literal_between where
  \<open>find_non_false_literal_between M a b C =
     find_in_list_between (\<lambda>L. polarity M L \<noteq> Some False) a b C\<close>

(* TODO change to return the iterator (i) instead of the position in the clause *)
definition isa_find_unwatched_between
 :: \<open>_ \<Rightarrow> trail_pol \<Rightarrow> arena \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat option) nres\<close> where
\<open>isa_find_unwatched_between P M' NU a b C = do {
  ASSERT(C+a \<le> length NU);
  ASSERT(C+b \<le> length NU);
  (x, _) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(found, i). True\<^esup>
    (\<lambda>(found, i). found = None \<and> i < C + b)
    (\<lambda>(_, i). do {
      ASSERT(i < C + (arena_length NU C));
      ASSERT(i \<ge> C);
      ASSERT(i < C + b);
      ASSERT(arena_lit_pre NU i);
      L \<leftarrow> mop_arena_lit NU i;
      ASSERT(polarity_pol_pre M' L);
      if P L then RETURN (Some (i - C), i) else RETURN (None, i+1)
    })
    (None, C+a);
  RETURN x
}
\<close>
definition isa_find_unwatched
  :: \<open>(nat literal \<Rightarrow> bool) \<Rightarrow> trail_pol \<Rightarrow> arena \<Rightarrow> nat \<Rightarrow> (nat option) nres\<close>
where
\<open>isa_find_unwatched P M' arena C = do {
    l \<leftarrow> mop_arena_length arena C;
    b \<leftarrow> RETURN(l \<le> MAX_LENGTH_SHORT_CLAUSE);
    if b then isa_find_unwatched_between P M' arena 2 l C
    else do {
      ASSERT(get_saved_pos_pre arena C);
      pos \<leftarrow> mop_arena_pos arena C;
      n \<leftarrow> isa_find_unwatched_between P M' arena pos l C;
      if n = None then isa_find_unwatched_between P M' arena 2 pos C
      else RETURN n
    }
  }
\<close>

definition isa_save_pos :: \<open>nat \<Rightarrow> nat \<Rightarrow> isasat \<Rightarrow> isasat nres\<close>
where
  \<open>isa_save_pos C i = (\<lambda>S. do {
      ASSERT(arena_is_valid_clause_idx (get_clauses_wl_heur S) C);
      if arena_length (get_clauses_wl_heur S) C > MAX_LENGTH_SHORT_CLAUSE then do {
        ASSERT(isa_update_pos_pre ((C, i), get_clauses_wl_heur S));
        let N = arena_update_pos C i  (get_clauses_wl_heur S);
        RETURN (set_clauses_wl_heur N S)
      } else RETURN S
    })
  \<close>


definition mark_conflict_to_rescore :: \<open>nat \<Rightarrow> isasat \<Rightarrow> isasat nres\<close> where
  \<open>mark_conflict_to_rescore C S = do {
  let M = get_trail_wl_heur S;
  let N = get_clauses_wl_heur S;
  let D = get_conflict_wl_heur S;
  let vm = get_vmtf_heur S;
  n \<leftarrow> mop_arena_length N C;
  ASSERT (n \<le> length N);
  (_, vm) \<leftarrow> WHILE\<^sub>T (\<lambda>(i, vm). i < n)
  (\<lambda>(i, vm). do{
      ASSERT (i < n);
     L \<leftarrow> mop_arena_lit2 N C i;
     vm \<leftarrow> isa_vmtf_bump_to_rescore_also_reasons_cl M N C (-L) vm;
    RETURN (i+1, vm)
   })
    (0, vm);
  let lbd = get_lbd S;
  (N, lbd) \<leftarrow> calculate_LBD_heur_st M N lbd C;
  let S = set_vmtf_wl_heur vm S;
  let S = set_clauses_wl_heur N S;
  let S = set_lbd_wl_heur lbd S;
  RETURN S
}\<close>


definition set_conflict_wl_heur
  :: \<open>nat \<Rightarrow> isasat \<Rightarrow> isasat nres\<close>
where
  \<open>set_conflict_wl_heur = (\<lambda>C S. do {
    S \<leftarrow> mark_conflict_to_rescore C S;
    let n = 0;
    let M = get_trail_wl_heur S;
    let N = get_clauses_wl_heur S;
    let D = get_conflict_wl_heur S;
    let outl = get_outlearned_heur S;
    ASSERT(curry5 isa_set_lookup_conflict_aa_pre M N C D n outl);
    (D, clvls, outl) \<leftarrow> isa_set_lookup_conflict_aa M N C D n outl;
    j \<leftarrow> mop_isa_length_trail M;
    let S = IsaSAT_Setup.set_conflict_wl_heur D S;
    let S = set_outl_wl_heur outl S;
    let S = set_count_max_wl_heur clvls S;
    let S = set_literals_to_update_wl_heur j S;
    RETURN S})\<close>


definition update_clause_wl_code_pre where
  \<open>update_clause_wl_code_pre = (\<lambda>((((((((L, L'), C), b), j), w), i), f), S).
      w < length (get_watched_wl_heur S ! nat_of_lit L) )\<close>

definition update_clause_wl_heur
   :: \<open>nat literal \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> isasat \<Rightarrow>
    (nat \<times> nat \<times> isasat) nres\<close>
where
  \<open>update_clause_wl_heur = (\<lambda>(L::nat literal) L' C b j w i f S. do {
     let N = get_clauses_wl_heur S;
     let W = get_watched_wl_heur S;
     K' \<leftarrow> mop_arena_lit2' (set (get_vdom S)) N C f;
     ASSERT(w < length N);
     N' \<leftarrow> mop_arena_swap C i f N;
     ASSERT(nat_of_lit K' < length W);
     ASSERT(length (W ! (nat_of_lit K')) < length N);
     let W = W[nat_of_lit K':= W ! (nat_of_lit K') @ [(C, L', b)]];
     let S = set_watched_wl_heur W S;
     let S = set_clauses_wl_heur N' S;
     RETURN (j, w+1, S)
  })\<close>

definition propagate_lit_wl_heur
  :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> isasat \<Rightarrow> isasat nres\<close>
where
  \<open>propagate_lit_wl_heur = (\<lambda>L' C i S. do {
      let M = get_trail_wl_heur S;
      let N = get_clauses_wl_heur S;
      let heur = get_heur S;
      ASSERT(i \<le> 1);
      M \<leftarrow> cons_trail_Propagated_tr L' C M;
      N' \<leftarrow> mop_arena_swap C 0 (1 - i) N;
      heur \<leftarrow> mop_save_phase_heur (atm_of L') (is_pos L') heur;
      let S = set_trail_wl_heur M S;
      let S = set_clauses_wl_heur N' S;
      let S = set_heur_wl_heur heur S;
      RETURN S
  })\<close>


definition propagate_lit_wl_bin_heur
  :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> isasat \<Rightarrow> isasat nres\<close>
where
  \<open>propagate_lit_wl_bin_heur = (\<lambda>L' C S. do {
      let M = get_trail_wl_heur S;
      let heur = get_heur S;
      M \<leftarrow> cons_trail_Propagated_tr L' C M;
      heur \<leftarrow> mop_save_phase_heur (atm_of L') (is_pos L') heur;
      let S = set_trail_wl_heur M S;
      let S = set_heur_wl_heur heur S;
      RETURN S
  })\<close>



definition unit_prop_body_wl_heur_inv where
  \<open>unit_prop_body_wl_heur_inv S j w L \<longleftrightarrow>
     (\<exists>S'. (S, S') \<in> twl_st_heur \<and> unit_prop_body_wl_inv S' j w L)\<close>

definition unit_prop_body_wl_D_find_unwatched_heur_inv where
  \<open>unit_prop_body_wl_D_find_unwatched_heur_inv f C S \<longleftrightarrow>
     (\<exists>S'. (S, S') \<in> twl_st_heur \<and> unit_prop_body_wl_find_unwatched_inv f C S')\<close>

definition keep_watch_heur where
  \<open>keep_watch_heur = (\<lambda>L i j S. do {
     let W = get_watched_wl_heur S;
     ASSERT(nat_of_lit L < length W);
     ASSERT(i < length (W ! nat_of_lit L));
     ASSERT(j < length (W ! nat_of_lit L));
     let W =  W[nat_of_lit L := (W!(nat_of_lit L))[i := W ! (nat_of_lit L) ! j]];
     RETURN (set_watched_wl_heur W S)
   })\<close>

definition update_blit_wl_heur
  :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat literal \<Rightarrow> isasat \<Rightarrow>
    (nat \<times> nat \<times> isasat) nres\<close>
where
  \<open>update_blit_wl_heur = (\<lambda>(L::nat literal) C b j w K S. do {
     let W = get_watched_wl_heur S;
     ASSERT(nat_of_lit L < length W);
     ASSERT(j < length (W ! nat_of_lit L));
     ASSERT(j < length (get_clauses_wl_heur S));
     ASSERT(w < length (get_clauses_wl_heur S));
     let W = W[nat_of_lit L := (W!nat_of_lit L)[j:= (C, K, b)]];
     RETURN (j+1, w+1, set_watched_wl_heur W S)
  })\<close>


definition pos_of_watched_heur :: \<open>isasat\<Rightarrow> nat \<Rightarrow> nat literal \<Rightarrow> nat nres\<close> where
\<open>pos_of_watched_heur S C L = do {
  L' \<leftarrow> mop_access_lit_in_clauses_heur S C 0;
  RETURN (if L = L' then 0 else 1)
}\<close>

definition unit_propagation_inner_loop_wl_loop_D_heur_inv0 where
  \<open>unit_propagation_inner_loop_wl_loop_D_heur_inv0 L =
   (\<lambda>(j, w, S'). \<exists>S. (S', S) \<in> twl_st_heur \<and> unit_propagation_inner_loop_wl_loop_inv L (j, w, S) \<and>
      length (watched_by S L) \<le> length (get_clauses_wl_heur S') - MIN_HEADER_SIZE)\<close>

definition other_watched_wl_heur :: \<open>isasat \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat literal nres\<close> where
\<open>other_watched_wl_heur S L C i = do {
    ASSERT(i < 2 \<and> arena_lit_pre2 (get_clauses_wl_heur S) C i \<and>
      arena_lit (get_clauses_wl_heur S) (C + i) = L \<and> arena_lit_pre2 (get_clauses_wl_heur S) C (1 - i));
    mop_access_lit_in_clauses_heur S C (1 - i)
  }\<close>

definition isa_find_unwatched_wl_st_heur
  :: \<open>isasat \<Rightarrow> nat \<Rightarrow> nat option nres\<close> where
\<open>isa_find_unwatched_wl_st_heur = (\<lambda>S i. do {
    isa_find_unwatched (\<lambda>L. polarity_pol (get_trail_wl_heur S) L \<noteq> Some False) (get_trail_wl_heur S) (get_clauses_wl_heur S) i
  })\<close>

definition unit_propagation_inner_loop_body_wl_heur
   :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> isasat \<Rightarrow> (nat \<times> nat \<times> isasat) nres\<close>
   where
  \<open>unit_propagation_inner_loop_body_wl_heur L j w S0 = do {
      ASSERT(unit_propagation_inner_loop_wl_loop_D_heur_inv0 L (j, w, S0));
      (C, K, b) \<leftarrow> mop_watched_by_app_heur S0 L w;
      S \<leftarrow> keep_watch_heur L j w S0;
      ASSERT(length (get_clauses_wl_heur S) = length (get_clauses_wl_heur S0));
      val_K \<leftarrow> mop_polarity_st_heur S K;
      if val_K = Some True
      then RETURN (j+1, w+1, S)
      else do {
        if b then do {
           if val_K = Some False
           then do {
             S \<leftarrow> set_conflict_wl_heur C S;
             RETURN (j+1, w+1, S)}
           else do {
             S \<leftarrow> propagate_lit_wl_bin_heur K C S;
             RETURN (j+1, w+1, S)}
        }
        else do {
	  \<comment>\<open>Now the costly operations:\<close>
	  ASSERT(clause_not_marked_to_delete_heur_pre (S, C));
	  if \<not>clause_not_marked_to_delete_heur S C
	  then RETURN (j, w+1, S)
	  else do {
	    i \<leftarrow> pos_of_watched_heur S C L;
            ASSERT(i \<le> 1);
	    L' \<leftarrow> other_watched_wl_heur S L C i;
	    val_L' \<leftarrow> mop_polarity_st_heur S L';
	    if val_L' = Some True
	    then update_blit_wl_heur L C b j w L' S
	    else do {
	      f \<leftarrow> isa_find_unwatched_wl_st_heur S C;
	      case f of
		None \<Rightarrow> do {
		  if val_L' = Some False
		  then do {
		    S \<leftarrow> set_conflict_wl_heur C S;
		    RETURN (j+1, w+1, S)}
		  else do {
		    S \<leftarrow> propagate_lit_wl_heur L' C i S;
		    RETURN (j+1, w+1, S)}
		}
	      | Some f \<Rightarrow> do {
		  S \<leftarrow> isa_save_pos C f S;
		  ASSERT(length (get_clauses_wl_heur S) = length (get_clauses_wl_heur S0));
		  K \<leftarrow> mop_access_lit_in_clauses_heur S C f;
		  val_L' \<leftarrow> mop_polarity_st_heur S K;
		  if val_L' = Some True
		  then update_blit_wl_heur L C b j w K S
		  else do {
		    update_clause_wl_heur L L' C b j w i f S
		  }
	       }
	    }
          }
        }
     }
   }\<close>


definition unit_propagation_inner_loop_wl_loop_D_heur_inv where
  \<open>unit_propagation_inner_loop_wl_loop_D_heur_inv S\<^sub>0 L =
   (\<lambda>(j, w, S'). \<exists>S\<^sub>0' S. (S\<^sub>0, S\<^sub>0') \<in> twl_st_heur \<and> (S', S) \<in> twl_st_heur \<and> unit_propagation_inner_loop_wl_loop_inv L (j, w, S) \<and>
        L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S) \<and> dom_m (get_clauses_wl S) = dom_m (get_clauses_wl S\<^sub>0') \<and>
        length (get_clauses_wl_heur S\<^sub>0) = length (get_clauses_wl_heur S'))\<close>


definition unit_propagation_inner_loop_wl_loop_D_heur
  :: \<open>nat literal \<Rightarrow> isasat \<Rightarrow> (nat \<times> nat \<times> isasat) nres\<close>
where
  \<open>unit_propagation_inner_loop_wl_loop_D_heur L S\<^sub>0 = do {
    ASSERT(length (watched_by_int S\<^sub>0 L) \<le> length (get_clauses_wl_heur S\<^sub>0));
    n \<leftarrow> mop_length_watched_by_int S\<^sub>0 L;
    WHILE\<^sub>T\<^bsup>unit_propagation_inner_loop_wl_loop_D_heur_inv S\<^sub>0 L\<^esup>
      (\<lambda>(j, w, S). w < n \<and> get_conflict_wl_is_None_heur S)
      (\<lambda>(j, w, S). do {
        unit_propagation_inner_loop_body_wl_heur L j w S
      })
      (0, 0, S\<^sub>0)
  }\<close>


definition cut_watch_list_heur
  :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat literal \<Rightarrow> isasat \<Rightarrow> isasat nres\<close>
where
  \<open>cut_watch_list_heur j w L =(\<lambda>S. do {
      let W = get_watched_wl_heur S;
      ASSERT(j \<le> length (W!nat_of_lit L) \<and> j \<le> w \<and> nat_of_lit L < length W \<and>
         w \<le> length (W ! (nat_of_lit L)));
      let W = W[nat_of_lit L := take j (W!(nat_of_lit L)) @ drop w (W!(nat_of_lit L))];
      RETURN (set_watched_wl_heur W S)
    })\<close>
definition cut_watch_list_heur2
 :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat literal \<Rightarrow> isasat \<Rightarrow> isasat nres\<close>
where
\<open>cut_watch_list_heur2 = (\<lambda>j w L S. do {
  let W = get_watched_wl_heur S;
  ASSERT(j \<le> length (W ! nat_of_lit L) \<and> j \<le> w \<and> nat_of_lit L < length W \<and>
     w \<le> length (W ! (nat_of_lit L)));
  let n = length (W!(nat_of_lit L));
  (j, w, W) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(j, w, W). j \<le> w \<and> w \<le> n \<and> nat_of_lit L < length W\<^esup>
    (\<lambda>(j, w, W). w < n)
    (\<lambda>(j, w, W). do {
      ASSERT(w < length (W!(nat_of_lit L)));
      RETURN (j+1, w+1, W[nat_of_lit L := (W!(nat_of_lit L))[j := W!(nat_of_lit L)!w]])
    })
    (j, w, W);
  ASSERT(j \<le> length (W ! nat_of_lit L) \<and> nat_of_lit L < length W);
  let W = W[nat_of_lit L := take j (W ! nat_of_lit L)];
  RETURN (set_watched_wl_heur W S)
})\<close>
definition unit_propagation_inner_loop_wl_D_heur
  :: \<open>nat literal \<Rightarrow> isasat \<Rightarrow> isasat nres\<close> where
  \<open>unit_propagation_inner_loop_wl_D_heur L S\<^sub>0 = do {
     (j, w, S) \<leftarrow> unit_propagation_inner_loop_wl_loop_D_heur L S\<^sub>0;
     ASSERT(length (watched_by_int S L) \<le> length (get_clauses_wl_heur S\<^sub>0) - MIN_HEADER_SIZE);
     cut_watch_list_heur2 j w L S
  }\<close>


definition select_and_remove_from_literals_to_update_wl_heur
  :: \<open>isasat \<Rightarrow> (isasat \<times> nat literal) nres\<close>
where
\<open>select_and_remove_from_literals_to_update_wl_heur S = do {
    ASSERT(literals_to_update_wl_heur S < length (fst (get_trail_wl_heur S)));
    ASSERT(literals_to_update_wl_heur S + 1 \<le> unat32_max);
    L \<leftarrow> isa_trail_nth (get_trail_wl_heur S) (literals_to_update_wl_heur S);
    RETURN (set_literals_to_update_wl_heur (literals_to_update_wl_heur S + 1) S, -L)
  }\<close>


definition unit_propagation_outer_loop_wl_D_heur_inv
 :: \<open>isasat \<Rightarrow> isasat \<Rightarrow> bool\<close>
where
  \<open>unit_propagation_outer_loop_wl_D_heur_inv S\<^sub>0 S' \<longleftrightarrow>
     (\<exists>S\<^sub>0' S. (S\<^sub>0, S\<^sub>0') \<in> twl_st_heur \<and> (S', S) \<in> twl_st_heur \<and>
       unit_propagation_outer_loop_wl_inv S \<and>
       dom_m (get_clauses_wl S) = dom_m (get_clauses_wl S\<^sub>0') \<and>
       length (get_clauses_wl_heur S') = length (get_clauses_wl_heur S\<^sub>0) \<and>
       isa_length_trail_pre (get_trail_wl_heur S'))\<close>

definition unit_propagation_update_statistics :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> isasat \<Rightarrow> isasat nres\<close> where
  \<open>unit_propagation_update_statistics p q S = do {
  let stats = get_stats_heur S;
  let pq = q - p;
  let stats = incr_propagation_by pq stats;
  let stats = (if get_conflict_wl_is_None_heur S then stats else incr_conflict stats);
  let stats = (if count_decided_pol (get_trail_wl_heur S) = 0 then incr_units_since_last_GC_by pq (incr_uset_by pq stats) else stats);
  height \<leftarrow> (if get_conflict_wl_is_None_heur S then RETURN q else do {j \<leftarrow> trail_height_before_conflict (get_trail_wl_heur S); RETURN (of_nat j)});
  let stats = set_no_conflict_until q stats;
  RETURN (set_stats_wl_heur stats S)}\<close>

definition unit_propagation_outer_loop_wl_D_heur
   :: \<open>isasat \<Rightarrow> isasat nres\<close> where
  \<open>unit_propagation_outer_loop_wl_D_heur S\<^sub>0 = do {
    let j1 = isa_length_trail (get_trail_wl_heur S\<^sub>0);
    _ \<leftarrow> RETURN (IsaSAT_Profile.start_propagate);
    S \<leftarrow> WHILE\<^sub>T\<^bsup>unit_propagation_outer_loop_wl_D_heur_inv S\<^sub>0\<^esup>
      (\<lambda>S. literals_to_update_wl_heur S < isa_length_trail (get_trail_wl_heur S))
      (\<lambda>S. do {
        ASSERT(literals_to_update_wl_heur S < isa_length_trail (get_trail_wl_heur S));
        (S', L) \<leftarrow> select_and_remove_from_literals_to_update_wl_heur S;
        ASSERT(length (get_clauses_wl_heur S') = length (get_clauses_wl_heur S));
        unit_propagation_inner_loop_wl_D_heur L S'
      })
    S\<^sub>0;
  let j2 = isa_length_trail (get_trail_wl_heur S);
  S \<leftarrow> unit_propagation_update_statistics (of_nat j1) (of_nat j2) S;
  _ \<leftarrow> RETURN (IsaSAT_Profile.stop_propagate);
  RETURN S}
  \<close>

definition isa_find_unset_lit :: \<open>trail_pol \<Rightarrow> arena \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat option nres\<close> where
  \<open>isa_find_unset_lit M = isa_find_unwatched_between (\<lambda>L. polarity_pol M L \<noteq> Some False) M\<close>

end