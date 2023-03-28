theory IsaSAT_Simplify_Units_Defs
  imports IsaSAT_Setup
    Watched_Literals.Watched_Literals_Watch_List_Inprocessing
    More_Refinement_Libs.WB_More_Refinement_Loops
    IsaSAT_Proofs
begin

definition simplify_clause_with_unit2_pre where
  \<open>simplify_clause_with_unit2_pre C M N \<longleftrightarrow>
     C \<in># dom_m N \<and> no_dup M\<close>

definition simplify_clause_with_unit2 where
  \<open>simplify_clause_with_unit2 C M N\<^sub>0 = do {
        ASSERT(C \<in># dom_m N\<^sub>0);
        let l = length (N\<^sub>0 \<propto> C);
        (i, j, N, del, is_true) \<leftarrow> WHILE\<^sub>T\<^bsup>(\<lambda>(i, j, N, del, b). C \<in># dom_m N)\<^esup>
        (\<lambda>(i, j, N, del, b). \<not>b \<and> j < l)
        (\<lambda>(i, j, N, del, is_true). do {
           ASSERT(i < length (N \<propto> C) \<and> j < length (N \<propto> C) \<and> C \<in># dom_m N \<and> i \<le> j);
           let L = N \<propto> C ! j;
           ASSERT(L \<in> set (N\<^sub>0 \<propto> C));
           let val = polarity M L;
           if val = Some True then RETURN (i, j+1, N, add_mset L del, True)
           else if val = Some False
           then RETURN (i, j+1, N, add_mset L del, False)
           else RETURN (i+1, j+1, N(C \<hookrightarrow> ((N \<propto> C)[i := L])), del, False)
        })
         (0, 0, N\<^sub>0, {#}, False);
    ASSERT(C \<in># dom_m N \<and> i \<le> length (N \<propto> C));
    ASSERT(is_true \<or> j = l);
    let L = N \<propto> C ! 0;
    if is_true \<or> i \<le> 1
    then RETURN (False, fmdrop C N, L, is_true, i)
    else if i = j \<and> \<not>is_true then RETURN (True, N, L, is_true, i)
    else do {
      RETURN (False, N(C \<hookrightarrow> (take i (N \<propto> C))), L, is_true, i)
    }
  }\<close>




definition simplify_clause_with_unit_st2 :: \<open>nat \<Rightarrow> nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close> where
  \<open>simplify_clause_with_unit_st2 =  (\<lambda>C (M, N\<^sub>0, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W). do {
    ASSERT(simplify_clause_with_unit_st_wl_pre C (M, N\<^sub>0, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W));
    ASSERT (C \<in># dom_m N\<^sub>0 \<and> count_decided M = 0 \<and> D = None);
    let S =  (M, N\<^sub>0, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W);
    let E = mset (N\<^sub>0 \<propto> C);
    let irr = irred N\<^sub>0 C;
    (unc, N, L, b, i) \<leftarrow> simplify_clause_with_unit2 C M N\<^sub>0;
    ASSERT(dom_m N \<subseteq># dom_m N\<^sub>0);
      if unc then do {
      ASSERT(N = N\<^sub>0);
      let T = (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W);
      RETURN T
    }
    else if b then do {
       let T = (M, N, D, (if irr then add_mset E else id) NE, (if \<not>irr then add_mset E else id) UE, NEk, UEk, NS, US, N0, U0, Q, W);
      ASSERT (set_mset (all_learned_lits_of_wl T) = set_mset (all_learned_lits_of_wl S));
      ASSERT (set_mset (all_init_lits_of_wl T) = set_mset (all_init_lits_of_wl S));
      ASSERT (set_mset (all_atms_st T) = set_mset (all_atms_st S));
      ASSERT (size (learned_clss_lf N) = size (learned_clss_lf N\<^sub>0) - (if irr then 0 else 1));
      ASSERT(\<not>irr \<longrightarrow> size (learned_clss_lf N\<^sub>0) \<ge> 1);
      RETURN T
    }
    else if i = 1
    then do {
      ASSERT (undefined_lit M L \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S));
      M \<leftarrow> cons_trail_propagate_l L 0 M;
      let T = (M, N, D, NE, UE, (if irr then add_mset {#L#} else id) NEk, (if \<not>irr then add_mset {#L#} else id)UEk, (if irr then add_mset E else id) NS, (if \<not>irr then add_mset E else id)US, N0, U0, add_mset (-L) Q, W);
      ASSERT (set_mset (all_learned_lits_of_wl T) = set_mset (all_learned_lits_of_wl S));
      ASSERT (set_mset (all_init_lits_of_wl T) = set_mset (all_init_lits_of_wl S));
      ASSERT (set_mset (all_atms_st T) = set_mset (all_atms_st S));
      ASSERT (size (learned_clss_lf N) = size (learned_clss_lf N\<^sub>0) - (if irr then 0 else 1));
      ASSERT(\<not>irr \<longrightarrow> size (learned_clss_lf N\<^sub>0) \<ge> 1);
      RETURN T
   }
    else if i = 0
    then do {
      let j = length M;
      let T = (M, N, Some {#}, NE, UE, NEk, UEk, (if irr then add_mset E else id) NS, (if \<not>irr then add_mset E else id) US, (if irr then add_mset {#} else id) N0, (if \<not>irr then add_mset {#} else id)U0, {#}, W);
      ASSERT (set_mset (all_learned_lits_of_wl T) = set_mset (all_learned_lits_of_wl S));
      ASSERT (set_mset (all_init_lits_of_wl T) = set_mset (all_init_lits_of_wl S));
      ASSERT (set_mset (all_atms_st T) = set_mset (all_atms_st S));
      ASSERT (size (learned_clss_lf N) = size (learned_clss_lf N\<^sub>0) - (if irr then 0 else 1));
      ASSERT(\<not>irr \<longrightarrow> size (learned_clss_lf N\<^sub>0) \<ge> 1);
      RETURN T
    }
    else do {
      let T = (M, N, D, NE, UE, NEk, UEk, (if irr then add_mset E else id) NS, (if \<not>irr then add_mset E else id) US, N0, U0, Q, W);
      ASSERT (set_mset (all_learned_lits_of_wl T) = set_mset (all_learned_lits_of_wl S));
      ASSERT (set_mset (all_init_lits_of_wl T) = set_mset (all_init_lits_of_wl S));
      ASSERT (set_mset (all_atms_st T) = set_mset (all_atms_st S));
      ASSERT (size (learned_clss_lf N) = size (learned_clss_lf N\<^sub>0));
      ASSERT (C \<in># dom_m N);
      RETURN T
    }
        })\<close>

definition simplify_clauses_with_unit_st2 :: \<open>nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close>  where
  \<open>simplify_clauses_with_unit_st2 S =
  do {
  ASSERT (simplify_clauses_with_unit_st_wl_pre S);
  xs \<leftarrow> SPEC(\<lambda>xs. finite xs);
  T \<leftarrow> FOREACHci(\<lambda>it T. simplify_clauses_with_unit_st_wl_inv S it T)
  (xs)
  (\<lambda>S. get_conflict_wl S = None)
  (\<lambda>i S. if i \<in># dom_m (get_clauses_wl S)
            then simplify_clause_with_unit_st2 i S else RETURN S)
  S;
  ASSERT(set_mset (all_learned_lits_of_wl T) \<subseteq> set_mset (all_learned_lits_of_wl S));
  ASSERT(set_mset (all_init_lits_of_wl T) = set_mset (all_init_lits_of_wl S));
  RETURN T
  }\<close>

definition isa_simplify_clause_with_unit2 where
  \<open>isa_simplify_clause_with_unit2 C M N = do {
     l \<leftarrow> mop_arena_length N C;
    ASSERT(l < length N \<and> l \<le> Suc (unat32_max div 2));
    (i, j, N::arena, is_true) \<leftarrow> WHILE\<^sub>T(\<lambda>(i, j, N::arena, b). \<not>b \<and> j < l)
    (\<lambda>(i, j, N, is_true). do {
      ASSERT(i \<le> j \<and> j < l);
      L \<leftarrow> mop_arena_lit2 N C j;
      val \<leftarrow> mop_polarity_pol M L;
      if val = Some True then RETURN (i, j+1, N,True)
      else if val = Some False
      then RETURN (i, j+1, N,  False)
        else do {
        N \<leftarrow> mop_arena_update_lit C i L N;
        RETURN (i+1, j+1, N, False)}
    })
      (0, 0, N, False);
   L \<leftarrow> mop_arena_lit2 N C 0;
   if is_true \<or> i \<le> 1
   then do {
     ASSERT(mark_garbage_pre (N, C));
     RETURN (False, extra_information_mark_to_delete N C, L, is_true, i)}
   else if i = j then RETURN (True, N, L, is_true, i)
   else do {
      N \<leftarrow> mop_arena_shorten C i N;
      RETURN (False, N, L, is_true, i)}
    }\<close>

definition set_conflict_to_false :: \<open>conflict_option_rel \<Rightarrow> conflict_option_rel\<close> where
  \<open>set_conflict_to_false = (\<lambda>(b, n, xs). (False, 0, xs))\<close>

text \<open>We butcher our statistics here, but the clauses are deleted later anyway.\<close>
definition isa_simplify_clause_with_unit_st2 :: \<open>nat \<Rightarrow> isasat \<Rightarrow> isasat nres\<close> where
  \<open>isa_simplify_clause_with_unit_st2 =  (\<lambda>C S. do {
   let lcount = get_learned_count S; let N = get_clauses_wl_heur S; let M = get_trail_wl_heur S;
   E \<leftarrow> mop_arena_status N C;
   ASSERT(E = LEARNED \<longrightarrow> 1 \<le> clss_size_lcount lcount);
   (unc, N, L, b, i) \<leftarrow> isa_simplify_clause_with_unit2 C M N;
   ASSERT (length N \<le> length (get_clauses_wl_heur S));
   if unc then RETURN (set_clauses_wl_heur N S)
   else if b then
   RETURN  (set_clauses_wl_heur N
     (set_stats_wl_heur (if E=LEARNED then (get_stats_heur S) else (decr_irred_clss (get_stats_heur S)))
     (set_learned_count_wl_heur (if E = LEARNED then clss_size_decr_lcount (lcount) else lcount)
     S)))
   else if i = 1
   then do {
     M \<leftarrow> cons_trail_Propagated_tr L 0 M;
     RETURN (set_clauses_wl_heur N
     (set_trail_wl_heur M
     (set_stats_wl_heur (if E=LEARNED then incr_uset (get_stats_heur S) else incr_uset (decr_irred_clss (get_stats_heur S)))
     (set_learned_count_wl_heur (if E = LEARNED then clss_size_decr_lcount (clss_size_incr_lcountUEk lcount) else lcount)
     S)))) }
   else if i = 0
   then do {
     j \<leftarrow> mop_isa_length_trail M;
     RETURN (set_clauses_wl_heur N
     (set_conflict_wl_heur (set_conflict_to_false (get_conflict_wl_heur S))
     (set_count_max_wl_heur 0
     (set_literals_to_update_wl_heur j
     (set_stats_wl_heur (if E=LEARNED then get_stats_heur S else decr_irred_clss (get_stats_heur S))
     (set_learned_count_wl_heur (if E = LEARNED then clss_size_decr_lcount lcount else lcount)
     S))))))
   }
   else do {
       let S = (set_clauses_wl_heur N S);
       _ \<leftarrow> log_new_clause_heur S C;
       RETURN S
     }
   })\<close>

definition isa_simplify_clauses_with_unit_st2 :: \<open>isasat \<Rightarrow> isasat nres\<close>  where
  \<open>isa_simplify_clauses_with_unit_st2 S =
  do {
     xs \<leftarrow> RETURN (get_avdom S @ get_ivdom S);
    ASSERT(length xs \<le> length (get_vdom S) \<and> length (get_vdom S) \<le> length (get_clauses_wl_heur S));
    (_, T) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(i, T). i < length xs \<and> get_conflict_wl_is_None_heur T)
      (\<lambda>(i,T). do {
           ASSERT((i < length (get_avdom T) \<longrightarrow> access_avdom_at_pre T i) \<and>
           (i \<ge> length (get_avdom T) \<longrightarrow> access_ivdom_at_pre T (i - length_avdom S)) \<and>
           length_avdom T = length_avdom S \<and>
           length (get_clauses_wl_heur T) = length (get_clauses_wl_heur S) \<and>
            learned_clss_count T \<le> learned_clss_count S);
          let C = (if i < length (get_avdom S) then access_avdom_at T i else access_ivdom_at T (i - length_avdom S));
          E \<leftarrow> mop_arena_status (get_clauses_wl_heur T) C;
          if E \<noteq> DELETED then do {
          T \<leftarrow> isa_simplify_clause_with_unit_st2 C T;
          ASSERT(i < length xs);
          RETURN (i+1, T)
        }
        else do {ASSERT(i < length xs); RETURN (i+1,T)}
      })
     (0, S);
    RETURN (reset_units_since_last_GC_st T)
  }\<close>

definition simplify_clauses_with_units_st_wl2 :: \<open>_\<close> where
  \<open>simplify_clauses_with_units_st_wl2 S = do {
  b \<leftarrow> SPEC(\<lambda>b::bool. b \<longrightarrow> get_conflict_wl S =None);
  if b then simplify_clauses_with_unit_st2 S else RETURN S
  }\<close>

definition isa_simplify_clauses_with_units_st_wl2 :: \<open>_\<close> where
  \<open>isa_simplify_clauses_with_units_st_wl2 S = do {
  b \<leftarrow> RETURN (get_conflict_wl_is_None_heur S \<and> units_since_last_GC_st S > 0);
  if b then isa_simplify_clauses_with_unit_st2 S else RETURN S
  }\<close>

end
