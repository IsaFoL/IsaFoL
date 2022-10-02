theory IsaSAT_Backtrack_Defs
  imports IsaSAT_Setup IsaSAT_VMTF IsaSAT_Rephase_State IsaSAT_LBD
     IsaSAT_Proofs
begin


chapter \<open>Backtrack\<close>

text \<open>
  The backtrack function is highly complicated and tricky to maintain.
\<close>

section \<open>Backtrack with direct extraction of literal if highest level\<close>

paragraph \<open>Empty conflict\<close>


definition empty_conflict_and_extract_clause_heur_inv where
  \<open>empty_conflict_and_extract_clause_heur_inv M outl =
    (\<lambda>(E, C, i). mset (take i C) = mset (take i outl) \<and>
            length C = length outl \<and> C ! 0 = outl ! 0 \<and> i \<ge> 1 \<and> i \<le> length outl \<and>
            (1 < length (take i C) \<longrightarrow>
                 highest_lit M (mset (tl (take i C)))
                  (Some (C ! 1, get_level M (C ! 1)))))\<close>

definition isa_empty_conflict_and_extract_clause_heur ::
  \<open>trail_pol \<Rightarrow> lookup_clause_rel \<Rightarrow> nat literal list \<Rightarrow> (_ \<times> nat literal list \<times> nat) nres\<close>
  where
    \<open>isa_empty_conflict_and_extract_clause_heur M D outl = do {
     let C = replicate (length outl) (outl!0);
     (D, C, _) \<leftarrow> WHILE\<^sub>T
         (\<lambda>(D, C, i). i < length_uint32_nat outl)
         (\<lambda>(D, C, i). do {
           ASSERT(i < length outl);
           ASSERT(i < length C);
           ASSERT(lookup_conflict_remove1_pre (outl ! i, D));
           let D = lookup_conflict_remove1 (outl ! i) D;
           let C = C[i := outl ! i];
	   ASSERT(get_level_pol_pre (M, C!i));
	   ASSERT(get_level_pol_pre (M, C!1));
	   ASSERT(1 < length C);
           let C = (if get_level_pol M (C!i) > get_level_pol M (C!1) then swap C 1 i else C);
           ASSERT(i+1 \<le> uint32_max);
           RETURN (D, C, i+1)
         })
        (D, C, 1);
     ASSERT(length outl \<noteq> 1 \<longrightarrow> length C > 1);
     ASSERT(length outl \<noteq> 1 \<longrightarrow>  get_level_pol_pre (M, C!1));
     RETURN ((True, D), C, if length outl = 1 then 0 else get_level_pol M (C!1))
  }\<close>


definition empty_cach_ref_set_inv where
  \<open>empty_cach_ref_set_inv cach0 support =
    (\<lambda>(i, cach). length cach = length cach0 \<and>
         (\<forall>L \<in> set (drop i support). L < length cach) \<and>
         (\<forall>L \<in> set (take i support).  cach ! L = SEEN_UNKNOWN) \<and>
         (\<forall>L < length cach. cach ! L \<noteq> SEEN_UNKNOWN \<longrightarrow> L \<in> set (drop i support)))\<close>

definition empty_cach_ref_set where
  \<open>empty_cach_ref_set = (\<lambda>(cach0, support). do {
    let n = length support;
    ASSERT(n \<le> Suc (uint32_max div 2));
    (_, cach) \<leftarrow> WHILE\<^sub>T\<^bsup>empty_cach_ref_set_inv cach0 support\<^esup>
      (\<lambda>(i, cach). i < length support)
      (\<lambda>(i, cach). do {
         ASSERT(i < length support);
         ASSERT(support ! i < length cach);
         RETURN(i+1, cach[support ! i := SEEN_UNKNOWN])
      })
     (0, cach0);
    RETURN (cach, emptied_list support)
  })\<close>

paragraph \<open>Minimisation of the conflict\<close>


definition empty_cach_ref_pre where
  \<open>empty_cach_ref_pre = (\<lambda>(cach :: minimize_status list, supp :: nat list).
         (\<forall>L\<in>set supp. L < length cach) \<and>
         length supp \<le> Suc (uint32_max div 2) \<and>
         (\<forall>L<length cach. cach ! L \<noteq> SEEN_UNKNOWN \<longrightarrow> L \<in> set supp))\<close>

definition (in -) empty_cach_ref where
  \<open>empty_cach_ref = (\<lambda>(cach, support). (replicate (length cach) SEEN_UNKNOWN, []))\<close>

definition extract_shorter_conflict_list_heur_st
  :: \<open>isasat \<Rightarrow> (isasat \<times> _ \<times> _) nres\<close>
  where
    \<open>extract_shorter_conflict_list_heur_st = (\<lambda>S. do {
     let M = get_trail_wl_heur S;
     let N = get_clauses_wl_heur S;
     let outl = get_outlearned_heur S;
     let vm = get_vmtf_heur S;
     let lbd = get_lbd S;
     let cach = get_conflict_cach S;
     let (_, D) = get_conflict_wl_heur S;
     lbd \<leftarrow> mark_lbd_from_list_heur M outl lbd;
     ASSERT(fst M \<noteq> []);
     let K = lit_of_last_trail_pol M;
     ASSERT(0 < length outl);
     ASSERT(lookup_conflict_remove1_pre (-K, D));
     let D = lookup_conflict_remove1 (-K) D;
     let outl = outl[0 := -K];
     vm \<leftarrow> isa_vmtf_mark_to_rescore_also_reasons M N outl (-K) vm;
     (D, cach, outl) \<leftarrow> isa_minimize_and_extract_highest_lookup_conflict M N D cach lbd outl;
     ASSERT(empty_cach_ref_pre cach);
     let cach = empty_cach_ref cach;
     ASSERT(outl \<noteq> [] \<and> length outl \<le> uint32_max);
     (D, C, n) \<leftarrow> isa_empty_conflict_and_extract_clause_heur M D outl;
     let S = set_outl_wl_heur (take 1 outl) S;
     let S = set_conflict_wl_heur D S; let S = set_vmtf_wl_heur vm S;
     let S = set_ccach_max_wl_heur cach S; let S = set_lbd_wl_heur lbd S;
     RETURN (S, n, C)
  })\<close>


definition update_propagation_heuristics_stats where
  \<open>update_propagation_heuristics_stats = (\<lambda>glue (fema, sema, res_info, wasted, phasing, reluctant, fullyproped, s).
     (ema_update glue fema, ema_update glue sema,
          incr_conflict_count_since_last_restart res_info, wasted,phasing, reluctant, False, s))\<close>

definition update_propagation_heuristics where
  \<open>update_propagation_heuristics glue = Restart_Heuristics o update_propagation_heuristics_stats glue o get_content\<close>

definition update_lbd_and_mark_used where
  \<open>update_lbd_and_mark_used i glue N = 
    (let N = update_lbd i glue N in
    (if glue \<le> TIER_TWO_MAXIMUM then mark_used2 N i else mark_used N i))\<close>

definition propagate_bt_wl_D_heur
  :: \<open>nat literal \<Rightarrow> nat clause_l \<Rightarrow> isasat \<Rightarrow> isasat nres\<close> where
  \<open>propagate_bt_wl_D_heur = (\<lambda>L C S\<^sub>0. do {
      let M = get_trail_wl_heur S\<^sub>0;
      let vdom = get_aivdom S\<^sub>0;
      let N0 = get_clauses_wl_heur S\<^sub>0;
      let W0 = get_watched_wl_heur S\<^sub>0;
      let lcount = get_learned_count S\<^sub>0;
      let heur = get_heur S\<^sub>0;
      let stats = get_stats_heur S\<^sub>0;
      let lbd = get_lbd S\<^sub>0;
      let vm0 = get_vmtf_heur S\<^sub>0;
      ASSERT(length (get_vdom_aivdom vdom) \<le> length N0);
      ASSERT(length (get_avdom_aivdom vdom) \<le> length N0);
      ASSERT(nat_of_lit (C!1) < length W0 \<and> nat_of_lit (-L) < length W0);
      ASSERT(length C > 1);
      let L' = C!1;
      ASSERT(length C \<le> uint32_max div 2 + 1);
      vm \<leftarrow> isa_vmtf_rescore C M vm0;
      glue \<leftarrow> get_LBD lbd;
      let b = False;
      let b' = (length C = 2);
      ASSERT(isasat_fast S\<^sub>0 \<longrightarrow> append_and_length_fast_code_pre ((b, C), N0));
      ASSERT(isasat_fast S\<^sub>0 \<longrightarrow> clss_size_lcount lcount < sint64_max);
      (N, i) \<leftarrow> fm_add_new b C N0;
      ASSERT(update_lbd_pre ((i, glue), N));
      let N = update_lbd_and_mark_used i glue N;
      ASSERT(isasat_fast S\<^sub>0 \<longrightarrow> length_ll W0 (nat_of_lit (-L)) < sint64_max);
      let W = W0[nat_of_lit (- L) := W0 ! nat_of_lit (- L) @ [(i, L', b')]];
      ASSERT(isasat_fast S\<^sub>0 \<longrightarrow> length_ll W (nat_of_lit L') < sint64_max);
      let W = W[nat_of_lit L' := W!nat_of_lit L' @ [(i, -L, b')]];
      lbd \<leftarrow> lbd_empty lbd;
      j \<leftarrow> mop_isa_length_trail M;
      ASSERT(i \<noteq> DECISION_REASON);
      ASSERT(cons_trail_Propagated_tr_pre ((-L, i), M));
      M \<leftarrow> cons_trail_Propagated_tr (- L) i M;
      vm \<leftarrow> isa_vmtf_flush_int M vm;
      heur \<leftarrow> mop_save_phase_heur (atm_of L') (is_neg L') heur;
      let S = set_watched_wl_heur W S\<^sub>0;
      let S = set_learned_count_wl_heur (clss_size_incr_lcount lcount) S;
      let S = set_aivdom_wl_heur (add_learned_clause_aivdom i vdom) S;
      let S = set_heur_wl_heur (heuristic_reluctant_tick (update_propagation_heuristics glue heur)) S;
      let S = set_stats_wl_heur (add_lbd (of_nat glue) stats) S;
      let S = set_trail_wl_heur M S;
      let S = set_clauses_wl_heur N S;
      let S = set_literals_to_update_wl_heur j S;
      let S = set_count_max_wl_heur 0 S;
      let S = set_vmtf_wl_heur vm S;
      let S = set_lbd_wl_heur lbd S;
      _ \<leftarrow> log_new_clause_heur S i;
      S \<leftarrow> maybe_mark_added_clause_heur2 S i;
      RETURN (S)
    })\<close>

definition propagate_unit_bt_wl_D_int
  :: \<open>nat literal \<Rightarrow> isasat \<Rightarrow> isasat nres\<close>
  where
    \<open>propagate_unit_bt_wl_D_int = (\<lambda>L S. do {
      let M = get_trail_wl_heur S;
      let vdom = get_aivdom S;
      let N = get_clauses_wl_heur S;
      let W0 = get_watched_wl_heur S;
      let lcount = get_learned_count S;
      let heur = get_heur S;
      let stats = get_stats_heur S;
      let lbd = get_lbd S;
      let vm0 = get_vmtf_heur S;
      vm \<leftarrow> isa_vmtf_flush_int M vm0;
      glue \<leftarrow> get_LBD lbd;
      lbd \<leftarrow> lbd_empty lbd;
      j \<leftarrow> mop_isa_length_trail M;
      ASSERT(0 \<noteq> DECISION_REASON);
      ASSERT(cons_trail_Propagated_tr_pre ((- L, 0::nat), M));
      M \<leftarrow> cons_trail_Propagated_tr (- L) 0 M;
      let stats = incr_units_since_last_GC (incr_uset stats);
      let S = set_stats_wl_heur stats S;
      let S = set_trail_wl_heur M S;
      let S = set_vmtf_wl_heur vm S;
      let S = set_lbd_wl_heur lbd S;
      let S = set_literals_to_update_wl_heur j S;
      let S = set_heur_wl_heur (heuristic_reluctant_tick (update_propagation_heuristics glue heur)) S;
      let S = set_learned_count_wl_heur (clss_size_incr_lcountUEk lcount) S;
      RETURN S})\<close>

paragraph \<open>Full function\<close>

definition backtrack_wl_D_heur_inv where
  \<open>backtrack_wl_D_heur_inv S \<longleftrightarrow> (\<exists>S'. (S, S') \<in> twl_st_heur_conflict_ana \<and> backtrack_wl_inv S')\<close>

definition backtrack_wl_D_nlit_heur
  :: \<open>isasat \<Rightarrow> isasat nres\<close>
  where
    \<open>backtrack_wl_D_nlit_heur S\<^sub>0 =
    do {
      ASSERT(backtrack_wl_D_heur_inv S\<^sub>0);
      ASSERT(fst (get_trail_wl_heur S\<^sub>0) \<noteq> []);
      L \<leftarrow> lit_of_hd_trail_st_heur S\<^sub>0;
      (S, n, C) \<leftarrow> extract_shorter_conflict_list_heur_st S\<^sub>0;
      ASSERT(get_clauses_wl_heur S = get_clauses_wl_heur S\<^sub>0 \<and>
           get_learned_count S = get_learned_count S\<^sub>0);
      S \<leftarrow> find_decomp_wl_st_int n S;

      ASSERT(get_clauses_wl_heur S = get_clauses_wl_heur S\<^sub>0 \<and>
           get_learned_count S = get_learned_count S\<^sub>0);
      if size C > 1
      then do {
        S \<leftarrow> propagate_bt_wl_D_heur L C S;
        save_phase_st S
      }
      else do {
        propagate_unit_bt_wl_D_int L S
     }
  }\<close>


lemma empty_cach_ref_set_empty_cach_ref:
  \<open>(empty_cach_ref_set, RETURN o empty_cach_ref) \<in>
    [\<lambda>(cach, supp). (\<forall>L \<in> set supp. L < length cach) \<and> length supp \<le> Suc (uint32_max div 2) \<and>
      (\<forall>L < length cach. cach ! L \<noteq> SEEN_UNKNOWN \<longrightarrow> L \<in> set supp)]\<^sub>f
    Id \<rightarrow> \<langle>Id\<rangle> nres_rel\<close>
proof -
  have H: \<open>WHILE\<^sub>T\<^bsup>empty_cach_ref_set_inv cach0 support'\<^esup> (\<lambda>(i, cach). i < length support')
       (\<lambda>(i, cach).
           ASSERT (i < length support') \<bind>
           (\<lambda>_. ASSERT (support' ! i < length cach) \<bind>
           (\<lambda>_. RETURN (i + 1, cach[support' ! i := SEEN_UNKNOWN]))))
       (0, cach0) \<bind>
      (\<lambda>(_, cach). RETURN (cach, emptied_list support'))
      \<le> \<Down> Id (RETURN (replicate (length cach0) SEEN_UNKNOWN, []))\<close>
    if
      \<open>\<forall>L\<in>set support'. L < length cach0\<close> and
      \<open>\<forall>L<length cach0. cach0 ! L \<noteq> SEEN_UNKNOWN \<longrightarrow> L \<in> set support'\<close>
    for cach support cach0 support'
  proof -
    have init: \<open>empty_cach_ref_set_inv cach0 support' (0, cach0)\<close>
      using that unfolding empty_cach_ref_set_inv_def
      by auto
    have valid_length:
      \<open>empty_cach_ref_set_inv cach0 support' s \<Longrightarrow> case s of (i, cach) \<Rightarrow> i < length support' \<Longrightarrow>
          s = (cach', sup') \<Longrightarrow> support' ! cach' < length sup'\<close>  for s cach' sup'
      using that unfolding empty_cach_ref_set_inv_def
      by auto
    have set_next: \<open>empty_cach_ref_set_inv cach0 support' (i + 1, cach'[support' ! i := SEEN_UNKNOWN])\<close>
      if
        inv: \<open>empty_cach_ref_set_inv cach0 support' s\<close> and
        cond: \<open>case s of (i, cach) \<Rightarrow> i < length support'\<close> and
        s: \<open>s = (i, cach')\<close> and
        valid[simp]: \<open>support' ! i < length cach'\<close>
      for s i cach'
    proof -
      have
        le_cach_cach0: \<open>length cach' = length cach0\<close> and
        le_length: \<open>\<forall>L\<in>set (drop i support'). L < length cach'\<close> and
        UNKNOWN: \<open>\<forall>L\<in>set (take i support'). cach' ! L = SEEN_UNKNOWN\<close> and
        support: \<open>\<forall>L<length cach'. cach' ! L \<noteq> SEEN_UNKNOWN \<longrightarrow> L \<in> set (drop i support')\<close> and
        [simp]: \<open>i < length support'\<close>
        using inv cond unfolding empty_cach_ref_set_inv_def s prod.case
        by auto

      show ?thesis
        unfolding empty_cach_ref_set_inv_def
        unfolding prod.case
        apply (intro conjI)
        subgoal by (simp add: le_cach_cach0)
        subgoal using le_length by (simp add: Cons_nth_drop_Suc[symmetric])
        subgoal using UNKNOWN by (auto simp add: take_Suc_conv_app_nth)
        subgoal using support by (auto simp add: Cons_nth_drop_Suc[symmetric])
        done
    qed
    have final: \<open>((cach', emptied_list support'), replicate (length cach0) SEEN_UNKNOWN, []) \<in> Id\<close>
      if
        inv: \<open>empty_cach_ref_set_inv cach0 support' s\<close> and
        cond: \<open>\<not> (case s of (i, cach) \<Rightarrow> i < length support')\<close> and
        s: \<open>s = (i, cach')\<close>
      for s cach' i
    proof -
      have
        le_cach_cach0: \<open>length cach' = length cach0\<close> and
        le_length: \<open>\<forall>L\<in>set (drop i support'). L < length cach'\<close> and
        UNKNOWN: \<open>\<forall>L\<in>set (take i support'). cach' ! L = SEEN_UNKNOWN\<close> and
        support: \<open>\<forall>L<length cach'. cach' ! L \<noteq> SEEN_UNKNOWN \<longrightarrow> L \<in> set (drop i support')\<close> and
        i: \<open>\<not>i < length support'\<close>
        using inv cond unfolding empty_cach_ref_set_inv_def s prod.case
        by auto
      have \<open>\<forall>L<length cach'. cach' ! L  = SEEN_UNKNOWN\<close>
        using support i by auto
      then have [dest]: \<open>L \<in> set cach' \<Longrightarrow> L = SEEN_UNKNOWN\<close> for L
        by (metis in_set_conv_nth)
      then have [dest]: \<open>SEEN_UNKNOWN \<notin> set cach' \<Longrightarrow> cach0 = [] \<and> cach' = []\<close>
        using le_cach_cach0 by (cases cach') auto
      show ?thesis
        by (auto simp: emptied_list_def list_eq_replicate_iff le_cach_cach0)
    qed
    show ?thesis
      unfolding conc_Id id_def
      apply (refine_vcg WHILEIT_rule[where R = \<open>measure (\<lambda>(i, _). length support' - i)\<close>])
      subgoal by auto
      subgoal by (rule init)
      subgoal by auto
      subgoal by (rule valid_length)
      subgoal by (rule set_next)
      subgoal by auto
      subgoal using final by simp
      done
  qed
  show ?thesis
    unfolding empty_cach_ref_set_def empty_cach_ref_def Let_def comp_def
    by (intro frefI nres_relI ASSERT_leI) (clarify intro!: H ASSERT_leI)

qed

end