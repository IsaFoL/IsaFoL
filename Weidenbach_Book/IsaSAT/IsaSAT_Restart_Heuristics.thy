theory IsaSAT_Restart_Heuristics
imports
  IsaSAT_Restart_Reduce IsaSAT_Restart_Inprocessing
begin

definition restart_required_heur :: \<open>isasat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 8 word nres\<close> where
  \<open>restart_required_heur S last_GC last_Restart n = do {
    ASSERT(learned_clss_count S \<ge> last_Restart);
    ASSERT(learned_clss_count S \<ge> last_GC);
    let opt_red = opts_reduction_st S;
    let opt_res = opts_restart_st S;
    let curr_phase = get_restart_phase S;
    let can_res = (learned_clss_count S > last_Restart);
    let can_GC = (learned_clss_count S - last_GC> n);
    let fully_proped = is_fully_propagated_heur_st S;

    if (\<not>can_res \<and> \<not>can_GC) \<or> \<not>opt_res \<or> \<not>opt_red \<or> \<not>fully_proped then RETURN FLAG_no_restart
    else if curr_phase = QUIET_PHASE
    then do {
      GC_required \<leftarrow> GC_required_heur S n;
      let upper = upper_restart_bound_not_reached S;
      if (opt_res \<or> opt_red) \<and> \<not>upper \<and> can_GC
      then RETURN FLAG_GC_restart
      else if heuristic_reluctant_triggered2_st S \<and> can_res
        then RETURN FLAG_restart
        else RETURN FLAG_no_restart
    }
    else do {
      let sema = ema_get_value (get_slow_ema_heur S);
      let limit = (opts_restart_coeff1_st S) * (shiftr (sema) 4);
      let fema = ema_get_value (get_fast_ema_heur S);
      let ccount = get_conflict_count_since_last_restart_heur S;
      let min_reached = (ccount > opts_minimum_between_restart_st S);
      let level = count_decided_st_heur S;
      let should_reduce = (opt_red \<and> \<not>upper_restart_bound_not_reached S \<and> can_GC);
      let should_restart = ((opt_res) \<and>
         limit > fema \<and> min_reached \<and> can_res \<and>
        level > 2 \<and> \<^cancel>\<open>This comment from Marijn Heule seems not to help:
           \<^term>\<open>level < max_restart_decision_lvl\<close>\<close>
        of_nat level > (shiftr fema 32));
      GC_required \<leftarrow> GC_required_heur S n;
      let should_inprocess = (GC_units_required S \<or> GC_required);
      if should_reduce
        then if should_inprocess
        then RETURN FLAG_Inprocess_restart
        else if GC_required
        then RETURN FLAG_GC_restart
        else RETURN FLAG_Reduce_restart
      else if should_restart
      then RETURN FLAG_restart
      else RETURN FLAG_no_restart
     }
   }\<close>


(*TODO Move clean: cdcl_twl_local_restart_wl_spec0 vs cdcl_twl_local_restart_wl_spec is mess*)


definition cdcl_twl_full_restart_wl_D_GC_heur_prog where
\<open>cdcl_twl_full_restart_wl_D_GC_heur_prog S0 = do {
    _ \<leftarrow> RETURN (IsaSAT_Profile.start_GC);
    S \<leftarrow> do {
      if count_decided_st_heur S0 > 0
      then do {
        S \<leftarrow> find_decomp_wl_st_int 0 S0;
        empty_Q (empty_US_heur S)
      } else RETURN (empty_US_heur S0)
    };
    ASSERT(length (get_clauses_wl_heur S) = length (get_clauses_wl_heur S0));
    ASSERT(learned_clss_count S \<le> learned_clss_count S0);
    T \<leftarrow> remove_one_annot_true_clause_imp_wl_D_heur S;
    ASSERT(length (get_clauses_wl_heur T) = length (get_clauses_wl_heur S0));
    ASSERT(learned_clss_count T \<le> learned_clss_count S0);
    U \<leftarrow> mark_to_delete_clauses_GC_wl_D_heur T;
    ASSERT(length (get_clauses_wl_heur U) = length (get_clauses_wl_heur S0));
    ASSERT(learned_clss_count U \<le> learned_clss_count S0);
    V \<leftarrow> isasat_GC_clauses_wl_D U;
    _ \<leftarrow> RETURN (IsaSAT_Profile.stop_GC);
    RETURN (clss_size_resetUS0_st V)
  }\<close>

lemma cdcl_twl_full_restart_wl_D_GC_heur_prog_alt_def:
  \<open>cdcl_twl_full_restart_wl_D_GC_heur_prog S0 = do {
    S \<leftarrow> do {
    if count_decided_st_heur S0 > 0
    then do {
    S \<leftarrow> find_decomp_wl_st_int 0 S0;
    empty_Q (empty_US_heur S)
    } else RETURN (empty_US_heur S0)
    };
    ASSERT(length (get_clauses_wl_heur S) = length (get_clauses_wl_heur S0));
    ASSERT(learned_clss_count S \<le> learned_clss_count S0);
    T \<leftarrow> remove_one_annot_true_clause_imp_wl_D_heur S;
    ASSERT(length (get_clauses_wl_heur T) = length (get_clauses_wl_heur S0));
    ASSERT(learned_clss_count T \<le> learned_clss_count S0);
    U \<leftarrow> mark_to_delete_clauses_GC_wl_D_heur T;
    ASSERT(length (get_clauses_wl_heur U) = length (get_clauses_wl_heur S0));
    ASSERT(learned_clss_count U \<le> learned_clss_count S0);
    V \<leftarrow> isasat_GC_clauses_wl_D U;
    RETURN (clss_size_resetUS0_st V)
  }\<close>
  unfolding cdcl_twl_full_restart_wl_D_GC_heur_prog_def IsaSAT_Profile.start_def
    IsaSAT_Profile.stop_def by auto

lemma twl_st_heur_twl_st_heur_loopD:
  \<open>(S, T) \<in> twl_st_heur \<Longrightarrow> (S, T) \<in> twl_st_heur_loop\<close> and
  twl_st_heur_loop_twl_st_heurD:
  \<open>(S, T) \<in> twl_st_heur_loop \<Longrightarrow> get_conflict_wl T = None \<Longrightarrow> (S, T) \<in> twl_st_heur\<close>
  by (auto simp: twl_st_heur_loop_def twl_st_heur_def)

lemma
    cdcl_twl_full_restart_wl_GC_prog_pre_heur:
      \<open>cdcl_twl_full_restart_wl_GC_prog_pre T \<Longrightarrow>
        (S, T) \<in> twl_st_heur''' r \<Longrightarrow> (S, T) \<in> twl_st_heur_restart_ana r\<close> (is \<open>_ \<Longrightarrow> ?Apre \<Longrightarrow> ?A\<close>) and
     cdcl_twl_full_restart_wl_D_GC_prog_post_heur:
       \<open>cdcl_twl_full_restart_wl_GC_prog_post S0 T \<Longrightarrow>
       (S, T) \<in> twl_st_heur_restart \<Longrightarrow> (clss_size_resetUS0_st S, T) \<in> twl_st_heur\<close>  (is \<open>_ \<Longrightarrow> _?Bpre \<Longrightarrow> ?B\<close>) and
     cdcl_twl_full_restart_wl_D_GC_prog_post_confl_heur:
       \<open>cdcl_twl_full_restart_wl_GC_prog_post_confl S0 T \<Longrightarrow>
      (S, T) \<in> twl_st_heur_restart \<Longrightarrow> get_conflict_wl T \<noteq> None \<Longrightarrow>
     (S, T) \<in> twl_st_heur_loop\<close>  (is \<open>_ \<Longrightarrow> ?Cpre \<Longrightarrow> ?Cconfl \<Longrightarrow> ?C\<close>)
proof -
  note cong = trail_pol_cong heuristic_rel_cong
      option_lookup_clause_rel_cong D\<^sub>0_cong isa_vmtf_cong phase_saving_cong
      cach_refinement_empty_cong vdom_m_cong isasat_input_nempty_cong
      isasat_input_bounded_cong

  show \<open>cdcl_twl_full_restart_wl_GC_prog_pre T \<Longrightarrow> ?Apre \<Longrightarrow> ?A\<close>
    supply [[goals_limit=1]]
    unfolding cdcl_twl_full_restart_wl_GC_prog_pre_def cdcl_twl_full_restart_l_GC_prog_pre_def
    apply normalize_goal+
    subgoal for U V
      using literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(3)[of T U V]
        cong[of \<open>all_atms_st T\<close> \<open>all_init_atms_st T\<close>]
	vdom_m_cong[of \<open>all_atms_st T\<close> \<open>all_init_atms_st T\<close> \<open>get_watched_wl T\<close> \<open>get_clauses_wl T\<close>]
      apply -
      apply (simp_all del: isasat_input_nempty_def isasat_input_bounded_def)
      apply (cases S; cases T)
      by (auto simp add: twl_st_heur_def twl_st_heur_restart_ana_def all_atms_st_def
        clss_size_corr_restart_def clss_size_corr_def
        twl_st_heur_restart_def all_init_atms_st_def simp del: isasat_input_nempty_def)
    done
  show \<open>cdcl_twl_full_restart_wl_GC_prog_post S0 T \<Longrightarrow> ?Bpre \<Longrightarrow> ?B\<close>
    supply [[goals_limit=1]]
    unfolding cdcl_twl_full_restart_wl_GC_prog_post_def
       cdcl_twl_full_restart_wl_GC_prog_post_def
       cdcl_twl_full_restart_l_GC_prog_pre_def
    apply normalize_goal+
    subgoal for S0' T' S0''
      apply (rule rtranclp_cdcl_twl_restart_l_inp_cdcl_twl_restart_inp[of S0' T' S0''], assumption+)
      apply (frule rtranclp_cdcl_twl_inp_twl_struct_invs, assumption+)
      subgoal for V
        using literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(3)[of T T']
          cong[of \<open>all_init_atms_st T\<close> \<open>all_atms_st T\<close>]
          vdom_m_cong[of \<open>all_init_atms_st T\<close> \<open>all_atms_st T\<close> \<open>get_watched_wl T\<close> \<open>get_clauses_wl T\<close>]
          cdcl_twl_restart_l_invs[of S0' S0'' T']
        apply -
        apply (cases S; cases T)
        by (auto simp add: twl_st_heur_def twl_st_heur_restart_def all_atms_st_def all_init_atms_st_def
            clss_size_resetUS0_st_def
          simp del: isasat_input_nempty_def intro: clss_size_corr_restart_clss_size_corr)
      done
    done
  show \<open>cdcl_twl_full_restart_wl_GC_prog_post_confl S0 T \<Longrightarrow> ?Cpre \<Longrightarrow> ?Cconfl \<Longrightarrow> ?C\<close>
    supply [[goals_limit=1]]
    unfolding cdcl_twl_full_restart_wl_GC_prog_post_confl_def
       cdcl_twl_full_restart_wl_GC_prog_post_def
       cdcl_twl_full_restart_l_GC_prog_pre_def
    apply normalize_goal+
    subgoal for S0' T' S0''
      apply (rule rtranclp_cdcl_twl_restart_l_inp_cdcl_twl_restart_inp[of S0' T' S0''], assumption+)
      apply (frule rtranclp_cdcl_twl_inp_twl_struct_invs, assumption+)
      subgoal for V
        using literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(3)[of T T']
          cong[of \<open>all_init_atms_st T\<close> \<open>all_atms_st T\<close>]
          vdom_m_cong[of \<open>all_init_atms_st T\<close> \<open>all_atms_st T\<close> \<open>get_watched_wl T\<close> \<open>get_clauses_wl T\<close>]
          cdcl_twl_restart_l_invs[of S0' S0'' T']
        apply -
        apply (cases S; cases T)
        by (clarsimp simp add: twl_st_heur_loop_def twl_st_heur_restart_def all_atms_st_def all_init_atms_st_def
          ac_simps
          simp del: isasat_input_nempty_def)
      done
    done
qed

lemma cdcl_twl_full_restart_wl_D_GC_heur_prog:
  \<open>(cdcl_twl_full_restart_wl_D_GC_heur_prog, cdcl_twl_full_restart_wl_GC_prog) \<in>
    twl_st_heur''''u r u \<rightarrow>\<^sub>f \<langle>twl_st_heur''''uu r u\<rangle>nres_rel\<close>
proof -
  have H: \<open>(S, S') \<in> twl_st_heur_restart_ana r \<Longrightarrow>
       (S, S')  \<in> twl_st_heur_restart_ana' r (learned_clss_count S)\<close> for S S'
    by auto
  have H2: \<open>(x, y) \<in> IsaSAT_Setup.twl_st_heur''''u r u \<Longrightarrow>
     cdcl_twl_full_restart_wl_GC_prog_pre y \<Longrightarrow>
    (x, y) \<in> twl_st_heur_restart_ana' r (learned_clss_count x)\<close> for x y
    using cdcl_twl_full_restart_wl_GC_prog_pre_heur[of y x r]
    by auto
  have UUa: \<open>(U, Ua) \<in> twl_st_heur_restart_ana' r u \<Longrightarrow>
    (U, Ua) \<in> twl_st_heur_restart'''u r u\<close> for U Ua r u
    by (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def)
  show ?thesis
    unfolding cdcl_twl_full_restart_wl_D_GC_heur_prog_alt_def
      cdcl_twl_full_restart_wl_GC_prog_def
    apply (intro frefI nres_relI)
    apply (refine_rcg cdcl_twl_local_restart_wl_spec0
      remove_one_annot_true_clause_imp_wl_D_heur_remove_one_annot_true_clause_imp_wl_D[where r=r, THEN fref_to_Down]
      mark_to_delete_clauses_wl_D_heur_mark_to_delete_clauses_GC_wl_D[where r=r, THEN fref_to_Down]
      isasat_GC_clauses_wl_D[where r=r, THEN fref_to_Down])
    apply (rule H2; assumption)
    subgoal
      unfolding cdcl_twl_full_restart_wl_GC_prog_pre_def
        cdcl_twl_full_restart_l_GC_prog_pre_def
      by normalize_goal+ auto
    subgoal by (auto simp: twl_st_heur_restart_ana_def)
    subgoal by (auto simp: twl_st_heur_restart_ana_def)
    apply (assumption)
    subgoal by (auto simp: twl_st_heur_restart_ana_def)
    subgoal by (auto simp: twl_st_heur_restart_ana_def)
    apply (assumption)
    subgoal by (auto simp: twl_st_heur_restart_ana_def)
    subgoal by (auto simp: twl_st_heur_restart_ana_def)
    apply (rule UUa; assumption)
    subgoal for x y S S' T T' U U' V V'
      using learned_clss_count_clss_size_resetUS0_st_le[of V]
      unfolding mem_Collect_eq prod.case
      apply (intro conjI cdcl_twl_full_restart_wl_D_GC_prog_post_heur)
      apply assumption+
      by auto
    done
qed


thm cdcl_twl_full_restart_inprocess_wl_prog_def
  cdcl_twl_full_restart_wl_D_GC_heur_prog_def



definition cdcl_twl_full_restart_wl_D_inprocess_heur_prog where
\<open>cdcl_twl_full_restart_wl_D_inprocess_heur_prog S0 = do {
    _ \<leftarrow> RETURN (IsaSAT_Profile.start_GC);
    S \<leftarrow> do {
      if count_decided_st_heur S0 > 0
      then do {
        S \<leftarrow> find_decomp_wl_st_int 0 S0;
        empty_Q (empty_US_heur S)
      } else RETURN (empty_US_heur S0)
    };
    ASSERT(length (get_clauses_wl_heur S) = length (get_clauses_wl_heur S0));
    ASSERT(learned_clss_count S \<le> learned_clss_count S0);
    T \<leftarrow> remove_one_annot_true_clause_imp_wl_D_heur S;
    ASSERT(length (get_clauses_wl_heur T) = length (get_clauses_wl_heur S0));
        ASSERT(learned_clss_count T \<le> learned_clss_count S0);
    T \<leftarrow> isa_mark_duplicated_binary_clauses_as_garbage_wl2 T;
    ASSERT(length (get_clauses_wl_heur T) = length (get_clauses_wl_heur S0));
        ASSERT(learned_clss_count T \<le> learned_clss_count S0);
    T \<leftarrow> isa_simplify_clauses_with_units_st_wl2 T;
    ASSERT(length (get_clauses_wl_heur T) = length (get_clauses_wl_heur S0));
    ASSERT(learned_clss_count T \<le> learned_clss_count S0);
    if \<not>get_conflict_wl_is_None_heur T then RETURN T
    else do {
      U \<leftarrow> mark_to_delete_clauses_GC_wl_D_heur T;
      ASSERT(length (get_clauses_wl_heur U) = length (get_clauses_wl_heur S0));
      ASSERT(learned_clss_count U \<le> learned_clss_count S0);
      V \<leftarrow> isasat_GC_clauses_wl_D U;
      _ \<leftarrow> RETURN (IsaSAT_Profile.stop_GC);
      RETURN (clss_size_resetUS0_st V)
    }
  }\<close>


lemma cdcl_twl_full_restart_wl_D_inprocess_heur_prog_alt_def:
\<open>cdcl_twl_full_restart_wl_D_inprocess_heur_prog S0 = do {
    S \<leftarrow> do {
      if count_decided_st_heur S0 > 0
      then do {
        S \<leftarrow> find_decomp_wl_st_int 0 S0;
        empty_Q (empty_US_heur S)
      } else RETURN (empty_US_heur S0)
    };
    ASSERT(length (get_clauses_wl_heur S) = length (get_clauses_wl_heur S0));
    ASSERT(learned_clss_count S \<le> learned_clss_count S0);
    T \<leftarrow> remove_one_annot_true_clause_imp_wl_D_heur S;
    ASSERT(length (get_clauses_wl_heur T) = length (get_clauses_wl_heur S0));
        ASSERT(learned_clss_count T \<le> learned_clss_count S0);
    T \<leftarrow> isa_mark_duplicated_binary_clauses_as_garbage_wl2 T;
    ASSERT(length (get_clauses_wl_heur T) = length (get_clauses_wl_heur S0));
        ASSERT(learned_clss_count T \<le> learned_clss_count S0);
    T \<leftarrow> isa_simplify_clauses_with_units_st_wl2 T;
    ASSERT(length (get_clauses_wl_heur T) = length (get_clauses_wl_heur S0));
    ASSERT(learned_clss_count T \<le> learned_clss_count S0);
    if \<not>get_conflict_wl_is_None_heur T then RETURN T
    else do {
      U \<leftarrow> mark_to_delete_clauses_GC_wl_D_heur T;
      ASSERT(length (get_clauses_wl_heur U) = length (get_clauses_wl_heur S0));
      ASSERT(learned_clss_count U \<le> learned_clss_count S0);
      V \<leftarrow> isasat_GC_clauses_wl_D U;
      RETURN (clss_size_resetUS0_st V)
   }
  }\<close>
  unfolding cdcl_twl_full_restart_wl_D_inprocess_heur_prog_def IsaSAT_Profile.start_def
    IsaSAT_Profile.stop_def by (auto intro!: bind_cong[OF refl])

text \<open>We need the plus one if we derive the empty conflict...

  TODO: we don't care about that case and can live with an overflow!\<close>
abbreviation twl_st_heur''''u'
   :: \<open>nat \<Rightarrow> nat \<Rightarrow> (isasat \<times> nat twl_st_wl) set\<close>
where
\<open>twl_st_heur''''u' r u \<equiv> {(S, T). (S, T) \<in> twl_st_heur \<and>
           length (get_clauses_wl_heur S) = r \<and>
           (get_conflict_wl T = None \<longrightarrow> learned_clss_count S \<le> u) \<and>
           (get_conflict_wl T \<noteq> None \<longrightarrow> learned_clss_count S \<le> u+1)}\<close>


lemma isa_simplify_clauses_with_unit_st2_isa_simplify_clauses_with_unit_wl:
  assumes \<open>(S,S') \<in> twl_st_heur_restart_ana' r u\<close>
  shows
    \<open>isa_simplify_clauses_with_units_st_wl2 S \<le> \<Down> (twl_st_heur_restart_ana' r u) (simplify_clauses_with_units_st_wl S')\<close>
  apply (rule order_trans)
    defer
  apply (rule ref_two_step')
  apply (rule simplify_clauses_with_units_st_wl2_simplify_clauses_with_units_st_wl[unfolded Down_id_eq, of _ S'])
  subgoal by auto
  subgoal
    apply (rule isa_simplify_clauses_with_units_st2_simplify_clauses_with_units_st2[THEN order_trans, of _ S'])
    apply (rule assms)
    subgoal using assms by auto
    done
  done

abbreviation twl_st_heur_loop''''uu where
  \<open>twl_st_heur_loop''''uu r u \<equiv> {(S, T). (S, T) \<in> twl_st_heur_loop \<and> length (get_clauses_wl_heur S) \<le> r \<and>
    learned_clss_count S \<le> u}\<close>

lemma cdcl_twl_full_restart_wl_D_inprocess_heur_prog:
  \<open>(cdcl_twl_full_restart_wl_D_inprocess_heur_prog, cdcl_twl_full_restart_inprocess_wl_prog) \<in>
    twl_st_heur''''u r u \<rightarrow>\<^sub>f \<langle>twl_st_heur_loop''''uu r u\<rangle>nres_rel\<close>
proof -
  have H: \<open>(S, S') \<in> twl_st_heur_restart_ana r \<Longrightarrow>
       (S, S')  \<in> twl_st_heur_restart_ana' r (learned_clss_count S)\<close> for S S'
    by auto
  have H2: \<open>(x, y) \<in> IsaSAT_Setup.twl_st_heur''''u r u \<Longrightarrow>
     cdcl_twl_full_restart_wl_GC_prog_pre y \<Longrightarrow>
    (x, y) \<in> twl_st_heur_restart_ana' r (learned_clss_count x)\<close> for x y
    using cdcl_twl_full_restart_wl_GC_prog_pre_heur[of y x r]
    by auto
  have UUa: \<open>(U, Ua) \<in> twl_st_heur_restart_ana' r u \<Longrightarrow>
    (U, Ua) \<in> twl_st_heur_restart'''u r u\<close> for U Ua r u
    by (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def)
  show ?thesis
    unfolding cdcl_twl_full_restart_wl_D_inprocess_heur_prog_alt_def
      cdcl_twl_full_restart_inprocess_wl_prog_def
    apply (intro frefI nres_relI)
    apply (refine_rcg cdcl_twl_local_restart_wl_spec0
      remove_one_annot_true_clause_imp_wl_D_heur_remove_one_annot_true_clause_imp_wl_D[where r=r, THEN fref_to_Down]
      mark_to_delete_clauses_wl_D_heur_mark_to_delete_clauses_GC_wl_D[where r=r, THEN fref_to_Down]
      isasat_GC_clauses_wl_D[where r=r, THEN fref_to_Down]
      isa_simplify_clauses_with_unit_st2_isa_simplify_clauses_with_unit_wl[where r=r]
      isa_mark_duplicated_binary_clauses_as_garbage_wl_mark_duplicated_binary_clauses_as_garbage_wl2[where r=r])
    apply (rule H2; assumption)
    subgoal
      unfolding cdcl_twl_full_restart_wl_GC_prog_pre_def
        cdcl_twl_full_restart_l_GC_prog_pre_def
      by normalize_goal+ auto
    subgoal by (auto simp: twl_st_heur_restart_ana_def)
    subgoal by (auto simp: twl_st_heur_restart_ana_def)
    apply (assumption)
    subgoal by (auto simp: twl_st_heur_restart_ana_def)
    subgoal by (auto simp: twl_st_heur_restart_ana_def)
    apply (solves auto)
    subgoal by (auto simp: twl_st_heur_restart_ana_def)
    subgoal by (auto simp: twl_st_heur_restart_ana_def)
    apply (assumption)
    subgoal by (auto simp: twl_st_heur_restart_ana_def)
    subgoal by (auto simp: twl_st_heur_restart_ana_def)
    subgoal
      by (subst get_conflict_wl_is_None_heur_get_conflict_wl_is_None_ana[THEN fref_to_Down_unRET_Id])
        (auto simp: get_conflict_wl_is_None_def)
    subgoal for x y
      unfolding mem_Collect_eq prod.case
      apply (subst cdcl_twl_full_restart_wl_D_GC_prog_post_confl_heur)
      apply assumption
      by (auto simp: twl_st_heur_restart_ana_def)
    apply (assumption)
    subgoal by (auto simp: twl_st_heur_restart_ana_def)
    subgoal by (auto simp: twl_st_heur_restart_ana_def)
    apply (rule UUa; assumption)
    subgoal for x y S S' T T' U U' V V' W W' X X'
      using learned_clss_count_clss_size_resetUS0_st_le[of X]
      unfolding mem_Collect_eq prod.case
      apply (intro conjI )
      by (auto intro: twl_st_heur_twl_st_heur_loopD intro!: cdcl_twl_full_restart_wl_D_GC_prog_post_heur)
    done
qed

definition restart_prog_wl_D_heur
  :: \<open>isasat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> (isasat \<times> nat \<times> nat \<times> nat) nres\<close>
where
  \<open>restart_prog_wl_D_heur S last_GC last_Restart n brk = do {
   if brk then RETURN (S, last_GC, last_Restart, n)
   else do {
      b \<leftarrow> restart_required_heur S last_GC last_Restart n;
      if b = FLAG_restart
      then do {
         T \<leftarrow> cdcl_twl_restart_wl_heur S;
         ASSERT(learned_clss_count T \<le> learned_clss_count S);
         RETURN (T, last_GC, learned_clss_count T, n)
      }
      else if b \<noteq> FLAG_no_restart
      then if b \<noteq> FLAG_Inprocess_restart then do {
         if b = FLAG_Reduce_restart
         then do {
           T \<leftarrow> cdcl_twl_full_restart_wl_prog_heur S;
           ASSERT(learned_clss_count T \<le> learned_clss_count S);
           RETURN (T, learned_clss_count T, learned_clss_count T, n+1)
         }
         else do {
           T \<leftarrow> cdcl_twl_full_restart_wl_D_GC_heur_prog S;
           ASSERT(learned_clss_count T \<le> learned_clss_count S);
           RETURN (T, learned_clss_count T, learned_clss_count T, n+1)
         }
     } else do {
         T \<leftarrow> cdcl_twl_full_restart_wl_D_inprocess_heur_prog S;
         ASSERT(learned_clss_count T \<le> learned_clss_count S);
         RETURN (T, learned_clss_count T, learned_clss_count T, n+1)
     }
      else RETURN (S, last_GC, last_Restart, n)
    }
  }\<close>

lemma restart_required_heur_restart_required_wl0:
  \<open>(uncurry3 restart_required_heur, uncurry3 restart_required_wl) \<in>
    [\<lambda>(((S, _), _), _). (get_init_clauses0_wl S = {#} \<and> get_learned_clauses0_wl S = {#})]\<^sub>f
    twl_st_heur''' r \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<rightarrow> \<langle>restart_flag_rel\<rangle>nres_rel\<close>
    unfolding restart_required_heur_def restart_required_wl_def uncurry_def Let_def
      restart_flag_rel_def  FLAG_GC_restart_def FLAG_restart_def FLAG_no_restart_def
      GC_required_heur_def FLAG_Reduce_restart_def learned_clss_count_def
      FLAG_Inprocess_restart_def
    apply (intro frefI nres_relI)
    apply refine_rcg
    subgoal
      by
       (auto simp add: twl_st_heur_def get_learned_clss_wl_def clss_size_lcountU0_def
        clss_size_def clss_size_lcount_def clss_size_lcountUE_def clss_size_corr_def
        clss_size_lcountUS_def clss_size_lcountUEk_def get_unit_learned_clss_wl_alt_def)
    subgoal
      by
       (auto simp add: twl_st_heur_def get_learned_clss_wl_def clss_size_lcountU0_def
        clss_size_def clss_size_lcount_def clss_size_lcountUE_def clss_size_corr_def
        clss_size_lcountUS_def clss_size_lcountUEk_def get_unit_learned_clss_wl_alt_def)
    subgoal
      by (clarsimp split: if_splits simp add: twl_st_heur_def RETURN_RES_refine_iff)
        (clarsimp simp add: twl_st_heur_def get_learned_clss_wl_def clss_size_corr_def
          clss_size_def clss_size_lcount_def clss_size_lcountUE_def RETURN_RES_refine_iff
         clss_size_lcountUS_def clss_size_lcountU0_def clss_size_lcountUEk_def ac_simps
        get_unit_learned_clss_wl_alt_def)
   done

lemma restart_prog_wl_D_heur_alt_def:
  \<open>restart_prog_wl_D_heur S last_GC last_Restart n brk =
    (if brk then RETURN (S, last_GC, last_Restart, n)
    else do {
    b \<leftarrow> restart_required_heur S last_GC last_Restart n;
    if b = FLAG_restart
    then do {
       T \<leftarrow> cdcl_twl_restart_wl_heur S;
       ASSERT(learned_clss_count T \<le> learned_clss_count S);
       RETURN (T, last_GC, learned_clss_count T, n)
    }
    else if b \<noteq> FLAG_no_restart
    then if b \<noteq> FLAG_Inprocess_restart then do {
       let b = b;
       T \<leftarrow> (if b = FLAG_Reduce_restart
          then cdcl_twl_full_restart_wl_prog_heur S
          else  cdcl_twl_full_restart_wl_D_GC_heur_prog S);
       ASSERT(learned_clss_count T \<le> learned_clss_count S);
       RETURN (T, learned_clss_count T, learned_clss_count T, n+1)
    }
    else do {
         T \<leftarrow> cdcl_twl_full_restart_wl_D_inprocess_heur_prog S;
         ASSERT(learned_clss_count T \<le> learned_clss_count S);
         RETURN (T, learned_clss_count T, learned_clss_count T, n+1)
     }
    else RETURN (S, last_GC, last_Restart, n)
  })\<close>
   unfolding restart_prog_wl_D_heur_def Let_def
   by (auto intro: bind_cong[OF refl])


lemma cdcl_twl_full_restart_wl_prog_heur_cdcl_twl_full_restart_wl_prog_D2:
  \<open>(cdcl_twl_full_restart_wl_prog_heur, cdcl_twl_full_restart_wl_prog) \<in>
     twl_st_heur''''u r u \<rightarrow>\<^sub>f \<langle>twl_st_heur''''uu r u\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (rule order_trans[OF cdcl_twl_full_restart_wl_prog_heur_cdcl_twl_full_restart_wl_prog_D[THEN fref_to_Down]])
  apply fast
  apply assumption
  apply (rule conc_fun_R_mono)
  by auto

lemma restart_prog_wl_alt_def2:
  \<open>restart_prog_wl S last_GC last_Restart n brk = do{
     ASSERT(restart_abs_wl_pre S last_GC last_Restart brk);
     ASSERT (last_GC
            \<le> size (get_learned_clss_wl S) + size (get_unit_learned_clss_wl S) +
              size (get_subsumed_learned_clauses_wl S) +
              size (get_learned_clauses0_wl S));
    ASSERT  (last_Restart
            \<le> size (get_learned_clss_wl S) + size (get_unit_learned_clss_wl S) +
              size (get_subsumed_learned_clauses_wl S) +
              size (get_learned_clauses0_wl S));
    if brk then RETURN (S, last_GC, last_Restart, n)
    else do {
     b \<leftarrow> restart_required_wl S last_GC last_Restart n;
     if b = RESTART \<and> \<not>brk then do {
       T \<leftarrow> cdcl_twl_restart_wl_prog S;
       RETURN (T, last_GC, size (get_all_learned_clss_wl T), n)
     }
     else if (b = GC \<or> b = INPROCESS) \<and> \<not>brk then
        if b \<noteq> INPROCESS then do {
          b \<leftarrow> SPEC(\<lambda>_. True);
          T \<leftarrow> (if b then cdcl_twl_full_restart_wl_prog S else cdcl_twl_full_restart_wl_GC_prog S);
          RETURN (T, size (get_all_learned_clss_wl T), size (get_all_learned_clss_wl T), n + 1)
        } else do {
          T \<leftarrow> cdcl_twl_full_restart_inprocess_wl_prog S;
          RETURN (T, size (get_all_learned_clss_wl T), size (get_all_learned_clss_wl T), n + 1)
       }
     else
       RETURN (S, last_GC, last_Restart, n)
   }}\<close> (is \<open>?A = ?B\<close>)
proof -
  have \<open>?A \<le> \<Down> Id ?B\<close>
    unfolding restart_prog_wl_def restart_required_wl_def
    by refine_vcg
      (auto simp: restart_required_wl_def RES_RETURN_RES intro!: bind_cong[OF refl])
  moreover have \<open>?B \<le> \<Down> Id ?A\<close>
    unfolding restart_prog_wl_def restart_required_wl_def nres_monad3
    by refine_vcg
      (auto simp: restart_required_wl_def RES_RETURN_RES intro!: bind_cong[OF refl])
  ultimately show ?thesis by simp
qed

lemma restart_abs_wl_pre_emptyN0S:
  assumes \<open>restart_abs_wl_pre S lastGC lastRestart C\<close> and [simp]: \<open>\<not>C\<close>
  shows \<open>get_init_clauses0_wl S = {#} \<and> get_learned_clauses0_wl S = {#}\<close>
proof -
  obtain x xa where
    Sx: \<open>(S, x) \<in> state_wl_l None\<close> and
    \<open>correct_watching S\<close> and
    \<open>blits_in_\<L>\<^sub>i\<^sub>n S\<close> and
    xxa: \<open>(x, xa) \<in> twl_st_l None\<close> and
    struct: \<open>twl_struct_invs xa\<close> and
    \<open>twl_list_invs x\<close> and
    \<open>clauses_to_update_l x = {#}\<close> and
    \<open>twl_stgy_invs xa\<close> and
    \<open>\<not> C \<longrightarrow> get_conflict xa = None\<close> and
    \<open>lastRestart \<le> size (get_all_learned_clss xa)\<close> and
    \<open>lastGC \<le> size (get_all_learned_clss xa)\<close>
    using assms unfolding restart_abs_wl_pre_def restart_abs_l_pre_def restart_prog_pre_def apply -
    apply normalize_goal+
    by fast

  then have \<open>get_conflict xa = None\<close>
    by simp
  moreover have \<open>clauses0_inv (pstate\<^sub>W_of xa)\<close>
    using struct unfolding twl_struct_invs_def pcdcl_all_struct_invs_def by fast
  ultimately have \<open>get_init_clauses0 xa = {#} \<and> get_learned_clauses0 xa = {#}\<close>
    unfolding clauses0_inv_def
    by (cases xa; auto simp: clauses0_inv_def)
  then show ?thesis
    using Sx xxa by auto
qed

abbreviation restart_prog_wl_heur_rel :: \<open>_\<close> where
  \<open>restart_prog_wl_heur_rel r u\<equiv> {((T, a, b, c), (U, d, e, f)). 
  (T,U) \<in> twl_st_heur_loop''''uu r u \<and>
  (get_conflict_wl U = None \<longrightarrow>((a,b,c), (d,e,f)) \<in> nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel)}\<close>

abbreviation restart_prog_wl_heur_rel2 :: \<open>_\<close> where
  \<open>restart_prog_wl_heur_rel2\<equiv> {((T, a, b, c), (U, d, e, f)). 
  (T,U) \<in> twl_st_heur_loop \<and>
  (get_conflict_wl U = None \<longrightarrow>((a,b,c), (d,e,f)) \<in> nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel)}\<close>

lemma restart_prog_wl_D_heur_restart_prog_wl_D:
  \<open>(uncurry4 restart_prog_wl_D_heur, uncurry4 restart_prog_wl) \<in>
  twl_st_heur''''u r u \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f bool_rel  \<rightarrow>\<^sub>f
  \<langle>restart_prog_wl_heur_rel r u\<rangle>nres_rel\<close>
proof -
  have [refine0]: \<open>RETURN b \<le> \<Down>{(c, c'). c' \<longleftrightarrow> (c = FLAG_Reduce_restart)} (SPEC (\<lambda>_::bool. True))\<close> for b
    by (auto simp: GC_required_heur_def RETURN_RES_refine_iff)
  have H: \<open>(x1g, x1c)
        \<in> twl_st_heur''''u r (learned_clss_count x1g)\<close>
    if
      \<open>(x, y)
       \<in> twl_st_heur''''u r u \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f bool_rel\<close> and
      \<open>x1b = (x1c, x2)\<close> and
      \<open>x1a = (x1b, x2a)\<close> and
      \<open>x1 = (x1a, x2b)\<close> and
      \<open>y = (x1, x2c)\<close> and
      \<open>x1f = (x1g, x2d)\<close> and
      \<open>x1e = (x1f, x2e)\<close> and
      \<open>x1d = (x1e, x2f)\<close> and
      \<open>x = (x1d, x2g)\<close> 
    for x y x1 x1a x1b x1c x2 x2a x2b x2c x1d x1e x1f x1g x2d x2e x2f x2g b ba bb
    using that by auto

  show ?thesis
    supply RETURN_as_SPEC_refine[refine2 del] learned_clss_count_twl_st_heur[simp]
    unfolding restart_prog_wl_D_heur_alt_def restart_prog_wl_alt_def2 uncurry_def
    apply (intro frefI nres_relI)
    subgoal for x y
    apply (refine_rcg
      restart_required_heur_restart_required_wl0[where r=r, THEN fref_to_Down_curry3]
        cdcl_twl_restart_wl_heur_cdcl_twl_restart_wl_D_prog[where r=r, THEN fref_to_Down]
        cdcl_twl_full_restart_wl_D_GC_heur_prog[where r=r, THEN fref_to_Down, THEN order_trans]
      cdcl_twl_full_restart_wl_prog_heur_cdcl_twl_full_restart_wl_prog_D2[where r=r and
      u = \<open>learned_clss_count (fst (fst (fst (fst x))))\<close>, THEN fref_to_Down]
      cdcl_twl_full_restart_wl_D_inprocess_heur_prog[where r=r and
      u = \<open>learned_clss_count (fst (fst (fst (fst x))))\<close>, THEN fref_to_Down])
    subgoal by auto
    subgoal by (auto intro!: twl_st_heur_twl_st_heur_loopD)
    subgoal by (auto dest: restart_abs_wl_pre_emptyN0S)
    subgoal by (auto dest: restart_abs_wl_pre_emptyN0S)
    subgoal by auto
    subgoal by (auto simp: restart_flag_rel_def FLAG_GC_restart_def FLAG_restart_def
      FLAG_no_restart_def FLAG_Reduce_restart_def FLAG_Inprocess_restart_def)
    apply (rule twl_st_heur'''_twl_st_heur''''uD)
    subgoal by auto
    subgoal by auto
    subgoal by (auto intro!: twl_st_heur_twl_st_heur_loopD)
    subgoal by (auto simp: restart_flag_rel_def FLAG_GC_restart_def FLAG_restart_def
      FLAG_no_restart_def FLAG_Reduce_restart_def FLAG_Inprocess_restart_def)
    subgoal by (auto simp: restart_flag_rel_def FLAG_GC_restart_def FLAG_restart_def
      FLAG_no_restart_def FLAG_Reduce_restart_def FLAG_Inprocess_restart_def)
    subgoal by (auto simp: restart_flag_rel_def FLAG_GC_restart_def FLAG_restart_def
      FLAG_no_restart_def FLAG_Reduce_restart_def FLAG_Inprocess_restart_def)
    subgoal by auto
    apply (rule H; assumption)
    subgoal for x1 x1a x1b x1c x2 x2a x2b x2c x1d x1e x1f x1g x2d x2e x2f x2g b ba bb
      by (rule conc_fun_R_mono) auto
    subgoal
      by auto
    subgoal
      by (auto dest: restart_abs_wl_pre_emptyN0S intro!: twl_st_heur_twl_st_heur_loopD)
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      by (auto dest: restart_abs_wl_pre_emptyN0S dest!: twl_st_heur_loop_twl_st_heurD)
    subgoal
      by (auto intro!: twl_st_heur_twl_st_heur_loopD)
    done
  done
 qed

lemma restart_prog_wl_D_heur_restart_prog_wl_D2:
  \<open>(uncurry4 restart_prog_wl_D_heur, uncurry4 restart_prog_wl) \<in>
  twl_st_heur \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f bool_rel \<rightarrow>\<^sub>f \<langle>restart_prog_wl_heur_rel2\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (rule_tac r2 = \<open>length(get_clauses_wl_heur (fst (fst (fst (fst x)))))\<close> and
       u2 = \<open>learned_clss_count (fst (fst (fst (fst x))))\<close> in
    order_trans[OF restart_prog_wl_D_heur_restart_prog_wl_D[THEN fref_to_Down]])
  apply fast
  apply (auto intro!: conc_fun_R_mono)
  done

end
