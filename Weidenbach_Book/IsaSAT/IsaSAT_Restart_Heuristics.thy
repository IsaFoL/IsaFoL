theory IsaSAT_Restart_Heuristics
imports
  IsaSAT_Restart_Reduce IsaSAT_Restart_Inprocessing
begin

definition restart_required_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 8 word nres\<close> where
  \<open>restart_required_heur S last_GC last_Restart n = do {
    ASSERT(learned_clss_count S \<ge> last_Restart);
    ASSERT(learned_clss_count S \<ge> last_GC);
    let opt_red = opts_reduction_st S;
    let opt_res = opts_restart_st S;
    let curr_phase = get_restart_phase S;
    let can_res = (learned_clss_count S > last_Restart);
    let can_GC = (learned_clss_count S - last_GC> n);
    let should_inprocess = GC_units_required S;

    if (\<not>can_res \<and> \<not>can_GC) \<or> \<not>opt_res \<or> \<not>opt_red then RETURN FLAG_no_restart
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
    RETURN V
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
    RETURN V
  }\<close>
  unfolding cdcl_twl_full_restart_wl_D_GC_heur_prog_def IsaSAT_Profile.start_def
    IsaSAT_Profile.stop_def by auto

lemma
    cdcl_twl_full_restart_wl_GC_prog_pre_heur:
      \<open>cdcl_twl_full_restart_wl_GC_prog_pre T \<Longrightarrow>
        (S, T) \<in> twl_st_heur''' r \<longleftrightarrow> (S, T) \<in> twl_st_heur_restart_ana r\<close> (is \<open>_ \<Longrightarrow> _ ?A\<close>) and
     cdcl_twl_full_restart_wl_D_GC_prog_post_heur:
       \<open>cdcl_twl_full_restart_wl_GC_prog_post S0 T \<Longrightarrow>
        (S, T) \<in> twl_st_heur \<longleftrightarrow> (S, T) \<in> twl_st_heur_restart\<close>  (is \<open>_ \<Longrightarrow> _ ?B\<close>) and
     cdcl_twl_full_restart_wl_D_GC_prog_post_confl_heur:
       \<open>cdcl_twl_full_restart_wl_GC_prog_post_confl S0 T \<Longrightarrow>
        (S, T) \<in> twl_st_heur \<longleftrightarrow> (S, T) \<in> twl_st_heur_restart\<close>  (is \<open>_ \<Longrightarrow> _ ?C\<close>)
proof -
  note cong = trail_pol_cong heuristic_rel_cong
      option_lookup_clause_rel_cong D\<^sub>0_cong isa_vmtf_cong phase_saving_cong
      cach_refinement_empty_cong vdom_m_cong isasat_input_nempty_cong
      isasat_input_bounded_cong

  show \<open>cdcl_twl_full_restart_wl_GC_prog_pre T \<Longrightarrow> ?A\<close>
    supply [[goals_limit=1]]
    unfolding cdcl_twl_full_restart_wl_GC_prog_pre_def cdcl_twl_full_restart_l_GC_prog_pre_def
    apply normalize_goal+
    apply (rule iffI)
    subgoal for U V
      using literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(3)[of T U V]
        cong[of \<open>all_atms_st T\<close> \<open>all_init_atms_st T\<close>]
	vdom_m_cong[of \<open>all_atms_st T\<close> \<open>all_init_atms_st T\<close> \<open>get_watched_wl T\<close> \<open>get_clauses_wl T\<close>]
      apply -
      apply (simp_all del: isasat_input_nempty_def isasat_input_bounded_def)
      apply (cases S; cases T)
      by (simp add: twl_st_heur_def twl_st_heur_restart_ana_def all_atms_st_def
        twl_st_heur_restart_def all_init_atms_st_def del: isasat_input_nempty_def)
    subgoal for U V
      using literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(3)[of T U V]
        cong[of \<open>all_init_atms_st T\<close> \<open>all_atms_st T\<close>]
	vdom_m_cong[of \<open>all_init_atms_st T\<close> \<open>all_atms_st T\<close> \<open>get_watched_wl T\<close> \<open>get_clauses_wl T\<close>]
      apply -
      by (cases S; cases T)
         (simp add: twl_st_heur_def twl_st_heur_restart_ana_def all_init_atms_st_def
        twl_st_heur_restart_def del: isasat_input_nempty_def)
    done
  show \<open>cdcl_twl_full_restart_wl_GC_prog_post S0 T \<Longrightarrow> ?B\<close>
    supply [[goals_limit=1]]
    unfolding cdcl_twl_full_restart_wl_GC_prog_post_def
       cdcl_twl_full_restart_wl_GC_prog_post_def
       cdcl_twl_full_restart_l_GC_prog_pre_def
    apply normalize_goal+
    subgoal for S0' T' S0''
    apply (rule iffI)
    subgoal
      apply (rule rtranclp_cdcl_twl_restart_l_inp_cdcl_twl_restart_inp[of S0' T' S0''], assumption+)
      apply (frule rtranclp_cdcl_twl_inp_twl_struct_invs, assumption+)
      subgoal for V
        using literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(3)[of T T' V]
          cong[of \<open>all_atms_st T\<close> \<open>all_init_atms_st T\<close>]
          vdom_m_cong[of \<open>all_atms_st T\<close> \<open>all_init_atms_st T\<close> \<open>get_watched_wl T\<close> \<open>get_clauses_wl T\<close>]
        apply -
        apply (clarsimp simp del: isasat_input_nempty_def isasat_input_bounded_def)
        apply (cases S; cases T; cases T'; cases V)
        apply (simp add: twl_st_heur_def twl_st_heur_restart_def all_atms_st_def all_init_atms_st_def
          del: isasat_input_nempty_def)
        using isa_vmtf_cong option_lookup_clause_rel_cong trail_pol_cong heuristic_rel_cong
        by presburger+
      done
    subgoal
      apply (rule rtranclp_cdcl_twl_restart_l_inp_cdcl_twl_restart_inp[of S0' T' S0''], assumption+)
      apply (frule rtranclp_cdcl_twl_inp_twl_struct_invs, assumption+)
      subgoal for V
        using literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(3)[of T T']
          cong[of \<open>all_init_atms_st T\<close> \<open>all_atms_st T\<close>]
          vdom_m_cong[of \<open>all_init_atms_st T\<close> \<open>all_atms_st T\<close> \<open>get_watched_wl T\<close> \<open>get_clauses_wl T\<close>]
          cdcl_twl_restart_l_invs[of S0' S0'' T']
        apply -
        apply (cases S; cases T)
        by (clarsimp simp add: twl_st_heur_def twl_st_heur_restart_def all_atms_st_def all_init_atms_st_def
          simp del: isasat_input_nempty_def)
      done
    done
    done
  show \<open>cdcl_twl_full_restart_wl_GC_prog_post_confl S0 T \<Longrightarrow> ?B\<close>
    supply [[goals_limit=1]]
    unfolding cdcl_twl_full_restart_wl_GC_prog_post_confl_def
       cdcl_twl_full_restart_wl_GC_prog_post_def
       cdcl_twl_full_restart_l_GC_prog_pre_def
    apply normalize_goal+
    subgoal for S0' T' S0''
    apply (rule iffI)
    subgoal
      apply (rule rtranclp_cdcl_twl_restart_l_inp_cdcl_twl_restart_inp[of S0' T' S0''], assumption+)
      apply (frule rtranclp_cdcl_twl_inp_twl_struct_invs, assumption+)
      subgoal for V
        using literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(3)[of T T' V]
          cong[of \<open>all_atms_st T\<close> \<open>all_init_atms_st T\<close>]
          vdom_m_cong[of \<open>all_atms_st T\<close> \<open>all_init_atms_st T\<close> \<open>get_watched_wl T\<close> \<open>get_clauses_wl T\<close>]
        apply -
        apply (clarsimp simp del: isasat_input_nempty_def isasat_input_bounded_def)
        apply (cases S; cases T; cases T'; cases V)
        apply (simp add: twl_st_heur_def twl_st_heur_restart_def all_atms_st_def all_init_atms_st_def
          del: isasat_input_nempty_def)
        using isa_vmtf_cong option_lookup_clause_rel_cong trail_pol_cong heuristic_rel_cong
        by presburger+
      done
    subgoal
      apply (rule rtranclp_cdcl_twl_restart_l_inp_cdcl_twl_restart_inp[of S0' T' S0''], assumption+)
      apply (frule rtranclp_cdcl_twl_inp_twl_struct_invs, assumption+)
      subgoal for V
        using literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(3)[of T T']
          cong[of \<open>all_init_atms_st T\<close> \<open>all_atms_st T\<close>]
          vdom_m_cong[of \<open>all_init_atms_st T\<close> \<open>all_atms_st T\<close> \<open>get_watched_wl T\<close> \<open>get_clauses_wl T\<close>]
          cdcl_twl_restart_l_invs[of S0' S0'' T']
        apply -
        apply (cases S; cases T)
        by (clarsimp simp add: twl_st_heur_def twl_st_heur_restart_def all_atms_st_def all_init_atms_st_def
          simp del: isasat_input_nempty_def)
      done
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
    subgoal for x y
      unfolding mem_Collect_eq prod.case
      apply (subst cdcl_twl_full_restart_wl_D_GC_prog_post_heur)
      apply assumption
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
    T \<leftarrow> isa_simplify_clauses_with_unit_st2 T;
    ASSERT(length (get_clauses_wl_heur T) = length (get_clauses_wl_heur S0));
    ASSERT(learned_clss_count T \<le> learned_clss_count S0);
    if \<not>get_conflict_wl_is_None_heur T then RETURN T
    else do {
      U \<leftarrow> mark_to_delete_clauses_GC_wl_D_heur T;
      ASSERT(length (get_clauses_wl_heur U) = length (get_clauses_wl_heur S0));
      ASSERT(learned_clss_count U \<le> learned_clss_count S0);
      V \<leftarrow> isasat_GC_clauses_wl_D U;
      _ \<leftarrow> RETURN (IsaSAT_Profile.stop_GC);
      RETURN V
    }
  }\<close>
thm restart_prog_wl_def

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
    T \<leftarrow> isa_simplify_clauses_with_unit_st2 T;
    ASSERT(length (get_clauses_wl_heur T) = length (get_clauses_wl_heur S0));
    ASSERT(learned_clss_count T \<le> learned_clss_count S0);
    if \<not>get_conflict_wl_is_None_heur T then RETURN T
    else do {
      U \<leftarrow> mark_to_delete_clauses_GC_wl_D_heur T;
      ASSERT(length (get_clauses_wl_heur U) = length (get_clauses_wl_heur S0));
      ASSERT(learned_clss_count U \<le> learned_clss_count S0);
      V \<leftarrow> isasat_GC_clauses_wl_D U;
      RETURN V
   }
  }\<close>
  unfolding cdcl_twl_full_restart_wl_D_inprocess_heur_prog_def IsaSAT_Profile.start_def
    IsaSAT_Profile.stop_def by (auto intro!: bind_cong[OF refl])

text \<open>We need the plus one if we derive the empty conflict...

  TODO: we don't care about that case and can live with an overflow!\<close>
abbreviation twl_st_heur''''u'
   :: \<open>nat \<Rightarrow> nat \<Rightarrow> (twl_st_wl_heur \<times> nat twl_st_wl) set\<close>
where
\<open>twl_st_heur''''u' r u \<equiv> {(S, T). (S, T) \<in> twl_st_heur \<and>
           length (get_clauses_wl_heur S) = r \<and>
           (get_conflict_wl T = None \<longrightarrow> learned_clss_count S \<le> u) \<and>
           (get_conflict_wl T \<noteq> None \<longrightarrow> learned_clss_count S \<le> u+1)}\<close>

lemma isa_simplify_clause_with_unit_st2_simplify_clause_with_unit_st2:
  assumes \<open>(S, S') \<in> (twl_st_heur''''u' r u)\<close> and \<open>(C,C')\<in> nat_rel\<close>
  shows \<open>isa_simplify_clause_with_unit_st2 C S \<le>
    \<Down>(twl_st_heur''''u' r (u)) (simplify_clause_with_unit_st2 C' S')\<close>
  oops
(*
proof -
  have H: \<open>A = B \<Longrightarrow> x \<in> A \<Longrightarrow> x \<in> B\<close> for A B x
    by auto
  have H': \<open>A = B \<Longrightarrow> A x \<Longrightarrow> B x\<close> for A B x
    by auto
  have H'': \<open>A = B \<Longrightarrow> A \<subseteq> c \<Longrightarrow> B \<subseteq> c\<close> for A B c
    by auto

  have vdom_m_cong2: \<open>set_mset \<A> = set_mset \<B> \<Longrightarrow> vdom_m \<A> W N \<subseteq> vd \<Longrightarrow> dom_m N' \<subseteq># dom_m N \<Longrightarrow>
    vdom_m \<B> W N' \<subseteq> vd\<close>
    for \<A> W N N' vd \<B>
    by (subst vdom_m_cong[of \<B> \<A>])
      (auto simp: vdom_m_def)
  note cong =  trail_pol_cong heuristic_rel_cong
    option_lookup_clause_rel_cong isa_vmtf_cong
    vdom_m_cong[THEN H] isasat_input_nempty_cong[THEN iffD1]
    isasat_input_bounded_cong[THEN iffD1]
    cach_refinement_empty_cong[THEN H']
    phase_saving_cong[THEN H']
    \<L>\<^sub>a\<^sub>l\<^sub>l_cong[THEN H]
    D\<^sub>0_cong[THEN H]
    D\<^sub>0_cong[OF sym]
    vdom_m_cong[THEN H'']
    vdom_m_cong2
  have set_conflict_to_false: \<open>(a, None) \<in> option_lookup_clause_rel \<A> \<Longrightarrow>
    (set_conflict_to_false a, Some {#}) \<in> option_lookup_clause_rel \<A>\<close> for a \<A>
    by (auto simp: option_lookup_clause_rel_def set_conflict_to_false_def
      lookup_clause_rel_def)
  have outl: \<open>out_learned x1 None x1s \<Longrightarrow> out_learned x1 (Some {#}) (x1s)\<close>
    \<open>0 \<in> counts_maximum_level x1 (Some {#})\<close> for x1 x1s
    by (cases x1s, auto simp: out_learned_def counts_maximum_level_def)

  show ?thesis
    supply [[goals_limit=1]]
    supply [simp] = learned_clss_count_def
    using assms
    unfolding isa_simplify_clause_with_unit_st2_def
      simplify_clause_with_unit_st2_def Let_def[of "(_,_)"] Let_def[of \<open>mset _\<close>]
    apply (refine_rcg isa_simplify_clause_with_unit2_isa_simplify_clause_with_unit[where
      vdom=\<open>set (get_vdom S)\<close> and \<A> = \<open>all_atms_st S'\<close>]
      mop_arena_status[where vdom = \<open>set (get_vdom S)\<close>]
      cons_trail_Propagated_tr2[where \<A> = \<open>all_atms_st S'\<close>]
      mop_isa_length_trail_length_u[of \<open>all_atms_st (S')\<close>, THEN fref_to_Down_Id_keep,
      unfolded length_uint32_nat_def comp_def])
    subgoal by auto
    subgoal by (auto simp: twl_st_heur_def)
    subgoal
      by (auto simp: twl_st_heur_def)
    subgoal
      by (auto simp: twl_st_heur_def)
    subgoal
      using literals_are_in_mm_clauses[of S']
      by auto
    subgoal
      by auto
    subgoal
      by (auto simp: twl_st_heur_def)
    subgoal
      by (auto simp: twl_st_heur_def)
    subgoal for x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h x1i x2i x1j x2j x1k x2k x1l x2l x1m x2m x1n x2n
      x1o x2o x1p x2p x1q x2q x1r x2r x1s x2s x1t x2t x1u x2u x1v x2v x1w x2w x1x x2x x1y x2y x x' x1z x2z x1aa x2aa x1ab
      x2ab x1ac x2ac x1ad x2ad x1ae x2ae
      by (clarsimp simp only: twl_st_heur_def in_pair_collect_simp prod.simps
        get_vdom.simps prod_rel_iff TrueI refl
        cong[of \<open>all_atms_st (x1, x1a, None, x1c, x1d, x1e, x1f, x1g, x1h,
        uminus `# lit_of `# mset (drop x1m (rev x1)), x2i)\<close>
        \<open>all_atms_st (_, _, _, (If _ _ _) _, _)\<close>]
        clss_size_def clss_size_incr_lcountUE_def
        clss_size_decr_lcount_def)
       (auto split: if_splits
        simp: clss_size_lcount_def clss_size_lcountUS_def clss_size_lcountUE_def
        clss_size_lcountU0_def)
   subgoal by simp
   subgoal by (auto simp: twl_st_heur_def)
   subgoal by auto
   subgoal by (auto simp: DECISION_REASON_def)
   subgoal for x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h x1i x2i x1j x2j x1k x2k x1l x2l x1m x2m x1n x2n x1o x2o x1p
     x2p x1q x2q x1r x2r x1s x2s x1t x2t x1u x2u x1v x2v x1w x2w x1x x2x x1y x2y E x x' x1z x2z x1aa x2aa x1ab x2ab x1ac x2ac x1ad
     x2ad x1ae x2ae M Ma
     by (clarsimp simp only: twl_st_heur_def in_pair_collect_simp prod.simps
       get_vdom.simps prod_rel_iff TrueI refl
       cong[of \<open>all_atms_st (x1, x1a, None, x1c, x1d, x1e, x1f, x1g, x1h,
       uminus `# lit_of `# mset (drop x1m (rev x1)), x2i)\<close>
       \<open>all_atms_st (_, _, _, (If _ _ _) _, _)\<close>] isa_vmtf_consD2
       clss_size_def clss_size_incr_lcountUE_def clss_size_incr_lcountUS_def
       clss_size_decr_lcount_def)
       (auto split: if_splits
        simp: clss_size_lcount_def clss_size_lcountUS_def clss_size_lcountUE_def
        clss_size_lcountU0_def)
   subgoal by simp
   subgoal by simp
   subgoal by (auto simp add: twl_st_heur_def)
   subgoal  for x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h x1i x2i x1j x2j x1k x2k x1l x2l x1m x2m x1n x2n x1o x2o x1p
     x2p x1q x2q x1r x2r x1s x2s x1t x2t x1u x2u x1v x2v x1w x2w x1x x2x x1y x2y E x x' x1z x2z x1aa x2aa x1ab x2ab x1ac x2ac x1ad
     x2ad x1ae x2ae
     by (clarsimp simp only: twl_st_heur_def in_pair_collect_simp prod.simps
       get_vdom.simps prod_rel_iff TrueI refl
       cong[of \<open>all_atms_st (x1, x1a, None, x1c, x1d, x1e, x1f, x1g, x1h,
       uminus `# lit_of `# mset (drop x1m (rev x1)), x2i)\<close>
       \<open>all_atms_st (_, _, _, _, _, (If _ _ _) _, _)\<close>] isa_vmtf_consD2
       clss_size_def clss_size_incr_lcountUE_def clss_size_incr_lcountUS_def
       clss_size_incr_lcountU0_def
       clss_size_decr_lcount_def
       option_lookup_clause_rel_cong[of \<open>all_atms_st (x1, x1a, None, x1c, x1d, x1e, x1f, x1g, x1h,
       uminus `# lit_of `# mset (drop x1m (rev x1)), x2i)\<close>
       \<open>all_atms_st (_, _, _, _, _, (If _ _ _) _, _)\<close>, OF sym] outl
       set_conflict_to_false)
     (auto split: if_splits
        simp: clss_size_lcount_def clss_size_lcountUS_def clss_size_lcountUE_def
        clss_size_lcountU0_def)
   subgoal  for x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h x1i x2i x1j x2j x1k x2k x1l x2l x1m x2m x1n x2n x1o x2o x1p
     x2p x1q x2q x1r x2r x1s x2s x1t x2t x1u x2u x1v x2v x1w x2w x1x x2x x1y x2y E x x' x1z x2z x1aa x2aa x1ab x2ab x1ac x2ac x1ad
     x2ad x1ae x2ae
     by (clarsimp simp only: twl_st_heur_def in_pair_collect_simp prod.simps
       get_vdom.simps prod_rel_iff TrueI refl
       cong[of \<open>all_atms_st (x1, x1a, None, x1c, x1d, x1e, x1f, x1g, x1h,
       uminus `# lit_of `# mset (drop x1m (rev x1)), x2i)\<close>
       \<open>all_atms_st (_, _, _, _, _, (If _ _ _) _, _)\<close>] isa_vmtf_consD2
       clss_size_def clss_size_incr_lcountUE_def clss_size_incr_lcountUS_def
       clss_size_incr_lcountU0_def
       clss_size_decr_lcount_def
       option_lookup_clause_rel_cong[of \<open>all_atms_st (x1, x1a, None, x1c, x1d, x1e, x1f, x1g, x1h,
       uminus `# lit_of `# mset (drop x1m (rev x1)), x2i)\<close>
       \<open>all_atms_st (_, _, _, _, _, (If _ _ _) _, _)\<close>, OF sym] outl
       set_conflict_to_false)
       (auto split: if_splits
        simp: clss_size_lcount_def clss_size_lcountUS_def clss_size_lcountUE_def
        clss_size_lcountU0_def)
   done
qed
*)

lemma get_conflict_wl_is_None_heur_get_conflict_wl_is_None_ana:
  \<open>(RETURN o get_conflict_wl_is_None_heur,  RETURN o get_conflict_wl_is_None) \<in>
    twl_st_heur_restart_ana' r (u) \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  unfolding get_conflict_wl_is_None_heur_def get_conflict_wl_is_None_def comp_def
  apply (intro WB_More_Refinement.frefI nres_relI) apply refine_rcg
  by (auto simp: twl_st_heur_restart_ana_def get_conflict_wl_is_None_heur_def get_conflict_wl_is_None_def
      option_lookup_clause_rel_def twl_st_heur_restart_def
     split: option.splits)

lemma isa_simplify_clauses_with_unit_st2_simplify_clauses_with_unit_st2:
  assumes \<open>(S, S') \<in> (twl_st_heur_restart_ana' r u)\<close>
  shows \<open>isa_simplify_clauses_with_unit_st2 S \<le>
    \<Down>(twl_st_heur_restart_ana' r (u)) (simplify_clauses_with_unit_st2 S')\<close>
proof -
  have isa_simplify_clauses_with_unit_st2_def: \<open>isa_simplify_clauses_with_unit_st2 S =
  do {
    xs \<leftarrow> RETURN [];
    T \<leftarrow> do {
    (_, T) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(i, T). i < length xs \<and> get_conflict_wl_is_None_heur T)
      (\<lambda>(i,T). do {
        T \<leftarrow> isa_simplify_clause_with_unit_st2 (xs!i) T;
        ASSERT(i < length xs);
        RETURN (i+1, T)
      })
     (0, S);
    RETURN T
    };
    RETURN T
    }\<close>
    unfolding isa_simplify_clauses_with_unit_st2_def by auto

  have [refine]: \<open>RETURN [] \<le> \<Down> {(xs, a). a = set xs \<and> distinct xs \<and> xs = []} (SPEC (\<lambda>xs. xs \<subseteq> set_mset (dom_m (get_clauses_wl S'))))\<close>
    by (auto simp: RETURN_RES_refine)

    have [refine]: \<open>(xs, xsa) \<in> {(xs, a). a = set xs \<and> distinct xs \<and> xs = []} \<Longrightarrow>
      xsa \<in> {xs. xs \<subseteq> set_mset (dom_m (get_clauses_wl S'))} \<Longrightarrow>
      ([0..<length xs], xsa) \<in> \<langle>{(i, a). xs ! i =a \<and> a \<in> xsa}\<rangle>list_set_rel\<close> for xs xsa
      by (auto simp: list_set_rel_def br_def
        intro!: relcompI[of _ xs])
       (* (auto simp: list_rel_def intro!: list_all2_all_nthI) *)
  show ?thesis
    unfolding isa_simplify_clauses_with_unit_st2_def simplify_clauses_with_unit_st2_def
      nfoldli_upt_by_while[symmetric]  nres_monad3
    apply (refine_vcg 
      LFOci_refine assms)
    subgoal for xs xsa s si
      by (subst get_conflict_wl_is_None_heur_get_conflict_wl_is_None_ana[THEN fref_to_Down_unRET_Id, of _ s])
      (auto simp: assms get_conflict_wl_is_None_def)
    subgoal by auto
    done
qed

lemma isa_simplify_clauses_with_unit_st2_isa_simplify_clauses_with_unit_wl:
  assumes \<open>(S,S') \<in> twl_st_heur_restart_ana' r u\<close>
  shows
    \<open>isa_simplify_clauses_with_unit_st2 S \<le> \<Down> (twl_st_heur_restart_ana' r u) (simplify_clauses_with_unit_st_wl S')\<close>
  apply (rule order_trans)
    defer
  apply (rule ref_two_step')
  apply (rule simplify_clauses_with_unit_st2_simplify_clauses_with_unit_st[unfolded Down_id_eq, of S'])
  subgoal by auto
  subgoal
    apply (rule isa_simplify_clauses_with_unit_st2_simplify_clauses_with_unit_st2[THEN order_trans, of _ S'])
    apply (rule assms)
    subgoal using assms by auto
    done
  done

thm twl_st_heur_restart_def
  twl_st_heur_def
  term twl_st_heur_restart'''
  thm cdcl_twl_full_restart_wl_GC_prog_post_def
lemma cdcl_twl_full_restart_wl_D_inprocess_heur_prog:
  \<open>(cdcl_twl_full_restart_wl_D_inprocess_heur_prog, cdcl_twl_full_restart_inprocess_wl_prog) \<in>
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
    unfolding cdcl_twl_full_restart_wl_D_inprocess_heur_prog_alt_def
      cdcl_twl_full_restart_inprocess_wl_prog_def
    apply (intro frefI nres_relI)
    apply (refine_rcg cdcl_twl_local_restart_wl_spec0
      remove_one_annot_true_clause_imp_wl_D_heur_remove_one_annot_true_clause_imp_wl_D[where r=r, THEN fref_to_Down]
      mark_to_delete_clauses_wl_D_heur_mark_to_delete_clauses_GC_wl_D[where r=r, THEN fref_to_Down]
      isasat_GC_clauses_wl_D[where r=r, THEN fref_to_Down]
      isa_simplify_clauses_with_unit_st2_isa_simplify_clauses_with_unit_wl[where r=r])
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
    subgoal for x y
      unfolding mem_Collect_eq prod.case
      apply (subst cdcl_twl_full_restart_wl_D_GC_prog_post_heur)
      apply assumption
      by auto
    done
qed

definition restart_prog_wl_D_heur
  :: \<open>twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> (twl_st_wl_heur \<times> nat \<times> nat \<times> nat) nres\<close>
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
       (auto simp add: twl_st_heur_def get_learned_clss_wl_def
        clss_size_def clss_size_lcount_def clss_size_lcountUE_def
        clss_size_lcountUS_def)
    subgoal
      by
       (auto simp add: twl_st_heur_def get_learned_clss_wl_def
        clss_size_def clss_size_lcount_def clss_size_lcountUE_def
        clss_size_lcountUS_def)
    subgoal
      by (simp split: if_splits add: twl_st_heur_def RETURN_RES_refine_iff)
        (auto simp add: twl_st_heur_def get_learned_clss_wl_def
          clss_size_def clss_size_lcount_def clss_size_lcountUE_def RETURN_RES_refine_iff
          clss_size_lcountUS_def clss_size_lcountU0_def)
    done

(*heuristic_rel (all_atms cd (cf + cg + ch + ci))
     (incr_restart_phase_end
       (incr_restart_phase*)

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

lemma restart_prog_wl_D_heur_restart_prog_wl_D:
  \<open>(uncurry4 restart_prog_wl_D_heur, uncurry4 restart_prog_wl) \<in>
  twl_st_heur''''u r u \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f bool_rel  \<rightarrow>\<^sub>f
  \<langle>twl_st_heur''''uu r u \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel\<rangle>nres_rel\<close>
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
    subgoal by auto
    subgoal by (auto dest: restart_abs_wl_pre_emptyN0S)
    subgoal by (auto dest: restart_abs_wl_pre_emptyN0S)
    subgoal by auto
    subgoal by (auto simp: restart_flag_rel_def FLAG_GC_restart_def FLAG_restart_def
      FLAG_no_restart_def FLAG_Reduce_restart_def FLAG_Inprocess_restart_def)
    apply (rule twl_st_heur'''_twl_st_heur''''uD)
    subgoal by auto
    subgoal by auto
    subgoal by auto
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
      by (auto dest: restart_abs_wl_pre_emptyN0S)
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      by (auto dest: restart_abs_wl_pre_emptyN0S)
    subgoal
      by auto
    done
  done
 qed

lemma restart_prog_wl_D_heur_restart_prog_wl_D2:
  \<open>(uncurry4 restart_prog_wl_D_heur, uncurry4 restart_prog_wl) \<in>
  twl_st_heur \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f bool_rel \<rightarrow>\<^sub>f \<langle>twl_st_heur \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (rule_tac r2 = \<open>length(get_clauses_wl_heur (fst (fst (fst (fst x)))))\<close> and
       u2 = \<open>learned_clss_count (fst (fst (fst (fst x))))\<close> in
    order_trans[OF restart_prog_wl_D_heur_restart_prog_wl_D[THEN fref_to_Down]])
  apply fast
  apply (auto intro!: conc_fun_R_mono)
  done

end
