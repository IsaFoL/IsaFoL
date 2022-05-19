theory IsaSAT_Stats
  imports IsaSAT_Literals IsaSAT_EMA IsaSAT_Rephase IsaSAT_Reluctant
begin


section \<open>Statistics\<close>
datatype 'a code_hider = Constructor (get_content: 'a)

definition code_hider_rel where code_hider_rel_def_internal:
  \<open>code_hider_rel R = {(a,b). (a, get_content b) \<in> R}\<close>

lemma code_hider_rel_def[refine_rel_defs]:
  "\<langle>R\<rangle>code_hider_rel \<equiv> {(a,b). (a, get_content b) \<in> R}"
  by (simp add: code_hider_rel_def_internal relAPP_def)


text \<open>
We do some statistics on the run.

NB: the statistics are not proven correct (especially they might
overflow), there are just there to look for regressions, do some comparisons (e.g., to conclude that
we are propagating slower than the other solvers), or to test different option combinations.
\<close>

type_synonym stats = \<open>64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times>
  64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> ema\<close>

type_synonym isasat_stats = \<open>stats code_hider\<close>

abbreviation Stats :: \<open>stats \<Rightarrow> isasat_stats\<close> where
  \<open>Stats a \<equiv> Constructor a\<close>

abbreviation get_stats :: \<open>isasat_stats \<Rightarrow> stats\<close> where
  \<open>get_stats a \<equiv> get_content a\<close>

definition incr_propagation_stats :: \<open>stats \<Rightarrow> stats\<close> where
  \<open>incr_propagation_stats = (\<lambda>(propa, confl, dec). (propa + 1, confl, dec))\<close>

definition incr_conflict_stats :: \<open>stats \<Rightarrow> stats\<close> where
  \<open>incr_conflict_stats = (\<lambda>(propa, confl, dec). (propa, confl + 1, dec))\<close>

definition incr_decision_stats :: \<open>stats \<Rightarrow> stats\<close> where
  \<open>incr_decision_stats = (\<lambda>(propa, confl, dec, res). (propa, confl, dec + 1, res))\<close>

definition incr_restart_stats :: \<open>stats \<Rightarrow> stats\<close> where
  \<open>incr_restart_stats = (\<lambda>(propa, confl, dec, res, lres). (propa, confl, dec, res + 1, lres))\<close>

definition incr_lrestart_stats :: \<open>stats \<Rightarrow> stats\<close> where
  \<open>incr_lrestart_stats = (\<lambda>(propa, confl, dec, res, lres, uset). (propa, confl, dec, res, lres + 1, uset))\<close>

definition incr_uset_stats :: \<open>stats \<Rightarrow> stats\<close> where
  \<open>incr_uset_stats = (\<lambda>(propa, confl, dec, res, lres, (uset, gcs)). (propa, confl, dec, res, lres, uset + 1, gcs))\<close>

definition incr_GC_stats :: \<open>stats \<Rightarrow> stats\<close> where
  \<open>incr_GC_stats = (\<lambda>(propa, confl, dec, res, lres, uset, gcs, lbds). (propa, confl, dec, res, lres, uset, gcs + 1, lbds))\<close>

definition stats_conflicts_stats :: \<open>stats \<Rightarrow> 64 word\<close> where
  \<open>stats_conflicts_stats = (\<lambda>(propa, confl, dec). confl)\<close>

definition incr_binary_unit_derived :: \<open>stats \<Rightarrow> stats\<close> where
  \<open>incr_binary_unit_derived = (\<lambda>(propa, confl, dec, res, lres, uset, gcs, units, irred_clss, binary_unit, binary_red_removed, lbds). (propa, confl, dec, res, lres, uset, gcs, units, irred_clss, binary_unit+1, binary_red_removed, lbds))\<close>

definition incr_binary_red_removed :: \<open>stats \<Rightarrow> stats\<close> where
  \<open>incr_binary_red_removed = (\<lambda>(propa, confl, dec, res, lres, uset, gcs, units, irred_clss, binary_unit, binary_red_removed, lbds). (propa, confl, dec, res, lres, uset, gcs, units, irred_clss, binary_unit, binary_red_removed+1, lbds))\<close>

definition add_lbd_stats :: \<open>32 word \<Rightarrow> stats \<Rightarrow> stats\<close> where
  \<open>add_lbd_stats lbd = (\<lambda>(propa, confl, dec, res, lres, uset, gcs, units, irred_clss, binary_unit, binary_red_removed, purelit_removed, purelit_rounds, lbds). (propa, confl, dec, res, lres, uset, gcs, units, irred_clss, binary_unit, binary_red_removed,  purelit_removed, purelit_rounds, ema_update (unat lbd) lbds))\<close>

definition units_since_last_GC_stats :: \<open>stats \<Rightarrow> 64 word\<close> where
  \<open>units_since_last_GC_stats = (\<lambda>(propa, confl, dec, res, lres, uset, gcs, units, lbds). units)\<close>

definition units_since_beginning_stats :: \<open>stats \<Rightarrow> 64 word\<close> where
  \<open>units_since_beginning_stats = (\<lambda>(propa, confl, dec, res, lres, uset, gcs, units, lbds). uset)\<close>

definition incr_units_since_last_GC_stats :: \<open>stats \<Rightarrow> stats\<close> where
  \<open>incr_units_since_last_GC_stats = (\<lambda>(propa, confl, dec, res, lres, uset, gcs, units, lbds). (propa, confl, dec, res, lres, uset, gcs, units + 1, lbds))\<close>


definition incr_purelit_elim_stats :: \<open>stats \<Rightarrow> stats\<close> where
  \<open>incr_purelit_elim_stats = (\<lambda>(propa, confl, dec, res, lres, uset, gcs, units, a, b, c, purelit_elim, purelit_rount, lbds::ema). (propa, confl, dec, res, lres, uset, gcs, units, a, b, c, purelit_elim + 1, purelit_rount, lbds))\<close>

definition incr_purelit_rounds_stats :: \<open>stats \<Rightarrow> stats\<close> where
  \<open>incr_purelit_rounds_stats = (\<lambda>(propa, confl, dec, res, lres, uset, gcs, units, a, b, c, purelit_elim, purelit_rount, lbds). (propa, confl, dec, res, lres, uset, gcs, units, a, b, c, purelit_elim, purelit_rount+1, lbds))\<close>


definition reset_units_since_last_GC_stats :: \<open>stats \<Rightarrow> stats\<close> where
  \<open>reset_units_since_last_GC_stats = (\<lambda>(propa, confl, dec, res, lres, uset, gcs, units, a, b, c, purelit_elim, purelit_round, lbds::ema). (propa, confl, dec, res, lres, uset, gcs, 0, a, b, c, purelit_elim, purelit_round, lbds))\<close>

definition incr_irred_clss_stats :: \<open>stats \<Rightarrow> stats\<close> where
  \<open>incr_irred_clss_stats = (\<lambda>(propa, confl, dec, res, lres, uset, gcs, units, irred_clss, lbds). (propa, confl, dec, res, lres, uset, gcs, units, irred_clss+1, lbds))\<close>

definition decr_irred_clss_stats :: \<open>stats \<Rightarrow> stats\<close> where
  \<open>decr_irred_clss_stats = (\<lambda>(propa, confl, dec, res, lres, uset, gcs, units, irred_clss, lbds). (propa, confl, dec, res, lres, uset, gcs, units, irred_clss-1, lbds))\<close>

definition incr_propagation :: \<open>isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>incr_propagation = Stats o incr_propagation_stats o get_stats\<close>

definition incr_conflict :: \<open>isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>incr_conflict = Stats o incr_conflict_stats o get_stats\<close>

definition incr_decision :: \<open>isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>incr_decision = Stats o incr_decision_stats o get_stats\<close>

definition incr_restart :: \<open>isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>incr_restart = Stats o incr_restart_stats o get_stats\<close>

definition incr_lrestart :: \<open>isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>incr_lrestart = Stats o incr_lrestart_stats o get_stats\<close>

definition incr_uset :: \<open>isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>incr_uset = Stats o incr_uset_stats o get_stats\<close>

definition incr_GC :: \<open>isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>incr_GC = Stats o incr_GC_stats o get_stats\<close>

definition stats_conflicts :: \<open>isasat_stats \<Rightarrow> 64 word\<close> where
  \<open>stats_conflicts = stats_conflicts_stats o get_stats\<close>

definition add_lbd :: \<open>32 word \<Rightarrow> isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>add_lbd lbd = Stats o add_lbd_stats lbd o get_stats\<close>

definition units_since_last_GC :: \<open>isasat_stats \<Rightarrow> 64 word\<close> where
  \<open>units_since_last_GC = units_since_last_GC_stats o get_stats\<close>

definition units_since_beginning :: \<open>isasat_stats \<Rightarrow> 64 word\<close> where
  \<open>units_since_beginning = units_since_beginning_stats o get_stats\<close>

definition incr_units_since_last_GC :: \<open>isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>incr_units_since_last_GC = Stats o incr_units_since_last_GC_stats o get_stats\<close>

definition reset_units_since_last_GC :: \<open>isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>reset_units_since_last_GC = Stats o reset_units_since_last_GC_stats o get_stats\<close>

definition incr_irred_clss :: \<open>isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>incr_irred_clss = Stats o incr_irred_clss_stats o get_stats\<close>

definition decr_irred_clss :: \<open>isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>decr_irred_clss = Stats o decr_irred_clss_stats o get_stats\<close>

definition incr_binary_unit_derived_clss :: \<open>isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>incr_binary_unit_derived_clss = Stats o incr_binary_unit_derived o get_stats\<close>

definition incr_binary_red_removed_clss :: \<open>isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>incr_binary_red_removed_clss = Stats o incr_binary_red_removed o get_stats\<close>

definition incr_purelit_elim :: \<open>isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>incr_purelit_elim = Stats o incr_purelit_elim_stats o get_stats\<close>

definition incr_purelit_rounds :: \<open>isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>incr_purelit_rounds = Stats o incr_purelit_rounds_stats o get_stats\<close>

definition get_conflict_count_stats :: \<open>stats \<Rightarrow> 64 word\<close> where
  \<open>get_conflict_count_stats =  (\<lambda>(propa, confl, dec, res, lres, uset, gcs, units, irred_clss, lbds). confl)\<close>

definition get_conflict_count :: \<open>isasat_stats \<Rightarrow> 64 word\<close> where
  \<open>get_conflict_count =  get_conflict_count_stats o get_stats\<close>

definition get_restart_count_stats :: \<open>stats \<Rightarrow> _\<close> where \<open>get_restart_count_stats = (\<lambda>(props, decs, confl, restarts, _). restarts)\<close>
definition get_restart_count where \<open>get_restart_count = get_restart_count_stats o get_content\<close>
definition get_lrestart_count_stats :: \<open>stats \<Rightarrow> _\<close> where \<open>get_lrestart_count_stats = (\<lambda>(props, decs, confl, restarts, lres, _). lres)\<close>
definition get_lrestart_count where \<open>get_lrestart_count = get_lrestart_count_stats o get_content\<close>


section \<open>Information related to restarts\<close>

definition NORMAL_PHASE :: \<open>64 word\<close> where
  \<open>NORMAL_PHASE = 0\<close>

definition QUIET_PHASE :: \<open>64 word\<close> where
  \<open>QUIET_PHASE = 1\<close>

definition DEFAULT_INIT_PHASE :: \<open>64 word\<close> where
  \<open>DEFAULT_INIT_PHASE = 10000\<close>

type_synonym restart_info = \<open>64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word\<close>

definition incr_conflict_count_since_last_restart :: \<open>restart_info \<Rightarrow> restart_info\<close> where
  \<open>incr_conflict_count_since_last_restart = (\<lambda>(ccount, ema_lvl, restart_phase, end_of_phase, length_phase).
    (ccount + 1, ema_lvl, restart_phase, end_of_phase, length_phase))\<close>

definition restart_info_update_lvl_avg :: \<open>32 word \<Rightarrow> restart_info \<Rightarrow> restart_info\<close> where
  \<open>restart_info_update_lvl_avg = (\<lambda>lvl (ccount, ema_lvl). (ccount, ema_lvl))\<close>

definition restart_info_init :: \<open>restart_info\<close> where
  \<open>restart_info_init = (0, 0, NORMAL_PHASE, DEFAULT_INIT_PHASE, 1000)\<close>

definition restart_info_restart_done :: \<open>restart_info \<Rightarrow> restart_info\<close> where
  \<open>restart_info_restart_done = (\<lambda>(ccount, lvl_avg). (0, lvl_avg))\<close>

type_synonym schedule_info = \<open>64 word\<close>

definition schedule_next_inprocessing_info :: \<open>schedule_info \<Rightarrow> schedule_info\<close> where
  \<open>schedule_next_inprocessing_info = (\<lambda>(inprocess). (inprocess * 3 >> 1))\<close>

definition next_inprocessing_schedule_info :: \<open>schedule_info \<Rightarrow> schedule_info\<close> where
  \<open>next_inprocessing_schedule_info = (\<lambda>(inprocess). inprocess)\<close>


section \<open>Heuristics\<close>

type_synonym restart_heuristics = \<open>ema \<times> ema \<times> restart_info \<times> 64 word \<times> phase_save_heur \<times> reluctant \<times> bool \<times> phase_saver \<times> schedule_info\<close>

type_synonym isasat_restart_heuristics = \<open>restart_heuristics code_hider\<close>


abbreviation Restart_Heuristics :: \<open>restart_heuristics \<Rightarrow> isasat_restart_heuristics\<close> where
  \<open>Restart_Heuristics a \<equiv> Constructor a\<close>

abbreviation get_restart_heuristics :: \<open>isasat_restart_heuristics \<Rightarrow> restart_heuristics\<close> where
  \<open>get_restart_heuristics a \<equiv> get_content a\<close>


fun fast_ema_of_stats :: \<open>restart_heuristics \<Rightarrow> ema\<close> where
  \<open>fast_ema_of_stats (fast_ema, slow_ema, restart_info, wasted, \<phi>) = fast_ema\<close>

fun slow_ema_of_stats :: \<open>restart_heuristics \<Rightarrow> ema\<close> where
  \<open>slow_ema_of_stats (fast_ema, slow_ema, restart_info, wasted, \<phi>) = slow_ema\<close>

fun restart_info_of_stats :: \<open>restart_heuristics \<Rightarrow> restart_info\<close> where
  \<open>restart_info_of_stats (fast_ema, slow_ema, restart_info, wasted, \<phi>) = restart_info\<close>

fun schedule_info_of_stats :: \<open>restart_heuristics \<Rightarrow> schedule_info\<close> where
  \<open>schedule_info_of_stats (fast_ema, slow_ema, restart_info, wasted, \<phi>, _, _, _, schedule) = schedule\<close>

fun current_restart_phase_stats :: \<open>restart_heuristics \<Rightarrow> 64 word\<close> where
  \<open>current_restart_phase_stats (fast_ema, slow_ema, (ccount, ema_lvl, restart_phase, end_of_phase), wasted, \<phi>) =
    restart_phase\<close>

fun incr_restart_phase_stats :: \<open>restart_heuristics \<Rightarrow> restart_heuristics\<close> where
  \<open>incr_restart_phase_stats (fast_ema, slow_ema, (ccount, ema_lvl, restart_phase, end_of_phase), wasted, \<phi>) =
    (fast_ema, slow_ema, (ccount, ema_lvl, restart_phase XOR 1, end_of_phase), wasted, \<phi>)\<close>

fun incr_wasted_stats :: \<open>64 word \<Rightarrow> restart_heuristics \<Rightarrow> restart_heuristics\<close> where
  \<open>incr_wasted_stats waste (fast_ema, slow_ema, res_info, wasted, \<phi>) =
    (fast_ema, slow_ema, res_info, wasted + waste, \<phi>)\<close>

fun set_zero_wasted_stats :: \<open>restart_heuristics \<Rightarrow> restart_heuristics\<close> where
  \<open>set_zero_wasted_stats (fast_ema, slow_ema, res_info, wasted, \<phi>) =
    (fast_ema, slow_ema, res_info, 0, \<phi>)\<close>

fun wasted_of_stats :: \<open>restart_heuristics \<Rightarrow> 64 word\<close> where
  \<open>wasted_of_stats (fast_ema, slow_ema, res_info, wasted, \<phi>) = wasted\<close>

fun get_conflict_count_since_last_restart_stats :: \<open>restart_heuristics \<Rightarrow> 64 word\<close> where
  \<open>get_conflict_count_since_last_restart_stats (fast_ema, slow_ema, (ccount, ema_lvl, restart_phase, end_of_phase), wasted, \<phi>) =
    ccount\<close>

definition get_conflict_count_since_last_restart :: \<open>isasat_restart_heuristics \<Rightarrow> 64 word\<close> where
  \<open>get_conflict_count_since_last_restart = get_conflict_count_since_last_restart_stats o get_content\<close>

definition heuristic_rel_stats :: \<open>nat multiset \<Rightarrow> restart_heuristics \<Rightarrow> bool\<close> where
  \<open>heuristic_rel_stats \<A> = (\<lambda>(fast_ema, slow_ema, res_info, wasted, \<phi>, _, _, lit_st, schedule). phase_save_heur_rel \<A> \<phi> \<and> phase_saving \<A> lit_st)\<close>

definition save_phase_heur_stats :: \<open>nat \<Rightarrow> bool \<Rightarrow> restart_heuristics \<Rightarrow> restart_heuristics\<close> where
\<open>save_phase_heur_stats L b = (\<lambda>(fast_ema, slow_ema, res_info, wasted, (\<phi>, target, best), reluctant).
    (fast_ema, slow_ema, res_info, wasted, (\<phi>[L := b], target, best), reluctant))\<close>

definition save_phase_heur_pre_stats :: \<open>nat \<Rightarrow> bool \<Rightarrow> restart_heuristics \<Rightarrow> bool\<close> where
\<open>save_phase_heur_pre_stats L b = (\<lambda>(fast_ema, slow_ema, res_info, wasted, (\<phi>, _), _). L < length \<phi>)\<close>

definition mop_save_phase_heur_stats :: \<open>nat \<Rightarrow> bool \<Rightarrow> restart_heuristics \<Rightarrow> restart_heuristics nres\<close> where
\<open>mop_save_phase_heur_stats L b heur = do {
   ASSERT(save_phase_heur_pre_stats L b heur);
   RETURN (save_phase_heur_stats L b heur)
}\<close>

definition mark_added_heur_stats :: \<open>nat \<Rightarrow> bool \<Rightarrow> restart_heuristics \<Rightarrow> restart_heuristics\<close> where
\<open>mark_added_heur_stats L b = (\<lambda>(fast_ema, slow_ema, res_info, wasted, \<phi>, reluctant, fully_proped, lits_st, schedule).
    (fast_ema, slow_ema, res_info, wasted, \<phi>, reluctant, fully_proped, lits_st[L := True], schedule))\<close>

definition mark_added_heur_pre_stats :: \<open>nat \<Rightarrow> bool \<Rightarrow> restart_heuristics \<Rightarrow> bool\<close> where
\<open>mark_added_heur_pre_stats L b = (\<lambda>(fast_ema, slow_ema, res_info, wasted, \<phi>, _,  fully_proped, lits_st, schedule). L < length lits_st)\<close>

definition mop_mark_added_heur_stats :: \<open>nat \<Rightarrow> bool \<Rightarrow> restart_heuristics \<Rightarrow> restart_heuristics nres\<close> where
\<open>mop_mark_added_heur_stats L b heur = do {
   ASSERT(mark_added_heur_pre_stats L b heur);
   RETURN (mark_added_heur_stats L b heur)
}\<close>

definition reset_added_heur_stats :: \<open>restart_heuristics \<Rightarrow> restart_heuristics\<close> where
\<open>reset_added_heur_stats = (\<lambda>(fast_ema, slow_ema, res_info, wasted, \<phi>, reluctant, fully_proped, lits_st, schedule).
    (fast_ema, slow_ema, res_info, wasted, \<phi>, reluctant, fully_proped, replicate (length lits_st) False, schedule))\<close>


definition reset_added_heur_stats2 :: \<open>restart_heuristics \<Rightarrow> restart_heuristics nres\<close> where
  \<open>reset_added_heur_stats2 = (\<lambda>(fast_ema, slow_ema, res_info, wasted, \<phi>, reluctant, fully_proped, lits_st\<^sub>0, schedule).
  do {
  (_, lits_st) \<leftarrow> WHILE\<^sub>T\<^bsup> \<lambda>(i, lits_st). (\<forall>k < i. \<not>lits_st ! k) \<and> i \<le> length lits_st \<and> length lits_st = length lits_st\<^sub>0\<^esup> (\<lambda>(i, lits_st). i < length lits_st)
    (\<lambda>(i, lits_st). do {ASSERT (i < length lits_st); RETURN (i+1, lits_st[i := False])})
    (0, lits_st\<^sub>0);
  RETURN  (fast_ema, slow_ema, res_info, wasted, \<phi>, reluctant, fully_proped, lits_st, schedule)
  })\<close>

lemma reset_added_heur_stats2_reset_added_heur_stats:
  \<open>reset_added_heur_stats2 heur \<le>\<Down>Id (RETURN (reset_added_heur_stats heur))\<close>
proof -
  obtain fast_ema slow_ema res_info wasted \<phi> reluctant fully_proped lits_st\<^sub>0 schedule where
    heur: \<open>heur = (fast_ema, slow_ema, res_info, wasted, \<phi>, reluctant, fully_proped, lits_st\<^sub>0, schedule)\<close>
    by (cases heur)
  have [refine0]: \<open>wf (measure (\<lambda>(i, lits_st). length lits_st\<^sub>0 - i))\<close>
    by auto
  show ?thesis
    unfolding reset_added_heur_stats2_def reset_added_heur_stats_def heur
       prod.simps
    apply (refine_vcg)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto split: if_splits)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (simp add: list_eq_iff_nth_eq)
    done
qed

definition is_marked_added_heur_stats :: \<open>restart_heuristics \<Rightarrow> nat \<Rightarrow> bool\<close> where
\<open>is_marked_added_heur_stats = (\<lambda>(fast_ema, slow_ema, res_info, wasted, \<phi>, reluctant, fully_proped, lits_st, schedule) L.
     lits_st ! L)\<close>

definition is_marked_added_heur_pre_stats :: \<open>restart_heuristics \<Rightarrow>nat \<Rightarrow> bool\<close> where
\<open>is_marked_added_heur_pre_stats = (\<lambda>(fast_ema, slow_ema, res_info, wasted, \<phi>, _,  fully_proped, lits_st, schedule) L. L < length lits_st)\<close>

definition mop_is_marked_added_heur_stats :: \<open>restart_heuristics \<Rightarrow> nat \<Rightarrow> bool nres\<close> where
\<open>mop_is_marked_added_heur_stats L heur = do {
   ASSERT(is_marked_added_heur_pre_stats L heur);
   RETURN (is_marked_added_heur_stats L heur)
}\<close>

definition get_saved_phase_heur_pre_stats :: \<open>nat \<Rightarrow> restart_heuristics \<Rightarrow> bool\<close> where
\<open>get_saved_phase_heur_pre_stats L = (\<lambda>(fast_ema, slow_ema, res_info, wasted, (\<phi>, _), _). L < length \<phi>)\<close>

definition get_saved_phase_heur_stats :: \<open>nat \<Rightarrow> restart_heuristics \<Rightarrow> bool\<close> where
\<open>get_saved_phase_heur_stats L = (\<lambda>(fast_ema, slow_ema, res_info, wasted, (\<phi>, _), _). \<phi>!L)\<close>

definition current_rephasing_phase_stats :: \<open>restart_heuristics \<Rightarrow> 64 word\<close> where
\<open>current_rephasing_phase_stats = (\<lambda>(fast_ema, slow_ema, res_info, wasted, \<phi>, _). phase_current_rephasing_phase \<phi>)\<close>

definition mop_get_saved_phase_heur_stats :: \<open>nat \<Rightarrow> restart_heuristics \<Rightarrow> bool nres\<close> where
\<open>mop_get_saved_phase_heur_stats L heur = do {
   ASSERT(get_saved_phase_heur_pre_stats L heur);
   RETURN (get_saved_phase_heur_stats L heur)
}\<close>

definition heuristic_reluctant_tick_stats :: \<open>restart_heuristics \<Rightarrow> restart_heuristics\<close> where
  \<open>heuristic_reluctant_tick_stats = (\<lambda>(fast_ema, slow_ema, res_info, wasted, \<phi>, reluctant, fullyproped).
     (fast_ema, slow_ema, res_info, wasted, \<phi>, reluctant_tick reluctant, fullyproped))\<close>

definition heuristic_reluctant_enable_stats :: \<open>restart_heuristics \<Rightarrow> restart_heuristics\<close> where
  \<open>heuristic_reluctant_enable_stats = (\<lambda>(fast_ema, slow_ema, res_info, wasted, \<phi>, reluctant, fullyproped).
     (fast_ema, slow_ema, res_info, wasted, \<phi>, reluctant_init, fullyproped))\<close>

definition heuristic_reluctant_disable_stats :: \<open>restart_heuristics \<Rightarrow> restart_heuristics\<close> where
  \<open>heuristic_reluctant_disable_stats = (\<lambda>(fast_ema, slow_ema, res_info, wasted, \<phi>, reluctant, fullyproped).
     (fast_ema, slow_ema, res_info, wasted, \<phi>, reluctant_disable reluctant, fullyproped))\<close>

definition heuristic_reluctant_triggered_stats :: \<open>restart_heuristics \<Rightarrow> restart_heuristics \<times> bool\<close> where
  \<open>heuristic_reluctant_triggered_stats = (\<lambda>(fast_ema, slow_ema, res_info, wasted, \<phi>, reluctant, fullyproped).
    let (reluctant, b) = reluctant_triggered reluctant in
     ((fast_ema, slow_ema, res_info, wasted, \<phi>, reluctant, fullyproped), b))\<close>

definition heuristic_reluctant_triggered2_stats :: \<open>restart_heuristics \<Rightarrow> bool\<close> where
  \<open>heuristic_reluctant_triggered2_stats = (\<lambda>(fast_ema, slow_ema, res_info, wasted, \<phi>, reluctant, fullyproped).
    reluctant_triggered2 reluctant)\<close>

definition heuristic_reluctant_untrigger_stats :: \<open>restart_heuristics \<Rightarrow> restart_heuristics\<close> where
  \<open>heuristic_reluctant_untrigger_stats = (\<lambda>(fast_ema, slow_ema, res_info, wasted, \<phi>, reluctant, fullyproped).
    (fast_ema, slow_ema, res_info, wasted, \<phi>, reluctant_untrigger reluctant, fullyproped))\<close>

definition end_of_rephasing_phase_heur_stats :: \<open>restart_heuristics \<Rightarrow> 64 word\<close> where
  \<open>end_of_rephasing_phase_heur_stats =
    (\<lambda>(fast_ema, slow_ema, res_info, wasted, phasing, reluctant). end_of_rephasing_phase phasing)\<close>

definition is_fully_propagated_heur_stats :: \<open>restart_heuristics \<Rightarrow> bool\<close> where
  \<open>is_fully_propagated_heur_stats =
    (\<lambda>(fast_ema, slow_ema, res_info, wasted, phasing, reluctant, fullyproped, _). fullyproped)\<close>

definition set_fully_propagated_heur_stats :: \<open>restart_heuristics \<Rightarrow> restart_heuristics\<close> where
  \<open>set_fully_propagated_heur_stats =
    (\<lambda>(fast_ema, slow_ema, res_info, wasted, phasing, reluctant, fullyproped, lit_st). (fast_ema, slow_ema, res_info, wasted, phasing, reluctant, True, lit_st))\<close>

definition unset_fully_propagated_heur_stats :: \<open>restart_heuristics \<Rightarrow> restart_heuristics\<close> where
  \<open>unset_fully_propagated_heur_stats =
    (\<lambda>(fast_ema, slow_ema, res_info, wasted, phasing, reluctant, fullyproped, lit_st). (fast_ema, slow_ema, res_info, wasted, phasing, reluctant, False, lit_st))\<close>

definition restart_info_restart_done_heur_stats :: \<open>restart_heuristics \<Rightarrow> restart_heuristics\<close> where
  \<open>restart_info_restart_done_heur_stats = (\<lambda>(fast_ema, slow_ema, res_info, wasted, phasing, reluctant, fullyproped, lit_st). (fast_ema, slow_ema, restart_info_restart_done res_info, wasted, phasing, reluctant, False, lit_st))\<close>

lemma heuristic_rel_statsI[intro!]:
  \<open>heuristic_rel_stats \<A> heur \<Longrightarrow> heuristic_rel_stats \<A> (incr_wasted_stats wast heur)\<close>
  \<open>heuristic_rel_stats \<A> heur \<Longrightarrow> heuristic_rel_stats \<A> (set_zero_wasted_stats heur)\<close>
  \<open>heuristic_rel_stats \<A> heur \<Longrightarrow> heuristic_rel_stats \<A> (incr_restart_phase_stats heur)\<close>
  \<open>heuristic_rel_stats \<A> heur \<Longrightarrow> heuristic_rel_stats \<A> (save_phase_heur_stats L b heur)\<close>
  \<open>heuristic_rel_stats \<A> heur \<Longrightarrow> heuristic_rel_stats \<A> (mark_added_heur_stats L b heur)\<close>
  \<open>heuristic_rel_stats \<A> heur \<Longrightarrow> heuristic_rel_stats \<A> (heuristic_reluctant_tick_stats heur)\<close>
  \<open>heuristic_rel_stats \<A> heur \<Longrightarrow> heuristic_rel_stats \<A> (heuristic_reluctant_enable_stats heur)\<close>
  \<open>heuristic_rel_stats \<A> heur \<Longrightarrow> heuristic_rel_stats \<A> (heuristic_reluctant_untrigger_stats heur)\<close>
  \<open>heuristic_rel_stats \<A> heur \<Longrightarrow> heuristic_rel_stats \<A> (set_fully_propagated_heur_stats heur)\<close>
  \<open>heuristic_rel_stats \<A> heur \<Longrightarrow> heuristic_rel_stats \<A> (unset_fully_propagated_heur_stats heur)\<close>
  by (clarsimp_all simp: heuristic_rel_stats_def save_phase_heur_stats_def phase_save_heur_rel_def phase_saving_def
    heuristic_reluctant_tick_stats_def heuristic_reluctant_enable_stats_def heuristic_reluctant_untrigger_stats_def
    set_fully_propagated_heur_stats_def unset_fully_propagated_heur_stats_def mark_added_heur_stats_def)

lemma heuristic_rel_stats_heuristic_reluctant_triggered_statsD:
  \<open>heuristic_rel_stats \<A> heur \<Longrightarrow>
     heuristic_rel_stats \<A> (fst (heuristic_reluctant_triggered_stats heur))\<close>
  by (clarsimp simp: heuristic_reluctant_triggered_stats_def heuristic_rel_stats_def  phase_save_heur_rel_def
    phase_saving_def reluctant_triggered_def)

lemma save_phase_heur_pre_statsI:
  \<open>heuristic_rel_stats \<A> heur \<Longrightarrow> a \<in># \<A> \<Longrightarrow> save_phase_heur_pre_stats a b heur\<close>
  by (auto simp: heuristic_rel_stats_def phase_saving_def save_phase_heur_pre_stats_def
     phase_save_heur_rel_def atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n)

definition fast_ema_of :: \<open>isasat_restart_heuristics \<Rightarrow> ema\<close> where
  \<open>fast_ema_of = fast_ema_of_stats o get_restart_heuristics\<close>

definition slow_ema_of :: \<open>isasat_restart_heuristics \<Rightarrow> ema\<close> where
  \<open>slow_ema_of = slow_ema_of_stats o get_restart_heuristics\<close>

definition restart_info_of :: \<open>isasat_restart_heuristics \<Rightarrow> restart_info\<close> where
  \<open>restart_info_of = restart_info_of_stats o get_restart_heuristics\<close>

definition current_restart_phase :: \<open>isasat_restart_heuristics \<Rightarrow> 64 word\<close> where
  \<open>current_restart_phase = current_restart_phase_stats o get_restart_heuristics\<close>

definition incr_restart_phase :: \<open>isasat_restart_heuristics \<Rightarrow> isasat_restart_heuristics\<close> where
  \<open>incr_restart_phase = Restart_Heuristics o incr_restart_phase_stats o get_restart_heuristics\<close>

definition incr_wasted :: \<open>64 word \<Rightarrow> isasat_restart_heuristics \<Rightarrow> isasat_restart_heuristics\<close> where
  \<open>incr_wasted waste = Restart_Heuristics o incr_wasted_stats waste o get_restart_heuristics\<close>

definition set_zero_wasted :: \<open>isasat_restart_heuristics \<Rightarrow> isasat_restart_heuristics\<close> where
  \<open>set_zero_wasted =  Restart_Heuristics o set_zero_wasted_stats o get_restart_heuristics\<close>

definition wasted_of :: \<open>isasat_restart_heuristics \<Rightarrow> 64 word\<close> where
  \<open>wasted_of = wasted_of_stats o get_restart_heuristics\<close>

definition heuristic_rel :: \<open>nat multiset \<Rightarrow> isasat_restart_heuristics \<Rightarrow> bool\<close> where
  \<open>heuristic_rel \<A> = heuristic_rel_stats \<A> o get_restart_heuristics\<close>

definition save_phase_heur :: \<open>nat \<Rightarrow> bool \<Rightarrow> isasat_restart_heuristics \<Rightarrow> isasat_restart_heuristics\<close> where
\<open>save_phase_heur L b = Restart_Heuristics o save_phase_heur_stats L b o get_restart_heuristics\<close>

definition save_phase_heur_pre :: \<open>nat \<Rightarrow> bool \<Rightarrow> isasat_restart_heuristics \<Rightarrow> bool\<close> where
  \<open>save_phase_heur_pre L b = save_phase_heur_pre_stats L b o get_restart_heuristics\<close>

definition mop_save_phase_heur :: \<open>nat \<Rightarrow> bool \<Rightarrow> isasat_restart_heuristics \<Rightarrow> isasat_restart_heuristics nres\<close> where
\<open>mop_save_phase_heur L b heur = do {
   ASSERT(save_phase_heur_pre L b heur);
   RETURN (save_phase_heur L b heur)
}\<close>

definition mark_added_heur :: \<open>nat \<Rightarrow> bool \<Rightarrow> isasat_restart_heuristics \<Rightarrow> isasat_restart_heuristics\<close> where
\<open>mark_added_heur L b = Restart_Heuristics o mark_added_heur_stats L b o get_restart_heuristics\<close>

definition mark_added_heur_pre :: \<open>nat \<Rightarrow> bool \<Rightarrow> isasat_restart_heuristics \<Rightarrow> bool\<close> where
\<open>mark_added_heur_pre L b = mark_added_heur_pre_stats L b o get_restart_heuristics\<close>

definition mop_mark_added_heur :: \<open>nat \<Rightarrow> bool \<Rightarrow> isasat_restart_heuristics \<Rightarrow> isasat_restart_heuristics nres\<close> where
\<open>mop_mark_added_heur L b heur = do {
   ASSERT(mark_added_heur_pre L b heur);
   RETURN (mark_added_heur L b heur)
}\<close>

definition reset_added_heur :: \<open>isasat_restart_heuristics \<Rightarrow> isasat_restart_heuristics\<close> where
\<open>reset_added_heur = Restart_Heuristics o reset_added_heur_stats o get_restart_heuristics\<close>

definition mop_reset_added_heur :: \<open>isasat_restart_heuristics \<Rightarrow> isasat_restart_heuristics nres\<close> where
\<open>mop_reset_added_heur heur = do {
   RETURN (reset_added_heur heur)
}\<close>

definition is_marked_added_heur :: \<open>isasat_restart_heuristics \<Rightarrow> nat \<Rightarrow> bool\<close> where
\<open>is_marked_added_heur = is_marked_added_heur_stats o get_restart_heuristics\<close>

definition is_marked_added_heur_pre :: \<open>isasat_restart_heuristics \<Rightarrow>  nat \<Rightarrow> bool\<close> where
\<open>is_marked_added_heur_pre = is_marked_added_heur_pre_stats o get_restart_heuristics\<close>

definition mop_is_marked_added_heur :: \<open>isasat_restart_heuristics \<Rightarrow> nat \<Rightarrow> bool nres\<close> where
\<open>mop_is_marked_added_heur L heur = do {
   ASSERT(is_marked_added_heur_pre L heur);
   RETURN (is_marked_added_heur L heur)
}\<close>

definition get_saved_phase_heur_pre :: \<open>nat \<Rightarrow> isasat_restart_heuristics \<Rightarrow> bool\<close> where
\<open>get_saved_phase_heur_pre L = get_saved_phase_heur_pre_stats L o get_restart_heuristics\<close>

definition get_saved_phase_heur :: \<open>nat \<Rightarrow> isasat_restart_heuristics \<Rightarrow> bool\<close> where
\<open>get_saved_phase_heur L = get_saved_phase_heur_stats L o get_restart_heuristics\<close>

definition current_rephasing_phase :: \<open>isasat_restart_heuristics \<Rightarrow> 64 word\<close> where
\<open>current_rephasing_phase = current_rephasing_phase_stats o get_restart_heuristics\<close>

definition mop_get_saved_phase_heur :: \<open>nat \<Rightarrow> isasat_restart_heuristics \<Rightarrow> bool nres\<close> where
\<open>mop_get_saved_phase_heur L heur = do {
   ASSERT(get_saved_phase_heur_pre L heur);
   RETURN (get_saved_phase_heur L heur)
}\<close>

definition heuristic_reluctant_tick :: \<open>isasat_restart_heuristics \<Rightarrow> isasat_restart_heuristics\<close> where
  \<open>heuristic_reluctant_tick = Restart_Heuristics o heuristic_reluctant_tick_stats o get_restart_heuristics\<close>

definition heuristic_reluctant_enable :: \<open>isasat_restart_heuristics \<Rightarrow> isasat_restart_heuristics\<close> where
  \<open>heuristic_reluctant_enable = Restart_Heuristics o heuristic_reluctant_enable_stats o get_restart_heuristics\<close>

definition heuristic_reluctant_disable :: \<open>isasat_restart_heuristics \<Rightarrow> isasat_restart_heuristics\<close> where
  \<open>heuristic_reluctant_disable = Restart_Heuristics o heuristic_reluctant_disable_stats o get_restart_heuristics\<close>

definition heuristic_reluctant_triggered :: \<open>isasat_restart_heuristics \<Rightarrow> isasat_restart_heuristics \<times> bool\<close> where
  \<open>heuristic_reluctant_triggered = apfst Restart_Heuristics o heuristic_reluctant_triggered_stats o get_restart_heuristics\<close>

definition heuristic_reluctant_triggered2 :: \<open>isasat_restart_heuristics \<Rightarrow> bool\<close> where
  \<open>heuristic_reluctant_triggered2 = heuristic_reluctant_triggered2_stats o get_restart_heuristics\<close>

definition heuristic_reluctant_untrigger :: \<open>isasat_restart_heuristics \<Rightarrow> isasat_restart_heuristics\<close> where
  \<open>heuristic_reluctant_untrigger = Restart_Heuristics o heuristic_reluctant_untrigger_stats o get_restart_heuristics\<close>

definition end_of_rephasing_phase_heur :: \<open>isasat_restart_heuristics \<Rightarrow> 64 word\<close> where
  \<open>end_of_rephasing_phase_heur = end_of_rephasing_phase_heur_stats o get_restart_heuristics\<close>

definition is_fully_propagated_heur :: \<open>isasat_restart_heuristics \<Rightarrow> bool\<close> where
  \<open>is_fully_propagated_heur = is_fully_propagated_heur_stats o get_restart_heuristics\<close>

definition set_fully_propagated_heur :: \<open>isasat_restart_heuristics \<Rightarrow> isasat_restart_heuristics\<close> where
  \<open>set_fully_propagated_heur = Restart_Heuristics o set_fully_propagated_heur_stats o get_restart_heuristics\<close>

definition unset_fully_propagated_heur :: \<open>isasat_restart_heuristics \<Rightarrow> isasat_restart_heuristics\<close> where
  \<open>unset_fully_propagated_heur =
  Restart_Heuristics o unset_fully_propagated_heur_stats o get_restart_heuristics\<close>

definition restart_info_restart_done_heur :: \<open>isasat_restart_heuristics \<Rightarrow> isasat_restart_heuristics\<close> where
  \<open>restart_info_restart_done_heur =
  Restart_Heuristics o restart_info_restart_done_heur_stats o get_restart_heuristics\<close>

definition schedule_info_of :: \<open>isasat_restart_heuristics \<Rightarrow> schedule_info\<close> where
  \<open>schedule_info_of = schedule_info_of_stats o get_restart_heuristics\<close>

definition schedule_next_inprocessing_stats :: \<open>restart_heuristics \<Rightarrow> restart_heuristics\<close> where
  \<open>schedule_next_inprocessing_stats = (\<lambda>(fast_ema, slow_ema, res_info, wasted, phasing, reluctant, fullyproped, lit_st, schedule). (fast_ema, slow_ema, restart_info_restart_done res_info, wasted, phasing, reluctant, fullyproped, lit_st, schedule_next_inprocessing_info schedule))\<close>

definition schedule_next_inprocessing :: \<open>isasat_restart_heuristics \<Rightarrow> isasat_restart_heuristics\<close> where
  \<open>schedule_next_inprocessing = Restart_Heuristics o schedule_next_inprocessing_stats o get_restart_heuristics\<close>

definition next_inprocessing_schedule_info_stats :: \<open>restart_heuristics \<Rightarrow> 64 word\<close> where
  \<open>next_inprocessing_schedule_info_stats = next_inprocessing_schedule_info o schedule_info_of_stats\<close>

definition next_inprocessing_schedule :: \<open>isasat_restart_heuristics \<Rightarrow> 64 word\<close> where
  \<open>next_inprocessing_schedule = next_inprocessing_schedule_info_stats o get_restart_heuristics\<close>

lemma heuristic_relI[intro!]:
  \<open>heuristic_rel \<A> heur \<Longrightarrow> heuristic_rel \<A> (incr_wasted wast heur)\<close>
  \<open>heuristic_rel \<A> heur \<Longrightarrow> heuristic_rel \<A> (set_zero_wasted heur)\<close>
  \<open>heuristic_rel \<A> heur \<Longrightarrow> heuristic_rel \<A> (incr_restart_phase heur)\<close>
  \<open>heuristic_rel \<A> heur \<Longrightarrow> heuristic_rel \<A> (save_phase_heur L b heur)\<close>
  \<open>heuristic_rel \<A> heur \<Longrightarrow> heuristic_rel \<A> (heuristic_reluctant_tick heur)\<close>
  \<open>heuristic_rel \<A> heur \<Longrightarrow> heuristic_rel \<A> (heuristic_reluctant_enable heur)\<close>
  \<open>heuristic_rel \<A> heur \<Longrightarrow> heuristic_rel \<A> (heuristic_reluctant_untrigger heur)\<close>
  \<open>heuristic_rel \<A> heur \<Longrightarrow> heuristic_rel \<A> (set_fully_propagated_heur heur)\<close>
  \<open>heuristic_rel \<A> heur \<Longrightarrow> heuristic_rel \<A> (unset_fully_propagated_heur heur)\<close>
  \<open>heuristic_rel \<A> heur \<Longrightarrow> heuristic_rel \<A> (mark_added_heur L b heur)\<close>
  by (auto simp: heuristic_rel_def save_phase_heur_def phase_save_heur_rel_def phase_saving_def
    heuristic_reluctant_tick_def heuristic_reluctant_enable_def heuristic_reluctant_untrigger_def
    set_fully_propagated_heur_def unset_fully_propagated_heur_def set_zero_wasted_def incr_wasted_def
    incr_restart_phase_def mark_added_heur_def)

lemma heuristic_rel_heuristic_reluctant_triggeredD:
  \<open>heuristic_rel \<A> heur \<Longrightarrow>
     heuristic_rel \<A> (fst (heuristic_reluctant_triggered heur))\<close>
  by (clarsimp simp: heuristic_reluctant_triggered_def heuristic_rel_def  phase_save_heur_rel_def
    phase_saving_def reluctant_triggered_def heuristic_rel_stats_heuristic_reluctant_triggered_statsD)

lemma save_phase_heur_preI:
  \<open>heuristic_rel \<A> heur \<Longrightarrow> a \<in># \<A> \<Longrightarrow> save_phase_heur_pre a b heur\<close>
  by (auto simp: heuristic_rel_def phase_saving_def save_phase_heur_pre_def save_phase_heur_pre_statsI
     phase_save_heur_rel_def atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n)

text \<open>Using \<^term>\<open>a + 1\<close> ensures that we do not get stuck with 0.\<close>
fun incr_restart_phase_end_stats :: \<open>restart_heuristics \<Rightarrow> restart_heuristics\<close> where
  \<open>incr_restart_phase_end_stats (fast_ema, slow_ema, (ccount, ema_lvl, restart_phase, end_of_phase, length_phase), wasted) =
  (fast_ema, slow_ema, (ccount, ema_lvl, restart_phase, end_of_phase + length_phase, (length_phase * 3) >> 1), wasted)\<close>

definition incr_restart_phase_end :: \<open>isasat_restart_heuristics \<Rightarrow> isasat_restart_heuristics\<close> where
  \<open>incr_restart_phase_end = Restart_Heuristics o incr_restart_phase_end_stats o get_content\<close>

lemma heuristic_rel_incr_restartI[intro!]:
  \<open>heuristic_rel \<A> heur \<Longrightarrow> heuristic_rel \<A> (incr_restart_phase_end heur)\<close>
  by (auto simp: heuristic_rel_def heuristic_rel_stats_def incr_restart_phase_end_def)

lemma [intro!]:
  \<open>heuristic_rel \<A> heur \<Longrightarrow> heuristic_rel \<A> (heuristic_reluctant_disable heur)\<close>
  \<open>heuristic_rel \<A> heur \<Longrightarrow> heuristic_rel \<A> (schedule_next_inprocessing heur)\<close>
  by (auto simp: heuristic_rel_def heuristic_reluctant_disable_def heuristic_rel_stats_def heuristic_reluctant_disable_stats_def
     next_inprocessing_schedule_def schedule_next_inprocessing_def schedule_next_inprocessing_stats_def)

lemma [simp]:
  \<open>heuristic_rel \<A> heur \<Longrightarrow> heuristic_rel \<A> (restart_info_restart_done_heur heur)\<close>
  by (auto simp: heuristic_rel_def heuristic_rel_stats_def restart_info_restart_done_heur_def
    restart_info_restart_done_heur_stats_def)


subsection \<open>Number of clauses\<close>

type_synonym clss_size = \<open>nat \<times> nat \<times> nat \<times> nat \<times> nat\<close>

definition clss_size
  :: \<open>'v clauses_l \<Rightarrow> 'v clauses \<Rightarrow> 'v clauses \<Rightarrow> 'v clauses \<Rightarrow> 'v clauses \<Rightarrow>'v clauses \<Rightarrow> 'v clauses \<Rightarrow>
     'v clauses \<Rightarrow> 'v clauses \<Rightarrow> clss_size\<close>
where
  \<open>clss_size N NE UE NEk UEk NS US N0 U0 =
     (size (learned_clss_lf N), size UE, size UEk, size US, size U0)\<close>

definition clss_size_lcount :: \<open>clss_size \<Rightarrow> nat\<close> where
  \<open>clss_size_lcount = (\<lambda>(lcount, lcountUE, lcountUEk, lcountUS). lcount)\<close>

definition clss_size_lcountUE :: \<open>clss_size \<Rightarrow> nat\<close> where
  \<open>clss_size_lcountUE = (\<lambda>(lcount, lcountUE, lcountUEk, lcountUS). lcountUE)\<close>

definition clss_size_lcountUEk :: \<open>clss_size \<Rightarrow> nat\<close> where
  \<open>clss_size_lcountUEk = (\<lambda>(lcount, lcountUE, lcountUEk, lcountUS). lcountUEk)\<close>

definition clss_size_lcountUS :: \<open>clss_size \<Rightarrow> nat\<close> where
  \<open>clss_size_lcountUS = (\<lambda>(lcount, lcountUE, lcountUEk, lcountUS, _). lcountUS)\<close>

definition clss_size_lcountU0 :: \<open>clss_size \<Rightarrow> nat\<close> where
  \<open>clss_size_lcountU0 = (\<lambda>(lcount, lcountUE, lcountUEk, lcountUS, lcountU0). lcountU0)\<close>

definition clss_size_incr_lcount :: \<open>clss_size \<Rightarrow> clss_size\<close> where
  \<open>clss_size_incr_lcount =
     (\<lambda>(lcount, lcountUE, lcountUEk, lcountUS). (lcount + 1, lcountUE, lcountUEk, lcountUS))\<close>

definition clss_size_decr_lcount :: \<open>clss_size \<Rightarrow> clss_size\<close> where
  \<open>clss_size_decr_lcount =
     (\<lambda>(lcount, lcountUE, lcountUEk, lcountUS). (lcount - 1, lcountUE, lcountUEk, lcountUS))\<close>

definition clss_size_incr_lcountUE :: \<open>clss_size \<Rightarrow> clss_size\<close> where
  \<open>clss_size_incr_lcountUE =
     (\<lambda>(lcount, lcountUE, lcountUEk, lcountUS). (lcount, lcountUE + 1, lcountUEk, lcountUS))\<close>

definition clss_size_incr_lcountUEk :: \<open>clss_size \<Rightarrow> clss_size\<close> where
  \<open>clss_size_incr_lcountUEk =
     (\<lambda>(lcount, lcountUE, lcountUEk, lcountUS). (lcount, lcountUE, lcountUEk + 1, lcountUS))\<close>

definition clss_size_incr_lcountUS :: \<open>clss_size \<Rightarrow> clss_size\<close> where
  \<open>clss_size_incr_lcountUS =
     (\<lambda>(lcount, lcountUE, lcountUEk, lcountUS, lcountU0). (lcount, lcountUE, lcountUEk, lcountUS + 1, lcountU0))\<close>

definition clss_size_incr_lcountU0 :: \<open>clss_size \<Rightarrow> clss_size\<close> where
  \<open>clss_size_incr_lcountU0 =
     (\<lambda>(lcount, lcountUE, lcountUEk, lcountUS, lcountU0). (lcount, lcountUE, lcountUEk, lcountUS, lcountU0 + 1))\<close>

definition clss_size_resetUS :: \<open>clss_size \<Rightarrow> clss_size\<close> where
  \<open>clss_size_resetUS =
     (\<lambda>(lcount, lcountUE, lcountUEk, lcountUS, lcountU0). (lcount, lcountUE, lcountUEk, 0, lcountU0))\<close>

definition clss_size_resetU0 :: \<open>clss_size \<Rightarrow> clss_size\<close> where
  \<open>clss_size_resetU0 =
     (\<lambda>(lcount, lcountUE, lcountUEk, lcountUS, lcountU0). (lcount, lcountUE, lcountUEk, lcountUS, 0))\<close>

definition clss_size_resetUE :: \<open>clss_size \<Rightarrow> clss_size\<close> where
  \<open>clss_size_resetUE =
     (\<lambda>(lcount, lcountUE, lcountUEk, lcountUS, lcountU0). (lcount, 0, lcountUEk, lcountUS, lcountU0))\<close>

definition clss_size_resetUEk :: \<open>clss_size \<Rightarrow> clss_size\<close> where
  \<open>clss_size_resetUEk =
     (\<lambda>(lcount, lcountUE, lcountUEk, lcountUS, lcountU0). (lcount, lcountUE, 0, lcountUS, lcountU0))\<close>

definition clss_size_allcount :: \<open>clss_size \<Rightarrow> nat\<close> where
  \<open>clss_size_allcount =
    (\<lambda>(lcount, lcountUE, lcountUEk, lcountUS, lcountU0). lcount + lcountUE + lcountUEk + lcountUS + lcountU0)\<close>

abbreviation clss_size_resetUS0 :: \<open>clss_size \<Rightarrow> _\<close> where
  \<open>clss_size_resetUS0 lcount \<equiv> clss_size_resetUE (clss_size_resetUS (clss_size_resetU0 lcount))\<close>

lemma clss_size_add_simp[simp]:
  \<open>clss_size N NE (add_mset D UE) NEk UEk NS US N0 U0 = clss_size_incr_lcountUE (clss_size N NE UE NEk UEk NS US N0 U0)\<close>
  \<open>clss_size N (add_mset C NE) UE NEk UEk NS US N0 U0 = clss_size N NE UE NEk UEk NS US N0 U0\<close>
  \<open>clss_size N NE UE NEk UEk (add_mset C NS) US N0 U0 = clss_size N NE UE NEk UEk NS US N0 U0\<close>
  by (auto simp: clss_size_def ran_m_fmdrop_If clss_size_decr_lcount_def
    clss_size_incr_lcountUE_def size_remove1_mset_If clss_size_resetUS_def)

lemma clss_size_upd_simp[simp]:
  \<open>C \<in># dom_m N \<Longrightarrow>  clss_size (N(C \<hookrightarrow> C')) NE UE NEk UEk NS US N0 U0 = clss_size N NE UE NEk UEk NS US N0 U0\<close>
  \<open>C \<notin># dom_m N \<Longrightarrow> \<not>snd D \<Longrightarrow> clss_size (fmupd C D N) NE UE NEk UEk NS US N0 U0 = clss_size_incr_lcount (clss_size N NE UE NEk UEk NS US N0 U0)\<close>
  \<open>C \<notin># dom_m N \<Longrightarrow> snd D \<Longrightarrow> clss_size (fmupd C D N) NE UE NEk UEk NS US N0 U0 = (clss_size N NE UE NEk UEk NS US N0 U0)\<close>
  by (auto simp: clss_size_def learned_clss_l_fmupd_if clss_size_incr_lcount_def)

lemma clss_size_del_simp[simp]:
  \<open>C \<in># dom_m N \<Longrightarrow> \<not>irred N C \<Longrightarrow> clss_size (fmdrop C N) NE UE NEk UEk NS US N0 U0 = clss_size_decr_lcount (clss_size N NE UE NEk UEk NS US N0 U0)\<close>
  \<open>C \<in># dom_m N \<Longrightarrow> irred N C \<Longrightarrow> clss_size (fmdrop C N) NE UE NEk UEk NS US N0 U0 = (clss_size N NE UE NEk UEk NS US N0 U0)\<close>
  by (auto simp: clss_size_def ran_m_fmdrop_If clss_size_decr_lcount_def
     size_remove1_mset_If clss_size_resetUS_def)


lemma clss_size_lcount_clss_size[simp]:
  \<open>clss_size_lcount (clss_size N NE UE NEk UEk NS US N0 U0) = size (learned_clss_l N)\<close>
  \<open>clss_size_allcount (clss_size N NE UE NEk UEk NS US N0 U0) = size (learned_clss_l N) + size UE + size UEk + size US + size U0\<close>
  by (auto simp: clss_size_lcount_def clss_size_def clss_size_allcount_def)

lemma clss_size_resetUS_simp[simp]:
  \<open>clss_size_resetUS (clss_size_decr_lcount (clss_size baa da ea NEk UEk fa ga ha ia)) =
     clss_size_decr_lcount (clss_size baa da ea NEk UEk fa {#} ha ia)\<close>
  \<open>clss_size_resetUS (clss_size_incr_lcount (clss_size baa da ea NEk UEk fa ga ha ia)) =
     clss_size_incr_lcount (clss_size baa da ea NEk UEk fa {#} ha ia)\<close>
  \<open>clss_size_resetUS  (clss_size_incr_lcountUE (clss_size baa da ea NEk UEk fa ga ha ia)) =
     clss_size_incr_lcountUE (clss_size baa da ea NEk UEk fa {#} ha ia)\<close>
  \<open>clss_size_resetUS (clss_size N NE UE NEk UEk NS US N0 U0) = (clss_size N NE UE NEk UEk NS {#} N0 U0)\<close>
  \<open>clss_size_lcountU0 (clss_size_resetUS x) = clss_size_lcountU0 x\<close>
  by (auto simp: clss_size_resetUS_def clss_size_decr_lcount_def clss_size_def
    clss_size_incr_lcount_def clss_size_incr_lcountUE_def clss_size_lcountU0_def
    split: prod.splits)

lemma [simp]: \<open>clss_size_resetUS (clss_size_incr_lcountUE st) =
         clss_size_incr_lcountUE (clss_size_resetUS st)\<close>
  by (solves \<open>cases st; auto simp: clss_size_incr_lcountUE_def clss_size_resetUS_def\<close>)+

lemma clss_size_lcount_simps2[simp]:
  \<open>clss_size_lcount (clss_size_resetUS S) = clss_size_lcount S\<close>
  \<open>clss_size_lcountUE (clss_size_resetUS S) = clss_size_lcountUE S\<close>
  \<open>clss_size_lcountUS (clss_size_resetUS S) = 0\<close>


  \<open>clss_size_lcount (clss_size_incr_lcountUE S) = clss_size_lcount S\<close>
  \<open>clss_size_lcountUE (clss_size_incr_lcountUE S) = Suc (clss_size_lcountUE S)\<close>
  \<open>clss_size_lcountUS (clss_size_incr_lcountUE S) = clss_size_lcountUS S\<close>


  \<open>clss_size_lcount (clss_size_decr_lcount S) = clss_size_lcount S - 1\<close>
  \<open>clss_size_lcountUE (clss_size_decr_lcount S) = clss_size_lcountUE S\<close>
  \<open>clss_size_lcountUS (clss_size_decr_lcount S) = clss_size_lcountUS S\<close>

  \<open>clss_size_incr_lcountUE (clss_size_decr_lcount S) =
        clss_size_decr_lcount (clss_size_incr_lcountUE S)\<close>
  \<open>clss_size_resetUS (clss_size_decr_lcount S) = 
     clss_size_decr_lcount (clss_size_resetUS S)\<close>
  \<open>clss_size_resetUS (clss_size_incr_lcountUE S) = clss_size_incr_lcountUE (clss_size_resetUS S)\<close>
  by (solves \<open>cases S; auto simp: clss_size_lcount_def clss_size_resetUS_def
    clss_size_lcountUE_def clss_size_lcountUS_def
    clss_size_incr_lcountUE_def clss_size_decr_lcount_def\<close>)+

lemma [simp]:
  \<open>clss_size_lcountU0 (clss_size_decr_lcount S) = clss_size_lcountU0 S\<close>
  \<open>clss_size_lcountU0 (clss_size_incr_lcountUE S) = clss_size_lcountU0 S\<close>
  \<open>clss_size_lcountU0 (clss_size_incr_lcountUS S) = clss_size_lcountU0 S\<close>
  \<open>clss_size_lcountU0 (clss_size_incr_lcountU0 S) = clss_size_lcountU0 S + 1\<close>
  by (auto simp: clss_size_lcountU0_def clss_size_decr_lcount_def clss_size_incr_lcountUE_def
      clss_size_incr_lcountUS_def clss_size_incr_lcountU0_def
    split: prod.splits)

lemma [simp]:
  \<open>clss_size_lcount (clss_size_incr_lcountUEk c) = clss_size_lcount c\<close>
  \<open>clss_size_lcountUE (clss_size_incr_lcountUEk c) = clss_size_lcountUE c\<close>
  \<open>clss_size_lcountUEk (clss_size_incr_lcountUEk c) = clss_size_lcountUEk c+1\<close>
  \<open>clss_size_lcountU0 (clss_size_incr_lcountUEk c) = clss_size_lcountU0 c\<close>
  \<open>clss_size_lcountUS (clss_size_incr_lcountUEk c) = clss_size_lcountUS c\<close>
  by (auto simp: clss_size_lcountUE_def clss_size_lcount_def clss_size_incr_lcountUEk_def
    clss_size_lcountUEk_def clss_size_lcountU0_def clss_size_lcountUS_def
    split: prod.splits)

lemma clss_size_simps3[simp]:
  \<open>clss_size_lcountUE (clss_size baa da ea NEk UEk fa x N0 U0) = size ea\<close>
  \<open>clss_size_lcountUEk (clss_size baa da ea NEk UEk fa x N0 U0) = size UEk\<close>
  \<open>clss_size_lcountUS (clss_size baa da ea NEk UEk fa x N0 U0) = size x\<close>
  \<open>clss_size_lcountU0 (clss_size baa da ea NEk UEk fa x N0 U0) = size U0\<close>
  by (auto simp: clss_size_lcountUE_def clss_size_lcountUS_def clss_size_lcountU0_def clss_size_def
    clss_size_lcountUEk_def)

(*TODO Move inside this file*)
lemma clss_size_lcount_incr_lcount_simps[simp]:
  \<open>clss_size_lcount (clss_size_incr_lcount S) = Suc (clss_size_lcount S)\<close>
  \<open>clss_size_lcountUE (clss_size_incr_lcount S) = (clss_size_lcountUE S)\<close>
  \<open>clss_size_lcountUEk (clss_size_incr_lcount S) = (clss_size_lcountUEk S)\<close>
  \<open>clss_size_lcountUS (clss_size_incr_lcount S) = (clss_size_lcountUS S)\<close>
  \<open>clss_size_lcountU0 (clss_size_incr_lcount (S)) = clss_size_lcountU0 ( (S))\<close>
  by (cases S; auto simp: clss_size_incr_lcount_def
      clss_size_lcount_def clss_size_def clss_size_lcountUEk_def
    clss_size_lcountUE_def clss_size_lcountUS_def clss_size_lcountU0_def; fail)+

lemma [simp]:
  \<open>clss_size_lcount (clss_size_resetU0 c) = clss_size_lcount c\<close>
  \<open>clss_size_lcount (clss_size_resetUE c) = clss_size_lcount c\<close>
  \<open>clss_size_lcount (clss_size_resetUEk c) = clss_size_lcount c\<close>
  \<open>clss_size_lcountUE (clss_size_resetU0 c) = clss_size_lcountUE c\<close>
  \<open>clss_size_lcountUE (clss_size_resetUEk c) = clss_size_lcountUE c\<close>
  \<open>clss_size_lcountU0 (clss_size_resetUE c) = clss_size_lcountU0 c\<close>
  \<open>clss_size_lcountU0 (clss_size_resetUEk c) = clss_size_lcountU0 c\<close>
  \<open>clss_size_lcountU0 (clss_size_resetU0 c) = 0\<close>
 \<open>clss_size_lcountU0 (clss_size_decr_lcount c) = clss_size_lcountU0 c\<close>
  \<open>clss_size_lcountUEk (clss_size_resetUE c) = clss_size_lcountUEk c\<close>
  \<open>clss_size_lcountUEk (clss_size_resetUS c) = clss_size_lcountUEk c\<close>
  \<open>clss_size_lcountUEk (clss_size_resetU0 c) = clss_size_lcountUEk c\<close>
  \<open>clss_size_lcountUEk (clss_size_resetUEk c) = 0\<close>
 \<open>clss_size_lcountUEk (clss_size_decr_lcount c) = clss_size_lcountUEk c\<close>
  \<open>clss_size_lcountUE (clss_size_resetUE c) = 0\<close>
  \<open>clss_size_lcountUS (clss_size_resetUE c) = clss_size_lcountUS c\<close>
  \<open>clss_size_lcountUS (clss_size_resetUEk c) = clss_size_lcountUS c\<close>
  by (auto simp: clss_size_resetU0_def clss_size_lcount_def clss_size_lcountU0_def
    clss_size_lcountUS_def clss_size_decr_lcount_def
    clss_size_resetUE_def clss_size_resetUEk_def clss_size_lcountUE_def clss_size_lcountUEk_def
    clss_size_resetUS_def split: prod.splits)

definition print_literal_of_trail where
  \<open>print_literal_of_trail _ = RETURN ()\<close>

definition print_trail where
  \<open>print_trail = (\<lambda>(M, _). do {
  i \<leftarrow> WHILE\<^sub>T(\<lambda>i. i < length M)
  (\<lambda>i. do {
  ASSERT(i < length M);
  print_literal_of_trail (M!i);
  RETURN (i+1)})
  0;
  print_literal_of_trail ((0::nat));
  RETURN ()
  })\<close>

definition print_trail2 where
  \<open>print_trail2 = (\<lambda>(M, _). RETURN ())\<close>

lemma print_trail_print_trail2:
  \<open>(M,M')\<in>Id \<Longrightarrow> print_trail M \<le> \<Down> Id (print_trail2 M')\<close>
  unfolding print_trail_def print_trail2_def
  apply (refine_vcg WHILET_rule[where
    R = \<open>measure (\<lambda>i. Suc (length (fst M)) - i)\<close> and
    I = \<open>\<lambda>i. i \<le> length (fst M)\<close>])
  subgoal by auto
  subgoal by auto
  subgoal unfolding print_literal_of_trail_def by auto
  subgoal unfolding print_literal_of_trail_def by auto
  done

lemma print_trail_print_trail2_rel:
  \<open>(print_trail, print_trail2) \<in> Id \<rightarrow>\<^sub>f \<langle>unit_rel\<rangle>nres_rel\<close>
  using print_trail_print_trail2 by (fastforce intro: frefI nres_relI)

definition clss_size_corr :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow>_ \<Rightarrow> _ \<Rightarrow>_ \<Rightarrow> _ \<Rightarrow>_ \<Rightarrow> clss_size \<Rightarrow> bool\<close> where
  \<open>clss_size_corr N NE UE NEk UEk NS US N0 U0 c \<longleftrightarrow> c = clss_size N NE UE NEk UEk NS US N0 U0\<close>

text \<open>There is no equivalence because of rounding errors. However, we do not care about that in
  the proofs and we are always safe in IsaSAT.

  However, the intro rule are still too dangerous and make it hard to recognize the original goal.
  Therefore, they are not marked as safe.
\<close>
lemma
  clss_size_corr_intro[intro!]:
    \<open>C \<in># dom_m N \<Longrightarrow> \<not>irred N C \<Longrightarrow>clss_size_corr N NE UE NEk UEk NS US N0 U0 c \<Longrightarrow> clss_size_corr (fmdrop C N) NE UE NEk UEk NS US N0 U0 (clss_size_decr_lcount c)\<close>
    \<open>C \<notin># dom_m N \<Longrightarrow> \<not>b \<Longrightarrow>clss_size_corr N NE UE NEk UEk NS US N0 U0 c \<Longrightarrow> clss_size_corr (fmupd C (D, b) N) NE UE NEk UEk NS US N0 U0 (clss_size_incr_lcount c)\<close>
    \<open>clss_size_corr N NE UE NEk UEk NS US N0 U0 c \<Longrightarrow> clss_size_corr N NE UE NEk (add_mset E UEk) NS US N0 U0 (clss_size_incr_lcountUEk c)\<close>
    \<open>clss_size_corr N NE UE NEk UEk NS US N0 U0 c \<Longrightarrow> clss_size_corr N NE (add_mset E UE) NEk UEk NS US N0 U0 (clss_size_incr_lcountUE c)\<close>
    \<open>clss_size_corr N NE UE NEk UEk NS US N0 U0 c \<Longrightarrow> clss_size_corr N NE UE NEk UEk NS (add_mset E US) N0 U0 (clss_size_incr_lcountUS c)\<close>
    \<open>clss_size_corr N NE UE NEk UEk NS US N0 U0 c \<Longrightarrow> clss_size_corr N NE UE NEk UEk NS US N0 (add_mset E U0) (clss_size_incr_lcountU0 c)\<close>
    \<open>clss_size_corr N NE UE NEk UEk NS US N0 U0 (clss_size N NE UE NEk UEk NS US N0 U0)\<close>
  and
  clss_size_corr_simp[simp]:
    \<open>clss_size_corr N NE UE NEk UEk NS US N0 U0 c \<Longrightarrow> clss_size_corr N NE UE NEk UEk NS {#} N0 U0 (clss_size_resetUS c)\<close>
    \<open>clss_size_corr N NE UE NEk UEk NS US N0 U0 c \<Longrightarrow> clss_size_corr N NE UE NEk {#} NS US N0 U0 (clss_size_resetUEk c)\<close>
    \<open>clss_size_corr N NE UE NEk UEk NS US N0 U0 c \<Longrightarrow> clss_size_corr N NE UE NEk UEk NS US N0 {#} (clss_size_resetU0 c)\<close>
    \<open>C \<notin># dom_m N \<Longrightarrow> b \<Longrightarrow> clss_size_corr (fmupd C (D, b) N) NE UE NEk UEk NS US N0 U0 c \<longleftrightarrow>
      clss_size_corr N NE UE NEk UEk NS US N0 U0 c\<close>
    \<open>C \<in># dom_m N \<Longrightarrow> irred N C \<Longrightarrow> clss_size_corr (fmdrop C N) NE UE NEk UEk NS US N0 U0 c = clss_size_corr N NE UE NEk UEk NS US N0 U0 c\<close>
    \<open>C \<in># dom_m N \<Longrightarrow> clss_size_corr (N(C \<hookrightarrow> swap (N \<propto> C) i j)) NE UE NEk UEk NS US N0 U0 c = clss_size_corr N NE UE NEk UEk NS US N0 U0 c\<close>
    \<open>clss_size_corr N NE UE (add_mset E NEk) UEk NS US N0 U0 c = clss_size_corr N NE UE NEk UEk NS US N0 U0 c\<close>
    \<open>clss_size_corr N (add_mset E NE) UE NEk UEk NS US N0 U0 c = clss_size_corr N NE UE NEk UEk NS US N0 U0 c\<close>
    \<open>clss_size_corr N NE UE NEk UEk (add_mset E NS) US N0 U0 c = clss_size_corr N NE UE NEk UEk NS US N0 U0 c\<close>
    \<open>clss_size_corr N NE UE NEk UEk NS US (add_mset E N0) U0 c = clss_size_corr N NE UE NEk UEk NS US N0 U0 c\<close>
    \<open>clss_size_corr N NE UE NEk UEk NS US N0 U0 lcount \<Longrightarrow> clss_size_lcount lcount = size (learned_clss_lf N)\<close>
  by (auto simp: clss_size_def ran_m_fmdrop_If clss_size_decr_lcount_def learned_clss_l_fmupd_if
    clss_size_incr_lcount_def clss_size_incr_lcountUS_def clss_size_incr_lcountU0_def clss_size_incr_lcountUEk_def
    clss_size_incr_lcountUE_def  clss_size_lcount_def clss_size_resetUEk_def clss_size_resetU0_def
      size_remove1_mset_If clss_size_resetUS_def clss_size_corr_def; fail)+

text \<open>This version of the counter is incomplete. It is however useful because we do not need to care
about some of the counts during restarts. In particular, it avoids taking care of overflows.
\<close>
definition clss_size_corr_restart :: \<open>'v clauses_l \<Rightarrow> 'v clauses \<Rightarrow> 'v clauses \<Rightarrow> 'v clauses \<Rightarrow> 'v clauses \<Rightarrow>
  'v clauses \<Rightarrow> 'v clauses \<Rightarrow> 'v clauses \<Rightarrow> 'v clauses \<Rightarrow> clss_size \<Rightarrow> bool\<close> where
  \<open>clss_size_corr_restart N NE UE NEk UEk NS US N0 U0 c \<longleftrightarrow> (\<exists>UE US U0. c = clss_size N NE UE NEk UEk NS US N0 U0)\<close>

lemma clss_size_corr_restart_clss_size_corr:
  \<open>clss_size_corr N NE UE NEk UEk NS US N0 U0 c \<Longrightarrow> clss_size_corr_restart N NE UE' NEk UEk NS US' N0 U0' c\<close>
  \<open>clss_size_corr_restart N NE UE NEk UEk NS US N0 U0 c \<Longrightarrow> clss_size_corr N NE {#} NEk UEk NS {#} N0 {#} (clss_size_resetUS0 c)\<close>
  by (auto simp: clss_size_corr_def clss_size_corr_restart_def clss_size_resetUS_def
    clss_size_resetU0_def clss_size_def clss_size_resetUE_def)

lemma
  clss_size_corr_restart_intro[intro]:
    \<open>C \<in># dom_m N \<Longrightarrow> \<not>irred N C \<Longrightarrow>clss_size_corr_restart N NE UE NEk UEk NS US N0 U0 c \<Longrightarrow> clss_size_corr_restart (fmdrop C N) NE {#} NEk UEk NS {#} N0 {#} (clss_size_decr_lcount c)\<close>
    \<open>C \<notin># dom_m N \<Longrightarrow> \<not>b \<Longrightarrow>clss_size_corr_restart N NE UE NEk UEk NS US N0 U0 c \<Longrightarrow> clss_size_corr_restart (fmupd C (D, b) N) NE {#} NEk UEk NS {#} N0 {#} (clss_size_incr_lcount c)\<close>
    \<open>clss_size_corr_restart N NE UE NEk UEk NS US N0 U0 c \<Longrightarrow> clss_size_corr_restart N NE {#} NEk (add_mset E UEk) NS {#} N0 {#} (clss_size_incr_lcountUEk c)\<close>
    \<open>clss_size_corr_restart N NE UE NEk UEk NS US N0 U0 (clss_size N NE {#} NEk UEk NS {#} N0 {#})\<close>
  \<open>clss_size_corr_restart N NE UE NEk UEk NS US N0 U0 c \<Longrightarrow> clss_size_corr_restart N NE {#} NEk UEk NS {#} N0 {#} c\<close>

  \<open>clss_size_corr_restart N NE UE NEk UEk NS US N0 U0 c \<Longrightarrow> clss_size_corr_restart N NE {#} NEk UEk NS US N0 U0 (c)\<close>
  \<open>clss_size_corr_restart N NE UE NEk UEk NS US N0 U0 c \<Longrightarrow> clss_size_corr_restart N NE UE NEk UEk NS US N0 {#} (c)\<close>
  \<open>clss_size_corr_restart N NE UE NEk UEk NS US N0 U0 c \<Longrightarrow> clss_size_corr_restart N NE UE NEk UEk NS {#} N0 U0 (c)\<close>
  \<open>clss_size_corr_restart N NE UE NEk UEk NS US N0 U0 c \<Longrightarrow> clss_size_corr_restart N NE UE NEk UEk NS US N0 {#} (c)\<close>
  and
  clss_size_corr_restart_simp[simp]:
  \<open>NO_MATCH {#} UE \<Longrightarrow> clss_size_corr_restart N NE UE NEk UEk NS US N0 U0 c \<longleftrightarrow> clss_size_corr_restart N NE {#} NEk UEk NS US N0 U0 (c)\<close>
  \<open>NO_MATCH {#} U0 \<Longrightarrow> clss_size_corr_restart N NE UE NEk UEk NS US N0 U0 c \<longleftrightarrow> clss_size_corr_restart N NE UE NEk UEk NS US N0 {#} (c)\<close>
  \<open>NO_MATCH {#} US \<Longrightarrow> clss_size_corr_restart N NE UE NEk UEk NS US N0 U0 c \<longleftrightarrow> clss_size_corr_restart N NE UE NEk UEk NS {#} N0 U0 (c)\<close>
  \<open>NO_MATCH {#} UE \<Longrightarrow> clss_size_corr_restart N NE UE NEk UEk NS US N0 U0 c \<longleftrightarrow> clss_size_corr_restart N NE UE NEk UEk NS US N0 {#} (c)\<close>
    (* \<open>clss_size_corr_restart N NE UE NEk UEk NS US N0 U0 c \<Longrightarrow> clss_size_corr_restart N NE UE NEk UEk NS {#} N0 U0 (c)\<close> *)
  \<open>clss_size_corr_restart N NE UE NEk UEk NS US N0 U0 c \<Longrightarrow> clss_size_corr_restart N NE UE NEk {#} NS US N0 U0 (clss_size_resetUEk c)\<close>
    \<open>clss_size_corr_restart N NE UE NEk UEk NS (add_mset E US) N0 U0 (c) \<longleftrightarrow> clss_size_corr_restart N NE UE NEk UEk NS US N0 U0 c\<close>
    \<open>clss_size_corr_restart N NE UE NEk UEk NS US N0 (add_mset E U0) (c) \<longleftrightarrow> clss_size_corr_restart N NE UE NEk UEk NS US N0 U0 c\<close>
    \<open>C \<notin># dom_m N \<Longrightarrow> b \<Longrightarrow> clss_size_corr_restart (fmupd C (D, b) N) NE UE NEk UEk NS US N0 U0 c \<longleftrightarrow>
      clss_size_corr_restart N NE UE NEk UEk NS US N0 U0 c\<close>
    \<open>C \<in># dom_m N \<Longrightarrow> irred N C \<Longrightarrow> clss_size_corr_restart (fmdrop C N) NE UE NEk UEk NS US N0 U0 c = clss_size_corr_restart N NE UE NEk UEk NS US N0 U0 c\<close>
    \<open>C \<in># dom_m N \<Longrightarrow> clss_size_corr_restart (N(C \<hookrightarrow> swap (N \<propto> C) i j)) NE UE NEk UEk NS US N0 U0 c = clss_size_corr_restart N NE UE NEk UEk NS US N0 U0 c\<close>
    \<open>clss_size_corr_restart N (add_mset E NE) UE NEk UEk NS US N0 U0 c = clss_size_corr_restart N NE UE NEk UEk NS US N0 U0 c\<close>
    \<open>clss_size_corr_restart N NE UE (add_mset E NEk) UEk NS US N0 U0 c = clss_size_corr_restart N NE UE NEk UEk NS US N0 U0 c\<close>
    \<open>clss_size_corr_restart N NE UE NEk UEk (add_mset E NS) US N0 U0 c = clss_size_corr_restart N NE UE NEk UEk NS US N0 U0 c\<close>
  \<open>clss_size_corr_restart N NE UE NEk UEk NS US (add_mset E N0) U0 c = clss_size_corr_restart N NE UE NEk UEk NS US N0 U0 c\<close>
  by (auto simp: clss_size_def ran_m_fmdrop_If clss_size_decr_lcount_def learned_clss_l_fmupd_if
    clss_size_incr_lcount_def clss_size_incr_lcountUS_def clss_size_incr_lcountU0_def clss_size_incr_lcountUEk_def
    clss_size_incr_lcountUE_def  clss_size_lcount_def clss_size_resetUEk_def clss_size_resetU0_def
    clss_size_resetUE_def
      size_remove1_mset_If clss_size_resetUS_def clss_size_corr_restart_def; fail)+

text \<open>The following lemmas produce loops, but usually only in the next file (!). Hence, we do
  not activate them by default as simp rules.
\<close>
lemma clss_size_corr_restart_rew:
  \<open>clss_size_corr_restart N NE UE NEk UEk NS US N0 U0 lcount \<Longrightarrow> clss_size_lcount lcount = size (learned_clss_lf N)\<close>
  by (auto simp: clss_size_def ran_m_fmdrop_If clss_size_decr_lcount_def learned_clss_l_fmupd_if
    clss_size_incr_lcount_def clss_size_incr_lcountUS_def clss_size_incr_lcountU0_def clss_size_incr_lcountUEk_def
    clss_size_incr_lcountUE_def  clss_size_lcount_def clss_size_resetUEk_def clss_size_resetU0_def
    clss_size_resetUE_def
      size_remove1_mset_If clss_size_resetUS_def clss_size_corr_restart_def; fail)+

lemma clss_size_corr_restart_simp3:
  \<open>clss_size_corr_restart N NE UE NEk (add_mset E UEk) NS US N0 U0 (clss_size_incr_lcountUEk c) \<longleftrightarrow>
  clss_size_corr_restart N NE UE NEk UEk NS US N0 U0 c\<close>
  by (auto simp: clss_size_corr_restart_def clss_size_incr_lcountUEk_def clss_size_def
    split: prod.splits)

subsection \<open>Lifting to heuristic level\<close>
definition get_next_phase_heur_pre_stats :: \<open>bool \<Rightarrow> nat \<Rightarrow> restart_heuristics \<Rightarrow> bool\<close> where
  \<open>get_next_phase_heur_pre_stats = (\<lambda>b L (_, _, _, _, rephase, _).
  get_next_phase_pre b L rephase)\<close>

definition get_next_phase_heur_stats :: \<open>bool \<Rightarrow> nat \<Rightarrow> restart_heuristics \<Rightarrow> bool nres\<close>  where
  \<open>get_next_phase_heur_stats = (\<lambda>b L (_, _, _, _, rephase, _).
    get_next_phase_stats b L rephase)\<close>

definition get_next_phase_heur :: \<open>bool \<Rightarrow> nat \<Rightarrow> isasat_restart_heuristics \<Rightarrow> bool nres\<close>  where
  \<open>get_next_phase_heur = (\<lambda>b L heur.
  let heur = get_restart_heuristics heur in
  get_next_phase_heur_stats b L heur)\<close>

definition end_of_restart_phase_stats :: \<open>restart_heuristics \<Rightarrow> 64 word\<close> where
  \<open>end_of_restart_phase_stats = (\<lambda>(_, _, (restart_phase,_ ,_ , end_of_phase, _), _).
    end_of_phase)\<close>

definition end_of_restart_phase :: \<open>isasat_restart_heuristics \<Rightarrow> 64 word\<close> where
  \<open>end_of_restart_phase = end_of_restart_phase_stats o get_content\<close>

end
