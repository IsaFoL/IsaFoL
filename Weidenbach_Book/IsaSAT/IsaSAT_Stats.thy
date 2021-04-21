theory IsaSAT_Stats
  imports IsaSAT_Literals IsaSAT_EMA IsaSAT_Rephase IsaSAT_Reluctant
begin


section \<open>Statistics\<close>

text \<open>
We do some statistics on the run.

NB: the statistics are not proven correct (especially they might
overflow), there are just there to look for regressions, do some comparisons (e.g., to conclude that
we are propagating slower than the other solvers), or to test different option combinations.
\<close>
type_synonym stats = \<open>64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times>
  64 word \<times> ema\<close>


definition incr_propagation :: \<open>stats \<Rightarrow> stats\<close> where
  \<open>incr_propagation = (\<lambda>(propa, confl, dec). (propa + 1, confl, dec))\<close>

definition incr_conflict :: \<open>stats \<Rightarrow> stats\<close> where
  \<open>incr_conflict = (\<lambda>(propa, confl, dec). (propa, confl + 1, dec))\<close>

definition incr_decision :: \<open>stats \<Rightarrow> stats\<close> where
  \<open>incr_decision = (\<lambda>(propa, confl, dec, res). (propa, confl, dec + 1, res))\<close>

definition incr_restart :: \<open>stats \<Rightarrow> stats\<close> where
  \<open>incr_restart = (\<lambda>(propa, confl, dec, res, lres). (propa, confl, dec, res + 1, lres))\<close>

definition incr_lrestart :: \<open>stats \<Rightarrow> stats\<close> where
  \<open>incr_lrestart = (\<lambda>(propa, confl, dec, res, lres, uset). (propa, confl, dec, res, lres + 1, uset))\<close>

definition incr_uset :: \<open>stats \<Rightarrow> stats\<close> where
  \<open>incr_uset = (\<lambda>(propa, confl, dec, res, lres, (uset, gcs)). (propa, confl, dec, res, lres, uset + 1, gcs))\<close>

definition incr_GC :: \<open>stats \<Rightarrow> stats\<close> where
  \<open>incr_GC = (\<lambda>(propa, confl, dec, res, lres, uset, gcs, lbds). (propa, confl, dec, res, lres, uset, gcs + 1, lbds))\<close>

definition stats_conflicts :: \<open>stats \<Rightarrow> 64 word\<close> where
  \<open>stats_conflicts = (\<lambda>(propa, confl, dec). confl)\<close>

definition add_lbd :: \<open>32 word \<Rightarrow> stats \<Rightarrow> stats\<close> where
  \<open>add_lbd lbd = (\<lambda>(propa, confl, dec, res, lres, uset, gcs, units, lbds). (propa, confl, dec, res, lres, uset, gcs, units, ema_update (unat lbd) lbds))\<close>


definition units_since_last_GC :: \<open>stats \<Rightarrow> 64 word\<close> where
  \<open>units_since_last_GC = (\<lambda>(propa, confl, dec, res, lres, uset, gcs, units, lbds). units)\<close>

definition incr_units_since_last_GC :: \<open>stats \<Rightarrow> stats\<close> where
  \<open>incr_units_since_last_GC = (\<lambda>(propa, confl, dec, res, lres, uset, gcs, units, lbds). (propa, confl, dec, res, lres, uset, gcs, units + 1, lbds))\<close>


definition reset_units_since_last_GC :: \<open>stats \<Rightarrow> stats\<close> where
  \<open>reset_units_since_last_GC = (\<lambda>(propa, confl, dec, res, lres, uset, gcs, units, lbds). (propa, confl, dec, res, lres, uset, gcs, 0, lbds))\<close>


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



section \<open>Heuristics\<close>

type_synonym restart_heuristics = \<open>ema \<times> ema \<times> restart_info \<times> 64 word \<times> phase_save_heur \<times> reluctant\<close>

fun fast_ema_of :: \<open>restart_heuristics \<Rightarrow> ema\<close> where
  \<open>fast_ema_of (fast_ema, slow_ema, restart_info, wasted, \<phi>) = fast_ema\<close>

fun slow_ema_of :: \<open>restart_heuristics \<Rightarrow> ema\<close> where
  \<open>slow_ema_of (fast_ema, slow_ema, restart_info, wasted, \<phi>) = slow_ema\<close>

fun restart_info_of :: \<open>restart_heuristics \<Rightarrow> restart_info\<close> where
  \<open>restart_info_of (fast_ema, slow_ema, restart_info, wasted, \<phi>) = restart_info\<close>

fun current_restart_phase :: \<open>restart_heuristics \<Rightarrow> 64 word\<close> where
  \<open>current_restart_phase (fast_ema, slow_ema, (ccount, ema_lvl, restart_phase, end_of_phase), wasted, \<phi>) =
    restart_phase\<close>

fun incr_restart_phase :: \<open>restart_heuristics \<Rightarrow> restart_heuristics\<close> where
  \<open>incr_restart_phase (fast_ema, slow_ema, (ccount, ema_lvl, restart_phase, end_of_phase), wasted, \<phi>) =
    (fast_ema, slow_ema, (ccount, ema_lvl, restart_phase XOR 1, end_of_phase), wasted, \<phi>)\<close>

fun incr_wasted :: \<open>64 word \<Rightarrow> restart_heuristics \<Rightarrow> restart_heuristics\<close> where
  \<open>incr_wasted waste (fast_ema, slow_ema, res_info, wasted, \<phi>) =
    (fast_ema, slow_ema, res_info, wasted + waste, \<phi>)\<close>

fun set_zero_wasted :: \<open>restart_heuristics \<Rightarrow> restart_heuristics\<close> where
  \<open>set_zero_wasted (fast_ema, slow_ema, res_info, wasted, \<phi>) =
    (fast_ema, slow_ema, res_info, 0, \<phi>)\<close>

fun wasted_of :: \<open>restart_heuristics \<Rightarrow> 64 word\<close> where
  \<open>wasted_of (fast_ema, slow_ema, res_info, wasted, \<phi>) = wasted\<close>

definition heuristic_rel :: \<open>nat multiset \<Rightarrow> restart_heuristics \<Rightarrow> bool\<close> where
  \<open>heuristic_rel \<A> = (\<lambda>(fast_ema, slow_ema, res_info, wasted, \<phi>, _). phase_save_heur_rel \<A> \<phi>)\<close>

definition save_phase_heur :: \<open>nat \<Rightarrow> bool \<Rightarrow> restart_heuristics \<Rightarrow> restart_heuristics\<close> where
\<open>save_phase_heur L b = (\<lambda>(fast_ema, slow_ema, res_info, wasted, (\<phi>, target, best), reluctant).
    (fast_ema, slow_ema, res_info, wasted, (\<phi>[L := b], target, best), reluctant))\<close>

definition save_phase_heur_pre :: \<open>nat \<Rightarrow> bool \<Rightarrow> restart_heuristics \<Rightarrow> bool\<close> where
\<open>save_phase_heur_pre L b = (\<lambda>(fast_ema, slow_ema, res_info, wasted, (\<phi>, _), _). L < length \<phi>)\<close>

definition mop_save_phase_heur :: \<open>nat \<Rightarrow> bool \<Rightarrow> restart_heuristics \<Rightarrow> restart_heuristics nres\<close> where
\<open>mop_save_phase_heur L b heur = do {
   ASSERT(save_phase_heur_pre L b heur);
   RETURN (save_phase_heur L b heur)
}\<close>

definition get_saved_phase_heur_pre :: \<open>nat \<Rightarrow> restart_heuristics \<Rightarrow> bool\<close> where
\<open>get_saved_phase_heur_pre L = (\<lambda>(fast_ema, slow_ema, res_info, wasted, (\<phi>, _), _). L < length \<phi>)\<close>

definition get_saved_phase_heur :: \<open>nat \<Rightarrow> restart_heuristics \<Rightarrow> bool\<close> where
\<open>get_saved_phase_heur L = (\<lambda>(fast_ema, slow_ema, res_info, wasted, (\<phi>, _), _). \<phi>!L)\<close>

definition current_rephasing_phase :: \<open>restart_heuristics \<Rightarrow> 64 word\<close> where
\<open>current_rephasing_phase = (\<lambda>(fast_ema, slow_ema, res_info, wasted, \<phi>, _). phase_current_rephasing_phase \<phi>)\<close>

definition mop_get_saved_phase_heur :: \<open>nat \<Rightarrow> restart_heuristics \<Rightarrow> bool nres\<close> where
\<open>mop_get_saved_phase_heur L heur = do {
   ASSERT(get_saved_phase_heur_pre L heur);
   RETURN (get_saved_phase_heur L heur)
}\<close>

definition heuristic_reluctant_tick :: \<open>restart_heuristics \<Rightarrow> restart_heuristics\<close> where
  \<open>heuristic_reluctant_tick = (\<lambda>(fast_ema, slow_ema, res_info, wasted, \<phi>, reluctant).
     (fast_ema, slow_ema, res_info, wasted, \<phi>, reluctant_tick reluctant))\<close>

definition heuristic_reluctant_enable :: \<open>restart_heuristics \<Rightarrow> restart_heuristics\<close> where
  \<open>heuristic_reluctant_enable = (\<lambda>(fast_ema, slow_ema, res_info, wasted, \<phi>, reluctant).
     (fast_ema, slow_ema, res_info, wasted, \<phi>, reluctant_init))\<close>

definition heuristic_reluctant_disable :: \<open>restart_heuristics \<Rightarrow> restart_heuristics\<close> where
  \<open>heuristic_reluctant_disable = (\<lambda>(fast_ema, slow_ema, res_info, wasted, \<phi>, reluctant).
     (fast_ema, slow_ema, res_info, wasted, \<phi>, reluctant_disable reluctant))\<close>

definition heuristic_reluctant_triggered :: \<open>restart_heuristics \<Rightarrow> restart_heuristics \<times> bool\<close> where
  \<open>heuristic_reluctant_triggered = (\<lambda>(fast_ema, slow_ema, res_info, wasted, \<phi>, reluctant).
    let (reluctant, b) = reluctant_triggered reluctant in
     ((fast_ema, slow_ema, res_info, wasted, \<phi>, reluctant), b))\<close>

definition heuristic_reluctant_triggered2 :: \<open>restart_heuristics \<Rightarrow> bool\<close> where
  \<open>heuristic_reluctant_triggered2 = (\<lambda>(fast_ema, slow_ema, res_info, wasted, \<phi>, reluctant).
    reluctant_triggered2 reluctant)\<close>

definition heuristic_reluctant_untrigger :: \<open>restart_heuristics \<Rightarrow> restart_heuristics\<close> where
  \<open>heuristic_reluctant_untrigger = (\<lambda>(fast_ema, slow_ema, res_info, wasted, \<phi>, reluctant).
    (fast_ema, slow_ema, res_info, wasted, \<phi>, reluctant_untrigger reluctant))\<close>

definition end_of_rephasing_phase_heur :: \<open>restart_heuristics \<Rightarrow> 64 word\<close> where
  \<open>end_of_rephasing_phase_heur =
    (\<lambda>(fast_ema, slow_ema, res_info, wasted, phasing, reluctant). end_of_rephasing_phase phasing)\<close>


lemma heuristic_relI[intro!]:
  \<open>heuristic_rel \<A> heur \<Longrightarrow> heuristic_rel \<A> (incr_wasted wast heur)\<close>
  \<open>heuristic_rel \<A> heur \<Longrightarrow> heuristic_rel \<A> (set_zero_wasted heur)\<close>
  \<open>heuristic_rel \<A> heur \<Longrightarrow> heuristic_rel \<A> (incr_restart_phase heur)\<close>
  \<open>heuristic_rel \<A> heur \<Longrightarrow> heuristic_rel \<A> (save_phase_heur L b heur)\<close>
  \<open>heuristic_rel \<A> heur \<Longrightarrow> heuristic_rel \<A> (heuristic_reluctant_tick heur)\<close>
  \<open>heuristic_rel \<A> heur \<Longrightarrow> heuristic_rel \<A> (heuristic_reluctant_enable heur)\<close>
  \<open>heuristic_rel \<A> heur \<Longrightarrow> heuristic_rel \<A> (heuristic_reluctant_untrigger heur)\<close>
  by (clarsimp_all simp: heuristic_rel_def save_phase_heur_def phase_save_heur_rel_def phase_saving_def
    heuristic_reluctant_tick_def heuristic_reluctant_enable_def heuristic_reluctant_untrigger_def)

lemma heuristic_rel_heuristic_reluctant_triggeredD:
  \<open>heuristic_rel \<A> heur \<Longrightarrow>
     heuristic_rel \<A> (fst (heuristic_reluctant_triggered heur))\<close>
  by (clarsimp simp: heuristic_reluctant_triggered_def heuristic_rel_def  phase_save_heur_rel_def
    phase_saving_def reluctant_triggered_def)

lemma save_phase_heur_preI:
  \<open>heuristic_rel \<A> heur \<Longrightarrow> a \<in># \<A> \<Longrightarrow> save_phase_heur_pre a b heur\<close>
  by (auto simp: heuristic_rel_def phase_saving_def save_phase_heur_pre_def
     phase_save_heur_rel_def atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n)

subsection \<open>Number of clauses\<close>

type_synonym clss_size = \<open>nat \<times> nat \<times> nat \<times> nat\<close>

definition clss_size
  :: \<open>'v clauses_l \<Rightarrow> 'v clauses \<Rightarrow> 'v clauses \<Rightarrow> 'v clauses \<Rightarrow> 'v clauses \<Rightarrow>'v clauses \<Rightarrow> 'v clauses \<Rightarrow>
     clss_size\<close>
where
  \<open>clss_size N NE UE NS US N0 U0 =
     (size (learned_clss_lf N), size UE, size US, size U0)\<close>

definition clss_size_lcount :: \<open>clss_size \<Rightarrow> nat\<close> where
  \<open>clss_size_lcount = (\<lambda>(lcount, lcountUE, lcountUS). lcount)\<close>

definition clss_size_lcountUE :: \<open>clss_size \<Rightarrow> nat\<close> where
  \<open>clss_size_lcountUE = (\<lambda>(lcount, lcountUE, lcountUS). lcountUE)\<close>

definition clss_size_lcountUS :: \<open>clss_size \<Rightarrow> nat\<close> where
  \<open>clss_size_lcountUS = (\<lambda>(lcount, lcountUE, lcountUS, _). lcountUS)\<close>

definition clss_size_lcountU0 :: \<open>clss_size \<Rightarrow> nat\<close> where
  \<open>clss_size_lcountU0 = (\<lambda>(lcount, lcountUE, lcountUS, lcountU0). lcountU0)\<close>

definition clss_size_incr_lcount :: \<open>clss_size \<Rightarrow> clss_size\<close> where
  \<open>clss_size_incr_lcount =
     (\<lambda>(lcount, lcountUE, lcountUS). (lcount + 1, lcountUE, lcountUS))\<close>

definition clss_size_decr_lcount :: \<open>clss_size \<Rightarrow> clss_size\<close> where
  \<open>clss_size_decr_lcount =
     (\<lambda>(lcount, lcountUE, lcountUS). (lcount - 1, lcountUE, lcountUS))\<close>

definition clss_size_incr_lcountUE :: \<open>clss_size \<Rightarrow> clss_size\<close> where
  \<open>clss_size_incr_lcountUE =
     (\<lambda>(lcount, lcountUE, lcountUS). (lcount, lcountUE + 1, lcountUS))\<close>

definition clss_size_incr_lcountUS :: \<open>clss_size \<Rightarrow> clss_size\<close> where
  \<open>clss_size_incr_lcountUS =
     (\<lambda>(lcount, lcountUE, lcountUS, lcountU0). (lcount, lcountUE, lcountUS + 1, lcountU0))\<close>

definition clss_size_incr_lcountU0 :: \<open>clss_size \<Rightarrow> clss_size\<close> where
  \<open>clss_size_incr_lcountU0 =
     (\<lambda>(lcount, lcountUE, lcountUS, lcountU0). (lcount, lcountUE, lcountUS, lcountU0 + 1))\<close>

definition clss_size_resetUS :: \<open>clss_size \<Rightarrow> clss_size\<close> where
  \<open>clss_size_resetUS =
     (\<lambda>(lcount, lcountUE, lcountUS, lcountU0). (lcount, lcountUE, 0, lcountU0))\<close>

definition clss_size_allcount :: \<open>clss_size \<Rightarrow> nat\<close> where
  \<open>clss_size_allcount =
    (\<lambda>(lcount, lcountUE, lcountUS, lcountU0). lcount + lcountUE + lcountUS + lcountU0)\<close>

lemma clss_size_add_simp[simp]:
  \<open>clss_size N NE (add_mset D UE) NS US N0 U0 = clss_size_incr_lcountUE (clss_size N NE UE NS US N0 U0)\<close>
  \<open>clss_size N (add_mset C NE) UE NS US N0 U0 = clss_size N NE UE NS US N0 U0\<close>
  \<open>clss_size N NE UE (add_mset C NS) US N0 U0 = clss_size N NE UE NS US N0 U0\<close>
  by (auto simp: clss_size_def ran_m_fmdrop_If clss_size_decr_lcount_def
    clss_size_incr_lcountUE_def size_remove1_mset_If clss_size_resetUS_def)

lemma clss_size_upd_simp[simp]:
  \<open>C \<in># dom_m N \<Longrightarrow>  clss_size (N(C \<hookrightarrow> C')) NE UE NS US N0 U0 = clss_size N NE UE NS US N0 U0\<close>
  \<open>C \<notin># dom_m N \<Longrightarrow> \<not>snd D \<Longrightarrow> clss_size (fmupd C D N) NE UE NS US N0 U0 = clss_size_incr_lcount (clss_size N NE UE NS US N0 U0)\<close>
  \<open>C \<notin># dom_m N \<Longrightarrow> snd D \<Longrightarrow> clss_size (fmupd C D N) NE UE NS US N0 U0 = (clss_size N NE UE NS US N0 U0)\<close>
  by (auto simp: clss_size_def learned_clss_l_fmupd_if clss_size_incr_lcount_def)

lemma clss_size_del_simp[simp]:
  \<open>C \<in># dom_m N \<Longrightarrow> \<not>irred N C \<Longrightarrow> clss_size (fmdrop C N) NE UE NS US N0 U0 = clss_size_decr_lcount (clss_size N NE UE NS US N0 U0)\<close>
  \<open>C \<in># dom_m N \<Longrightarrow> irred N C \<Longrightarrow> clss_size (fmdrop C N) NE UE NS US N0 U0 = (clss_size N NE UE NS US N0 U0)\<close>
  by (auto simp: clss_size_def ran_m_fmdrop_If clss_size_decr_lcount_def
     size_remove1_mset_If clss_size_resetUS_def)


lemma clss_size_lcount_clss_size[simp]:
  \<open>clss_size_lcount (clss_size N NE UE NS US N0 U0) = size (learned_clss_l N)\<close>
  \<open>clss_size_allcount (clss_size N NE UE NS US N0 U0) = size (learned_clss_l N) + size UE + size US + size U0\<close>
  by (auto simp: clss_size_lcount_def clss_size_def clss_size_allcount_def)

lemma clss_size_resetUS_simp[simp]:
  \<open>clss_size_resetUS (clss_size_decr_lcount (clss_size baa da ea fa ga ha ia)) =
     clss_size_decr_lcount (clss_size baa da ea fa {#} ha ia)\<close>
  \<open>clss_size_resetUS (clss_size_incr_lcount (clss_size baa da ea fa ga ha ia)) =
     clss_size_incr_lcount (clss_size baa da ea fa {#} ha ia)\<close>
  \<open>clss_size_resetUS  (clss_size_incr_lcountUE (clss_size baa da ea fa ga ha ia)) =
     clss_size_incr_lcountUE (clss_size baa da ea fa {#} ha ia)\<close>
  \<open>clss_size_resetUS (clss_size N NE UE NS US N0 U0) = (clss_size N NE UE NS {#} N0 U0)\<close>
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


definition print_trail_st where
  \<open>print_trail_st = (\<lambda>(M, _). print_trail M)\<close>

definition print_trail_st2 where
  \<open>print_trail_st2 _ = ()\<close>

lemma print_trail_st_print_trail_st2:
  \<open>print_trail_st S \<le> \<Down>unit_rel (RETURN (print_trail_st2 S))\<close>
  unfolding print_trail_st2_def print_trail_st_def
    print_trail_def
  apply (refine_vcg WHILET_rule[where 
       R = \<open>measure (\<lambda>i. Suc (length (fst (fst S))) - i)\<close> and
       I = \<open>\<lambda>i. i \<le> length (fst (fst S))\<close>])
  subgoal by auto
  subgoal by auto
  subgoal unfolding print_literal_of_trail_def by auto
  subgoal unfolding print_literal_of_trail_def by auto
  done

lemma print_trail_st_print_trail_st2_rel:
  \<open>(print_trail_st, RETURN o print_trail_st2) \<in> Id \<rightarrow>\<^sub>f (\<langle>unit_rel\<rangle>nres_rel)\<close>
  using print_trail_st_print_trail_st2 by (force intro!: frefI nres_relI)

end