theory IsaSAT_Stats
  imports IsaSAT_Literals IsaSAT_EMA IsaSAT_Rephase IsaSAT_Reluctant Tuple16
begin


section \<open>Statistics\<close>

text \<open>
We do some statistics on the run.

NB: the statistics are not proven correct (especially they might
overflow), there are just there to look for regressions, do some comparisons (e.g., to conclude that
we are propagating slower than the other solvers), or to test different option combinations.


Remark that the code here has grown organically when I needed to add information. It never felt 
important to reorganize it in a meaningful way... although getting some parts right is absolutely
critical for performance.

If I were to redo it, I would use (like in other places) a datatype and try to stick to setters to be 
certain of what is changed during statistics. For example, I tend to bundle update of the number of 
phases and increasing the length... but if I copy-paste it wrong then some other definitions might 
have unforseen side effects and given the number of statistics, it is pretty hard to realize.
\<close>

type_synonym limit = \<open>64 word \<times> 64 word\<close>

text \<open>The statistics have the following meaning:

  \<^enum> search information
  (propagations, conflicts, decision, restarts,
  reductions, fixed variables, GCs,
  units since last GC, fixed irredundant clss),

  \<^enum> binary simplification (binary unit, binary red removed),
  \<^enum> pure literals (purelit removed, purelit rounds),
  \<^enum> forward subsumption (forward rounds, forward strengthen, forward subsumed)
  \<^enum> other: max kept lbd, 
  \<^enum> ticks
  \<^enum> average lbds
  \<^enum> heuristics for scheduling


At first we used a tuple that became longer and longer. We even had statistics bug because we changed
the wrong element of the tuple. Therefore, we changed to a structure and kept some free spots.
\<close>

subsection \<open>Search Information\<close>

type_synonym search_stats = \<open>64 word \<times> 64 word \<times>64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times>64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word\<close>

definition Search_Stats_propagations :: \<open>search_stats \<Rightarrow> 64 word\<close> where
  \<open>Search_Stats_propagations = (\<lambda>(propa, confl, dec, res, reduction, uset, gcs, units, irred_cls, no_conflict_until, ticks_stable, ticks_focused). propa)\<close>

definition Search_Stats_incr_propagation :: \<open>search_stats \<Rightarrow> search_stats\<close> where
  \<open>Search_Stats_incr_propagation = (\<lambda>(propa, confl, dec, res, reduction, uset, gcs, units, irred_cls, no_conflict_until). (propa+1, confl, dec, res, reduction, uset, gcs, units, irred_cls, no_conflict_until))\<close>

definition Search_Stats_incr_propagation_by :: \<open>64 word \<Rightarrow> search_stats \<Rightarrow> search_stats\<close> where
  \<open>Search_Stats_incr_propagation_by = (\<lambda>p (propa, confl, dec, res, reduction, uset, gcs, units, irred_cls, no_conflict_until). (propa+p, confl, dec, res, reduction, uset, gcs, units, irred_cls, no_conflict_until))\<close>

definition Search_Stats_conflicts :: \<open>search_stats \<Rightarrow> 64 word\<close> where
  \<open>Search_Stats_conflicts = (\<lambda>(propa, confl, dec, res, reduction, uset, gcs, units, irred_cls, no_conflict_until). confl)\<close>

definition Search_Stats_incr_conflicts :: \<open>search_stats \<Rightarrow> search_stats\<close> where
  \<open>Search_Stats_incr_conflicts = (\<lambda>(propa, confl, dec, res, reduction, uset, gcs, units, irred_cls, no_conflict_until). (propa, confl+1, dec, res, reduction, uset, gcs, units, irred_cls, no_conflict_until))\<close>

definition Search_Stats_decisions :: \<open>search_stats \<Rightarrow> 64 word\<close> where
  \<open>Search_Stats_decisions = (\<lambda>(propa, confl, dec, res, reduction, uset, gcs, units, irred_cls, no_conflict_until). dec)\<close>

definition Search_Stats_incr_decisions :: \<open>search_stats \<Rightarrow> search_stats\<close> where
  \<open>Search_Stats_incr_decisions = (\<lambda>(propa, confl, dec, res, reduction, uset, gcs, units, irred_cls, no_conflict_until). (propa, confl, dec+1, res, reduction, uset, gcs, units, irred_cls, no_conflict_until))\<close>

definition Search_Stats_restarts :: \<open>search_stats \<Rightarrow> 64 word\<close> where
  \<open>Search_Stats_restarts = (\<lambda>(propa, confl, dec, res, reduction, uset, gcs, units, irred_cls, no_conflict_until). res)\<close>

definition Search_Stats_incr_restarts :: \<open>search_stats \<Rightarrow> search_stats\<close> where
  \<open>Search_Stats_incr_restarts = (\<lambda>(propa, confl, dec, res, reduction, uset, gcs, units, irred_cls, no_conflict_until). (propa, confl, dec, res+1, reduction, uset, gcs, units, irred_cls, no_conflict_until))\<close>

definition Search_Stats_reductions :: \<open>search_stats \<Rightarrow> 64 word\<close> where
  \<open>Search_Stats_reductions = (\<lambda>(propa, confl, dec, res, reduction, uset, gcs, units, irred_cls, no_conflict_until). reduction)\<close>

definition Search_Stats_incr_reductions :: \<open>search_stats \<Rightarrow> search_stats\<close> where
  \<open>Search_Stats_incr_reductions = (\<lambda>(propa, confl, dec, res, reduction, uset, gcs, units, irred_cls, no_conflict_until). (propa, confl, dec, res, reduction+1, uset, gcs, units, irred_cls, no_conflict_until))\<close>

definition Search_Stats_fixed :: \<open>search_stats \<Rightarrow> 64 word\<close> where
  \<open>Search_Stats_fixed = (\<lambda>(propa, confl, dec, res, reduction, uset, gcs, units, irred_cls, no_conflict_until). uset)\<close>

definition Search_Stats_incr_fixed :: \<open>search_stats \<Rightarrow> search_stats\<close> where
  \<open>Search_Stats_incr_fixed = (\<lambda>(propa, confl, dec, res, reduction, uset, gcs, units, irred_cls, no_conflict_until). (propa, confl, dec, res, reduction, uset+1, gcs, units, irred_cls, no_conflict_until))\<close>

definition Search_Stats_incr_fixed_by :: \<open>64 word \<Rightarrow> search_stats \<Rightarrow> search_stats\<close> where
  \<open>Search_Stats_incr_fixed_by = (\<lambda>p (propa, confl, dec, res, reduction, uset, gcs, units, irred_cls, no_conflict_until). (propa, confl, dec, res, reduction, uset+p, gcs, units, irred_cls, no_conflict_until))\<close>

definition Search_Stats_gcs :: \<open>search_stats \<Rightarrow> 64 word\<close> where
  \<open>Search_Stats_gcs = (\<lambda>(propa, confl, dec, res, reduction, uset, gcs, units, irred_cls, no_conflict_until). gcs)\<close>

definition Search_Stats_incr_gcs :: \<open>search_stats \<Rightarrow> search_stats\<close> where
  \<open>Search_Stats_incr_gcs = (\<lambda>(propa, confl, dec, res, reduction, uset, gcs, units, irred_cls, no_conflict_until). (propa, confl, dec, res, reduction, uset, gcs+1, units, irred_cls, no_conflict_until))\<close>

definition Search_Stats_reset_units_since_gc :: \<open>search_stats \<Rightarrow> search_stats\<close> where
  \<open>Search_Stats_reset_units_since_gc = (\<lambda>(propa, confl, dec, res, reduction, uset, gcs, units, irred_cls, no_conflict_until). (propa, confl, dec, res, reduction, uset, gcs, 0, irred_cls, no_conflict_until))\<close>

definition Search_Stats_units_since_gcs :: \<open>search_stats \<Rightarrow> 64 word\<close> where
  \<open>Search_Stats_units_since_gcs = (\<lambda>(propa, confl, dec, res, reduction, uset, units_since_gcs, units, irred_cls, no_conflict_until). units_since_gcs)\<close>

definition Search_Stats_incr_units_since_gc :: \<open>search_stats \<Rightarrow> search_stats\<close> where
  \<open>Search_Stats_incr_units_since_gc = (\<lambda>(propa, confl, dec, res, reduction, uset, gcs, units, irred_cls, no_conflict_until). (propa, confl, dec, res, reduction, uset, gcs, units+1, irred_cls, no_conflict_until))\<close>

definition Search_Stats_incr_units_since_gc_by :: \<open>64 word \<Rightarrow> search_stats \<Rightarrow> search_stats\<close> where
  \<open>Search_Stats_incr_units_since_gc_by = (\<lambda>p (propa, confl, dec, res, reduction, uset, gcs, units, irred_cls, no_conflict_until). (propa, confl, dec, res, reduction, uset, gcs, units+p, irred_cls, no_conflict_until))\<close>

definition Search_Stats_incr_irred :: \<open>search_stats \<Rightarrow> search_stats\<close> where
  \<open>Search_Stats_incr_irred = (\<lambda>(propa, confl, dec, res, reduction, uset, gcs, units, irred_cls, no_conflict_until). (propa, confl, dec, res, reduction, uset, gcs, units, irred_cls+1, no_conflict_until))\<close>

definition Search_Stats_decr_irred :: \<open>search_stats \<Rightarrow> search_stats\<close> where
  \<open>Search_Stats_decr_irred = (\<lambda>(propa, confl, dec, res, reduction, uset, gcs, units, irred_cls, no_conflict_until). (propa, confl, dec, res, reduction, uset, gcs, units, irred_cls-1, no_conflict_until))\<close>

definition Search_Stats_irred :: \<open>search_stats \<Rightarrow> 64 word\<close> where
  \<open>Search_Stats_irred = (\<lambda>(propa, confl, dec, res, reduction, uset, gcs, units, irred_cls, no_conflict_until). irred_cls)\<close>

definition Search_Stats_no_conflict_until :: \<open>search_stats \<Rightarrow> 64 word\<close> where
  \<open>Search_Stats_no_conflict_until = (\<lambda>(propa, confl, dec, res, reduction, uset, gcs, units, irred_cls, no_conflict_until, ticks). no_conflict_until)\<close>

definition Search_Stats_set_no_conflict_until :: \<open>64 word \<Rightarrow> search_stats \<Rightarrow> search_stats\<close> where
  \<open>Search_Stats_set_no_conflict_until = (\<lambda>p (propa, confl, dec, res, reduction, uset, gcs, units, irred_cls, no_conflict_until, ticks). (propa, confl, dec, res, reduction, uset, gcs, units, irred_cls, p, ticks))\<close>

definition Search_Stats_ticks_stable :: \<open>search_stats \<Rightarrow> 64 word\<close> where
  \<open>Search_Stats_ticks_stable = (\<lambda>(propa, confl, dec, res, reduction, uset, gcs, units, irred_cls, no_conflict_until, ticks, ticks_focused). ticks)\<close>

definition Search_Stats_set_ticks_stable :: \<open>64 word \<Rightarrow> search_stats \<Rightarrow> search_stats\<close> where
  \<open>Search_Stats_set_ticks_stable = (\<lambda>ticks (propa, confl, dec, res, reduction, uset, gcs, units, irred_cls, no_conflict_until, _, ticks_focused). (propa, confl, dec, res, reduction, uset, gcs, units, irred_cls, no_conflict_until, ticks, ticks_focused))\<close>

definition Search_Stats_incr_ticks_stable :: \<open>64 word \<Rightarrow> search_stats \<Rightarrow> search_stats\<close> where
  \<open>Search_Stats_incr_ticks_stable = (\<lambda>t (propa, confl, dec, res, reduction, uset, gcs, units, irred_cls, no_conflict_until, ticks, ticks_focused). (propa, confl, dec, res, reduction, uset, gcs, units, irred_cls, no_conflict_until, ticks+t, ticks_focused))\<close>
  
definition Search_Stats_ticks_focused :: \<open>search_stats \<Rightarrow> 64 word\<close> where
  \<open>Search_Stats_ticks_focused = (\<lambda>(propa, confl, dec, res, reduction, uset, gcs, units, irred_cls, no_conflict_until, _, ticks_focused). ticks_focused)\<close>

definition Search_Stats_set_ticks_focused :: \<open>64 word \<Rightarrow> search_stats \<Rightarrow> search_stats\<close> where
  \<open>Search_Stats_set_ticks_focused = (\<lambda>ticks_focused (propa, confl, dec, res, reduction, uset, gcs, units, irred_cls, no_conflict_until, ticks, _). (propa, confl, dec, res, reduction, uset, gcs, units, irred_cls, no_conflict_until, ticks, ticks_focused))\<close>

definition Search_Stats_incr_ticks_focused :: \<open>64 word \<Rightarrow> search_stats \<Rightarrow> search_stats\<close> where
  \<open>Search_Stats_incr_ticks_focused = (\<lambda>t (propa, confl, dec, res, reduction, uset, gcs, units, irred_cls, no_conflict_until, ticks, ticks_focused). (propa, confl, dec, res, reduction, uset, gcs, units, irred_cls, no_conflict_until, ticks, ticks_focused+t))\<close>


subsection \<open>Inprocessing Information\<close>

type_synonym inprocessing_binary_stats = \<open>64 word \<times> 64 word \<times> 64 word\<close>

definition Binary_Stats_incr_rounds :: \<open>inprocessing_binary_stats \<Rightarrow> inprocessing_binary_stats\<close> where
  \<open>Binary_Stats_incr_rounds = (\<lambda>(rounds, units, removed). (rounds + 1, units, removed))\<close>

definition Binary_Stats_incr_units :: \<open>inprocessing_binary_stats \<Rightarrow> inprocessing_binary_stats\<close> where
  \<open>Binary_Stats_incr_units = (\<lambda>(rounds, units, removed). (rounds, units+1, removed))\<close>

definition Binary_Stats_incr_removed :: \<open>inprocessing_binary_stats \<Rightarrow> inprocessing_binary_stats\<close> where
  \<open>Binary_Stats_incr_removed = (\<lambda>(rounds, units, removed). (rounds, units, removed+1))\<close>



text \<open>\<^term>\<open>ticks\<close> is currently unused: it is supposed to be used as to limit the number of clauses to try.\<close>
type_synonym inprocessing_subsumption_stats = \<open>64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word\<close>

definition Subsumption_Stats_rounds :: \<open>inprocessing_subsumption_stats \<Rightarrow> 64 word\<close> where
  \<open>Subsumption_Stats_rounds = (\<lambda>(rounds, strengthened, subsumed, _). rounds)\<close>

definition Subsumption_Stats_subsumed :: \<open>inprocessing_subsumption_stats \<Rightarrow> 64 word\<close> where
  \<open>Subsumption_Stats_subsumed = (\<lambda>(rounds, strengthened, subsumed, _). subsumed)\<close>

definition Subsumption_Stats_tried :: \<open>inprocessing_subsumption_stats \<Rightarrow> 64 word\<close> where
  \<open>Subsumption_Stats_tried = (\<lambda>(rounds, strengthened, subsumed, _, tried, budget). tried)\<close>

definition Subsumption_Stats_strengthened:: \<open>inprocessing_subsumption_stats \<Rightarrow> 64 word\<close> where
  \<open>Subsumption_Stats_strengthened = (\<lambda>(rounds, strengethened, subsumed, _). strengethened)\<close>

definition Subsumption_Stats_incr_rounds :: \<open>inprocessing_subsumption_stats \<Rightarrow> inprocessing_subsumption_stats\<close> where
  \<open>Subsumption_Stats_incr_rounds = (\<lambda>(rounds, units, removed, subcheck, tried). (rounds + 1, units, removed, subcheck, tried))\<close>

definition Subsumption_Stats_incr_strengthening :: \<open>inprocessing_subsumption_stats \<Rightarrow> inprocessing_subsumption_stats\<close> where
  \<open>Subsumption_Stats_incr_strengthening = (\<lambda>(rounds, units, removed). (rounds, units+1, removed))\<close>

definition Subsumption_Stats_incr_subsumed :: \<open>inprocessing_subsumption_stats \<Rightarrow> inprocessing_subsumption_stats\<close> where
  \<open>Subsumption_Stats_incr_subsumed = (\<lambda>(rounds, units, removed, subchecks). (rounds, units, removed+1, subchecks))\<close>

definition Subsumption_Stats_incr_tried :: \<open>inprocessing_subsumption_stats \<Rightarrow> inprocessing_subsumption_stats\<close> where
  \<open>Subsumption_Stats_incr_tried = (\<lambda>(rounds, units, removed, subchecks, tried, budget). (rounds, units, removed, subchecks, tried+1, budget))\<close>

definition Subsumption_Stats_incr_subchecks_limit :: \<open>64 word \<Rightarrow> inprocessing_subsumption_stats \<Rightarrow> inprocessing_subsumption_stats\<close> where
  \<open>Subsumption_Stats_incr_subchecks_limit = (\<lambda>subs (rounds, units, removed, subchecks, tried). (rounds, units, removed, subchecks + subs, tried))\<close>

definition Subsumption_Stats_limit :: \<open>inprocessing_subsumption_stats \<Rightarrow> 64 word\<close> where
  \<open>Subsumption_Stats_limit = (\<lambda>(rounds, units, removed, subchecks, tried). subchecks)\<close>

definition Subsumption_Stats_ticks_tried :: \<open>inprocessing_subsumption_stats \<Rightarrow> 64 word\<close> where
  \<open>Subsumption_Stats_ticks_tried = (\<lambda>(rounds, units, removed, subchecks, tried, budget). tried)\<close>

definition Subsumption_Stats_incr_ticks_tried :: \<open>64 word \<Rightarrow> inprocessing_subsumption_stats \<Rightarrow> inprocessing_subsumption_stats\<close> where
  \<open>Subsumption_Stats_incr_ticks_tried = (\<lambda>t (rounds, units, removed, subchecks, tried, budget). (rounds, units, removed, subchecks, tried+t, budget))\<close>
  
definition Subsumption_Stats_set_budget :: \<open>64 word \<Rightarrow> inprocessing_subsumption_stats \<Rightarrow> inprocessing_subsumption_stats\<close> where
  \<open>Subsumption_Stats_set_budget = (\<lambda>budget (rounds, units, removed, subchecks, tried, _). (rounds, units, removed, subchecks, tried, budget))\<close>
  
definition Subsumption_Stats_budget :: \<open>inprocessing_subsumption_stats \<Rightarrow> 64 word\<close> where
  \<open>Subsumption_Stats_budget = (\<lambda>(rounds, units, removed, subchecks, tried, budget). budget)\<close>
  

definition Subsumption_Stats_incr_subchecks :: \<open>64 word \<Rightarrow> inprocessing_subsumption_stats \<Rightarrow> inprocessing_subsumption_stats\<close> where
  \<open>Subsumption_Stats_incr_subchecks = (\<lambda>w (rounds, units, removed, subchecks, tried, budget). (rounds, units, removed, subchecks+w, tried, budget))\<close>
  
definition Subsumption_Stats_subchecks :: \<open>inprocessing_subsumption_stats \<Rightarrow> 64 word\<close> where
  \<open>Subsumption_Stats_subchecks = (\<lambda>(rounds, units, removed, subchecks, tried, budget). subchecks)\<close>
  

  
type_synonym inprocessing_pure_lits_stats = \<open>64 word \<times> 64 word\<close>

definition Pure_lits_Stats_incr_rounds :: \<open>inprocessing_pure_lits_stats \<Rightarrow> inprocessing_pure_lits_stats\<close> where
  \<open>Pure_lits_Stats_incr_rounds = (\<lambda>(rounds, removed). (rounds + 1, removed))\<close>

definition Pure_lits_Stats_incr_removed :: \<open>inprocessing_pure_lits_stats \<Rightarrow> inprocessing_pure_lits_stats\<close> where
  \<open>Pure_lits_Stats_incr_removed = (\<lambda>(rounds, removed). (rounds, removed+1))\<close>


subsubsection \<open>Biggest Seen Clause\<close>

type_synonym lbd_size_limit_stats = \<open>nat \<times> nat\<close>

definition LSize_Stats_lbd where
  \<open>LSize_Stats_lbd = (\<lambda>(lbd, size). lbd)\<close>

definition LSize_Stats_size where
  \<open>LSize_Stats_size = (\<lambda>(lbd, size). size)\<close>

definition LSize_Stats where
  \<open>LSize_Stats lbd size' = (lbd, size')\<close>

  
subsubsection \<open>Rephasing\<close>
  
type_synonym rephase_stats = \<open>64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word\<close>

definition Rephase_Stats_total :: \<open>rephase_stats \<Rightarrow> _\<close> where
  \<open>Rephase_Stats_total = (\<lambda>(rephased, original, best, invert, flipped, random). rephased)\<close>

definition Rephase_Stats_incr_total :: \<open>rephase_stats \<Rightarrow> rephase_stats\<close> where
  \<open>Rephase_Stats_incr_total = (\<lambda>(rephased, original, best, invert, flipped, random). (rephased+1, original, best, invert, flipped, random))\<close>


subsubsection \<open>Rate\<close>

text \<open>Rate = number of decision between conflicts. If the number is too high, then we should not do
 recursive bumping, especially since our sorting is less efficient than the one in kissat.\<close>

type_synonym isasat_rate = \<open>(ema \<times> ema \<times> 64 word)\<close>

definition Rate_get_rate :: \<open>bool \<Rightarrow> isasat_rate \<Rightarrow> 64 word\<close> where
  \<open>Rate_get_rate is_stable = (\<lambda>(rate_focused, rate_stable, last_decision). if is_stable then ema_extract_value rate_stable else ema_extract_value rate_focused)\<close>

definition Rate_get_rate_last_decision :: \<open>isasat_rate \<Rightarrow> 64 word\<close> where
  \<open>Rate_get_rate_last_decision = (\<lambda>(rate_focused, rate_stable, last_decision). last_decision)\<close>

definition Rate_set_rate_last_decision :: \<open>64 word \<Rightarrow> isasat_rate \<Rightarrow> isasat_rate\<close> where
  \<open>Rate_set_rate_last_decision last_decision  = (\<lambda>(rate_focused, rate_stable, _). (rate_focused, rate_stable, last_decision))\<close>

definition Rate_update_rate :: \<open>bool \<Rightarrow> 64 word \<Rightarrow> isasat_rate \<Rightarrow> isasat_rate\<close> where
  \<open>Rate_update_rate is_stable r = (\<lambda>(rate_focused, rate_stable, last_decision).
  (if is_stable then rate_focused else ema_update_word (r - last_decision) rate_focused,
   if is_stable then ema_update_word  (r - last_decision) rate_stable else rate_stable, r))\<close>


subsection \<open>All Together\<close>

type_synonym isasat_stats = \<open>
  (search_stats, inprocessing_binary_stats, inprocessing_subsumption_stats, ema,
  inprocessing_pure_lits_stats, lbd_size_limit_stats,
  rephase_stats,
  isasat_rate,

  64 word, 64 word,64 word, 64 word,
  64 word, 64 word, 32 word, 64 word) tuple16\<close>
text \<open>The unused part starts after the line break, but Isabelle does not allow for comments there.\<close>


abbreviation Stats :: \<open>_ \<Rightarrow> _ \<Rightarrow>_ \<Rightarrow> _ \<Rightarrow>_ \<Rightarrow> _ \<Rightarrow>_ \<Rightarrow> _ \<Rightarrow>_ \<Rightarrow> _ \<Rightarrow>_ \<Rightarrow> _ \<Rightarrow>_ \<Rightarrow> _ \<Rightarrow>_ \<Rightarrow> _ \<Rightarrow> isasat_stats\<close> where
  \<open>Stats \<equiv> Tuple16\<close>

definition get_search_stats :: \<open>isasat_stats \<Rightarrow> search_stats\<close> where
  \<open>get_search_stats \<equiv> Tuple16.Tuple16_get_a\<close>

definition get_binary_stats :: \<open>isasat_stats \<Rightarrow> inprocessing_binary_stats\<close> where
  \<open>get_binary_stats \<equiv> Tuple16.Tuple16_get_b\<close>

definition get_subsumption_stats :: \<open>isasat_stats \<Rightarrow> inprocessing_subsumption_stats\<close> where
  \<open>get_subsumption_stats \<equiv> Tuple16.Tuple16_get_c\<close>

definition get_avg_lbd_stats :: \<open>isasat_stats \<Rightarrow> ema\<close> where
  \<open>get_avg_lbd_stats \<equiv> Tuple16.Tuple16_get_d\<close>

definition get_pure_lits_stats :: \<open>isasat_stats \<Rightarrow> inprocessing_pure_lits_stats\<close> where
  \<open>get_pure_lits_stats \<equiv> Tuple16.Tuple16_get_e\<close>

definition get_lsize_limit_stats :: \<open>isasat_stats \<Rightarrow> lbd_size_limit_stats\<close> where
  \<open>get_lsize_limit_stats \<equiv> Tuple16.Tuple16_get_f\<close>

definition get_rephase_stats :: \<open>isasat_stats \<Rightarrow> rephase_stats\<close> where
  \<open>get_rephase_stats \<equiv> Tuple16.Tuple16_get_g\<close>

definition get_rate_stats :: \<open>isasat_stats \<Rightarrow> isasat_rate\<close> where
  \<open>get_rate_stats \<equiv> Tuple16.Tuple16_get_h\<close>

definition set_propagation_stats :: \<open>search_stats \<Rightarrow> isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>set_propagation_stats \<equiv> Tuple16.set_a\<close>

definition set_binary_stats :: \<open>inprocessing_binary_stats \<Rightarrow> isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>set_binary_stats \<equiv> Tuple16.set_b\<close>

definition set_subsumption_stats :: \<open>inprocessing_subsumption_stats \<Rightarrow> isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>set_subsumption_stats \<equiv> Tuple16.set_c\<close>

definition set_avg_lbd_stats :: \<open>ema \<Rightarrow> isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>set_avg_lbd_stats \<equiv> Tuple16.set_d\<close>

definition set_pure_lits_stats :: \<open>inprocessing_pure_lits_stats \<Rightarrow> isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>set_pure_lits_stats \<equiv> Tuple16.set_e\<close>

definition set_lsize_limit_stats :: \<open>lbd_size_limit_stats \<Rightarrow> isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>set_lsize_limit_stats \<equiv> Tuple16.set_f\<close>

definition set_rephase_stats :: \<open>rephase_stats \<Rightarrow> isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>set_rephase_stats \<equiv> Tuple16.set_g\<close>

definition set_rate_stats :: \<open>isasat_rate \<Rightarrow> isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>set_rate_stats \<equiv> Tuple16.set_h\<close>
  
definition incr_propagation :: \<open>isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>incr_propagation S = (set_propagation_stats (Search_Stats_incr_propagation (get_search_stats S)) S)\<close>

definition incr_propagation_by :: \<open>64 word \<Rightarrow> isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>incr_propagation_by p S = (set_propagation_stats (Search_Stats_incr_propagation_by p (get_search_stats S)) S)\<close>

definition incr_search_ticks_stable_by :: \<open>64 word \<Rightarrow> isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>incr_search_ticks_stable_by p S = (set_propagation_stats (Search_Stats_incr_ticks_stable p (get_search_stats S)) S)\<close>
  
definition incr_search_ticks_focused_by :: \<open>64 word \<Rightarrow> isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>incr_search_ticks_focused_by p S = (set_propagation_stats (Search_Stats_incr_ticks_focused p (get_search_stats S)) S)\<close>

definition incr_conflict :: \<open>isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>incr_conflict S = (set_propagation_stats (Search_Stats_incr_conflicts (get_search_stats S)) S)\<close>

definition incr_decision :: \<open>isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>incr_decision S = (set_propagation_stats (Search_Stats_incr_decisions (get_search_stats S)) S)\<close>

definition get_decisions :: \<open>isasat_stats \<Rightarrow> 64 word\<close> where
  \<open>get_decisions S = (Search_Stats_decisions (get_search_stats S))\<close>
  
definition incr_restart :: \<open>isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>incr_restart S = (set_propagation_stats (Search_Stats_incr_restarts (get_search_stats S)) S)\<close>

definition incr_reduction :: \<open>isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>incr_reduction S = (set_propagation_stats (Search_Stats_incr_reductions (get_search_stats S)) S)\<close>

definition incr_uset :: \<open>isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>incr_uset S = (set_propagation_stats (Search_Stats_incr_fixed (get_search_stats S)) S)\<close>

definition incr_uset_by :: \<open>64 word \<Rightarrow> isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>incr_uset_by p S = (set_propagation_stats (Search_Stats_incr_fixed_by p (get_search_stats S)) S)\<close>

definition incr_GC :: \<open>isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>incr_GC S = (set_propagation_stats (Search_Stats_incr_gcs (get_search_stats S)) S)\<close>

definition units_since_last_GC :: \<open>isasat_stats \<Rightarrow> 64 word\<close> where
  \<open>units_since_last_GC = Search_Stats_units_since_gcs o get_search_stats\<close>

definition units_since_beginning :: \<open>isasat_stats \<Rightarrow> 64 word\<close> where
  \<open>units_since_beginning = Search_Stats_fixed o get_search_stats\<close>

definition incr_units_since_last_GC :: \<open>isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>incr_units_since_last_GC S = (set_propagation_stats (Search_Stats_incr_units_since_gc (get_search_stats S)) S)\<close>

definition incr_units_since_last_GC_by :: \<open>64 word \<Rightarrow> isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>incr_units_since_last_GC_by p S = (set_propagation_stats (Search_Stats_incr_units_since_gc_by p (get_search_stats S)) S)\<close>

definition stats_conflicts :: \<open>isasat_stats \<Rightarrow> 64 word\<close> where
  \<open>stats_conflicts = Search_Stats_conflicts o get_search_stats\<close>

definition incr_binary_unit_derived :: \<open>isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>incr_binary_unit_derived S = set_binary_stats (Binary_Stats_incr_units (get_binary_stats S)) S\<close>

definition incr_binary_red_removed :: \<open>isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>incr_binary_red_removed S = set_binary_stats (Binary_Stats_incr_removed (get_binary_stats S)) S\<close>

definition incr_forward_strengethening :: \<open>isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>incr_forward_strengethening S = set_subsumption_stats (Subsumption_Stats_incr_strengthening (get_subsumption_stats S)) S\<close>

definition incr_forward_subsumed :: \<open>isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>incr_forward_subsumed S = set_subsumption_stats (Subsumption_Stats_incr_subsumed (get_subsumption_stats S)) S\<close>

definition incr_forward_tried :: \<open>isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>incr_forward_tried S = set_subsumption_stats (Subsumption_Stats_incr_tried (get_subsumption_stats S)) S\<close>

definition incr_forward_rounds :: \<open>isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>incr_forward_rounds S = set_subsumption_stats (Subsumption_Stats_incr_rounds (get_subsumption_stats S)) S\<close>

definition stats_forward_rounds :: \<open>isasat_stats \<Rightarrow> _\<close> where
  \<open>stats_forward_rounds = Subsumption_Stats_rounds o get_subsumption_stats\<close>

definition stats_forward_subsumed :: \<open>isasat_stats \<Rightarrow> _\<close> where
  \<open>stats_forward_subsumed = Subsumption_Stats_subsumed o get_subsumption_stats\<close>

definition stats_forward_strengthened :: \<open>isasat_stats \<Rightarrow> _\<close> where
  \<open>stats_forward_strengthened = Subsumption_Stats_strengthened o get_subsumption_stats\<close>
  
definition set_forward_budget :: \<open>64 word \<Rightarrow> isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>set_forward_budget w S = set_subsumption_stats (Subsumption_Stats_set_budget w (get_subsumption_stats S)) S\<close>
  
definition forward_budget :: \<open>isasat_stats \<Rightarrow> 64 word\<close> where
  \<open>forward_budget S = Subsumption_Stats_budget (get_subsumption_stats S)\<close>

definition incr_forward_subchecks_by :: \<open>64 word \<Rightarrow>  isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>incr_forward_subchecks_by w S = set_subsumption_stats (Subsumption_Stats_incr_subchecks w (get_subsumption_stats S)) S\<close>
  
definition forward_subchecks :: \<open>isasat_stats \<Rightarrow> 64 word\<close> where
  \<open>forward_subchecks S = Subsumption_Stats_subchecks (get_subsumption_stats S)\<close>

definition stats_forward_tried :: \<open>isasat_stats \<Rightarrow> _\<close> where
  \<open>stats_forward_tried = Subsumption_Stats_tried o get_subsumption_stats\<close>

definition get_restart_count where
  \<open>get_restart_count S = Search_Stats_restarts (get_search_stats S)\<close>

definition get_reduction_count where
  \<open>get_reduction_count S = Search_Stats_reductions (get_search_stats S)\<close>

definition incr_rephase_total :: \<open>isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>incr_rephase_total S = (set_rephase_stats (Rephase_Stats_incr_total (get_rephase_stats S)) S)\<close>

definition stats_rephase :: \<open>isasat_stats \<Rightarrow> 64 word\<close> where
  \<open>stats_rephase = Rephase_Stats_total o get_rephase_stats\<close>

definition print_open_colour :: \<open>64 word \<Rightarrow> unit\<close> where
  \<open>print_open_colour _ = ()\<close>

definition print_close_colour :: \<open>64 word \<Rightarrow> unit\<close> where
  \<open>print_close_colour _ = ()\<close>

definition stats_propagations :: \<open>isasat_stats \<Rightarrow> 64 word\<close> where
  \<open>stats_propagations = Search_Stats_propagations o get_search_stats\<close>

definition stats_restarts :: \<open>isasat_stats \<Rightarrow> 64 word\<close> where
  \<open>stats_restarts = Search_Stats_restarts o get_search_stats\<close>

definition stats_reductions :: \<open>isasat_stats \<Rightarrow> 64 word\<close> where
  \<open>stats_reductions = Search_Stats_reductions o get_search_stats\<close>

definition stats_fixed :: \<open>isasat_stats \<Rightarrow> 64 word\<close> where
  \<open>stats_fixed = Search_Stats_fixed o get_search_stats\<close>

definition stats_gcs :: \<open>isasat_stats \<Rightarrow> 64 word\<close> where
  \<open>stats_gcs = Search_Stats_gcs o get_search_stats\<close>

definition stats_avg_lbd :: \<open>isasat_stats \<Rightarrow> ema\<close> where
  \<open>stats_avg_lbd = get_avg_lbd_stats\<close>


definition stats_decisions :: \<open>isasat_stats \<Rightarrow> 64 word\<close> where
  \<open>stats_decisions = Search_Stats_decisions o get_search_stats\<close>

definition stats_irred :: \<open>isasat_stats \<Rightarrow> 64 word\<close> where
  \<open>stats_irred = Search_Stats_irred o get_search_stats\<close>

definition Binary_Stats_rounds :: \<open>inprocessing_binary_stats \<Rightarrow> 64 word\<close> where
  \<open>Binary_Stats_rounds = (\<lambda>(rounds, units, removed). rounds)\<close>

definition stats_binary_rounds :: \<open>isasat_stats \<Rightarrow> 64 word\<close> where
  \<open>stats_binary_rounds = Binary_Stats_rounds o get_binary_stats\<close>

definition Binary_Stats_units :: \<open>inprocessing_binary_stats \<Rightarrow> 64 word\<close> where
  \<open>Binary_Stats_units = (\<lambda>(units, units, removed). units)\<close>

definition stats_binary_units :: \<open>isasat_stats \<Rightarrow> 64 word\<close> where
  \<open>stats_binary_units = Binary_Stats_units o get_binary_stats\<close>

definition Binary_Stats_removed :: \<open>inprocessing_binary_stats \<Rightarrow> 64 word\<close> where
  \<open>Binary_Stats_removed = (\<lambda>(removed, units, removed). removed)\<close>

definition stats_binary_removed :: \<open>isasat_stats \<Rightarrow> 64 word\<close> where
  \<open>stats_binary_removed = Binary_Stats_removed o get_binary_stats\<close>

definition Pure_Lits_Stats_removed :: \<open>inprocessing_pure_lits_stats \<Rightarrow> 64 word\<close> where
  \<open>Pure_Lits_Stats_removed = (\<lambda>(removed, removed). removed)\<close>

definition stats_pure_lits_removed :: \<open>isasat_stats \<Rightarrow> 64 word\<close> where
  \<open>stats_pure_lits_removed = Pure_Lits_Stats_removed o get_pure_lits_stats\<close>
  
definition stats_ticks_stable :: \<open>isasat_stats \<Rightarrow> 64 word\<close> where
  \<open>stats_ticks_stable = Search_Stats_ticks_stable o get_search_stats\<close>
  
definition stats_ticks_focused :: \<open>isasat_stats \<Rightarrow> 64 word\<close> where
  \<open>stats_ticks_focused = Search_Stats_ticks_focused o get_search_stats\<close>

definition Pure_Lits_Stats_rounds :: \<open>inprocessing_pure_lits_stats \<Rightarrow> 64 word\<close> where
  \<open>Pure_Lits_Stats_rounds = (\<lambda>(rounds, rounds). rounds)\<close> 

definition stats_pure_lits_rounds :: \<open>isasat_stats \<Rightarrow> 64 word\<close> where
  \<open>stats_pure_lits_rounds = Pure_Lits_Stats_rounds o get_pure_lits_stats\<close>


definition add_lbd :: \<open>32 word \<Rightarrow> isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>add_lbd lbd S = set_avg_lbd_stats (ema_update (unat lbd) (get_avg_lbd_stats S)) S\<close>

definition incr_purelit_elim :: \<open>isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>incr_purelit_elim S = set_pure_lits_stats (Pure_lits_Stats_incr_removed (get_pure_lits_stats S)) S\<close>

definition incr_purelit_rounds :: \<open>isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>incr_purelit_rounds S = set_pure_lits_stats (Pure_lits_Stats_incr_rounds (get_pure_lits_stats S)) S\<close>


definition reset_units_since_last_GC :: \<open>isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>reset_units_since_last_GC S = (set_propagation_stats (Search_Stats_reset_units_since_gc (get_search_stats S)) S)\<close>

definition incr_irred_clss :: \<open>isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>incr_irred_clss S = set_propagation_stats (Search_Stats_incr_irred (get_search_stats S)) S\<close>

definition set_no_conflict_until :: \<open>64 word \<Rightarrow> isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>set_no_conflict_until p S = set_propagation_stats (Search_Stats_set_no_conflict_until p (get_search_stats S)) S\<close>

definition no_conflict_until :: \<open>isasat_stats \<Rightarrow> 64 word\<close> where
  \<open>no_conflict_until S = Search_Stats_no_conflict_until (get_search_stats S)\<close>

definition decr_irred_clss :: \<open>isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>decr_irred_clss S = set_propagation_stats (Search_Stats_decr_irred (get_search_stats S)) S\<close>

definition irredundant_clss :: \<open>isasat_stats \<Rightarrow> 64 word\<close> where
  \<open>irredundant_clss = Search_Stats_irred o get_search_stats\<close>

abbreviation (input) get_conflict_count :: \<open>isasat_stats \<Rightarrow> 64 word\<close> where
  \<open>get_conflict_count \<equiv> stats_conflicts\<close>

definition stats_lbd_limit :: \<open>isasat_stats \<Rightarrow> nat\<close> where
  \<open>stats_lbd_limit = LSize_Stats_lbd o get_lsize_limit_stats\<close>

definition stats_size_limit :: \<open>isasat_stats \<Rightarrow> nat\<close> where
  \<open>stats_size_limit = LSize_Stats_size o get_lsize_limit_stats\<close>

definition set_stats_size_limit :: \<open>nat \<Rightarrow> nat \<Rightarrow> isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>set_stats_size_limit lbd size' = set_lsize_limit_stats (lbd, size')\<close>

context begin
qualified definition BUMPREASONRATE where
  \<open>BUMPREASONRATE = 10\<close> (*Kissat has 10, but our sorting is worse, so maybe decrease*)

qualified definition current_rate :: \<open>bool \<Rightarrow> isasat_stats \<Rightarrow> 64 word\<close> where
  \<open>current_rate is_stable stats = (Rate_get_rate is_stable (get_rate_stats stats))\<close>
  
qualified definition rate_should_bump_reason :: \<open>bool \<Rightarrow> isasat_stats \<Rightarrow> bool\<close> where
  \<open>rate_should_bump_reason is_stable stats = (Rate_get_rate is_stable (get_rate_stats stats) \<ge> BUMPREASONRATE)\<close>

qualified definition update_rate :: \<open>bool \<Rightarrow> 64 word \<Rightarrow> isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>update_rate is_stable dec stats = (set_rate_stats (Rate_update_rate is_stable dec (get_rate_stats stats)) stats)\<close>

qualified definition rate_set_last_decision :: \<open>64 word \<Rightarrow> isasat_stats \<Rightarrow> isasat_stats\<close> where
  \<open>rate_set_last_decision dec stats = (set_rate_stats (Rate_set_rate_last_decision dec (get_rate_stats stats)) stats)\<close>


end


section \<open>Information related to restarts\<close>

definition FOCUSED_MODE :: \<open>64 word\<close> where
  \<open>FOCUSED_MODE = 0\<close>

definition STABLE_MODE :: \<open>64 word\<close> where
  \<open>STABLE_MODE = 1\<close>

definition DEFAULT_INIT_PHASE :: \<open>64 word\<close> where
  \<open>DEFAULT_INIT_PHASE = 10000\<close>

type_synonym restart_info = \<open>64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word\<close>
text \<open>
This datastructure contains:
 \<^item> \<^term>\<open>ccount\<close>: the "conflict count" since the beginning of the current mode. Will soon contain that or the ticks (in cadical: \<^text>\<open>last.stabilize.ticks\<close>).
 \<^item> \<^term>\<open>ema_lvl\<close>: average restart level (purely for statistics)
 \<^item> \<^term>\<open>end_of_phase\<close>: scheduled end of phase (to be interpreted as ticks or conflicts)
 \<^item> \<^term>\<open>lenth_phase\<close>: length of the current phase (useful to schedule next one). Will soon be the number of mode changes.
 \<^item> \<^term>\<open>init_phase_ticks\<close>: length in ticks of the very first phase
\<close>

definition incr_conflict_count_since_last_restart :: \<open>restart_info \<Rightarrow> restart_info\<close> where
  \<open>incr_conflict_count_since_last_restart = (\<lambda>(ccount, ema_lvl, restart_phase, end_of_phase, stabmode, init_phase_ticks).
    (ccount + 1, ema_lvl, restart_phase, end_of_phase, stabmode, init_phase_ticks))\<close>

definition restart_info_update_lvl_avg :: \<open>32 word \<Rightarrow> restart_info \<Rightarrow> restart_info\<close> where
  \<open>restart_info_update_lvl_avg = (\<lambda>lvl (ccount, ema_lvl). (ccount, ema_lvl))\<close>

definition restart_info_init :: \<open>restart_info\<close> where
  \<open>restart_info_init = (0, 0, FOCUSED_MODE, DEFAULT_INIT_PHASE, 0, 0)\<close>

definition restart_info_restart_done :: \<open>restart_info \<Rightarrow> restart_info\<close> where
  \<open>restart_info_restart_done = (\<lambda>(ccount, lvl_avg). (0, lvl_avg))\<close>

definition empty_stats :: \<open>isasat_stats\<close> where
  \<open>empty_stats = Tuple16( (0,0,0,0,0,0,0,0,0,0,0,0)::search_stats)
  ((0,0,0)::inprocessing_binary_stats) ((0,0,0,0,0,0)::inprocessing_subsumption_stats)
  (ema_fast_init::ema) ((0,0)::inprocessing_pure_lits_stats) (0,0) ((0,0,0,0,0,0))
  ((ema_slow_init, ema_slow_init, 0)::isasat_rate) 0 0 0 0 0 0 0 0\<close>

definition empty_stats_clss :: \<open>64 word \<Rightarrow> isasat_stats\<close> where
  \<open>empty_stats_clss n = Tuple16( (0,0,0,0,0,0,0,0,n,0,0,0)::search_stats)
  ((0,0,0)::inprocessing_binary_stats) ((0,0,0,0,0,0)::inprocessing_subsumption_stats)
  (ema_fast_init::ema) ((0,0)::inprocessing_pure_lits_stats) (0,0) (0,0,0,0,0,0)
  ((ema_slow_init, ema_slow_init, 0)::isasat_rate) 0 0 0 0 0 0 0 0\<close>


section \<open>Scheduling Information\<close>

type_synonym schedule_info = \<open>64 word \<times> 64 word \<times> 64 word\<close>

definition schedule_next_pure_lits_info :: \<open>schedule_info \<Rightarrow> schedule_info\<close> where
  \<open>schedule_next_pure_lits_info = (\<lambda>(inprocess, reduce, forwardsubsumption). (inprocess * 3 >> 1, reduce, forwardsubsumption))\<close>

definition next_pure_lits_schedule_info :: \<open>schedule_info \<Rightarrow> 64 word\<close> where
  \<open>next_pure_lits_schedule_info = (\<lambda>(inprocess, reduce, forwardsubsumption). inprocess)\<close>

definition schedule_next_reduce_info :: \<open>64 word \<Rightarrow> schedule_info \<Rightarrow> schedule_info\<close> where
  \<open>schedule_next_reduce_info delta = (\<lambda>(inprocess, reduce, forwardsubsumption). (inprocess, reduce + delta, forwardsubsumption))\<close>

definition next_reduce_schedule_info :: \<open>schedule_info \<Rightarrow> 64 word\<close> where
  \<open>next_reduce_schedule_info = (\<lambda>(inprocess, reduce, forwardsubsumption). reduce)\<close>

definition next_subsume_schedule_info :: \<open>schedule_info \<Rightarrow> 64 word\<close> where
  \<open>next_subsume_schedule_info = (\<lambda>(inprocess, reduce, forwardsubsumption). forwardsubsumption)\<close>

definition schedule_next_subsume_info :: \<open>64 word \<Rightarrow> schedule_info \<Rightarrow> schedule_info\<close> where
  \<open>schedule_next_subsume_info delta = (\<lambda>(inprocess, reduce, forwardsubsumption). (inprocess, reduce, forwardsubsumption + delta))\<close>


datatype 'a code_hider = Constructor (get_content: 'a)

definition code_hider_rel where code_hider_rel_def_internal:
  \<open>code_hider_rel R = {(a,b). (a, get_content b) \<in> R}\<close>

lemma code_hider_rel_def[refine_rel_defs]:
  "\<langle>R\<rangle>code_hider_rel \<equiv> {(a,b). (a, get_content b) \<in> R}"
  by (simp add: code_hider_rel_def_internal relAPP_def)

type_synonym restart_heuristics = \<open>ema \<times> ema \<times> restart_info \<times> 64 word \<times> phase_save_heur \<times> reluctant \<times> bool \<times> phase_saver \<times> schedule_info \<times> ema \<times> ema\<close>

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
  \<open>schedule_info_of_stats (fast_ema, slow_ema, restart_info, wasted, \<phi>, _, _, _, schedule, _, _) = schedule\<close>

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

definition swap_emas_stats :: \<open>restart_heuristics \<Rightarrow> restart_heuristics\<close> where
  \<open>swap_emas_stats = (\<lambda>(fast_ema, slow_ema, restart_info, wasted, \<phi>, a, b, lit_st, schedule, other_fema, other_sema).
  (other_fema, other_sema, restart_info, wasted, \<phi>, a, b, lit_st, schedule, fast_ema, slow_ema))\<close>

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
  \<open>heuristic_rel_stats \<A> heur \<Longrightarrow> heuristic_rel_stats \<A> (swap_emas_stats heur)\<close>
  by (clarsimp_all simp: heuristic_rel_stats_def save_phase_heur_stats_def phase_save_heur_rel_def phase_saving_def
    heuristic_reluctant_tick_stats_def heuristic_reluctant_enable_stats_def heuristic_reluctant_untrigger_stats_def
    set_fully_propagated_heur_stats_def unset_fully_propagated_heur_stats_def mark_added_heur_stats_def swap_emas_stats_def)

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

definition swap_emas :: \<open>isasat_restart_heuristics \<Rightarrow> isasat_restart_heuristics\<close> where
  \<open>swap_emas = Restart_Heuristics o swap_emas_stats o get_restart_heuristics\<close>

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

definition schedule_next_pure_lits_stats :: \<open>restart_heuristics \<Rightarrow> restart_heuristics\<close> where
  \<open>schedule_next_pure_lits_stats = (\<lambda>(fast_ema, slow_ema, res_info, wasted, phasing, reluctant, fullyproped, lit_st, schedule, other_fema, other_sema).
  (fast_ema, slow_ema, restart_info_restart_done res_info, wasted, phasing, reluctant, fullyproped, lit_st, schedule_next_pure_lits_info schedule, other_fema, other_sema))\<close>

definition schedule_next_pure_lits :: \<open>isasat_restart_heuristics \<Rightarrow> isasat_restart_heuristics\<close> where
  \<open>schedule_next_pure_lits = Restart_Heuristics o schedule_next_pure_lits_stats o get_restart_heuristics\<close>

definition next_pure_lits_schedule_info_stats :: \<open>restart_heuristics \<Rightarrow> 64 word\<close> where
  \<open>next_pure_lits_schedule_info_stats = next_pure_lits_schedule_info o schedule_info_of_stats\<close>

definition next_pure_lits_schedule :: \<open>isasat_restart_heuristics \<Rightarrow> 64 word\<close> where
  \<open>next_pure_lits_schedule = next_pure_lits_schedule_info_stats o get_restart_heuristics\<close>

definition schedule_next_reduce_stats :: \<open>64 word \<Rightarrow> restart_heuristics \<Rightarrow> restart_heuristics\<close> where
  \<open>schedule_next_reduce_stats delta = (\<lambda>(fast_ema, slow_ema, res_info, wasted, phasing, reluctant, fullyproped, lit_st, schedule, other_fema, other_sema). (fast_ema, slow_ema, restart_info_restart_done res_info, wasted, phasing, reluctant, fullyproped, lit_st, schedule_next_reduce_info delta schedule, other_fema, other_sema))\<close>

definition schedule_next_reduce :: \<open>64 word \<Rightarrow> isasat_restart_heuristics \<Rightarrow> isasat_restart_heuristics\<close> where
  \<open>schedule_next_reduce delta = Restart_Heuristics o schedule_next_reduce_stats delta o get_restart_heuristics\<close>

definition next_reduce_schedule_info_stats :: \<open>restart_heuristics \<Rightarrow> 64 word\<close> where
  \<open>next_reduce_schedule_info_stats = next_reduce_schedule_info o schedule_info_of_stats\<close>

definition next_reduce_schedule :: \<open>isasat_restart_heuristics \<Rightarrow> 64 word\<close> where
  \<open>next_reduce_schedule = next_reduce_schedule_info_stats o get_restart_heuristics\<close>

definition schedule_next_subsume_stats :: \<open>64 word \<Rightarrow> restart_heuristics \<Rightarrow> restart_heuristics\<close> where
  \<open>schedule_next_subsume_stats delta = (\<lambda>(fast_ema, slow_ema, res_info, wasted, phasing, reluctant, fullyproped, lit_st, schedule, other_fema, other_sema). (fast_ema, slow_ema, restart_info_restart_done res_info, wasted, phasing, reluctant, fullyproped, lit_st, schedule_next_subsume_info delta schedule, other_fema, other_sema))\<close>

definition schedule_next_subsume :: \<open>64 word \<Rightarrow> isasat_restart_heuristics \<Rightarrow> isasat_restart_heuristics\<close> where
  \<open>schedule_next_subsume delta = Restart_Heuristics o schedule_next_subsume_stats delta o get_restart_heuristics\<close>

definition next_subsume_schedule_info_stats :: \<open>restart_heuristics \<Rightarrow> 64 word\<close> where
  \<open>next_subsume_schedule_info_stats = next_subsume_schedule_info o schedule_info_of_stats\<close>

definition next_subsume_schedule :: \<open>isasat_restart_heuristics \<Rightarrow> 64 word\<close> where
  \<open>next_subsume_schedule = next_subsume_schedule_info_stats o get_restart_heuristics\<close>

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
  \<open>heuristic_rel \<A> heur \<Longrightarrow> heuristic_rel \<A> (swap_emas heur)\<close>
  by (auto simp: heuristic_rel_def save_phase_heur_def phase_save_heur_rel_def phase_saving_def
    heuristic_reluctant_tick_def heuristic_reluctant_enable_def heuristic_reluctant_untrigger_def
    set_fully_propagated_heur_def unset_fully_propagated_heur_def set_zero_wasted_def incr_wasted_def
    incr_restart_phase_def mark_added_heur_def swap_emas_def)

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
fun incr_restart_phase_end_stats :: \<open>64 word \<Rightarrow> restart_heuristics \<Rightarrow> restart_heuristics\<close> where
  \<open>incr_restart_phase_end_stats end_of_phase (fast_ema, slow_ema, (ccount, ema_lvl, restart_phase, _, stabmode, init_phase_ticks), wasted) =
  (fast_ema, slow_ema, (ccount, ema_lvl, restart_phase, end_of_phase, stabmode, init_phase_ticks), wasted)\<close>

fun incr_restart_phase_and_length_end_stats :: \<open>64 word \<Rightarrow> restart_heuristics \<Rightarrow> restart_heuristics\<close> where
  \<open>incr_restart_phase_and_length_end_stats end_of_phase (fast_ema, slow_ema, (ccount, ema_lvl, restart_phase, _, stabmode, init_phase_ticks), wasted) =
  (fast_ema, slow_ema, (ccount, ema_lvl, restart_phase, end_of_phase, stabmode +1, init_phase_ticks), wasted)\<close>


fun init_phase_ticks_stats :: \<open>restart_heuristics \<Rightarrow> 64 word\<close> where
  \<open>init_phase_ticks_stats (fast_ema, slow_ema, (ccount, ema_lvl, restart_phase, end_of_phase, stabmode, init_phase_ticks), wasted) = init_phase_ticks\<close>

fun set_init_phase_ticks_stats :: \<open>64 word \<Rightarrow> restart_heuristics \<Rightarrow> restart_heuristics\<close> where
  \<open>set_init_phase_ticks_stats init_phase_ticks (fast_ema, slow_ema, (ccount, ema_lvl, restart_phase, end_of_phase, stabmode, _), wasted) =
  (fast_ema, slow_ema, (ccount, ema_lvl, restart_phase, end_of_phase, stabmode, init_phase_ticks), wasted)\<close>

definition incr_restart_phase_and_length_end :: \<open>64 word \<Rightarrow> isasat_restart_heuristics \<Rightarrow> isasat_restart_heuristics\<close> where
  \<open>incr_restart_phase_and_length_end end_of_phase = Restart_Heuristics o (incr_restart_phase_and_length_end_stats end_of_phase) o get_content\<close>

definition set_init_phase_ticks :: \<open>64 word \<Rightarrow> isasat_restart_heuristics \<Rightarrow> isasat_restart_heuristics\<close> where
  \<open>set_init_phase_ticks end_of_phase = Restart_Heuristics o (set_init_phase_ticks_stats end_of_phase) o get_content\<close>

lemma heuristic_rel_incr_restart_lengthI[intro!]:
  \<open>heuristic_rel \<A> heur \<Longrightarrow> heuristic_rel \<A> (incr_restart_phase_and_length_end lcount heur)\<close>
  by (auto simp: heuristic_rel_def heuristic_rel_stats_def incr_restart_phase_and_length_end_def)

lemma heuristic_rel_set_init_phase_ticks[intro!]:
  \<open>heuristic_rel \<A> heur \<Longrightarrow> heuristic_rel \<A> (set_init_phase_ticks lcount heur)\<close>
  by (auto simp: heuristic_rel_def heuristic_rel_stats_def set_init_phase_ticks_def)

definition incr_restart_phase_end :: \<open>64 word \<Rightarrow> isasat_restart_heuristics \<Rightarrow> isasat_restart_heuristics\<close> where
  \<open>incr_restart_phase_end end_of_phase = Restart_Heuristics o (incr_restart_phase_end_stats end_of_phase) o get_content\<close>

lemma heuristic_rel_incr_restartI[intro!]:
  \<open>heuristic_rel \<A> heur \<Longrightarrow> heuristic_rel \<A> (incr_restart_phase_end lcount heur)\<close>
  by (auto simp: heuristic_rel_def heuristic_rel_stats_def incr_restart_phase_end_def)


lemma [intro!]:
  \<open>heuristic_rel \<A> heur \<Longrightarrow> heuristic_rel \<A> (heuristic_reluctant_disable heur)\<close>
  \<open>heuristic_rel \<A> heur \<Longrightarrow> heuristic_rel \<A> (schedule_next_pure_lits heur)\<close>
  \<open>heuristic_rel \<A> heur \<Longrightarrow> heuristic_rel \<A> (heuristic_reluctant_disable heur)\<close>
  \<open>heuristic_rel \<A> heur \<Longrightarrow> heuristic_rel \<A> (schedule_next_reduce delta heur)\<close>
  by (auto simp: heuristic_rel_def heuristic_reluctant_disable_def heuristic_rel_stats_def heuristic_reluctant_disable_stats_def
     next_pure_lits_schedule_def schedule_next_pure_lits_def schedule_next_pure_lits_stats_def
     next_reduce_schedule_def schedule_next_reduce_def schedule_next_reduce_stats_def)

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

definition stabmode_stats :: \<open>restart_heuristics \<Rightarrow> 64 word\<close> where
  \<open>stabmode_stats = (\<lambda>(_, _, (restart_phase,_ ,_ , end_of_phase, stabmode, _::64 word), _). stabmode)\<close>
  
definition end_of_restart_phase :: \<open>isasat_restart_heuristics \<Rightarrow> 64 word\<close> where
  \<open>end_of_restart_phase = end_of_restart_phase_stats o get_content\<close>


definition nbstable_phase :: \<open>isasat_restart_heuristics \<Rightarrow> 64 word\<close> where
  \<open>nbstable_phase = stabmode_stats o get_content\<close>
  
definition init_phase_ticks :: \<open>isasat_restart_heuristics \<Rightarrow> 64 word\<close> where
  \<open>init_phase_ticks = init_phase_ticks_stats o get_content\<close>

end
