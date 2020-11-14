theory IsaSAT_Stats_LLVM
imports IsaSAT_Stats IsaSAT_EMA_LLVM IsaSAT_Rephase_LLVM IsaSAT_Reluctant_LLVM
begin
  abbreviation stats_rel :: \<open>(stats \<times> stats) set\<close> where
  \<open>stats_rel \<equiv> word64_rel \<times>\<^sub>r word64_rel \<times>\<^sub>r word64_rel \<times>\<^sub>r word64_rel \<times>\<^sub>r word64_rel
     \<times>\<^sub>r word64_rel \<times>\<^sub>r word64_rel \<times>\<^sub>r ema_rel\<close>

abbreviation stats_assn :: \<open>stats \<Rightarrow> stats \<Rightarrow> assn\<close> where
  \<open>stats_assn \<equiv> word64_assn \<times>\<^sub>a word64_assn \<times>\<^sub>a  word64_assn \<times>\<^sub>a word64_assn \<times>\<^sub>a word64_assn \<times>\<^sub>a
     word64_assn \<times>\<^sub>a word64_assn \<times>\<^sub>a ema_assn\<close>


lemma [sepref_import_param]:
  \<open>(incr_propagation,incr_propagation) \<in> stats_rel \<rightarrow> stats_rel\<close>
  \<open>(stats_conflicts,stats_conflicts) \<in> stats_rel \<rightarrow> word_rel\<close>
  \<open>(incr_conflict,incr_conflict) \<in> stats_rel \<rightarrow> stats_rel\<close>
  \<open>(incr_decision,incr_decision) \<in> stats_rel \<rightarrow> stats_rel\<close>
  \<open>(incr_restart,incr_restart) \<in> stats_rel \<rightarrow> stats_rel\<close>
  \<open>(incr_lrestart,incr_lrestart) \<in> stats_rel \<rightarrow> stats_rel\<close>
  \<open>(incr_uset,incr_uset) \<in> stats_rel \<rightarrow> stats_rel\<close>
  \<open>(incr_GC,incr_GC) \<in> stats_rel \<rightarrow> stats_rel\<close>
  \<open>(add_lbd,add_lbd) \<in> word32_rel \<rightarrow> stats_rel \<rightarrow> stats_rel\<close>
  by auto

lemmas [llvm_inline] =
  incr_propagation_def
  incr_conflict_def
  incr_decision_def
  incr_restart_def
  incr_lrestart_def
  incr_uset_def
  incr_GC_def
  stats_conflicts_def


abbreviation (input) \<open>restart_info_rel \<equiv> word64_rel \<times>\<^sub>r word64_rel \<times>\<^sub>r word64_rel \<times>\<^sub>r word64_rel \<times>\<^sub>r word64_rel\<close>

abbreviation (input) restart_info_assn where
  \<open>restart_info_assn \<equiv> word64_assn \<times>\<^sub>a word64_assn \<times>\<^sub>a word64_assn \<times>\<^sub>a word64_assn \<times>\<^sub>a word64_assn\<close>

lemma restart_info_params[sepref_import_param]:
  "(incr_conflict_count_since_last_restart,incr_conflict_count_since_last_restart) \<in>
    restart_info_rel \<rightarrow> restart_info_rel"
  "(restart_info_update_lvl_avg,restart_info_update_lvl_avg) \<in>
    word32_rel \<rightarrow> restart_info_rel \<rightarrow> restart_info_rel"
  \<open>(restart_info_init,restart_info_init) \<in> restart_info_rel\<close>
  \<open>(restart_info_restart_done,restart_info_restart_done) \<in> restart_info_rel \<rightarrow> restart_info_rel\<close>
  by auto

lemmas [llvm_inline] =
  incr_conflict_count_since_last_restart_def
  restart_info_update_lvl_avg_def
  restart_info_init_def
  restart_info_restart_done_def



sepref_register NORMAL_PHASE QUIET_PHASE DEFAULT_INIT_PHASE

sepref_def NORMAL_PHASE_impl
  is \<open>uncurry0 (RETURN NORMAL_PHASE)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding NORMAL_PHASE_def
  by sepref

sepref_def QUIET_PHASE_impl
  is \<open>uncurry0 (RETURN QUIET_PHASE)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding QUIET_PHASE_def
  by sepref

definition lcount_assn :: \<open>clss_size \<Rightarrow> _ \<Rightarrow> assn\<close> where
  \<open>lcount_assn \<equiv> uint64_nat_assn \<times>\<^sub>a uint64_nat_assn \<times>\<^sub>a uint64_nat_assn \<times>\<^sub>a uint64_nat_assn\<close>

lemma [safe_constraint_rules]:
  \<open>CONSTRAINT Sepref_Basic.is_pure lcount_assn\<close>
  unfolding lcount_assn_def
  by auto

sepref_def clss_size_lcount_fast_code
  is \<open>RETURN o clss_size_lcount\<close>
  :: \<open>lcount_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  unfolding clss_size_lcount_def lcount_assn_def
  by sepref

sepref_register clss_size_resetUS

lemma clss_size_resetUS_alt_def:
  \<open>RETURN o clss_size_resetUS =
  (\<lambda>(lcount, lcountUE, lcountUS, lcountU0). RETURN (lcount, lcountUE, 0, lcountU0))\<close>
  by (auto simp: clss_size_resetUS_def)

sepref_def clss_size_resetUS_fast_code
  is \<open>RETURN o clss_size_resetUS\<close>
  :: \<open>lcount_assn\<^sup>d \<rightarrow>\<^sub>a lcount_assn\<close>
  unfolding clss_size_resetUS_alt_def lcount_assn_def
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

lemma clss_size_incr_lcountUS_alt_def:
  \<open>RETURN o clss_size_incr_lcountUS =
  (\<lambda>(lcount, lcountUE, lcountUS, lcountU0). RETURN (lcount, lcountUE, lcountUS + 1, lcountU0))\<close>
  by (auto simp: clss_size_incr_lcountUS_def)

sepref_def clss_size_incr_lcountUS_fast_code
  is \<open>RETURN o clss_size_incr_lcountUS\<close>
  :: \<open>[\<lambda>S. clss_size_lcountUS S < uint64_max]\<^sub>a lcount_assn\<^sup>d \<rightarrow> lcount_assn\<close>
  unfolding clss_size_incr_lcountUS_alt_def lcount_assn_def clss_size_lcountUS_def
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

lemma clss_size_incr_lcountU0_alt_def:
  \<open>RETURN o clss_size_incr_lcountU0 =
  (\<lambda>(lcount, lcountUE, lcountUS, lcountU0). RETURN (lcount, lcountUE, lcountUS, lcountU0+1))\<close>
  by (auto simp: clss_size_incr_lcountU0_def)

sepref_def clss_size_incr_lcountU0_fast_code
  is \<open>RETURN o clss_size_incr_lcountU0\<close>
  :: \<open>[\<lambda>S. clss_size_lcountU0 S < uint64_max]\<^sub>a lcount_assn\<^sup>d \<rightarrow> lcount_assn\<close>
  unfolding clss_size_incr_lcountU0_alt_def lcount_assn_def clss_size_lcountU0_def
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

lemma clss_size_incr_lcountUE_alt_def:
  \<open>RETURN o clss_size_incr_lcountUE =
  (\<lambda>(lcount, lcountUE, lcountUS). RETURN (lcount, lcountUE + 1, lcountUS))\<close>
  by (auto simp: clss_size_incr_lcountUE_def)

sepref_def clss_size_incr_lcountUE_fast_code
  is \<open>RETURN o clss_size_incr_lcountUE\<close>
  :: \<open>[\<lambda>S. clss_size_lcountUE S < uint64_max]\<^sub>a lcount_assn\<^sup>d \<rightarrow> lcount_assn\<close>
  unfolding clss_size_incr_lcountUE_alt_def lcount_assn_def clss_size_lcountUE_def
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

schematic_goal mk_free_lookup_clause_rel_assn[sepref_frame_free_rules]: \<open>MK_FREE lcount_assn ?fr\<close>
  unfolding lcount_assn_def
  by (rule free_thms sepref_frame_free_rules)+ (* TODO: Write a method for that! *)

lemma clss_size_lcountUE_alt_def:
  \<open>RETURN o clss_size_lcountUE = (\<lambda>(lcount, lcountUE, lcountUS). RETURN lcountUE)\<close>
  by (auto simp: clss_size_lcountUE_def)

sepref_def clss_size_lcountUE_fast_code
  is \<open>RETURN o clss_size_lcountUE\<close>
  :: \<open>lcount_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  unfolding lcount_assn_def clss_size_lcountUE_alt_def clss_size_lcount_def
  by sepref

lemma clss_size_lcountUS_alt_def:
  \<open>RETURN o clss_size_lcountUS = (\<lambda>(lcount, lcountUE, lcountUS, lcountU0). RETURN lcountUS)\<close>
  by (auto simp: clss_size_lcountUS_def)

sepref_def clss_size_lcountUSt_fast_code
  is \<open>RETURN o clss_size_lcountUS\<close>
  :: \<open>lcount_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  unfolding lcount_assn_def clss_size_lcountUS_alt_def clss_size_lcount_def
  by sepref

lemma clss_size_lcountU0_alt_def:
  \<open>RETURN o clss_size_lcountU0 = (\<lambda>(lcount, lcountUE, lcountUS, lcountU0). RETURN lcountU0)\<close>
  by (auto simp: clss_size_lcountU0_def)

sepref_def clss_size_lcountU0_fast_code
  is \<open>RETURN o clss_size_lcountU0\<close>
  :: \<open>lcount_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  unfolding lcount_assn_def clss_size_lcountU0_alt_def clss_size_lcount_def
  by sepref

lemma clss_size_incr_allcount_alt_def:
  \<open>RETURN o clss_size_allcount =
  (\<lambda>(lcount, lcountUE, lcountUS, lcountU0). RETURN (lcount + lcountUE + lcountUS + lcountU0))\<close>
  by (auto simp: clss_size_allcount_def)

sepref_def clss_size_allcount_fast_code
  is \<open>RETURN o clss_size_allcount\<close>
  :: \<open>[\<lambda>S. clss_size_allcount S < max_snat 64]\<^sub>a lcount_assn\<^sup>d \<rightarrow> uint64_nat_assn\<close>
  unfolding clss_size_incr_allcount_alt_def lcount_assn_def clss_size_allcount_def
  by sepref


lemma clss_size_decr_lcount_alt_def:
  \<open>RETURN o clss_size_decr_lcount =
  (\<lambda>(lcount, lcountUE, lcountUS). RETURN (lcount - 1, lcountUE, lcountUS))\<close>
  by (auto simp: clss_size_decr_lcount_def)

sepref_def clss_size_decr_lcount_fast_code
  is \<open>RETURN o clss_size_decr_lcount\<close>
  :: \<open>[\<lambda>S. clss_size_lcount S \<ge> 1]\<^sub>a lcount_assn\<^sup>d \<rightarrow> lcount_assn\<close>
  unfolding lcount_assn_def clss_size_decr_lcount_alt_def clss_size_lcount_def
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref


lemma emag_get_value_alt_def:
  \<open>ema_get_value = (\<lambda>(a, b, c, d). a)\<close>
  by auto

sepref_def ema_get_value_impl
  is \<open>RETURN o ema_get_value\<close>
  :: \<open>ema_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding emag_get_value_alt_def
  by sepref

lemma emag_extract_value_alt_def:
  \<open>ema_extract_value = (\<lambda>(a, b, c, d). a >> EMA_FIXPOINT_SIZE)\<close>
  by auto

sepref_def ema_extract_value_impl
  is \<open>RETURN o ema_extract_value\<close>
  :: \<open>ema_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding emag_extract_value_alt_def EMA_FIXPOINT_SIZE_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

type_synonym heur_assn = \<open>(ema \<times> ema \<times> restart_info \<times> 64 word \<times>
   (phase_saver_assn \<times> 64 word \<times> phase_saver'_assn \<times> 64 word \<times> phase_saver'_assn \<times> 64 word \<times> 64 word \<times> 64 word) \<times> reluctant_rel_assn)\<close>

definition heuristic_assn :: \<open>restart_heuristics \<Rightarrow> heur_assn \<Rightarrow> assn\<close> where
  \<open>heuristic_assn = ema_assn \<times>\<^sub>a
  ema_assn \<times>\<^sub>a
  restart_info_assn \<times>\<^sub>a
  word64_assn \<times>\<^sub>a phase_heur_assn \<times>\<^sub>a reluctant_assn\<close>

lemma set_zero_wasted_def:
  \<open>set_zero_wasted = (\<lambda>(fast_ema, slow_ema, res_info, wasted, \<phi>).
    (fast_ema, slow_ema, res_info, 0, \<phi>))\<close>
  by (auto intro!: ext)

sepref_def set_zero_wasted_impl
  is \<open>RETURN o set_zero_wasted\<close>
  :: \<open>heuristic_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_assn\<close>
  unfolding heuristic_assn_def set_zero_wasted_def
  by sepref

lemma mop_save_phase_heur_alt_def:
  \<open>mop_save_phase_heur = (\<lambda> L b (fast_ema, slow_ema, res_info, wasted, (\<phi>, target, best), rel). do {
    ASSERT(L < length \<phi>);
    RETURN (fast_ema, slow_ema, res_info, wasted, (\<phi>[L := b], target,
                 best), rel)})\<close>
  unfolding mop_save_phase_heur_def save_phase_heur_def save_phase_heur_pre_def
    heuristic_assn_def
  by (auto intro!: ext)

sepref_def mop_save_phase_heur_impl
  is \<open>uncurry2 (mop_save_phase_heur)\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a heuristic_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_assn\<close>
  supply [[goals_limit=1]]
  unfolding mop_save_phase_heur_alt_def save_phase_heur_def save_phase_heur_pre_def
    heuristic_assn_def phase_heur_assn_def
  apply annot_all_atm_idxs
  by sepref


sepref_def heuristic_reluctant_tick_impl
  is \<open>RETURN o heuristic_reluctant_tick\<close>
  :: \<open>heuristic_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_assn\<close>
  unfolding heuristic_reluctant_tick_def heuristic_assn_def
  by sepref


sepref_def heuristic_reluctant_enable_impl
  is \<open>RETURN o heuristic_reluctant_enable\<close>
  :: \<open>heuristic_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_assn\<close>
  unfolding heuristic_reluctant_enable_def heuristic_assn_def
  by sepref

sepref_def heuristic_reluctant_disable_impl
  is \<open>RETURN o heuristic_reluctant_disable\<close>
  :: \<open>heuristic_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_assn\<close>
  unfolding heuristic_reluctant_disable_def heuristic_assn_def
  by sepref

sepref_def heuristic_reluctant_triggered_impl
  is \<open>RETURN o heuristic_reluctant_triggered\<close>
  :: \<open>heuristic_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_assn \<times>\<^sub>a bool1_assn\<close>
  unfolding heuristic_reluctant_triggered_def heuristic_assn_def
  by sepref

sepref_def heuristic_reluctant_triggered2_impl
  is \<open>RETURN o heuristic_reluctant_triggered2\<close>
  :: \<open>heuristic_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding heuristic_reluctant_triggered2_def heuristic_assn_def
  by sepref

sepref_def heuristic_reluctant_untrigger_impl
  is \<open>RETURN o heuristic_reluctant_untrigger\<close>
  :: \<open>heuristic_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_assn\<close>
  unfolding heuristic_reluctant_untrigger_def heuristic_assn_def
  by sepref

lemma clss_size_incr_lcount_alt_def:
  \<open>RETURN o clss_size_incr_lcount =
  (\<lambda>(lcount,  lcountUE, lcountUS). RETURN (lcount + 1, lcountUE, lcountUS))\<close>
  by (auto simp: clss_size_incr_lcount_def)

sepref_register clss_size_incr_lcount
sepref_def clss_size_incr_lcount_fast_code
  is \<open>RETURN o clss_size_incr_lcount\<close>
  :: \<open>[\<lambda>S. clss_size_lcount S \<le> max_snat 64]\<^sub>a lcount_assn\<^sup>d \<rightarrow> lcount_assn\<close>
  unfolding clss_size_incr_lcount_alt_def lcount_assn_def clss_size_lcount_def
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

schematic_goal mk_free_heuristic_assn[sepref_frame_free_rules]: \<open>MK_FREE heuristic_assn ?fr\<close>
  unfolding heuristic_assn_def
  by synthesize_free

end