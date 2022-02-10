theory IsaSAT_Stats_LLVM
imports IsaSAT_Stats IsaSAT_EMA_LLVM IsaSAT_Rephase_LLVM IsaSAT_Reluctant_LLVM
begin
no_notation WB_More_Refinement.fref (\<open>[_]\<^sub>f _ \<rightarrow> _\<close> [0,60,60] 60)
no_notation WB_More_Refinement.freft (\<open>_ \<rightarrow>\<^sub>f _\<close> [60,60] 60)
hide_const (open) NEMonad.RETURN NEMonad.ASSERT


lemma Exists_eq_simp_sym: \<open>(\<exists>x. (P x \<and>* \<up> (b = x)) s) \<longleftrightarrow> P b s\<close>
  by (subst eq_commute[of b])
     (rule Exists_eq_simp)

definition code_hider_assn where
  \<open>code_hider_assn R S = hr_comp R (\<langle>S\<rangle>code_hider_rel)\<close>


lemma get_content_destroyed_kept[sepref_fr_rules]:
  \<open>CONSTRAINT is_pure R \<Longrightarrow> (Mreturn o id, RETURN o get_content) \<in>  (code_hider_assn R S)\<^sup>k \<rightarrow>\<^sub>a hr_comp R S\<close>
  unfolding code_hider_assn_def code_hider_rel_def
  apply sepref_to_hoare
  apply vcg
  apply (auto simp: br_def ENTAILS_def Exists_eq_simp Exists_eq_simp_sym hr_comp_def pure_true_conv)
  by (smt (z3) Sep_Algebra_Add.pure_part_pure entails_def is_pure_conv pure_app_eq pure_partI sep.mult_assoc sep_conj_def split_conj_is_pure)

lemma Constructor_assn_destroyed:
  \<open>(Mreturn o id, RETURN o Constructor) \<in> (hr_comp R S)\<^sup>d \<rightarrow>\<^sub>a code_hider_assn R S\<close>
  unfolding code_hider_assn_def code_hider_rel_def
  apply sepref_to_hoare
  apply vcg
  by (auto simp: br_def ENTAILS_def Exists_eq_simp Exists_eq_simp_sym hr_comp_def pure_true_conv)

lemma get_content_destroyed:
  \<open>(Mreturn o id, RETURN o get_content) \<in>  (code_hider_assn R S)\<^sup>d \<rightarrow>\<^sub>a hr_comp R S\<close>
  unfolding code_hider_assn_def code_hider_rel_def
  apply sepref_to_hoare
  apply vcg
  by (auto simp: br_def ENTAILS_def Exists_eq_simp Exists_eq_simp_sym hr_comp_def pure_true_conv)

lemma get_content_hnr[sepref_fr_rules]:
  \<open>(id, get_content) \<in>  \<langle>S\<rangle>code_hider_rel \<rightarrow>\<^sub>f S\<close>
  unfolding code_hider_rel_def
  by (auto simp: intro!: frefI)


lemma Constructor_hnr[sepref_fr_rules]:
  \<open>(id, Constructor) \<in>  S \<rightarrow>\<^sub>f \<langle>S\<rangle>code_hider_rel\<close>
  unfolding code_hider_rel_def
  by (auto simp: intro!: frefI)

abbreviation stats_int_rel :: \<open>(stats \<times> stats) set\<close> where
  \<open>stats_int_rel \<equiv> word64_rel \<times>\<^sub>r word64_rel \<times>\<^sub>r word64_rel \<times>\<^sub>r word64_rel \<times>\<^sub>r word64_rel
     \<times>\<^sub>r word64_rel \<times>\<^sub>r word64_rel \<times>\<^sub>r word64_rel \<times>\<^sub>r word64_rel \<times>\<^sub>r ema_rel\<close>

abbreviation stats_int_assn :: \<open>stats \<Rightarrow> stats \<Rightarrow> assn\<close> where
  \<open>stats_int_assn \<equiv> word64_assn \<times>\<^sub>a word64_assn \<times>\<^sub>a  word64_assn \<times>\<^sub>a word64_assn \<times>\<^sub>a word64_assn \<times>\<^sub>a
     word64_assn \<times>\<^sub>a word64_assn \<times>\<^sub>a word64_assn \<times>\<^sub>a word64_assn \<times>\<^sub>a ema_assn\<close>

abbreviation stats_rel :: \<open>(stats \<times> isasat_stats) set\<close> where
  \<open>stats_rel \<equiv> \<langle>stats_int_rel\<rangle>code_hider_rel\<close>

definition stats_assn :: \<open>isasat_stats \<Rightarrow> stats \<Rightarrow> assn\<close> where
  \<open>stats_assn = code_hider_assn stats_int_assn Id\<close>

lemma [sepref_import_param]:
  \<open>(incr_propagation_stats,incr_propagation) \<in> stats_rel \<rightarrow> stats_rel\<close>
  \<open>(stats_conflicts_stats,stats_conflicts) \<in> stats_rel \<rightarrow> word_rel\<close>
  \<open>(incr_conflict_stats,incr_conflict) \<in> stats_rel \<rightarrow> stats_rel\<close>
  \<open>(incr_decision_stats,incr_decision) \<in> stats_rel \<rightarrow> stats_rel\<close>
  \<open>(incr_restart_stats,incr_restart) \<in> stats_rel \<rightarrow> stats_rel\<close>
  \<open>(incr_lrestart_stats,incr_lrestart) \<in> stats_rel \<rightarrow> stats_rel\<close>
  \<open>(incr_uset_stats,incr_uset) \<in> stats_rel \<rightarrow> stats_rel\<close>
  \<open>(incr_GC_stats,incr_GC) \<in> stats_rel \<rightarrow> stats_rel\<close>
  \<open>(add_lbd_stats,add_lbd) \<in> word32_rel \<rightarrow> stats_rel \<rightarrow> stats_rel\<close>
  \<open>(units_since_last_GC_stats,units_since_last_GC)\<in> stats_rel \<rightarrow> word_rel\<close>
  \<open>(decr_irred_clss_stats,decr_irred_clss)\<in> stats_rel \<rightarrow> stats_rel\<close>
  \<open>(incr_irred_clss_stats,incr_irred_clss)\<in> stats_rel \<rightarrow> stats_rel\<close>
  \<open>(incr_units_since_last_GC_stats, incr_units_since_last_GC) \<in> stats_rel \<rightarrow> stats_rel\<close>
  \<open>(get_conflict_count_stats, get_conflict_count) \<in> stats_rel \<rightarrow> word64_rel\<close>
  \<open>(add_lbd_stats, add_lbd) \<in> word_rel \<rightarrow> stats_rel \<rightarrow> stats_rel\<close>
  by (auto simp: incr_propagation_def code_hider_rel_def
    stats_conflicts_def
    incr_conflict_def incr_decision_def
    incr_lrestart_def incr_uset_def
    incr_GC_def add_lbd_def add_lbd_def
    units_since_last_GC_def
    incr_restart_def incr_irred_clss_def get_conflict_count_def
    decr_irred_clss_def incr_units_since_last_GC_def)

lemmas [llvm_inline] =
  incr_propagation_stats_def
  incr_conflict_stats_def
  incr_decision_stats_def
  incr_restart_stats_def
  incr_lrestart_stats_def
  incr_uset_stats_def
  incr_GC_stats_def
  stats_conflicts_stats_def
  units_since_last_GC_stats_def
  decr_irred_clss_stats_def
  incr_irred_clss_stats_def
  incr_units_since_last_GC_stats_def
  get_conflict_count_stats_def


lemma id_unat[sepref_fr_rules]:
  \<open>(Mreturn o id, RETURN o unat) \<in> word32_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  apply sepref_to_hoare
  apply vcg
  by (auto simp: ENTAILS_def unat_rel_def unat.rel_def br_def pred_lift_merge_simps
    pred_lift_def pure_true_conv)

sepref_def add_lbd_stats_impl
  is \<open>uncurry (RETURN oo add_lbd_stats)\<close>
  :: \<open>word32_assn\<^sup>k *\<^sub>a stats_int_assn\<^sup>d \<rightarrow>\<^sub>a stats_int_assn\<close>
  unfolding add_lbd_stats_def
  by sepref

lemma add_lbd_stats_add_lbd:
  \<open>(add_lbd_stats, add_lbd) \<in> word_rel \<rightarrow> stats_rel \<rightarrow> stats_rel\<close> and
  get_conflict_count_stats_get_conflict_count:
  \<open>(get_conflict_count_stats, get_conflict_count) \<in> stats_rel \<rightarrow> word_rel\<close> and
  units_since_last_GC_stats_units_since_last_GC:
  \<open>(units_since_last_GC_stats, units_since_last_GC) \<in> stats_rel \<rightarrow> word_rel\<close> and
  reset_units_since_last_GC_stats_reset_units_since_last_GC:
  \<open>(reset_units_since_last_GC_stats, reset_units_since_last_GC) \<in> stats_rel \<rightarrow> stats_rel\<close> and
  incr_irred_clss_stats_incr_irred_clss:
  \<open>(incr_irred_clss_stats, incr_irred_clss) \<in> stats_rel \<rightarrow> stats_rel\<close>and
  decr_irred_clss_stats_decr_irred_clss:
  \<open>(decr_irred_clss_stats, decr_irred_clss) \<in> stats_rel \<rightarrow> stats_rel\<close> and
  incr_propagation_stats_incr_propagation:
  \<open>(incr_propagation_stats, incr_propagation) \<in> stats_rel \<rightarrow> stats_rel\<close>and
  incr_conflict_stats_incr_conflict:
  \<open>(incr_conflict_stats, incr_conflict) \<in> stats_rel \<rightarrow> stats_rel\<close>and
  incr_decision_stats_incr_decision:
  \<open>(incr_decision_stats, incr_decision) \<in> stats_rel \<rightarrow> stats_rel\<close>and
  incr_GC_stats_incr_GC:
  \<open>(incr_GC_stats, incr_GC) \<in> stats_rel \<rightarrow> stats_rel\<close>and
  incr_uset_stats_incr_uset:
  \<open>(incr_uset_stats, incr_uset) \<in> stats_rel \<rightarrow> stats_rel\<close>and
  incr_restart_stats_incr_restart:
  \<open>(incr_restart_stats, incr_restart) \<in> stats_rel \<rightarrow> stats_rel\<close>and
  incr_lrestart_stats_incr_lrestart:
  \<open>(incr_lrestart_stats, incr_lrestart) \<in> stats_rel \<rightarrow> stats_rel\<close> and
  stats_conflicts_stats_stats_conflicts:
  \<open>(stats_conflicts_stats, stats_conflicts)\<in> stats_rel \<rightarrow> word_rel\<close> and
  incr_units_since_last_GC_stats_incr_units_since_last_GC:
  \<open>(incr_units_since_last_GC_stats, incr_units_since_last_GC) \<in> stats_rel \<rightarrow> stats_rel\<close>
  by (auto simp: incr_propagation_def code_hider_rel_def
    stats_conflicts_def
    incr_conflict_def incr_decision_def
    incr_lrestart_def incr_uset_def
    incr_GC_def add_lbd_def add_lbd_def
    units_since_last_GC_def reset_units_since_last_GC_def
    incr_restart_def incr_irred_clss_def get_conflict_count_def
    decr_irred_clss_def incr_units_since_last_GC_def)

sepref_def get_conflict_count_stats_impl
  is \<open>(RETURN o get_conflict_count_stats)\<close>
  :: \<open>stats_int_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding get_conflict_count_stats_def
  by sepref


sepref_def units_since_last_GC_stats_impl
  is \<open>(RETURN o units_since_last_GC_stats)\<close>
  :: \<open>stats_int_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding units_since_last_GC_stats_def
  by sepref

sepref_def reset_units_since_last_GC_stats_impl
  is \<open>(RETURN o reset_units_since_last_GC_stats)\<close>
  :: \<open>stats_int_assn\<^sup>d \<rightarrow>\<^sub>a stats_int_assn\<close>
  unfolding reset_units_since_last_GC_stats_def
  by sepref

sepref_def incr_irred_clss_stats_impl
  is \<open>RETURN o incr_irred_clss_stats\<close>
  :: \<open>stats_int_assn\<^sup>d \<rightarrow>\<^sub>a stats_int_assn\<close>
  unfolding incr_irred_clss_stats_def
  by sepref

sepref_def decr_irred_clss_stats_impl
  is \<open>RETURN o decr_irred_clss_stats\<close>
  :: \<open>stats_int_assn\<^sup>d \<rightarrow>\<^sub>a stats_int_assn\<close>
  unfolding decr_irred_clss_stats_def
  by sepref

sepref_def incr_propagation_stats_impl
  is \<open>RETURN o incr_propagation_stats\<close>
  :: \<open>stats_int_assn\<^sup>d \<rightarrow>\<^sub>a stats_int_assn\<close>
  unfolding incr_propagation_stats_def
  by sepref

sepref_def incr_conflict_stats_impl
  is \<open>RETURN o incr_conflict_stats\<close>
  :: \<open>stats_int_assn\<^sup>d \<rightarrow>\<^sub>a stats_int_assn\<close>
  unfolding incr_conflict_stats_def
  by sepref

sepref_def incr_decision_stats_impl
  is \<open>RETURN o incr_decision_stats\<close>
  :: \<open>stats_int_assn\<^sup>d \<rightarrow>\<^sub>a stats_int_assn\<close>
  unfolding incr_decision_stats_def
  by sepref

sepref_def incr_restart_stats_impl
  is \<open>RETURN o incr_restart_stats\<close>
  :: \<open>stats_int_assn\<^sup>d \<rightarrow>\<^sub>a stats_int_assn\<close>
  unfolding incr_restart_stats_def
  by sepref

sepref_def incr_lrestart_stats_impl
  is \<open>RETURN o incr_lrestart_stats\<close>
  :: \<open>stats_int_assn\<^sup>d \<rightarrow>\<^sub>a stats_int_assn\<close>
  unfolding incr_lrestart_stats_def
  by sepref

sepref_def incr_uset_stats_impl
  is \<open>RETURN o incr_uset_stats\<close>
  :: \<open>stats_int_assn\<^sup>d \<rightarrow>\<^sub>a stats_int_assn\<close>
  unfolding incr_uset_stats_def
  by sepref

sepref_def incr_GC_stats_impl
  is \<open>RETURN o incr_GC_stats\<close>
  :: \<open>stats_int_assn\<^sup>d \<rightarrow>\<^sub>a stats_int_assn\<close>
  unfolding incr_GC_stats_def
  by sepref

sepref_def stats_conflicts_stats_impl
  is \<open>RETURN o stats_conflicts_stats\<close>
  :: \<open>stats_int_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding stats_conflicts_stats_def
    by sepref

sepref_def incr_units_since_last_GC_stats_impl
  is \<open>RETURN o incr_units_since_last_GC_stats\<close>
  :: \<open>stats_int_assn\<^sup>d \<rightarrow>\<^sub>a stats_int_assn\<close>
  unfolding incr_units_since_last_GC_stats_def
  by sepref

lemma stats_assn_alt_def: \<open>stats_assn = hr_comp stats_int_assn stats_rel\<close>
  \<open>stats_int_assn = hr_comp stats_int_assn stats_int_rel\<close>
  by (auto simp: stats_assn_def code_hider_assn_def)

context
  notes [fcomp_norm_unfold] = stats_assn_alt_def[symmetric] stats_assn_def[symmetric]
begin

lemmas [sepref_fr_rules] =
  add_lbd_stats_impl.refine[FCOMP add_lbd_stats_add_lbd]
  get_conflict_count_stats_impl.refine[FCOMP get_conflict_count_stats_get_conflict_count]
  units_since_last_GC_stats_impl.refine[FCOMP units_since_last_GC_stats_units_since_last_GC]
  reset_units_since_last_GC_stats_impl.refine[FCOMP reset_units_since_last_GC_stats_reset_units_since_last_GC]
  incr_irred_clss_stats_impl.refine[FCOMP incr_irred_clss_stats_incr_irred_clss]
  decr_irred_clss_stats_impl.refine[FCOMP decr_irred_clss_stats_decr_irred_clss]
  incr_propagation_stats_impl.refine[FCOMP incr_propagation_stats_incr_propagation]
  incr_decision_stats_impl.refine[FCOMP incr_decision_stats_incr_decision]
  incr_restart_stats_impl.refine[FCOMP incr_restart_stats_incr_restart]
  incr_lrestart_stats_impl.refine[FCOMP incr_lrestart_stats_incr_lrestart]
  incr_uset_stats_impl.refine[FCOMP incr_uset_stats_incr_uset]
  incr_conflict_stats_impl.refine[FCOMP incr_conflict_stats_incr_conflict]
  incr_GC_stats_impl.refine[FCOMP incr_GC_stats_incr_GC]
  stats_conflicts_stats_impl.refine[FCOMP stats_conflicts_stats_stats_conflicts]
  incr_units_since_last_GC_stats_impl.refine[FCOMP incr_units_since_last_GC_stats_incr_units_since_last_GC]
  hn_id[FCOMP Constructor_hnr, of stats_int_assn stats_int_rel, unfolded stats_assn_alt_def[symmetric]]
  hn_id[FCOMP get_content_hnr, of stats_int_assn stats_int_rel, unfolded stats_assn_alt_def[symmetric]]

end

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
  \<open>lcount_assn \<equiv> uint64_nat_assn \<times>\<^sub>a uint64_nat_assn \<times>\<^sub>a uint64_nat_assn \<times>\<^sub>a uint64_nat_assn \<times>\<^sub>a uint64_nat_assn\<close>

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
  (\<lambda>(lcount, lcountUE, lcountUEk, lcountUS, lcountU0). RETURN (lcount, lcountUE, lcountUEk, 0, lcountU0))\<close>
  by (auto simp: clss_size_resetUS_def)

sepref_def clss_size_resetUS_fast_code
  is \<open>RETURN o clss_size_resetUS\<close>
  :: \<open>lcount_assn\<^sup>d \<rightarrow>\<^sub>a lcount_assn\<close>
  unfolding clss_size_resetUS_alt_def lcount_assn_def
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

lemma clss_size_incr_lcountUS_alt_def:
  \<open>RETURN o clss_size_incr_lcountUS =
  (\<lambda>(lcount, lcountUE, lcountUEk, lcountUS, lcountU0). RETURN (lcount, lcountUE, lcountUEk, lcountUS + 1, lcountU0))\<close>
  by (auto simp: clss_size_incr_lcountUS_def)

sepref_def clss_size_incr_lcountUS_fast_code
  is \<open>RETURN o clss_size_incr_lcountUS\<close>
  :: \<open>[\<lambda>S. clss_size_lcountUS S < uint64_max]\<^sub>a lcount_assn\<^sup>d \<rightarrow> lcount_assn\<close>
  unfolding clss_size_incr_lcountUS_alt_def lcount_assn_def clss_size_lcountUS_def
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

lemma clss_size_resetU0_alt_def:
  \<open>RETURN o clss_size_resetU0 =
  (\<lambda>(lcount, lcountUE, lcountUEk, lcountUS, lcountU0). RETURN (lcount, lcountUE, lcountUEk, lcountUS, 0))\<close>
  by (auto simp: clss_size_resetU0_def)

sepref_def clss_size_resetU0_fast_code
  is \<open>RETURN o clss_size_resetU0\<close>
  :: \<open>lcount_assn\<^sup>d \<rightarrow>\<^sub>a lcount_assn\<close>
  unfolding clss_size_resetU0_alt_def lcount_assn_def
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

lemma clss_size_incr_lcountU0_alt_def:
  \<open>RETURN o clss_size_incr_lcountU0 =
  (\<lambda>(lcount, lcountUE, lcountUEk, lcountUS, lcountU0). RETURN (lcount, lcountUE, lcountUEk, lcountUS, lcountU0+1))\<close>
  by (auto simp: clss_size_incr_lcountU0_def)

sepref_def clss_size_incr_lcountU0_fast_code
  is \<open>RETURN o clss_size_incr_lcountU0\<close>
  :: \<open>[\<lambda>S. clss_size_lcountU0 S < uint64_max]\<^sub>a lcount_assn\<^sup>d \<rightarrow> lcount_assn\<close>
  unfolding clss_size_incr_lcountU0_alt_def lcount_assn_def clss_size_lcountU0_def
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

lemma clss_size_resetUE_alt_def:
  \<open>RETURN o clss_size_resetUE =
  (\<lambda>(lcount, lcountUE, lcountUEk, lcountUS, lcountU0). RETURN (lcount, 0, lcountUEk, lcountUS, lcountU0))\<close>
  by (auto simp: clss_size_resetUE_def)

sepref_def clss_size_resetUE_fast_code
  is \<open>RETURN o clss_size_resetUE\<close>
  :: \<open>lcount_assn\<^sup>d \<rightarrow>\<^sub>a lcount_assn\<close>
  unfolding clss_size_resetUE_alt_def lcount_assn_def
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

lemma clss_size_incr_lcountUEk_alt_def:
  \<open>RETURN o clss_size_incr_lcountUEk =
  (\<lambda>(lcount, lcountUE, lcountUEk, lcountUS). RETURN (lcount, lcountUE, lcountUEk + 1, lcountUS))\<close>
  by (auto simp: clss_size_incr_lcountUEk_def)

sepref_def clss_size_incr_lcountUEk_fast_code
  is \<open>RETURN o clss_size_incr_lcountUEk\<close>
  :: \<open>[\<lambda>S. clss_size_lcountUEk S < uint64_max]\<^sub>a lcount_assn\<^sup>d \<rightarrow> lcount_assn\<close>
  unfolding clss_size_incr_lcountUEk_alt_def lcount_assn_def clss_size_lcountUEk_def
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
  \<open>RETURN o clss_size_lcountUS = (\<lambda>(lcount, lcountUE, lcountUEk, lcountUS, lcountU0). RETURN lcountUS)\<close>
  by (auto simp: clss_size_lcountUS_def)

sepref_def clss_size_lcountUSt_fast_code
  is \<open>RETURN o clss_size_lcountUS\<close>
  :: \<open>lcount_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  unfolding lcount_assn_def clss_size_lcountUS_alt_def clss_size_lcount_def
  by sepref

lemma clss_size_lcountU0_alt_def:
  \<open>RETURN o clss_size_lcountU0 = (\<lambda>(lcount, lcountUE, lcountUEk, lcountUS, lcountU0). RETURN lcountU0)\<close>
  by (auto simp: clss_size_lcountU0_def)

sepref_def clss_size_lcountU0_fast_code
  is \<open>RETURN o clss_size_lcountU0\<close>
  :: \<open>lcount_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  unfolding lcount_assn_def clss_size_lcountU0_alt_def clss_size_lcount_def
  by sepref

lemma clss_size_incr_allcount_alt_def:
  \<open>RETURN o clss_size_allcount =
  (\<lambda>(lcount, lcountUE, lcountUEk, lcountUS, lcountU0). RETURN (lcount + lcountUE + lcountUEk + lcountUS + lcountU0))\<close>
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
   (phase_saver_assn \<times> 64 word \<times> phase_saver'_assn \<times> 64 word \<times> phase_saver'_assn \<times> 64 word \<times> 64 word \<times> 64 word) \<times> reluctant_rel_assn \<times> 1 word)\<close>

definition heuristic_int_assn :: \<open>restart_heuristics \<Rightarrow> heur_assn \<Rightarrow> assn\<close> where
  \<open>heuristic_int_assn = ema_assn \<times>\<^sub>a
  ema_assn \<times>\<^sub>a
  restart_info_assn \<times>\<^sub>a
  word64_assn \<times>\<^sub>a phase_heur_assn \<times>\<^sub>a reluctant_assn \<times>\<^sub>a bool1_assn\<close>

abbreviation heur_int_rel :: \<open>(restart_heuristics \<times> restart_heuristics) set\<close> where
  \<open>heur_int_rel \<equiv> Id\<close>

abbreviation heur_rel :: \<open>(restart_heuristics \<times> isasat_restart_heuristics) set\<close> where
  \<open>heur_rel \<equiv> \<langle>heur_int_rel\<rangle>code_hider_rel\<close>

definition heuristic_assn :: \<open>isasat_restart_heuristics \<Rightarrow> _ \<Rightarrow> assn\<close> where
  \<open>heuristic_assn = code_hider_assn heuristic_int_assn heur_int_rel\<close>

lemma heuristic_assn_alt_def:
  \<open>heuristic_assn = hr_comp heuristic_int_assn heur_rel\<close>
  unfolding heuristic_assn_def code_hider_assn_def by auto

context
  notes [fcomp_norm_unfold] = heuristic_assn_def[symmetric] heuristic_assn_alt_def[symmetric]
begin

lemma set_zero_wasted_stats_set_zero_wasted_stats:
  \<open>(set_zero_wasted_stats, set_zero_wasted) \<in> heur_rel \<rightarrow> heur_rel\<close> and
  heuristic_reluctant_tick_stats_heuristic_reluctant_tick:
  \<open>(heuristic_reluctant_tick_stats, heuristic_reluctant_tick) \<in> heur_rel \<rightarrow> heur_rel\<close> and
  heuristic_reluctant_enable_stats_heuristic_reluctant_enable:
  \<open>(heuristic_reluctant_enable_stats,heuristic_reluctant_enable) \<in> heur_rel \<rightarrow> heur_rel\<close> and
  heuristic_reluctant_disable_stats_heuristic_reluctant_disable:
  \<open>(heuristic_reluctant_disable_stats,heuristic_reluctant_disable) \<in> heur_rel \<rightarrow> heur_rel\<close> and
  heuristic_reluctant_triggered_stats_heuristic_reluctant_triggered:
  \<open>(heuristic_reluctant_triggered_stats,heuristic_reluctant_triggered) \<in> heur_rel \<rightarrow> heur_rel \<times>\<^sub>f bool_rel\<close> and
  heuristic_reluctant_triggered2_stats_heuristic_reluctant_triggered2:
  \<open>(heuristic_reluctant_triggered2_stats,heuristic_reluctant_triggered2) \<in> heur_rel \<rightarrow> bool_rel\<close> and
  heuristic_reluctant_untrigger_stats_heuristic_reluctant_untrigger:
  \<open>(heuristic_reluctant_untrigger_stats, heuristic_reluctant_untrigger) \<in> heur_rel \<rightarrow> heur_rel\<close> and
  end_of_rephasing_phase_heur_stats_end_of_rephasing_phase_heur:
  \<open>(end_of_rephasing_phase_heur_stats, end_of_rephasing_phase_heur) \<in> heur_rel \<rightarrow> word64_rel\<close> and
  is_fully_propagated_heur_stats_is_fully_propagated_heur:
  \<open>(is_fully_propagated_heur_stats, is_fully_propagated_heur) \<in> heur_rel \<rightarrow> bool_rel\<close> and
  set_fully_propagated_heur_stats_set_fully_propagated_heur:
    \<open>(set_fully_propagated_heur_stats, set_fully_propagated_heur) \<in> heur_rel \<rightarrow> heur_rel\<close>and
  unset_fully_propagated_heur_stats_unset_fully_propagated_heur:
  \<open>(unset_fully_propagated_heur_stats, unset_fully_propagated_heur) \<in> heur_rel \<rightarrow> heur_rel\<close> and
  restart_info_restart_done_heur_stats_restart_info_restart_done_heur:
  \<open>(restart_info_restart_done_heur_stats, restart_info_restart_done_heur) \<in> heur_rel \<rightarrow> heur_rel\<close> and
  set_zero_wasted_stats_set_zero_wasted:
  \<open>(set_zero_wasted_stats, set_zero_wasted) \<in> heur_rel \<rightarrow> heur_rel\<close> and
  wasted_of_stats_wasted_of:
  \<open>(wasted_of_stats, wasted_of) \<in> heur_rel \<rightarrow> word64_rel\<close> and
  slow_ema_of_stats_slow_ema_of:
  \<open>(slow_ema_of_stats, slow_ema_of) \<in> heur_rel \<rightarrow> ema_rel\<close> and
  fast_ema_of_stats_fast_ema_of:
  \<open>(fast_ema_of_stats, fast_ema_of) \<in> heur_rel \<rightarrow> ema_rel\<close> and
  current_restart_phase_stats_current_restart_phase:
  \<open>(current_restart_phase_stats, current_restart_phase) \<in> heur_rel \<rightarrow> word_rel\<close> and
  incr_wasted_stats_incr_wasted:
  \<open>(incr_wasted_stats, incr_wasted) \<in> word_rel \<rightarrow> heur_rel \<rightarrow> heur_rel\<close> and
  current_rephasing_phase_stats_current_rephasing_phase:
  \<open>(current_rephasing_phase_stats, current_rephasing_phase) \<in> heur_rel \<rightarrow> word_rel\<close> and
  get_next_phase_heur_stats_get_next_phase_heur:
  \<open>(uncurry2 (get_next_phase_heur_stats), uncurry2 (get_next_phase_heur))
  \<in> Id \<times>\<^sub>f Id \<times>\<^sub>f heur_rel \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close> and
  get_conflict_count_since_last_restart_stats_get_conflict_count_since_last_restart_stats:
  \<open>(get_conflict_count_since_last_restart_stats, get_conflict_count_since_last_restart)
  \<in> heur_rel \<rightarrow> word_rel\<close>
  by (auto simp: set_zero_wasted_def code_hider_rel_def heuristic_reluctant_tick_def
    heuristic_reluctant_enable_def heuristic_reluctant_triggered_def apfst_def map_prod_def
    heuristic_reluctant_disable_def heuristic_reluctant_triggered2_def is_fully_propagated_heur_def
    end_of_rephasing_phase_heur_def unset_fully_propagated_heur_def restart_info_restart_done_heur_def
    heuristic_reluctant_untrigger_def set_fully_propagated_heur_def wasted_of_def get_next_phase_heur_def
    slow_ema_of_def fast_ema_of_def current_restart_phase_def incr_wasted_def current_rephasing_phase_def
    get_conflict_count_since_last_restart_def
    intro!: frefI nres_relI
    split: prod.splits)

(*heuristic_reluctant_triggered*)
lemma set_zero_wasted_stats_alt_def:
   \<open>set_zero_wasted_stats= (\<lambda>(fast_ema, slow_ema, res_info, wasted, \<phi>).
    (fast_ema, slow_ema, res_info, 0, \<phi>))\<close>
 by auto

sepref_def set_zero_wasted_stats_impl
  is \<open>RETURN o set_zero_wasted_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_int_assn\<close>
  unfolding heuristic_int_assn_def set_zero_wasted_stats_alt_def
  by sepref

sepref_def heuristic_reluctant_tick_stats_impl
  is \<open>RETURN o heuristic_reluctant_tick_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_int_assn\<close>
  unfolding heuristic_int_assn_def heuristic_reluctant_tick_stats_def
  by sepref

sepref_def heuristic_reluctant_enable_stats_impl
  is \<open>RETURN o heuristic_reluctant_enable_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_int_assn\<close>
  unfolding heuristic_int_assn_def heuristic_reluctant_enable_stats_def
  by sepref

sepref_def heuristic_reluctant_disable_stats_impl
  is \<open>RETURN o heuristic_reluctant_disable_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_int_assn\<close>
  unfolding heuristic_int_assn_def heuristic_reluctant_disable_stats_def
  by sepref

sepref_def heuristic_reluctant_triggered_stats_impl
  is \<open>RETURN o heuristic_reluctant_triggered_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_int_assn \<times>\<^sub>a bool1_assn\<close>
  unfolding heuristic_reluctant_triggered_stats_def heuristic_int_assn_def
  by sepref

sepref_def heuristic_reluctant_triggered2_stats_impl
  is \<open>RETURN o heuristic_reluctant_triggered2_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding heuristic_reluctant_triggered2_stats_def heuristic_int_assn_def
  by sepref


sepref_def heuristic_reluctant_untrigger_stats_impl
  is \<open>RETURN o heuristic_reluctant_untrigger_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_int_assn\<close>
  unfolding heuristic_int_assn_def heuristic_reluctant_untrigger_stats_def
  by sepref


sepref_def end_of_rephasing_phase_impl [llvm_inline]
  is \<open>RETURN o end_of_rephasing_phase\<close>
  :: \<open>phase_heur_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding end_of_rephasing_phase_def phase_heur_assn_def
  by sepref

sepref_def end_of_rephasing_phase_heur_stats_impl
  is \<open>RETURN o end_of_rephasing_phase_heur_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding heuristic_int_assn_def end_of_rephasing_phase_heur_stats_def
  by sepref

sepref_def is_fully_propagated_heur_stats_impl
  is \<open>RETURN o is_fully_propagated_heur_stats\<close>
  ::  \<open>heuristic_int_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding heuristic_int_assn_def is_fully_propagated_heur_stats_def
  by sepref

sepref_def set_fully_propagated_heur_stats_impl
  is \<open>RETURN o set_fully_propagated_heur_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_int_assn\<close>
  unfolding heuristic_int_assn_def set_fully_propagated_heur_stats_def
  by sepref

sepref_def unset_fully_propagated_heur_stats_impl
  is \<open>RETURN o unset_fully_propagated_heur_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_int_assn\<close>
  unfolding heuristic_int_assn_def unset_fully_propagated_heur_stats_def
  by sepref
 
sepref_def restart_info_restart_done_heur_stats_impl
  is \<open>RETURN o restart_info_restart_done_heur_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_int_assn\<close>
  unfolding heuristic_int_assn_def restart_info_restart_done_heur_stats_def
  by sepref

sepref_def set_zero_wasted_impl
  is \<open>RETURN o set_zero_wasted_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_int_assn\<close>
  unfolding heuristic_int_assn_def set_zero_wasted_stats_alt_def
  by sepref

lemma wasted_of_stats_alt_def:
  \<open>RETURN o wasted_of_stats = (\<lambda>(fast_ema, slow_ema, res_info, wasted, \<phi>). RETURN wasted)\<close>
  by auto

sepref_def wasted_of_stats_impl
  is \<open>RETURN o wasted_of_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding heuristic_int_assn_def wasted_of_stats_alt_def
  by sepref

lemma slow_ema_of_stats_alt_def:
  \<open>RETURN o slow_ema_of_stats = (\<lambda>(fast_ema, slow_ema, res_info, wasted, \<phi>). RETURN slow_ema)\<close> and
  fast_ema_of_stats_alt_def:
  \<open>RETURN o fast_ema_of_stats = (\<lambda>(fast_ema, slow_ema, res_info, wasted, \<phi>). RETURN fast_ema)\<close>
  by auto

sepref_def slow_ema_of_stats_impl
  is \<open>RETURN o slow_ema_of_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  unfolding heuristic_int_assn_def slow_ema_of_stats_alt_def
  by sepref

sepref_def fast_ema_of_stats_impl
  is \<open>RETURN o fast_ema_of_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  unfolding heuristic_int_assn_def fast_ema_of_stats_alt_def
  by sepref

lemma current_restart_phase_stats_alt_def:
  \<open>RETURN o current_restart_phase_stats =
  (\<lambda>(fast_ema, slow_ema, (ccount, ema_lvl, restart_phase, end_of_phase), wasted, \<phi>). RETURN restart_phase)\<close>
  by auto

sepref_def current_restart_phase_impl
  is \<open>RETURN o current_restart_phase_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding heuristic_int_assn_def current_restart_phase_stats_alt_def
  by sepref

lemma incr_wasted_stats_stats_alt_def:
  \<open>RETURN oo incr_wasted_stats =
  (\<lambda>waste (fast_ema, slow_ema, res_info, wasted, \<phi>). RETURN (fast_ema, slow_ema, res_info, wasted + waste, \<phi>))\<close>
  by (auto intro!: ext)

sepref_def incr_wasted_stats_impl
  is \<open>uncurry (RETURN oo incr_wasted_stats)\<close>
  :: \<open>word64_assn\<^sup>k *\<^sub>a heuristic_int_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_int_assn\<close>
  unfolding heuristic_int_assn_def incr_wasted_stats_stats_alt_def
  by sepref

sepref_def current_rephasing_phase_stats_impl
  is \<open>RETURN o current_rephasing_phase_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding heuristic_int_assn_def current_rephasing_phase_stats_def
    phase_current_rephasing_phase_def phase_heur_assn_def
  by sepref

sepref_def get_next_phase_heur_stats_impl
  is \<open>uncurry2 get_next_phase_heur_stats\<close>
  :: \<open>bool1_assn\<^sup>k *\<^sub>a atom_assn\<^sup>k *\<^sub>a heuristic_int_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding get_next_phase_heur_stats_def heuristic_int_assn_def
  by sepref

lemma get_conflict_count_since_last_restart_stats_alt_def:
  \<open>get_conflict_count_since_last_restart_stats =
  (\<lambda>(fast_ema, slow_ema, (ccount, ema_lvl, restart_phase, end_of_phase), wasted, \<phi>). ccount)\<close>
  by auto

sepref_def get_conflict_count_since_last_restart_stats_impl
  is \<open>RETURN o get_conflict_count_since_last_restart_stats\<close>
  :: \<open>heuristic_int_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding get_conflict_count_since_last_restart_stats_alt_def heuristic_int_assn_def
  by sepref
  
lemma hn_id_pure:
  \<open>CONSTRAINT is_pure A \<Longrightarrow> (Mreturn, RETURN o id) \<in> A\<^sup>k \<rightarrow>\<^sub>a A\<close>
  apply sepref_to_hoare
  apply vcg
  apply (auto simp: ENTAILS_def is_pure_conv pure_def)
  by (smt (z3) entails_def entails_lift_extract_simps(1) pure_true_conv sep_conj_empty')

lemmas [sepref_fr_rules] =
  set_zero_wasted_stats_impl.refine[FCOMP set_zero_wasted_stats_set_zero_wasted_stats]
  heuristic_reluctant_tick_stats_impl.refine[FCOMP heuristic_reluctant_tick_stats_heuristic_reluctant_tick]
  heuristic_reluctant_enable_stats_impl.refine[FCOMP heuristic_reluctant_enable_stats_heuristic_reluctant_enable]
  heuristic_reluctant_disable_stats_impl.refine[FCOMP heuristic_reluctant_disable_stats_heuristic_reluctant_disable]
  heuristic_reluctant_triggered_stats_impl.refine[FCOMP heuristic_reluctant_triggered_stats_heuristic_reluctant_triggered]
  heuristic_reluctant_triggered2_stats_impl.refine[FCOMP heuristic_reluctant_triggered2_stats_heuristic_reluctant_triggered2]
  heuristic_reluctant_untrigger_stats_impl.refine[FCOMP heuristic_reluctant_untrigger_stats_heuristic_reluctant_untrigger]
  end_of_rephasing_phase_heur_stats_impl.refine[FCOMP end_of_rephasing_phase_heur_stats_end_of_rephasing_phase_heur]
  is_fully_propagated_heur_stats_impl.refine[FCOMP is_fully_propagated_heur_stats_is_fully_propagated_heur]
  set_fully_propagated_heur_stats_impl.refine[FCOMP set_fully_propagated_heur_stats_set_fully_propagated_heur]
  unset_fully_propagated_heur_stats_impl.refine[FCOMP unset_fully_propagated_heur_stats_unset_fully_propagated_heur]
  restart_info_restart_done_heur_stats_impl.refine[FCOMP restart_info_restart_done_heur_stats_restart_info_restart_done_heur]
  set_zero_wasted_impl.refine[FCOMP set_zero_wasted_stats_set_zero_wasted]
  wasted_of_stats_impl.refine[FCOMP wasted_of_stats_wasted_of]
  current_restart_phase_impl.refine[FCOMP current_restart_phase_stats_current_restart_phase]
  slow_ema_of_stats_impl.refine[FCOMP slow_ema_of_stats_slow_ema_of]
  fast_ema_of_stats_impl.refine[FCOMP fast_ema_of_stats_fast_ema_of]
  incr_wasted_stats_impl.refine[FCOMP incr_wasted_stats_incr_wasted]
  current_rephasing_phase_stats_impl.refine[FCOMP current_rephasing_phase_stats_current_rephasing_phase]
  get_next_phase_heur_stats_impl.refine[FCOMP get_next_phase_heur_stats_get_next_phase_heur]
  get_conflict_count_since_last_restart_stats_impl.refine[FCOMP get_conflict_count_since_last_restart_stats_get_conflict_count_since_last_restart_stats]
  hn_id[of heuristic_int_assn, FCOMP get_content_hnr[of heur_int_rel]]
  hn_id[of heuristic_int_assn, FCOMP Constructor_hnr[of heur_int_rel]]

lemmas get_restart_heuristics_pure_rule =
  hn_id_pure[of heuristic_int_assn, FCOMP get_content_hnr[of heur_int_rel]]

end


sepref_register set_zero_wasted_stats save_phase_heur_stats heuristic_reluctant_tick_stats
  heuristic_reluctant_tick is_fully_propagated_heur_stats get_content


lemma mop_save_phase_heur_stats_alt_def:
  \<open>mop_save_phase_heur_stats = (\<lambda> L b (fast_ema, slow_ema, res_info, wasted, (\<phi>, target, best), rel). do {
    ASSERT(L < length \<phi>);
    RETURN (fast_ema, slow_ema, res_info, wasted, (\<phi>[L := b], target,
                 best), rel)})\<close>
  unfolding mop_save_phase_heur_stats_def save_phase_heur_def save_phase_heur_pre_stats_def save_phase_heur_stats_def
  by (auto intro!: ext)

sepref_def mop_save_phase_heur_stats_impl
  is \<open>uncurry2 (mop_save_phase_heur_stats)\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a heuristic_int_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_int_assn\<close>
  supply [[goals_limit=1]]
  unfolding mop_save_phase_heur_stats_alt_def save_phase_heur_stats_def save_phase_heur_pre_stats_def
    phase_heur_assn_def mop_save_phase_heur_def heuristic_int_assn_def
  apply annot_all_atm_idxs
  by sepref

lemma mop_save_phase_heur_alt_def:
  \<open>mop_save_phase_heur L b S = do {
  let S = get_restart_heuristics S;
  S \<leftarrow> mop_save_phase_heur_stats L b S;
  RETURN (Restart_Heuristics S)
    }\<close>
    unfolding Let_def mop_save_phase_heur_def mop_save_phase_heur_def save_phase_heur_def
      mop_save_phase_heur_stats_def save_phase_heur_pre_def
  by auto

sepref_def mop_save_phase_heur_impl
  is \<open>uncurry2 (mop_save_phase_heur)\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a heuristic_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_assn\<close>
  supply [[goals_limit=1]]
  unfolding mop_save_phase_heur_alt_def save_phase_heur_def save_phase_heur_pre_def
    phase_heur_assn_def mop_save_phase_heur_def
  apply annot_all_atm_idxs
  by sepref

schematic_goal mk_free_heuristic_int_assn[sepref_frame_free_rules]: \<open>MK_FREE heuristic_int_assn ?fr\<close>
  unfolding heuristic_int_assn_def code_hider_assn_def
  by synthesize_free

schematic_goal mk_free_heuristic_assn[sepref_frame_free_rules]: \<open>MK_FREE heuristic_assn ?fr\<close>
  unfolding heuristic_assn_def code_hider_assn_def
  by synthesize_free

lemma [safe_constraint_rules]: \<open>CONSTRAINT is_pure A \<Longrightarrow> CONSTRAINT is_pure (code_hider_assn A B)\<close>
  unfolding code_hider_assn_def by (auto simp: hr_comp_is_pure)


lemma clss_size_incr_lcount_alt_def:
  \<open>RETURN o clss_size_incr_lcount =
  (\<lambda>(lcount,  lcountUE, lcountUS). RETURN (lcount + 1, lcountUE, lcountUS))\<close>
  by (auto simp: clss_size_incr_lcount_def)

lemma clss_size_lcountUEk_alt_def:
  \<open>RETURN o clss_size_lcountUEk = (\<lambda>(lcount, lcountUE, lcountUEk, lcountUS). RETURN lcountUEk)\<close>
  by (auto simp: clss_size_lcountUEk_def)

sepref_def clss_size_lcountUEk_fast_code
  is \<open>RETURN o clss_size_lcountUEk\<close>
  :: \<open>lcount_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  unfolding lcount_assn_def clss_size_lcountUEk_alt_def clss_size_lcount_def
  by sepref

sepref_register clss_size_incr_lcount
sepref_def clss_size_incr_lcount_fast_code
  is \<open>RETURN o clss_size_incr_lcount\<close>
  :: \<open>[\<lambda>S. clss_size_lcount S \<le> max_snat 64]\<^sub>a lcount_assn\<^sup>d \<rightarrow> lcount_assn\<close>
  unfolding clss_size_incr_lcount_alt_def lcount_assn_def clss_size_lcount_def
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_register unset_fully_propagated_heur is_fully_propagated_heur set_fully_propagated_heur

end
