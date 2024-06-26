theory IsaSAT_Restart_Heuristics_LLVM
  imports IsaSAT_Restart_Heuristics_Defs IsaSAT_Setup_LLVM
     IsaSAT_VMTF_State_LLVM IsaSAT_Rephase_State_LLVM
     IsaSAT_Arena_Sorting_LLVM
     IsaSAT_Restart_Reduce_LLVM
     IsaSAT_Inprocessing_LLVM
     IsaSAT_Proofs_LLVM
begin

hide_fact (open) Sepref_Rules.frefI

(*TODO Move*)
  (*End Move*)


sepref_def FLAG_restart_impl
  is \<open>uncurry0 (RETURN FLAG_restart)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding FLAG_restart_def
  by sepref

sepref_def FLAG_no_restart_impl
  is \<open>uncurry0 (RETURN FLAG_no_restart)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding FLAG_no_restart_def
  by sepref

sepref_def FLAG_GC_restart_impl
  is \<open>uncurry0 (RETURN FLAG_GC_restart)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding FLAG_GC_restart_def
  by sepref

sepref_def FLAG_Reduce_restart_impl
  is \<open>uncurry0 (RETURN FLAG_Reduce_restart)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding FLAG_Reduce_restart_def
  by sepref

sepref_def FLAG_Inprocess_restart_impl
  is \<open>uncurry0 (RETURN FLAG_Inprocess_restart)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding FLAG_Inprocess_restart_def
  by sepref

definition end_of_restart_phase_st_impl :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>end_of_restart_phase_st_impl = read_heur_wl_heur_code end_of_restart_phase_impl\<close>

global_interpretation end_of_restart_phase: read_heur_param_adder0 where
  f' = \<open>RETURN o end_of_restart_phase\<close> and
  f = end_of_restart_phase_impl and
  x_assn = word_assn and
  P = \<open>\<lambda>_. True\<close>
  rewrites \<open>read_heur_wl_heur (RETURN o end_of_restart_phase) = RETURN o end_of_restart_phase_st\<close> and
    \<open>read_heur_wl_heur_code end_of_restart_phase_impl = end_of_restart_phase_st_impl\<close>
  apply unfold_locales
  apply (rule end_of_restart_phase_impl_refine)
  subgoal by (auto simp: read_all_st_def end_of_restart_phase_st_def intro!: ext
    split: isasat_int_splits)
  subgoal by (auto simp: end_of_restart_phase_st_impl_def)
  done
 
definition end_of_rephasing_phase_st_impl :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>end_of_rephasing_phase_st_impl = read_heur_wl_heur_code end_of_rephasing_phase_heur_stats_impl\<close>

global_interpretation end_of_rephasing_phase: read_heur_param_adder0 where
  f' = \<open>RETURN o end_of_rephasing_phase_heur\<close> and
  f = end_of_rephasing_phase_heur_stats_impl and
  x_assn = word_assn and
  P = \<open>\<lambda>_. True\<close>
  rewrites \<open>read_heur_wl_heur (RETURN o end_of_rephasing_phase_heur) = RETURN o end_of_rephasing_phase_st\<close> and
    \<open>read_heur_wl_heur_code end_of_rephasing_phase_heur_stats_impl = end_of_rephasing_phase_st_impl\<close>
  apply unfold_locales
  apply (rule heur_refine)
  subgoal by (auto simp: read_all_st_def end_of_rephasing_phase_st_def intro!: ext
    split: isasat_int_splits)
  subgoal by (auto simp: end_of_rephasing_phase_st_impl_def)
  done


lemmas [sepref_fr_rules] = end_of_restart_phase.refine end_of_rephasing_phase.refine
lemmas [unfolded inline_direct_return_node_case, llvm_code] =
  end_of_restart_phase_st_impl_def[unfolded read_all_st_code_def]
  end_of_rephasing_phase_st_impl_def[unfolded read_all_st_code_def]

sepref_register incr_restart_phase incr_restart_phase_end
  update_restart_mode


lemma update_restart_mode_alt_def:
  \<open>update_restart_mode = (\<lambda>S. do {
     end_of_restart_phase \<leftarrow> RETURN (end_of_restart_phase_st S);
     let lcount = get_global_conflict_count S;
     let (heur, S) = extract_heur_wl_heur S;
     let (vm, S) = extract_vmtf_wl_heur S;
     let (stats, S) = extract_stats_wl_heur S;
     let init_ticks = init_phase_ticks heur;
     let curr = current_restart_phase heur;
     if init_ticks = 0 \<comment>\<open>This is still the very first phase, here the limit is given by conflicts\<close>
     then do{
       if (end_of_restart_phase \<ge> lcount) then RETURN (update_heur_wl_heur heur (update_vmtf_wl_heur vm (update_stats_wl_heur stats S)))
       else do {
          let search_ticks = (if current_restart_phase heur = STABLE_MODE then stats_ticks_stable stats else stats_ticks_focused stats);
          let ticks = stats_ticks_focused stats;
          let vm = switch_bump_heur vm;
          heur \<leftarrow> RETURN (if curr \<noteq> STABLE_MODE then heuristic_reluctant_enable heur else heuristic_reluctant_disable heur);
          heur \<leftarrow> RETURN (incr_restart_phase heur);
          heur \<leftarrow> RETURN (set_init_phase_ticks search_ticks heur);
          let lim = search_ticks + search_ticks;
          heur \<leftarrow> RETURN (incr_restart_phase_end lim heur);

          heur \<leftarrow> RETURN (swap_emas heur);
          
          let (lcount, S) = extract_lcount_wl_heur S;
          let _ = isasat_print_progress 125 curr stats lcount;
          _ \<leftarrow> RETURN (IsaSAT_Profile.stop_focused_mode);
          _ \<leftarrow> RETURN (IsaSAT_Profile.start_stable_mode);
          let _ = isasat_print_progress 93 (curr XOR 1) stats lcount;
          let stats = IsaSAT_Stats.rate_set_last_decision (get_decisions stats) stats;
          RETURN (update_heur_wl_heur heur (update_vmtf_wl_heur vm (update_stats_wl_heur stats (update_lcount_wl_heur lcount S))))
       }
     } else do { \<comment>\<open>This is still the very first phase, here the limit is given by ticks\<close>
        let search_ticks = (if current_restart_phase heur = STABLE_MODE then stats_ticks_stable stats else stats_ticks_focused stats);
        if (end_of_restart_phase \<ge> search_ticks) then RETURN (update_heur_wl_heur heur (update_vmtf_wl_heur vm (update_stats_wl_heur stats S)))
        else do {
          let vm = switch_bump_heur vm;
          heur \<leftarrow> RETURN (incr_restart_phase heur);
          heur \<leftarrow> RETURN (if curr \<noteq> STABLE_MODE then heuristic_reluctant_enable heur else heuristic_reluctant_disable heur);
          let search_ticks = (if curr = STABLE_MODE then stats_ticks_stable stats else stats_ticks_focused stats);
          let stable_number = nbstable_phase heur + 1;
          let delta = init_ticks * stable_number * stable_number;
          let lim = search_ticks + delta;
          heur \<leftarrow> RETURN (if curr = STABLE_MODE then incr_restart_phase_and_length_end lim heur else incr_restart_phase_end lim heur);
          heur \<leftarrow> RETURN (swap_emas heur);
          let (lcount2, S) = extract_lcount_wl_heur S;
          let (open, close) = (if curr = STABLE_MODE then (91, 125) else (123, 93));
          let _ = isasat_print_progress close curr stats lcount2;
          _ \<leftarrow> (if curr = STABLE_MODE then RETURN (IsaSAT_Profile.stop_stable_mode) else RETURN (IsaSAT_Profile.stop_focused_mode));
          _ \<leftarrow> (if curr = STABLE_MODE then RETURN (IsaSAT_Profile.start_focused_mode) else RETURN (IsaSAT_Profile.start_stable_mode));
          let _ = isasat_print_progress open (curr XOR 1) stats lcount2;
          let stats = IsaSAT_Stats.rate_set_last_decision (get_decisions stats) stats;
          RETURN (update_heur_wl_heur heur (update_vmtf_wl_heur vm (update_stats_wl_heur stats (update_lcount_wl_heur lcount2 S))))
      }
    }
  })\<close>
  by (auto simp: update_restart_mode_def state_extractors Let_def split: isasat_int_splits intro!: ext bind_cong[OF refl]
    cong: if_cong)

lemma update_restart_mode_conflicts_alt_def:
  \<open>update_restart_mode_conflicts = (\<lambda>S. do {
     let lcount = get_global_conflict_count S;
     let (heur, S) = extract_heur_wl_heur S;
     let curr = current_restart_phase heur;
     let (vm, S) = extract_vmtf_wl_heur S;
     let (stats, S) = extract_stats_wl_heur S;
     let vm = switch_bump_heur vm;
     heur \<leftarrow> RETURN (incr_restart_phase heur);
     heur \<leftarrow> RETURN (incr_restart_phase_end lcount heur);
     heur \<leftarrow> RETURN (if current_restart_phase heur = STABLE_MODE then heuristic_reluctant_enable heur else heuristic_reluctant_disable heur);
     _ \<leftarrow> (if curr = STABLE_MODE then RETURN (IsaSAT_Profile.stop_stable_mode) else RETURN (IsaSAT_Profile.stop_focused_mode));
     _ \<leftarrow> (if curr = STABLE_MODE then RETURN (IsaSAT_Profile.start_focused_mode) else RETURN (IsaSAT_Profile.start_stable_mode));
     let (lcount2, S) = extract_lcount_wl_heur S;
     let (open, close) = (if curr = STABLE_MODE then (91::64 word, 125::64 word) else (123, 93));
     let _ = isasat_print_progress close curr stats lcount2;
     let _ = isasat_print_progress open (curr XOR 1) stats lcount2;
     heur \<leftarrow> RETURN (swap_emas heur);
     RETURN (update_heur_wl_heur heur (update_vmtf_wl_heur vm (update_stats_wl_heur stats (update_lcount_wl_heur lcount2 S))))
  })\<close>
  by (auto simp: Let_def update_restart_mode_conflicts_def state_extractors split: isasat_int_splits intro!: ext bind_cong)

sepref_def update_restart_mode_impl
  is \<open>update_restart_mode\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_restart_mode_alt_def
  by sepref

sepref_register upper_restart_bound_reached

sepref_def upper_restart_bound_reached_fast_impl
  is \<open>(RETURN o upper_restart_bound_reached)\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding upper_restart_bound_reached_def PR_CONST_def
    fold_tuple_optimizations get_restart_count_st_def[symmetric]
    get_global_conflict_count_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref

sepref_register max_restart_decision_lvl

sepref_def minimum_number_between_restarts_impl
  is \<open>uncurry0 (RETURN minimum_number_between_restarts)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding minimum_number_between_restarts_def
  by sepref

sepref_def uint32_nat_assn_impl
  is \<open>uncurry0 (RETURN max_restart_decision_lvl)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding max_restart_decision_lvl_def
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref

sepref_def GC_required_heur_fast_code
  is \<open>uncurry GC_required_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  supply [[goals_limit=1]] of_nat_snat[sepref_import_param]
  unfolding GC_required_heur_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_def GC_units_required_heur_fast_code
  is \<open>RETURN o GC_units_required\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  supply [[goals_limit=1]] of_nat_snat[sepref_import_param]
  unfolding GC_units_required_def
  by sepref

sepref_register should_inprocess_or_unit_reduce_st

sepref_def should_inprocess_or_unit_reduce_st
  is \<open>uncurry (RETURN oo should_inprocess_or_unit_reduce_st)\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding should_inprocess_or_unit_reduce_st_def should_inprocess_st_def
  by sepref

sepref_register ema_get_value get_fast_ema_heur get_slow_ema_heur

sepref_def restart_required_heur_fast_code
  is \<open>uncurry3 restart_required_heur\<close>
  :: \<open>[\<lambda>(((S, _), _), _). learned_clss_count S \<le> unat64_max]\<^sub>a isasat_bounded_assn\<^sup>k *\<^sub>a
     uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> word_assn\<close>
  supply [[goals_limit=1]] isasat_fast_def[simp] clss_size_allcount_alt_def[simp]
    learned_clss_count_def[simp]
  unfolding restart_required_heur_def get_slow_ema_heur_st_def[symmetric]
    get_fast_ema_heur_st_def[symmetric]
  apply (rewrite in \<open>\<hole> \<le> _\<close> unat_const_fold[where 'a=32])
(* apply (rewrite in \<open>(_ >> 32) < \<hole>\<close> annot_unat_unat_upcast[where 'l=64])*)
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

lemma isasat_replace_annot_in_trail_alt_def:
  \<open>isasat_replace_annot_in_trail L C = (\<lambda>S. do {
    let (lcount, S) = extract_lcount_wl_heur S;
    let (M, S) = extract_trail_wl_heur S;
    let lcount = clss_size_resetUS0 lcount;
    M \<leftarrow> replace_reason_in_trail L C M;
    RETURN (update_trail_wl_heur M (update_lcount_wl_heur lcount S))
  })\<close>
  by (auto simp: isasat_replace_annot_in_trail_def state_extractors
        intro!: ext split: isasat_int_splits)
sepref_register isasat_replace_annot_in_trail
sepref_def isasat_replace_annot_in_trail_code
  is \<open>uncurry2 isasat_replace_annot_in_trail\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a (sint64_nat_assn)\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_replace_annot_in_trail_alt_def
  by sepref

sepref_register remove_one_annot_true_clause_one_imp_wl_D_heur

lemma remove_one_annot_true_clause_one_imp_wl_D_heurI:
  \<open>isasat_fast b \<Longrightarrow>
       learned_clss_count xb \<le> learned_clss_count b \<Longrightarrow>
        learned_clss_count xb \<le> unat64_max\<close>
 by (auto simp: isasat_fast_def)


sepref_def remove_one_annot_true_clause_one_imp_wl_D_heur_code
  is \<open>uncurry remove_one_annot_true_clause_one_imp_wl_D_heur\<close>
  :: \<open>[\<lambda>(C, S). learned_clss_count S \<le> unat64_max]\<^sub>a
       sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> sint64_nat_assn \<times>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]] remove_one_annot_true_clause_one_imp_wl_D_heurI[intro]
  unfolding remove_one_annot_true_clause_one_imp_wl_D_heur_def
    isasat_trail_nth_st_def[symmetric] get_the_propagation_reason_pol_st_def[symmetric]
    fold_tuple_optimizations
  apply (rewrite in \<open>_ = \<hole>\<close> snat_const_fold(1)[where 'a=64])
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_register remove_one_annot_true_clause_imp_wl_D_heur

lemma remove_one_annot_true_clause_imp_wl_D_heurI:
  \<open>learned_clss_count x \<le> unat64_max \<Longrightarrow>
       remove_one_annot_true_clause_imp_wl_D_heur_inv x (a1', a2') \<Longrightarrow>
       learned_clss_count a2' \<le> unat64_max\<close>
  by (auto simp: isasat_fast_def remove_one_annot_true_clause_imp_wl_D_heur_inv_def)

sepref_def remove_one_annot_true_clause_imp_wl_D_heur_code
  is \<open>remove_one_annot_true_clause_imp_wl_D_heur\<close>
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> snat64_max \<and> 
          learned_clss_count S \<le> unat64_max]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]] remove_one_annot_true_clause_imp_wl_D_heurI[intro]
  unfolding remove_one_annot_true_clause_imp_wl_D_heur_def
    isasat_length_trail_st_def[symmetric] get_pos_of_level_in_trail_imp_st_def[symmetric]
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref


sepref_register number_clss_to_keep


lemma [sepref_fr_rules]:
  \<open>(Mreturn o id, RETURN o unat) \<in> word64_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
proof -
  have [simp]: \<open>(\<lambda>s. \<exists>xa. (\<up>(xa = unat x) \<and>* \<up>(xa = unat x)) s) = \<up>True\<close>
    by (intro ext)
     (auto intro!: exI[of _ \<open>unat x\<close>] simp: pure_true_conv pure_part_pure_eq pred_lift_def
      simp flip: import_param_3)
  show ?thesis
    apply sepref_to_hoare
    apply (vcg)
    apply (auto simp: unat_rel_def unat.rel_def br_def pred_lift_def ENTAILS_def pure_true_conv simp flip: import_param_3 pure_part_def)
    done
qed

sepref_def number_clss_to_keep_fast_code
  is \<open>number_clss_to_keep_impl\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  supply [[goals_limit = 1]]
  unfolding number_clss_to_keep_impl_def length_tvdom_def[symmetric] length_tvdom_aivdom_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

lemma number_clss_to_keep_impl_number_clss_to_keep:
  \<open>(number_clss_to_keep_impl, number_clss_to_keep) \<in> Sepref_Rules.freft Id (\<lambda>_. \<langle>nat_rel\<rangle>nres_rel)\<close>
  by (auto simp: number_clss_to_keep_impl_def number_clss_to_keep_def Let_def intro!: Sepref_Rules.frefI nres_relI)

lemma number_clss_to_keep_fast_code_refine[sepref_fr_rules]:
  \<open>(number_clss_to_keep_fast_code, number_clss_to_keep) \<in> (isasat_bounded_assn)\<^sup>k \<rightarrow>\<^sub>a snat_assn\<close>
  using hfcomp[OF number_clss_to_keep_fast_code.refine
    number_clss_to_keep_impl_number_clss_to_keep, simplified]
  by auto

(*TODO Move to IsaSAT_Setup2*)
experiment
begin
  export_llvm restart_required_heur_fast_code access_avdom_at_fast_code
  trail_zeroed_until_state_fast_code
end

end
