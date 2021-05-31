theory IsaSAT_Restart_Heuristics_LLVM
  imports IsaSAT_Restart_Heuristics IsaSAT_Setup_LLVM
     IsaSAT_VMTF_State_LLVM IsaSAT_Rephase_State_LLVM
     IsaSAT_Arena_Sorting_LLVM
     IsaSAT_Restart_Reduce_LLVM
     IsaSAT_Inprocessing_LLVM
begin

hide_fact (open) Sepref_Rules.frefI
no_notation Sepref_Rules.fref (\<open>[_]\<^sub>f\<^sub>d _ \<rightarrow> _\<close> [0,60,60] 60)
no_notation Sepref_Rules.freft (\<open>_ \<rightarrow>\<^sub>f\<^sub>d _\<close> [60,60] 60)
no_notation Sepref_Rules.freftnd (\<open>_ \<rightarrow>\<^sub>f _\<close> [60,60] 60)
no_notation Sepref_Rules.frefnd (\<open>[_]\<^sub>f _ \<rightarrow> _\<close> [0,60,60] 60)

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

sepref_def end_of_restart_phase_impl
  is \<open>RETURN o end_of_restart_phase\<close>
  :: \<open>heuristic_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding end_of_restart_phase_def heuristic_assn_def
  by sepref

sepref_def end_of_restart_phase_st_impl
  is \<open>RETURN o end_of_restart_phase_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding end_of_restart_phase_st_def isasat_bounded_assn_def
  by sepref

sepref_def end_of_rephasing_phase_impl
  is \<open>RETURN o end_of_rephasing_phase\<close>
  :: \<open>phase_heur_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding end_of_rephasing_phase_def phase_heur_assn_def
  by sepref

sepref_def end_of_rephasing_phase_heur_impl
  is \<open>RETURN o end_of_rephasing_phase_heur\<close>
  :: \<open>heuristic_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding end_of_rephasing_phase_heur_def heuristic_assn_def
  by sepref

sepref_def end_of_rephasing_phase_st_impl
  is \<open>RETURN o end_of_rephasing_phase_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding end_of_rephasing_phase_st_def isasat_bounded_assn_def
  by sepref

lemma incr_restart_phase_end_alt_def:
  \<open>incr_restart_phase_end = (\<lambda>(fast_ema, slow_ema,
    (ccount, ema_lvl, restart_phase, end_of_phase, length_phase), wasted).
    (fast_ema, slow_ema, (ccount, ema_lvl, restart_phase, end_of_phase + length_phase,
      (length_phase * 3) >> 1), wasted))\<close>
  by auto

sepref_def incr_restart_phase_end_impl
  is \<open>RETURN o incr_restart_phase_end\<close>
  :: \<open>heuristic_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_assn\<close>
  supply[[goals_limit=1]]
  unfolding heuristic_assn_def incr_restart_phase_end_alt_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref


lemma incr_restart_phase_alt_def:
  \<open>incr_restart_phase = (\<lambda>(fast_ema, slow_ema,
    (ccount, ema_lvl, restart_phase, end_of_phase), wasted).
     (fast_ema, slow_ema, (ccount, ema_lvl, restart_phase XOR 1, end_of_phase), wasted))\<close>
  by auto

sepref_def incr_restart_phase_impl
  is \<open>RETURN o incr_restart_phase\<close>
  :: \<open>heuristic_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_assn\<close>
  unfolding heuristic_assn_def incr_restart_phase_alt_def
  by sepref

sepref_register incr_restart_phase incr_restart_phase_end
  update_restart_phases

sepref_def update_restart_phases_impl
  is \<open>update_restart_phases\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding update_restart_phases_def isasat_bounded_assn_def
    fold_tuple_optimizations
  by sepref

sepref_register upper_restart_bound_not_reached

sepref_def upper_restart_bound_not_reached_fast_impl
  is \<open>(RETURN o upper_restart_bound_not_reached)\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding upper_restart_bound_not_reached_def PR_CONST_def isasat_bounded_assn_def
    fold_tuple_optimizations
  supply [[goals_limit = 1]]
  by sepref

sepref_register lower_restart_bound_not_reached
sepref_def lower_restart_bound_not_reached_impl
  is \<open>(RETURN o lower_restart_bound_not_reached)\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding lower_restart_bound_not_reached_def PR_CONST_def isasat_bounded_assn_def
    fold_tuple_optimizations
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

sepref_def get_reductions_count_fast_code
  is \<open>RETURN o get_reductions_count\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding get_reduction_count_alt_def isasat_bounded_assn_def
  by sepref

sepref_register get_reductions_count


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

sepref_register ema_get_value get_fast_ema_heur get_slow_ema_heur

sepref_def restart_required_heur_fast_code
  is \<open>uncurry3 restart_required_heur\<close>
  :: \<open>[\<lambda>(((S, _), _), _). learned_clss_count S \<le> uint64_max]\<^sub>a isasat_bounded_assn\<^sup>k *\<^sub>a
     uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> word_assn\<close>
  supply [[goals_limit=1]] isasat_fast_def[simp] clss_size_allcount_alt_def[simp]
    learned_clss_count_def[simp]
  unfolding restart_required_heur_def
  apply (rewrite in \<open>\<hole> < _\<close> unat_const_fold(3)[where 'a=32])
  apply (rewrite in \<open>(_ >> 32) < \<hole>\<close> annot_unat_unat_upcast[where 'l=64])
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_register isasat_replace_annot_in_trail
sepref_def isasat_replace_annot_in_trail_code
  is \<open>uncurry2 isasat_replace_annot_in_trail\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a (sint64_nat_assn)\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_replace_annot_in_trail_def isasat_bounded_assn_def
    trail_pol_fast_assn_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  apply (rewrite at \<open>list_update _ _ _\<close> annot_index_of_atm)
  by sepref

sepref_register remove_one_annot_true_clause_one_imp_wl_D_heur

lemma remove_one_annot_true_clause_one_imp_wl_D_heurI:
  \<open>isasat_fast b \<Longrightarrow>
       learned_clss_count xb \<le> learned_clss_count b \<Longrightarrow>
        learned_clss_count xb \<le> uint64_max\<close>
 by (auto simp: isasat_fast_def)

sepref_def remove_one_annot_true_clause_one_imp_wl_D_heur_code
  is \<open>uncurry remove_one_annot_true_clause_one_imp_wl_D_heur\<close>
  :: \<open>[\<lambda>(C, S). learned_clss_count S \<le> uint64_max]\<^sub>a
       sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> sint64_nat_assn \<times>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]] remove_one_annot_true_clause_one_imp_wl_D_heurI[intro]
  unfolding remove_one_annot_true_clause_one_imp_wl_D_heur_def
    isasat_trail_nth_st_def[symmetric] get_the_propagation_reason_pol_st_def[symmetric]
    fold_tuple_optimizations
  apply (rewrite in \<open>_ = \<hole>\<close> snat_const_fold(1)[where 'a=64])
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_register mark_clauses_as_unused_wl_D_heur remove_one_annot_true_clause_imp_wl_D_heur

lemma remove_one_annot_true_clause_imp_wl_D_heurI:
  \<open>learned_clss_count x \<le> uint64_max \<Longrightarrow>
       remove_one_annot_true_clause_imp_wl_D_heur_inv x (a1', a2') \<Longrightarrow>
       learned_clss_count a2' \<le> uint64_max\<close>
  by (auto simp: isasat_fast_def remove_one_annot_true_clause_imp_wl_D_heur_inv_def)

sepref_def remove_one_annot_true_clause_imp_wl_D_heur_code
  is \<open>remove_one_annot_true_clause_imp_wl_D_heur\<close>
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max \<and> 
          learned_clss_count S \<le> uint64_max]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]] remove_one_annot_true_clause_imp_wl_D_heurI[intro]
  unfolding remove_one_annot_true_clause_imp_wl_D_heur_def
    isasat_length_trail_st_def[symmetric] get_pos_of_level_in_trail_imp_st_def[symmetric]
  apply (rewrite at \<open>(\<hole>, _)\<close> annot_unat_snat_upcast[where 'l=64])
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref


sepref_def mark_clauses_as_unused_wl_D_heur_fast_code
  is \<open>uncurry mark_clauses_as_unused_wl_D_heur\<close>
  :: \<open>[\<lambda>(_, S). length (get_avdom S) \<le> sint64_max]\<^sub>a
    sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]] length_avdom_def[simp]
  unfolding mark_clauses_as_unused_wl_D_heur_def
    mark_unused_st_heur_def[symmetric]
    access_vdom_at_def[symmetric] length_avdom_def[symmetric]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

experiment
begin
  export_llvm restart_required_heur_fast_code
    access_vdom_at_fast_code
end

end
