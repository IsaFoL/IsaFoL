theory IsaSAT_Setup3_LLVM
  imports IsaSAT_Setup IsaSAT_Watch_List_LLVM IsaSAT_Lookup_Conflict_LLVM
    More_Sepref.WB_More_Refinement IsaSAT_Clauses_LLVM LBD_LLVM
    IsaSAT_Options_LLVM IsaSAT_VMTF_Setup_LLVM
    IsaSAT_Arena_Sorting_LLVM
    IsaSAT_Rephase_LLVM
    IsaSAT_EMA_LLVM
    IsaSAT_Stats_LLVM
    IsaSAT_Setup0_LLVM
begin

sepref_def wasted_bytes_st_impl
  is \<open>RETURN o wasted_bytes_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_bounded_assn_def wasted_bytes_st_def
  by sepref


sepref_register set_zero_wasted mop_save_phase_heur add_lbd


sepref_register isa_trail_nth isasat_trail_nth_st

sepref_def isasat_trail_nth_st_code
  is \<open>uncurry isasat_trail_nth_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a unat_lit_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_trail_nth_st_alt_def isasat_bounded_assn_def
  by sepref


sepref_def lit_of_hd_trail_st_heur_fast_code
  is \<open>lit_of_hd_trail_st_heur\<close>
  :: \<open>[\<lambda>S. True]\<^sub>a isasat_bounded_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  unfolding lit_of_hd_trail_st_heur_alt_def isasat_bounded_assn_def
  by sepref

sepref_def heuristic_reluctant_triggered2_st_impl
  is \<open>RETURN o heuristic_reluctant_triggered2_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding heuristic_reluctant_triggered2_st_def isasat_bounded_assn_def
  by sepref

sepref_def heuristic_reluctant_untrigger_st_impl
  is \<open>RETURN o heuristic_reluctant_untrigger_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding heuristic_reluctant_untrigger_st_def isasat_bounded_assn_def
    fold_tuple_optimizations
  by sepref


sepref_register incr_restart_stat


sepref_register clss_size_lcountUE clss_size_lcountUS learned_clss_count clss_size_allcount

sepref_def incr_restart_stat_fast_code
  is \<open>incr_restart_stat\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding incr_restart_stat_def isasat_bounded_assn_def PR_CONST_def fold_tuple_optimizations
  by sepref

sepref_register incr_lrestart_stat clss_size_decr_lcount
    clss_size_incr_lcountUE clss_size_incr_lcountUS

sepref_def incr_lrestart_stat_fast_code
  is \<open>incr_lrestart_stat\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding incr_lrestart_stat_def isasat_bounded_assn_def PR_CONST_def
    fold_tuple_optimizations
  by sepref

sepref_register mark_unused_st_heur
sepref_def mark_unused_st_fast_code
  is \<open>uncurry (RETURN oo mark_unused_st_heur)\<close>
  :: \<open>[\<lambda>(C, S). arena_act_pre (get_clauses_wl_heur S) C]\<^sub>a
        sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding mark_unused_st_heur_def isasat_bounded_assn_def
    arena_act_pre_mark_used[intro!] fold_tuple_optimizations
  supply [[goals_limit = 1]]
  by sepref

sepref_def mop_mark_unused_st_heur_impl
  is \<open>uncurry mop_mark_unused_st_heur\<close>
  :: \<open> sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding mop_mark_unused_st_heur_def fold_tuple_optimizations
  by sepref


sepref_register get_the_propagation_reason_pol_st

sepref_def get_the_propagation_reason_pol_st_code
  is \<open>uncurry get_the_propagation_reason_pol_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a snat_option_assn' TYPE(64)\<close>
  supply [[goals_limit=1]]
  unfolding get_the_propagation_reason_pol_st_alt_def isasat_bounded_assn_def
  by sepref

sepref_def empty_US_heur_code
  is \<open>RETURN o empty_US_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding empty_US_heur_def isasat_bounded_assn_def
  by sepref

sepref_def get_restart_phase_imp
  is \<open>(RETURN o get_restart_phase)\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding get_restart_phase_def isasat_bounded_assn_def
  by sepref

sepref_register mark_garbage_heur2 mark_garbage_heur4
sepref_def mark_garbage_heur2_code
  is \<open>uncurry mark_garbage_heur2\<close>
  :: \<open>[\<lambda>(C, S). mark_garbage_pre (get_clauses_wl_heur S, C) \<and> arena_is_valid_clause_vdom (get_clauses_wl_heur S) C]\<^sub>a
     sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding mark_garbage_heur2_def isasat_bounded_assn_def
    fold_tuple_optimizations
  by sepref

sepref_def mark_garbage_heur4_code
  is \<open>uncurry mark_garbage_heur4\<close>
  :: \<open>[\<lambda>(C, S). mark_garbage_pre (get_clauses_wl_heur S, C) \<and> arena_is_valid_clause_vdom (get_clauses_wl_heur S) C \<and>
        learned_clss_count S \<le> uint64_max]\<^sub>a
     sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]] isasat_fast_countD[dest] learned_clss_count_def[simp]
  unfolding mark_garbage_heur4_def isasat_bounded_assn_def
    fold_tuple_optimizations
  by sepref

sepref_def access_avdom_at_fast_code
  is \<open>uncurry (RETURN oo access_avdom_at)\<close>
  :: \<open>[uncurry access_avdom_at_pre]\<^sub>a isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> sint64_nat_assn\<close>
  unfolding access_avdom_at_alt_def access_avdom_at_pre_def isasat_bounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

sepref_def access_ivdom_at_fast_code
  is \<open>uncurry (RETURN oo access_ivdom_at)\<close>
  :: \<open>[uncurry access_ivdom_at_pre]\<^sub>a isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> sint64_nat_assn\<close>
  unfolding access_ivdom_at_alt_def access_ivdom_at_pre_def isasat_bounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

sepref_register mop_access_lit_in_clauses_heur mop_watched_by_app_heur
  get_target_opts get_opts

sepref_def mop_access_lit_in_clauses_heur_impl
  is \<open>uncurry2 mop_access_lit_in_clauses_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a unat_lit_assn\<close>
  supply [[goals_limit=1]]
  unfolding mop_access_lit_in_clauses_heur_alt_def isasat_bounded_assn_def
  by sepref

lemma get_opts_alt_def:
  \<open>get_opts = (\<lambda>(_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, opts, _). opts)\<close>
  by (auto intro!: ext)

sepref_def get_opts_impl
  is \<open>RETURN o get_opts\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a opts_assn\<close>
  unfolding get_opts_alt_def isasat_bounded_assn_def
  by sepref

sepref_def get_target_opts_impl
  is \<open>RETURN o get_target_opts\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a word_assn' TYPE(3)\<close>
  unfolding get_target_opts_def
  by sepref

sepref_register print_literal_of_trail
    print_trail print_trail_st print_trail_st2

sepref_def print_literal_of_trail_code
  is print_literal_of_trail
  :: \<open>unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_literal_of_trail_def
  by sepref

sepref_def print_encoded_lit_end_code
  is print_literal_of_trail
  :: \<open>uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_literal_of_trail_def
  by sepref

sepref_def print_trail_code
  is \<open>print_trail\<close>
  :: \<open>trail_pol_fast_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_trail_def trail_pol_fast_assn_def
  apply (rewrite at \<open>print_literal_of_trail (\<hole>)\<close> unat_const_fold[where 'a=32])
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

lemmas print_trail[sepref_fr_rules] =
  print_trail_code.refine[FCOMP print_trail_print_trail2_rel[unfolded convert_fref],
  unfolded trail_pol_fast_assn_def]
sepref_register print_trail2

sepref_def print_trail_st_code
  is \<open>print_trail_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_trail_st_def isasat_bounded_assn_def
    fold_tuple_optimizations
  by sepref

lemmas [sepref_fr_rules] =
  print_trail_st_code.refine[FCOMP print_trail_st_print_trail_st2_rel[unfolded convert_fref]]

sepref_register is_fully_propagated_heur_st

sepref_def is_fully_propagated_heur_st_code
  is \<open>RETURN o is_fully_propagated_heur_st\<close>
  ::  \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding is_fully_propagated_heur_st_def isasat_bounded_assn_def
    fold_tuple_optimizations
  by sepref

end