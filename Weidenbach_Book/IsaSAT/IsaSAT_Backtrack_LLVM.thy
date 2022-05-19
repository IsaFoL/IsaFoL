theory IsaSAT_Backtrack_LLVM
  imports IsaSAT_Backtrack IsaSAT_VMTF_State_LLVM IsaSAT_Lookup_Conflict_LLVM
    IsaSAT_Rephase_State_LLVM IsaSAT_LBD_LLVM IsaSAT_Proofs_LLVM
    IsaSAT_Stats_LLVM
begin

lemma update_lbd_pre_arena_act_preD:
  \<open>update_lbd_pre ((a, ba), b) \<Longrightarrow>
  arena_act_pre (update_lbd a ba b) a\<close>
  unfolding update_lbd_pre_def arena_act_pre_def prod.simps
  by (auto simp: arena_is_valid_clause_idx_def intro!: valid_arena_update_lbd)

sepref_register update_lbd_and_mark_used
sepref_def update_lbd_and_mark_used_impl
  is \<open>uncurry2 (RETURN ooo update_lbd_and_mark_used)\<close>
    :: \<open>[update_lbd_pre]\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>d  \<rightarrow> arena_fast_assn\<close>
  unfolding update_lbd_and_mark_used_def LBD_SHIFT_def
  supply [dest] = update_lbd_pre_arena_act_preD
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref

lemma mop_mark_added_heur_st_alt_def:
  \<open>mop_mark_added_heur_st L S = do {
  let (heur, S) = extract_heur_wl_heur S;
  heur \<leftarrow> mop_mark_added_heur L True heur;
  RETURN (update_heur_wl_heur heur S)
  }\<close>
  unfolding mop_mark_added_heur_st_def
  by (auto simp: incr_restart_stat_def state_extractors split: isasat_int.splits
    intro!: ext)

sepref_def mop_mark_added_heur_iml
  is \<open>uncurry2 mop_mark_added_heur\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a heuristic_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_assn\<close>
  supply [sepref_fr_rules] = mark_added_heur_impl_refine
  unfolding mop_mark_added_heur_def
  by sepref

sepref_register mop_mark_added_heur mop_mark_added_heur_st mark_added_clause_heur2

sepref_def mop_mark_added_heur_st_impl
  is \<open>uncurry mop_mark_added_heur_st\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding mop_mark_added_heur_st_alt_def
  by sepref

sepref_def mark_added_clause_heur2_impl
  is \<open>uncurry mark_added_clause_heur2\<close>
  :: \<open>isasat_bounded_assn\<^sup>d *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding mark_added_clause_heur2_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

lemma isa_empty_conflict_and_extract_clause_heur_alt_def:
    \<open>isa_empty_conflict_and_extract_clause_heur M D outl = do {
     let C = replicate (length outl) (outl!0);
     (D, C, _) \<leftarrow> WHILE\<^sub>T
         (\<lambda>(D, C, i). i < length_uint32_nat outl)
         (\<lambda>(D, C, i). do {
           ASSERT(i < length outl);
           ASSERT(i < length C);
           ASSERT(lookup_conflict_remove1_pre (outl ! i, D));
           let D = lookup_conflict_remove1 (outl ! i) D;
           let C = C[i := outl ! i];
	   ASSERT(get_level_pol_pre (M, C!i));
	   ASSERT(get_level_pol_pre (M, C!1));
	   ASSERT(1 < length C);
           let L1 = C!i;
           let L2 = C!1;
           let C = (if get_level_pol M L1 > get_level_pol M L2 then swap C 1 i else C);
           ASSERT(i+1 \<le> uint32_max);
           RETURN (D, C, i+1)
         })
        (D, C, 1);
     ASSERT(length outl \<noteq> 1 \<longrightarrow> length C > 1);
     ASSERT(length outl \<noteq> 1 \<longrightarrow>  get_level_pol_pre (M, C!1));
     RETURN ((True, D), C, if length outl = 1 then 0 else get_level_pol M (C!1))
  }\<close>
  unfolding isa_empty_conflict_and_extract_clause_heur_def (*WB_More_Refinement_List.swap_def
    swap_def[symmetric]*)
  by auto

sepref_def empty_conflict_and_extract_clause_heur_fast_code
  is \<open>uncurry2 (isa_empty_conflict_and_extract_clause_heur)\<close>
  :: \<open>[\<lambda>((M, D), outl). outl \<noteq> [] \<and> length outl \<le> uint32_max]\<^sub>a
      trail_pol_fast_assn\<^sup>k *\<^sub>a lookup_clause_rel_assn\<^sup>d *\<^sub>a out_learned_assn\<^sup>k \<rightarrow>
       (conflict_option_rel_assn) \<times>\<^sub>a clause_ll_assn \<times>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=1]] image_image[simp]
  supply [simp] = max_snat_def uint32_max_def
  unfolding isa_empty_conflict_and_extract_clause_heur_alt_def
    larray_fold_custom_replicate length_uint32_nat_def conflict_option_rel_assn_def
  apply (rewrite at \<open>\<hole>\<close> in \<open>_ !1\<close> snat_const_fold[where 'a=64])+
  apply (rewrite at \<open>\<hole>\<close> in \<open>_ !0\<close> snat_const_fold[where 'a=64])
  apply (rewrite at \<open>swap _ \<hole> _\<close> snat_const_fold[where 'a=64])
  apply (rewrite at \<open>\<hole>\<close> in \<open>(_, _, _ + 1)\<close> snat_const_fold[where 'a=64])
  apply (rewrite at \<open>\<hole>\<close> in \<open>(_, _, 1)\<close> snat_const_fold[where 'a=64])
  apply (rewrite at \<open>\<hole>\<close> in \<open>If (length _ = \<hole>)\<close> snat_const_fold[where 'a=64])
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  unfolding gen_swap convert_swap
  by sepref


lemma emptied_list_alt_def: \<open>emptied_list xs = take 0 xs\<close>
  by (auto simp: emptied_list_def)

sepref_def empty_cach_code
  is \<open>empty_cach_ref_set\<close>
  :: \<open>cach_refinement_l_assn\<^sup>d \<rightarrow>\<^sub>a cach_refinement_l_assn\<close>
  supply [[goals_limit=1]]
  unfolding empty_cach_ref_set_def comp_def cach_refinement_l_assn_def emptied_list_alt_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  apply (rewrite at \<open>_[\<hole> := SEEN_UNKNOWN]\<close> value_of_atm_def[symmetric])
  apply (rewrite at \<open>_[\<hole> := SEEN_UNKNOWN]\<close> index_of_atm_def[symmetric])
  by sepref



theorem empty_cach_code_empty_cach_ref[sepref_fr_rules]:
  \<open>(empty_cach_code, RETURN \<circ> empty_cach_ref)
    \<in> [empty_cach_ref_pre]\<^sub>a
    cach_refinement_l_assn\<^sup>d \<rightarrow> cach_refinement_l_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in>[comp_PRE Id
     (\<lambda>(cach, supp).
         (\<forall>L\<in>set supp. L < length cach) \<and>
         length supp \<le> Suc (uint32_max div 2) \<and>
         (\<forall>L<length cach. cach ! L \<noteq> SEEN_UNKNOWN \<longrightarrow> L \<in> set supp))
     (\<lambda>x y. True)
     (\<lambda>x. nofail ((RETURN \<circ> empty_cach_ref) x))]\<^sub>a
      hrp_comp (cach_refinement_l_assn\<^sup>d)
                     Id \<rightarrow> hr_comp cach_refinement_l_assn Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE[OF empty_cach_code.refine[unfolded PR_CONST_def convert_fref]
        empty_cach_ref_set_empty_cach_ref[unfolded convert_fref]] by simp
  have pre: \<open>?pre' h x\<close> if \<open>?pre x\<close> for x h
    using that by (auto simp: comp_PRE_def trail_pol_def
        ann_lits_split_reasons_def empty_cach_ref_pre_def)
  have im: \<open>?im' = ?im\<close>
    by simp
  have f: \<open>?f' = ?f\<close>
    by auto
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f apply assumption
    using pre ..
qed

sepref_register fm_add_new_fast

lemma isasat_fast_length_leD: \<open>isasat_fast S \<Longrightarrow> Suc (length (get_clauses_wl_heur S)) < max_snat 64\<close>
  by (cases S) (auto simp: isasat_fast_def max_snat_def sint64_max_def)

sepref_register update_propagation_heuristics
sepref_def update_heuristics_stats_impl
  is \<open>uncurry (RETURN oo update_propagation_heuristics_stats)\<close>
  :: \<open>uint32_nat_assn\<^sup>k *\<^sub>a heuristic_int_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_int_assn\<close>
  unfolding update_propagation_heuristics_stats_def heuristic_int_assn_def
  by sepref

sepref_def update_heuristics_impl
  is \<open>uncurry (RETURN oo update_propagation_heuristics)\<close>
  :: \<open>uint32_nat_assn\<^sup>k *\<^sub>a heuristic_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_assn\<close>
  unfolding update_propagation_heuristics_def
  by sepref

(*TODO Move to isasat_fast_countD*)
lemma isasat_fast_countD_tmp:
  \<open>isasat_fast S \<Longrightarrow> clss_size_lcountUEk (get_learned_count S) < uint64_max\<close>
  by (auto simp: isasat_fast_def learned_clss_count_def)

lemma propagate_unit_bt_wl_D_int_alt_def:
    \<open>propagate_unit_bt_wl_D_int = (\<lambda>L S\<^sub>0. do {
      let (M, S) = extract_trail_wl_heur S\<^sub>0;
      let (N, S) = extract_arena_wl_heur S;
      ASSERT (N = get_clauses_wl_heur S\<^sub>0);
      let (lcount, S) = extract_lcount_wl_heur S;
      ASSERT (lcount = get_learned_count S\<^sub>0);
      let (heur, S) = extract_heur_wl_heur S;
      let (stats, S) = extract_stats_wl_heur S;
      let (lbd, S) = extract_lbd_wl_heur S;
      let (vm0, S) = extract_vmtf_wl_heur S;
      vm \<leftarrow> isa_vmtf_flush_int M vm0;
      glue \<leftarrow> get_LBD lbd;
      lbd \<leftarrow> lbd_empty lbd;
      j \<leftarrow> mop_isa_length_trail M;
      ASSERT(0 \<noteq> DECISION_REASON);
      ASSERT(cons_trail_Propagated_tr_pre ((- L, 0::nat), M));
      M \<leftarrow> cons_trail_Propagated_tr (- L) 0 M;
      let stats = incr_units_since_last_GC (incr_uset stats);
      let S = update_stats_wl_heur stats S;
      let S = update_trail_wl_heur M S;
      let S = update_lbd_wl_heur lbd S;
      let S = update_literals_to_update_wl_heur j S;
      let S = update_heur_wl_heur (heuristic_reluctant_tick (update_propagation_heuristics glue heur)) S;
      let S = update_lcount_wl_heur (clss_size_incr_lcountUEk lcount) S;
      let S = update_arena_wl_heur N S;
      let S = update_vmtf_wl_heur vm S;
      let _ = log_unit_clause (-L);
        RETURN S})\<close>
  by (auto simp: propagate_unit_bt_wl_D_int_def state_extractors log_unit_clause_def intro!: ext split: isasat_int.splits)

sepref_register cons_trail_Propagated_tr update_heur_wl_heur
sepref_def propagate_unit_bt_wl_D_fast_code
  is \<open>uncurry propagate_unit_bt_wl_D_int\<close>
  :: \<open>[\<lambda>(L, S). isasat_fast S]\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit = 1]]
    isasat_fast_countD[dest] isasat_fast_countD_tmp[dest]
  unfolding propagate_unit_bt_wl_D_int_alt_def
    PR_CONST_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref


definition propagate_bt_wl_D_heur_extract where
  \<open>propagate_bt_wl_D_heur_extract = (\<lambda>S\<^sub>0. do {
      let (M,S) = extract_trail_wl_heur S\<^sub>0;
      let (vdom, S) = extract_vdom_wl_heur S;
      let (N0, S) = extract_arena_wl_heur S;
      let (W0, S) = extract_watchlist_wl_heur S;
      let (lcount, S) = extract_lcount_wl_heur S;
      let (heur, S) = extract_heur_wl_heur S;
      let (stats, S) = extract_stats_wl_heur S;
      let (lbd, S) = extract_lbd_wl_heur S;
      let (vm0, S) = extract_vmtf_wl_heur S;
      RETURN (M, vdom, N0, W0, lcount, heur, stats, lbd, vm0, S)})\<close>

sepref_def propagate_bt_wl_D_heur_extract_impl
  is \<open>propagate_bt_wl_D_heur_extract\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a trail_pol_fast_assn \<times>\<^sub>a aivdom_assn \<times>\<^sub>a arena_fast_assn \<times>\<^sub>a
  watchlist_fast_assn \<times>\<^sub>a lcount_assn \<times>\<^sub>a heuristic_assn \<times>\<^sub>a stats_assn \<times>\<^sub>a lbd_assn \<times>\<^sub>a
  vmtf_remove_assn \<times>\<^sub>a isasat_bounded_assn\<close>
  unfolding propagate_bt_wl_D_heur_extract_def
  by sepref

definition propagate_bt_wl_D_heur_update where
  \<open>propagate_bt_wl_D_heur_update = (\<lambda>S\<^sub>0 M vdom N0 W0 lcount heur stats lbd vm0 j. do {
      let (S) = update_trail_wl_heur M S\<^sub>0;
      let (S) = update_vdom_wl_heur vdom S;
      let (S) = update_arena_wl_heur N0 S;
      let (S) = update_watchlist_wl_heur W0 S;
      let (S) = update_lcount_wl_heur lcount S;
      let (S) = update_heur_wl_heur heur S;
      let (S) = update_stats_wl_heur stats S;
      let S = update_lbd_wl_heur lbd S;
      let (S) = update_vmtf_wl_heur vm0 S;
      let S = update_clvls_wl_heur 0 S;
      let S = update_literals_to_update_wl_heur j S;
      RETURN (S)})\<close>

sepref_def propagate_bt_wl_D_heur_update_impl
  is \<open>uncurry10 propagate_bt_wl_D_heur_update\<close>
  :: \<open>isasat_bounded_assn\<^sup>d *\<^sub>a trail_pol_fast_assn\<^sup>d *\<^sub>a aivdom_assn\<^sup>d *\<^sub>a arena_fast_assn\<^sup>d *\<^sub>a
  watchlist_fast_assn\<^sup>d *\<^sub>a lcount_assn\<^sup>d *\<^sub>a heuristic_assn\<^sup>d *\<^sub>a stats_assn\<^sup>d *\<^sub>a lbd_assn\<^sup>d *\<^sub>a
  vmtf_remove_assn\<^sup>d *\<^sub>a sint64_nat_assn\<^sup>k  \<rightarrow>\<^sub>a  isasat_bounded_assn\<close>
  supply [[goals_limit = 1]]
  unfolding propagate_bt_wl_D_heur_update_def
  apply (rewrite at \<open>update_clvls_wl_heur \<hole> _\<close> unat_const_fold[where 'a=32])
  by sepref

lemma propagate_bt_wl_D_heur_alt_def:
  \<open>propagate_bt_wl_D_heur = (\<lambda>L C S\<^sub>0. do {
      (M, vdom, N0, W0, lcount, heur, stats, lbd, vm0, S) \<leftarrow> propagate_bt_wl_D_heur_extract S\<^sub>0;
      ASSERT (N0 = get_clauses_wl_heur S\<^sub>0);
      ASSERT (vdom = get_aivdom S\<^sub>0);
      ASSERT(length (get_vdom_aivdom vdom) \<le> length N0);
      ASSERT(length (get_avdom_aivdom vdom) \<le> length N0);
      ASSERT(nat_of_lit (C!1) < length W0 \<and> nat_of_lit (-L) < length W0);
      ASSERT(length C > 1);
      let L' = C!1;
      ASSERT(length C \<le> uint32_max div 2 + 1);
      vm \<leftarrow> isa_vmtf_rescore C M vm0;
      glue \<leftarrow> get_LBD lbd;
      let b = False;
      let l = 2;
      let b' = (length C = l);
      ASSERT(isasat_fast S\<^sub>0 \<longrightarrow> append_and_length_fast_code_pre ((b, C), N0));
      ASSERT(isasat_fast S\<^sub>0 \<longrightarrow> clss_size_lcount lcount < sint64_max);
      (N, i) \<leftarrow> fm_add_new b C N0;
      ASSERT(update_lbd_pre ((i, glue), N));
      let N = update_lbd_and_mark_used i glue N;
      ASSERT(isasat_fast S\<^sub>0 \<longrightarrow> length_ll W0 (nat_of_lit (-L)) < sint64_max);
      let W = W0[nat_of_lit (- L) := W0 ! nat_of_lit (- L) @ [(i, L', b')]];
      ASSERT(isasat_fast S\<^sub>0 \<longrightarrow> length_ll W (nat_of_lit L') < sint64_max);
      let W = W[nat_of_lit L' := W!nat_of_lit L' @ [(i, -L, b')]];
      lbd \<leftarrow> lbd_empty lbd;
      j \<leftarrow> mop_isa_length_trail M;
      ASSERT(i \<noteq> DECISION_REASON);
      ASSERT(cons_trail_Propagated_tr_pre ((-L, i), M));
      M \<leftarrow> cons_trail_Propagated_tr (- L) i M;
      vm \<leftarrow> isa_vmtf_flush_int M vm;
      heur \<leftarrow> mop_save_phase_heur (atm_of L') (is_neg L') heur;
      S \<leftarrow> propagate_bt_wl_D_heur_update S M (add_learned_clause_aivdom i vdom) N
          W (clss_size_incr_lcount lcount) (heuristic_reluctant_tick (update_propagation_heuristics glue heur)) (add_lbd (of_nat glue) stats) lbd vm j;
        _ \<leftarrow> log_new_clause_heur S i;
      S \<leftarrow> mark_added_clause_heur2 S i;
      RETURN (S)
        })\<close>
  unfolding propagate_bt_wl_D_heur_def Let_def propagate_bt_wl_D_heur_update_def
          propagate_bt_wl_D_heur_extract_def nres_monad3
  by (auto simp: propagate_bt_wl_D_heur_def Let_def state_extractors propagate_bt_wl_D_heur_update_def
          propagate_bt_wl_D_heur_extract_def intro!: ext bind_cong[OF refl]
          split: isasat_int.splits)

lemmas [sepref_bounds_simps] =
  max_snat_def[of 64, simplified]
  max_unat_def[of 64, simplified]

definition two_sint64 :: nat where [simp]: \<open>two_sint64 = 2\<close>
lemma [sepref_fr_rules]:
   \<open>(uncurry0 (Mreturn 2), uncurry0 (RETURN two_sint64)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  apply sepref_to_hoare
  apply (vcg, auto simp: snat_rel_def snat.rel_def br_def snat_invar_def ENTAILS_def
      snat_numeral max_snat_def exists_eq_star_conv Exists_eq_simp
      sep_conj_commute pure_true_conv)
  done

sepref_register propagate_bt_wl_D_heur_update propagate_bt_wl_D_heur_extract two_sint64
sepref_def propagate_bt_wl_D_fast_codeXX
  is \<open>uncurry2 propagate_bt_wl_D_heur\<close>
  :: \<open>[\<lambda>((L, C), S). isasat_fast S]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit = 1]] append_ll_def[simp] isasat_fast_length_leD[dest]
     propagate_bt_wl_D_fast_code_isasat_fastI2[intro] length_ll_def[simp]
     propagate_bt_wl_D_fast_code_isasat_fastI3[intro]
     isasat_fast_countD[dest]
  unfolding propagate_bt_wl_D_heur_alt_def
    fm_add_new_fast_def[symmetric]
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    append_ll_def[symmetric] append_ll_def[symmetric] two_sint64_def[symmetric]
    PR_CONST_def save_phase_def fold_tuple_optimizations
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

lemma extract_shorter_conflict_list_heur_st_alt_def:
    \<open>extract_shorter_conflict_list_heur_st = (\<lambda>S\<^sub>0. do {
     let (M,S) = extract_trail_wl_heur S\<^sub>0;
     let (N, S) = extract_arena_wl_heur S;
     ASSERT (N = get_clauses_wl_heur S\<^sub>0);
     let (lbd, S) = extract_lbd_wl_heur S;
     let (vm0, S) = extract_vmtf_wl_heur S;
     let (outl, S) = extract_outl_wl_heur S;
     let (bD, S) = extract_conflict_wl_heur S;
     let (ccach, S) = extract_ccach_wl_heur S;
     lbd \<leftarrow> mark_lbd_from_list_heur M outl lbd;
     let D =  the_lookup_conflict bD;
     ASSERT(fst M \<noteq> []);
     let K = lit_of_last_trail_pol M;
     ASSERT(0 < length outl);
     ASSERT(lookup_conflict_remove1_pre (-K, D));
     let D = lookup_conflict_remove1 (-K) D;
     let outl = outl[0 := -K];
     vm \<leftarrow> isa_vmtf_mark_to_rescore_also_reasons M N outl (-K) vm0;
     (D, ccach, outl) \<leftarrow> isa_minimize_and_extract_highest_lookup_conflict M N D ccach lbd outl;
     ASSERT(empty_cach_ref_pre ccach);
     let ccach = empty_cach_ref ccach;
     ASSERT(outl \<noteq> [] \<and> length outl \<le> uint32_max);
     (D, C, n) \<leftarrow> isa_empty_conflict_and_extract_clause_heur M D outl;
      let S = update_trail_wl_heur M S;
      let S = update_arena_wl_heur N S;
      let S = update_vmtf_wl_heur vm S;
      let S = update_lbd_wl_heur lbd S;
      let S = update_outl_wl_heur (take 1 outl) S;
      let S = update_ccach_wl_heur ccach S;
      let S = update_conflict_wl_heur D S;
     RETURN (S, n, C)
  })\<close>
  unfolding extract_shorter_conflict_list_heur_st_def
  by (auto simp: the_lookup_conflict_def Let_def state_extractors intro!: ext bind_cong[OF refl]
    split: isasat_int.splits)

sepref_register isa_minimize_and_extract_highest_lookup_conflict
    empty_conflict_and_extract_clause_heur
    isa_vmtf_mark_to_rescore_also_reasons

sepref_def extract_shorter_conflict_list_heur_st_fast
  is \<open>extract_shorter_conflict_list_heur_st\<close>
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a
        isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn \<times>\<^sub>a uint32_nat_assn \<times>\<^sub>a clause_ll_assn\<close>
  supply [[goals_limit=1]] empty_conflict_and_extract_clause_pre_def[simp]
  unfolding extract_shorter_conflict_list_heur_st_alt_def PR_CONST_def
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_register find_lit_of_max_level_wl
  extract_shorter_conflict_list_heur_st lit_of_hd_trail_st_heur propagate_bt_wl_D_heur
  propagate_unit_bt_wl_D_int
sepref_register backtrack_wl

lemma get_learned_count_learned_clss_countD2:
  \<open>get_learned_count S = (get_learned_count T) \<Longrightarrow>
       learned_clss_count S \<le> learned_clss_count T\<close>
  by (cases S; cases T) (auto simp: learned_clss_count_def)

lemma backtrack_wl_D_nlit_heurI:
  \<open>isasat_fast x \<Longrightarrow>
       get_clauses_wl_heur xc = get_clauses_wl_heur x \<Longrightarrow>
       get_learned_count xc = get_learned_count x \<Longrightarrow> isasat_fast xc\<close>
  by (auto simp: isasat_fast_def dest: get_learned_count_learned_clss_countD2)

sepref_register save_phase_st
sepref_def backtrack_wl_D_fast_code
  is \<open>backtrack_wl_D_nlit_heur\<close>
  :: \<open>[isasat_fast]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
    size_conflict_wl_def[simp] isasat_fast_length_leD[intro] backtrack_wl_D_nlit_heurI[intro]
    isasat_fast_countD[dest] IsaSAT_Setup.isasat_fast_length_leD[dest]
  unfolding backtrack_wl_D_nlit_heur_def PR_CONST_def
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    append_ll_def[symmetric]
    size_conflict_wl_def[symmetric]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

(* TODO: Move *)
lemmas [llvm_inline] = add_lbd_def

experiment
begin
  export_llvm
     empty_conflict_and_extract_clause_heur_fast_code
     empty_cach_code
     update_heuristics_impl
     update_heuristics_impl
     isa_vmtf_flush_fast_code
     get_LBD_code
     mop_isa_length_trail_fast_code
     cons_trail_Propagated_tr_fast_code
     update_heuristics_impl
     vmtf_rescore_fast_code
     append_and_length_fast_code
     update_lbd_impl
     reluctant_tick_impl
     propagate_bt_wl_D_fast_codeXX
end


end
