theory IsaSAT_Restart_Reduce_LLVM
  imports IsaSAT_Restart_Reduce_Defs IsaSAT_Setup_LLVM IsaSAT_VMTF_State_LLVM
begin


lemma schedule_next_reduce_st_alt_def:
  \<open>schedule_next_reduce_st b S = (let (heur, S) = extract_heur_wl_heur S; heur = schedule_next_reduce b heur in update_heur_wl_heur heur S)\<close>
  by (auto simp: schedule_next_reduce_st_def state_extractors Let_def intro!: ext split: isasat_int_splits)

sepref_def schedule_next_reduce_st_impl
  is \<open>uncurry (RETURN oo schedule_next_reduce_st)\<close>
  :: \<open>word64_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding schedule_next_reduce_st_alt_def
  by sepref

lemmas [sepref_fr_rules] = irredandant_count.refine
lemmas [unfolded inline_direct_return_node_case, llvm_code] =
  get_irredundant_count_st_code_def[unfolded read_all_st_code_def]

lemma schedule_next_reduction_stI: \<open>\<not>a < (10 :: 64 word) \<Longrightarrow> a > 0\<close>
  unfolding word_le_not_less[symmetric]
  apply (rule order.strict_trans2)
  prefer 2
  apply assumption
  by auto

sepref_def schedule_next_reduction_st_impl
  is \<open>RETURN o schedule_next_reduction_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  supply [simp] = schedule_next_reduction_stI 
  supply of_nat_snat[sepref_import_param]
  unfolding schedule_next_reduction_st_def
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

definition vmtf_array_nxt_score :: \<open>vmtf \<Rightarrow> _\<close> where \<open>vmtf_array_nxt_score x = fst (snd x)\<close>

lemma \<open>current_vmtf_array_nxt_score x = (case x of Bump_Heuristics a b c d \<Rightarrow>
  (if c then vmtf_array_nxt_score b else vmtf_array_nxt_score a))\<close>
  by (cases x) (auto simp: vmtf_array_nxt_score_def current_vmtf_array_nxt_score_def
    bump_get_heuristics_def)

lemma vmtf_array_nxt_score_alt_def: \<open>RETURN o vmtf_array_nxt_score = (\<lambda>(a,b,c,d,e) . let b' = COPY b in RETURN b)\<close>
  by (auto intro!: ext simp: vmtf_array_nxt_score_def)

find_theorems hn_refine PASS
sepref_def vmtf_array_nxt_score_code
  is \<open>RETURN o vmtf_array_nxt_score\<close>
  :: \<open>vmtf_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  unfolding vmtf_array_nxt_score_alt_def vmtf_assn_def
  by sepref

lemma current_vmtf_array_nxt_score_alt_def: \<open>RETURN o current_vmtf_array_nxt_score = (\<lambda>x. case x of Bump_Heuristics hstable focused foc a \<Rightarrow>
    if foc then RETURN (vmtf_array_nxt_score focused) else RETURN (vmtf_array_nxt_score hstable))\<close>
    by (auto intro!: ext simp: bump_get_heuristics_def current_vmtf_array_nxt_score_def vmtf_array_nxt_score_def
      split: bump_heuristics_splits)

sepref_def current_vmtf_array_nxt_score_code
  is \<open>RETURN o current_vmtf_array_nxt_score\<close>
  :: \<open>heuristic_bump_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  unfolding current_vmtf_array_nxt_score_alt_def
  by sepref


sepref_def find_local_restart_target_level_fast_code
  is \<open>uncurry find_local_restart_target_level_int\<close>
  :: \<open>trail_pol_fast_assn\<^sup>k *\<^sub>a heuristic_bump_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=1]] length_rev[simp del]
  unfolding find_local_restart_target_level_int_def find_local_restart_target_level_int_inv_def
    length_uint32_nat_def trail_pol_fast_assn_def
  apply (annot_unat_const \<open>TYPE(32)\<close>)
   apply (rewrite in \<open>(_ ! _)\<close> annot_unat_snat_upcast[where 'l=64])
   apply (rewrite in \<open>(_ ! \<hole>)\<close> annot_unat_snat_upcast[where 'l=64])
   apply (rewrite in \<open>(\<hole> < length _)\<close> annot_unat_snat_upcast[where 'l=64])
  by sepref


definition find_local_restart_target_level_st_fast_code :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>find_local_restart_target_level_st_fast_code = (read_all_st_code (\<lambda>M _ _ _ _ N _ _ _ _ _ _ _ _ _ _ _. find_local_restart_target_level_fast_code M N))\<close>

global_interpretation find_restart_lvl: read_trail_vmtf_param_adder0 where
  P = \<open>\<lambda>_ _. True\<close> and
  f' = \<open>find_local_restart_target_level_int\<close> and
  f = \<open>find_local_restart_target_level_fast_code\<close> and
  x_assn = \<open>uint32_nat_assn\<close>
  rewrites
    \<open>(read_all_st (\<lambda>M _ _ _ _ N _ _ _ _ _ _ _ _ _ _ _. find_local_restart_target_level_int M N)) = find_local_restart_target_level_st\<close> and
    \<open>(read_all_st_code (\<lambda>M _ _ _ _ N _ _ _ _ _ _ _ _ _ _ _. find_local_restart_target_level_fast_code M N)) = find_local_restart_target_level_st_fast_code\<close>
  apply unfold_locales
  apply (subst lambda_comp_true)
  apply (rule find_local_restart_target_level_fast_code.refine)
  subgoal by (auto simp: read_all_st_def find_local_restart_target_level_st_def
    intro!: ext split: isasat_int_splits)
  subgoal by (auto simp: find_local_restart_target_level_st_fast_code_def)
  done

lemmas [sepref_fr_rules] = find_restart_lvl.refine
lemmas [unfolded inline_direct_return_node_case, llvm_code] = find_local_restart_target_level_st_fast_code_def[unfolded read_all_st_code_def]

lemma empty_Q_alt_def:
  \<open>empty_Q = (\<lambda>S. do{
  let (M, S) = extract_trail_wl_heur S;
  let (heur, S) = extract_heur_wl_heur S;
  j \<leftarrow> mop_isa_length_trail M;
  RETURN (update_heur_wl_heur (restart_info_restart_done_heur heur) (update_literals_to_update_wl_heur j (update_trail_wl_heur M S)))
    })\<close>
  by (auto simp: state_extractors empty_Q_def intro!: ext split: isasat_int_splits)

sepref_def empty_Q_fast_code
  is \<open>empty_Q\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding empty_Q_alt_def
  by sepref

sepref_register cdcl_twl_local_restart_wl_D_heur
    empty_Q find_decomp_wl_st_int

(*TODO: deduplicate*)
lemma [def_pat_rules]: \<open>count_decided_st_heur$S \<equiv> isa_count_decided_st$S\<close>
  by (auto simp: isa_count_decided_st_def count_decided_st_heur_def)

sepref_def cdcl_twl_local_restart_wl_D_heur_fast_code
  is \<open>cdcl_twl_local_restart_wl_D_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding cdcl_twl_local_restart_wl_D_heur_def PR_CONST_def
  supply [[goals_limit = 1]]
  by sepref

definition lbd_sort_clauses_raw :: \<open>arena \<Rightarrow> vdom \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list nres\<close> where
  \<open>lbd_sort_clauses_raw arena N = pslice_sort_spec idx_cdom clause_score_less arena N\<close>

definition lbd_sort_clauses_avdom :: \<open>arena \<Rightarrow> vdom \<Rightarrow> nat list nres\<close> where
  \<open>lbd_sort_clauses_avdom arena N = lbd_sort_clauses_raw arena N 0 (length N)\<close>

lemmas LBD_introsort[sepref_fr_rules] =
  LBD_it.introsort_param_impl_correct[unfolded lbd_sort_clauses_raw_def[symmetric] PR_CONST_def]

sepref_register lbd_sort_clauses_raw
sepref_def lbd_sort_clauses_avdom_impl
  is \<open>uncurry lbd_sort_clauses_avdom\<close>
  :: \<open>arena_fast_assn\<^sup>k *\<^sub>a vdom_fast_assn\<^sup>d \<rightarrow>\<^sub>a vdom_fast_assn\<close>
  supply[[goals_limit=1]]
  unfolding lbd_sort_clauses_avdom_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_register remove_deleted_clauses_from_avdom arena_status DELETED
lemma mark_to_delete_clauses_wl_D_heur_is_Some_iff:
  \<open>D = Some C \<longleftrightarrow> D \<noteq> None \<and> ((the D) = C)\<close>
  by auto

sepref_def mop_marked_as_used_impl
  is \<open>uncurry mop_marked_as_used\<close>
  :: \<open>arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a unat_assn' TYPE(2)\<close>
  supply [[goals_limit=1]]
  unfolding mop_marked_as_used_def
  by sepref

sepref_def MINIMUM_DELETION_LBD_impl
  is \<open>uncurry0 (RETURN MINIMUM_DELETION_LBD)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding MINIMUM_DELETION_LBD_def
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref

sepref_def isa_is_candidate_for_removal_impl
  is \<open>uncurry2 isa_is_candidate_for_removal\<close>
  :: \<open>trail_pol_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding isa_is_candidate_for_removal_def
  unfolding
    access_avdom_at_def[symmetric] length_avdom_def[symmetric]
    get_the_propagation_reason_heur_def[symmetric]
    clause_is_learned_heur_def[symmetric]
    clause_lbd_heur_def[symmetric]
    access_length_heur_def[symmetric]
    mark_to_delete_clauses_wl_D_heur_is_Some_iff
    marked_as_used_st_def[symmetric] if_conn(4)
    fold_tuple_optimizations
  supply [[goals_limit = 1]] of_nat_snat[sepref_import_param]
      length_avdom_def[symmetric, simp] access_avdom_at_def[simp]
  apply (rewrite in \<open>let _ = \<hole> in _\<close> short_circuit_conv)+
  apply (rewrite in \<open>_ = 0\<close> unat_const_fold[where 'a=2])
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_register isa_is_candidate_for_removal

sepref_def remove_deleted_clauses_from_avdom_fast_code
  is \<open>uncurry2 isa_gather_candidates_for_reduction\<close>
  :: \<open>[\<lambda>((M, N), vdom). length (get_vdom_aivdom vdom) \<le> sint64_max]\<^sub>a
  trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>d *\<^sub>a aivdom_assn\<^sup>d \<rightarrow>
  arena_fast_assn \<times>\<^sub>a aivdom_assn\<close>
  supply [[goals_limit=1]]
  supply [simp] = length_avdom_aivdom_def
  unfolding isa_gather_candidates_for_reduction_def
    convert_swap gen_swap if_conn(4) length_avdom_aivdom_def[symmetric]
    avdom_aivdom_at_def[symmetric]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref


definition lbd_sort_clauses :: \<open>arena \<Rightarrow> aivdom2 \<Rightarrow> aivdom2 nres\<close> where
  \<open>lbd_sort_clauses arena N = map_tvdom_aivdom_int (lbd_sort_clauses_avdom arena) N\<close>

sepref_def lbd_sort_clauses_impl
  is \<open>uncurry lbd_sort_clauses\<close>
  :: \<open>[\<lambda>(N, vdom). length (fst vdom) \<le> sint64_max]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a aivdom_int_assn\<^sup>d \<rightarrow> aivdom_int_assn\<close>
  unfolding lbd_sort_clauses_def map_tvdom_aivdom_int_def
  by sepref

lemma
  map_vdom_aivdom_int2:
  \<open>(uncurry (\<lambda>arena. map_vdom_aivdom_int (f arena)), uncurry (\<lambda>arena. map_vdom_aivdom (f arena)))
  \<in> Id \<times>\<^sub>r aivdom_rel \<rightarrow>\<^sub>f \<langle>aivdom_rel\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  subgoal for x y
    using map_vdom_aivdom_int[of \<open>f (fst x)\<close>]
    apply (cases x; cases y)
    apply (auto intro!: frefI nres_relI simp: fref_def nres_rel_def)
    done
  done

lemma get_aivdom_eq_aivdom_iff:
  \<open>IsaSAT_VDom.get_aivdom b = (x1, a, aa, ba) \<longleftrightarrow> b = AIvdom (x1, a, aa, ba)\<close>
  by (cases b) auto

lemma quicksort_clauses_by_score_sort:
  \<open>(uncurry lbd_sort_clauses, uncurry sort_clauses_by_score) \<in>
  Id \<times>\<^sub>r aivdom_rel \<rightarrow>\<^sub>f \<langle>aivdom_rel\<rangle>nres_rel\<close>
  apply (intro fun_relI nres_relI frefI)
  subgoal for arena arena'
    unfolding uncurry_def lbd_sort_clauses_def map_tvdom_aivdom_int_def
      lbd_sort_clauses_avdom_def lbd_sort_clauses_raw_def sort_clauses_by_score_def
    apply (refine_vcg)
    apply (rule specify_left)
    apply (auto simp: lbd_sort_clauses_def lbd_sort_clauses_raw_def
      pslice_sort_spec_def le_ASSERT_iff idx_cdom_def slice_rel_def br_def uncurry_def
      conc_fun_RES sort_spec_def map_vdom_aivdom_int_def lbd_sort_clauses_avdom_def
      code_hider_rel_def
      split:prod.splits
      intro!: ASSERT_leI 
      )
    apply (case_tac x2; auto)

    apply (rule order_trans)
    apply (rule slice_sort_spec_refine_sort)
    apply (auto simp: lbd_sort_clauses_def lbd_sort_clauses_raw_def
      pslice_sort_spec_def le_ASSERT_iff idx_cdom_def slice_rel_def br_def uncurry_def
      conc_fun_RES sort_spec_def map_vdom_aivdom_int_def lbd_sort_clauses_avdom_def
      code_hider_rel_def
      split:prod.splits
      intro!: ASSERT_leI 
      )
    apply (case_tac x2; auto simp: get_aivdom_eq_aivdom_iff)
    apply (rule_tac x = \<open>AIvdom (x1a, ac, ad, x)\<close> in exI)
    apply auto
    by (metis slice_complete)
  done

context
  notes [fcomp_norm_unfold] = aivdom_assn_alt_def[symmetric] aivdom_assn_def[symmetric]
begin

lemma lbd_sort_clauses_impl_lbd_sort_clauses[sepref_fr_rules]:
  \<open>(uncurry lbd_sort_clauses_impl, uncurry sort_clauses_by_score)
  \<in> [\<lambda>(N, vdom). length (get_avdom_aivdom vdom) \<le> sint64_max]\<^sub>a (al_assn arena_el_impl_assn)\<^sup>k *\<^sub>a aivdom_assn\<^sup>d \<rightarrow> aivdom_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
\<in> [comp_PRE (Id \<times>\<^sub>f aivdom_rel) (\<lambda>_. True) (\<lambda>x y. case y of (N, vdom) \<Rightarrow> length (fst vdom) \<le> sint64_max)
   (\<lambda>x. nofail (uncurry sort_clauses_by_score x))]\<^sub>a ?im \<rightarrow> ?f\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> _\<close>)
    using hfref_compI_PRE[OF lbd_sort_clauses_impl.refine,
  OF quicksort_clauses_by_score_sort, unfolded fcomp_norm_unfold] by blast
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that 
    by (case_tac x, case_tac \<open>snd x\<close>)
      (auto simp: comp_PRE_def code_hider_rel_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H apply assumption
    using pre ..
qed

end

lemma sort_vdom_heur_alt_def:
  \<open>sort_vdom_heur = (\<lambda>S\<^sub>0. do {
    let (vdom, S) = extract_vdom_wl_heur S\<^sub>0;
    ASSERT (vdom = get_aivdom S\<^sub>0);
    let (M', S) = extract_trail_wl_heur S;
    ASSERT (M' = get_trail_wl_heur S\<^sub>0);
    let (arena, S) = extract_arena_wl_heur S;
    ASSERT (arena = get_clauses_wl_heur S\<^sub>0);
    ASSERT(length (get_avdom_aivdom vdom) \<le> length arena);
    ASSERT(length (get_vdom_aivdom vdom) \<le> length arena);
    (arena', vdom) \<leftarrow> isa_gather_candidates_for_reduction M' arena vdom;
    ASSERT(valid_sort_clause_score_pre arena (get_vdom_aivdom vdom));
    ASSERT(EQ (length arena) (length arena'));
    ASSERT(length (get_avdom_aivdom vdom) \<le> length arena);
    vdom \<leftarrow> sort_clauses_by_score arena' vdom;
    RETURN (update_arena_wl_heur arena' (update_vdom_wl_heur vdom (update_trail_wl_heur M' S)))
    })\<close>
   by (auto intro!: ext split: isasat_int_splits simp: sort_vdom_heur_def state_extractors)

sepref_def sort_vdom_heur_fast_code
  is \<open>sort_vdom_heur\<close>
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>aisasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding sort_vdom_heur_alt_def EQ_def
  by sepref

sepref_def find_largest_lbd_and_size_impl
  is \<open>uncurry find_largest_lbd_and_size\<close>
  :: \<open>sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn \<times>\<^sub>a sint64_nat_assn\<close>
  supply [simp] = length_tvdom_def[symmetric]
  supply [dest] = isasat_bounded_assn_length_arenaD
  supply [sepref_fr_rules] = arena_get_lbd.mop_refine (*TODO: Should in IsaSAT_Setup1*)
  unfolding find_largest_lbd_and_size_def access_tvdom_at_def[symmetric]
    length_tvdom_def[symmetric] max_def
  apply (rewrite at \<open>(_, _, \<hole>)\<close> snat_const_fold[where 'a=64])
  apply (rewrite at \<open>(\<hole>, _)\<close> snat_const_fold[where 'a=64])
  apply (rewrite at \<open>(_, \<hole>, _)\<close> unat_const_fold[where 'a=32])
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

experiment
begin
  export_llvm sort_vdom_heur_fast_code remove_deleted_clauses_from_avdom_fast_code
end

end