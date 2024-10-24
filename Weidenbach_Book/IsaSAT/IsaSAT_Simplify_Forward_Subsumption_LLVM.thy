theory IsaSAT_Simplify_Forward_Subsumption_LLVM
  imports
    IsaSAT_Simplify_Forward_Subsumption_Defs
    IsaSAT_Setup_LLVM
    IsaSAT_Trail_LLVM
    IsaSAT_Proofs_LLVM
    IsaSAT_Arena_Sorting_LLVM
    IsaSAT_Show_LLVM
    IsaSAT_LBD_LLVM
begin

lemma incr_forward_subsumed_st_alt_def: \<open>incr_forward_subsumed_st S = (
  let (stats, S) = extract_stats_wl_heur S; stats = incr_forward_subsumed stats in
    update_stats_wl_heur stats S
    )\<close> and
  incr_forward_strengthened_st_alt_def: \<open>incr_forward_strengthened_st S = (
  let (stats, S) = extract_stats_wl_heur S; stats = incr_forward_strengethening stats in
    update_stats_wl_heur stats S
    )\<close> and
  incr_forward_tried_st_alt_def: \<open>incr_forward_tried_st S = (
  let (stats, S) = extract_stats_wl_heur S; stats = incr_forward_tried stats in
    update_stats_wl_heur stats S
    )\<close> and
  incr_forward_rounds_st_alt_def: \<open>incr_forward_rounds_st S = (
  let (stats, S) = extract_stats_wl_heur S; stats = incr_forward_rounds stats in
    update_stats_wl_heur stats S
    )\<close> and
  isa_forward_reset_added_and_stats_alt_def: \<open>isa_forward_reset_added_and_stats S = (
  let (stats, S) = extract_stats_wl_heur S;
    (heur, S) = extract_heur_wl_heur S;
    stats = incr_forward_rounds stats;
    heur = reset_added_heur heur in
    update_stats_wl_heur stats (update_heur_wl_heur heur S))\<close>
  by (auto simp: isa_push_to_occs_list_st_def state_extractors incr_forward_subsumed_st_def
    incr_forward_strengthened_st_def incr_forward_tried_st_def incr_forward_rounds_st_def
    isa_forward_reset_added_and_stats_def
      split: isasat_int_splits)

sepref_def incr_forward_strengthened_st_impl
  is \<open>RETURN o incr_forward_strengthened_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding incr_forward_strengthened_st_alt_def
  by sepref

sepref_def incr_forward_tried_st_impl
  is \<open>RETURN o incr_forward_tried_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding incr_forward_tried_st_alt_def
  by sepref

sepref_def incr_forward_rounds_st_impl
  is \<open>RETURN o incr_forward_rounds_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding incr_forward_rounds_st_alt_def
  by sepref

sepref_def incr_forward_subsumed_st_impl
  is \<open>RETURN o incr_forward_subsumed_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding incr_forward_subsumed_st_alt_def
  by sepref

sepref_def isa_forward_reset_added_and_stats_impl
  is \<open>RETURN o isa_forward_reset_added_and_stats\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding isa_forward_reset_added_and_stats_alt_def
  by sepref

sepref_register incr_forward_subsumed_st incr_forward_strengthened_st incr_forward_rounds_st incr_forward_tried_st
  isa_forward_reset_added_and_stats

definition clause_size_sort_clauses_raw :: \<open>arena \<Rightarrow> vdom \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list nres\<close> where
  \<open>clause_size_sort_clauses_raw arena N = pslice_sort_spec idx_clause_cdom clause_size_less arena N\<close>

definition clause_size_sort_clauses_avdom :: \<open>arena \<Rightarrow> vdom \<Rightarrow> nat list nres\<close> where
  \<open>clause_size_sort_clauses_avdom arena N = clause_size_sort_clauses_raw arena N 0 (length N)\<close>

lemmas Size_Ordering_introsort[sepref_fr_rules] =
  Size_Ordering_it.introsort_param_impl_correct[unfolded clause_size_sort_clauses_raw_def[symmetric] PR_CONST_def]

sepref_register clause_size_sort_clauses_raw
sepref_def clause_size_sort_clauses_avdom_impl
  is \<open>uncurry clause_size_sort_clauses_avdom\<close>
  :: \<open>arena_fast_assn\<^sup>k *\<^sub>a vdom_fast_assn\<^sup>d \<rightarrow>\<^sub>a vdom_fast_assn\<close>
  supply[[goals_limit=1]]
  unfolding clause_size_sort_clauses_avdom_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

definition clause_size_sort_clauses :: \<open>arena \<Rightarrow> aivdom2 \<Rightarrow> aivdom2 nres\<close> where
  \<open>clause_size_sort_clauses arena N = map_tvdom_aivdom_int (clause_size_sort_clauses_avdom arena) N\<close>

sepref_def clause_size_sort_clauses_impl
  is \<open>uncurry clause_size_sort_clauses\<close>
  :: \<open>arena_fast_assn\<^sup>k *\<^sub>a aivdom_int_assn\<^sup>d \<rightarrow>\<^sub>a aivdom_int_assn\<close>
  unfolding clause_size_sort_clauses_def map_tvdom_aivdom_int_def
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
hide_const (open) NEMonad.ASSERT NEMonad.RETURN NEMonad.ASSERT NEMonad.SPEC

definition sort_cands_by_length2 :: \<open>_ \<Rightarrow> isasat_aivdom \<Rightarrow> isasat_aivdom nres\<close> where
  \<open>sort_cands_by_length2 arena avdom = do {
  ASSERT (\<forall>i\<in>set (get_tvdom_aivdom avdom). arena_is_valid_clause_idx arena i);
  SPEC (\<lambda>cands'.
       mset (get_tvdom_aivdom cands') = mset (get_tvdom_aivdom avdom) \<and>
       (get_avdom_aivdom cands') = (get_avdom_aivdom avdom) \<and>
       (get_ivdom_aivdom cands') = (get_ivdom_aivdom avdom) \<and>
       (get_vdom_aivdom cands') = (get_vdom_aivdom avdom) \<and>
    sorted_wrt (\<lambda>a b. arena_length arena a \<le> arena_length arena b) (get_tvdom_aivdom cands'))
}\<close>

lemma quicksort_clauses_by_score_sort:
  \<open>(uncurry clause_size_sort_clauses, uncurry sort_cands_by_length2) \<in>
  Id \<times>\<^sub>r aivdom_rel \<rightarrow>\<^sub>f \<langle>aivdom_rel\<rangle>nres_rel\<close>
  apply (intro fun_relI nres_relI frefI)
  subgoal for arena arena'
    unfolding uncurry_def sort_cands_by_length2_def map_tvdom_aivdom_int_def
      clause_size_sort_clauses_def clause_size_sort_clauses_avdom_def
      clause_size_sort_clauses_raw_def pslice_sort_spec_def nres_monad3
    apply (refine_vcg)
    subgoal for x1 x2 x1a x2a x1b x2b x1c x2c
      by (cases x2) (auto simp: idx_clause_cdom_def code_hider_rel_def)
    subgoal for x1 x2 x1a x2a x1b x2b x1c x2c
      apply (rule specify_left)
      apply (rule order_trans)
      apply (rule slice_sort_spec_refine_sort)
      apply (auto simp:
        pslice_sort_spec_def le_ASSERT_iff idx_cdom_def slice_rel_def br_def uncurry_def
        conc_fun_RES sort_spec_def map_vdom_aivdom_int_def 
        code_hider_rel_def
        split:prod.splits
        simp del: slice_complete
        intro!: ASSERT_leI 
        )
      subgoal for x1d x
        using slice_complete[of x]
        apply (rule_tac x = \<open>AIvdom (x1d, x1b, x1c, x)\<close> in exI)
        apply (case_tac x2; auto simp: clause_size_less_def slice_complete
          le_by_lt_def)
        unfolding le_by_lt_def
        apply (auto simp: clause_size_less_def
          intro!: arg_cong[of \<open>(\<lambda>a b. \<not> arena_length x1 b < arena_length x1 a)\<close> \<open>(\<lambda>a b. arena_length x1 a \<le> arena_length x1 b)\<close> \<open>\<lambda>a. sorted_wrt a x\<close>, THEN iffD1]ext
          )
        done
      done
    done
  done



context
  notes [fcomp_norm_unfold] = aivdom_assn_alt_def[symmetric] aivdom_assn_def[symmetric]
begin

lemma clause_size_sort_clauses_impl_sort_cands_by_length2[sepref_fr_rules]:
  \<open>(uncurry clause_size_sort_clauses_impl, uncurry sort_cands_by_length2)
  \<in> (al_assn arena_el_impl_assn)\<^sup>k *\<^sub>a aivdom_assn\<^sup>d \<rightarrow>\<^sub>a aivdom_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
\<in> [comp_PRE (Id \<times>\<^sub>f aivdom_rel) (\<lambda>_. True) (\<lambda>x y. True)
   (\<lambda>x. nofail (uncurry sort_cands_by_length2 x))]\<^sub>a ?im \<rightarrow> ?f\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> _\<close>)
    using hfref_compI_PRE[OF clause_size_sort_clauses_impl.refine,
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


lemma sort_cands_by_length_alt_def:
  \<open>sort_cands_by_length S\<^sub>0 = do {
  let (aivdom, S) = extract_vdom_wl_heur S\<^sub>0;
  ASSERT (aivdom = get_aivdom S\<^sub>0);
  let (arena, S) = extract_arena_wl_heur S;
  ASSERT (arena = get_clauses_wl_heur S\<^sub>0);
  aivdom \<leftarrow> sort_cands_by_length2 arena aivdom;
  let S = update_arena_wl_heur arena S;
  let S = update_vdom_wl_heur aivdom S;
  RETURN S
}\<close>
    apply (auto simp: sort_cands_by_length_def sort_cands_by_length2_def state_extractors Let_def RES_RETURN_RES image_iff
      intro!: bind_cong[OF refl]
         split: isasat_int_splits)
    apply (case_tac xb)
    apply auto
    done

sepref_def sort_cands_by_length_impl
  is sort_cands_by_length
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding sort_cands_by_length_alt_def
  by sepref

sepref_register mop_is_marked_added_heur_st
(*TODO: kill mop_arena_lit2_st*)
sepref_def isa_all_lit_clause_unset_impl
  is \<open>uncurry isa_all_lit_clause_unset\<close>
  :: \<open>sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  supply [[goals_limit=1]]
  unfolding isa_all_lit_clause_unset_def
    mop_access_lit_in_clauses_heur_def[symmetric] mop_polarity_st_heur_def[symmetric]
    tri_bool_eq_def[symmetric] UNSET_def[symmetric]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

lemma rdomp_aivdom_assn_length_avdomD: \<open>rdomp aivdom_assn x \<Longrightarrow> length (get_avdom_aivdom x) < max_snat 64\<close>
  unfolding isasat_bounded_assn_def
  apply (cases x)
  apply (auto simp: isasat_bounded_assn_def snat64_max_def max_snat_def length_avdom_def
    aivdom_assn_def code_hider_assn_def hr_comp_def code_hider_rel_def
    split: isasat_int_splits
    dest: al_assn_boundD[of sint64_nat_assn] mod_starD)
  done

lemma rdomp_isasat_bounded_assn_length_avdomD:
  \<open>rdomp isasat_bounded_assn x \<Longrightarrow> length_avdom x < max_snat 64\<close>
  using rdomp_aivdom_assn_length_avdomD[of \<open>get_aivdom x\<close>] apply -
  unfolding isasat_bounded_assn_def rdomp_def
  apply normalize_goal+
  by (cases x)
   (force simp: isasat_bounded_assn_def length_avdom_def 
    split: isasat_int_splits
    dest!: rdomp_aivdom_assn_length_avdomD mod_starD)


sepref_register isa_all_lit_clause_unset isa_push_to_occs_list_st
  find_best_subsumption_candidate find_best_subsumption_candidate_and_push sort_cands_by_length

sepref_def find_best_subsumption_candidate_code
  is \<open>uncurry find_best_subsumption_candidate\<close>
  :: \<open>sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a unat_lit_assn\<close>
  supply [[goals_limit=1]]
  unfolding find_best_subsumption_candidate_def
    mop_access_lit_in_clauses_heur_def[symmetric]
    tri_bool_eq_def[symmetric] UNSET_def[symmetric]
    length_occs_def[symmetric]
    get_occs_list_at_def[symmetric]
    length_occs_at_def[symmetric]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

lemma isa_push_to_occs_list_st_alt_def:
    \<open>isa_push_to_occs_list_st C S = do {
     L \<leftarrow> find_best_subsumption_candidate C S;
     let (occs, T) = extract_occs_wl_heur S;
     ASSERT (length (occs ! nat_of_lit L) < length (get_clauses_wl_heur S));
     occs \<leftarrow> mop_cocc_list_append C occs L;
     RETURN (update_occs_wl_heur occs T)
  }\<close>
  by (auto simp: isa_push_to_occs_list_st_def state_extractors
         split: isasat_int_splits)

sepref_register mop_cocc_list_append
sepref_def mop_cocc_list_append_impl
  is \<open>uncurry2 mop_cocc_list_append\<close>
  :: \<open>[\<lambda>((C,occs), L). Suc (length (occs ! nat_of_lit L)) < max_snat 64]\<^sub>a
    sint64_nat_assn\<^sup>k *\<^sub>a occs_assn\<^sup>d *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> occs_assn\<close>
  unfolding mop_cocc_list_append_def cocc_list_append_pre_def cocc_list_append_def
    fold_op_list_list_push_back
  by sepref

lemma empty_tvdom_st_alt_def:
  \<open>empty_tvdom_st S = do {
    let (aivdom, S) = extract_vdom_wl_heur S;
    let aivdom = empty_tvdom aivdom;
    RETURN (update_vdom_wl_heur aivdom S)
  }\<close>
  by (auto simp: isa_push_to_occs_list_st_def state_extractors empty_tvdom_st_def
         split: isasat_int_splits)

sepref_def empty_tvdom_st_impl
  is empty_tvdom_st
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding empty_tvdom_st_alt_def
  by sepref

sepref_register empty_tvdom_st

sepref_def isa_push_to_occs_list_st_impl
  is \<open>uncurry isa_push_to_occs_list_st\<close>
  :: \<open>[\<lambda>(_, S). isasat_fast_relaxed S]\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding isa_push_to_occs_list_st_alt_def isasat_fast_relaxed_def
  by sepref

sepref_def find_best_subsumption_candidate_and_push_code
  is \<open>uncurry find_best_subsumption_candidate_and_push\<close>
  :: \<open>sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a unat_lit_assn \<times>\<^sub>a bool1_assn\<close>
  supply [[goals_limit=1]]
  unfolding find_best_subsumption_candidate_and_push_def
    mop_access_lit_in_clauses_heur_def[symmetric]
    tri_bool_eq_def[symmetric] UNSET_def[symmetric]
    length_occs_def[symmetric]
    get_occs_list_at_def[symmetric]
    mop_is_marked_added_heur_st_def[symmetric]
    length_occs_at_def[symmetric]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref


lemma isa_maybe_push_to_occs_list_st_alt_def:
    \<open>isa_maybe_push_to_occs_list_st C S = do {
     (L, push) \<leftarrow> find_best_subsumption_candidate_and_push C S;
     if push then do {
       let (occs, T) = extract_occs_wl_heur S;
       ASSERT (length (occs ! nat_of_lit L) < length (get_clauses_wl_heur S));
       occs \<leftarrow> mop_cocc_list_append C occs L;
       RETURN (update_occs_wl_heur occs T)
     } else RETURN S
  }\<close>
  unfolding isa_maybe_push_to_occs_list_st_def Let_def
  by (auto simp: state_extractors cong: if_cong split: isasat_int_splits)

sepref_def isa_maybe_push_to_occs_list_st_impl
  is \<open>uncurry isa_maybe_push_to_occs_list_st\<close>
  :: \<open>[\<lambda>(_, S). isasat_fast_relaxed S]\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding isa_maybe_push_to_occs_list_st_alt_def isasat_fast_relaxed_def
  by sepref


(*TODD move to Setup1*)
lemmas [sepref_fr_rules] = arena_get_lbd.mop_refine
sepref_def isa_is_candidate_forward_subsumption_impl
  is \<open>uncurry isa_is_candidate_forward_subsumption\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding isa_is_candidate_forward_subsumption_def
    mop_access_lit_in_clauses_heur_def[symmetric]
    mop_is_marked_added_heur_st_def[symmetric]
    mop_arena_lbd_st_def[symmetric]
    mop_arena_length_st_def[symmetric]
    mop_arena_status_st_def[symmetric]
    UNSET_def[symmetric] tri_bool_eq_def[symmetric]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

lemma push_to_tvdom_st_alt_def:
  \<open>push_to_tvdom_st C S = do {
    let (av, T) = extract_vdom_wl_heur S;
    ASSERT (length (get_vdom_aivdom av) \<le> length (get_clauses_wl_heur S));
    ASSERT (length (get_tvdom_aivdom av) < length (get_clauses_wl_heur S));
    let av = push_to_tvdom C av;
    RETURN (update_vdom_wl_heur av T)
  }\<close>
  by (auto simp: isa_push_to_occs_list_st_def state_extractors push_to_tvdom_st_def
         split: isasat_int_splits)

sepref_def push_to_tvdom_st_impl
  is \<open>uncurry push_to_tvdom_st\<close>
  :: \<open>[\<lambda>(_, S). isasat_fast_relaxed S]\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding push_to_tvdom_st_alt_def isasat_fast_relaxed_def
  by sepref

lemma isa_populate_occs_inv_isasat_fast_relaxedI:
  \<open>isa_populate_occs_inv x cands (a1', a2') \<Longrightarrow> isasat_fast_relaxed x \<Longrightarrow> isasat_fast_relaxed a2'\<close>
  by (auto simp: isa_populate_occs_inv_def isasat_fast_relaxed_def)

sepref_def isa_populate_occs_code
  is isa_populate_occs
  :: \<open>[isasat_fast_relaxed]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  supply [dest] = rdomp_isasat_bounded_assn_length_avdomD isasat_bounded_assn_length_arenaD
  supply [intro] = isa_populate_occs_inv_isasat_fast_relaxedI
  unfolding isa_populate_occs_def access_avdom_at_def[symmetric] length_avdom_def[symmetric] length_ivdom_def[symmetric]
    al_fold_custom_empty[where 'l=64] Let_def[of \<open>get_avdom _ @ get_ivdom _\<close>] Let_def[of \<open>get_occs _\<close>]
    Let_def[of \<open>get_tvdom _\<close>] nth_append length_append access_ivdom_at_def[symmetric]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_register isa_forward_subsumption_all isa_populate_occs

sepref_register mop_cch_create mop_cch_add_all_clause mop_cch_add mop_cch_in


abbreviation cch_assn where
  \<open>cch_assn \<equiv> IICF_Array.array_assn bool1_assn\<close>

sepref_def mop_cch_create_impl
  is mop_cch_create
  :: \<open>sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a cch_assn\<close>
  unfolding mop_cch_create_def  op_list_replicate_def[symmetric] array_fold_custom_replicate
  by sepref

sepref_def mop_cch_add_impl
  is \<open>uncurry mop_cch_add\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a cch_assn\<^sup>d \<rightarrow>\<^sub>a cch_assn\<close>
  unfolding mop_cch_add_def cch_add_def cch_add_pre_def
  by sepref


sepref_def mop_cch_in_impl
  is \<open>uncurry mop_cch_in\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a cch_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding mop_cch_in_def cch_in_def cch_in_pre_def
  by sepref

sepref_def mop_cch_add_all_clause_impl
  is \<open>uncurry2 mop_cch_add_all_clause\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a cch_assn\<^sup>d \<rightarrow>\<^sub>a cch_assn\<close>
  unfolding mop_cch_add_all_clause_def
    mop_access_lit_in_clauses_heur_def[symmetric]
  supply [dest] = isasat_bounded_assn_length_arenaD
  supply [[goals_limit=1]]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref



sepref_register isa_try_to_forward_subsume_wl2


sepref_def isa_try_to_forward_subsume_wl2_break_impl
  is isa_try_to_forward_subsume_wl2_break
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding isa_try_to_forward_subsume_wl2_break_def
    forward_budget_st_def[symmetric]
    forward_subchecks_st_def[symmetric]
  by sepref

sepref_register isa_try_to_forward_subsume_wl2_break

(*TODO requiring anything from the unused parts of the struct is not really useful*)
definition subsumption_rel :: \<open>('c \<times> nat) set
  \<Rightarrow> ('b \<times> 'd literal) set \<Rightarrow> ('c \<times> nat) set \<Rightarrow> ((3 word \<times> 'b \<times> _) \<times> 'd subsumption) set\<close> where
subsumption_rel_internal_def:  \<open>subsumption_rel R1 R2 R3 = {((tag, x, y),b).
  case b of NONE \<Rightarrow> tag = 0
          | SUBSUMED_BY x' \<Rightarrow> (y, x') \<in> R1 \<and> tag = 1
          | STRENGTHENED_BY x' y' \<Rightarrow> (x, x') \<in> R2 \<and> (y, y') \<in> R3 \<and> tag = 2}\<close>

lemma subsumption_rel_def: \<open>\<langle>R1,R2,R3\<rangle>subsumption_rel = {((tag, x, y),b).
  case b of NONE \<Rightarrow> tag = 0
          | SUBSUMED_BY x' \<Rightarrow> (y, x') \<in> R1 \<and> tag = 1
    | STRENGTHENED_BY x' y' \<Rightarrow> (x, x') \<in> R2 \<and> (y, y') \<in> R3 \<and> tag = 2}\<close>
    unfolding subsumption_rel_internal_def relAPP_def by auto

definition is_NONE where
  \<open>is_NONE x \<longleftrightarrow> NONE = x\<close>
lemma is_subsumption:
  \<open>(\<lambda>(tag, _). tag = 0, is_NONE) \<in> \<langle>R1,R2,R3\<rangle>subsumption_rel \<rightarrow> bool_rel\<close>
  \<open>(\<lambda>(tag, _). tag = 1, is_subsumed) \<in> \<langle>R1,R2,R3\<rangle>subsumption_rel \<rightarrow> bool_rel\<close>
  \<open>(\<lambda>(tag, _). tag = 2, is_strengthened) \<in> \<langle>R1,R2,R3\<rangle>subsumption_rel \<rightarrow> bool_rel\<close>
  \<open>((0, 0, 0), NONE) \<in> \<langle>R1,R2,R3\<rangle>subsumption_rel\<close>
  \<open>(\<lambda>C. (1, 0, C), SUBSUMED_BY) \<in> R1 \<rightarrow> \<langle>R1,R2,R3\<rangle>subsumption_rel\<close>
  \<open>(\<lambda>C D. (2, C, D), STRENGTHENED_BY) \<in> R2 \<rightarrow> R3 \<rightarrow> \<langle>R1,R2,R3\<rangle>subsumption_rel\<close>
  \<open>(\<lambda>(tag, C, D). D, subsumed_by) \<in> [is_subsumed]\<^sub>f \<langle>R1,R2,R3\<rangle>subsumption_rel \<rightarrow> R1\<close>
  \<open>(\<lambda>(tag, C, D). D, strengthened_by) \<in> [is_strengthened]\<^sub>f \<langle>R1,R2,R3\<rangle>subsumption_rel \<rightarrow> R3\<close>
  \<open>(\<lambda>(tag, C, D). C, strengthened_on_lit) \<in> [is_strengthened]\<^sub>f \<langle>R1,R2,R3\<rangle>subsumption_rel \<rightarrow> R2\<close>
  unfolding subsumption_rel_def
  by (auto simp: IS_LEFT_UNIQUE_def single_valued_def is_NONE_def
    intro!: frefI
    split: subsumption.splits)

abbreviation subsumption_raw_assn where
  \<open>subsumption_raw_assn \<equiv> word_assn' TYPE(3) \<times>\<^sub>a word_assn \<times>\<^sub>a id_assn\<close>

definition subsumption_assn where
  \<open>subsumption_assn = hr_comp subsumption_raw_assn (\<langle>snat_rel' TYPE(64), unat_lit_rel,snat_rel' TYPE(64)\<rangle>subsumption_rel)\<close>


sepref_definition is_NONE_impl
  is \<open>RETURN o (\<lambda>(tag, _). tag = 0)\<close>
  :: \<open>subsumption_raw_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

sepref_definition is_subsumed_impl
  is \<open>RETURN o (\<lambda>(tag, _). tag = 1)\<close>
  :: \<open>subsumption_raw_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref


sepref_definition is_strengthened_impl
  is \<open>RETURN o (\<lambda>(tag, _). tag = 2)\<close>
  :: \<open>subsumption_raw_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

sepref_definition STRENGTHENED_BY_impl
  is \<open>uncurry (RETURN oo (\<lambda>C D. (2, C, D)))\<close>
  :: \<open>word_assn\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow>\<^sub>a subsumption_raw_assn\<close>
  by sepref

sepref_definition SUBSUMED_BY_impl
  is \<open>RETURN o (\<lambda>C. (1, 0, C))\<close>
  :: \<open>word_assn\<^sup>k \<rightarrow>\<^sub>a subsumption_raw_assn\<close>
  by sepref

sepref_definition NONE_impl
  is \<open>uncurry0 (RETURN (0, 0, 0::64 word))\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a subsumption_raw_assn\<close>
  by sepref

sepref_definition subsumed_by_impl
  is \<open>RETURN o (\<lambda>(tag, C, D). D)\<close>
  :: \<open>subsumption_raw_assn\<^sup>k \<rightarrow>\<^sub>a id_assn\<close>
  by sepref

sepref_definition strengthened_on_lit_impl
  is \<open>RETURN o (\<lambda>(tag, C, D). C)\<close>
  :: \<open>subsumption_raw_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  by sepref

sepref_register is_NONE is_subsumed is_strengthened STRENGTHENED_BY SUBSUMED_BY NONE subsumed_by strengthened_by strengthened_on_lit

lemmas [sepref_fr_rules] = 
  is_NONE_impl.refine[FCOMP is_subsumption(1), of \<open>snat_rel' TYPE(64)\<close> \<open>unat_lit_rel\<close> \<open>snat_rel' TYPE(64)\<close>, unfolded subsumption_assn_def[symmetric] is_NONE_def[symmetric]]
  is_subsumed_impl.refine[FCOMP is_subsumption(2), of \<open>snat_rel' TYPE(64)\<close> \<open>unat_lit_rel\<close> \<open>snat_rel' TYPE(64)\<close>, unfolded subsumption_assn_def[symmetric]]
  is_strengthened_impl.refine[FCOMP is_subsumption(3), of \<open>snat_rel' TYPE(64)\<close> \<open>unat_lit_rel\<close> \<open>snat_rel' TYPE(64)\<close>, unfolded subsumption_assn_def[symmetric]]
  SUBSUMED_BY_impl.refine[FCOMP is_subsumption(5), of \<open>snat_assn' TYPE(64)\<close> unat_lit_rel \<open>snat_rel' TYPE(64)\<close>, unfolded the_pure_pure subsumption_assn_def[symmetric]]
  STRENGTHENED_BY_impl.refine[FCOMP is_subsumption(6), of unat_lit_assn \<open>snat_assn' TYPE(64)\<close> \<open>snat_rel' TYPE(64)\<close>, unfolded the_pure_pure subsumption_assn_def[symmetric]]
  NONE_impl.refine[FCOMP is_subsumption(4), of \<open>snat_rel' TYPE(64)\<close> unat_lit_rel \<open>snat_rel' TYPE(64)\<close>, unfolded the_pure_pure subsumption_assn_def[symmetric]]
  subsumed_by_impl.refine[FCOMP is_subsumption(7), of \<open>snat_assn' TYPE(64)\<close> unat_lit_rel \<open>snat_rel' TYPE(64)\<close>, unfolded the_pure_pure subsumption_assn_def[symmetric]]
  subsumed_by_impl.refine[FCOMP is_subsumption(8), of \<open>snat_assn' TYPE(64)\<close> \<open>snat_rel' TYPE(64)\<close> unat_lit_rel, unfolded the_pure_pure subsumption_assn_def[symmetric]]
  strengthened_on_lit_impl.refine[FCOMP is_subsumption(9), of unat_lit_assn \<open>snat_rel' TYPE(64)\<close> \<open>snat_rel' TYPE(64)\<close>, unfolded the_pure_pure subsumption_assn_def[symmetric]]

lemma fold_is_NONE: \<open>x = NONE \<longleftrightarrow> is_NONE x\<close> \<open>NONE = x \<longleftrightarrow> is_NONE x\<close>
  by (auto simp: is_NONE_def)

lemma isa_subsume_clauses_match2_alt_def:
  \<open>isa_subsume_clauses_match2 C' C N D = do {
  ASSERT (isa_subsume_clauses_match2_pre C' C N D);
  n \<leftarrow> mop_arena_length_st N C';
  ASSERT (n \<le> length (get_clauses_wl_heur N));
  (i, st) \<leftarrow> WHILE\<^sub>T\<^bsup> \<lambda>(i,s). True\<^esup> (\<lambda>(i, st). i < n\<and> st \<noteq> NONE)
    (\<lambda>(i, st). do {
      ASSERT (i < n);
      L \<leftarrow> mop_arena_lit2 (get_clauses_wl_heur N) C' i;
      lin \<leftarrow> mop_cch_in L D;
      if lin
      then RETURN (i+1, st)
      else do {
      lin \<leftarrow> mop_cch_in (-L) D;
      if lin
      then if is_subsumed st
      then do {mop_free st; RETURN (i+1, STRENGTHENED_BY L C')}
      else do {mop_free st; RETURN (i+1, NONE)}
      else do {mop_free st; RETURN (i+1, NONE)}
    }})
     (0, SUBSUMED_BY C');
  RETURN st
  }\<close>
  unfolding isa_subsume_clauses_match2_def mop_free_def bind_to_let_conv Let_def
  by auto

schematic_goal mk_free_lbd_assn[sepref_frame_free_rules]: \<open>MK_FREE subsumption_assn ?fr\<close>
  unfolding subsumption_assn_def by synthesize_free+


lemma [safe_constraint_rules]: \<open>CONSTRAINT is_pure subsumption_assn\<close>
  unfolding subsumption_assn_def by auto

sepref_register isa_subsume_clauses_match2 
sepref_def isa_subsume_clauses_match2_impl
  is \<open>uncurry3 isa_subsume_clauses_match2\<close>
  :: \<open>sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a  isasat_bounded_assn\<^sup>k *\<^sub>a cch_assn\<^sup>k \<rightarrow>\<^sub>a subsumption_assn\<close>
  unfolding isa_subsume_clauses_match2_alt_def fold_is_NONE
    mop_access_lit_in_clauses_heur_def[symmetric]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_def mop_cch_remove_one_impl
  is \<open>uncurry mop_cch_remove_one\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a cch_assn\<^sup>d \<rightarrow>\<^sub>a cch_assn\<close>
  unfolding mop_cch_remove_one_def
  by sepref

sepref_register mop_cch_remove_one mop_arena_status_st mop_arena_promote_st

(*TODO share with propagation!*)
sepref_def swap_lits_impl is \<open>uncurry3 mop_arena_swap\<close>
  :: \<open>sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>d \<rightarrow>\<^sub>a arena_fast_assn\<close>
  unfolding mop_arena_swap_def swap_lits_pre_def
  unfolding gen_swap
  by sepref

sepref_def mop_cch_remove_all_clauses_impl
  is \<open>uncurry2 mop_cch_remove_all_clauses\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a cch_assn\<^sup>d \<rightarrow>\<^sub>a cch_assn\<close>
  unfolding mop_cch_remove_all_clauses_def mop_access_lit_in_clauses_heur_def[symmetric]
    mop_arena_length_st_def[symmetric]
  supply [dest] = isasat_bounded_assn_length_arenaD
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_register ASize

lemma arena_is_valid_clause_idxD:
  assumes \<open>arena_is_valid_clause_idx a b\<close>
    \<open>rdomp (al_assn arena_el_impl_assn) a\<close>
    \<open>j \<le> arena_length a b\<close>
  shows \<open>j - 2  < max_unat 32\<close>
proof -
  obtain N vdom where
    \<open>valid_arena a N vdom\<close> and
    \<open>b \<in># dom_m N\<close>
    using assms(1) unfolding arena_is_valid_clause_idx_def
    by auto
  then have eq: \<open>length (N \<propto> b) = arena_length a b\<close> and
    le: \<open>b < length a\<close> and
    size: \<open>is_Size (a ! (b - SIZE_SHIFT))\<close>
    by (auto simp: arena_lifting)

  have \<open>i<length a \<Longrightarrow> rdomp arena_el_impl_assn (a ! i)\<close> for i
    using rdomp_al_dest'[OF assms(2)]
    by auto
  from this[of \<open>b - SIZE_SHIFT\<close>] have \<open>rdomp arena_el_impl_assn (a ! (b - SIZE_SHIFT))\<close>
    using le by auto
  then have \<open>length (N \<propto> b) \<le> unat32_max + 2\<close>
    using size eq unfolding rdomp_pure
    apply (auto simp: rdomp_def arena_el_impl_rel_def is_Size_def
       comp_def pure_def unat_rel_def unat.rel_def br_def arena_el_rel_def
       arena_length_def unat32_max_def)
     subgoal for x
       using unat_lt_max_unat[of x]
       apply (auto simp: max_unat_def)
       done
    done
  then show ?thesis
    using assms POS_SHIFT_def
    unfolding isa_update_pos_pre_def
    by (auto simp: arena_is_valid_clause_idx_def arena_lifting eq
       unat32_max_def max_unat_def)
qed

lemma arena_is_valid_clause_idxD2: \<open>arena_is_valid_clause_idx b a \<Longrightarrow> a - Suc 0 < length b\<close>
  \<open>arena_is_valid_clause_idx b a \<Longrightarrow> MAX_LENGTH_SHORT_CLAUSE < arena_length b a \<Longrightarrow> 3 \<le> a\<close>
  \<open>arena_is_valid_clause_idx b a \<Longrightarrow> MAX_LENGTH_SHORT_CLAUSE < arena_length b a \<Longrightarrow> a - 3 < length b\<close>
  using arena_lengthI(2) less_imp_diff_less apply blast
  apply (auto simp: arena_is_valid_clause_idx_def header_size_def arena_lifting split: if_splits dest: arena_lifting(1)[of _ _ _ a])
  apply (metis arena_header_size_def arena_lifting(1) valid_arena_header_size)
  using valid_arena_def by fastforce

sepref_def mop_arena_shorten_impl
  is \<open>uncurry2 mop_arena_shorten\<close>
  :: \<open>sint64_nat_assn\<^sup>k  *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>d \<rightarrow>\<^sub>a arena_fast_assn\<close>
  unfolding mop_arena_shorten_def arena_shorten_def arena_shorten_pre_def SIZE_SHIFT_def POS_SHIFT_def
    arena_is_valid_clause_idxD2
  supply [intro] = arena_lengthI arena_is_valid_clause_idxD arena_is_valid_clause_idxD2
  apply (rewrite at \<open>APos \<hole>\<close> unat_const_fold[where 'a=32])
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  apply (rewrite at \<open>If _ (_[_ := ASize \<hole>, _ := _]) _\<close> annot_snat_unat_downcast[where 'l=32])
  apply (rewrite at \<open>If _ _ (_[_ := ASize \<hole>])\<close> annot_snat_unat_downcast[where 'l=32])
  by sepref

sepref_def remove_lit_from_clause_impl
  is \<open>uncurry2 remove_lit_from_clause\<close>
  :: \<open>arena_fast_assn\<^sup>d *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a arena_fast_assn\<close>
  unfolding remove_lit_from_clause_def if_not_swap
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

lemma remove_lit_from_clause_st_alt_def: \<open>remove_lit_from_clause_st S C L = do {
    let (N, S) = extract_arena_wl_heur S;
    N \<leftarrow> remove_lit_from_clause N C L;
    RETURN (update_arena_wl_heur N S)
}\<close>
  by (auto simp: remove_lit_from_clause_st_def state_extractors push_to_tvdom_st_def
         split: isasat_int_splits)

sepref_def remove_lit_from_clause_st_impl
  is \<open>uncurry2 remove_lit_from_clause_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>d *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding remove_lit_from_clause_st_alt_def
  by sepref

sepref_register remove_lit_from_clause_st

lemma mark_garbage_heur_as_subsumed_alt_def:
  \<open>mark_garbage_heur_as_subsumed C S\<^sub>0 = (do{
    ASSERT (arena_is_valid_clause_vdom (get_clauses_wl_heur S\<^sub>0) C);
    _ \<leftarrow> log_del_clause_heur S\<^sub>0 C;
    ASSERT (mark_garbage_pre (get_clauses_wl_heur S\<^sub>0, C));
    size \<leftarrow> mop_arena_length (get_clauses_wl_heur S\<^sub>0) C;
    let (N', S) = extract_arena_wl_heur S\<^sub>0;
    ASSERT (N' = get_clauses_wl_heur S\<^sub>0);
    let st = arena_status N' C = IRRED;
    let N' = extra_information_mark_to_delete (N') C;
    let (lcount, S) = extract_lcount_wl_heur S;
    ASSERT(\<not>st \<longrightarrow> clss_size_lcount lcount \<ge> 1);
    let lcount = (if st then lcount else (clss_size_decr_lcount lcount));
    let (stats, S) = extract_stats_wl_heur S;
    let stats = (if st then decr_irred_clss stats else stats);
    let S = update_arena_wl_heur N' S;
    let S = update_lcount_wl_heur lcount S;
    let S = update_stats_wl_heur stats S;
    let S = incr_wasted_st (of_nat size) S;
    RETURN S
  })\<close>
  by (auto simp: mark_garbage_heur_as_subsumed_def Let_def state_extractors push_to_tvdom_st_def
    intro!: bind_cong[OF refl]
    split: isasat_int_splits)

sepref_def mark_garbage_heur_as_subsumed_impl
  is \<open>uncurry mark_garbage_heur_as_subsumed\<close>
  :: \<open>sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  supply of_nat_snat[sepref_import_param]
  unfolding mark_garbage_heur_as_subsumed_alt_def
    mop_arena_length_st_def[symmetric]
  by sepref

sepref_def isa_strengthen_clause_wl2_impl
  is \<open>uncurry3 isa_strengthen_clause_wl2\<close>
  :: \<open>sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding isa_strengthen_clause_wl2_def mop_arena_status_st_def[symmetric]
    mop_arena_length_st_def[symmetric]
  apply (subst incr_forward_strengthened_st_def[symmetric])+
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref


lemma subsumption_cases_split:
  \<open>(case s of SUBSUMED_BY s \<Rightarrow> f s | STRENGTHENED_BY x y \<Rightarrow> g x y | NONE \<Rightarrow> h) =
  (if is_NONE s then h else if is_subsumed s then f (subsumed_by s) else do {ASSERT (is_strengthened s); g (strengthened_on_lit s) (strengthened_by s)})\<close>
  by (auto simp: is_NONE_def split: subsumption.splits)

sepref_register isa_strengthen_clause_wl2 isa_subsume_or_strengthen_wl
sepref_def isa_subsume_or_strengthen_wl_impl
  is \<open>uncurry2 isa_subsume_or_strengthen_wl\<close>
  :: \<open>sint64_nat_assn\<^sup>k *\<^sub>a subsumption_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding isa_subsume_or_strengthen_wl_def subsumption_cases_split mop_arena_status_st_def[symmetric]
    incr_forward_subsumed_st_def[symmetric]
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

lemma isa_forward_set_budget_alt_def:
  \<open>isa_forward_set_budget S = do {
     let (stats, S) = extract_stats_wl_heur S;
     let delta = stats_propagations stats;
     let delta = (if delta < subsumemineff then subsumemineff else delta);
     let delta = (if delta > subsumemaxeff then subsumemaxeff else delta);
     let budget = delta + forward_budget stats;
     let stats = set_forward_budget budget stats;
     RETURN (update_stats_wl_heur stats S)
  }\<close>
  by (auto simp: isa_forward_set_budget_def Let_def state_extractors push_to_tvdom_st_def
    intro!: bind_cong[OF refl]
    split: isasat_int_splits)
sepref_def isa_forward_set_budget_impl
  is \<open>isa_forward_set_budget\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding isa_forward_set_budget_alt_def subsumemineff_def subsumemaxeff_def
  by sepref

lemma isa_forward_subsumption_one_wl_alt_def:
  \<open>isa_forward_subsumption_one_wl = (\<lambda>C D L S. do {
  ASSERT (isa_forward_subsumption_one_wl_pre C L S);
  ASSERT (nat_of_lit L < length (get_occs S));
  n \<leftarrow> mop_cocc_list_length (get_occs S) L;
  (i, s) \<leftarrow>
    WHILE\<^sub>T\<^bsup> isa_forward_subsumption_one_wl2_inv S C L \<^esup> (\<lambda>(i, s). i < n \<and> s = NONE)
    (\<lambda>(i, s). do {
      ASSERT (i < n);
      C' \<leftarrow> mop_cocc_list_at (get_occs S) L i;
      status \<leftarrow> mop_arena_status (get_clauses_wl_heur S) C';
      if status = DELETED
      then RETURN (i+1, s)
      else do  {
        s \<leftarrow> isa_subsume_clauses_match2 C' C S D;
       RETURN (i+1, s)
      }
    })
        (0, NONE);
  D \<leftarrow> (if s \<noteq> NONE then mop_cch_remove_all_clauses S C D else RETURN D);
  S \<leftarrow> (if is_strengthened s then isa_maybe_push_to_occs_list_st C S else RETURN S);
  S \<leftarrow> isa_subsume_or_strengthen_wl C s S;
  let (stats, S) = extract_stats_wl_heur S;
  let stats = incr_forward_subchecks_by (of_nat i) stats;
  let S = update_stats_wl_heur stats S;
  RETURN (S, s, D)
  })\<close>
  by (auto simp: isa_forward_subsumption_one_wl_def Let_def state_extractors push_to_tvdom_st_def
    intro!: bind_cong[OF refl] ext
    split: isasat_int_splits)

sepref_def isa_forward_subsumption_one_wl_impl
  is \<open>uncurry3 isa_forward_subsumption_one_wl\<close>
  :: \<open>[\<lambda>((_, _), S). isasat_fast_relaxed S]\<^sub>asint64_nat_assn\<^sup>k *\<^sub>a  cch_assn\<^sup>d *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn \<times>\<^sub>a subsumption_assn \<times>\<^sub>a cch_assn\<close>
  supply [dest] = rdomp_isasat_bounded_assn_length_avdomD isasat_bounded_assn_length_arenaD
  supply [[goals_limit=1]]
  unfolding isa_forward_subsumption_one_wl_alt_def get_occs_list_at_def[symmetric] fold_is_NONE
    mop_access_lit_in_clauses_heur_def[symmetric] length_occs_at_def[symmetric] mop_arena_status_st_def[symmetric]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  apply (rewrite at \<open>of_nat \<hole>\<close> annot_snat_unat_conv)
  by sepref

lemma isa_try_to_forward_subsume_wl_invI:
  \<open>isa_try_to_forward_subsume_wl_inv S C (i, changed, break, D, T)\<Longrightarrow> isasat_fast_relaxed S \<Longrightarrow> isasat_fast_relaxed T\<close>
  unfolding isa_try_to_forward_subsume_wl_inv_def prod.simps
  by normalize_goal+ (auto simp add: isasat_fast_relaxed_def)

lemma isasat_bounded_assn_get_vdomD: \<open>rdomp isasat_bounded_assn a \<Longrightarrow>  length (get_tvdom a) < max_snat 64\<close>
  using al_assn_boundD[of sint64_nat_assn, where 'l=\<open>64\<close>, of \<open>get_tvdom a\<close>]
  apply -
  unfolding rdomp_def
  apply normalize_goal+
  apply (cases a, case_tac xa; cases \<open>get_aivdom a\<close>)
  apply (auto 7 5 simp: isasat_bounded_assn_def snat64_max_def max_snat_def aivdom_assn_def
         code_hider_assn_def hr_comp_def code_hider_rel_def import_param_3 pred_lift_def
      split: isasat_int_splits
      dest!: mod_starD al_assn_boundD[of sint64_nat_assn, where 'l=\<open>64\<close>])
  apply auto
  done

sepref_def isa_try_to_forward_subsume_wl2_impl
  is \<open>uncurry3 isa_try_to_forward_subsume_wl2\<close>
  :: \<open>[\<lambda>(((_, _), _), S). isasat_fast_relaxed S]\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a  cch_assn\<^sup>d *\<^sub>a (al_assn' TYPE(64) sint64_nat_assn)\<^sup>d *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>
  cch_assn \<times>\<^sub>a al_assn' TYPE(64) sint64_nat_assn \<times>\<^sub>a isasat_bounded_assn\<close>
  unfolding isa_try_to_forward_subsume_wl2_def
    mop_access_lit_in_clauses_heur_def[symmetric] Let_def[of \<open>is_strengthened _\<close>] fold_is_NONE
     Let_def[of \<open>if is_strengthened _ then _ else _\<close>]
  supply [[goals_limit=1]]
  supply [intro] = isa_try_to_forward_subsume_wl_invI
  supply [dest] = isasat_bounded_assn_get_vdomD
  apply (rewrite at \<open>if _ then mark_clause_for_unit_as_unchanged \<hole> else _\<close> unat_const_fold[where 'a=\<open>64\<close>])
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

lemma empty_occs2_st_alt_def:
  \<open>empty_occs2_st S = do {
  let (occs, S) = extract_occs_wl_heur S;
  occs \<leftarrow> empty_occs2 occs;
  RETURN (update_occs_wl_heur occs S)
  }\<close>
  by (auto simp: empty_occs2_st_def Let_def state_extractors
    intro!: bind_cong[OF refl]
    split: isasat_int_splits)


sepref_def empty_occs2_impl
  is \<open>empty_occs2\<close>
  :: \<open>occs_assn\<^sup>d \<rightarrow>\<^sub>a occs_assn\<close>
  unfolding empty_occs2_def fold_op_list_list_take op_list_list_len_def[symmetric]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_def empty_occs2_st_impl
  is \<open>empty_occs2_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding empty_occs2_st_alt_def
  by sepref

lemma isa_forward_subsumption_all_wl_invI:
  \<open>isa_forward_subsumption_all_wl_inv R S (i, D, shrunken, T) \<Longrightarrow> isasat_fast_relaxed R \<Longrightarrow> isasat_fast_relaxed T\<close>
  unfolding isa_forward_subsumption_all_wl_inv_def prod.simps
  apply normalize_goal+
  by (auto simp: isasat_fast_relaxed_def)

sepref_register empty_occs2_st forward_subsumption_finalize schedule_next_subsume_st

sepref_def mark_added_clause_heur2_impl
  is \<open>uncurry mark_added_clause_heur2\<close>
  :: \<open>isasat_bounded_assn\<^sup>d *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding mark_added_clause_heur2_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

lemma schedule_next_subsume_st_alt_def:
  \<open>schedule_next_subsume_st b S = (let (heur, S) = extract_heur_wl_heur S;
      heur = schedule_next_subsume b  heur in
      update_heur_wl_heur heur S)\<close>
  by (auto simp: schedule_next_subsume_st_def Let_def state_extractors
    split: isasat_int_splits)

sepref_def schedule_next_subsume_st
  is \<open>uncurry (RETURN oo schedule_next_subsume_st)\<close>
  :: \<open>word64_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding schedule_next_subsume_st_alt_def
  by sepref

sepref_def forward_subsumption_finalize_impl
  is \<open>uncurry forward_subsumption_finalize\<close>
  :: \<open>(al_assn' TYPE(64) sint64_nat_assn)\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding forward_subsumption_finalize_def
  supply [[goals_limit=1]]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_def isa_forward_subsumption_all_impl
  is isa_forward_subsumption_all
  :: \<open>[isasat_fast_relaxed]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  supply [intro] = isa_forward_subsumption_all_wl_invI
  unfolding isa_forward_subsumption_all_def
    access_tvdom_at_def[symmetric] length_tvdom_def[symmetric]
    length_watchlist_raw_def[symmetric]
    al_fold_custom_empty[where 'l=64]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref


lemma get_subsumption_opts_alt_def:
  \<open>get_subsumption_opts S = (case S of IsaSAT M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs \<Rightarrow> opts_subsumption opts)\<close>
  by (cases S) (auto simp: get_subsumption_opts_def)

sepref_def get_subsumption_opts_impl
  is \<open>RETURN o get_subsumption_opts\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding get_subsumption_opts_alt_def
  by sepref

lemma next_subsume_schedule_st_def:
  \<open>next_subsume_schedule_st S = (case S of IsaSAT M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs \<Rightarrow> next_subsume_schedule heur)\<close>
  by (cases S) (auto simp: next_subsume_schedule_st_def)

sepref_def next_subsume_schedule_st_impl
  is \<open>RETURN o next_subsume_schedule_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding next_subsume_schedule_st_def
  by sepref

sepref_def should_subsume_st
  is \<open>RETURN o should_subsume_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding should_subsume_st_def
  by sepref

sepref_def isa_forward_subsume_impl
  is isa_forward_subsume
  :: \<open>[isasat_fast_relaxed]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding isa_forward_subsume_def
  by sepref

end