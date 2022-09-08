theory IsaSAT_Simplify_Forward_Subsumption_LLVM
  imports
    IsaSAT_Simplify_Forward_Subsumption
    IsaSAT_Setup_LLVM
    IsaSAT_Trail_LLVM
    IsaSAT_Proofs_LLVM
begin

no_notation WB_More_Refinement.fref (\<open>[_]\<^sub>f _ \<rightarrow> _\<close> [0,60,60] 60)
no_notation WB_More_Refinement.freft (\<open>_ \<rightarrow>\<^sub>f _\<close> [60,60] 60)

(*TODO: kill mop_arena_lit2_st*)
sepref_def isa_all_lit_clause_unset
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
  apply (auto simp: isasat_bounded_assn_def sint64_max_def max_snat_def length_avdom_def
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
  find_best_subsumption_candidate 

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

sepref_def isa_good_candidate_for_subsumption_impl
  is \<open>uncurry isa_good_candidate_for_subsumption\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding isa_good_candidate_for_subsumption_def
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

sepref_register isa_good_candidate_for_subsumption sort_cands_by_length

term sort_cands_by_length
lemma isa_populate_occs_inv_isasat_fast_relaxedI:
  \<open>isa_populate_occs_inv x cands (a1', a2') \<Longrightarrow> isasat_fast_relaxed x \<Longrightarrow> isasat_fast_relaxed a2'\<close>
  by (auto simp: isa_populate_occs_inv_def isasat_fast_relaxed_def)

sepref_def isa_populate_occs_code
  is isa_populate_occs
  :: \<open>[isasat_fast_relaxed]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  supply [dest] = rdomp_isasat_bounded_assn_length_avdomD
  supply [intro] = isa_populate_occs_inv_isasat_fast_relaxedI
  unfolding isa_populate_occs_def access_avdom_at_def[symmetric] length_avdom_def[symmetric]
    al_fold_custom_empty[where 'l=64] Let_def[of \<open>get_avdom _\<close>] Let_def[of \<open>get_occs _\<close>]
    Let_def[of \<open>get_tvdom _\<close>]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  apply sepref_dbg_side_unfold
  subgoal premises p
apply auto
  oops

thm isa_populate_occs_def
thm access_avdom_at_def
find_theorems get_avdom length
thm isa_forward_subsumption_all_wl2_def
sepref_register isa_forward_subsumption_all_wl2 isa_populate_occs

sepref_register isa_forward_subsumption_all

sepref_def isa_forward_subsumption_all
  is \<open>isa_forward_subsumption_all\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding isa_forward_subsumption_all_def
  by sepref

end