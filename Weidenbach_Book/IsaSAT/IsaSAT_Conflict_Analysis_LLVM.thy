theory IsaSAT_Conflict_Analysis_LLVM
imports IsaSAT_Conflict_Analysis IsaSAT_VMTF_LLVM IsaSAT_Setup_LLVM IsaSAT_LBD_LLVM
begin

sepref_def maximum_level_removed_eq_count_dec_fast_code
  is \<open>uncurry (maximum_level_removed_eq_count_dec_heur)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding maximum_level_removed_eq_count_dec_heur_def
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref

lemma is_decided_hd_trail_wl_heur_alt_def:
  \<open>is_decided_hd_trail_wl_heur = (\<lambda>((M, xs, lvls, reasons, k), _).
      let r = reasons ! (atm_of (last M)) in
      r = DECISION_REASON)\<close>
  unfolding is_decided_hd_trail_wl_heur_def last_trail_pol_def
  by (auto simp: is_decided_hd_trail_wl_heur_pre_def last_trail_pol_def
     Let_def intro!: ext split: if_splits)

sepref_def is_decided_hd_trail_wl_fast_code
  is \<open>RETURN o is_decided_hd_trail_wl_heur\<close>
  :: \<open>[is_decided_hd_trail_wl_heur_pre]\<^sub>a isasat_bounded_assn\<^sup>k \<rightarrow> bool1_assn\<close>
  supply [[goals_limit=1]]
  unfolding is_decided_hd_trail_wl_heur_alt_def isasat_bounded_assn_def
    is_decided_hd_trail_wl_heur_pre_def last_trail_pol_def trail_pol_fast_assn_def
    last_trail_pol_pre_def
  by sepref

sepref_def lit_and_ann_of_propagated_st_heur_fast_code
  is \<open>lit_and_ann_of_propagated_st_heur\<close>
  :: \<open>[\<lambda>_. True]\<^sub>a
       isasat_bounded_assn\<^sup>k \<rightarrow> (unat_lit_assn \<times>\<^sub>a sint64_nat_assn)\<close>
  supply [[goals_limit=1]]
  supply get_trail_wl_heur_def[simp]
  unfolding lit_and_ann_of_propagated_st_heur_def isasat_bounded_assn_def
    lit_and_ann_of_propagated_st_heur_pre_def trail_pol_fast_assn_def
  unfolding fold_tuple_optimizations
  by sepref

sepref_def atm_is_in_conflict_st_heur_fast_code
  is \<open>uncurry (atm_is_in_conflict_st_heur)\<close>
  :: \<open>[\<lambda>_. True]\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>k \<rightarrow> bool1_assn\<close>
  supply [[goals_limit=1]]
  unfolding atm_is_in_conflict_st_heur_def atm_is_in_conflict_st_heur_pre_def isasat_bounded_assn_def
    atm_in_conflict_lookup_def trail_pol_fast_assn_def NOTIN_def[symmetric]
   is_NOTIN_def[symmetric] conflict_option_rel_assn_def lookup_clause_rel_assn_def
  unfolding fold_tuple_optimizations atm_in_conflict_lookup_pre_def
  by sepref

lemma tl_state_wl_heurI: \<open>tl_state_wl_heur_pre (a, b) \<Longrightarrow> fst a \<noteq> []\<close>
  \<open>tl_state_wl_heur_pre (a, b) \<Longrightarrow> tl_trailt_tr_pre a\<close>
  \<open>tl_state_wl_heur_pre (a1', a1'a, a1'b, a1'c, a1'd, a1'e, a1'f, a2'f) \<Longrightarrow>
       vmtf_unset_pre (atm_of (lit_of_last_trail_pol a1')) a1'e\<close>
  by (auto simp: tl_state_wl_heur_pre_def tl_trailt_tr_pre_def
    vmtf_unset_pre_def lit_of_last_trail_pol_def)

lemma tl_state_wl_heur_alt_def:
  \<open>tl_state_wl_heur = (\<lambda>(M, N, D, WS, Q, vmtf, \<phi>, clvls). do {
       ASSERT(tl_state_wl_heur_pre (M, N, D, WS, Q, vmtf, \<phi>, clvls));
       let L = (atm_of (lit_of_last_trail_pol M));
       RETURN (False, (tl_trailt_tr M, N, D, WS, Q, isa_vmtf_unset L vmtf, \<phi>, clvls))
  })\<close>
  by (auto simp: tl_state_wl_heur_def)

sepref_def tl_state_wl_heur_fast_code
  is \<open>tl_state_wl_heur\<close>
  :: \<open>[\<lambda>_. True]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> bool1_assn \<times>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]] if_splits[split] tl_state_wl_heurI[dest]
  unfolding tl_state_wl_heur_alt_def[abs_def] isasat_bounded_assn_def get_trail_wl_heur_def
    vmtf_unset_def bind_ref_tag_def short_circuit_conv
  unfolding fold_tuple_optimizations
  apply (rewrite in \<open>ASSERT \<hole>\<close> fold_tuple_optimizations[symmetric])+
  by sepref


definition extract_values_of_lookup_conflict :: \<open>conflict_option_rel \<Rightarrow> bool\<close> where
\<open>extract_values_of_lookup_conflict = (\<lambda>(b, (_, xs)). b)\<close>


sepref_def extract_values_of_lookup_conflict_impl
  is \<open>RETURN o extract_values_of_lookup_conflict\<close>
  :: \<open>conflict_option_rel_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding extract_values_of_lookup_conflict_def conflict_option_rel_assn_def
    lookup_clause_rel_assn_def
  by sepref

sepref_register extract_values_of_lookup_conflict
declare extract_values_of_lookup_conflict_impl.refine[sepref_fr_rules]

sepref_register isasat_lookup_merge_eq2 update_confl_tl_wl_heur

lemma update_confl_tl_wl_heur_alt_def:
  \<open>update_confl_tl_wl_heur = (\<lambda>L C (M, N, bnxs, Q, W, vm, clvls, cach, lbd, outl, stats). do {
      (N, lbd) \<leftarrow> calculate_LBD_heur_st M N lbd C;
      ASSERT (clvls \<ge> 1);
      let L' = atm_of L;
      ASSERT(arena_is_valid_clause_idx N C);
      (bnxs, clvls, outl) \<leftarrow>
        if arena_length N C = 2 then isasat_lookup_merge_eq2 L M N C bnxs clvls outl
        else isa_resolve_merge_conflict_gt2 M N C bnxs clvls outl;
      let b = extract_values_of_lookup_conflict bnxs;
      let nxs = the_lookup_conflict bnxs;
      ASSERT(curry lookup_conflict_remove1_pre L nxs \<and> clvls \<ge> 1);
      let nxs = lookup_conflict_remove1 L nxs;
      ASSERT(arena_act_pre N C);
      ASSERT(vmtf_unset_pre L' vm);
      ASSERT(tl_trailt_tr_pre M);
      RETURN (False, (tl_trailt_tr M, N, (None_lookup_conflict b nxs), Q, W, isa_vmtf_unset L' vm,
          clvls - 1, cach, lbd, outl, stats))
   })\<close>
  unfolding update_confl_tl_wl_heur_def
  by (auto intro!: ext bind_cong simp: None_lookup_conflict_def the_lookup_conflict_def
    extract_values_of_lookup_conflict_def Let_def)

sepref_def update_confl_tl_wl_fast_code
  is \<open>uncurry2 update_confl_tl_wl_heur\<close>
  :: \<open>[\<lambda>((i, L), S). isasat_fast S]\<^sub>a
   unat_lit_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>aisasat_bounded_assn\<^sup>d \<rightarrow> bool1_assn \<times>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]] isasat_fast_length_leD[intro]
  unfolding update_confl_tl_wl_heur_alt_def isasat_bounded_assn_def
    PR_CONST_def
  apply (rewrite at \<open>If (_ = \<hole>)\<close> snat_const_fold[where 'a=64])
  apply (annot_unat_const \<open>TYPE (32)\<close>)
  unfolding fold_tuple_optimizations
  by sepref

declare update_confl_tl_wl_fast_code.refine[sepref_fr_rules]

sepref_register is_in_conflict_st atm_is_in_conflict_st_heur
sepref_def skip_and_resolve_loop_wl_D_fast
  is \<open>skip_and_resolve_loop_wl_D_heur\<close>
  :: \<open>[\<lambda>S. isasat_fast S]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
    skip_and_resolve_loop_wl_DI[intro]
    isasat_fast_after_skip_and_resolve_loop_wl_D_heur_inv[intro]
  unfolding skip_and_resolve_loop_wl_D_heur_def
  unfolding fold_tuple_optimizations
  apply (rewrite at \<open>\<not>_ \<and> \<not> _\<close> short_circuit_conv)
  by sepref (* slow *)

declare skip_and_resolve_loop_wl_D_fast.refine[sepref_fr_rules]

experiment
begin
  export_llvm
    get_count_max_lvls_heur_impl
    maximum_level_removed_eq_count_dec_fast_code
    is_decided_hd_trail_wl_fast_code
    lit_and_ann_of_propagated_st_heur_fast_code
    is_in_option_lookup_conflict_code
    atm_is_in_conflict_st_heur_fast_code
    lit_of_last_trail_fast_code
    tl_state_wl_heur_fast_code
    None_lookup_conflict_impl
    extract_values_of_lookup_conflict_impl
    update_confl_tl_wl_fast_code
    skip_and_resolve_loop_wl_D_fast

end



end