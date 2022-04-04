theory IsaSAT_Conflict_Analysis_LLVM
imports IsaSAT_Conflict_Analysis IsaSAT_VMTF_LLVM IsaSAT_Setup_LLVM IsaSAT_LBD_LLVM
begin

sepref_def maximum_level_removed_eq_count_dec_fast_code
  is \<open>uncurry (maximum_level_removed_eq_count_dec_heur)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding maximum_level_removed_eq_count_dec_heur_def
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref

definition is_decided_trail where \<open>is_decided_trail = (\<lambda>(M, xs, lvls, reasons, k).
      let r = reasons ! (atm_of (last M)) in
      RETURN (r = DECISION_REASON))\<close>

sepref_def is_decided_trail_impl
  is \<open>is_decided_trail\<close>
  :: \<open>[(\<lambda>S. fst S \<noteq> [] \<and> last_trail_pol_pre S)]\<^sub>a trail_pol_fast_assn\<^sup>k \<rightarrow> bool1_assn\<close>
  unfolding is_decided_trail_def trail_pol_fast_assn_def last_trail_pol_pre_def
  by sepref

definition is_decided_hd_trail_wl_fast_code :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>is_decided_hd_trail_wl_fast_code = read_trail_wl_heur_code is_decided_trail_impl\<close>
definition ptr_is_decided_hd_trail_wl_fast_code where
  \<open>ptr_is_decided_hd_trail_wl_fast_code = ptr_read0_code is_decided_hd_trail_wl_fast_code\<close>

global_interpretation is_decided_hd: read_trail_param_adder0 where
  f = \<open>is_decided_trail_impl\<close> and
  f' = \<open>is_decided_trail\<close> and
  x_assn = bool1_assn and
  P = \<open>(\<lambda>S. fst S \<noteq> [] \<and> last_trail_pol_pre S)\<close>
  rewrites \<open>read_trail_wl_heur is_decided_trail = RETURN o is_decided_hd_trail_wl_heur\<close> and
  \<open>read_trail_wl_heur_code is_decided_trail_impl = is_decided_hd_trail_wl_fast_code\<close> and
  \<open>case_isasat_int (\<lambda>M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. fst M \<noteq> [] \<and> last_trail_pol_pre M) = is_decided_hd_trail_wl_heur_pre\<close>
  apply unfold_locales
  apply (rule is_decided_trail_impl.refine)
  subgoal
    by (auto simp: read_all_st_def is_decided_hd_trail_wl_heur_def is_decided_trail_def last_trail_pol_def Let_def
      intro!: ext
      split: isasat_int.splits)
  subgoal
    by (auto simp: is_decided_hd_trail_wl_fast_code_def)
  subgoal by (auto simp: is_decided_hd_trail_wl_heur_pre_def intro!: ext split: isasat_int.splits)
  done


definition lit_and_ann_of_propagated_trail_heur
   :: \<open>_ \<Rightarrow> (nat literal \<times> nat) nres\<close>
where
  \<open>lit_and_ann_of_propagated_trail_heur = (\<lambda>(M, _, _, reasons, _) . do {
     ASSERT(M \<noteq> [] \<and> atm_of (last M) < length reasons);
     RETURN (last M, reasons ! (atm_of (last M)))})\<close>

sepref_def lit_and_ann_of_propagated_trail_heur_impl
  is lit_and_ann_of_propagated_trail_heur
  :: \<open>trail_pol_fast_assn\<^sup>k \<rightarrow>\<^sub>a (unat_lit_assn \<times>\<^sub>a sint64_nat_assn)\<close>
  unfolding lit_and_ann_of_propagated_trail_heur_def trail_pol_fast_assn_def
  by sepref

definition lit_and_ann_of_propagated_st_heur_fast_code :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>lit_and_ann_of_propagated_st_heur_fast_code = read_trail_wl_heur_code lit_and_ann_of_propagated_trail_heur_impl\<close>
definition ptr_lit_and_ann_of_propagated_st_heur_fast_code :: \<open>_\<close> where
  \<open>ptr_lit_and_ann_of_propagated_st_heur_fast_code = ptr_read0_code lit_and_ann_of_propagated_st_heur_fast_code\<close>

global_interpretation lit_and_of_proped_lit: read_trail_param_adder0 where
  f = \<open>lit_and_ann_of_propagated_trail_heur_impl\<close> and
  f' = \<open>lit_and_ann_of_propagated_trail_heur\<close> and
  x_assn = \<open>unat_lit_assn \<times>\<^sub>a sint64_nat_assn\<close> and
  P = \<open>(\<lambda>S. True)\<close>
  rewrites \<open>read_trail_wl_heur lit_and_ann_of_propagated_trail_heur = lit_and_ann_of_propagated_st_heur\<close> and
  \<open>read_trail_wl_heur_code lit_and_ann_of_propagated_trail_heur_impl = lit_and_ann_of_propagated_st_heur_fast_code\<close>
  apply unfold_locales
  apply (rule lit_and_ann_of_propagated_trail_heur_impl.refine)
  subgoal
    by (auto simp: read_all_st_def lit_and_ann_of_propagated_st_heur_def lit_and_ann_of_propagated_trail_heur_def last_trail_pol_def Let_def
      intro!: ext
      split: isasat_int.splits)
  subgoal
    by (auto simp: lit_and_ann_of_propagated_st_heur_fast_code_def)
  done


definition atm_is_in_conflict_confl_heur :: \<open>_ \<Rightarrow> nat literal \<Rightarrow>bool nres\<close> where
  \<open>atm_is_in_conflict_confl_heur = (\<lambda>(_, D) L. do {
     ASSERT (atm_in_conflict_lookup_pre (atm_of L) D); RETURN (\<not>atm_in_conflict_lookup (atm_of L) D) })\<close>

sepref_def atm_is_in_conflict_confl_heur_impl
  is \<open>uncurry atm_is_in_conflict_confl_heur\<close>
  :: \<open>conflict_option_rel_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k  \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding atm_is_in_conflict_confl_heur_def conflict_option_rel_assn_def
  by sepref

definition atm_is_in_conflict_st_heur_fast_code :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>atm_is_in_conflict_st_heur_fast_code = (\<lambda>N C. read_conflict_wl_heur_code (\<lambda>M. atm_is_in_conflict_confl_heur_impl M C) N)\<close>
definition ptr_atm_is_in_conflict_st_heur_fast_code :: \<open>_\<close> where
  \<open>ptr_atm_is_in_conflict_st_heur_fast_code = ptr_read_code atm_is_in_conflict_st_heur_fast_code\<close>


definition atm_is_in_conflict_st_heur' :: \<open>isasat \<Rightarrow> nat literal \<Rightarrow> bool nres\<close> where
  \<open>atm_is_in_conflict_st_heur' S L = (\<lambda>(_, D). do {
     ASSERT (atm_in_conflict_lookup_pre (atm_of L) D); RETURN (\<not>atm_in_conflict_lookup (atm_of L) D) }) (get_conflict_wl_heur S)\<close>

global_interpretation atm_in_conflict: read_conflict_param_adder where
  f = \<open> \<lambda>S L. atm_is_in_conflict_confl_heur_impl L S\<close> and
  f' = \<open>\<lambda>S L. atm_is_in_conflict_confl_heur L S\<close> and
  x_assn = \<open>bool1_assn\<close> and
  P = \<open>(\<lambda>_ _. True)\<close> and
  R = \<open>unat_lit_rel\<close>
  rewrites \<open>(\<lambda>N C. read_conflict_wl_heur (\<lambda>M. atm_is_in_conflict_confl_heur M C) N) = atm_is_in_conflict_st_heur'\<close> and
  \<open>(\<lambda>N C. read_conflict_wl_heur_code (\<lambda>M. atm_is_in_conflict_confl_heur_impl M C) N) = atm_is_in_conflict_st_heur_fast_code\<close>
  apply unfold_locales
  apply (subst lambda_comp_true,
     rule atm_is_in_conflict_confl_heur_impl.refine)
  subgoal
    by (auto simp: read_all_st_def atm_is_in_conflict_st_heur'_def atm_is_in_conflict_confl_heur_def Let_def
      intro!: ext
      split: isasat_int.splits)
  subgoal
    by (auto simp: atm_is_in_conflict_st_heur_fast_code_def)
  done

lemmas [unfolded lambda_comp_true, sepref_fr_rules] =
  is_decided_hd.refine lit_and_of_proped_lit.refine atm_in_conflict.refine
  ptr_read0_loc.refine[unfolded ptr_read0_loc_def, OF is_decided_hd.refine[unfolded lambda_comp_true],
  unfolded ptr_is_decided_hd_trail_wl_fast_code_def[symmetric] ptr_read0_def]
  ptr_read0_loc.refine[unfolded ptr_read0_loc_def, OF lit_and_of_proped_lit.refine[unfolded lambda_comp_true],
  unfolded ptr_lit_and_ann_of_propagated_st_heur_fast_code_def[symmetric] ptr_read0_def]
  ptr_read_loc.refine[unfolded ptr_read_loc_def, OF atm_in_conflict.refine[unfolded lambda_comp_true],
  unfolded ptr_atm_is_in_conflict_st_heur_fast_code_def[symmetric] ptr_read_def]

lemmas [unfolded inline_direct_return_node_case ptr_read_code_def ptr_read0_code_def, llvm_code] =
  is_decided_hd_trail_wl_fast_code_def[unfolded read_all_st_code_def]
  lit_and_ann_of_propagated_st_heur_fast_code_def[unfolded read_all_st_code_def]
  atm_is_in_conflict_st_heur_fast_code_def[unfolded read_all_st_code_def]
  ptr_atm_is_in_conflict_st_heur_fast_code_def
  ptr_lit_and_ann_of_propagated_st_heur_fast_code_def
  ptr_is_decided_hd_trail_wl_fast_code_def


sepref_def atm_is_in_conflict_st_heur_fast2_code
  is \<open>uncurry (atm_is_in_conflict_st_heur)\<close>
  :: \<open>[\<lambda>_. True]\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>k \<rightarrow> bool1_assn\<close>
  supply [[goals_limit=1]]
  unfolding atm_is_in_conflict_st_heur_def atm_is_in_conflict_st_heur'_def[symmetric]
  by sepref

lemma tl_state_wl_heurI: \<open>tl_state_wl_heur_pre S \<Longrightarrow> fst (get_trail_wl_heur S) \<noteq> []\<close>
  \<open>tl_state_wl_heur_pre S \<Longrightarrow> tl_trailt_tr_pre (get_trail_wl_heur S)\<close>
  \<open>tl_state_wl_heur_pre S \<Longrightarrow>
       vmtf_unset_pre (atm_of (lit_of_last_trail_pol (get_trail_wl_heur S))) (get_vmtf_heur S)\<close>
  by (auto simp: tl_state_wl_heur_pre_def tl_trailt_tr_pre_def Let_def
    vmtf_unset_pre_def lit_of_last_trail_pol_def)

lemma tl_state_wl_heur_alt_def:
  \<open>tl_state_wl_heur = (\<lambda>S\<^sub>0. do {
       ASSERT(tl_state_wl_heur_pre S\<^sub>0);
       let (M, S) = extract_trail_wl_heur S\<^sub>0; let (vm, S) = extract_vmtf_wl_heur S;
       ASSERT (M = get_trail_wl_heur S\<^sub>0);
       ASSERT (vm = get_vmtf_heur S\<^sub>0);
       let L = lit_of_last_trail_pol M;
       let S = update_trail_wl_heur (tl_trailt_tr M) S;
       let S = update_vmtf_wl_heur (isa_vmtf_unset (atm_of L) vm) S;
       RETURN (False, S)
  })\<close>
  by (auto simp: tl_state_wl_heur_def state_extractors intro!: ext split: isasat_int.splits)

sepref_def tl_state_wl_heur_fast_code
  is \<open>tl_state_wl_heur\<close>
  :: \<open>[\<lambda>_. True]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> bool1_assn \<times>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]] if_splits[split] tl_state_wl_heurI[dest]
  unfolding vmtf_unset_def bind_ref_tag_def short_circuit_conv tl_state_wl_heur_alt_def
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
  \<open>update_confl_tl_wl_heur = (\<lambda>L C S\<^sub>0. do {
      let (M, S) = extract_trail_wl_heur S\<^sub>0;
      let (N, S) = extract_arena_wl_heur S;
      let (lbd, S) = extract_lbd_wl_heur S;
      let (outl, S) = extract_outl_wl_heur S;
      let (clvls, S) = extract_clvls_wl_heur S;
      let (vm, S) = extract_vmtf_wl_heur S;
      let (bnxs, S) = extract_conflict_wl_heur S;
      (N, lbd) \<leftarrow> calculate_LBD_heur_st M N lbd C;
      ASSERT (clvls \<ge> 1);
      let L' = atm_of L;
      ASSERT(arena_is_valid_clause_idx N C);
      (bnxs, clvls, outl) \<leftarrow>
        if arena_length N C = 2 then isasat_lookup_merge_eq2 L M N C bnxs clvls outl
        else isa_resolve_merge_conflict_gt2 M N C bnxs clvls outl;
      let b = extract_values_of_lookup_conflict bnxs;
      let nxs = the_lookup_conflict bnxs;
      ASSERT(curry lookup_conflict_remove1_pre L (nxs) \<and> clvls \<ge> 1);
      let (nxs) = lookup_conflict_remove1 L (nxs);
      ASSERT(arena_act_pre N C);
      vm \<leftarrow> isa_vmtf_mark_to_rescore_also_reasons_cl M N C (-L) vm;
      ASSERT(vmtf_unset_pre L' vm);
      ASSERT(tl_trailt_tr_pre M);
      let S = update_trail_wl_heur (tl_trailt_tr M) S;
      let S = update_conflict_wl_heur (None_lookup_conflict b nxs) S;
      let S = update_vmtf_wl_heur (isa_vmtf_unset L' vm) S;
      let S = update_clvls_wl_heur (clvls - 1) S;
      let S = update_outl_wl_heur outl S;
      let S = update_arena_wl_heur N S;
      let S = update_lbd_wl_heur lbd S;
      RETURN (False, S)
   })\<close>
  unfolding update_confl_tl_wl_heur_def
  by (auto intro!: ext bind_cong simp: None_lookup_conflict_def the_lookup_conflict_def
    extract_values_of_lookup_conflict_def Let_def state_extractors split: isasat_int.splits)

sepref_def update_confl_tl_wl_fast_code
  is \<open>uncurry2 update_confl_tl_wl_heur\<close>
  :: \<open>[\<lambda>((i, L), S). isasat_fast S]\<^sub>a
   unat_lit_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>aisasat_bounded_assn\<^sup>d \<rightarrow> bool1_assn \<times>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]] isasat_fast_length_leD[intro]
  unfolding update_confl_tl_wl_heur_alt_def
    PR_CONST_def
  apply (rewrite at \<open>If (_ = \<hole>)\<close> snat_const_fold[where 'a=64])
  apply (annot_unat_const \<open>TYPE (32)\<close>)
  by sepref

sepref_register is_in_conflict_st atm_is_in_conflict_st_heur
sepref_def skip_and_resolve_loop_wl_D_fast
  is \<open>skip_and_resolve_loop_wl_D_heur\<close>
  :: \<open>[\<lambda>S. isasat_fast S]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
    skip_and_resolve_loop_wl_DI[intro]
    isasat_fast_after_skip_and_resolve_loop_wl_D_heur_inv[intro]
  unfolding skip_and_resolve_loop_wl_D_heur_def
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