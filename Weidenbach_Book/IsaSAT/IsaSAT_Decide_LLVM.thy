theory IsaSAT_Decide_LLVM
  imports IsaSAT_Decide_Defs IsaSAT_VMTF_State_LLVM IsaSAT_Setup_LLVM IsaSAT_Rephase_State_LLVM
begin
lemma decide_lit_wl_heur_alt_def:
  \<open>decide_lit_wl_heur = (\<lambda>L' S. do {
      let (M, S) = extract_trail_wl_heur S;
      let (stats, S) = extract_stats_wl_heur S;
      ASSERT(isa_length_trail_pre M);
      let j = isa_length_trail M;
      let S = update_literals_to_update_wl_heur j S;
      ASSERT(cons_trail_Decided_tr_pre (L', M));
      let M = cons_trail_Decided_tr L' M;
      let stats = incr_decision stats;
      let S = update_trail_wl_heur M S;
      let S = update_stats_wl_heur stats S;
        RETURN S})\<close>
   by (auto simp: decide_lit_wl_heur_def state_extractors split: isasat_int_splits intro!: ext)

sepref_def decide_lit_wl_fast_code
  is \<open>uncurry decide_lit_wl_heur\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding decide_lit_wl_heur_alt_def
  by sepref


sepref_register find_unassigned_lit_wl_D_heur decide_lit_wl_heur

sepref_register isa_vmtf_find_next_undef

sepref_def isa_vmtf_find_next_undef_code is
  \<open>uncurry isa_vmtf_find_next_undef\<close> :: \<open>vmtf_assn\<^sup>k *\<^sub>a trail_pol_fast_assn\<^sup>k \<rightarrow>\<^sub>a atom.option_assn\<close>
  unfolding isa_vmtf_find_next_undef_def vmtf_assn_def
  unfolding atom.fold_option
  apply (rewrite in \<open>WHILEIT _ \<hole>\<close> short_circuit_conv)
  supply [[goals_limit = 1]]
  apply annot_all_atm_idxs
  by sepref


lemma isa_bump_find_next_undef_alt_def: \<open>
  isa_bump_find_next_undef x M = (case x of Bump_Heuristics hstable focused foc h \<Rightarrow>
    if foc then isa_vmtf_find_next_undef focused M
      else isa_vmtf_find_next_undef hstable M)\<close>
  unfolding isa_bump_find_next_undef_def by (cases x) auto

sepref_def isa_bump_find_next_undef_code is
  \<open>uncurry isa_bump_find_next_undef\<close> :: \<open>heuristic_bump_assn\<^sup>k *\<^sub>a trail_pol_fast_assn\<^sup>k \<rightarrow>\<^sub>a atom.option_assn\<close>
  unfolding isa_bump_find_next_undef_alt_def
  unfolding atom.fold_option
  supply [[goals_limit = 1]]
  apply annot_all_atm_idxs
  by sepref

sepref_register update_next_search
sepref_def update_next_search_code is
  \<open>uncurry (RETURN oo update_next_search)\<close> :: \<open>atom.option_assn\<^sup>k *\<^sub>a vmtf_assn\<^sup>d \<rightarrow>\<^sub>a vmtf_assn\<close>
  unfolding update_next_search_def vmtf_assn_def
  by sepref

lemma isa_bump_update_next_search_alt_def: \<open>
  isa_bump_update_next_search L x = (case x of Bump_Heuristics hstable focused foc h \<Rightarrow>if foc
  then Bump_Heuristics hstable (update_next_search L focused) foc h
    else Bump_Heuristics (update_next_search L hstable) focused foc h)\<close>
  unfolding isa_bump_update_next_search_def by (cases x) auto

sepref_def isa_bump_update_next_search_code is
  \<open>uncurry (RETURN oo isa_bump_update_next_search)\<close> :: \<open>atom.option_assn\<^sup>k *\<^sub>a heuristic_bump_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_bump_assn\<close>
  unfolding isa_bump_update_next_search_alt_def
  by sepref

sepref_register isa_vmtf_find_next_undef_upd  mop_get_saved_phase_heur get_next_phase_st
  isa_bump_update_next_search
sepref_def isa_vmtf_find_next_undef_upd_code is
  \<open>uncurry isa_vmtf_find_next_undef_upd\<close>
    :: \<open>trail_pol_fast_assn\<^sup>d *\<^sub>a heuristic_bump_assn\<^sup>d \<rightarrow>\<^sub>a (trail_pol_fast_assn \<times>\<^sub>a heuristic_bump_assn) \<times>\<^sub>a atom.option_assn\<close>
  unfolding isa_vmtf_find_next_undef_upd_def
  by sepref

lemma find_unassigned_lit_wl_D_heur2_alt_def:
  \<open>find_unassigned_lit_wl_D_heur2 = (\<lambda>S. do {
    let (M, S) = extract_trail_wl_heur S;
    let (vm, S) = extract_vmtf_wl_heur S;
    let (heur, S) = extract_heur_wl_heur S;
      ((M, vm), L) \<leftarrow> isa_vmtf_find_next_undef_upd M vm;
      RETURN (update_heur_wl_heur (set_fully_propagated_heur heur) (update_trail_wl_heur M (update_vmtf_wl_heur vm S)), L)
    })\<close>
   by (auto simp: find_unassigned_lit_wl_D_heur2_def state_extractors split: isasat_int_splits intro!: ext)
sepref_register find_unassigned_lit_wl_D_heur2
sepref_def find_unassigned_lit_wl_D_heur_impl
  is \<open>find_unassigned_lit_wl_D_heur2\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn \<times>\<^sub>a atom.option_assn\<close>
  unfolding find_unassigned_lit_wl_D_heur2_alt_def
  by sepref

sepref_definition get_next_phase_heur_stats_impl'
  is \<open>uncurry2 (\<lambda>S C' D'. get_next_phase_heur C' D' S)\<close>
  :: \<open>[uncurry2 (\<lambda>S C D. True)]\<^sub>a heuristic_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a atom_assn\<^sup>k \<rightarrow> bool1_assn\<close>
  by sepref

definition get_next_phase_st'_impl :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>get_next_phase_st'_impl = (\<lambda>N C D. read_heur_wl_heur_code (get_next_phase_heur_stats_impl C D) N)\<close>

definition get_next_phase_st' :: \<open>_\<close> where
  \<open>get_next_phase_st' N C D = (get_next_phase_st C D N)\<close>

global_interpretation get_next_phase: read_heur_param_adder2 where
  R = bool1_rel and
  R' = atom_rel and
  f' = \<open> \<lambda>C D S. get_next_phase_heur C D S\<close> and
  f = \<open>\<lambda>C D S. get_next_phase_heur_stats_impl C D S\<close> and
  x_assn = \<open>bool1_assn\<close> and
  P = \<open>(\<lambda>_ _ _. True)\<close>
  rewrites
     \<open>(\<lambda>N C D. read_heur_wl_heur_code (get_next_phase_heur_stats_impl C D) N) = get_next_phase_st'_impl\<close> and
     \<open>(\<lambda>N C D. read_heur_wl_heur (get_next_phase_heur C D) N) = get_next_phase_st'\<close>
  apply unfold_locales
  apply (rule get_next_phase_heur_stats_impl'.refine[unfolded get_next_phase_heur_stats_impl'_def])
  subgoal by (auto simp: get_next_phase_st'_impl_def)
  subgoal by (auto simp: read_all_st_def get_next_phase_st_def get_next_phase_st'_def split: isasat_int_splits
    intro!: ext)
  done

lemmas [sepref_fr_rules] = get_next_phase.refine
lemmas [unfolded inline_direct_return_node_case, llvm_code] =
  get_next_phase_st'_impl_def[unfolded read_all_st_code_def]

sepref_def get_next_phase_st_impl
  is \<open>uncurry2 get_next_phase_st\<close>
  :: \<open>bool1_assn\<^sup>k *\<^sub>a atom_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding get_next_phase_st'_def[symmetric]
  by sepref

sepref_def decide_wl_or_skip_D_fast_code
  is \<open>decide_wl_or_skip_D_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a bool1_assn \<times>\<^sub>a isasat_bounded_assn\<close>
  supply[[goals_limit=1]]
  apply (rule hfref_refine_with_pre[OF decide_wl_or_skip_D_heur'_decide_wl_or_skip_D_heur, unfolded Down_id_eq])
  unfolding decide_wl_or_skip_D_heur'_def option.case_eq_if atom.fold_option
  by sepref

experiment begin

export_llvm
  decide_lit_wl_fast_code
  isa_vmtf_find_next_undef_code
  update_next_search_code
  isa_vmtf_find_next_undef_upd_code
  decide_wl_or_skip_D_fast_code

end


end
