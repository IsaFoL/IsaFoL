theory IsaSAT_Initialisation_State_LLVM
  imports IsaSAT_Initialisation Tuple15_LLVM IsaSAT_Setup_LLVM IsaSAT_Mark_LLVM
    IsaSAT_VMTF_LLVM Watched_Literals.Watched_Literals_Watch_List_Initialisation
    IsaSAT_Mark_LLVM
begin
hide_const (open) NEMonad.RETURN  NEMonad.ASSERT

type_synonym bump_heuristics_init_assn = \<open>
  ((64 word \<times> 32 word \<times> 32 word) ptr \<times> 64 word \<times> 32 word \<times> 32 word \<times> 32 word,
  (64 word \<times> 32 word \<times> 32 word) ptr \<times> 64 word \<times> 32 word \<times> 32 word \<times> 32 word,
  1 word, (64 word \<times> 64 word \<times> 32 word ptr) \<times> 1 word ptr) tuple4\<close>

type_synonym vmtf_init = \<open>(nat, nat) vmtf_node list \<times> nat \<times> nat option \<times> nat option \<times> nat option\<close>
definition (in -) vmtf_init_assn :: \<open>vmtf_init \<Rightarrow> _ \<Rightarrow> llvm_amemory \<Rightarrow> bool\<close> where
  \<open>vmtf_init_assn \<equiv> (array_assn vmtf_node_assn \<times>\<^sub>a uint64_nat_assn \<times>\<^sub>a
    atom.option_assn \<times>\<^sub>a atom.option_assn \<times>\<^sub>a atom.option_assn)\<close>

type_synonym bump_heuristics_init = \<open>(vmtf_init, vmtf_init, bool, nat list \<times> bool list) tuple4\<close>

abbreviation Bump_Heuristics_Init :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bump_heuristics_init\<close> where
  \<open>Bump_Heuristics_Init a b c d \<equiv> Tuple4 a b c d\<close>

definition heuristic_bump_init_assn :: \<open>bump_heuristics_init \<Rightarrow> bump_heuristics_init_assn \<Rightarrow> _\<close> where
  \<open>heuristic_bump_init_assn = tuple4_assn vmtf_init_assn vmtf_init_assn bool1_assn distinct_atoms_assn\<close>

definition bottom_atom where
  \<open>bottom_atom = 0\<close>

definition bottom_init_vmtf :: \<open>vmtf_init\<close> where
  \<open>bottom_init_vmtf = (replicate 0 (VMTF_Node 0 None None), 0, None, None, None)\<close>

definition extract_bump_stable where
  \<open>extract_bump_stable = tuple4_state_ops.remove_a bottom_init_vmtf\<close>
definition extract_bump_focused where
  \<open>extract_bump_focused = tuple4_state_ops.remove_b bottom_init_vmtf\<close>

lemma [sepref_fr_rules]: \<open>(uncurry0 (Mreturn 0), uncurry0 (RETURN bottom_atom)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a atom_assn\<close>
  unfolding bottom_atom_def
  apply sepref_to_hoare
  apply vcg
  apply (auto simp: atom_rel_def unat_rel_def unat.rel_def br_def entails_def ENTAILS_def)
  by (smt (verit, best) pure_true_conv rel_simps(51) sep.add_0)

sepref_def bottom_init_vmtf_code
  is \<open>uncurry0 (RETURN bottom_init_vmtf)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a vmtf_init_assn\<close>
  unfolding bottom_init_vmtf_def
  apply (rewrite in \<open>((\<hole>, _, _, _, _))\<close> array_fold_custom_replicate)
  unfolding
   atom.fold_option array_fold_custom_replicate vmtf_init_assn_def
    al_fold_custom_empty[where 'l=64]
  apply (rewrite at 0 in \<open>VMTF_Node \<hole>\<close> unat_const_fold[where 'a=64])
  apply (rewrite at \<open>(_, \<hole>, _, _)\<close> unat_const_fold[where 'a=64])
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

schematic_goal free_vmtf_remove_assn[sepref_frame_free_rules]: \<open>MK_FREE vmtf_init_assn ?a\<close>
  unfolding vmtf_init_assn_def
  by synthesize_free

sepref_def free_vmtf_remove
  is \<open>mop_free\<close>
  :: \<open>vmtf_init_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

definition extract_bump_is_focused where
  \<open>extract_bump_is_focused = tuple4_state_ops.remove_c False\<close>

definition bottom_atms_hash where
  \<open>bottom_atms_hash = ([], replicate 0 False)\<close>

definition extract_bump_atms_to_bump where
  \<open>extract_bump_atms_to_bump = tuple4_state_ops.remove_d bottom_atms_hash\<close>
  
sepref_def bottom_atms_hash_code
  is \<open>uncurry0 (RETURN bottom_atms_hash)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a distinct_atoms_assn\<close>
  unfolding bottom_atms_hash_def
  unfolding
   atom.fold_option array_fold_custom_replicate
    al_fold_custom_empty[where 'l=64]
  apply (rewrite at \<open>(\<hole>, _)\<close> annotate_assn[where A =\<open>al_assn atom_assn\<close>])
  apply (rewrite at \<open>(_, \<hole>)\<close> annotate_assn[where A =\<open>atoms_hash_assn\<close>])
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

lemma free_vmtf_init_assn_assn2: \<open>MK_FREE vmtf_init_assn free_vmtf_remove\<close>
  unfolding free_vmtf_remove_def
  by (rule back_subst[of \<open>MK_FREE vmtf_init_assn\<close>, OF free_vmtf_remove_assn])
    (auto intro!: ext)

global_interpretation Bump_Heur_Init: tuple4_state where
  a_assn = vmtf_init_assn and
  b_assn = vmtf_init_assn and
  c_assn = bool1_assn and
  d_assn = distinct_atoms_assn and
  a_default = bottom_init_vmtf and
  a = \<open>bottom_init_vmtf_code\<close> and
  a_free = free_vmtf_remove and
  b_default = bottom_init_vmtf and
  b = \<open>bottom_init_vmtf_code\<close> and
  b_free = free_vmtf_remove and
  c_default = False and
  c = \<open>bottom_focused\<close> and
  c_free = free_focused and
  d_default = \<open>bottom_atms_hash\<close> and
  d = \<open>bottom_atms_hash_code\<close> and
  d_free = \<open>free_atms_hash_code\<close>
  rewrites
  \<open>Bump_Heur_Init.tuple4_int_assn \<equiv> heuristic_bump_init_assn\<close>and
  \<open>Bump_Heur_Init.remove_a \<equiv> extract_bump_stable\<close> and
  \<open>Bump_Heur_Init.remove_b \<equiv> extract_bump_focused\<close> and
  \<open>Bump_Heur_Init.remove_c \<equiv> extract_bump_is_focused\<close> and
  \<open>Bump_Heur_Init.remove_d \<equiv> extract_bump_atms_to_bump\<close>
  apply unfold_locales
  apply (rule bottom_init_vmtf_code.refine bottom_focused.refine
    bottom_atms_hash_code.refine free_vmtf_init_assn_assn2 free_focused_assn2
    free_distinct_atoms_assn2)+
  subgoal unfolding heuristic_bump_init_assn_def tuple4_state_ops.tuple4_int_assn_def by auto
  subgoal unfolding extract_bump_stable_def by auto
  subgoal unfolding extract_bump_focused_def by auto
  subgoal unfolding extract_bump_is_focused_def by auto
  subgoal unfolding extract_bump_atms_to_bump_def by auto
  done

lemmas [unfolded Tuple4_LLVM.inline_direct_return_node_case, llvm_code] =
  Bump_Heur_Init.code_rules[unfolded Mreturn_comp_Tuple4]

lemmas [sepref_fr_rules] =
  Bump_Heur_Init.separation_rules


type_synonym (in -)twl_st_wll_trail_init =
  \<open>(trail_pol_fast_assn, arena_assn, option_lookup_clause_assn,
    64 word, watched_wl_uint32, bump_heuristics_init_assn, phase_saver_assn,
    32 word, cach_refinement_l_assn, lbd_assn, vdom_fast_assn, vdom_fast_assn, 1 word,
  (64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word), mark_assn) tuple15\<close>

definition isasat_init_assn
  :: \<open>twl_st_wl_heur_init \<Rightarrow> twl_st_wll_trail_init \<Rightarrow> assn\<close>
where
\<open>isasat_init_assn = tuple15_assn
  trail_pol_fast_assn arena_fast_assn
  conflict_option_rel_assn
  sint64_nat_assn
  watchlist_fast_assn
  heuristic_bump_init_assn phase_saver_assn
  uint32_nat_assn
  cach_refinement_l_assn
  lbd_assn
  vdom_fast_assn
  vdom_fast_assn
  bool1_assn lcount_assn
  marked_struct_assn\<close>


definition bottom_vdom :: \<open>_\<close> where
  \<open>bottom_vdom = []\<close>


sepref_def bottom_vdom_code
  is \<open>uncurry0 (RETURN bottom_vdom)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a vdom_fast_assn\<close>
  supply [[goals_limit=1]]
  unfolding bottom_vdom_def
  unfolding al_fold_custom_empty[where 'l=64]
  by sepref

sepref_def free_vdom
  is \<open>mop_free\<close>
  :: \<open>vdom_fast_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref


schematic_goal free_vdom[sepref_frame_free_rules]: \<open>MK_FREE vdom_fast_assn ?a\<close>
  by synthesize_free

lemma free_vdom2: \<open>MK_FREE vdom_fast_assn free_vdom\<close>
  unfolding free_arena_fast_def
  by (rule back_subst[of \<open>MK_FREE vdom_fast_assn\<close>, OF free_vdom])
    (auto intro!: ext simp: free_vdom_def)

sepref_def free_phase_saver
  is \<open>mop_free\<close>
  :: \<open>phase_saver_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

definition bottom_phase_saver :: \<open>phase_saver\<close> where
  \<open>bottom_phase_saver = op_larray_custom_replicate 0 False\<close>


sepref_def bottom_phase_saver_code
  is \<open>uncurry0 (RETURN bottom_phase_saver)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a phase_saver_assn\<close>
  supply [[goals_limit=1]]
  unfolding bottom_phase_saver_def
  unfolding larray_fold_custom_replicate
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

schematic_goal free_phase_saver[sepref_frame_free_rules]: \<open>MK_FREE phase_saver_assn ?a\<close>
  by synthesize_free

lemma free_phase_saver2: \<open>MK_FREE phase_saver_assn free_phase_saver\<close>
  unfolding free_arena_fast_def
  by (rule back_subst[of \<open>MK_FREE phase_saver_assn\<close>, OF free_phase_saver])
    (auto intro!: ext simp: free_phase_saver_def)

definition bottom_init_bump :: \<open>bump_heuristics_init\<close> where
  \<open>bottom_init_bump = Bump_Heuristics_Init bottom_init_vmtf bottom_init_vmtf False bottom_atms_hash\<close>

schematic_goal free_vmtf_init_assn[sepref_frame_free_rules]: \<open>MK_FREE heuristic_bump_init_assn ?a\<close>
  unfolding heuristic_bump_init_assn_def
  by synthesize_free

sepref_def free_bottom_init_bump_code
  is \<open>mop_free\<close>
  :: \<open>heuristic_bump_init_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref


lemma free_vmtf_remove2: \<open>MK_FREE heuristic_bump_init_assn free_bottom_init_bump_code\<close>
  unfolding free_bottom_init_bump_code_def
  apply (rule back_subst[of \<open>MK_FREE heuristic_bump_init_assn\<close>, OF free_vmtf_init_assn])
  apply (auto intro!: ext simp: M_monad_laws)
  by (metis M_monad_laws(1))


definition op_empty_array where
  \<open>op_empty_array \<equiv> []\<close>

lemma [sepref_fr_rules]: \<open>(uncurry0 (Mreturn null), uncurry0 (RETURN op_empty_array)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a array_assn R\<close>
  unfolding array_assn_def op_empty_array_def
  apply sepref_to_hoare
  apply vcg
  apply (auto simp: array_assn_def ENTAILS_def hr_comp_def[abs_def] Exists_eq_simp
    pure_true_conv narray_assn_null_init)
  done

sepref_def bottom_init_vmtf2_code
  is \<open>uncurry0 (RETURN bottom_init_bump)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a heuristic_bump_init_assn\<close>
  unfolding bottom_init_bump_def atom.fold_None
  unfolding al_fold_custom_empty[where 'l=64]
  by sepref

definition bottom_bool where
  \<open>bottom_bool = False\<close>

sepref_def bottom_bool_code
  is \<open>uncurry0 (RETURN bottom_bool)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding bottom_bool_def
  by sepref

sepref_def free_bool
  is \<open>mop_free\<close>
  :: \<open>bool1_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

schematic_goal free_bool[sepref_frame_free_rules]: \<open>MK_FREE bool1_assn ?a\<close>
  by synthesize_free

lemma free_bool2: \<open>MK_FREE bool1_assn free_bool\<close>
  unfolding free_focused_def
  by (rule back_subst[of \<open>MK_FREE bool1_assn\<close>, OF free_bool])
    (auto intro!: ext simp: free_bool_def free_focused_def)

definition bottom_marked_struct :: \<open>_\<close> where
  \<open>bottom_marked_struct = (0, [])\<close>

sepref_def bottom_marked_struct_code
  is \<open>uncurry0 (RETURN bottom_marked_struct)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a marked_struct_assn\<close>
  unfolding bottom_marked_struct_def marked_struct_assn_def op_empty_array_def[symmetric]
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref

sepref_def free_marked_struct_code
  is \<open>mop_free\<close>
  :: \<open>marked_struct_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding bottom_marked_struct_def marked_struct_assn_def
  by sepref

schematic_goal free_marked_struct[sepref_frame_free_rules]: \<open>MK_FREE marked_struct_assn ?a\<close>
  unfolding marked_struct_assn_def
  by synthesize_free

lemma free_marked_struct2: \<open>MK_FREE marked_struct_assn free_marked_struct_code\<close>
  unfolding free_arena_fast_def
  by (rule back_subst[of \<open>MK_FREE marked_struct_assn\<close>, OF free_marked_struct])
    (auto intro!: ext simp: free_marked_struct_code_def)

global_interpretation IsaSAT_Init: tuple15_state_ops where
  a_assn = trail_pol_fast_assn and
  b_assn = arena_fast_assn and
  c_assn = conflict_option_rel_assn and
  d_assn = sint64_nat_assn and
  e_assn = watchlist_fast_assn and
  f_assn = heuristic_bump_init_assn and
  g_assn = phase_saver_assn and
  h_assn = uint32_nat_assn and
  i_assn = cach_refinement_l_assn and
  j_assn = lbd_assn and
  k_assn = vdom_fast_assn and
  l_assn = vdom_fast_assn and
  m_assn = bool1_assn and
  n_assn = lcount_assn and
  o_assn = marked_struct_assn and
  a_default = bottom_trail and
  a = \<open>bottom_trail_code\<close> and
  b_default = bottom_arena and
  b = \<open>bottom_arena_code\<close> and
  c_default = bottom_conflict and
  c = \<open>bottom_conflict_code\<close> and
  d_default = \<open>bottom_decision_level\<close> and
  d = \<open>(bottom_decision_level_code)\<close> and
  e_default = bottom_watchlist and
  e = \<open>bottom_watchlist_code\<close> and
  f_default = bottom_init_bump and
  f = \<open>bottom_init_vmtf2_code\<close> and
  g_default = bottom_phase_saver and
  g = \<open>bottom_phase_saver_code\<close> and
  h_default = bottom_clvls and
  h = \<open>bottom_clvls_code\<close>and
  i_default = bottom_ccach and
  i = \<open>bottom_ccach_code\<close> and
  j_default = empty_lbd and
  j = \<open>empty_lbd_code\<close> and
  k_default = bottom_vdom and
  k = \<open>bottom_vdom_code\<close> and
  l_default = bottom_vdom and
  l = \<open>bottom_vdom_code\<close> and
  m_default = bottom_bool and
  m = \<open>bottom_bool_code\<close> and
  n_default = bottom_lcount and
  n = \<open>bottom_lcount_code\<close> and
  ko_default = bottom_marked_struct and
  ko = \<open>bottom_marked_struct_code\<close>
(*  rewrites
   \<open>IsaSAT_Init.tuple15_int_assn \<equiv> isasat_init_assn\<close>
  subgoal unfolding isasat_init_assn_def tuple15_state_ops.tuple15_int_assn_def .
*)  .

definition extract_trail_wl_heur_init where
  \<open>extract_trail_wl_heur_init = IsaSAT_Init.remove_a\<close>

definition extract_arena_wl_heur_init where
  \<open>extract_arena_wl_heur_init = IsaSAT_Init.remove_b\<close>

definition extract_conflict_wl_heur_init where
  \<open>extract_conflict_wl_heur_init = IsaSAT_Init.remove_c\<close>

definition extract_literals_to_update_wl_heur_init where
  \<open>extract_literals_to_update_wl_heur_init = IsaSAT_Init.remove_d\<close>

definition extract_watchlist_wl_heur_init where
  \<open>extract_watchlist_wl_heur_init = IsaSAT_Init.remove_e\<close>

definition extract_vmtf_wl_heur_init where
  \<open>extract_vmtf_wl_heur_init = IsaSAT_Init.remove_f\<close>

definition extract_phase_saver_wl_heur_init where
  \<open>extract_phase_saver_wl_heur_init = IsaSAT_Init.remove_g\<close>

definition extract_clvls_wl_heur_init where
  \<open>extract_clvls_wl_heur_init = IsaSAT_Init.remove_h\<close>

definition extract_ccach_wl_heur_init where
  \<open>extract_ccach_wl_heur_init = IsaSAT_Init.remove_i\<close>

definition extract_lbd_wl_heur_init where
  \<open>extract_lbd_wl_heur_init = IsaSAT_Init.remove_j\<close>

definition extract_vdom_wl_heur_init where
  \<open>extract_vdom_wl_heur_init = IsaSAT_Init.remove_k\<close>

definition extract_ivdom_wl_heur_init where
  \<open>extract_ivdom_wl_heur_init = IsaSAT_Init.remove_l\<close>

definition extract_failed_wl_heur_init where
  \<open>extract_failed_wl_heur_init = IsaSAT_Init.remove_m\<close>

definition extract_lcount_wl_heur_init where
  \<open>extract_lcount_wl_heur_init = IsaSAT_Init.remove_n\<close>

definition extract_marked_wl_heur_init where
  \<open>extract_marked_wl_heur_init = IsaSAT_Init.remove_o\<close>

global_interpretation IsaSAT_Init: tuple15_state where
  a_assn = trail_pol_fast_assn and
  b_assn = arena_fast_assn and
  c_assn = conflict_option_rel_assn and
  d_assn = sint64_nat_assn and
  e_assn = watchlist_fast_assn and
  f_assn = heuristic_bump_init_assn and
  g_assn = phase_saver_assn and
  h_assn = uint32_nat_assn and
  i_assn = cach_refinement_l_assn and
  j_assn = lbd_assn and
  k_assn = vdom_fast_assn and
  l_assn = vdom_fast_assn and
  m_assn = bool1_assn and
  n_assn = lcount_assn and
  o_assn = marked_struct_assn and
  a_default = bottom_trail and
  a = \<open>bottom_trail_code\<close> and
  a_free = free_trail_pol_fast and
  b_default = bottom_arena and
  b = \<open>bottom_arena_code\<close> and
  b_free = free_arena_fast and
  c_default = bottom_conflict and
  c = \<open>bottom_conflict_code\<close> and
  c_free = free_conflict_option_rel and
  d_default = \<open>bottom_decision_level\<close> and
  d = \<open>bottom_decision_level_code\<close> and
  d_free = \<open>free_sint64_nat\<close> and
  e_default = bottom_watchlist and
  e = \<open>bottom_watchlist_code\<close> and
  e_free = free_watchlist_fast and
  f_default = bottom_init_bump and
  f = \<open>bottom_init_vmtf2_code\<close> and
  f_free = free_bottom_init_bump_code and
  g_default = bottom_phase_saver and
  g = \<open>bottom_phase_saver_code\<close> and
  g_free = free_phase_saver and
  h_default = bottom_clvls and
  h = \<open>bottom_clvls_code\<close>and
  h_free = free_uint32_nat and
  i_default = bottom_ccach and
  i = \<open>bottom_ccach_code\<close> and
  i_free = free_cach_refinement_l and
  j_default = empty_lbd and
  j = \<open>empty_lbd_code\<close> and
  j_free = free_lbd and
  k_default = bottom_vdom and
  k = \<open>bottom_vdom_code\<close> and
  k_free = free_vdom and
  l_default = bottom_vdom and
  l = \<open>bottom_vdom_code\<close> and
  l_free = free_vdom and
  m_default = bottom_bool and
  m = \<open>bottom_bool_code\<close> and
  m_free = free_bool and
  n_default = bottom_lcount and
  n = \<open>bottom_lcount_code\<close> and
  n_free = free_lcount and
  ko_default = bottom_marked_struct and
  ko = \<open>bottom_marked_struct_code\<close> and
  o_free = free_marked_struct_code
  rewrites
    \<open>IsaSAT_Init.tuple15_int_assn = isasat_init_assn\<close>  and
    \<open>IsaSAT_Init.remove_a = extract_trail_wl_heur_init\<close> and
    \<open>IsaSAT_Init.remove_b = extract_arena_wl_heur_init\<close> and
    \<open>IsaSAT_Init.remove_c = extract_conflict_wl_heur_init\<close> and
    \<open>IsaSAT_Init.remove_d = extract_literals_to_update_wl_heur_init\<close> and
    \<open>IsaSAT_Init.remove_e = extract_watchlist_wl_heur_init\<close> and
    \<open>IsaSAT_Init.remove_f = extract_vmtf_wl_heur_init\<close> and
    \<open>IsaSAT_Init.remove_g = extract_phase_saver_wl_heur_init\<close> and
    \<open>IsaSAT_Init.remove_h = extract_clvls_wl_heur_init\<close> and
    \<open>IsaSAT_Init.remove_i = extract_ccach_wl_heur_init\<close> and
    \<open>IsaSAT_Init.remove_j = extract_lbd_wl_heur_init\<close> and
    \<open>IsaSAT_Init.remove_k = extract_vdom_wl_heur_init\<close> and
    \<open>IsaSAT_Init.remove_l = extract_ivdom_wl_heur_init\<close> and
    \<open>IsaSAT_Init.remove_m = extract_failed_wl_heur_init\<close> and
    \<open>IsaSAT_Init.remove_n = extract_lcount_wl_heur_init\<close> and
    \<open>IsaSAT_Init.remove_o = extract_marked_wl_heur_init\<close>
  apply unfold_locales
  subgoal by (rule bottom_trail_code.refine)
  subgoal by (rule bottom_arena_code.refine)
  subgoal by (rule bottom_conflict_code.refine)
  subgoal by (rule bottom_decision_level_code.refine)
  subgoal by (rule bottom_watchlist_code.refine)
  subgoal by (rule bottom_init_vmtf2_code.refine)
  subgoal by (rule bottom_phase_saver_code.refine)
  subgoal by (rule bottom_clvls_code.refine)
  subgoal by (rule bottom_ccach_code.refine)
  subgoal by (rule empty_lbd_hnr)
  subgoal by (rule bottom_vdom_code.refine)
  subgoal by (rule bottom_bool_code.refine)
  subgoal by (rule bottom_lcount_code.refine)
  subgoal by (rule bottom_marked_struct_code.refine)
  subgoal by (rule free_trail_pol_fast_assn2)
  subgoal by (rule free_arena_fast_assn2)
  subgoal by (rule free_conflict_option_rel_assn2)
  subgoal by (synthesize_free)
  subgoal by (synthesize_free)
  subgoal by (rule free_vmtf_remove2)
  subgoal by (rule free_phase_saver2)
  subgoal by (synthesize_free)
  subgoal by (synthesize_free)
  subgoal by (synthesize_free)
  subgoal by (rule free_vdom2)
  subgoal by (rule free_bool2)
  subgoal by (synthesize_free)
  subgoal by (rule free_marked_struct2)
  subgoal unfolding isasat_init_assn_def tuple15_state_ops.tuple15_int_assn_def ..
  subgoal unfolding extract_trail_wl_heur_init_def ..
  subgoal unfolding extract_arena_wl_heur_init_def ..
  subgoal unfolding extract_conflict_wl_heur_init_def ..
  subgoal unfolding extract_literals_to_update_wl_heur_init_def ..
  subgoal unfolding extract_watchlist_wl_heur_init_def ..
  subgoal unfolding extract_vmtf_wl_heur_init_def ..
  subgoal unfolding extract_phase_saver_wl_heur_init_def ..
  subgoal unfolding extract_clvls_wl_heur_init_def ..
  subgoal unfolding extract_ccach_wl_heur_init_def ..
  subgoal unfolding extract_lbd_wl_heur_init_def ..
  subgoal unfolding extract_vdom_wl_heur_init_def ..
  subgoal unfolding extract_ivdom_wl_heur_init_def ..
  subgoal unfolding extract_failed_wl_heur_init_def ..
  subgoal unfolding extract_lcount_wl_heur_init_def ..
  subgoal unfolding extract_marked_wl_heur_init_def ..
  done

lemmas [unfolded Tuple15_LLVM.inline_direct_return_node_case, llvm_code] =
  IsaSAT_Init.code_rules[unfolded Mreturn_comp_Tuple15]

lemmas [sepref_fr_rules] =
  IsaSAT_Init.separation_rules

lemmas isasat_init_getters_and_setters_def =
  IsaSAT_Init.setter_and_getters_def
  extract_trail_wl_heur_init_def
  extract_arena_wl_heur_init_def
  extract_conflict_wl_heur_init_def
  extract_literals_to_update_wl_heur_init_def
  extract_marked_wl_heur_init_def
  extract_lcount_wl_heur_init_def
  extract_failed_wl_heur_init_def
  extract_ivdom_wl_heur_init_def
  extract_vdom_wl_heur_init_def
  extract_lbd_wl_heur_init_def
  extract_ccach_wl_heur_init_def
  extract_clvls_wl_heur_init_def
  extract_phase_saver_wl_heur_init_def
  extract_vmtf_wl_heur_init_def
  extract_watchlist_wl_heur_init_def
  IsaSAT_Init.remove_a_def
  IsaSAT_Init.remove_b_def
  IsaSAT_Init.remove_c_def
  IsaSAT_Init.remove_d_def
  IsaSAT_Init.remove_e_def
  IsaSAT_Init.remove_f_def
  IsaSAT_Init.remove_g_def
  IsaSAT_Init.remove_h_def
  IsaSAT_Init.remove_i_def
  IsaSAT_Init.remove_j_def
  IsaSAT_Init.remove_k_def
  IsaSAT_Init.remove_l_def
  IsaSAT_Init.remove_m_def
  IsaSAT_Init.remove_n_def
  IsaSAT_Init.remove_o_def



lemma (in -) case_isasat_int_split_getter: \<open>P 
  (Tuple15_a S)
  (Tuple15_b S)
  (Tuple15_c S)
  (Tuple15_d S)
  (Tuple15_e S)
  (Tuple15_f S)
  (Tuple15_g S)
  (Tuple15_h S)
  (Tuple15_i S)
  (Tuple15_j S)
  (Tuple15_k S)
  (Tuple15_l S)
  (Tuple15_m S)
  (Tuple15_n S)
  (Tuple15_o S) = case_tuple15 P S\<close>
  by (auto split: tuple15.splits)


context tuple15_state
begin
context
  fixes
    f' :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'g \<Rightarrow> 'h \<Rightarrow> 'i \<Rightarrow> 'j \<Rightarrow> 'k \<Rightarrow> 'l \<Rightarrow> 'm \<Rightarrow> 'n \<Rightarrow> 'o \<Rightarrow> 'x nres\<close> and
    P  :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'g \<Rightarrow> 'h \<Rightarrow> 'i \<Rightarrow> 'j \<Rightarrow> 'k \<Rightarrow> 'l \<Rightarrow> 'm \<Rightarrow> 'n \<Rightarrow> 'o \<Rightarrow> bool\<close>
begin
definition mop where
  \<open>mop S C = do {
  ASSERT (P C
  (Tuple15_a S)
  (Tuple15_b S)
  (Tuple15_c S)
  (Tuple15_d S)
  (Tuple15_e S)
  (Tuple15_f S)
  (Tuple15_g S)
  (Tuple15_h S)
  (Tuple15_i S)
  (Tuple15_j S)
  (Tuple15_k S)
  (Tuple15_l S)
  (Tuple15_m S)
  (Tuple15_n S)
  (Tuple15_o S));
   read_all_st (f' C) S
  }\<close>

context
  fixes R and kf and x_assn :: \<open>'x \<Rightarrow> 'q \<Rightarrow> assn\<close>
  assumes not_deleted_code_refine:
    \<open>(uncurry15 (\<lambda>a b c d e f g h i j k l m n ko C. kf C a b c d e f g h i j k l m n ko),
    uncurry15 (\<lambda>a b c d e f g h i j k l m n ko C. f' C a b c d e f g h i j k l m n ko))
    \<in> [uncurry15 (\<lambda>a b c d e f g h i j k l m n ko C. P C a b c d e f g h i j k l m n ko)]\<^sub>a
    a_assn\<^sup>k *\<^sub>a b_assn\<^sup>k *\<^sub>a c_assn\<^sup>k *\<^sub>a d_assn\<^sup>k *\<^sub>a
  e_assn\<^sup>k *\<^sub>a f_assn\<^sup>k *\<^sub>a g_assn\<^sup>k  *\<^sub>a h_assn\<^sup>k *\<^sub>a i_assn\<^sup>k *\<^sub>a
  j_assn\<^sup>k *\<^sub>a k_assn\<^sup>k *\<^sub>a l_assn\<^sup>k *\<^sub>a m_assn\<^sup>k *\<^sub>a
  n_assn\<^sup>k *\<^sub>a o_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
begin

context
begin
lemma not_deleted_code_refine_tmp:
  \<open>\<And>C C'. (C, C') \<in> R \<Longrightarrow> (uncurry14 (kf C), uncurry14 (f' C')) \<in> [uncurry14 (P C')]\<^sub>a
    a_assn\<^sup>k *\<^sub>a b_assn\<^sup>k *\<^sub>a c_assn\<^sup>k *\<^sub>a d_assn\<^sup>k *\<^sub>a
  e_assn\<^sup>k *\<^sub>a f_assn\<^sup>k *\<^sub>a g_assn\<^sup>k  *\<^sub>a h_assn\<^sup>k *\<^sub>a i_assn\<^sup>k *\<^sub>a
  j_assn\<^sup>k *\<^sub>a k_assn\<^sup>k *\<^sub>a l_assn\<^sup>k *\<^sub>a m_assn\<^sup>k *\<^sub>a
  n_assn\<^sup>k *\<^sub>a o_assn\<^sup>k \<rightarrow> x_assn\<close>
  apply (rule remove_pure_parameter2'[where R=R])
  apply (rule hfref_cong[OF not_deleted_code_refine])
  apply (auto simp add: uncurry_def)
  done
end
lemma read_all_refine:
  \<open>(uncurry (\<lambda>N C. read_all_st_code (kf C) N),
    uncurry (\<lambda>N C'. read_all_st (f' C') N))
  \<in> [uncurry (\<lambda>S C. P C
  (Tuple15_a S)
  (Tuple15_b S)
  (Tuple15_c S)
  (Tuple15_d S)
  (Tuple15_e S)
  (Tuple15_f S)
  (Tuple15_g S)
  (Tuple15_h S)
  (Tuple15_i S)
  (Tuple15_j S)
  (Tuple15_k S)
  (Tuple15_l S)
  (Tuple15_m S)
  (Tuple15_n S)
  (Tuple15_o S))]\<^sub>a tuple15_int_assn\<^sup>k  *\<^sub>a (pure R)\<^sup>k\<rightarrow> x_assn\<close>
  apply (rule add_pure_parameter2)
  unfolding tuple15.case_distrib case_isasat_int_split_getter
  apply (rule read_all_st_code_refine)
  apply (rule not_deleted_code_refine_tmp)
  apply assumption
  done

lemma read_all_mop_refine:
  \<open>(uncurry (\<lambda>N C. read_all_st_code (kf C) N),
    uncurry mop)
  \<in> tuple15_int_assn\<^sup>k  *\<^sub>a (pure R)\<^sup>k\<rightarrow>\<^sub>a x_assn\<close>
  unfolding mop_def
  apply (rule refine_ASSERT_move_to_pre)
  apply (rule read_all_refine)
  done
end
end

abbreviation read_trail_wl_heur_code :: \<open>_\<close> where
  \<open>read_trail_wl_heur_code kf \<equiv> IsaSAT_Init.read_all_st_code  (\<lambda>M _ _ _ _ _ _ _ _ _ _ _ _ _ _. kf M)\<close>
abbreviation read_trail_wl_heur :: \<open>_\<close> where
  \<open>read_trail_wl_heur kf \<equiv> IsaSAT_Init.read_all_st (\<lambda>M _ _ _ _ _ _ _ _ _ _ _ _ _ _. kf M)\<close>


context
  fixes R and kf and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(uncurry (\<lambda>S C. kf C S), uncurry (\<lambda>S C. f' C S)) \<in> [uncurry (\<lambda>S C. P C S)]\<^sub>a a_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
begin
private lemma not_deleted_code_refine':
  \<open>(uncurry15 (\<lambda>M _ _ _ _ _ _ _ _ _ _ _ _ _ _ C. kf C M), uncurry15 (\<lambda>M _ _ _ _ _ _ _ _ _ _ _ _ _ _ C'. f' C' M)) \<in> [uncurry15 (\<lambda>M _ _ _ _ _ _ _ _ _ _ _ _ _ _ C. P C M)]\<^sub>a
   a_assn\<^sup>k *\<^sub>a b_assn\<^sup>k *\<^sub>a c_assn\<^sup>k *\<^sub>a d_assn\<^sup>k *\<^sub>a
  e_assn\<^sup>k *\<^sub>a f_assn\<^sup>k *\<^sub>a g_assn\<^sup>k  *\<^sub>a h_assn\<^sup>k *\<^sub>a i_assn\<^sup>k *\<^sub>a
  j_assn\<^sup>k *\<^sub>a k_assn\<^sup>k *\<^sub>a l_assn\<^sup>k *\<^sub>a m_assn\<^sup>k *\<^sub>a
  n_assn\<^sup>k *\<^sub>a o_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
  apply (insert not_deleted_code_refine)
  apply (drule remove_component_middle[where X = b_assn])
  apply (drule remove_component_middle[where X = c_assn])
  apply (drule remove_component_middle[where X = d_assn])
  apply (drule remove_component_middle[where X = e_assn])
  apply (drule remove_component_middle[where X = f_assn])
  apply (drule remove_component_middle[where X = g_assn])
  apply (drule remove_component_middle[where X = h_assn])
  apply (drule remove_component_middle[where X = i_assn])
  apply (drule remove_component_middle[where X = j_assn])
  apply (drule remove_component_middle[where X = k_assn])
  apply (drule remove_component_middle[where X = l_assn])
  apply (drule remove_component_middle[where X = m_assn])
  apply (drule remove_component_middle[where X = n_assn])
  apply (drule remove_component_middle[where X = o_assn])
  apply (rule hfref_cong, assumption)
  apply (auto simp add: uncurry_def)
  done

lemmas read_trail_refine = read_all_refine[OF not_deleted_code_refine']
lemmas mop_read_trail_refine = read_all_mop_refine[OF not_deleted_code_refine']
end


abbreviation read_conflict_wl_heur_code :: \<open>_\<close> where
  \<open>read_conflict_wl_heur_code kf \<equiv> IsaSAT_Init.read_all_st_code  (\<lambda>M _ _ _ _ _ _ _ _ _ _ _ _ _ _. kf M)\<close>
abbreviation read_conflict_wl_heur :: \<open>_\<close> where
  \<open>read_conflict_wl_heur kf \<equiv> IsaSAT_Init.read_all_st (\<lambda>M _ _ _ _ _ _ _ _ _ _ _ _ _ _. kf M)\<close>


context
  fixes R and kf and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(uncurry (\<lambda>S C. kf C S), uncurry (\<lambda>S C. f' C S)) \<in> [uncurry (\<lambda>S C. P C S)]\<^sub>a c_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
begin
private lemma not_deleted_code_refine_conflict:
  \<open>(uncurry15 (\<lambda>_ _ M _ _ _ _ _ _ _ _ _ _ _ _ C. kf C M), uncurry15 (\<lambda>_ _ M _ _ _ _ _ _ _ _ _ _ _ _ C'. f' C' M)) \<in> [uncurry15 (\<lambda>_ _ M _ _ _ _ _ _ _ _ _ _ _ _ C. P C M)]\<^sub>a
   a_assn\<^sup>k *\<^sub>a b_assn\<^sup>k *\<^sub>a c_assn\<^sup>k *\<^sub>a d_assn\<^sup>k *\<^sub>a
  e_assn\<^sup>k *\<^sub>a f_assn\<^sup>k *\<^sub>a g_assn\<^sup>k  *\<^sub>a h_assn\<^sup>k *\<^sub>a i_assn\<^sup>k *\<^sub>a
  j_assn\<^sup>k *\<^sub>a k_assn\<^sup>k *\<^sub>a l_assn\<^sup>k *\<^sub>a m_assn\<^sup>k *\<^sub>a
  n_assn\<^sup>k *\<^sub>a o_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
  apply (rule add_pure_parameter2)
  apply (drule remove_pure_parameter2'[where f =kf and f'=f', OF not_deleted_code_refine])
  apply (drule remove_component_left[where X = a_assn])
  apply (drule remove_component_middle[where X = b_assn])
  apply (drule remove_component_right[where X = d_assn])
  apply (drule remove_component_right[where X = e_assn])
  apply (drule remove_component_right[where X = f_assn])
  apply (drule remove_component_right[where X = g_assn])
  apply (drule remove_component_right[where X = h_assn])
  apply (drule remove_component_right[where X = i_assn])
  apply (drule remove_component_right[where X = j_assn])
  apply (drule remove_component_right[where X = k_assn])
  apply (drule remove_component_right[where X = l_assn])
  apply (drule remove_component_right[where X = m_assn])
  apply (drule remove_component_right[where X = n_assn])
  apply (drule remove_component_right[where X = o_assn])
  apply (rule hfref_cong, assumption)
  apply (auto simp add: uncurry_def)
  done

lemmas read_conflict_refine = read_all_refine[OF not_deleted_code_refine_conflict]
lemmas mop_read_conflict_refine = read_all_mop_refine[OF not_deleted_code_refine_conflict]
end

context
  fixes R and kf and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>((\<lambda>S. kf S), (\<lambda>S. f' S)) \<in> [(\<lambda>S. P S)]\<^sub>a c_assn\<^sup>k \<rightarrow> x_assn\<close>
begin

lemmas read_conflict_refine0 = read_conflict_refine[OF not_deleted_code_refine[THEN remove_component_right],
  THEN remove_unused_unit_parameter]
lemmas mop_read_conflict_refine0 = mop_read_conflict_refine[OF not_deleted_code_refine[THEN remove_component_right]]

end



abbreviation read_b_wl_heur_code :: \<open>_\<close> where
  \<open>read_b_wl_heur_code kf \<equiv> IsaSAT_Init.read_all_st_code  (\<lambda>_ M _ _ _ _ _ _ _ _ _ _ _ _ _. kf M)\<close>
abbreviation read_b_wl_heur :: \<open>_\<close> where
  \<open>read_b_wl_heur kf \<equiv> IsaSAT_Init.read_all_st (\<lambda>_ M _ _ _ _ _ _ _ _ _ _ _ _ _. kf M)\<close>



context
  fixes R and kf and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(uncurry (\<lambda>S C. kf C S), uncurry (\<lambda>S C. f' C S)) \<in> [uncurry (\<lambda>S C. P C S)]\<^sub>a b_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
begin
private lemma not_deleted_code_refine_b:
  \<open>(uncurry15 (\<lambda>_ M _ _ _ _ _ _ _ _ _ _ _ _ _ C. kf C M), uncurry15 (\<lambda>_ M _ _ _ _ _ _ _ _ _ _ _ _ _ C'. f' C' M)) \<in> [uncurry15 (\<lambda>_ M _ _ _ _ _ _ _ _ _ _ _ _ _ C. P C M)]\<^sub>a
   a_assn\<^sup>k *\<^sub>a b_assn\<^sup>k *\<^sub>a c_assn\<^sup>k *\<^sub>a d_assn\<^sup>k *\<^sub>a
  e_assn\<^sup>k *\<^sub>a f_assn\<^sup>k *\<^sub>a g_assn\<^sup>k  *\<^sub>a h_assn\<^sup>k *\<^sub>a i_assn\<^sup>k *\<^sub>a
  j_assn\<^sup>k *\<^sub>a k_assn\<^sup>k *\<^sub>a l_assn\<^sup>k *\<^sub>a m_assn\<^sup>k *\<^sub>a
  n_assn\<^sup>k *\<^sub>a o_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
  apply (rule add_pure_parameter2)
  apply (drule remove_pure_parameter2'[where f =kf and f'=f', OF not_deleted_code_refine])
  apply (drule remove_component_left[where X = a_assn])
  apply (drule remove_component_right[where X = c_assn])
  apply (drule remove_component_right[where X = d_assn])
  apply (drule remove_component_right[where X = e_assn])
  apply (drule remove_component_right[where X = f_assn])
  apply (drule remove_component_right[where X = g_assn])
  apply (drule remove_component_right[where X = h_assn])
  apply (drule remove_component_right[where X = i_assn])
  apply (drule remove_component_right[where X = j_assn])
  apply (drule remove_component_right[where X = k_assn])
  apply (drule remove_component_right[where X = l_assn])
  apply (drule remove_component_right[where X = m_assn])
  apply (drule remove_component_right[where X = n_assn])
  apply (drule remove_component_right[where X = o_assn])
  apply (rule hfref_cong, assumption)
  apply (auto simp add: uncurry_def)
  done

lemmas read_b_refine = read_all_refine[OF not_deleted_code_refine_b]
lemmas mop_read_b_refine = read_all_mop_refine[OF not_deleted_code_refine_b]
end


context
  fixes R and kf and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>((\<lambda>S. kf S), (\<lambda>S. f' S)) \<in> [(\<lambda>S. P S)]\<^sub>a b_assn\<^sup>k \<rightarrow> x_assn\<close>
begin

lemmas read_b_refine0 = read_b_refine[OF not_deleted_code_refine[THEN remove_component_right],
  THEN remove_unused_unit_parameter]
lemmas mop_read_b_refine0 = mop_read_b_refine[OF not_deleted_code_refine[THEN remove_component_right]]

end

  

context
  fixes R and kf and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(uncurry (\<lambda>S C. kf C S), uncurry (\<lambda>S C. f' C S)) \<in> [uncurry (\<lambda>S C. P C S)]\<^sub>a n_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
begin
private lemma not_deleted_code_refine_n:
  \<open>(uncurry15 (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ M _ C. kf C M), uncurry15 (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ M _ C'. f' C' M)) \<in> [uncurry15 (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ M _ C. P C M)]\<^sub>a
   a_assn\<^sup>k *\<^sub>a b_assn\<^sup>k *\<^sub>a c_assn\<^sup>k *\<^sub>a d_assn\<^sup>k *\<^sub>a
  e_assn\<^sup>k *\<^sub>a f_assn\<^sup>k *\<^sub>a g_assn\<^sup>k  *\<^sub>a h_assn\<^sup>k *\<^sub>a i_assn\<^sup>k *\<^sub>a
  j_assn\<^sup>k *\<^sub>a k_assn\<^sup>k *\<^sub>a l_assn\<^sup>k *\<^sub>a m_assn\<^sup>k *\<^sub>a
  n_assn\<^sup>k *\<^sub>a o_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
  apply (rule add_pure_parameter2)
  apply (drule remove_pure_parameter2'[where f =kf and f'=f', OF not_deleted_code_refine])
  apply (drule remove_component_left[where X = a_assn])
  apply (drule remove_component_middle[where X = b_assn])
  apply (drule remove_component_middle[where X = c_assn])
  apply (drule remove_component_middle[where X = d_assn])
  apply (drule remove_component_middle[where X = e_assn])
  apply (drule remove_component_middle[where X = f_assn])
  apply (drule remove_component_middle[where X = g_assn])
  apply (drule remove_component_middle[where X = h_assn])
  apply (drule remove_component_middle[where X = i_assn])
  apply (drule remove_component_middle[where X = j_assn])
  apply (drule remove_component_middle[where X = k_assn])
  apply (drule remove_component_middle[where X = l_assn])
  apply (drule remove_component_middle[where X = m_assn])
  apply (drule remove_component_right[where X = o_assn])
  apply (rule hfref_cong, assumption)
  apply (auto simp add: uncurry_def)
  done

lemmas read_n_refine = read_all_refine[OF not_deleted_code_refine_n]
lemmas mop_read_n_refine = read_all_mop_refine[OF not_deleted_code_refine_n]
end


context
  fixes R and kf and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>((\<lambda>S. kf S), (\<lambda>S. f' S)) \<in> [(\<lambda>S. P S)]\<^sub>a n_assn\<^sup>k \<rightarrow> x_assn\<close>
begin

lemmas read_n_refine0 = read_n_refine[OF not_deleted_code_refine[THEN remove_component_right],
  THEN remove_unused_unit_parameter]
lemmas mop_read_n_refine0 = mop_read_n_refine[OF not_deleted_code_refine[THEN remove_component_right]]

end


context
  fixes R and kf and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(uncurry (\<lambda>S C. kf C S), uncurry (\<lambda>S C. f' C S)) \<in> [uncurry (\<lambda>S C. P C S)]\<^sub>a m_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
begin
private lemma not_deleted_code_refine_m:
  \<open>(uncurry15 (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ M _ _ C. kf C M), uncurry15 (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ M _ _ C'. f' C' M)) \<in> [uncurry15 (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ M _ _ C. P C M)]\<^sub>a
   a_assn\<^sup>k *\<^sub>a b_assn\<^sup>k *\<^sub>a c_assn\<^sup>k *\<^sub>a d_assn\<^sup>k *\<^sub>a
  e_assn\<^sup>k *\<^sub>a f_assn\<^sup>k *\<^sub>a g_assn\<^sup>k  *\<^sub>a h_assn\<^sup>k *\<^sub>a i_assn\<^sup>k *\<^sub>a
  j_assn\<^sup>k *\<^sub>a k_assn\<^sup>k *\<^sub>a l_assn\<^sup>k *\<^sub>a m_assn\<^sup>k *\<^sub>a
  n_assn\<^sup>k *\<^sub>a o_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
  apply (rule add_pure_parameter2)
  apply (drule remove_pure_parameter2'[where f =kf and f'=f', OF not_deleted_code_refine])
  apply (drule remove_component_left[where X = a_assn])
  apply (drule remove_component_middle[where X = b_assn])
  apply (drule remove_component_middle[where X = c_assn])
  apply (drule remove_component_middle[where X = d_assn])
  apply (drule remove_component_middle[where X = e_assn])
  apply (drule remove_component_middle[where X = f_assn])
  apply (drule remove_component_middle[where X = g_assn])
  apply (drule remove_component_middle[where X = h_assn])
  apply (drule remove_component_middle[where X = i_assn])
  apply (drule remove_component_middle[where X = j_assn])
  apply (drule remove_component_middle[where X = k_assn])
  apply (drule remove_component_middle[where X = l_assn])
  apply (drule remove_component_right[where X = n_assn])
  apply (drule remove_component_right[where X = o_assn])
  apply (rule hfref_cong, assumption)
  apply (auto simp add: uncurry_def)
  done

lemmas read_m_refine = read_all_refine[OF not_deleted_code_refine_m]
lemmas mop_read_m_refine = read_all_mop_refine[OF not_deleted_code_refine_m]
end


context
  fixes R and kf and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>((\<lambda>S. kf S), (\<lambda>S. f' S)) \<in> [(\<lambda>S. P S)]\<^sub>a m_assn\<^sup>k \<rightarrow> x_assn\<close>
begin

lemmas read_m_refine0 = read_m_refine[OF not_deleted_code_refine[THEN remove_component_right],
  THEN remove_unused_unit_parameter]
lemmas mop_read_m_refine0 = mop_read_m_refine[OF not_deleted_code_refine[THEN remove_component_right]]

end
end
end