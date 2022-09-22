theory IsaSAT_Setup0_LLVM
  imports IsaSAT_Watch_List_LLVM IsaSAT_Lookup_Conflict_LLVM
    More_Sepref.WB_More_Refinement IsaSAT_Clauses_LLVM LBD_LLVM
    IsaSAT_Options_LLVM IsaSAT_VMTF_Setup_LLVM
    IsaSAT_Arena_Sorting_LLVM
    IsaSAT_Rephase_LLVM
    IsaSAT_EMA_LLVM
    IsaSAT_Stats_LLVM
    IsaSAT_VDom_LLVM
    Isabelle_LLVM.LLVM_DS_Block_Alloc
    Tuple17_LLVM
begin

no_notation WB_More_Refinement.fref (\<open>[_]\<^sub>f _ \<rightarrow> _\<close> [0,60,60] 60)
no_notation WB_More_Refinement.freft (\<open>_ \<rightarrow>\<^sub>f _\<close> [60,60] 60)
hide_const (open) NEMonad.ASSERT NEMonad.RETURN

text \<open>
This is the setup for accessing and modifying the state. The construction is kept generic 
(even if still targetting only our state). There is a lot of copy-paste that would be nice to automate
at some point.


We define 3 sort of operations:

  \<^enum> extracting an element, replacing it by an default element. Modifies the state. The name starts 
with \<^text>\<open>exctr\<close>

  \<^enum> reinserting an element, freeing the current one. Modifies the state. The name starts with
 \<^text>\<open>update\<close>

  \<^enum> in-place reading a value, possibly with pure parameters. Does not modify the state. The name
starts with \<^text>\<open>read\<close>

\<close>

type_synonym occs_assn = \<open>(64,(64 word),64)array_array_list\<close>

abbreviation \<open>occs_assn \<equiv> aal_assn' TYPE(64) TYPE(64) sint64_nat_assn\<close>

type_synonym twl_st_wll_trail_fast2 =
  \<open>(trail_pol_fast_assn, arena_assn, option_lookup_clause_assn,
    64 word, watched_wl_uint32, vmtf_remove_assn,
    32 word, cach_refinement_l_assn, lbd_assn, out_learned_assn,
    isasat_stats_assn, heur_assn,
   aivdom_assn, (64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word),
  opts_assn, arena_assn, occs_assn) tuple17\<close>

definition isasat_bounded_assn :: \<open>isasat \<Rightarrow> twl_st_wll_trail_fast2 \<Rightarrow> assn\<close> where
\<open>isasat_bounded_assn = tuple17_assn
  trail_pol_fast_assn  arena_fast_assn
  conflict_option_rel_assn
  sint64_nat_assn
  watchlist_fast_assn
  vmtf_remove_assn
  uint32_nat_assn
  cach_refinement_l_assn
  lbd_assn
  out_learned_assn
  isasat_stats_assn
  heuristic_assn
  aivdom_assn
  lcount_assn
  opts_assn
  arena_fast_assn
  occs_assn\<close>

sepref_register mop_arena_length

type_synonym twl_st_wll_trail_fast =
  \<open>trail_pol_fast_assn \<times> arena_assn \<times> option_lookup_clause_assn \<times>
    64 word \<times> watched_wl_uint32 \<times> vmtf_remove_assn \<times>
    32 word \<times> cach_refinement_l_assn \<times> lbd_assn \<times> out_learned_assn \<times> isasat_stats \<times>
    heur_assn \<times>
   aivdom_assn \<times> (64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word) \<times>
  opts_assn \<times> arena_assn \<times> occs_assn\<close>


text \<open>The following constants are not useful for the initialisation for the solver, but only as temporary replacement
  for values in state.\<close>
definition bottom_trail :: trail_pol where
  \<open>bottom_trail = do {
     let M0 = [] in
     let cs = [] in
     let M = replicate 0 UNSET in
     let M' = replicate 0 0 in
     let M'' = replicate 0 1 in
    ((M0, M, M', M'', 0, cs))
}\<close>

definition extract_trail_wl_heur where
  \<open>extract_trail_wl_heur = isasat_state_ops.remove_a bottom_trail\<close>

sepref_def bottom_trail_code
  is \<open>uncurry0 (RETURN bottom_trail)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a trail_pol_fast_assn\<close>
  unfolding bottom_trail_def trail_pol_fast_assn_def
  apply (rewrite in \<open>let _ = \<hole> in _\<close> annotate_assn[where A=\<open>arl64_assn unat_lit_assn\<close>])
  apply (rewrite in \<open>let _ = \<hole> in _\<close> al_fold_custom_empty[where 'l=64])
  apply (rewrite in \<open>let _ = _; _ = \<hole> in _\<close> al_fold_custom_empty[where 'l=64])
  apply (rewrite in \<open>let _ = _; _ = \<hole> in _\<close> annotate_assn[where A=\<open>arl64_assn uint32_nat_assn\<close>])

  apply (rewrite in \<open>let _ = _;_ = \<hole> in _\<close> annotate_assn[where A=\<open>larray64_assn (tri_bool_assn)\<close>])
  apply (rewrite in \<open>let _ = _;_ = _;_ = \<hole> in _\<close> annotate_assn[where A=\<open>larray64_assn uint32_nat_assn\<close>])
  apply (rewrite in \<open>let _ = _ in _\<close> larray_fold_custom_replicate)
  apply (rewrite in \<open>let _ = _ in _\<close> larray_fold_custom_replicate)
  apply (rewrite in \<open>let _ = _ in _\<close> larray_fold_custom_replicate)
  apply (rewrite at \<open>(_, \<hole>, _)\<close> unat_const_fold[where 'a=32])
  apply (rewrite at \<open>(op_larray_custom_replicate _ \<hole>)\<close> unat_const_fold[where 'a=32])
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  supply [[goals_limit = 1]]
  by sepref

definition bottom_arena :: \<open>arena\<close> where
  \<open>bottom_arena = []\<close>

definition extract_arena_wl_heur where
  \<open>extract_arena_wl_heur = isasat_state_ops.remove_b bottom_arena\<close>

sepref_def bottom_arena_code
  is \<open>uncurry0 (RETURN bottom_arena)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a arena_fast_assn\<close>
  unfolding bottom_arena_def al_fold_custom_empty[where 'l=64]
  by sepref

definition bottom_conflict :: \<open>conflict_option_rel\<close> where
  \<open>bottom_conflict = (True, 0, replicate 0 NOTIN)\<close>

definition extract_conflict_wl_heur where
  \<open>extract_conflict_wl_heur = isasat_state_ops.remove_c bottom_conflict\<close>

sepref_def bottom_conflict_code
  is \<open>uncurry0 (RETURN bottom_conflict)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a conflict_option_rel_assn\<close>
  unfolding bottom_conflict_def
    conflict_option_rel_assn_def lookup_clause_rel_assn_def array_fold_custom_replicate
  apply (rewrite at \<open>(_, \<hole>, _)\<close> unat_const_fold[where 'a=32])
  apply (annot_snat_const \<open>TYPE(32)\<close>)
  by sepref

definition bottom_decision_level :: nat where
  \<open>bottom_decision_level = 0\<close>

definition extract_literals_to_update_wl_heur :: \<open>_ \<Rightarrow> _\<close> where
  \<open>extract_literals_to_update_wl_heur = isasat_state_ops.remove_d bottom_decision_level\<close>

sepref_def bottom_decision_level_code
  is \<open>uncurry0 (RETURN bottom_decision_level)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  unfolding bottom_decision_level_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

definition bottom_watchlist :: \<open>(nat) watcher list list\<close> where
  \<open>bottom_watchlist = replicate 0 []\<close>

definition extract_watchlist_wl_heur where
  \<open>extract_watchlist_wl_heur = isasat_state_ops.remove_e bottom_watchlist\<close>

sepref_def bottom_watchlist_code
  is \<open>uncurry0 (RETURN bottom_watchlist)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a watchlist_fast_assn\<close>
  unfolding bottom_watchlist_def aal_fold_custom_empty[where 'l=64 and 'll=64]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

definition bottom_atom where
  \<open>bottom_atom = 0\<close>
lemma [sepref_fr_rules]: \<open>(uncurry0 (Mreturn 0), uncurry0 (RETURN bottom_atom)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a atom_assn\<close>
  unfolding bottom_atom_def
  apply sepref_to_hoare
  apply vcg
  apply (auto simp: atom_rel_def unat_rel_def unat.rel_def br_def entails_def ENTAILS_def)
  by (smt (verit, best) pure_true_conv rel_simps(51) sep.add_0)

definition bottom_vmtf :: \<open>isa_vmtf_remove_int\<close> where
  \<open>bottom_vmtf = ((replicate 0 (VMTF_Node 0 None None), 0, bottom_atom, bottom_atom, None), [], replicate 0 False)\<close>

definition extract_vmtf_wl_heur where
  \<open>extract_vmtf_wl_heur = isasat_state_ops.remove_f bottom_vmtf\<close>

sepref_def bottom_vmtf_code
  is \<open>uncurry0 (RETURN bottom_vmtf)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a vmtf_remove_assn\<close>
  unfolding bottom_vmtf_def
  apply (rewrite in \<open>((\<hole>, _, _, _, _), _, _)\<close> array_fold_custom_replicate)
  unfolding
   atom.fold_option array_fold_custom_replicate vmtf_remove_assn_def
    al_fold_custom_empty[where 'l=64]
  apply (rewrite at 0 in \<open>VMTF_Node \<hole>\<close> unat_const_fold[where 'a=64])
  apply (rewrite at \<open>(_, \<hole>, _, _)\<close> unat_const_fold[where 'a=64])
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  apply (rewrite at \<open>(\<hole>, _, _)\<close> annotate_assn[where A = vmtf_assn])
  apply (rewrite at \<open>(_, \<hole>, _)\<close> annotate_assn[where A =\<open>al_assn atom_assn\<close>])
  apply (rewrite at \<open>(_, _, \<hole>)\<close> annotate_assn[where A =\<open>phase_saver'_assn\<close>])
  by sepref

definition bottom_clvls :: \<open>nat\<close> where
  \<open>bottom_clvls = 0\<close>

definition extract_clvls_wl_heur where
  \<open>extract_clvls_wl_heur = isasat_state_ops.remove_g bottom_clvls\<close>

sepref_def bottom_clvls_code
  is \<open>uncurry0 (RETURN bottom_clvls)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding bottom_clvls_def
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref

definition bottom_ccach :: \<open>minimize_status list \<times> nat list\<close> where
  \<open>bottom_ccach = (replicate 0 SEEN_UNKNOWN, [])\<close>

definition extract_ccach_wl_heur where
  \<open>extract_ccach_wl_heur = isasat_state_ops.remove_h bottom_ccach\<close>

sepref_def bottom_ccach_code
  is \<open>uncurry0 (RETURN bottom_ccach)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a cach_refinement_l_assn\<close>
  unfolding bottom_ccach_def cach_refinement_l_assn_def array_fold_custom_replicate
  apply (rewrite at \<open>(_, \<hole>)\<close> al_fold_custom_empty[where 'l=64])
  apply (rewrite at \<open>(\<hole>, _)\<close> annotate_assn[where A = \<open>IICF_Array.array_assn minimize_status_assn\<close>])
  apply (annot_snat_const \<open>TYPE(32)\<close>)
  by sepref

definition extract_lbd_wl_heur where
  \<open>extract_lbd_wl_heur = isasat_state_ops.remove_i empty_lbd\<close>

definition bottom_outl :: \<open>out_learned\<close> where
  \<open>bottom_outl = []\<close>

definition extract_outl_wl_heur where
  \<open>extract_outl_wl_heur = isasat_state_ops.remove_j bottom_outl\<close>

sepref_def bottom_outl_code
  is \<open>uncurry0 (RETURN bottom_outl)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a out_learned_assn\<close>
  unfolding bottom_outl_def cach_refinement_l_assn_def array_fold_custom_replicate
  apply (rewrite at \<open>(\<hole>)\<close> al_fold_custom_empty[where 'l=64])
  by sepref

definition bottom_stats :: \<open>isasat_stats\<close> where
  \<open>bottom_stats = empty_stats\<close>

definition extract_stats_wl_heur where
  \<open>extract_stats_wl_heur = isasat_state_ops.remove_k bottom_stats\<close>

sepref_def bottom_stats_code
  is \<open>uncurry0 (RETURN bottom_stats)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a isasat_stats_assn\<close>
  unfolding bottom_stats_def
  by sepref

definition bottom_heur_int :: \<open> restart_heuristics\<close> where
  \<open>bottom_heur_int = (
  let \<phi> = replicate 0 False in
  let fema = ema_init (0) in
  let sema = ema_init (0) in let ccount = restart_info_init in
  let n = 0  in
  (fema, sema, ccount, 0, (\<phi>, 0, replicate n False, 0, replicate n False, 10000, 1000, 1), reluctant_init, False, replicate 0 False, (0, 0)))
\<close>
sepref_def bottom_heur_int_code
  is \<open>uncurry0 (RETURN bottom_heur_int)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a heuristic_int_assn\<close>
  supply [[goals_limit=1]]
  unfolding bottom_heur_int_def heuristic_int_assn_def phase_heur_assn_def
  apply (rewrite in \<open>(replicate _ False, _)\<close> annotate_assn[where A=phase_saver'_assn])
  apply (rewrite in \<open>(replicate _ False, _)\<close> array_fold_custom_replicate)
  apply (rewrite at \<open>(_, _, _, \<hole>, _, (_, _))\<close> annotate_assn[where A=phase_saver'_assn])
  apply (rewrite in \<open>(_, _, \<hole>, _)\<close> array_fold_custom_replicate)
  apply (rewrite at \<open>(_, \<hole>, _,_,_,_)\<close> snat_const_fold[where 'a=64])
  apply (rewrite at \<open>(_, _,_,\<hole>, _,_,_)\<close> snat_const_fold[where 'a=64])
  apply (rewrite in \<open>let _ =\<hole> in _\<close> annotate_assn[where A=phase_saver_assn])
  unfolding larray_fold_custom_replicate
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

definition bottom_heur :: \<open>_\<close> where
  \<open>bottom_heur = Restart_Heuristics (bottom_heur_int)\<close>

definition extract_heur_wl_heur where
  \<open>extract_heur_wl_heur = isasat_state_ops.remove_l bottom_heur\<close>

sepref_def bottom_heur_code
  is \<open>uncurry0 (RETURN bottom_heur)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a heuristic_assn\<close>
  supply [[goals_limit=1]]
  unfolding bottom_heur_def
  by sepref

definition bottom_vdom :: \<open>_\<close> where
  \<open>bottom_vdom = AIvdom_init [] [] []\<close>

definition extract_vdom_wl_heur where
  \<open>extract_vdom_wl_heur = isasat_state_ops.remove_m bottom_vdom\<close>

sepref_def bottom_vdom_code
  is \<open>uncurry0 (RETURN bottom_vdom)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a aivdom_assn\<close>
  supply [[goals_limit=1]]
  unfolding bottom_vdom_def
  unfolding al_fold_custom_empty[where 'l=64]
  by sepref

definition bottom_lcount :: \<open>clss_size\<close> where
  \<open>bottom_lcount = (0, 0, 0, 0, 0)\<close>

definition extract_lcount_wl_heur where
  \<open>extract_lcount_wl_heur = isasat_state_ops.remove_n bottom_lcount\<close>

sepref_def bottom_lcount_code
  is \<open>uncurry0 (RETURN bottom_lcount)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a lcount_assn\<close>
  supply [[goals_limit=1]]
  unfolding bottom_lcount_def lcount_assn_def
  unfolding al_fold_custom_empty[where 'l=64]
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

definition bottom_opts :: \<open>opts\<close> where
  \<open>bottom_opts = IsaOptions False False False 0 0 0 0 0 0 0\<close>

definition extract_opts_wl_heur where
  \<open>extract_opts_wl_heur = isasat_state_ops.remove_o bottom_opts\<close>

sepref_def bottom_opts_code
  is \<open>uncurry0 (RETURN bottom_opts)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a opts_assn\<close>
  supply [[goals_limit=1]]
  unfolding bottom_opts_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

definition bottom_old_arena :: \<open>arena\<close> where
  \<open>bottom_old_arena = []\<close>

definition extract_old_arena_wl_heur where
  \<open>extract_old_arena_wl_heur = isasat_state_ops.remove_p bottom_old_arena\<close>

sepref_def bottom_old_arena_code
  is \<open>uncurry0 (RETURN bottom_old_arena)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a arena_fast_assn\<close>
  supply [[goals_limit=1]]
  unfolding bottom_old_arena_def  al_fold_custom_empty[where 'l=64]
  by sepref

schematic_goal free_trail_pol_fast_assn[sepref_frame_free_rules]: \<open>MK_FREE trail_pol_fast_assn ?a\<close>
    unfolding trail_pol_fast_assn_def
    by synthesize_free

sepref_def free_trail_pol_fast
  is \<open>mop_free\<close>
  :: \<open>trail_pol_fast_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

lemma free_trail_pol_fast_assn2: \<open>MK_FREE trail_pol_fast_assn free_trail_pol_fast\<close>
  unfolding free_trail_pol_fast_def
  by (rule back_subst[of \<open>MK_FREE trail_pol_fast_assn\<close>, OF free_trail_pol_fast_assn])
    (auto intro!: ext)
 
schematic_goal free_arena_fast_assn[sepref_frame_free_rules]: \<open>MK_FREE arena_fast_assn ?a\<close>
    by synthesize_free

sepref_def free_arena_fast
  is \<open>mop_free\<close>
  :: \<open>arena_fast_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

lemma free_arena_fast_assn2: \<open>MK_FREE arena_fast_assn free_arena_fast\<close>
  unfolding free_arena_fast_def
  by (rule back_subst[of \<open>MK_FREE arena_fast_assn\<close>, OF free_arena_fast_assn])
    (auto intro!: ext)

schematic_goal free_conflict_option_rel_assn[sepref_frame_free_rules]: \<open>MK_FREE conflict_option_rel_assn ?a\<close>
    by synthesize_free

sepref_def free_conflict_option_rel
  is \<open>mop_free\<close>
  :: \<open>conflict_option_rel_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

lemma free_conflict_option_rel_assn2: \<open>MK_FREE conflict_option_rel_assn free_conflict_option_rel\<close>
  unfolding free_conflict_option_rel_def
  by (rule back_subst[of \<open>MK_FREE conflict_option_rel_assn\<close>, OF free_conflict_option_rel_assn])
    (auto intro!: ext)

schematic_goal free_sint64_nat_assn[sepref_frame_free_rules]: \<open>MK_FREE sint64_nat_assn ?a\<close>
    by synthesize_free

sepref_def free_sint64_nat
  is \<open>mop_free\<close>
  :: \<open>sint64_nat_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

lemma free_sint64_nat_assn_assn2: \<open>MK_FREE sint64_nat_assn free_sint64_nat\<close>
  unfolding free_sint64_nat_def
  by (rule back_subst[of \<open>MK_FREE sint64_nat_assn\<close>, OF free_sint64_nat_assn])
    (auto intro!: ext)

schematic_goal free_watchlist_fast_assn[sepref_frame_free_rules]: \<open>MK_FREE watchlist_fast_assn ?a\<close>
    by synthesize_free

sepref_def free_watchlist_fast
  is \<open>mop_free\<close>
  :: \<open>watchlist_fast_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

lemma free_watchlist_fast_assn2: \<open>MK_FREE watchlist_fast_assn free_watchlist_fast\<close>
  unfolding free_watchlist_fast_def
  by (rule back_subst[of \<open>MK_FREE watchlist_fast_assn\<close>, OF free_watchlist_fast_assn])
    (auto intro!: ext)

schematic_goal free_vmtf_remove_assn[sepref_frame_free_rules]: \<open>MK_FREE vmtf_remove_assn ?a\<close>
    unfolding vmtf_remove_assn_def
    by synthesize_free

sepref_def free_vmtf_remove
  is \<open>mop_free\<close>
  :: \<open>vmtf_remove_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

lemma free_vmtf_remove_assn2: \<open>MK_FREE vmtf_remove_assn free_vmtf_remove\<close>
  unfolding free_vmtf_remove_def
  by (rule back_subst[of \<open>MK_FREE vmtf_remove_assn\<close>, OF free_vmtf_remove_assn])
    (auto intro!: ext)

schematic_goal free_uint32_nat_assn[sepref_frame_free_rules]: \<open>MK_FREE uint32_nat_assn ?a\<close>
    by synthesize_free

sepref_def free_uint32_nat
  is \<open>mop_free\<close>
  :: \<open>uint32_nat_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

lemma free_uint32_nat_assn2: \<open>MK_FREE uint32_nat_assn free_uint32_nat\<close>
  unfolding free_uint32_nat_def
  by (rule back_subst[of \<open>MK_FREE uint32_nat_assn\<close>, OF free_uint32_nat_assn])
    (auto intro!: ext)
 
schematic_goal free_cach_refinement_l_assn[sepref_frame_free_rules]: \<open>MK_FREE cach_refinement_l_assn ?a\<close>
    by synthesize_free

sepref_def free_cach_refinement_l
  is \<open>mop_free\<close>
  :: \<open>cach_refinement_l_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

lemma free_cach_refinement_l_assn2: \<open>MK_FREE cach_refinement_l_assn free_cach_refinement_l\<close>
  unfolding free_cach_refinement_l_def
  by (rule back_subst[of \<open>MK_FREE cach_refinement_l_assn\<close>, OF free_cach_refinement_l_assn])
    (auto intro!: ext)
 
schematic_goal free_lbd_assn[sepref_frame_free_rules]: \<open>MK_FREE lbd_assn ?a\<close>
    by synthesize_free

sepref_def free_lbd
  is \<open>mop_free\<close>
  :: \<open>lbd_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

lemma free_lbd_assn2: \<open>MK_FREE lbd_assn free_lbd\<close>
  unfolding free_lbd_def
  by (rule back_subst[of \<open>MK_FREE lbd_assn\<close>, OF free_lbd_assn])
    (auto intro!: ext)
 
schematic_goal free_outl_assn[sepref_frame_free_rules]: \<open>MK_FREE out_learned_assn ?a\<close>
    by synthesize_free

sepref_def free_outl
  is \<open>mop_free\<close>
  :: \<open>out_learned_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

lemma free_outl_assn2: \<open>MK_FREE out_learned_assn free_outl\<close>
  unfolding free_outl_def
  by (rule back_subst[of \<open>MK_FREE out_learned_assn\<close>, OF free_outl_assn])
    (auto intro!: ext)

schematic_goal free_heur_assn[sepref_frame_free_rules]: \<open>MK_FREE heuristic_assn ?a\<close>
    unfolding heuristic_assn_def code_hider_assn_def
    by synthesize_free

sepref_def free_heur
  is \<open>mop_free\<close>
  :: \<open>heuristic_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

lemma free_heur_assn2: \<open>MK_FREE heuristic_assn free_heur\<close>
  unfolding free_heur_def
  by (rule back_subst[of \<open>MK_FREE heuristic_assn\<close>, OF free_heur_assn])
    (auto intro!: ext)

schematic_goal free_isasat_stats_assn[sepref_frame_free_rules]: \<open>MK_FREE isasat_stats_assn ?a\<close>
  unfolding isasat_stats_assn_def code_hider_assn_def
  by synthesize_free

sepref_def free_stats
  is \<open>mop_free\<close>
  :: \<open>isasat_stats_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

lemma free_isasat_stats_assn2: \<open>MK_FREE isasat_stats_assn free_stats\<close>
  unfolding free_stats_def
  by (rule back_subst[of \<open>MK_FREE isasat_stats_assn\<close>, OF free_isasat_stats_assn])
    (auto intro!: ext)

schematic_goal free_vdom_assn[sepref_frame_free_rules]: \<open>MK_FREE aivdom_assn ?a\<close>
    unfolding aivdom_assn_def code_hider_assn_def
    by synthesize_free

sepref_def free_vdom
  is \<open>mop_free\<close>
  :: \<open>aivdom_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

lemma free_vdom_assn2: \<open>MK_FREE aivdom_assn free_vdom\<close>
  unfolding free_vdom_def
  by (rule back_subst[of \<open>MK_FREE aivdom_assn\<close>, OF free_vdom_assn])
    (auto intro!: ext)

schematic_goal free_lcount_assn[sepref_frame_free_rules]: \<open>MK_FREE lcount_assn ?a\<close>
    unfolding lcount_assn_def code_hider_assn_def
    by synthesize_free

sepref_def free_lcount
  is \<open>mop_free\<close>
  :: \<open>lcount_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

lemma free_lcount_assn2: \<open>MK_FREE lcount_assn free_lcount\<close>
  unfolding free_lcount_def
  by (rule back_subst[of \<open>MK_FREE lcount_assn\<close>, OF free_lcount_assn])
    (auto intro!: ext)

schematic_goal free_opts_assn[sepref_frame_free_rules]: \<open>MK_FREE opts_assn ?a\<close>
    unfolding opts_assn_def code_hider_assn_def opts_rel_assn_def
    by synthesize_free

sepref_def free_opts
  is \<open>mop_free\<close>
  :: \<open>opts_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

lemma free_opts_assn2: \<open>MK_FREE opts_assn free_opts\<close>
  unfolding free_opts_def
  by (rule back_subst[of \<open>MK_FREE opts_assn\<close>, OF free_opts_assn])
    (auto intro!: ext)

schematic_goal free_old_arena_fast_assn[sepref_frame_free_rules]: \<open>MK_FREE arena_fast_assn ?a\<close>
    by synthesize_free

sepref_def free_old_arena_fast
  is \<open>mop_free\<close>
  :: \<open>arena_fast_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

lemma free_old_arena_fast_assn2: \<open>MK_FREE arena_fast_assn free_old_arena_fast\<close>
  unfolding free_old_arena_fast_def free_arena_fast_def
  by (rule back_subst[of \<open>MK_FREE arena_fast_assn\<close>, OF free_old_arena_fast_assn])
    (auto intro!: ext)

sepref_def free_occs_fast
  is \<open>mop_free\<close>
  :: \<open>occs_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref


definition bottom_occs :: \<open>nat list list\<close> where
  \<open>bottom_occs = op_aal_lempty TYPE(64) TYPE(64) 0\<close>

definition extract_occs_wl_heur where
  \<open>extract_occs_wl_heur = isasat_state_ops.remove_q bottom_occs\<close>

sepref_def bottom_occs_code
  is \<open>uncurry0 (RETURN bottom_occs)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a occs_assn\<close>
  supply [[goals_limit=1]]
  unfolding bottom_occs_def aal_fold_custom_empty[where 'l=64 and 'll=64]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

schematic_goal free_occs_fast_assn[sepref_frame_free_rules]: \<open>MK_FREE occs_assn ?a\<close>
  by synthesize_free

lemma free_occs_fast_assn2: \<open>MK_FREE occs_assn free_occs_fast\<close>
  unfolding free_occs_fast_def
  by (rule back_subst[of \<open>MK_FREE occs_assn\<close>, OF free_occs_fast_assn])
    (auto intro!: ext)

global_interpretation isasat_state where
  a_assn = trail_pol_fast_assn and
  b_assn = arena_fast_assn and
  c_assn = conflict_option_rel_assn and
  d_assn = sint64_nat_assn and
  e_assn = watchlist_fast_assn and
  f_assn = vmtf_remove_assn and
  g_assn = uint32_nat_assn and
  h_assn = cach_refinement_l_assn and
  i_assn = lbd_assn and
  j_assn = out_learned_assn and
  k_assn = isasat_stats_assn and
  l_assn = heuristic_assn and
  m_assn = aivdom_assn and
  n_assn = lcount_assn and
  o_assn = opts_assn and
  p_assn = arena_fast_assn and
  q_assn = occs_assn and
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
  d = \<open>(bottom_decision_level_code)\<close> and
  d_free = \<open>free_sint64_nat\<close> and
  e_default = bottom_watchlist and
  e = \<open>bottom_watchlist_code\<close> and
  e_free = free_watchlist_fast and
  f_default = bottom_vmtf and
  f = \<open>bottom_vmtf_code\<close> and
  f_free = free_vmtf_remove and
  g_default = bottom_clvls and
  g = \<open>bottom_clvls_code\<close>and
  g_free = free_uint32_nat and
  h_default = bottom_ccach and
  h = \<open>bottom_ccach_code\<close> and
  h_free = free_cach_refinement_l and
  i_default = empty_lbd and
  i = \<open>empty_lbd_code\<close> and
  i_free = free_lbd and
  j_default = bottom_outl and
  j = \<open>bottom_outl_code\<close> and
  j_free = free_outl and
  k_default = bottom_stats and
  k = \<open>bottom_stats_code\<close> and
  k_free = free_stats and
  l_default = bottom_heur and
  l = \<open>bottom_heur_code\<close> and
  l_free = free_heur and
  m_default = bottom_vdom and
  m = \<open>bottom_vdom_code\<close> and
  m_free = free_vdom and
  n_default = bottom_lcount and
  n = \<open>bottom_lcount_code\<close> and
  n_free = free_lcount and
  ko_default = bottom_opts and
  ko = \<open>bottom_opts_code\<close> and
  o_free = free_opts and
  p_default = bottom_old_arena and
  p = \<open>bottom_old_arena_code\<close> and
  p_free = free_old_arena_fast and
  q_default = bottom_occs and
  q = bottom_occs_code and
  q_free = free_occs_fast
  rewrites
    \<open>isasat_assn \<equiv> isasat_bounded_assn\<close> and
    \<open>remove_a \<equiv> extract_trail_wl_heur\<close> and
    \<open>remove_b \<equiv> extract_arena_wl_heur\<close> and
    \<open>remove_c \<equiv> extract_conflict_wl_heur\<close> and
    \<open>remove_d \<equiv> extract_literals_to_update_wl_heur\<close> and
    \<open>remove_e \<equiv> extract_watchlist_wl_heur\<close> and
    \<open>remove_f \<equiv> extract_vmtf_wl_heur\<close> and
    \<open>remove_g \<equiv> extract_clvls_wl_heur\<close> and
    \<open>remove_h \<equiv> extract_ccach_wl_heur\<close> and
    \<open>remove_i \<equiv> extract_lbd_wl_heur\<close> and
    \<open>remove_j  \<equiv> extract_outl_wl_heur\<close> and
    \<open>remove_k \<equiv> extract_stats_wl_heur\<close> and
    \<open>remove_l \<equiv> extract_heur_wl_heur\<close> and
    \<open>remove_m \<equiv> extract_vdom_wl_heur\<close> and
    \<open>remove_n \<equiv> extract_lcount_wl_heur\<close> and
    \<open>remove_o \<equiv> extract_opts_wl_heur\<close> and
    \<open>remove_p \<equiv> extract_old_arena_wl_heur\<close>and
    \<open>remove_q \<equiv> extract_occs_wl_heur\<close>
  apply unfold_locales
  subgoal by (rule bottom_trail_code.refine)
  subgoal by (rule bottom_arena_code.refine)
  subgoal by (rule bottom_conflict_code.refine)
  subgoal by (rule bottom_decision_level_code.refine)
  subgoal by (rule bottom_watchlist_code.refine)
  subgoal by (rule bottom_vmtf_code.refine)
  subgoal by (rule bottom_clvls_code.refine)
  subgoal by (rule bottom_ccach_code.refine)
  subgoal by (rule empty_lbd_hnr)
  subgoal by (rule bottom_outl_code.refine)
  subgoal by (rule bottom_stats_code.refine)
  subgoal by (rule bottom_heur_code.refine)
  subgoal by (rule bottom_vdom_code.refine)
  subgoal by (rule bottom_lcount_code.refine)
  subgoal by (rule bottom_opts_code.refine)
  subgoal by (rule bottom_old_arena_code.refine)
  subgoal by (rule bottom_occs_code.refine)
  subgoal by (rule free_trail_pol_fast_assn2)
  subgoal by (rule free_arena_fast_assn2)
  subgoal by (rule free_conflict_option_rel_assn2)
  subgoal by (rule free_sint64_nat_assn_assn2)
  subgoal by (rule free_watchlist_fast_assn2)
  subgoal by (rule free_vmtf_remove_assn2)
  subgoal by (rule free_uint32_nat_assn2)
  subgoal by (rule free_cach_refinement_l_assn2)
  subgoal by (rule free_lbd_assn2)
  subgoal by (rule free_outl_assn2)
  subgoal by (rule free_isasat_stats_assn2)
  subgoal by (rule free_heur_assn2)
  subgoal by (rule free_vdom_assn2)
  subgoal by (rule free_lcount_assn2)
  subgoal by (rule free_opts_assn2)
  subgoal by (rule free_old_arena_fast_assn2)
  subgoal by (rule free_occs_fast_assn2)
  subgoal unfolding isasat_bounded_assn_def isasat_state_ops.isasat_assn_def .
  subgoal unfolding extract_trail_wl_heur_def .
  subgoal unfolding extract_arena_wl_heur_def .
  subgoal unfolding extract_conflict_wl_heur_def .
  subgoal unfolding extract_literals_to_update_wl_heur_def .
  subgoal unfolding extract_watchlist_wl_heur_def .
  subgoal unfolding extract_vmtf_wl_heur_def .
  subgoal unfolding extract_clvls_wl_heur_def .
  subgoal unfolding extract_ccach_wl_heur_def .
  subgoal unfolding extract_lbd_wl_heur_def .
  subgoal unfolding extract_outl_wl_heur_def .
  subgoal unfolding extract_stats_wl_heur_def .
  subgoal unfolding extract_heur_wl_heur_def .
  subgoal unfolding extract_vdom_wl_heur_def .
  subgoal unfolding extract_lcount_wl_heur_def .
  subgoal unfolding extract_opts_wl_heur_def .
  subgoal unfolding extract_old_arena_wl_heur_def .
  subgoal unfolding extract_occs_wl_heur_def .
  done


(*There must some setup missing for Sepref to do that automatically*)
lemma [llvm_pre_simp]:
  \<open>(Mreturn \<circ>\<^sub>1\<^sub>7 IsaSAT_int) a1 a2 a3 x a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 =
  Mreturn (IsaSAT_int a1 a2 a3 x a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17)\<close>
  by auto

lemmas [llvm_code del] =
  update_a_code_def
  update_b_code_def
  update_c_code_def
  update_d_code_def
  update_e_code_def
  update_f_code_def
  update_h_code_def
  update_i_code_def
  update_j_code_def
  update_k_code_def
  update_l_code_def
  update_m_code_def
  update_n_code_def
  update_o_code_def
  update_p_code_def
  update_q_code_def

lemmas [unfolded comp_def inline_node_case, llvm_code] =
  remove_d_code_alt_def
  remove_b_code_alt_def
  remove_a_code_alt_def
  bottom_decision_level_code_def
  bottom_arena_code_def
  bottom_trail_code_def
  update_a_code_alt_def
  update_b_code_alt_def
  update_c_code_alt_def
  update_d_code_alt_def
  update_e_code_alt_def
  update_f_code_alt_def
  update_h_code_alt_def
  update_i_code_alt_def
  update_j_code_alt_def
  update_k_code_alt_def
  update_l_code_alt_def
  update_m_code_alt_def
  update_n_code_alt_def
  update_o_code_alt_def
  update_p_code_alt_def
  update_q_code_alt_def

lemma add_pure_parameter:
  assumes \<open>\<And>C C'. (C, C') \<in> R \<Longrightarrow> (f C, f' C') \<in> [P C']\<^sub>a A \<rightarrow> b\<close>
  shows \<open>(uncurry f, uncurry f') \<in> [uncurry P]\<^sub>a (pure R)\<^sup>k *\<^sub>a A \<rightarrow> b\<close>
  apply sepref_to_hoare
  apply vcg
  apply auto
  apply (subst POSTCOND_def hn_ctxt_def sep_conj_empty' pure_true_conv EXTRACT_def)+
  apply (rule assms[to_hnr, simplified, unfolded hn_ctxt_def hn_refine_def htriple_def
    sep_conj_empty' pure_true_conv, rule_format])
  apply auto
  done

lemma remove_pure_parameter:
  assumes  \<open>(uncurry f, uncurry f') \<in> [uncurry P]\<^sub>a (pure R)\<^sup>k *\<^sub>a A \<rightarrow> b\<close> \<open>(C, C') \<in> R\<close>
  shows \<open>(f C, f' C') \<in> [P C']\<^sub>a A \<rightarrow> b\<close>
  using assms(2) assms(1)[to_hnr, simplified, unfolded hn_ctxt_def hn_refine_def htriple_def
    sep_conj_empty' pure_true_conv, rule_format]
  apply sepref_to_hoare
  apply vcg
  apply (subst POSTCOND_def hn_ctxt_def sep_conj_empty' pure_true_conv EXTRACT_def)+
  by (auto simp: pure_true_conv)

lemma add_pure_parameter2:
  assumes \<open>\<And>C C'. (C, C') \<in> R \<Longrightarrow> (\<lambda>S. f S C, \<lambda>S. f' S C') \<in> [\<lambda>S. P S C']\<^sub>a A \<rightarrow> b\<close>
  shows \<open>(uncurry f, uncurry f') \<in> [uncurry P]\<^sub>a A *\<^sub>a (pure R)\<^sup>k \<rightarrow> b\<close>
  apply sepref_to_hoare
  apply vcg
  apply auto
  apply (subst POSTCOND_def hn_ctxt_def sep_conj_empty' pure_true_conv EXTRACT_def)+
  apply (rule assms[to_hnr, simplified, unfolded hn_ctxt_def hn_refine_def htriple_def
    sep_conj_empty' pure_true_conv, rule_format])
  apply auto
  done

lemma remove_pure_parameter2:
  assumes  \<open>(uncurry f, uncurry f') \<in> [uncurry P]\<^sub>a A *\<^sub>a (pure R)\<^sup>k \<rightarrow> b\<close> \<open>(C, C') \<in> R\<close>
  shows \<open>(\<lambda>S. f S C, \<lambda>S. f' S C') \<in> [\<lambda>S. P  S C']\<^sub>a A \<rightarrow> b\<close>
  using assms(2) assms(1)[to_hnr, simplified, unfolded hn_ctxt_def hn_refine_def htriple_def
    sep_conj_empty' pure_true_conv, rule_format]
  apply sepref_to_hoare
  apply vcg
  apply (subst POSTCOND_def hn_ctxt_def sep_conj_empty' pure_true_conv EXTRACT_def)+
  apply (auto simp: pure_true_conv)
  done

lemma remove_pure_parameter2':
  assumes  \<open>(uncurry (\<lambda>S C. f C S), uncurry (\<lambda>S C. f' C S)) \<in> [uncurry P]\<^sub>a A *\<^sub>a (pure R)\<^sup>k \<rightarrow> b\<close> \<open>(C, C') \<in> R\<close>
  shows \<open>(f C, f' C') \<in> [\<lambda>S. P S C']\<^sub>a A \<rightarrow> b\<close>
  by (rule remove_pure_parameter2)
    (rule assms)+

lemma remove_pure_parameter2_twoargs:
  assumes  \<open>(uncurry2 f, uncurry2 f') \<in> [uncurry2 P]\<^sub>a A *\<^sub>a (pure R)\<^sup>k *\<^sub>a (pure R')\<^sup>k \<rightarrow> b\<close> \<open>(C, C') \<in> R\<close> \<open>(D,D')\<in>R'\<close>
  shows \<open>(\<lambda>S. f S C D, \<lambda>S. f' S C' D') \<in> [\<lambda>S. P  S C' D']\<^sub>a A \<rightarrow> b\<close>
  using assms(2-) assms(1)[to_hnr, simplified, unfolded hn_ctxt_def hn_refine_def htriple_def
    sep_conj_empty' pure_true_conv, rule_format]
  apply sepref_to_hoare
  apply vcg
  apply (subst POSTCOND_def hn_ctxt_def sep_conj_empty' pure_true_conv EXTRACT_def)+
  apply (auto simp: pure_true_conv)
  done


locale read_trail_param_adder0_ops =
  fixes P :: \<open>trail_pol \<Rightarrow> bool\<close> and f' :: \<open>trail_pol \<Rightarrow> 'r nres\<close>
begin

definition mop where
  \<open>mop N = do {
    ASSERT (P (get_trail_wl_heur N));
    read_all_st (\<lambda>M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. f' M) N
   }\<close>

end

lemma remove_component_right:
  assumes \<open>(f, f') \<in> [P]\<^sub>a A \<rightarrow> B\<close>
  shows \<open>(uncurry (\<lambda>M _. f M), uncurry (\<lambda>M _. f' M)) \<in> [uncurry (\<lambda>M _. P M)]\<^sub>a A *\<^sub>a X\<^sup>k \<rightarrow> B\<close>
  using assms
  unfolding hfref_def
  apply clarsimp
  apply (rule hn_refine_frame')
  apply auto
  done
lemma hn_refine_frame'': "hn_refine \<Gamma> c \<Gamma>' R CP m \<Longrightarrow> hn_refine (F**\<Gamma>) c (F**\<Gamma>') R CP m"
  by (metis hn_refine_frame' sep_conj_c(1))

lemma hn_refine_frame_mid'': "hn_refine (F**G) c (F'**G') R CP m \<Longrightarrow> hn_refine (F**\<Gamma>**G) c (F'**\<Gamma>**G') R CP m"
  by (smt (verit) hn_refine_frame' sep_conj_aci(2) sep_conj_c(1))

lemma remove_component_left:
  assumes \<open>(f, f') \<in> [P]\<^sub>a A \<rightarrow> B\<close>
  shows \<open>(uncurry (\<lambda>_ M. f M), uncurry (\<lambda>_ M. f' M)) \<in> [uncurry (\<lambda>_ M. P M)]\<^sub>a  X\<^sup>k *\<^sub>a A \<rightarrow> B\<close>
  using assms
  unfolding hfref_def
  apply clarsimp
  apply (rule hn_refine_frame'')
  apply auto
  done

lemma remove_component_middle:
  assumes \<open>(f, f') \<in> [P]\<^sub>a A *\<^sub>a B \<rightarrow> C\<close>
  shows \<open>(uncurry2 (\<lambda>M _ N. f (M, N)), uncurry2 (\<lambda>M _ N. f' (M, N))) \<in> [uncurry2 (\<lambda>M _ N. P (M, N))]\<^sub>a  A *\<^sub>a X\<^sup>k *\<^sub>a B\<rightarrow> C\<close>
  using assms
  unfolding hfref_def
  apply clarsimp
  apply (rule hn_refine_frame_mid'')
  apply auto
  done


lemma (in -)hfref_cong: \<open>(a, b) \<in> [P]\<^sub>a A \<rightarrow> B \<Longrightarrow> a = a' \<Longrightarrow> b = b' \<Longrightarrow> P = P' \<Longrightarrow> (a',b')\<in> [P']\<^sub>a A \<rightarrow> B\<close>
  by auto

lemma split_snd_pure_arg:
  assumes \<open>(uncurry (\<lambda>N C. f C N), uncurry (\<lambda>N C'.  f' C' N))
    \<in> [uncurry (\<lambda>S C. P S C)]\<^sub>a K\<^sup>k *\<^sub>a (pure (R \<times>\<^sub>f R'))\<^sup>k \<rightarrow> x_assn\<close>
  shows \<open>(uncurry2 (\<lambda>N C D. f (C,D) N), uncurry2 (\<lambda>N C' D'.  f' (C',D') N))
    \<in> [uncurry2 (\<lambda>S C D. P S (C, D))]\<^sub>a K\<^sup>k *\<^sub>a (pure(R))\<^sup>k *\<^sub>a (pure R')\<^sup>k \<rightarrow> x_assn\<close>
  using assms unfolding hfref_def
  by (auto simp flip: prod_assn_pure_conv)

lemma add_pure_parameter2_twoargs:
  assumes \<open>\<And>C C' D D'. (C, C') \<in> R \<Longrightarrow>  (D, D') \<in> R' \<Longrightarrow> (\<lambda>S. f S C D, \<lambda>S. f' S C' D') \<in> [\<lambda>S. P S C' D']\<^sub>a A \<rightarrow> b\<close>
  shows \<open>(uncurry2 f, uncurry2 f') \<in> [uncurry2 P]\<^sub>a A *\<^sub>a (pure R)\<^sup>k*\<^sub>a (pure R')\<^sup>k \<rightarrow> b\<close>
  apply sepref_to_hoare
  apply vcg
  apply auto
  apply (subst POSTCOND_def hn_ctxt_def sep_conj_empty' pure_true_conv EXTRACT_def)+
  apply (rule assms[to_hnr, simplified, unfolded hn_ctxt_def hn_refine_def htriple_def EXTRACT_def
    sep_conj_empty' pure_true_conv, rule_format])
  apply auto
  done

lemma remove_unused_unit_parameter:
  assumes \<open>(uncurry (\<lambda>S _. f S), uncurry (\<lambda>S _. f' S)) \<in> [uncurry (\<lambda>S _. P S)]\<^sub>a A *\<^sub>a (pure unit_rel)\<^sup>k \<rightarrow> b\<close>
  shows \<open>(f, f') \<in> [P]\<^sub>a A \<rightarrow> b\<close>
  apply sepref_to_hoare
  apply vcg
  apply (subst POSTCOND_def hn_ctxt_def sep_conj_empty' pure_true_conv EXTRACT_def)+
  apply (rule assms[to_hnr, simplified, unfolded hn_ctxt_def hn_refine_def htriple_def
    sep_conj_empty' pure_true_conv, rule_format])
  apply auto
  done

lemma add_pure_parameter_unit:
  assumes \<open>(\<lambda>S. f S (), \<lambda>S. f' S ()) \<in> [\<lambda>S. P S]\<^sub>a A \<rightarrow> b\<close>
  shows \<open>(f (), f' ()) \<in> [P]\<^sub>a A \<rightarrow> b\<close>
  apply sepref_to_hoare
  apply vcg
  apply (subst POSTCOND_def hn_ctxt_def sep_conj_empty' pure_true_conv EXTRACT_def)+
  apply (rule assms[to_hnr, simplified, unfolded hn_ctxt_def hn_refine_def htriple_def
    sep_conj_empty' pure_true_conv, rule_format])
  apply auto
  done


abbreviation read_trail_wl_heur_code :: \<open>_ \<Rightarrow> _ \<Rightarrow> _\<close> where
  \<open>read_trail_wl_heur_code f \<equiv> read_all_st_code  (\<lambda>M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. f M)\<close>
abbreviation read_trail_wl_heur :: \<open>_ \<Rightarrow> isasat \<Rightarrow> _\<close> where
  \<open>read_trail_wl_heur f \<equiv> read_all_st  (\<lambda>M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. f M)\<close>

locale read_trail_param_adder0 = read_trail_param_adder0_ops P f'
  for P :: \<open> trail_pol \<Rightarrow> bool\<close> and f' :: \<open>trail_pol \<Rightarrow> 'r nres\<close> +
  fixes f and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close>
  assumes not_deleted_code_refine: \<open>(f, f') \<in> [P]\<^sub>a trail_pol_fast_assn\<^sup>k \<rightarrow> x_assn\<close>
begin

text \<open>I tried to automate the generation of the theorem but I failed (although generating the sequence
  is actually very easy...)\<close>
lemma not_deleted_code_refine':
  \<open>(uncurry16 (\<lambda>M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. f M), uncurry16 (\<lambda>M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. f' M)) \<in>
   [uncurry16 (\<lambda>M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. P M)]\<^sub>a
   trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a
  watchlist_fast_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a cach_refinement_l_assn\<^sup>k *\<^sub>a
  lbd_assn\<^sup>k *\<^sub>a out_learned_assn\<^sup>k *\<^sub>a isasat_stats_assn\<^sup>k *\<^sub>a heuristic_assn\<^sup>k *\<^sub>a
  aivdom_assn\<^sup>k *\<^sub>a lcount_assn\<^sup>k *\<^sub>a opts_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a occs_assn\<^sup>k \<rightarrow> x_assn\<close>
  apply (insert not_deleted_code_refine)
  apply (drule remove_component_right[where X = arena_fast_assn])
  apply (drule remove_component_right[where X = conflict_option_rel_assn])
  apply (drule remove_component_right[where X = sint64_nat_assn])
  apply (drule remove_component_right[where X = watchlist_fast_assn])
  apply (drule remove_component_right[where X = vmtf_remove_assn])
  apply (drule remove_component_right[where X = uint32_nat_assn])
  apply (drule remove_component_right[where X = cach_refinement_l_assn])
  apply (drule remove_component_right[where X = lbd_assn])
  apply (drule remove_component_right[where X = out_learned_assn])
  apply (drule remove_component_right[where X = isasat_stats_assn])
  apply (drule remove_component_right[where X = heuristic_assn])
  apply (drule remove_component_right[where X = aivdom_assn])
  apply (drule remove_component_right[where X = lcount_assn])
  apply (drule remove_component_right[where X = opts_assn])
  apply (drule remove_component_right[where X = arena_fast_assn])
  apply (drule remove_component_right[where X = occs_assn])
  apply (rule hfref_cong, assumption)
  apply (auto simp add: uncurry_def)
  done

lemmas refine = read_all_code_refine[OF not_deleted_code_refine']

lemma mop_refine:
  \<open>(read_trail_wl_heur_code f, mop) \<in> isasat_bounded_assn\<^sup>k\<rightarrow>\<^sub>a x_assn\<close>
  unfolding mop_def
  apply (rule refine_ASSERT_move_to_pre0)
  apply (rule hfref_cong[OF refine])
  apply (auto intro!: ext split: isasat_int_splits)
  done

end

locale read_all_param_adder_ops =
  fixes f' :: \<open>'a \<Rightarrow> trail_pol \<Rightarrow> arena \<Rightarrow>
      conflict_option_rel \<Rightarrow> nat \<Rightarrow> (nat watcher) list list \<Rightarrow> isa_vmtf_remove_int \<Rightarrow>
      nat \<Rightarrow> conflict_min_cach_l \<Rightarrow> lbd \<Rightarrow> out_learned \<Rightarrow> isasat_stats \<Rightarrow> isasat_restart_heuristics \<Rightarrow> 
    isasat_aivdom \<Rightarrow> clss_size \<Rightarrow> opts \<Rightarrow> arena \<Rightarrow> occurences_ref \<Rightarrow> 'e nres\<close> and
    P :: \<open>'a \<Rightarrow> trail_pol \<Rightarrow> arena \<Rightarrow>
      conflict_option_rel \<Rightarrow> nat \<Rightarrow> (nat watcher) list list \<Rightarrow> isa_vmtf_remove_int \<Rightarrow>
      nat \<Rightarrow> conflict_min_cach_l \<Rightarrow> lbd \<Rightarrow> out_learned \<Rightarrow> isasat_stats \<Rightarrow> isasat_restart_heuristics \<Rightarrow> 
    isasat_aivdom \<Rightarrow> clss_size \<Rightarrow> opts \<Rightarrow> arena \<Rightarrow> occurences_ref \<Rightarrow> bool\<close> 
begin
definition mop where
  \<open>mop S C = do {
  ASSERT (P C (get_trail_wl_heur S) 
  (get_clauses_wl_heur S)
  (get_conflict_wl_heur S)
  (literals_to_update_wl_heur S)
  (get_watched_wl_heur S)
  (get_vmtf_heur S)
  (get_count_max_lvls_heur S)
  (get_conflict_cach S)
  (get_lbd S)
  (get_outlearned_heur S)
  (get_stats_heur S)
  (get_heur S)
  (get_aivdom S)
  (get_learned_count S)
  (get_opts S)
  (get_old_arena S)
  (get_occs S));
   read_all_st (f' C) S
  }\<close>
 end

locale read_all_param_adder = read_all_param_adder_ops f' P
  for f' :: \<open>'a \<Rightarrow> trail_pol \<Rightarrow> arena \<Rightarrow>
      conflict_option_rel \<Rightarrow> nat \<Rightarrow> (nat watcher) list list \<Rightarrow> isa_vmtf_remove_int \<Rightarrow>
      nat \<Rightarrow> conflict_min_cach_l \<Rightarrow> lbd \<Rightarrow> out_learned \<Rightarrow> isasat_stats \<Rightarrow> isasat_restart_heuristics \<Rightarrow> 
    isasat_aivdom \<Rightarrow> clss_size \<Rightarrow> opts \<Rightarrow> arena \<Rightarrow> occurences_ref \<Rightarrow> 'r nres\<close> and
    P :: \<open>'a \<Rightarrow> trail_pol \<Rightarrow> arena \<Rightarrow>
      conflict_option_rel \<Rightarrow> nat \<Rightarrow> (nat watcher) list list \<Rightarrow> isa_vmtf_remove_int \<Rightarrow>
      nat \<Rightarrow> conflict_min_cach_l \<Rightarrow> lbd \<Rightarrow> out_learned \<Rightarrow> isasat_stats \<Rightarrow> isasat_restart_heuristics \<Rightarrow> 
    isasat_aivdom \<Rightarrow> clss_size \<Rightarrow> opts \<Rightarrow> arena \<Rightarrow> occurences_ref \<Rightarrow> bool\<close>  +
  fixes R and f and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close>
  assumes not_deleted_code_refine:
    \<open>(uncurry17 (\<lambda>a b c d e kf g h i j k l m n ko p q C. f C a b c d e kf g h i j k l m n ko p q),
    uncurry17 (\<lambda>a b c d e kf g h i j k l m n ko p q C. f' C a b c d e kf g h i j k l m n ko p q))
    \<in> [uncurry17  (\<lambda>a b c d e kf g h i j k l m n ko p q C. P C a b c d e kf g h i j k l m n ko p q)]\<^sub>a
    trail_pol_fast_assn\<^sup>k *\<^sub>a
    arena_fast_assn\<^sup>k *\<^sub>a
  conflict_option_rel_assn\<^sup>k *\<^sub>a
  sint64_nat_assn\<^sup>k *\<^sub>a
  watchlist_fast_assn\<^sup>k *\<^sub>a
  vmtf_remove_assn\<^sup>k *\<^sub>a
  uint32_nat_assn\<^sup>k *\<^sub>a
  cach_refinement_l_assn\<^sup>k *\<^sub>a
  lbd_assn\<^sup>k *\<^sub>a
  out_learned_assn\<^sup>k *\<^sub>a
  isasat_stats_assn\<^sup>k *\<^sub>a
  heuristic_assn\<^sup>k *\<^sub>a
  aivdom_assn\<^sup>k *\<^sub>a
  lcount_assn\<^sup>k *\<^sub>a
  opts_assn\<^sup>k *\<^sub>a
  arena_fast_assn\<^sup>k *\<^sub>a occs_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
begin

context
begin
lemma not_deleted_code_refine_tmp:
  \<open>\<And>C C'. (C, C') \<in> R \<Longrightarrow> (uncurry16 (f C), uncurry16 (f' C')) \<in> [uncurry16 (P C')]\<^sub>a
    trail_pol_fast_assn\<^sup>k *\<^sub>a
    arena_fast_assn\<^sup>k *\<^sub>a
  conflict_option_rel_assn\<^sup>k *\<^sub>a
  sint64_nat_assn\<^sup>k *\<^sub>a
  watchlist_fast_assn\<^sup>k *\<^sub>a
  vmtf_remove_assn\<^sup>k *\<^sub>a
  uint32_nat_assn\<^sup>k *\<^sub>a
  cach_refinement_l_assn\<^sup>k *\<^sub>a
  lbd_assn\<^sup>k *\<^sub>a
  out_learned_assn\<^sup>k *\<^sub>a
  isasat_stats_assn\<^sup>k *\<^sub>a
  heuristic_assn\<^sup>k *\<^sub>a
  aivdom_assn\<^sup>k *\<^sub>a
  lcount_assn\<^sup>k *\<^sub>a
  opts_assn\<^sup>k *\<^sub>a
  arena_fast_assn\<^sup>k *\<^sub>a occs_assn\<^sup>k \<rightarrow> x_assn\<close>
  apply (rule remove_pure_parameter2'[where R=R])
  apply (rule hfref_cong[OF not_deleted_code_refine])
  apply (auto simp add: uncurry_def)
  done
end

lemma (in -) case_isasat_int_split_getter: \<open>P (get_trail_wl_heur S) 
  (get_clauses_wl_heur S)
  (get_conflict_wl_heur S)
  (literals_to_update_wl_heur S)
  (get_watched_wl_heur S)
  (get_vmtf_heur S)
  (get_count_max_lvls_heur S)
  (get_conflict_cach S)
  (get_lbd S)
  (get_outlearned_heur S)
  (get_stats_heur S)
  (get_heur S)
  (get_aivdom S)
  (get_learned_count S)
  (get_opts S)
  (get_old_arena S) (get_occs S) = case_isasat_int P S\<close>
  by (auto split: isasat_int_splits)

lemma refine:
  \<open>(uncurry (\<lambda>N C. read_all_st_code (f C) N),
    uncurry (\<lambda>N C'. read_all_st (f' C') N))
  \<in> [uncurry (\<lambda>S C. P C (get_trail_wl_heur S) 
  (get_clauses_wl_heur S)
  (get_conflict_wl_heur S)
  (literals_to_update_wl_heur S)
  (get_watched_wl_heur S)
  (get_vmtf_heur S)
  (get_count_max_lvls_heur S)
  (get_conflict_cach S)
  (get_lbd S)
  (get_outlearned_heur S)
  (get_stats_heur S)
  (get_heur S)
  (get_aivdom S)
  (get_learned_count S)
  (get_opts S)
  (get_old_arena S) (get_occs S))]\<^sub>a isasat_bounded_assn\<^sup>k  *\<^sub>a (pure R)\<^sup>k\<rightarrow> x_assn\<close>
  apply (rule add_pure_parameter2)
  unfolding tuple17.case_distrib case_isasat_int_split_getter
  apply (rule read_all_code_refine)
  apply (rule not_deleted_code_refine_tmp)
  apply assumption
  done

lemma mop_refine:
  \<open>(uncurry (\<lambda>N C. read_all_st_code (f C) N),
    uncurry mop)
  \<in> isasat_bounded_assn\<^sup>k  *\<^sub>a (pure R)\<^sup>k\<rightarrow>\<^sub>a x_assn\<close>
  unfolding mop_def
  apply (rule refine_ASSERT_move_to_pre)
  apply (rule refine)
  done
end
 
locale read_trail_param_adder =
  fixes R and f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(uncurry (\<lambda>S C. f C S), uncurry (\<lambda>S C. f' C S)) \<in> [uncurry (\<lambda>S C. P C S)]\<^sub>a trail_pol_fast_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
begin

lemma not_deleted_code_refine':
  \<open>(uncurry17 (\<lambda>M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C. f C M), uncurry17 (\<lambda>M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C'. f' C' M)) \<in>
  [uncurry17 (\<lambda>M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C'. P C' M)]\<^sub>a
   trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a
  watchlist_fast_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a cach_refinement_l_assn\<^sup>k *\<^sub>a
  lbd_assn\<^sup>k *\<^sub>a out_learned_assn\<^sup>k *\<^sub>a isasat_stats_assn\<^sup>k *\<^sub>a heuristic_assn\<^sup>k *\<^sub>a
  aivdom_assn\<^sup>k *\<^sub>a lcount_assn\<^sup>k *\<^sub>a opts_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a occs_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
  apply (rule add_pure_parameter2)
  apply (drule remove_pure_parameter2'[where f =f and f'=f', OF not_deleted_code_refine])
  apply (drule remove_component_right[where X = arena_fast_assn])
  apply (drule remove_component_right[where X = conflict_option_rel_assn])
  apply (drule remove_component_right[where X = sint64_nat_assn])
  apply (drule remove_component_right[where X = watchlist_fast_assn])
  apply (drule remove_component_right[where X = vmtf_remove_assn])
  apply (drule remove_component_right[where X = uint32_nat_assn])
  apply (drule remove_component_right[where X = cach_refinement_l_assn])
  apply (drule remove_component_right[where X = lbd_assn])
  apply (drule remove_component_right[where X = out_learned_assn])
  apply (drule remove_component_right[where X = isasat_stats_assn])
  apply (drule remove_component_right[where X = heuristic_assn])
  apply (drule remove_component_right[where X = aivdom_assn])
  apply (drule remove_component_right[where X = lcount_assn])
  apply (drule remove_component_right[where X = opts_assn])
  apply (drule remove_component_right[where X = arena_fast_assn])
  apply (drule remove_component_right[where X = occs_assn])
  by (rule hfref_cong, assumption) auto

sublocale XX : read_all_param_adder where
  f = \<open>(\<lambda>C M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. f C M)\<close> and
  f' = \<open>(\<lambda>C M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. f' C M)\<close> and
  P = \<open>(\<lambda>C M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. P C M)\<close>
  by unfold_locales
   (rule not_deleted_code_refine')

lemmas refine = XX.refine
lemmas mop_refine = XX.mop_refine
end



locale read_arena_param_adder_ops =
  fixes P :: \<open>'b \<Rightarrow> arena \<Rightarrow> bool\<close> and f' :: \<open>'b \<Rightarrow> arena_el list \<Rightarrow> 'r nres\<close>
begin
definition mop where
  \<open>mop N C = do {
    ASSERT (P C (get_clauses_wl_heur N));
    read_all_st (\<lambda>_ N _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. f' C N) N   }\<close>

end

locale read_arena_param_adder = read_arena_param_adder_ops P f'
  for P :: \<open>'b \<Rightarrow> arena \<Rightarrow> bool\<close> and f' :: \<open>'b \<Rightarrow> arena_el list \<Rightarrow> 'r nres\<close> +
  fixes R :: \<open>('a \<times> 'b) set\<close> and f and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close>
  assumes not_deleted_code_refine: \<open>(uncurry (\<lambda>S C. f C S), uncurry (\<lambda>S C'. f' C' S)) \<in> [uncurry (\<lambda>S C. P C S)]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
begin

lemma not_deleted_code_refine':
  \<open>(uncurry17 (\<lambda>_ M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C. f C M), uncurry17 (\<lambda>_ M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C'. f' C' M)) \<in>
  [uncurry17 (\<lambda>_ M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C'. P C' M)]\<^sub>a
   trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a
  watchlist_fast_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a cach_refinement_l_assn\<^sup>k *\<^sub>a
  lbd_assn\<^sup>k *\<^sub>a out_learned_assn\<^sup>k *\<^sub>a isasat_stats_assn\<^sup>k *\<^sub>a heuristic_assn\<^sup>k *\<^sub>a
  aivdom_assn\<^sup>k *\<^sub>a lcount_assn\<^sup>k *\<^sub>a opts_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k  *\<^sub>a occs_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
  apply (rule add_pure_parameter2)
  apply (drule remove_pure_parameter2'[where f =f and f'=f', OF not_deleted_code_refine])
  apply (drule remove_component_left[where X = trail_pol_fast_assn])
  apply (drule remove_component_right[where X = conflict_option_rel_assn])
  apply (drule remove_component_right[where X = sint64_nat_assn])
  apply (drule remove_component_right[where X = watchlist_fast_assn])
  apply (drule remove_component_right[where X = vmtf_remove_assn])
  apply (drule remove_component_right[where X = uint32_nat_assn])
  apply (drule remove_component_right[where X = cach_refinement_l_assn])
  apply (drule remove_component_right[where X = lbd_assn])
  apply (drule remove_component_right[where X = out_learned_assn])
  apply (drule remove_component_right[where X = isasat_stats_assn])
  apply (drule remove_component_right[where X = heuristic_assn])
  apply (drule remove_component_right[where X = aivdom_assn])
  apply (drule remove_component_right[where X = lcount_assn])
  apply (drule remove_component_right[where X = opts_assn])
  apply (drule remove_component_right[where X = arena_fast_assn])
  apply (drule remove_component_right[where X = occs_assn])
  by (rule hfref_cong, assumption) auto

sublocale XX: read_all_param_adder where
  f = \<open>(\<lambda>C _ M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. f C M)\<close> and
  f' = \<open>(\<lambda>C _ M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. f' C M)\<close> and
  P = \<open>(\<lambda>C _ M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. P C M)\<close>
  by unfold_locales
   (rule not_deleted_code_refine')
lemmas refine = XX.refine

lemma mop_refine:
  \<open>(uncurry (\<lambda>N C. read_all_st_code (\<lambda>_ M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. f C M) N),
    uncurry mop)
  \<in> isasat_bounded_assn\<^sup>k  *\<^sub>a (pure R)\<^sup>k\<rightarrow>\<^sub>a x_assn\<close>
  unfolding mop_def
  apply (rule refine_ASSERT_move_to_pre)
  apply (rule refine)
  done

end

locale read_arena_param_adder0 =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(f, f') \<in> [P]\<^sub>a arena_fast_assn\<^sup>k \<rightarrow> x_assn\<close>
begin

sublocale XX: read_arena_param_adder where
  f = \<open>\<lambda>_ N. f N\<close> and
  f' = \<open>\<lambda>_ N. f' N\<close> and
  P = \<open>\<lambda>_. P\<close> and
  R = \<open>unit_rel\<close>
  apply unfold_locales
  using not_deleted_code_refine[THEN remove_component_right] .

lemmas refine = XX.refine[THEN remove_unused_unit_parameter]
lemmas mop_refine = XX.mop_refine
end

lemma merge_second_pure_argument_generalized:
  \<open>(uncurry2 f, uncurry2 f')
  \<in> [uncurry2 P]\<^sub>a A *\<^sub>a (pure R)\<^sup>k *\<^sub>a (pure R')\<^sup>k \<rightarrow> x_assn \<Longrightarrow>
  (uncurry (\<lambda>S C. (case C of (C, D) \<Rightarrow> f S C D)),
  uncurry (\<lambda>S C'. (case C' of (C, D) \<Rightarrow> f' S C D)))
    \<in> [uncurry
     (\<lambda>S C. (case C of (C, D) \<Rightarrow> P S C D))]\<^sub>a A *\<^sub>a (pure (R \<times>\<^sub>f R'))\<^sup>k \<rightarrow> x_assn\<close>
  unfolding hfref_def 
  by (auto simp flip: prod_assn_pure_conv)

 lemma merge_second_pure_argument:
  \<open>(uncurry2 (\<lambda>S C D. f C D S), uncurry2 (\<lambda>S C' D'. f' C' D' S))
  \<in> [uncurry2
   (\<lambda>S C' D'.
    P C' D' S)]\<^sub>a A *\<^sub>a (pure R)\<^sup>k *\<^sub>a (pure R')\<^sup>k \<rightarrow> x_assn \<Longrightarrow>
  (uncurry (\<lambda>S C. (case C of (C, D) \<Rightarrow> f C D) S),
  uncurry (\<lambda>S C'. (case C' of (C, D) \<Rightarrow> f' C D) S))
   \<in> [uncurry (\<lambda>S C. (case C of (C, D) \<Rightarrow> P C D) S)]\<^sub>a A *\<^sub>a (pure (R \<times>\<^sub>f R'))\<^sup>k \<rightarrow> x_assn\<close>
  unfolding hfref_def 
  by (auto simp flip: prod_assn_pure_conv)


lemma merge_third_pure_argument':
  \<open>(uncurry3 (\<lambda>S C D E. f C D E S), uncurry3 (\<lambda>S C' D' E'. f' C' D' E' S))
  \<in> [uncurry3
   (\<lambda>S C' D' E'.
    P C' D' E' S)]\<^sub>a A *\<^sub>a (pure R)\<^sup>k *\<^sub>a (pure R')\<^sup>k  *\<^sub>a (pure R'')\<^sup>k \<rightarrow> x_assn \<Longrightarrow>
  (uncurry2 (\<lambda>S E C. (case C of (C, D) \<Rightarrow> f E C D) S),
  uncurry2 (\<lambda>S E' C'. (case C' of (C, D) \<Rightarrow> f' E' C D) S))
    \<in> [uncurry2
     (\<lambda>S E C. (case C of (C, D) \<Rightarrow> P E C D)
  S)]\<^sub>a A *\<^sub>a (pure R)\<^sup>k *\<^sub>a  (pure (R' \<times>\<^sub>f R''))\<^sup>k \<rightarrow> x_assn\<close>
  unfolding hfref_def 
  by (auto simp flip: prod_assn_pure_conv)
 
abbreviation read_arena_wl_heur_code :: \<open>_\<close> where
  \<open>read_arena_wl_heur_code f \<equiv> read_all_st_code  (\<lambda>_ M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. f M)\<close>
abbreviation read_arena_wl_heur :: \<open>_\<close> where
  \<open>read_arena_wl_heur f \<equiv> read_all_st  (\<lambda>_ M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. f M)\<close>

locale read_arena_param_adder2_twoargs_ops =
  fixes
    f' :: \<open>'b \<Rightarrow> 'd \<Rightarrow> arena \<Rightarrow> 'r nres\<close> and
    P :: \<open>'b \<Rightarrow> 'd \<Rightarrow> arena \<Rightarrow> bool\<close>
begin
definition mop where
  \<open>mop N C C' = do {
     ASSERT (P C C' (get_clauses_wl_heur N));
     read_arena_wl_heur (\<lambda>N. f' C C' N) N
  }\<close>
end


locale read_arena_param_adder2_twoargs =
  read_arena_param_adder2_twoargs_ops f' P
  for f' :: \<open>'b \<Rightarrow> 'd \<Rightarrow> arena \<Rightarrow> 'r nres\<close> and P +
  fixes R and R' and f and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close>
  assumes not_deleted_code_refine:
    \<open>(uncurry2 (\<lambda>S C D. f C D S), uncurry2 (\<lambda>S C' D'. f' C' D' S)) \<in>
    [uncurry2 (\<lambda>S C' D'. P C' D' S)]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k *\<^sub>a (pure R')\<^sup>k \<rightarrow> x_assn\<close>
begin

sublocale XX: read_arena_param_adder where
  f = \<open>\<lambda>(C,D) N. f C D N\<close> and
  f' = \<open>\<lambda>(C,D) N. f' C D N\<close> and
  P = \<open>\<lambda>(C,D) N. P C D N\<close> and
  R = \<open>R \<times>\<^sub>f R'\<close>
  apply unfold_locales
  using not_deleted_code_refine[THEN merge_second_pure_argument] .

lemma refine:
  \<open>(uncurry2 (\<lambda>N C D. read_arena_wl_heur_code (f C D) N),
    uncurry2 (\<lambda>N C' D. read_arena_wl_heur (f' C' D) N))
  \<in> [uncurry2 (\<lambda>S C D. P C D (get_clauses_wl_heur S))]\<^sub>a isasat_bounded_assn\<^sup>k  *\<^sub>a (pure R)\<^sup>k *\<^sub>a (pure R')\<^sup>k \<rightarrow> x_assn\<close>
  by (rule XX.refine[THEN split_snd_pure_arg, unfolded prod.case])

lemma mop_refine:
  \<open>(uncurry2 (\<lambda>N C D. read_arena_wl_heur_code (\<lambda>N. f C D N) N), uncurry2 mop) \<in> isasat_bounded_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k *\<^sub>a (pure R')\<^sup>k \<rightarrow>\<^sub>a x_assn\<close>
  unfolding mop_def
  apply (rule refine_ASSERT_move_to_pre2)
  apply (rule refine[unfolded comp_def])
  done

end

abbreviation read_conflict_wl_heur_code :: \<open>_\<close> where
  \<open>read_conflict_wl_heur_code f \<equiv> read_all_st_code  (\<lambda>_ _ M _ _ _ _ _ _ _ _ _ _ _ _ _ _. f M)\<close>
abbreviation read_conflict_wl_heur :: \<open>_\<close> where
  \<open>read_conflict_wl_heur f \<equiv> read_all_st  (\<lambda>_ _ M _ _ _ _ _ _ _ _ _ _ _ _ _ _. f M)\<close>


locale read_conflict_param_adder =
  fixes R and f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(uncurry (\<lambda>S C. f C S), uncurry (\<lambda>S C'. f' C' S)) \<in> [uncurry (\<lambda>S C. P C S)]\<^sub>a conflict_option_rel_assn\<^sup>k  *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
begin

lemma not_deleted_code_refine':
  shows \<open>
  (uncurry17 (\<lambda>_ _ M _ _ _ _ _ _ _ _ _ _ _ _ _ _ C. f C M), uncurry17 (\<lambda>_ _ M _ _ _ _ _ _ _ _ _ _ _ _ _ _ C'. f' C' M)) \<in>
  [uncurry17 (\<lambda>_ _ M _ _ _ _ _ _ _ _ _ _ _ _ _ _ C'. P C' M)]\<^sub>a
   trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a
  watchlist_fast_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a cach_refinement_l_assn\<^sup>k *\<^sub>a
  lbd_assn\<^sup>k *\<^sub>a out_learned_assn\<^sup>k *\<^sub>a isasat_stats_assn\<^sup>k *\<^sub>a heuristic_assn\<^sup>k *\<^sub>a
  aivdom_assn\<^sup>k *\<^sub>a lcount_assn\<^sup>k *\<^sub>a opts_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a occs_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
  apply (rule add_pure_parameter2)
  apply (drule remove_pure_parameter2'[where f =f and f'=f', OF not_deleted_code_refine])
  apply (drule remove_component_left[where X = trail_pol_fast_assn])
  apply (drule remove_component_middle[where X = arena_fast_assn])
  apply (drule remove_component_right[where X = sint64_nat_assn])
  apply (drule remove_component_right[where X = watchlist_fast_assn])
  apply (drule remove_component_right[where X = vmtf_remove_assn])
  apply (drule remove_component_right[where X = uint32_nat_assn])
  apply (drule remove_component_right[where X = cach_refinement_l_assn])
  apply (drule remove_component_right[where X = lbd_assn])
  apply (drule remove_component_right[where X = out_learned_assn])
  apply (drule remove_component_right[where X = isasat_stats_assn])
  apply (drule remove_component_right[where X = heuristic_assn])
  apply (drule remove_component_right[where X = aivdom_assn])
  apply (drule remove_component_right[where X = lcount_assn])
  apply (drule remove_component_right[where X = opts_assn])
  apply (drule remove_component_right[where X = arena_fast_assn])
  apply (drule remove_component_right[where X = occs_assn])
  by (rule hfref_cong, assumption) auto

sublocale XX : read_all_param_adder where
  f = \<open>(\<lambda>C _ _ M _ _ _ _ _ _ _ _ _ _ _ _ _ _. f C M)\<close> and
  f' = \<open>(\<lambda>C _ _ M _ _ _ _ _ _ _ _ _ _ _ _ _ _. f' C M)\<close> and
  P = \<open>(\<lambda>C _ _ M _ _ _ _ _ _ _ _ _ _ _ _ _ _. P C M)\<close>
  by unfold_locales
   (rule not_deleted_code_refine')

lemmas refine = XX.refine
end

locale read_conflict_param_adder0 =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(f, f') \<in> [P]\<^sub>a conflict_option_rel_assn\<^sup>k \<rightarrow> x_assn\<close>
begin
sublocale XX: read_conflict_param_adder where
  f = \<open>\<lambda>_. f\<close> and
  f' = \<open>\<lambda>_. f'\<close> and
  P = \<open>\<lambda>_. P\<close> and
  R = unit_rel
  apply unfold_locales
  using not_deleted_code_refine[THEN remove_component_right] .

lemmas refine = XX.refine[THEN remove_unused_unit_parameter]
end


abbreviation read_literals_to_update_wl_heur_code :: \<open>_\<close> where
  \<open>read_literals_to_update_wl_heur_code f \<equiv> read_all_st_code  (\<lambda>_ _ _ M _ _ _ _ _ _ _ _ _ _ _ _ _. f M)\<close>
abbreviation read_literals_to_update_wl_heur :: \<open>_\<close> where
  \<open>read_literals_to_update_wl_heur f \<equiv> read_all_st  (\<lambda>_ _ _ M _ _ _ _ _ _ _ _ _ _ _ _ _. f M)\<close>

locale read_literals_to_update_param_adder =
  fixes R and f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(uncurry (\<lambda>S C. f C S), uncurry (\<lambda>S C'. f' C' S)) \<in> [uncurry (\<lambda>S C. P C S)]\<^sub>a sint64_nat_assn\<^sup>k  *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
begin

lemma not_deleted_code_refine':
  shows \<open>
  (uncurry17 (\<lambda>_ _ _ M _ _ _ _ _ _ _ _ _ _ _ _ _ C. f C M), uncurry17 (\<lambda>_ _ _ M _ _ _ _ _ _ _ _ _ _ _ _ _ C'. f' C' M)) \<in>
  [uncurry17 (\<lambda>_ _ _ M _ _ _ _ _ _ _ _ _ _ _ _ _ C'. P C' M)]\<^sub>a
   trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a
  watchlist_fast_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a cach_refinement_l_assn\<^sup>k *\<^sub>a
  lbd_assn\<^sup>k *\<^sub>a out_learned_assn\<^sup>k *\<^sub>a isasat_stats_assn\<^sup>k *\<^sub>a heuristic_assn\<^sup>k *\<^sub>a
  aivdom_assn\<^sup>k *\<^sub>a lcount_assn\<^sup>k *\<^sub>a opts_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a occs_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
  apply (rule add_pure_parameter2)
  apply (drule remove_pure_parameter2'[where f =f and f'=f', OF not_deleted_code_refine])
  apply (drule remove_component_left[where X = trail_pol_fast_assn])
  apply (drule remove_component_middle[where X = arena_fast_assn])
  apply (drule remove_component_middle[where X = conflict_option_rel_assn])
  apply (drule remove_component_right[where X = watchlist_fast_assn])
  apply (drule remove_component_right[where X = vmtf_remove_assn])
  apply (drule remove_component_right[where X = uint32_nat_assn])
  apply (drule remove_component_right[where X = cach_refinement_l_assn])
  apply (drule remove_component_right[where X = lbd_assn])
  apply (drule remove_component_right[where X = out_learned_assn])
  apply (drule remove_component_right[where X = isasat_stats_assn])
  apply (drule remove_component_right[where X = heuristic_assn])
  apply (drule remove_component_right[where X = aivdom_assn])
  apply (drule remove_component_right[where X = lcount_assn])
  apply (drule remove_component_right[where X = opts_assn])
  apply (drule remove_component_right[where X = arena_fast_assn])
  apply (drule remove_component_right[where X = occs_assn])
  by (rule hfref_cong, assumption) auto

sublocale XX : read_all_param_adder where
  f = \<open>(\<lambda>C _ _ _ M _ _ _ _ _ _ _ _ _ _ _ _ _. f C M)\<close> and
  f' = \<open>(\<lambda>C _ _ _ M _ _ _ _ _ _ _ _ _ _ _ _ _. f' C M)\<close> and
  P = \<open>(\<lambda>C _ _ _ M _ _ _ _ _ _ _ _ _ _ _ _ _. P C M)\<close>
  by unfold_locales
   (rule not_deleted_code_refine')

lemmas refine = XX.refine
end


locale read_literals_to_update_param_adder0 =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(f, f') \<in> [P]\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> x_assn\<close>
begin
sublocale XX: read_literals_to_update_param_adder where
  f = \<open>\<lambda>_. f\<close> and
  f' = \<open>\<lambda>_. f'\<close> and
  P = \<open>\<lambda>_. P\<close>
  apply unfold_locales
  using not_deleted_code_refine[THEN remove_component_right] .

lemmas refine = XX.refine[THEN remove_unused_unit_parameter]
end

abbreviation read_watchlist_wl_heur_code :: \<open>_\<close> where
  \<open>read_watchlist_wl_heur_code f \<equiv> read_all_st_code  (\<lambda>_ _ _ _ M _ _ _ _ _ _ _ _ _ _ _ _. f M)\<close>
abbreviation read_watchlist_wl_heur :: \<open>_\<close> where
  \<open>read_watchlist_wl_heur f \<equiv> read_all_st  (\<lambda>_ _ _ _ M _ _ _ _ _ _ _ _ _ _ _ _. f M)\<close>


locale read_watchlist_param_adder =
  fixes R and f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine:
    \<open>(uncurry (\<lambda>S C. f C S), uncurry (\<lambda>S C'. f' C' S)) \<in> [uncurry (\<lambda>S C. P C S)]\<^sub>a watchlist_fast_assn\<^sup>k  *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
begin

lemma not_deleted_code_refine':
  shows \<open>
  (uncurry17 (\<lambda>_ _ _ _ M _ _ _ _ _ _ _ _ _ _ _ _ C. f C M), uncurry17 (\<lambda>_ _ _ _ M _ _ _ _ _ _ _ _ _ _ _ _ C'. f' C' M)) \<in>
  [uncurry17 (\<lambda>_ _ _ _ M _ _ _ _ _ _ _ _ _ _ _ _ C'. P C' M)]\<^sub>a
   trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a
  watchlist_fast_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a cach_refinement_l_assn\<^sup>k *\<^sub>a
  lbd_assn\<^sup>k *\<^sub>a out_learned_assn\<^sup>k *\<^sub>a isasat_stats_assn\<^sup>k *\<^sub>a heuristic_assn\<^sup>k *\<^sub>a
  aivdom_assn\<^sup>k *\<^sub>a lcount_assn\<^sup>k *\<^sub>a opts_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k  *\<^sub>a occs_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
  apply (rule add_pure_parameter2)
  apply (drule remove_pure_parameter2'[where f =f and f'=f', OF not_deleted_code_refine])
  apply (drule remove_component_left[where X = trail_pol_fast_assn])
  apply (drule remove_component_middle[where X = arena_fast_assn])
  apply (drule remove_component_middle[where X = conflict_option_rel_assn])
  apply (drule remove_component_middle[where X = sint64_nat_assn])
  apply (drule remove_component_right[where X = vmtf_remove_assn])
  apply (drule remove_component_right[where X = uint32_nat_assn])
  apply (drule remove_component_right[where X = cach_refinement_l_assn])
  apply (drule remove_component_right[where X = lbd_assn])
  apply (drule remove_component_right[where X = out_learned_assn])
  apply (drule remove_component_right[where X = isasat_stats_assn])
  apply (drule remove_component_right[where X = heuristic_assn])
  apply (drule remove_component_right[where X = aivdom_assn])
  apply (drule remove_component_right[where X = lcount_assn])
  apply (drule remove_component_right[where X = opts_assn])
  apply (drule remove_component_right[where X = arena_fast_assn])
  apply (drule remove_component_right[where X = occs_assn])
  by (rule hfref_cong, assumption) auto

sublocale XX : read_all_param_adder where
  f = \<open>(\<lambda>C _ _ _ _ M _ _ _ _ _ _ _ _ _ _ _ _. f C M)\<close> and
  f' = \<open>(\<lambda>C _ _ _ _ M _ _ _ _ _ _ _ _ _ _ _ _. f' C M)\<close> and
  P = \<open>(\<lambda>C _ _ _ _ M _ _ _ _ _ _ _ _ _ _ _ _. P C M)\<close>
  by unfold_locales
   (rule not_deleted_code_refine')

lemmas refine = XX.refine
lemmas mop_refine = XX.mop_refine
end


locale read_watchlist_param_adder0 =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(f, f') \<in> [P]\<^sub>a watchlist_fast_assn\<^sup>k \<rightarrow> x_assn\<close>
begin

sublocale XX: read_watchlist_param_adder where
  f = \<open>\<lambda>_. f\<close> and
  f' = \<open>\<lambda>_. f'\<close> and
  P = \<open>\<lambda>_. P\<close>
  apply unfold_locales
  using not_deleted_code_refine[THEN remove_component_right] .

lemmas refine = XX.refine[THEN remove_unused_unit_parameter]

end


locale read_watchlist_param_adder_twoargs =
  fixes R and R' and f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine:
    \<open>(uncurry2 (\<lambda>S C D. f C D S), uncurry2 (\<lambda>S C' D'. f' C' D' S)) \<in>
    [uncurry2 (\<lambda>S C' D'. P C' D' S)]\<^sub>a watchlist_fast_assn\<^sup>k  *\<^sub>a (pure R)\<^sup>k *\<^sub>a (pure R')\<^sup>k \<rightarrow> x_assn\<close>
begin

sublocale XX: read_watchlist_param_adder where
  f = \<open>\<lambda>(C,D). f C D\<close> and
  f' = \<open>\<lambda>(C,D). f' C D\<close> and
  P = \<open>\<lambda>(C,D). P C D\<close> and
  R = \<open>R \<times>\<^sub>f R'\<close>
  apply unfold_locales
  using not_deleted_code_refine[THEN merge_second_pure_argument] .


lemma refine:
  \<open>(uncurry2 (\<lambda>N C D. read_watchlist_wl_heur_code (f C D) N),
    uncurry2 (\<lambda>N C' D'. read_watchlist_wl_heur (f' C' D') N))
  \<in> [uncurry2 (\<lambda>S C D. P C D (get_watched_wl_heur S))]\<^sub>a
    isasat_bounded_assn\<^sup>k  *\<^sub>a (pure R)\<^sup>k  *\<^sub>a (pure R')\<^sup>k\<rightarrow> x_assn\<close>
  by (rule XX.refine[THEN split_snd_pure_arg, unfolded prod.case])

lemmas mop_refine = XX.XX.mop_refine
end



abbreviation read_vmtf_wl_heur_code :: \<open>_\<close> where
  \<open>read_vmtf_wl_heur_code f \<equiv> read_all_st_code  (\<lambda>_ _ _ _ _ M _ _ _ _ _ _ _ _ _ _ _. f M)\<close>
abbreviation read_vmtf_wl_heur :: \<open>_\<close> where
  \<open>read_vmtf_wl_heur f \<equiv> read_all_st  (\<lambda>_ _ _ _ _ M _ _ _ _ _ _ _ _ _ _ _. f M)\<close>

locale read_vmtf_param_adder =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P and R
  assumes not_deleted_code_refine: \<open>(uncurry (\<lambda>S C. f C S), uncurry (\<lambda>S C'. f' C' S)) \<in> [uncurry (\<lambda>S C. P C S)]\<^sub>a vmtf_remove_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
begin

lemma not_deleted_code_refine':
  shows \<open>
  (uncurry17 (\<lambda>_ _ _ _ _ M _ _ _ _ _ _ _ _ _ _ _ C. f C M), uncurry17 (\<lambda>_ _ _ _ _ M _ _ _ _ _ _ _ _ _ _ _ C'. f' C' M)) \<in>
  [uncurry17 (\<lambda>_ _ _ _ _ M _ _ _ _ _ _ _ _ _ _ _ C'. P C' M)]\<^sub>a
   trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a
  watchlist_fast_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a cach_refinement_l_assn\<^sup>k *\<^sub>a
  lbd_assn\<^sup>k *\<^sub>a out_learned_assn\<^sup>k *\<^sub>a isasat_stats_assn\<^sup>k *\<^sub>a heuristic_assn\<^sup>k *\<^sub>a
  aivdom_assn\<^sup>k *\<^sub>a lcount_assn\<^sup>k *\<^sub>a opts_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k  *\<^sub>a occs_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k  \<rightarrow> x_assn\<close>
  apply (rule add_pure_parameter2)
  apply (drule remove_pure_parameter2'[where f =f and f'=f', OF not_deleted_code_refine])
  apply (drule remove_component_left[where X = trail_pol_fast_assn])
  apply (drule remove_component_middle[where X = arena_fast_assn])
  apply (drule remove_component_middle[where X = conflict_option_rel_assn])
  apply (drule remove_component_middle[where X = sint64_nat_assn])
  apply (drule remove_component_middle[where X = watchlist_fast_assn])
  apply (drule remove_component_right[where X = uint32_nat_assn])
  apply (drule remove_component_right[where X = cach_refinement_l_assn])
  apply (drule remove_component_right[where X = lbd_assn])
  apply (drule remove_component_right[where X = out_learned_assn])
  apply (drule remove_component_right[where X = isasat_stats_assn])
  apply (drule remove_component_right[where X = heuristic_assn])
  apply (drule remove_component_right[where X = aivdom_assn])
  apply (drule remove_component_right[where X = lcount_assn])
  apply (drule remove_component_right[where X = opts_assn])
  apply (drule remove_component_right[where X = arena_fast_assn])
  apply (drule remove_component_right[where X = occs_assn])
  by (rule hfref_cong, assumption) auto

sublocale XX : read_all_param_adder where
  f = \<open>(\<lambda>C _ _ _ _ _ M _ _ _ _ _ _ _ _ _ _ _. f C M)\<close> and
  f' = \<open>(\<lambda>C _ _ _ _ _ M _ _ _ _ _ _ _ _ _ _ _. f' C M)\<close> and
  P = \<open>(\<lambda>C _ _ _ _ _ M _ _ _ _ _ _ _ _ _ _ _. P C M)\<close>
  by unfold_locales
   (rule not_deleted_code_refine')

lemmas refine = XX.refine
end


locale read_vmtf_param_adder0 =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(f, f') \<in> [P]\<^sub>a vmtf_remove_assn\<^sup>k \<rightarrow> x_assn\<close>
begin

sublocale XX: read_vmtf_param_adder where
  f = \<open>\<lambda>_. f\<close> and
  f' = \<open>\<lambda>_. f'\<close> and
  P = \<open>\<lambda>_. P\<close>
  apply unfold_locales
  using not_deleted_code_refine[THEN remove_component_right] .

lemmas refine = XX.refine[THEN remove_unused_unit_parameter]

end



abbreviation read_ccount_wl_heur_code :: \<open>_ \<Rightarrow> twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>read_ccount_wl_heur_code f \<equiv> read_all_st_code  (\<lambda>_ _ _ _ _ _ M _ _ _ _ _ _ _ _ _ _. f M)\<close>
abbreviation read_ccount_wl_heur :: \<open>_ \<Rightarrow> isasat \<Rightarrow> _\<close> where
  \<open>read_ccount_wl_heur f \<equiv> read_all_st  (\<lambda>_ _ _ _ _ _ M _ _ _ _ _ _ _ _ _ _. f M)\<close>

locale read_ccount_param_adder =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P and R
  assumes not_deleted_code_refine: \<open>(uncurry (\<lambda>S C. f C S), uncurry (\<lambda>S C'. f' C' S)) \<in> [uncurry (\<lambda>S C. P C S)]\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
begin

lemma not_deleted_code_refine':
  shows \<open>
  (uncurry17 (\<lambda>_ _ _ _ _ _ M _ _ _ _ _ _ _ _ _ _ C. f C M), uncurry17 (\<lambda>_ _ _ _ _ _ M _ _ _ _ _ _ _ _ _ _ C'. f' C' M)) \<in>
  [uncurry17 (\<lambda>_ _ _ _ _ _ M _ _ _ _ _ _ _ _ _ _ C'. P C' M)]\<^sub>a
   trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a
  watchlist_fast_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a cach_refinement_l_assn\<^sup>k *\<^sub>a
  lbd_assn\<^sup>k *\<^sub>a out_learned_assn\<^sup>k *\<^sub>a isasat_stats_assn\<^sup>k *\<^sub>a heuristic_assn\<^sup>k *\<^sub>a
  aivdom_assn\<^sup>k *\<^sub>a lcount_assn\<^sup>k *\<^sub>a opts_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k  *\<^sub>a occs_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k  \<rightarrow> x_assn\<close>
  apply (rule add_pure_parameter2)
  apply (drule remove_pure_parameter2'[where f =f and f'=f', OF not_deleted_code_refine])
  apply (drule remove_component_left[where X = trail_pol_fast_assn])
  apply (drule remove_component_middle[where X = arena_fast_assn])
  apply (drule remove_component_middle[where X = conflict_option_rel_assn])
  apply (drule remove_component_middle[where X = sint64_nat_assn])
  apply (drule remove_component_middle[where X = watchlist_fast_assn])
  apply (drule remove_component_middle[where X = vmtf_remove_assn])
  apply (drule remove_component_right[where X = cach_refinement_l_assn])
  apply (drule remove_component_right[where X = lbd_assn])
  apply (drule remove_component_right[where X = out_learned_assn])
  apply (drule remove_component_right[where X = isasat_stats_assn])
  apply (drule remove_component_right[where X = heuristic_assn])
  apply (drule remove_component_right[where X = aivdom_assn])
  apply (drule remove_component_right[where X = lcount_assn])
  apply (drule remove_component_right[where X = opts_assn])
  apply (drule remove_component_right[where X = arena_fast_assn])
  apply (drule remove_component_right[where X = occs_assn])
  by (rule hfref_cong, assumption)
    (auto intro!: ext)

sublocale XX : read_all_param_adder where
  f =  \<open>(\<lambda>C _ _ _ _ _ _ M _ _ _ _ _ _ _ _ _ _. f C M)\<close> and
  f' = \<open>(\<lambda>C _ _ _ _ _ _ M _ _ _ _ _ _ _ _ _ _. f' C M)\<close> and
  P =  \<open>(\<lambda>C _ _ _ _ _ _ M _ _ _ _ _ _ _ _ _ _. P C M)\<close>
  by unfold_locales
   (rule not_deleted_code_refine')

lemmas refine = XX.refine
end

locale read_ccount_param_adder0 =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(f, f') \<in> [P]\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> x_assn\<close>
begin

sublocale XX: read_ccount_param_adder where
  f = \<open>\<lambda>_. f\<close> and
  f' = \<open>\<lambda>_. f'\<close> and
  P = \<open>\<lambda>_. P\<close>
  apply unfold_locales
  using not_deleted_code_refine[THEN remove_component_right] .

lemmas refine = XX.refine[THEN remove_unused_unit_parameter]
end


abbreviation read_ccach_wl_heur_code :: \<open>_ \<Rightarrow> twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>read_ccach_wl_heur_code f \<equiv> read_all_st_code  (\<lambda>_ _ _ _ _ _ _ M _ _ _ _ _ _ _ _ _. f M)\<close>
abbreviation read_ccach_wl_heur :: \<open>_ \<Rightarrow> isasat \<Rightarrow> _\<close> where
  \<open>read_ccach_wl_heur f \<equiv> read_all_st  (\<lambda>_ _ _ _ _ _ _ M _ _ _ _ _ _ _ _ _. f M)\<close>

locale read_ccach_param_adder =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P and R
  assumes not_deleted_code_refine: \<open>(uncurry (\<lambda>S C. f C S), uncurry (\<lambda>S C'. f' C' S)) \<in> [uncurry (\<lambda>S C. P C S)]\<^sub>a cach_refinement_l_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
begin

lemma not_deleted_code_refine':
  shows \<open>
  (uncurry17 (\<lambda>_ _ _ _ _ _ _ M _ _ _ _ _ _ _ _ _ C. f C M), uncurry17 (\<lambda>_ _ _ _ _ _ _ M _ _ _ _ _ _ _ _ _ C'. f' C' M)) \<in>
  [uncurry17 (\<lambda>_ _ _ _ _ _ _ M _ _ _ _ _ _ _ _ _ C'. P C' M)]\<^sub>a
   trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a
  watchlist_fast_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a cach_refinement_l_assn\<^sup>k *\<^sub>a
  lbd_assn\<^sup>k *\<^sub>a out_learned_assn\<^sup>k *\<^sub>a isasat_stats_assn\<^sup>k *\<^sub>a heuristic_assn\<^sup>k *\<^sub>a
  aivdom_assn\<^sup>k *\<^sub>a lcount_assn\<^sup>k *\<^sub>a opts_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k  *\<^sub>a occs_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
  apply (rule add_pure_parameter2)
  apply (drule remove_pure_parameter2'[where f =f and f'=f', OF not_deleted_code_refine])
  apply (drule remove_component_left[where X = trail_pol_fast_assn])
  apply (drule remove_component_middle[where X = arena_fast_assn])
  apply (drule remove_component_middle[where X = conflict_option_rel_assn])
  apply (drule remove_component_middle[where X = sint64_nat_assn])
  apply (drule remove_component_middle[where X = watchlist_fast_assn])
  apply (drule remove_component_middle[where X = vmtf_remove_assn])
  apply (drule remove_component_middle[where X = uint32_nat_assn])
  apply (drule remove_component_right[where X = lbd_assn])
  apply (drule remove_component_right[where X = out_learned_assn])
  apply (drule remove_component_right[where X = isasat_stats_assn])
  apply (drule remove_component_right[where X = heuristic_assn])
  apply (drule remove_component_right[where X = aivdom_assn])
  apply (drule remove_component_right[where X = lcount_assn])
  apply (drule remove_component_right[where X = opts_assn])
  apply (drule remove_component_right[where X = arena_fast_assn])
  apply (drule remove_component_right[where X = occs_assn])
  by (rule hfref_cong, assumption) auto

sublocale XX : read_all_param_adder where
  f =  \<open>(\<lambda>C _ _ _ _ _ _ _ M _ _ _ _ _ _ _ _ _. f C M)\<close> and
  f' = \<open>(\<lambda>C _ _ _ _ _ _ _ M _ _ _ _ _ _ _ _ _. f' C M)\<close> and
  P =  \<open>(\<lambda>C _ _ _ _ _ _ _ M _ _ _ _ _ _ _ _ _. P C M)\<close>
  by unfold_locales
   (rule not_deleted_code_refine')

lemmas refine = XX.refine
end


abbreviation read_lbd_wl_heur_code :: \<open>_ \<Rightarrow> twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>read_lbd_wl_heur_code f \<equiv> read_all_st_code  (\<lambda>_ _ _ _ _ _ _ _ M _ _ _ _ _ _ _ _. f M)\<close>
abbreviation read_lbd_wl_heur :: \<open>_ \<Rightarrow> isasat \<Rightarrow> _\<close> where
  \<open>read_lbd_wl_heur f \<equiv> read_all_st  (\<lambda>_ _ _ _ _ _ _ _ M _ _ _ _ _ _ _ _. f M)\<close>

locale read_lbd_param_adder =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P and R
  assumes not_deleted_code_refine: \<open>(uncurry (\<lambda>S C. f C S), uncurry (\<lambda>S C'. f' C' S)) \<in> [uncurry (\<lambda>S C. P C S)]\<^sub>a lbd_assn\<^sup>k  *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
begin

lemma not_deleted_code_refine':
  shows \<open>
  (uncurry17 (\<lambda>_ _ _ _ _ _ _ _ M _ _ _ _ _ _ _ _ C. f C M), uncurry17 (\<lambda>_ _ _ _ _ _ _ _ M _ _ _ _ _ _ _ _ C'. f' C' M)) \<in>
  [uncurry17 (\<lambda>_ _ _ _ _ _ _ _ M _ _ _ _ _ _ _ _ C'. P C' M)]\<^sub>a
   trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a
  watchlist_fast_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a cach_refinement_l_assn\<^sup>k *\<^sub>a
  lbd_assn\<^sup>k *\<^sub>a out_learned_assn\<^sup>k *\<^sub>a isasat_stats_assn\<^sup>k *\<^sub>a heuristic_assn\<^sup>k *\<^sub>a
  aivdom_assn\<^sup>k *\<^sub>a lcount_assn\<^sup>k *\<^sub>a opts_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a occs_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
  apply (rule add_pure_parameter2)
  apply (drule remove_pure_parameter2'[where f =f and f'=f', OF not_deleted_code_refine])
  apply (drule remove_component_left[where X = trail_pol_fast_assn])
  apply (drule remove_component_middle[where X = arena_fast_assn])
  apply (drule remove_component_middle[where X = conflict_option_rel_assn])
  apply (drule remove_component_middle[where X = sint64_nat_assn])
  apply (drule remove_component_middle[where X = watchlist_fast_assn])
  apply (drule remove_component_middle[where X = vmtf_remove_assn])
  apply (drule remove_component_middle[where X = uint32_nat_assn])
  apply (drule remove_component_middle[where X = cach_refinement_l_assn])
  apply (drule remove_component_right[where X = out_learned_assn])
  apply (drule remove_component_right[where X = isasat_stats_assn])
  apply (drule remove_component_right[where X = heuristic_assn])
  apply (drule remove_component_right[where X = aivdom_assn])
  apply (drule remove_component_right[where X = lcount_assn])
  apply (drule remove_component_right[where X = opts_assn])
  apply (drule remove_component_right[where X = arena_fast_assn])
  apply (drule remove_component_right[where X = occs_assn])
  by (rule hfref_cong, assumption) auto

sublocale XX : read_all_param_adder where
  f =  \<open>(\<lambda>C _ _ _ _ _ _ _ _ M _ _ _ _ _ _ _ _. f C M)\<close> and
  f' = \<open>(\<lambda>C _ _ _ _ _ _ _ _ M _ _ _ _ _ _ _ _. f' C M)\<close> and
  P =  \<open>(\<lambda>C _ _ _ _ _ _ _ _ M _ _ _ _ _ _ _ _. P C M)\<close>
  by unfold_locales
   (rule not_deleted_code_refine')

lemmas refine = XX.refine
end

locale read_lbd_param_adder0 =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(f, f') \<in> [P]\<^sub>a lbd_assn\<^sup>k \<rightarrow> x_assn\<close>
begin
sublocale XX: read_lbd_param_adder where
  f = \<open>\<lambda>_. f\<close> and
  f' = \<open>\<lambda>_. f'\<close> and
  P = \<open>\<lambda>_. P\<close>
  apply unfold_locales
  using not_deleted_code_refine[THEN remove_component_right] .

lemmas refine = XX.refine[THEN remove_unused_unit_parameter]
end

abbreviation read_outl_wl_heur_code :: \<open>_ \<Rightarrow> twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>read_outl_wl_heur_code f \<equiv> read_all_st_code  (\<lambda>_ _ _ _ _ _ _ _ _ M _ _ _ _ _ _ _. f M)\<close>
abbreviation read_outl_wl_heur :: \<open>_ \<Rightarrow> isasat \<Rightarrow> _\<close> where
  \<open>read_outl_wl_heur f \<equiv> read_all_st  (\<lambda>_ _ _ _ _ _ _ _ _ M _ _ _ _ _ _ _. f M)\<close>

locale read_outl_param_adder =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P and R
  assumes not_deleted_code_refine: \<open>(uncurry (\<lambda>S C. f C S), uncurry (\<lambda>S C'. f' C' S)) \<in> [uncurry (\<lambda>S C. P C S)]\<^sub>a out_learned_assn\<^sup>k  *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
begin

lemma not_deleted_code_refine':
  shows \<open>
  (uncurry17 (\<lambda>_ _ _ _ _ _ _ _ _ M _ _ _ _ _ _ _ C. f C M), uncurry17 (\<lambda>_ _ _ _ _ _ _ _ _ M _ _ _ _ _ _ _ C'. f' C' M)) \<in>
  [uncurry17 (\<lambda>_ _ _ _ _ _ _ _ _ M _ _ _ _ _ _ _ C'. P C' M)]\<^sub>a
   trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a
  watchlist_fast_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a cach_refinement_l_assn\<^sup>k *\<^sub>a
  lbd_assn\<^sup>k *\<^sub>a out_learned_assn\<^sup>k *\<^sub>a isasat_stats_assn\<^sup>k *\<^sub>a heuristic_assn\<^sup>k *\<^sub>a
  aivdom_assn\<^sup>k *\<^sub>a lcount_assn\<^sup>k *\<^sub>a opts_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a occs_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
  apply (rule add_pure_parameter2)
  apply (drule remove_pure_parameter2'[where f =f and f'=f', OF not_deleted_code_refine])
  apply (drule remove_component_left[where X = trail_pol_fast_assn])
  apply (drule remove_component_middle[where X = arena_fast_assn])
  apply (drule remove_component_middle[where X = conflict_option_rel_assn])
  apply (drule remove_component_middle[where X = sint64_nat_assn])
  apply (drule remove_component_middle[where X = watchlist_fast_assn])
  apply (drule remove_component_middle[where X = vmtf_remove_assn])
  apply (drule remove_component_middle[where X = uint32_nat_assn])
  apply (drule remove_component_middle[where X = cach_refinement_l_assn])
  apply (drule remove_component_middle[where X = lbd_assn])
  apply (drule remove_component_right[where X = isasat_stats_assn])
  apply (drule remove_component_right[where X = heuristic_assn])
  apply (drule remove_component_right[where X = aivdom_assn])
  apply (drule remove_component_right[where X = lcount_assn])
  apply (drule remove_component_right[where X = opts_assn])
  apply (drule remove_component_right[where X = arena_fast_assn])
  apply (drule remove_component_right[where X = occs_assn])
  by (rule hfref_cong, assumption) auto

sublocale XX : read_all_param_adder where
  f =  \<open>(\<lambda>C _ _ _ _ _ _ _ _ _ M _ _ _ _ _ _ _. f C M)\<close> and
  f' = \<open>(\<lambda>C _ _ _ _ _ _ _ _ _ M _ _ _ _ _ _ _. f' C M)\<close> and
  P =  \<open>(\<lambda>C _ _ _ _ _ _ _ _ _ M _ _ _ _ _ _ _. P C M)\<close>
  by unfold_locales
   (rule not_deleted_code_refine')

lemmas refine = XX.refine

end

locale read_outl_param_adder0 =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(f, f') \<in> [P]\<^sub>a out_learned_assn\<^sup>k \<rightarrow> x_assn\<close>
begin

sublocale XX: read_outl_param_adder where
  f = \<open>\<lambda>_. f\<close> and
  f' = \<open>\<lambda>_. f'\<close> and
  P = \<open>\<lambda>_. P\<close>
  apply unfold_locales
  using not_deleted_code_refine[THEN remove_component_right] .

lemmas refine = XX.refine[THEN remove_unused_unit_parameter]
end


abbreviation read_stats_wl_heur_code :: \<open>_ \<Rightarrow> twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>read_stats_wl_heur_code f \<equiv> read_all_st_code  (\<lambda>_ _ _ _ _ _ _ _ _ _ M _ _ _ _ _ _. f M)\<close>
abbreviation read_stats_wl_heur :: \<open>_ \<Rightarrow> isasat \<Rightarrow> _\<close> where
  \<open>read_stats_wl_heur f \<equiv> read_all_st  (\<lambda>_ _ _ _ _ _ _ _ _ _ M _ _ _ _ _ _. f M)\<close>

locale read_stats_param_adder =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(uncurry (\<lambda>S C. f C S), uncurry (\<lambda>S C'. f' C' S)) \<in> [uncurry (\<lambda>S C. P C S)]\<^sub>a isasat_stats_assn\<^sup>k  *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
begin

lemma not_deleted_code_refine':
  shows \<open>
  (uncurry17 (\<lambda>_ _ _ _ _ _ _ _ _ _ M _ _ _ _ _ _ C. f C M), uncurry17 (\<lambda>_ _ _ _ _ _ _ _ _ _ M _ _ _ _ _ _ C'. f' C' M)) \<in>
  [uncurry17 (\<lambda>_ _ _ _ _ _ _ _ _ _ M _ _ _ _ _ _ C'. P C' M)]\<^sub>a
   trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a
  watchlist_fast_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a cach_refinement_l_assn\<^sup>k *\<^sub>a
  lbd_assn\<^sup>k *\<^sub>a out_learned_assn\<^sup>k *\<^sub>a isasat_stats_assn\<^sup>k *\<^sub>a heuristic_assn\<^sup>k *\<^sub>a
  aivdom_assn\<^sup>k *\<^sub>a lcount_assn\<^sup>k *\<^sub>a opts_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a occs_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
  apply (rule add_pure_parameter2)
  apply (drule remove_pure_parameter2'[where f =f and f'=f', OF not_deleted_code_refine])
  apply (drule remove_component_left[where X = trail_pol_fast_assn])
  apply (drule remove_component_middle[where X = arena_fast_assn])
  apply (drule remove_component_middle[where X = conflict_option_rel_assn])
  apply (drule remove_component_middle[where X = sint64_nat_assn])
  apply (drule remove_component_middle[where X = watchlist_fast_assn])
  apply (drule remove_component_middle[where X = vmtf_remove_assn])
  apply (drule remove_component_middle[where X = uint32_nat_assn])
  apply (drule remove_component_middle[where X = cach_refinement_l_assn])
  apply (drule remove_component_middle[where X = lbd_assn])
  apply (drule remove_component_middle[where X = out_learned_assn])
  apply (drule remove_component_right[where X = heuristic_assn])
  apply (drule remove_component_right[where X = aivdom_assn])
  apply (drule remove_component_right[where X = lcount_assn])
  apply (drule remove_component_right[where X = opts_assn])
  apply (drule remove_component_right[where X = arena_fast_assn])
  apply (drule remove_component_right[where X = occs_assn])
  by (rule hfref_cong, assumption) auto

sublocale XX : read_all_param_adder where
  f =  \<open>(\<lambda>C _ _ _ _ _ _ _ _ _ _ M _ _ _ _ _ _. f C M)\<close> and
  f' = \<open>(\<lambda>C _ _ _ _ _ _ _ _ _ _ M _ _ _ _ _ _. f' C M)\<close> and
  P =  \<open>(\<lambda>C _ _ _ _ _ _ _ _ _ _ M _ _ _ _ _ _. P C M)\<close>
  by unfold_locales
   (rule not_deleted_code_refine')

lemmas refine = XX.refine
end

locale read_stats_param_adder0 =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(f, f') \<in> [P]\<^sub>a isasat_stats_assn\<^sup>k \<rightarrow> x_assn\<close>
begin
sublocale XX: read_stats_param_adder where
  f = \<open>\<lambda>_. f\<close> and
  f' = \<open>\<lambda>_. f'\<close> and
  P = \<open>\<lambda>_. P\<close>
  apply unfold_locales
  using not_deleted_code_refine[THEN remove_component_right] .

lemmas refine = XX.refine[THEN remove_unused_unit_parameter]
end


abbreviation read_heur_wl_heur_code :: \<open>_ \<Rightarrow> twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>read_heur_wl_heur_code f \<equiv> read_all_st_code  (\<lambda>_ _ _ _ _ _ _ _ _ _ _ M _ _ _ _ _. f M)\<close>
abbreviation read_heur_wl_heur :: \<open>_ \<Rightarrow> isasat \<Rightarrow> _\<close> where
  \<open>read_heur_wl_heur f \<equiv> read_all_st  (\<lambda>_ _ _ _ _ _ _ _ _ _ _ M _ _ _ _ _. f M)\<close>

locale read_heur_param_adder =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P and R
  assumes not_deleted_code_refine: \<open>(uncurry (\<lambda>S C. f C S), uncurry (\<lambda>S C'. f' C' S)) \<in> [uncurry (\<lambda>S C. P C S)]\<^sub>a heuristic_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
begin

lemma not_deleted_code_refine':
  shows \<open>
  (uncurry17 (\<lambda>_ _ _ _ _ _ _ _ _ _ _ M _ _ _ _ _ C. f C M), uncurry17 (\<lambda>_ _ _ _ _ _ _ _ _ _ _ M _ _ _ _ _ C'. f' C' M)) \<in>
  [uncurry17 (\<lambda>_ _ _ _ _ _ _ _ _ _ _ M _ _ _ _ _ C'. P C' M)]\<^sub>a
   trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a
  watchlist_fast_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a cach_refinement_l_assn\<^sup>k *\<^sub>a
  lbd_assn\<^sup>k *\<^sub>a out_learned_assn\<^sup>k *\<^sub>a isasat_stats_assn\<^sup>k *\<^sub>a heuristic_assn\<^sup>k *\<^sub>a
  aivdom_assn\<^sup>k *\<^sub>a lcount_assn\<^sup>k *\<^sub>a opts_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a occs_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
  apply (rule add_pure_parameter2)
  apply (drule remove_pure_parameter2'[where f =f and f'=f', OF not_deleted_code_refine])
  apply (drule remove_component_left[where X = trail_pol_fast_assn])
  apply (drule remove_component_middle[where X = arena_fast_assn])
  apply (drule remove_component_middle[where X = conflict_option_rel_assn])
  apply (drule remove_component_middle[where X = sint64_nat_assn])
  apply (drule remove_component_middle[where X = watchlist_fast_assn])
  apply (drule remove_component_middle[where X = vmtf_remove_assn])
  apply (drule remove_component_middle[where X = uint32_nat_assn])
  apply (drule remove_component_middle[where X = cach_refinement_l_assn])
  apply (drule remove_component_middle[where X = lbd_assn])
  apply (drule remove_component_middle[where X = out_learned_assn])
  apply (drule remove_component_middle[where X = isasat_stats_assn])
  apply (drule remove_component_right[where X = aivdom_assn])
  apply (drule remove_component_right[where X = lcount_assn])
  apply (drule remove_component_right[where X = opts_assn])
  apply (drule remove_component_right[where X = arena_fast_assn])
  apply (drule remove_component_right[where X = occs_assn])
  by (rule hfref_cong, assumption) auto

sublocale XX : read_all_param_adder where
  f =  \<open>(\<lambda>C _ _ _ _ _ _ _ _ _ _ _ M _ _ _ _ _. f C M)\<close> and
  f' = \<open>(\<lambda>C _ _ _ _ _ _ _ _ _ _ _ M _ _ _ _ _. f' C M)\<close> and
  P =  \<open>(\<lambda>C _ _ _ _ _ _ _ _ _ _ _ M _ _ _ _ _. P C M)\<close>
  by unfold_locales
   (rule not_deleted_code_refine')

lemmas refine = XX.refine
end

locale read_heur_param_adder0 =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(f, f') \<in> [P]\<^sub>a heuristic_assn\<^sup>k \<rightarrow> x_assn\<close>
begin
sublocale XX: read_heur_param_adder where
  f = \<open>\<lambda>_. f\<close> and
  f' = \<open>\<lambda>_. f'\<close> and
  P = \<open>\<lambda>_. P\<close>
  apply unfold_locales
  using not_deleted_code_refine[THEN remove_component_right] .

lemmas refine = XX.refine[THEN remove_unused_unit_parameter]
end


locale read_heur_param_adder2 =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P and R and R'
  assumes not_deleted_code_refine: \<open>(uncurry2 (\<lambda>S C D. f C D S), uncurry2 (\<lambda>S C' D'. f' C' D' S)) \<in> [uncurry2 (\<lambda>S C D. P C D S)]\<^sub>a heuristic_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k*\<^sub>a (pure R')\<^sup>k \<rightarrow> x_assn\<close>
begin
sublocale XX: read_heur_param_adder where
  f = \<open>\<lambda>(C,D) N. f C D N\<close> and
  f' = \<open>\<lambda>(C,D) N. f' C D N\<close> and
  P = \<open>\<lambda>(C,D) N. P C D N\<close> and
  R = \<open>R \<times>\<^sub>f R'\<close>
  apply unfold_locales
  using not_deleted_code_refine[THEN merge_second_pure_argument] .

lemma refine:
  \<open>(uncurry2 (\<lambda>N C D. read_heur_wl_heur_code (f C D) N),
    uncurry2 (\<lambda>N C' D. read_heur_wl_heur (f' C' D) N))
  \<in> [uncurry2 (\<lambda>S C D. P C D (get_heur S))]\<^sub>a isasat_bounded_assn\<^sup>k  *\<^sub>a (pure R)\<^sup>k *\<^sub>a (pure R')\<^sup>k \<rightarrow> x_assn\<close>
  by (rule XX.refine[THEN split_snd_pure_arg, unfolded prod.case])

end

abbreviation read_vdom_wl_heur_code :: \<open>_ \<Rightarrow> twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>read_vdom_wl_heur_code f \<equiv> read_all_st_code  (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ M _ _ _ _. f M)\<close>
abbreviation read_vdom_wl_heur :: \<open>_ \<Rightarrow> isasat \<Rightarrow> _\<close> where
  \<open>read_vdom_wl_heur f \<equiv> read_all_st  (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ M _ _ _ _. f M)\<close>

locale read_vdom_param_adder =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P and R
  assumes not_deleted_code_refine: \<open>(uncurry (\<lambda>S C. f C S), uncurry (\<lambda>S C'. f' C' S)) \<in> [uncurry (\<lambda>S C. P C S)]\<^sub>a aivdom_assn\<^sup>k  *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
begin

lemma not_deleted_code_refine':
  shows \<open>
  (uncurry17 (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ M _ _ _ _ C. f C M), uncurry17 (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ M _ _ _ _ C'. f' C' M)) \<in>
  [uncurry17 (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ M _ _ _ _ C'. P C' M)]\<^sub>a
   trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a
  watchlist_fast_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a cach_refinement_l_assn\<^sup>k *\<^sub>a
  lbd_assn\<^sup>k *\<^sub>a out_learned_assn\<^sup>k *\<^sub>a isasat_stats_assn\<^sup>k *\<^sub>a heuristic_assn\<^sup>k *\<^sub>a
  aivdom_assn\<^sup>k *\<^sub>a lcount_assn\<^sup>k *\<^sub>a opts_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a occs_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
  apply (rule add_pure_parameter2)
  apply (drule remove_pure_parameter2'[where f =f and f'=f', OF not_deleted_code_refine])
  apply (drule remove_component_left[where X = trail_pol_fast_assn])
  apply (drule remove_component_middle[where X = arena_fast_assn])
  apply (drule remove_component_middle[where X = conflict_option_rel_assn])
  apply (drule remove_component_middle[where X = sint64_nat_assn])
  apply (drule remove_component_middle[where X = watchlist_fast_assn])
  apply (drule remove_component_middle[where X = vmtf_remove_assn])
  apply (drule remove_component_middle[where X = uint32_nat_assn])
  apply (drule remove_component_middle[where X = cach_refinement_l_assn])
  apply (drule remove_component_middle[where X = lbd_assn])
  apply (drule remove_component_middle[where X = out_learned_assn])
  apply (drule remove_component_middle[where X = isasat_stats_assn])
  apply (drule remove_component_middle[where X = heuristic_assn])
  apply (drule remove_component_right[where X = lcount_assn])
  apply (drule remove_component_right[where X = opts_assn])
  apply (drule remove_component_right[where X = arena_fast_assn])
  apply (drule remove_component_right[where X = occs_assn])
  by (rule hfref_cong, assumption) auto

sublocale XX : read_all_param_adder where
  f =  \<open>(\<lambda>C _ _ _ _ _ _ _ _ _ _ _ _ M _ _ _ _. f C M)\<close> and
  f' = \<open>(\<lambda>C _ _ _ _ _ _ _ _ _ _ _ _ M _ _ _ _. f' C M)\<close> and
  P =  \<open>(\<lambda>C _ _ _ _ _ _ _ _ _ _ _ _ M _ _ _ _. P C M)\<close>
  by unfold_locales
   (rule not_deleted_code_refine')

lemmas refine = XX.refine
end

locale read_vdom_param_adder0 =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(f, f') \<in> [P]\<^sub>a aivdom_assn\<^sup>k \<rightarrow> x_assn\<close>
begin

sublocale XX: read_vdom_param_adder where
  f = \<open>\<lambda>_. f\<close> and
  f' = \<open>\<lambda>_. f'\<close> and
  P = \<open>\<lambda>_. P\<close>
  apply unfold_locales
  using not_deleted_code_refine[THEN remove_component_right] .

lemmas refine = XX.refine[THEN remove_unused_unit_parameter]
end



abbreviation read_lcount_wl_heur_code :: \<open>_ \<Rightarrow> twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>read_lcount_wl_heur_code f \<equiv> read_all_st_code  (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ M _ _ _. f M)\<close>
abbreviation read_lcount_wl_heur :: \<open>_ \<Rightarrow> isasat \<Rightarrow> _\<close> where
  \<open>read_lcount_wl_heur f \<equiv> read_all_st  (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ M _ _ _. f M)\<close>


locale read_lcount_param_adder =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P and R
  assumes not_deleted_code_refine: \<open>(uncurry (\<lambda>S C. f C S), uncurry (\<lambda>S C'. f' C' S)) \<in> [uncurry (\<lambda>S C. P C S)]\<^sub>a lcount_assn\<^sup>k  *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
begin

lemma not_deleted_code_refine':
  shows \<open>
  (uncurry17 (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ M _ _ _ C. f C M), uncurry17 (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ M _ _ _ C'. f' C' M)) \<in>
  [uncurry17 (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ M _ _ _ C'. P C' M)]\<^sub>a
   trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a
  watchlist_fast_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a cach_refinement_l_assn\<^sup>k *\<^sub>a
  lbd_assn\<^sup>k *\<^sub>a out_learned_assn\<^sup>k *\<^sub>a isasat_stats_assn\<^sup>k *\<^sub>a heuristic_assn\<^sup>k *\<^sub>a
  aivdom_assn\<^sup>k *\<^sub>a lcount_assn\<^sup>k *\<^sub>a opts_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a occs_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
  apply (rule add_pure_parameter2)
  apply (drule remove_pure_parameter2'[where f =f and f'=f', OF not_deleted_code_refine])
  apply (drule remove_component_left[where X = trail_pol_fast_assn])
  apply (drule remove_component_middle[where X = arena_fast_assn])
  apply (drule remove_component_middle[where X = conflict_option_rel_assn])
  apply (drule remove_component_middle[where X = sint64_nat_assn])
  apply (drule remove_component_middle[where X = watchlist_fast_assn])
  apply (drule remove_component_middle[where X = vmtf_remove_assn])
  apply (drule remove_component_middle[where X = uint32_nat_assn])
  apply (drule remove_component_middle[where X = cach_refinement_l_assn])
  apply (drule remove_component_middle[where X = lbd_assn])
  apply (drule remove_component_middle[where X = out_learned_assn])
  apply (drule remove_component_middle[where X = isasat_stats_assn])
  apply (drule remove_component_middle[where X = heuristic_assn])
  apply (drule remove_component_middle[where X = aivdom_assn])
  apply (drule remove_component_right[where X = opts_assn])
  apply (drule remove_component_right[where X = arena_fast_assn])
  apply (drule remove_component_right[where X = occs_assn])
  by (rule hfref_cong, assumption) auto

sublocale XX : read_all_param_adder where
  f =  \<open>(\<lambda>C _ _ _ _ _ _ _ _ _ _ _ _ _ M _ _ _. f C M)\<close> and
  f' = \<open>(\<lambda>C _ _ _ _ _ _ _ _ _ _ _ _ _ M _ _ _. f' C M)\<close> and
  P =  \<open>(\<lambda>C _ _ _ _ _ _ _ _ _ _ _ _ _ M _ _ _. P C M)\<close>
  by unfold_locales
   (rule not_deleted_code_refine')

lemmas refine = XX.refine
end

locale read_lcount_param_adder0 =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(f, f') \<in> [P]\<^sub>a lcount_assn\<^sup>k \<rightarrow> x_assn\<close>
begin
sublocale XX: read_lcount_param_adder where
  f = \<open>\<lambda>_. f\<close> and
  f' = \<open>\<lambda>_. f'\<close> and
  P = \<open>\<lambda>_. P\<close>
  apply unfold_locales
  using not_deleted_code_refine[THEN remove_component_right] .

lemmas refine = XX.refine[THEN remove_unused_unit_parameter]
end



abbreviation read_opts_wl_heur_code :: \<open>_ \<Rightarrow> twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>read_opts_wl_heur_code f \<equiv> read_all_st_code  (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ _ M _ _. f M)\<close>
abbreviation read_opts_wl_heur :: \<open>_ \<Rightarrow> isasat \<Rightarrow> _\<close> where
  \<open>read_opts_wl_heur f \<equiv> read_all_st  (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ _ M _ _. f M)\<close>

locale read_opts_param_adder =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(uncurry (\<lambda>S C. f C S), uncurry (\<lambda>S C'. f' C' S)) \<in> [uncurry (\<lambda>S C. P C S)]\<^sub>a opts_assn\<^sup>k  *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
begin

lemma not_deleted_code_refine':
  shows \<open>
  (uncurry17 (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ _ M _ _ C. f C M), uncurry17 (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ _ M _ _ C'. f' C' M)) \<in>
  [uncurry17 (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ _ M _ _ C'. P C' M)]\<^sub>a
   trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a
  watchlist_fast_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a cach_refinement_l_assn\<^sup>k *\<^sub>a
  lbd_assn\<^sup>k *\<^sub>a out_learned_assn\<^sup>k *\<^sub>a isasat_stats_assn\<^sup>k *\<^sub>a heuristic_assn\<^sup>k *\<^sub>a
  aivdom_assn\<^sup>k *\<^sub>a lcount_assn\<^sup>k *\<^sub>a opts_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a occs_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
  apply (rule add_pure_parameter2)
  apply (drule remove_pure_parameter2'[where f =f and f'=f', OF not_deleted_code_refine])
  apply (drule remove_component_left[where X = trail_pol_fast_assn])
  apply (drule remove_component_middle[where X = arena_fast_assn])
  apply (drule remove_component_middle[where X = conflict_option_rel_assn])
  apply (drule remove_component_middle[where X = sint64_nat_assn])
  apply (drule remove_component_middle[where X = watchlist_fast_assn])
  apply (drule remove_component_middle[where X = vmtf_remove_assn])
  apply (drule remove_component_middle[where X = uint32_nat_assn])
  apply (drule remove_component_middle[where X = cach_refinement_l_assn])
  apply (drule remove_component_middle[where X = lbd_assn])
  apply (drule remove_component_middle[where X = out_learned_assn])
  apply (drule remove_component_middle[where X = isasat_stats_assn])
  apply (drule remove_component_middle[where X = heuristic_assn])
  apply (drule remove_component_middle[where X = aivdom_assn])
  apply (drule remove_component_middle[where X = lcount_assn])
  apply (drule remove_component_right[where X = arena_fast_assn])
  apply (drule remove_component_right[where X = occs_assn])
  by (rule hfref_cong, assumption) auto

sublocale XX : read_all_param_adder where
  f =  \<open>(\<lambda>C _ _ _ _ _ _ _ _ _ _ _ _ _ _ M _ _. f C M)\<close> and
  f' = \<open>(\<lambda>C _ _ _ _ _ _ _ _ _ _ _ _ _ _ M _ _. f' C M)\<close> and
  P =  \<open>(\<lambda>C _ _ _ _ _ _ _ _ _ _ _ _ _ _ M _ _. P C M)\<close>
  by unfold_locales
   (rule not_deleted_code_refine')

lemmas refine = XX.refine
end

locale read_opts_param_adder0 =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(f, f') \<in> [P]\<^sub>a opts_assn\<^sup>k \<rightarrow> x_assn\<close>
begin

sublocale XX: read_opts_param_adder where
  f = \<open>\<lambda>_. f\<close> and
  f' = \<open>\<lambda>_. f'\<close> and
  P = \<open>\<lambda>_. P\<close>
  apply unfold_locales
  using not_deleted_code_refine[THEN remove_component_right] .

lemmas refine = XX.refine[THEN remove_unused_unit_parameter]
end



abbreviation read_old_arena_wl_heur_code :: \<open>_ \<Rightarrow> twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>read_old_arena_wl_heur_code f \<equiv> read_all_st_code  (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M. f M)\<close>
abbreviation read_old_arena_wl_heur :: \<open>_ \<Rightarrow> isasat \<Rightarrow> _\<close> where
  \<open>read_old_arena_wl_heur f \<equiv> read_all_st  (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M. f M)\<close>

locale read_old_arena_param_adder =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(uncurry (\<lambda>S C. f C S), uncurry (\<lambda>S C'. f' C' S)) \<in> [uncurry (\<lambda>S C. P C S)]\<^sub>a arena_fast_assn\<^sup>k  *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
begin

lemma not_deleted_code_refine':
  shows \<open>
  (uncurry17 (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M _ C. f C M), uncurry17 (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M _ C'. f' C' M)) \<in>
  [uncurry17 (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M _ C'. P C' M)]\<^sub>a
   trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a
  watchlist_fast_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a cach_refinement_l_assn\<^sup>k *\<^sub>a
  lbd_assn\<^sup>k *\<^sub>a out_learned_assn\<^sup>k *\<^sub>a isasat_stats_assn\<^sup>k *\<^sub>a heuristic_assn\<^sup>k *\<^sub>a
  aivdom_assn\<^sup>k *\<^sub>a lcount_assn\<^sup>k *\<^sub>a opts_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a occs_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
  apply (rule add_pure_parameter2)
  apply (drule remove_pure_parameter2'[where f =f and f'=f', OF not_deleted_code_refine])
  apply (drule remove_component_left[where X = trail_pol_fast_assn])
  apply (drule remove_component_middle[where X = arena_fast_assn])
  apply (drule remove_component_middle[where X = conflict_option_rel_assn])
  apply (drule remove_component_middle[where X = sint64_nat_assn])
  apply (drule remove_component_middle[where X = watchlist_fast_assn])
  apply (drule remove_component_middle[where X = vmtf_remove_assn])
  apply (drule remove_component_middle[where X = uint32_nat_assn])
  apply (drule remove_component_middle[where X = cach_refinement_l_assn])
  apply (drule remove_component_middle[where X = lbd_assn])
  apply (drule remove_component_middle[where X = out_learned_assn])
  apply (drule remove_component_middle[where X = isasat_stats_assn])
  apply (drule remove_component_middle[where X = heuristic_assn])
  apply (drule remove_component_middle[where X = aivdom_assn])
  apply (drule remove_component_middle[where X = lcount_assn])
  apply (drule remove_component_middle[where X = opts_assn])
  apply (drule remove_component_right[where X = occs_assn])
  by (rule hfref_cong, assumption) auto

sublocale XX : read_all_param_adder where
  f =  \<open>(\<lambda>C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M _. f C M)\<close> and
  f' = \<open>(\<lambda>C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M _. f' C M)\<close> and
  P =  \<open>(\<lambda>C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M _. P C M)\<close>
  by unfold_locales
   (rule not_deleted_code_refine')

lemmas refine = XX.refine
end


locale read_old_arena_param_adder0 =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(f, f') \<in> [P]\<^sub>a arena_fast_assn\<^sup>k \<rightarrow> x_assn\<close>
begin

sublocale XX: read_old_arena_param_adder where
  f = \<open>\<lambda>_. f\<close> and
  f' = \<open>\<lambda>_. f'\<close> and
  P = \<open>\<lambda>_. P\<close>
  apply unfold_locales
  using not_deleted_code_refine[THEN remove_component_right] .

lemmas refine = XX.refine[THEN remove_unused_unit_parameter]
end


abbreviation read_occs_wl_heur_code :: \<open>_ \<Rightarrow> twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>read_occs_wl_heur_code f \<equiv> read_all_st_code  (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M. f M)\<close>
abbreviation read_occs_wl_heur :: \<open>_ \<Rightarrow> isasat \<Rightarrow> _\<close> where
  \<open>read_occs_wl_heur f \<equiv> read_all_st  (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M. f M)\<close>

locale read_occs_param_adder =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P and R
  assumes not_deleted_code_refine: \<open>(uncurry (\<lambda>S C. f C S), uncurry (\<lambda>S C'. f' C' S)) \<in> [uncurry (\<lambda>S C. P C S)]\<^sub>a occs_assn\<^sup>k  *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
begin

lemma not_deleted_code_refine':
  shows \<open>
  (uncurry17 (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M C. f C M), uncurry17 (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M C'. f' C' M)) \<in>
  [uncurry17 (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M C'. P C' M)]\<^sub>a
   trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a
  watchlist_fast_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a cach_refinement_l_assn\<^sup>k *\<^sub>a
  lbd_assn\<^sup>k *\<^sub>a out_learned_assn\<^sup>k *\<^sub>a isasat_stats_assn\<^sup>k *\<^sub>a heuristic_assn\<^sup>k *\<^sub>a
  aivdom_assn\<^sup>k *\<^sub>a lcount_assn\<^sup>k *\<^sub>a opts_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a occs_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
  apply (rule add_pure_parameter2)
  apply (drule remove_pure_parameter2'[where f =f and f'=f', OF not_deleted_code_refine])
  apply (drule remove_component_left[where X = trail_pol_fast_assn])
  apply (drule remove_component_middle[where X = arena_fast_assn])
  apply (drule remove_component_middle[where X = conflict_option_rel_assn])
  apply (drule remove_component_middle[where X = sint64_nat_assn])
  apply (drule remove_component_middle[where X = watchlist_fast_assn])
  apply (drule remove_component_middle[where X = vmtf_remove_assn])
  apply (drule remove_component_middle[where X = uint32_nat_assn])
  apply (drule remove_component_middle[where X = cach_refinement_l_assn])
  apply (drule remove_component_middle[where X = lbd_assn])
  apply (drule remove_component_middle[where X = out_learned_assn])
  apply (drule remove_component_middle[where X = isasat_stats_assn])
  apply (drule remove_component_middle[where X = heuristic_assn])
  apply (drule remove_component_middle[where X = aivdom_assn])
  apply (drule remove_component_middle[where X = lcount_assn])
  apply (drule remove_component_middle[where X = opts_assn])
  apply (drule remove_component_middle[where X = arena_fast_assn])
  by (rule hfref_cong, assumption) auto

sublocale XX : read_all_param_adder where
  f =  \<open>(\<lambda>C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M. f C M)\<close> and
  f' = \<open>(\<lambda>C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M. f' C M)\<close> and
  P =  \<open>(\<lambda>C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M. P C M)\<close>
  by unfold_locales
   (rule not_deleted_code_refine')

lemmas refine = XX.refine
end


locale read_occs_param_adder0 =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(f, f') \<in> [P]\<^sub>a occs_assn\<^sup>k \<rightarrow> x_assn\<close>
begin

sublocale XX: read_occs_param_adder where
  f = \<open>\<lambda>_. f\<close> and
  f' = \<open>\<lambda>_. f'\<close> and
  P = \<open>\<lambda>_. P\<close>
  apply unfold_locales
  using not_deleted_code_refine[THEN remove_component_right] .

lemmas refine = XX.refine[THEN remove_unused_unit_parameter]
end

locale read_occs_param_adder2 =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P and R and R'
  assumes not_deleted_code_refine: \<open>(uncurry2 (\<lambda>S C D. f C D S), uncurry2 (\<lambda>S C' D'. f' C' D' S)) \<in> [uncurry2 (\<lambda>S C D. P C D S)]\<^sub>a occs_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k*\<^sub>a (pure R')\<^sup>k \<rightarrow> x_assn\<close>
begin

sublocale XX: read_occs_param_adder where
  f = \<open>\<lambda>(C,D) N. f C D N\<close> and
  f' = \<open>\<lambda>(C,D) N. f' C D N\<close> and
  P = \<open>\<lambda>(C,D) N. P C D N\<close> and
  R = \<open>R \<times>\<^sub>f R'\<close>
  apply unfold_locales
  using not_deleted_code_refine[THEN merge_second_pure_argument] .

lemma refine:
  \<open>(uncurry2 (\<lambda>N C D. read_occs_wl_heur_code (f C D) N),
    uncurry2 (\<lambda>N C' D. read_occs_wl_heur (f' C' D) N))
  \<in> [uncurry2 (\<lambda>S C D. P C D (get_occs S))]\<^sub>a isasat_bounded_assn\<^sup>k  *\<^sub>a (pure R)\<^sup>k *\<^sub>a (pure R')\<^sup>k \<rightarrow> x_assn\<close>
  by (rule XX.refine[THEN split_snd_pure_arg, unfolded prod.case])

lemma mop_refine:
  \<open>(uncurry2 (\<lambda>N C D. read_occs_wl_heur_code (f C D) N), uncurry2 (\<lambda>N C D. XX.XX.mop N (C,D))) \<in>
  isasat_bounded_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k *\<^sub>a (pure R')\<^sup>k \<rightarrow>\<^sub>a x_assn\<close>
  unfolding mop_def XX.XX.mop_def
  apply (rule refine_ASSERT_move_to_pre2)
  unfolding prod.simps
  apply (rule refine[unfolded comp_def])
  done

end


locale read_trail_arena_param_adder_ops =
  fixes P :: \<open>'b \<Rightarrow> trail_pol \<Rightarrow> arena \<Rightarrow> bool\<close> and f' :: \<open>'b \<Rightarrow> trail_pol \<Rightarrow> arena_el list \<Rightarrow> 'r nres\<close>
begin

definition mop where
  \<open>mop N C = do {
    ASSERT (P C (get_trail_wl_heur N) (get_clauses_wl_heur N));
    read_all_st (\<lambda>M N _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. f' C M N) N
   }\<close>

end

locale read_trail_arena_param_adder = read_trail_arena_param_adder_ops P f'
  for P :: \<open>'b \<Rightarrow> trail_pol \<Rightarrow> arena \<Rightarrow> bool\<close> and f' :: \<open>'b \<Rightarrow> trail_pol \<Rightarrow> arena_el list \<Rightarrow> 'r nres\<close> +
  fixes R :: \<open>('a \<times> 'b) set\<close> and f and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close>
  assumes not_deleted_code_refine: \<open>(uncurry2 (\<lambda>S T C. f C S T), uncurry2 (\<lambda>S T C'. f' C' S T)) \<in> [uncurry2 (\<lambda>S T C. P C S T)]\<^sub>a trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
begin

lemma not_deleted_code_refine':
  \<open>(uncurry17 (\<lambda>M N _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C. f C M N), uncurry17 (\<lambda>M N _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C'. f' C' M N)) \<in>
  [uncurry17 (\<lambda>M N _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C'. P C' M N)]\<^sub>a
   trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a
  watchlist_fast_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a cach_refinement_l_assn\<^sup>k *\<^sub>a
  lbd_assn\<^sup>k *\<^sub>a out_learned_assn\<^sup>k *\<^sub>a isasat_stats_assn\<^sup>k *\<^sub>a heuristic_assn\<^sup>k *\<^sub>a
  aivdom_assn\<^sup>k *\<^sub>a lcount_assn\<^sup>k *\<^sub>a opts_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k  *\<^sub>a occs_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
  apply (rule add_pure_parameter2)
  apply (drule remove_pure_parameter2'[OF not_deleted_code_refine])
  apply (drule remove_component_right[where X = conflict_option_rel_assn])
  apply (drule remove_component_right[where X = sint64_nat_assn])
  apply (drule remove_component_right[where X = watchlist_fast_assn])
  apply (drule remove_component_right[where X = vmtf_remove_assn])
  apply (drule remove_component_right[where X = uint32_nat_assn])
  apply (drule remove_component_right[where X = cach_refinement_l_assn])
  apply (drule remove_component_right[where X = lbd_assn])
  apply (drule remove_component_right[where X = out_learned_assn])
  apply (drule remove_component_right[where X = isasat_stats_assn])
  apply (drule remove_component_right[where X = heuristic_assn])
  apply (drule remove_component_right[where X = aivdom_assn])
  apply (drule remove_component_right[where X = lcount_assn])
  apply (drule remove_component_right[where X = opts_assn])
  apply (drule remove_component_right[where X = arena_fast_assn])
  apply (drule remove_component_right[where X = occs_assn])
  by (rule hfref_cong, assumption) auto

sublocale XX : read_all_param_adder where
  f = \<open>(\<lambda>C M N _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. f C M N)\<close> and
  f' = \<open>(\<lambda>C M N _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. f' C M N)\<close> and
  P = \<open>(\<lambda>C M N _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. P C M N)\<close>
  by unfold_locales
   (rule not_deleted_code_refine')

lemmas refine = XX.refine

lemma mop_refine:
  \<open>(uncurry (\<lambda>N C. read_all_st_code (\<lambda>M N _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. f C M N) N),
    uncurry mop)
  \<in> isasat_bounded_assn\<^sup>k  *\<^sub>a (pure R)\<^sup>k\<rightarrow>\<^sub>a x_assn\<close>
  unfolding mop_def
  apply (rule refine_ASSERT_move_to_pre)
  apply (rule refine)
  done
end


locale read_trail_arena_param_adder2_twoargs_ops =
  fixes
    f' :: \<open>'b \<Rightarrow> 'd \<Rightarrow> trail_pol \<Rightarrow> arena \<Rightarrow> 'r nres\<close> and
    P :: \<open>'b \<Rightarrow> 'd \<Rightarrow> trail_pol \<Rightarrow> arena \<Rightarrow> bool\<close>
begin
definition mop where
  \<open>mop N C C' = do {
     ASSERT (P C C' (get_trail_wl_heur N) (get_clauses_wl_heur N));
     read_all_st (\<lambda>M N  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. f' C C' M N) N
  }\<close>
end

locale read_trail_arena_param_adder2_twoargs =
  read_trail_arena_param_adder2_twoargs_ops f' P
  for f' :: \<open>'b \<Rightarrow> 'd \<Rightarrow> trail_pol \<Rightarrow> arena \<Rightarrow> 'r nres\<close> and P +
  fixes R and R' and f and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close>
  assumes not_deleted_code_refine:
    \<open>(uncurry3 (\<lambda>S T C D. f C D S T), uncurry3 (\<lambda>S T C' D'. f' C' D' S T)) \<in>
    [uncurry3 (\<lambda>S T C' D'. P C' D' S T)]\<^sub>a trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k *\<^sub>a (pure R')\<^sup>k \<rightarrow> x_assn\<close>
begin

sublocale XX: read_trail_arena_param_adder where
  f = \<open>\<lambda>(C,D) N. f C D N\<close> and
  f' = \<open>\<lambda>(C,D) N. f' C D N\<close> and
  P = \<open>\<lambda>(C,D) N. P C D N\<close> and
  R = \<open>R \<times>\<^sub>f R'\<close>
  apply unfold_locales
  by (rule hfref_cong[OF not_deleted_code_refine[THEN merge_second_pure_argument]]) auto

lemmas refine = XX.refine[unfolded case_isasat_int_split_getter]

lemma mop_refine:
  \<open>(uncurry2 (\<lambda>N C D. read_all_st_code
        (\<lambda>M N _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. f C D M N) N), uncurry2 mop) \<in> isasat_bounded_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k *\<^sub>a (pure R')\<^sup>k \<rightarrow>\<^sub>a x_assn\<close>
  unfolding mop_def
  apply (rule refine_ASSERT_move_to_pre2)
  apply (rule refine[THEN split_snd_pure_arg, unfolded prod.case])
  done
end

locale read_trail_arena_param_adder2_threeargs_ops =
  fixes
    f' :: \<open>'b \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> trail_pol \<Rightarrow> arena \<Rightarrow> 'r nres\<close> and
    P :: \<open>'b \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> trail_pol \<Rightarrow> arena \<Rightarrow> bool\<close>
begin
definition mop where
  \<open>mop N C D E = do {
     ASSERT (P C D E (get_trail_wl_heur N) (get_clauses_wl_heur N));
     read_all_st (\<lambda>M N  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. f' C D E M N) N
  }\<close>
end


lemma refine_ASSERT_move_to_pre3:
  assumes \<open>(uncurry3 g, uncurry3 h) \<in> [uncurry3 P]\<^sub>a A *\<^sub>a B *\<^sub>a C *\<^sub>a D \<rightarrow> x_assn\<close>
  shows
  \<open>(uncurry3 g, uncurry3 (\<lambda>N C D E. do {ASSERT (P N C D E); h N C D E}))
    \<in> A *\<^sub>a B *\<^sub>a C *\<^sub>a D \<rightarrow>\<^sub>a x_assn\<close>
  apply sepref_to_hoare
  apply vcg
  apply (subst POSTCOND_def hn_ctxt_def sep_conj_empty' pure_true_conv EXTRACT_def)+
  apply (auto simp: nofail_ASSERT_bind)
  apply (rule assms[to_hnr, simplified, unfolded hn_ctxt_def hn_refine_def htriple_def
    sep_conj_empty' pure_true_conv sep.add_assoc, rule_format])
  apply auto
  done
 
locale read_trail_arena_param_adder2_threeargs =
  read_trail_arena_param_adder2_threeargs_ops f' P
  for f' :: \<open>'b \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> trail_pol \<Rightarrow> arena \<Rightarrow> 'r nres\<close> and P +
  fixes R and R' and R'' and f and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close>
  assumes not_deleted_code_refine:
    \<open>(uncurry4 (\<lambda>S T C D E. f C D E S T), uncurry4 (\<lambda>S T C' D' E'. f' C' D' E' S T)) \<in>
    [uncurry4 (\<lambda>S T C' D' E'. P C' D' E' S T)]\<^sub>a trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k *\<^sub>a (pure R')\<^sup>k*\<^sub>a (pure R'')\<^sup>k \<rightarrow> x_assn\<close>
begin
sublocale XX: read_trail_arena_param_adder where
  f = \<open>\<lambda>(C,D,E) N. f C D E N\<close> and
  f' = \<open>\<lambda>(C,D,E) N. f' C D E N\<close> and
  P = \<open>\<lambda>(C,D,E) N. P C D E N\<close> and
  R = \<open>R \<times>\<^sub>r R' \<times>\<^sub>r R''\<close>
  apply unfold_locales
  subgoal
    using not_deleted_code_refine[THEN merge_second_pure_argument]
    by (auto simp flip: prod_assn_pure_conv simp: hfref_def)
  done


text \<open>It would be better to this without calling auto, but fighting uncurry is just too hard
  and not really useful.\<close>
lemma refine:
  \<open>(uncurry3 (\<lambda>N C D E. read_all_st_code (\<lambda>M N _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. f C D E M N) N),
  uncurry3 (\<lambda>N C D E. read_all_st (\<lambda>M N _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. f' C D E M N) N))
  \<in> [uncurry3 (\<lambda>S C' D' E'. P C' D' E' (get_trail_wl_heur S) (get_clauses_wl_heur S))]\<^sub>a
  isasat_bounded_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k *\<^sub>a (pure R')\<^sup>k *\<^sub>a (pure R'')\<^sup>k \<rightarrow> x_assn\<close>
  using XX.refine[THEN split_snd_pure_arg, unfolded prod.case] unfolding hfref_def
  by (auto simp flip: prod_assn_pure_conv)
lemma mop_refine:
  \<open>(uncurry3 (\<lambda>N C D E. read_all_st_code
        (\<lambda>M N _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. f C D E M N) N), uncurry3 mop) \<in> isasat_bounded_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k *\<^sub>a (pure R')\<^sup>k *\<^sub>a (pure R'')\<^sup>k \<rightarrow>\<^sub>a x_assn\<close>
  unfolding mop_def
  apply (rule refine_ASSERT_move_to_pre3)
  apply (rule refine)
  done

end


locale read_trail_vmtf_param_adder =
  fixes P :: \<open>'b \<Rightarrow> _ \<Rightarrow> isa_vmtf_remove_int \<Rightarrow> bool\<close> and f' :: \<open>'b \<Rightarrow> trail_pol \<Rightarrow> _ \<Rightarrow> 'r nres\<close> and
     R :: \<open>('a \<times> 'b) set\<close> and f and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close>
  assumes not_deleted_code_refine: \<open>(uncurry2 (\<lambda>S T C. f C S T), uncurry2 (\<lambda>S T C'. f' C' S T)) \<in> [uncurry2 (\<lambda>S T C. P C S T)]\<^sub>a trail_pol_fast_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
begin

lemma not_deleted_code_refine':
  \<open>(uncurry17 (\<lambda>M _ _ _ _ N _ _ _ _ _ _ _ _ _ _ _ C. f C M N), uncurry17 (\<lambda>M _ _ _ _ N _ _ _ _ _ _ _ _ _ _ _ C'. f' C' M N)) \<in>
  [uncurry17 (\<lambda>M _ _ _ _ N _ _ _ _ _ _ _ _ _ _ _ C'. P C' M N)]\<^sub>a
   trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a
  watchlist_fast_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a cach_refinement_l_assn\<^sup>k *\<^sub>a
  lbd_assn\<^sup>k *\<^sub>a out_learned_assn\<^sup>k *\<^sub>a isasat_stats_assn\<^sup>k *\<^sub>a heuristic_assn\<^sup>k *\<^sub>a
  aivdom_assn\<^sup>k *\<^sub>a lcount_assn\<^sup>k *\<^sub>a opts_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k  *\<^sub>a occs_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k \<rightarrow> x_assn\<close>
  apply (rule add_pure_parameter2)
  apply (drule remove_pure_parameter2'[OF not_deleted_code_refine])
  apply (drule remove_component_middle[where X = arena_fast_assn])
  apply (drule remove_component_middle[where X = conflict_option_rel_assn])
  apply (drule remove_component_middle[where X = sint64_nat_assn])
  apply (drule remove_component_middle[where X = watchlist_fast_assn])
  apply (drule remove_component_right[where X = uint32_nat_assn])
  apply (drule remove_component_right[where X = cach_refinement_l_assn])
  apply (drule remove_component_right[where X = lbd_assn])
  apply (drule remove_component_right[where X = out_learned_assn])
  apply (drule remove_component_right[where X = isasat_stats_assn])
  apply (drule remove_component_right[where X = heuristic_assn])
  apply (drule remove_component_right[where X = aivdom_assn])
  apply (drule remove_component_right[where X = lcount_assn])
  apply (drule remove_component_right[where X = opts_assn])
  apply (drule remove_component_right[where X = arena_fast_assn])
  apply (drule remove_component_right[where X = occs_assn])
  by (rule hfref_cong, assumption) auto

sublocale XX : read_all_param_adder where
  f = \<open>(\<lambda>C M _ _ _ _ N _ _ _ _ _ _ _ _ _ _ _. f C M N)\<close> and
  f' = \<open>(\<lambda>C M _ _ _ _ N _ _ _ _ _ _ _ _ _ _ _. f' C M N)\<close> and
  P = \<open>(\<lambda>C M _ _ _ _ N _ _ _ _ _ _ _ _ _ _ _. P C M N)\<close>
  by unfold_locales
   (rule not_deleted_code_refine')

lemmas refine = XX.refine
end

lemma hn_refine_frame''': "hn_refine (F**G) c (F'**G') R CP m \<Longrightarrow> hn_refine (F**G**H) c (F'**G'**H) R CP m"
  by (metis hn_refine_frame_mid'' sep.mult_commute)

locale read_trail_vmtf_param_adder0 =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(uncurry (\<lambda>S T. f S T), uncurry (\<lambda>S T. f' S T)) \<in> [uncurry (\<lambda>S T. P S T)]\<^sub>a trail_pol_fast_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>k \<rightarrow> x_assn\<close>
begin

sublocale XX: read_trail_vmtf_param_adder where
  f = \<open>\<lambda>_::unit. f\<close> and
  f' = \<open>\<lambda>_::unit. f'\<close> and
  P = \<open>\<lambda>_::unit. P\<close> and 
  R = \<open>unit_rel\<close>
  apply unfold_locales
  using not_deleted_code_refine apply -
  unfolding hfref_def
  apply clarsimp
  apply (rule hn_refine_frame''')
  apply auto
  done

lemmas refine = XX.refine[THEN remove_unused_unit_parameter]
end



lemma Mreturn_comp_IsaSAT_int:
  \<open>(Mreturn o\<^sub>1\<^sub>7 IsaSAT_int) a b c d e f g h i j k l m n ko p q =
  Mreturn (IsaSAT_int a b c d e f g h i j k l m n ko p q)\<close>
  by auto

sepref_register
  remove_a remove_b remove_c remove_d
  remove_e remove_f remove_g remove_h
  remove_i remove_j remove_k remove_l
  remove_m remove_n remove_o remove_p remove_q

lemmas [sepref_fr_rules] =
  remove_a_code.refine
  remove_b_code.refine
  remove_c_code.refine
  remove_d_code.refine
  remove_e_code.refine
  remove_f_code.refine
  remove_g_code.refine
  remove_h_code.refine
  remove_i_code.refine
  remove_j_code.refine
  remove_k_code.refine
  remove_l_code.refine
  remove_m_code.refine
  remove_n_code.refine
  remove_o_code.refine
  remove_p_code.refine
  remove_q_code.refine


lemma lambda_comp_true: \<open>(\<lambda>S. True) \<circ> f = (\<lambda>_. True)\<close> \<open>uncurry (\<lambda>a b. True) = (\<lambda>_. True)\<close>  \<open>uncurry2 (\<lambda>a b c. True) = (\<lambda>_. True)\<close>
  \<open>case_isasat_int (\<lambda>M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _. True) = (\<lambda>_. True)\<close>
  by (auto intro!: ext split: isasat_int_splits)

named_theorems state_extractors \<open>Definition of all functions modifying the state\<close>
lemmas [state_extractors] =
  extract_trail_wl_heur_def
  extract_arena_wl_heur_def
  extract_conflict_wl_heur_def
  extract_watchlist_wl_heur_def
  extract_vmtf_wl_heur_def
  extract_ccach_wl_heur_def
  extract_clvls_wl_heur_def
  extract_lbd_wl_heur_def
  extract_outl_wl_heur_def
  extract_stats_wl_heur_def
  extract_heur_wl_heur_def
  extract_vdom_wl_heur_def
  extract_lcount_wl_heur_def
  extract_opts_wl_heur_def
  extract_literals_to_update_wl_heur_def
  extract_occs_wl_heur_def
  tuple17_getters_setters



lemmas [llvm_inline] =
  DEFAULT_INIT_PHASE_def
  FOCUSED_MODE_def

lemma from_bool1: "from_bool True = 1"
  by auto
lemmas [llvm_pre_simp] = from_bool1

lemmas [unfolded inline_direct_return_node_case, llvm_code] =
  remove_a_code_alt_def[unfolded isasat_state.remove_a_code_alt_def Mreturn_comp_IsaSAT_int]
  remove_b_code_alt_def[unfolded isasat_state.remove_b_code_alt_def Mreturn_comp_IsaSAT_int]
  remove_c_code_alt_def[unfolded isasat_state.remove_c_code_alt_def Mreturn_comp_IsaSAT_int]
  remove_d_code_alt_def[unfolded isasat_state.remove_d_code_alt_def Mreturn_comp_IsaSAT_int]
  remove_e_code_alt_def[unfolded isasat_state.remove_e_code_alt_def Mreturn_comp_IsaSAT_int]
  remove_f_code_alt_def[unfolded isasat_state.remove_f_code_alt_def Mreturn_comp_IsaSAT_int]
  remove_g_code_alt_def[unfolded isasat_state.remove_g_code_alt_def Mreturn_comp_IsaSAT_int]
  remove_h_code_alt_def[unfolded isasat_state.remove_h_code_alt_def Mreturn_comp_IsaSAT_int]
  remove_i_code_alt_def[unfolded isasat_state.remove_i_code_alt_def Mreturn_comp_IsaSAT_int]
  remove_j_code_alt_def[unfolded isasat_state.remove_j_code_alt_def Mreturn_comp_IsaSAT_int]
  remove_k_code_alt_def[unfolded isasat_state.remove_k_code_alt_def Mreturn_comp_IsaSAT_int]
  remove_l_code_alt_def[unfolded isasat_state.remove_l_code_alt_def Mreturn_comp_IsaSAT_int]
  remove_m_code_alt_def[unfolded isasat_state.remove_m_code_alt_def Mreturn_comp_IsaSAT_int]
  remove_n_code_alt_def[unfolded isasat_state.remove_n_code_alt_def Mreturn_comp_IsaSAT_int]
  remove_o_code_alt_def[unfolded isasat_state.remove_o_code_alt_def Mreturn_comp_IsaSAT_int]
  remove_p_code_alt_def[unfolded isasat_state.remove_p_code_alt_def Mreturn_comp_IsaSAT_int]
  remove_q_code_alt_def[unfolded isasat_state.remove_q_code_alt_def Mreturn_comp_IsaSAT_int]

abbreviation update_trail_wl_heur :: \<open>trail_pol \<Rightarrow> isasat \<Rightarrow> _\<close> where
  \<open>update_trail_wl_heur \<equiv> update_a\<close>

abbreviation update_arena_wl_heur :: \<open>arena \<Rightarrow>isasat \<Rightarrow> _\<close> where
  \<open>update_arena_wl_heur \<equiv> update_b\<close>

abbreviation update_conflict_wl_heur :: \<open>conflict_option_rel \<Rightarrow>isasat \<Rightarrow> _\<close> where
  \<open>update_conflict_wl_heur \<equiv> update_c\<close>

abbreviation update_literals_to_update_wl_heur :: \<open>nat \<Rightarrow>isasat \<Rightarrow> _\<close> where
  \<open>update_literals_to_update_wl_heur \<equiv> update_d\<close>

abbreviation update_watchlist_wl_heur :: \<open>nat watcher list list \<Rightarrow>isasat \<Rightarrow> _\<close> where
  \<open>update_watchlist_wl_heur \<equiv> update_e\<close>

abbreviation update_vmtf_wl_heur :: \<open>isa_vmtf_remove_int \<Rightarrow>isasat \<Rightarrow> _\<close> where
  \<open>update_vmtf_wl_heur \<equiv> update_f\<close>

abbreviation update_clvls_wl_heur :: \<open>nat \<Rightarrow>isasat \<Rightarrow> _\<close> where
  \<open>update_clvls_wl_heur \<equiv> update_g\<close>

abbreviation update_ccach_wl_heur :: \<open>conflict_min_cach_l \<Rightarrow>isasat \<Rightarrow> _\<close> where
  \<open>update_ccach_wl_heur \<equiv> update_h\<close>

abbreviation update_lbd_wl_heur :: \<open>lbd \<Rightarrow>isasat \<Rightarrow> _\<close> where
  \<open>update_lbd_wl_heur \<equiv> update_i\<close>

abbreviation update_outl_wl_heur :: \<open>out_learned \<Rightarrow>isasat \<Rightarrow> _\<close> where
  \<open>update_outl_wl_heur \<equiv> update_j\<close>

abbreviation update_stats_wl_heur :: \<open>isasat_stats \<Rightarrow> isasat \<Rightarrow> isasat\<close> where
  \<open>update_stats_wl_heur \<equiv> update_k\<close>

abbreviation update_heur_wl_heur :: \<open>isasat_restart_heuristics \<Rightarrow>isasat \<Rightarrow> isasat\<close> where
  \<open>update_heur_wl_heur \<equiv> update_l\<close>

abbreviation update_vdom_wl_heur :: \<open>isasat_aivdom \<Rightarrow>isasat \<Rightarrow> _\<close> where
  \<open>update_vdom_wl_heur \<equiv> update_m\<close>

abbreviation update_lcount_wl_heur :: \<open>clss_size \<Rightarrow>isasat \<Rightarrow> _\<close> where
  \<open>update_lcount_wl_heur \<equiv> update_n\<close>

abbreviation update_opts_wl_heur :: \<open>opts \<Rightarrow>isasat \<Rightarrow> _\<close> where
  \<open>update_opts_wl_heur \<equiv> update_o\<close>

abbreviation update_old_arena_wl_heur :: \<open>arena \<Rightarrow>isasat \<Rightarrow> _\<close> where
  \<open>update_old_arena_wl_heur \<equiv> update_p\<close>

abbreviation update_occs_wl_heur :: \<open>occurences_ref \<Rightarrow>isasat \<Rightarrow> _\<close> where
  \<open>update_occs_wl_heur \<equiv> update_q\<close>
end
