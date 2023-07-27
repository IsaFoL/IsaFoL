theory IsaSAT_Bump_Heuristics_State_LLVM
  imports IsaSAT_Bump_Heuristics_State
    IsaSAT_VMTF_Setup_LLVM
    Tuple4_LLVM
    IsaSAT_ACIDS_LLVM
begin
hide_const (open) NEMonad.ASSERT NEMonad.RETURN

type_synonym bump_heuristics_assn = \<open>
  ((32 word ptr \<times> 32 word ptr \<times> 32 word ptr \<times> 32 word ptr \<times> 64 word ptr \<times> 32 word) \<times> 64 word,
     (64 word \<times> 32 word \<times> 32 word) ptr \<times> 64 word \<times> 32 word \<times> 32 word \<times> 32 word,
     1 word, (64 word \<times> 64 word \<times> 32 word ptr) \<times> 1 word ptr) tuple4\<close>

definition heuristic_bump_assn :: \<open>bump_heuristics \<Rightarrow> bump_heuristics_assn \<Rightarrow> _\<close> where
  \<open>heuristic_bump_assn = tuple4_assn acids_assn2 vmtf_assn bool1_assn distinct_atoms_assn\<close>

definition bottom_atom where
  \<open>bottom_atom = 0\<close>

definition bottom_vmtf :: \<open>vmtf\<close> where
  \<open>bottom_vmtf = ((replicate 0 (VMTF_Node 0 None None), 0, bottom_atom, bottom_atom, None))\<close>


definition extract_bump_stable where
  \<open>extract_bump_stable = tuple4_state_ops.remove_a empty_acids\<close>
definition extract_bump_focused where
  \<open>extract_bump_focused = tuple4_state_ops.remove_b bottom_vmtf\<close>

lemma [sepref_fr_rules]: \<open>(uncurry0 (Mreturn 0), uncurry0 (RETURN bottom_atom)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a atom_assn\<close>
  unfolding bottom_atom_def
  apply sepref_to_hoare
  apply vcg
  apply (auto simp: atom_rel_def unat_rel_def unat.rel_def br_def entails_def ENTAILS_def)
  by (smt (verit, best) pure_true_conv rel_simps(51) sep.add_0)

sepref_def bottom_vmtf_code
  is \<open>uncurry0 (RETURN bottom_vmtf)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a vmtf_assn\<close>
  unfolding bottom_vmtf_def
  apply (rewrite in \<open>((\<hole>, _, _, _, _))\<close> array_fold_custom_replicate)
  unfolding
   atom.fold_option array_fold_custom_replicate vmtf_assn_def
    al_fold_custom_empty[where 'l=64]
  apply (rewrite at 0 in \<open>VMTF_Node \<hole>\<close> unat_const_fold[where 'a=64])
  apply (rewrite at \<open>(_, \<hole>, _, _)\<close> unat_const_fold[where 'a=64])
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

schematic_goal free_vmtf_remove_assn[sepref_frame_free_rules]: \<open>MK_FREE vmtf_assn ?a\<close>
  unfolding vmtf_assn_def
  by synthesize_free

sepref_def free_vmtf_remove
  is \<open>mop_free\<close>
  :: \<open>vmtf_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

sepref_def bottom_focused
  is \<open>uncurry0 (RETURN False)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref
sepref_def free_focused
  is \<open>mop_free\<close>
  :: \<open>bool1_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
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
sepref_def free_atms_hash_code
  is \<open>mop_free\<close>
  :: \<open>distinct_atoms_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

lemma free_vmtf_assn_assn2: \<open>MK_FREE vmtf_assn free_vmtf_remove\<close>
  unfolding free_vmtf_remove_def
  by (rule back_subst[of \<open>MK_FREE vmtf_assn\<close>, OF free_vmtf_remove_assn])
    (auto intro!: ext)

schematic_goal free_focused_assn: \<open>MK_FREE bool1_assn ?a\<close>
  unfolding vmtf_assn_def
  by synthesize_free
schematic_goal free_distinct_atoms_assn: \<open>MK_FREE distinct_atoms_assn ?a\<close>
  by synthesize_free
 
lemma free_focused_assn2: \<open>MK_FREE bool1_assn free_focused\<close>
  unfolding free_focused_def
  by (rule back_subst[of \<open>MK_FREE bool1_assn\<close>, OF free_focused_assn])
    (auto intro!: ext)

lemma free_distinct_atoms_assn2: \<open>MK_FREE (distinct_atoms_assn) free_atms_hash_code\<close>
  unfolding free_atms_hash_code_def
  by (rule back_subst[of \<open>MK_FREE distinct_atoms_assn\<close>, OF free_distinct_atoms_assn])
    (auto intro!: ext)

global_interpretation Bump_Heur: tuple4_state where
  a_assn = acids_assn2 and
  b_assn = vmtf_assn and
  c_assn = bool1_assn and
  d_assn = distinct_atoms_assn and
  a_default = empty_acids and
  a = \<open>empty_acids_code\<close> and
  a_free = free_acids and
  b_default = bottom_vmtf and
  b = \<open>bottom_vmtf_code\<close> and
  b_free = free_vmtf_remove and
  c_default = False and
  c = \<open>bottom_focused\<close> and
  c_free = free_focused and
  d_default = \<open>bottom_atms_hash\<close> and
  d = \<open>bottom_atms_hash_code\<close> and
  d_free = \<open>free_atms_hash_code\<close>
  rewrites
  \<open>Bump_Heur.tuple4_int_assn \<equiv> heuristic_bump_assn\<close>and
  \<open>Bump_Heur.remove_a \<equiv> extract_bump_stable\<close> and
  \<open>Bump_Heur.remove_b \<equiv> extract_bump_focused\<close> and
  \<open>Bump_Heur.remove_c \<equiv> extract_bump_is_focused\<close> and
  \<open>Bump_Heur.remove_d \<equiv> extract_bump_atms_to_bump\<close>
  apply unfold_locales
  apply (rule bottom_vmtf_code.refine bottom_focused.refine empty_acids_code.refine
    bottom_atms_hash_code.refine free_vmtf_assn_assn2 free_focused_assn2 free_acids_assn2'
    free_distinct_atoms_assn2)+
  subgoal unfolding heuristic_bump_assn_def tuple4_state_ops.tuple4_int_assn_def by auto
  subgoal unfolding extract_bump_stable_def by auto
  subgoal unfolding extract_bump_focused_def by auto
  subgoal unfolding extract_bump_is_focused_def by auto
  subgoal unfolding extract_bump_atms_to_bump_def by auto
  done

lemmas [unfolded Tuple4_LLVM.inline_direct_return_node_case, llvm_code] =
  Bump_Heur.code_rules[unfolded Mreturn_comp_Tuple4]

lemmas [sepref_fr_rules] =
  Bump_Heur.separation_rules

(*The if/then/else is a work-around for sepref...*)
lemma switch_bump_heur_alt_def:
  \<open>RETURN o switch_bump_heur = (\<lambda>x. case x of Bump_Heuristics hstable focused foc b \<Rightarrow> do {
  f \<leftarrow> RETURN (\<not>foc);
  mop_free foc;
  RETURN (Bump_Heuristics hstable focused (f) b)})\<close>
  by (auto intro!: ext simp: mop_free_def switch_bump_heur_def split: bump_heuristics_splits)

sepref_def switch_bump_heur_code
  is \<open>RETURN o switch_bump_heur\<close>
  :: \<open>heuristic_bump_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_bump_assn\<close>
  unfolding switch_bump_heur_alt_def
  by sepref

end
