theory IsaSAT_Arena_SML
imports IsaSAT_Arena Refine_Imperative_HOL.IICF
begin

sepref_definition isa_arena_length_code
  is \<open>uncurry isa_arena_length\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  supply arena_el_assn_alt_def[symmetric, simp] sum_uint64_assn[sepref_fr_rules]
  unfolding isa_arena_length_def
  by sepref

lemma isa_arena_length_code_refine[sepref_fr_rules]:
  \<open>(uncurry isa_arena_length_code, uncurry (RETURN \<circ>\<circ> arena_length))
  \<in> [uncurry arena_is_valid_clause_idx]\<^sub>a
    arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  using isa_arena_length_code.refine[FCOMP isa_arena_length_arena_length]
  unfolding hr_comp_assoc[symmetric] uncurry_def list_rel_compp
  by (simp add: arl_assn_comp)

sepref_definition isa_arena_length_fast_code
  is \<open>uncurry isa_arena_length\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  supply arena_el_assn_alt_def[symmetric, simp] sum_uint64_assn[sepref_fr_rules]
    minus_uint64_nat_assn[sepref_fr_rules]
  unfolding isa_arena_length_def SIZE_SHIFT_def fast_minus_def one_uint64_nat_def[symmetric]
  by sepref

lemma isa_arena_length_fast_code_refine[sepref_fr_rules]:
  \<open>(uncurry isa_arena_length_fast_code, uncurry (RETURN \<circ>\<circ> arena_length))
  \<in> [uncurry arena_is_valid_clause_idx]\<^sub>a
    arena_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  using isa_arena_length_fast_code.refine[FCOMP isa_arena_length_arena_length]
  unfolding hr_comp_assoc[symmetric] uncurry_def list_rel_compp
  by (simp add: arl_assn_comp)
sepref_definition isa_arena_lit_code
  is \<open>uncurry isa_arena_lit\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  supply arena_el_assn_alt_def[symmetric, simp] sum_uint64_assn[sepref_fr_rules]
  unfolding isa_arena_lit_def
  by sepref

lemma isa_arena_lit_code_refine[sepref_fr_rules]:
  \<open>(uncurry isa_arena_lit_code, uncurry (RETURN \<circ>\<circ> arena_lit))
  \<in> [uncurry arena_lit_pre]\<^sub>a
    arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  using isa_arena_lit_code.refine[FCOMP isa_arena_lit_arena_lit]
  unfolding hr_comp_assoc[symmetric] uncurry_def list_rel_compp
  by (simp add: arl_assn_comp)

sepref_definition (in-) isa_arena_lit_fast_code
  is \<open>uncurry isa_arena_lit\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  supply arena_el_assn_alt_def[symmetric, simp] sum_uint64_assn[sepref_fr_rules]
  unfolding isa_arena_lit_def
  by sepref

declare isa_arena_lit_fast_code.refine

lemma isa_arena_lit_fast_code_refine[sepref_fr_rules]:
  \<open>(uncurry isa_arena_lit_fast_code, uncurry (RETURN \<circ>\<circ> arena_lit))
  \<in> [uncurry arena_lit_pre]\<^sub>a
    arena_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  using isa_arena_lit_fast_code.refine[FCOMP isa_arena_lit_arena_lit]
  unfolding hr_comp_assoc[symmetric] uncurry_def list_rel_compp
  by (simp add: arl_assn_comp)

sepref_definition arena_status_code
  is \<open>uncurry isa_arena_status\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  supply arena_el_assn_alt_def[symmetric, simp] sum_uint64_assn[sepref_fr_rules]
  unfolding isa_arena_status_def
  by sepref

lemma isa_arena_status_refine[sepref_fr_rules]:
  \<open>(uncurry arena_status_code, uncurry (RETURN \<circ>\<circ> arena_status))
  \<in> [uncurry arena_is_valid_clause_vdom]\<^sub>a
    arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> status_assn\<close>
  using arena_status_code.refine[FCOMP isa_arena_status_arena_status]
  unfolding hr_comp_assoc[symmetric] uncurry_def list_rel_compp status_assn_alt_def
  by (simp add: arl_assn_comp)

sepref_definition swap_lits_code
  is \<open>uncurry3 isa_arena_swap\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (arl_assn uint32_assn)\<^sup>d  \<rightarrow>\<^sub>a arl_assn uint32_assn\<close>
  unfolding isa_arena_swap_def
  by sepref

lemma swap_lits_refine[sepref_fr_rules]:
  \<open>(uncurry3 swap_lits_code, uncurry3 (RETURN oooo swap_lits))
  \<in> [uncurry3 swap_lits_pre]\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a arena_assn\<^sup>d \<rightarrow> arena_assn\<close>
  using swap_lits_code.refine[FCOMP isa_arena_swap]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp)

sepref_definition isa_update_lbd_code
  is \<open>uncurry2 isa_update_lbd\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a uint32_assn\<^sup>k *\<^sub>a (arl_assn uint32_assn)\<^sup>d  \<rightarrow>\<^sub>a arl_assn uint32_assn\<close>
  unfolding isa_update_lbd_def
  by sepref


lemma update_lbd_hnr[sepref_fr_rules]:
  \<open>(uncurry2 isa_update_lbd_code, uncurry2 (RETURN ooo update_lbd))
  \<in> [update_lbd_pre]\<^sub>a nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a arena_assn\<^sup>d \<rightarrow> arena_assn\<close>
  using isa_update_lbd_code.refine[FCOMP isa_update_lbd]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)


sepref_definition (in -)isa_update_lbd_fast_code
  is \<open>uncurry2 isa_update_lbd\<close>
  :: \<open>uint64_nat_assn\<^sup>k *\<^sub>a uint32_assn\<^sup>k *\<^sub>a (arl_assn uint32_assn)\<^sup>d  \<rightarrow>\<^sub>a arl_assn uint32_assn\<close>
  supply LBD_SHIFT_hnr[sepref_fr_rules]
  unfolding isa_update_lbd_def
  by sepref

lemma update_lbd_fast_hnr[sepref_fr_rules]:
  \<open>(uncurry2 isa_update_lbd_fast_code, uncurry2 (RETURN ooo update_lbd))
  \<in> [update_lbd_pre]\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a arena_assn\<^sup>d \<rightarrow> arena_assn\<close>
  using isa_update_lbd_fast_code.refine[FCOMP isa_update_lbd]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)

sepref_definition isa_get_clause_LBD_code
  is \<open>uncurry isa_get_clause_LBD\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  unfolding isa_get_clause_LBD_def fast_minus_def[symmetric]
  by sepref

lemma isa_get_clause_LBD_code[sepref_fr_rules]:
  \<open>(uncurry isa_get_clause_LBD_code, uncurry (RETURN \<circ>\<circ> get_clause_LBD))
     \<in> [uncurry get_clause_LBD_pre]\<^sub>a arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  using isa_get_clause_LBD_code.refine[FCOMP isa_get_clause_LBD_get_clause_LBD]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)

sepref_definition isa_get_saved_pos_fast_code
  is \<open>uncurry isa_get_saved_pos\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  supply sum_uint64_assn[sepref_fr_rules]
  unfolding isa_get_saved_pos_def
  by sepref

lemma get_saved_pos_code:
  \<open>(uncurry isa_get_saved_pos_fast_code, uncurry (RETURN \<circ>\<circ> arena_pos))
     \<in> [uncurry get_saved_pos_pre]\<^sub>a arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  using isa_get_saved_pos_fast_code.refine[FCOMP isa_get_saved_pos_get_saved_pos]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)

sepref_definition isa_get_saved_pos_code
  is \<open>uncurry isa_get_saved_pos'\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  supply sum_uint64_assn[sepref_fr_rules]
  unfolding isa_get_saved_pos_def isa_get_saved_pos'_def
  by sepref
(* TODO check if we use this version anywhere *)
lemma get_saved_pos_code':
  \<open>(uncurry isa_get_saved_pos_code, uncurry (RETURN \<circ>\<circ> arena_pos))
     \<in> [uncurry get_saved_pos_pre]\<^sub>a arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  using isa_get_saved_pos_code.refine[FCOMP isa_get_saved_pos_get_saved_pos']
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)

sepref_definition isa_get_saved_pos_fast_code2
  is \<open>uncurry isa_get_saved_pos\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  supply sum_uint64_assn[sepref_fr_rules] POS_SHIFT_uint64_hnr[sepref_fr_rules]
  unfolding isa_get_saved_pos_def
  by sepref

lemma get_saved_pos_code2[sepref_fr_rules]:
  \<open>(uncurry isa_get_saved_pos_fast_code2, uncurry (RETURN \<circ>\<circ> arena_pos))
     \<in> [uncurry get_saved_pos_pre]\<^sub>a arena_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  using isa_get_saved_pos_fast_code2.refine[FCOMP isa_get_saved_pos_get_saved_pos]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)

sepref_definition isa_update_pos_code
  is \<open>uncurry2 isa_update_pos\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (arl_assn uint32_assn)\<^sup>d  \<rightarrow>\<^sub>a arl_assn uint32_assn\<close>
  supply minus_uint32_assn[sepref_fr_rules]
  unfolding isa_update_pos_def
  by sepref

lemma isa_update_pos_code_hnr[sepref_fr_rules]:
  \<open>(uncurry2 isa_update_pos_code, uncurry2 (RETURN ooo arena_update_pos))
  \<in> [isa_update_pos_pre]\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a arena_assn\<^sup>d \<rightarrow> arena_assn\<close>
  using isa_update_pos_code.refine[FCOMP isa_update_pos]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp isa_update_pos_pre_def)

sepref_definition mark_garbage_code
  is \<open>uncurry mark_garbage\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a arl_assn uint32_assn\<close>
  unfolding mark_garbage_def fast_minus_def[symmetric]
  by sepref

lemma mark_garbage_hnr[sepref_fr_rules]:
  \<open>(uncurry mark_garbage_code, uncurry (RETURN oo extra_information_mark_to_delete))
  \<in> [mark_garbage_pre]\<^sub>a  arena_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow> arena_assn\<close>
  using mark_garbage_code.refine[FCOMP isa_mark_garbage]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)

sepref_definition isa_arena_act_code
  is \<open>uncurry isa_arena_act\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  unfolding isa_arena_act_def ACTIVITY_SHIFT_def fast_minus_def[symmetric]
  by sepref

lemma isa_arena_act_code[sepref_fr_rules]:
  \<open>(uncurry isa_arena_act_code, uncurry (RETURN \<circ>\<circ> arena_act))
     \<in> [uncurry arena_act_pre]\<^sub>a arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  using isa_arena_act_code.refine[FCOMP isa_arena_act_arena_act]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)

sepref_definition isa_arena_incr_act_code
  is \<open>uncurry isa_arena_incr_act\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a (arl_assn uint32_assn)\<close>
  unfolding isa_arena_incr_act_def ACTIVITY_SHIFT_def fast_minus_def
  by sepref

lemma isa_arena_incr_act_code[sepref_fr_rules]:
  \<open>(uncurry isa_arena_incr_act_code, uncurry (RETURN \<circ>\<circ> arena_incr_act))
     \<in> [uncurry arena_act_pre]\<^sub>a arena_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow> arena_assn\<close>
  using isa_arena_incr_act_code.refine[FCOMP isa_arena_incr_act_arena_incr_act]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)

sepref_definition isa_arena_decr_act_code
  is \<open>uncurry isa_arena_decr_act\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a (arl_assn uint32_assn)\<close>
  unfolding isa_arena_decr_act_def ACTIVITY_SHIFT_def fast_minus_def
  by sepref

lemma isa_arena_decr_act_code[sepref_fr_rules]:
  \<open>(uncurry isa_arena_decr_act_code, uncurry (RETURN \<circ>\<circ> arena_decr_act))
     \<in> [uncurry arena_act_pre]\<^sub>a arena_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow> arena_assn\<close>
  using isa_arena_decr_act_code.refine[FCOMP isa_arena_decr_act_arena_decr_act]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)


sepref_definition isa_arena_decr_act_fast_code
  is \<open>uncurry isa_arena_decr_act\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a (arl_assn uint32_assn)\<close>
  unfolding isa_arena_decr_act_def
  three_uint32_def[symmetric] ACTIVITY_SHIFT_hnr[sepref_fr_rules]
  by sepref

lemma isa_arena_decr_act_fast_code[sepref_fr_rules]:
  \<open>(uncurry isa_arena_decr_act_fast_code, uncurry (RETURN \<circ>\<circ> arena_decr_act))
     \<in> [uncurry arena_act_pre]\<^sub>a arena_assn\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> arena_assn\<close>
  using isa_arena_decr_act_fast_code.refine[FCOMP isa_arena_decr_act_arena_decr_act]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)

sepref_definition isa_mark_used_code
  is \<open>uncurry isa_mark_used\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a (arl_assn uint32_assn)\<close>
  unfolding isa_mark_used_def ACTIVITY_SHIFT_def fast_minus_def[symmetric]
  by sepref

lemma isa_mark_used_code[sepref_fr_rules]:
  \<open>(uncurry isa_mark_used_code, uncurry (RETURN \<circ>\<circ> mark_used))
     \<in> [uncurry arena_act_pre]\<^sub>a arena_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow> arena_assn\<close>
  using isa_mark_used_code.refine[FCOMP isa_mark_used_mark_used]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)


sepref_definition isa_mark_used_fast_code
  is \<open>uncurry isa_mark_used\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a (arl_assn uint32_assn)\<close>
  supply four_uint32_hnr[sepref_fr_rules] STATUS_SHIFT_hnr[sepref_fr_rules]
  unfolding isa_mark_used_def four_uint32_def[symmetric]
  by sepref

lemma isa_mark_used_fast_code[sepref_fr_rules]:
  \<open>(uncurry isa_mark_used_fast_code, uncurry (RETURN \<circ>\<circ> mark_used))
     \<in> [uncurry arena_act_pre]\<^sub>a arena_assn\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> arena_assn\<close>
  using isa_mark_used_fast_code.refine[FCOMP isa_mark_used_mark_used]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)

sepref_definition isa_mark_unused_code
  is \<open>uncurry isa_mark_unused\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a (arl_assn uint32_assn)\<close>
  unfolding isa_mark_unused_def ACTIVITY_SHIFT_def fast_minus_def[symmetric]
  by sepref

lemma isa_mark_unused_code[sepref_fr_rules]:
  \<open>(uncurry isa_mark_unused_code, uncurry (RETURN \<circ>\<circ> mark_unused))
     \<in> [uncurry arena_act_pre]\<^sub>a arena_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow> arena_assn\<close>
  using isa_mark_unused_code.refine[FCOMP isa_mark_unused_mark_unused]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)

sepref_definition isa_mark_unused_fast_code
  is \<open>uncurry isa_mark_unused\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a (arl_assn uint32_assn)\<close>
  supply STATUS_SHIFT_hnr[sepref_fr_rules]
  unfolding isa_mark_unused_def ACTIVITY_SHIFT_def fast_minus_def[symmetric]
  by sepref


lemma isa_mark_unused_fast_code[sepref_fr_rules]:
  \<open>(uncurry isa_mark_unused_fast_code, uncurry (RETURN \<circ>\<circ> mark_unused))
     \<in> [uncurry arena_act_pre]\<^sub>a arena_assn\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> arena_assn\<close>
  using isa_mark_unused_fast_code.refine[FCOMP isa_mark_unused_mark_unused]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)

sepref_definition isa_marked_as_used_code
  is \<open>uncurry isa_marked_as_used\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply op_eq_uint32[sepref_fr_rules]
  unfolding isa_marked_as_used_def fast_minus_def[symmetric]
  by sepref



lemma isa_marked_as_used_code[sepref_fr_rules]:
  \<open>(uncurry isa_marked_as_used_code, uncurry (RETURN \<circ>\<circ> marked_as_used))
     \<in> [uncurry marked_as_used_pre]\<^sub>a arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> bool_assn\<close>
  using isa_marked_as_used_code.refine[FCOMP isa_marked_as_used_marked_as_used]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)



sepref_definition (in -) isa_arena_incr_act_fast_code
  is \<open>uncurry isa_arena_incr_act\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a (arl_assn uint32_assn)\<close>
  supply ACTIVITY_SHIFT_hnr[sepref_fr_rules]
  unfolding isa_arena_incr_act_def
  by sepref

lemma isa_arena_incr_act_fast_code[sepref_fr_rules]:
  \<open>(uncurry isa_arena_incr_act_fast_code, uncurry (RETURN \<circ>\<circ> arena_incr_act))
     \<in> [uncurry arena_act_pre]\<^sub>a arena_assn\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> arena_assn\<close>
  using isa_arena_incr_act_fast_code.refine[FCOMP isa_arena_incr_act_arena_incr_act]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)

sepref_definition arena_status_fast_code
  is \<open>uncurry isa_arena_status\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  supply arena_el_assn_alt_def[symmetric, simp] sum_uint64_assn[sepref_fr_rules]
    three_uint32_hnr[sepref_fr_rules] STATUS_SHIFT_hnr[sepref_fr_rules]
  unfolding isa_arena_status_def three_uint32_def[symmetric]
  by sepref

lemma isa_arena_status_fast_hnr[sepref_fr_rules]:
  \<open>(uncurry arena_status_fast_code, uncurry (RETURN \<circ>\<circ> arena_status))
  \<in> [uncurry arena_is_valid_clause_vdom]\<^sub>a
    arena_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> status_assn\<close>
  using arena_status_fast_code.refine[FCOMP isa_arena_status_arena_status]
  unfolding hr_comp_assoc[symmetric] uncurry_def list_rel_compp status_assn_alt_def
  by (simp add: arl_assn_comp)

sepref_definition isa_update_pos_fast_code
  is \<open>uncurry2 isa_update_pos\<close>
  :: \<open>uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a (arl_assn uint32_assn)\<^sup>d  \<rightarrow>\<^sub>a arl_assn uint32_assn\<close>
  supply minus_uint32_assn[sepref_fr_rules] POS_SHIFT_uint64_hnr[sepref_fr_rules] minus_uint64_assn[sepref_fr_rules]
  unfolding isa_update_pos_def  uint32_nat_assn_minus[sepref_fr_rules] two_uint64_nat_def[symmetric]
  by sepref

lemma isa_update_pos_code_fast_hnr[sepref_fr_rules]:
  \<open>(uncurry2 isa_update_pos_fast_code, uncurry2 (RETURN ooo arena_update_pos))
  \<in> [isa_update_pos_pre]\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a arena_assn\<^sup>d \<rightarrow> arena_assn\<close>
  using isa_update_pos_fast_code.refine[FCOMP isa_update_pos]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp isa_update_pos_pre_def)

declare isa_update_pos_fast_code.refine[sepref_fr_rules]
  arena_status_fast_code.refine[sepref_fr_rules]

end