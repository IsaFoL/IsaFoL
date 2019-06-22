theory IsaSAT_Arena_SML
  imports IsaSAT_Arena IsaSAT_Literals_SML Watched_Literals.IICF_Array_List64
begin


abbreviation arena_el_assn :: "arena_el \<Rightarrow> uint32 \<Rightarrow> assn" where
  \<open>arena_el_assn \<equiv> hr_comp uint32_nat_assn arena_el_rel\<close>

abbreviation arena_assn :: "arena_el list \<Rightarrow> uint32 array_list \<Rightarrow> assn" where
  \<open>arena_assn \<equiv> arl_assn arena_el_assn\<close>

abbreviation arena_fast_assn :: "arena_el list \<Rightarrow> uint32 array_list64 \<Rightarrow> assn" where
  \<open>arena_fast_assn \<equiv> arl64_assn arena_el_assn\<close>

abbreviation status_assn where
  \<open>status_assn \<equiv> hr_comp uint32_nat_assn status_rel\<close>

abbreviation clause_status_assn where
  \<open>clause_status_assn \<equiv> (id_assn :: clause_status \<Rightarrow> _)\<close>

lemma IRRED_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return IRRED), uncurry0 (RETURN IRRED)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a clause_status_assn\<close>
  by sepref_to_hoare sep_auto

lemma LEARNED_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return LEARNED), uncurry0 (RETURN LEARNED)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a clause_status_assn\<close>
  by sepref_to_hoare sep_auto

lemma DELETED_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return DELETED), uncurry0 (RETURN DELETED)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a clause_status_assn\<close>
  by sepref_to_hoare sep_auto

lemma ACTIVITY_SHIFT_hnr:
  \<open>(uncurry0 (return 3), uncurry0 (RETURN ACTIVITY_SHIFT) ) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: ACTIVITY_SHIFT_def uint64_nat_rel_def br_def)
lemma STATUS_SHIFT_hnr:
  \<open>(uncurry0 (return 4), uncurry0 (RETURN STATUS_SHIFT) ) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: STATUS_SHIFT_def uint64_nat_rel_def br_def)

lemma [sepref_fr_rules]:
  \<open>(uncurry0 (return 1), uncurry0 (RETURN SIZE_SHIFT)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: SIZE_SHIFT_def)

lemma [sepref_fr_rules]:
  \<open>(return o id, RETURN o xarena_length) \<in> [is_Size]\<^sub>a arena_el_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: SIZE_SHIFT_def uint32_nat_rel_def
    arena_el_rel_def br_def hr_comp_def split: arena_el.splits)

lemma (in -) POS_SHIFT_uint64_hnr:
  \<open>(uncurry0 (return 5), uncurry0 (RETURN POS_SHIFT)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: POS_SHIFT_def uint64_nat_rel_def br_def)

lemma nat_of_uint64_eq_2_iff[simp]: \<open>nat_of_uint64 c = 2 \<longleftrightarrow> c = 2\<close>
  using word_nat_of_uint64_Rep_inject by fastforce

lemma arena_el_assn_alt_def:
  \<open>arena_el_assn = hr_comp uint32_assn (uint32_nat_rel O arena_el_rel)\<close>
  by (auto simp: hr_comp_assoc[symmetric])

lemma arena_el_comp: \<open>hn_val (uint32_nat_rel O arena_el_rel) = hn_ctxt arena_el_assn\<close>
  by (auto simp: hn_ctxt_def arena_el_assn_alt_def)

lemma status_assn_hnr_eq[sepref_fr_rules]:
  \<open>(uncurry (return oo (=)), uncurry (RETURN oo (=))) \<in> status_assn\<^sup>k *\<^sub>a status_assn\<^sup>k \<rightarrow>\<^sub>a
    bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: status_rel_def hr_comp_def uint32_nat_rel_def br_def
    nat_of_uint32_0_iff nat_of_uint32_Suc03_iff nat_of_uint32_013_neq)

lemma IRRED_status_assn[sepref_fr_rules]:
  \<open>(uncurry0 (return 0), uncurry0 (RETURN IRRED)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a status_assn\<close>
  by (sepref_to_hoare) (sep_auto simp: status_rel_def hr_comp_def uint32_nat_rel_def br_def)

lemma LEARNED_status_assn[sepref_fr_rules]:
  \<open>(uncurry0 (return 1), uncurry0 (RETURN LEARNED)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a status_assn\<close>
  by (sepref_to_hoare) (sep_auto simp: status_rel_def hr_comp_def uint32_nat_rel_def br_def)

lemma DELETED_status_assn[sepref_fr_rules]:
  \<open>(uncurry0 (return 3), uncurry0 (RETURN DELETED)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a status_assn\<close>
  by (sepref_to_hoare) (sep_auto simp: status_rel_def hr_comp_def uint32_nat_rel_def br_def
    nat_of_uint32_Suc03_iff)

lemma status_assn_alt_def:
  \<open>status_assn = pure (uint32_nat_rel O status_rel)\<close>
  unfolding hr_comp_pure by simp

lemma [sepref_fr_rules]:
  \<open>(uncurry0 (return 2), uncurry0 (RETURN LBD_SHIFT)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: LBD_SHIFT_def)

lemma [sepref_fr_rules]:
  \<open>(uncurry0 (return 4), uncurry0 (RETURN STATUS_SHIFT)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: STATUS_SHIFT_def)

lemma (in -) LBD_SHIFT_hnr:
  \<open>(uncurry0 (return 2), uncurry0 (RETURN LBD_SHIFT) ) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: LBD_SHIFT_def uint64_nat_rel_def br_def)

lemma MAX_LENGTH_SHORT_CLAUSE_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return 4), uncurry0 (RETURN MAX_LENGTH_SHORT_CLAUSE)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint64_nat_rel_def br_def)

definition four_uint32 where \<open>four_uint32 = (4 :: uint32)\<close>

lemma four_uint32_hnr:
  \<open>(uncurry0 (return 4), uncurry0 (RETURN (four_uint32 :: uint32)) ) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def four_uint32_def)

lemma [sepref_fr_rules]:
  \<open>(uncurry0 (return 5), uncurry0 (RETURN POS_SHIFT)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: SHIFTS_def)

lemma [sepref_fr_rules]:
  \<open>(return o id, RETURN o xarena_lit) \<in> [is_Lit]\<^sub>a arena_el_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  by sepref_to_hoare (sep_auto simp: SIZE_SHIFT_def uint32_nat_rel_def unat_lit_rel_def
    arena_el_rel_def br_def hr_comp_def split: arena_el.splits)

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
  using isa_arena_length_code.refine[FCOMP isa_arena_length_arena_length[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] uncurry_def list_rel_compp
  by (simp add: arl_assn_comp)

sepref_definition isa_arena_length_fast_code
  is \<open>uncurry isa_arena_length\<close>
  :: \<open>(arl64_assn uint32_assn)\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  supply arena_el_assn_alt_def[symmetric, simp] sum_uint64_assn[sepref_fr_rules]
    minus_uint64_nat_assn[sepref_fr_rules]
  unfolding isa_arena_length_def SIZE_SHIFT_def fast_minus_def one_uint64_nat_def[symmetric]
  by sepref

lemma isa_arena_length_fast_code_refine[sepref_fr_rules]:
  \<open>(uncurry isa_arena_length_fast_code, uncurry (RETURN \<circ>\<circ> arena_length))
  \<in> [uncurry arena_is_valid_clause_idx]\<^sub>a
    arena_fast_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  using isa_arena_length_fast_code.refine[FCOMP isa_arena_length_arena_length[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] uncurry_def list_rel_compp
  by (simp add: arl64_assn_comp)

sepref_definition isa_arena_length_fast_code2
  is \<open>uncurry isa_arena_length\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  supply arena_el_assn_alt_def[symmetric, simp] sum_uint64_assn[sepref_fr_rules]
    minus_uint64_nat_assn[sepref_fr_rules]
  unfolding isa_arena_length_def SIZE_SHIFT_def fast_minus_def one_uint64_nat_def[symmetric]
  by sepref

lemma isa_arena_length_fast_code2_refine[sepref_fr_rules]:
  \<open>(uncurry isa_arena_length_fast_code2, uncurry (RETURN \<circ>\<circ> arena_length))
  \<in> [uncurry arena_is_valid_clause_idx]\<^sub>a
    arena_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  using isa_arena_length_fast_code2.refine[FCOMP isa_arena_length_arena_length[unfolded convert_fref]]
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
  using isa_arena_lit_code.refine[FCOMP isa_arena_lit_arena_lit[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] uncurry_def list_rel_compp
  by (simp add: arl_assn_comp)

sepref_definition (in-) isa_arena_lit_fast_code
  is \<open>uncurry isa_arena_lit\<close>
  :: \<open>(arl64_assn uint32_assn)\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  supply arena_el_assn_alt_def[symmetric, simp] sum_uint64_assn[sepref_fr_rules]
  unfolding isa_arena_lit_def
  by sepref

declare isa_arena_lit_fast_code.refine

lemma isa_arena_lit_fast_code_refine[sepref_fr_rules]:
  \<open>(uncurry isa_arena_lit_fast_code, uncurry (RETURN \<circ>\<circ> arena_lit))
  \<in> [uncurry arena_lit_pre]\<^sub>a
    arena_fast_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  using isa_arena_lit_fast_code.refine[FCOMP isa_arena_lit_arena_lit[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] uncurry_def list_rel_compp
  by (simp add: arl64_assn_comp)


sepref_definition (in-) isa_arena_lit_fast_code2
  is \<open>uncurry isa_arena_lit\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  supply arena_el_assn_alt_def[symmetric, simp] sum_uint64_assn[sepref_fr_rules]
  unfolding isa_arena_lit_def
  by sepref

declare isa_arena_lit_fast_code2.refine

lemma isa_arena_lit_fast_code2_refine[sepref_fr_rules]:
  \<open>(uncurry isa_arena_lit_fast_code2, uncurry (RETURN \<circ>\<circ> arena_lit))
  \<in> [uncurry arena_lit_pre]\<^sub>a
    arena_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  using isa_arena_lit_fast_code2.refine[FCOMP isa_arena_lit_arena_lit[unfolded convert_fref]]
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
  using arena_status_code.refine[FCOMP isa_arena_status_arena_status[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] uncurry_def list_rel_compp status_assn_alt_def
  by (simp add: arl_assn_comp)


sepref_definition swap_lits_code
  is \<open>Sepref_Misc.uncurry3 isa_arena_swap\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (arl_assn uint32_assn)\<^sup>d  \<rightarrow>\<^sub>a arl_assn uint32_assn\<close>
  unfolding isa_arena_swap_def WB_More_Refinement_List.swap_def IICF_List.swap_def[symmetric]
  by sepref

lemma swap_lits_refine[sepref_fr_rules]:
  \<open>(uncurry3 swap_lits_code, uncurry3 (RETURN oooo swap_lits))
  \<in> [uncurry3 swap_lits_pre]\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a arena_assn\<^sup>d \<rightarrow> arena_assn\<close>
  using swap_lits_code.refine[FCOMP isa_arena_swap[unfolded convert_fref]]
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
  using isa_update_lbd_code.refine[FCOMP isa_update_lbd[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)


sepref_definition (in -)isa_update_lbd_fast_code
  is \<open>uncurry2 isa_update_lbd\<close>
  :: \<open>uint64_nat_assn\<^sup>k *\<^sub>a uint32_assn\<^sup>k *\<^sub>a (arl64_assn uint32_assn)\<^sup>d  \<rightarrow>\<^sub>a arl64_assn uint32_assn\<close>
  supply LBD_SHIFT_hnr[sepref_fr_rules]
  unfolding isa_update_lbd_def
  by sepref

lemma update_lbd_fast_hnr[sepref_fr_rules]:
  \<open>(uncurry2 isa_update_lbd_fast_code, uncurry2 (RETURN ooo update_lbd))
  \<in> [update_lbd_pre]\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>d \<rightarrow> arena_fast_assn\<close>
  using isa_update_lbd_fast_code.refine[FCOMP isa_update_lbd[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl64_assn_comp update_lbd_pre_def)

sepref_definition (in -)isa_update_lbd_fast_code2
  is \<open>uncurry2 isa_update_lbd\<close>
  :: \<open>uint64_nat_assn\<^sup>k *\<^sub>a uint32_assn\<^sup>k *\<^sub>a (arl_assn uint32_assn)\<^sup>d  \<rightarrow>\<^sub>a arl_assn uint32_assn\<close>
  supply LBD_SHIFT_hnr[sepref_fr_rules]
  unfolding isa_update_lbd_def
  by sepref

lemma update_lbd_fast_hnr2[sepref_fr_rules]:
  \<open>(uncurry2 isa_update_lbd_fast_code2, uncurry2 (RETURN ooo update_lbd))
  \<in> [update_lbd_pre]\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a arena_assn\<^sup>d \<rightarrow> arena_assn\<close>
  using isa_update_lbd_fast_code2.refine[FCOMP isa_update_lbd[unfolded convert_fref]]
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
  using isa_get_clause_LBD_code.refine[FCOMP isa_get_clause_LBD_get_clause_LBD[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)

sepref_definition isa_get_saved_pos_fast_code
  is \<open>uncurry isa_get_saved_pos\<close>
  :: \<open>(arl64_assn uint32_assn)\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  supply sum_uint64_assn[sepref_fr_rules] POS_SHIFT_uint64_hnr[sepref_fr_rules]
  unfolding isa_get_saved_pos_def
  by sepref

lemma get_saved_pos_fast_code[sepref_fr_rules]:
  \<open>(uncurry isa_get_saved_pos_fast_code, uncurry (RETURN \<circ>\<circ> arena_pos))
     \<in> [uncurry get_saved_pos_pre]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  using isa_get_saved_pos_fast_code.refine[FCOMP isa_get_saved_pos_get_saved_pos[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl64_assn_comp update_lbd_pre_def)

sepref_definition isa_get_saved_pos_code
  is \<open>uncurry isa_get_saved_pos\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  supply sum_uint64_assn[sepref_fr_rules]
  unfolding isa_get_saved_pos_def POS_SHIFT_def
  by sepref

lemma get_saved_pos_code[sepref_fr_rules]:
  \<open>(uncurry isa_get_saved_pos_code, uncurry (RETURN \<circ>\<circ> arena_pos))
     \<in> [uncurry get_saved_pos_pre]\<^sub>a arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  using isa_get_saved_pos_code.refine[FCOMP isa_get_saved_pos_get_saved_pos[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)

sepref_definition isa_get_saved_pos_code'
  is \<open>uncurry isa_get_saved_pos'\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  supply sum_uint64_assn[sepref_fr_rules]
  unfolding isa_get_saved_pos_def isa_get_saved_pos'_def
  by sepref
(* TODO check if we use this version anywhere *)
lemma get_saved_pos_code':
\<open>(uncurry isa_get_saved_pos_code', uncurry (RETURN \<circ>\<circ> arena_pos))
     \<in> [uncurry get_saved_pos_pre]\<^sub>a arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  using isa_get_saved_pos_code'.refine[FCOMP isa_get_saved_pos_get_saved_pos'[unfolded convert_fref]]
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
  using isa_get_saved_pos_fast_code2.refine[FCOMP isa_get_saved_pos_get_saved_pos[unfolded convert_fref]]
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
  using isa_update_pos_code.refine[FCOMP isa_update_pos[unfolded convert_fref]]
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
  using mark_garbage_code.refine[FCOMP isa_mark_garbage[unfolded convert_fref]]
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
  using isa_arena_act_code.refine[FCOMP isa_arena_act_arena_act[unfolded convert_fref]]
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
  using isa_arena_incr_act_code.refine[FCOMP isa_arena_incr_act_arena_incr_act[unfolded convert_fref]]
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
  using isa_arena_decr_act_code.refine[FCOMP isa_arena_decr_act_arena_decr_act[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)


sepref_definition isa_arena_decr_act_fast_code
  is \<open>uncurry isa_arena_decr_act\<close>
  :: \<open>(arl64_assn uint32_assn)\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a (arl64_assn uint32_assn)\<close>
  unfolding isa_arena_decr_act_def
  three_uint32_def[symmetric] ACTIVITY_SHIFT_hnr[sepref_fr_rules]
  by sepref

lemma isa_arena_decr_act_fast_code[sepref_fr_rules]:
  \<open>(uncurry isa_arena_decr_act_fast_code, uncurry (RETURN \<circ>\<circ> arena_decr_act))
     \<in> [uncurry arena_act_pre]\<^sub>a arena_fast_assn\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> arena_fast_assn\<close>
  using isa_arena_decr_act_fast_code.refine[FCOMP isa_arena_decr_act_arena_decr_act[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl64_assn_comp update_lbd_pre_def)

sepref_definition isa_mark_used_code
  is \<open>uncurry isa_mark_used\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a (arl_assn uint32_assn)\<close>
  unfolding isa_mark_used_def ACTIVITY_SHIFT_def fast_minus_def[symmetric]
  by sepref

lemma isa_mark_used_code[sepref_fr_rules]:
  \<open>(uncurry isa_mark_used_code, uncurry (RETURN \<circ>\<circ> mark_used))
     \<in> [uncurry arena_act_pre]\<^sub>a arena_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow> arena_assn\<close>
  using isa_mark_used_code.refine[FCOMP isa_mark_used_mark_used[unfolded convert_fref]]
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
  using isa_mark_used_fast_code.refine[FCOMP isa_mark_used_mark_used[unfolded convert_fref]]
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
  using isa_mark_unused_code.refine[FCOMP isa_mark_unused_mark_unused[unfolded convert_fref]]
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
  using isa_mark_unused_fast_code.refine[FCOMP isa_mark_unused_mark_unused[unfolded convert_fref]]
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
  using isa_marked_as_used_code.refine[FCOMP isa_marked_as_used_marked_as_used[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)



sepref_definition (in -) isa_arena_incr_act_fast_code
  is \<open>uncurry isa_arena_incr_act\<close>
  :: \<open>(arl64_assn uint32_assn)\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a (arl64_assn uint32_assn)\<close>
  supply ACTIVITY_SHIFT_hnr[sepref_fr_rules]
  unfolding isa_arena_incr_act_def
  by sepref

lemma isa_arena_incr_act_fast_code[sepref_fr_rules]:
  \<open>(uncurry isa_arena_incr_act_fast_code, uncurry (RETURN \<circ>\<circ> arena_incr_act))
     \<in> [uncurry arena_act_pre]\<^sub>a arena_fast_assn\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> arena_fast_assn\<close>
  using isa_arena_incr_act_fast_code.refine[FCOMP isa_arena_incr_act_arena_incr_act[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl64_assn_comp update_lbd_pre_def)

sepref_definition arena_status_fast_code
  is \<open>uncurry isa_arena_status\<close>
  :: \<open>(arl64_assn uint32_assn)\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  supply arena_el_assn_alt_def[symmetric, simp] sum_uint64_assn[sepref_fr_rules]
    three_uint32_hnr[sepref_fr_rules] STATUS_SHIFT_hnr[sepref_fr_rules]
  unfolding isa_arena_status_def three_uint32_def[symmetric]
  by sepref

lemma isa_arena_status_fast_hnr[sepref_fr_rules]:
  \<open>(uncurry arena_status_fast_code, uncurry (RETURN \<circ>\<circ> arena_status))
  \<in> [uncurry arena_is_valid_clause_vdom]\<^sub>a
    arena_fast_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> status_assn\<close>
  using arena_status_fast_code.refine[FCOMP isa_arena_status_arena_status[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] uncurry_def list_rel_compp status_assn_alt_def
  by (simp add: arl64_assn_comp)

context
  notes [fcomp_norm_unfold] = arl64_assn_def[symmetric] arl64_assn_comp'
  notes [intro!] = hfrefI hn_refineI[THEN hn_refine_preI]
  notes [simp] = pure_def hn_ctxt_def invalid_assn_def
begin

definition arl64_get2 :: "'a::heap array_list64 \<Rightarrow> nat \<Rightarrow> 'a Heap" where
  "arl64_get2 \<equiv> \<lambda>(a,n) i. Array.nth a i"
thm arl64_get_hnr_aux
lemma arl64_get2_hnr_aux: "(uncurry arl64_get2,uncurry (RETURN oo op_list_get)) \<in> [\<lambda>(l,i). i<length l]\<^sub>a (is_array_list64\<^sup>k *\<^sub>a nat_assn\<^sup>k) \<rightarrow> id_assn"
    by sepref_to_hoare (sep_auto simp: arl64_get2_def is_array_list64_def)

  sepref_decl_impl arl64_get2: arl64_get2_hnr_aux .
end

sepref_definition arena_status_fast_code2
  is \<open>uncurry isa_arena_status\<close>
  :: \<open>(arl64_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  supply arena_el_assn_alt_def[symmetric, simp] sum_uint64_assn[sepref_fr_rules]
    three_uint32_hnr[sepref_fr_rules]
  unfolding isa_arena_status_def STATUS_SHIFT_def fast_minus_def
  by sepref

lemma isa_arena_status_fast_hnr2[sepref_fr_rules]:
  \<open>(uncurry arena_status_fast_code2, uncurry (RETURN \<circ>\<circ> arena_status))
  \<in> [uncurry arena_is_valid_clause_vdom]\<^sub>a
    arena_fast_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> status_assn\<close>
  using arena_status_fast_code2.refine[FCOMP isa_arena_status_arena_status[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] uncurry_def list_rel_compp status_assn_alt_def
  by (simp add: arl64_assn_comp)

sepref_definition isa_update_pos_fast_code
  is \<open>uncurry2 isa_update_pos\<close>
  :: \<open>uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a (arl64_assn uint32_assn)\<^sup>d  \<rightarrow>\<^sub>a arl64_assn uint32_assn\<close>
  supply minus_uint32_assn[sepref_fr_rules] POS_SHIFT_uint64_hnr[sepref_fr_rules] minus_uint64_assn[sepref_fr_rules]
  unfolding isa_update_pos_def  uint32_nat_assn_minus[sepref_fr_rules] two_uint64_nat_def[symmetric]
  by sepref

lemma isa_update_pos_code_fast_hnr[sepref_fr_rules]:
  \<open>(uncurry2 isa_update_pos_fast_code, uncurry2 (RETURN ooo arena_update_pos))
  \<in> [isa_update_pos_pre]\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>d \<rightarrow> arena_fast_assn\<close>
  using isa_update_pos_fast_code.refine[FCOMP isa_update_pos[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl64_assn_comp isa_update_pos_pre_def)

declare isa_update_pos_fast_code.refine[sepref_fr_rules]
  arena_status_fast_code.refine[sepref_fr_rules]

end