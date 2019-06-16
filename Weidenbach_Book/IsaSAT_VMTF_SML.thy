theory IsaSAT_VMTF_SML
imports Watched_Literals.WB_Sort IsaSAT_VMTF IsaSAT_Setup_SML
begin

lemma size_conflict_code_refine_raw:
  \<open>(return o (\<lambda>(_, n, _). n), RETURN o size_conflict_int) \<in> conflict_option_rel_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare  (sep_auto simp: size_conflict_int_def)

concrete_definition (in -) size_conflict_code
   uses size_conflict_code_refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) size_conflict_code_def


lemmas size_conflict_code_hnr[sepref_fr_rules] = size_conflict_code.refine

lemma VMTF_Node_ref[sepref_fr_rules]:
  \<open>(uncurry2 (return ooo VMTF_Node), uncurry2 (RETURN ooo VMTF_Node)) \<in>
    uint64_nat_assn\<^sup>k *\<^sub>a (option_assn uint32_nat_assn)\<^sup>k *\<^sub>a (option_assn uint32_nat_assn)\<^sup>k \<rightarrow>\<^sub>a
    vmtf_node_assn\<close>
  by sepref_to_hoare
   (sep_auto simp: vmtf_node_rel_def uint32_nat_rel_def br_def option_assn_alt_def
     split: option.splits)

lemma stamp_ref[sepref_fr_rules]:
  \<open>(return o stamp, RETURN o stamp) \<in> vmtf_node_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare
    (auto simp: ex_assn_move_out(2)[symmetric] return_cons_rule ent_ex_up_swap vmtf_node_rel_def
      simp del: ex_assn_move_out)

lemma get_next_ref[sepref_fr_rules]:
  \<open>(return o get_next, RETURN o get_next) \<in> vmtf_node_assn\<^sup>k \<rightarrow>\<^sub>a
   option_assn uint32_nat_assn\<close>
  unfolding option_assn_pure_conv
  by sepref_to_hoare (sep_auto simp: return_cons_rule vmtf_node_rel_def)

lemma get_prev_ref[sepref_fr_rules]:
  \<open>(return o get_prev, RETURN o get_prev) \<in> vmtf_node_assn\<^sup>k \<rightarrow>\<^sub>a
   option_assn uint32_nat_assn\<close>
  unfolding option_assn_pure_conv
  by sepref_to_hoare (sep_auto simp: return_cons_rule vmtf_node_rel_def)

sepref_definition atoms_hash_del_code
  is \<open>uncurry (RETURN oo atoms_hash_del)\<close>
  :: \<open>[uncurry atoms_hash_del_pre]\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a (array_assn bool_assn)\<^sup>d \<rightarrow> array_assn bool_assn\<close>
  unfolding atoms_hash_del_def atoms_hash_del_pre_def
  by sepref

declare atoms_hash_del_code.refine[sepref_fr_rules]
sepref_definition (in -) atoms_hash_insert_code
  is \<open>uncurry (RETURN oo atoms_hash_insert)\<close>
  :: \<open>[uncurry atms_hash_insert_pre]\<^sub>a
      uint32_nat_assn\<^sup>k *\<^sub>a (arl_assn uint32_nat_assn *a array_assn bool_assn)\<^sup>d \<rightarrow>
      arl_assn uint32_nat_assn *a array_assn bool_assn\<close>
  unfolding atoms_hash_insert_def atms_hash_insert_pre_def
  by sepref

declare atoms_hash_insert_code.refine[sepref_fr_rules]

sepref_definition (in -) get_pos_of_level_in_trail_imp_fast_code
  is \<open>uncurry get_pos_of_level_in_trail_imp\<close>
  :: \<open>trail_pol_fast_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding get_pos_of_level_in_trail_imp_def
  by sepref


declare tl_trail_tr_no_CS_code.refine[sepref_fr_rules] tl_trail_tr_no_CS_fast_code.refine[sepref_fr_rules]

sepref_register find_decomp_wl_imp
sepref_register rescore_clause vmtf_flush
sepref_register vmtf_mark_to_rescore
sepref_register vmtf_mark_to_rescore_clause

sepref_register vmtf_mark_to_rescore_also_reasons get_the_propagation_reason_pol

sepref_register find_decomp_w_ns
sepref_definition (in -) get_pos_of_level_in_trail_imp_code
  is \<open>uncurry get_pos_of_level_in_trail_imp\<close>
  :: \<open>trail_pol_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding get_pos_of_level_in_trail_imp_def
  by sepref

declare get_pos_of_level_in_trail_imp_code.refine[sepref_fr_rules]
   get_pos_of_level_in_trail_imp_fast_code.refine[sepref_fr_rules]

lemma update_next_search_ref[sepref_fr_rules]:
  \<open>(uncurry (return oo update_next_search), uncurry (RETURN oo update_next_search)) \<in>
      (option_assn uint32_nat_assn)\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow>\<^sub>a vmtf_remove_conc\<close>
  unfolding option_assn_pure_conv
  by sepref_to_hoare (sep_auto simp: update_next_search_def)

sepref_definition (in -)ns_vmtf_dequeue_code
   is \<open>uncurry (RETURN oo ns_vmtf_dequeue)\<close>
   :: \<open>[vmtf_dequeue_pre]\<^sub>a
        uint32_nat_assn\<^sup>k *\<^sub>a (array_assn vmtf_node_assn)\<^sup>d \<rightarrow> array_assn vmtf_node_assn\<close>
  supply [[goals_limit = 1]]
  supply option.splits[split]
  unfolding ns_vmtf_dequeue_def vmtf_dequeue_pre_alt_def
  by sepref

declare ns_vmtf_dequeue_code.refine[sepref_fr_rules]

abbreviation vmtf_conc_option_fst_As where
  \<open>vmtf_conc_option_fst_As \<equiv>
    (array_assn vmtf_node_assn *a uint64_nat_assn *a option_assn uint32_nat_assn
      *a option_assn uint32_nat_assn *a option_assn uint32_nat_assn)\<close>

sepref_definition vmtf_dequeue_code
   is \<open>uncurry (RETURN oo vmtf_dequeue)\<close>
   :: \<open>[\<lambda>(L,(ns,m,fst_As,next_search)). L < length ns \<and> vmtf_dequeue_pre (L, ns)]\<^sub>a
        uint32_nat_assn\<^sup>k *\<^sub>a vmtf_conc\<^sup>d \<rightarrow> vmtf_conc_option_fst_As\<close>
  supply [[goals_limit = 1]]
  unfolding vmtf_dequeue_def
  by sepref

declare vmtf_dequeue_code.refine[sepref_fr_rules]

sepref_definition vmtf_enqueue_code
   is \<open>uncurry2 isa_vmtf_enqueue\<close>
   :: \<open>[vmtf_enqueue_pre]\<^sub>a
        trail_pol_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a vmtf_conc_option_fst_As\<^sup>d \<rightarrow> vmtf_conc\<close>
  supply [[goals_limit = 1]]
  unfolding isa_vmtf_enqueue_def vmtf_enqueue_pre_def defined_atm_def[symmetric]
   one_uint64_nat_def[symmetric]
  by sepref

declare vmtf_enqueue_code.refine[sepref_fr_rules]


sepref_definition vmtf_enqueue_fast_code
   is \<open>uncurry2 isa_vmtf_enqueue\<close>
   :: \<open>[vmtf_enqueue_pre]\<^sub>a
        trail_pol_fast_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a vmtf_conc_option_fst_As\<^sup>d \<rightarrow> vmtf_conc\<close>
  supply [[goals_limit = 1]]
  unfolding isa_vmtf_enqueue_def vmtf_enqueue_pre_def defined_atm_def[symmetric]
   one_uint64_nat_def[symmetric]
  by sepref

declare vmtf_enqueue_fast_code.refine[sepref_fr_rules]


(* TODO uint uint32_nat_assn*)
sepref_definition partition_vmtf_nth_code
   is \<open>uncurry3 partition_vmtf_nth\<close>
   :: \<open>[\<lambda>(((ns, _), hi), xs). (\<forall>x\<in>set xs. x < length ns)]\<^sub>a
  (array_assn vmtf_node_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (arl_assn uint32_nat_assn)\<^sup>d \<rightarrow>
  arl_assn uint32_nat_assn *a nat_assn\<close>
  unfolding partition_vmtf_nth_def insert_sort_inner_def fast_minus_def[symmetric]
    partition_main_def choose_pivot3_def
    WB_More_Refinement_List.swap_def IICF_List.swap_def[symmetric]
  supply [[goals_limit = 1]]
  supply partition_vmtf_nth_code_helper3[intro] partition_main_inv_def[simp]
  by sepref

declare partition_vmtf_nth_code.refine[sepref_fr_rules]

sepref_register partition_between_ref

sepref_definition (in -) partition_between_ref_vmtf_code
   is \<open>uncurry3 partition_between_ref_vmtf\<close>
   :: \<open>[\<lambda>(((vm), _), remove). (\<forall>x\<in>#mset remove. x < length (fst vm)) \<and> length remove \<le> uint32_max]\<^sub>a
      (array_assn vmtf_node_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (arl_assn uint32_nat_assn)\<^sup>d  \<rightarrow>
       arl_assn uint32_nat_assn *a nat_assn\<close>
  unfolding quicksort_vmtf_nth_def insert_sort_def partition_vmtf_nth_def[symmetric]
    quicksort_vmtf_nth_ref_def List.null_def quicksort_ref_def
    length_0_conv[symmetric] length_uint32_nat_def[symmetric]
    zero_uint32_nat_def[symmetric] partition_between_ref_vmtf_def
    partition_between_ref_def
    partition_vmtf_nth_def[symmetric] choose_pivot3_def
    WB_More_Refinement_List.swap_def IICF_List.swap_def[symmetric]
  by sepref

sepref_register partition_between_ref_vmtf quicksort_vmtf_nth_ref
declare partition_between_ref_vmtf_code.refine[sepref_fr_rules]

sepref_definition (in -) quicksort_vmtf_nth_ref_code
   is \<open>uncurry3 quicksort_vmtf_nth_ref\<close>
   :: \<open>[\<lambda>((vm, _), remove). (\<forall>x\<in>#mset remove. x < length (fst vm)) \<and> length remove \<le> uint32_max]\<^sub>a
      (array_assn vmtf_node_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (arl_assn uint32_nat_assn)\<^sup>d  \<rightarrow>
       arl_assn uint32_nat_assn\<close>
  unfolding quicksort_vmtf_nth_def insert_sort_def partition_vmtf_nth_def[symmetric]
    quicksort_vmtf_nth_ref_def List.null_def quicksort_ref_def
    length_0_conv[symmetric] length_uint32_nat_def[symmetric]
    zero_uint32_nat_def[symmetric]
   partition_vmtf_nth_def[symmetric]
   partition_between_ref_vmtf_def[symmetric]
   partition_vmtf_nth_def[symmetric]
  supply [[goals_limit = 1]]
  supply mset_eq_setD[dest] mset_eq_length[dest]
    arl_length_hnr[sepref_fr_rules]
  by sepref

declare quicksort_vmtf_nth_ref_code.refine[sepref_fr_rules]

sepref_definition (in -) quicksort_vmtf_nth_code
   is \<open>uncurry quicksort_vmtf_nth\<close>
   :: \<open>[\<lambda>(vm, remove). (\<forall>x\<in>#mset remove. x < length (fst vm)) \<and> length remove \<le> uint32_max]\<^sub>a
      vmtf_conc\<^sup>k *\<^sub>a (arl_assn uint32_nat_assn)\<^sup>d  \<rightarrow>
       arl_assn uint32_nat_assn\<close>
  unfolding quicksort_vmtf_nth_def insert_sort_def partition_vmtf_nth_def[symmetric]
    full_quicksort_ref_def List.null_def
    length_0_conv[symmetric]
    quicksort_vmtf_nth_ref_def[symmetric]
  supply [[goals_limit = 1]]
  supply mset_eq_setD[dest] mset_eq_length[dest]
    arl_length_hnr[sepref_fr_rules]
  by sepref

declare quicksort_vmtf_nth_code.refine[sepref_fr_rules]

lemma quicksort_vmtf_nth_code_reorder_list[sepref_fr_rules]:
   \<open>(uncurry quicksort_vmtf_nth_code, uncurry reorder_list) \<in>
      [\<lambda>((a, _), b). (\<forall>x\<in>set b. x < length a) \<and> length b \<le> uint32_max]\<^sub>a
      vmtf_conc\<^sup>k *\<^sub>a (arl_assn uint32_nat_assn)\<^sup>d \<rightarrow> arl_assn uint32_nat_assn\<close>
      supply [[show_types]]
  using quicksort_vmtf_nth_code.refine[FCOMP quicksort_vmtf_nth_reorder[unfolded convert_fref]]
  by auto
sepref_register isa_vmtf_enqueue

lemma current_stamp_hnr[sepref_fr_rules]:
  \<open>(return o current_stamp, RETURN o current_stamp) \<in> vmtf_conc\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: vmtf_node_rel_def current_stamp_alt_def)

sepref_definition vmtf_en_dequeue_code
   is \<open>uncurry2 isa_vmtf_en_dequeue\<close>
   :: \<open>[isa_vmtf_en_dequeue_pre]\<^sub>a
        trail_pol_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a vmtf_conc\<^sup>d \<rightarrow> vmtf_conc\<close>
  supply [[goals_limit = 1]]
  supply isa_vmtf_en_dequeue_preD[dest] isa_vmtf_en_dequeue_pre_vmtf_enqueue_pre[dest]
  unfolding isa_vmtf_en_dequeue_def
  by sepref

declare vmtf_en_dequeue_code.refine[sepref_fr_rules]

sepref_definition vmtf_en_dequeue_fast_code
   is \<open>uncurry2 isa_vmtf_en_dequeue\<close>
   :: \<open>[isa_vmtf_en_dequeue_pre]\<^sub>a
        trail_pol_fast_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a vmtf_conc\<^sup>d \<rightarrow> vmtf_conc\<close>
  supply [[goals_limit = 1]]
  supply isa_vmtf_en_dequeue_preD[dest] isa_vmtf_en_dequeue_pre_vmtf_enqueue_pre[dest]
  unfolding isa_vmtf_en_dequeue_def
  by sepref

declare vmtf_en_dequeue_fast_code.refine[sepref_fr_rules]

sepref_register vmtf_rescale
sepref_definition vmtf_rescale_code
   is \<open>vmtf_rescale\<close>
   :: \<open>vmtf_conc\<^sup>d \<rightarrow>\<^sub>a vmtf_conc\<close>
  supply [[goals_limit = 1]]
  supply vmtf_en_dequeue_pre_def[simp] le_uint32_max_le_uint64_max[intro]
  unfolding vmtf_rescale_alt_def zero_uint64_nat_def[symmetric] PR_CONST_def update_stamp.simps
    one_uint64_nat_def[symmetric]
  by sepref

declare vmtf_rescale_code.refine[sepref_fr_rules]

sepref_register isa_vmtf_en_dequeue
sepref_definition isa_vmtf_flush_code
   is \<open>uncurry isa_vmtf_flush_int\<close>
   :: \<open>trail_pol_assn\<^sup>k *\<^sub>a (vmtf_conc *a (arl_assn uint32_nat_assn *a atoms_hash_assn))\<^sup>d \<rightarrow>\<^sub>a
        (vmtf_conc *a (arl_assn uint32_nat_assn *a atoms_hash_assn))\<close>
  supply [[goals_limit = 1]]
  unfolding vmtf_flush_def PR_CONST_def isa_vmtf_flush_int_def zero_uint32_nat_def[symmetric]
    current_stamp_def[symmetric] one_uint32_nat_def[symmetric]
  apply (rewrite at \<open>\<lambda>(i, vm, h). _ < \<hole>\<close> length_uint32_nat_def[symmetric])
  apply (rewrite at \<open>length _ + \<hole>\<close> nat_of_uint64_conv_def[symmetric])
  by sepref

declare isa_vmtf_flush_code.refine[sepref_fr_rules]

sepref_definition isa_vmtf_flush_fast_code
   is \<open>uncurry isa_vmtf_flush_int\<close>
   :: \<open>trail_pol_fast_assn\<^sup>k *\<^sub>a (vmtf_conc *a (arl_assn uint32_nat_assn *a atoms_hash_assn))\<^sup>d \<rightarrow>\<^sub>a
        (vmtf_conc *a (arl_assn uint32_nat_assn *a atoms_hash_assn))\<close>
  supply [[goals_limit = 1]]
  unfolding isa_vmtf_flush_int_def PR_CONST_def vmtf_flush_int_def zero_uint32_nat_def[symmetric]
    current_stamp_def[symmetric] one_uint32_nat_def[symmetric]
  apply (rewrite at \<open>\<lambda>(i, vm, h). _ < \<hole>\<close> length_uint32_nat_def[symmetric])
  apply (rewrite at \<open>length _ + \<hole>\<close> nat_of_uint64_conv_def[symmetric])
  by sepref

declare isa_vmtf_flush_code.refine[sepref_fr_rules]
  isa_vmtf_flush_fast_code.refine[sepref_fr_rules]

sepref_register isa_vmtf_mark_to_rescore
sepref_definition isa_vmtf_mark_to_rescore_code
  is \<open>uncurry (RETURN oo isa_vmtf_mark_to_rescore)\<close>
  :: \<open>[uncurry isa_vmtf_mark_to_rescore_pre]\<^sub>a
     uint32_nat_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow> vmtf_remove_conc\<close>
  supply [[goals_limit=1]] option.splits[split] vmtf_def[simp] in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff[simp]
    neq_NilE[elim!] literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset[simp]
  unfolding isa_vmtf_mark_to_rescore_pre_def isa_vmtf_mark_to_rescore_def
  by sepref

declare isa_vmtf_mark_to_rescore_code.refine[sepref_fr_rules]

sepref_register isa_vmtf_unset
sepref_definition isa_vmtf_unset_code
  is \<open>uncurry (RETURN oo isa_vmtf_unset)\<close>
  :: \<open>[uncurry vmtf_unset_pre]\<^sub>a
     uint32_nat_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow> vmtf_remove_conc\<close>
  supply [[goals_limit=1]] option.splits[split] vmtf_def[simp] in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff[simp]
    neq_NilE[elim!] literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset[simp]
  unfolding isa_vmtf_unset_def vmtf_unset_pre_def
  apply (rewrite in \<open>If (_ \<or> _)\<close> short_circuit_conv)
  by sepref

declare isa_vmtf_unset_code.refine[sepref_fr_rules]

sepref_definition vmtf_mark_to_rescore_and_unset_code
  is \<open>uncurry (RETURN oo isa_vmtf_mark_to_rescore_and_unset)\<close>
  :: \<open>[isa_vmtf_mark_to_rescore_and_unset_pre]\<^sub>a
      uint32_nat_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow> vmtf_remove_conc\<close>
  supply image_image[simp] uminus_\<A>\<^sub>i\<^sub>n_iff[iff] in_diffD[dest] option.splits[split]
    if_splits[split] isa_vmtf_unset_def[simp]
  supply [[goals_limit=1]]
  unfolding isa_vmtf_mark_to_rescore_and_unset_def isa_vmtf_mark_to_rescore_def
    save_phase_def isa_vmtf_mark_to_rescore_and_unset_pre_def
  by sepref

declare vmtf_mark_to_rescore_and_unset_code.refine[sepref_fr_rules]
sepref_definition find_decomp_wl_imp_code
  is \<open>uncurry2 (isa_find_decomp_wl_imp)\<close>
  :: \<open>[\<lambda>((M, lev), vm). True]\<^sub>a trail_pol_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d
    \<rightarrow> trail_pol_assn *a vmtf_remove_conc\<close>
  unfolding isa_find_decomp_wl_imp_def get_maximum_level_remove_def[symmetric] PR_CONST_def
    trail_pol_conv_to_no_CS_def
  supply [[goals_limit=1]] literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset[simp] trail_conv_to_no_CS_def[simp]
    lit_of_hd_trail_def[simp]
  supply uint32_nat_assn_one[sepref_fr_rules] vmtf_unset_pre_def[simp]
  supply uint32_nat_assn_minus[sepref_fr_rules]
  by sepref

declare find_decomp_wl_imp_code.refine[sepref_fr_rules]

sepref_definition find_decomp_wl_imp_fast_code
  is \<open>uncurry2 (isa_find_decomp_wl_imp)\<close>
  :: \<open>[\<lambda>((M, lev), vm). True]\<^sub>a trail_pol_fast_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d
    \<rightarrow> trail_pol_fast_assn *a vmtf_remove_conc\<close>
  unfolding isa_find_decomp_wl_imp_def get_maximum_level_remove_def[symmetric] PR_CONST_def
    trail_pol_conv_to_no_CS_def
  supply trail_conv_to_no_CS_def[simp] lit_of_hd_trail_def[simp]
  supply [[goals_limit=1]] literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset[simp]
  supply uint32_nat_assn_one[sepref_fr_rules] vmtf_unset_pre_def[simp]
  supply uint32_nat_assn_minus[sepref_fr_rules]
  by sepref

declare find_decomp_wl_imp_fast_code.refine[sepref_fr_rules]

sepref_definition vmtf_rescore_code
  is \<open>uncurry3 isa_vmtf_rescore\<close>
  :: \<open>(array_assn unat_lit_assn)\<^sup>k *\<^sub>a trail_pol_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d *\<^sub>a phase_saver_conc\<^sup>d \<rightarrow>\<^sub>a
       vmtf_remove_conc *a phase_saver_conc\<close>
  unfolding isa_vmtf_rescore_body_def[abs_def] PR_CONST_def isa_vmtf_rescore_def
  supply [[goals_limit = 1]] fold_is_None[simp]
  by sepref

sepref_definition vmtf_rescore_fast_code
  is \<open>uncurry3 isa_vmtf_rescore\<close>
  :: \<open>(array_assn unat_lit_assn)\<^sup>k *\<^sub>a trail_pol_fast_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d *\<^sub>a phase_saver_conc\<^sup>d \<rightarrow>\<^sub>a
       vmtf_remove_conc *a phase_saver_conc\<close>
  unfolding isa_vmtf_rescore_body_def[abs_def] PR_CONST_def isa_vmtf_rescore_def
  supply [[goals_limit = 1]] fold_is_None[simp]
  by sepref

declare
  vmtf_rescore_code.refine[sepref_fr_rules]
  vmtf_rescore_fast_code.refine[sepref_fr_rules]

sepref_definition find_decomp_wl_imp'_code
  is \<open>uncurry find_decomp_wl_st_int\<close>
  :: \<open>uint32_nat_assn\<^sup>k *\<^sub>a isasat_unbounded_assn\<^sup>d  \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  unfolding find_decomp_wl_st_int_def PR_CONST_def isasat_unbounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

declare find_decomp_wl_imp'_code.refine[sepref_fr_rules]

sepref_definition find_decomp_wl_imp'_fast_code
  is \<open>uncurry find_decomp_wl_st_int\<close>
  :: \<open>uint32_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d  \<rightarrow>\<^sub>a
        isasat_bounded_assn\<close>
  unfolding find_decomp_wl_st_int_def PR_CONST_def isasat_bounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

declare find_decomp_wl_imp'_fast_code.refine[sepref_fr_rules]
sepref_definition vmtf_mark_to_rescore_clause_code
  is \<open>uncurry2 (isa_vmtf_mark_to_rescore_clause)\<close>
  :: \<open>arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow>\<^sub>a vmtf_remove_conc\<close>
  supply [[goals_limit=1]]
  unfolding isa_vmtf_mark_to_rescore_clause_def PR_CONST_def
  by sepref

declare vmtf_mark_to_rescore_clause_code.refine[sepref_fr_rules]

sepref_definition vmtf_mark_to_rescore_also_reasons_code
  is \<open>uncurry3 (isa_vmtf_mark_to_rescore_also_reasons)\<close>
  :: \<open>trail_pol_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a (arl_assn unat_lit_assn)\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow>\<^sub>a vmtf_remove_conc\<close>
  supply image_image[simp] uminus_\<A>\<^sub>i\<^sub>n_iff[iff] in_diffD[dest] option.splits[split]
    in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n[simp]
  supply [[goals_limit=1]]
  unfolding isa_vmtf_mark_to_rescore_also_reasons_def PR_CONST_def
  by sepref

declare vmtf_mark_to_rescore_also_reasons_code.refine[sepref_fr_rules]

sepref_definition vmtf_mark_to_rescore_clause_fast_code
  is \<open>uncurry2 (isa_vmtf_mark_to_rescore_clause)\<close>
  :: \<open>[\<lambda>((N, _), _). length N \<le> uint64_max]\<^sub>a
       arena_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow> vmtf_remove_conc\<close>
  supply [[goals_limit=1]] arena_is_valid_clause_idx_le_uint64_max[intro]
  unfolding isa_vmtf_mark_to_rescore_clause_def PR_CONST_def nat_of_uint64_conv_def
  apply (rewrite at \<open>[\<hole>..<_]\<close> nat_of_uint64_conv_def[symmetric])
  apply (rewrite at \<open>[_..<\<hole>]\<close> nat_of_uint64_conv_def[symmetric])
  by sepref

declare vmtf_mark_to_rescore_clause_fast_code.refine[sepref_fr_rules]

sepref_definition vmtf_mark_to_rescore_also_reasons_fast_code
  is \<open>uncurry3 (isa_vmtf_mark_to_rescore_also_reasons)\<close>
  :: \<open>[\<lambda>(((_, N), _), _). length N \<le> uint64_max]\<^sub>a
      trail_pol_fast_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a (arl_assn unat_lit_assn)\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow>
      vmtf_remove_conc\<close>
  supply image_image[simp] uminus_\<A>\<^sub>i\<^sub>n_iff[iff] in_diffD[dest] option.splits[split]
    in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n[simp]
  supply [[goals_limit=1]]
  unfolding isa_vmtf_mark_to_rescore_also_reasons_def PR_CONST_def
  apply (rewrite at \<open>If (_ = \<hole>)\<close> zero_uint64_nat_def[symmetric])
  by sepref

declare vmtf_mark_to_rescore_also_reasons_fast_code.refine[sepref_fr_rules]


end