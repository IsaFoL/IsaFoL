theory IsaSAT_Initialisation_SML
  imports IsaSAT_Setup_SML IsaSAT_VMTF_SML Watched_Literals.Watched_Literals_Watch_List_Initialisation
  Watched_Literals.Watched_Literals_Watch_List_Initialisation
    IsaSAT_Initialisation
begin
term mset_rel
type_synonym vdom_fast_assn = \<open>uint64 array_list\<close>
abbreviation vdom_fast_assn :: \<open>vdom \<Rightarrow> vdom_fast_assn \<Rightarrow> assn\<close> where
  \<open>vdom_fast_assn \<equiv> arl_assn uint64_nat_assn\<close>

abbreviation (in -) vmtf_conc_option_fst_As where
  \<open>vmtf_conc_option_fst_As \<equiv> (array_assn vmtf_node_assn *a uint64_nat_assn *a
    option_assn uint32_nat_assn *a option_assn uint32_nat_assn *a option_assn uint32_nat_assn)\<close>

abbreviation vmtf_remove_conc_option_fst_As
  :: \<open>isa_vmtf_remove_int_option_fst_As \<Rightarrow> vmtf_remove_assn_option_fst_As \<Rightarrow> assn\<close>
where
  \<open>vmtf_remove_conc_option_fst_As \<equiv> vmtf_conc_option_fst_As *a distinct_atoms_assn\<close>

sepref_register atoms_hash_empty
sepref_definition (in -) atoms_hash_empty_code
  is \<open>atoms_hash_int_empty\<close>
  :: \<open>nat_assn\<^sup>k \<rightarrow>\<^sub>a phase_saver_conc\<close>
  unfolding atoms_hash_int_empty_def array_fold_custom_replicate
  by sepref

find_theorems replicate arl64_assn
sepref_definition distinct_atms_empty_code
  is \<open>distinct_atms_int_empty\<close>
  :: \<open>nat_assn\<^sup>k \<rightarrow>\<^sub>a arl_assn uint32_nat_assn *a atoms_hash_assn\<close>
  unfolding distinct_atms_int_empty_def array_fold_custom_replicate
    IICF_Array_List.arl.fold_custom_empty
  by sepref

declare distinct_atms_empty_code.refine[sepref_fr_rules]

  
type_synonym (in -)twl_st_wll_trail_init =
  \<open>trail_pol_fast_assn \<times> isasat_clauses_assn \<times> option_lookup_clause_assn \<times>
    uint32 \<times> watched_wl_uint32 \<times> vmtf_remove_assn_option_fst_As \<times> phase_saver_assn \<times>
    uint32 \<times> minimize_assn \<times> lbd_assn \<times> vdom_assn \<times> bool\<close>

definition isasat_init_assn
  :: \<open>twl_st_wl_heur_init \<Rightarrow> twl_st_wll_trail_init \<Rightarrow> assn\<close>
where
\<open>isasat_init_assn =
  trail_pol_fast_assn *a arena_assn *a
  isasat_conflict_assn *a
  uint32_nat_assn *a
  watchlist_fast_assn *a
  vmtf_remove_conc_option_fst_As *a phase_saver_conc *a
  uint32_nat_assn *a
  cach_refinement_l_assn *a
  lbd_assn *a
  vdom_assn *a
  bool_assn\<close>


type_synonym (in -)twl_st_wll_trail_init_unbounded =
  \<open>trail_pol_assn \<times> isasat_clauses_assn \<times> option_lookup_clause_assn \<times>
    uint32 \<times> watched_wl \<times> vmtf_remove_assn_option_fst_As \<times> phase_saver_assn \<times>
    uint32 \<times> minimize_assn \<times> lbd_assn \<times> vdom_assn \<times> bool\<close>

definition isasat_init_unbounded_assn
  :: \<open>twl_st_wl_heur_init \<Rightarrow> twl_st_wll_trail_init_unbounded \<Rightarrow> assn\<close>
where
\<open>isasat_init_unbounded_assn =
  trail_pol_assn *a arena_assn *a
  isasat_conflict_assn *a
  uint32_nat_assn *a
  watchlist_assn *a
  vmtf_remove_conc_option_fst_As *a phase_saver_conc *a
  uint32_nat_assn *a
  cach_refinement_l_assn *a
  lbd_assn *a
  vdom_assn *a
  bool_assn\<close>

sepref_definition initialise_VMTF_code
  is \<open>uncurry initialise_VMTF\<close>
  :: \<open>[\<lambda>(N, n). True]\<^sub>a (arl_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> vmtf_remove_conc_option_fst_As\<close>
  supply nat_of_uint32_int32_assn[sepref_fr_rules] uint64_max_def[simp] uint32_max_def[simp]
  unfolding initialise_VMTF_def vmtf_cons_def Suc_eq_plus1 one_uint64_nat_def[symmetric]
  apply (rewrite in \<open>(_, _, Some \<hole>)\<close> annotate_assn[where A=\<open>uint32_nat_assn\<close>])
  apply (rewrite in \<open>WHILE\<^sub>T _ _ (_, _, \<hole>)\<close> annotate_assn[where A=\<open>option_assn uint32_nat_assn\<close>])
  apply (rewrite in \<open>do {ASSERT _; let _ = \<hole>; _}\<close> annotate_assn[where A=\<open>uint32_nat_assn\<close>])
  apply (rewrite in \<open>let _ = \<hole> in _ \<close> array_fold_custom_replicate op_list_replicate_def[symmetric])
  apply (rewrite in \<open>VMTF_Node zero_uint64_nat \<hole> _\<close> annotate_assn[where A=\<open>option_assn uint32_nat_assn\<close>])
  apply (rewrite in \<open>VMTF_Node zero_uint64_nat _ \<hole>\<close> annotate_assn[where A=\<open>option_assn uint32_nat_assn\<close>])
  supply [[goals_limit = 1]]
  by sepref

declare initialise_VMTF_code.refine[sepref_fr_rules]

sepref_definition propagate_unit_cls_code
  is \<open>uncurry (propagate_unit_cls_heur)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_init_assn\<^sup>d \<rightarrow>\<^sub>a isasat_init_assn\<close>
  supply [[goals_limit=1]] DECISION_REASON_def[simp]
  unfolding propagate_unit_cls_heur_def isasat_init_assn_def
  PR_CONST_def cons_trail_Propagated_def[symmetric] zero_uint64_nat_def[symmetric]
  by sepref

sepref_definition propagate_unit_cls_code_unb
  is \<open>uncurry (propagate_unit_cls_heur)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_init_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_init_unbounded_assn\<close>
  supply [[goals_limit=1]] DECISION_REASON_def[simp]
  unfolding propagate_unit_cls_heur_def isasat_init_unbounded_assn_def
  PR_CONST_def cons_trail_Propagated_def[symmetric]
  by sepref

declare propagate_unit_cls_code_unb.refine[sepref_fr_rules]
  propagate_unit_cls_code.refine[sepref_fr_rules]


sepref_definition already_propagated_unit_cls_code
  is \<open>uncurry already_propagated_unit_cls_heur\<close>
  :: \<open>(list_assn unat_lit_assn)\<^sup>k *\<^sub>a isasat_init_assn\<^sup>d  \<rightarrow>\<^sub>a isasat_init_assn\<close>
  supply [[goals_limit=1]]
  unfolding already_propagated_unit_cls_heur_def isasat_init_assn_def
  PR_CONST_def cons_trail_Propagated_def[symmetric]
  by sepref

sepref_definition already_propagated_unit_cls_code_unb
  is \<open>uncurry already_propagated_unit_cls_heur\<close>
  :: \<open>(list_assn unat_lit_assn)\<^sup>k *\<^sub>a isasat_init_unbounded_assn\<^sup>d  \<rightarrow>\<^sub>a isasat_init_unbounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding already_propagated_unit_cls_heur_def isasat_init_unbounded_assn_def
  PR_CONST_def cons_trail_Propagated_def[symmetric]
  by sepref

declare already_propagated_unit_cls_code.refine[sepref_fr_rules]
  already_propagated_unit_cls_code_unb.refine[sepref_fr_rules]


sepref_definition set_conflict_unit_code
  is \<open>uncurry set_conflict_unit_heur\<close>
  :: \<open>[\<lambda>(L, (b, n, xs)). atm_of L < length xs]\<^sub>a
        unat_lit_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d \<rightarrow> conflict_option_rel_assn\<close>
  supply one_uint32_nat[sepref_fr_rules]
  unfolding set_conflict_unit_heur_def one_uint32_nat_def[symmetric] ISIN_def[symmetric]
  by sepref

declare set_conflict_unit_code.refine[sepref_fr_rules]

sepref_definition conflict_propagated_unit_cls_code
  is \<open>uncurry (conflict_propagated_unit_cls_heur)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_init_assn\<^sup>d  \<rightarrow>\<^sub>a isasat_init_assn\<close>
  supply [[goals_limit=1]]
  unfolding conflict_propagated_unit_cls_heur_def isasat_init_assn_def
  PR_CONST_def cons_trail_Propagated_def[symmetric]
  by sepref


sepref_definition conflict_propagated_unit_cls_code_unb
  is \<open>uncurry conflict_propagated_unit_cls_heur\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_init_unbounded_assn\<^sup>d  \<rightarrow>\<^sub>a isasat_init_unbounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding conflict_propagated_unit_cls_heur_def isasat_init_unbounded_assn_def
  PR_CONST_def cons_trail_Propagated_def[symmetric]
  by sepref

declare conflict_propagated_unit_cls_code.refine[sepref_fr_rules]
  conflict_propagated_unit_cls_code_unb.refine[sepref_fr_rules]

sepref_register fm_add_new


sepref_definition add_init_cls_code
  is \<open>uncurry add_init_cls_heur_unb\<close>
  :: \<open>(list_assn unat_lit_assn)\<^sup>k *\<^sub>a isasat_init_assn\<^sup>d  \<rightarrow>\<^sub>a isasat_init_assn\<close>
  supply [[goals_limit=1]] append_ll_def[simp]
  unfolding add_init_cls_heur_def isasat_init_assn_def add_init_cls_heur_unb_def
  PR_CONST_def cons_trail_Propagated_def[symmetric] nat_of_uint32_conv_def
  unfolding isasat_init_assn_def Array_List_Array.swap_ll_def[symmetric]
    nth_rll_def[symmetric] delete_index_and_swap_update_def[symmetric]
    delete_index_and_swap_ll_def[symmetric]
    append_ll_def[symmetric]
  apply (rewrite in \<open>let _ = \<hole> in _\<close> op_list_copy_def[symmetric])
  apply (rewrite in \<open>let _ = \<hole> in _\<close> op_array_of_list_def[symmetric])
  by sepref


sepref_definition add_init_cls_code_unb
  is \<open>uncurry add_init_cls_heur_unb\<close>
  :: \<open>(list_assn unat_lit_assn)\<^sup>k *\<^sub>a isasat_init_unbounded_assn\<^sup>d  \<rightarrow>\<^sub>a isasat_init_unbounded_assn\<close>
  supply [[goals_limit=1]] append_ll_def[simp]
  unfolding add_init_cls_heur_def isasat_init_unbounded_assn_def add_init_cls_heur_unb_def
  PR_CONST_def cons_trail_Propagated_def[symmetric] nat_of_uint32_conv_def
  unfolding isasat_init_unbounded_assn_def Array_List_Array.swap_ll_def[symmetric]
    nth_rll_def[symmetric] delete_index_and_swap_update_def[symmetric]
    delete_index_and_swap_ll_def[symmetric]
    append_ll_def[symmetric]
  apply (rewrite in \<open>let _ = \<hole> in _\<close> op_list_copy_def[symmetric])
  apply (rewrite in \<open>let _ = \<hole> in _\<close> op_array_of_list_def[symmetric])
  by sepref

declare add_init_cls_code.refine[sepref_fr_rules]
   add_init_cls_code_unb.refine[sepref_fr_rules]

sepref_definition already_propagated_unit_cls_conflict_code
  is \<open>uncurry already_propagated_unit_cls_conflict_heur\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_init_assn\<^sup>d  \<rightarrow>\<^sub>a isasat_init_assn\<close>
  supply [[goals_limit=1]]
  unfolding already_propagated_unit_cls_conflict_heur_def isasat_init_assn_def
  PR_CONST_def cons_trail_Propagated_def[symmetric]
  by sepref

declare already_propagated_unit_cls_conflict_code.refine[sepref_fr_rules]

sepref_definition (in -) set_conflict_empty_code
  is \<open>RETURN o lookup_set_conflict_empty\<close>
  :: \<open>conflict_option_rel_assn\<^sup>d  \<rightarrow>\<^sub>a conflict_option_rel_assn\<close>
  supply [[goals_limit=1]]
  unfolding lookup_set_conflict_empty_def
  by sepref

declare set_conflict_empty_code.refine[sepref_fr_rules]

sepref_definition set_empty_clause_as_conflict_code
  is \<open>set_empty_clause_as_conflict_heur\<close>
  :: \<open>isasat_init_assn\<^sup>d \<rightarrow>\<^sub>a isasat_init_assn\<close>
  supply [[goals_limit=1]]
  unfolding set_empty_clause_as_conflict_heur_def isasat_init_assn_def
  by sepref

sepref_definition set_empty_clause_as_conflict_code_unb
  is \<open>set_empty_clause_as_conflict_heur\<close>
  :: \<open>isasat_init_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_init_unbounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding set_empty_clause_as_conflict_heur_def isasat_init_unbounded_assn_def
  by sepref

declare set_empty_clause_as_conflict_code.refine[sepref_fr_rules]
  set_empty_clause_as_conflict_code_unb.refine[sepref_fr_rules]

sepref_definition add_clause_to_others_code
  is \<open>uncurry add_clause_to_others_heur\<close>
  :: \<open>(list_assn unat_lit_assn)\<^sup>k *\<^sub>a isasat_init_assn\<^sup>d \<rightarrow>\<^sub>a isasat_init_assn\<close>
  supply [[goals_limit=1]]
  unfolding add_clause_to_others_heur_def isasat_init_assn_def
  by sepref

sepref_definition add_clause_to_others_code_unb
  is \<open>uncurry add_clause_to_others_heur\<close>
  :: \<open>(list_assn unat_lit_assn)\<^sup>k *\<^sub>a isasat_init_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_init_unbounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding add_clause_to_others_heur_def isasat_init_unbounded_assn_def
  by sepref

declare add_clause_to_others_code.refine[sepref_fr_rules]
  add_clause_to_others_code_unb.refine[sepref_fr_rules]

lemma (in -)list_length_1_hnr[sepref_fr_rules]:
  assumes \<open>CONSTRAINT is_pure R \<close>
  shows \<open>(return o list_length_1_code, RETURN o list_length_1) \<in> (list_assn R)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
proof -
  obtain R' where
     \<open>R' = the_pure R\<close> and
     R_R': \<open>R = pure R'\<close>
    using assms by fastforce
  show ?thesis
    unfolding R_R' list_assn_pure_conv
    by (sepref_to_hoare)
       (sep_auto simp: list_length_1_code_def list_rel_def list_all2_lengthD[symmetric]
        split: list.splits)
qed


sepref_definition get_conflict_wl_is_None_init_code
  is \<open>RETURN o get_conflict_wl_is_None_heur_init\<close>
  :: \<open>isasat_init_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding get_conflict_wl_is_None_heur_init_alt_def isasat_init_assn_def length_ll_def[symmetric]
  supply [[goals_limit=1]]
  by sepref

sepref_definition get_conflict_wl_is_None_init_code_unb
  is \<open>RETURN o get_conflict_wl_is_None_heur_init\<close>
  :: \<open>isasat_init_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding get_conflict_wl_is_None_heur_init_alt_def isasat_init_unbounded_assn_def
    length_ll_def[symmetric]
  supply [[goals_limit=1]]
  by sepref

declare get_conflict_wl_is_None_init_code.refine[sepref_fr_rules]
   get_conflict_wl_is_None_init_code_unb.refine[sepref_fr_rules]

sepref_definition polarity_st_heur_init_code
  is \<open>uncurry (RETURN oo polarity_st_heur_init)\<close>
  :: \<open>[\<lambda>(S, L). polarity_pol_pre (get_trail_wl_heur_init S) L]\<^sub>a isasat_init_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> tri_bool_assn\<close>
  unfolding polarity_st_heur_init_def isasat_init_assn_def
  supply [[goals_limit = 1]]
  by sepref

sepref_definition polarity_st_heur_init_code_unb
  is \<open>uncurry (RETURN oo polarity_st_heur_init)\<close>
  :: \<open>[\<lambda>(S, L). polarity_pol_pre (get_trail_wl_heur_init S) L]\<^sub>a
       isasat_init_unbounded_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> tri_bool_assn\<close>
  unfolding polarity_st_heur_init_def isasat_init_unbounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

declare polarity_st_heur_init_code.refine[sepref_fr_rules]
  polarity_st_heur_init_code_unb.refine[sepref_fr_rules]


lemma is_Nil_hnr[sepref_fr_rules]:
 \<open>(return o is_Nil, RETURN o is_Nil) \<in> (list_assn R)\<^sup>k\<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto split: list.splits)

sepref_register init_dt_step_wl
  get_conflict_wl_is_None_heur_init already_propagated_unit_cls_heur
  conflict_propagated_unit_cls_heur add_clause_to_others_heur
  add_init_cls_heur set_empty_clause_as_conflict_heur

sepref_register polarity_st_heur_init propagate_unit_cls_heur

sepref_definition init_dt_step_wl_code
  is \<open>uncurry (init_dt_step_wl_heur_unb)\<close>
  :: \<open>[\<lambda>(C, S). True]\<^sub>a (list_assn unat_lit_assn)\<^sup>d *\<^sub>a isasat_init_assn\<^sup>d \<rightarrow>
       isasat_init_assn\<close>
  supply [[goals_limit=1]]
  supply polarity_None_undefined_lit[simp] polarity_st_init_def[simp]
  option.splits[split] get_conflict_wl_is_None_heur_init_alt_def[simp]
  tri_bool_eq_def[simp]
  unfolding init_dt_step_wl_heur_def lms_fold_custom_empty PR_CONST_def
    init_dt_step_wl_heur_unb_def if_True add_init_cls_heur_unb_def[symmetric]
  unfolding watched_app_def[symmetric]
  unfolding nth_rll_def[symmetric]
  unfolding lms_fold_custom_empty swap_ll_def[symmetric]
  unfolding
    cons_trail_Propagated_def[symmetric] get_conflict_wl_is_None_init
    polarity_st_heur_init_alt_def[symmetric]
    get_conflict_wl_is_None_heur_init_alt_def[symmetric]
    SET_TRUE_def[symmetric] SET_FALSE_def[symmetric] UNSET_def[symmetric]
    tri_bool_eq_def[symmetric]
  by sepref

sepref_definition init_dt_step_wl_code_unb
  is \<open>uncurry (init_dt_step_wl_heur_unb)\<close>
  :: \<open>[\<lambda>(C, S). True]\<^sub>a (list_assn unat_lit_assn)\<^sup>d *\<^sub>a isasat_init_unbounded_assn\<^sup>d \<rightarrow>
       isasat_init_unbounded_assn\<close>
  supply [[goals_limit=1]]
  supply polarity_None_undefined_lit[simp] polarity_st_init_def[simp]
  option.splits[split] get_conflict_wl_is_None_heur_init_alt_def[simp]
  tri_bool_eq_def[simp]
  unfolding init_dt_step_wl_heur_def lms_fold_custom_empty PR_CONST_def
    add_init_cls_heur_unb_def[symmetric] init_dt_step_wl_heur_unb_def
  unfolding watched_app_def[symmetric]
  unfolding nth_rll_def[symmetric]
  unfolding lms_fold_custom_empty swap_ll_def[symmetric]
  unfolding
    cons_trail_Propagated_def[symmetric] get_conflict_wl_is_None_init
    polarity_st_heur_init_alt_def[symmetric]
    get_conflict_wl_is_None_heur_init_alt_def[symmetric]
    SET_TRUE_def[symmetric] SET_FALSE_def[symmetric] UNSET_def[symmetric]
    tri_bool_eq_def[symmetric]
  by sepref

declare init_dt_step_wl_code.refine[sepref_fr_rules]
  init_dt_step_wl_code_unb.refine[sepref_fr_rules]


sepref_register init_dt_wl_heur_unb


abbreviation isasat_atms_ext_rel_assn where
  \<open>isasat_atms_ext_rel_assn \<equiv> array_assn uint64_nat_assn *a uint32_nat_assn *a
       arl_assn uint32_nat_assn\<close>

abbreviation nat_lit_list_hm_assn where
  \<open>nat_lit_list_hm_assn \<equiv> hr_comp isasat_atms_ext_rel_assn isasat_atms_ext_rel\<close>


lemma (in -) [sepref_fr_rules]:
  \<open>(return o init_next_size, RETURN o init_next_size)
  \<in> [\<lambda>L. L \<le> uint32_max div 2]\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  by (sepref_to_hoare)
   (sep_auto simp: init_next_size_def br_def uint32_nat_rel_def nat_of_uint32_add
      nat_of_uint32_distrib_mult2 uint_max_def)


sepref_definition nat_lit_lits_init_assn_assn_in
  is \<open>uncurry add_to_atms_ext\<close>
  :: \<open>uint32_nat_assn\<^sup>k *\<^sub>a isasat_atms_ext_rel_assn\<^sup>d \<rightarrow>\<^sub>a isasat_atms_ext_rel_assn\<close>
  supply [[goals_limit=1]]
  unfolding add_to_atms_ext_def two_uint64_nat_def[symmetric] Suc_0_le_uint64_max[simp]
    heap_array_set_u_def[symmetric]
  by sepref

lemma [sepref_fr_rules]:
  \<open>(uncurry nat_lit_lits_init_assn_assn_in,  uncurry (RETURN \<circ>\<circ> op_set_insert))
  \<in> [\<lambda>(a, b). a \<le> uint_max div 2]\<^sub>a
    uint32_nat_assn\<^sup>k *\<^sub>a nat_lit_list_hm_assn\<^sup>d \<rightarrow> nat_lit_list_hm_assn\<close>
  by (rule nat_lit_lits_init_assn_assn_in.refine[FCOMP add_to_atms_ext_op_set_insert
  [unfolded convert_fref op_set_insert_def[symmetric]]])

sepref_definition extract_atms_cls_imp
  is \<open>uncurry extract_atms_cls_i\<close>
  :: \<open>(list_assn unat_lit_assn)\<^sup>k *\<^sub>a nat_lit_list_hm_assn\<^sup>d \<rightarrow>\<^sub>a nat_lit_list_hm_assn\<close>
  unfolding extract_atms_cls_i_def
  by sepref

declare extract_atms_cls_imp.refine[sepref_fr_rules]

sepref_definition extract_atms_clss_imp
  is \<open>uncurry extract_atms_clss_i\<close>
  :: \<open>(list_assn (list_assn unat_lit_assn))\<^sup>k *\<^sub>a nat_lit_list_hm_assn\<^sup>d \<rightarrow>\<^sub>a nat_lit_list_hm_assn\<close>
  unfolding extract_atms_clss_i_def
  by sepref

lemma extract_atms_clss_hnr[sepref_fr_rules]:
  \<open>(uncurry extract_atms_clss_imp, uncurry (RETURN \<circ>\<circ> extract_atms_clss))
    \<in> [\<lambda>(a, b). \<forall>C\<in>set a. \<forall>L\<in>set C. nat_of_lit L \<le> uint_max]\<^sub>a
      (list_assn (list_assn unat_lit_assn))\<^sup>k *\<^sub>a nat_lit_list_hm_assn\<^sup>d \<rightarrow> nat_lit_list_hm_assn\<close>
  using extract_atms_clss_imp.refine[FCOMP extract_atms_clss_i_extract_atms_clss[unfolded convert_fref]] .

sepref_definition extract_atms_clss_imp_empty_assn
  is \<open>uncurry0 extract_atms_clss_imp_empty_rel\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a isasat_atms_ext_rel_assn\<close>
  unfolding extract_atms_clss_imp_empty_rel_def
    array_fold_custom_replicate
  supply [[goals_limit=1]]
  apply (rewrite at \<open>(_, _, \<hole>)\<close> IICF_Array_List.arl.fold_custom_empty)
  apply (rewrite in \<open>(_, _, \<hole>)\<close> annotate_assn[where A=\<open>arl_assn uint32_nat_assn\<close>])
  apply (rewrite in \<open>(\<hole>, _, _)\<close> zero_uint64_nat_def[symmetric])
  apply (rewrite in \<open>(_, \<hole>, _)\<close> zero_uint32_nat_def[symmetric])
  by sepref

lemma extract_atms_clss_imp_empty_assn[sepref_fr_rules]:
  \<open>(uncurry0 extract_atms_clss_imp_empty_assn, uncurry0 (RETURN op_extract_list_empty))
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a nat_lit_list_hm_assn\<close>
  using extract_atms_clss_imp_empty_assn.refine[FCOMP extract_atms_clss_imp_empty_rel
    [unfolded convert_fref uncurry0_def[symmetric]]] .

declare atm_of_hnr[sepref_fr_rules]

lemma extract_atms_clss_imp_empty_rel_alt_def:
  \<open>extract_atms_clss_imp_empty_rel = (RETURN (op_array_replicate 1024 zero_uint64_nat, 0, []))\<close>
  by (auto simp: extract_atms_clss_imp_empty_rel_def)


subsubsection \<open>Full Initialisation\<close>

sepref_definition rewatch_heur_st_code
  is \<open>(rewatch_heur_st)\<close>
  :: \<open>isasat_init_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_init_unbounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding rewatch_heur_st_def PR_CONST_def
    isasat_init_unbounded_assn_def
  by sepref

sepref_definition rewatch_heur_fast_code
  is \<open>uncurry2 (rewatch_heur)\<close>
  :: \<open>[\<lambda>((vdom, arena), W). (\<forall>x \<in> set vdom. x \<le> uint64_max) \<and> length arena \<le> uint64_max]\<^sub>a
        vdom_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a watchlist_fast_assn\<^sup>d \<rightarrow> watchlist_fast_assn\<close>
  supply [[goals_limit=1]] uint64_of_nat_conv_def[simp]
     arena_lit_pre_le_uint64_max[intro] append_aa64_hnr[sepref_fr_rules]
  unfolding rewatch_heur_alt_def Let_def two_uint64_nat_def[symmetric] PR_CONST_def
    one_uint64_nat_def[symmetric] to_watcher_fast_def[symmetric]
  apply (rewrite in \<open>append_ll _ (nat_of_lit _)\<close> nat_of_uint32_conv_def[symmetric])
  apply (rewrite in \<open>append_ll _ (nat_of_lit _)\<close> nat_of_uint32_conv_def[symmetric])
  apply (rewrite in \<open>append_ll _ (nat_of_lit _)\<close> nat_of_uint32_conv_def[symmetric])
  apply (rewrite in \<open>append_ll (append_ll _ _ _) (\<hole>)\<close> nat_of_uint32_conv_def[symmetric])
  by sepref

declare rewatch_heur_fast_code.refine[sepref_fr_rules]

sepref_definition rewatch_heur_st_fast_code
  is \<open>(rewatch_heur_st_fast)\<close>
  :: \<open>[rewatch_heur_st_fast_pre]\<^sub>a
       isasat_init_assn\<^sup>d \<rightarrow> isasat_init_assn\<close>
  supply [[goals_limit=1]]
  unfolding rewatch_heur_st_def PR_CONST_def rewatch_heur_st_fast_pre_def
    isasat_init_assn_def rewatch_heur_st_fast_def
  by sepref

declare rewatch_heur_st_code.refine[sepref_fr_rules]
  rewatch_heur_st_fast_code.refine[sepref_fr_rules]


sepref_register rewatch_heur_st init_dt_step_wl_heur

sepref_definition init_dt_wl_heur_code
  is \<open>uncurry (init_dt_wl_heur_unb)\<close>
  :: \<open>(list_assn (list_assn unat_lit_assn))\<^sup>k *\<^sub>a isasat_init_assn\<^sup>d \<rightarrow>\<^sub>a isasat_init_assn\<close>
  supply [[goals_limit=1]]
  unfolding init_dt_wl_heur_def PR_CONST_def init_dt_step_wl_heur_unb_def[symmetric] if_True
   init_dt_wl_heur_unb_def
  by sepref

sepref_definition init_dt_wl_heur_code_unb
  is \<open>uncurry (init_dt_wl_heur_unb)\<close>
  :: \<open>(list_assn (list_assn unat_lit_assn))\<^sup>k *\<^sub>a isasat_init_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a
      isasat_init_unbounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding init_dt_wl_heur_def PR_CONST_def init_dt_step_wl_heur_unb_def[symmetric] if_True
   init_dt_wl_heur_unb_def
  by sepref

declare init_dt_wl_heur_code.refine[sepref_fr_rules]
  init_dt_wl_heur_code_unb.refine[sepref_fr_rules]

sepref_definition init_dt_wl_heur_full_code
  is \<open>uncurry (init_dt_wl_heur_full_unb)\<close>
  :: \<open>(list_assn (list_assn unat_lit_assn))\<^sup>k *\<^sub>a isasat_init_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a
      isasat_init_unbounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding init_dt_wl_heur_full_def PR_CONST_def init_dt_wl_heur_full_unb_def
    init_dt_wl_heur_unb_def[symmetric]
  by sepref

declare init_dt_wl_heur_full_code.refine[sepref_fr_rules]


sepref_definition (in -) extract_lits_sorted_code
   is \<open>extract_lits_sorted\<close>
   :: \<open>[\<lambda>(xs, n, vars). (\<forall>x\<in>#mset vars. x < length xs)]\<^sub>a
      isasat_atms_ext_rel_assn\<^sup>d  \<rightarrow>
       arl_assn uint32_nat_assn *a uint32_nat_assn\<close>
  unfolding extract_lits_sorted_def
  supply [[goals_limit = 1]]
  supply mset_eq_setD[dest] mset_eq_length[dest]
  by sepref

declare extract_lits_sorted_code.refine[sepref_fr_rules]


abbreviation lits_with_max_assn where
  \<open>lits_with_max_assn \<equiv> hr_comp (arl_assn uint32_nat_assn *a uint32_nat_assn) lits_with_max_rel\<close>

lemma extract_lits_sorted_hnr[sepref_fr_rules]:
  \<open>(extract_lits_sorted_code, RETURN \<circ> mset_set) \<in> nat_lit_list_hm_assn\<^sup>d \<rightarrow>\<^sub>a lits_with_max_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE isasat_atms_ext_rel (\<lambda>_. True)
         (\<lambda>_ (xs, n, vars). \<forall>x\<in>#mset vars. x < length xs) (\<lambda>_. True)]\<^sub>a
       hrp_comp (isasat_atms_ext_rel_assn\<^sup>d) isasat_atms_ext_rel \<rightarrow> lits_with_max_assn\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF extract_lits_sorted_code.refine
    extract_lits_sorted_mset_set[unfolded convert_fref]] .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that by (auto simp: comp_PRE_def isasat_atms_ext_rel_def init_valid_rep_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep by simp
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im PR_CONST_def apply assumption
    using pre ..
qed


sepref_definition finalise_init_code'
  is \<open>uncurry finalise_init_code\<close>
  :: \<open>[\<lambda>(_, S). length (get_clauses_wl_heur_init S) \<le> uint64_max]\<^sub>a
      opts_assn\<^sup>d *\<^sub>a isasat_init_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply zero_uin64_hnr[sepref_fr_rules] [[goals_limit=1]]
    Pos_unat_lit_assn'[sepref_fr_rules] uint_max_def[simp] op_arl_replicate_def[simp]
  unfolding finalise_init_code_def isasat_init_assn_def isasat_bounded_assn_def
     arl_fold_custom_replicate two_uint32_def[symmetric]
  apply (rewrite at \<open>(_, \<hole>, _)\<close> arl64_of_arl_def[symmetric])
  apply (rewrite at \<open>(_, \<hole>, _)\<close> arl.fold_custom_empty)
  apply (rewrite in \<open>op_arl_empty\<close> annotate_assn[where A=\<open>vdom_assn\<close>])
  apply (rewrite at \<open>(_, \<hole>)\<close> arl64.fold_custom_empty)
  apply (rewrite in \<open>op_arl64_empty\<close> annotate_assn[where A=\<open>arena_fast_assn\<close>])
  by sepref

sepref_definition finalise_init_code_unb
  is \<open>uncurry finalise_init_code\<close>
  :: \<open>opts_assn\<^sup>d *\<^sub>a isasat_init_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply zero_uin64_hnr[sepref_fr_rules] [[goals_limit=1]]
    Pos_unat_lit_assn'[sepref_fr_rules] uint_max_def[simp] op_arl_replicate_def[simp]
  unfolding finalise_init_code_def isasat_init_unbounded_assn_def isasat_unbounded_assn_def
    IICF_Array_List.arl.fold_custom_empty arl_fold_custom_replicate two_uint32_def[symmetric] zero_uint64_nat_def
  by sepref

declare finalise_init_code'.refine[sepref_fr_rules]
  finalise_init_code_unb.refine[sepref_fr_rules]


lemma (in -)arrayO_raa_empty_sz_empty_list[sepref_fr_rules]:
  \<open>(arrayO_raa_empty_sz, RETURN o init_aa) \<in>
    nat_assn\<^sup>k \<rightarrow>\<^sub>a (arlO_assn clause_ll_assn)\<close>
  by sepref_to_hoare (sep_auto simp: init_rll_def hr_comp_def clauses_ll_assn_def init_aa_def)

lemma init_aa'_alt_def: \<open>RETURN o init_aa' = (\<lambda>n. RETURN op_arl_empty)\<close>
  by (auto simp: init_aa'_def op_arl_empty_def)

sepref_definition init_aa'_code
  is \<open>RETURN o init_aa'\<close>
  :: \<open>nat_assn\<^sup>k \<rightarrow>\<^sub>a arl_assn (clause_status_assn *a uint32_nat_assn *a uint32_nat_assn)\<close>
  unfolding init_aa'_alt_def
  by sepref

declare init_aa'_code.refine[sepref_fr_rules]


sepref_register initialise_VMTF


sepref_definition init_trail_D_code
  is \<open>uncurry2 init_trail_D\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a trail_pol_assn\<close>
  unfolding init_trail_D_def PR_CONST_def
  apply (rewrite in \<open>let _ = \<hole> in _\<close> arl.fold_custom_empty)
  apply (rewrite in \<open>let _ = \<hole> in _\<close> annotate_assn[where A=\<open>arl_assn unat_lit_assn\<close>])
  apply (rewrite in \<open>let _ = _; _ = \<hole> in _\<close> IICF_Array_List.arl.fold_custom_empty)
  apply (rewrite in \<open>let _ = _; _ = \<hole> in _\<close> annotate_assn[where A=\<open>arl_assn uint32_nat_assn\<close>])

  apply (rewrite in \<open>let _ = _;_ = \<hole> in _\<close> annotate_assn[where A=\<open>array_assn (tri_bool_assn)\<close>])
  apply (rewrite in \<open>let _ = _;_ = _;_ = \<hole> in _\<close> annotate_assn[where A=\<open>array_assn uint32_nat_assn\<close>])
  apply (rewrite in \<open>let _ = _ in _\<close> array_fold_custom_replicate)
  apply (rewrite in \<open>let _ = _ in _\<close> array_fold_custom_replicate)
  apply (rewrite in \<open>let _ = _ in _\<close> array_fold_custom_replicate)
  supply [[goals_limit = 1]]
  by sepref

declare init_trail_D_code.refine[sepref_fr_rules]

sepref_definition init_trail_D_fast_code
  is \<open>uncurry2 init_trail_D_fast\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a trail_pol_fast_assn\<close>
  unfolding init_trail_D_def PR_CONST_def init_trail_D_fast_def
  apply (rewrite in \<open>let _ = \<hole> in _\<close> arl32.fold_custom_empty)
  apply (rewrite in \<open>let _ = \<hole> in _\<close> annotate_assn[where A=\<open>arl32_assn unat_lit_assn\<close>])
  apply (rewrite in \<open>let _ = _; _ = \<hole> in _\<close> arl32.fold_custom_empty)
  apply (rewrite in \<open>let _ = _; _ = \<hole> in _\<close> annotate_assn[where A=\<open>arl32_assn uint32_nat_assn\<close>])

  apply (rewrite in \<open>let _ = _;_ = \<hole> in _\<close> annotate_assn[where A=\<open>array_assn (tri_bool_assn)\<close>])
  apply (rewrite in \<open>let _ = _;_ = _;_ = \<hole> in _\<close> annotate_assn[where A=\<open>array_assn uint32_nat_assn\<close>])
  apply (rewrite in \<open>let _ = _ in _\<close> array_fold_custom_replicate)
  apply (rewrite in \<open>let _ = _ in _\<close> array_fold_custom_replicate)
  apply (rewrite in \<open>let _ = _ in _\<close> array_fold_custom_replicate)
  apply (rewrite in \<open>let _ = op_array_replicate _ \<hole> in _\<close> one_uint64_nat_def[symmetric])
  supply [[goals_limit = 1]]
  by sepref

declare init_trail_D_fast_code.refine[sepref_fr_rules]


sepref_definition init_state_wl_D'_code
  is \<open>init_state_wl_D'\<close>
  :: \<open>(arl_assn uint32_assn *a uint32_assn)\<^sup>d \<rightarrow>\<^sub>a isasat_init_assn\<close>
  unfolding init_state_wl_D'_def PR_CONST_def init_trail_D_fast_def[symmetric] isasat_init_assn_def
  apply (rewrite at \<open>let _ = (_, \<hole>) in _\<close> IICF_Array_List.arl.fold_custom_empty)
  apply (rewrite at \<open>let _ = \<hole> in _\<close>  init_lrl_def[symmetric])
  unfolding array_fold_custom_replicate init_lrl64_def[symmetric]
  apply (rewrite at \<open>let _ = \<hole> in let _ = (True, _, _) in _\<close> IICF_Array_List.arl.fold_custom_empty)
  apply (rewrite at \<open>let _ = \<hole> in _\<close> annotate_assn[where A=\<open>arena_assn\<close>])
  apply (rewrite at \<open>let _= _; _= \<hole> in _\<close> annotate_assn[where A=\<open>watchlist_fast_assn\<close>])
  apply (rewrite at \<open>let _= \<hole> in RETURN _\<close> IICF_Array_List.arl.fold_custom_empty)
  supply [[goals_limit = 1]]
  by sepref

sepref_definition init_state_wl_D'_code_unb
  is \<open>init_state_wl_D'\<close>
  :: \<open>(arl_assn uint32_assn *a uint32_assn)\<^sup>d \<rightarrow>\<^sub>a trail_pol_assn *a arena_assn *a
    conflict_option_rel_assn *a
    uint32_nat_assn *a
    watchlist_assn *a
    vmtf_remove_conc_option_fst_As *a
    phase_saver_conc *a uint32_nat_assn *a
    cach_refinement_l_assn *a lbd_assn *a vdom_assn *a bool_assn\<close>
  unfolding init_state_wl_D'_def PR_CONST_def
  apply (rewrite at \<open>let _ = (_, \<hole>) in _\<close> IICF_Array_List.arl.fold_custom_empty)
  apply (rewrite at \<open>let _ = \<hole> in _\<close>  init_lrl_def[symmetric])
  unfolding array_fold_custom_replicate
  apply (rewrite at \<open>let _ = \<hole> in let _ = (True, _, _) in _\<close> IICF_Array_List.arl.fold_custom_empty)
  apply (rewrite at \<open>let _ = \<hole> in _\<close> annotate_assn[where A=\<open>arena_assn\<close>])
  apply (rewrite at \<open>let _= _; _= \<hole> in _\<close> annotate_assn[where A=\<open>watchlist_assn\<close>])
  apply (rewrite at \<open>let _= \<hole> in RETURN _\<close> IICF_Array_List.arl.fold_custom_empty)
  supply [[goals_limit = 1]]
  by sepref

declare init_state_wl_D'_code.refine[sepref_fr_rules]
  init_state_wl_D'_code_unb.refine[sepref_fr_rules]


lemma to_init_state_code_hnr:
  \<open>(return o to_init_state_code, RETURN o id) \<in> isasat_init_assn\<^sup>d \<rightarrow>\<^sub>a isasat_init_assn\<close>
  unfolding to_init_state_code_def
  by (rule id_ref)

abbreviation (in -)lits_with_max_assn_clss where
  \<open>lits_with_max_assn_clss \<equiv> hr_comp lits_with_max_assn (\<langle>nat_rel\<rangle>mset_rel)\<close>

end