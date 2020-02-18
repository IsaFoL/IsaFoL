theory IsaSAT_Initialisation_LLVM
  imports IsaSAT_Setup_LLVM IsaSAT_VMTF_LLVM Watched_Literals.Watched_Literals_Watch_List_Initialisation
  Watched_Literals.Watched_Literals_Watch_List_Initialisation
    IsaSAT_Initialisation
begin


abbreviation unat_rel32 :: \<open>(32 word \<times> nat) set\<close> where \<open>unat_rel32 \<equiv> unat_rel\<close>
abbreviation unat_rel64 :: \<open>(64 word \<times> nat) set\<close> where \<open>unat_rel64 \<equiv> unat_rel\<close>
abbreviation snat_rel32 :: \<open>(32 word \<times> nat) set\<close> where \<open>snat_rel32 \<equiv> snat_rel\<close>
abbreviation snat_rel64 :: \<open>(64 word \<times> nat) set\<close> where \<open>snat_rel64 \<equiv> snat_rel\<close>

type_synonym (in -)vmtf_assn_option_fst_As =
  \<open>vmtf_node_assn ptr \<times> 64 word \<times> 32 word \<times> 32 word \<times> 32 word\<close>

type_synonym (in -)vmtf_remove_assn_option_fst_As =
  \<open>vmtf_assn_option_fst_As \<times> (32 word array_list64) \<times> 1 word ptr\<close>

abbreviation (in -) vmtf_conc_option_fst_As :: \<open>_ \<Rightarrow> _ \<Rightarrow> llvm_amemory \<Rightarrow> bool\<close> where
  \<open>vmtf_conc_option_fst_As \<equiv> (array_assn vmtf_node_assn \<times>\<^sub>a uint64_nat_assn \<times>\<^sub>a
    atom.option_assn \<times>\<^sub>a atom.option_assn \<times>\<^sub>a atom.option_assn)\<close>

abbreviation vmtf_remove_conc_option_fst_As
  :: \<open>isa_vmtf_remove_int_option_fst_As \<Rightarrow> vmtf_remove_assn_option_fst_As \<Rightarrow> assn\<close>
where
  \<open>vmtf_remove_conc_option_fst_As \<equiv> vmtf_conc_option_fst_As \<times>\<^sub>a distinct_atoms_assn\<close>

sepref_register atoms_hash_empty
sepref_def (in -) atoms_hash_empty_code
  is \<open>atoms_hash_int_empty\<close>
:: \<open>sint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a atoms_hash_assn\<close>
  unfolding atoms_hash_int_empty_def array_fold_custom_replicate
  by sepref

sepref_def distinct_atms_empty_code
  is \<open>distinct_atms_int_empty\<close>
  :: \<open>sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a distinct_atoms_assn\<close>
  unfolding distinct_atms_int_empty_def array_fold_custom_replicate
    al_fold_custom_empty[where 'l=64]
  by sepref

lemmas [sepref_fr_rules] = distinct_atms_empty_code.refine atoms_hash_empty_code.refine

type_synonym (in -)twl_st_wll_trail_init =
  \<open>trail_pol_fast_assn \<times> arena_assn \<times> option_lookup_clause_assn \<times>
    64 word \<times> watched_wl_uint32 \<times> vmtf_remove_assn_option_fst_As \<times> phase_saver_assn \<times>
    32 word \<times> cach_refinement_l_assn \<times> lbd_assn \<times> vdom_fast_assn \<times> 1 word\<close>

definition isasat_init_assn
  :: \<open>twl_st_wl_heur_init \<Rightarrow> trail_pol_fast_assn \<times> arena_assn \<times> option_lookup_clause_assn \<times>
       64 word \<times> watched_wl_uint32 \<times> _ \<times> phase_saver_assn \<times>
       32 word \<times> cach_refinement_l_assn \<times> lbd_assn \<times> vdom_fast_assn \<times> 1 word \<Rightarrow> assn\<close>
where
\<open>isasat_init_assn =
  trail_pol_fast_assn \<times>\<^sub>a arena_fast_assn \<times>\<^sub>a
  conflict_option_rel_assn \<times>\<^sub>a
  sint64_nat_assn \<times>\<^sub>a
  watchlist_fast_assn \<times>\<^sub>a
  vmtf_remove_conc_option_fst_As \<times>\<^sub>a phase_saver_assn \<times>\<^sub>a
  uint32_nat_assn \<times>\<^sub>a
  cach_refinement_l_assn \<times>\<^sub>a
  lbd_assn \<times>\<^sub>a
  vdom_fast_assn \<times>\<^sub>a
  bool1_assn\<close>

sepref_def initialise_VMTF_code
  is \<open>uncurry initialise_VMTF\<close>
  :: \<open>[\<lambda>(N, n). True]\<^sub>a (arl64_assn atom_assn)\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> vmtf_remove_conc_option_fst_As\<close>
  unfolding initialise_VMTF_def vmtf_cons_def Suc_eq_plus1 atom.fold_option length_uint32_nat_def
    option.case_eq_if
  apply (rewrite in \<open>let _ = \<hole> in _ \<close> array_fold_custom_replicate op_list_replicate_def[symmetric])
  apply (rewrite at 0 in \<open>VMTF_Node \<hole>\<close> unat_const_fold[where 'a=64])
  apply (rewrite at \<open>VMTF_Node (\<hole> + 1)\<close> annot_snat_unat_conv)
  apply (rewrite at 1 in \<open>VMTF_Node \<hole>\<close> unat_const_fold[where 'a=64])
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  apply (rewrite in \<open>list_update _ _ _\<close> annot_index_of_atm)
  apply (rewrite in \<open>if _ then _ else list_update _ _ _\<close> annot_index_of_atm)
  apply (rewrite at \<open>\<hole>\<close> in \<open>_ ! atom.the _\<close> annot_index_of_atm)+
  apply (rewrite at \<open>RETURN ((_, \<hole>, _), _)\<close> annot_snat_unat_conv)
  supply [[goals_limit = 1]]
  by sepref

declare initialise_VMTF_code.refine[sepref_fr_rules]
sepref_register cons_trail_Propagated_tr
sepref_def propagate_unit_cls_code
  is \<open>uncurry (propagate_unit_cls_heur)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_init_assn\<^sup>d \<rightarrow>\<^sub>a isasat_init_assn\<close>
  supply [[goals_limit=1]] DECISION_REASON_def[simp]
  unfolding propagate_unit_cls_heur_def isasat_init_assn_def
    PR_CONST_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

declare propagate_unit_cls_code.refine[sepref_fr_rules]

definition already_propagated_unit_cls_heur' where
  \<open>already_propagated_unit_cls_heur' = (\<lambda>(M, N, D, Q, oth).
     RETURN (M, N, D, Q, oth))\<close>

lemma already_propagated_unit_cls_heur'_alt:
  \<open>already_propagated_unit_cls_heur L = already_propagated_unit_cls_heur'\<close>
  unfolding already_propagated_unit_cls_heur_def already_propagated_unit_cls_heur'_def
  by auto

sepref_def already_propagated_unit_cls_code
  is \<open>already_propagated_unit_cls_heur'\<close>
  :: \<open>isasat_init_assn\<^sup>d  \<rightarrow>\<^sub>a isasat_init_assn\<close>
  supply [[goals_limit=1]]
  unfolding already_propagated_unit_cls_heur'_def isasat_init_assn_def
  PR_CONST_def
  by sepref

declare already_propagated_unit_cls_code.refine[sepref_fr_rules]


sepref_def set_conflict_unit_code
  is \<open>uncurry set_conflict_unit_heur\<close>
  :: \<open>[\<lambda>(L, (b, n, xs)). atm_of L < length xs]\<^sub>a
        unat_lit_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d \<rightarrow> conflict_option_rel_assn\<close>
  supply [[goals_limit=1]]
  unfolding set_conflict_unit_heur_def ISIN_def[symmetric] conflict_option_rel_assn_def
    lookup_clause_rel_assn_def
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref

declare set_conflict_unit_code.refine[sepref_fr_rules]

sepref_def conflict_propagated_unit_cls_code
  is \<open>uncurry (conflict_propagated_unit_cls_heur)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_init_assn\<^sup>d  \<rightarrow>\<^sub>a isasat_init_assn\<close>
  supply [[goals_limit=1]]
  unfolding conflict_propagated_unit_cls_heur_def isasat_init_assn_def
  PR_CONST_def
  by sepref



declare conflict_propagated_unit_cls_code.refine[sepref_fr_rules]

sepref_register fm_add_new


lemma add_init_cls_code_bI:
  assumes
    \<open>length at' \<le> Suc (Suc uint32_max)\<close> and
    \<open>2 \<le> length at'\<close> and
    \<open>length a1'j \<le> length a1'a\<close> and
    \<open>length a1'a \<le> sint64_max - length at' - 5\<close>
  shows \<open>append_and_length_fast_code_pre ((True, at'), a1'a)\<close> \<open>5 \<le> sint64_max - length at'\<close>
  using assms unfolding append_and_length_fast_code_pre_def
  by (auto simp: uint64_max_def uint32_max_def sint64_max_def)

lemma add_init_cls_code_bI2:
  assumes
    \<open>length at' \<le> Suc (Suc uint32_max)\<close>
  shows \<open>5 \<le> sint64_max - length at'\<close>
  using assms unfolding append_and_length_fast_code_pre_def
  by (auto simp: uint64_max_def uint32_max_def sint64_max_def)

lemma add_init_clss_codebI:
  assumes
    \<open>length at' \<le> Suc (Suc uint32_max)\<close> and
    \<open>2 \<le> length at'\<close> and
    \<open>length a1'j \<le> length a1'a\<close> and
    \<open>length a1'a \<le> uint64_max - (length at' + 5)\<close>
  shows \<open>length a1'j < uint64_max\<close>
  using assms by (auto simp: uint64_max_def uint32_max_def)

abbreviation clauses_ll_assn where
  \<open>clauses_ll_assn \<equiv> aal_assn' TYPE(64) TYPE(64) unat_lit_assn\<close>

definition fm_add_new_fast' where
  \<open>fm_add_new_fast' b C i = fm_add_new_fast b (C!i)\<close>

lemma op_list_list_llen_alt_def: \<open>op_list_list_llen xss i = length (xss ! i)\<close>
  unfolding op_list_list_llen_def
  by auto

lemma op_list_list_idx_alt_def: \<open>op_list_list_idx xs i j = xs ! i ! j\<close>
  unfolding op_list_list_idx_def ..

sepref_def append_and_length_fast_code
  is \<open>uncurry3 fm_add_new_fast'\<close>
  :: \<open>[\<lambda>(((b, C), i), N). i < length C \<and> append_and_length_fast_code_pre ((b, C!i), N)]\<^sub>a
     bool1_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a (arena_fast_assn)\<^sup>d \<rightarrow>
       arena_fast_assn \<times>\<^sub>a sint64_nat_assn\<close>
  supply [[goals_limit=1]]
  supply [simp] = fm_add_new_bounds1[simplified] shorten_lbd_le
  supply [split] = if_splits
  unfolding fm_add_new_fast_def fm_add_new_def append_and_length_fast_code_pre_def
    fm_add_new_fast'_def op_list_list_llen_alt_def[symmetric] op_list_list_idx_alt_def[symmetric]
    is_short_clause_def header_size_def
  apply (rewrite at \<open>APos \<hole>\<close> unat_const_fold[where 'a=32])+
  apply (rewrite at \<open>op_list_list_llen _ _ - 2\<close> annot_snat_unat_downcast[where 'l=32])
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_register fm_add_new_fast'

sepref_def add_init_cls_code_b
  is \<open>uncurry2 add_init_cls_heur_b'\<close>
  :: \<open>[\<lambda>((xs, i), S). i < length xs]\<^sub>a
     (clauses_ll_assn)\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_init_assn\<^sup>d  \<rightarrow> isasat_init_assn\<close>
  supply [[goals_limit=1]] append_ll_def[simp]add_init_clss_codebI[intro]
    add_init_cls_code_bI[intro]  add_init_cls_code_bI2[intro]
  unfolding add_init_cls_heur_def add_init_cls_heur_b_def
  PR_CONST_def
  Let_def length_uint64_nat_def add_init_cls_heur_b'_def
  op_list_list_llen_alt_def[symmetric] op_list_list_idx_alt_def[symmetric]
  unfolding isasat_init_assn_def
    nth_rll_def[symmetric] delete_index_and_swap_update_def[symmetric]
    delete_index_and_swap_ll_def[symmetric]
    append_ll_def[symmetric] fm_add_new_fast_def[symmetric]
  fm_add_new_fast'_def[symmetric]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

declare
   add_init_cls_code_b.refine[sepref_fr_rules]

sepref_def already_propagated_unit_cls_conflict_code
  is \<open>uncurry already_propagated_unit_cls_conflict_heur\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_init_assn\<^sup>d  \<rightarrow>\<^sub>a isasat_init_assn\<close>
  supply [[goals_limit=1]]
  unfolding already_propagated_unit_cls_conflict_heur_def isasat_init_assn_def
    PR_CONST_def
  by sepref

declare already_propagated_unit_cls_conflict_code.refine[sepref_fr_rules]

sepref_def (in -) set_conflict_empty_code
  is \<open>RETURN o lookup_set_conflict_empty\<close>
  :: \<open>conflict_option_rel_assn\<^sup>d  \<rightarrow>\<^sub>a conflict_option_rel_assn\<close>
  supply [[goals_limit=1]]
  unfolding lookup_set_conflict_empty_def conflict_option_rel_assn_def
  by sepref

declare set_conflict_empty_code.refine[sepref_fr_rules]

sepref_def set_empty_clause_as_conflict_code
  is \<open>set_empty_clause_as_conflict_heur\<close>
  :: \<open>isasat_init_assn\<^sup>d \<rightarrow>\<^sub>a isasat_init_assn\<close>
  supply [[goals_limit=1]]
  unfolding set_empty_clause_as_conflict_heur_def isasat_init_assn_def
    conflict_option_rel_assn_def lookup_clause_rel_assn_def
  by sepref

declare set_empty_clause_as_conflict_code.refine[sepref_fr_rules]

definition (in -) add_clause_to_others_heur'
   :: \<open>twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close> where
  \<open>add_clause_to_others_heur' = (\<lambda> (M, N, D, Q, NS, US, WS).
      RETURN (M, N, D, Q, NS, US, WS))\<close>

lemma add_clause_to_others_heur'_alt: \<open>add_clause_to_others_heur L = add_clause_to_others_heur'\<close>
  unfolding add_clause_to_others_heur'_def add_clause_to_others_heur_def
  ..
sepref_def add_clause_to_others_code
  is \<open>add_clause_to_others_heur'\<close>
  :: \<open>isasat_init_assn\<^sup>d \<rightarrow>\<^sub>a isasat_init_assn\<close>
  supply [[goals_limit=1]]
  unfolding add_clause_to_others_heur_def isasat_init_assn_def add_clause_to_others_heur'_def
  by sepref

declare add_clause_to_others_code.refine[sepref_fr_rules]

sepref_def get_conflict_wl_is_None_init_code
  is \<open>RETURN o get_conflict_wl_is_None_heur_init\<close>
  :: \<open>isasat_init_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding get_conflict_wl_is_None_heur_init_alt_def isasat_init_assn_def length_ll_def[symmetric]
    conflict_option_rel_assn_def
  supply [[goals_limit=1]]
  by sepref

declare get_conflict_wl_is_None_init_code.refine[sepref_fr_rules]

sepref_def polarity_st_heur_init_code
  is \<open>uncurry (RETURN oo polarity_st_heur_init)\<close>
  :: \<open>[\<lambda>(S, L). polarity_pol_pre (get_trail_wl_heur_init S) L]\<^sub>a isasat_init_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> tri_bool_assn\<close>
  unfolding polarity_st_heur_init_def isasat_init_assn_def
  supply [[goals_limit = 1]]
  by sepref


declare polarity_st_heur_init_code.refine[sepref_fr_rules]

sepref_register init_dt_step_wl
  get_conflict_wl_is_None_heur_init already_propagated_unit_cls_heur
  conflict_propagated_unit_cls_heur add_clause_to_others_heur
  add_init_cls_heur set_empty_clause_as_conflict_heur

sepref_register polarity_st_heur_init propagate_unit_cls_heur

lemma is_Nil_length: \<open>is_Nil xs \<longleftrightarrow> length xs = 0\<close>
  by (cases xs) auto

definition init_dt_step_wl_heur_b'
   :: \<open>nat clause_l list \<Rightarrow> nat \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close> where
\<open>init_dt_step_wl_heur_b' C i = init_dt_step_wl_heur_b (C!i)\<close>


sepref_def init_dt_step_wl_code_b
  is \<open>uncurry2 (init_dt_step_wl_heur_b')\<close>
  :: \<open>[\<lambda>((xs, i), S). i < length xs]\<^sub>a (clauses_ll_assn)\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_init_assn\<^sup>d \<rightarrow>
       isasat_init_assn\<close>
  supply [[goals_limit=1]]
  supply polarity_None_undefined_lit[simp] polarity_st_init_def[simp]
  option.splits[split] get_conflict_wl_is_None_heur_init_alt_def[simp]
  tri_bool_eq_def[simp]
  unfolding init_dt_step_wl_heur_def PR_CONST_def
    init_dt_step_wl_heur_b_def
    init_dt_step_wl_heur_b'_def list_length_1_def is_Nil_length
    op_list_list_llen_alt_def[symmetric] op_list_list_idx_alt_def[symmetric]
    already_propagated_unit_cls_heur'_alt
    add_init_cls_heur_b'_def[symmetric] add_clause_to_others_heur'_def[symmetric]
    add_clause_to_others_heur'_alt
  unfolding watched_app_def[symmetric]
  unfolding nth_rll_def[symmetric]
  unfolding is_Nil_length get_conflict_wl_is_None_init
    polarity_st_heur_init_alt_def[symmetric]
    get_conflict_wl_is_None_heur_init_alt_def[symmetric]
    SET_TRUE_def[symmetric] SET_FALSE_def[symmetric] UNSET_def[symmetric]
    tri_bool_eq_def[symmetric]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

declare
  init_dt_step_wl_code_b.refine[sepref_fr_rules]


sepref_register init_dt_wl_heur_unb


abbreviation isasat_atms_ext_rel_assn where
  \<open>isasat_atms_ext_rel_assn \<equiv> larray64_assn uint64_nat_assn \<times>\<^sub>a uint32_nat_assn \<times>\<^sub>a
       arl64_assn atom_assn\<close>

abbreviation nat_lit_list_hm_assn where
  \<open>nat_lit_list_hm_assn \<equiv> hr_comp isasat_atms_ext_rel_assn isasat_atms_ext_rel\<close>


sepref_def init_next_size_impl
  is \<open>RETURN o init_next_size\<close>
  :: \<open>[\<lambda>L. L \<le> uint32_max div 2]\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> sint64_nat_assn\<close>
  unfolding init_next_size_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref


find_in_thms op_list_grow_init in sepref_fr_rules
sepref_def nat_lit_lits_init_assn_assn_in
  is \<open>uncurry add_to_atms_ext\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a isasat_atms_ext_rel_assn\<^sup>d \<rightarrow>\<^sub>a isasat_atms_ext_rel_assn\<close>
  supply [[goals_limit=1]]
  unfolding add_to_atms_ext_def length_uint32_nat_def
  apply (rewrite at \<open>max \<hole> _\<close> value_of_atm_def[symmetric])
  apply (rewrite at \<open>\<hole> < _\<close> value_of_atm_def[symmetric])
  apply (rewrite at \<open>list_grow _ (init_next_size \<hole>)\<close> value_of_atm_def[symmetric])
  apply (rewrite at \<open>list_grow _ (init_next_size \<hole>)\<close> index_of_atm_def[symmetric])
  apply (rewrite at \<open>\<hole> < _\<close> annot_unat_unat_upcast[where 'l=64])
  unfolding max_def list_grow_alt
    op_list_grow_init'_alt
  apply (annot_all_atm_idxs)
  apply (rewrite at \<open>op_list_grow_init \<hole>\<close> unat_const_fold[where 'a=64])
  apply (rewrite at \<open>_ < \<hole>\<close> annot_snat_unat_conv)
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref


find_theorems nfoldli WHILET
lemma [sepref_fr_rules]:
  \<open>(uncurry nat_lit_lits_init_assn_assn_in,  uncurry (RETURN \<circ>\<circ> op_set_insert))
  \<in> [\<lambda>(a, b). a \<le> uint32_max div 2]\<^sub>a
    atom_assn\<^sup>k *\<^sub>a nat_lit_list_hm_assn\<^sup>d \<rightarrow> nat_lit_list_hm_assn\<close>
  by (rule nat_lit_lits_init_assn_assn_in.refine[FCOMP add_to_atms_ext_op_set_insert
  [unfolded convert_fref op_set_insert_def[symmetric]]])

lemma while_nfoldli:
  "do {
    (_,\<sigma>) \<leftarrow> WHILE\<^sub>T (FOREACH_cond c) (\<lambda>x. do {ASSERT (FOREACH_cond c x); FOREACH_body f x}) (l,\<sigma>);
    RETURN \<sigma>
  } \<le> nfoldli l c f \<sigma>"
  apply (induct l arbitrary: \<sigma>)
  apply (subst WHILET_unfold)
  apply (simp add: FOREACH_cond_def)

  apply (subst WHILET_unfold)
  apply (auto
    simp: FOREACH_cond_def FOREACH_body_def
    intro: bind_mono Refine_Basic.bind_mono(1))
 done


definition extract_atms_cls_i' where
  \<open>extract_atms_cls_i' C i = extract_atms_cls_i (C!i)\<close>

(*TODO Move*)
lemma aal_assn_boundsD':
  assumes A: \<open>rdomp (aal_assn' TYPE('l::len2) TYPE('ll::len2) A) xss\<close> and \<open>i < length xss\<close>
  shows \<open>length (xss ! i) < max_snat LENGTH('ll)\<close>
  using aal_assn_boundsD_aux1[OF A] assms
  by auto

sepref_def extract_atms_cls_imp
  is \<open>uncurry2 extract_atms_cls_i'\<close>
  :: \<open>[\<lambda>((N, i), _). i < length N]\<^sub>a
      (clauses_ll_assn)\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a nat_lit_list_hm_assn\<^sup>d \<rightarrow> nat_lit_list_hm_assn\<close>
  supply [dest!] = aal_assn_boundsD'
  unfolding extract_atms_cls_i_def extract_atms_cls_i'_def
  apply (subst nfoldli_by_idx[abs_def])
  unfolding nfoldli_upt_by_while
    op_list_list_llen_alt_def[symmetric] op_list_list_idx_alt_def[symmetric]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

declare extract_atms_cls_imp.refine[sepref_fr_rules]

sepref_def extract_atms_clss_imp
  is \<open>uncurry extract_atms_clss_i\<close>
  :: \<open>(clauses_ll_assn)\<^sup>k *\<^sub>a nat_lit_list_hm_assn\<^sup>d \<rightarrow>\<^sub>a nat_lit_list_hm_assn\<close>
  supply [dest] = aal_assn_boundsD'
  unfolding extract_atms_clss_i_def
  apply (subst nfoldli_by_idx)
  unfolding nfoldli_upt_by_while Let_def extract_atms_cls_i'_def[symmetric]
    op_list_list_llen_alt_def[symmetric] op_list_list_idx_alt_def[symmetric]
    op_list_list_len_def[symmetric]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

lemma extract_atms_clss_hnr[sepref_fr_rules]:
  \<open>(uncurry extract_atms_clss_imp, uncurry (RETURN \<circ>\<circ> extract_atms_clss))
    \<in> [\<lambda>(a, b). \<forall>C\<in>set a. \<forall>L\<in>set C. nat_of_lit L \<le> uint32_max]\<^sub>a
      (clauses_ll_assn)\<^sup>k *\<^sub>a nat_lit_list_hm_assn\<^sup>d \<rightarrow> nat_lit_list_hm_assn\<close>
  using extract_atms_clss_imp.refine[FCOMP extract_atms_clss_i_extract_atms_clss[unfolded convert_fref]]
  by simp

sepref_def extract_atms_clss_imp_empty_assn
  is \<open>uncurry0 extract_atms_clss_imp_empty_rel\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a isasat_atms_ext_rel_assn\<close>
  unfolding extract_atms_clss_imp_empty_rel_def
    larray_fold_custom_replicate
  supply [[goals_limit=1]]
  apply (rewrite at \<open>(_, _, \<hole>)\<close> al_fold_custom_empty[where 'l=64])
  apply (rewrite in \<open>(\<hole>, _, _)\<close> annotate_assn[where A=\<open>larray64_assn uint64_nat_assn\<close>])
  apply (rewrite in \<open>(\<hole>, _, _)\<close> snat_const_fold[where 'a=64])
  apply (rewrite in \<open>(_, \<hole>, _)\<close> unat_const_fold[where 'a=32])
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

lemma extract_atms_clss_imp_empty_assn[sepref_fr_rules]:
  \<open>(uncurry0 extract_atms_clss_imp_empty_assn, uncurry0 (RETURN op_extract_list_empty))
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a nat_lit_list_hm_assn\<close>
  using extract_atms_clss_imp_empty_assn.refine[unfolded uncurry0_def, FCOMP extract_atms_clss_imp_empty_rel
    [unfolded convert_fref]]
  unfolding uncurry0_def
  by simp

lemma extract_atms_clss_imp_empty_rel_alt_def:
  \<open>extract_atms_clss_imp_empty_rel = (RETURN (op_larray_custom_replicate 1024 0, 0, []))\<close>
  by (auto simp: extract_atms_clss_imp_empty_rel_def)


subsubsection \<open>Full Initialisation\<close>

sepref_def rewatch_heur_st_fast_code
  is \<open>(rewatch_heur_st_fast)\<close>
  :: \<open>[rewatch_heur_st_fast_pre]\<^sub>a
       isasat_init_assn\<^sup>d \<rightarrow> isasat_init_assn\<close>
  supply [[goals_limit=1]]
  unfolding rewatch_heur_st_def PR_CONST_def rewatch_heur_st_fast_pre_def
    isasat_init_assn_def rewatch_heur_st_fast_def
  by sepref

declare
  rewatch_heur_st_fast_code.refine[sepref_fr_rules]


sepref_register rewatch_heur_st init_dt_step_wl_heur

sepref_def init_dt_wl_heur_code_b
  is \<open>uncurry (init_dt_wl_heur_b)\<close>
  :: \<open>(clauses_ll_assn)\<^sup>k *\<^sub>a isasat_init_assn\<^sup>d \<rightarrow>\<^sub>a
      isasat_init_assn\<close>
  supply [[goals_limit=1]]
  unfolding init_dt_wl_heur_def PR_CONST_def init_dt_step_wl_heur_b_def[symmetric] if_True
   init_dt_wl_heur_b_def
  apply (subst nfoldli_by_idx[abs_def])
  unfolding nfoldli_upt_by_while op_list_list_len_def[symmetric] Let_def
    init_dt_step_wl_heur_b'_def[symmetric]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

declare
  init_dt_wl_heur_code_b.refine[sepref_fr_rules]


definition extract_lits_sorted' where
  \<open>extract_lits_sorted' xs n vars = extract_lits_sorted (xs, n, vars)\<close>

lemma extract_lits_sorted_extract_lits_sorted':
   \<open>extract_lits_sorted = (\<lambda>(xs, n, vars). do {res \<leftarrow> extract_lits_sorted' xs n vars; mop_free xs; RETURN res})\<close>
  by (auto simp: extract_lits_sorted'_def mop_free_def intro!: ext)

sepref_def (in -) extract_lits_sorted'_impl
   is \<open>uncurry2 extract_lits_sorted'\<close>
   :: \<open>[\<lambda>((xs, n), vars). (\<forall>x\<in>#mset vars. x < length xs)]\<^sub>a
      (larray64_assn uint64_nat_assn)\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a
       (arl64_assn atom_assn)\<^sup>d  \<rightarrow>
       arl64_assn atom_assn \<times>\<^sub>a uint32_nat_assn\<close>
  unfolding extract_lits_sorted'_def extract_lits_sorted_def nres_monad1
    prod.case
  by sepref

lemmas [sepref_fr_rules] = extract_lits_sorted'_impl.refine


sepref_def (in -) extract_lits_sorted_code
   is \<open>extract_lits_sorted\<close>
   :: \<open>[\<lambda>(xs, n, vars). (\<forall>x\<in>#mset vars. x < length xs)]\<^sub>a
      isasat_atms_ext_rel_assn\<^sup>d  \<rightarrow>
       arl64_assn atom_assn \<times>\<^sub>a uint32_nat_assn\<close>
  apply (subst extract_lits_sorted_extract_lits_sorted')
  unfolding extract_lits_sorted'_def extract_lits_sorted_def nres_monad1
    prod.case
  supply [[goals_limit = 1]]
  supply mset_eq_setD[dest] mset_eq_length[dest]
  by sepref

declare extract_lits_sorted_code.refine[sepref_fr_rules]


abbreviation lits_with_max_assn where
  \<open>lits_with_max_assn \<equiv> hr_comp (arl64_assn atom_assn \<times>\<^sub>a uint32_nat_assn) lits_with_max_rel\<close>

lemma extract_lits_sorted_hnr[sepref_fr_rules]:
  \<open>(extract_lits_sorted_code, RETURN \<circ> mset_set) \<in> nat_lit_list_hm_assn\<^sup>d \<rightarrow>\<^sub>a lits_with_max_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>hrr_comp isasat_atms_ext_rel
        (\<lambda>_ _. al_assn atom_assn \<times>\<^sub>a unat_assn) (\<lambda>_. lits_with_max_rel) =
       (\<lambda>_ _. lits_with_max_assn)\<close>
    by (auto simp: hrr_comp_def intro!: ext)

  have H: \<open>?c
    \<in> [comp_PRE isasat_atms_ext_rel (\<lambda>_. True)
         (\<lambda>_ (xs, n, vars). \<forall>x\<in>#mset vars. x < length xs) (\<lambda>_. True)]\<^sub>a
       hrp_comp (isasat_atms_ext_rel_assn\<^sup>d) isasat_atms_ext_rel \<rightarrow> lits_with_max_assn\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF extract_lits_sorted_code.refine
      extract_lits_sorted_mset_set[unfolded convert_fref]]
      unfolding H
    by auto

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


definition INITIAL_OUTL_SIZE :: \<open>nat\<close> where
[simp]: \<open>INITIAL_OUTL_SIZE = 160\<close>

sepref_def INITIAL_OUTL_SIZE_impl
  is \<open>uncurry0 (RETURN INITIAL_OUTL_SIZE)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  unfolding INITIAL_OUTL_SIZE_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

definition atom_of_value :: \<open>nat \<Rightarrow> nat\<close> where [simp]: \<open>atom_of_value x = x\<close>

lemma atom_of_value_simp_hnr:
  \<open>(\<exists>x. (\<up>(x = unat xi \<and> P x) \<and>* \<up>(x = unat xi)) s) =
    (\<exists>x. (\<up>(x = unat xi \<and> P x)) s)\<close>
  \<open>(\<exists>x. (\<up>(x = unat xi \<and> P x)) s) = (\<up>(P (unat xi))) s\<close>
  unfolding import_param_3[symmetric]
  by (auto simp: pred_lift_extract_simps)


lemma atom_of_value_hnr[sepref_fr_rules]:
   \<open>(return o (\<lambda>x. x), RETURN o atom_of_value) \<in> [\<lambda>n. n < 2 ^31]\<^sub>a (uint32_nat_assn)\<^sup>d \<rightarrow> atom_assn\<close>
  apply sepref_to_hoare
  apply vcg'
  apply (auto simp: unat_rel_def atom_rel_def unat.rel_def br_def ENTAILS_def
    atom_of_value_simp_hnr pure_true_conv Defer_Slot.remove_slot)
  apply (rule Defer_Slot.remove_slot)
  done

sepref_register atom_of_value

lemma [sepref_gen_algo_rules]: \<open>GEN_ALGO (Pos 0) (is_init unat_lit_assn)\<close>
  by (auto simp: unat_lit_rel_def is_init_def unat_rel_def unat.rel_def
    br_def nat_lit_rel_def GEN_ALGO_def)

sepref_def finalise_init_code'
  is \<open>uncurry finalise_init_code\<close>
  :: \<open>[\<lambda>(_, S). length (get_clauses_wl_heur_init S) \<le> sint64_max]\<^sub>a
      opts_assn\<^sup>d *\<^sub>a isasat_init_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply  [[goals_limit=1]]
  unfolding finalise_init_code_def isasat_init_assn_def isasat_bounded_assn_def
     INITIAL_OUTL_SIZE_def[symmetric] atom.fold_the vmtf_remove_assn_def
     heuristic_assn_def
  apply (rewrite at \<open>Pos \<hole>\<close> unat_const_fold[where 'a=32])
  apply (rewrite at \<open>Pos \<hole>\<close> atom_of_value_def[symmetric])
  apply (rewrite at \<open>take \<hole>\<close> snat_const_fold[where 'a=64])
  apply (rewrite at \<open>(_, _,_,\<hole>, _,_,_,_,_)\<close> snat_const_fold[where 'a=64])
  apply (rewrite at \<open>(_, _,_,\<hole>, _,_,_)\<close> snat_const_fold[where 'a=64])
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  apply (rewrite at \<open>(_, \<hole>, _)\<close> al_fold_custom_empty[where 'l=64])
  apply (rewrite at \<open>(_, \<hole>)\<close> al_fold_custom_empty[where 'l=64])
  apply (rewrite in \<open>take _ \<hole>\<close> al_fold_custom_replicate)
  apply (rewrite at \<open>replicate _ False\<close> annotate_assn[where A=phase_saver'_assn])
  apply (rewrite in \<open>replicate _ False\<close> array_fold_custom_replicate)
  apply (rewrite at \<open>replicate _ False\<close> annotate_assn[where A=phase_saver'_assn])
  apply (rewrite in \<open>replicate _ False\<close> array_fold_custom_replicate)
  by sepref

declare finalise_init_code'.refine[sepref_fr_rules]



(*sepref_definition init_aa'_code
  is \<open>RETURN o init_aa'\<close>
  :: \<open>sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a arl_assn (clause_status_assn \<times>\<^sub>a uint32_nat_assn \<times>\<^sub>a uint32_nat_assn)\<close>
  unfolding init_aa'_alt_def
  by sepref

declare init_aa'_code.refine[sepref_fr_rules]
*)


sepref_register initialise_VMTF
abbreviation snat64_assn :: \<open>nat \<Rightarrow> 64 word \<Rightarrow> _\<close> where \<open>snat64_assn \<equiv> snat_assn\<close>
abbreviation snat32_assn :: \<open>nat \<Rightarrow> 32 word \<Rightarrow> _\<close> where \<open>snat32_assn \<equiv> snat_assn\<close>
abbreviation unat64_assn :: \<open>nat \<Rightarrow> 64 word \<Rightarrow> _\<close> where \<open>unat64_assn \<equiv> unat_assn\<close>
abbreviation unat32_assn :: \<open>nat \<Rightarrow> 32 word \<Rightarrow> _\<close> where \<open>unat32_assn \<equiv> unat_assn\<close>

sepref_def init_trail_D_fast_code
  is \<open>uncurry2 init_trail_D_fast\<close>
  :: \<open>(arl64_assn atom_assn)\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a trail_pol_fast_assn\<close>
  unfolding init_trail_D_def PR_CONST_def init_trail_D_fast_def trail_pol_fast_assn_def
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

declare init_trail_D_fast_code.refine[sepref_fr_rules]

sepref_def init_state_wl_D'_code
  is \<open>init_state_wl_D'\<close>
  :: \<open>(arl64_assn atom_assn \<times>\<^sub>a uint32_nat_assn)\<^sup>k \<rightarrow>\<^sub>a isasat_init_assn\<close>
  supply[[goals_limit=1]]
  unfolding init_state_wl_D'_def PR_CONST_def init_trail_D_fast_def[symmetric] isasat_init_assn_def
   cach_refinement_l_assn_def Suc_eq_plus1_left conflict_option_rel_assn_def  lookup_clause_rel_assn_def
  apply (rewrite at \<open>let _ = 1 + \<hole> in _\<close> annot_unat_snat_upcast[where 'l=64])
  apply (rewrite at \<open>let _ = (_, \<hole>) in _\<close> al_fold_custom_empty[where 'l=64])
  apply (rewrite at \<open>let _ = (\<hole>,_) in _\<close> annotate_assn[where A= \<open>array_assn minimize_status_assn\<close>])
  apply (rewrite at \<open>let _ = (_, \<hole>) in _\<close> annotate_assn[where A= \<open>arl64_assn atom_assn\<close>])
  apply (rewrite in \<open>replicate _ []\<close> aal_fold_custom_empty(1)[where 'l=64 and 'll=64])
  apply (rewrite at \<open>let _= _; _= \<hole> in _\<close> annotate_assn[where A=\<open>watchlist_fast_assn\<close>])
  apply (rewrite at \<open>let _= \<hole>; _=_;_=_;_ = _ in RETURN _\<close> annotate_assn[where A=\<open>phase_saver_assn\<close>])
  apply (rewrite in \<open>let _= \<hole>; _=_;_=_;_ = _ in RETURN _\<close> larray_fold_custom_replicate)
  apply (rewrite in \<open>let _= (True, _, \<hole>) in  _\<close> array_fold_custom_replicate)
  unfolding array_fold_custom_replicate
  apply (rewrite at \<open>let _ = \<hole> in let _ = (True, _, _) in _\<close> al_fold_custom_empty[where 'l=64])
  apply (rewrite in \<open>let _= (True, \<hole>, _) in _\<close> unat_const_fold[where 'a=32])
  apply (rewrite at \<open>let _ = \<hole> in _\<close> annotate_assn[where A=\<open>arena_fast_assn\<close>])
  apply (rewrite at \<open>let _= \<hole> in RETURN _\<close> annotate_assn[where A = \<open>vdom_fast_assn\<close>])
  apply (rewrite in \<open>let _= \<hole> in RETURN _\<close> al_fold_custom_empty[where 'l=64])
  apply (rewrite at \<open>(_,\<hole>, _ ,_, _, False)\<close> unat_const_fold[where 'a=32])
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  apply (rewrite at \<open>RETURN \<hole>\<close> annotate_assn[where A=\<open>isasat_init_assn\<close>, unfolded isasat_init_assn_def
     conflict_option_rel_assn_def cach_refinement_l_assn_def lookup_clause_rel_assn_def])
  by sepref

declare init_state_wl_D'_code.refine[sepref_fr_rules]


lemma to_init_state_code_hnr:
  \<open>(return o to_init_state_code, RETURN o id) \<in> isasat_init_assn\<^sup>d \<rightarrow>\<^sub>a isasat_init_assn\<close>
  unfolding to_init_state_code_def
  by sepref_to_hoare vcg'

abbreviation (in -)lits_with_max_assn_clss where
  \<open>lits_with_max_assn_clss \<equiv> hr_comp lits_with_max_assn (\<langle>nat_rel\<rangle>mset_rel)\<close>


experiment
begin
  export_llvm init_state_wl_D'_code
    rewatch_heur_st_fast_code
    init_dt_wl_heur_code_b

end

end