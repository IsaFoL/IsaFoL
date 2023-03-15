theory IsaSAT_Initialisation_LLVM
  imports  IsaSAT_VMTF_LLVM Watched_Literals.Watched_Literals_Watch_List_Initialisation
    IsaSAT_Initialisation IsaSAT_Setup_LLVM IsaSAT_Mark_LLVM
    IsaSAT_Initialisation_State_LLVM
begin
hide_const (open) NEMonad.RETURN  NEMonad.ASSERT

definition split_vmtf2 :: \<open>bump_heuristics_option_fst_As \<Rightarrow> _\<close> where
  \<open>split_vmtf2 = (\<lambda>x. x)\<close>

sepref_def split_vmtf2_impl
  is \<open>RETURN o split_vmtf2\<close>
  :: \<open>vmtf_remove_conc_option_fst_As\<^sup>d \<rightarrow>\<^sub>a vmtf_conc_option_fst_As \<times>\<^sub>a distinct_atoms_assn\<close>
  unfolding split_vmtf2_def
  by sepref

definition polarity_st_heur_init :: \<open>twl_st_wl_heur_init \<Rightarrow> _\<close> where
  \<open>polarity_st_heur_init S L = polarity_pol (Tuple15_a S) L\<close>

definition polarity_st_heur_init_code :: \<open>twl_st_wll_trail_init \<Rightarrow> _\<close> where
  \<open>polarity_st_heur_init_code N C = IsaSAT_Init.read_all_st_code (\<lambda>M _ _ _ _ _ _ _ _ _ _ _ _ _ _. polarity_pol_fast_code M C) N\<close>

lemma polarity_st_heur_init_alt_def:
  \<open>(\<lambda>N C'. IsaSAT_Init.read_all_st (\<lambda>M _ _ _ _ _ _ _ _ _ _ _ _ _ _. (RETURN \<circ>\<circ> polarity_pol) M C') N) =
  RETURN oo polarity_st_heur_init\<close>
  by (auto simp: IsaSAT_Init.read_all_st_def polarity_st_heur_init_def intro!: ext
    split: tuple15.splits)

lemmas polarity_st_heur_init_code_refine [sepref_fr_rules] =
  IsaSAT_Init.read_trail_refine[OF polarity_pol_fast_code.refine,
  unfolded polarity_st_heur_init_alt_def polarity_st_heur_init_code_def[symmetric]]


definition get_conflict_wl_is_None_init_code :: \<open>twl_st_wll_trail_init \<Rightarrow> _\<close> where
  \<open>get_conflict_wl_is_None_init_code = IsaSAT_Init.read_all_st_code (\<lambda>_ _ M _ _ _ _ _ _ _ _ _ _ _ _. conflict_is_None_code M)\<close>

lemma get_conflict_wl_is_None_heur_init_alt_def:
  \<open>RETURN o get_conflict_wl_is_None_heur_init = IsaSAT_Init.read_all_st (\<lambda>_ _ M _ _ _ _ _ _ _ _ _ _ _ _. conflict_is_None M)\<close>
  by (auto simp: IsaSAT_Init.read_all_st_def polarity_st_heur_init_def get_conflict_wl_is_None_heur_init_def
    conflict_is_None_def
    intro!: ext
    split: tuple15.splits)

lemmas get_conflict_wl_is_None_init_code_refine [sepref_fr_rules] =
   IsaSAT_Init.read_conflict_refine0[OF conflict_is_None_code_refine,
    unfolded get_conflict_wl_is_None_init_code_def[symmetric] get_conflict_wl_is_None_heur_init_alt_def[symmetric]]

definition full_arena_length_st_init :: \<open>twl_st_wl_heur_init \<Rightarrow> _\<close> where
  \<open>full_arena_length_st_init S = length (get_clauses_wl_heur_init S)\<close>

lemma full_arena_length_st_init_alt_def:
  \<open>RETURN o full_arena_length_st_init = IsaSAT_Init.read_all_st (\<lambda>_ M _ _ _ _ _ _ _ _ _ _ _ _ _. (RETURN \<circ> length) M)\<close>
  by (auto simp: full_arena_length_st_init_def IsaSAT_Init.read_all_st_def
    intro!: ext
    split: tuple15.splits)

definition full_arena_length_st_init_code :: \<open>twl_st_wll_trail_init \<Rightarrow> _\<close> where
  \<open>full_arena_length_st_init_code = IsaSAT_Init.read_all_st_code (\<lambda>_ M _ _ _ _ _ _ _ _ _ _ _ _ _. arena_full_length_impl M)\<close>

definition clss_size_lcount_st_init :: \<open>twl_st_wl_heur_init \<Rightarrow> _\<close> where
  \<open>clss_size_lcount_st_init S = clss_size_lcount (get_learned_count_init S)\<close>

lemma clss_size_lcount_st_init_alt_def:
  \<open>RETURN o clss_size_lcount_st_init = IsaSAT_Init.read_all_st (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ M _. (RETURN \<circ> clss_size_lcount) M)\<close>
  by (auto simp: clss_size_lcount_st_init_def IsaSAT_Init.read_all_st_def
    intro!: ext
    split: tuple15.splits)

definition clss_size_lcount_st_init_impl :: \<open>twl_st_wll_trail_init \<Rightarrow> _\<close> where
  \<open>clss_size_lcount_st_init_impl = IsaSAT_Init.read_all_st_code (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ M _. clss_size_lcount_fast_code M)\<close>

definition clss_size_lcountUE_st_init :: \<open>twl_st_wl_heur_init \<Rightarrow> _\<close> where
  \<open>clss_size_lcountUE_st_init S = clss_size_lcountUE (get_learned_count_init S)\<close>

lemma clss_size_lcountUE_st_init_alt_def:
  \<open>RETURN o clss_size_lcountUE_st_init = IsaSAT_Init.read_all_st (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ M _. (RETURN \<circ> clss_size_lcountUE) M)\<close>
  by (auto simp: clss_size_lcountUE_st_init_def IsaSAT_Init.read_all_st_def
    intro!: ext
    split: tuple15.splits)

definition clss_size_lcountUE_st_init_impl :: \<open>twl_st_wll_trail_init \<Rightarrow> _\<close> where
  \<open>clss_size_lcountUE_st_init_impl = IsaSAT_Init.read_all_st_code (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ M _. clss_size_lcountUE_fast_code M)\<close>

definition clss_size_lcountUEk_st_init :: \<open>twl_st_wl_heur_init \<Rightarrow> _\<close> where
  \<open>clss_size_lcountUEk_st_init S = clss_size_lcountUEk (get_learned_count_init S)\<close>

lemma clss_size_lcountUEk_st_init_alt_def:
  \<open>RETURN o clss_size_lcountUEk_st_init = IsaSAT_Init.read_all_st (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ M _. (RETURN \<circ> clss_size_lcountUEk) M)\<close>
  by (auto simp: clss_size_lcountUEk_st_init_def IsaSAT_Init.read_all_st_def
    intro!: ext
    split: tuple15.splits)

definition clss_size_lcountUEk_st_init_impl :: \<open>twl_st_wll_trail_init \<Rightarrow> _\<close> where
  \<open>clss_size_lcountUEk_st_init_impl = IsaSAT_Init.read_all_st_code (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ M _. clss_size_lcountUEk_fast_code M)\<close>

definition clss_size_lcountUS_st_init :: \<open>twl_st_wl_heur_init \<Rightarrow> _\<close> where
  \<open>clss_size_lcountUS_st_init S = clss_size_lcountUS (get_learned_count_init S)\<close>

lemma clss_size_lcountUS_st_init_alt_def:
  \<open>RETURN o clss_size_lcountUS_st_init = IsaSAT_Init.read_all_st (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ M _. (RETURN \<circ> clss_size_lcountUS) M)\<close>
  by (auto simp: clss_size_lcountUS_st_init_def IsaSAT_Init.read_all_st_def
    intro!: ext
    split: tuple15.splits)

definition clss_size_lcountUS_st_init_impl :: \<open>twl_st_wll_trail_init \<Rightarrow> _\<close> where
  \<open>clss_size_lcountUS_st_init_impl = IsaSAT_Init.read_all_st_code (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ M _. clss_size_lcountUSt_fast_code M)\<close>

definition clss_size_lcountU0_st_init :: \<open>twl_st_wl_heur_init \<Rightarrow> _\<close> where
  \<open>clss_size_lcountU0_st_init S = clss_size_lcountU0 (get_learned_count_init S)\<close>

lemma clss_size_lcountU0_st_init_alt_def:
  \<open>RETURN o clss_size_lcountU0_st_init = IsaSAT_Init.read_all_st (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ M _. (RETURN \<circ> clss_size_lcountU0) M)\<close>
  by (auto simp: clss_size_lcountU0_st_init_def IsaSAT_Init.read_all_st_def
    intro!: ext
    split: tuple15.splits)

definition clss_size_lcountU0_st_init_impl :: \<open>twl_st_wll_trail_init \<Rightarrow> _\<close> where
  \<open>clss_size_lcountU0_st_init_impl = IsaSAT_Init.read_all_st_code (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ _ M _. clss_size_lcountU0_fast_code M)\<close>


definition is_failed_loc :: \<open>bool \<Rightarrow> bool\<close> where
  \<open>is_failed_loc x = x\<close>

sepref_def is_failed_loc_impl
  is \<open>RETURN o is_failed_loc\<close>
  :: \<open>bool1_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding is_failed_loc_def
  by sepref

lemma is_failed_heur_init_alt_def:
  \<open>RETURN o is_failed_heur_init = IsaSAT_Init.read_all_st (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ M _ _. (RETURN o is_failed_loc) M)\<close>
  by (auto simp: is_failed_loc_def IsaSAT_Init.read_all_st_def
    intro!: ext
    split: tuple15.splits)
definition is_failed_heur_init_impl :: \<open>twl_st_wll_trail_init \<Rightarrow> _\<close> where
  \<open>is_failed_heur_init_impl = IsaSAT_Init.read_all_st_code (\<lambda>_ _ _ _ _ _ _ _ _ _ _ _ M _ _. is_failed_loc_impl M)\<close>

lemmas [sepref_fr_rules] =
  IsaSAT_Init.read_b_refine0[OF arena_full_length_impl.refine,
    unfolded full_arena_length_st_init_code_def[symmetric] full_arena_length_st_init_alt_def[symmetric]]
  IsaSAT_Init.read_n_refine0[OF get_learned_count_number.not_deleted_code_refine,
    unfolded clss_size_lcount_st_init_impl_def[symmetric] clss_size_lcount_st_init_alt_def[symmetric]]
  IsaSAT_Init.read_n_refine0[OF clss_size_lcountUE_fast_code.refine,
    unfolded clss_size_lcountUE_st_init_impl_def[symmetric] clss_size_lcountUE_st_init_alt_def[symmetric]]
  IsaSAT_Init.read_n_refine0[OF clss_size_lcountUEk_fast_code.refine,
    unfolded clss_size_lcountUEk_st_init_impl_def[symmetric] clss_size_lcountUEk_st_init_alt_def[symmetric]]
  IsaSAT_Init.read_n_refine0[OF clss_size_lcountUSt_fast_code.refine,
    unfolded clss_size_lcountUS_st_init_impl_def[symmetric] clss_size_lcountUS_st_init_alt_def[symmetric]]
  IsaSAT_Init.read_n_refine0[OF clss_size_lcountU0_fast_code.refine,
    unfolded clss_size_lcountU0_st_init_impl_def[symmetric] clss_size_lcountU0_st_init_alt_def[symmetric]]
  IsaSAT_Init.read_m_refine0[OF is_failed_loc_impl.refine,
    unfolded is_failed_heur_init_impl_def[symmetric] is_failed_heur_init_alt_def[symmetric]]

lemmas [unfolded Tuple15_LLVM.inline_direct_return_node_case, llvm_code] =
  polarity_st_heur_init_code_def[unfolded IsaSAT_Init.read_all_st_code_def]
  full_arena_length_st_init_code_def[unfolded IsaSAT_Init.read_all_st_code_def]
  clss_size_lcount_st_init_impl_def[unfolded IsaSAT_Init.read_all_st_code_def]
  clss_size_lcountUE_st_init_impl_def[unfolded IsaSAT_Init.read_all_st_code_def]
  clss_size_lcountUEk_st_init_impl_def[unfolded IsaSAT_Init.read_all_st_code_def]
  clss_size_lcountUS_st_init_impl_def[unfolded IsaSAT_Init.read_all_st_code_def]
  clss_size_lcountU0_st_init_impl_def[unfolded IsaSAT_Init.read_all_st_code_def]
  is_failed_heur_init_impl_def[unfolded IsaSAT_Init.read_all_st_code_def]

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


abbreviation unat_rel32 :: \<open>(32 word \<times> nat) set\<close> where \<open>unat_rel32 \<equiv> unat_rel\<close>
abbreviation unat_rel64 :: \<open>(64 word \<times> nat) set\<close> where \<open>unat_rel64 \<equiv> unat_rel\<close>
abbreviation snat_rel32 :: \<open>(32 word \<times> nat) set\<close> where \<open>snat_rel32 \<equiv> snat_rel\<close>
abbreviation snat_rel64 :: \<open>(64 word \<times> nat) set\<close> where \<open>snat_rel64 \<equiv> snat_rel\<close>

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

lemma propagate_unit_cls_heur_b_alt_def:
  \<open>propagate_unit_cls_heur_b L S =
     do {
        let (M, S) = extract_trail_wl_heur_init S;
        M \<leftarrow> cons_trail_Propagated_tr L 0 M;
       RETURN (IsaSAT_Init.update_a M S)
     }\<close>
  by (cases S)
    (auto simp:propagate_unit_cls_heur_b_def propagate_unit_cls_heur_def isasat_init_getters_and_setters_def
      Let_def intro!: ext)

sepref_def propagate_unit_cls_code
  is \<open>uncurry (propagate_unit_cls_heur_b)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_init_assn\<^sup>d \<rightarrow>\<^sub>a isasat_init_assn\<close>
  supply [[goals_limit=1]] DECISION_REASON_def[simp]
  unfolding propagate_unit_cls_heur_b_alt_def
    PR_CONST_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

declare propagate_unit_cls_code.refine[sepref_fr_rules]

(*TODO Move*)

definition already_propagated_unit_cls_heur'
   :: \<open>bool \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close>
where
  \<open>already_propagated_unit_cls_heur' = (\<lambda>unbdd S. RETURN S)\<close>

lemma already_propagated_unit_cls_heur'_alt:
  \<open>already_propagated_unit_cls_heur unbd L = already_propagated_unit_cls_heur' unbd\<close>
  unfolding already_propagated_unit_cls_heur'_def already_propagated_unit_cls_heur_def
  by auto

definition already_propagated_unit_cls_heur_b where
  \<open>already_propagated_unit_cls_heur_b = already_propagated_unit_cls_heur' False\<close>

sepref_def already_propagated_unit_cls_code
  is \<open>already_propagated_unit_cls_heur_b\<close>
  :: \<open>isasat_init_assn\<^sup>d  \<rightarrow>\<^sub>a isasat_init_assn\<close>
  supply [[goals_limit=1]]
  unfolding already_propagated_unit_cls_heur'_def
  PR_CONST_def already_propagated_unit_cls_heur_b_def
  by sepref


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

lemma conflict_propagated_unit_cls_heur_b_alt_def:
  \<open>conflict_propagated_unit_cls_heur_b L S =
     do {
       let (D, S) = extract_conflict_wl_heur_init S;
       let (M, S) = extract_trail_wl_heur_init S;
       Refine_Basic.ASSERT(atm_of L < length (snd (snd D)));
       D \<leftarrow> set_conflict_unit_heur L D;
       Refine_Basic.ASSERT(isa_length_trail_pre M);
       let j = isa_length_trail M;
       RETURN (IsaSAT_Init.update_d j (IsaSAT_Init.update_c D (IsaSAT_Init.update_a M S)))
    }\<close>
   by (cases S)
    (auto simp: isasat_init_getters_and_setters_def conflict_propagated_unit_cls_heur_b_def
     conflict_propagated_unit_cls_heur_def)

sepref_def conflict_propagated_unit_cls_code
  is \<open>uncurry (conflict_propagated_unit_cls_heur_b)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_init_assn\<^sup>d  \<rightarrow>\<^sub>a isasat_init_assn\<close>
  supply [[goals_limit=1]]
  unfolding conflict_propagated_unit_cls_heur_b_alt_def
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

lemma op_list_list_llen_alt_def: \<open>op_list_list_llen xss i = length (xss ! i)\<close>
  unfolding op_list_list_llen_def
  by auto

lemma op_list_list_idx_alt_def: \<open>op_list_list_idx xs i j = xs ! i ! j\<close>
  unfolding op_list_list_idx_def ..

sepref_def append_and_length_fast_code
  is \<open>uncurry2 fm_add_new_fast\<close>
  :: \<open>[\<lambda>((b, C), N). append_and_length_fast_code_pre ((b, C), N)]\<^sub>a
     bool1_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>k *\<^sub>a (arena_fast_assn)\<^sup>d \<rightarrow>
       arena_fast_assn \<times>\<^sub>a sint64_nat_assn\<close>
  supply [[goals_limit=1]]
  supply [simp] = fm_add_new_bounds1[simplified] shorten_lbd_le
  supply [split] = if_splits
  unfolding fm_add_new_fast_def fm_add_new_def append_and_length_fast_code_pre_def
    op_list_list_llen_alt_def[symmetric] op_list_list_idx_alt_def[symmetric]
    is_short_clause_def header_size_def
  apply (rewrite at \<open>APos \<hole>\<close> unat_const_fold[where 'a=32])+
  apply (rewrite at \<open>length _ - 2\<close> annot_snat_unat_downcast[where 'l=32])
  apply (rewrite at \<open>AStatus _ \<hole>\<close> unat_const_fold[where 'a=2])+
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_register fm_add_new_fast

lemma add_init_cls_heur_b_alt_def:
  \<open>add_init_cls_heur_b C S = do {
     let C = C;
     ASSERT(length C \<le> uint32_max + 2);
     ASSERT(length C \<ge> 2);
     let (N, S) = extract_arena_wl_heur_init S;
     let (failed, S) = extract_failed_wl_heur_init S;
     if (length N \<le> sint64_max - length C - 5 \<and> \<not>failed)
     then do {
       let (vdom, S) = extract_vdom_wl_heur_init S;
       let (ivdom, S) = extract_ivdom_wl_heur_init S;
       ASSERT(length vdom \<le> length N \<and> vdom = ivdom);
       (N, i) \<leftarrow> fm_add_new True C N;
       let vdom = vdom @ [i];
       let ivdom = ivdom @ [i];
       RETURN (IsaSAT_Init.update_b N (IsaSAT_Init.update_k vdom (IsaSAT_Init.update_l ivdom (IsaSAT_Init.update_m failed S))))
   } else RETURN (IsaSAT_Init.update_m True (IsaSAT_Init.update_b N S))}\<close>
   by (cases S)
    (auto simp: isasat_init_getters_and_setters_def conflict_propagated_unit_cls_heur_b_def add_init_cls_heur_b_def add_init_cls_heur_def
     conflict_propagated_unit_cls_heur_def)

sepref_def add_init_cls_code_b
  is \<open>uncurry add_init_cls_heur_b\<close>
  :: \<open>[\<lambda>(C, S). True]\<^sub>a
     (clause_ll_assn)\<^sup>k *\<^sub>a isasat_init_assn\<^sup>d  \<rightarrow> isasat_init_assn\<close>
  supply [[goals_limit=1]] append_ll_def[simp]add_init_clss_codebI[intro]
    add_init_cls_code_bI[intro]  add_init_cls_code_bI2[intro]
  unfolding add_init_cls_heur_b_alt_def
  PR_CONST_def
  Let_def length_uint64_nat_def add_init_cls_heur_b'_def
  op_list_list_llen_alt_def[symmetric] op_list_list_idx_alt_def[symmetric]
  unfolding
    nth_rll_def[symmetric] delete_index_and_swap_update_def[symmetric]
    delete_index_and_swap_ll_def[symmetric]
    append_ll_def[symmetric] fm_add_new_fast_def[symmetric]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

lemma already_propagated_unit_cls_conflict_heur_b_alt_def:
  \<open>already_propagated_unit_cls_conflict_heur_b L S = do {
     ASSERT (isa_length_trail_pre (get_trail_init_wl_heur S));
    let (M, S) = extract_trail_wl_heur_init S;
     let j = isa_length_trail M;
     RETURN (IsaSAT_Init.update_d j (IsaSAT_Init.update_a M S))
  }\<close>
   by (cases S)
    (auto simp: isasat_init_getters_and_setters_def conflict_propagated_unit_cls_heur_b_def add_init_cls_heur_b_def add_init_cls_heur_def
     already_propagated_unit_cls_conflict_heur_def already_propagated_unit_cls_conflict_heur_b_def)

sepref_def already_propagated_unit_cls_conflict_code
  is \<open>uncurry already_propagated_unit_cls_conflict_heur_b\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_init_assn\<^sup>d  \<rightarrow>\<^sub>a isasat_init_assn\<close>
  supply [[goals_limit=1]]
  unfolding already_propagated_unit_cls_conflict_heur_b_alt_def PR_CONST_def
  by sepref

sepref_def (in -) set_conflict_empty_code
  is \<open>RETURN o lookup_set_conflict_empty\<close>
  :: \<open>conflict_option_rel_assn\<^sup>d  \<rightarrow>\<^sub>a conflict_option_rel_assn\<close>
  supply [[goals_limit=1]]
  unfolding lookup_set_conflict_empty_def conflict_option_rel_assn_def
  by sepref


definition set_conflict_to_empty where
  \<open>set_conflict_to_empty = (\<lambda>(_, nxs). (False, nxs))\<close>

sepref_def set_conflict_to_empty_impl
  is \<open>RETURN o set_conflict_to_empty\<close>
  :: \<open>conflict_option_rel_assn\<^sup>d \<rightarrow>\<^sub>a conflict_option_rel_assn\<close>
  unfolding set_conflict_to_empty_def conflict_option_rel_assn_def
   by sepref

lemma set_empty_clause_as_conflict_heur_alt_def:
  \<open>set_empty_clause_as_conflict_heur S = (do {
     let (M, S) = extract_trail_wl_heur_init S;
     let (D, S) = extract_conflict_wl_heur_init S;
     ASSERT(isa_length_trail_pre M);
     let j = isa_length_trail M;
     RETURN (IsaSAT_Init.update_c (set_conflict_to_empty D) (IsaSAT_Init.update_d j (IsaSAT_Init.update_a M S)))
  })\<close>
   by (cases S)
    (auto simp: isasat_init_getters_and_setters_def conflict_propagated_unit_cls_heur_b_def set_conflict_to_empty_def
     set_empty_clause_as_conflict_heur_def already_propagated_unit_cls_conflict_heur_b_def)


sepref_def set_empty_clause_as_conflict_code
  is \<open>set_empty_clause_as_conflict_heur\<close>
  :: \<open>isasat_init_assn\<^sup>d \<rightarrow>\<^sub>a isasat_init_assn\<close>
  supply [[goals_limit=1]]
  unfolding set_empty_clause_as_conflict_heur_alt_def lookup_clause_rel_assn_def
  by sepref


definition (in -) add_clause_to_others_heur'
   :: \<open>twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close> where
  \<open>add_clause_to_others_heur' = (\<lambda> S.
      RETURN S)\<close>

lemma add_clause_to_others_heur'_alt: \<open>add_clause_to_others_heur L = add_clause_to_others_heur'\<close>
  unfolding add_clause_to_others_heur'_def add_clause_to_others_heur_def
  by auto

sepref_def add_clause_to_others_code
  is \<open>add_clause_to_others_heur'\<close>
  :: \<open>isasat_init_assn\<^sup>d \<rightarrow>\<^sub>a isasat_init_assn\<close>
  supply [[goals_limit=1]]
  unfolding add_clause_to_others_heur_def add_clause_to_others_heur'_def
  by sepref

declare add_clause_to_others_code.refine[sepref_fr_rules]

sepref_register init_dt_step_wl
  get_conflict_wl_is_None_heur_init already_propagated_unit_cls_heur
  conflict_propagated_unit_cls_heur add_clause_to_others_heur
  add_init_cls_heur set_empty_clause_as_conflict_heur

sepref_register polarity_st_heur_init propagate_unit_cls_heur

lemma is_Nil_length: \<open>is_Nil xs \<longleftrightarrow> length xs = 0\<close>
  by (cases xs) auto

definition pre_simplify_clause_lookup' where
  \<open>pre_simplify_clause_lookup' i xs = pre_simplify_clause_lookup (xs ! i)\<close>

lemma pre_simplify_clause_lookup'I:
  \<open>a < length bb \<Longrightarrow>
  a1' < length (bb ! a) \<Longrightarrow>
  rdomp (aal_assn' TYPE(64) TYPE(64) unat_lit_assn) bb \<Longrightarrow>
  Suc a1' < max_snat 64\<close>
  for aa aaa ad ag::\<open>64 word\<close> and ac :: \<open>32 word\<close> and ae af :: \<open>1 word\<close>
  by (auto dest!: aal_assn_boundsD' bspec[of _ _ \<open>bb ! a\<close>])

sepref_def pre_simplify_clause_lookup_impl
  is \<open>uncurry3 pre_simplify_clause_lookup'\<close>
  :: \<open>[\<lambda>(((i,xs),_),_). i < length xs]\<^sub>a
     sint64_nat_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>d *\<^sub>a marked_struct_assn\<^sup>d \<rightarrow>
    bool1_assn \<times>\<^sub>a clause_ll_assn \<times>\<^sub>a marked_struct_assn\<close>
  supply [intro] = pre_simplify_clause_lookup'I
  unfolding pre_simplify_clause_lookup_def pre_simplify_clause_lookup'_def
    op_list_list_llen_alt_def[symmetric] op_list_list_idx_alt_def[symmetric]
  by (annot_snat_const \<open>TYPE(64)\<close>)
     sepref

definition pre_simplify_clause_lookup_st' where
  \<open>pre_simplify_clause_lookup_st' i xs = pre_simplify_clause_lookup_st (xs ! i)\<close>

lemma pre_simplify_clause_lookup_st_alt_def:
  \<open>pre_simplify_clause_lookup_st = (\<lambda>C E S\<^sub>0. do {
  let (mark, S) = extract_marked_wl_heur_init S\<^sub>0;
  (tauto, C, mark) \<leftarrow> pre_simplify_clause_lookup C E mark; 
  RETURN (tauto, C, (IsaSAT_Init.update_o mark S))
  })\<close>
  by (auto simp: isasat_init_getters_and_setters_def pre_simplify_clause_lookup_st_def
    intro!: ext split: tuple15.splits)

sepref_register pre_simplify_clause_lookup' pre_simplify_clause_lookup_st'

sepref_def pre_simplify_clause_lookup_st_impl
  is \<open>uncurry3 pre_simplify_clause_lookup_st'\<close>
  :: \<open>[\<lambda>(((i,xs),_),_). i < length xs]\<^sub>a
    sint64_nat_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>d *\<^sub>a  isasat_init_assn\<^sup>d \<rightarrow>
   bool1_assn \<times>\<^sub>a clause_ll_assn \<times>\<^sub>a isasat_init_assn\<close>
  unfolding pre_simplify_clause_lookup_st_alt_def
    fold_tuple_optimizations pre_simplify_clause_lookup_st'_def
    op_list_list_llen_alt_def[symmetric] op_list_list_idx_alt_def[symmetric]
    pre_simplify_clause_lookup'_def[symmetric]
  by sepref

definition init_dt_step_wl_heur_b'
   :: \<open>nat clause_l list \<Rightarrow> nat \<Rightarrow> twl_st_wl_heur_init \<times> _ \<Rightarrow> (twl_st_wl_heur_init \<times> _) nres\<close> where
\<open>init_dt_step_wl_heur_b' C i = init_dt_step_wl_heur_b (C!i)\<close>

definition add_tautology_to_clauses' where
  \<open>add_tautology_to_clauses' = (\<lambda>S.
  RETURN S)\<close>

lemma add_tautology_to_clauses_alt_def:
  \<open>add_tautology_to_clauses C S = add_tautology_to_clauses' S\<close>
  by (cases S) (auto simp: add_tautology_to_clauses'_def add_tautology_to_clauses_def)

sepref_def add_tautology_to_clauses'_impl
  is add_tautology_to_clauses'
  :: \<open>isasat_init_assn\<^sup>d \<rightarrow>\<^sub>a isasat_init_assn\<close>
  unfolding add_tautology_to_clauses'_def
  by sepref

sepref_def init_dt_step_wl_code_b
  is \<open>uncurry2 (init_dt_step_wl_heur_b')\<close>
  :: \<open>[\<lambda>((xs, i), S). i < length xs]\<^sub>a
    (clauses_ll_assn)\<^sup>k  *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a (isasat_init_assn \<times>\<^sub>a clause_ll_assn)\<^sup>d \<rightarrow>
       isasat_init_assn \<times>\<^sub>a clause_ll_assn\<close>
  supply [[goals_limit=1]]
  supply polarity_None_undefined_lit[simp] polarity_st_init_def[simp]
  option.splits[split] get_conflict_wl_is_None_heur_init_alt_def[simp]
  tri_bool_eq_def[simp]
  unfolding init_dt_step_wl_heur_def PR_CONST_def
    init_dt_step_wl_heur_b_def
    list_length_1_def is_Nil_length init_dt_step_wl_heur_b'_def
    op_list_list_llen_alt_def[symmetric] op_list_list_idx_alt_def[symmetric]
    already_propagated_unit_cls_heur'_alt
    add_clause_to_others_heur'_def[symmetric]
    add_clause_to_others_heur'_alt
    already_propagated_unit_cls_heur_b_def[symmetric]
    propagate_unit_cls_heur_b_def[symmetric]
    conflict_propagated_unit_cls_heur_b_def[symmetric]
    pre_simplify_clause_lookup_st'_def[symmetric]
    add_tautology_to_clauses_alt_def
    add_init_cls_heur_b_def[symmetric]
  unfolding watched_app_def[symmetric]
  unfolding nth_rll_def[symmetric]
  unfolding is_Nil_length get_conflict_wl_is_None_init
    polarity_st_heur_init_alt_def[symmetric]
    get_conflict_wl_is_None_heur_init_alt_def[symmetric]
    SET_TRUE_def[symmetric] SET_FALSE_def[symmetric] UNSET_def[symmetric]
    tri_bool_eq_def[symmetric] polarity_st_heur_init_def[symmetric]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref


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


lemma [sepref_fr_rules]:
  \<open>(uncurry nat_lit_lits_init_assn_assn_in,  uncurry (RETURN \<circ>\<circ> op_set_insert))
  \<in> [\<lambda>(a, b). a \<le> uint32_max div 2]\<^sub>a
    atom_assn\<^sup>k *\<^sub>a nat_lit_list_hm_assn\<^sup>d \<rightarrow> nat_lit_list_hm_assn\<close>
  by (rule nat_lit_lits_init_assn_assn_in.refine[FCOMP add_to_atms_ext_op_set_insert
  [unfolded op_set_insert_def[symmetric]]])
hide_const (open) NEMonad.ASSERT NEMonad.RETURN
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
  using extract_atms_clss_imp.refine[FCOMP extract_atms_clss_i_extract_atms_clss]
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
    ]
  unfolding uncurry0_def
  by simp

lemma extract_atms_clss_imp_empty_rel_alt_def:
  \<open>extract_atms_clss_imp_empty_rel = (RETURN (op_larray_custom_replicate 1024 0, 0, []))\<close>
  by (auto simp: extract_atms_clss_imp_empty_rel_def)


subsubsection \<open>Full Initialisation\<close>

lemma rewatch_heur_st_init_alt_def:
\<open>rewatch_heur_st_init = (\<lambda>S\<^sub>0. do {
  let (vdom, S) = extract_vdom_wl_heur_init S\<^sub>0;
  ASSERT (vdom = get_vdom_heur_init S\<^sub>0);
  let (arena, S) = extract_arena_wl_heur_init S;
  ASSERT (arena = get_clauses_wl_heur_init S\<^sub>0);
  let (W, S) = extract_watchlist_wl_heur_init S;
  ASSERT(length (vdom) \<le> length arena);
  W \<leftarrow> rewatch_heur vdom arena W;
  RETURN (IsaSAT_Init.update_e W (IsaSAT_Init.update_b arena (IsaSAT_Init.update_k vdom S)))
  })\<close>
  by (auto simp: rewatch_heur_st_init_def isasat_init_getters_and_setters_def split: tuple15.splits
      intro!: ext)
sepref_def rewatch_heur_st_fast_code
  is \<open>(rewatch_heur_st_init)\<close>
  :: \<open>[rewatch_heur_st_fast_pre]\<^sub>a
       isasat_init_assn\<^sup>d \<rightarrow> isasat_init_assn\<close>
  supply [[goals_limit=1]]
  unfolding rewatch_heur_st_init_alt_def PR_CONST_def rewatch_heur_st_fast_pre_def
    rewatch_heur_st_fast_def
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
   apply (rewrite at \<open>(_, _, \<hole>)\<close> al_fold_custom_empty[where 'l=64])
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref


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
        (\<lambda>_. al_assn atom_assn \<times>\<^sub>a unat_assn) (\<lambda>_. lits_with_max_rel) =
       (\<lambda>_. lits_with_max_assn)\<close>
    by (auto simp: hrr_comp_def intro!: ext)

  have H: \<open>?c
    \<in> [comp_PRE isasat_atms_ext_rel (\<lambda>_. True)
         (\<lambda>_ (xs, n, vars). \<forall>x\<in>#mset vars. x < length xs) (\<lambda>_. True)]\<^sub>a
       hrp_comp (isasat_atms_ext_rel_assn\<^sup>d) isasat_atms_ext_rel \<rightarrow> lits_with_max_assn\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF extract_lits_sorted_code.refine
      extract_lits_sorted_mset_set]
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
   \<open>(Mreturn o (\<lambda>x. x), RETURN o atom_of_value) \<in> [\<lambda>n. n < 2 ^31]\<^sub>a (uint32_nat_assn)\<^sup>d \<rightarrow> atom_assn\<close>
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

schematic_goal mk_free_lbd_assn[sepref_frame_free_rules]: \<open>MK_FREE marked_struct_assn ?fr\<close>
  unfolding marked_struct_assn_def
  by synthesize_free

sepref_def reduce_interval_init_impl
  is \<open>uncurry0 (RETURN reduce_interval_init)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding reduce_interval_init_def
  by sepref

sepref_def inprocessing_interval_init_impl
  is \<open>uncurry0 (RETURN inprocessing_interval_init)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding inprocessing_interval_init_def
  by sepref

sepref_def rephasing_end_of_initial_phase_impl
  is \<open>uncurry0 (RETURN rephasing_end_of_initial_phase)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding rephasing_end_of_initial_phase_def
  by sepref

sepref_def rephasing_initial_phase_impl
  is \<open>uncurry0 (RETURN rephasing_initial_phase)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding rephasing_initial_phase_def
  by sepref

sepref_def subsuming_length_initial_phase_impl
  is \<open>uncurry0 (RETURN subsuming_length_initial_phase)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding subsuming_length_initial_phase_def
  by sepref

definition empty_heuristics_stats :: \<open>_ \<Rightarrow> _ \<Rightarrow> restart_heuristics\<close> where
  \<open>empty_heuristics_stats opts \<phi> = (
  let fema = ema_init (opts_fema opts) in
  let sema = ema_init (opts_sema opts) in let ccount = restart_info_init in
  let n = (length \<phi>)  in
    (fema, sema, ccount, 0, (\<phi>, 0, replicate n False, 0, replicate n False, rephasing_end_of_initial_phase, 0, rephasing_initial_phase),
    reluctant_init, False, replicate n False, (inprocessing_interval_init, reduce_interval_init, subsuming_length_initial_phase), fema, sema))\<close>

sepref_def empty_heuristics_stats_impl
  is \<open>uncurry (RETURN oo empty_heuristics_stats)\<close>
  :: \<open>opts_assn\<^sup>k *\<^sub>a phase_saver_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_int_assn\<close>
  supply  [[goals_limit=1]]
  unfolding heuristic_int_assn_def empty_heuristics_stats_def phase_heur_assn_def
  apply (rewrite at \<open>replicate _ False\<close> annotate_assn[where A=phase_saver'_assn])
  apply (rewrite in \<open>replicate _ False\<close> array_fold_custom_replicate)
  apply (rewrite at \<open>replicate _ False\<close> annotate_assn[where A=phase_saver'_assn])
  apply (rewrite in \<open>replicate _ False\<close> array_fold_custom_replicate)
  apply (rewrite at \<open>replicate _ False\<close> annotate_assn[where A=phase_saver_assn])
  apply (rewrite in \<open>replicate _ False\<close> larray_fold_custom_replicate)
  by sepref

lemma finalise_init_code_alt_def:
  \<open>finalise_init_code opts =
  (\<lambda>S. case S of Tuple15 M'  N' D' Q' W' vm \<phi> clvls cach
  lbd vdom ivdom failed lcount mark \<Rightarrow> do {
  let ((ns, m, fst_As, lst_As, next_search), to_remove) = split_vmtf2 vm;
   ASSERT(lst_As \<noteq> None \<and> fst_As \<noteq> None);
  let init_stats = empty_stats_clss (of_nat(length ivdom));
  let heur = empty_heuristics_stats opts \<phi>;
    mop_free mark; mop_free failed;
  let vm = recombine_vmtf ((ns, m, the fst_As, the lst_As, next_search), to_remove);
  let occs =  replicate (length W') [];
  RETURN (IsaSAT M' N' D' Q' W' vm
    clvls cach lbd (take 1(replicate 160 (Pos 0))) init_stats
    (Restart_Heuristics heur) (AIvdom_init vdom [] ivdom) lcount opts [] occs)
    })\<close>
    unfolding finalise_init_code_def mop_free_def empty_heuristics_stats_def split_vmtf2_def
    by (auto simp: Let_def recombine_vmtf_def split: prod.splits tuple15.splits intro!: ext)


sepref_def finalise_init_code'
  is \<open>uncurry finalise_init_code\<close>
  :: \<open>[\<lambda>(_, S). length (get_clauses_wl_heur_init S) \<le> sint64_max]\<^sub>a
      opts_assn\<^sup>d *\<^sub>a isasat_init_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply  [[goals_limit=1]]  of_nat_snat[sepref_import_param]
  unfolding finalise_init_code_alt_def isasat_init_assn_def
     INITIAL_OUTL_SIZE_def[symmetric] atom.fold_the vmtf_remove_assn_def
     phase_heur_assn_def op_list_list_len_def[symmetric]
  apply (rewrite at \<open>Pos \<hole>\<close> unat_const_fold[where 'a=32])
  apply (rewrite at \<open>Pos \<hole>\<close> atom_of_value_def[symmetric])
  apply (rewrite at \<open>take \<hole>\<close> snat_const_fold[where 'a=64])
  apply (rewrite at \<open>AIvdom_init _ \<hole> _\<close> al_fold_custom_empty[where 'l=64])
  apply (rewrite at \<open>IsaSAT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ \<hole> _\<close> al_fold_custom_empty[where 'l=64])
  apply (rewrite in \<open>take _ \<hole>\<close> al_fold_custom_replicate)
  apply (rewrite in \<open>replicate _ []\<close> aal_fold_custom_empty(1)[where 'l=64 and 'll=64])
  apply (rewrite at \<open>let vm = recombine_vmtf _; _ = \<hole> in _\<close> annotate_assn[where A=\<open>occs_assn\<close>])
  by sepref

sepref_register initialise_VMTF

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
definition empty_mark_struct :: \<open>nat \<Rightarrow> nat \<times> bool option list\<close> where
  \<open>empty_mark_struct (n::nat) = (0::nat, replicate n NoMark)\<close>

sepref_def empty_mark_struct_impl
  is \<open>RETURN o empty_mark_struct\<close>
  :: \<open>sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a marked_struct_assn\<close>
  unfolding empty_mark_struct_def marked_struct_assn_def
  apply (rewrite at \<open>(\<hole>, replicate _ NoMark)\<close> unat_const_fold[where 'a=32])
  unfolding array_fold_custom_replicate
  by sepref
 

definition combine_conflict where
  \<open>combine_conflict x = x\<close>
sepref_def combine_conflict_impl
  is \<open>RETURN o combine_conflict\<close>
  :: \<open>(bool1_assn \<times>\<^sub>a unat32_assn \<times>\<^sub>a IICF_Array.array_assn option_bool_impl_assn)\<^sup>d \<rightarrow>\<^sub>a conflict_option_rel_assn\<close>
  unfolding combine_conflict_def conflict_option_rel_assn_def lookup_clause_rel_assn_def
  by sepref

definition combine_ccach where
  \<open>combine_ccach x = x\<close>
sepref_def combine_ccach_impl
  is \<open>RETURN o combine_ccach\<close>
  :: \<open>(array_assn minimize_status_assn \<times>\<^sub>a arl64_assn atom_assn)\<^sup>d \<rightarrow>\<^sub>a cach_refinement_l_assn\<close>
  unfolding combine_ccach_def cach_refinement_l_assn_def
  by sepref

definition combine_lcount where
  \<open>combine_lcount x = x\<close>
sepref_def combine_lcount_impl
  is \<open>RETURN o combine_lcount\<close>
  :: \<open>(uint64_nat_assn \<times>\<^sub>a uint64_nat_assn \<times>\<^sub>a uint64_nat_assn \<times>\<^sub>a uint64_nat_assn \<times>\<^sub>a uint64_nat_assn)\<^sup>k \<rightarrow>\<^sub>a lcount_assn\<close>
  unfolding combine_lcount_def lcount_assn_def
  by sepref

sepref_register empty_mark_struct combine_conflict combine_ccach combine_lcount

lemma init_state_wl_D'_alt_def:
  \<open>init_state_wl_D' = (\<lambda>(\<A>\<^sub>i\<^sub>n, n). do {
     ASSERT(Suc (2 * (n)) \<le> uint32_max);
     let n = Suc (n);
     let m = 2 * n;
     M \<leftarrow> init_trail_D \<A>\<^sub>i\<^sub>n n m;
     let N = [];
     let D = combine_conflict (True, 0, replicate n NOTIN);
     let mark = (0, replicate n None);
     let WS = replicate m [];
     vm \<leftarrow> initialise_VMTF \<A>\<^sub>i\<^sub>n n;
     let \<phi> = replicate n False;
     let cach = combine_ccach (replicate n SEEN_UNKNOWN, []);
     let lbd = empty_lbd;
     let vdom = [];
     let ivdom = [];
     let lcount = combine_lcount (0, 0, 0, 0, 0);
     RETURN (Tuple15 M N D 0 WS vm \<phi> 0 cach lbd vdom ivdom False lcount mark)
       })\<close>
   unfolding combine_conflict_def combine_ccach_def init_state_wl_D'_def combine_lcount_def by auto

sepref_definition init_state_wl_D'_code
  is \<open>init_state_wl_D'\<close>
  :: \<open>(arl64_assn atom_assn \<times>\<^sub>a uint32_nat_assn)\<^sup>k \<rightarrow>\<^sub>a isasat_init_assn\<close>
  supply[[goals_limit=1]]
  unfolding init_state_wl_D'_alt_def PR_CONST_def init_trail_D_fast_def[symmetric]  Suc_eq_plus1_left
    NoMark_def[symmetric] empty_mark_struct_def[symmetric] of_nat_snat[sepref_import_param]
  apply (rewrite at \<open>let _ = 1 + \<hole> in _\<close> annot_unat_snat_upcast[where 'l=64])
  apply (rewrite at \<open>let _ = combine_ccach (_, \<hole>) in _\<close> al_fold_custom_empty[where 'l=64])
  apply (rewrite at \<open>let _ = combine_ccach (\<hole>,_) in _\<close> annotate_assn[where A= \<open>array_assn minimize_status_assn\<close>])
  apply (rewrite at \<open>let _ = combine_ccach (_, \<hole>) in _\<close> annotate_assn[where A= \<open>arl64_assn atom_assn\<close>])
  apply (rewrite in \<open>replicate _ []\<close> aal_fold_custom_empty(1)[where 'l=64 and 'll=64])
  apply (rewrite at \<open>let _= _; _= \<hole> in _\<close> annotate_assn[where A=\<open>watchlist_fast_assn\<close>])
  apply (rewrite at \<open>let _= \<hole>; _=_;_=_;_ = _;_=_; _ = _ in RETURN _\<close> annotate_assn[where A=\<open>phase_saver_assn\<close>])
  apply (rewrite in \<open>let _= \<hole>; _=_;_=_;_ = _; _= _; _=_ in RETURN _\<close> larray_fold_custom_replicate)
  apply (rewrite in \<open>let _= combine_conflict(True, _, \<hole>) in  _\<close> array_fold_custom_replicate)
  unfolding array_fold_custom_replicate
  apply (rewrite at \<open>let _ = \<hole> in let _ = combine_conflict (True, _, _) in _\<close> al_fold_custom_empty[where 'l=64])
  apply (rewrite in \<open>let _= combine_conflict (True, \<hole>, _) in _\<close> unat_const_fold[where 'a=32])
  apply (rewrite at \<open>let _ = \<hole> in _\<close> annotate_assn[where A=\<open>arena_fast_assn\<close>])
  apply (rewrite at \<open>let _= \<hole>; _ = _ ; _ =_ in RETURN _\<close> annotate_assn[where A = \<open>vdom_fast_assn\<close>])
  apply (rewrite at \<open>let _= \<hole>; _ = _ in RETURN _\<close> annotate_assn[where A = \<open>vdom_fast_assn\<close>])
  apply (rewrite in \<open>let _= \<hole>; _=_; _ = _ in RETURN _\<close> al_fold_custom_empty[where 'l=64])
  apply (rewrite in \<open>let _= \<hole>; _ = _ in RETURN _\<close> al_fold_custom_empty[where 'l=64])
  apply (rewrite at \<open>Tuple15 _ _ _ _ _ _ _ \<hole>\<close> unat_const_fold[where 'a=32])
  apply (rewrite at \<open>let _ = combine_lcount (\<hole>, _, _) in RETURN _\<close> unat_const_fold[where 'a=64])
  apply (rewrite at \<open>let _ = combine_lcount (_, \<hole>, _) in RETURN _\<close> unat_const_fold[where 'a=64])
  apply (rewrite at \<open>let _ = combine_lcount ( _, _, \<hole>, _) in RETURN _\<close> unat_const_fold[where 'a=64])
  apply (rewrite at \<open>let _ = combine_lcount ( _, _, _, \<hole>, _) in RETURN _\<close> unat_const_fold[where 'a=64])
  apply (rewrite at \<open>let _ = combine_lcount ( _, _, _, _, \<hole>) in RETURN _\<close> unat_const_fold[where 'a=64])
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  apply (rewrite at \<open>RETURN \<hole>\<close> annotate_assn[where A=\<open>isasat_init_assn\<close>])
  by sepref

declare init_state_wl_D'_code.refine[sepref_fr_rules]


lemma to_init_state_code_hnr:
  \<open>(Mreturn o to_init_state_code, RETURN o id) \<in> isasat_init_assn\<^sup>d \<rightarrow>\<^sub>a isasat_init_assn\<close>
  unfolding to_init_state_code_def
  by sepref_to_hoare vcg'

abbreviation (in -)lits_with_max_assn_clss where
  \<open>lits_with_max_assn_clss \<equiv> hr_comp lits_with_max_assn (\<langle>nat_rel\<rangle>mset_rel)\<close>

lemmas [unfolded Tuple15_LLVM.inline_direct_return_node_case, llvm_code] =
  get_conflict_wl_is_None_init_code_def[unfolded IsaSAT_Init.read_all_st_code_def]

(*TODO check why this is actually needed*)
lemmas [llvm_code] =
   init_state_wl_D'_code_def[unfolded comp_def]

lemmas [unfolded Tuple15_LLVM.inline_direct_return_node_case, llvm_code] =
  get_conflict_wl_is_None_init_code_def[unfolded IsaSAT_Init.read_all_st_code_def]

schematic_goal mk_free_isasat_init_assn[sepref_frame_free_rules]: \<open>MK_FREE isasat_init_assn ?fr\<close>
  unfolding isasat_init_assn_def
  by synthesize_free+

experiment
begin
  export_llvm init_state_wl_D'_code
    rewatch_heur_st_fast_code
    init_dt_wl_heur_code_b
    init_state_wl_D'_code
end

end
