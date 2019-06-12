theory IsaSAT_Lookup_Conflict_SML
imports
    IsaSAT_Lookup_Conflict
    IsaSAT_Trail_SML
    IsaSAT_Clauses_SML
begin


sepref_definition (in -) delete_from_lookup_conflict_code
  is \<open>uncurry delete_from_lookup_conflict\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a lookup_clause_rel_assn\<^sup>d \<rightarrow>\<^sub>a lookup_clause_rel_assn\<close>
  unfolding delete_from_lookup_conflict_def NOTIN_def[symmetric]
  by sepref

sepref_definition resolve_lookup_conflict_merge_code
  is \<open>uncurry6 isa_set_lookup_conflict\<close>
  :: \<open>[\<lambda>((((((M, N), i), (_, xs)), _), _), out). i < length N]\<^sub>a
      trail_pol_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d *\<^sub>a
         uint32_nat_assn\<^sup>k *\<^sub>a lbd_assn\<^sup>d *\<^sub>a out_learned_assn\<^sup>d \<rightarrow>
      conflict_option_rel_assn *a uint32_nat_assn *a lbd_assn *a out_learned_assn\<close>
  supply length_rll_def[simp] nth_rll_def[simp] uint_max_def[simp]
    uint32_nat_assn_one[sepref_fr_rules] image_image[simp] literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[simp]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_get_level_uint_max[dest]
    Suc_uint32_nat_assn_hnr[sepref_fr_rules] fmap_length_rll_u_def[simp]
  unfolding isa_lookup_conflict_merge_def lookup_conflict_merge_def add_to_lookup_conflict_def
    PR_CONST_def nth_rll_def[symmetric]
    isa_outlearned_add_def isa_clvls_add_def isa_set_lookup_conflict_def
    isasat_codegen
    fmap_rll_u_def[symmetric]
    fmap_rll_def[symmetric]
    is_NOTIN_def[symmetric]
  apply (rewrite at \<open>_ + \<hole>\<close> nat_of_uint64_conv_def[symmetric])
  supply [[goals_limit = 1]]
  by sepref

declare resolve_lookup_conflict_merge_code.refine[sepref_fr_rules]


sepref_definition resolve_lookup_conflict_merge_fast_code
  is \<open>uncurry6 isa_set_lookup_conflict\<close>
  :: \<open>[\<lambda>((((((M, N), i), (_, xs)), _), _), out). i < length N \<and>
         length N \<le> uint64_max]\<^sub>a
      trail_pol_fast_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d *\<^sub>a
         uint32_nat_assn\<^sup>k *\<^sub>a lbd_assn\<^sup>d *\<^sub>a out_learned_assn\<^sup>d \<rightarrow>
      conflict_option_rel_assn *a uint32_nat_assn *a lbd_assn *a out_learned_assn\<close>
  supply length_rll_def[simp] nth_rll_def[simp] uint_max_def[simp]
    uint32_nat_assn_one[sepref_fr_rules] image_image[simp] literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[simp]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_get_level_uint_max[dest]
    Suc_uint32_nat_assn_hnr[sepref_fr_rules] fmap_length_rll_u_def[simp]
    arena_is_valid_clause_idx_le_uint64_max[intro]
  unfolding isa_lookup_conflict_merge_def lookup_conflict_merge_def add_to_lookup_conflict_def
    PR_CONST_def nth_rll_def[symmetric]
    isa_outlearned_add_def isa_clvls_add_def isa_set_lookup_conflict_def
    isa_set_lookup_conflict_def
    fmap_rll_u_def[symmetric]
    fmap_rll_def[symmetric]
    is_NOTIN_def[symmetric]
    zero_uint64_nat_def[symmetric]
  apply (rewrite at \<open>RETURN (\<hole>, _ ,_, _)\<close>  Suc_eq_plus1)
  apply (rewrite at \<open>RETURN (_ + \<hole>, _ ,_, _)\<close> one_uint64_nat_def[symmetric])
  supply [[goals_limit = 1]]
  by sepref


declare resolve_lookup_conflict_merge_fast_code.refine[sepref_fr_rules]



sepref_definition set_lookup_conflict_aa_code
  is \<open>uncurry6 isa_set_lookup_conflict_aa\<close>
  :: \<open>trail_pol_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d *\<^sub>a
         uint32_nat_assn\<^sup>k *\<^sub>a lbd_assn\<^sup>d *\<^sub>a out_learned_assn\<^sup>d \<rightarrow>\<^sub>a
      conflict_option_rel_assn *a uint32_nat_assn *a lbd_assn *a out_learned_assn\<close>
  supply length_rll_def[simp] nth_rll_def[simp] uint_max_def[simp]
    image_image[simp] literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[simp]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_get_level_uint_max[dest]
    fmap_length_rll_u_def[simp]
  unfolding set_lookup_conflict_aa_def lookup_conflict_merge_def add_to_lookup_conflict_def
    PR_CONST_def nth_rll_def[symmetric] length_rll_def[symmetric]
    length_aa_u_def[symmetric] isa_outlearned_add_def isa_clvls_add_def
    isasat_codegen isa_set_lookup_conflict_aa_def isa_lookup_conflict_merge_def
    fmap_rll_u_def[symmetric]
    fmap_rll_def[symmetric]
    is_NOTIN_def[symmetric] isa_set_lookup_conflict_aa_pre_def
  supply [[goals_limit = 1]]
  apply (rewrite at \<open>_ + \<hole>\<close> nat_of_uint64_conv_def[symmetric])
  apply (rewrite in \<open>_ + 1\<close> one_uint32_nat_def[symmetric])
  apply (rewrite in \<open>_ + 1\<close> one_uint32_nat_def[symmetric])
  by sepref

declare set_lookup_conflict_aa_code.refine[sepref_fr_rules]

sepref_definition set_lookup_conflict_aa_fast_code
  is \<open>uncurry6 isa_set_lookup_conflict_aa\<close>
  :: \<open>[\<lambda>((((((M, N), i), (_, xs)), _), _), _). length N \<le> uint64_max]\<^sub>a
      trail_pol_fast_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d *\<^sub>a
         uint32_nat_assn\<^sup>k *\<^sub>a lbd_assn\<^sup>d  *\<^sub>a out_learned_assn\<^sup>d \<rightarrow>
      conflict_option_rel_assn *a uint32_nat_assn *a lbd_assn *a out_learned_assn\<close>
  supply length_rll_def[simp] nth_rll_def[simp] uint_max_def[simp]
    image_image[simp] literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[simp]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_get_level_uint_max[dest]
    fmap_length_rll_u_def[simp]
    arena_is_valid_clause_idx_le_uint64_max[intro]
  unfolding set_lookup_conflict_aa_def lookup_conflict_merge_def add_to_lookup_conflict_def
    PR_CONST_def nth_rll_def[symmetric] length_rll_def[symmetric]
    length_aa_u_def[symmetric] isa_outlearned_add_def isa_clvls_add_def
    isasat_codegen isa_set_lookup_conflict_aa_def isa_lookup_conflict_merge_def
    fmap_rll_u_def[symmetric]
    fmap_rll_def[symmetric]
    is_NOTIN_def[symmetric] isa_set_lookup_conflict_aa_pre_def zero_uint64_nat_def[symmetric]
  supply [[goals_limit = 1]]
  apply (rewrite in \<open>_ + 1\<close> one_uint32_nat_def[symmetric])
  apply (rewrite in \<open>_ + 1\<close> one_uint32_nat_def[symmetric])
  apply (rewrite at \<open>RETURN (\<hole>, _ ,_, _)\<close>  Suc_eq_plus1)
  apply (rewrite at \<open>RETURN (_ + \<hole>, _ ,_, _)\<close> one_uint64_nat_def[symmetric])
  supply [[goals_limit = 1]]
  by sepref

declare set_lookup_conflict_aa_fast_code.refine[sepref_fr_rules]


sepref_definition resolve_merge_conflict_code
  is \<open>uncurry6 isa_resolve_merge_conflict_gt2\<close>
  :: \<open>[isa_set_lookup_conflict_aa_pre]\<^sub>a
      trail_pol_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d *\<^sub>a
         uint32_nat_assn\<^sup>k *\<^sub>a lbd_assn\<^sup>d *\<^sub>a out_learned_assn\<^sup>d \<rightarrow>
      conflict_option_rel_assn *a uint32_nat_assn *a lbd_assn *a out_learned_assn\<close>
  supply length_rll_def[simp] nth_rll_def[simp] uint_max_def[simp]
    image_image[simp] literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[simp]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_get_level_uint_max[dest]
    fmap_length_rll_u_def[simp]
  unfolding set_lookup_conflict_aa_def lookup_conflict_merge_def add_to_lookup_conflict_def
    PR_CONST_def nth_rll_def[symmetric] length_rll_def[symmetric]
    length_aa_u_def[symmetric] isa_outlearned_add_def isa_clvls_add_def
    isasat_codegen isa_set_lookup_conflict_aa_def isa_lookup_conflict_merge_def
    fmap_rll_u_def[symmetric]
    fmap_rll_def[symmetric]
    is_NOTIN_def[symmetric] isa_set_lookup_conflict_aa_pre_def
    isa_resolve_merge_conflict_gt2_def
  apply (rewrite at \<open>_ + \<hole>\<close> nat_of_uint64_conv_def[symmetric])
  apply (rewrite in \<open>_ + 1\<close> one_uint32_nat_def[symmetric])
  apply (rewrite in \<open>_ + 1\<close> one_uint32_nat_def[symmetric])
  supply [[goals_limit = 1]]
  by sepref

declare resolve_merge_conflict_code.refine[sepref_fr_rules]

sepref_definition resolve_merge_conflict_fast_code
  is \<open>uncurry6 isa_resolve_merge_conflict_gt2\<close>
  :: \<open>[uncurry6 (\<lambda>M N i (b, xs) clvls lbd outl. length N \<le> uint64_max \<and>
         isa_set_lookup_conflict_aa_pre ((((((M, N), i), (b, xs)), clvls), lbd), outl))]\<^sub>a
      trail_pol_fast_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d *\<^sub>a
         uint32_nat_assn\<^sup>k *\<^sub>a lbd_assn\<^sup>d *\<^sub>a out_learned_assn\<^sup>d \<rightarrow>
      conflict_option_rel_assn *a uint32_nat_assn *a lbd_assn *a out_learned_assn\<close>
  supply length_rll_def[simp] nth_rll_def[simp] uint_max_def[simp]
    image_image[simp] literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[simp]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_get_level_uint_max[dest]
    fmap_length_rll_u_def[simp]
    arena_is_valid_clause_idx_le_uint64_max[intro]
  unfolding set_lookup_conflict_aa_def lookup_conflict_merge_def add_to_lookup_conflict_def
    PR_CONST_def nth_rll_def[symmetric] length_rll_def[symmetric]
    length_aa_u_def[symmetric] isa_outlearned_add_def isa_clvls_add_def
    isasat_codegen isa_set_lookup_conflict_aa_def isa_lookup_conflict_merge_def
    fmap_rll_u_def[symmetric]
    fmap_rll_def[symmetric] nat_of_uint64_conv_def
    is_NOTIN_def[symmetric] isa_set_lookup_conflict_aa_pre_def
    isa_resolve_merge_conflict_gt2_def
  apply (rewrite in \<open>_ + 1\<close> one_uint32_nat_def[symmetric])
  apply (rewrite in \<open>_ + 1\<close> one_uint32_nat_def[symmetric])
  apply (rewrite in \<open>_ + 1\<close> one_uint64_nat_def[symmetric])
  apply (rewrite in \<open>RETURN (Suc _, _)\<close> Suc_eq_plus1)
  apply (rewrite in \<open>_ + 1\<close> one_uint64_nat_def[symmetric])
  supply [[goals_limit = 1]]
  by sepref

declare resolve_merge_conflict_fast_code.refine[sepref_fr_rules]


sepref_definition (in -) atm_in_conflict_code
  is \<open>uncurry (RETURN oo atm_in_conflict_lookup)\<close>
  :: \<open>[uncurry atm_in_conflict_lookup_pre]\<^sub>a
     uint32_nat_assn\<^sup>k *\<^sub>a lookup_clause_rel_assn\<^sup>k \<rightarrow> bool_assn\<close>
  unfolding atm_in_conflict_lookup_def atm_in_conflict_lookup_pre_def
  by sepref

declare atm_in_conflict_code.refine[sepref_fr_rules]
sepref_definition (in -) conflict_min_cach_l_code
  is \<open>uncurry (RETURN oo conflict_min_cach_l)\<close>
  :: \<open>[conflict_min_cach_l_pre]\<^sub>a cach_refinement_l_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> minimize_status_assn\<close>
  unfolding conflict_min_cach_l_def conflict_min_cach_l_pre_def
  by sepref

declare conflict_min_cach_l_code.refine[sepref_fr_rules]

sepref_definition (in -) conflict_min_cach_set_failed_l_code
  is \<open>uncurry conflict_min_cach_set_failed_l\<close>
  :: \<open>cach_refinement_l_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a cach_refinement_l_assn\<close>
  supply arl_append_hnr[sepref_fr_rules]
  unfolding conflict_min_cach_set_failed_l_def
  by sepref


sepref_definition (in -) conflict_min_cach_set_removable_l_code
  is \<open>uncurry conflict_min_cach_set_removable_l\<close>
  :: \<open>cach_refinement_l_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a cach_refinement_l_assn\<close>
  supply arl_append_hnr[sepref_fr_rules]
  unfolding conflict_min_cach_set_removable_l_def
  by sepref

declare conflict_min_cach_set_removable_l_code.refine[sepref_fr_rules]


sepref_definition isa_mark_failed_lits_stack_code
  is \<open>uncurry2 (isa_mark_failed_lits_stack)\<close>
  :: \<open>arena_assn\<^sup>k *\<^sub>a analyse_refinement_assn\<^sup>d *\<^sub>a cach_refinement_l_assn\<^sup>d \<rightarrow>\<^sub>a
      cach_refinement_l_assn\<close>
  supply [[goals_limit = 1]] neq_Nil_revE[elim!] image_image[simp] length_rll_def[simp]
    mark_failed_lits_stack_inv_helper1[dest] mark_failed_lits_stack_inv_helper2[dest]
    fmap_length_rll_u_def[simp]
  unfolding isa_mark_failed_lits_stack_def PR_CONST_def
    conflict_min_cach_set_failed_def[symmetric]
    conflict_min_cach_def[symmetric]
    get_literal_and_remove_of_analyse_wl_def
    nth_rll_def[symmetric]
    fmap_rll_def[symmetric]
    conflict_min_cach_set_failed_l_def
  apply (rewrite at \<open>arena_lit _ (_ + \<hole> - _)\<close> nat_of_uint32_conv_def[symmetric])
  by sepref


sepref_definition isa_mark_failed_lits_stack_fast_code
  is \<open>uncurry2 (isa_mark_failed_lits_stack)\<close>
  :: \<open>[\<lambda>((N, _), _). length N \<le> uint64_max]\<^sub>a
    arena_assn\<^sup>k *\<^sub>a analyse_refinement_fast_assn\<^sup>d *\<^sub>a cach_refinement_l_assn\<^sup>d \<rightarrow>
    cach_refinement_l_assn\<close>
  supply [[goals_limit = 1]] neq_Nil_revE[elim!] image_image[simp] length_rll_def[simp]
    mark_failed_lits_stack_inv_helper1[dest] mark_failed_lits_stack_inv_helper2[dest]
    fmap_length_rll_u_def[simp]
    arena_is_valid_clause_idx_le_uint64_max[intro]
  unfolding isa_mark_failed_lits_stack_def PR_CONST_def
    conflict_min_cach_set_failed_def[symmetric]
    conflict_min_cach_def[symmetric]
    get_literal_and_remove_of_analyse_wl_def
    nth_rll_def[symmetric]
    fmap_rll_def[symmetric]
    arena_lit_def[symmetric]
    conflict_min_cach_set_failed_l_def
  apply (rewrite at \<open>arena_lit _ (_ + \<hole> - _)\<close> uint64_of_uint32_conv_def[symmetric])
  apply (rewrite in \<open>_ - \<hole>\<close> one_uint64_nat_def[symmetric])
  apply (rewrite in \<open>_ - \<hole>\<close> one_uint64_nat_def[symmetric])
  apply (rewrite in \<open>_ - \<hole>\<close> one_uint64_nat_def[symmetric])
  unfolding
    fast_minus_def[symmetric]
  by sepref

declare isa_mark_failed_lits_stack_code.refine[sepref_fr_rules]
declare isa_mark_failed_lits_stack_fast_code.refine[sepref_fr_rules]

sepref_definition isa_get_literal_and_remove_of_analyse_wl_code
  is \<open>uncurry (RETURN oo isa_get_literal_and_remove_of_analyse_wl)\<close>
  :: \<open>[uncurry isa_get_literal_and_remove_of_analyse_wl_pre]\<^sub>a
      arena_assn\<^sup>k *\<^sub>a analyse_refinement_assn\<^sup>d \<rightarrow>
      unat_lit_assn *a analyse_refinement_assn\<close>
  unfolding isa_get_literal_and_remove_of_analyse_wl_pre_def
    isa_get_literal_and_remove_of_analyse_wl_def fast_minus_def[symmetric]
  apply (rewrite at \<open>arena_lit _ (_ + \<hole>)\<close> nat_of_uint32_conv_def[symmetric])
  apply (rewrite at \<open>(_ + \<hole>)\<close> one_uint32_nat_def[symmetric])
  by sepref

sepref_definition isa_get_literal_and_remove_of_analyse_wl_fast_code
  is \<open>uncurry (RETURN oo isa_get_literal_and_remove_of_analyse_wl)\<close>
  :: \<open>[\<lambda>(arena, analyse). isa_get_literal_and_remove_of_analyse_wl_pre arena analyse \<and>
         length arena \<le> uint64_max]\<^sub>a
      arena_assn\<^sup>k *\<^sub>a analyse_refinement_fast_assn\<^sup>d \<rightarrow>
      unat_lit_assn *a analyse_refinement_fast_assn\<close>
  supply [[goals_limit=1]] arena_lit_pre_le2[dest]
  unfolding isa_get_literal_and_remove_of_analyse_wl_pre_def
  isa_get_literal_and_remove_of_analyse_wl_def fast_minus_def[symmetric]
  apply (rewrite at \<open>_ + \<hole>\<close> one_uint32_nat_def[symmetric])
  apply (rewrite at \<open>arena_lit _ (_ + \<hole>)\<close> uint64_of_uint32_conv_def[symmetric])
  by sepref

declare isa_get_literal_and_remove_of_analyse_wl_code.refine[sepref_fr_rules]
declare isa_get_literal_and_remove_of_analyse_wl_fast_code.refine[sepref_fr_rules]

sepref_definition ana_lookup_conv_lookup_fast_code
  is \<open>uncurry (RETURN oo ana_lookup_conv_lookup)\<close>
  :: \<open>[uncurry ana_lookup_conv_lookup_pre]\<^sub>a arena_assn\<^sup>k *\<^sub>a
    (uint64_nat_assn *a uint32_nat_assn *a bool_assn)\<^sup>k
     \<rightarrow> uint64_nat_assn *a uint64_nat_assn *a uint64_nat_assn *a uint64_nat_assn\<close>
  unfolding ana_lookup_conv_lookup_pre_def ana_lookup_conv_lookup_def
    zero_uint64_nat_def[symmetric] one_uint64_nat_def[symmetric]
  apply (rewrite at \<open>(_, _, \<hole>, _)\<close> uint64_of_uint32_conv_def[symmetric])
  by sepref

sepref_definition ana_lookup_conv_lookup_code
  is \<open>uncurry (RETURN oo ana_lookup_conv_lookup)\<close>
  :: \<open>[uncurry ana_lookup_conv_lookup_pre]\<^sub>a arena_assn\<^sup>k *\<^sub>a
    (nat_assn *a uint32_nat_assn *a bool_assn)\<^sup>k
     \<rightarrow> nat_assn *a uint64_nat_assn *a uint64_nat_assn *a uint64_nat_assn\<close>
  unfolding ana_lookup_conv_lookup_pre_def ana_lookup_conv_lookup_def
    zero_uint64_nat_def[symmetric] one_uint64_nat_def[symmetric]
  apply (rewrite at \<open>(_, _, \<hole>, _)\<close> uint64_of_uint32_conv_def[symmetric])
  by sepref

declare ana_lookup_conv_lookup_fast_code.refine[sepref_fr_rules]
   ana_lookup_conv_lookup_code.refine[sepref_fr_rules]


sepref_definition lit_redundant_reason_stack_wl_lookup_code
  is \<open>uncurry2 (RETURN ooo lit_redundant_reason_stack_wl_lookup)\<close>
  :: \<open>[uncurry2 lit_redundant_reason_stack_wl_lookup_pre]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>
      ana_refinement_assn\<close>
  unfolding lit_redundant_reason_stack_wl_lookup_def lit_redundant_reason_stack_wl_lookup_pre_def
    one_uint32_nat_def[symmetric] zero_uint32_nat_def[symmetric]
  apply (rewrite at \<open>2 < \<hole>\<close> nat_of_uint64_conv_def[symmetric])
  by sepref

sepref_definition lit_redundant_reason_stack_wl_lookup_fast_code
  is \<open>uncurry2 (RETURN ooo lit_redundant_reason_stack_wl_lookup)\<close>
  :: \<open>[uncurry2 lit_redundant_reason_stack_wl_lookup_pre]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>
      ana_refinement_fast_assn\<close>
  unfolding lit_redundant_reason_stack_wl_lookup_def lit_redundant_reason_stack_wl_lookup_pre_def
    two_uint64_nat_def[symmetric] zero_uint32_nat_def[symmetric]
    one_uint32_nat_def[symmetric]
  by sepref

declare lit_redundant_reason_stack_wl_lookup_fast_code.refine[sepref_fr_rules]
  lit_redundant_reason_stack_wl_lookup_code.refine[sepref_fr_rules]


declare get_propagation_reason_code.refine[sepref_fr_rules]

(* TODO fst (lst last) \<le> uint_max? *)
sepref_definition lit_redundant_rec_wl_lookup_code
  is \<open>uncurry5 (isa_lit_redundant_rec_wl_lookup)\<close>
  :: \<open>[\<lambda>(((((M, NU), D), cach), analysis), lbd). True]\<^sub>a
      trail_pol_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a (uint32_nat_assn *a array_assn option_bool_assn)\<^sup>k *\<^sub>a
        cach_refinement_l_assn\<^sup>d *\<^sub>a analyse_refinement_assn\<^sup>d *\<^sub>a lbd_assn\<^sup>k \<rightarrow>
      cach_refinement_l_assn *a analyse_refinement_assn *a bool_assn\<close>
  supply [[goals_limit = 1]] neq_Nil_revE[elim] image_image[simp]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l[intro]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l_atms[intro] length_rll_def[simp]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l_atms[intro] nth_rll_def[simp]
    fmap_length_rll_u_def[simp]
    fmap_length_rll_def[simp]
  unfolding isa_lit_redundant_rec_wl_lookup_def
    conflict_min_cach_set_removable_def[symmetric]
    conflict_min_cach_def[symmetric]
    get_literal_and_remove_of_analyse_wl_def
    nth_rll_def[symmetric] PR_CONST_def
    fmap_rll_u_def[symmetric]
    fmap_rll_def[symmetric]
    butlast_nonresizing_def[symmetric]
    nat_of_uint64_conv_def
  apply (rewrite at \<open>(_, \<hole>, _)\<close> arl.fold_custom_empty)+
  apply (rewrite at \<open>op_arl_empty\<close> annotate_assn[where A=analyse_refinement_assn])
  unfolding nth_rll_def[symmetric] length_rll_def[symmetric]
    fmap_rll_def[symmetric]
    fmap_length_rll_def[symmetric]
  apply (rewrite at \<open>arena_lit _ (_ + \<hole>)\<close> nat_of_uint64_conv_def[symmetric])
  by sepref


declare lit_redundant_rec_wl_lookup_code.refine[sepref_fr_rules]

sepref_definition lit_redundant_rec_wl_lookup_fast_code
  is \<open>uncurry5 (isa_lit_redundant_rec_wl_lookup)\<close>
  :: \<open>[\<lambda>(((((M, NU), D), cach), analysis), lbd). length NU \<le> uint64_max]\<^sub>a
      trail_pol_fast_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a (uint32_nat_assn *a array_assn option_bool_assn)\<^sup>k *\<^sub>a
        cach_refinement_l_assn\<^sup>d *\<^sub>a analyse_refinement_fast_assn\<^sup>d *\<^sub>a lbd_assn\<^sup>k \<rightarrow>
      cach_refinement_l_assn *a analyse_refinement_fast_assn *a bool_assn\<close>
  supply [[goals_limit = 1]] neq_Nil_revE[elim] image_image[simp]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l[intro]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l_atms[intro] length_rll_def[simp]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l_atms[intro] nth_rll_def[simp]
    fmap_length_rll_u_def[simp]
    fmap_length_rll_def[simp]
    arena_lit_pre_le[intro]
  unfolding isa_lit_redundant_rec_wl_lookup_def
    conflict_min_cach_set_removable_def[symmetric]
    conflict_min_cach_def[symmetric]
    get_literal_and_remove_of_analyse_wl_def
    nth_rll_def[symmetric] PR_CONST_def
    fmap_rll_u_def[symmetric]
    fmap_rll_def[symmetric]
    butlast_nonresizing_def[symmetric]
    nat_of_uint64_conv_def
  apply (rewrite at \<open>(_, \<hole>, _)\<close> arl.fold_custom_empty)+
  apply (rewrite at \<open>op_arl_empty\<close> annotate_assn[where A=analyse_refinement_fast_assn])

  unfolding nth_rll_def[symmetric] length_rll_def[symmetric]
    fmap_rll_def[symmetric]
    fmap_length_rll_def[symmetric]
  unfolding nth_rll_def[symmetric] length_rll_def[symmetric]
    fmap_rll_def[symmetric]
    fmap_length_rll_def[symmetric]
    zero_uint32_nat_def[symmetric]
    fmap_rll_u_def[symmetric]
  by sepref (* slow *)

declare lit_redundant_rec_wl_lookup_fast_code.refine[sepref_fr_rules]

sepref_definition delete_index_and_swap_code
  is \<open>uncurry (RETURN oo delete_index_and_swap)\<close>
  :: \<open>[\<lambda>(xs, i). i < length xs]\<^sub>a
      (arl_assn unat_lit_assn)\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> arl_assn unat_lit_assn\<close>
  unfolding delete_index_and_swap.simps
  by sepref

declare delete_index_and_swap_code.refine[sepref_fr_rules]

sepref_definition (in -)lookup_conflict_upd_None_code
  is \<open>uncurry (RETURN oo lookup_conflict_upd_None)\<close>
  :: \<open>[\<lambda>((n, xs), i). i < length xs \<and> n > 0]\<^sub>a
     lookup_clause_rel_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> lookup_clause_rel_assn\<close>
  unfolding lookup_conflict_upd_None_RETURN_def fast_minus_def[symmetric]
  by sepref

declare lookup_conflict_upd_None_code.refine[sepref_fr_rules]


sepref_definition literal_redundant_wl_lookup_code
  is \<open>uncurry5 isa_literal_redundant_wl_lookup\<close>
  :: \<open>[\<lambda>(((((M, NU), D), cach), L), lbd). True]\<^sub>a
      trail_pol_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a lookup_clause_rel_assn\<^sup>k *\<^sub>a
      cach_refinement_l_assn\<^sup>d *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a lbd_assn\<^sup>k \<rightarrow>
      cach_refinement_l_assn *a analyse_refinement_assn *a bool_assn\<close>
  supply [[goals_limit=1]] Pos_unat_lit_assn[sepref_fr_rules] Neg_unat_lit_assn[sepref_fr_rules]
  literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l[intro]
  literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l_atms[intro]
  unfolding isa_literal_redundant_wl_lookup_def zero_uint32_nat_def[symmetric] PR_CONST_def
  apply (rewrite at \<open>(_, \<hole>, _)\<close> arl.fold_custom_empty)+
  unfolding single_replicate
  unfolding arl.fold_custom_empty
  by sepref

declare literal_redundant_wl_lookup_code.refine[sepref_fr_rules]

sepref_definition literal_redundant_wl_lookup_fast_code
  is \<open>uncurry5 isa_literal_redundant_wl_lookup\<close>
  :: \<open>[\<lambda>(((((M, NU), D), cach), L), lbd). length NU \<le> uint64_max]\<^sub>a
      trail_pol_fast_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a lookup_clause_rel_assn\<^sup>k *\<^sub>a
      cach_refinement_l_assn\<^sup>d *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a lbd_assn\<^sup>k \<rightarrow>
      cach_refinement_l_assn *a analyse_refinement_fast_assn *a bool_assn\<close>
  supply [[goals_limit=1]] Pos_unat_lit_assn[sepref_fr_rules] Neg_unat_lit_assn[sepref_fr_rules]
  literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l[intro]
  literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l_atms[intro]
  unfolding isa_literal_redundant_wl_lookup_def zero_uint32_nat_def[symmetric] PR_CONST_def
  apply (rewrite at \<open>(_, \<hole>, _)\<close> arl.fold_custom_empty)+
  unfolding single_replicate one_uint64_nat_def[symmetric]
  unfolding arl.fold_custom_empty
  by sepref

declare literal_redundant_wl_lookup_fast_code.refine[sepref_fr_rules]

sepref_definition conflict_remove1_code
  is \<open>uncurry (RETURN oo lookup_conflict_remove1)\<close>
  :: \<open>[lookup_conflict_remove1_pre]\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a lookup_clause_rel_assn\<^sup>d \<rightarrow>
     lookup_clause_rel_assn\<close>
  supply [[goals_limit=2]] one_uint32_nat[sepref_fr_rules]
  unfolding lookup_conflict_remove1_def one_uint32_nat_def[symmetric] fast_minus_def[symmetric]
  lookup_conflict_remove1_pre_def
  by sepref

declare conflict_remove1_code.refine[sepref_fr_rules]


sepref_definition minimize_and_extract_highest_lookup_conflict_code
  is \<open>uncurry5 (isa_minimize_and_extract_highest_lookup_conflict)\<close>
  :: \<open>[\<lambda>(((((M, NU), D), cach), lbd), outl). True]\<^sub>a
       trail_pol_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a lookup_clause_rel_assn\<^sup>d *\<^sub>a
        cach_refinement_l_assn\<^sup>d *\<^sub>a lbd_assn\<^sup>k *\<^sub>a out_learned_assn\<^sup>d \<rightarrow>
      lookup_clause_rel_assn *a cach_refinement_l_assn *a out_learned_assn\<close>
  supply [[goals_limit=1]] Pos_unat_lit_assn[sepref_fr_rules] Neg_unat_lit_assn[sepref_fr_rules]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l[intro]
    minimize_and_extract_highest_lookup_conflict_inv_def[simp]
    in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint_max'[intro] length_u_hnr[sepref_fr_rules]
    array_set_hnr_u[sepref_fr_rules]
  unfolding isa_minimize_and_extract_highest_lookup_conflict_def zero_uint32_nat_def[symmetric]
    one_uint32_nat_def[symmetric] PR_CONST_def
    length_uint32_nat_def[symmetric] minimize_and_extract_highest_lookup_conflict_inv_def
  by sepref

declare minimize_and_extract_highest_lookup_conflict_code.refine[sepref_fr_rules]

sepref_definition minimize_and_extract_highest_lookup_conflict_fast_code
  is \<open>uncurry5 isa_minimize_and_extract_highest_lookup_conflict\<close>
  :: \<open>[\<lambda>(((((M, NU), D), cach), lbd), outl). length NU \<le> uint64_max]\<^sub>a
       trail_pol_fast_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a lookup_clause_rel_assn\<^sup>d *\<^sub>a
        cach_refinement_l_assn\<^sup>d *\<^sub>a lbd_assn\<^sup>k *\<^sub>a out_learned_assn\<^sup>d \<rightarrow>
      lookup_clause_rel_assn *a cach_refinement_l_assn *a out_learned_assn\<close>
  supply [[goals_limit=1]] Pos_unat_lit_assn[sepref_fr_rules] Neg_unat_lit_assn[sepref_fr_rules]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l[intro]
    minimize_and_extract_highest_lookup_conflict_inv_def[simp]
    in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint_max'[intro] length_u_hnr[sepref_fr_rules]
    array_set_hnr_u[sepref_fr_rules]
  unfolding isa_minimize_and_extract_highest_lookup_conflict_def zero_uint32_nat_def[symmetric]
    one_uint32_nat_def[symmetric] PR_CONST_def
    length_uint32_nat_def[symmetric] minimize_and_extract_highest_lookup_conflict_inv_def
  by sepref

declare minimize_and_extract_highest_lookup_conflict_fast_code.refine[sepref_fr_rules]

sepref_definition isasat_lookup_merge_eq2_code
  is \<open>uncurry7 isasat_lookup_merge_eq2\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a trail_pol_assn\<^sup>k  *\<^sub>a arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d *\<^sub>a
         uint32_nat_assn\<^sup>k *\<^sub>a lbd_assn\<^sup>d *\<^sub>a out_learned_assn\<^sup>d \<rightarrow>\<^sub>a
      conflict_option_rel_assn *a uint32_nat_assn *a lbd_assn *a out_learned_assn\<close>
  supply [[goals_limit = 1]]
  unfolding isasat_lookup_merge_eq2_def add_to_lookup_conflict_def
    isa_outlearned_add_def isa_clvls_add_def
    is_NOTIN_def[symmetric]
  supply length_rll_def[simp] nth_rll_def[simp]
    image_image[simp] literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[simp]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_get_level_uint_max[dest]
    fmap_length_rll_u_def[simp]
    arena_is_valid_clause_idx_le_uint64_max[intro]
  apply (rewrite in \<open>if _ then _ + \<hole> else _\<close> one_uint32_nat_def[symmetric])
  apply (rewrite in \<open>if _ then _ + \<hole> else _\<close> one_uint32_nat_def[symmetric])
  by sepref

sepref_definition isasat_lookup_merge_eq2_fast_code
  is \<open>uncurry7 isasat_lookup_merge_eq2\<close>
  :: \<open>[\<lambda>(((((((L, M), NU), _), _), _), _), _). length NU \<le> uint64_max]\<^sub>a
     unat_lit_assn\<^sup>k *\<^sub>a trail_pol_fast_assn\<^sup>k  *\<^sub>a arena_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a
       conflict_option_rel_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a lbd_assn\<^sup>d *\<^sub>a out_learned_assn\<^sup>d \<rightarrow>
      conflict_option_rel_assn *a uint32_nat_assn *a lbd_assn *a out_learned_assn\<close>
  supply [[goals_limit = 1]]
  unfolding isasat_lookup_merge_eq2_def add_to_lookup_conflict_def
    isa_outlearned_add_def isa_clvls_add_def
    is_NOTIN_def[symmetric]
  supply length_rll_def[simp] nth_rll_def[simp]
    image_image[simp] literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[simp]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_get_level_uint_max[dest]
    fmap_length_rll_u_def[simp]
    arena_is_valid_clause_idx_le_uint64_max[dest]
    arena_lit_pre_le2[dest]
  apply (rewrite in \<open>if _ then _ + \<hole> else _\<close> one_uint32_nat_def[symmetric])
  apply (rewrite in \<open>if _ then _ + \<hole> else _\<close> one_uint32_nat_def[symmetric])
  apply (rewrite in \<open>if _ then arena_lit _ (_ + \<hole>) else _\<close> one_uint64_nat_def[symmetric])
  by sepref

declare
  isasat_lookup_merge_eq2_fast_code.refine[sepref_fr_rules]
  isasat_lookup_merge_eq2_code.refine[sepref_fr_rules]

end