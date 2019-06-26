theory IsaSAT_Lookup_Conflict_SML
imports
    IsaSAT_Lookup_Conflict
    IsaSAT_Trail_SML
    IsaSAT_Clauses_SML
    LBD_SML
begin

sepref_register set_lookup_conflict_aa
type_synonym lookup_clause_assn = \<open>uint32 \<times> bool array\<close>

type_synonym (in -) option_lookup_clause_assn = \<open>bool \<times> uint32 \<times> bool array\<close>

definition analyse_refinement_rel where
  \<open>analyse_refinement_rel = nat_rel \<times>\<^sub>f {(n, (L, b)). \<exists>L'. (L', L) \<in> uint32_nat_rel \<and>
      n = uint64_of_uint32 L' + (if b then 1 << 32 else 0)}\<close>

definition to_ana_ref_id where
  [simp]: \<open>to_ana_ref_id = (\<lambda>a b c. (a, b, c))\<close>

definition to_ana_ref :: \<open>_ \<Rightarrow> uint32 \<Rightarrow> bool \<Rightarrow> _\<close> where
  \<open>to_ana_ref = (\<lambda>a c b. (a, uint64_of_uint32 c OR (if b then 1 << 32 else (0 :: uint64))))\<close>

definition from_ana_ref_id where
  [simp]: \<open>from_ana_ref_id x = x\<close>

definition from_ana_ref where
  \<open>from_ana_ref = (\<lambda>(a, b). (a, uint32_of_uint64 (take_only_lower32 b), is_marked_binary_code (a, b)))\<close>

abbreviation option_bool_assn where
  \<open>option_bool_assn \<equiv>  pure option_bool_rel\<close>

type_synonym (in -) out_learned_assn = \<open>uint32 array_list32\<close>

abbreviation (in -) out_learned_assn :: \<open>out_learned \<Rightarrow> out_learned_assn \<Rightarrow> assn\<close> where
  \<open>out_learned_assn \<equiv> arl32_assn unat_lit_assn\<close>


abbreviation (in -) minimize_status_assn where
  \<open>minimize_status_assn \<equiv> (id_assn :: minimize_status \<Rightarrow> _)\<close>

abbreviation (in -) lookup_clause_rel_assn
  :: \<open>lookup_clause_rel \<Rightarrow> lookup_clause_assn \<Rightarrow> assn\<close>
where
 \<open>lookup_clause_rel_assn \<equiv> (uint32_nat_assn *a array_assn option_bool_assn)\<close>

abbreviation (in -)conflict_option_rel_assn
  :: \<open>conflict_option_rel \<Rightarrow> option_lookup_clause_assn \<Rightarrow> assn\<close>
where
 \<open>conflict_option_rel_assn \<equiv> (bool_assn *a lookup_clause_rel_assn)\<close>

abbreviation isasat_conflict_assn where
  \<open>isasat_conflict_assn \<equiv> bool_assn *a uint32_nat_assn *a array_assn option_bool_assn\<close>

definition (in -)ana_refinement_assn where
  \<open>ana_refinement_assn \<equiv> hr_comp (nat_assn *a uint64_assn) analyse_refinement_rel\<close>

definition (in -)ana_refinement_fast_assn where
  \<open>ana_refinement_fast_assn \<equiv> hr_comp (uint64_nat_assn *a uint64_assn) analyse_refinement_rel\<close>

abbreviation (in -)analyse_refinement_assn where
  \<open>analyse_refinement_assn \<equiv> arl32_assn ana_refinement_assn\<close>

(*TODO move*)
lemma ex_assn_def_pure_eq_start:
  \<open>(\<exists>\<^sub>Aba. \<up> (ba = h) * P ba) = P h\<close>
  by (subst ex_assn_def, auto)+

lemma ex_assn_def_pure_eq_start':
  \<open>(\<exists>\<^sub>Aba. \<up> (h = ba) * P ba) = P h\<close>
  by (subst ex_assn_def, auto)+

lemma ex_assn_def_pure_eq_start2:
  \<open>(\<exists>\<^sub>Aba b. \<up> (ba = h b) * P b ba) = (\<exists>\<^sub>Ab .  P b (h b))\<close>
  by (subst ex_assn_def, subst (2) ex_assn_def, auto)+

lemma ex_assn_def_pure_eq_start3:
  \<open>(\<exists>\<^sub>Aba b c. \<up> (ba = h b) * P b ba c) = (\<exists>\<^sub>Ab c.  P b (h b) c)\<close>
  by (subst ex_assn_def, subst (3) ex_assn_def, auto)+

lemma ex_assn_def_pure_eq_start3':
  \<open>(\<exists>\<^sub>Aba b c. \<up> (bb = ba) * P b ba c) = (\<exists>\<^sub>Ab c.  P b bb c)\<close>
  by (subst ex_assn_def, subst (3) ex_assn_def, auto)+

lemma ex_assn_def_pure_eq_start4':
  \<open>(\<exists>\<^sub>Aba b c d. \<up> (bb = ba) * P b ba c d) = (\<exists>\<^sub>Ab c d.  P b bb c d)\<close>
  by (subst ex_assn_def, subst (4) ex_assn_def, auto)+

lemma ex_assn_def_pure_eq_start1:
  \<open>(\<exists>\<^sub>Aba. \<up> (ba = h b) * P ba) = (P (h b))\<close>
  by (subst ex_assn_def, auto)+
(*End Move*)

lemma ex_assn_cong:
  \<open>(\<And>x. P x = P' x) \<Longrightarrow> (\<exists>\<^sub>Ax. P x) = (\<exists>\<^sub>Ax. P' x)\<close>
  by auto


abbreviation (in -)analyse_refinement_fast_assn where
  \<open>analyse_refinement_fast_assn \<equiv>
    arl32_assn ana_refinement_fast_assn\<close>

lemma lookup_clause_assn_is_None_lookup_clause_assn_is_None:
 \<open>(return o lookup_clause_assn_is_None, RETURN o lookup_clause_assn_is_None) \<in>
  conflict_option_rel_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare
   (sep_auto simp: lookup_clause_assn_is_None_def)

lemma NOTIN_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return False), uncurry0 (RETURN NOTIN)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a option_bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: NOTIN_def option_bool_rel_def)

lemma POSIN_hnr[sepref_fr_rules]:
  \<open>(return o (\<lambda>_. True), RETURN o ISIN) \<in> bool_assn\<^sup>k \<rightarrow>\<^sub>a option_bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: ISIN_def option_bool_rel_def)

lemma is_NOTIN_hnr[sepref_fr_rules]:
  \<open>(return o Not, RETURN o is_NOTIN) \<in> option_bool_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: is_NOTIN_def option_bool_rel_def split: option.splits)

lemma (in -) SEEN_REMOVABLE[sepref_fr_rules]:
  \<open>(uncurry0 (return SEEN_REMOVABLE),uncurry0 (RETURN SEEN_REMOVABLE)) \<in>
     unit_assn\<^sup>k \<rightarrow>\<^sub>a minimize_status_assn\<close>
  by (sepref_to_hoare) sep_auto

lemma (in -) SEEN_FAILED[sepref_fr_rules]:
  \<open>(uncurry0 (return SEEN_FAILED),uncurry0 (RETURN SEEN_FAILED)) \<in>
     unit_assn\<^sup>k \<rightarrow>\<^sub>a minimize_status_assn\<close>
  by (sepref_to_hoare) sep_auto

lemma (in -) SEEN_UNKNOWN[sepref_fr_rules]:
  \<open>(Sepref_Misc.uncurry0 (return SEEN_UNKNOWN),Sepref_Misc.uncurry0 (RETURN SEEN_UNKNOWN)) \<in>
     unit_assn\<^sup>k \<rightarrow>\<^sub>a minimize_status_assn\<close>
  by (sepref_to_hoare) sep_auto

lemma size_lookup_conflict[sepref_fr_rules]:
   \<open>(return o (\<lambda>(_, n, _). n), RETURN o size_lookup_conflict) \<in>
   (bool_assn *a lookup_clause_rel_assn)\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding size_lookup_conflict_def
  apply sep_auto
  apply sepref_to_hoare
  subgoal for x xi
    apply (cases x, cases xi)
    apply sep_auto
    done
  done


lemma option_bool_assn_is_None[sepref_fr_rules]:
  \<open>(return o Not, RETURN o is_None) \<in> option_bool_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare
     (sep_auto simp: option_bool_rel_def hr_comp_def)

sepref_definition is_in_conflict_code
  is \<open>uncurry (RETURN oo is_in_lookup_conflict)\<close>
  :: \<open>[\<lambda>((n, xs), L). atm_of L < length xs]\<^sub>a
       lookup_clause_rel_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> bool_assn\<close>
  supply length_rll_def[simp] nth_rll_def[simp] uint32_max_def[simp]
    uint32_nat_assn_one[sepref_fr_rules] image_image[simp]
  unfolding is_in_lookup_conflict_def
  by sepref

declare is_in_conflict_code.refine[sepref_fr_rules]

lemma lookup_clause_assn_is_empty_lookup_clause_assn_is_empty:
 \<open>(return o lookup_clause_assn_is_empty, RETURN o lookup_clause_assn_is_empty) \<in>
  conflict_option_rel_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare
     (sep_auto simp: lookup_clause_assn_is_empty_def uint32_nat_rel_def br_def nat_of_uint32_0_iff)

lemma to_ana_ref_id_fast_hnr[sepref_fr_rules]:
  \<open>(uncurry2 (return ooo to_ana_ref), uncurry2 (RETURN ooo to_ana_ref_id)) \<in>
   uint64_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a bool_assn\<^sup>k \<rightarrow>\<^sub>a
   ana_refinement_fast_assn\<close>
 by sepref_to_hoare
   (sep_auto simp: to_ana_ref_def to_ana_ref_id_def uint32_nat_rel_def
   analyse_refinement_rel_def uint64_nat_rel_def br_def OR_132_is_sum
   pure_def ana_refinement_fast_assn_def hr_comp_def
   nat_of_uint64_uint64_of_uint32
   nat_of_uint32_le_uint32_max)

lemma to_ana_ref_id_hnr[sepref_fr_rules]:
  \<open>(uncurry2 (return ooo to_ana_ref), uncurry2 (RETURN ooo to_ana_ref_id)) \<in>
   nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a bool_assn\<^sup>k \<rightarrow>\<^sub>a
   ana_refinement_assn\<close>
  by sepref_to_hoare
  (sep_auto simp: to_ana_ref_def to_ana_ref_id_def uint32_nat_rel_def
   analyse_refinement_rel_def uint64_nat_rel_def br_def OR_132_is_sum
   pure_def ana_refinement_assn_def hr_comp_def
   nat_of_uint64_uint64_of_uint32
   nat_of_uint32_le_uint32_max)

lemma [sepref_fr_rules]:
  \<open>((return o from_ana_ref), (RETURN o from_ana_ref_id)) \<in>
   ana_refinement_fast_assn\<^sup>k \<rightarrow>\<^sub>a
   uint64_nat_assn *a uint32_nat_assn *a bool_assn\<close>
proof -
  have \<open>(4294967296::uint64) = (0::uint64) \<longleftrightarrow> (0 :: uint64) = 4294967296\<close>
    by argo
  also have \<open>\<dots> \<longleftrightarrow> False\<close>
    by auto
  finally have [iff]: \<open>(4294967296::uint64) \<noteq> (0::uint64)\<close>
    by blast
  have eq: \<open>(1::uint64) << (32::nat) = 4294967296\<close>
    by (auto simp: numeral_eq_Suc shiftl_t2n_uint64)

  show ?thesis
    apply sepref_to_hoare
    apply (case_tac xi)
    apply
      (sep_auto simp: from_ana_ref_def from_ana_ref_id_def
      analyse_refinement_rel_def uint64_nat_rel_def br_def
      case_prod_beta ana_refinement_fast_assn_def pure_def)
    apply (auto simp: hr_comp_def uint32_nat_rel_def br_def
      take_only_lower32_le_uint32_max nat_of_uint64_uint64_of_uint32
      nat_of_uint32_le_uint32_max nat_of_uint64_1_32 take_only_lower32_1_32
	take_only_lower32_le_uint32_max_ge_uint32_max AND_2_32_bool
	le_uint32_max_AND2_32_eq0)
    apply (auto simp: eq  simp del: star_aci(2))[]
    apply (subst norm_assertion_simps(17)[symmetric])
    apply (subst star_aci(2))
    apply (rule ent_refl_true)
    done
qed

lemma [sepref_fr_rules]:
  \<open>((return o from_ana_ref), (RETURN o from_ana_ref_id)) \<in>
   ana_refinement_assn\<^sup>k \<rightarrow>\<^sub>a
  nat_assn *a uint32_nat_assn *a bool_assn\<close>
proof -
  have \<open>(4294967296::uint64) = (0::uint64) \<longleftrightarrow> (0 :: uint64) = 4294967296\<close>
    by argo
  also have \<open>\<dots> \<longleftrightarrow> False\<close>
    by auto
  finally have [iff]: \<open>(4294967296::uint64) \<noteq> (0::uint64)\<close>
    by blast
  have eq: \<open>(1::uint64) << (32::nat) = 4294967296\<close>
    by (auto simp: numeral_eq_Suc shiftl_t2n_uint64)

  show ?thesis
    apply sepref_to_hoare
    apply (case_tac xi)
    apply
      (sep_auto simp: from_ana_ref_def from_ana_ref_id_def
      analyse_refinement_rel_def uint64_nat_rel_def br_def
      case_prod_beta ana_refinement_assn_def pure_def)
    apply (auto simp: hr_comp_def uint32_nat_rel_def br_def
      take_only_lower32_le_uint32_max nat_of_uint64_uint64_of_uint32
      nat_of_uint32_le_uint32_max nat_of_uint64_1_32 take_only_lower32_1_32
	take_only_lower32_le_uint32_max_ge_uint32_max AND_2_32_bool
	le_uint32_max_AND2_32_eq0)
    apply (auto simp: eq  simp del: star_aci(2))[]
    apply (subst norm_assertion_simps(17)[symmetric])
    apply (subst star_aci(2))
    apply (rule ent_refl_true)
    done
qed

lemma minimize_status_eq_hnr[sepref_fr_rules]:
  \<open>(uncurry (return oo (=)), uncurry (RETURN oo (=))) \<in>
    minimize_status_assn\<^sup>k *\<^sub>a minimize_status_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by (sepref_to_hoare) (sep_auto)


abbreviation (in -) cach_refinement_l_assn where
  \<open>cach_refinement_l_assn \<equiv> array_assn minimize_status_assn *a arl32_assn uint32_nat_assn\<close>

sepref_register conflict_min_cach_l
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
  supply length_rll_def[simp] nth_rll_def[simp] uint32_max_def[simp]
    uint32_nat_assn_one[sepref_fr_rules] image_image[simp] literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[simp]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_get_level_uint32_max[dest]
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
      trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d *\<^sub>a
         uint32_nat_assn\<^sup>k *\<^sub>a lbd_assn\<^sup>d *\<^sub>a out_learned_assn\<^sup>d \<rightarrow>
      conflict_option_rel_assn *a uint32_nat_assn *a lbd_assn *a out_learned_assn\<close>
  supply length_rll_def[simp] nth_rll_def[simp] uint32_max_def[simp]
    uint32_nat_assn_one[sepref_fr_rules] image_image[simp] literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[simp]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_get_level_uint32_max[dest]
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
  supply length_rll_def[simp] nth_rll_def[simp] uint32_max_def[simp]
    image_image[simp] literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[simp]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_get_level_uint32_max[dest]
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
      trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d *\<^sub>a
         uint32_nat_assn\<^sup>k *\<^sub>a lbd_assn\<^sup>d  *\<^sub>a out_learned_assn\<^sup>d \<rightarrow>
      conflict_option_rel_assn *a uint32_nat_assn *a lbd_assn *a out_learned_assn\<close>
  supply length_rll_def[simp] nth_rll_def[simp] uint32_max_def[simp]
    image_image[simp] literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[simp]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_get_level_uint32_max[dest]
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



sepref_register isa_resolve_merge_conflict_gt2

sepref_definition resolve_merge_conflict_code
  is \<open>uncurry6 isa_resolve_merge_conflict_gt2\<close>
  :: \<open>[isa_set_lookup_conflict_aa_pre]\<^sub>a
      trail_pol_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d *\<^sub>a
         uint32_nat_assn\<^sup>k *\<^sub>a lbd_assn\<^sup>d *\<^sub>a out_learned_assn\<^sup>d \<rightarrow>
      conflict_option_rel_assn *a uint32_nat_assn *a lbd_assn *a out_learned_assn\<close>
  supply length_rll_def[simp] nth_rll_def[simp] uint32_max_def[simp]
    image_image[simp] literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[simp]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_get_level_uint32_max[dest]
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
      trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d *\<^sub>a
         uint32_nat_assn\<^sup>k *\<^sub>a lbd_assn\<^sup>d *\<^sub>a out_learned_assn\<^sup>d \<rightarrow>
      conflict_option_rel_assn *a uint32_nat_assn *a lbd_assn *a out_learned_assn\<close>
  supply length_rll_def[simp] nth_rll_def[simp] uint32_max_def[simp]
    image_image[simp] literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[simp]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_get_level_uint32_max[dest]
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

lemma conflict_min_cach_set_failed_l_alt_def:
  \<open>conflict_min_cach_set_failed_l = (\<lambda>(cach, sup) L. do {
     ASSERT(L < length cach);
     ASSERT(length sup \<le> 1 + uint32_max div 2);
     let b = (cach ! L = SEEN_UNKNOWN);
     RETURN (cach[L := SEEN_FAILED], if b  then sup @ [L] else sup)
   })\<close>
  unfolding conflict_min_cach_set_failed_l_def Let_def by auto

lemma le_uint32_max_div2_le_uint32_max: \<open>a2' \<le> Suc (uint32_max div 2) \<Longrightarrow> a2' < uint32_max\<close>
  by (auto simp: uint32_max_def)

sepref_definition (in -) conflict_min_cach_set_failed_l_code
  is \<open>uncurry conflict_min_cach_set_failed_l\<close>
  :: \<open>cach_refinement_l_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a cach_refinement_l_assn\<close>
  supply arl_append_hnr[sepref_fr_rules] le_uint32_max_div2_le_uint32_max[intro]
  unfolding conflict_min_cach_set_failed_l_alt_def
  by sepref

lemma conflict_min_cach_set_removable_l_alt_def:
  \<open>conflict_min_cach_set_removable_l = (\<lambda>(cach, sup) L. do {
     ASSERT(L < length cach);
     ASSERT(length sup \<le> 1 + uint32_max div 2);
     let b = (cach ! L = SEEN_UNKNOWN);
     RETURN (cach[L := SEEN_REMOVABLE], if b then sup @ [L] else sup)
   })\<close>
  unfolding conflict_min_cach_set_removable_l_def by auto

sepref_definition (in -) conflict_min_cach_set_removable_l_code
  is \<open>uncurry conflict_min_cach_set_removable_l\<close>
  :: \<open>cach_refinement_l_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a cach_refinement_l_assn\<close>
  supply arl_append_hnr[sepref_fr_rules] le_uint32_max_div2_le_uint32_max[intro]
  unfolding conflict_min_cach_set_removable_l_alt_def
  by sepref

declare conflict_min_cach_set_removable_l_code.refine[sepref_fr_rules]


lemma lookup_conflict_size_hnr[sepref_fr_rules]:
  \<open>(return o fst, RETURN o lookup_conflict_size) \<in> lookup_clause_rel_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare sep_auto

lemma single_replicate: \<open>[C] = op_list_append [] C\<close>
  by auto
lemma [safe_constraint_rules]: \<open>CONSTRAINT is_pure ana_refinement_fast_assn\<close>
  unfolding CONSTRAINT_def ana_refinement_fast_assn_def
  by (auto intro: hr_comp_is_pure)

lemma [safe_constraint_rules]: \<open>CONSTRAINT is_pure ana_refinement_assn\<close>
  unfolding CONSTRAINT_def ana_refinement_assn_def
  by (auto intro: hr_comp_is_pure)

sepref_register lookup_conflict_remove1

sepref_register isa_lit_redundant_rec_wl_lookup


abbreviation (in -) highest_lit_assn where
  \<open>highest_lit_assn \<equiv> option_assn (unat_lit_assn *a uint32_nat_assn)\<close>

sepref_register from_ana_ref_id

sepref_register isa_mark_failed_lits_stack

sepref_register lit_redundant_rec_wl_lookup conflict_min_cach_set_removable_l
  get_propagation_reason_pol lit_redundant_reason_stack_wl_lookup

sepref_register isa_minimize_and_extract_highest_lookup_conflict isa_literal_redundant_wl_lookup

lemma set_lookup_empty_conflict_to_none_hnr[sepref_fr_rules]:
  \<open>(return o set_lookup_empty_conflict_to_none, RETURN o set_lookup_empty_conflict_to_none) \<in>
     lookup_clause_rel_assn\<^sup>d \<rightarrow>\<^sub>a conflict_option_rel_assn\<close>
  by sepref_to_hoare (sep_auto simp: set_lookup_empty_conflict_to_none_def)

lemma isa_mark_failed_lits_stackI:
  assumes 
    \<open>length ba \<le> Suc (uint32_max div 2)\<close> and
    \<open>a1' < length ba\<close>
  shows \<open>Suc a1' \<le> uint32_max\<close>
  using assms by (auto simp: uint32_max_def)

sepref_register to_ana_ref_id
sepref_definition isa_mark_failed_lits_stack_code
  is \<open>uncurry2 (isa_mark_failed_lits_stack)\<close>
  :: \<open>arena_assn\<^sup>k *\<^sub>a analyse_refinement_assn\<^sup>d *\<^sub>a cach_refinement_l_assn\<^sup>d \<rightarrow>\<^sub>a
      cach_refinement_l_assn\<close>
  supply [[goals_limit = 1]] neq_Nil_revE[elim!] image_image[simp] length_rll_def[simp]
    mark_failed_lits_stack_inv_helper1[dest] mark_failed_lits_stack_inv_helper2[dest]
    fmap_length_rll_u_def[simp] isa_mark_failed_lits_stackI[intro] le_uint32_max_div2_le_uint32_max[intro]
  unfolding isa_mark_failed_lits_stack_def PR_CONST_def
    conflict_min_cach_set_failed_def[symmetric]
    conflict_min_cach_def[symmetric]
    get_literal_and_remove_of_analyse_wl_def
    nth_rll_def[symmetric]
    fmap_rll_def[symmetric]
    conflict_min_cach_set_failed_l_alt_def
  apply (rewrite at \<open>arena_lit _ (_ + \<hole> - _)\<close> nat_of_uint32_conv_def[symmetric])
  apply (rewrite in \<open>_ + \<hole>\<close> one_uint32_nat_def[symmetric])
  apply (rewrite in \<open>(\<hole>, _)\<close> zero_uint32_nat_def[symmetric])
  by sepref


sepref_definition isa_mark_failed_lits_stack_fast_code
  is \<open>uncurry2 (isa_mark_failed_lits_stack)\<close>
  :: \<open>[\<lambda>((N, _), _). length N \<le> uint64_max]\<^sub>a
    arena_fast_assn\<^sup>k *\<^sub>a analyse_refinement_fast_assn\<^sup>d *\<^sub>a cach_refinement_l_assn\<^sup>d \<rightarrow>
    cach_refinement_l_assn\<close>
  supply [[goals_limit = 1]] neq_Nil_revE[elim!] image_image[simp] length_rll_def[simp]
    mark_failed_lits_stack_inv_helper1[dest] mark_failed_lits_stack_inv_helper2[dest]
    fmap_length_rll_u_def[simp] isa_mark_failed_lits_stackI[intro]
    arena_is_valid_clause_idx_le_uint64_max[intro] le_uint32_max_div2_le_uint32_max[intro]
  unfolding isa_mark_failed_lits_stack_def PR_CONST_def
    conflict_min_cach_set_failed_def[symmetric]
    conflict_min_cach_def[symmetric]
    get_literal_and_remove_of_analyse_wl_def
    nth_rll_def[symmetric]
    fmap_rll_def[symmetric]
    arena_lit_def[symmetric]
    conflict_min_cach_set_failed_l_alt_def
  apply (rewrite at \<open>arena_lit _ (_ + \<hole> - _)\<close> uint64_of_uint32_conv_def[symmetric])
  apply (rewrite in \<open>_ - \<hole>\<close> one_uint64_nat_def[symmetric])
  apply (rewrite in \<open>_ - \<hole>\<close> one_uint64_nat_def[symmetric])
  apply (rewrite in \<open>_ - \<hole>\<close> one_uint64_nat_def[symmetric])
  apply (rewrite in \<open>_ + \<hole>\<close> one_uint32_nat_def[symmetric])
  apply (rewrite in \<open>(\<hole>, _)\<close> zero_uint32_nat_def[symmetric])
  by sepref

declare isa_mark_failed_lits_stack_code.refine[sepref_fr_rules]
  isa_mark_failed_lits_stack_fast_code.refine[sepref_fr_rules]

sepref_definition isa_get_literal_and_remove_of_analyse_wl_code
  is \<open>uncurry (RETURN oo isa_get_literal_and_remove_of_analyse_wl)\<close>
  :: \<open>[uncurry isa_get_literal_and_remove_of_analyse_wl_pre]\<^sub>a
      arena_assn\<^sup>k *\<^sub>a analyse_refinement_assn\<^sup>d \<rightarrow>
      unat_lit_assn *a analyse_refinement_assn\<close>
  unfolding isa_get_literal_and_remove_of_analyse_wl_pre_def
    isa_get_literal_and_remove_of_analyse_wl_def fast_minus_def[symmetric]
    one_uint32_nat_def[symmetric]
  apply (rewrite at \<open>arena_lit _ (_ + \<hole>)\<close> nat_of_uint32_conv_def[symmetric])
  by sepref

sepref_definition isa_get_literal_and_remove_of_analyse_wl_fast_code
  is \<open>uncurry (RETURN oo isa_get_literal_and_remove_of_analyse_wl)\<close>
  :: \<open>[\<lambda>(arena, analyse). isa_get_literal_and_remove_of_analyse_wl_pre arena analyse \<and>
         length arena \<le> uint64_max]\<^sub>a
      arena_fast_assn\<^sup>k *\<^sub>a analyse_refinement_fast_assn\<^sup>d \<rightarrow>
      unat_lit_assn *a analyse_refinement_fast_assn\<close>
  supply [[goals_limit=1]] arena_lit_pre_le2[dest]
  unfolding isa_get_literal_and_remove_of_analyse_wl_pre_def
  isa_get_literal_and_remove_of_analyse_wl_def fast_minus_def[symmetric]
  one_uint32_nat_def[symmetric]
  apply (rewrite at \<open>arena_lit _ (_ + \<hole>)\<close> uint64_of_uint32_conv_def[symmetric])
  by sepref

declare isa_get_literal_and_remove_of_analyse_wl_code.refine[sepref_fr_rules]
declare isa_get_literal_and_remove_of_analyse_wl_fast_code.refine[sepref_fr_rules]

sepref_definition ana_lookup_conv_lookup_fast_code
  is \<open>uncurry (RETURN oo ana_lookup_conv_lookup)\<close>
  :: \<open>[uncurry ana_lookup_conv_lookup_pre]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a
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
      unat_lit_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>
      ana_refinement_fast_assn\<close>
  unfolding lit_redundant_reason_stack_wl_lookup_def lit_redundant_reason_stack_wl_lookup_pre_def
    two_uint64_nat_def[symmetric] zero_uint32_nat_def[symmetric]
    one_uint32_nat_def[symmetric]
  by sepref

declare lit_redundant_reason_stack_wl_lookup_fast_code.refine[sepref_fr_rules]
  lit_redundant_reason_stack_wl_lookup_code.refine[sepref_fr_rules]


declare get_propagation_reason_code.refine[sepref_fr_rules]

lemma isa_lit_redundant_rec_wl_lookupI:
  assumes 
    \<open>length ba \<le> Suc (uint32_max div 2)\<close>
  shows \<open>length ba < uint32_max\<close>
  using assms by (auto simp: uint32_max_def)

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
    fmap_length_rll_u_def[simp] isa_lit_redundant_rec_wl_lookupI[intro]
    fmap_length_rll_def[simp] isa_mark_failed_lits_stackI[intro]
  unfolding isa_lit_redundant_rec_wl_lookup_def
    conflict_min_cach_set_removable_def[symmetric]
    conflict_min_cach_def[symmetric]
    get_literal_and_remove_of_analyse_wl_def
    nth_rll_def[symmetric] PR_CONST_def
    fmap_rll_u_def[symmetric]
    fmap_rll_def[symmetric]
    butlast_nonresizing_def[symmetric]
    nat_of_uint64_conv_def
  apply (rewrite at \<open>(_, \<hole>, _)\<close> arl32.fold_custom_empty)+
  apply (rewrite at \<open>op_arl32_empty\<close> annotate_assn[where A=analyse_refinement_assn])
  unfolding nth_rll_def[symmetric] length_rll_def[symmetric]
    fmap_rll_def[symmetric]
    fmap_length_rll_def[symmetric]
  apply (rewrite at \<open>arena_lit _ (_ + \<hole>)\<close> nat_of_uint64_conv_def[symmetric])
  by sepref


declare lit_redundant_rec_wl_lookup_code.refine[sepref_fr_rules]

sepref_definition lit_redundant_rec_wl_lookup_fast_code
  is \<open>uncurry5 (isa_lit_redundant_rec_wl_lookup)\<close>
  :: \<open>[\<lambda>(((((M, NU), D), cach), analysis), lbd). length NU \<le> uint64_max]\<^sub>a
      trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a (uint32_nat_assn *a array_assn option_bool_assn)\<^sup>k *\<^sub>a
        cach_refinement_l_assn\<^sup>d *\<^sub>a analyse_refinement_fast_assn\<^sup>d *\<^sub>a lbd_assn\<^sup>k \<rightarrow>
      cach_refinement_l_assn *a analyse_refinement_fast_assn *a bool_assn\<close>
  supply [[goals_limit = 1]] neq_Nil_revE[elim] image_image[simp]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l[intro]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l_atms[intro] length_rll_def[simp]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l_atms[intro] nth_rll_def[simp]
    fmap_length_rll_u_def[simp]
    fmap_length_rll_def[simp]  isa_lit_redundant_rec_wl_lookupI[intro]
    arena_lit_pre_le[intro]  isa_mark_failed_lits_stackI[intro]
  unfolding isa_lit_redundant_rec_wl_lookup_def
    conflict_min_cach_set_removable_def[symmetric]
    conflict_min_cach_def[symmetric]
    get_literal_and_remove_of_analyse_wl_def
    nth_rll_def[symmetric] PR_CONST_def
    fmap_rll_u_def[symmetric]
    fmap_rll_def[symmetric]
    butlast_nonresizing_def[symmetric]
    nat_of_uint64_conv_def
  apply (rewrite at \<open>(_, \<hole>, _)\<close> arl32.fold_custom_empty)+
  apply (rewrite at \<open>op_arl32_empty\<close> annotate_assn[where A=analyse_refinement_fast_assn])

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
(*TODO Move taken from trail*)

  definition arl32_butlast_nonresizing :: \<open>'a array_list32 \<Rightarrow> 'a array_list32\<close> where
  \<open>arl32_butlast_nonresizing = (\<lambda>(xs, a). (xs, a - 1))\<close>

lemma butlast32_nonresizing_hnr[sepref_fr_rules]:
  \<open>(return o arl32_butlast_nonresizing, RETURN o butlast_nonresizing) \<in>
    [\<lambda>xs. xs \<noteq> []]\<^sub>a (arl32_assn R)\<^sup>d \<rightarrow> arl32_assn R\<close>
proof -
  have [simp]: \<open>nat_of_uint32 (b - 1) = nat_of_uint32 b - 1\<close>
    if
      \<open>x \<noteq> []\<close> and
      \<open>(take (nat_of_uint32 b) l', x) \<in> \<langle>the_pure R\<rangle>list_rel\<close>
    for x :: \<open>'b list\<close> and a :: \<open>'a array\<close> and b :: \<open>uint32\<close> and l' :: \<open>'a list\<close> and aa :: \<open>Heap.heap\<close> and ba :: \<open>nat set\<close>
  by (metis less_one list_rel_pres_neq_nil nat_of_uint32_012(3) nat_of_uint32_less_iff
    nat_of_uint32_notle_minus take_eq_Nil that)

  show ?thesis
    by sepref_to_hoare
     (sep_auto simp: arl32_butlast_nonresizing_def arl32_assn_def hr_comp_def
       is_array_list32_def  butlast_take list_rel_imp_same_length nat_of_uint32_ge_minus
      dest:
        list_rel_butlast[of \<open>take _ _\<close>]
      simp flip: nat_of_uint32_le_iff)
qed
(*END Move *)

find_theorems butlast arl32_assn
sepref_definition delete_index_and_swap_code
  is \<open>uncurry (RETURN oo delete_index_and_swap)\<close>
  :: \<open>[\<lambda>(xs, i). i < length xs]\<^sub>a
      (arl32_assn unat_lit_assn)\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> arl32_assn unat_lit_assn\<close>
  unfolding delete_index_and_swap.simps butlast_nonresizing_def[symmetric]
  by sepref

declare delete_index_and_swap_code.refine[sepref_fr_rules]

sepref_definition (in -)lookup_conflict_upd_None_code
  is \<open>uncurry (RETURN oo lookup_conflict_upd_None)\<close>
  :: \<open>[\<lambda>((n, xs), i). i < length xs \<and> n > 0]\<^sub>a
     lookup_clause_rel_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> lookup_clause_rel_assn\<close>
  unfolding lookup_conflict_upd_None_RETURN_def fast_minus_def[symmetric]
  by sepref

declare lookup_conflict_upd_None_code.refine[sepref_fr_rules]

lemma uint32_max_ge0:  \<open>0 < uint32_max\<close> by (auto simp: uint32_max_def)
sepref_definition literal_redundant_wl_lookup_code
  is \<open>uncurry5 isa_literal_redundant_wl_lookup\<close>
  :: \<open>[\<lambda>(((((M, NU), D), cach), L), lbd). True]\<^sub>a
      trail_pol_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a lookup_clause_rel_assn\<^sup>k *\<^sub>a
      cach_refinement_l_assn\<^sup>d *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a lbd_assn\<^sup>k \<rightarrow>
      cach_refinement_l_assn *a analyse_refinement_assn *a bool_assn\<close>
  supply [[goals_limit=1]] Pos_unat_lit_assn[sepref_fr_rules] Neg_unat_lit_assn[sepref_fr_rules]
  literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l[intro] op_arl32_empty_def[simp]
  literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l_atms[intro] uint32_max_ge0[intro!]
  unfolding isa_literal_redundant_wl_lookup_def zero_uint32_nat_def[symmetric] PR_CONST_def
  apply (rewrite at \<open>(_, \<hole>, _)\<close> arl32.fold_custom_empty)+
  unfolding single_replicate
  unfolding arl32.fold_custom_empty
  by sepref

declare literal_redundant_wl_lookup_code.refine[sepref_fr_rules]

sepref_definition literal_redundant_wl_lookup_fast_code
  is \<open>uncurry5 isa_literal_redundant_wl_lookup\<close>
  :: \<open>[\<lambda>(((((M, NU), D), cach), L), lbd). length NU \<le> uint64_max]\<^sub>a
      trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a lookup_clause_rel_assn\<^sup>k *\<^sub>a
      cach_refinement_l_assn\<^sup>d *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a lbd_assn\<^sup>k \<rightarrow>
      cach_refinement_l_assn *a analyse_refinement_fast_assn *a bool_assn\<close>
  supply [[goals_limit=1]] Pos_unat_lit_assn[sepref_fr_rules] Neg_unat_lit_assn[sepref_fr_rules]
  literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l[intro] uint32_max_ge0[intro!]
  literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l_atms[intro] op_arl32_empty_def[simp]
  unfolding isa_literal_redundant_wl_lookup_def zero_uint32_nat_def[symmetric] PR_CONST_def
  apply (rewrite at \<open>(_, \<hole>, _)\<close> arl32.fold_custom_empty)+
  unfolding single_replicate one_uint64_nat_def[symmetric]
  unfolding arl32.fold_custom_empty
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

find_theorems delete_index_and_swap arl_assn
sepref_definition minimize_and_extract_highest_lookup_conflict_code
  is \<open>uncurry5 (isa_minimize_and_extract_highest_lookup_conflict)\<close>
  :: \<open>[\<lambda>(((((M, NU), D), cach), lbd), outl). True]\<^sub>a
       trail_pol_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a lookup_clause_rel_assn\<^sup>d *\<^sub>a
        cach_refinement_l_assn\<^sup>d *\<^sub>a lbd_assn\<^sup>k *\<^sub>a out_learned_assn\<^sup>d \<rightarrow>
      lookup_clause_rel_assn *a cach_refinement_l_assn *a out_learned_assn\<close>
  supply [[goals_limit=1]] Pos_unat_lit_assn[sepref_fr_rules] Neg_unat_lit_assn[sepref_fr_rules]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l[intro]
    minimize_and_extract_highest_lookup_conflict_inv_def[simp]
    in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint32_max'[intro] length_u_hnr[sepref_fr_rules]
    array_set_hnr_u[sepref_fr_rules]
  unfolding isa_minimize_and_extract_highest_lookup_conflict_def zero_uint32_nat_def[symmetric]
    one_uint32_nat_def[symmetric] PR_CONST_def
    minimize_and_extract_highest_lookup_conflict_inv_def
  by sepref

declare minimize_and_extract_highest_lookup_conflict_code.refine[sepref_fr_rules]

sepref_definition minimize_and_extract_highest_lookup_conflict_fast_code
  is \<open>uncurry5 isa_minimize_and_extract_highest_lookup_conflict\<close>
  :: \<open>[\<lambda>(((((M, NU), D), cach), lbd), outl). length NU \<le> uint64_max]\<^sub>a
       trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a lookup_clause_rel_assn\<^sup>d *\<^sub>a
        cach_refinement_l_assn\<^sup>d *\<^sub>a lbd_assn\<^sup>k *\<^sub>a out_learned_assn\<^sup>d \<rightarrow>
      lookup_clause_rel_assn *a cach_refinement_l_assn *a out_learned_assn\<close>
  supply [[goals_limit=1]] Pos_unat_lit_assn[sepref_fr_rules] Neg_unat_lit_assn[sepref_fr_rules]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l[intro]
    minimize_and_extract_highest_lookup_conflict_inv_def[simp]
    in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint32_max'[intro] length_u_hnr[sepref_fr_rules]
    array_set_hnr_u[sepref_fr_rules]
  unfolding isa_minimize_and_extract_highest_lookup_conflict_def zero_uint32_nat_def[symmetric]
    one_uint32_nat_def[symmetric] PR_CONST_def
    minimize_and_extract_highest_lookup_conflict_inv_def
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
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_get_level_uint32_max[dest]
    fmap_length_rll_u_def[simp]
    arena_is_valid_clause_idx_le_uint64_max[intro]
  apply (rewrite in \<open>if _ then _ + \<hole> else _\<close> one_uint32_nat_def[symmetric])
  apply (rewrite in \<open>if _ then _ + \<hole> else _\<close> one_uint32_nat_def[symmetric])
  by sepref

sepref_definition isasat_lookup_merge_eq2_fast_code
  is \<open>uncurry7 isasat_lookup_merge_eq2\<close>
  :: \<open>[\<lambda>(((((((L, M), NU), _), _), _), _), _). length NU \<le> uint64_max]\<^sub>a
     unat_lit_assn\<^sup>k *\<^sub>a trail_pol_fast_assn\<^sup>k  *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a
       conflict_option_rel_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a lbd_assn\<^sup>d *\<^sub>a out_learned_assn\<^sup>d \<rightarrow>
      conflict_option_rel_assn *a uint32_nat_assn *a lbd_assn *a out_learned_assn\<close>
  supply [[goals_limit = 1]]
  unfolding isasat_lookup_merge_eq2_def add_to_lookup_conflict_def
    isa_outlearned_add_def isa_clvls_add_def
    is_NOTIN_def[symmetric]
  supply length_rll_def[simp] nth_rll_def[simp]
    image_image[simp] literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[simp]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_get_level_uint32_max[dest]
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
