theory IsaSAT_Lookup_Conflict_LLVM
imports
    IsaSAT_Lookup_Conflict
    IsaSAT_Trail_LLVM
    IsaSAT_Clauses_LLVM
    LBD_LLVM
    IsaSAT_Profile_LLVM
begin
hide_const (open) NEMonad.ASSERT NEMonad.RETURN

sepref_register set_lookup_conflict_aa
type_synonym lookup_clause_assn = \<open>32 word \<times> (1 word) ptr\<close>

type_synonym (in -) option_lookup_clause_assn = \<open>1 word \<times> lookup_clause_assn\<close>

type_synonym (in -) out_learned_assn = \<open>32 word array_list64\<close>

abbreviation (in -) out_learned_assn :: \<open>out_learned \<Rightarrow> out_learned_assn \<Rightarrow> assn\<close> where
  \<open>out_learned_assn \<equiv> arl64_assn unat_lit_assn\<close>


definition minimize_status_int_rel :: \<open>(nat \<times> minimize_status) set\<close> where
\<open>minimize_status_int_rel = {(0, SEEN_UNKNOWN), (1, SEEN_FAILED),  (2, SEEN_REMOVABLE)}\<close>

abbreviation minimize_status_ref_rel where
\<open>minimize_status_ref_rel \<equiv> snat_rel' TYPE(8)\<close>

abbreviation minimize_status_ref_assn where
  \<open>minimize_status_ref_assn \<equiv> pure minimize_status_ref_rel\<close>

definition minimize_status_rel :: \<open>_\<close> where
\<open>minimize_status_rel = minimize_status_ref_rel O minimize_status_int_rel\<close>

abbreviation minimize_status_assn :: \<open>_\<close> where
\<open>minimize_status_assn \<equiv> pure minimize_status_rel\<close>

lemma minimize_status_assn_alt_def:
  \<open>minimize_status_assn = pure (snat_rel O minimize_status_int_rel)\<close>
  unfolding minimize_status_rel_def ..

lemmas [fcomp_norm_unfold] = minimize_status_assn_alt_def[symmetric]

definition minimize_status_rel_eq :: \<open>minimize_status \<Rightarrow> minimize_status \<Rightarrow> bool\<close> where
 [simp]: \<open>minimize_status_rel_eq = (=)\<close>

lemma minimize_status_rel_eq:
   \<open>((=), minimize_status_rel_eq) \<in> minimize_status_int_rel \<rightarrow> minimize_status_int_rel \<rightarrow> bool_rel\<close>
  by (auto simp: minimize_status_int_rel_def)

sepref_def minimize_status_rel_eq_impl
  is [] \<open>uncurry (RETURN oo (=))\<close>
  :: \<open>minimize_status_ref_assn\<^sup>k *\<^sub>a minimize_status_ref_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  supply [[goals_limit=1]]
  by sepref

sepref_register minimize_status_rel_eq

lemmas [sepref_fr_rules] = minimize_status_rel_eq_impl.refine[ FCOMP minimize_status_rel_eq]

lemma
   SEEN_FAILED_rel: \<open>(1, SEEN_FAILED) \<in> minimize_status_int_rel\<close> and
   SEEN_UNKNOWN_rel:  \<open>(0, SEEN_UNKNOWN) \<in> minimize_status_int_rel\<close> and
   SEEN_REMOVABLE_rel:  \<open>(2, SEEN_REMOVABLE) \<in> minimize_status_int_rel\<close>
  by (auto simp: minimize_status_int_rel_def)

sepref_def SEEN_FAILED_impl
  is [] \<open>uncurry0 (RETURN 1)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a minimize_status_ref_assn\<close>
  supply [[goals_limit=1]]
  apply (annot_snat_const \<open>TYPE(8)\<close>)
  by sepref

sepref_def SEEN_UNKNOWN_impl
  is [] \<open>uncurry0 (RETURN 0)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a minimize_status_ref_assn\<close>
  supply [[goals_limit=1]]
  apply (annot_snat_const \<open>TYPE(8)\<close>)
  by sepref

sepref_def SEEN_REMOVABLE_impl
  is [] \<open>uncurry0 (RETURN 2)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a minimize_status_ref_assn\<close>
  supply [[goals_limit=1]]
  apply (annot_snat_const \<open>TYPE(8)\<close>)
  by sepref

lemmas [sepref_fr_rules] = SEEN_FAILED_impl.refine[FCOMP SEEN_FAILED_rel]
   SEEN_UNKNOWN_impl.refine[FCOMP SEEN_UNKNOWN_rel]
   SEEN_REMOVABLE_impl.refine[FCOMP SEEN_REMOVABLE_rel]


definition option_bool_impl_rel where
  \<open>option_bool_impl_rel = bool1_rel O option_bool_rel\<close>

abbreviation option_bool_impl_assn :: \<open>_\<close> where
\<open>option_bool_impl_assn \<equiv> pure (option_bool_impl_rel)\<close>

lemma option_bool_impl_assn_alt_def:
   \<open>option_bool_impl_assn = hr_comp bool1_assn option_bool_rel\<close>
  unfolding option_bool_impl_rel_def by (simp add: hr_comp_pure)

lemmas [fcomp_norm_unfold] = option_bool_impl_assn_alt_def[symmetric]
   option_bool_impl_rel_def[symmetric]

lemma Some_rel: \<open>(\<lambda>_. True, ISIN) \<in> bool_rel \<rightarrow> option_bool_rel\<close>
  by (auto simp: option_bool_rel_def)

sepref_def Some_impl
  is [] \<open>RETURN o (\<lambda>_. True)\<close>
  ::  \<open>bool1_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

lemmas [sepref_fr_rules] = Some_impl.refine[FCOMP Some_rel]

lemma is_Notin_rel: \<open>(\<lambda>x. \<not>x, is_NOTIN) \<in> option_bool_rel \<rightarrow> bool_rel\<close>
  by (auto simp: option_bool_rel_def)

sepref_def is_Notin_impl
  is [] \<open>RETURN o (\<lambda>x. \<not>x)\<close>
  ::  \<open>bool1_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

lemmas [sepref_fr_rules] = is_Notin_impl.refine[FCOMP is_Notin_rel]


lemma NOTIN_rel: \<open>(False, NOTIN) \<in> option_bool_rel\<close>
  by (auto simp: option_bool_rel_def)

sepref_def NOTIN_impl
  is [] \<open>uncurry0 (RETURN False)\<close>
  ::  \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

lemmas [sepref_fr_rules] = NOTIN_impl.refine[FCOMP NOTIN_rel]


definition (in -) lookup_clause_rel_assn
  :: \<open>lookup_clause_rel \<Rightarrow> lookup_clause_assn \<Rightarrow> assn\<close>
where
 \<open>lookup_clause_rel_assn \<equiv> (uint32_nat_assn \<times>\<^sub>a array_assn option_bool_impl_assn)\<close>

definition (in -)conflict_option_rel_assn
  :: \<open>conflict_option_rel \<Rightarrow> option_lookup_clause_assn \<Rightarrow> assn\<close>
where
 \<open>conflict_option_rel_assn \<equiv> (bool1_assn \<times>\<^sub>a lookup_clause_rel_assn)\<close>

lemmas [fcomp_norm_unfold] = conflict_option_rel_assn_def[symmetric]
  lookup_clause_rel_assn_def[symmetric]

definition (in -)ana_refinement_fast_rel where
  \<open>ana_refinement_fast_rel \<equiv> snat_rel' TYPE(64) \<times>\<^sub>r unat_rel' TYPE(32) \<times>\<^sub>r bool1_rel\<close>


abbreviation (in -)ana_refinement_fast_assn where
  \<open>ana_refinement_fast_assn \<equiv> sint64_nat_assn \<times>\<^sub>a uint32_nat_assn \<times>\<^sub>a bool1_assn\<close>

lemma ana_refinement_fast_assn_def:
  \<open>ana_refinement_fast_assn = pure ana_refinement_fast_rel\<close>
  by (auto simp: ana_refinement_fast_rel_def)

abbreviation (in -)analyse_refinement_fast_assn where
  \<open>analyse_refinement_fast_assn \<equiv>
    arl64_assn ana_refinement_fast_assn\<close>


lemma lookup_clause_assn_is_None_alt_def:
  \<open>RETURN o lookup_clause_assn_is_None = (\<lambda>(b, _, _). RETURN b)\<close>
  unfolding lookup_clause_assn_is_None_def by auto

sepref_def lookup_clause_assn_is_None_impl
  is \<open>RETURN o lookup_clause_assn_is_None\<close>
  :: \<open>conflict_option_rel_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding lookup_clause_assn_is_None_alt_def conflict_option_rel_assn_def
    lookup_clause_rel_assn_def
  by sepref

lemma size_lookup_conflict_alt_def:
  \<open>RETURN o size_lookup_conflict = (\<lambda>(_, b, _). RETURN b)\<close>
  unfolding size_lookup_conflict_def by auto

sepref_def size_lookup_conflict_impl
  is \<open>RETURN o size_lookup_conflict\<close>
  :: \<open>conflict_option_rel_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding size_lookup_conflict_alt_def conflict_option_rel_assn_def
    lookup_clause_rel_assn_def
  by sepref


sepref_def is_in_conflict_code
  is \<open>uncurry (RETURN oo is_in_lookup_conflict)\<close>
  :: \<open>[\<lambda>((n, xs), L). atm_of L < length xs]\<^sub>a
       lookup_clause_rel_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> bool1_assn\<close>
  supply [[goals_limit=1]]
  unfolding is_in_lookup_conflict_def is_NOTIN_alt_def[symmetric]
    lookup_clause_rel_assn_def
  by sepref


lemma lookup_clause_assn_is_empty_alt_def:
   \<open>lookup_clause_assn_is_empty = (\<lambda>S. size_lookup_conflict S = 0)\<close>
  by (auto simp: size_lookup_conflict_def lookup_clause_assn_is_empty_def fun_eq_iff)

sepref_def lookup_clause_assn_is_empty_impl
  is \<open>RETURN o lookup_clause_assn_is_empty\<close>
  :: \<open>conflict_option_rel_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding lookup_clause_assn_is_empty_alt_def
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref


definition the_lookup_conflict :: \<open>conflict_option_rel \<Rightarrow> _\<close> where
\<open>the_lookup_conflict = snd\<close>

lemma the_lookup_conflict_alt_def:
  \<open>RETURN o the_lookup_conflict = (\<lambda>(_, (n, xs)). RETURN (n, xs))\<close>
  by (auto simp: the_lookup_conflict_def)

sepref_def the_lookup_conflict_impl
  is \<open>RETURN o the_lookup_conflict\<close>
  :: \<open>conflict_option_rel_assn\<^sup>d \<rightarrow>\<^sub>a lookup_clause_rel_assn\<close>
  unfolding the_lookup_conflict_alt_def conflict_option_rel_assn_def
    lookup_clause_rel_assn_def
  by sepref


definition Some_lookup_conflict :: \<open>_ \<Rightarrow> conflict_option_rel\<close> where
\<open>Some_lookup_conflict xs = (False, xs)\<close>


lemma Some_lookup_conflict_alt_def:
  \<open>RETURN o Some_lookup_conflict = (\<lambda>xs. RETURN (False, xs))\<close>
  by (auto simp: Some_lookup_conflict_def)

sepref_def Some_lookup_conflict_impl
  is \<open>RETURN o Some_lookup_conflict\<close>
  :: \<open>lookup_clause_rel_assn\<^sup>d \<rightarrow>\<^sub>a conflict_option_rel_assn\<close>
  unfolding Some_lookup_conflict_alt_def conflict_option_rel_assn_def
    lookup_clause_rel_assn_def
  by sepref
sepref_register Some_lookup_conflict

type_synonym cach_refinement_l_assn = \<open>8 word ptr \<times> 32 word array_list64\<close>

definition (in -) cach_refinement_l_assn :: \<open>_ \<Rightarrow> cach_refinement_l_assn \<Rightarrow> _\<close> where
  \<open>cach_refinement_l_assn \<equiv> array_assn minimize_status_assn \<times>\<^sub>a arl64_assn atom_assn\<close>

sepref_register conflict_min_cach_l
sepref_def delete_from_lookup_conflict_code
  is \<open>uncurry delete_from_lookup_conflict\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a lookup_clause_rel_assn\<^sup>d \<rightarrow>\<^sub>a lookup_clause_rel_assn\<close>
  unfolding delete_from_lookup_conflict_def NOTIN_def[symmetric]
    conflict_option_rel_assn_def
    lookup_clause_rel_assn_def
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref

lemma arena_is_valid_clause_idx_le_uint64_max:
  \<open>arena_is_valid_clause_idx be bd \<Longrightarrow>
    length be \<le> sint64_max \<Longrightarrow>
   bd + arena_length be bd \<le> sint64_max\<close>
  \<open>arena_is_valid_clause_idx be bd \<Longrightarrow> length be \<le> sint64_max \<Longrightarrow>
   bd \<le> sint64_max\<close>
  using arena_lifting(10)[of be _ _ bd]
  by (fastforce simp: arena_lifting arena_is_valid_clause_idx_def)+

lemma add_to_lookup_conflict_alt_def:
  \<open>RETURN oo add_to_lookup_conflict = (\<lambda>L (n, xs). RETURN (if xs ! atm_of L = NOTIN then n + 1 else n,
      xs[atm_of L := ISIN (is_pos L)]))\<close>
  unfolding add_to_lookup_conflict_def by (auto simp: fun_eq_iff)

sepref_register ISIN NOTIN atm_of add_to_lookup_conflict

sepref_def add_to_lookup_conflict_impl
  is \<open>uncurry (RETURN oo add_to_lookup_conflict)\<close>
  :: \<open>[\<lambda>(L, (n, xs)). atm_of L < length xs \<and> n + 1 \<le> uint32_max]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a (lookup_clause_rel_assn)\<^sup>d \<rightarrow> lookup_clause_rel_assn\<close>
  unfolding add_to_lookup_conflict_alt_def lookup_clause_rel_assn_def
     is_NOTIN_alt_def[symmetric] fold_is_None NOTIN_def
  apply (rewrite at \<open>_ + \<hole>\<close> unat_const_fold[where 'a = \<open>32\<close>])
  by sepref



lemma isa_lookup_conflict_merge_alt_def:
  \<open>isa_lookup_conflict_merge i0  = (\<lambda>M N i zs clvls outl.
 do {
     let xs = the_lookup_conflict zs;
    ASSERT( arena_is_valid_clause_idx N i);
     (_, clvls, zs, outl) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i::nat, clvls :: nat, zs, outl).
         length (snd zs) = length (snd xs) \<and>
             Suc (fst zs) \<le> uint32_max \<and> Suc clvls \<le> uint32_max\<^esup>
       (\<lambda>(j :: nat, clvls, zs, outl). j < i + arena_length N i)
       (\<lambda>(j :: nat, clvls, zs, outl). do {
           ASSERT(j < length N);
           ASSERT(arena_lit_pre N j);
           ASSERT(get_level_pol_pre (M, arena_lit N j));
	   ASSERT(get_level_pol M (arena_lit N j) \<le> Suc (uint32_max div 2));
           ASSERT(atm_of (arena_lit N j) < length (snd zs));
           ASSERT(\<not>is_in_lookup_conflict zs (arena_lit N j) \<longrightarrow> length outl < uint32_max);
           let outl = isa_outlearned_add M (arena_lit N j) zs outl;
           let clvls = isa_clvls_add M (arena_lit N j) zs clvls;
           let zs = add_to_lookup_conflict (arena_lit N j) zs;
           RETURN(Suc j, clvls, zs, outl)
        })
       (i + i0, clvls, xs, outl);
     RETURN (Some_lookup_conflict zs, clvls, outl)
   })\<close>
  unfolding isa_lookup_conflict_merge_def Some_lookup_conflict_def
    the_lookup_conflict_def
  by (auto simp: fun_eq_iff)

sepref_def resolve_lookup_conflict_merge_fast_code
  is \<open>uncurry5 isa_set_lookup_conflict_aa\<close>
  :: \<open>[\<lambda>(((((M, N), i), (_, xs)), _), out).
         length N \<le> sint64_max]\<^sub>a
      trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d *\<^sub>a
         uint32_nat_assn\<^sup>k *\<^sub>a out_learned_assn\<^sup>d \<rightarrow>
      conflict_option_rel_assn \<times>\<^sub>a uint32_nat_assn \<times>\<^sub>a out_learned_assn\<close>
  supply
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_get_level_uint32_max[dest]
    arena_is_valid_clause_idx_le_uint64_max[dest]
  unfolding isa_set_lookup_conflict_aa_def lookup_conflict_merge_def
    PR_CONST_def nth_rll_def[symmetric]
    isa_outlearned_add_def isa_clvls_add_def
    isa_lookup_conflict_merge_alt_def
    fmap_rll_u_def[symmetric]
    fmap_rll_def[symmetric]
    is_NOTIN_def[symmetric] add_0_right
  apply (rewrite at \<open>RETURN (\<hole>, _ ,_, _)\<close>  Suc_eq_plus1)
  apply (rewrite at \<open>RETURN (_ + \<hole>, _ ,_, _)\<close> snat_const_fold[where 'a = \<open>64\<close>])
  apply (rewrite in \<open>If _ \<hole>\<close> unat_const_fold[where 'a = \<open>32\<close>])
  supply [[goals_limit = 1]]
  unfolding fold_tuple_optimizations
  by sepref

sepref_register isa_resolve_merge_conflict_gt2

lemma arena_is_valid_clause_idx_le_uint64_max2:
  \<open>arena_is_valid_clause_idx be bd \<Longrightarrow>
    length be \<le> sint64_max \<Longrightarrow>
   bd + arena_length be bd \<le> sint64_max\<close>
  \<open>arena_is_valid_clause_idx be bd \<Longrightarrow> length be \<le> sint64_max \<Longrightarrow>
   bd < sint64_max\<close>
  using arena_lifting(10)[of be _ _ bd]
  apply (fastforce simp: arena_lifting arena_is_valid_clause_idx_def)
  using arena_lengthI(2) less_le_trans by blast

sepref_def resolve_merge_conflict_fast_code
  is \<open>uncurry5 isa_resolve_merge_conflict_gt2\<close>
  :: \<open>[uncurry5 (\<lambda>M N i (b, xs) clvls outl. length N \<le> sint64_max)]\<^sub>a
      trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d *\<^sub>a
         uint32_nat_assn\<^sup>k *\<^sub>a  out_learned_assn\<^sup>d \<rightarrow>
      conflict_option_rel_assn \<times>\<^sub>a uint32_nat_assn \<times>\<^sub>a out_learned_assn\<close>
  supply
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_get_level_uint32_max[dest]
    fmap_length_rll_u_def[simp]
    arena_is_valid_clause_idx_le_uint64_max[intro]
    arena_is_valid_clause_idx_le_uint64_max2[dest]
  unfolding isa_resolve_merge_conflict_gt2_def lookup_conflict_merge_def
    PR_CONST_def nth_rll_def[symmetric]
    isa_outlearned_add_def isa_clvls_add_def
    isa_lookup_conflict_merge_alt_def
    fmap_rll_u_def[symmetric]
    fmap_rll_def[symmetric]
    is_NOTIN_def[symmetric] add_0_right
  apply (rewrite at \<open>RETURN (\<hole>, _ ,_, _)\<close>  Suc_eq_plus1)
  apply (rewrite at \<open>WHILEIT _ _ _ (_ + \<hole>, _ ,_, _)\<close> snat_const_fold[where 'a = \<open>64\<close>])
  apply (rewrite at \<open>RETURN (_ + \<hole>, _ ,_, _)\<close> snat_const_fold[where 'a = \<open>64\<close>])
  apply (rewrite in \<open>If _ \<hole>\<close> unat_const_fold[where 'a = \<open>32\<close>])
  supply [[goals_limit = 1]]
  unfolding fold_tuple_optimizations
  by sepref


sepref_def atm_in_conflict_code
  is \<open>uncurry (RETURN oo atm_in_conflict_lookup)\<close>
  :: \<open>[uncurry atm_in_conflict_lookup_pre]\<^sub>a
     atom_assn\<^sup>k *\<^sub>a lookup_clause_rel_assn\<^sup>k \<rightarrow> bool1_assn\<close>
  unfolding atm_in_conflict_lookup_def atm_in_conflict_lookup_pre_def
     is_NOTIN_alt_def[symmetric] fold_is_None NOTIN_def lookup_clause_rel_assn_def
  apply (rewrite at \<open> _ ! _\<close> annot_index_of_atm)
  by sepref

sepref_def conflict_min_cach_l_code
  is \<open>uncurry (RETURN oo conflict_min_cach_l)\<close>
  :: \<open>[conflict_min_cach_l_pre]\<^sub>a cach_refinement_l_assn\<^sup>k *\<^sub>a atom_assn\<^sup>k \<rightarrow> minimize_status_assn\<close>
  unfolding conflict_min_cach_l_def conflict_min_cach_l_pre_def cach_refinement_l_assn_def
  apply (rewrite at \<open>nth _\<close> eta_expand)
  apply (rewrite at \<open> _ ! _\<close> annot_index_of_atm)
  by sepref


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

sepref_def conflict_min_cach_set_failed_l_code
  is \<open>uncurry conflict_min_cach_set_failed_l\<close>
  :: \<open>cach_refinement_l_assn\<^sup>d *\<^sub>a atom_assn\<^sup>k \<rightarrow>\<^sub>a cach_refinement_l_assn\<close>
  supply [[goals_limit=1]] le_uint32_max_div2_le_uint32_max[dest]
  unfolding conflict_min_cach_set_failed_l_alt_def
    minimize_status_rel_eq_def[symmetric] cach_refinement_l_assn_def

  apply (rewrite at \<open> _ ! _\<close> annot_index_of_atm)
  apply (rewrite at \<open>list_update _ _ _\<close> annot_index_of_atm)
  by sepref


lemma conflict_min_cach_set_removable_l_alt_def:
  \<open>conflict_min_cach_set_removable_l = (\<lambda>(cach, sup) L. do {
     ASSERT(L < length cach);
     ASSERT(length sup \<le> 1 + uint32_max div 2);
     let b = (cach ! L = SEEN_UNKNOWN);
     RETURN (cach[L := SEEN_REMOVABLE], if b then sup @ [L] else sup)
   })\<close>
  unfolding conflict_min_cach_set_removable_l_def by auto

sepref_def conflict_min_cach_set_removable_l_code
  is \<open>uncurry conflict_min_cach_set_removable_l\<close>
  :: \<open>cach_refinement_l_assn\<^sup>d *\<^sub>a atom_assn\<^sup>k \<rightarrow>\<^sub>a cach_refinement_l_assn\<close>
  unfolding conflict_min_cach_set_removable_l_alt_def
    minimize_status_rel_eq_def[symmetric] cach_refinement_l_assn_def
  apply (rewrite at \<open> _ ! _\<close> annot_index_of_atm)
  apply (rewrite at \<open>list_update _ _ _\<close> annot_index_of_atm)
  by sepref


lemma lookup_conflict_size_impl_alt_def:
   \<open>RETURN o (\<lambda>(n, xs). n) = (\<lambda>(n, xs). RETURN n)\<close>
  by auto

(* TODO: Invalid abstract head! Cannot be registered as sepref_fr_rule!
  Probably not required at all?
*)
sepref_def lookup_conflict_size_impl
  is [] \<open>RETURN o (\<lambda>(n, xs). n)\<close>
  :: \<open>lookup_clause_rel_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding lookup_clause_rel_assn_def lookup_conflict_size_impl_alt_def
  by sepref

lemma single_replicate: \<open>[C] = op_list_append [] C\<close>
  by auto

sepref_register lookup_conflict_remove1

sepref_register isa_lit_redundant_rec_wl_lookup

sepref_register isa_mark_failed_lits_stack

sepref_register lit_redundant_rec_wl_lookup conflict_min_cach_set_removable_l
  get_propagation_reason_pol lit_redundant_reason_stack_wl_lookup

sepref_register isa_minimize_and_extract_highest_lookup_conflict isa_literal_redundant_wl_lookup

lemma  set_lookup_empty_conflict_to_none_alt_def:
  \<open>RETURN o set_lookup_empty_conflict_to_none = (\<lambda>(n, xs). RETURN (True, n, xs))\<close>
  by (auto simp: set_lookup_empty_conflict_to_none_def)

sepref_def set_lookup_empty_conflict_to_none_imple
  is \<open>RETURN o set_lookup_empty_conflict_to_none\<close>
  :: \<open>lookup_clause_rel_assn\<^sup>d \<rightarrow>\<^sub>a conflict_option_rel_assn\<close>
  unfolding set_lookup_empty_conflict_to_none_alt_def
    lookup_clause_rel_assn_def conflict_option_rel_assn_def
  by sepref


lemma isa_mark_failed_lits_stackI:
  assumes
    \<open>length ba \<le> Suc (uint32_max div 2)\<close> and
    \<open>a1' < length ba\<close>
  shows \<open>Suc a1' \<le> uint32_max\<close>
  using assms by (auto simp: uint32_max_def)

sepref_register conflict_min_cach_set_failed_l
sepref_def isa_mark_failed_lits_stack_fast_code
  is \<open>uncurry2 (isa_mark_failed_lits_stack)\<close>
  :: \<open>[\<lambda>((N, _), _). length N \<le> sint64_max]\<^sub>a
    arena_fast_assn\<^sup>k *\<^sub>a analyse_refinement_fast_assn\<^sup>k *\<^sub>a cach_refinement_l_assn\<^sup>d \<rightarrow>
    cach_refinement_l_assn\<close>
  supply [[goals_limit = 1]] neq_Nil_revE[elim!] image_image[simp]
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
    minimize_status_rel_eq_def[symmetric]
  apply (rewrite at 1  in \<open>conflict_min_cach_set_failed_l _ \<hole>\<close> snat_const_fold[where 'a = \<open>64\<close>])
  apply (rewrite in \<open>RETURN (_ + \<hole>, _)\<close> snat_const_fold[where 'a = \<open>64\<close>])
  apply (rewrite at 0 in \<open>(\<hole>, _)\<close>  snat_const_fold[where 'a = \<open>64\<close>])
  apply (rewrite at \<open>arena_lit _ (_ + \<hole> - _)\<close> annot_unat_snat_upcast[where 'l = 64])
  by sepref


sepref_def isa_get_literal_and_remove_of_analyse_wl_fast_code
  is \<open>uncurry (RETURN oo isa_get_literal_and_remove_of_analyse_wl)\<close>
  :: \<open>[\<lambda>(arena, analyse). isa_get_literal_and_remove_of_analyse_wl_pre arena analyse \<and>
         length arena \<le> sint64_max]\<^sub>a
      arena_fast_assn\<^sup>k *\<^sub>a analyse_refinement_fast_assn\<^sup>d \<rightarrow>
      unat_lit_assn \<times>\<^sub>a analyse_refinement_fast_assn\<close>
  supply [[goals_limit=1]] arena_lit_pre_le2[dest]
    and [dest] =  arena_lit_implI
  unfolding isa_get_literal_and_remove_of_analyse_wl_pre_def
  isa_get_literal_and_remove_of_analyse_wl_def
  apply (rewrite at \<open>length _ - \<hole>\<close> snat_const_fold[where 'a=64])
  apply (rewrite at \<open>arena_lit _ (_ + \<hole>)\<close> annot_unat_snat_upcast[where 'l = 64])
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref


sepref_def ana_lookup_conv_lookup_fast_code
  is \<open>uncurry (RETURN oo ana_lookup_conv_lookup)\<close>
  :: \<open>[uncurry ana_lookup_conv_lookup_pre]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a
    (ana_refinement_fast_assn)\<^sup>k
     \<rightarrow> sint64_nat_assn \<times>\<^sub>a sint64_nat_assn \<times>\<^sub>a sint64_nat_assn \<times>\<^sub>a sint64_nat_assn\<close>
  unfolding ana_lookup_conv_lookup_pre_def ana_lookup_conv_lookup_def
  apply (rewrite at \<open>(_, _, \<hole>, _)\<close> annot_unat_snat_upcast[where 'l = 64])
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_register arena_lit
sepref_def lit_redundant_reason_stack_wl_lookup_fast_code
  is \<open>uncurry2 (RETURN ooo lit_redundant_reason_stack_wl_lookup)\<close>
  :: \<open>[uncurry2 lit_redundant_reason_stack_wl_lookup_pre]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>
      ana_refinement_fast_assn\<close>
  unfolding lit_redundant_reason_stack_wl_lookup_def lit_redundant_reason_stack_wl_lookup_pre_def
  apply (rewrite at \<open>\<hole> < _\<close> snat_const_fold[where 'a=64])
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref


lemma isa_lit_redundant_rec_wl_lookupI:
  assumes
    \<open>length ba \<le> Suc (uint32_max div 2)\<close>
  shows \<open>length ba < uint32_max\<close>
  using assms by (auto simp: uint32_max_def)

lemma arena_lit_pre_le: \<open>
       arena_lit_pre a i \<Longrightarrow> length a \<le> sint64_max \<Longrightarrow> i \<le> sint64_max\<close>
   using arena_lifting(7)[of a _ _] unfolding arena_lit_pre_def arena_is_valid_clause_idx_and_access_def
  by fastforce

lemma get_propagation_reason_pol_get_propagation_reason_pol_raw: \<open>do {
		 C \<leftarrow> get_propagation_reason_pol M (-L);
		 case C of
		   Some C \<Rightarrow> f C
		 | None \<Rightarrow> g
            } = do {
		 C \<leftarrow> get_propagation_reason_raw_pol M (-L);
		 if C \<noteq> DECISION_REASON then f C else g
            }\<close>
  by (cases M) (auto simp: get_propagation_reason_pol_def get_propagation_reason_raw_pol_def)

sepref_register atm_in_conflict_lookup
sepref_def lit_redundant_rec_wl_lookup_fast_code
  is \<open>uncurry5 (isa_lit_redundant_rec_wl_lookup)\<close>
  :: \<open>[\<lambda>(((((M, NU), D), cach), analysis), lbd). length NU \<le> sint64_max]\<^sub>a
      trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a (lookup_clause_rel_assn)\<^sup>k *\<^sub>a
        cach_refinement_l_assn\<^sup>d *\<^sub>a analyse_refinement_fast_assn\<^sup>d *\<^sub>a lbd_assn\<^sup>k \<rightarrow>
      cach_refinement_l_assn \<times>\<^sub>a analyse_refinement_fast_assn \<times>\<^sub>a bool1_assn\<close>
  supply [[goals_limit = 1]] neq_Nil_revE[elim] image_image[simp]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l[intro]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l_atms[intro]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l_atms[intro] nth_rll_def[simp]
    fmap_length_rll_u_def[simp]
    (*fmap_length_rll_def[simp]*)  isa_lit_redundant_rec_wl_lookupI[intro]
    arena_lit_pre_le[dest]  isa_mark_failed_lits_stackI[intro]

  unfolding isa_lit_redundant_rec_wl_lookup_def
    conflict_min_cach_set_removable_def[symmetric]
    conflict_min_cach_def[symmetric]
    get_literal_and_remove_of_analyse_wl_def
    nth_rll_def[symmetric] PR_CONST_def
    fmap_rll_u_def[symmetric] minimize_status_rel_eq_def[symmetric]
    fmap_rll_def[symmetric] length_0_conv[symmetric]
  apply (subst get_propagation_reason_pol_get_propagation_reason_pol_raw)
  apply (rewrite at \<open>get_level_pol _ _ = \<hole>\<close> unat_const_fold[where 'a=32])
  apply (rewrite at \<open>(_, \<hole>, _)\<close> annotate_assn[where A=analyse_refinement_fast_assn])
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  unfolding nth_rll_def[symmetric]
    fmap_rll_def[symmetric]
    fmap_length_rll_def[symmetric]
  unfolding nth_rll_def[symmetric]
    fmap_rll_def[symmetric]
    fmap_length_rll_def[symmetric]
    fmap_rll_u_def[symmetric]
  by sepref (*slow *)


sepref_def delete_index_and_swap_code
  is \<open>uncurry (RETURN oo delete_index_and_swap)\<close>
  :: \<open>[\<lambda>(xs, i). i < length xs]\<^sub>a
      (arl64_assn unat_lit_assn)\<^sup>d *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> arl64_assn unat_lit_assn\<close>
  unfolding delete_index_and_swap.simps
  by sepref


sepref_def lookup_conflict_upd_None_code
  is \<open>uncurry (RETURN oo lookup_conflict_upd_None)\<close>
  :: \<open>[\<lambda>((n, xs), i). i < length xs \<and> n > 0]\<^sub>a
     lookup_clause_rel_assn\<^sup>d *\<^sub>a sint32_nat_assn\<^sup>k \<rightarrow> lookup_clause_rel_assn\<close>
  unfolding lookup_conflict_upd_None_RETURN_def lookup_clause_rel_assn_def
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref

lemma uint32_max_ge0:  \<open>0 < uint32_max\<close> by (auto simp: uint32_max_def)

sepref_def literal_redundant_wl_lookup_fast_code
  is \<open>uncurry5 isa_literal_redundant_wl_lookup\<close>
  :: \<open>[\<lambda>(((((M, NU), D), cach), L), lbd). length NU \<le> sint64_max]\<^sub>a
      trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a lookup_clause_rel_assn\<^sup>k *\<^sub>a
      cach_refinement_l_assn\<^sup>d *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a lbd_assn\<^sup>k \<rightarrow>
      cach_refinement_l_assn \<times>\<^sub>a analyse_refinement_fast_assn \<times>\<^sub>a bool1_assn\<close>
  supply [[goals_limit=1]]
  literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l[intro] uint32_max_ge0[intro!]
  literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l_atms[intro]
  unfolding isa_literal_redundant_wl_lookup_def PR_CONST_def
    minimize_status_rel_eq_def[symmetric]
  apply (rewrite at \<open>(_, \<hole>, _)\<close> al_fold_custom_empty[where 'l=64])+
  unfolding single_replicate
  apply (rewrite at \<open>get_level_pol _ _ = \<hole>\<close> unat_const_fold[where 'a=32])
  unfolding al_fold_custom_empty[where 'l=64]
  apply (subst get_propagation_reason_pol_get_propagation_reason_pol_raw)
  by sepref


sepref_def conflict_remove1_code
  is \<open>uncurry (RETURN oo lookup_conflict_remove1)\<close>
  :: \<open>[lookup_conflict_remove1_pre]\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a lookup_clause_rel_assn\<^sup>d \<rightarrow>
     lookup_clause_rel_assn\<close>
  supply [[goals_limit=2]]
  unfolding lookup_conflict_remove1_def lookup_conflict_remove1_pre_def lookup_clause_rel_assn_def
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref


sepref_def minimize_and_extract_highest_lookup_conflict_fast_code
  is \<open>uncurry5 isa_minimize_and_extract_highest_lookup_conflict\<close>
  :: \<open>[\<lambda>(((((M, NU), D), cach), lbd), outl). length NU \<le> sint64_max]\<^sub>a
       trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a lookup_clause_rel_assn\<^sup>d *\<^sub>a
        cach_refinement_l_assn\<^sup>d *\<^sub>a lbd_assn\<^sup>k *\<^sub>a out_learned_assn\<^sup>d \<rightarrow>
      lookup_clause_rel_assn \<times>\<^sub>a cach_refinement_l_assn \<times>\<^sub>a out_learned_assn\<close>
  supply [[goals_limit=1]]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l[intro]
    minimize_and_extract_highest_lookup_conflict_inv_def[simp]
    in_\<L>\<^sub>a\<^sub>l\<^sub>l_less_uint32_max'[intro]
  unfolding isa_minimize_and_extract_highest_lookup_conflict_def
    PR_CONST_def
    minimize_and_extract_highest_lookup_conflict_inv_def
  apply (rewrite at \<open>(_, \<hole>, _, _)\<close> snat_const_fold[where 'a = 64])
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref


lemma isasat_lookup_merge_eq2_alt_def:
  \<open>isasat_lookup_merge_eq2 L M N C = (\<lambda>zs clvls outl. do {
    let zs = the_lookup_conflict zs;
    ASSERT(arena_lit_pre N C);
    ASSERT(arena_lit_pre N (C+1));
    let L0 = arena_lit N C;
    let L' = (if L0 = L then arena_lit N (C + 1) else L0);
    ASSERT(get_level_pol_pre (M, L'));
    ASSERT(get_level_pol M L' \<le> Suc (uint32_max div 2));
    ASSERT(atm_of L' < length (snd zs));
    ASSERT(length outl < uint32_max);
    let outl = isa_outlearned_add M L' zs outl;
    ASSERT(clvls < uint32_max);
    ASSERT(fst zs < uint32_max);
    let clvls = isa_clvls_add M L' zs clvls;
    let zs = add_to_lookup_conflict L' zs;
    RETURN(Some_lookup_conflict zs, clvls, outl)
  })\<close>
  by (auto simp: the_lookup_conflict_def Some_lookup_conflict_def Let_def
     isasat_lookup_merge_eq2_def fun_eq_iff)

sepref_def isasat_lookup_merge_eq2_fast_code
  is \<open>uncurry6 isasat_lookup_merge_eq2\<close>
  :: \<open>[\<lambda>((((((L, M), NU), _), _), _), _). length NU \<le> sint64_max]\<^sub>a
     unat_lit_assn\<^sup>k *\<^sub>a trail_pol_fast_assn\<^sup>k  *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a
       conflict_option_rel_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a out_learned_assn\<^sup>d \<rightarrow>
      conflict_option_rel_assn \<times>\<^sub>a uint32_nat_assn \<times>\<^sub>a out_learned_assn\<close>
  supply [[goals_limit = 1]]
  unfolding isasat_lookup_merge_eq2_alt_def
    isa_outlearned_add_def isa_clvls_add_def
    is_NOTIN_def[symmetric]
  supply
    image_image[simp] literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[simp]
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail_get_level_uint32_max[dest]
    fmap_length_rll_u_def[simp] the_lookup_conflict_def[simp]
    arena_is_valid_clause_idx_le_uint64_max[dest]
    arena_lit_pre_le2[dest] arena_lit_pre_le[dest]
  apply (rewrite in \<open>if _ then _ + \<hole> else _\<close> unat_const_fold[where 'a=32])
  apply (rewrite in \<open>if _ then arena_lit _ (_ + \<hole>) else _\<close> snat_const_fold[where 'a=64])
  by sepref


sepref_def is_in_option_lookup_conflict_code
  is \<open>uncurry (RETURN oo is_in_option_lookup_conflict)\<close>
  :: \<open>[\<lambda>(L, (c, n, xs)). atm_of L < length xs]\<^sub>a
        unat_lit_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>k \<rightarrow> bool1_assn\<close>
  unfolding is_in_option_lookup_conflict_alt_def is_in_lookup_conflict_def PROTECT_def
     is_NOTIN_alt_def[symmetric] conflict_option_rel_assn_def lookup_clause_rel_assn_def
  by sepref

definition None_lookup_conflict :: \<open>_ \<Rightarrow> _ \<Rightarrow> conflict_option_rel\<close> where
\<open>None_lookup_conflict b xs = (b, xs)\<close>


sepref_def None_lookup_conflict_impl
  is \<open>uncurry (RETURN oo None_lookup_conflict)\<close>
  :: \<open>bool1_assn\<^sup>k *\<^sub>a lookup_clause_rel_assn\<^sup>d \<rightarrow>\<^sub>a conflict_option_rel_assn\<close>
  unfolding None_lookup_conflict_def conflict_option_rel_assn_def
    lookup_clause_rel_assn_def
  by sepref

sepref_register None_lookup_conflict
declare None_lookup_conflict_impl.refine[sepref_fr_rules]

schematic_goal mk_free_lookup_clause_rel_assn[sepref_frame_free_rules]: \<open>MK_FREE lookup_clause_rel_assn ?fr\<close>
  unfolding conflict_option_rel_assn_def lookup_clause_rel_assn_def
  by synthesize_free

schematic_goal mk_free_cach_refinement_l_assn[sepref_frame_free_rules]: \<open>MK_FREE cach_refinement_l_assn ?fr\<close>
  unfolding cach_refinement_l_assn_def
  by synthesize_free

schematic_goal mk_free_trail_pol_fast_assn[sepref_frame_free_rules]: \<open>MK_FREE conflict_option_rel_assn ?fr\<close>
  unfolding conflict_option_rel_assn_def
  by synthesize_free

experiment begin

export_llvm
  nat_lit_eq_impl
  minimize_status_rel_eq_impl
  SEEN_FAILED_impl
  SEEN_UNKNOWN_impl
  SEEN_REMOVABLE_impl
  Some_impl
  is_Notin_impl
  NOTIN_impl
  lookup_clause_assn_is_None_impl
  size_lookup_conflict_impl
  is_in_conflict_code
  lookup_clause_assn_is_empty_impl
  the_lookup_conflict_impl
  Some_lookup_conflict_impl
  delete_from_lookup_conflict_code
  add_to_lookup_conflict_impl
  resolve_lookup_conflict_merge_fast_code
  resolve_merge_conflict_fast_code
  atm_in_conflict_code
  conflict_min_cach_l_code
  conflict_min_cach_set_failed_l_code
  conflict_min_cach_set_removable_l_code
  lookup_conflict_size_impl
  set_lookup_empty_conflict_to_none_imple
  isa_mark_failed_lits_stack_fast_code
  isa_get_literal_and_remove_of_analyse_wl_fast_code
  ana_lookup_conv_lookup_fast_code
  lit_redundant_reason_stack_wl_lookup_fast_code
  lit_redundant_rec_wl_lookup_fast_code
  delete_index_and_swap_code
  lookup_conflict_upd_None_code
  literal_redundant_wl_lookup_fast_code
  conflict_remove1_code
  minimize_and_extract_highest_lookup_conflict_fast_code
  isasat_lookup_merge_eq2_fast_code

end

end
