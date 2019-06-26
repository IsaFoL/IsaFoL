theory IsaSAT_Clauses_SML
  imports IsaSAT_Clauses IsaSAT_Arena_SML
begin

abbreviation isasat_clauses_assn where
  \<open>isasat_clauses_assn \<equiv> arlO_assn clause_ll_assn *a arl_assn (clause_status_assn *a uint32_nat_assn *a uint32_nat_assn)\<close>

lemma AStatus_IRRED [sepref_fr_rules]:
  \<open>(uncurry0 (return 0), uncurry0 (RETURN AStatus_IRRED)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a arena_el_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: AStatus_IRRED_def arena_el_rel_def hr_comp_def uint32_nat_rel_def br_def
      status_rel_def bitfield_rel_def nat_0_AND)

lemma AStatus_IRRED2 [sepref_fr_rules]:
  \<open>(uncurry0 (return 0b100), uncurry0 (RETURN AStatus_IRRED2)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a arena_el_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: AStatus_IRRED2_def arena_el_rel_def hr_comp_def uint32_nat_rel_def br_def
      status_rel_def bitfield_rel_def nat_0_AND)

lemma AStatus_LEARNED [sepref_fr_rules]:
  \<open>(uncurry0 (return 0b101), uncurry0 (RETURN AStatus_LEARNED)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a arena_el_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: AStatus_LEARNED_def arena_el_rel_def hr_comp_def uint32_nat_rel_def br_def
      status_rel_def bitfield_rel_def)

lemma AStatus_LEARNED2 [sepref_fr_rules]:
  \<open>(uncurry0 (return 0b001), uncurry0 (RETURN AStatus_LEARNED2)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a arena_el_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: AStatus_LEARNED2_def arena_el_rel_def hr_comp_def uint32_nat_rel_def br_def
    status_rel_def bitfield_rel_def)

lemma AActivity_hnr[sepref_fr_rules]:
  \<open>(return o id, RETURN o AActivity) \<in> uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a arena_el_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: AStatus_LEARNED_def arena_el_rel_def hr_comp_def uint32_nat_rel_def br_def
    status_rel_def)

lemma ALBD_hnr[sepref_fr_rules]:
  \<open>(return o id, RETURN o ALBD) \<in> uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a arena_el_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: AStatus_LEARNED_def arena_el_rel_def hr_comp_def uint32_nat_rel_def br_def
    status_rel_def)

lemma ASize_hnr[sepref_fr_rules]:
  \<open>(return o id, RETURN o ASize) \<in> uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a arena_el_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: AStatus_LEARNED_def arena_el_rel_def hr_comp_def uint32_nat_rel_def br_def
    status_rel_def)

lemma APos_hnr[sepref_fr_rules]:
  \<open>(return o id, RETURN o APos) \<in> uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a arena_el_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: arena_el_rel_def hr_comp_def uint32_nat_rel_def br_def
    status_rel_def)

lemma ALit_hnr[sepref_fr_rules]:
  \<open>(return o id, RETURN o ALit) \<in> unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a arena_el_assn\<close>
  apply sepref_to_hoare
  by sep_auto
    (sep_auto simp: arena_el_rel_def hr_comp_def uint32_nat_rel_def br_def unat_lit_rel_def)
lemma (in-)
  four_uint64_nat_hnr[sepref_fr_rules]:
    \<open>(uncurry0 (return 4), uncurry0 (RETURN four_uint64_nat)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close> and
  five_uint64_nat_hnr[sepref_fr_rules]:
    \<open>(uncurry0 (return 5), uncurry0 (RETURN five_uint64_nat)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by (sepref_to_hoare; sep_auto simp: uint64_nat_rel_def br_def)+

sepref_register fm_mv_clause_to_new_arena


definition clauses_ll_assn
   :: \<open>vdom \<Rightarrow> nat clauses_l \<Rightarrow> uint32 array_list \<Rightarrow> assn\<close>
where
  \<open>clauses_ll_assn vdom = hr_comp arena_assn (clauses_l_fmat vdom)\<close>

lemma nth_raa_i_uint64_hnr':
  assumes p: \<open>is_pure R\<close>
  shows
    \<open>(uncurry2 (\<lambda>(N, _) j. nth_raa_i_u64 N j), uncurry2 (RETURN \<circ>\<circ>\<circ> (\<lambda>(N, _) j. nth_rll N j))) \<in>
       [\<lambda>(((l, _),i),j). i < length l \<and> j < length_rll l i]\<^sub>a
       (arlO_assn (array_assn R) *a GG)\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> R\<close>
  unfolding nth_raa_i_u64_def
  supply nth_aa_hnr[to_hnr, sep_heap_rules]
  using assms
  by sepref_to_hoare (sep_auto simp: uint64_nat_rel_def br_def)

lemma nth_raa_hnr':
  assumes p: \<open>is_pure R\<close>
  shows
    \<open>(uncurry2 (\<lambda>(N, _) j k. nth_raa N j k), uncurry2 (RETURN \<circ>\<circ>\<circ> (\<lambda>(N, _) i. nth_rll N i))) \<in>
       [\<lambda>(((l, _),i),j). i < length l \<and> j < length_rll l i]\<^sub>a
       (arlO_assn (array_assn R) *a GG)\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> R\<close>
  using assms
  by sepref_to_hoare sep_auto

sepref_definition nth_rll_u32_i64_clauses
  is \<open>uncurry2 (RETURN ooo (\<lambda>(N, _) j. nth_rll N j))\<close>
  :: \<open>[\<lambda>(((xs, _), i), j). i < length xs \<and> j < length (xs !i)]\<^sub>a
     (isasat_clauses_assn)\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  by sepref


sepref_definition nth_rll_u64_i64_clauses
  is \<open>uncurry2 (RETURN ooo (\<lambda>(N, _) j. nth_rll N j))\<close>
  :: \<open>[\<lambda>(((xs, _), i), j). i < length xs \<and> j < length (xs !i)]\<^sub>a
     (isasat_clauses_assn)\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  by sepref


sepref_definition length_rll_n_uint32_clss
  is \<open>uncurry (RETURN oo (\<lambda>(N, _) i. length_rll_n_uint32 N i))\<close>
  :: \<open>[\<lambda>((xs, _), i). i < length xs \<and> length (xs ! i) \<le> uint32_max]\<^sub>a
       isasat_clauses_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  by sepref


sepref_definition length_raa_i64_u_clss
  is \<open>uncurry (RETURN oo (\<lambda>(N, _) i. length_rll_n_uint32 N i))\<close>
  :: \<open>[\<lambda>((xs, _), i). i < length xs \<and> length (xs ! i) \<le> uint32_max]\<^sub>a
       isasat_clauses_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  by sepref


sepref_definition length_raa_u64_clss
  is \<open>uncurry ((RETURN \<circ>\<circ>\<circ> case_prod) (\<lambda>N _. length_rll_n_uint64 N))\<close>
  :: \<open>[\<lambda>((xs, _), i). i < length xs \<and> length (xs ! i) \<le> uint64_max]\<^sub>a
        isasat_clauses_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  by sepref

sepref_definition length_raa_u32_u64_clss
  is \<open>uncurry ((RETURN \<circ>\<circ>\<circ> case_prod) (\<lambda>N _. length_rll_n_uint64 N))\<close>
  :: \<open>[\<lambda>((xs, _), i). i < length xs \<and> length (xs ! i) \<le> uint64_max]\<^sub>a
        isasat_clauses_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  by sepref

sepref_definition length_raa_u64_u64_clss
  is \<open>uncurry ((RETURN \<circ>\<circ>\<circ> case_prod) (\<lambda>N _. length_rll_n_uint64 N))\<close>
  :: \<open>[\<lambda>((xs, _), i). i < length xs \<and> length (xs ! i) \<le> uint64_max]\<^sub>a
        isasat_clauses_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  by sepref



sepref_definition length_raa_u32_clss
  is \<open>uncurry (RETURN \<circ>\<circ> (\<lambda>(N, _) i. length_rll N i))\<close>
  :: \<open>[\<lambda>((xs, _), i). i < length xs]\<^sub>a isasat_clauses_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  by sepref

sepref_definition length_raa_clss
  is \<open>uncurry (RETURN \<circ>\<circ> (\<lambda>(N, _) i. length_rll N i))\<close>
  :: \<open>[\<lambda>((xs, _), i). i < length xs]\<^sub>a isasat_clauses_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  by sepref


sepref_definition swap_aa_clss
  is \<open>uncurry3 (RETURN oooo (\<lambda>(N, xs) i j k. (swap_ll N i j k, xs)))\<close>
  :: \<open>[\<lambda>((((xs, _), k), i), j). k < length xs \<and> i < length_rll xs k \<and> j < length_rll xs k]\<^sub>a
      isasat_clauses_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> isasat_clauses_assn\<close>
  by sepref

sepref_definition is_short_clause_code
  is \<open>RETURN o is_short_clause\<close>
  :: \<open>clause_ll_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding is_short_clause_def MAX_LENGTH_SHORT_CLAUSE_def
  by sepref
declare is_short_clause_code.refine[sepref_fr_rules]

sepref_definition header_size_code
  is \<open>RETURN o header_size\<close>
  :: \<open>clause_ll_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  unfolding header_size_def
  by sepref

declare header_size_code.refine[sepref_fr_rules]

sepref_definition append_and_length_code
  is \<open>uncurry2 fm_add_new\<close>
  :: \<open>[\<lambda>((b, C), N). length C \<le> uint32_max+2 \<and> length C \<ge> 2]\<^sub>a bool_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>d *\<^sub>a (arena_assn)\<^sup>d \<rightarrow>
       arena_assn *a nat_assn\<close>
  supply [[goals_limit=1]] le_uint32_max_le_uint64_max[intro]
  unfolding fm_add_new_def AStatus_IRRED_def[symmetric] AStatus_IRRED2_def[symmetric]
   AStatus_LEARNED_def[symmetric] AStatus_LEARNED2_def[symmetric]
   two_uint64_nat_def[symmetric] one_uint64_nat_def[symmetric]
   apply (rewrite in \<open>(\<hole>, _)\<close> zero_uint64_nat_def[symmetric])
   apply (rewrite in \<open>let _ = _ - _ in _\<close> length_uint64_nat_def[symmetric])
   apply (rewrite in \<open>let _ = _ in let _ = _ in let _ = \<hole> in _\<close> uint32_of_uint64_conv_def[symmetric])
   apply (rewrite at \<open>WHILEIT _ (\<lambda>(_, _)._ < \<hole>)\<close> length_uint64_nat_def[symmetric])
  unfolding zero_uint32_nat_def[symmetric]
  by sepref

declare append_and_length_code.refine[sepref_fr_rules]


sepref_definition (in -) header_size_fast_code
  is \<open>RETURN o header_size\<close>
  :: \<open>clause_ll_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  supply uint64_max_def[simp]
  unfolding header_size_def  five_uint64_nat_def[symmetric] four_uint64_nat_def[symmetric]
(*
  apply (subst nat_of_uint64_loc.nat_of_uint64_numeral_def[symmetric])
  apply (simp add: uint64_max_def IsaSAT_Clauses.nat_of_uint64_def)
  apply (subst nat_of_uint64_loc.nat_of_uint64_numeral_def[symmetric])
   apply (simp add: uint64_max_def IsaSAT_Clauses.nat_of_uint64_def)
  apply (rewrite at \<open>If _ \<hole>\<close> PR_CONST_def[symmetric])
  apply (rewrite at \<open>If _ _ \<hole>\<close> PR_CONST_def[symmetric])
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_constraints*)
  by sepref

declare (in -)header_size_fast_code.refine[sepref_fr_rules]
(* End Move *)


sepref_definition (in -)append_and_length_fast_code
  is \<open>uncurry2 fm_add_new_fast\<close>
  :: \<open>[append_and_length_fast_code_pre]\<^sub>a
     bool_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>d *\<^sub>a (arena_fast_assn)\<^sup>d \<rightarrow>
       arena_fast_assn *a uint64_nat_assn\<close>
  supply [[goals_limit=1]] le_uint32_max_le_uint64_max[intro] append_and_length_code_fast[intro]
    header_size_def[simp] if_splits[split] header_size_fast_code.refine[sepref_fr_rules]
  unfolding fm_add_new_def AStatus_IRRED_def[symmetric] append_and_length_fast_code_pre_def
   AStatus_LEARNED_def[symmetric] AStatus_LEARNED2_def[symmetric]
   AStatus_IRRED2_def[symmetric]  four_uint64_nat_def[symmetric]
   two_uint64_nat_def[symmetric] fm_add_new_fast_def
   two_uint64_nat_def[symmetric] one_uint64_nat_def[symmetric]
   apply (rewrite in \<open>(\<hole>, _)\<close> zero_uint64_nat_def[symmetric])
   apply (rewrite in \<open>let _ = _ - _ in _\<close> length_uint64_nat_def[symmetric])
   apply (rewrite in \<open>let _ = _ in let _ = _ in let _ = \<hole> in _\<close> uint32_of_uint64_conv_def[symmetric])
  apply (rewrite at \<open>WHILEIT _ (\<lambda>(_, _)._ < \<hole>)\<close> length_uint64_nat_def[symmetric])
  unfolding zero_uint32_nat_def[symmetric]
  by sepref

declare append_and_length_fast_code.refine[sepref_fr_rules]

sepref_definition fmap_swap_ll_u64_clss
  is \<open>uncurry3 (RETURN oooo (\<lambda>(N, xs) i j k. (swap_ll N i j k, xs)))\<close>
  ::\<open>[\<lambda>((((xs, _), k), i), j). k < length xs \<and> i < length_rll xs k \<and> j < length_rll xs k]\<^sub>a
     (isasat_clauses_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k)  \<rightarrow>
           isasat_clauses_assn\<close>
  by sepref

sepref_definition fmap_rll_u_clss
  is \<open>uncurry2 (RETURN ooo (\<lambda>(N, _) i. nth_rll N i))\<close>
  :: \<open>[\<lambda>(((l, _), i), j). i < length l \<and> j < length_rll l i]\<^sub>a
       isasat_clauses_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k  \<rightarrow>
        unat_lit_assn\<close>
  by sepref

sepref_definition fmap_rll_u32_clss
  is \<open>uncurry2 (RETURN ooo (\<lambda>(N, _) i. nth_rll N i))\<close>
  :: \<open>[\<lambda>(((l, _), i), j). i < length l \<and> j < length_rll l i]\<^sub>a
       isasat_clauses_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k  \<rightarrow>
        unat_lit_assn\<close>
  supply length_rll_def[simp]
  by sepref

sepref_definition swap_lits_code
  is \<open>uncurry3 isa_arena_swap\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (arl_assn uint32_assn)\<^sup>d  \<rightarrow>\<^sub>a arl_assn uint32_assn\<close>
  unfolding isa_arena_swap_def WB_More_Refinement_List.swap_def IICF_List.swap_def[symmetric]
  by sepref

lemma swap_lits_refine[sepref_fr_rules]:
  \<open>(uncurry3 swap_lits_code, uncurry3 (RETURN oooo swap_lits))
  \<in> [uncurry3 swap_lits_pre]\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a arena_assn\<^sup>d \<rightarrow> arena_assn\<close>
  using swap_lits_code.refine[FCOMP isa_arena_swap[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp)


sepref_definition (in -) swap_lits_fast_code
  is \<open>uncurry3 isa_arena_swap\<close>
  :: \<open>[\<lambda>(((_, _), _), N). length N \<le> uint64_max]\<^sub>a
      uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a (arl64_assn uint32_assn)\<^sup>d  \<rightarrow>
         arl64_assn uint32_assn\<close>
  unfolding isa_arena_swap_def WB_More_Refinement_List.swap_def IICF_List.swap_def[symmetric]
  by sepref


lemma swap_lits_fast_refine[sepref_fr_rules]:
  \<open>(uncurry3 swap_lits_fast_code, uncurry3 (RETURN oooo swap_lits))
  \<in> [\<lambda>(((C, i), j), arena). swap_lits_pre C i j arena \<and> length arena \<le> uint64_max]\<^sub>a
     uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>d \<rightarrow> arena_fast_assn\<close>
  using swap_lits_fast_code.refine[FCOMP isa_arena_swap[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl64_assn_comp)

declare swap_lits_fast_code.refine[sepref_fr_rules]
sepref_definition fm_mv_clause_to_new_arena_code
  is \<open>uncurry2 fm_mv_clause_to_new_arena\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a arena_assn\<^sup>d \<rightarrow>\<^sub>a arena_assn\<close>
  supply [[goals_limit=1]]
  unfolding fm_mv_clause_to_new_arena_def length_uint64_nat_def
  apply (rewrite at \<open>_ \<le> \<hole>\<close> four_uint64_nat_def[symmetric])+
  apply (rewrite at \<open>let _ = _ + \<hole> in _\<close> nat_of_uint64_conv_def[symmetric])
  by sepref

declare fm_mv_clause_to_new_arena_code.refine[sepref_fr_rules]
sepref_definition fm_mv_clause_to_new_arena_fast_code
  is \<open>uncurry2 fm_mv_clause_to_new_arena\<close>
  :: \<open>[\<lambda>((n, arena\<^sub>o), arena). length arena\<^sub>o \<le> uint64_max \<and> length arena + arena_length arena\<^sub>o n +
         (if arena_length arena\<^sub>o  n \<le> 4 then 4 else 5) \<le> uint64_max]\<^sub>a
       uint64_nat_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>d \<rightarrow> arena_fast_assn\<close>
  supply [[goals_limit=1]] if_splits[split]
  unfolding fm_mv_clause_to_new_arena_def four_uint64_nat_def[symmetric] five_uint64_nat_def[symmetric]
    one_uint64_nat_def[symmetric] nat_of_uint64_conv_def
  by sepref

declare fm_mv_clause_to_new_arena_code.refine[sepref_fr_rules]

end