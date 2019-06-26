theory IsaSAT_Clauses_LLVM
  imports IsaSAT_Clauses  IsaSAT_Arena_LLVM
begin

sepref_register fm_mv_clause_to_new_arena

abbreviation clause_ll_assn :: \<open>nat clause_l \<Rightarrow> _ \<Rightarrow> assn\<close> where
  \<open>clause_ll_assn \<equiv> array_assn unat_lit_assn\<close>

sepref_definition is_short_clause_code
  is \<open>RETURN o is_short_clause\<close>
  :: \<open> clause_ll_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding is_short_clause_def MAX_LENGTH_SHORT_CLAUSE_def
  apply (annot_snat_const "TYPE(32)")
apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  apply sepref_dbg_side_unfold
oops
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
   two_uint64_nat_def[symmetric]
   apply (rewrite in \<open>let _ = _ - _ in _\<close> length_uint64_nat_def[symmetric])
   apply (rewrite in \<open>let _ = _ in let _ = _ in let _ = \<hole> in _\<close> uint32_of_uint64_conv_def[symmetric])
   apply (rewrite at \<open>WHILEIT _ (\<lambda>(_, _)._ < \<hole>)\<close> length_uint64_nat_def[symmetric])
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
   apply (rewrite in \<open>let _ = _ - _ in _\<close> length_uint64_nat_def[symmetric])
   apply (rewrite in \<open>let _ = _ in let _ = _ in let _ = \<hole> in _\<close> uint32_of_uint64_conv_def[symmetric])
  apply (rewrite at \<open>WHILEIT _ (\<lambda>(_, _)._ < \<hole>)\<close> length_uint64_nat_def[symmetric])
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
  unfolding fm_mv_clause_to_new_arena_def
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