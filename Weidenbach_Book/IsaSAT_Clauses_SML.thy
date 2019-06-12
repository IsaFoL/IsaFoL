theory IsaSAT_Clauses_SML
  imports IsaSAT_Arena_SML IsaSAT_Clauses
begin
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
  :: \<open>[\<lambda>((xs, _), i). i < length xs \<and> length (xs ! i) \<le> uint_max]\<^sub>a
       isasat_clauses_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  by sepref


sepref_definition length_raa_i64_u_clss
  is \<open>uncurry (RETURN oo (\<lambda>(N, _) i. length_rll_n_uint32 N i))\<close>
  :: \<open>[\<lambda>((xs, _), i). i < length xs \<and> length (xs ! i) \<le> uint_max]\<^sub>a
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
   two_uint64_nat_def[symmetric]
   apply (rewrite in \<open>let _ = _ - _ in _\<close> length_uint64_nat_def[symmetric])
   apply (rewrite in \<open>let _ = _ in let _ = _ in let _ = \<hole> in _\<close> uint32_of_uint64_conv_def[symmetric])
   apply (rewrite in \<open>_ < length _\<close> length_uint64_nat_def[symmetric])
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
     bool_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>d *\<^sub>a (arena_assn)\<^sup>d \<rightarrow>
       arena_assn *a uint64_nat_assn\<close>
  supply [[goals_limit=1]] le_uint32_max_le_uint64_max[intro] append_and_length_code_fast[intro]
    header_size_def[simp]
  unfolding fm_add_new_def AStatus_IRRED_def[symmetric] append_and_length_fast_code_pre_def
   AStatus_LEARNED_def[symmetric] AStatus_LEARNED2_def[symmetric]
   AStatus_IRRED2_def[symmetric]
   two_uint64_nat_def[symmetric] fm_add_new_fast_def
   apply (rewrite in \<open>let _ = _ - _ in _\<close> length_uint64_nat_def[symmetric])
   apply (rewrite in \<open>let _ = _ in _\<close> length_uint64_nat_def[symmetric])
   apply (rewrite in \<open>let _ = _ in let _ = _ in let _ = \<hole> in _\<close> uint32_of_uint64_conv_def[symmetric])
  apply (rewrite in \<open>_ < length _\<close> length_uint64_nat_def[symmetric])
  by sepref

declare append_and_length_fast_code.refine[sepref_fr_rules]

sepref_definition fmap_swap_ll_u64_clss
  is \<open>uncurry3 (RETURN oooo (\<lambda>(N, xs) i j k. (swap_ll N i j k, xs)))\<close>
  ::\<open>[\<lambda>((((xs, _), k), i), j). k < length xs \<and> i < length_rll xs k \<and> j < length_rll xs k]\<^sub>a
     (isasat_clauses_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k)  \<rightarrow>
           isasat_clauses_assn\<close>
  by sepref

sepref_definition fmap_rll_u_clss
  is \<open>uncurry2 (RETURN ooo (\<lambda>(N, _) i. Array_List_Array.nth_rll N i))\<close>
  :: \<open>[\<lambda>(((l, _), i), j). i < length l \<and> j < length_rll l i]\<^sub>a
       isasat_clauses_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k  \<rightarrow>
        unat_lit_assn\<close>
  by sepref

sepref_definition fmap_rll_u32_clss
  is \<open>uncurry2 (RETURN ooo (\<lambda>(N, _) i. Array_List_Array.nth_rll N i))\<close>
  :: \<open>[\<lambda>(((l, _), i), j). i < length l \<and> j < length_rll l i]\<^sub>a
       isasat_clauses_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k  \<rightarrow>
        unat_lit_assn\<close>
  supply length_rll_def[simp]
  by sepref

sepref_definition (in -) swap_lits_fast_code
  is \<open>uncurry3 isa_arena_swap\<close>
  :: \<open>[\<lambda>(((_, _), _), N). length N \<le> uint64_max]\<^sub>a
      uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a (arl_assn uint32_assn)\<^sup>d  \<rightarrow>
         arl_assn uint32_assn\<close>
  unfolding isa_arena_swap_def
  by sepref

declare swap_lits_fast_code.refine[sepref_fr_rules]
sepref_definition fm_mv_clause_to_new_arena_code
  is \<open>uncurry2 fm_mv_clause_to_new_arena\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a arena_assn\<^sup>d \<rightarrow>\<^sub>a arena_assn\<close>
  supply [[goals_limit=1]]
  unfolding fm_mv_clause_to_new_arena_def
  by sepref

declare fm_mv_clause_to_new_arena_code.refine[sepref_fr_rules]

end