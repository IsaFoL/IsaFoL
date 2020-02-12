theory IsaSAT_Backtrack_LLVM
  imports IsaSAT_Backtrack IsaSAT_VMTF_LLVM IsaSAT_Lookup_Conflict_LLVM
    IsaSAT_Rephase_LLVM
begin

lemma isa_empty_conflict_and_extract_clause_heur_alt_def:
    \<open>isa_empty_conflict_and_extract_clause_heur M D outl = do {
     let C = replicate (length outl) (outl!0);
     (D, C, _) \<leftarrow> WHILE\<^sub>T
         (\<lambda>(D, C, i). i < length_uint32_nat outl)
         (\<lambda>(D, C, i). do {
           ASSERT(i < length outl);
           ASSERT(i < length C);
           ASSERT(lookup_conflict_remove1_pre (outl ! i, D));
           let D = lookup_conflict_remove1 (outl ! i) D;
           let C = C[i := outl ! i];
	   ASSERT(get_level_pol_pre (M, C!i));
	   ASSERT(get_level_pol_pre (M, C!1));
	   ASSERT(1 < length C);
           let L1 = C!i;
           let L2 = C!1;
           let C = (if get_level_pol M L1 > get_level_pol M L2 then swap C 1 i else C);
           ASSERT(i+1 \<le> uint32_max);
           RETURN (D, C, i+1)
         })
        (D, C, 1);
     ASSERT(length outl \<noteq> 1 \<longrightarrow> length C > 1);
     ASSERT(length outl \<noteq> 1 \<longrightarrow>  get_level_pol_pre (M, C!1));
     RETURN ((True, D), C, if length outl = 1 then 0 else get_level_pol M (C!1))
  }\<close>
  unfolding isa_empty_conflict_and_extract_clause_heur_def (*WB_More_Refinement_List.swap_def
    swap_def[symmetric]*)
  by auto

sepref_def empty_conflict_and_extract_clause_heur_fast_code
  is \<open>uncurry2 (isa_empty_conflict_and_extract_clause_heur)\<close>
  :: \<open>[\<lambda>((M, D), outl). outl \<noteq> [] \<and> length outl \<le> uint32_max]\<^sub>a
      trail_pol_fast_assn\<^sup>k *\<^sub>a lookup_clause_rel_assn\<^sup>d *\<^sub>a out_learned_assn\<^sup>k \<rightarrow>
       (conflict_option_rel_assn) \<times>\<^sub>a clause_ll_assn \<times>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=1]] image_image[simp]
  supply [simp] = max_snat_def uint32_max_def
  unfolding isa_empty_conflict_and_extract_clause_heur_alt_def
    larray_fold_custom_replicate length_uint32_nat_def conflict_option_rel_assn_def
  apply (rewrite at \<open>\<hole>\<close> in \<open>_ !1\<close> snat_const_fold[where 'a=64])+
  apply (rewrite at \<open>\<hole>\<close> in \<open>_ !0\<close> snat_const_fold[where 'a=64])
  apply (rewrite at \<open>swap _ \<hole> _\<close> snat_const_fold[where 'a=64])
  apply (rewrite at \<open>\<hole>\<close> in \<open>(_, _, _ + 1)\<close> snat_const_fold[where 'a=64])
  apply (rewrite at \<open>\<hole>\<close> in \<open>(_, _, 1)\<close> snat_const_fold[where 'a=64])
  apply (rewrite at \<open>\<hole>\<close> in \<open>If (length _ = \<hole>)\<close> snat_const_fold[where 'a=64])
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  unfolding gen_swap convert_swap
  by sepref


lemma emptied_list_alt_def: \<open>emptied_list xs = take 0 xs\<close>
  by (auto simp: emptied_list_def)

sepref_def empty_cach_code
  is \<open>empty_cach_ref_set\<close>
  :: \<open>cach_refinement_l_assn\<^sup>d \<rightarrow>\<^sub>a cach_refinement_l_assn\<close>
  supply [[goals_limit=1]]
  unfolding empty_cach_ref_set_def comp_def cach_refinement_l_assn_def emptied_list_alt_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  apply (rewrite at \<open>_[\<hole> := SEEN_UNKNOWN]\<close> value_of_atm_def[symmetric])
  apply (rewrite at \<open>_[\<hole> := SEEN_UNKNOWN]\<close> index_of_atm_def[symmetric])
  by sepref



theorem empty_cach_code_empty_cach_ref[sepref_fr_rules]:
  \<open>(empty_cach_code, RETURN \<circ> empty_cach_ref)
    \<in> [empty_cach_ref_pre]\<^sub>a
    cach_refinement_l_assn\<^sup>d \<rightarrow> cach_refinement_l_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in>[comp_PRE Id
     (\<lambda>(cach, supp).
         (\<forall>L\<in>set supp. L < length cach) \<and>
         length supp \<le> Suc (uint32_max div 2) \<and>
         (\<forall>L<length cach. cach ! L \<noteq> SEEN_UNKNOWN \<longrightarrow> L \<in> set supp))
     (\<lambda>x y. True)
     (\<lambda>x. nofail ((RETURN \<circ> empty_cach_ref) x))]\<^sub>a
      hrp_comp (cach_refinement_l_assn\<^sup>d)
                     Id \<rightarrow> hr_comp cach_refinement_l_assn Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE[OF empty_cach_code.refine[unfolded PR_CONST_def convert_fref]
        empty_cach_ref_set_empty_cach_ref[unfolded convert_fref]] by simp
  have pre: \<open>?pre' h x\<close> if \<open>?pre x\<close> for x h
    using that by (auto simp: comp_PRE_def trail_pol_def
        ann_lits_split_reasons_def empty_cach_ref_pre_def)
  have im: \<open>?im' = ?im\<close>
    by simp
  have f: \<open>?f' = ?f\<close>
    by auto
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f apply assumption
    using pre ..
qed

sepref_register fm_add_new_fast

lemma isasat_fast_length_leD: \<open>isasat_fast S \<Longrightarrow> Suc (length (get_clauses_wl_heur S)) < max_snat 64\<close>
  by (cases S) (auto simp: isasat_fast_def max_snat_def sint64_max_def)

sepref_register update_heuristics
sepref_def update_heuristics_impl
  is [llvm_inline,sepref_fr_rules] \<open>uncurry (RETURN oo update_heuristics)\<close>
  :: \<open>uint32_nat_assn\<^sup>k *\<^sub>a heuristic_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_assn\<close>
  unfolding update_heuristics_def heuristic_assn_def
  by sepref

sepref_register cons_trail_Propagated_tr
sepref_def propagate_unit_bt_wl_D_fast_code
  is \<open>uncurry propagate_unit_bt_wl_D_int\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit = 1]] vmtf_flush_def[simp] image_image[simp] uminus_\<A>\<^sub>i\<^sub>n_iff[simp]
  unfolding propagate_unit_bt_wl_D_int_def isasat_bounded_assn_def
    PR_CONST_def
  unfolding fold_tuple_optimizations
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref


sepref_def propagate_bt_wl_D_fast_codeXX
  is \<open>uncurry2 propagate_bt_wl_D_heur\<close>
  :: \<open>[\<lambda>((L, C), S). isasat_fast S]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>

  supply [[goals_limit = 1]] append_ll_def[simp] isasat_fast_length_leD[dest]
    propagate_bt_wl_D_fast_code_isasat_fastI2[intro] length_ll_def[simp]
    propagate_bt_wl_D_fast_code_isasat_fastI3[intro]
  unfolding propagate_bt_wl_D_heur_alt_def
    isasat_bounded_assn_def
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    append_ll_def[symmetric] append_ll_def[symmetric]
    PR_CONST_def save_phase_def
  apply (rewrite in \<open>add_lbd (of_nat \<hole>) _\<close> annot_unat_unat_upcast[where 'l=64])
  apply (rewrite in \<open>(_ + \<hole>, _)\<close> unat_const_fold[where 'a=64])
  apply (rewrite at \<open>RETURN (_, _, _, _, _, _, \<hole>, _)\<close> unat_const_fold[where 'a=32])
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  unfolding fold_tuple_optimizations
  apply (rewrite in \<open>isasat_fast \<hole>\<close> fold_tuple_optimizations[symmetric])+
  by sepref

lemma extract_shorter_conflict_list_heur_st_alt_def:
    \<open>extract_shorter_conflict_list_heur_st = (\<lambda>(M, N, (bD), Q', W', vm, clvls, cach, lbd, outl,
       stats, ccont, vdom). do {
     let D =  the_lookup_conflict bD;
     ASSERT(fst M \<noteq> []);
     let K = lit_of_last_trail_pol M;
     ASSERT(0 < length outl);
     ASSERT(lookup_conflict_remove1_pre (-K, D));
     let D = lookup_conflict_remove1 (-K) D;
     let outl = outl[0 := -K];
     vm \<leftarrow> isa_vmtf_mark_to_rescore_also_reasons M N outl vm;
     (D, cach, outl) \<leftarrow> isa_minimize_and_extract_highest_lookup_conflict M N D cach lbd outl;
     ASSERT(empty_cach_ref_pre cach);
     let cach = empty_cach_ref cach;
     ASSERT(outl \<noteq> [] \<and> length outl \<le> uint32_max);
     (D, C, n) \<leftarrow> isa_empty_conflict_and_extract_clause_heur M D outl;
     RETURN ((M, N, D, Q', W', vm, clvls, cach, lbd, take 1 outl, stats, ccont, vdom), n, C)
  })\<close>
  unfolding extract_shorter_conflict_list_heur_st_def
  by (auto simp: the_lookup_conflict_def Let_def intro!: ext)

sepref_register isa_minimize_and_extract_highest_lookup_conflict
  empty_conflict_and_extract_clause_heur

sepref_def extract_shorter_conflict_list_heur_st_fast
  is \<open>extract_shorter_conflict_list_heur_st\<close>
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a
        isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn \<times>\<^sub>a uint32_nat_assn \<times>\<^sub>a clause_ll_assn\<close>
  supply [[goals_limit=1]] empty_conflict_and_extract_clause_pre_def[simp]
  unfolding extract_shorter_conflict_list_heur_st_alt_def PR_CONST_def isasat_bounded_assn_def
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    fold_tuple_optimizations
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref


sepref_register find_lit_of_max_level_wl
  extract_shorter_conflict_list_heur_st lit_of_hd_trail_st_heur propagate_bt_wl_D_heur
  propagate_unit_bt_wl_D_int
sepref_register backtrack_wl

sepref_def lit_of_hd_trail_st_heur_fast_code
  is \<open>lit_of_hd_trail_st_heur\<close>
  :: \<open>[\<lambda>S. True]\<^sub>a isasat_bounded_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  unfolding lit_of_hd_trail_st_heur_alt_def isasat_bounded_assn_def
  by sepref

sepref_register save_phase_st
sepref_def backtrack_wl_D_fast_code
  is \<open>backtrack_wl_D_nlit_heur\<close>
  :: \<open>[isasat_fast]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
    size_conflict_wl_def[simp] isasat_fast_length_leD[intro] isasat_fast_def[simp]
  unfolding backtrack_wl_D_nlit_heur_def PR_CONST_def
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    append_ll_def[symmetric]
    size_conflict_wl_def[symmetric]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

(* TODO: Move *)
lemmas [llvm_inline] = add_lbd_def

experiment
begin

  export_llvm
    empty_conflict_and_extract_clause_heur_fast_code
    empty_cach_code
    propagate_bt_wl_D_fast_codeXX
    propagate_unit_bt_wl_D_fast_code
    extract_shorter_conflict_list_heur_st_fast
    lit_of_hd_trail_st_heur_fast_code
    backtrack_wl_D_fast_code

end


end
