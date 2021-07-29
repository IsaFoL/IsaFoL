theory IsaSAT_Restart_Reduce_LLVM
  imports IsaSAT_Restart_Reduce IsaSAT_Setup_LLVM IsaSAT_VMTF_State_LLVM
begin

hide_fact (open) Sepref_Rules.frefI
no_notation Sepref_Rules.fref (\<open>[_]\<^sub>f\<^sub>d _ \<rightarrow> _\<close> [0,60,60] 60)
no_notation Sepref_Rules.freft (\<open>_ \<rightarrow>\<^sub>f\<^sub>d _\<close> [60,60] 60)
no_notation Sepref_Rules.freftnd (\<open>_ \<rightarrow>\<^sub>f _\<close> [60,60] 60)
no_notation Sepref_Rules.frefnd (\<open>[_]\<^sub>f _ \<rightarrow> _\<close> [0,60,60] 60)

sepref_def find_local_restart_target_level_fast_code
  is \<open>uncurry find_local_restart_target_level_int\<close>
  :: \<open>trail_pol_fast_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=1]] length_rev[simp del]
  unfolding find_local_restart_target_level_int_def find_local_restart_target_level_int_inv_def
    length_uint32_nat_def vmtf_remove_assn_def trail_pol_fast_assn_def
  apply (annot_unat_const \<open>TYPE(32)\<close>)
   apply (rewrite at \<open>stamp (\<hole>)\<close> annot_index_of_atm)
   apply (rewrite in \<open>(_ ! _)\<close> annot_unat_snat_upcast[where 'l=64])
   apply (rewrite in \<open>(_ ! \<hole>)\<close> annot_unat_snat_upcast[where 'l=64])
   apply (rewrite in \<open>(\<hole> < length _)\<close> annot_unat_snat_upcast[where 'l=64])
  by sepref


sepref_def find_local_restart_target_level_st_fast_code
  is \<open>find_local_restart_target_level_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=1]] length_rev[simp del]
  unfolding find_local_restart_target_level_st_alt_def isasat_bounded_assn_def PR_CONST_def
    fold_tuple_optimizations
  by sepref

sepref_def empty_Q_fast_code
  is \<open>empty_Q\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding empty_Q_def isasat_bounded_assn_def fold_tuple_optimizations
  by sepref

sepref_register cdcl_twl_local_restart_wl_D_heur
    empty_Q find_decomp_wl_st_int

sepref_def cdcl_twl_local_restart_wl_D_heur_fast_code
  is \<open>cdcl_twl_local_restart_wl_D_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding cdcl_twl_local_restart_wl_D_heur_def PR_CONST_def
    fold_tuple_optimizations
  supply [[goals_limit = 1]]
  by sepref

definition lbd_sort_clauses_raw :: \<open>arena \<Rightarrow> vdom \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list nres\<close> where
  \<open>lbd_sort_clauses_raw arena N = pslice_sort_spec idx_cdom clause_score_less arena N\<close>

definition lbd_sort_clauses_avdom :: \<open>arena \<Rightarrow> vdom \<Rightarrow> nat list nres\<close> where
  \<open>lbd_sort_clauses_avdom arena N = lbd_sort_clauses_raw arena N 0 (length N)\<close>

lemmas LBD_introsort[sepref_fr_rules] =
  LBD_it.introsort_param_impl_correct[unfolded lbd_sort_clauses_raw_def[symmetric] PR_CONST_def]

sepref_register lbd_sort_clauses_raw
sepref_def lbd_sort_clauses_avdom_impl
  is \<open>uncurry lbd_sort_clauses_avdom\<close>
  :: \<open>arena_fast_assn\<^sup>k *\<^sub>a vdom_fast_assn\<^sup>d \<rightarrow>\<^sub>a vdom_fast_assn\<close>
  supply[[goals_limit=1]]
  unfolding lbd_sort_clauses_avdom_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_register remove_deleted_clauses_from_avdom arena_status DELETED

sepref_def remove_deleted_clauses_from_avdom_fast_code
  is \<open>uncurry isa_remove_deleted_clauses_from_avdom\<close>
  :: \<open>[\<lambda>(N, vdom). length (get_avdom_aivdom vdom) \<le> sint64_max]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a aivdom_assn\<^sup>d \<rightarrow> aivdom_assn\<close>
  supply [[goals_limit=1]]
  supply [simp] = length_avdom_aivdom_def
  unfolding isa_remove_deleted_clauses_from_avdom_def
    convert_swap gen_swap if_conn(4) length_avdom_aivdom_def[symmetric]
    avdom_aivdom_at_def[symmetric]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref


definition lbd_sort_clauses :: \<open>arena \<Rightarrow> aivdom2 \<Rightarrow> aivdom2 nres\<close> where
  \<open>lbd_sort_clauses arena N = map_vdom_aivdom_int (lbd_sort_clauses_avdom arena) N\<close>

sepref_def lbd_sort_clauses_impl
  is \<open>uncurry lbd_sort_clauses\<close>
  :: \<open>[\<lambda>(N, vdom). length (fst vdom) \<le> sint64_max]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a aivdom_int_assn\<^sup>d \<rightarrow> aivdom_int_assn\<close>
  unfolding lbd_sort_clauses_def map_vdom_aivdom_int_def
  by sepref

lemma
  map_vdom_aivdom_int2:
  \<open>(uncurry (\<lambda>arena. map_vdom_aivdom_int (f arena)), uncurry (\<lambda>arena. map_vdom_aivdom (f arena)))
  \<in> Id \<times>\<^sub>r aivdom_rel \<rightarrow>\<^sub>f \<langle>aivdom_rel\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  subgoal for x y
    using map_vdom_aivdom_int[of \<open>f (fst x)\<close>]
    apply (cases x; cases y)
    apply (auto intro!: frefI nres_relI simp: fref_def nres_rel_def)
    done
  done

lemma get_aivdom_eq_aivdom_iff:
  \<open>IsaSAT_VDom.get_aivdom b = (x1, a, aa, ba) \<longleftrightarrow> b = AIvdom (x1, a, aa, ba)\<close>
  by (cases b) auto
lemma quicksort_clauses_by_score_sort:
  \<open>(uncurry lbd_sort_clauses, uncurry sort_clauses_by_score) \<in>
  Id \<times>\<^sub>r aivdom_rel \<rightarrow>\<^sub>f \<langle>aivdom_rel\<rangle>nres_rel\<close>
  apply (intro fun_relI nres_relI frefI)
  subgoal for arena arena'
    unfolding uncurry_def lbd_sort_clauses_def map_vdom_aivdom_int_def
      lbd_sort_clauses_avdom_def lbd_sort_clauses_raw_def sort_clauses_by_score_def
    apply (refine_vcg)
    apply (rule specify_left)
    apply (auto simp: lbd_sort_clauses_def lbd_sort_clauses_raw_def
      pslice_sort_spec_def le_ASSERT_iff idx_cdom_def slice_rel_def br_def uncurry_def
      conc_fun_RES sort_spec_def map_vdom_aivdom_int_def lbd_sort_clauses_avdom_def
      code_hider_rel_def
      split:prod.splits
      intro!: ASSERT_leI 
      )
    apply (case_tac x2; auto)

    apply (rule order_trans)
    apply (rule slice_sort_spec_refine_sort)
    apply (auto simp: lbd_sort_clauses_def lbd_sort_clauses_raw_def
      pslice_sort_spec_def le_ASSERT_iff idx_cdom_def slice_rel_def br_def uncurry_def
      conc_fun_RES sort_spec_def map_vdom_aivdom_int_def lbd_sort_clauses_avdom_def
      code_hider_rel_def
      split:prod.splits
      intro!: ASSERT_leI 
      )
    apply (case_tac x2; auto simp: get_aivdom_eq_aivdom_iff)
    apply (rule_tac x = \<open>AIvdom (x1a, x, ad, bb)\<close> in exI)
    apply auto
    by (metis slice_complete)
  done

context
  notes [fcomp_norm_unfold] = aivdom_assn_alt_def[symmetric] aivdom_assn_def[symmetric]
begin

lemma lbd_sort_clauses_impl_lbd_sort_clauses[sepref_fr_rules]:
  \<open>(uncurry lbd_sort_clauses_impl, uncurry sort_clauses_by_score)
  \<in> [\<lambda>(N, vdom). length (get_avdom_aivdom vdom) \<le> sint64_max]\<^sub>a (al_assn arena_el_impl_assn)\<^sup>k *\<^sub>a aivdom_assn\<^sup>d \<rightarrow> aivdom_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
\<in> [comp_PRE (Id \<times>\<^sub>f aivdom_rel) (\<lambda>_. True) (\<lambda>x y. case y of (N, vdom) \<Rightarrow> length (fst vdom) \<le> sint64_max)
   (\<lambda>x. nofail (uncurry sort_clauses_by_score x))]\<^sub>a ?im \<rightarrow> ?f\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> _\<close>)
    using hfref_compI_PRE[OF lbd_sort_clauses_impl.refine,
  OF quicksort_clauses_by_score_sort[unfolded convert_fref], unfolded fcomp_norm_unfold] by blast
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that 
    by (case_tac x, case_tac \<open>snd x\<close>)
      (auto simp: comp_PRE_def code_hider_rel_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H apply assumption
    using pre ..
qed

end

sepref_def sort_vdom_heur_fast_code
  is \<open>sort_vdom_heur\<close>
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>aisasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply sort_clauses_by_score_invI[intro]
    [[goals_limit=1]]
  unfolding sort_vdom_heur_def isasat_bounded_assn_def
  by sepref


experiment
begin
  export_llvm sort_vdom_heur_fast_code remove_deleted_clauses_from_avdom_fast_code
end

end