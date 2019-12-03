theory IsaSAT_Sorting
  imports IsaSAT_Setup IsaSAT_Setup_LLVM
    Isabelle_LLVM.Sorting_Introsort
begin

definition clause_score_ordering where
  \<open>clause_score_ordering = (\<lambda>(lbd, act) (lbd', act'). lbd < lbd' \<or> (lbd = lbd' \<and> act < act'))\<close>

definition (in -) clause_score_extract :: \<open>arena \<Rightarrow> nat \<Rightarrow> nat \<times> nat\<close> where
  \<open>clause_score_extract arena C = (
     if arena_status arena C = DELETED
     then (uint32_max, 0) \<comment> \<open>deleted elements are the
        largest possible\<close>
     else
       let lbd = arena_lbd arena C in
       let act = arena_act arena C in
       (lbd, act)
  )\<close>

definition valid_sort_clause_score_pre_at where
  \<open>valid_sort_clause_score_pre_at arena C \<longleftrightarrow>
    (\<exists>i vdom. C = vdom ! i \<and> arena_is_valid_clause_vdom arena (vdom!i) \<and>
          (arena_status arena (vdom!i) \<noteq> DELETED \<longrightarrow>
             (get_clause_LBD_pre arena (vdom!i) \<and> arena_act_pre arena (vdom!i)))
          \<and> i < length vdom)\<close>

definition (in -)valid_sort_clause_score_pre where
  \<open>valid_sort_clause_score_pre arena vdom \<longleftrightarrow>
    (\<forall>C \<in> set vdom. arena_is_valid_clause_vdom arena C \<and>
        (arena_status arena C \<noteq> DELETED \<longrightarrow>
             (get_clause_LBD_pre arena C \<and> arena_act_pre arena C)))\<close>


definition clause_score_less :: "arena \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "clause_score_less arena i j \<longleftrightarrow>
     clause_score_ordering (clause_score_extract arena i) (clause_score_extract arena j)"

definition idx_cdom :: "arena \<Rightarrow> nat set" where
 "idx_cdom arena \<equiv> {i. valid_sort_clause_score_pre_at arena i}"

definition mop_clause_score_less where
  \<open>mop_clause_score_less arena i j = do {
    ASSERT(valid_sort_clause_score_pre_at arena i);
    ASSERT(valid_sort_clause_score_pre_at arena j);
    RETURN (clause_score_ordering (clause_score_extract arena i) (clause_score_extract arena j))
  }\<close>

sepref_register clause_score_extract

sepref_def (in -) clause_score_extract_code
  is \<open>uncurry (RETURN oo clause_score_extract)\<close>
  :: \<open>[uncurry valid_sort_clause_score_pre_at]\<^sub>a
      arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn *a uint32_nat_assn\<close>
  supply [[goals_limit = 1]]
  unfolding clause_score_extract_def valid_sort_clause_score_pre_at_def
  apply (annot_unat_const "TYPE(32)")
  by sepref

sepref_def (in -) clause_score_ordering_code
  is \<open>uncurry (RETURN oo clause_score_ordering)\<close>
  :: \<open>(uint32_nat_assn *a uint32_nat_assn)\<^sup>k *\<^sub>a (uint32_nat_assn *a uint32_nat_assn)\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  supply [[goals_limit = 1]]
  unfolding clause_score_ordering_def
  by sepref

sepref_register mop_clause_score_less clause_score_less clause_score_ordering
sepref_def mop_clause_score_less_impl
  is \<open>uncurry2 mop_clause_score_less\<close>
  :: \<open>arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding mop_clause_score_less_def
  by sepref


interpretation LBD: weak_ordering_on_lt where
  C = "idx_cdom vs" and
  less = "clause_score_less vs"
  by unfold_locales
   (auto simp: clause_score_less_def clause_score_extract_def
      clause_score_ordering_def split: if_splits)

interpretation LBD: parameterized_weak_ordering idx_cdom clause_score_less
    mop_clause_score_less
  by unfold_locales
   (auto simp: mop_clause_score_less_def
     idx_cdom_def clause_score_less_def)


locale pure_eo_adapter =
  fixes elem_assn :: "'a \<Rightarrow> 'ai::llvm_rep \<Rightarrow> assn"
    and wo_assn :: "'a list \<Rightarrow> 'oi::llvm_rep \<Rightarrow> assn"
    and wo_get_impl :: "'oi \<Rightarrow> 'size::len2 word \<Rightarrow> 'ai llM"
    and wo_set_impl :: "'oi \<Rightarrow> 'size::len2 word \<Rightarrow> 'ai \<Rightarrow> 'oi llM"
  assumes pure[safe_constraint_rules]: "is_pure elem_assn"
      and get_hnr: "(uncurry wo_get_impl,uncurry mop_list_get) \<in> wo_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a elem_assn"
      and set_hnr: "(uncurry2 wo_set_impl,uncurry2 mop_list_set) \<in> wo_assn\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a elem_assn\<^sup>k \<rightarrow>\<^sub>a\<^sub>d (\<lambda>_ ((ai,_),_). cnc_assn (\<lambda>x. x=ai) wo_assn)"
begin

  lemmas [sepref_fr_rules] = get_hnr set_hnr


  definition "only_some_rel \<equiv> {(a, Some a) | a. True} \<union> {(x, None) | x. True}"

  definition "eo_assn \<equiv> hr_comp wo_assn (\<langle>only_some_rel\<rangle>list_rel)"

  definition "eo_extract1 p i \<equiv> doN { r \<leftarrow> mop_list_get p i; RETURN (r,p) }"
  sepref_definition eo_extract_impl is "uncurry eo_extract1"
    :: "wo_assn\<^sup>d *\<^sub>a (snat_assn' TYPE('size))\<^sup>k \<rightarrow>\<^sub>a elem_assn \<times>\<^sub>a wo_assn"
    unfolding eo_extract1_def
    by sepref

  lemma mop_eo_extract_aux: "mop_eo_extract p i = doN { r \<leftarrow> mop_list_get p i; ASSERT (r\<noteq>None \<and> i<length p); RETURN (the r, p[i:=None]) }"
    by (auto simp: pw_eq_iff refine_pw_simps)

  lemma assign_none_only_some_list_rel:
    assumes SR[param]: "(a, a') \<in> \<langle>only_some_rel\<rangle>list_rel" and L: "i < length a'"
      shows "(a, a'[i := None]) \<in> \<langle>only_some_rel\<rangle>list_rel"
  proof -
    have "(a[i := a!i], a'[i := None]) \<in> \<langle>only_some_rel\<rangle>list_rel"
      apply (parametricity)
      by (auto simp: only_some_rel_def)
    also from L list_rel_imp_same_length[OF SR] have "a[i := a!i] = a" by auto
    finally show ?thesis .
  qed


  lemma eo_extract1_refine: "(eo_extract1, mop_eo_extract) \<in> \<langle>only_some_rel\<rangle>list_rel \<rightarrow> nat_rel \<rightarrow> \<langle>Id \<times>\<^sub>r \<langle>only_some_rel\<rangle>list_rel\<rangle>nres_rel"
    unfolding eo_extract1_def mop_eo_extract_aux
    supply R = mop_list_get.fref[THEN frefD, OF TrueI prod_relI, unfolded uncurry_apply, THEN nres_relD]
    apply (refine_rcg R)
    apply assumption
    apply (clarsimp simp: assign_none_only_some_list_rel)
    by (auto simp: only_some_rel_def)

  lemma eo_list_set_refine: "(mop_list_set, mop_eo_set) \<in> \<langle>only_some_rel\<rangle>list_rel \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>\<langle>only_some_rel\<rangle>list_rel\<rangle>nres_rel"
    unfolding mop_list_set_alt mop_eo_set_alt
    apply refine_rcg
    apply (simp add: list_rel_imp_same_length)
    apply simp
    apply parametricity
    apply (auto simp: only_some_rel_def)
    done


  lemma set_hnr': "(uncurry2 wo_set_impl,uncurry2 mop_list_set) \<in> wo_assn\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a elem_assn\<^sup>k \<rightarrow>\<^sub>a wo_assn"
    apply (rule hfref_cons[OF set_hnr])
    apply (auto simp: cnc_assn_def entails_lift_extract_simps sep_algebra_simps)
    done



  context
    notes [fcomp_norm_unfold] = eo_assn_def[symmetric]
  begin
    lemmas eo_extract_refine_aux = eo_extract_impl.refine[FCOMP eo_extract1_refine]

    lemma eo_extract_refine: "(uncurry eo_extract_impl, uncurry mop_eo_extract) \<in> eo_assn\<^sup>d *\<^sub>a snat_assn\<^sup>k
      \<rightarrow>\<^sub>a\<^sub>d (\<lambda>_ (ai,_). elem_assn \<times>\<^sub>a cnc_assn (\<lambda>x. x=ai) eo_assn)"
      apply (sepref_to_hnr)
      apply (rule hn_refine_nofailI)
      unfolding cnc_assn_prod_conv
      apply (rule hnr_ceq_assnI)
      subgoal
        supply R = eo_extract_refine_aux[to_hnr, unfolded APP_def]
        apply (rule hn_refine_cons[OF _ R])
        apply (auto simp: sep_algebra_simps entails_lift_extract_simps hn_ctxt_def pure_def invalid_assn_def)
        done
      subgoal
        unfolding eo_extract_impl_def mop_eo_extract_def hn_ctxt_def eo_assn_def hr_comp_def
        supply R = get_hnr[to_hnr, THEN hn_refineD, unfolded APP_def hn_ctxt_def]
        thm R
        supply [vcg_rules] = R
        supply [simp] = refine_pw_simps list_rel_imp_same_length
        apply (vcg)
        done
      done


    lemmas eo_set_refine_aux = set_hnr'[FCOMP eo_list_set_refine]

    lemma pure_part_cnc_imp_eq: "pure_part (cnc_assn (\<lambda>x. x = cc) wo_assn a c) \<Longrightarrow> c=cc"
      by (auto simp: pure_part_def cnc_assn_def pred_lift_extract_simps)

    (* TODO: Move *)
    lemma pure_entails_empty: "is_pure A \<Longrightarrow> A a c \<turnstile> \<box>"
      by (auto simp: is_pure_def sep_algebra_simps entails_lift_extract_simps)


    lemma eo_set_refine: "(uncurry2 wo_set_impl, uncurry2 mop_eo_set) \<in> eo_assn\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a elem_assn\<^sup>d \<rightarrow>\<^sub>a\<^sub>d (\<lambda>_ ((ai, _), _). cnc_assn (\<lambda>x. x = ai) eo_assn)"
      apply (sepref_to_hnr)
      apply (rule hn_refine_nofailI)
      apply (rule hnr_ceq_assnI)
      subgoal
        supply R = eo_set_refine_aux[to_hnr, unfolded APP_def]
        apply (rule hn_refine_cons[OF _ R])
        apply (auto simp: sep_algebra_simps entails_lift_extract_simps hn_ctxt_def pure_def invalid_assn_def pure_entails_empty[OF pure])
        done
      subgoal
        unfolding hn_ctxt_def eo_assn_def hr_comp_def
        supply R = set_hnr[to_hnr, THEN hn_refineD, unfolded APP_def hn_ctxt_def]
        supply [vcg_rules] = R
        supply [simp] = refine_pw_simps list_rel_imp_same_length pure_part_cnc_imp_eq
        apply (vcg')
        done
      done

  end
  thm mop_eo_extract_def


  find_theorems mop_eo_set mop_list_set

  thm mop_eo_set_alt

  lemma id_Some_only_some_rel: "(id, Some) \<in> Id \<rightarrow> only_some_rel"
    by (auto simp: only_some_rel_def)

  lemma map_some_only_some_rel_iff: "(xs, map Some ys) \<in> \<langle>only_some_rel\<rangle>list_rel \<longleftrightarrow> xs=ys"
    apply (rule iffI)
    subgoal
      apply (induction xs "map Some ys" arbitrary: ys rule: list_rel_induct)
      apply (auto simp: only_some_rel_def)
      done
    subgoal
      apply (rewrite in "(\<hole>,_)" list.map_id[symmetric])
      apply (parametricity add: id_Some_only_some_rel)
      by simp
    done


  lemma wo_assn_conv: "wo_assn xs ys = eo_assn (map Some xs) ys"
    unfolding eo_assn_def hr_comp_def
    by (auto simp: pred_lift_extract_simps sep_algebra_simps fun_eq_iff map_some_only_some_rel_iff)

  lemma to_eo_conv_refine: "(return, mop_to_eo_conv) \<in> wo_assn\<^sup>d \<rightarrow>\<^sub>a\<^sub>d (\<lambda>_ ai. cnc_assn (\<lambda>x. x = ai) eo_assn)"
    unfolding mop_to_eo_conv_def cnc_assn_def
    apply sepref_to_hoare
    apply (rewrite wo_assn_conv)
    apply vcg
    done

  lemma "None \<notin> set xs \<longleftrightarrow> (\<exists>ys. xs = map Some ys)"
    using None_not_in_set_conv by auto

  lemma to_wo_conv_refine: "(return, mop_to_wo_conv) \<in> eo_assn\<^sup>d \<rightarrow>\<^sub>a\<^sub>d (\<lambda>_ ai. cnc_assn (\<lambda>x. x = ai) wo_assn)"
    unfolding mop_to_wo_conv_def cnc_assn_def eo_assn_def hr_comp_def
    apply sepref_to_hoare
    apply (auto simp add: refine_pw_simps map_some_only_some_rel_iff elim!: None_not_in_set_conv)
    by vcg

  lemma random_access_iterator: "random_access_iterator wo_assn eo_assn elem_assn
    return return
    eo_extract_impl
    wo_set_impl"
    apply unfold_locales
    using to_eo_conv_refine to_wo_conv_refine eo_extract_refine eo_set_refine
    apply blast+
    done

  sublocale random_access_iterator wo_assn eo_assn elem_assn
    return return
    eo_extract_impl
    wo_set_impl
    by (rule random_access_iterator)


  find_theorems "?a = UNPROTECT ?a"

end



global_interpretation LBD: parameterized_sort_impl_context
  "woarray_assn snat_assn" "eoarray_assn snat_assn" snat_assn
  return return
  eo_extract_impl
  array_upd
  idx_cdom clause_score_less mop_clause_score_less mop_clause_score_less_impl
  "arena_fast_assn"
  defines
          LBD_is_guarded_insert_impl = LBD.is_guarded_param_insert_impl
      and LBD_is_unguarded_insert_impl = LBD.is_unguarded_param_insert_impl
      and LBD_unguarded_insertion_sort_impl = LBD.unguarded_insertion_sort_param_impl
      and LBD_guarded_insertion_sort_impl = LBD.guarded_insertion_sort_param_impl
      and LBD_final_insertion_sort_impl = LBD.final_insertion_sort_param_impl
      (*and LBD_mop_lchild_impl  = LBD.mop_lchild_impl
      and LBD_mop_rchild_impl  = LBD.mop_rchild_impl
      and LBD_has_rchild_impl  = LBD.has_rchild_impl
      and LBD_has_lchild_impl  = LBD.has_lchild_impl *)

      and LBD_pcmpo_idxs_impl  = LBD.pcmpo_idxs_impl
      and LBD_pcmpo_v_idx_impl  = LBD.pcmpo_v_idx_impl
      and LBD_pcmpo_idx_v_impl  = LBD.pcmpo_idx_v_impl
      and LBD_pcmp_idxs_impl  = LBD.pcmp_idxs_impl

      and LBD_mop_geth_impl    = LBD.mop_geth_impl
      and LBD_mop_seth_impl    = LBD.mop_seth_impl
      and LBD_sift_down_impl   = LBD.sift_down_impl
      and LBD_heapify_btu_impl = LBD.heapify_btu_impl
      and LBD_heapsort_impl    = LBD.heapsort_param_impl
      and LBD_qsp_next_l_impl       = LBD.qsp_next_l_impl
      and LBD_qsp_next_h_impl       = LBD.qsp_next_h_impl
      and LBD_qs_partition_impl     = LBD.qs_partition_impl
(*      and LBD_qs_partitionXXX_impl     = LBD.qs_partitionXXX_impl *)
      and LBD_partition_pivot_impl  = LBD.partition_pivot_impl
      and LBD_introsort_aux_impl = LBD.introsort_aux_param_impl
      and LBD_introsort_impl        = LBD.introsort_param_impl
      and LBD_move_median_to_first_impl = LBD.move_median_to_first_param_impl

  apply unfold_locales
  apply (rule eo_hnr_dep)+
  unfolding GEN_ALGO_def refines_param_relp_def (* TODO: thm gen_refines_param_relpI *)
  by (rule mop_clause_score_less_impl.refine)



lemma al_pure_eo: "is_pure A \<Longrightarrow> pure_eo_adapter A (al_assn A) arl_nth arl_upd"
  apply unfold_locales
  apply assumption
  apply (rule al_nth_hnr_mop; simp)
  subgoal
    apply (sepref_to_hnr)
    apply (rule hn_refine_nofailI)
    apply (rule hnr_ceq_assnI)
    subgoal
      supply R = al_upd_hnr_mop[to_hnr, unfolded APP_def, of A]
      apply (rule hn_refine_cons[OF _ R])
      apply (auto simp: hn_ctxt_def pure_def invalid_assn_def sep_algebra_simps entails_lift_extract_simps)
      done
    subgoal
      unfolding hn_ctxt_def al_assn_def hr_comp_def pure_def in_snat_rel_conv_assn
      apply (erule is_pureE)
      apply (simp add: refine_pw_simps)
      supply [simp] = list_rel_imp_same_length
      by vcg
    done
  done


global_interpretation
  LBD_it: pure_eo_adapter sint64_nat_assn vdom_fast_assn arl_nth arl_upd
  defines LBD_it_eo_extract_impl = LBD_it.eo_extract_impl
  apply (rule al_pure_eo)
  by simp



global_interpretation LBD_it: parameterized_sort_impl_context
  vdom_fast_assn "LBD_it.eo_assn" sint64_nat_assn
  return return
  LBD_it_eo_extract_impl
  arl_upd
  idx_cdom clause_score_less mop_clause_score_less mop_clause_score_less_impl
  "arena_fast_assn"
  defines
          LBD_it_is_guarded_insert_impl = LBD_it.is_guarded_param_insert_impl
      and LBD_it_is_unguarded_insert_impl = LBD_it.is_unguarded_param_insert_impl
      and LBD_it_unguarded_insertion_sort_impl = LBD_it.unguarded_insertion_sort_param_impl
      and LBD_it_guarded_insertion_sort_impl = LBD_it.guarded_insertion_sort_param_impl
      and LBD_it_final_insertion_sort_impl = LBD_it.final_insertion_sort_param_impl
      (*and LBD_it_mop_lchild_impl  = LBD_it.mop_lchild_impl
      and LBD_it_mop_rchild_impl  = LBD_it.mop_rchild_impl
      and LBD_it_has_rchild_impl  = LBD_it.has_rchild_impl
      and LBD_it_has_lchild_impl  = LBD_it.has_lchild_impl *)

      and LBD_it_pcmpo_idxs_impl  = LBD_it.pcmpo_idxs_impl
      and LBD_it_pcmpo_v_idx_impl  = LBD_it.pcmpo_v_idx_impl
      and LBD_it_pcmpo_idx_v_impl  = LBD_it.pcmpo_idx_v_impl
      and LBD_it_pcmp_idxs_impl  = LBD_it.pcmp_idxs_impl

      and LBD_it_mop_geth_impl    = LBD_it.mop_geth_impl
      and LBD_it_mop_seth_impl    = LBD_it.mop_seth_impl
      and LBD_it_sift_down_impl   = LBD_it.sift_down_impl
      and LBD_it_heapify_btu_impl = LBD_it.heapify_btu_impl
      and LBD_it_heapsort_impl    = LBD_it.heapsort_param_impl
      and LBD_it_qsp_next_l_impl       = LBD_it.qsp_next_l_impl
      and LBD_it_qsp_next_h_impl       = LBD_it.qsp_next_h_impl
      and LBD_it_qs_partition_impl     = LBD_it.qs_partition_impl
(*      and LBD_it_qs_partitionXXX_impl     = LBD_it.qs_partitionXXX_impl *)
      and LBD_it_partition_pivot_impl  = LBD_it.partition_pivot_impl
      and LBD_it_introsort_aux_impl = LBD_it.introsort_aux_param_impl
      and LBD_it_introsort_impl        = LBD_it.introsort_param_impl
      and LBD_it_move_median_to_first_impl = LBD_it.move_median_to_first_param_impl

  apply unfold_locales
  unfolding GEN_ALGO_def refines_param_relp_def (* TODO: thm gen_refines_param_relpI *)
  apply (rule mop_clause_score_less_impl.refine)
  done



lemmas [llvm_inline] = LBD_it.eo_extract_impl_def[THEN meta_fun_cong, THEN meta_fun_cong]

print_named_simpset llvm_inline
export_llvm
  "LBD_heapsort_impl :: _ \<Rightarrow> _ \<Rightarrow> _"
  "LBD_introsort_impl :: _ \<Rightarrow> _ \<Rightarrow> _"


end