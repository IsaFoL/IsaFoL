theory IsaSAT_VMTF_LLVM
imports Watched_Literals.WB_Sort IsaSAT_VMTF IsaSAT_Setup_LLVM
   Isabelle_LLVM.Sorting_Introsort
   IsaSAT_Sorting_LLVM
begin

(* TODO: Mathias! Only import the refinement stuff over a single point,
  and at this point, do all necessary adaptations.
  
  Currently, this point is Refine_Monadic_Thin

*)
(*declare is_None_def[simp del] *)


(*
lemma VMTF_Node_ref[sepref_fr_rules]:
  \<open>(uncurry2 (return ooo VMTF_Node), uncurry2 (RETURN ooo VMTF_Node)) \<in>
    uint64_nat_assn\<^sup>k *\<^sub>a (option_assn uint32_nat_assn)\<^sup>k *\<^sub>a (option_assn uint32_nat_assn)\<^sup>k \<rightarrow>\<^sub>a
    vmtf_node_assn\<close>
  by sepref_to_hoare
   (sep_auto simp: vmtf_node_rel_def uint32_nat_rel_def br_def option_assn_alt_def
     split: option.splits)

lemma stamp_ref[sepref_fr_rules]:
  \<open>(return o stamp, RETURN o stamp) \<in> vmtf_node_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare
    (auto simp: ex_assn_move_out(2)[symmetric] return_cons_rule ent_ex_up_swap vmtf_node_rel_def
      simp del: ex_assn_move_out)

lemma get_next_ref[sepref_fr_rules]:
  \<open>(return o get_next, RETURN o get_next) \<in> vmtf_node_assn\<^sup>k \<rightarrow>\<^sub>a
   option_assn uint32_nat_assn\<close>
  unfolding option_assn_pure_conv
  by sepref_to_hoare (sep_auto simp: return_cons_rule vmtf_node_rel_def)

lemma get_prev_ref[sepref_fr_rules]:
  \<open>(return o get_prev, RETURN o get_prev) \<in> vmtf_node_assn\<^sup>k \<rightarrow>\<^sub>a
   option_assn uint32_nat_assn\<close>
  unfolding option_assn_pure_conv
  by sepref_to_hoare (sep_auto simp: return_cons_rule vmtf_node_rel_def)
*)



no_notation WB_More_Refinement.fref ("[_]\<^sub>f _ \<rightarrow> _" [0,60,60] 60)
no_notation WB_More_Refinement.freft ("_ \<rightarrow>\<^sub>f _" [60,60] 60)
declare \<alpha>_butlast[simp del]

definition idx_cdom :: "nat_vmtf_node list \<Rightarrow> nat set" where
 "idx_cdom xs \<equiv> {i. i < length xs}"

definition VMTF_score_less where
  \<open>VMTF_score_less xs i j \<longleftrightarrow> stamp (xs ! i) < stamp (xs ! j)\<close>
  
definition mop_VMTF_score_less where
  \<open>mop_VMTF_score_less xs i j = do {
    ASSERT(i < length xs);
    ASSERT(j < length xs);
    RETURN (stamp (xs ! i) < stamp (xs ! j))
  }\<close>

sepref_register VMTF_score_less

sepref_def (in -) mop_VMTF_score_less_impl
  is \<open>uncurry2 (mop_VMTF_score_less)\<close>
  :: \<open>(array_assn vmtf_node_assn)\<^sup>k *\<^sub>a atom_assn\<^sup>k *\<^sub>a atom_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  supply [[goals_limit = 1]]
  unfolding mop_VMTF_score_less_def
  apply (rewrite at \<open>stamp (_ ! \<hole>)\<close> value_of_atm_def[symmetric])
  apply (rewrite at \<open>stamp (_ ! \<hole>)\<close> in \<open>_ < \<hole>\<close> value_of_atm_def[symmetric])
  unfolding index_of_atm_def[symmetric]
  by sepref


interpretation VMTF: weak_ordering_on_lt where
  C = "idx_cdom vs" and
  less = "VMTF_score_less vs"
  by unfold_locales
   (auto simp: VMTF_score_less_def split: if_splits)

interpretation VMTF: parameterized_weak_ordering idx_cdom VMTF_score_less
    mop_VMTF_score_less
  by unfold_locales
   (auto simp: mop_VMTF_score_less_def
     idx_cdom_def VMTF_score_less_def)


global_interpretation VMTF: parameterized_sort_impl_context
  "woarray_assn atom_assn" "eoarray_assn atom_assn" atom_assn
  return return
  eo_extract_impl
  array_upd
  idx_cdom VMTF_score_less mop_VMTF_score_less mop_VMTF_score_less_impl
  "array_assn vmtf_node_assn"
  defines
          VMTF_is_guarded_insert_impl = VMTF.is_guarded_param_insert_impl
      and VMTF_is_unguarded_insert_impl = VMTF.is_unguarded_param_insert_impl
      and VMTF_unguarded_insertion_sort_impl = VMTF.unguarded_insertion_sort_param_impl
      and VMTF_guarded_insertion_sort_impl = VMTF.guarded_insertion_sort_param_impl
      and VMTF_final_insertion_sort_impl = VMTF.final_insertion_sort_param_impl
      (*and VMTF_mop_lchild_impl  = VMTF.mop_lchild_impl
      and VMTF_mop_rchild_impl  = VMTF.mop_rchild_impl
      and VMTF_has_rchild_impl  = VMTF.has_rchild_impl
      and VMTF_has_lchild_impl  = VMTF.has_lchild_impl *)

      and VMTF_pcmpo_idxs_impl  = VMTF.pcmpo_idxs_impl
      and VMTF_pcmpo_v_idx_impl  = VMTF.pcmpo_v_idx_impl
      and VMTF_pcmpo_idx_v_impl  = VMTF.pcmpo_idx_v_impl
      and VMTF_pcmp_idxs_impl  = VMTF.pcmp_idxs_impl

      and VMTF_mop_geth_impl    = VMTF.mop_geth_impl
      and VMTF_mop_seth_impl    = VMTF.mop_seth_impl
      and VMTF_sift_down_impl   = VMTF.sift_down_impl
      and VMTF_heapify_btu_impl = VMTF.heapify_btu_impl
      and VMTF_heapsort_impl    = VMTF.heapsort_param_impl
      and VMTF_qsp_next_l_impl       = VMTF.qsp_next_l_impl
      and VMTF_qsp_next_h_impl       = VMTF.qsp_next_h_impl
      and VMTF_qs_partition_impl     = VMTF.qs_partition_impl
(*      and VMTF_qs_partitionXXX_impl     = VMTF.qs_partitionXXX_impl *)
      and VMTF_partition_pivot_impl  = VMTF.partition_pivot_impl
      and VMTF_introsort_aux_impl = VMTF.introsort_aux_param_impl
      and VMTF_introsort_impl        = VMTF.introsort_param_impl
      and VMTF_move_median_to_first_impl = VMTF.move_median_to_first_param_impl

  apply unfold_locales
  apply (rule eo_hnr_dep)+
  unfolding GEN_ALGO_def refines_param_relp_def (* TODO: thm gen_refines_param_relpI *)
  supply[[unify_trace_failure]]
  by (rule mop_VMTF_score_less_impl.refine)


 
global_interpretation
  VMTF_it: pure_eo_adapter atom_assn "arl64_assn atom_assn" arl_nth arl_upd
  defines VMTF_it_eo_extract_impl = VMTF_it.eo_extract_impl
  apply (rule al_pure_eo)
  by (simp add: safe_constraint_rules)



global_interpretation VMTF_it: parameterized_sort_impl_context
  where
    wo_assn = \<open>arl64_assn atom_assn\<close>
    and eo_assn = VMTF_it.eo_assn
    and elem_assn = atom_assn
    and to_eo_impl = return
    and to_wo_impl = return
    and extract_impl = VMTF_it_eo_extract_impl
    and set_impl = arl_upd
    and cdom = idx_cdom
    and pless = VMTF_score_less
    and pcmp = mop_VMTF_score_less
    and pcmp_impl = mop_VMTF_score_less_impl
    and cparam_assn = \<open>array_assn vmtf_node_assn\<close>
  defines
          VMTF_it_is_guarded_insert_impl = VMTF_it.is_guarded_param_insert_impl
      and VMTF_it_is_unguarded_insert_impl = VMTF_it.is_unguarded_param_insert_impl
      and VMTF_it_unguarded_insertion_sort_impl = VMTF_it.unguarded_insertion_sort_param_impl
      and VMTF_it_guarded_insertion_sort_impl = VMTF_it.guarded_insertion_sort_param_impl
      and VMTF_it_final_insertion_sort_impl = VMTF_it.final_insertion_sort_param_impl
      (*and VMTF_it_mop_lchild_impl  = VMTF_it.mop_lchild_impl
      and VMTF_it_mop_rchild_impl  = VMTF_it.mop_rchild_impl
      and VMTF_it_has_rchild_impl  = VMTF_it.has_rchild_impl
      and VMTF_it_has_lchild_impl  = VMTF_it.has_lchild_impl *)

      and VMTF_it_pcmpo_idxs_impl  = VMTF_it.pcmpo_idxs_impl
      and VMTF_it_pcmpo_v_idx_impl  = VMTF_it.pcmpo_v_idx_impl
      and VMTF_it_pcmpo_idx_v_impl  = VMTF_it.pcmpo_idx_v_impl
      and VMTF_it_pcmp_idxs_impl  = VMTF_it.pcmp_idxs_impl

      and VMTF_it_mop_geth_impl    = VMTF_it.mop_geth_impl
      and VMTF_it_mop_seth_impl    = VMTF_it.mop_seth_impl
      and VMTF_it_sift_down_impl   = VMTF_it.sift_down_impl
      and VMTF_it_heapify_btu_impl = VMTF_it.heapify_btu_impl
      and VMTF_it_heapsort_impl    = VMTF_it.heapsort_param_impl
      and VMTF_it_qsp_next_l_impl       = VMTF_it.qsp_next_l_impl
      and VMTF_it_qsp_next_h_impl       = VMTF_it.qsp_next_h_impl
      and VMTF_it_qs_partition_impl     = VMTF_it.qs_partition_impl
(*      and VMTF_it_qs_partitionXXX_impl     = VMTF_it.qs_partitionXXX_impl *)
      and VMTF_it_partition_pivot_impl  = VMTF_it.partition_pivot_impl
      and VMTF_it_introsort_aux_impl = VMTF_it.introsort_aux_param_impl
      and VMTF_it_introsort_impl        = VMTF_it.introsort_param_impl
      and VMTF_it_move_median_to_first_impl = VMTF_it.move_median_to_first_param_impl

  apply unfold_locales
  unfolding GEN_ALGO_def refines_param_relp_def (* TODO: thm gen_refines_param_relpI *)
  apply (rule mop_VMTF_score_less_impl.refine)
  done


lemmas [llvm_inline] = VMTF_it.eo_extract_impl_def[THEN meta_fun_cong, THEN meta_fun_cong]

print_named_simpset llvm_inline
export_llvm
  "VMTF_heapsort_impl :: _ \<Rightarrow> _ \<Rightarrow> _"
  "VMTF_introsort_impl :: _ \<Rightarrow> _ \<Rightarrow> _"

definition VMTF_sort_scores_raw :: \<open>_\<close> where
  \<open>VMTF_sort_scores_raw = pslice_sort_spec idx_cdom VMTF_score_less\<close>

definition VMTF_sort_scores :: \<open>_\<close> where
  \<open>VMTF_sort_scores xs ys = VMTF_sort_scores_raw xs ys 0 (length ys)\<close>

lemmas VMTF_introsort[sepref_fr_rules] =
  VMTF_it.introsort_param_impl_correct[unfolded VMTF_sort_scores_raw_def[symmetric] PR_CONST_def]

sepref_register VMTF_sort_scores_raw vmtf_reorder_list_raw

lemma VMTF_sort_scores_vmtf_reorder_list_raw:
  \<open>(VMTF_sort_scores, vmtf_reorder_list_raw) \<in> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  unfolding VMTF_sort_scores_def VMTF_sort_scores_raw_def pslice_sort_spec_def
    vmtf_reorder_list_raw_def
  apply (refine_rcg)
  subgoal by (auto simp: idx_cdom_def)
  subgoal for vm vm' arr arr'
    by (auto intro!: slice_sort_spec_refine_sort[THEN order_trans, of _ arr' arr']
    simp: idx_cdom_def slice_rel_def br_def reorder_list_def conc_fun_RES sort_spec_def
      eq_commute[of \<open>length _\<close> \<open>length arr'\<close>])
  done

sepref_def VMTF_sort_scores_raw_impl
  is \<open>uncurry VMTF_sort_scores\<close>
  :: \<open>(IICF_Array.array_assn vmtf_node_assn)\<^sup>k *\<^sub>a VMTF_it.arr_assn\<^sup>d \<rightarrow>\<^sub>a VMTF_it.arr_assn\<close>
  unfolding VMTF_sort_scores_def
  apply (annot_snat_const "TYPE(64)")
  by sepref

lemmas[sepref_fr_rules] =
  VMTF_sort_scores_raw_impl.refine[FCOMP VMTF_sort_scores_vmtf_reorder_list_raw]

sepref_def VMTF_sort_scores_impl
  is \<open>uncurry vmtf_reorder_list\<close>
  :: \<open>(vmtf_assn)\<^sup>k *\<^sub>a VMTF_it.arr_assn\<^sup>d \<rightarrow>\<^sub>a VMTF_it.arr_assn\<close>
  unfolding vmtf_reorder_list_def
  by sepref

sepref_def atoms_hash_del_code
  is \<open>uncurry (RETURN oo atoms_hash_del)\<close>
  :: \<open>[uncurry atoms_hash_del_pre]\<^sub>a atom_assn\<^sup>k *\<^sub>a (atoms_hash_assn)\<^sup>d \<rightarrow> atoms_hash_assn\<close>
  unfolding atoms_hash_del_def atoms_hash_del_pre_def
  apply annot_all_atm_idxs
  by sepref

sepref_def atoms_hash_insert_code
  is \<open>uncurry (RETURN oo atoms_hash_insert)\<close>
  :: \<open>[uncurry atms_hash_insert_pre]\<^sub>a
      atom_assn\<^sup>k *\<^sub>a (distinct_atoms_assn)\<^sup>d \<rightarrow>  distinct_atoms_assn\<close>
  unfolding atoms_hash_insert_def atms_hash_insert_pre_def
  supply [[goals_limit=1]]
  apply annot_all_atm_idxs
  by sepref


sepref_register find_decomp_wl_imp
sepref_register rescore_clause vmtf_flush
sepref_register vmtf_mark_to_rescore
sepref_register vmtf_mark_to_rescore_clause

sepref_register vmtf_mark_to_rescore_also_reasons get_the_propagation_reason_pol

sepref_register find_decomp_w_ns


sepref_def update_next_search_impl
  is \<open>uncurry (RETURN oo update_next_search)\<close>
  :: \<open>(atom.option_assn)\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>d \<rightarrow>\<^sub>a vmtf_remove_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_next_search_def vmtf_remove_assn_def
  by sepref

lemma case_option_split:
  \<open>(case a of None \<Rightarrow> x | Some y \<Rightarrow> f y) = 
   (if is_None a then x else let y = the a in f y)\<close>
  by (auto split: option.splits)
(*lemma is_pure_snat_option[safe_constraint_rules]: \<open>CONSTRAINT is_pure snat.option_assn\<close>
  using snat.A_pure snat.option_assn_pure unfolding CONSTRAINT_def by blast
*)

  
sepref_def ns_vmtf_dequeue_code
   is \<open>uncurry (RETURN oo ns_vmtf_dequeue)\<close>
   :: \<open>[vmtf_dequeue_pre]\<^sub>a
        atom_assn\<^sup>k *\<^sub>a (array_assn vmtf_node_assn)\<^sup>d \<rightarrow> array_assn vmtf_node_assn\<close>
  supply [[goals_limit = 1]]
  supply option.splits[split] if_splits[split]
  unfolding ns_vmtf_dequeue_def vmtf_dequeue_pre_alt_def case_option_split atom.fold_option
  apply annot_all_atm_idxs
  by sepref
  

sepref_register get_next get_prev stamp
lemma eq_Some_iff: "x = Some b \<longleftrightarrow> (\<not>is_None x \<and> the x = b)"
  by (cases x) auto

lemma hfref_refine_with_pre:
  assumes "\<And>x. P x \<Longrightarrow> g' x \<le> g x"  
  assumes "(f,g') \<in> [P]\<^sub>a\<^sub>d A \<rightarrow> R"
  shows "(f,g) \<in> [P]\<^sub>a\<^sub>d A \<rightarrow> R"
  using assms(2)[THEN hfrefD] assms(1)
  by (auto intro!: hfrefI intro: hn_refine_ref)
  
  
lemma isa_vmtf_en_dequeue_preI:
  assumes "isa_vmtf_en_dequeue_pre ((M,L),(ns, m, fst_As, lst_As, next_search))"  
  shows "fst_As < length ns" "L < length ns" "Suc m < max_unat 64"
    and "get_next (ns!L) = Some i \<longrightarrow> i < length ns"
    and "fst_As \<noteq> lst_As \<longrightarrow> get_prev (ns ! lst_As) \<noteq> None"
    and "get_next (ns ! fst_As) \<noteq> None \<longrightarrow> get_prev (ns ! lst_As) \<noteq> None"
  using assms
  unfolding isa_vmtf_en_dequeue_pre_def vmtf_dequeue_pre_def
  apply (auto simp: max_unat_def uint64_max_def sint64_max_def)
  done
  
  
find_theorems "_ \<noteq> None \<longleftrightarrow> _"  
  
lemma isa_vmtf_en_dequeue_alt_def2:
   \<open>isa_vmtf_en_dequeue_pre x \<Longrightarrow> uncurry2 (\<lambda>M L vm.
    case vm of (ns, m, fst_As, lst_As, next_search) \<Rightarrow> doN {
      ASSERT(L<length ns);
      nsL \<leftarrow> mop_list_get ns (index_of_atm L);
      let fst_As = (if fst_As = L then get_next nsL else (Some fst_As));
      
      let next_search = (if next_search = (Some L) then get_next nsL
                        else next_search);
      let lst_As = (if lst_As = L then get_prev nsL else (Some lst_As));
      ASSERT (vmtf_dequeue_pre (L,ns));
      let ns = ns_vmtf_dequeue L ns;
      ASSERT (defined_atm_pol_pre M L);
      let de = (defined_atm_pol M L);
      ASSERT (Suc m < max_unat 64);
      case fst_As of
        None \<Rightarrow> RETURN
          (ns[L := VMTF_Node m fst_As None], m + 1, L, L,
           if de then None else Some L)
      | Some fst_As \<Rightarrow> doN {
          ASSERT (L < length ns \<and> fst_As < length ns \<and> lst_As \<noteq> None);
          let fst_As' =
                VMTF_Node (stamp (ns ! fst_As)) (Some L)
                 (get_next (ns ! fst_As));
          RETURN (
            ns[L := VMTF_Node (m + 1) None (Some fst_As),
            fst_As := fst_As'],
            m + 1, L, the lst_As,
            if de then next_search else Some L)
      }
    }) x
  \<le> uncurry2 (isa_vmtf_en_dequeue) x
    \<close>
  unfolding isa_vmtf_en_dequeue_def vmtf_dequeue_def isa_vmtf_enqueue_def
    annot_unat_snat_upcast[symmetric] ASSN_ANNOT_def
  apply (cases x; simp add: Let_def)
  apply (simp 
    only: pw_le_iff refine_pw_simps 
    split: prod.splits
    )
  supply isa_vmtf_en_dequeue_preD[simp] (*isa_vmtf_en_dequeue_pre_vmtf_enqueue_pre[dest]*)
  apply (auto 
    split!: if_splits option.splits 
    simp: refine_pw_simps isa_vmtf_en_dequeue_preI dest: isa_vmtf_en_dequeue_preI 
    simp del: not_None_eq
    (*dest: isa_vmtf_en_dequeue_preI*))
  done
  
(* TODO: This is a general setup to identify any numeral by id-op (numeral is already in Sepref_Id_Op.thy.)
  Note: Naked int/nat numerals will be rejected by translate, as they need to be type-annotated.
*)  
sepref_register 1 0  



lemma vmtf_en_dequeue_fast_codeI:
  assumes "isa_vmtf_en_dequeue_pre ((M, L),(ns,m,fst_As, lst_As, next_search))"
  shows "Suc m < max_unat 64"
  using assms
  unfolding isa_vmtf_en_dequeue_pre_def max_unat_def uint64_max_def
  by auto
  
  
schematic_goal mk_free_trail_pol_fast_assn[sepref_frame_free_rules]: "MK_FREE trail_pol_fast_assn ?fr"  
  unfolding trail_pol_fast_assn_def
  by (rule free_thms sepref_frame_free_rules)+ (* TODO: Write a method for that! *)

sepref_def vmtf_en_dequeue_fast_code
   is \<open>uncurry2 isa_vmtf_en_dequeue\<close>
   :: \<open>[isa_vmtf_en_dequeue_pre]\<^sub>a
        trail_pol_fast_assn\<^sup>k *\<^sub>a atom_assn\<^sup>k *\<^sub>a vmtf_assn\<^sup>d \<rightarrow> vmtf_assn\<close>
  apply (rule hfref_refine_with_pre[OF isa_vmtf_en_dequeue_alt_def2], assumption)
  
  supply [[goals_limit = 1]]
  unfolding isa_vmtf_en_dequeue_alt_def2 case_option_split eq_Some_iff 
  apply (rewrite in "if \<hole> then get_next _ else _" short_circuit_conv)
  apply annot_all_atm_idxs    
  apply (annot_unat_const "TYPE(64)")
  unfolding atom.fold_option
  unfolding fold_tuple_optimizations
  by sepref


sepref_register vmtf_rescale
sepref_def vmtf_rescale_code
   is \<open>vmtf_rescale\<close>
   :: \<open>vmtf_assn\<^sup>d \<rightarrow>\<^sub>a vmtf_assn\<close>
  supply [[goals_limit = 1]]
  supply vmtf_en_dequeue_pre_def[simp]
  unfolding vmtf_rescale_alt_def update_stamp.simps
  unfolding atom.fold_option
  apply (annot_unat_const "TYPE(64)")
  apply annot_all_atm_idxs    
  by sepref


sepref_register partition_between_ref

(*lemma partition_between_ref_vmtf_code_aux:
  "\<lbrakk>(loi,lo)\<in>snat_rel' TYPE(64); (hii,hi)\<in>snat_rel' TYPE(64)\<rbrakk> \<Longrightarrow> lo + (hi - lo) div 2 < max_snat 64"
  apply sepref_bounds
  apply (drule in_snat_rel_imp_less_max')+ 
  by auto
*)
sepref_register isa_vmtf_enqueue

(*
lemma uint64_nal_rel_le_uint64_max: \<open>(a, b) \<in> uint64_nat_rel \<Longrightarrow> b \<le> uint64_max\<close>
  by (auto simp: uint64_nat_rel_def br_def nat_of_uint64_le_uint64_max)
*)  
lemma emptied_list_alt_def: \<open>emptied_list xs = take 0 xs\<close>
  by (auto simp: emptied_list_def)

sepref_def current_stamp_impl
  is \<open>RETURN o current_stamp\<close>
  :: \<open>vmtf_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  unfolding current_stamp_alt_def
  by sepref



sepref_register isa_vmtf_en_dequeue

sepref_def isa_vmtf_flush_fast_code
   is \<open>uncurry isa_vmtf_flush_int\<close>
   :: \<open>trail_pol_fast_assn\<^sup>k *\<^sub>a (vmtf_remove_assn)\<^sup>d \<rightarrow>\<^sub>a
        vmtf_remove_assn\<close>
  supply [[goals_limit = 1]]
  unfolding vmtf_flush_def PR_CONST_def isa_vmtf_flush_int_def
    current_stamp_def[symmetric] emptied_list_alt_def
    vmtf_remove_assn_def
  apply (rewrite at \<open>If (_ - _ \<le> \<hole>) _ _\<close> annot_snat_unat_conv)
  apply (rewrite at \<open>WHILEIT _ (\<lambda>(_, _, _)._ < \<hole>)\<close> annot_snat_unat_conv)
  apply (rewrite at \<open>isa_vmtf_en_dequeue _ (_ ! \<hole>)\<close> annot_unat_snat_conv)
  apply (rewrite at \<open>atoms_hash_del (_ ! \<hole>)\<close> annot_unat_snat_conv)
  apply (rewrite at \<open>take \<hole> _\<close> snat_const_fold[where 'a=64])
  apply (annot_unat_const "TYPE(64)")
  by sepref


sepref_register isa_vmtf_mark_to_rescore
sepref_def isa_vmtf_mark_to_rescore_code
  is \<open>uncurry (RETURN oo isa_vmtf_mark_to_rescore)\<close>
  :: \<open>[uncurry isa_vmtf_mark_to_rescore_pre]\<^sub>a
     atom_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>d \<rightarrow> vmtf_remove_assn\<close>
  supply [[goals_limit=1]] option.splits[split] vmtf_def[simp] in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff[simp]
    neq_NilE[elim!] literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset[simp]
  unfolding isa_vmtf_mark_to_rescore_pre_def isa_vmtf_mark_to_rescore_def vmtf_remove_assn_def
  by sepref


sepref_register isa_vmtf_unset
sepref_def isa_vmtf_unset_code
  is \<open>uncurry (RETURN oo isa_vmtf_unset)\<close>
  :: \<open>[uncurry vmtf_unset_pre]\<^sub>a
     atom_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>d \<rightarrow> vmtf_remove_assn\<close>
  supply [[goals_limit=1]] option.splits[split] vmtf_def[simp] in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff[simp]
    neq_NilE[elim!] literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset[simp]
  unfolding isa_vmtf_unset_def vmtf_unset_pre_def vmtf_remove_assn_def atom.fold_option
  apply (rewrite in \<open>If (_ \<or> _)\<close> short_circuit_conv)
  apply annot_all_atm_idxs
  by sepref


lemma isa_vmtf_mark_to_rescore_and_unsetI:  \<open>
     atms_hash_insert_pre ak (ad, ba) \<Longrightarrow>
       isa_vmtf_mark_to_rescore_pre ak ((a, aa, ab, ac, Some ak'), ad, ba)\<close>
  by (auto simp: isa_vmtf_mark_to_rescore_pre_def)

sepref_def vmtf_mark_to_rescore_and_unset_code
  is \<open>uncurry (RETURN oo isa_vmtf_mark_to_rescore_and_unset)\<close>
  :: \<open>[isa_vmtf_mark_to_rescore_and_unset_pre]\<^sub>a
      atom_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>d \<rightarrow> vmtf_remove_assn\<close>
  supply image_image[simp] uminus_\<A>\<^sub>i\<^sub>n_iff[iff] in_diffD[dest] option.splits[split]
    if_splits[split] isa_vmtf_unset_def[simp] isa_vmtf_mark_to_rescore_and_unsetI[intro!]
  supply [[goals_limit=1]]
  unfolding isa_vmtf_mark_to_rescore_and_unset_def isa_vmtf_mark_to_rescore_and_unset_pre_def
    save_phase_def isa_vmtf_mark_to_rescore_and_unset_pre_def
  by sepref


sepref_def find_decomp_wl_imp_fast_code
  is \<open>uncurry2 (isa_find_decomp_wl_imp)\<close>
  :: \<open>[\<lambda>((M, lev), vm). True]\<^sub>a trail_pol_fast_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>d
    \<rightarrow> trail_pol_fast_assn *a vmtf_remove_assn\<close>
  unfolding isa_find_decomp_wl_imp_def get_maximum_level_remove_def[symmetric] PR_CONST_def
    trail_pol_conv_to_no_CS_def
  supply trail_conv_to_no_CS_def[simp] lit_of_hd_trail_def[simp]
  supply [[goals_limit=1]] literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset[simp]
  supply vmtf_unset_pre_def[simp]
  apply (rewrite at \<open>let _ = _ - \<hole> in _\<close> annot_unat_snat_upcast[where 'l=64])
  apply (annot_snat_const "TYPE(64)")
  by sepref


sepref_def vmtf_rescore_fast_code
  is \<open>uncurry2 isa_vmtf_rescore\<close>
  :: \<open>clause_ll_assn\<^sup>k *\<^sub>a trail_pol_fast_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>d \<rightarrow>\<^sub>a
       vmtf_remove_assn\<close>
  unfolding isa_vmtf_rescore_body_def[abs_def] PR_CONST_def isa_vmtf_rescore_def
  supply [[goals_limit = 1]] fold_is_None[simp]
  apply (annot_snat_const "TYPE(64)")
  by sepref


sepref_def find_decomp_wl_imp'_fast_code
  is \<open>uncurry find_decomp_wl_st_int\<close>
  :: \<open>uint32_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d  \<rightarrow>\<^sub>a
        isasat_bounded_assn\<close>
  unfolding find_decomp_wl_st_int_def PR_CONST_def isasat_bounded_assn_def
  supply [[goals_limit = 1]]
  unfolding fold_tuple_optimizations
  by sepref


lemma (in -) arena_is_valid_clause_idx_le_uint64_max:
  \<open>arena_is_valid_clause_idx be bd \<Longrightarrow>
    length be \<le> sint64_max \<Longrightarrow>
   bd + arena_length be bd < max_snat 64\<close>
  \<open>arena_is_valid_clause_idx be bd \<Longrightarrow> length be \<le> sint64_max \<Longrightarrow>
   bd < max_snat 64\<close>
  using arena_lifting(10)[of be _ _ bd] unfolding max_snat_def sint64_max_def
  by (fastforce simp: arena_lifting arena_is_valid_clause_idx_def)+

sepref_def vmtf_mark_to_rescore_clause_fast_code
  is \<open>uncurry2 (isa_vmtf_mark_to_rescore_clause)\<close>
  :: \<open>[\<lambda>((N, _), _). length N \<le> sint64_max]\<^sub>a
       arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>d \<rightarrow> vmtf_remove_assn\<close>
  supply [[goals_limit=1]] arena_is_valid_clause_idx_le_uint64_max[intro]
  unfolding isa_vmtf_mark_to_rescore_clause_def PR_CONST_def
  unfolding while_eq_nfoldli[symmetric]
  apply (subst while_upt_while_direct, simp)
  unfolding nres_monad3
  apply (annot_snat_const "TYPE(64)")
  by sepref


sepref_def vmtf_mark_to_rescore_also_reasons_fast_code
  is \<open>uncurry3 (isa_vmtf_mark_to_rescore_also_reasons)\<close>
  :: \<open>[\<lambda>(((_, N), _), _). length N \<le> sint64_max]\<^sub>a
      trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a out_learned_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>d \<rightarrow>
      vmtf_remove_assn\<close>
  supply image_image[simp] uminus_\<A>\<^sub>i\<^sub>n_iff[iff] in_diffD[dest] option.splits[split]
    in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n[simp]
  supply [[goals_limit=1]]
  unfolding isa_vmtf_mark_to_rescore_also_reasons_def PR_CONST_def
  unfolding while_eq_nfoldli[symmetric]
  apply (subst while_upt_while_direct, simp)
  apply (annot_snat_const "TYPE(64)")
  unfolding  nres_monad3 case_option_split
  by sepref

experiment begin

export_llvm
  ns_vmtf_dequeue_code
  atoms_hash_del_code
  atoms_hash_insert_code
  update_next_search_impl
  ns_vmtf_dequeue_code
  vmtf_en_dequeue_fast_code
  vmtf_rescale_code
  partition_vmtf_nth_code
  partition_between_ref_vmtf_code
  quicksort_vmtf_nth_ref_code
  quicksort_vmtf_nth_code
  current_stamp_impl
  isa_vmtf_flush_fast_code
  isa_vmtf_mark_to_rescore_code
  isa_vmtf_unset_code
  vmtf_mark_to_rescore_and_unset_code
  find_decomp_wl_imp_fast_code
  vmtf_rescore_fast_code
  find_decomp_wl_imp'_fast_code
  vmtf_mark_to_rescore_clause_fast_code
  vmtf_mark_to_rescore_also_reasons_fast_code
  
end  

end