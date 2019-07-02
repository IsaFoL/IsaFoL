theory IsaSAT_VMTF_LLVM
imports Watched_Literals.WB_Sort IsaSAT_VMTF IsaSAT_Setup_LLVM
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

sepref_definition atoms_hash_del_code
  is \<open>uncurry (RETURN oo atoms_hash_del)\<close>
  :: \<open>[uncurry atoms_hash_del_pre]\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a (atoms_hash_assn)\<^sup>d \<rightarrow> atoms_hash_assn\<close>
  unfolding atoms_hash_del_def atoms_hash_del_pre_def
  apply (rewrite at \<open>list_update _ \<hole>\<close> annot_unat_snat_upcast[where 'l=64])
  by sepref

declare atoms_hash_del_code.refine[sepref_fr_rules]
sepref_definition (in -) atoms_hash_insert_code
  is \<open>uncurry (RETURN oo atoms_hash_insert)\<close>
  :: \<open>[uncurry atms_hash_insert_pre]\<^sub>a
      uint32_nat_assn\<^sup>k *\<^sub>a (distinct_atoms_assn)\<^sup>d \<rightarrow>  distinct_atoms_assn\<close>
  unfolding atoms_hash_insert_def atms_hash_insert_pre_def
  supply [simp] = uint32_max_def max_snat_def
  supply [[goals_limit=1]]
  apply (rewrite at \<open>list_update _ \<hole>\<close> annot_unat_snat_upcast[where 'l=64])
  apply (rewrite at \<open>_ ! \<hole>\<close> annot_unat_snat_upcast[where 'l=64])
  by sepref

declare atoms_hash_insert_code.refine[sepref_fr_rules]


sepref_register find_decomp_wl_imp
sepref_register rescore_clause vmtf_flush
sepref_register vmtf_mark_to_rescore
sepref_register vmtf_mark_to_rescore_clause

sepref_register vmtf_mark_to_rescore_also_reasons get_the_propagation_reason_pol

sepref_register find_decomp_w_ns


sepref_definition update_next_search_impl
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

  
sepref_definition (in -)ns_vmtf_dequeue_code
   is \<open>uncurry (RETURN oo ns_vmtf_dequeue)\<close>
   :: \<open>[vmtf_dequeue_pre]\<^sub>a
        atom_assn\<^sup>k *\<^sub>a (array_assn vmtf_node_assn)\<^sup>d \<rightarrow> array_assn vmtf_node_assn\<close>
  supply [[goals_limit = 1]]
  supply option.splits[split] if_splits[split]
  unfolding ns_vmtf_dequeue_def vmtf_dequeue_pre_alt_def case_option_split atom.fold_option
  apply annot_all_atm_idxs
  by sepref
  

declare ns_vmtf_dequeue_code.refine[sepref_fr_rules]

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
  shows "fst_As < length ns" "L < length ns" "m < max_snat 64"
    and "get_next (ns!L) = Some i \<longrightarrow> i < length ns"
    and "fst_As \<noteq> lst_As \<longrightarrow> get_prev (ns ! lst_As) \<noteq> None"
    and "get_next (ns ! fst_As) \<noteq> None \<longrightarrow> get_prev (ns ! lst_As) \<noteq> None"
  using assms
  unfolding isa_vmtf_en_dequeue_pre_def vmtf_dequeue_pre_def
  apply (auto simp: max_snat_def sint64_max_def)
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
      ASSERT (m < max_snat 64);
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
  shows "m < max_snat 64"
  using assms
  unfolding isa_vmtf_en_dequeue_pre_def max_snat_def sint64_max_def
  by auto
  
  
schematic_goal mk_free_trail_pol_fast_assn[sepref_frame_free_rules]: "MK_FREE trail_pol_fast_assn ?fr"  
  unfolding trail_pol_fast_assn_def
  by (rule free_thms sepref_frame_free_rules)+ (* TODO: Write a method for that! *)

sepref_definition vmtf_en_dequeue_fast_code
   is \<open>uncurry2 isa_vmtf_en_dequeue\<close>
   :: \<open>[isa_vmtf_en_dequeue_pre]\<^sub>a
        trail_pol_fast_assn\<^sup>k *\<^sub>a atom_assn\<^sup>k *\<^sub>a vmtf_assn\<^sup>d \<rightarrow> vmtf_assn\<close>
  apply (rule hfref_refine_with_pre[OF isa_vmtf_en_dequeue_alt_def2], assumption)
  
  supply [[goals_limit = 1]]
  supply [simp] = max_unat_def max_snat_def
  unfolding isa_vmtf_en_dequeue_alt_def2 case_option_split eq_Some_iff 
  apply (rewrite in "if \<hole> then get_next _ else _" short_circuit_conv)
  apply annot_all_atm_idxs    
  apply (annot_unat_const "TYPE(64)")
  unfolding atom.fold_option
  by sepref

declare vmtf_en_dequeue_fast_code.refine[sepref_fr_rules]

sepref_register vmtf_rescale
sepref_definition vmtf_rescale_code
   is \<open>vmtf_rescale\<close>
   :: \<open>vmtf_assn\<^sup>d \<rightarrow>\<^sub>a vmtf_assn\<close>
  supply [[goals_limit = 1]]
  supply [simp] = uint32_max_def max_snat_def max_unat_def
  
  supply vmtf_en_dequeue_pre_def[simp]
  unfolding vmtf_rescale_alt_def update_stamp.simps
  unfolding atom.fold_option
  apply (annot_unat_const "TYPE(64)")
  apply annot_all_atm_idxs    
  by sepref
  
declare vmtf_rescale_code.refine[sepref_fr_rules]



sepref_definition partition_vmtf_nth_code
   is \<open>uncurry3 partition_vmtf_nth\<close>
   :: \<open>[\<lambda>(((ns, _), hi), xs). (\<forall>x\<in>set xs. x < length ns) \<and> length xs \<le> uint32_max]\<^sub>a
  (array_assn vmtf_node_assn)\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a (arl64_assn uint32_nat_assn)\<^sup>d \<rightarrow>
  arl64_assn uint32_nat_assn *a sint64_nat_assn\<close>
  unfolding partition_vmtf_nth_def
    partition_main_def choose_pivot3_def
    convert_swap gen_swap
    
  apply (rewrite at "stamp (_!\<hole>)" annot_unat_snat_upcast[where 'l=64])  
  apply (rewrite at "stamp (_!\<hole>)" in "if \<hole> then _ else _" annot_unat_snat_upcast[where 'l=64])  
  apply (annot_snat_const "TYPE(64)")  
  supply [[goals_limit = 1]]
  supply [simp] = max_snat_def uint32_max_def
  supply partition_vmtf_nth_code_helper3[intro] partition_main_inv_def[simp]
  by sepref

declare partition_vmtf_nth_code.refine[sepref_fr_rules]

sepref_register partition_between_ref

(*lemma partition_between_ref_vmtf_code_aux:
  "\<lbrakk>(loi,lo)\<in>snat_rel' TYPE(64); (hii,hi)\<in>snat_rel' TYPE(64)\<rbrakk> \<Longrightarrow> lo + (hi - lo) div 2 < max_snat 64"
  apply sepref_bounds
  apply (drule in_snat_rel_imp_less_max')+ 
  by auto
*)  
  
    
  
(*TODO Move*)
sepref_definition (in -) partition_between_ref_vmtf_code
   is \<open>uncurry3 partition_between_ref_vmtf\<close>
   :: \<open>[\<lambda>(((vm), _), remove). (\<forall>x\<in>#mset remove. x < length (fst vm)) \<and> length remove \<le> uint32_max]\<^sub>a
      (array_assn vmtf_node_assn)\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a (arl64_assn uint32_nat_assn)\<^sup>d  \<rightarrow>
       arl64_assn uint32_nat_assn *a sint64_nat_assn\<close>
  supply [[goals_limit=1]]
  unfolding quicksort_vmtf_nth_def partition_vmtf_nth_def[symmetric]
    quicksort_vmtf_nth_ref_def List.null_def quicksort_ref_def
    partition_between_ref_vmtf_def
    partition_between_ref_def 
    partition_vmtf_nth_def[symmetric] choose_pivot3_def
    convert_swap gen_swap
  apply (annot_snat_const "TYPE(64)")
  apply (rewrite at "_!_" at "stamp (_!\<hole>)" annot_unat_snat_upcast[where 'l=64])+  
  by sepref  
sepref_register partition_between_ref_vmtf quicksort_vmtf_nth_ref
declare partition_between_ref_vmtf_code.refine[sepref_fr_rules]

lemma quicksort_vmtf_nth_ref_code_avoid_minus: "p - (1::nat) \<le> lo \<longleftrightarrow> p=0 \<or> p \<le> lo + 1" by auto
sepref_definition (in -) quicksort_vmtf_nth_ref_code
   is \<open>uncurry3 quicksort_vmtf_nth_ref\<close>
   :: \<open>[\<lambda>((vm, _), remove). (\<forall>x\<in>#mset remove. x < length (fst vm)) \<and> length remove \<le> uint32_max]\<^sub>a
      (array_assn vmtf_node_assn)\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a (arl64_assn uint32_nat_assn)\<^sup>d  \<rightarrow>
       arl64_assn uint32_nat_assn\<close>
  unfolding quicksort_vmtf_nth_def partition_vmtf_nth_def[symmetric]
    quicksort_vmtf_nth_ref_def List.null_def quicksort_ref_def
    length_0_conv[symmetric] (*length_uint32_nat_def[symmetric]*)
   partition_vmtf_nth_def[symmetric]
   partition_between_ref_vmtf_def[symmetric]
   partition_vmtf_nth_def[symmetric]
  apply (rewrite quicksort_vmtf_nth_ref_code_avoid_minus)
  apply (annot_snat_const "TYPE(64)")
  supply [[goals_limit = 1]]
  supply mset_eq_setD[dest] mset_eq_length[dest]
  by sepref

declare quicksort_vmtf_nth_ref_code.refine[sepref_fr_rules]

sepref_definition (in -) quicksort_vmtf_nth_code
   is \<open>uncurry quicksort_vmtf_nth\<close>
   :: \<open>[\<lambda>(vm, remove). (\<forall>x\<in>#mset remove. x < length (fst vm)) \<and> length remove \<le> uint32_max]\<^sub>a
      vmtf_assn\<^sup>k *\<^sub>a (arl64_assn uint32_nat_assn)\<^sup>d  \<rightarrow>
       arl64_assn uint32_nat_assn\<close>
  unfolding quicksort_vmtf_nth_def partition_vmtf_nth_def[symmetric]
    full_quicksort_ref_def List.null_def 
    length_0_conv[symmetric] 
    quicksort_vmtf_nth_ref_def[symmetric]
  supply [[goals_limit = 1]]
  supply mset_eq_setD[dest] mset_eq_length[dest]
  apply (annot_snat_const "TYPE(64)")
  by sepref

declare quicksort_vmtf_nth_code.refine[sepref_fr_rules]

lemma quicksort_vmtf_nth_code_reorder_list[sepref_fr_rules]:
   \<open>(uncurry quicksort_vmtf_nth_code, uncurry reorder_list) \<in>
      [\<lambda>((a, _), b). (\<forall>x\<in>set b. x < length a) \<and> length b \<le> uint32_max]\<^sub>a
      vmtf_assn\<^sup>k *\<^sub>a (arl64_assn uint32_nat_assn)\<^sup>d \<rightarrow> arl64_assn uint32_nat_assn\<close>
      supply [[show_types]]
  using quicksort_vmtf_nth_code.refine[FCOMP quicksort_vmtf_nth_reorder[unfolded convert_fref]]
  by auto
sepref_register isa_vmtf_enqueue

(*
lemma uint64_nal_rel_le_uint64_max: \<open>(a, b) \<in> uint64_nat_rel \<Longrightarrow> b \<le> uint64_max\<close>
  by (auto simp: uint64_nat_rel_def br_def nat_of_uint64_le_uint64_max)
*)  


xxx, ctd here: We have this definitions already!

(*TODO deduplitacte*)
text \<open>This functions deletes all elements of a resizable array, without resizing it.\<close>
definition emptied_arl :: \<open>'a array_list32 \<Rightarrow> 'a array_list32\<close> where
\<open>emptied_arl = (\<lambda>(a, n). (a, 0))\<close>

lemma emptied_arl_refine[sepref_fr_rules]:
  \<open>(return o emptied_arl, RETURN o emptied_list) \<in> (arl64_assn R)\<^sup>d \<rightarrow>\<^sub>a arl64_assn R\<close>
  unfolding emptied_arl_def emptied_list_def
  by sepref_to_hoare (sep_auto simp: arl64_assn_def hr_comp_def is_array_list32_def)

sepref_register isa_vmtf_en_dequeue
sepref_definition isa_vmtf_flush_code
   is \<open>uncurry isa_vmtf_flush_int\<close>
   :: \<open>trail_pol_assn\<^sup>k *\<^sub>a (vmtf_conc *a (arl64_assn uint32_nat_assn *a atoms_hash_assn))\<^sup>d \<rightarrow>\<^sub>a
        (vmtf_conc *a (arl64_assn uint32_nat_assn *a atoms_hash_assn))\<close>
  supply [[goals_limit = 1]] minus_uint64_nat_assn[sepref_fr_rules] uint64_max_uint64_nat_assn[sepref_fr_rules]
    uint64_nal_rel_le_uint64_max[intro]
  unfolding vmtf_flush_def PR_CONST_def isa_vmtf_flush_int_def zero_uint32_nat_def[symmetric]
    current_stamp_def[symmetric] one_uint32_nat_def[symmetric] uint64_max_uint64_def[symmetric]
  apply (rewrite at \<open>If (\<hole> \<ge> _)\<close> uint64_of_uint32_conv_def[symmetric])
  apply (rewrite at \<open>length _ + \<hole>\<close> nat_of_uint64_conv_def[symmetric])
  by sepref

declare isa_vmtf_flush_code.refine[sepref_fr_rules]

sepref_definition isa_vmtf_flush_fast_code
   is \<open>uncurry isa_vmtf_flush_int\<close>
   :: \<open>trail_pol_fast_assn\<^sup>k *\<^sub>a (vmtf_conc *a (arl64_assn uint32_nat_assn *a atoms_hash_assn))\<^sup>d \<rightarrow>\<^sub>a
        (vmtf_conc *a (arl64_assn uint32_nat_assn *a atoms_hash_assn))\<close>
  supply [[goals_limit = 1]] minus_uint64_nat_assn[sepref_fr_rules] uint64_max_uint64_nat_assn[sepref_fr_rules]
    uint64_nal_rel_le_uint64_max[intro]
  unfolding vmtf_flush_def PR_CONST_def isa_vmtf_flush_int_def zero_uint32_nat_def[symmetric]
    current_stamp_def[symmetric] one_uint32_nat_def[symmetric] uint64_max_uint64_def[symmetric]
  apply (rewrite at \<open>If (\<hole> \<ge> _)\<close> uint64_of_uint32_conv_def[symmetric])
  apply (rewrite at \<open>length _ + \<hole>\<close> nat_of_uint64_conv_def[symmetric])
  by sepref

declare isa_vmtf_flush_code.refine[sepref_fr_rules]
  isa_vmtf_flush_fast_code.refine[sepref_fr_rules]

sepref_register isa_vmtf_mark_to_rescore
sepref_definition isa_vmtf_mark_to_rescore_code
  is \<open>uncurry (RETURN oo isa_vmtf_mark_to_rescore)\<close>
  :: \<open>[uncurry isa_vmtf_mark_to_rescore_pre]\<^sub>a
     uint32_nat_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>d \<rightarrow> vmtf_remove_assn\<close>
  supply [[goals_limit=1]] option.splits[split] vmtf_def[simp] in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff[simp]
    neq_NilE[elim!] literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset[simp]
  unfolding isa_vmtf_mark_to_rescore_pre_def isa_vmtf_mark_to_rescore_def
  by sepref

declare isa_vmtf_mark_to_rescore_code.refine[sepref_fr_rules]

sepref_register isa_vmtf_unset
sepref_definition isa_vmtf_unset_code
  is \<open>uncurry (RETURN oo isa_vmtf_unset)\<close>
  :: \<open>[uncurry vmtf_unset_pre]\<^sub>a
     uint32_nat_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>d \<rightarrow> vmtf_remove_assn\<close>
  supply [[goals_limit=1]] option.splits[split] vmtf_def[simp] in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff[simp]
    neq_NilE[elim!] literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset[simp]
  unfolding isa_vmtf_unset_def vmtf_unset_pre_def
  apply (rewrite in \<open>If (_ \<or> _)\<close> short_circuit_conv)
  by sepref

declare isa_vmtf_unset_code.refine[sepref_fr_rules]

sepref_definition vmtf_mark_to_rescore_and_unset_code
  is \<open>uncurry (RETURN oo isa_vmtf_mark_to_rescore_and_unset)\<close>
  :: \<open>[isa_vmtf_mark_to_rescore_and_unset_pre]\<^sub>a
      uint32_nat_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>d \<rightarrow> vmtf_remove_assn\<close>
  supply image_image[simp] uminus_\<A>\<^sub>i\<^sub>n_iff[iff] in_diffD[dest] option.splits[split]
    if_splits[split] isa_vmtf_unset_def[simp]
  supply [[goals_limit=1]]
  unfolding isa_vmtf_mark_to_rescore_and_unset_def isa_vmtf_mark_to_rescore_def
    save_phase_def isa_vmtf_mark_to_rescore_and_unset_pre_def
  by sepref

declare vmtf_mark_to_rescore_and_unset_code.refine[sepref_fr_rules]
sepref_definition find_decomp_wl_imp_code
  is \<open>uncurry2 (isa_find_decomp_wl_imp)\<close>
  :: \<open>[\<lambda>((M, lev), vm). True]\<^sub>a trail_pol_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>d
    \<rightarrow> trail_pol_assn *a vmtf_remove_assn\<close>
  unfolding isa_find_decomp_wl_imp_def get_maximum_level_remove_def[symmetric] PR_CONST_def
    trail_pol_conv_to_no_CS_def
  supply [[goals_limit=1]] literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset[simp] trail_conv_to_no_CS_def[simp]
    lit_of_hd_trail_def[simp]
  supply uint32_nat_assn_one[sepref_fr_rules] vmtf_unset_pre_def[simp]
  supply uint32_nat_assn_minus[sepref_fr_rules]
  by sepref

declare find_decomp_wl_imp_code.refine[sepref_fr_rules]

sepref_definition find_decomp_wl_imp_fast_code
  is \<open>uncurry2 (isa_find_decomp_wl_imp)\<close>
  :: \<open>[\<lambda>((M, lev), vm). True]\<^sub>a trail_pol_fast_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>d
    \<rightarrow> trail_pol_fast_assn *a vmtf_remove_assn\<close>
  unfolding isa_find_decomp_wl_imp_def get_maximum_level_remove_def[symmetric] PR_CONST_def
    trail_pol_conv_to_no_CS_def
  supply trail_conv_to_no_CS_def[simp] lit_of_hd_trail_def[simp]
  supply [[goals_limit=1]] literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset[simp]
  supply uint32_nat_assn_one[sepref_fr_rules] vmtf_unset_pre_def[simp]
  supply uint32_nat_assn_minus[sepref_fr_rules]
  by sepref

declare find_decomp_wl_imp_fast_code.refine[sepref_fr_rules]

sepref_definition vmtf_rescore_code
  is \<open>uncurry3 isa_vmtf_rescore\<close>
  :: \<open>(array_assn unat_lit_assn)\<^sup>k *\<^sub>a trail_pol_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>d *\<^sub>a phase_saver_conc\<^sup>d \<rightarrow>\<^sub>a
       vmtf_remove_assn *a phase_saver_conc\<close>
  unfolding isa_vmtf_rescore_body_def[abs_def] PR_CONST_def isa_vmtf_rescore_def
  supply [[goals_limit = 1]] fold_is_None[simp]
  by sepref

sepref_definition vmtf_rescore_fast_code
  is \<open>uncurry3 isa_vmtf_rescore\<close>
  :: \<open>(array_assn unat_lit_assn)\<^sup>k *\<^sub>a trail_pol_fast_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>d *\<^sub>a phase_saver_conc\<^sup>d \<rightarrow>\<^sub>a
       vmtf_remove_assn *a phase_saver_conc\<close>
  unfolding isa_vmtf_rescore_body_def[abs_def] PR_CONST_def isa_vmtf_rescore_def
  supply [[goals_limit = 1]] fold_is_None[simp]
  by sepref

declare
  vmtf_rescore_code.refine[sepref_fr_rules]
  vmtf_rescore_fast_code.refine[sepref_fr_rules]

sepref_definition find_decomp_wl_imp'_code
  is \<open>uncurry find_decomp_wl_st_int\<close>
  :: \<open>uint32_nat_assn\<^sup>k *\<^sub>a isasat_unbounded_assn\<^sup>d  \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  unfolding find_decomp_wl_st_int_def PR_CONST_def isasat_unbounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

declare find_decomp_wl_imp'_code.refine[sepref_fr_rules]

sepref_definition find_decomp_wl_imp'_fast_code
  is \<open>uncurry find_decomp_wl_st_int\<close>
  :: \<open>uint32_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d  \<rightarrow>\<^sub>a
        isasat_bounded_assn\<close>
  unfolding find_decomp_wl_st_int_def PR_CONST_def isasat_bounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

declare find_decomp_wl_imp'_fast_code.refine[sepref_fr_rules]
sepref_definition vmtf_mark_to_rescore_clause_code
  is \<open>uncurry2 (isa_vmtf_mark_to_rescore_clause)\<close>
  :: \<open>arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>d \<rightarrow>\<^sub>a vmtf_remove_assn\<close>
  supply [[goals_limit=1]]
  unfolding isa_vmtf_mark_to_rescore_clause_def PR_CONST_def
  by sepref

declare vmtf_mark_to_rescore_clause_code.refine[sepref_fr_rules]

sepref_definition vmtf_mark_to_rescore_also_reasons_code
  is \<open>uncurry3 (isa_vmtf_mark_to_rescore_also_reasons)\<close>
  :: \<open>trail_pol_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a (arl64_assn unat_lit_assn)\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>d \<rightarrow>\<^sub>a vmtf_remove_assn\<close>
  supply image_image[simp] uminus_\<A>\<^sub>i\<^sub>n_iff[iff] in_diffD[dest] option.splits[split]
    in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n[simp]
  supply [[goals_limit=1]]
  unfolding isa_vmtf_mark_to_rescore_also_reasons_def PR_CONST_def
  unfolding while_eq_nfoldli[symmetric]
  apply (subst while_upt_while_direct, simp)
  apply (rewrite at \<open>(\<hole>, _)\<close> zero_uint32_nat_def[symmetric])
  unfolding one_uint32_nat_def[symmetric] nres_monad3
  by sepref

declare vmtf_mark_to_rescore_also_reasons_code.refine[sepref_fr_rules]

(*TODO kill and ann an imp_for64*)
sepref_definition (in-) isa_arena_lit_fast_code2
  is \<open>uncurry isa_arena_lit\<close>
  :: \<open>(arl64_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  supply arena_el_assn_alt_def[symmetric, simp] sum_uint64_assn[sepref_fr_rules]
  unfolding isa_arena_lit_def
  by sepref

declare isa_arena_lit_fast_code.refine

lemma isa_arena_lit_fast_code_refine[sepref_fr_rules]:
  \<open>(uncurry isa_arena_lit_fast_code2, uncurry (RETURN \<circ>\<circ> arena_lit))
  \<in> [uncurry arena_lit_pre]\<^sub>a
    arena_fast_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  using isa_arena_lit_fast_code2.refine[FCOMP isa_arena_lit_arena_lit[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] uncurry_def list_rel_compp
  by (simp add: arl64_assn_comp)
(*ENd Move*)

sepref_definition vmtf_mark_to_rescore_clause_fast_code
  is \<open>uncurry2 (isa_vmtf_mark_to_rescore_clause)\<close>
  :: \<open>[\<lambda>((N, _), _). length N \<le> uint64_max]\<^sub>a
       arena_fast_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>d \<rightarrow> vmtf_remove_assn\<close>
  supply [[goals_limit=1]] arena_is_valid_clause_idx_le_uint64_max[intro]
  unfolding isa_vmtf_mark_to_rescore_clause_def PR_CONST_def nat_of_uint64_conv_def
  unfolding while_eq_nfoldli[symmetric]
  apply (subst while_upt_while_direct, simp)
  unfolding one_uint64_nat_def[symmetric] nres_monad3 zero_uint64_nat_def[symmetric]
  by sepref

declare vmtf_mark_to_rescore_clause_fast_code.refine[sepref_fr_rules]

sepref_definition vmtf_mark_to_rescore_also_reasons_fast_code
  is \<open>uncurry3 (isa_vmtf_mark_to_rescore_also_reasons)\<close>
  :: \<open>[\<lambda>(((_, N), _), _). length N \<le> uint64_max]\<^sub>a
      trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a (arl64_assn unat_lit_assn)\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>d \<rightarrow>
      vmtf_remove_assn\<close>
  supply image_image[simp] uminus_\<A>\<^sub>i\<^sub>n_iff[iff] in_diffD[dest] option.splits[split]
    in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n[simp]
  supply [[goals_limit=1]]
  unfolding isa_vmtf_mark_to_rescore_also_reasons_def PR_CONST_def
  unfolding while_eq_nfoldli[symmetric]
  apply (subst while_upt_while_direct, simp)
  apply (rewrite at \<open>(\<hole>, _)\<close> zero_uint32_nat_def[symmetric])
  unfolding one_uint32_nat_def[symmetric] nres_monad3 zero_uint64_nat_def[symmetric]
  by sepref

declare vmtf_mark_to_rescore_also_reasons_fast_code.refine[sepref_fr_rules]


sepref_definition vmtf_find_next_undef_fast_code
  is \<open>uncurry (isa_vmtf_find_next_undef)\<close>
  :: \<open>vmtf_remove_conc\<^sup>k *\<^sub>a trail_pol_fast_assn\<^sup>k \<rightarrow>\<^sub>a option_assn uint32_nat_assn\<close>
  supply [[goals_limit=1]]
  supply not_is_None_not_None[simp]
  unfolding isa_vmtf_find_next_undef_def PR_CONST_def
  apply (rewrite at \<open>WHILE\<^sub>T\<^bsup>_\<^esup> (\<lambda> _ . \<hole>) _ _\<close> short_circuit_conv)
  by sepref

declare vmtf_find_next_undef_code.refine[sepref_fr_rules]
  vmtf_find_next_undef_fast_code.refine[sepref_fr_rules]


sepref_register vmtf_find_next_undef_upd

sepref_definition vmtf_find_next_undef_upd_fast_code
  is \<open>uncurry isa_vmtf_find_next_undef_upd\<close>
  :: \<open>trail_pol_fast_assn\<^sup>d *\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow>\<^sub>a
     (trail_pol_fast_assn *a vmtf_remove_conc) *a
        option_assn uint32_nat_assn\<close>
  supply [[goals_limit=1]]
  supply not_is_None_not_None[simp]
  unfolding isa_vmtf_find_next_undef_upd_def PR_CONST_def
  by sepref

declare
  vmtf_find_next_undef_upd_fast_code.refine[sepref_fr_rules]

end