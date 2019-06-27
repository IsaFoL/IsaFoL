theory IsaSAT_Arena_LLVM
  imports IsaSAT_Arena IsaSAT_Literals_LLVM
begin
no_notation WB_More_Refinement.fref ("[_]\<^sub>f _ \<rightarrow> _" [0,60,60] 60)
no_notation WB_More_Refinement.freft ("_ \<rightarrow>\<^sub>f _" [60,60] 60)



(* TODO: Let monadify-phase do this automatically? trade-of: goal-size vs. lost information *) 
lemma protected_bind_assoc: "Refine_Basic.bind$(Refine_Basic.bind$m$(\<lambda>\<^sub>2x. f x))$(\<lambda>\<^sub>2y. g y) = Refine_Basic.bind$m$(\<lambda>\<^sub>2x. Refine_Basic.bind$(f x)$(\<lambda>\<^sub>2y. g y))" by simp


lemma convert_swap: "WB_More_Refinement_List.swap = More_List.swap"
  unfolding WB_More_Refinement_List.swap_def More_List.swap_def ..


subsubsection \<open>Code Generation\<close>


definition "arena_el_impl_rel \<equiv> unat_rel' TYPE(32) O arena_el_rel"
lemmas [fcomp_norm_unfold] = arena_el_impl_rel_def[symmetric]
abbreviation "arena_el_impl_assn \<equiv> pure arena_el_impl_rel"


paragraph \<open>Arena Element Operations\<close>

context
  notes [simp] = arena_el_rel_def
  notes [split] = arena_el.splits
  notes [intro!] = frefI
begin  

text \<open>Literal\<close>
lemma xarena_lit_refine1: "(\<lambda>eli. eli, xarena_lit) \<in> [is_Lit]\<^sub>f arena_el_rel \<rightarrow> nat_lit_rel" by auto
sepref_definition xarena_lit_impl is "RETURN o (\<lambda>eli. eli)" :: "uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn" by sepref
lemmas [sepref_fr_rules] = xarena_lit_impl.refine[FCOMP xarena_lit_refine1]  

lemma ALit_refine1: "(\<lambda>x. x,ALit) \<in> nat_lit_rel \<rightarrow> arena_el_rel" by auto
sepref_definition ALit_impl is "RETURN o (\<lambda>x. x)" :: "uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn" by sepref
lemmas [sepref_fr_rules] = ALit_impl.refine[FCOMP ALit_refine1]  

text \<open>LBD\<close>
lemma xarena_lbd_refine1: "(\<lambda>eli. eli, xarena_lbd) \<in> [is_LBD]\<^sub>f arena_el_rel \<rightarrow> nat_rel" by auto
sepref_definition xarena_lbd_impl is "RETURN o (\<lambda>eli. eli)" :: "uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn" by sepref
lemmas [sepref_fr_rules] = xarena_lbd_impl.refine[FCOMP xarena_lbd_refine1]

lemma ALBD_refine1: "(\<lambda>eli. eli, ALBD) \<in> nat_rel \<rightarrow> arena_el_rel" by auto
sepref_definition xarena_ALBD_impl is "RETURN o (\<lambda>eli. eli)" :: "uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn" by sepref
lemmas [sepref_fr_rules] = xarena_ALBD_impl.refine[FCOMP ALBD_refine1]

text \<open>Activity\<close>
lemma xarena_act_refine1: "(\<lambda>eli. eli, xarena_act) \<in> [is_Act]\<^sub>f arena_el_rel \<rightarrow> nat_rel" by auto
sepref_definition xarena_act_impl is "RETURN o (\<lambda>eli. eli)" :: "uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn" by sepref
lemmas [sepref_fr_rules] = xarena_act_impl.refine[FCOMP xarena_act_refine1]  

lemma AAct_refine1: "(\<lambda>x. x,AActivity) \<in> nat_rel \<rightarrow> arena_el_rel" by auto
sepref_definition AAct_impl is "RETURN o (\<lambda>x. x)" :: "uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn" by sepref
lemmas [sepref_fr_rules] = AAct_impl.refine[FCOMP AAct_refine1]  

text \<open>Size\<close>
lemma xarena_length_refine1: "(\<lambda>eli. eli, xarena_length) \<in> [is_Size]\<^sub>f arena_el_rel \<rightarrow> nat_rel" by auto
sepref_definition xarena_len_impl is "RETURN o (\<lambda>eli. eli)" :: "uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn" by sepref
lemmas [sepref_fr_rules] = xarena_len_impl.refine[FCOMP xarena_length_refine1]  

lemma ASize_refine1: "(\<lambda>x. x,ASize) \<in> nat_rel \<rightarrow> arena_el_rel" by auto
sepref_definition ASize_impl is "RETURN o (\<lambda>x. x)" :: "uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn" by sepref
lemmas [sepref_fr_rules] = ASize_impl.refine[FCOMP ASize_refine1]  

text \<open>Position\<close>
lemma xarena_pos_refine1: "(\<lambda>eli. eli, xarena_pos) \<in> [is_Pos]\<^sub>f arena_el_rel \<rightarrow> nat_rel" by auto
sepref_definition xarena_pos_impl is "RETURN o (\<lambda>eli. eli)" :: "uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn" by sepref
lemmas [sepref_fr_rules] = xarena_pos_impl.refine[FCOMP xarena_pos_refine1]

lemma APos_refine1: "(\<lambda>x. x,APos) \<in> nat_rel \<rightarrow> arena_el_rel" by auto
sepref_definition APos_impl is "RETURN o (\<lambda>x. x)" :: "uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn" by sepref
lemmas [sepref_fr_rules] = APos_impl.refine[FCOMP APos_refine1]  
  

text \<open>Status\<close>
definition "status_impl_rel \<equiv> unat_rel' TYPE(32) O status_rel"
lemmas [fcomp_norm_unfold] = status_impl_rel_def[symmetric]
abbreviation "status_impl_assn \<equiv> pure status_impl_rel"

lemma xarena_status_refine1: "(\<lambda>eli. eli AND 0b11, xarena_status) \<in> [is_Status]\<^sub>f arena_el_rel \<rightarrow> status_rel" by (auto simp: is_Status_def)
sepref_definition xarena_status_impl is "RETURN o (\<lambda>eli. eli AND 0b11)" :: "uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn"
  apply (annot_unat_const "TYPE(32)")
  supply [simp] = max_unat_def
  by sepref
lemmas [sepref_fr_rules] = xarena_status_impl.refine[FCOMP xarena_status_refine1]  

lemma xarena_used_refine1: "(\<lambda>eli. eli AND 0b100 \<noteq> 0, xarena_used) \<in> [is_Status]\<^sub>f arena_el_rel \<rightarrow> bool_rel" 
  by (auto simp: is_Status_def status_rel_def bitfield_rel_def)
  
sepref_definition xarena_used_impl is "RETURN o (\<lambda>eli. eli AND 0b100 \<noteq> 0)" :: "uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  apply (annot_unat_const "TYPE(32)")
  supply [simp] = max_unat_def
  by sepref
lemmas [sepref_fr_rules] = xarena_used_impl.refine[FCOMP xarena_used_refine1]  

lemma status_eq_refine1: "((=),(=)) \<in> status_rel \<rightarrow> status_rel \<rightarrow> bool_rel"
  by (auto simp: status_rel_def)

sepref_definition status_eq_impl is "uncurry (RETURN oo (=))" 
  :: "(unat_assn' TYPE(32))\<^sup>k *\<^sub>a (unat_assn' TYPE(32))\<^sup>k \<rightarrow>\<^sub>a bool1_assn"  
  by sepref

lemmas [sepref_fr_rules] = status_eq_impl.refine[FCOMP status_eq_refine1]


definition "AStatus_impl1 cs used \<equiv> (cs AND unat_const TYPE(32) 0b11) + (if used then unat_const TYPE(32) 0b100 else unat_const TYPE(32) 0b0)"
lemma AStatus_refine1: "(AStatus_impl1, AStatus) \<in> status_rel \<rightarrow> bool_rel \<rightarrow> arena_el_rel"
  by (auto simp: status_rel_def bitfield_rel_def AStatus_impl1_def split: if_splits)
sepref_definition AStatus_impl is "uncurry (RETURN oo AStatus_impl1)" :: "uint32_nat_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn"
  unfolding AStatus_impl1_def
  supply [simp] = max_unat_def and [split] = if_splits
  by sepref
lemmas [sepref_fr_rules] = AStatus_impl.refine[FCOMP AStatus_refine1]







subsubsection \<open>Arena Operations\<close>

paragraph \<open>Length\<close>

abbreviation "arena_fast_assn \<equiv> al_assn' TYPE(64) arena_el_impl_assn"

lemma arena_lengthI: 
  assumes "arena_is_valid_clause_idx a b"
  shows "Suc 0 \<le> b"
  and "b < length a"
  and "is_Size (a ! (b - Suc 0))"
  using SIZE_SHIFT_def assms
  by (auto simp: arena_is_valid_clause_idx_def arena_lifting)
  
lemma arena_length_impl_bounds_aux1: 
  "(ac, a) \<in> unat_rel' TYPE(32) \<Longrightarrow> a < 9223372036854775806"
  by (auto dest!: in_unat_rel_imp_less_max' simp: max_unat_def)

lemma arena_length_alt: 
  \<open>arena_length arena i = (
    let l = xarena_length (arena!(i - snat_const TYPE(64) 1)) 
    in snat_const TYPE(64) 2 + op_unat_snat_upcast TYPE(64) l)\<close>
  by (simp add: arena_length_def SIZE_SHIFT_def)  
  
sepref_register arena_length  
sepref_definition arena_length_impl 
  is "uncurry (RETURN oo arena_length)" 
    :: "[uncurry arena_is_valid_clause_idx]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> snat_assn' TYPE(64)"
  unfolding arena_length_alt
  supply [simp] = max_snat_def max_unat_def arena_length_impl_bounds_aux1
    and [dest] = arena_lengthI
  by sepref
lemmas [sepref_fr_rules] = arena_length_impl.refine


paragraph \<open>Literal at given position\<close>

lemma arena_lit_implI:
  assumes "arena_lit_pre a b"
  shows "b < length a" "is_Lit (a ! b)"
  using assms unfolding arena_lit_pre_def arena_is_valid_clause_idx_and_access_def
  by (fastforce dest: arena_lifting)+

sepref_register arena_lit xarena_lit
sepref_definition arena_lit_impl 
  is "uncurry (RETURN oo arena_lit)" 
    :: "[uncurry arena_lit_pre]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> unat_lit_assn"
  supply [intro] = arena_lit_implI
  unfolding arena_lit_def
  by sepref
lemmas [sepref_fr_rules] = arena_lit_impl.refine

      
paragraph \<open>Status of the clause\<close>

lemma arena_status_implI:
  assumes "arena_is_valid_clause_vdom a b"
  shows "4 \<le> b" "b - 4 < length a" "is_Status (a ! (b-4))"
  using assms STATUS_SHIFT_def arena_dom_status_iff
  unfolding arena_is_valid_clause_vdom_def
  by (auto dest: valid_arena_in_vdom_le_arena)

sepref_register arena_status xarena_status
sepref_definition arena_status_impl 
  is "uncurry (RETURN oo arena_status)" 
    :: "[uncurry arena_is_valid_clause_vdom]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> status_impl_assn"
  supply [intro] = arena_status_implI
  supply [simp] = max_snat_def
  unfolding arena_status_def STATUS_SHIFT_def
  apply (annot_snat_const "TYPE(64)")
  by sepref
lemmas [sepref_fr_rules] = arena_status_impl.refine


paragraph \<open>Swap literals\<close>
sepref_register swap_lits
sepref_definition swap_lits_impl is "uncurry3 (RETURN oooo swap_lits)"
  :: "[\<lambda>(((C,i),j),arena). C + i < length arena \<and> C + j < length arena]\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>d \<rightarrow> arena_fast_assn"
  unfolding swap_lits_def convert_swap
  supply [dest] = rdomp_al_imp_len_bound
  unfolding gen_swap
  by sepref

lemmas [sepref_fr_rules] = swap_lits_impl.refine
  
paragraph \<open>Get LBD\<close>

lemma get_clause_LBD_preI:
  assumes "get_clause_LBD_pre a b"
  shows "2 \<le> b"
  and "b < length a"
  and "is_LBD (a ! (b - 2))"
  using LBD_SHIFT_def assms
  by (auto simp: get_clause_LBD_pre_def arena_is_valid_clause_idx_def arena_lifting)

sepref_register arena_lbd
sepref_definition arena_lbd_impl
  is "uncurry (RETURN oo arena_lbd)"
    :: "[uncurry get_clause_LBD_pre]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>uint32_nat_assn"
  unfolding arena_lbd_def LBD_SHIFT_def
  supply [simp] = max_snat_def max_unat_def
    and [dest] = get_clause_LBD_preI
  apply (annot_snat_const "TYPE(64)")
  by sepref
lemmas [sepref_fr_rules] = arena_lbd_impl.refine

paragraph \<open>Get Saved Position\<close>


lemma arena_posI:
  assumes "get_saved_pos_pre a b"
  shows "5 \<le> b"
  and "b < length a"
  and "is_Pos (a ! (b - 5))"
  using POS_SHIFT_def assms is_short_clause_def[of \<open>_ \<propto> b\<close>]
  apply (auto simp: get_saved_pos_pre_def arena_is_valid_clause_idx_def arena_lifting
     MAX_LENGTH_SHORT_CLAUSE_def[symmetric] simp del: MAX_LENGTH_SHORT_CLAUSE_def)
  using arena_lifting(1) arena_lifting(4) header_size_def apply fastforce
  done

lemma arena_pos_alt: 
  \<open>arena_pos arena i = (
    let l = xarena_pos (arena!(i - snat_const TYPE(64) 5)) 
    in snat_const TYPE(64) 2 + op_unat_snat_upcast TYPE(64) l)\<close>
  by (simp add: arena_pos_def POS_SHIFT_def)  

sepref_register arena_pos
sepref_definition arena_pos_impl 
  is "uncurry (RETURN oo arena_pos)" 
    :: "[uncurry get_saved_pos_pre]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> snat_assn' TYPE(64)"
  unfolding arena_pos_alt
  supply [simp] = max_snat_def max_unat_def arena_length_impl_bounds_aux1
    and [dest] = arena_posI
  by sepref
lemmas [sepref_fr_rules] = arena_pos_impl.refine

paragraph \<open>Update LBD\<close>

lemma update_lbdI:
  assumes "update_lbd_pre ((b, lbd), a)"
  shows "2 \<le> b"
  and "b -2 < length a"
  using LBD_SHIFT_def assms
  apply (auto simp: arena_is_valid_clause_idx_def arena_lifting update_lbd_pre_def
    dest: arena_lifting(10))
  by (simp add: less_imp_diff_less valid_arena_def)

sepref_register update_lbd
sepref_definition update_lbd_impl 
  is "uncurry2 (RETURN ooo update_lbd)" 
    :: "[update_lbd_pre]\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>d  \<rightarrow> arena_fast_assn"
  unfolding update_lbd_def LBD_SHIFT_def
  supply [simp] = max_snat_def max_unat_def arena_length_impl_bounds_aux1 update_lbdI
    and [dest] = arena_posI
  apply (annot_snat_const "TYPE(64)")
  by sepref

lemmas [sepref_fr_rules] = update_lbd_impl.refine
  
  
paragraph \<open>Update Saved Position\<close>

lemma update_posI:
  assumes "isa_update_pos_pre ((b, pos), a)"
  shows "5 \<le> b" "2 \<le> pos" "b-5 < length a"
  using assms POS_SHIFT_def
  unfolding isa_update_pos_pre_def
  apply (auto simp: arena_is_valid_clause_idx_def arena_lifting)
  (* TODO: Clean up this mess *)
  apply (metis (full_types) MAX_LENGTH_SHORT_CLAUSE_def arena_is_valid_clause_idx_def arena_posI(1) get_saved_pos_pre_def)
  by (simp add: less_imp_diff_less valid_arena_def)
  
lemma update_posI2:
  assumes "isa_update_pos_pre ((b, pos), a)"
  assumes "rdomp (al_assn arena_el_impl_assn) a"
  shows "pos < 2 + max_unat 32"
  using assms POS_SHIFT_def
  unfolding isa_update_pos_pre_def
  apply (auto simp: arena_is_valid_clause_idx_def arena_lifting)
  sorry (* TODO !*)
  

sepref_register arena_update_pos   
sepref_definition update_pos_impl
  is "uncurry2 (RETURN ooo arena_update_pos)" 
    :: "[isa_update_pos_pre]\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>d  \<rightarrow> arena_fast_assn"
  unfolding arena_update_pos_def POS_SHIFT_def
  apply (annot_snat_const "TYPE(64)")
  apply (rewrite at "APos \<hole>" annot_snat_unat_downcast[where 'l=32])
  supply [simp] = max_snat_def max_unat_def update_posI and [dest] = update_posI2
  (*apply (rule hfref_with_rdomI)*)
  by sepref
lemmas [sepref_fr_rules] = update_pos_impl.refine
  
sepref_register IRRED LEARNED DELETED
lemma IRRED_impl[sepref_import_param]: "(0,IRRED) \<in> status_impl_rel"
  unfolding status_impl_rel_def status_rel_def unat_rel_def unat.rel_def
  by (auto simp: in_br_conv)
    
lemma LEARNED_impl[sepref_import_param]: "(1,LEARNED) \<in> status_impl_rel"
  unfolding status_impl_rel_def status_rel_def unat_rel_def unat.rel_def
  by (auto simp: in_br_conv)

lemma DELETED_impl[sepref_import_param]: "(3,DELETED) \<in> status_impl_rel"
  unfolding status_impl_rel_def status_rel_def unat_rel_def unat.rel_def
  by (auto simp: in_br_conv)

  
lemma mark_garbageI:
  assumes "mark_garbage_pre (a, b)"
  shows "4 \<le> b" "b-4 < length a"
  using assms STATUS_SHIFT_def
  unfolding mark_garbage_pre_def
  apply (auto simp: arena_is_valid_clause_idx_def arena_lifting)
  apply (metis (full_types) arena_dom_status_iff(5) insertCI valid_arena_extra_information_mark_to_delete)
  by (simp add: less_imp_diff_less valid_arena_def)

sepref_register extra_information_mark_to_delete      
sepref_definition mark_garbage_impl is "uncurry (RETURN oo extra_information_mark_to_delete)" 
  :: "[mark_garbage_pre]\<^sub>a arena_fast_assn\<^sup>d *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> arena_fast_assn"
  unfolding extra_information_mark_to_delete_def STATUS_SHIFT_def
  apply (annot_snat_const "TYPE(64)")
  supply [simp] = max_snat_def mark_garbageI
  by sepref
lemmas [sepref_fr_rules] = mark_garbage_impl.refine
  


paragraph \<open>Activity\<close>

lemma arena_act_implI:
  assumes "arena_act_pre a b"
  shows "3 \<le> b" "b - 3 < length a" "is_Act (a ! (b-3))"
  using assms ACTIVITY_SHIFT_def 
  apply (auto simp: arena_act_pre_def arena_is_valid_clause_idx_def arena_lifting)
  by (simp add: less_imp_diff_less valid_arena_def)
  
sepref_register arena_act
sepref_definition arena_act_impl 
  is "uncurry (RETURN oo arena_act)" 
    :: "[uncurry arena_act_pre]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn"
  supply [intro] = arena_act_implI
  supply [simp] = max_snat_def
  unfolding arena_act_def ACTIVITY_SHIFT_def
  apply (annot_snat_const "TYPE(64)")
  by sepref
lemmas [sepref_fr_rules] = arena_act_impl.refine



paragraph \<open>Increment Activity\<close>

context begin                                             

interpretation llvm_prim_arith_setup .

sepref_register op_incr_mod32
lemma op_incr_mod32_hnr[sepref_fr_rules]: 
  "(\<lambda>x. ll_add x 1, RETURN o op_incr_mod32) \<in> uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn"
  unfolding unat_rel_def unat.rel_def 
  apply sepref_to_hoare
  apply (simp add: in_br_conv)
  apply vcg'
  unfolding op_incr_mod32_def
  by (simp add: unat_word_ariths)

end  
  
sepref_register arena_incr_act
sepref_definition arena_incr_act_impl is "uncurry (RETURN oo arena_incr_act)" 
  :: "[uncurry arena_act_pre]\<^sub>a arena_fast_assn\<^sup>d *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> arena_fast_assn"
  unfolding arena_incr_act_def ACTIVITY_SHIFT_def
  supply [intro] = arena_act_implI
  supply [simp] = max_snat_def
  apply (annot_snat_const "TYPE(64)")
  by sepref
lemmas [sepref_fr_rules] = arena_incr_act_impl.refine

sepref_register arena_decr_act
sepref_definition arena_decr_act_impl is "uncurry (RETURN oo arena_decr_act)" 
  :: "[uncurry arena_act_pre]\<^sub>a arena_fast_assn\<^sup>d *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> arena_fast_assn"
  unfolding arena_decr_act_def ACTIVITY_SHIFT_def
  supply [intro] = arena_act_implI
  supply [simp] = max_snat_def max_unat_def
  apply (rewrite at "_ div \<hole>"  unat_const_fold[where 'a=32])
  apply (annot_snat_const "TYPE(64)")
  by sepref
lemmas [sepref_fr_rules] = arena_decr_act_impl.refine


paragraph \<open>Mark used\<close>

term mark_used

lemma arena_mark_used_implI:
  assumes "arena_act_pre a b"
  shows "4 \<le> b" "b - 4 < length a" "is_Status (a ! (b-4))"
  using assms STATUS_SHIFT_def 
  apply (auto simp: arena_act_pre_def arena_is_valid_clause_idx_def arena_lifting)
  subgoal by (metis (full_types) arena_is_valid_clause_vdom_def arena_status_implI(1) insertCI valid_arena_extra_information_mark_to_delete)
  subgoal by (simp add: less_imp_diff_less valid_arena_def)
  done

(* TODO: Wrong name for precondition! *)
sepref_register mark_used
sepref_definition mark_used_impl is "uncurry (RETURN oo mark_used)" 
  :: "[uncurry arena_act_pre]\<^sub>a arena_fast_assn\<^sup>d *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> arena_fast_assn"
  unfolding mark_used_def STATUS_SHIFT_def
  supply [intro] = arena_mark_used_implI
  supply [simp] = max_snat_def max_unat_def
  apply (annot_snat_const "TYPE(64)")
  by sepref
lemmas [sepref_fr_rules] = mark_used_impl.refine

sepref_register mark_unused
sepref_definition mark_unused_impl is "uncurry (RETURN oo mark_unused)" 
  :: "[uncurry arena_act_pre]\<^sub>a arena_fast_assn\<^sup>d *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> arena_fast_assn"
  unfolding mark_unused_def STATUS_SHIFT_def
  supply [intro] = arena_mark_used_implI
  supply [simp] = max_snat_def max_unat_def
  apply (annot_snat_const "TYPE(64)")
  by sepref
lemmas [sepref_fr_rules] = mark_unused_impl.refine

 

paragraph \<open>Marked as used?\<close>

lemma arena_marked_as_used_implI:
  assumes "marked_as_used_pre a b"
  shows "4 \<le> b" "b - 4 < length a" "is_Status (a ! (b-4))"
  using assms STATUS_SHIFT_def 
  apply (auto simp: marked_as_used_pre_def arena_is_valid_clause_idx_def arena_lifting)
  subgoal by (metis (full_types) arena_is_valid_clause_vdom_def arena_status_implI(1) insertCI valid_arena_extra_information_mark_to_delete)
  subgoal by (simp add: less_imp_diff_less valid_arena_def)
  done

sepref_register marked_as_used
sepref_definition marked_as_used_impl 
  is "uncurry (RETURN oo marked_as_used)" 
    :: "[uncurry marked_as_used_pre]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> bool1_assn"
  supply [intro] = arena_marked_as_used_implI
  supply [simp] = max_snat_def
  unfolding marked_as_used_def STATUS_SHIFT_def
  apply (annot_snat_const "TYPE(64)")
  by sepref
lemmas [sepref_fr_rules] = marked_as_used_impl.refine

sepref_register MAX_LENGTH_SHORT_CLAUSE
sepref_definition MAX_LENGTH_SHORT_CLAUSE_impl is "uncurry0 (RETURN MAX_LENGTH_SHORT_CLAUSE)" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn"
  unfolding MAX_LENGTH_SHORT_CLAUSE_def
  apply (annot_snat_const "TYPE(64)")
  supply [simp] = max_snat_def
  by sepref
lemmas [sepref_fr_rules] = MAX_LENGTH_SHORT_CLAUSE_impl.refine


end

end