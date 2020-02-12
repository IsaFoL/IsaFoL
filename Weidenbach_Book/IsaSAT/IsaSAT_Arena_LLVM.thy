theory IsaSAT_Arena_LLVM
  imports IsaSAT_Arena IsaSAT_Literals_LLVM
    WB_More_Word
begin


section \<open>Code Generation\<close>

no_notation WB_More_Refinement.fref (\<open>[_]\<^sub>f _ \<rightarrow> _\<close> [0,60,60] 60)
no_notation WB_More_Refinement.freft (\<open>_ \<rightarrow>\<^sub>f _\<close> [60,60] 60)



(* TODO: Let monadify-phase do this automatically? trade-of: goal-size vs. lost information *)
lemma protected_bind_assoc: \<open>Refine_Basic.bind$(Refine_Basic.bind$m$(\<lambda>\<^sub>2x. f x))$(\<lambda>\<^sub>2y. g y) = Refine_Basic.bind$m$(\<lambda>\<^sub>2x. Refine_Basic.bind$(f x)$(\<lambda>\<^sub>2y. g y))\<close> by simp


lemma convert_swap: \<open>WB_More_Refinement_List.swap = More_List.swap\<close>
  unfolding WB_More_Refinement_List.swap_def More_List.swap_def ..


subsubsection \<open>Code Generation\<close>


definition \<open>arena_el_impl_rel \<equiv> unat_rel' TYPE(32) O arena_el_rel\<close>
lemmas [fcomp_norm_unfold] = arena_el_impl_rel_def[symmetric]
abbreviation \<open>arena_el_impl_assn \<equiv> pure arena_el_impl_rel\<close>


paragraph \<open>Arena Element Operations\<close>

context
  notes [simp] = arena_el_rel_def
  notes [split] = arena_el.splits
  notes [intro!] = frefI
begin

text \<open>Literal\<close>
lemma xarena_lit_refine1: \<open>(\<lambda>eli. eli, xarena_lit) \<in> [is_Lit]\<^sub>f arena_el_rel \<rightarrow> nat_lit_rel\<close> by auto
sepref_def xarena_lit_impl [llvm_inline] is [] \<open>RETURN o (\<lambda>eli. eli)\<close> :: \<open>uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close> by sepref
lemmas [sepref_fr_rules] = xarena_lit_impl.refine[FCOMP xarena_lit_refine1]

lemma ALit_refine1: \<open>(\<lambda>x. x,ALit) \<in> nat_lit_rel \<rightarrow> arena_el_rel\<close> by auto
sepref_def ALit_impl [llvm_inline] is [] \<open>RETURN o (\<lambda>x. x)\<close> :: \<open>uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close> by sepref
lemmas [sepref_fr_rules] = ALit_impl.refine[FCOMP ALit_refine1]

text \<open>LBD\<close>
lemma xarena_lbd_refine1: \<open>(\<lambda>eli. eli, xarena_lbd) \<in> [is_LBD]\<^sub>f arena_el_rel \<rightarrow> nat_rel\<close> by auto
sepref_def xarena_lbd_impl [llvm_inline] is [] \<open>RETURN o (\<lambda>eli. eli)\<close> :: \<open>uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close> by sepref
lemmas [sepref_fr_rules] = xarena_lbd_impl.refine[FCOMP xarena_lbd_refine1]

lemma ALBD_refine1: \<open>(\<lambda>eli. eli, ALBD) \<in> nat_rel \<rightarrow> arena_el_rel\<close> by auto
sepref_def xarena_ALBD_impl [llvm_inline] is [] \<open>RETURN o (\<lambda>eli. eli)\<close> :: \<open>uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close> by sepref
lemmas [sepref_fr_rules] = xarena_ALBD_impl.refine[FCOMP ALBD_refine1]

text \<open>Activity\<close>
lemma xarena_act_refine1: \<open>(\<lambda>eli. eli, xarena_act) \<in> [is_Act]\<^sub>f arena_el_rel \<rightarrow> nat_rel\<close> by auto
sepref_def xarena_act_impl [llvm_inline] is [] \<open>RETURN o (\<lambda>eli. eli)\<close> :: \<open>uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close> by sepref
lemmas [sepref_fr_rules] = xarena_act_impl.refine[FCOMP xarena_act_refine1]

lemma AAct_refine1: \<open>(\<lambda>x. x,AActivity) \<in> nat_rel \<rightarrow> arena_el_rel\<close> by auto
sepref_def AAct_impl [llvm_inline] is [] \<open>RETURN o (\<lambda>x. x)\<close> :: \<open>uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close> by sepref
lemmas [sepref_fr_rules] = AAct_impl.refine[FCOMP AAct_refine1]

text \<open>Size\<close>
lemma xarena_length_refine1: \<open>(\<lambda>eli. eli, xarena_length) \<in> [is_Size]\<^sub>f arena_el_rel \<rightarrow> nat_rel\<close> by auto
sepref_def xarena_len_impl [llvm_inline] is [] \<open>RETURN o (\<lambda>eli. eli)\<close> :: \<open>uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close> by sepref
lemmas [sepref_fr_rules] = xarena_len_impl.refine[FCOMP xarena_length_refine1]

lemma ASize_refine1: \<open>(\<lambda>x. x,ASize) \<in> nat_rel \<rightarrow> arena_el_rel\<close> by auto
sepref_def ASize_impl [llvm_inline] is [] \<open>RETURN o (\<lambda>x. x)\<close> :: \<open>uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close> by sepref
lemmas [sepref_fr_rules] = ASize_impl.refine[FCOMP ASize_refine1]

text \<open>Position\<close>
lemma xarena_pos_refine1: \<open>(\<lambda>eli. eli, xarena_pos) \<in> [is_Pos]\<^sub>f arena_el_rel \<rightarrow> nat_rel\<close> by auto
sepref_def xarena_pos_impl [llvm_inline] is [] \<open>RETURN o (\<lambda>eli. eli)\<close> :: \<open>uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close> by sepref
lemmas [sepref_fr_rules] = xarena_pos_impl.refine[FCOMP xarena_pos_refine1]

lemma APos_refine1: \<open>(\<lambda>x. x,APos) \<in> nat_rel \<rightarrow> arena_el_rel\<close> by auto
sepref_def APos_impl [llvm_inline] is [] \<open>RETURN o (\<lambda>x. x)\<close> :: \<open>uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close> by sepref
lemmas [sepref_fr_rules] = APos_impl.refine[FCOMP APos_refine1]


text \<open>Status\<close>
definition \<open>status_impl_rel \<equiv> unat_rel' TYPE(32) O status_rel\<close>
lemmas [fcomp_norm_unfold] = status_impl_rel_def[symmetric]
abbreviation \<open>status_impl_assn \<equiv> pure status_impl_rel\<close>

lemma xarena_status_refine1: \<open>(\<lambda>eli. eli AND 0b11, xarena_status) \<in> [is_Status]\<^sub>f arena_el_rel \<rightarrow> status_rel\<close> by (auto simp: is_Status_def)
sepref_def xarena_status_impl [llvm_inline] is [] \<open>RETURN o (\<lambda>eli. eli AND 0b11)\<close> :: \<open>uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref
lemmas [sepref_fr_rules] = xarena_status_impl.refine[FCOMP xarena_status_refine1]

lemma xarena_used_refine1: \<open>(\<lambda>eli. eli AND 0b100 \<noteq> 0, xarena_used) \<in> [is_Status]\<^sub>f arena_el_rel \<rightarrow> bool_rel\<close>
  by (auto simp: is_Status_def status_rel_def bitfield_rel_def)

sepref_def xarena_used_impl [llvm_inline] is [] \<open>RETURN o (\<lambda>eli. eli AND 0b100 \<noteq> 0)\<close> :: \<open>uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref
lemmas [sepref_fr_rules] = xarena_used_impl.refine[FCOMP xarena_used_refine1]

lemma status_eq_refine1: \<open>((=),(=)) \<in> status_rel \<rightarrow> status_rel \<rightarrow> bool_rel\<close>
  by (auto simp: status_rel_def)

sepref_def status_eq_impl [llvm_inline] is [] \<open>uncurry (RETURN oo (=))\<close>
  :: \<open>(unat_assn' TYPE(32))\<^sup>k *\<^sub>a (unat_assn' TYPE(32))\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  by sepref

lemmas [sepref_fr_rules] = status_eq_impl.refine[FCOMP status_eq_refine1]


definition \<open>AStatus_impl1 cs used \<equiv> (cs AND unat_const TYPE(32) 0b11) + (if used then unat_const TYPE(32) 0b100 else unat_const TYPE(32) 0b0)\<close>
lemma AStatus_refine1: \<open>(AStatus_impl1, AStatus) \<in> status_rel \<rightarrow> bool_rel \<rightarrow> arena_el_rel\<close>
  by (auto simp: status_rel_def bitfield_rel_def AStatus_impl1_def split: if_splits)
sepref_def AStatus_impl [llvm_inline] is [] \<open>uncurry (RETURN oo AStatus_impl1)\<close> :: \<open>uint32_nat_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding AStatus_impl1_def
  supply [split] = if_splits
  by sepref
lemmas [sepref_fr_rules] = AStatus_impl.refine[FCOMP AStatus_refine1]







subsubsection \<open>Arena Operations\<close>

paragraph \<open>Length\<close>

abbreviation \<open>arena_fast_assn \<equiv> al_assn' TYPE(64) arena_el_impl_assn\<close>

lemma arena_lengthI:
  assumes \<open>arena_is_valid_clause_idx a b\<close>
  shows \<open>Suc 0 \<le> b\<close>
  and \<open>b < length a\<close>
  and \<open>is_Size (a ! (b - Suc 0))\<close>
  using SIZE_SHIFT_def assms
  by (auto simp: arena_is_valid_clause_idx_def arena_lifting)

(*
lemma arena_length_impl_bounds_aux1:
  \<open>(ac, a) \<in> unat_rel' TYPE(32) \<Longrightarrow> a < 9223372036854775806\<close>
  by (auto dest!: in_unat_rel_imp_less_max' simp: max_unat_def)
*)

lemma arena_length_alt:
  \<open>arena_length arena i = (
    let l = xarena_length (arena!(i - snat_const TYPE(64) 1))
    in snat_const TYPE(64) 2 + op_unat_snat_upcast TYPE(64) l)\<close>
  by (simp add: arena_length_def SIZE_SHIFT_def)

sepref_register arena_length
sepref_def arena_length_impl
  is \<open>uncurry (RETURN oo arena_length)\<close>
    :: \<open>[uncurry arena_is_valid_clause_idx]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> snat_assn' TYPE(64)\<close>
  unfolding arena_length_alt
  supply [dest] = arena_lengthI
  by sepref


paragraph \<open>Literal at given position\<close>

lemma arena_lit_implI:
  assumes \<open>arena_lit_pre a b\<close>
  shows \<open>b < length a\<close> \<open>is_Lit (a ! b)\<close>
  using assms unfolding arena_lit_pre_def arena_is_valid_clause_idx_and_access_def
  by (fastforce dest: arena_lifting)+

sepref_register arena_lit xarena_lit
sepref_def arena_lit_impl
  is \<open>uncurry (RETURN oo arena_lit)\<close>
    :: \<open>[uncurry arena_lit_pre]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  supply [intro] = arena_lit_implI
  unfolding arena_lit_def
  by sepref

sepref_register mop_arena_lit mop_arena_lit2
sepref_def mop_arena_lit_impl
  is \<open>uncurry (mop_arena_lit)\<close>
    :: \<open>arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a unat_lit_assn\<close>
  supply [intro] = arena_lit_implI
  unfolding mop_arena_lit_def
  by sepref

sepref_def mop_arena_lit2_impl
  is \<open>uncurry2 (mop_arena_lit2)\<close>
    :: \<open>[\<lambda>((N, _), _). length N \<le> sint64_max]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k  *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  supply [intro] = arena_lit_implI
  supply [dest] = arena_lit_pre_le_lengthD
  unfolding mop_arena_lit2_def
  by sepref



paragraph \<open>Status of the clause\<close>

lemma arena_status_implI:
  assumes \<open>arena_is_valid_clause_vdom a b\<close>
  shows \<open>4 \<le> b\<close> \<open>b - 4 < length a\<close> \<open>is_Status (a ! (b-4))\<close>
  using assms STATUS_SHIFT_def arena_dom_status_iff
  unfolding arena_is_valid_clause_vdom_def
  by (auto dest: valid_arena_in_vdom_le_arena)

sepref_register arena_status xarena_status
sepref_def arena_status_impl
  is \<open>uncurry (RETURN oo arena_status)\<close>
    :: \<open>[uncurry arena_is_valid_clause_vdom]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> status_impl_assn\<close>
  supply [intro] = arena_status_implI
  unfolding arena_status_def STATUS_SHIFT_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref


paragraph \<open>Swap literals\<close>
sepref_register swap_lits
sepref_def swap_lits_impl is \<open>uncurry3 (RETURN oooo swap_lits)\<close>
  :: \<open>[\<lambda>(((C,i),j),arena). C + i < length arena \<and> C + j < length arena]\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>d \<rightarrow> arena_fast_assn\<close>
  unfolding swap_lits_def convert_swap
  unfolding gen_swap
  by sepref


paragraph \<open>Get LBD\<close>

lemma get_clause_LBD_preI:
  assumes \<open>get_clause_LBD_pre a b\<close>
  shows \<open>2 \<le> b\<close>
  and \<open>b < length a\<close>
  and \<open>is_LBD (a ! (b - 2))\<close>
  using LBD_SHIFT_def assms
  by (auto simp: get_clause_LBD_pre_def arena_is_valid_clause_idx_def arena_lifting)

sepref_register arena_lbd
sepref_def arena_lbd_impl
  is \<open>uncurry (RETURN oo arena_lbd)\<close>
    :: \<open>[uncurry get_clause_LBD_pre]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>uint32_nat_assn\<close>
  unfolding arena_lbd_def LBD_SHIFT_def
  supply [dest] = get_clause_LBD_preI
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

paragraph \<open>Get Saved Position\<close>


lemma arena_posI:
  assumes \<open>get_saved_pos_pre a b\<close>
  shows \<open>5 \<le> b\<close>
  and \<open>b < length a\<close>
  and \<open>is_Pos (a ! (b - 5))\<close>
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
sepref_def arena_pos_impl
  is \<open>uncurry (RETURN oo arena_pos)\<close>
    :: \<open>[uncurry get_saved_pos_pre]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> snat_assn' TYPE(64)\<close>
  unfolding arena_pos_alt
  supply [dest] = arena_posI
  by sepref

paragraph \<open>Update LBD\<close>

lemma update_lbdI:
  assumes \<open>update_lbd_pre ((b, lbd), a)\<close>
  shows \<open>2 \<le> b\<close>
  and \<open>b -2 < length a\<close>
  using LBD_SHIFT_def assms
  apply (auto simp: arena_is_valid_clause_idx_def arena_lifting update_lbd_pre_def
    dest: arena_lifting(10))
  by (simp add: less_imp_diff_less valid_arena_def)

sepref_register update_lbd
sepref_def update_lbd_impl
  is \<open>uncurry2 (RETURN ooo update_lbd)\<close>
    :: \<open>[update_lbd_pre]\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>d  \<rightarrow> arena_fast_assn\<close>
  unfolding update_lbd_def LBD_SHIFT_def
  supply [simp] = update_lbdI
    and [dest] = arena_posI
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref



paragraph \<open>Update Saved Position\<close>

lemma update_posI:
  assumes \<open>isa_update_pos_pre ((b, pos), a)\<close>
  shows \<open>5 \<le> b\<close> \<open>2 \<le> pos\<close> \<open>b-5 < length a\<close>
  using assms POS_SHIFT_def
  unfolding isa_update_pos_pre_def
  apply (auto simp: arena_is_valid_clause_idx_def arena_lifting)
  (* TODO: Clean up this mess *)
  apply (metis (full_types) MAX_LENGTH_SHORT_CLAUSE_def arena_is_valid_clause_idx_def arena_posI(1) get_saved_pos_pre_def)
  by (simp add: less_imp_diff_less valid_arena_def)

lemma update_posI2:
  assumes \<open>isa_update_pos_pre ((b, pos), a)\<close>
  assumes \<open>rdomp (al_assn arena_el_impl_assn :: _ \<Rightarrow> (32 word, 64) array_list \<Rightarrow> assn) a\<close>
  shows \<open>pos - 2 < max_unat 32\<close>
proof -
  obtain N vdom where
    \<open>valid_arena a N vdom\<close> and
    \<open>b \<in># dom_m N\<close>
    using assms(1) unfolding isa_update_pos_pre_def arena_is_valid_clause_idx_def
    by auto
  then have eq: \<open>length (N \<propto> b) = arena_length a b\<close> and
    le: \<open>b < length a\<close> and
    size: \<open>is_Size (a ! (b - SIZE_SHIFT))\<close>
    by (auto simp: arena_lifting)

  have \<open>i<length a \<Longrightarrow> rdomp arena_el_impl_assn (a ! i)\<close> for i
    using rdomp_al_dest'[OF assms(2)]
    by auto
  from this[of \<open>b - SIZE_SHIFT\<close>] have \<open>rdomp arena_el_impl_assn (a ! (b - SIZE_SHIFT))\<close>
    using le by auto
  then have \<open>length (N \<propto> b) \<le> uint32_max + 2\<close>
    using size eq unfolding rdomp_pure
    apply (auto simp: rdomp_def arena_el_impl_rel_def is_Size_def
       comp_def pure_def unat_rel_def unat.rel_def br_def
       arena_length_def uint32_max_def)
     subgoal for x
       using unat_lt_max_unat[of x]
       apply (auto simp: max_unat_def)
       done
    done
  then show ?thesis
    using assms POS_SHIFT_def
    unfolding isa_update_pos_pre_def
    by (auto simp: arena_is_valid_clause_idx_def arena_lifting eq
       uint32_max_def max_unat_def)
qed

sepref_register arena_update_pos
sepref_def update_pos_impl
  is \<open>uncurry2 (RETURN ooo arena_update_pos)\<close>
    :: \<open>[isa_update_pos_pre]\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>d  \<rightarrow> arena_fast_assn\<close>
  unfolding arena_update_pos_def POS_SHIFT_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  apply (rewrite at \<open>APos \<hole>\<close> annot_snat_unat_downcast[where 'l=32])
  supply [simp] = update_posI and [dest] = update_posI2
  by sepref


sepref_register IRRED LEARNED DELETED
lemma IRRED_impl[sepref_import_param]: \<open>(0,IRRED) \<in> status_impl_rel\<close>
  unfolding status_impl_rel_def status_rel_def unat_rel_def unat.rel_def
  by (auto simp: in_br_conv)

lemma LEARNED_impl[sepref_import_param]: \<open>(1,LEARNED) \<in> status_impl_rel\<close>
  unfolding status_impl_rel_def status_rel_def unat_rel_def unat.rel_def
  by (auto simp: in_br_conv)

lemma DELETED_impl[sepref_import_param]: \<open>(3,DELETED) \<in> status_impl_rel\<close>
  unfolding status_impl_rel_def status_rel_def unat_rel_def unat.rel_def
  by (auto simp: in_br_conv)


lemma mark_garbageI:
  assumes \<open>mark_garbage_pre (a, b)\<close>
  shows \<open>4 \<le> b\<close> \<open>b-4 < length a\<close>
  using assms STATUS_SHIFT_def
  unfolding mark_garbage_pre_def
  apply (auto simp: arena_is_valid_clause_idx_def arena_lifting)
  apply (metis (full_types) arena_dom_status_iff(5) insertCI valid_arena_extra_information_mark_to_delete)
  by (simp add: less_imp_diff_less valid_arena_def)

sepref_register extra_information_mark_to_delete
sepref_def mark_garbage_impl is \<open>uncurry (RETURN oo extra_information_mark_to_delete)\<close>
  :: \<open>[mark_garbage_pre]\<^sub>a arena_fast_assn\<^sup>d *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> arena_fast_assn\<close>
  unfolding extra_information_mark_to_delete_def STATUS_SHIFT_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  supply [simp] = mark_garbageI
  by sepref



paragraph \<open>Activity\<close>

lemma arena_act_implI:
  assumes \<open>arena_act_pre a b\<close>
  shows \<open>3 \<le> b\<close> \<open>b - 3 < length a\<close> \<open>is_Act (a ! (b-3))\<close>
  using assms ACTIVITY_SHIFT_def
  apply (auto simp: arena_act_pre_def arena_is_valid_clause_idx_def arena_lifting)
  by (simp add: less_imp_diff_less valid_arena_def)

sepref_register arena_act
sepref_def arena_act_impl
  is \<open>uncurry (RETURN oo arena_act)\<close>
    :: \<open>[uncurry arena_act_pre]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  supply [intro] = arena_act_implI
  unfolding arena_act_def ACTIVITY_SHIFT_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref



paragraph \<open>Increment Activity\<close>

context begin

interpretation llvm_prim_arith_setup .

sepref_register op_incr_mod32
lemma op_incr_mod32_hnr[sepref_fr_rules]:
  \<open>(\<lambda>x. ll_add x 1, RETURN o op_incr_mod32) \<in> uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding unat_rel_def unat.rel_def
  apply sepref_to_hoare
  apply (simp add: in_br_conv)
  apply vcg'
  unfolding op_incr_mod32_def
  by (simp add: unat_word_ariths)

end

sepref_register arena_incr_act
sepref_def arena_incr_act_impl is \<open>uncurry (RETURN oo arena_incr_act)\<close>
  :: \<open>[uncurry arena_act_pre]\<^sub>a arena_fast_assn\<^sup>d *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> arena_fast_assn\<close>
  unfolding arena_incr_act_def ACTIVITY_SHIFT_def
  supply [intro] = arena_act_implI
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_register arena_decr_act
sepref_def arena_decr_act_impl is \<open>uncurry (RETURN oo arena_decr_act)\<close>
  :: \<open>[uncurry arena_act_pre]\<^sub>a arena_fast_assn\<^sup>d *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> arena_fast_assn\<close>
  unfolding arena_decr_act_def ACTIVITY_SHIFT_def
  supply [intro] = arena_act_implI
  apply (rewrite at \<open>_ div \<hole>\<close>  unat_const_fold[where 'a=32])
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref


paragraph \<open>Mark used\<close>

term mark_used

lemma arena_mark_used_implI:
  assumes \<open>arena_act_pre a b\<close>
  shows \<open>4 \<le> b\<close> \<open>b - 4 < length a\<close> \<open>is_Status (a ! (b-4))\<close>
  using assms STATUS_SHIFT_def
  apply (auto simp: arena_act_pre_def arena_is_valid_clause_idx_def arena_lifting)
  subgoal by (metis (full_types) arena_is_valid_clause_vdom_def arena_status_implI(1) insertCI valid_arena_extra_information_mark_to_delete)
  subgoal by (simp add: less_imp_diff_less valid_arena_def)
  done

(* TODO: Wrong name for precondition! *)
sepref_register mark_used
sepref_def mark_used_impl is \<open>uncurry (RETURN oo mark_used)\<close>
  :: \<open>[uncurry arena_act_pre]\<^sub>a arena_fast_assn\<^sup>d *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> arena_fast_assn\<close>
  unfolding mark_used_def STATUS_SHIFT_def
  supply [intro] = arena_mark_used_implI
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_register mark_unused
sepref_def mark_unused_impl is \<open>uncurry (RETURN oo mark_unused)\<close>
  :: \<open>[uncurry arena_act_pre]\<^sub>a arena_fast_assn\<^sup>d *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> arena_fast_assn\<close>
  unfolding mark_unused_def STATUS_SHIFT_def
  supply [intro] = arena_mark_used_implI
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref



paragraph \<open>Marked as used?\<close>

lemma arena_marked_as_used_implI:
  assumes \<open>marked_as_used_pre a b\<close>
  shows \<open>4 \<le> b\<close> \<open>b - 4 < length a\<close> \<open>is_Status (a ! (b-4))\<close>
  using assms STATUS_SHIFT_def
  apply (auto simp: marked_as_used_pre_def arena_is_valid_clause_idx_def arena_lifting)
  subgoal by (metis (full_types) arena_is_valid_clause_vdom_def arena_status_implI(1) insertCI valid_arena_extra_information_mark_to_delete)
  subgoal by (simp add: less_imp_diff_less valid_arena_def)
  done

sepref_register marked_as_used
sepref_def marked_as_used_impl
  is \<open>uncurry (RETURN oo marked_as_used)\<close>
    :: \<open>[uncurry marked_as_used_pre]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> bool1_assn\<close>
  supply [intro] = arena_marked_as_used_implI
  unfolding marked_as_used_def STATUS_SHIFT_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_register MAX_LENGTH_SHORT_CLAUSE
sepref_def MAX_LENGTH_SHORT_CLAUSE_impl is \<open>uncurry0 (RETURN MAX_LENGTH_SHORT_CLAUSE)\<close> :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  unfolding MAX_LENGTH_SHORT_CLAUSE_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref


definition arena_other_watched_as_swap :: \<open>nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat nres\<close> where
\<open>arena_other_watched_as_swap S L C i = do {
    ASSERT(i < 2 \<and>
      C + i < length S \<and>
      C < length S \<and>
      (C + 1) < length S);
    K \<leftarrow> RETURN (S ! C);
    K' \<leftarrow> RETURN (S ! (1 + C));
    RETURN (L XOR K XOR K')
  }\<close>

lemma arena_other_watched_as_swap_arena_other_watched:
  assumes
    N: \<open>(N, N') \<in> \<langle>arena_el_rel\<rangle>list_rel\<close> and
    L: \<open>(L, L') \<in> nat_lit_rel\<close> and
    C: \<open>(C, C') \<in> nat_rel\<close> and
    i: \<open>(i, i') \<in> nat_rel\<close>
  shows
    \<open>arena_other_watched_as_swap N L C i \<le> \<Down>nat_lit_rel
        (arena_other_watched N' L' C' i')\<close>
proof -
   have eq: \<open>i =i'\<close> \<open>C=C'\<close>
     using assms by auto
   have A: \<open>Pos (L div 2) = A \<Longrightarrow> even L \<Longrightarrow> L = 2 * atm_of A\<close> for A :: \<open>nat literal\<close>
     by (cases A)
      auto
   have Ci: \<open>(C' + i', C' + i') \<in> nat_rel\<close>
     unfolding eq by auto
   have [simp]: \<open>L = N ! (C+i)\<close> if \<open>L' = arena_lit N' (C' + i')\<close> \<open>C' + i' < length N'\<close>
     \<open>arena_lit_pre2 N' C i\<close>
     using that param_nth[OF that(2) Ci N] C i L
     unfolding arena_lit_pre2_def
     apply - apply normalize_goal+
     subgoal for N'' vdom
       using arena_lifting(6)[of N' N'' vdom C i] A[of \<open>arena_lit N' (C' + i')\<close>]
       apply (simp only: list_rel_imp_same_length[of N] eq)
     apply (cases \<open>N' ! (C' + i')\<close>; cases \<open>arena_lit N' (C' + i')\<close>)
     apply (simp_all add: eq nat_lit_rel_def br_def)
     apply (auto split: if_splits simp: eq_commute[of _ \<open>Pos (L div 2)\<close>]
       eq_commute[of _ \<open>ALit (Pos (_ div 2))\<close>] arena_lit_def)
     using div2_even_ext_nat by blast
    done
   have [simp]: \<open>N ! (C' + i') XOR N ! C' XOR N ! Suc C' = N ! (C' + (Suc 0 - i))\<close> if \<open>i < 2\<close>
     using that i
     by (cases i; cases \<open>i-1\<close>)
      (auto simp: bin_pos_same_XOR3_nat)
  have Ci': \<open>(C' + (1 - i'), C' + (1 - i')) \<in> nat_rel\<close>
    unfolding eq by auto

  have [intro!]: \<open>(N ! (Suc C' - i'), arena_lit N' (Suc C' - i')) \<in> nat_lit_rel\<close>
     if \<open>arena_lit_pre2 N' C i\<close> \<open>i < 2\<close>
     using that param_nth[OF _ Ci' N]
     unfolding arena_lit_pre2_def
     apply - apply normalize_goal+
     apply (subgoal_tac \<open>C' + (Suc 0 - i') < length N'\<close>)
     defer
       subgoal for N'' vdom
       using
         arena_lifting(7)[of N' N'' vdom C i]
        apply (auto simp: arena_lit_pre2_def list_rel_imp_same_length[of N]
          simp del: arena_el_rel_def)
        by (metis add.right_neutral add_Suc add_diff_cancel_left' arena_lifting(22) arena_lifting(4) arena_lifting(7) eq(1) eq(2) less_2_cases less_Suc_eq not_less_eq plus_1_eq_Suc)
     apply (subgoal_tac \<open>(Suc 0 - i') < length (x \<propto> C)\<close>)
     defer
     subgoal for N'' vdom
       using
         arena_lifting(7)[of N' N'' vdom C i]
       by (auto simp: arena_lit_pre2_def list_rel_imp_same_length[of N]
          arena_lifting(22) arena_lifting(4) less_imp_diff_less
          simp del: arena_el_rel_def)
     subgoal for N'' vdom
       using
         arena_lifting(6)[of N' N'' vdom C \<open>Suc 0 - i\<close>]
       by (cases \<open>N' ! (C' + (Suc 0 - i'))\<close>)
        (auto simp: arena_lit_pre2_def list_rel_imp_same_length[of N] eq
          arena_lit_def arena_lifting)
     done
   show ?thesis
     using assms
     unfolding arena_other_watched_as_swap_def arena_other_watched_def
       le_ASSERT_iff mop_arena_lit2_def
     apply (refine_vcg)
     apply (auto simp: le_ASSERT_iff list_rel_imp_same_length arena_lit_pre2_def
       arena_lifting
       bin_pos_same_XOR3_nat)
     using arena_lifting(22) arena_lifting(4) arena_lifting(7) apply fastforce
     using arena_lifting(22) arena_lifting(4) arena_lifting(7) arena_lit_pre2_def apply fastforce
     done
qed


sepref_def arena_other_watched_as_swap_impl
  is \<open>uncurry3 arena_other_watched_as_swap\<close>
  :: \<open>(al_assn' (TYPE(64)) uint32_nat_assn)\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a
       sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply[[goals_limit=1]]
  unfolding arena_other_watched_as_swap_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

lemma arena_other_watched_as_swap_arena_other_watched':
  \<open>(arena_other_watched_as_swap, arena_other_watched) \<in>
     \<langle>arena_el_rel\<rangle>list_rel \<rightarrow> nat_lit_rel \<rightarrow> nat_rel \<rightarrow> nat_rel \<rightarrow>
      \<langle>nat_lit_rel\<rangle>nres_rel\<close>
  apply (intro fun_relI nres_relI)
  using arena_other_watched_as_swap_arena_other_watched
  by blast

lemma arena_fast_al_unat_assn:
  \<open>hr_comp (al_assn unat_assn) (\<langle>arena_el_rel\<rangle>list_rel) = arena_fast_assn\<close>
  unfolding al_assn_def hr_comp_assoc
  by (auto simp: arena_el_impl_rel_def list_rel_compp)

lemmas [sepref_fr_rules] =
  arena_other_watched_as_swap_impl.refine[FCOMP arena_other_watched_as_swap_arena_other_watched',
    unfolded arena_fast_al_unat_assn]

end

sepref_def mop_arena_length_impl
  is \<open>uncurry mop_arena_length\<close>
  :: \<open>arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  unfolding mop_arena_length_def
  by sepref

experiment begin
export_llvm
  arena_length_impl
  arena_lit_impl
  arena_status_impl
  swap_lits_impl
  arena_lbd_impl
  arena_pos_impl
  update_lbd_impl
  update_pos_impl
  mark_garbage_impl
  arena_act_impl
  arena_incr_act_impl
  arena_decr_act_impl
  mark_used_impl
  mark_unused_impl
  marked_as_used_impl
  MAX_LENGTH_SHORT_CLAUSE_impl

end

end
