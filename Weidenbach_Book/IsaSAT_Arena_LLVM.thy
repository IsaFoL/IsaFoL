theory IsaSAT_Arena_LLVM
  imports IsaSAT_Arena IsaSAT_Literals_LLVM
begin
no_notation WB_More_Refinement.fref ("[_]\<^sub>f _ \<rightarrow> _" [0,60,60] 60)
no_notation WB_More_Refinement.freft ("_ \<rightarrow>\<^sub>f _" [60,60] 60)


subsubsection \<open>Code Generation\<close>


term arena_el_rel

term xarena_length

definition "arena_el_impl_rel \<equiv> unat_rel' TYPE(32) O arena_el_rel"
lemmas [fcomp_norm_unfold] = arena_el_impl_rel_def[symmetric]

abbreviation "arena_el_impl_assn \<equiv> pure arena_el_impl_rel"

lemma xarena_length_refine1: "(\<lambda>eli. eli, xarena_length) \<in> [is_Size]\<^sub>f arena_el_rel \<rightarrow> nat_rel"
  by (auto intro!: frefI simp: arena_el_rel_def split: arena_el.splits)

sepref_definition xarena_len_impl is "RETURN o (\<lambda>eli. eli)" :: "uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn"
  by sepref
  
lemmas [sepref_fr_rules] = xarena_len_impl.refine[FCOMP xarena_length_refine1]  
  
abbreviation "arena_assn \<equiv> al_assn' TYPE(64) arena_el_impl_assn"


lemma arena_lifting': 
  assumes "arena_is_valid_clause_idx a b"
  shows "Suc 0 \<le> b"
  and "b < length a"
  and "is_Size (a ! (b - Suc 0))"
  using SIZE_SHIFT_def assms
  by (auto simp: arena_is_valid_clause_idx_def arena_lifting)

(* TODO: Let monadify-phase do this automatically? trade-of: goal-size vs. lost information *) 
lemma protected_bind_assoc: "Refine_Basic.bind$(Refine_Basic.bind$m$(\<lambda>\<^sub>2x. f x))$(\<lambda>\<^sub>2y. g y) = Refine_Basic.bind$m$(\<lambda>\<^sub>2x. Refine_Basic.bind$(f x)$(\<lambda>\<^sub>2y. g y))" by simp
  
lemma arena_length_impl_bounds_aux1: 
  "(ac, a) \<in> unat_rel' TYPE(32) \<Longrightarrow> a < 9223372036854775806"
  by (auto dest!: in_unat_rel_imp_less_max' simp: max_unat_def)

lemma arena_length_alt: 
  \<open>arena_length arena i = (
    let l = xarena_length (arena!(i - snat_const TYPE(64) 1)) 
    in snat_const TYPE(64) 2 + op_unat_snat_upcast TYPE(64) l)\<close>
  by (simp add: arena_length_def SIZE_SHIFT_def)  
  
  
sepref_definition arena_length_impl 
  is "uncurry (RETURN oo arena_length)" 
    :: "[uncurry arena_is_valid_clause_idx]\<^sub>a arena_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> snat_assn' TYPE(64)"
  unfolding arena_length_alt
  supply [simp] = max_snat_def max_unat_def arena_length_impl_bounds_aux1
    and [dest] = arena_lifting'
  by sepref
  


paragraph \<open>Literal at given position\<close>


lemma xarena_lit_refine1: "(\<lambda>eli. eli, xarena_lit) \<in> [is_Lit]\<^sub>f arena_el_rel \<rightarrow> nat_lit_rel"
  by (auto intro!: frefI simp: arena_el_rel_def split: arena_el.splits)

sepref_definition xarena_lit_impl is "RETURN o (\<lambda>eli. eli)" :: "uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn"
  by sepref

lemmas [sepref_fr_rules] = xarena_lit_impl.refine[FCOMP xarena_lit_refine1]  

lemma arena_lit_implI:
  assumes "arena_lit_pre a b"
  shows "b < length a" "is_Lit (a ! b)"
  using assms unfolding arena_lit_pre_def arena_is_valid_clause_idx_and_access_def
  by (fastforce dest: arena_lifting)+

sepref_register arena_lit xarena_lit
sepref_definition arena_lit_impl 
  is "uncurry (RETURN oo arena_lit)" 
    :: "[uncurry arena_lit_pre]\<^sub>a arena_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> unat_lit_assn"
  supply [intro] = arena_lit_implI
  unfolding arena_lit_def
  by sepref


      
paragraph \<open>Status of the clause\<close>

definition "status_impl_rel \<equiv>unat_rel' TYPE(32) O status_rel"
lemmas [fcomp_norm_unfold] = status_impl_rel_def[symmetric]
abbreviation "status_impl_assn \<equiv> pure status_impl_rel"

term arena_el_rel
lemma xarena_status_refine1: "(\<lambda>eli. eli AND 0b11, xarena_status) \<in> [is_Status]\<^sub>f arena_el_rel \<rightarrow> status_rel"
  by (auto intro!: frefI simp: arena_el_rel_def is_Status_def split: arena_el.split)

sepref_definition xarena_status_impl is "RETURN o (\<lambda>eli. eli AND 0b11)" :: "uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn"
  apply (annot_unat_const "TYPE(32)")
  supply [simp] = max_unat_def
  by sepref

lemmas [sepref_fr_rules] = xarena_status_impl.refine[FCOMP xarena_status_refine1]  

lemma arena_status_implI:
  assumes "arena_is_valid_clause_vdom a b"
  shows "4 \<le> b" "b - 4 < length a" "is_Status (a ! (b-4))"
  using assms STATUS_SHIFT_def arena_dom_status_iff
  unfolding arena_is_valid_clause_vdom_def
  by (auto dest: valid_arena_in_vdom_le_arena)

sepref_register arena_status xarena_status
sepref_definition arena_status_impl 
  is "uncurry (RETURN oo arena_status)" 
    :: "[uncurry arena_is_valid_clause_vdom]\<^sub>a arena_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> status_impl_assn"
  supply [intro] = arena_status_implI
  supply [simp] = max_snat_def
  unfolding arena_status_def STATUS_SHIFT_def
  apply (annot_snat_const "TYPE(64)")
  by sepref





paragraph \<open>Swap literals\<close>

(* TODO: Move
  TODO: Should be generic algorithm!
*)  
lemma mop_list_swap_unfold: "mop_list_swap xs i j = do {
  xi \<leftarrow> mop_list_get xs i;
  xj \<leftarrow> mop_list_get xs j;
  xs \<leftarrow> mop_list_set xs i xj;
  mop_list_set xs j xi
}"
  by (auto simp: pw_eq_iff refine_pw_simps swap_def)

lemma swap_unfold: "swap xs i j = (let
  xi = op_list_get xs i;
  xj = op_list_get xs j;
  xs = op_list_set xs i xj;
  xs = op_list_set xs j xi 
  in xs)"
  by (auto simp: swap_def)

lemma convert_swap: "WB_More_Refinement_List.swap = IICF_List.swap"
  unfolding WB_More_Refinement_List.swap_def IICF_List.swap_def ..

sepref_definition swap_lits_impl is "uncurry3 (RETURN oooo swap_lits)"
  :: "[\<lambda>(((C,i),j),arena). C + i < length arena \<and> C + j < length arena]\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a arena_assn\<^sup>d \<rightarrow> arena_assn"
  unfolding swap_lits_def convert_swap
  supply [dest] = rdomp_al_imp_len_bound
  unfolding swap_unfold
  by sepref

paragraph \<open>Get LBD\<close>

lemma xarena_lbd_refine1: "(\<lambda>eli. eli, xarena_lbd) \<in> [is_LBD]\<^sub>f arena_el_rel \<rightarrow> nat_rel"
  by (auto intro!: frefI simp: arena_el_rel_def split: arena_el.splits)

sepref_definition xarena_lbd_impl is "RETURN o (\<lambda>eli. eli)" :: "uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn"
  by sepref

lemmas [sepref_fr_rules] = xarena_len_impl.refine[FCOMP xarena_lbd_refine1]

lemma get_clause_LBD_preI:
  assumes "get_clause_LBD_pre a b"
  shows "2 \<le> b"
  and "b < length a"
  and "is_LBD (a ! (b - 2))"
  using LBD_SHIFT_def assms
  by (auto simp: get_clause_LBD_pre_def arena_is_valid_clause_idx_def arena_lifting)

definition get_clause_LBD :: \<open>arena \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>get_clause_LBD arena C =  xarena_lbd (arena ! (C - LBD_SHIFT))\<close>

sepref_definition arena_lbd_impl
  is "uncurry (RETURN oo get_clause_LBD)"
    :: "[uncurry get_clause_LBD_pre]\<^sub>a arena_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>uint32_nat_assn"
  unfolding get_clause_LBD_def LBD_SHIFT_def
  supply [simp] = max_snat_def max_unat_def
    and [dest] = get_clause_LBD_preI
  apply (annot_snat_const "TYPE(64)")
  by sepref

paragraph \<open>Get LBD\<close>

lemma xarena_pos_refine1: "(\<lambda>eli. eli, xarena_pos) \<in> [is_Pos]\<^sub>f arena_el_rel \<rightarrow> nat_rel"
  by (auto intro!: frefI simp: arena_el_rel_def split: arena_el.splits)

sepref_definition xarena_pos_impl is "RETURN o (\<lambda>eli. eli)" :: "uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn"
  by sepref

lemmas [sepref_fr_rules] = xarena_len_impl.refine[FCOMP xarena_pos_refine1]

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


sepref_definition arena_pos_impl 
  is "uncurry (RETURN oo arena_pos)" 
    :: "[uncurry get_saved_pos_pre]\<^sub>a arena_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> snat_assn' TYPE(64)"
  unfolding arena_pos_alt
  supply [simp] = max_snat_def max_unat_def arena_length_impl_bounds_aux1
    and [dest] = arena_posI
  by sepref

paragraph \<open>Update LBD\<close>

lemma ALBD_refine1: "(\<lambda>eli. eli, ALBD) \<in> nat_rel \<rightarrow> arena_el_rel"
  by (auto intro!: frefI simp: arena_el_rel_def split: arena_el.splits)

sepref_definition xarena_ALBD_impl is "RETURN o (\<lambda>eli. eli)" :: "uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn"
  by sepref

lemmas [sepref_fr_rules] = xarena_ALBD_impl.refine[FCOMP ALBD_refine1]

lemma update_lbdI:
  assumes "update_lbd_pre ((b, lbd), a)"
  shows "2 \<le> b"
  and "b -2 < length a"
  using LBD_SHIFT_def assms
  apply (auto simp: arena_is_valid_clause_idx_def arena_lifting update_lbd_pre_def
    dest: arena_lifting(10))
  by (simp add: less_imp_diff_less valid_arena_def)

(* TODO: Let monadify-phase do this automatically? trade-of: goal-size vs. lost information *) 

sepref_definition update_lbd_impl 
  is "uncurry2 (RETURN ooo update_lbd)" 
    :: "[update_lbd_pre]\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a arena_assn\<^sup>d  \<rightarrow> arena_assn"
  unfolding update_lbd_def LBD_SHIFT_def
  supply [simp] = max_snat_def max_unat_def arena_length_impl_bounds_aux1 update_lbdI
    and [dest] = arena_posI
  apply (annot_snat_const "TYPE(64)")
  by sepref

paragraph \<open>Update Saved Position\<close>

(* TODO: converting from nat to uint32 is a little stupid and always useless (uint64 is enough everytime) *)
definition isa_update_pos :: \<open>nat \<Rightarrow> nat \<Rightarrow> uint32 list \<Rightarrow> uint32 list nres\<close> where
  \<open>isa_update_pos C n arena = do {
      ASSERT(C - POS_SHIFT < length arena \<and> C \<ge> POS_SHIFT \<and> n \<ge> 2 \<and> n - 2 \<le> uint32_max);
      RETURN (arena [C - POS_SHIFT := (uint32_of_nat (n - 2))])
  }\<close>

definition arena_update_pos where
  \<open>arena_update_pos C pos arena = arena[C - POS_SHIFT := APos (pos - 2)]\<close>

lemma arena_update_pos_alt_def:
  \<open>arena_update_pos C i N = update_pos_direct C (i - 2) N\<close>
  by (auto simp: arena_update_pos_def update_pos_direct_def)

lemma arena_update_pos_conv:
  assumes
    valid: \<open>valid_arena arena N x\<close> and
    j: \<open>j \<in># dom_m N\<close> and
    a: \<open>(a, arena) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close> and
    length: \<open>arena_length arena j > MAX_LENGTH_SHORT_CLAUSE\<close> and
    pos_le: \<open>pos \<le> arena_length arena j\<close> and
    b': \<open>pos \<ge> 2\<close>
  shows
    \<open>j - POS_SHIFT < length arena\<close> (is ?le) and
    \<open>j \<ge> POS_SHIFT\<close> (is ?ge)
    \<open>(a[j - POS_SHIFT := uint32_of_nat (pos - 2)], arena_update_pos j pos arena) \<in>
      \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close> (is ?unat) and
    \<open>pos - 2 \<le> uint32_max\<close>
proof -
  have j_le: \<open>j < length arena\<close> and
    length: \<open>length (N \<propto> j) = arena_length arena j\<close> and
    k1:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> N \<propto> j ! k = arena_lit arena (j + k)\<close> and
    k2:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> is_Lit (arena ! (j+k))\<close> and
    le: \<open>j + length (N \<propto> j) \<le> length arena\<close>  and
    j_ge: \<open>header_size (N \<propto> j) \<le> j\<close> and
    long: \<open>is_long_clause (N \<propto> j)\<close> and
    pos: \<open>is_Pos (arena ! (j - POS_SHIFT))\<close> and
    is_size: \<open>is_Size (arena ! (j - SIZE_SHIFT))\<close>
    using arena_lifting[OF valid j] length by (auto simp: is_short_clause_def header_size_def)
  show le': ?le and ?ge
    using le j_ge long unfolding length[symmetric] header_size_def
    by (auto split: if_splits simp: POS_SHIFT_def)
  have
    \<open>(a ! (j - SIZE_SHIFT),
         (arena ! (j - SIZE_SHIFT)))
       \<in> uint32_nat_rel O arena_el_rel\<close>
    by (rule param_nth[OF _ _ a]) (use j_le in auto)
  then show \<open>pos - 2 \<le> uint32_max\<close>
    using b' length is_size pos_le nat_of_uint32_le_uint32_max[of \<open>a ! (j - SIZE_SHIFT)\<close>]
    by (cases \<open>arena ! (j - SIZE_SHIFT)\<close>)
      (auto simp: uint32_nat_rel_def br_def arena_el_rel_def arena_length_def)
  then show ?unat
    using length a pos b'
      valid_arena_update_pos[OF valid j \<open>is_long_clause (N \<propto> j)\<close> ]
    by (auto simp: arena_el_rel_def unat_lit_rel_def arena_lit_def arena_update_pos_def
        uint32_nat_rel_def br_def Collect_eq_comp nat_of_uint32_notle_minus
        nat_of_uint32_uint32_of_nat_id
       split: arena_el.splits
       intro!: list_rel_update')
qed


lemma isa_update_pos:
  \<open>(uncurry2 isa_update_pos, uncurry2 (RETURN ooo arena_update_pos)) \<in>
    [isa_update_pos_pre]\<^sub>f
     nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel \<rightarrow>
    \<langle>\<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<rangle>nres_rel\<close>
  unfolding isa_arena_status_def arena_status_def
  by (intro frefI nres_relI)
    (auto simp: arena_is_valid_clause_idx_def uint64_nat_rel_def br_def two_uint64_def
        list_rel_imp_same_length arena_length_uint64_conv arena_lifting
        arena_is_valid_clause_idx_and_access_def arena_lbd_conv
        arena_is_valid_clause_vdom_def arena_status_literal_conv
        update_lbd_pre_def isa_update_pos_def update_pos_direct_def isa_update_pos_pre_def
        isa_arena_swap_def swap_lits_def swap_lits_pre_def isa_update_lbd_def
        arena_update_pos_conv
      intro!: ASSERT_refine_left)


paragraph \<open>Mark clause as garbage\<close>


definition mark_garbage where
  \<open>mark_garbage arena C = do {
    ASSERT(C \<ge> STATUS_SHIFT \<and> C - STATUS_SHIFT < length arena);
    RETURN (arena[C - STATUS_SHIFT := (3 :: uint32)])
  }\<close>

lemma mark_garbage_pre:
  assumes
    j: \<open>j \<in># dom_m N\<close> and
    valid: \<open>valid_arena arena N x\<close> and
    arena: \<open>(a, arena) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close>
  shows
    \<open>STATUS_SHIFT \<le> j\<close> (is ?ge) and
    \<open>(a[j - STATUS_SHIFT := 3], arena[j - STATUS_SHIFT := AStatus DELETED False])
         \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close> (is ?rel) and
    \<open>j - STATUS_SHIFT < length arena\<close> (is ?le)
proof -
  have j_le: \<open>j < length arena\<close> and
    length: \<open>length (N \<propto> j) = arena_length arena j\<close> and
    k1:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> N \<propto> j ! k = arena_lit arena (j + k)\<close> and
    k2:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> is_Lit (arena ! (j+k))\<close> and
    le: \<open>j + length (N \<propto> j) \<le> length arena\<close>  and
    j_ge: \<open>header_size (N \<propto> j) \<le> j\<close>
    using arena_lifting[OF valid j] by (auto simp: )
  show le': ?le
     using le j_ge unfolding length[symmetric] header_size_def
     by (auto split: if_splits simp: SHIFTS_def)

  show ?rel
     apply (rule list_rel_update'[OF arena])
     using length
     by
      (auto simp: arena_el_rel_def unat_lit_rel_def arena_lit_def update_lbd_def
        uint32_nat_rel_def br_def Collect_eq_comp status_rel_def bitfield_rel_def
       split: arena_el.splits
       intro!: )
  show ?ge
    using le j_ge unfolding length[symmetric] header_size_def
    by (auto split: if_splits simp: SHIFTS_def)
qed

lemma isa_mark_garbage:
  \<open>(uncurry mark_garbage, uncurry (RETURN oo extra_information_mark_to_delete)) \<in>
    [mark_garbage_pre]\<^sub>f
     \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel \<times>\<^sub>f nat_rel  \<rightarrow>
    \<langle>\<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<rangle>nres_rel\<close>
  unfolding isa_arena_status_def arena_status_def
  by (intro frefI nres_relI)
    (auto simp: arena_is_valid_clause_idx_def uint64_nat_rel_def br_def two_uint64_def
        list_rel_imp_same_length arena_length_uint64_conv arena_lifting
        arena_is_valid_clause_idx_and_access_def arena_lbd_conv
        arena_is_valid_clause_vdom_def arena_status_literal_conv mark_garbage_pre
        mark_garbage_def mark_garbage_pre_def extra_information_mark_to_delete_def
        isa_arena_swap_def swap_lits_def swap_lits_pre_def isa_update_lbd_def
      intro!: ASSERT_refine_left)


paragraph \<open>Activity\<close>


definition isa_arena_act :: \<open>uint32 list \<Rightarrow> nat \<Rightarrow> uint32 nres\<close> where
  \<open>isa_arena_act arena C = do {
      ASSERT(C - ACTIVITY_SHIFT < length arena \<and> C \<ge> ACTIVITY_SHIFT);
      RETURN (arena ! (C - ACTIVITY_SHIFT))
  }\<close>

lemma arena_act_conv:
  assumes
    valid: \<open>valid_arena arena N x\<close> and
    j: \<open>j \<in># dom_m N\<close> and
    a: \<open>(a, arena) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close>
  shows
    \<open>j - ACTIVITY_SHIFT < length arena\<close> (is ?le) and
    \<open>ACTIVITY_SHIFT \<le> j\<close> (is ?ge) and
    \<open>(a ! (j - ACTIVITY_SHIFT),
        xarena_act (arena ! (j - ACTIVITY_SHIFT)))
       \<in> uint32_nat_rel\<close>
proof -
  have j_le: \<open>j < length arena\<close> and
    length: \<open>length (N \<propto> j) = arena_length arena j\<close> and
    k1:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> N \<propto> j ! k = arena_lit arena (j + k)\<close> and
    k2:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> is_Lit (arena ! (j+k))\<close> and
    le: \<open>j + length (N \<propto> j) \<le> length arena\<close>  and
    j_ge: \<open>header_size (N \<propto> j) \<le> j\<close> and
    lbd: \<open>is_Act (arena ! (j - ACTIVITY_SHIFT))\<close>
    using arena_lifting[OF valid j] by auto
  show le': ?le
     using le j_ge unfolding length[symmetric] header_size_def
     by (auto split: if_splits simp: ACTIVITY_SHIFT_def)
  show ?ge
    using j_ge by (auto simp: SHIFTS_def header_size_def split: if_splits)
  have
    \<open>(a ! (j - ACTIVITY_SHIFT),
         (arena ! (j - ACTIVITY_SHIFT)))
       \<in> uint32_nat_rel O arena_el_rel\<close>
    by (rule param_nth[OF _ _ a]) (use j_le in auto)
  then show \<open>(a ! (j - ACTIVITY_SHIFT),
        xarena_act (arena ! (j - ACTIVITY_SHIFT)))
       \<in> uint32_nat_rel\<close>
    using lbd by (cases \<open>arena ! (j - ACTIVITY_SHIFT)\<close>) (auto simp: arena_el_rel_def)
qed

lemma isa_arena_act_arena_act:
  \<open>(uncurry isa_arena_act, uncurry (RETURN oo arena_act)) \<in>
    [uncurry arena_act_pre]\<^sub>f
     \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel \<times>\<^sub>f nat_rel \<rightarrow>
    \<langle>uint32_nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: isa_arena_act_def arena_act_def arena_get_lbd_conv
      arena_act_pre_def arena_is_valid_clause_idx_def
      list_rel_imp_same_length arena_act_conv
      intro!: ASSERT_leI)


paragraph \<open>Increment Activity\<close>

definition isa_arena_incr_act :: \<open>uint32 list \<Rightarrow> nat \<Rightarrow> uint32 list nres\<close> where
  \<open>isa_arena_incr_act arena C = do {
      ASSERT(C - ACTIVITY_SHIFT < length arena \<and> C \<ge> ACTIVITY_SHIFT);
      let act = arena ! (C - ACTIVITY_SHIFT);
      RETURN (arena[C - ACTIVITY_SHIFT := act + 1])
  }\<close>

definition arena_incr_act where
  \<open>arena_incr_act arena i = arena[i - ACTIVITY_SHIFT := AActivity (sum_mod_uint32_max 1 (xarena_act (arena!(i - ACTIVITY_SHIFT))))]\<close>

lemma arena_incr_act_conv:
  assumes
    valid: \<open>valid_arena arena N x\<close> and
    j: \<open>j \<in># dom_m N\<close> and
    a: \<open>(a, arena) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close>
  shows
    \<open>j - ACTIVITY_SHIFT < length arena\<close> (is ?le) and
    \<open>ACTIVITY_SHIFT \<le> j\<close> (is ?ge) and
    \<open>(a[j - ACTIVITY_SHIFT := a ! (j - ACTIVITY_SHIFT) + 1], arena_incr_act arena j) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close>
proof -
  have j_le: \<open>j < length arena\<close> and
    length: \<open>length (N \<propto> j) = arena_length arena j\<close> and
    k1:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> N \<propto> j ! k = arena_lit arena (j + k)\<close> and
    k2:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> is_Lit (arena ! (j+k))\<close> and
    le: \<open>j + length (N \<propto> j) \<le> length arena\<close>  and
    j_ge: \<open>header_size (N \<propto> j) \<le> j\<close> and
    lbd: \<open>is_Act (arena ! (j - ACTIVITY_SHIFT))\<close>
    using arena_lifting[OF valid j] by auto
  show le': ?le
     using le j_ge unfolding length[symmetric] header_size_def
     by (auto split: if_splits simp: ACTIVITY_SHIFT_def)
  show ?ge
    using j_ge by (auto simp: SHIFTS_def header_size_def split: if_splits)
  have b:
    \<open>(a ! (j - ACTIVITY_SHIFT),
         (arena ! (j - ACTIVITY_SHIFT)))
       \<in> uint32_nat_rel O arena_el_rel\<close>
    by (rule param_nth[OF _ _ a]) (use j_le in auto)
  show \<open>(a[j - ACTIVITY_SHIFT := a ! (j - ACTIVITY_SHIFT) + 1], arena_incr_act arena j) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close>
    unfolding arena_incr_act_def
    by (rule list_rel_update'[OF a])
      (cases \<open>arena ! (j - ACTIVITY_SHIFT)\<close>;
      use lbd b in \<open>auto simp add: uint32_nat_rel_def br_def arena_el_rel_def
        Collect_eq_comp sum_mod_uint32_max_def nat_of_uint32_plus\<close>)
qed


lemma isa_arena_incr_act_arena_incr_act:
  \<open>(uncurry isa_arena_incr_act, uncurry (RETURN oo arena_incr_act)) \<in>
    [uncurry arena_act_pre]\<^sub>f
     \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel \<times>\<^sub>f nat_rel \<rightarrow>
    \<langle> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
   (auto simp: isa_arena_incr_act_def arena_act_def arena_get_lbd_conv
      arena_act_pre_def arena_is_valid_clause_idx_def arena_incr_act_conv
      list_rel_imp_same_length arena_act_conv
      intro!: ASSERT_leI)

lemma length_arena_incr_act[simp]:
  \<open>length (arena_incr_act arena C) = length arena\<close>
  by (auto simp: arena_incr_act_def)

lemma valid_arena_arena_incr_act:
  assumes C: \<open>C \<in># dom_m N\<close> and valid: \<open>valid_arena arena N vdom\<close>
  shows
   \<open>valid_arena (arena_incr_act arena C) N vdom\<close>
proof -
  let ?arena = \<open>arena_incr_act arena C\<close>
  have act: \<open>\<forall>i\<in>#dom_m N.
     i < length (arena) \<and>
     header_size (N \<propto> i) \<le> i \<and>
     xarena_active_clause (clause_slice arena N i)
      (the (fmlookup N i))\<close> and
    dead: \<open>\<And>i. i \<in> vdom \<Longrightarrow> i \<notin># dom_m N \<Longrightarrow> i < length arena \<and>
           4 \<le> i \<and> arena_dead_clause (Misc.slice (i - 4) i arena)\<close> and
    C_ge: \<open>header_size (N \<propto> C) \<le> C\<close> and
    C_le: \<open>C < length arena\<close> and
    C_act: \<open>xarena_active_clause (clause_slice arena N C)
      (the (fmlookup N C))\<close>
    using assms
    by (auto simp: valid_arena_def)
  have
   [simp]: \<open>clause_slice ?arena N C ! (header_size (N \<propto> C) - LBD_SHIFT) =
           clause_slice arena N C ! (header_size (N \<propto> C) - LBD_SHIFT)\<close> and
   [simp]: \<open>clause_slice ?arena N C ! (header_size (N \<propto> C) - STATUS_SHIFT) =
           clause_slice arena N C ! (header_size (N \<propto> C) - STATUS_SHIFT)\<close> and
   [simp]: \<open>clause_slice ?arena N C ! (header_size (N \<propto> C) - SIZE_SHIFT) =
           clause_slice arena N C ! (header_size (N \<propto> C) - SIZE_SHIFT)\<close> and
   [simp]: \<open>is_long_clause (N \<propto> C) \<Longrightarrow> clause_slice ?arena N C ! (header_size (N \<propto> C) - POS_SHIFT) =
           clause_slice arena N C ! (header_size (N \<propto> C) - POS_SHIFT)\<close> and
   [simp]: \<open>length (clause_slice  ?arena N C) = length (clause_slice arena N C)\<close> and
   [simp]: \<open>is_Act (clause_slice ?arena N C ! (header_size (N \<propto> C) - ACTIVITY_SHIFT))\<close> and
   [simp]: \<open>Misc.slice C (C + length (N \<propto> C)) ?arena =
     Misc.slice C (C + length (N \<propto> C)) arena\<close>
    using C_le C_ge unfolding SHIFTS_def arena_incr_act_def header_size_def
    by (auto simp: Misc.slice_def drop_update_swap split: if_splits)

  have \<open>xarena_active_clause (clause_slice ?arena N C) (the (fmlookup N C))\<close>
    using C_act C_le C_ge unfolding xarena_active_clause_alt_def
    by simp

  then have 1: \<open>xarena_active_clause (clause_slice arena N i) (the (fmlookup N i)) \<Longrightarrow>
     xarena_active_clause (clause_slice (arena_incr_act arena C) N i) (the (fmlookup N i))\<close>
    if \<open>i \<in># dom_m N\<close>
    for i
    using minimal_difference_between_valid_index[of N arena C i, OF act]
      minimal_difference_between_valid_index[of N arena i C, OF act] assms
      that C_ge
    by (cases \<open>C < i\<close>; cases \<open>C > i\<close>)
      (auto simp: arena_incr_act_def header_size_def ACTIVITY_SHIFT_def
      split: if_splits)

  have 2:
    \<open>arena_dead_clause (Misc.slice (i - 4) i ?arena)\<close>
    if \<open>i \<in> vdom\<close>\<open>i \<notin># dom_m N\<close>\<open>arena_dead_clause (Misc.slice (i - 4) i arena)\<close>
    for i
  proof -
    have i_ge: \<open>i \<ge> 4\<close> \<open>i < length arena\<close>
      using that valid unfolding valid_arena_def
      by auto
    show ?thesis
      using dead[of i] that C_le C_ge
      minimal_difference_between_invalid_index[OF valid, of C i]
      minimal_difference_between_invalid_index2[OF valid, of C i]
      by (cases \<open>C < i\<close>; cases \<open>C > i\<close>)
        (auto simp: arena_incr_act_def header_size_def ACTIVITY_SHIFT_def C
          split: if_splits)
  qed
  show ?thesis
    using 1 2 valid
    by (auto simp: valid_arena_def)
qed


paragraph \<open>Divide activity by two\<close>

definition isa_arena_decr_act :: \<open>uint32 list \<Rightarrow> nat \<Rightarrow> uint32 list nres\<close> where
  \<open>isa_arena_decr_act arena C = do {
      ASSERT(C - ACTIVITY_SHIFT < length arena \<and> C \<ge> ACTIVITY_SHIFT);
      let act = arena ! (C - ACTIVITY_SHIFT);
      RETURN (arena[C - ACTIVITY_SHIFT := (act >> 1)])
  }\<close>

lemma arena_decr_act_conv:
  assumes
    valid: \<open>valid_arena arena N x\<close> and
    j: \<open>j \<in># dom_m N\<close> and
    a: \<open>(a, arena) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close>
  shows
    \<open>j - ACTIVITY_SHIFT < length arena\<close> (is ?le) and
    \<open>ACTIVITY_SHIFT \<le> j\<close> (is ?ge) and
    \<open>(a[j - ACTIVITY_SHIFT := a ! (j - ACTIVITY_SHIFT) >> Suc 0], arena_decr_act arena j)
       \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close>
proof -
  have j_le: \<open>j < length arena\<close> and
    length: \<open>length (N \<propto> j) = arena_length arena j\<close> and
    k1:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> N \<propto> j ! k = arena_lit arena (j + k)\<close> and
    k2:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> is_Lit (arena ! (j+k))\<close> and
    le: \<open>j + length (N \<propto> j) \<le> length arena\<close>  and
    j_ge: \<open>header_size (N \<propto> j) \<le> j\<close> and
    lbd: \<open>is_Act (arena ! (j - ACTIVITY_SHIFT))\<close>
    using arena_lifting[OF valid j] by auto
  show le': ?le
     using le j_ge unfolding length[symmetric] header_size_def
     by (auto split: if_splits simp: ACTIVITY_SHIFT_def)
  show ?ge
    using j_ge by (auto simp: SHIFTS_def header_size_def split: if_splits)
  have b:
    \<open>(a ! (j - ACTIVITY_SHIFT),
         (arena ! (j - ACTIVITY_SHIFT)))
       \<in> uint32_nat_rel O arena_el_rel\<close>
    by (rule param_nth[OF _ _ a]) (use j_le in auto)
  show \<open>(a[j - ACTIVITY_SHIFT := a ! (j - ACTIVITY_SHIFT) >> Suc 0], arena_decr_act arena j)
      \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close>
    unfolding arena_decr_act_def
    by (rule list_rel_update'[OF a])
      (cases \<open>arena ! (j - ACTIVITY_SHIFT)\<close>;
      use lbd b in \<open>auto simp add: uint32_nat_rel_def br_def arena_el_rel_def
        Collect_eq_comp sum_mod_uint32_max_def nat_of_uint32_plus
	nat_of_uint32_shiftr\<close>)
qed

lemma isa_arena_decr_act_arena_decr_act:
  \<open>(uncurry isa_arena_decr_act, uncurry (RETURN oo arena_decr_act)) \<in>
    [uncurry arena_act_pre]\<^sub>f
     \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel \<times>\<^sub>f nat_rel \<rightarrow>
    \<langle> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
   (auto simp: isa_arena_decr_act_def arena_act_def arena_get_lbd_conv
      arena_act_pre_def arena_is_valid_clause_idx_def arena_decr_act_conv
      list_rel_imp_same_length arena_act_conv
      intro!: ASSERT_leI)

      
lemma valid_arena_arena_decr_act:
  assumes C: \<open>C \<in># dom_m N\<close> and valid: \<open>valid_arena arena N vdom\<close>
  shows
   \<open>valid_arena (arena_decr_act arena C) N vdom\<close>
proof -
  let ?arena = \<open>arena_decr_act arena C\<close>
  have act: \<open>\<forall>i\<in>#dom_m N.
     i < length (arena) \<and>
     header_size (N \<propto> i) \<le> i \<and>
     xarena_active_clause (clause_slice arena N i)
      (the (fmlookup N i))\<close> and
    dead: \<open>\<And>i. i \<in> vdom \<Longrightarrow> i \<notin># dom_m N \<Longrightarrow> i < length arena \<and>
           4 \<le> i \<and> arena_dead_clause (Misc.slice (i - 4) i arena)\<close> and
    C_ge: \<open>header_size (N \<propto> C) \<le> C\<close> and
    C_le: \<open>C < length arena\<close> and
    C_act: \<open>xarena_active_clause (clause_slice arena N C)
      (the (fmlookup N C))\<close>
    using assms
    by (auto simp: valid_arena_def)
  have
   [simp]: \<open>clause_slice ?arena N C ! (header_size (N \<propto> C) - LBD_SHIFT) =
           clause_slice arena N C ! (header_size (N \<propto> C) - LBD_SHIFT)\<close> and
   [simp]: \<open>clause_slice ?arena N C ! (header_size (N \<propto> C) - STATUS_SHIFT) =
           clause_slice arena N C ! (header_size (N \<propto> C) - STATUS_SHIFT)\<close> and
   [simp]: \<open>clause_slice ?arena N C ! (header_size (N \<propto> C) - SIZE_SHIFT) =
           clause_slice arena N C ! (header_size (N \<propto> C) - SIZE_SHIFT)\<close> and
   [simp]: \<open>is_long_clause (N \<propto> C) \<Longrightarrow> clause_slice ?arena N C ! (header_size (N \<propto> C) - POS_SHIFT) =
           clause_slice arena N C ! (header_size (N \<propto> C) - POS_SHIFT)\<close> and
   [simp]: \<open>length (clause_slice  ?arena N C) = length (clause_slice arena N C)\<close> and
   [simp]: \<open>is_Act (clause_slice ?arena N C ! (header_size (N \<propto> C) - ACTIVITY_SHIFT))\<close> and
   [simp]: \<open>Misc.slice C (C + length (N \<propto> C)) ?arena =
     Misc.slice C (C + length (N \<propto> C)) arena\<close>
    using C_le C_ge unfolding SHIFTS_def arena_decr_act_def header_size_def
    by (auto simp: Misc.slice_def drop_update_swap split: if_splits)

  have \<open>xarena_active_clause (clause_slice ?arena N C) (the (fmlookup N C))\<close>
    using C_act C_le C_ge unfolding xarena_active_clause_alt_def
    by simp

  then have 1: \<open>xarena_active_clause (clause_slice arena N i) (the (fmlookup N i)) \<Longrightarrow>
     xarena_active_clause (clause_slice (arena_decr_act arena C) N i) (the (fmlookup N i))\<close>
    if \<open>i \<in># dom_m N\<close>
    for i
    using minimal_difference_between_valid_index[of N arena C i, OF act]
      minimal_difference_between_valid_index[of N arena i C, OF act] assms
      that C_ge
    by (cases \<open>C < i\<close>; cases \<open>C > i\<close>)
      (auto simp: arena_decr_act_def header_size_def ACTIVITY_SHIFT_def
      split: if_splits)

  have 2:
    \<open>arena_dead_clause (Misc.slice (i - 4) i ?arena)\<close>
    if \<open>i \<in> vdom\<close>\<open>i \<notin># dom_m N\<close>\<open>arena_dead_clause (Misc.slice (i - 4) i arena)\<close>
    for i
  proof -
    have i_ge: \<open>i \<ge> 4\<close> \<open>i < length arena\<close>
      using that valid unfolding valid_arena_def
      by auto
    show ?thesis
      using dead[of i] that C_le C_ge
      minimal_difference_between_invalid_index[OF valid, of C i]
      minimal_difference_between_invalid_index2[OF valid, of C i]
      by (cases \<open>C < i\<close>; cases \<open>C > i\<close>)
        (auto simp: arena_decr_act_def header_size_def ACTIVITY_SHIFT_def C
          split: if_splits)
  qed
  show ?thesis
    using 1 2 valid
    by (auto simp: valid_arena_def)
qed


paragraph \<open>Mark used\<close>

definition isa_mark_used :: \<open>uint32 list \<Rightarrow> nat \<Rightarrow> uint32 list nres\<close> where
  \<open>isa_mark_used arena C = do {
      ASSERT(C - STATUS_SHIFT < length arena \<and> C \<ge> STATUS_SHIFT);
      let act = arena ! (C - STATUS_SHIFT);
      RETURN (arena[C - STATUS_SHIFT := act OR 0b100])
  }\<close>

lemma isa_mark_used_conv:
  assumes
    valid: \<open>valid_arena arena N x\<close> and
    j: \<open>j \<in># dom_m N\<close> and
    a: \<open>(a, arena) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close>
  shows
    \<open>j - STATUS_SHIFT < length arena\<close> (is ?le) and
    \<open>STATUS_SHIFT \<le> j\<close> (is ?ge) and
    \<open>(a[j - STATUS_SHIFT := a ! (j - STATUS_SHIFT) OR 4], mark_used arena j) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close>
proof -
  have j_le: \<open>j < length arena\<close> and
    length: \<open>length (N \<propto> j) = arena_length arena j\<close> and
    k1:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> N \<propto> j ! k = arena_lit arena (j + k)\<close> and
    k2:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> is_Lit (arena ! (j+k))\<close> and
    le: \<open>j + length (N \<propto> j) \<le> length arena\<close>  and
    j_ge: \<open>header_size (N \<propto> j) \<le> j\<close> and
    lbd: \<open>is_Status (arena ! (j - STATUS_SHIFT))\<close>
    using arena_lifting[OF valid j] by auto
  show le': ?le
     using le j_ge unfolding length[symmetric] header_size_def
     by (auto split: if_splits simp: STATUS_SHIFT_def)
  show ?ge
    using j_ge by (auto simp: SHIFTS_def header_size_def split: if_splits)
  have b:
    \<open>(a ! (j - STATUS_SHIFT),
         (arena ! (j - STATUS_SHIFT)))
       \<in> uint32_nat_rel O arena_el_rel\<close>
    by (rule param_nth[OF _ _ a]) (use j_le in auto)
  have [simp]: \<open>(a OR 4) AND 3 = a AND 3\<close> for a :: int
    supply [[show_types]]
    by (smt BIT_special_simps(1) BIT_special_simps(4) One_nat_def bbw_ao_dist expand_BIT(2)
      int_and_comm int_and_numerals(17) int_and_numerals(3) int_or_extra_simps(1)
      numeral_One numeral_plus_one of_nat_numeral semiring_1_class.of_nat_simps(1)
      semiring_1_class.of_nat_simps(2) semiring_norm(2) semiring_norm(8))
  have Pos: \<open>b \<ge>0 \<Longrightarrow> a \<le> a OR b\<close> for a b :: int
    by (rule le_int_or)
      (auto simp: bin_sign_def)
  have [simp]: \<open>(0::int) \<le> int a OR (4::int)\<close> for a :: nat
    by (rule order_trans[OF _ Pos])
      auto
  then have [simp]: \<open>(a OR 4) AND 3 = a AND 3\<close> for a :: nat
    supply [[show_types]]
    unfolding bitAND_nat_def bitOR_nat_def
    by auto

  have [simp]: \<open>(a OR 4) AND 4 = 4\<close> for a :: nat
    supply [[show_types]]
    unfolding bitAND_nat_def bitOR_nat_def
    by auto
  have nat_of_uint32_4: \<open>4 = nat_of_uint32 4\<close>
    by auto
  have [simp]: \<open>nat_of_uint32 (a OR 4) = nat_of_uint32 a OR 4\<close> for a
    by (subst nat_of_uint32_4, subst nat_of_uint32_ao) simp

  show \<open>(a[j - STATUS_SHIFT := a ! (j - STATUS_SHIFT) OR 0b100],
      mark_used arena j) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close>
    unfolding mark_used_def
    by (rule list_rel_update'[OF a])
      (cases \<open>arena ! (j - STATUS_SHIFT)\<close>;
      use lbd b in \<open>auto simp add: uint32_nat_rel_def br_def arena_el_rel_def
          status_rel_def bitfield_rel_def
          Collect_eq_comp sum_mod_uint32_max_def nat_of_uint32_plus\<close>)
qed


lemma isa_mark_used_mark_used:
  \<open>(uncurry isa_mark_used, uncurry (RETURN oo mark_used)) \<in>
    [uncurry arena_act_pre]\<^sub>f
     \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel \<times>\<^sub>f nat_rel \<rightarrow>
    \<langle> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
   (auto simp: isa_mark_used_def arena_get_lbd_conv
      arena_act_pre_def arena_is_valid_clause_idx_def arena_incr_act_conv
      list_rel_imp_same_length isa_mark_used_conv
      intro!: ASSERT_leI)
 
paragraph \<open>Mark unused\<close>

definition isa_mark_unused :: \<open>uint32 list \<Rightarrow> nat \<Rightarrow> uint32 list nres\<close> where
  \<open>isa_mark_unused arena C = do {
      ASSERT(C - STATUS_SHIFT < length arena \<and> C \<ge> STATUS_SHIFT);
      let act = arena ! (C - STATUS_SHIFT);
      RETURN (arena[C - STATUS_SHIFT := act AND 0b11])
  }\<close>

lemma isa_mark_unused_conv:
  assumes
    valid: \<open>valid_arena arena N x\<close> and
    j: \<open>j \<in># dom_m N\<close> and
    a: \<open>(a, arena) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close>
  shows
    \<open>j - STATUS_SHIFT < length arena\<close> (is ?le) and
    \<open>STATUS_SHIFT \<le> j\<close> (is ?ge) and
    \<open>(a[j - STATUS_SHIFT := a ! (j - STATUS_SHIFT) AND 3], mark_unused arena j) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close>
proof -
  have j_le: \<open>j < length arena\<close> and
    length: \<open>length (N \<propto> j) = arena_length arena j\<close> and
    k1:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> N \<propto> j ! k = arena_lit arena (j + k)\<close> and
    k2:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> is_Lit (arena ! (j+k))\<close> and
    le: \<open>j + length (N \<propto> j) \<le> length arena\<close>  and
    j_ge: \<open>header_size (N \<propto> j) \<le> j\<close> and
    lbd: \<open>is_Status (arena ! (j - STATUS_SHIFT))\<close>
    using arena_lifting[OF valid j] by auto
  show le': ?le
     using le j_ge unfolding length[symmetric] header_size_def
     by (auto split: if_splits simp: STATUS_SHIFT_def)
  show ?ge
    using j_ge by (auto simp: SHIFTS_def header_size_def split: if_splits)
  have b:
    \<open>(a ! (j - STATUS_SHIFT),
         (arena ! (j - STATUS_SHIFT)))
       \<in> uint32_nat_rel O arena_el_rel\<close>
    by (rule param_nth[OF _ _ a]) (use j_le in auto)
  have [simp]: \<open>(a OR 4) AND 3 = a AND 3\<close> for a :: int
    supply [[show_types]]
    by (smt BIT_special_simps(1) BIT_special_simps(4) One_nat_def bbw_ao_dist expand_BIT(2)
      int_and_comm int_and_numerals(17) int_and_numerals(3) int_or_extra_simps(1)
      numeral_One numeral_plus_one of_nat_numeral semiring_1_class.of_nat_simps(1)
      semiring_1_class.of_nat_simps(2) semiring_norm(2) semiring_norm(8))
  have Pos: \<open>b \<ge>0 \<Longrightarrow> a \<le> a OR b\<close> for a b :: int
    by (rule le_int_or)
      (auto simp: bin_sign_def)
  have [simp]: \<open>(0::int) \<le> int a OR (4::int)\<close> for a :: nat
    by (rule order_trans[OF _ Pos])
      auto
  then have [simp]: \<open>(a OR 4) AND 3 = a AND 3\<close> for a :: nat
    supply [[show_types]]
    unfolding bitAND_nat_def bitOR_nat_def
    by auto

  have [simp]: \<open>(a OR 4) AND 4 = 4\<close> for a :: nat
    supply [[show_types]]
    unfolding bitAND_nat_def bitOR_nat_def
    by auto
  have nat_of_uint32_4: \<open>3 = nat_of_uint32 3\<close>
    by auto
  have [simp]: \<open>nat_of_uint32 (a AND 3) = nat_of_uint32 a AND 3\<close> for a
    by (subst nat_of_uint32_4, subst nat_of_uint32_ao) simp
  (* TODO mark nat_0_AND as [simp] *)
  show \<open>(a[j - STATUS_SHIFT := a ! (j - STATUS_SHIFT) AND 3],
      mark_unused arena j) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close>
    unfolding mark_unused_def
    supply [[show_types]]
    by (rule list_rel_update'[OF a])
      (cases \<open>arena ! (j - STATUS_SHIFT)\<close>;
      use lbd b in \<open>auto simp add: uint32_nat_rel_def br_def arena_el_rel_def
          status_rel_def bitfield_rel_def nat_0_AND
          Collect_eq_comp sum_mod_uint32_max_def nat_of_uint32_plus\<close>)
qed


lemma isa_mark_unused_mark_unused:
  \<open>(uncurry isa_mark_unused, uncurry (RETURN oo mark_unused)) \<in>
    [uncurry arena_act_pre]\<^sub>f
     \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel \<times>\<^sub>f nat_rel \<rightarrow>
    \<langle> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
   (auto simp: isa_mark_unused_def arena_get_lbd_conv
      arena_act_pre_def arena_is_valid_clause_idx_def arena_incr_act_conv
      list_rel_imp_same_length isa_mark_unused_conv
      intro!: ASSERT_leI)


paragraph \<open>Marked as used?\<close>

definition isa_marked_as_used :: \<open>uint32 list \<Rightarrow> nat \<Rightarrow> bool nres\<close> where
  \<open>isa_marked_as_used arena C = do {
      ASSERT(C - STATUS_SHIFT < length arena \<and> C \<ge> STATUS_SHIFT);
      RETURN (arena ! (C - STATUS_SHIFT) AND 4 \<noteq> 0)
  }\<close>



lemma arena_marked_as_used_conv:
  assumes
    valid: \<open>valid_arena arena N x\<close> and
    j: \<open>j \<in># dom_m N\<close> and
    a: \<open>(a, arena) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close>
  shows
    \<open>j - STATUS_SHIFT < length arena\<close> (is ?le) and
    \<open>STATUS_SHIFT \<le> j\<close> (is ?ge) and
    \<open>a ! (j - STATUS_SHIFT) AND 4 \<noteq> 0 \<longleftrightarrow>
        marked_as_used arena j\<close>
proof -
  have j_le: \<open>j < length arena\<close> and
    length: \<open>length (N \<propto> j) = arena_length arena j\<close> and
    k1: \<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> N \<propto> j ! k = arena_lit arena (j + k)\<close> and
    k2: \<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> is_Lit (arena ! (j+k))\<close> and
    le: \<open>j + length (N \<propto> j) \<le> length arena\<close>  and
    j_ge: \<open>header_size (N \<propto> j) \<le> j\<close> and
    lbd: \<open>is_Status (arena ! (j - STATUS_SHIFT))\<close>
    using arena_lifting[OF valid j] by (auto simp: )
  show le': ?le
     using le j_ge unfolding length[symmetric] header_size_def
     by (auto split: if_splits simp: STATUS_SHIFT_def)
  show ?ge
    using j_ge by (auto simp: SHIFTS_def header_size_def split: if_splits)
  have [simp]: \<open>a \<noteq> 0 \<longleftrightarrow> nat_of_uint32 a \<noteq> 0\<close> for a:: uint32
    by (simp add: nat_of_uint32_0_iff)
  have
    \<open>(a ! (j - STATUS_SHIFT),
         (arena ! (j - STATUS_SHIFT)))
       \<in> uint32_nat_rel O arena_el_rel\<close>
    by (rule param_nth[OF _ _ a]) (use j_le in auto)
  then show \<open>a ! (j - STATUS_SHIFT) AND 4 \<noteq> 0 \<longleftrightarrow>
        marked_as_used arena j\<close>
    using lbd by (cases \<open>arena ! (j - STATUS_SHIFT)\<close>)
      (auto simp: arena_el_rel_def bitfield_rel_def nat_of_uint32_ao[symmetric]
      marked_as_used_def uint32_nat_rel_def br_def)
qed



lemma isa_marked_as_used_marked_as_used:
  \<open>(uncurry isa_marked_as_used, uncurry (RETURN oo marked_as_used)) \<in>
    [uncurry marked_as_used_pre]\<^sub>f
     \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel \<times>\<^sub>f nat_rel \<rightarrow>
    \<langle>bool_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: marked_as_used_pre_def arena_marked_as_used_conv
      get_clause_LBD_pre_def arena_is_valid_clause_idx_def
      list_rel_imp_same_length isa_marked_as_used_def
      intro!: ASSERT_leI)

abbreviation arena_el_assn :: "arena_el \<Rightarrow> uint32 \<Rightarrow> assn" where
  \<open>arena_el_assn \<equiv> hr_comp uint32_nat_assn arena_el_rel\<close>

abbreviation arena_assn :: "arena_el list \<Rightarrow> uint32 array_list \<Rightarrow> assn" where
  \<open>arena_assn \<equiv> arl_assn arena_el_assn\<close>

abbreviation arena_fast_assn :: "arena_el list \<Rightarrow> uint32 array_list64 \<Rightarrow> assn" where
  \<open>arena_fast_assn \<equiv> arl64_assn arena_el_assn\<close>

abbreviation status_assn where
  \<open>status_assn \<equiv> hr_comp uint32_nat_assn status_rel\<close>

abbreviation clause_status_assn where
  \<open>clause_status_assn \<equiv> (id_assn :: clause_status \<Rightarrow> _)\<close>

lemma IRRED_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return IRRED), uncurry0 (RETURN IRRED)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a clause_status_assn\<close>
  by sepref_to_hoare sep_auto

lemma LEARNED_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return LEARNED), uncurry0 (RETURN LEARNED)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a clause_status_assn\<close>
  by sepref_to_hoare sep_auto

lemma DELETED_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return DELETED), uncurry0 (RETURN DELETED)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a clause_status_assn\<close>
  by sepref_to_hoare sep_auto

lemma ACTIVITY_SHIFT_hnr:
  \<open>(uncurry0 (return 3), uncurry0 (RETURN ACTIVITY_SHIFT) ) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: ACTIVITY_SHIFT_def uint64_nat_rel_def br_def)
lemma STATUS_SHIFT_hnr:
  \<open>(uncurry0 (return 4), uncurry0 (RETURN STATUS_SHIFT) ) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: STATUS_SHIFT_def uint64_nat_rel_def br_def)

lemma [sepref_fr_rules]:
  \<open>(uncurry0 (return 1), uncurry0 (RETURN SIZE_SHIFT)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: SIZE_SHIFT_def)

lemma [sepref_fr_rules]:
  \<open>(return o id, RETURN o xarena_length) \<in> [is_Size]\<^sub>a arena_el_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: SIZE_SHIFT_def uint32_nat_rel_def
    arena_el_rel_def br_def hr_comp_def split: arena_el.splits)

lemma (in -) POS_SHIFT_uint64_hnr:
  \<open>(uncurry0 (return 5), uncurry0 (RETURN POS_SHIFT)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: POS_SHIFT_def uint64_nat_rel_def br_def)

lemma nat_of_uint64_eq_2_iff[simp]: \<open>nat_of_uint64 c = 2 \<longleftrightarrow> c = 2\<close>
  using word_nat_of_uint64_Rep_inject by fastforce

lemma arena_el_assn_alt_def:
  \<open>arena_el_assn = hr_comp uint32_assn (uint32_nat_rel O arena_el_rel)\<close>
  by (auto simp: hr_comp_assoc[symmetric])

lemma arena_el_comp: \<open>hn_val (uint32_nat_rel O arena_el_rel) = hn_ctxt arena_el_assn\<close>
  by (auto simp: hn_ctxt_def arena_el_assn_alt_def)

lemma status_assn_hnr_eq[sepref_fr_rules]:
  \<open>(uncurry (return oo (=)), uncurry (RETURN oo (=))) \<in> status_assn\<^sup>k *\<^sub>a status_assn\<^sup>k \<rightarrow>\<^sub>a
    bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: status_rel_def hr_comp_def uint32_nat_rel_def br_def
    nat_of_uint32_0_iff nat_of_uint32_Suc03_iff nat_of_uint32_013_neq)

lemma IRRED_status_assn[sepref_fr_rules]:
  \<open>(uncurry0 (return 0), uncurry0 (RETURN IRRED)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a status_assn\<close>
  by (sepref_to_hoare) (sep_auto simp: status_rel_def hr_comp_def uint32_nat_rel_def br_def)

lemma LEARNED_status_assn[sepref_fr_rules]:
  \<open>(uncurry0 (return 1), uncurry0 (RETURN LEARNED)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a status_assn\<close>
  by (sepref_to_hoare) (sep_auto simp: status_rel_def hr_comp_def uint32_nat_rel_def br_def)

lemma DELETED_status_assn[sepref_fr_rules]:
  \<open>(uncurry0 (return 3), uncurry0 (RETURN DELETED)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a status_assn\<close>
  by (sepref_to_hoare) (sep_auto simp: status_rel_def hr_comp_def uint32_nat_rel_def br_def
    nat_of_uint32_Suc03_iff)

lemma status_assn_alt_def:
  \<open>status_assn = pure (uint32_nat_rel O status_rel)\<close>
  unfolding hr_comp_pure by simp

lemma [sepref_fr_rules]:
  \<open>(uncurry0 (return 2), uncurry0 (RETURN LBD_SHIFT)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: LBD_SHIFT_def)

lemma [sepref_fr_rules]:
  \<open>(uncurry0 (return 4), uncurry0 (RETURN STATUS_SHIFT)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: STATUS_SHIFT_def)

lemma (in -) LBD_SHIFT_hnr:
  \<open>(uncurry0 (return 2), uncurry0 (RETURN LBD_SHIFT) ) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: LBD_SHIFT_def uint64_nat_rel_def br_def)

lemma MAX_LENGTH_SHORT_CLAUSE_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return 4), uncurry0 (RETURN MAX_LENGTH_SHORT_CLAUSE)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint64_nat_rel_def br_def)

definition four_uint32 where \<open>four_uint32 = (4 :: uint32)\<close>

lemma four_uint32_hnr:
  \<open>(uncurry0 (return 4), uncurry0 (RETURN (four_uint32 :: uint32)) ) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def four_uint32_def)

lemma [sepref_fr_rules]:
  \<open>(uncurry0 (return 5), uncurry0 (RETURN POS_SHIFT)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: SHIFTS_def)

lemma [sepref_fr_rules]:
  \<open>(return o id, RETURN o xarena_lit) \<in> [is_Lit]\<^sub>a arena_el_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  by sepref_to_hoare (sep_auto simp: SIZE_SHIFT_def uint32_nat_rel_def unat_lit_rel_def
    arena_el_rel_def br_def hr_comp_def split: arena_el.splits)

sepref_definition isa_arena_length_code
  is \<open>uncurry isa_arena_length\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  supply arena_el_assn_alt_def[symmetric, simp] sum_uint64_assn[sepref_fr_rules]
  unfolding isa_arena_length_def
  by sepref

lemma isa_arena_length_code_refine[sepref_fr_rules]:
  \<open>(uncurry isa_arena_length_code, uncurry (RETURN \<circ>\<circ> arena_length))
  \<in> [uncurry arena_is_valid_clause_idx]\<^sub>a
    arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  using isa_arena_length_code.refine[FCOMP isa_arena_length_arena_length[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] uncurry_def list_rel_compp
  by (simp add: arl_assn_comp)

sepref_definition isa_arena_length_fast_code
  is \<open>uncurry isa_arena_length\<close>
  :: \<open>(arl64_assn uint32_assn)\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  supply arena_el_assn_alt_def[symmetric, simp] sum_uint64_assn[sepref_fr_rules]
    minus_uint64_nat_assn[sepref_fr_rules]
  unfolding isa_arena_length_def SIZE_SHIFT_def fast_minus_def one_uint64_nat_def[symmetric]
  by sepref

lemma isa_arena_length_fast_code_refine[sepref_fr_rules]:
  \<open>(uncurry isa_arena_length_fast_code, uncurry (RETURN \<circ>\<circ> arena_length))
  \<in> [uncurry arena_is_valid_clause_idx]\<^sub>a
    arena_fast_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  using isa_arena_length_fast_code.refine[FCOMP isa_arena_length_arena_length[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] uncurry_def list_rel_compp
  by (simp add: arl64_assn_comp)

sepref_definition isa_arena_length_fast_code2
  is \<open>uncurry isa_arena_length\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  supply arena_el_assn_alt_def[symmetric, simp] sum_uint64_assn[sepref_fr_rules]
    minus_uint64_nat_assn[sepref_fr_rules]
  unfolding isa_arena_length_def SIZE_SHIFT_def fast_minus_def one_uint64_nat_def[symmetric]
  by sepref

lemma isa_arena_length_fast_code2_refine[sepref_fr_rules]:
  \<open>(uncurry isa_arena_length_fast_code2, uncurry (RETURN \<circ>\<circ> arena_length))
  \<in> [uncurry arena_is_valid_clause_idx]\<^sub>a
    arena_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  using isa_arena_length_fast_code2.refine[FCOMP isa_arena_length_arena_length[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] uncurry_def list_rel_compp
  by (simp add: arl_assn_comp)

sepref_definition isa_arena_lit_code
  is \<open>uncurry isa_arena_lit\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  supply arena_el_assn_alt_def[symmetric, simp] sum_uint64_assn[sepref_fr_rules]
  unfolding isa_arena_lit_def
  by sepref

lemma isa_arena_lit_code_refine[sepref_fr_rules]:
  \<open>(uncurry isa_arena_lit_code, uncurry (RETURN \<circ>\<circ> arena_lit))
  \<in> [uncurry arena_lit_pre]\<^sub>a
    arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  using isa_arena_lit_code.refine[FCOMP isa_arena_lit_arena_lit[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] uncurry_def list_rel_compp
  by (simp add: arl_assn_comp)

sepref_definition (in-) isa_arena_lit_fast_code
  is \<open>uncurry isa_arena_lit\<close>
  :: \<open>(arl64_assn uint32_assn)\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  supply arena_el_assn_alt_def[symmetric, simp] sum_uint64_assn[sepref_fr_rules]
  unfolding isa_arena_lit_def
  by sepref

declare isa_arena_lit_fast_code.refine

lemma isa_arena_lit_fast_code_refine[sepref_fr_rules]:
  \<open>(uncurry isa_arena_lit_fast_code, uncurry (RETURN \<circ>\<circ> arena_lit))
  \<in> [uncurry arena_lit_pre]\<^sub>a
    arena_fast_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  using isa_arena_lit_fast_code.refine[FCOMP isa_arena_lit_arena_lit[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] uncurry_def list_rel_compp
  by (simp add: arl64_assn_comp)


sepref_definition (in-) isa_arena_lit_fast_code2
  is \<open>uncurry isa_arena_lit\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  supply arena_el_assn_alt_def[symmetric, simp] sum_uint64_assn[sepref_fr_rules]
  unfolding isa_arena_lit_def
  by sepref

declare isa_arena_lit_fast_code2.refine

lemma isa_arena_lit_fast_code2_refine[sepref_fr_rules]:
  \<open>(uncurry isa_arena_lit_fast_code2, uncurry (RETURN \<circ>\<circ> arena_lit))
  \<in> [uncurry arena_lit_pre]\<^sub>a
    arena_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  using isa_arena_lit_fast_code2.refine[FCOMP isa_arena_lit_arena_lit[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] uncurry_def list_rel_compp
  by (simp add: arl_assn_comp)

sepref_definition arena_status_code
  is \<open>uncurry isa_arena_status\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  supply arena_el_assn_alt_def[symmetric, simp] sum_uint64_assn[sepref_fr_rules]
  unfolding isa_arena_status_def
  by sepref

lemma isa_arena_status_refine[sepref_fr_rules]:
  \<open>(uncurry arena_status_code, uncurry (RETURN \<circ>\<circ> arena_status))
  \<in> [uncurry arena_is_valid_clause_vdom]\<^sub>a
    arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> status_assn\<close>
  using arena_status_code.refine[FCOMP isa_arena_status_arena_status[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] uncurry_def list_rel_compp status_assn_alt_def
  by (simp add: arl_assn_comp)


sepref_definition swap_lits_code
  is \<open>Sepref_Misc.uncurry3 isa_arena_swap\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (arl_assn uint32_assn)\<^sup>d  \<rightarrow>\<^sub>a arl_assn uint32_assn\<close>
  unfolding isa_arena_swap_def WB_More_Refinement_List.swap_def IICF_List.swap_def[symmetric]
  by sepref

lemma swap_lits_refine[sepref_fr_rules]:
  \<open>(uncurry3 swap_lits_code, uncurry3 (RETURN oooo swap_lits))
  \<in> [uncurry3 swap_lits_pre]\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a arena_assn\<^sup>d \<rightarrow> arena_assn\<close>
  using swap_lits_code.refine[FCOMP isa_arena_swap[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp)

sepref_definition isa_update_lbd_code
  is \<open>uncurry2 isa_update_lbd\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a uint32_assn\<^sup>k *\<^sub>a (arl_assn uint32_assn)\<^sup>d  \<rightarrow>\<^sub>a arl_assn uint32_assn\<close>
  unfolding isa_update_lbd_def
  by sepref


lemma update_lbd_hnr[sepref_fr_rules]:
  \<open>(uncurry2 isa_update_lbd_code, uncurry2 (RETURN ooo update_lbd))
  \<in> [update_lbd_pre]\<^sub>a nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a arena_assn\<^sup>d \<rightarrow> arena_assn\<close>
  using isa_update_lbd_code.refine[FCOMP isa_update_lbd[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)


sepref_definition (in -)isa_update_lbd_fast_code
  is \<open>uncurry2 isa_update_lbd\<close>
  :: \<open>uint64_nat_assn\<^sup>k *\<^sub>a uint32_assn\<^sup>k *\<^sub>a (arl64_assn uint32_assn)\<^sup>d  \<rightarrow>\<^sub>a arl64_assn uint32_assn\<close>
  supply LBD_SHIFT_hnr[sepref_fr_rules]
  unfolding isa_update_lbd_def
  by sepref

lemma update_lbd_fast_hnr[sepref_fr_rules]:
  \<open>(uncurry2 isa_update_lbd_fast_code, uncurry2 (RETURN ooo update_lbd))
  \<in> [update_lbd_pre]\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>d \<rightarrow> arena_fast_assn\<close>
  using isa_update_lbd_fast_code.refine[FCOMP isa_update_lbd[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl64_assn_comp update_lbd_pre_def)

sepref_definition (in -)isa_update_lbd_fast_code2
  is \<open>uncurry2 isa_update_lbd\<close>
  :: \<open>uint64_nat_assn\<^sup>k *\<^sub>a uint32_assn\<^sup>k *\<^sub>a (arl_assn uint32_assn)\<^sup>d  \<rightarrow>\<^sub>a arl_assn uint32_assn\<close>
  supply LBD_SHIFT_hnr[sepref_fr_rules]
  unfolding isa_update_lbd_def
  by sepref

lemma update_lbd_fast_hnr2[sepref_fr_rules]:
  \<open>(uncurry2 isa_update_lbd_fast_code2, uncurry2 (RETURN ooo update_lbd))
  \<in> [update_lbd_pre]\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a arena_assn\<^sup>d \<rightarrow> arena_assn\<close>
  using isa_update_lbd_fast_code2.refine[FCOMP isa_update_lbd[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)

sepref_definition isa_get_clause_LBD_code
  is \<open>uncurry isa_get_clause_LBD\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  unfolding isa_get_clause_LBD_def fast_minus_def[symmetric]
  by sepref

lemma isa_get_clause_LBD_code[sepref_fr_rules]:
  \<open>(uncurry isa_get_clause_LBD_code, uncurry (RETURN \<circ>\<circ> get_clause_LBD))
     \<in> [uncurry get_clause_LBD_pre]\<^sub>a arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  using isa_get_clause_LBD_code.refine[FCOMP isa_get_clause_LBD_get_clause_LBD[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)

sepref_definition isa_get_saved_pos_fast_code
  is \<open>uncurry isa_get_saved_pos\<close>
  :: \<open>(arl64_assn uint32_assn)\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  supply sum_uint64_assn[sepref_fr_rules] POS_SHIFT_uint64_hnr[sepref_fr_rules]
  unfolding isa_get_saved_pos_def
  by sepref

lemma get_saved_pos_fast_code[sepref_fr_rules]:
  \<open>(uncurry isa_get_saved_pos_fast_code, uncurry (RETURN \<circ>\<circ> arena_pos))
     \<in> [uncurry get_saved_pos_pre]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  using isa_get_saved_pos_fast_code.refine[FCOMP isa_get_saved_pos_get_saved_pos[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl64_assn_comp update_lbd_pre_def)

sepref_definition isa_get_saved_pos_code
  is \<open>uncurry isa_get_saved_pos\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  supply sum_uint64_assn[sepref_fr_rules]
  unfolding isa_get_saved_pos_def POS_SHIFT_def
  by sepref

lemma get_saved_pos_code[sepref_fr_rules]:
  \<open>(uncurry isa_get_saved_pos_code, uncurry (RETURN \<circ>\<circ> arena_pos))
     \<in> [uncurry get_saved_pos_pre]\<^sub>a arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  using isa_get_saved_pos_code.refine[FCOMP isa_get_saved_pos_get_saved_pos[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)

sepref_definition isa_get_saved_pos_code'
  is \<open>uncurry isa_get_saved_pos'\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  supply sum_uint64_assn[sepref_fr_rules]
  unfolding isa_get_saved_pos_def isa_get_saved_pos'_def
  by sepref
(* TODO check if we use this version anywhere *)
lemma get_saved_pos_code':
\<open>(uncurry isa_get_saved_pos_code', uncurry (RETURN \<circ>\<circ> arena_pos))
     \<in> [uncurry get_saved_pos_pre]\<^sub>a arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  using isa_get_saved_pos_code'.refine[FCOMP isa_get_saved_pos_get_saved_pos'[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)

sepref_definition isa_get_saved_pos_fast_code2
  is \<open>uncurry isa_get_saved_pos\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  supply sum_uint64_assn[sepref_fr_rules] POS_SHIFT_uint64_hnr[sepref_fr_rules]
  unfolding isa_get_saved_pos_def
  by sepref

lemma get_saved_pos_code2[sepref_fr_rules]:
  \<open>(uncurry isa_get_saved_pos_fast_code2, uncurry (RETURN \<circ>\<circ> arena_pos))
     \<in> [uncurry get_saved_pos_pre]\<^sub>a arena_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  using isa_get_saved_pos_fast_code2.refine[FCOMP isa_get_saved_pos_get_saved_pos[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)

sepref_definition isa_update_pos_code
  is \<open>uncurry2 isa_update_pos\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (arl_assn uint32_assn)\<^sup>d  \<rightarrow>\<^sub>a arl_assn uint32_assn\<close>
  supply minus_uint32_assn[sepref_fr_rules]
  unfolding isa_update_pos_def
  by sepref

lemma isa_update_pos_code_hnr[sepref_fr_rules]:
  \<open>(uncurry2 isa_update_pos_code, uncurry2 (RETURN ooo arena_update_pos))
  \<in> [isa_update_pos_pre]\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a arena_assn\<^sup>d \<rightarrow> arena_assn\<close>
  using isa_update_pos_code.refine[FCOMP isa_update_pos[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp isa_update_pos_pre_def)

sepref_definition mark_garbage_code
  is \<open>uncurry mark_garbage\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a arl_assn uint32_assn\<close>
  unfolding mark_garbage_def fast_minus_def[symmetric]
  by sepref

lemma mark_garbage_hnr[sepref_fr_rules]:
  \<open>(uncurry mark_garbage_code, uncurry (RETURN oo extra_information_mark_to_delete))
  \<in> [mark_garbage_pre]\<^sub>a  arena_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow> arena_assn\<close>
  using mark_garbage_code.refine[FCOMP isa_mark_garbage[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)

sepref_definition isa_arena_act_code
  is \<open>uncurry isa_arena_act\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  unfolding isa_arena_act_def ACTIVITY_SHIFT_def fast_minus_def[symmetric]
  by sepref

lemma isa_arena_act_code[sepref_fr_rules]:
  \<open>(uncurry isa_arena_act_code, uncurry (RETURN \<circ>\<circ> arena_act))
     \<in> [uncurry arena_act_pre]\<^sub>a arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  using isa_arena_act_code.refine[FCOMP isa_arena_act_arena_act[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)

sepref_definition isa_arena_incr_act_code
  is \<open>uncurry isa_arena_incr_act\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a (arl_assn uint32_assn)\<close>
  unfolding isa_arena_incr_act_def ACTIVITY_SHIFT_def fast_minus_def
  by sepref

lemma isa_arena_incr_act_code[sepref_fr_rules]:
  \<open>(uncurry isa_arena_incr_act_code, uncurry (RETURN \<circ>\<circ> arena_incr_act))
     \<in> [uncurry arena_act_pre]\<^sub>a arena_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow> arena_assn\<close>
  using isa_arena_incr_act_code.refine[FCOMP isa_arena_incr_act_arena_incr_act[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)

sepref_definition isa_arena_decr_act_code
  is \<open>uncurry isa_arena_decr_act\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a (arl_assn uint32_assn)\<close>
  unfolding isa_arena_decr_act_def ACTIVITY_SHIFT_def fast_minus_def
  by sepref

lemma isa_arena_decr_act_code[sepref_fr_rules]:
  \<open>(uncurry isa_arena_decr_act_code, uncurry (RETURN \<circ>\<circ> arena_decr_act))
     \<in> [uncurry arena_act_pre]\<^sub>a arena_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow> arena_assn\<close>
  using isa_arena_decr_act_code.refine[FCOMP isa_arena_decr_act_arena_decr_act[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)


sepref_definition isa_arena_decr_act_fast_code
  is \<open>uncurry isa_arena_decr_act\<close>
  :: \<open>(arl64_assn uint32_assn)\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a (arl64_assn uint32_assn)\<close>
  unfolding isa_arena_decr_act_def
  three_uint32_def[symmetric] ACTIVITY_SHIFT_hnr[sepref_fr_rules]
  by sepref

lemma isa_arena_decr_act_fast_code[sepref_fr_rules]:
  \<open>(uncurry isa_arena_decr_act_fast_code, uncurry (RETURN \<circ>\<circ> arena_decr_act))
     \<in> [uncurry arena_act_pre]\<^sub>a arena_fast_assn\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> arena_fast_assn\<close>
  using isa_arena_decr_act_fast_code.refine[FCOMP isa_arena_decr_act_arena_decr_act[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl64_assn_comp update_lbd_pre_def)

sepref_definition isa_mark_used_code
  is \<open>uncurry isa_mark_used\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a (arl_assn uint32_assn)\<close>
  unfolding isa_mark_used_def ACTIVITY_SHIFT_def fast_minus_def[symmetric]
  by sepref

lemma isa_mark_used_code[sepref_fr_rules]:
  \<open>(uncurry isa_mark_used_code, uncurry (RETURN \<circ>\<circ> mark_used))
     \<in> [uncurry arena_act_pre]\<^sub>a arena_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow> arena_assn\<close>
  using isa_mark_used_code.refine[FCOMP isa_mark_used_mark_used[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)


sepref_definition isa_mark_used_fast_code
  is \<open>uncurry isa_mark_used\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a (arl_assn uint32_assn)\<close>
  supply four_uint32_hnr[sepref_fr_rules] STATUS_SHIFT_hnr[sepref_fr_rules]
  unfolding isa_mark_used_def four_uint32_def[symmetric]
  by sepref

lemma isa_mark_used_fast_code[sepref_fr_rules]:
  \<open>(uncurry isa_mark_used_fast_code, uncurry (RETURN \<circ>\<circ> mark_used))
     \<in> [uncurry arena_act_pre]\<^sub>a arena_assn\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> arena_assn\<close>
  using isa_mark_used_fast_code.refine[FCOMP isa_mark_used_mark_used[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)

sepref_definition isa_mark_unused_code
  is \<open>uncurry isa_mark_unused\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a (arl_assn uint32_assn)\<close>
  unfolding isa_mark_unused_def ACTIVITY_SHIFT_def fast_minus_def[symmetric]
  by sepref

lemma isa_mark_unused_code[sepref_fr_rules]:
  \<open>(uncurry isa_mark_unused_code, uncurry (RETURN \<circ>\<circ> mark_unused))
     \<in> [uncurry arena_act_pre]\<^sub>a arena_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow> arena_assn\<close>
  using isa_mark_unused_code.refine[FCOMP isa_mark_unused_mark_unused[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)

sepref_definition isa_mark_unused_fast_code
  is \<open>uncurry isa_mark_unused\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a (arl_assn uint32_assn)\<close>
  supply STATUS_SHIFT_hnr[sepref_fr_rules]
  unfolding isa_mark_unused_def ACTIVITY_SHIFT_def fast_minus_def[symmetric]
  by sepref


lemma isa_mark_unused_fast_code[sepref_fr_rules]:
  \<open>(uncurry isa_mark_unused_fast_code, uncurry (RETURN \<circ>\<circ> mark_unused))
     \<in> [uncurry arena_act_pre]\<^sub>a arena_assn\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> arena_assn\<close>
  using isa_mark_unused_fast_code.refine[FCOMP isa_mark_unused_mark_unused[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)

sepref_definition isa_marked_as_used_code
  is \<open>uncurry isa_marked_as_used\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply op_eq_uint32[sepref_fr_rules]
  unfolding isa_marked_as_used_def fast_minus_def[symmetric]
  by sepref



lemma isa_marked_as_used_code[sepref_fr_rules]:
  \<open>(uncurry isa_marked_as_used_code, uncurry (RETURN \<circ>\<circ> marked_as_used))
     \<in> [uncurry marked_as_used_pre]\<^sub>a arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> bool_assn\<close>
  using isa_marked_as_used_code.refine[FCOMP isa_marked_as_used_marked_as_used[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl_assn_comp update_lbd_pre_def)



sepref_definition (in -) isa_arena_incr_act_fast_code
  is \<open>uncurry isa_arena_incr_act\<close>
  :: \<open>(arl64_assn uint32_assn)\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a (arl64_assn uint32_assn)\<close>
  supply ACTIVITY_SHIFT_hnr[sepref_fr_rules]
  unfolding isa_arena_incr_act_def
  by sepref

lemma isa_arena_incr_act_fast_code[sepref_fr_rules]:
  \<open>(uncurry isa_arena_incr_act_fast_code, uncurry (RETURN \<circ>\<circ> arena_incr_act))
     \<in> [uncurry arena_act_pre]\<^sub>a arena_fast_assn\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> arena_fast_assn\<close>
  using isa_arena_incr_act_fast_code.refine[FCOMP isa_arena_incr_act_arena_incr_act[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl64_assn_comp update_lbd_pre_def)

sepref_definition arena_status_fast_code
  is \<open>uncurry isa_arena_status\<close>
  :: \<open>(arl64_assn uint32_assn)\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  supply arena_el_assn_alt_def[symmetric, simp] sum_uint64_assn[sepref_fr_rules]
    three_uint32_hnr[sepref_fr_rules] STATUS_SHIFT_hnr[sepref_fr_rules]
  unfolding isa_arena_status_def three_uint32_def[symmetric]
  by sepref

lemma isa_arena_status_fast_hnr[sepref_fr_rules]:
  \<open>(uncurry arena_status_fast_code, uncurry (RETURN \<circ>\<circ> arena_status))
  \<in> [uncurry arena_is_valid_clause_vdom]\<^sub>a
    arena_fast_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> status_assn\<close>
  using arena_status_fast_code.refine[FCOMP isa_arena_status_arena_status[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] uncurry_def list_rel_compp status_assn_alt_def
  by (simp add: arl64_assn_comp)

context
  notes [fcomp_norm_unfold] = arl64_assn_def[symmetric] arl64_assn_comp'
  notes [intro!] = hfrefI hn_refineI[THEN hn_refine_preI]
  notes [simp] = pure_def hn_ctxt_def invalid_assn_def
begin

definition arl64_get2 :: "'a::heap array_list64 \<Rightarrow> nat \<Rightarrow> 'a Heap" where
  "arl64_get2 \<equiv> \<lambda>(a,n) i. Array.nth a i"
thm arl64_get_hnr_aux
lemma arl64_get2_hnr_aux: "(uncurry arl64_get2,uncurry (RETURN oo op_list_get)) \<in> [\<lambda>(l,i). i<length l]\<^sub>a (is_array_list64\<^sup>k *\<^sub>a nat_assn\<^sup>k) \<rightarrow> id_assn"
    by sepref_to_hoare (sep_auto simp: arl64_get2_def is_array_list64_def)

  sepref_decl_impl arl64_get2: arl64_get2_hnr_aux .
end

sepref_definition arena_status_fast_code2
  is \<open>uncurry isa_arena_status\<close>
  :: \<open>(arl64_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  supply arena_el_assn_alt_def[symmetric, simp] sum_uint64_assn[sepref_fr_rules]
    three_uint32_hnr[sepref_fr_rules]
  unfolding isa_arena_status_def STATUS_SHIFT_def fast_minus_def
  by sepref

lemma isa_arena_status_fast_hnr2[sepref_fr_rules]:
  \<open>(uncurry arena_status_fast_code2, uncurry (RETURN \<circ>\<circ> arena_status))
  \<in> [uncurry arena_is_valid_clause_vdom]\<^sub>a
    arena_fast_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> status_assn\<close>
  using arena_status_fast_code2.refine[FCOMP isa_arena_status_arena_status[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] uncurry_def list_rel_compp status_assn_alt_def
  by (simp add: arl64_assn_comp)

sepref_definition isa_update_pos_fast_code
  is \<open>uncurry2 isa_update_pos\<close>
  :: \<open>uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a (arl64_assn uint32_assn)\<^sup>d  \<rightarrow>\<^sub>a arl64_assn uint32_assn\<close>
  supply minus_uint32_assn[sepref_fr_rules] POS_SHIFT_uint64_hnr[sepref_fr_rules] minus_uint64_assn[sepref_fr_rules]
  unfolding isa_update_pos_def  uint32_nat_assn_minus[sepref_fr_rules] two_uint64_nat_def[symmetric]
  by sepref

lemma isa_update_pos_code_fast_hnr[sepref_fr_rules]:
  \<open>(uncurry2 isa_update_pos_fast_code, uncurry2 (RETURN ooo arena_update_pos))
  \<in> [isa_update_pos_pre]\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>d \<rightarrow> arena_fast_assn\<close>
  using isa_update_pos_fast_code.refine[FCOMP isa_update_pos[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl64_assn_comp isa_update_pos_pre_def)

declare isa_update_pos_fast_code.refine[sepref_fr_rules]
  arena_status_fast_code.refine[sepref_fr_rules]

end