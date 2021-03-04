theory IsaSAT_Arena_SML
  imports Refine_Imperative_HOL.IICF IsaSAT_Arena IsaSAT_Literals_SML Watched_Literals.IICF_Array_List64
begin

no_notation WB_More_Refinement.fref (\<open>[_]\<^sub>f _ \<rightarrow> _\<close> [0,60,60] 60)
no_notation WB_More_Refinement.freft (\<open>_ \<rightarrow>\<^sub>f _\<close> [60,60] 60)

notation Sepref_Rules.fref (\<open>[_]\<^sub>f _ \<rightarrow> _\<close> [0,60,60] 60)
notation Sepref_Rules.freft (\<open>_ \<rightarrow>\<^sub>f _\<close> [60,60] 60)

instance clause_status :: heap
proof standard
  let ?f = \<open>(\<lambda>x. case x of IRRED \<Rightarrow> (0::nat) | LEARNED \<Rightarrow> 1 | DELETED \<Rightarrow> 2)\<close>
  have \<open>inj ?f\<close>
    by (auto simp: inj_def split: clause_status.splits)
  then show \<open>\<exists>f. inj (f:: clause_status \<Rightarrow> nat)\<close>
    by blast
qed

subsubsection \<open>Code Generation\<close>

paragraph \<open>Length\<close>

definition isa_arena_length where
  \<open>isa_arena_length arena i = do {
      ASSERT(i \<ge> SIZE_SHIFT \<and> i < length arena);
      RETURN (two_uint64 + uint64_of_uint32 ((arena ! (fast_minus i SIZE_SHIFT))))
  }\<close>

lemma arena_length_uint64_conv:
  assumes
    a: \<open>(a, aa) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close> and
    ba: \<open>ba \<in># dom_m N\<close> and
    valid: \<open>valid_arena aa N vdom\<close>
  shows \<open>Suc (Suc (xarena_length (aa ! (ba - SIZE_SHIFT)))) =
         nat_of_uint64 (2 + uint64_of_uint32 (a ! (ba - SIZE_SHIFT)))\<close>
proof -
  have ba_le: \<open>ba < length aa\<close> and
    size: \<open>is_Size (aa ! (ba - SIZE_SHIFT))\<close> and
    length: \<open>length (N \<propto> ba) = arena_length aa ba\<close>
    using ba valid by (auto simp: arena_lifting)
  have \<open>(a ! (ba - SIZE_SHIFT), aa ! (ba - SIZE_SHIFT))
      \<in> uint32_nat_rel O arena_el_rel\<close>
    by (rule param_nth[OF _ _ a, of \<open>ba - SIZE_SHIFT\<close> \<open>ba - SIZE_SHIFT\<close>])
      (use ba_le in auto)
  then have \<open>aa ! (ba - SIZE_SHIFT) = ASize (nat_of_uint32 (a ! (ba - SIZE_SHIFT)))\<close>
    using size unfolding arena_el_rel_def
    by (auto split: arena_el.splits simp: uint32_nat_rel_def br_def)
  moreover have \<open>Suc (Suc (nat_of_uint32 (a ! (ba - SIZE_SHIFT)))) \<le> uint64_max\<close>
    using nat_of_uint32_le_uint32_max[of \<open>a ! (ba - SIZE_SHIFT)\<close>]
    by (auto simp: uint64_max_def uint32_max_def)
  ultimately show ?thesis by (simp add: nat_of_uint64_add nat_of_uint64_uint64_of_uint32)
qed

lemma isa_arena_length_arena_length:
  \<open>(uncurry (isa_arena_length), uncurry (RETURN oo arena_length)) \<in>
    [uncurry arena_is_valid_clause_idx]\<^sub>f
     \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel \<times>\<^sub>r nat_rel \<rightarrow> \<langle>uint64_nat_rel\<rangle>nres_rel\<close>
  unfolding isa_arena_length_def arena_length_def
  by (intro frefI nres_relI)
    (auto simp: arena_is_valid_clause_idx_def uint64_nat_rel_def br_def two_uint64_def
       list_rel_imp_same_length arena_length_uint64_conv arena_lifting
    intro!: ASSERT_refine_left)


paragraph \<open>Literal at given position\<close>

definition isa_arena_lit where
  \<open>isa_arena_lit arena i = do {
      ASSERT(i < length arena);
      RETURN (arena ! i)
  }\<close>


lemma arena_length_literal_conv:
  assumes
    valid: \<open>valid_arena arena N x\<close> and
    j: \<open>j \<in># dom_m N\<close> and
    ba_le: \<open>ba - j < arena_length arena j\<close> and
    a: \<open>(a, arena) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close> and
    ba_j: \<open>ba \<ge> j\<close>
  shows
    \<open>ba < length arena\<close> (is ?le) and
    \<open>(a ! ba, xarena_lit (arena ! ba)) \<in> unat_lit_rel\<close> (is ?unat)
proof -
  have j_le: \<open>j < length arena\<close> and
    length: \<open>length (N \<propto> j) = arena_length arena j\<close> and
    k1:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> N \<propto> j ! k = arena_lit arena (j + k)\<close> and
    k2:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> is_Lit (arena ! (j+k))\<close> and
    le: \<open>j + length (N \<propto> j) \<le> length arena\<close>  and
    j_ge: \<open>header_size (N \<propto> j) \<le> j\<close>
    using arena_lifting[OF valid j] by (auto simp: )
  show le': ?le
     using le ba_le j_ge unfolding length[symmetric] header_size_def
     by (auto split: if_splits)

  have \<open>(a ! ba, arena ! ba)
      \<in> uint32_nat_rel O arena_el_rel\<close>
    by (rule param_nth[OF _ _ a, of \<open>ba\<close> \<open>ba\<close>])
      (use ba_le le' in auto)
  then show ?unat
     using k1[of \<open>ba - j\<close>] k2[of \<open>ba - j\<close>] ba_le length ba_j
     by (cases \<open>arena ! ba\<close>)
      (auto simp: arena_el_rel_def unat_lit_rel_def arena_lit_def
       split: arena_el.splits)
qed

lemma nat_of_uint32_div:
  \<open>nat_of_uint32 (a div b) = nat_of_uint32 a div nat_of_uint32 b\<close>
  by transfer (auto simp: unat_div)


lemma isa_arena_lit_arena_lit:
  \<open>(uncurry isa_arena_lit, uncurry (RETURN oo arena_lit)) \<in>
    [uncurry arena_lit_pre]\<^sub>f
     \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel \<times>\<^sub>r nat_rel \<rightarrow> \<langle>unat_lit_rel\<rangle>nres_rel\<close>
  unfolding isa_arena_lit_def arena_lit_def
  by (intro frefI nres_relI)
    (auto simp: arena_is_valid_clause_idx_def uint64_nat_rel_def br_def two_uint64_def
        list_rel_imp_same_length arena_length_uint64_conv arena_lifting
        arena_is_valid_clause_idx_and_access_def arena_length_literal_conv
        arena_lit_pre_def
      intro!: ASSERT_refine_left)

paragraph \<open>Status of the clause\<close>

definition isa_arena_status where
  \<open>isa_arena_status arena i = do {
      ASSERT(i < length arena);
      ASSERT(i \<ge> STATUS_SHIFT);
      RETURN (arena ! (fast_minus i STATUS_SHIFT) AND 0b11)
  }\<close>

lemma arena_status_literal_conv:
  assumes
    valid: \<open>valid_arena arena N x\<close> and
    j: \<open>j \<in> x\<close> and
    a: \<open>(a, arena) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close>
  shows
    \<open>j < length arena\<close> (is ?le) and
    \<open>4 \<le> j\<close> and
    \<open>j \<ge> STATUS_SHIFT\<close> and
    \<open> (a ! (j - STATUS_SHIFT) AND 0b11, xarena_status (arena ! (j - STATUS_SHIFT)))
       \<in> uint32_nat_rel O status_rel\<close> (is ?rel)
proof -
  show le: ?le and i4: \<open>4 \<le> j\<close> and  \<open>j \<ge> STATUS_SHIFT\<close>
    using valid j unfolding valid_arena_def
    by (cases \<open>j \<in># dom_m N\<close>; auto simp: header_size_def SHIFTS_def split: if_splits; fail)+
  have [intro]: \<open>\<And>a y. (a, y) \<in> uint32_nat_rel \<Longrightarrow>
      (a AND 3, y AND 3) \<in> uint32_nat_rel\<close>
    apply (auto simp: uint32_nat_rel_def br_def nat_of_uint32_ao)
     by (metis nat_of_uint32_3 nat_of_uint32_ao(1))
  have [dest]: \<open>(y, AStatus x61 x62) \<in> arena_el_rel \<Longrightarrow> (y AND 3, x61) \<in> status_rel\<close> for y x61 x62
    by (auto simp: status_rel_def arena_el_rel_def)
  have \<open>(a ! (j - STATUS_SHIFT), arena ! (j - STATUS_SHIFT)) \<in> uint32_nat_rel O arena_el_rel\<close>
    by (rule param_nth[OF _ _ a]) (use le in \<open>auto simp: list_rel_imp_same_length\<close>)
  then have  \<open>(a ! (j - STATUS_SHIFT) AND 0b11, xarena_status (arena ! (j - STATUS_SHIFT))) \<in> uint32_nat_rel O status_rel\<close>
    using arena_dom_status_iff[OF valid j]
    by (cases \<open>arena ! (j - STATUS_SHIFT)\<close>)
      (auto intro!: relcomp.relcompI)
  then show ?rel
    using arena_dom_status_iff[OF valid j]
    by (cases \<open>arena ! (j - STATUS_SHIFT)\<close>)
      (auto simp: arena_el_rel_def)
qed


lemma isa_arena_status_arena_status:
  \<open>(uncurry isa_arena_status, uncurry (RETURN oo arena_status)) \<in>
    [uncurry arena_is_valid_clause_vdom]\<^sub>f
     \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel \<times>\<^sub>r nat_rel \<rightarrow> \<langle>uint32_nat_rel O status_rel\<rangle>nres_rel\<close>
  unfolding isa_arena_status_def arena_status_def
  by (intro frefI nres_relI)
   (auto simp: arena_is_valid_clause_idx_def uint64_nat_rel_def br_def two_uint64_def
        list_rel_imp_same_length arena_length_uint64_conv arena_lifting
        arena_is_valid_clause_idx_and_access_def arena_length_literal_conv
        arena_is_valid_clause_vdom_def arena_status_literal_conv
      intro!: ASSERT_refine_left)


paragraph \<open>Swap literals\<close>

definition isa_arena_swap where
  \<open>isa_arena_swap C i j arena = do {
      ASSERT(C + i < length arena \<and> C + j < length arena);
      RETURN (swap arena (C+i) (C+j))
  }\<close>

lemma convert_swap[simp]: \<open>WB_More_Refinement_List.swap = IICF_List.swap\<close>
  unfolding swap_def WB_More_Refinement_List.swap_def
  by auto

lemma isa_arena_swap:
  \<open>(uncurry3 isa_arena_swap, uncurry3 (RETURN oooo swap_lits)) \<in>
    [uncurry3 swap_lits_pre]\<^sub>f
     nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel \<rightarrow>
    \<langle>\<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<rangle>nres_rel\<close>
  unfolding isa_arena_status_def arena_status_def
  by (intro frefI nres_relI)
   (auto simp: arena_is_valid_clause_idx_def uint64_nat_rel_def br_def two_uint64_def
        list_rel_imp_same_length arena_length_uint64_conv arena_lifting
        arena_is_valid_clause_idx_and_access_def arena_length_literal_conv
        arena_is_valid_clause_vdom_def arena_status_literal_conv
        isa_arena_swap_def swap_lits_def swap_lits_pre_def
      intro!: ASSERT_refine_left swap_param)


paragraph \<open>Update LBD\<close>

definition isa_update_lbd :: \<open>nat \<Rightarrow> uint32 \<Rightarrow> uint32 list \<Rightarrow> uint32 list nres\<close> where
  \<open>isa_update_lbd C lbd arena = do {
      ASSERT(C - LBD_SHIFT < length arena \<and> C \<ge> LBD_SHIFT);
      RETURN (arena [C - LBD_SHIFT := lbd])
  }\<close>

lemma arena_lbd_conv:
  assumes
    valid: \<open>valid_arena arena N x\<close> and
    j: \<open>j \<in># dom_m N\<close> and
    a: \<open>(a, arena) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close> and
    b: \<open>(b, bb) \<in> uint32_nat_rel\<close>
  shows
    \<open>j - LBD_SHIFT < length arena\<close> (is ?le) and
    \<open>(a[j - LBD_SHIFT := b], update_lbd j bb arena) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close>
       (is ?unat)
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
     by (auto split: if_splits simp: LBD_SHIFT_def)

  show ?unat
     using length a b
     by
      (auto simp: arena_el_rel_def unat_lit_rel_def arena_lit_def update_lbd_def
        uint32_nat_rel_def br_def Collect_eq_comp
       split: arena_el.splits
       intro!: list_rel_update')
qed

lemma isa_update_lbd:
  \<open>(uncurry2 isa_update_lbd, uncurry2 (RETURN ooo update_lbd)) \<in>
    [update_lbd_pre]\<^sub>f
     nat_rel \<times>\<^sub>f uint32_nat_rel \<times>\<^sub>f \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel \<rightarrow>
    \<langle>\<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<rangle>nres_rel\<close>
  unfolding isa_arena_status_def arena_status_def
  by (intro frefI nres_relI)
   (auto simp: arena_is_valid_clause_idx_def uint64_nat_rel_def br_def two_uint64_def
        list_rel_imp_same_length arena_length_uint64_conv arena_lifting
        arena_is_valid_clause_idx_and_access_def arena_lbd_conv
        arena_is_valid_clause_vdom_def arena_status_literal_conv
        update_lbd_pre_def
        isa_arena_swap_def swap_lits_def swap_lits_pre_def isa_update_lbd_def
      intro!: ASSERT_refine_left)


paragraph \<open>Get LBD\<close>

definition get_clause_LBD :: \<open>arena \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>get_clause_LBD arena C =  xarena_lbd (arena ! (C - LBD_SHIFT))\<close>


definition isa_get_clause_LBD :: \<open>uint32 list \<Rightarrow> nat \<Rightarrow> uint32 nres\<close> where
  \<open>isa_get_clause_LBD arena C = do {
      ASSERT(C - LBD_SHIFT < length arena \<and> C \<ge> LBD_SHIFT);
      RETURN (arena ! (C - LBD_SHIFT))
  }\<close>

lemma arena_get_lbd_conv:
  assumes
    valid: \<open>valid_arena arena N x\<close> and
    j: \<open>j \<in># dom_m N\<close> and
    a: \<open>(a, arena) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close>
  shows
    \<open>j - LBD_SHIFT < length arena\<close> (is ?le) and
    \<open>LBD_SHIFT \<le> j\<close> (is ?ge) and
    \<open>(a ! (j - LBD_SHIFT),
        xarena_lbd (arena ! (j - LBD_SHIFT)))
       \<in> uint32_nat_rel\<close>
proof -
  have j_le: \<open>j < length arena\<close> and
    length: \<open>length (N \<propto> j) = arena_length arena j\<close> and
    k1:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> N \<propto> j ! k = arena_lit arena (j + k)\<close> and
    k2:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> is_Lit (arena ! (j+k))\<close> and
    le: \<open>j + length (N \<propto> j) \<le> length arena\<close>  and
    j_ge: \<open>header_size (N \<propto> j) \<le> j\<close> and
    lbd: \<open>is_LBD (arena ! (j - LBD_SHIFT))\<close>
    using arena_lifting[OF valid j] by (auto simp: )
  show le': ?le
     using le j_ge unfolding length[symmetric] header_size_def
     by (auto split: if_splits simp: LBD_SHIFT_def)
  show ?ge
    using j_ge by (auto simp: SHIFTS_def header_size_def split: if_splits)
  have
    \<open>(a ! (j - LBD_SHIFT),
         (arena ! (j - LBD_SHIFT)))
       \<in> uint32_nat_rel O arena_el_rel\<close>
    by (rule param_nth[OF _ _ a]) (use j_le in auto)
  then show \<open>(a ! (j - LBD_SHIFT),
        xarena_lbd (arena ! (j - LBD_SHIFT)))
       \<in> uint32_nat_rel\<close>
    using lbd by (cases \<open>arena ! (j - LBD_SHIFT)\<close>) (auto simp: arena_el_rel_def)
qed

lemma isa_get_clause_LBD_get_clause_LBD:
  \<open>(uncurry isa_get_clause_LBD, uncurry (RETURN oo get_clause_LBD)) \<in>
    [uncurry get_clause_LBD_pre]\<^sub>f
     \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel \<times>\<^sub>f nat_rel \<rightarrow>
    \<langle>uint32_nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: isa_get_clause_LBD_def get_clause_LBD_def arena_get_lbd_conv
      get_clause_LBD_pre_def arena_is_valid_clause_idx_def
      list_rel_imp_same_length
      intro!: ASSERT_leI)


definition isa_get_saved_pos :: \<open>uint32 list \<Rightarrow> nat \<Rightarrow> uint64 nres\<close> where
  \<open>isa_get_saved_pos arena C = do {
      ASSERT(C - POS_SHIFT < length arena \<and> C \<ge> POS_SHIFT);
      RETURN (uint64_of_uint32 (arena ! (C - POS_SHIFT)) + two_uint64)
  }\<close>

lemma arena_get_pos_conv:
  assumes
    valid: \<open>valid_arena arena N x\<close> and
    j: \<open>j \<in># dom_m N\<close> and
    a: \<open>(a, arena) \<in> \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel\<close> and
    length: \<open>arena_length arena j > MAX_LENGTH_SHORT_CLAUSE\<close>
  shows
    \<open>j - POS_SHIFT < length arena\<close> (is ?le) and
    \<open>POS_SHIFT \<le> j\<close> (is ?ge) and
    \<open>(uint64_of_uint32 (a ! (j - POS_SHIFT)) + two_uint64,
        arena_pos arena j)
       \<in> uint64_nat_rel\<close> (is ?rel) and
    \<open>nat_of_uint64
        (uint64_of_uint32
          (a ! (j - POS_SHIFT)) +
         two_uint64) =
       Suc (Suc (xarena_pos
                  (arena ! (j - POS_SHIFT))))\<close> (is ?eq')
proof -
  have j_le: \<open>j < length arena\<close> and
    length: \<open>length (N \<propto> j) = arena_length arena j\<close> and
    k1:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> N \<propto> j ! k = arena_lit arena (j + k)\<close> and
    k2:\<open>\<And>k. k < length (N \<propto> j) \<Longrightarrow> is_Lit (arena ! (j+k))\<close> and
    le: \<open>j + length (N \<propto> j) \<le> length arena\<close>  and
    j_ge: \<open>header_size (N \<propto> j) \<le> j\<close> and
    lbd: \<open>is_Pos (arena ! (j - POS_SHIFT))\<close> and
    ge: \<open>length (N \<propto> j) > MAX_LENGTH_SHORT_CLAUSE\<close>
    using arena_lifting[OF valid j] length by (auto simp: is_short_clause_def)
  show le': ?le
     using le j_ge unfolding length[symmetric] header_size_def
     by (auto split: if_splits simp: POS_SHIFT_def)
  show ?ge
    using j_ge ge by (auto simp: SHIFTS_def header_size_def split: if_splits)
  have
    \<open>(a ! (j - POS_SHIFT),
         (arena ! (j - POS_SHIFT)))
       \<in> uint32_nat_rel O arena_el_rel\<close>
    by (rule param_nth[OF _ _ a]) (use j_le in auto)
  moreover have \<open>Suc (Suc (nat_of_uint32 (a ! (j - POS_SHIFT)))) \<le> uint64_max\<close>
    using nat_of_uint32_le_uint32_max[of \<open>a ! (j - POS_SHIFT)\<close>]
    unfolding uint64_max_def uint32_max_def
    by auto
  ultimately show ?rel
    using lbd apply (cases \<open>arena ! (j - POS_SHIFT)\<close>)
    by (auto simp: arena_el_rel_def
      uint64_nat_rel_def br_def two_uint64_def uint32_nat_rel_def nat_of_uint64_add
      uint64_of_uint32_def nat_of_uint64_add arena_pos_def
      nat_of_uint64_uint64_of_nat_id nat_of_uint32_le_uint64_max)
  then show ?eq'
    using lbd \<open>?rel\<close> apply (cases \<open>arena ! (j - POS_SHIFT)\<close>)
    by (auto simp: arena_el_rel_def
      uint64_nat_rel_def br_def two_uint64_def uint32_nat_rel_def nat_of_uint64_add
      uint64_of_uint32_def nat_of_uint64_add arena_pos_def
      nat_of_uint64_uint64_of_nat_id nat_of_uint32_le_uint64_max)
qed

lemma isa_get_saved_pos_get_saved_pos:
  \<open>(uncurry isa_get_saved_pos, uncurry (RETURN oo arena_pos)) \<in>
    [uncurry get_saved_pos_pre]\<^sub>f
     \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel \<times>\<^sub>f nat_rel \<rightarrow>
    \<langle>uint64_nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: isa_get_saved_pos_def arena_get_lbd_conv
      arena_is_valid_clause_idx_def arena_get_pos_conv
      list_rel_imp_same_length get_saved_pos_pre_def
      intro!: ASSERT_leI)

definition isa_get_saved_pos' :: \<open>uint32 list \<Rightarrow> nat \<Rightarrow> nat nres\<close> where
  \<open>isa_get_saved_pos' arena C = do {
      pos \<leftarrow> isa_get_saved_pos arena C;
      RETURN (nat_of_uint64 pos)
  }\<close>

lemma isa_get_saved_pos_get_saved_pos':
  \<open>(uncurry isa_get_saved_pos', uncurry (RETURN oo arena_pos)) \<in>
    [uncurry get_saved_pos_pre]\<^sub>f
     \<langle>uint32_nat_rel O arena_el_rel\<rangle>list_rel \<times>\<^sub>f nat_rel \<rightarrow>
    \<langle>nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: isa_get_saved_pos_def arena_pos_def
      arena_is_valid_clause_idx_def arena_get_pos_conv isa_get_saved_pos'_def
      list_rel_imp_same_length get_saved_pos_pre_def
      intro!: ASSERT_leI)


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
    unfolding and_nat_def or_nat_def
    by auto

  have [simp]: \<open>(a OR 4) AND 4 = 4\<close> for a :: nat
    supply [[show_types]]
    unfolding and_nat_def or_nat_def
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
    unfolding and_nat_def or_nat_def
    by auto

  have [simp]: \<open>(a OR 4) AND 4 = 4\<close> for a :: nat
    supply [[show_types]]
    unfolding and_nat_def or_nat_def
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

abbreviation arena_el_assn :: \<open>arena_el \<Rightarrow> uint32 \<Rightarrow> assn\<close> where
  \<open>arena_el_assn \<equiv> hr_comp uint32_nat_assn arena_el_rel\<close>

abbreviation arena_assn :: \<open>arena_el list \<Rightarrow> uint32 array_list \<Rightarrow> assn\<close> where
  \<open>arena_assn \<equiv> arl_assn arena_el_assn\<close>

abbreviation arena_fast_assn :: \<open>arena_el list \<Rightarrow> uint32 array_list64 \<Rightarrow> assn\<close> where
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
  \<in> [mark_garbage_pre]\<^sub>a arena_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow> arena_assn\<close>
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

definition arl64_get2 :: \<open>'a::heap array_list64 \<Rightarrow> nat \<Rightarrow> 'a Heap\<close> where
  \<open>arl64_get2 \<equiv> \<lambda>(a,n) i. Array.nth a i\<close>
thm arl64_get_hnr_aux
lemma arl64_get2_hnr_aux: \<open>(uncurry arl64_get2,uncurry (RETURN oo op_list_get)) \<in> [\<lambda>(l,i). i<length l]\<^sub>a (is_array_list64\<^sup>k *\<^sub>a nat_assn\<^sup>k) \<rightarrow> id_assn\<close>
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