theory IsaSAT_Bump_Heuristics
  imports Watched_Literals_VMTF
    IsaSAT_VMTF
    IsaSAT_VSIDS
    Tuple4
begin



section \<open>Backtrack level for Restarts\<close>

hide_const (open) find_decomp_wl_imp
  
text \<open>
  We here find out how many decisions can be reused. Remark that since VMTF does not reuse many levels anyway,
  the implementation might be mostly useless, but I was not aware of that when I implemented it.
\<close>
(* TODO ded-uplicate definitions *)
definition find_decomp_w_ns_pre where
  \<open>find_decomp_w_ns_pre \<A> = (\<lambda>((M, highest), vm).
       no_dup M \<and>
       highest < count_decided M \<and>
       isasat_input_bounded \<A> \<and>
       literals_are_in_\<L>\<^sub>i\<^sub>n_trail \<A> M \<and>
       vm \<in> bump_heur \<A> M)\<close>

definition find_decomp_wl_imp
  :: \<open>nat multiset \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> nat \<Rightarrow> bump_heuristics \<Rightarrow>
       ((nat, nat) ann_lits \<times> bump_heuristics) nres\<close>
where
  \<open>find_decomp_wl_imp \<A> = (\<lambda>M\<^sub>0 lev vm. do {
    let k = count_decided M\<^sub>0;
    let M\<^sub>0 = trail_conv_to_no_CS M\<^sub>0;
    let n = length M\<^sub>0;
    pos \<leftarrow> get_pos_of_level_in_trail M\<^sub>0 lev;
    ASSERT((n - pos) \<le> uint32_max);
    ASSERT(n \<ge> pos);
    let target = n - pos;
    (_, M, vm') \<leftarrow>
       WHILE\<^sub>T\<^bsup>\<lambda>(j, M, vm'). j \<le> target \<and>
           M = drop j M\<^sub>0 \<and> target \<le> length M\<^sub>0 \<and>
           vm' \<in> bump_heur \<A> M \<and> literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (lit_of `# mset M)\<^esup>
         (\<lambda>(j, M, vm). j < target)
         (\<lambda>(j, M, vm). do {
            ASSERT(M \<noteq> []);
            ASSERT(Suc j \<le> uint32_max);
            let L = atm_of (lit_of_hd_trail M);
            ASSERT(L \<in># \<A>);
            RETURN (j + 1, tl M, isa_vmtf_unset L vm)
         })
         (0, M\<^sub>0, vm);
    ASSERT(lev = count_decided M);
    let M = trail_conv_back lev M;
    RETURN (M, vm')
  })\<close>

definition isa_find_decomp_wl_imp
  :: \<open>trail_pol \<Rightarrow> nat \<Rightarrow> bump_heuristics \<Rightarrow> (trail_pol \<times> bump_heuristics) nres\<close>
where
  \<open>isa_find_decomp_wl_imp = (\<lambda>M\<^sub>0 lev vm. do {
    let k = count_decided_pol M\<^sub>0;
    let M\<^sub>0 = trail_pol_conv_to_no_CS M\<^sub>0;
    ASSERT(isa_length_trail_pre M\<^sub>0);
    let n = isa_length_trail M\<^sub>0;
    pos \<leftarrow> get_pos_of_level_in_trail_imp M\<^sub>0 lev;
    ASSERT((n - pos) \<le> uint32_max);
    ASSERT(n \<ge> pos);
    let target = n - pos;
    (_, M, vm') \<leftarrow>
       WHILE\<^sub>T\<^bsup>\<lambda>(j, M, vm'). j \<le> target\<^esup>
         (\<lambda>(j, M, vm). j < target)
         (\<lambda>(j, M, vm). do {
            ASSERT(Suc j \<le> uint32_max);
            ASSERT(case M of (M, _) \<Rightarrow> M \<noteq> []);
            ASSERT(tl_trailt_tr_no_CS_pre M);
            let L = atm_of (lit_of_last_trail_pol M);
            ASSERT(vmtf_unset_pre L vm);
            RETURN (j + 1, tl_trailt_tr_no_CS M, isa_vmtf_unset L vm)
         })
         (0, M\<^sub>0, vm);
    M \<leftarrow> trail_conv_back_imp lev M;
    RETURN (M, vm')
  })\<close>


abbreviation find_decomp_w_ns_prop where
  \<open>find_decomp_w_ns_prop \<A> \<equiv>
     (\<lambda>(M::(nat, nat) ann_lits) highest _.
        (\<lambda>(M1, vm). \<exists>K M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
          get_level M K = Suc highest \<and> vm \<in> vmtf \<A> M1))\<close>

definition find_decomp_w_ns where
  \<open>find_decomp_w_ns \<A> =
     (\<lambda>(M::(nat, nat) ann_lits) highest vm.
        SPEC(find_decomp_w_ns_prop \<A> M highest vm))\<close>

lemma isa_find_decomp_wl_imp_find_decomp_wl_imp:
  \<open>(uncurry2 isa_find_decomp_wl_imp, uncurry2 (find_decomp_wl_imp \<A>)) \<in>
     [\<lambda>((M, lev), vm). lev < count_decided M]\<^sub>f trail_pol \<A> \<times>\<^sub>f nat_rel \<times>\<^sub>f (Id \<times>\<^sub>r distinct_atoms_rel \<A>) \<rightarrow>
     \<langle>trail_pol \<A> \<times>\<^sub>r (Id \<times>\<^sub>r distinct_atoms_rel \<A>)\<rangle>nres_rel\<close>
proof -
  have [intro]: \<open>(M', M) \<in> trail_pol \<A> \<Longrightarrow>  (M', M) \<in> trail_pol_no_CS \<A>\<close> for M' M
    by (auto simp: trail_pol_def trail_pol_no_CS_def control_stack_length_count_dec[symmetric])

  have [refine0]: \<open>((0, trail_pol_conv_to_no_CS x1c, x2c),
        0, trail_conv_to_no_CS x1a, x2a)
        \<in> nat_rel \<times>\<^sub>r trail_pol_no_CS \<A> \<times>\<^sub>r (Id \<times>\<^sub>r distinct_atoms_rel \<A>)\<close>
    if
      \<open>case y of
       (x, xa) \<Rightarrow> (case x of (M, lev) \<Rightarrow> \<lambda>_. lev < count_decided M) xa\<close> and
      \<open>(x, y)
       \<in> trail_pol \<A> \<times>\<^sub>f nat_rel \<times>\<^sub>f (Id \<times>\<^sub>f distinct_atoms_rel \<A>)\<close> and   \<open>x1 = (x1a, x2)\<close> and
      \<open>y = (x1, x2a)\<close> and
      \<open>x1b = (x1c, x2b)\<close> and
      \<open>x = (x1b, x2c)\<close> and
      \<open>isa_length_trail_pre (trail_pol_conv_to_no_CS x1c)\<close> and
      \<open>(pos, posa) \<in> nat_rel\<close> and
      \<open>length (trail_conv_to_no_CS x1a) - posa \<le> uint32_max\<close> and
      \<open>isa_length_trail (trail_pol_conv_to_no_CS x1c) - pos \<le> uint32_max\<close> and
      \<open>case (0, trail_conv_to_no_CS x1a, x2a) of
       (j, M, vm') \<Rightarrow>
         j \<le> length (trail_conv_to_no_CS x1a) - posa \<and>
         M = drop j (trail_conv_to_no_CS x1a) \<and>
         length (trail_conv_to_no_CS x1a) - posa
         \<le> length (trail_conv_to_no_CS x1a) \<and>
         vm' \<in> vmtf \<A> M \<and> literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (lit_of `# mset M)\<close>
     for x y x1 x1a x2 x2a x1b x1c x2b x2c pos posa
  proof -
    show ?thesis
      supply trail_pol_conv_to_no_CS_def[simp] trail_conv_to_no_CS_def[simp]
      using that by auto
  qed
  have trail_pol_empty: \<open>(([], x2g), M) \<in> trail_pol_no_CS \<A> \<Longrightarrow> M = []\<close> for M x2g
    by (auto simp: trail_pol_no_CS_def ann_lits_split_reasons_def)

  have isa_vmtf: \<open>(x2c, x2a) \<in> Id \<times>\<^sub>f distinct_atoms_rel \<A> \<Longrightarrow>
       (((aa, ab, ac, ad, ba), baa, ca), x2e) \<in> Id \<times>\<^sub>f distinct_atoms_rel \<A> \<Longrightarrow>
       x2e \<in> vmtf \<A> (drop x1d x1a) \<Longrightarrow>
       ((aa, ab, ac, ad, ba), baa, ca) \<in> bump_heur \<A> (drop x1d x1a)\<close>
       for x y x1 x1a x2 x2a x1b x1c x2b x2c pos posa xa x' x1d x2d x1e x2e x1f x2f
       x1g x1h x2g x2h aa ab ac ad ba baa ca
       by (cases x2e)
        (auto 6 6 simp: isa_vmtf_def Image_iff converse_iff prod_rel_iff
         intro!: bexI[of _ x2e])
  have trail_pol_no_CS_last_hd:
    \<open>((x1h, t), M) \<in> trail_pol_no_CS \<A> \<Longrightarrow> M \<noteq> [] \<Longrightarrow> (last x1h) = lit_of (hd M)\<close>
    for x1h t M
    by (auto simp: trail_pol_no_CS_def ann_lits_split_reasons_def last_map last_rev)

  have trail_conv_back: \<open>trail_conv_back_imp x2b x1g
        \<le> SPEC
           (\<lambda>c. (c, trail_conv_back x2 x1e)
                \<in> trail_pol \<A>)\<close>
    if
      \<open>case y of (x, xa) \<Rightarrow> (case x of (M, lev) \<Rightarrow> \<lambda>vm. lev < count_decided M) xa\<close> and
      \<open>(x, y) \<in> trail_pol \<A> \<times>\<^sub>f nat_rel \<times>\<^sub>f (Id \<times>\<^sub>f distinct_atoms_rel \<A>)\<close> and
      \<open>x1 = (x1a, x2)\<close> and
      \<open>y = (x1, x2a)\<close> and
      \<open>x1b = (x1c, x2b)\<close> and
      \<open>x = (x1b, x2c)\<close> and
      \<open>isa_length_trail_pre (trail_pol_conv_to_no_CS x1c)\<close> and
      \<open>(pos, posa) \<in> nat_rel\<close> and
      \<open>length (trail_conv_to_no_CS x1a) - posa \<le> uint32_max\<close> and
      \<open>isa_length_trail (trail_pol_conv_to_no_CS x1c) - pos \<le> uint32_max\<close> and
      \<open>(xa, x') \<in> nat_rel \<times>\<^sub>f (trail_pol_no_CS \<A> \<times>\<^sub>f (Id \<times>\<^sub>f distinct_atoms_rel \<A>))\<close> and
       \<open>x2d = (x1e, x2e)\<close> and
      \<open>x' = (x1d, x2d)\<close> and
      \<open>x2f = (x1g, x2g)\<close> and
      \<open>xa = (x1f, x2f)\<close> and
      \<open>x2 = count_decided x1e\<close>
    for x y x1 x1a x2 x2a x1b x1c x2b x2c pos posa xa x' x1d x2d x1e x2e x1f x2f
       x1g x2g
   apply (rule trail_conv_back[THEN fref_to_Down_curry, THEN order_trans])
   using that by (auto simp: conc_fun_RETURN)


  show ?thesis
    supply trail_pol_conv_to_no_CS_def[simp] trail_conv_to_no_CS_def[simp]
    unfolding isa_find_decomp_wl_imp_def find_decomp_wl_imp_def uncurry_def
    apply (intro frefI nres_relI)
    apply (refine_vcg
      id_trail_conv_to_no_CS[THEN fref_to_Down, unfolded comp_def]
      get_pos_of_level_in_trail_imp_get_pos_of_level_in_trail[of \<A>, THEN fref_to_Down_curry])
    subgoal
      by (rule isa_length_trail_pre) auto
    subgoal
      by (auto simp: get_pos_of_level_in_trail_pre_def)
    subgoal
      by auto
    subgoal
      by (subst isa_length_trail_length_u_no_CS[THEN fref_to_Down_unRET_Id]) auto
    subgoal
      by (subst isa_length_trail_length_u_no_CS[THEN fref_to_Down_unRET_Id]) auto
    apply (assumption+)[10]
    subgoal
      by (subst isa_length_trail_length_u_no_CS[THEN fref_to_Down_unRET_Id]) auto
    subgoal
      by (subst isa_length_trail_length_u_no_CS[THEN fref_to_Down_unRET_Id]) auto
    subgoal
      by (auto dest!: trail_pol_empty)
    subgoal
      by (auto dest!: trail_pol_empty)
    subgoal for x y x1 x1a x2 x2a x1b x1c x2b x2c pos posa
      by (rule tl_trailt_tr_no_CS_pre) auto
    subgoal for x y x1 x1a x2 x2a x1b x1c x2b x2c pos posa xa x' x1d x2d x1e x2e x1f x2f
       x1g x1h x2g x2h
       by (cases x1g, cases x2h)
         (auto intro!: vmtf_unset_pre[of _ _ _ _ _ _ \<A> \<open>drop x1d x1a\<close>] isa_vmtf
           simp: lit_of_last_trail_pol_def trail_pol_no_CS_last_hd lit_of_hd_trail_def)
    subgoal
      by (auto simp: lit_of_last_trail_pol_def trail_pol_no_CS_last_hd lit_of_hd_trail_def
        intro!: tl_trail_tr_no_CS[THEN fref_to_Down_unRET]
          isa_vmtf_unset_vmtf_unset[THEN fref_to_Down_unRET_uncurry])
    apply (rule trail_conv_back; assumption)
    subgoal
      by auto
  done
qed


definition (in -) find_decomp_wl_st :: \<open>nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close> where
  \<open>find_decomp_wl_st = (\<lambda>L (M, N, D, oth).  do{
     M' \<leftarrow> find_decomp_wl' M (the D) L;
    RETURN (M', N, D, oth)
  })\<close>

definition find_decomp_wl_st_int :: \<open>nat \<Rightarrow> isasat \<Rightarrow> isasat nres\<close> where
  \<open>find_decomp_wl_st_int = (\<lambda>highest S. do{
     let M = get_trail_wl_heur S;
     let vm = get_vmtf_heur S;
     (M', vm) \<leftarrow> isa_find_decomp_wl_imp M highest vm;
     let S = set_trail_wl_heur M' S;
     let S = set_vmtf_wl_heur vm S;
     RETURN S
  })\<close>

lemma
  assumes
    vm: \<open>vm \<in> vmtf \<A> M\<^sub>0\<close> and
    lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail \<A> M\<^sub>0\<close> and
    target: \<open>highest < count_decided M\<^sub>0\<close> and
    n_d: \<open>no_dup M\<^sub>0\<close> and
    bounded: \<open>isasat_input_bounded \<A>\<close>
  shows
    find_decomp_wl_imp_le_find_decomp_wl':
      \<open>find_decomp_wl_imp \<A> M\<^sub>0 highest vm \<le> find_decomp_w_ns \<A> M\<^sub>0 highest vm\<close>
     (is ?decomp)
proof -
  have length_M0:  \<open>length M\<^sub>0 \<le> uint32_max div 2 + 1\<close>
    using length_trail_uint32_max_div2[of \<A> M\<^sub>0, OF bounded]
      n_d literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l[of \<A>, OF lits]
    by (auto simp: lits_of_def)
  have 1: \<open>((count_decided x1g, x1g), count_decided x1, x1) \<in> Id\<close>
    if \<open>x1g = x1\<close> for x1g x1 :: \<open>(nat, nat) ann_lits\<close>
    using that by auto
  have [simp]: \<open>\<exists>M'a. M' @ x2g = M'a @ tl x2g\<close> for M' x2g :: \<open>(nat, nat) ann_lits\<close>
    by (rule exI[of _ \<open>M' @ (if x2g = [] then [] else [hd x2g])\<close>]) auto
  have butlast_nil_iff: \<open>butlast xs = [] \<longleftrightarrow> xs = [] \<or> (\<exists>a. xs = [a])\<close> for xs :: \<open>(nat, nat) ann_lits\<close>
    by (cases xs) auto
  have butlast1: \<open>tl x2g = drop (Suc (length x1) - length x2g) x1\<close> (is \<open>?G1\<close>)
    if \<open>x2g = drop (length x1 - length x2g) x1\<close> for x2g x1 :: \<open>'a list\<close>
  proof -
    have [simp]: \<open>Suc (length x1 - length x2g) = Suc (length x1) - length x2g\<close>
      by (metis Suc_diff_le diff_le_mono2 diff_zero length_drop that zero_le)
    show ?G1
      by (subst that) (auto simp: butlast_conv_take tl_drop_def)[]
  qed
  have butlast2: \<open>tl x2g = drop (length x1 - (length x2g - Suc 0)) x1\<close> (is \<open>?G2\<close>)
    if \<open>x2g = drop (length x1 - length x2g) x1\<close> and x2g: \<open>x2g \<noteq> []\<close> for x2g x1 :: \<open>'a list\<close>
  proof -
    have [simp]: \<open>Suc (length x1 - length x2g) = Suc (length x1) - length x2g\<close>
      by (metis Suc_diff_le diff_le_mono2 diff_zero length_drop that(1) zero_le)
    have [simp]: \<open>Suc (length x1) - length x2g = length x1 - (length x2g - Suc 0)\<close>
      using x2g by auto
    show ?G2
      by (subst that) (auto simp: butlast_conv_take tl_drop_def)[]
  qed
  note butlast = butlast1 butlast2

  have count_decided_not_Nil[simp]:  \<open>0 < count_decided M \<Longrightarrow> M \<noteq> []\<close> for M :: \<open>(nat, nat) ann_lits\<close>
    by auto
  have get_lev_last: \<open>get_level (M' @ M) (lit_of (last M')) = Suc (count_decided M)\<close>
    if \<open>M\<^sub>0 = M' @ M\<close> and \<open>M' \<noteq> []\<close> and \<open>is_decided (last M')\<close> for M' M
    apply (cases M' rule: rev_cases)
    using that apply (solves simp)
    using n_d that by auto

  have atm_of_N:
    \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (lit_of `# mset aa) \<Longrightarrow> aa \<noteq> [] \<Longrightarrow> atm_of (lit_of (hd aa)) \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
    for aa
    by (cases aa) (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
  have Lin_drop_tl: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (lit_of `# mset (drop b M\<^sub>0)) \<Longrightarrow>
      literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (lit_of `# mset (tl (drop b M\<^sub>0)))\<close> for b
    apply (rule literals_are_in_\<L>\<^sub>i\<^sub>n_mono)
     apply assumption
    by (cases \<open>drop b M\<^sub>0\<close>) auto

  have highest: \<open>highest = count_decided M\<close> and
     ex_decomp: \<open>\<exists>K M2.
       (Decided K # M, M2)
       \<in> set (get_all_ann_decomposition M\<^sub>0) \<and>
       get_level M\<^sub>0 K = Suc highest \<and> vm \<in> vmtf \<A> M\<close>
    if
      pos: \<open>pos < length M\<^sub>0 \<and> is_decided (rev M\<^sub>0 ! pos) \<and> get_level M\<^sub>0 (lit_of (rev M\<^sub>0 ! pos)) =
         highest + 1\<close> and
      \<open>length M\<^sub>0 - pos \<le> uint32_max\<close> and
      inv: \<open>case s of (j, M, vm') \<Rightarrow>
         j \<le> length M\<^sub>0 - pos \<and>
         M = drop j M\<^sub>0 \<and>
         length M\<^sub>0 - pos \<le> length M\<^sub>0 \<and>
         vm' \<in> vmtf \<A> M \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (lit_of `# mset M)\<close> and
      cond: \<open>\<not> (case s of
         (j, M, vm) \<Rightarrow> j < length M\<^sub>0 - pos)\<close> and
      s: \<open>s = (j, s')\<close> \<open>s' = (M, vm)\<close>
    for pos s j s' M vm
  proof -
    have
      \<open>j = length M\<^sub>0 - pos\<close> and
      M: \<open>M = drop (length M\<^sub>0 - pos) M\<^sub>0\<close> and
      vm: \<open>vm \<in> vmtf \<A> (drop (length M\<^sub>0 - pos) M\<^sub>0)\<close> and
      \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (lit_of `# mset (drop (length M\<^sub>0 - pos) M\<^sub>0))\<close>
      using cond inv unfolding s
      by auto
    define M2 and L where \<open>M2 = take (length M\<^sub>0 - Suc pos) M\<^sub>0\<close> and \<open>L = rev M\<^sub>0 ! pos\<close>
    have le_Suc_pos: \<open>length M\<^sub>0 - pos = Suc (length M\<^sub>0 - Suc pos)\<close>
      using pos by auto
    have 1: \<open>take (length M\<^sub>0 - pos) M\<^sub>0 = take (length M\<^sub>0 - Suc pos) M\<^sub>0 @ [rev M\<^sub>0 ! pos]\<close>
      unfolding le_Suc_pos
      apply (subst take_Suc_conv_app_nth)
      using pos by (auto simp: rev_nth)
    have M\<^sub>0: \<open>M\<^sub>0 = M2 @ L # M\<close>
      apply (subst append_take_drop_id[symmetric, of _ \<open>length M\<^sub>0 - pos\<close>])
      unfolding M L_def M2_def 1
      by auto
    have L': \<open>Decided (lit_of L) = L\<close>
      using pos unfolding L_def[symmetric] by (cases L) auto
    then have M\<^sub>0': \<open>M\<^sub>0 = M2 @ Decided (lit_of L) # M\<close>
      unfolding M\<^sub>0 by auto

    have \<open>highest = count_decided M\<close> and \<open>get_level M\<^sub>0 (lit_of L) = Suc highest\<close> and \<open>is_decided L\<close>
      using n_d pos unfolding L_def[symmetric] unfolding M\<^sub>0
      by (auto simp: get_level_append_if split: if_splits)
    then show
     \<open>\<exists>K M2.
       (Decided K # M, M2)
       \<in> set (get_all_ann_decomposition M\<^sub>0) \<and>
       get_level M\<^sub>0 K = Suc highest \<and> vm \<in> vmtf \<A> M\<close>
      using get_all_ann_decomposition_ex[of \<open>lit_of L\<close> M M2] vm unfolding M\<^sub>0'[symmetric] M[symmetric]
      by blast
    show \<open>highest = count_decided M\<close>
      using  \<open>highest = count_decided M\<close> .
  qed
  show ?decomp
    unfolding find_decomp_wl_imp_def Let_def find_decomp_w_ns_def trail_conv_to_no_CS_def
      get_pos_of_level_in_trail_def trail_conv_back_def
    apply (refine_vcg 1 WHILEIT_rule[where R=\<open>measure (\<lambda>(_, M, _). length M)\<close>])
    subgoal using length_M0 unfolding uint32_max_def by simp
    subgoal by auto
    subgoal by auto
    subgoal using target by (auto simp: count_decided_ge_get_maximum_level)
    subgoal by auto
    subgoal by auto
    subgoal using vm by auto
    subgoal using lits unfolding literals_are_in_\<L>\<^sub>i\<^sub>n_trail_lit_of_mset by auto
    subgoal for target s j b M vm by simp
    subgoal using length_M0 unfolding uint32_max_def by simp
    subgoal for x s a ab aa bb
      by (cases \<open>drop a M\<^sub>0\<close>)
        (auto simp: lit_of_hd_trail_def literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset)
    subgoal by auto
    subgoal by (auto simp: drop_Suc drop_tl)
    subgoal by auto
    subgoal for s a b aa ba vm x2 x1a x2a
      by (cases vm)
        (auto intro!: vmtf_unset_vmtf_tl atm_of_N drop_tl simp: lit_of_hd_trail_def)
    subgoal for s a b aa ba x1 x2 x1a x2a
      using lits by (auto intro: Lin_drop_tl)
    subgoal by auto
    subgoal by (rule highest)
    subgoal by (rule ex_decomp) (assumption+, auto)
    done
qed


lemma find_decomp_wl_imp_find_decomp_wl':
  \<open>(uncurry2 (find_decomp_wl_imp \<A>), uncurry2 (find_decomp_w_ns \<A>)) \<in>
    [find_decomp_w_ns_pre \<A>]\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id \<times>\<^sub>f Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
   (auto simp: find_decomp_w_ns_pre_def simp del: twl_st_of_wl.simps
       intro!: find_decomp_wl_imp_le_find_decomp_wl')

lemma find_decomp_wl_imp_code_conbine_cond:
  \<open>(\<lambda>((b, a), c). find_decomp_w_ns_pre \<A> ((b, a), c) \<and> a < count_decided b) = (\<lambda>((b, a), c).
         find_decomp_w_ns_pre \<A> ((b, a), c))\<close>
  by (auto intro!: ext simp: find_decomp_w_ns_pre_def)

end


end