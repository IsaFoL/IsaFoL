theory IsaSAT_ACIDS
  imports IsaSAT_Literals
    Pairing_Heap_LLVM.Heaps_Abs
    Watched_Literals_VMTF
begin
text \<open>Instead of using VSIDS (which requires float), we use the more stable ACIDS variant
  that works simply on integers and does not seem much worse.

  We use ACIDS in a practical way, i.e., when the weight reaches the maximum
integer, we simply stop incrementing it. \<close>

(*TODO rename VSIDS to ACIDS even if the difference is simply the bumping score*)
section \<open>ACIDS\<close>

type_synonym ('a, 'v) acids = \<open>('a multiset \<times> 'a multiset \<times> ('a \<Rightarrow> 'v)) \<times> 'v\<close>
definition acids :: \<open>'a multiset \<Rightarrow> ('a, 'ann) ann_lits \<Rightarrow> ('a, 'v::{zero,linorder}) acids set\<close> where
\<open>acids \<A> M = {((\<B>, b, w), m). set_mset \<B> = set_mset \<A> \<and> b \<subseteq># \<A> \<and> Max ({0} \<union> w ` set_mset b) \<le> m \<and> (\<forall>L \<in>#\<A>. L \<notin># b \<longrightarrow> defined_lit M (Pos L)) \<and> distinct_mset b}\<close>

lemma acids_prepend: \<open>ac \<in> acids \<A> M \<Longrightarrow> ac \<in> acids \<A> (L # M)\<close>
  unfolding acids_def by (auto simp: defined_lit_map)

interpretation ACIDS: hmstruct_with_prio where
  le = \<open>(\<ge>) :: nat \<Rightarrow> nat \<Rightarrow> bool\<close> and
  lt = \<open>(>)\<close>
  apply unfold_locales
  subgoal by auto
  subgoal by auto
  subgoal by (auto simp: transp_def)
  subgoal by (auto simp: totalp_on_def)
  done

definition acids_tl_pre :: \<open>'a \<Rightarrow> ('a, 'v) acids \<Rightarrow> bool\<close> where
  \<open>acids_tl_pre L = (\<lambda>(ac, m). L \<in># fst ac)\<close>

definition acids_tl :: \<open>'a \<Rightarrow> ('a, 'v::ord) acids \<Rightarrow> ('a, 'v) acids nres\<close> where
  \<open>acids_tl L = (\<lambda>(ac, m). do {
    ASSERT (acids_tl_pre L (ac, m));
    ac \<leftarrow> ACIDS.mop_prio_insert_unchanged L ac;
    w \<leftarrow> ACIDS.mop_prio_old_weight L ac;
    RETURN (ac, max m w)
  })\<close>

lemma acids_tl:
  \<open>ac \<in> acids \<A> M \<Longrightarrow> L \<in># \<A> \<Longrightarrow> M \<noteq> [] \<Longrightarrow> L = atm_of (lit_of (hd M)) \<Longrightarrow> acids_tl L ac \<le> RES (acids \<A> (tl M))\<close>
  unfolding acids_tl_def ACIDS.mop_prio_insert_unchanged_def
    ACIDS.mop_prio_insert_raw_unchanged_def nres_monad3
    ACIDS.mop_prio_is_in_def
    ACIDS.mop_prio_old_weight_def
    ACIDS.mop_prio_insert_def RES_RES_RETURN_RES RETURN_def
    ACIDS.mop_prio_old_weight_def case_prod_beta nres_monad1
  apply (refine_vcg lhs_step_If)
  subgoal
    by (cases M) (auto simp: acids_def ACIDS.mop_prio_insert_unchanged_def insert_subset_eq_iff
        acids_tl_pre_def
      intro!: subset_add_mset_notin_subset)
  subgoal
    by (auto simp: acids_def ACIDS.mop_prio_insert_unchanged_def insert_subset_eq_iff
        acids_tl_pre_def
      intro!: subset_add_mset_notin_subset)
  subgoal
    apply (auto simp: acids_def ACIDS.mop_prio_insert_unchanged_def RES_RES_RETURN_RES
      defined_lit_map acids_tl_pre_def dest: subset_add_mset_notin_subset
      dest: multi_member_split)
    apply (smt (verit, best) image_iff not_hd_in_tl)
    apply refine_vcg
    apply fastforce
    apply fastforce
    apply (smt (verit, del_insts) Union_iff imageE insert_DiffM insert_subset_eq_iff prod.simps(1)
      singletonD subset_add_mset_notin_subset_mset)
    apply (auto simp: max_def)
    apply fastforce
    by (smt (verit, best) image_iff not_hd_in_tl)
  done

definition acids_get_min :: \<open>('a, nat) acids \<Rightarrow> 'a nres\<close> where
  \<open>acids_get_min = (\<lambda>(ac, m). do {
    L \<leftarrow> ACIDS.mop_prio_peek_min ac;
    RETURN L
  })\<close>

definition acids_mset :: \<open>('a, 'v) acids \<Rightarrow> _\<close> where
  \<open>acids_mset x = fst (snd (fst x))\<close>

lemma acids_get_min:
  \<open>acids_mset x \<noteq> {#} \<Longrightarrow> acids_get_min x \<le> SPEC (\<lambda>v. ACIDS.prio_peek_min (fst x) v)\<close>
  unfolding acids_get_min_def ACIDS.mop_prio_peek_min_def acids_mset_def
  by refine_vcg (auto simp: ACIDS.prio_peek_min_def)

definition acids_pop_min :: \<open>('a, nat) acids \<Rightarrow> ('a \<times> ('a, nat) acids) nres\<close> where
  \<open>acids_pop_min = (\<lambda>(ac, m). do {
    (v, ac) \<leftarrow> ACIDS.mop_prio_pop_min ac;
    RETURN (v, (ac, m))
  })\<close>

definition acids_find_next_undef :: \<open>nat multiset \<Rightarrow> (nat, nat) acids \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> (nat option \<times> (nat, nat) acids) nres\<close> where
\<open>acids_find_next_undef \<A> = (\<lambda>ac M. do {
  WHILE\<^sub>T\<^bsup>(\<lambda>(L, ac).
        (L = None \<longrightarrow> ac \<in> acids \<A> M) \<and>
        (L \<noteq> None \<longrightarrow> ac \<in> acids \<A> (Decided (Pos (the L)) # M) \<and> Pos (the L) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<and> undefined_lit M (Pos (the L))))
  \<^esup>
      (\<lambda>(nxt, ac). nxt = None \<and> acids_mset ac \<noteq> {#})
      (\<lambda>(a, ac). do {
         ASSERT (a = None);
         (L, ac) \<leftarrow> acids_pop_min ac;
         ASSERT(Pos L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l  \<A>);
         if defined_lit M (Pos L) then RETURN (None, ac)
         else RETURN (Some L, ac)
        }
      )
      (None, ac)
  })\<close>

lemma acids_pop_min:
  \<open>acids_mset x \<noteq> {#} \<Longrightarrow> x \<in> acids \<A> M \<Longrightarrow>
  acids_pop_min x \<le> SPEC (\<lambda>(v, ac). acids_mset ac = acids_mset x - {#v#} \<and> v \<in># acids_mset x \<and>
    ACIDS.prio_peek_min (fst x) v \<and>
    (defined_lit M (Pos v) \<longrightarrow> ac \<in> acids \<A> M) \<and>
    (undefined_lit M (Pos v) \<longrightarrow> ac \<in> acids \<A> (Decided (Pos v) # M)))\<close>
  unfolding ACIDS.mop_prio_pop_min_def acids_pop_min_def
    ACIDS.mop_prio_peek_min_def ACIDS.mop_prio_del_def
  by refine_vcg
   (auto simp: acids_def ACIDS.prio_peek_min_def distinct_mset_remove1_All ACIDS.prio_del_def
      defined_lit_map acids_mset_def dest: in_diffD)

lemma acids_find_next_undef:
  assumes
    vmtf: \<open>ac \<in> acids \<A> M\<close>
  shows \<open>acids_find_next_undef \<A> ac M
     \<le> \<Down> Id (SPEC (\<lambda>(L, ac).
        (L = None \<longrightarrow> ac \<in> acids \<A> M \<and> (\<forall>L\<in>#\<L>\<^sub>a\<^sub>l\<^sub>l \<A>. defined_lit M L)) \<and>
        (L \<noteq> None \<longrightarrow> ac \<in> acids \<A> (Decided (Pos (the L)) # M) \<and> Pos (the L) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<and> undefined_lit M (Pos (the L)))))\<close>
proof -
  have [refine0]: \<open>wf (measure (\<lambda>(_, ac). size (acids_mset ac)))\<close>
    by auto
  show ?thesis
    unfolding acids_find_next_undef_def
    apply (refine_vcg acids_pop_min[of _ \<A> M, THEN order_trans])
    subgoal using assms by auto
    subgoal by auto
    subgoal by (auto simp: ACIDS.prio_peek_min_def acids_def acids_mset_def
      in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: acids_def ACIDS.prio_peek_min_def
      in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: ACIDS.prio_peek_min_def acids_mset_def dest: multi_member_split)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: ACIDS.prio_peek_min_def acids_mset_def dest: multi_member_split)
    subgoal by auto
    subgoal by (auto simp: ACIDS.prio_peek_min_def acids_mset_def acids_def
      in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n dest!: multi_member_split[of \<open>_ :: nat\<close>])
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

definition acids_push_literal_pre where
  \<open>acids_push_literal_pre \<A> L = (\<lambda>ac. L \<in># \<A>)\<close>

definition acids_push_literal :: \<open>'a \<Rightarrow> ('a, nat) acids \<Rightarrow> ('a, nat) acids nres\<close> where
  \<open>acids_push_literal L = (\<lambda>(ac, m). do {
  ASSERT (L \<in># fst ac);
  w \<leftarrow> ACIDS.mop_prio_old_weight L ac;
  let w = min m w;
  ASSERT (w \<le> m);
  ASSERT ((m - w) div 2 \<le> m);
  let w = m - ((m - w) div 2);
  ac \<leftarrow> ACIDS.mop_prio_insert_maybe L w ac;
  RETURN (ac, m)
  })\<close>

lemma acids_push_literal:
  \<open>ac \<in> acids \<A> M \<Longrightarrow> acids_push_literal_pre \<A> L ac \<Longrightarrow> acids_push_literal L ac \<le> SPEC (\<lambda>ac. ac \<in> acids \<A> M)\<close>
  unfolding acids_push_literal_def ACIDS.mop_prio_insert_maybe_def
    ACIDS.mop_prio_old_weight_def acids_push_literal_pre_def
    ACIDS.mop_prio_insert_def ACIDS.mop_prio_change_weight_def
    ACIDS.mop_prio_is_in_def
  apply refine_vcg
  subgoal by (auto simp: acids_def acids_mset_def)
  subgoal by (auto simp: acids_def dest!: multi_member_split)
  subgoal by (auto simp: ACIDS.mop_prio_change_weight_def acids_def
    dest!: multi_member_split)
  subgoal by (auto simp: acids_def dest!: multi_member_split)
  subgoal by (auto simp: acids_def acids_mset_def)
  subgoal by (auto simp: acids_def acids_mset_def dest!: multi_member_split
    dest: subset_add_mset_notin_subset)
  subgoal by (auto simp: acids_def acids_mset_def dest!: multi_member_split
    dest: subset_add_mset_notin_subset)
  subgoal by (auto simp: acids_def acids_mset_def dest!: multi_member_split
    dest: subset_add_mset_notin_subset)
  subgoal by (auto simp: acids_def acids_mset_def dest!: multi_member_split
    dest: subset_add_mset_notin_subset)
  subgoal by (auto simp: acids_def acids_mset_def dest!: multi_member_split
    dest: subset_add_mset_notin_subset)
  subgoal by (auto simp: acids_def acids_mset_def dest!: multi_member_split
    dest: subset_add_mset_notin_subset)
  subgoal by (auto simp: acids_def acids_mset_def dest!: multi_member_split
    dest: subset_add_mset_notin_subset)
  subgoal by (auto simp: acids_def acids_mset_def dest!: multi_member_split
    dest: subset_add_mset_notin_subset)
  subgoal by (auto simp: acids_def acids_mset_def dest!: multi_member_split
    dest: subset_add_mset_notin_subset)
  subgoal by (auto simp: acids_def acids_mset_def dest!: multi_member_split
    dest: subset_add_mset_notin_subset)
  subgoal by (auto simp: acids_def acids_mset_def dest!: multi_member_split
    dest: subset_add_mset_notin_subset)
  subgoal by (auto simp: acids_def acids_mset_def dest!: multi_member_split
    dest: subset_add_mset_notin_subset)
  subgoal by (auto simp: acids_def acids_mset_def dest!: multi_member_split
    dest: subset_add_mset_notin_subset)
  subgoal by (auto simp: acids_def acids_mset_def dest!: multi_member_split
    dest: subset_add_mset_notin_subset)
  subgoal by (auto simp: acids_def acids_mset_def dest!: multi_member_split
    dest: subset_add_mset_notin_subset)
  subgoal by (auto simp: acids_def acids_mset_def dest!: multi_member_split
    dest: subset_add_mset_notin_subset)
  done

definition acids_flush_int :: \<open>nat multiset \<Rightarrow> (nat,nat) ann_lits \<Rightarrow> (nat, nat) acids \<Rightarrow> _ \<Rightarrow> ((nat, nat) acids \<times> _)nres\<close> where
\<open>acids_flush_int \<A>\<^sub>i\<^sub>n = (\<lambda>M vm (to_remove, h). do {
    ASSERT(length to_remove \<le> unat32_max);
    (_, vm, h) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i, vm', h). i \<le> length to_remove \<and>
          (i < length to_remove \<longrightarrow> acids_push_literal_pre \<A>\<^sub>i\<^sub>n (to_remove!i) (vm'))\<^esup>
      (\<lambda>(i, vm, h). i < length to_remove)
      (\<lambda>(i, vm, h). do {
         ASSERT(i < length to_remove);
         ASSERT(to_remove!i \<in># \<A>\<^sub>i\<^sub>n);
         ASSERT(atoms_hash_del_pre (to_remove!i) h);
         vm \<leftarrow> acids_push_literal (to_remove!i) vm;
         RETURN (i+1, vm, atoms_hash_del (to_remove!i) h)})
      (0, vm, h);
    RETURN (vm, (emptied_list to_remove, h))
  })\<close>


definition acids_flush
   :: \<open>nat multiset \<Rightarrow> (nat,nat) ann_lits \<Rightarrow> (nat, nat) acids \<Rightarrow> nat set \<Rightarrow> ((nat, nat) acids \<times> nat set) nres\<close>
where
  \<open>acids_flush \<A>\<^sub>i\<^sub>n = (\<lambda>M vm remove_int. SPEC (\<lambda>x. (fst x) \<in> acids \<A>\<^sub>i\<^sub>n M \<and> snd x = {}))\<close>

lemma acids_change_to_remove_order:
  assumes
    vmtf: \<open>ac \<in> acids \<A>\<^sub>i\<^sub>n M\<close> and
    CD_rem: \<open>((C, D), to_remove) \<in> distinct_atoms_rel \<A>\<^sub>i\<^sub>n\<close> and
    nempty: \<open>isasat_input_nempty \<A>\<^sub>i\<^sub>n\<close> and
    bounded: \<open>isasat_input_bounded \<A>\<^sub>i\<^sub>n\<close> and
    t: \<open>to_remove \<subseteq> set_mset \<A>\<^sub>i\<^sub>n\<close>
  shows \<open>acids_flush_int \<A>\<^sub>i\<^sub>n M ac (C, D) \<le> \<Down>(Id \<times>\<^sub>r distinct_atoms_rel \<A>\<^sub>i\<^sub>n) (acids_flush \<A>\<^sub>i\<^sub>n M ac to_remove)\<close>
proof -
  have to_C: \<open>to_remove = set C\<close>
    using CD_rem by (auto simp: distinct_atoms_rel_def distinct_hash_atoms_rel_def)
  have length_le: \<open>length (fst (C,D)) \<le> unat32_max\<close>
  proof -
    have lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n (Pos `# mset C)\<close> and
      dist: \<open>distinct C\<close>
      using vmtf CD_rem t unfolding vmtf_def
        vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def
      apply (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_alt_def distinct_atoms_rel_alt_def inj_on_def)
      by (metis atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n in_mono)
    have dist: \<open>distinct_mset (Pos `# mset C)\<close>
      by (subst distinct_image_mset_inj)
        (use dist in \<open>auto simp: inj_on_def\<close>)
    have tauto: \<open>\<not> tautology (poss (mset C))\<close>
      by (auto simp: tautology_decomp)

    show ?thesis
      using simple_clss_size_upper_div2[OF bounded lits dist tauto]
      by (auto simp: unat32_max_def)
  qed
  have acids_push_literal_pre: \<open>acids_push_literal_pre \<A>\<^sub>i\<^sub>n (C ! i) ac\<close>
    if \<open>i < length C\<close> for i
    using t that CD_rem unfolding acids_push_literal_pre_def distinct_atoms_rel_def
      distinct_hash_atoms_rel_def by auto
  define I where \<open>I \<equiv> \<lambda>(i::nat, vm'::(nat, nat)acids, h). vm' \<in> acids \<A>\<^sub>i\<^sub>n M \<and>
    ((drop i C, h), to_remove - set (take i C)) \<in> distinct_atoms_rel \<A>\<^sub>i\<^sub>n \<and> i \<le> length C\<close>

  have sin: \<open>fst s < length (fst (C, D)) \<Longrightarrow> fst (C, D) ! fst s \<in># \<A>\<^sub>i\<^sub>n\<close> and
    atms: \<open>I s \<Longrightarrow> fst s < length (fst (C, D)) \<Longrightarrow> atoms_hash_del_pre (fst (C, D) ! fst s) (snd (snd s))\<close> for s
    using t CD_rem nth_mem[of \<open>fst s\<close> C]
    unfolding acids_push_literal_pre_def distinct_atoms_rel_def
      distinct_hash_atoms_rel_def I_def atoms_hash_del_pre_def atoms_hash_rel_def by (auto simp del: nth_mem)

  let ?R = \<open>measure (\<lambda>(i, vm', h). length C - i)\<close>

  have I_inv1_acids_push_literal_pre: \<open>I s \<Longrightarrow>
    fst (C, D) ! fst s \<in># \<A>\<^sub>i\<^sub>n \<Longrightarrow>
    x \<in> acids \<A>\<^sub>i\<^sub>n M \<Longrightarrow>
    fst (fst s + 1, x,
    atoms_hash_del (fst (C, D) ! fst s) (snd (snd s)))
    < length (fst (C, D)) \<Longrightarrow>
    acids_push_literal_pre \<A>\<^sub>i\<^sub>n
    (fst (C, D) ! fst (fst s + 1, x,
    atoms_hash_del (fst (C, D) ! fst s) (snd (snd s))))
    (fst (snd (fst s + 1, x, atoms_hash_del (fst (C, D) ! fst s) (snd (snd s)))))\<close>
    for s x
    using t CD_rem unfolding acids_push_literal_pre_def distinct_atoms_rel_def
      distinct_hash_atoms_rel_def by auto
  have I_Suc: \<open>I s \<Longrightarrow>
    fst s < length (fst (C, D)) \<Longrightarrow>
    fst (C, D) ! fst s \<in># \<A>\<^sub>i\<^sub>n \<Longrightarrow>
    atoms_hash_del_pre (fst (C, D) ! fst s) (snd (snd s)) \<Longrightarrow>
    x \<in> acids \<A>\<^sub>i\<^sub>n M \<Longrightarrow>
    I (fst s + 1, x, atoms_hash_del (fst (C, D) ! fst s) (snd (snd s)))\<close>
    for s x
    apply (auto simp: I_def distinct_atoms_rel_def 
      distinct_hash_atoms_rel_def
      intro!: relcompI[of _ \<open>(drop (Suc (fst s)) C, (snd (snd s))[C ! (fst s) := False], to_remove - set (take (Suc (fst s)) C))\<close>])
    apply (rule  relcompI[of _ \<open>(drop (Suc (fst s)) C, to_remove - set (take (Suc (fst s)) C))\<close>])
    subgoal
      by (auto simp: atoms_hash_rel_def atoms_hash_del_def take_Suc_conv_app_nth)
    subgoal
      by (auto simp: take_Suc_conv_app_nth simp flip: Cons_nth_drop_Suc)
    done

  show ?thesis
    unfolding acids_flush_int_def acids_flush_def case_prod_beta
    apply (refine_vcg specify_left[OF WHILEIT_rule_stronger_inv[where \<Phi> = \<open>(\<lambda>x. I x \<and> fst x =length (fst (C, D)))\<close> and I' = \<open>I\<close> and R = ?R]]
      acids_push_literal[where \<A>=\<A>\<^sub>i\<^sub>n and M=M])
    subgoal by (rule length_le)
    subgoal by auto
    subgoal by auto
    subgoal by (auto intro!: acids_push_literal_pre)
    subgoal using assms by (auto simp: I_def)
    subgoal by (rule sin)
    subgoal by (rule atms)
    subgoal by (auto simp: I_def)
    subgoal by auto
    subgoal by auto
    subgoal for s x by (rule I_inv1_acids_push_literal_pre)
    subgoal by (rule I_Suc)
    subgoal for s x by (auto simp: I_def)
    subgoal by (auto simp: emptied_list_def conc_fun_RES I_def)
    subgoal by (auto simp add: emptied_list_def conc_fun_RES I_def Image_iff to_C)
    done
qed
end
