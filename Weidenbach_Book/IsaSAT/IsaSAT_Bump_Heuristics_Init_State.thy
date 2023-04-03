theory IsaSAT_Bump_Heuristics_Init_State
imports Watched_Literals_VMTF IsaSAT_ACIDS
  Tuple4 IsaSAT_ACIDS_LLVM
begin

type_synonym vmtf_remove_int_option_fst_As = \<open>nat_vmtf_node list \<times> nat \<times> nat option \<times> nat option \<times> nat option\<close>


definition isa_vmtf_init
   :: \<open>nat multiset \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> vmtf_remove_int_option_fst_As set\<close>
where
  \<open>isa_vmtf_init \<A>\<^sub>i\<^sub>n M = {(ns, m, fst_As, lst_As, next_search).
   \<A>\<^sub>i\<^sub>n \<noteq> {#} \<longrightarrow> (fst_As \<noteq> None \<and> lst_As \<noteq> None \<and> (ns, m, the fst_As, the lst_As, next_search) \<in> vmtf \<A>\<^sub>i\<^sub>n M)}\<close>

(*TODO: share the to_remove part of Bump_Heuristics_Init*)
type_synonym bump_heuristics_init = \<open>((nat,nat)acids,vmtf_remove_int_option_fst_As, bool, nat list \<times> bool list) tuple4\<close>

abbreviation Bump_Heuristics_Init :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bump_heuristics_init\<close> where
  \<open>Bump_Heuristics_Init a b c d \<equiv> Tuple4 a b c d\<close>

lemmas bump_heuristics_init_splits = Tuple4.tuple4.splits
hide_fact tuple4.splits

abbreviation get_stable_heuristics :: \<open>bump_heuristics_init \<Rightarrow> (nat,nat) acids\<close> where
  \<open>get_stable_heuristics \<equiv> Tuple4_a\<close>

abbreviation get_focused_heuristics :: \<open>bump_heuristics_init \<Rightarrow> vmtf_remove_int_option_fst_As\<close> where
  \<open>get_focused_heuristics \<equiv> Tuple4_b\<close>

abbreviation is_focused_heuristics :: \<open>bump_heuristics_init \<Rightarrow> bool\<close> where
  \<open>is_focused_heuristics \<equiv> Tuple4_c\<close>

abbreviation is_stable_heuristics:: \<open>bump_heuristics_init \<Rightarrow> bool\<close> where
  \<open>is_stable_heuristics x \<equiv> \<not>is_focused_heuristics x\<close>

abbreviation get_bumped_variables :: \<open>bump_heuristics_init \<Rightarrow> nat list \<times> bool list\<close> where
  \<open>get_bumped_variables \<equiv> Tuple4_d\<close>

abbreviation set_stable_heuristics :: \<open>(nat,nat)acids \<Rightarrow>bump_heuristics_init \<Rightarrow> _\<close> where
  \<open>set_stable_heuristics \<equiv> Tuple4.set_a\<close>

abbreviation set_focused_heuristics :: \<open>vmtf_remove_int_option_fst_As \<Rightarrow>bump_heuristics_init \<Rightarrow> _\<close> where
  \<open>set_focused_heuristics \<equiv> Tuple4.set_b\<close>

abbreviation set_is_focused_heuristics :: \<open>bool \<Rightarrow>bump_heuristics_init \<Rightarrow> _\<close> where
  \<open>set_is_focused_heuristics \<equiv> Tuple4.set_c\<close>

abbreviation set_bumped_variables :: \<open>nat list \<times> bool list \<Rightarrow>bump_heuristics_init \<Rightarrow> _\<close> where
  \<open>set_bumped_variables \<equiv> Tuple4.set_d\<close>

definition get_unit_trail where
  \<open>get_unit_trail M = (rev (takeWhile (\<lambda>x. \<not>is_decided x) (rev M)))\<close>

definition bump_heur_init :: \<open>_ \<Rightarrow> _ \<Rightarrow> bump_heuristics_init set\<close> where
  \<open>bump_heur_init \<A> M = {x.
      get_stable_heuristics x \<in> acids \<A> M \<and>
       get_focused_heuristics x \<in> isa_vmtf_init \<A> M \<and>
  (get_bumped_variables x, set (fst (get_bumped_variables x))) \<in> distinct_atoms_rel \<A> \<and>
  count_decided M = 0
  }\<close>


lemma get_unit_trail_count_decided_0[simp]: \<open>count_decided M = 0 \<Longrightarrow> get_unit_trail M = M\<close>
  by (auto simp: get_unit_trail_def count_decided_0_iff)
   (metis rev_swap set_rev takeWhile_eq_all_conv)


subsection \<open>Access Function\<close>

(*TODO: replace by proper shared init later*)
definition vmtf_heur_import_variable :: \<open>nat \<Rightarrow> vmtf_remove_int_option_fst_As \<Rightarrow> _\<close> where
  \<open>vmtf_heur_import_variable L = (\<lambda>(n, stmp, fst, last, cnext).
     (vmtf_cons n L cnext stmp, stmp+1, fst, Some L, cnext))\<close>

definition acids_heur_import_variable :: \<open>nat \<Rightarrow> (nat, nat) acids \<Rightarrow> _\<close> where
  \<open>acids_heur_import_variable L = (\<lambda>(bw, m). do {
     ASSERT (m \<le> unat32_max);
     bw \<leftarrow> ACIDS.mop_prio_insert L m bw;
     RETURN (bw, (m+1))
  })\<close>


(*TODO: should be a single loop*)
definition initialise_VMTF :: \<open>nat list \<Rightarrow> nat \<Rightarrow> vmtf_remove_int_option_fst_As nres\<close> where
\<open>initialise_VMTF N n = do {
   let A = replicate n (VMTF_Node 0 None None);
   ASSERT(length N \<le> unat32_max);
   (n, A, cnext) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(i, A, cnext). i < length_uint32_nat N)
      (\<lambda>(i, A, cnext). do {
        ASSERT(i < length_uint32_nat N);
        let L = (N ! i);
        ASSERT(L < length A);
        ASSERT(cnext \<noteq> None \<longrightarrow> the cnext < length A);
        ASSERT(i + 1 \<le> unat32_max);
        RETURN (i + 1, vmtf_cons A L cnext (i), Some L)
      })
      (0, A, None);
   RETURN ((A, n, cnext, (if N = [] then None else Some ((N!0))), cnext))
  }\<close>

definition init_ACIDS0 :: \<open>_ \<Rightarrow> nat \<Rightarrow>  (nat multiset \<times> nat multiset \<times> (nat \<Rightarrow> nat)) nres\<close> where
  \<open>init_ACIDS0 \<A> n = do {
    ASSERT (\<A> \<noteq> {#} \<longrightarrow> n > Max (insert 0 (set_mset \<A>)));
    RETURN ((\<A>, {#}, \<lambda>_. 0))
  }\<close>

definition hp_init_ACIDS0 where
  \<open>hp_init_ACIDS0 _ n = do {
    RETURN ((replicate n None, replicate n None, replicate n None, replicate n None, replicate n 0, None))
  }\<close>

lemma hp_acids_empty:
  \<open>(hp_init_ACIDS0 \<A>, init_ACIDS0 \<A>) \<in> 
   Id \<rightarrow>\<^sub>f \<langle>((\<langle>\<langle>nat_rel\<rangle>option_rel, \<langle>nat_rel\<rangle>option_rel\<rangle>pairing_heaps_rel)) O
   acids_encoded_hmrel\<rangle>nres_rel\<close>
proof -
  have 1: \<open>((\<A>, (\<lambda>_. None, \<lambda>_. None, \<lambda>_. None, \<lambda>_. None, \<lambda>_. Some 0), None), (\<A>, {#}, \<lambda>_. 0)) \<in> acids_encoded_hmrel\<close>
    by (auto simp: acids_encoded_hmrel_def bottom_acids0_def pairing_heaps_rel_def map_fun_rel_def
      ACIDS.hmrel_def encoded_hp_prop_list_conc_def encoded_hp_prop_def empty_outside_def empty_acids0_def
      intro!: relcompI)
  have H: \<open>mset_nodes ya \<noteq> {#}\<close> for ya
    by (cases ya) auto
  show ?thesis
    unfolding uncurry0_def hp_init_ACIDS0_def init_ACIDS0_def
    apply (intro frefI nres_relI)
    apply refine_rcg
    apply (rule relcompI[of])
    defer
    apply (rule 1)
    by (auto simp add: acids_encoded_hmrel_def  encoded_hp_prop_def hp_init_ACIDS0_def
      ACIDS.hmrel_def encoded_hp_prop_list_conc_def pairing_heaps_rel_def H map_fun_rel_def
      split: option.splits dest!: multi_member_split)
qed

definition init_ACIDS where
  \<open>init_ACIDS \<A> n = do {
  ac \<leftarrow> init_ACIDS0 \<A> n;
  RETURN (ac, 0)
  }\<close>


definition initialise_ACIDS :: \<open>nat list \<Rightarrow> nat \<Rightarrow> (nat, nat) acids nres\<close> where
\<open>initialise_ACIDS N n = do {
   A \<leftarrow> init_ACIDS (mset N) n;
   ASSERT(length N \<le> unat32_max);
   (n, A) \<leftarrow> WHILE\<^sub>T\<^bsup> \<lambda>_. True\<^esup>
      (\<lambda>(i, A). i < length_uint32_nat N)
      (\<lambda>(i, A). do {
        ASSERT(i < length_uint32_nat N);
        let L = (N ! i);
        ASSERT (snd A = i);
          ASSERT(i + 1 \<le> unat32_max);
        A \<leftarrow> acids_heur_import_variable L A;
        RETURN (i + 1, A)
      })
      (0, A);
   RETURN A
  }\<close>

definition (in -) distinct_atms_empty where
  \<open>distinct_atms_empty _ = {}\<close>

definition (in -) distinct_atms_int_empty where
  \<open>distinct_atms_int_empty n = RETURN ([], replicate n False)\<close>


lemma distinct_atms_int_empty_distinct_atms_empty:
  \<open>(distinct_atms_int_empty, RETURN o distinct_atms_empty) \<in>
     [\<lambda>n. (\<forall>L\<in>#\<L>\<^sub>a\<^sub>l\<^sub>l \<A>. atm_of L < n)]\<^sub>f nat_rel \<rightarrow> \<langle>distinct_atoms_rel \<A>\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (auto simp: distinct_atoms_rel_alt_def distinct_atms_empty_def distinct_atms_int_empty_def)
  by (metis atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n atms_of_def imageE)

lemma initialise_VMTF:
  shows  \<open>(uncurry initialise_VMTF, uncurry (\<lambda>N n. RES (isa_vmtf_init N []))) \<in>
      [\<lambda>(N,n). (\<forall>L\<in># N. L < n) \<and> (distinct_mset N) \<and> size N < unat32_max \<and> set_mset N = set_mset \<A>]\<^sub>f
      (\<langle>nat_rel\<rangle>list_rel_mset_rel) \<times>\<^sub>f nat_rel \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
    (is \<open>(?init, ?R) \<in> _\<close>)
proof -
  have vmtf_ns_notin_empty: \<open>vmtf_ns_notin [] 0 (replicate n (VMTF_Node 0 None None))\<close> for n
    unfolding vmtf_ns_notin_def
    by auto

  have K2: \<open>distinct N \<Longrightarrow> fst_As < length N \<Longrightarrow> N!fst_As \<in> set (take fst_As N) \<Longrightarrow> False\<close>
    for fst_As x N
    by (metis (no_types, lifting) in_set_conv_nth length_take less_not_refl min_less_iff_conj
      nth_eq_iff_index_eq nth_take)
  have W_ref: \<open>WHILE\<^sub>T (\<lambda>(i, A, cnext). i < length_uint32_nat N')
        (\<lambda>(i, A, cnext). do {
              _ \<leftarrow> ASSERT (i < length_uint32_nat N');
              let L = (N' ! i);
              _ \<leftarrow> ASSERT (L < length A);
              _ \<leftarrow> ASSERT (cnext \<noteq> None \<longrightarrow> the cnext < length A);
              _ \<leftarrow> ASSERT (i + 1 \<le> unat32_max);
              RETURN
               (i + 1,
                vmtf_cons A L cnext (i), Some L)
            })
        (0, replicate n' (VMTF_Node 0 None None),
         None)
    \<le> SPEC(\<lambda>(i, A', cnext).
      vmtf_ns (rev ((take i N'))) i A'
        \<and> cnext = (option_last (take i N')) \<and>  i = length N' \<and>
          length A' = n \<and> vmtf_ns_notin (rev ((take i N'))) i A'
      )\<close>
    (is \<open>_ \<le> SPEC ?P\<close>)
    if H: \<open>case y of (N, n) \<Rightarrow>(\<forall>L\<in># N. L < n) \<and> distinct_mset N \<and> size N < unat32_max \<and>
         set_mset N = set_mset \<A>\<close> and
       ref: \<open>(x, y) \<in> \<langle>Id\<rangle>list_rel_mset_rel \<times>\<^sub>f nat_rel\<close> and
       st[simp]: \<open>x = (N', n')\<close> \<open>y = (N, n)\<close>
     for N N' n n' A x y
  proof -
  have [simp]: \<open>n = n'\<close> and NN': \<open>(N', N) \<in> \<langle>Id\<rangle>list_rel_mset_rel\<close>
    using ref unfolding st by auto
  then have dist: \<open>distinct N'\<close>
    using NN' H by (auto simp: list_rel_def br_def list_mset_rel_def list.rel_eq
      list_all2_op_eq_map_right_iff' distinct_image_mset_inj list_rel_mset_rel_def)

  have L_N: \<open>\<forall>L\<in>set N'. L < n\<close>
    using H ref by (auto simp: list_rel_def br_def list_mset_rel_def
      list_all2_op_eq_map_right_iff' list_rel_mset_rel_def list.rel_eq)
  let ?Q = \<open>\<lambda>(i, A', cnext).
      vmtf_ns (rev ((take i N'))) i A' \<and> i \<le> length N' \<and>
      cnext = (option_last (take i N')) \<and>
      length A' = n \<and> vmtf_ns_notin (rev ((take i N'))) i A'\<close>
  show ?thesis
    apply (refine_vcg WHILET_rule[where R = \<open>measure (\<lambda>(i, _). length N' + 1 - i)\<close> and I = \<open>?Q\<close>])
    subgoal by auto
    subgoal by (auto intro: vmtf_ns.intros)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal for S N' x2 A'
      unfolding assert_bind_spec_conv vmtf_ns_notin_def
      using L_N dist
      by (auto 5 5 simp: take_Suc_conv_app_nth hd_drop_conv_nth nat_shiftr_div2
          option_last_def hd_rev last_map intro!: vmtf_cons dest: K2)
    subgoal by auto
    subgoal
      using L_N dist
      by (auto simp: take_Suc_conv_app_nth hd_drop_conv_nth nat_shiftr_div2
          option_last_def hd_rev last_map)
    subgoal
      using L_N dist
      by (auto simp: last_take_nth_conv option_last_def)
    subgoal
      using H dist ref
      by (auto simp: last_take_nth_conv option_last_def list_rel_mset_rel_imp_same_length)
    subgoal
      using L_N dist
      by (auto 5 5 simp: take_Suc_conv_app_nth option_last_def hd_rev last_map intro!: vmtf_cons
          dest: K2)
    subgoal by (auto simp: take_Suc_conv_app_nth)
    subgoal by (auto simp: take_Suc_conv_app_nth)
    subgoal by auto
    subgoal
      using L_N dist
      by (auto 5 5 simp: take_Suc_conv_app_nth hd_rev last_map option_last_def
          intro!: vmtf_notin_vmtf_cons dest: K2 split: if_splits)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
  qed
  have [simp]: \<open>vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l n' [] ((set N, {}))\<close>
    if \<open>(N, n') \<in> \<langle>Id\<rangle>list_rel_mset_rel\<close> for N N' n'
    using that unfolding vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def
    by (auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_def atms_of_def image_image image_Un list_rel_def
       br_def list_mset_rel_def list_all2_op_eq_map_right_iff'
      list_rel_mset_rel_def list.rel_eq)
  have in_N_in_N1: \<open>L \<in> set N' \<Longrightarrow>  L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l N)\<close>
    if  \<open>(N', N) \<in> list_mset_rel\<close> for L N N' y
    using that by (auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_def atms_of_def image_image image_Un list_rel_def
      list.rel_eq br_def list_mset_rel_def list_all2_op_eq_map_right_iff')

  have length_ba: \<open>\<forall>L\<in># N. L < length ba \<Longrightarrow> L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l N) \<Longrightarrow>
     L < length ba\<close>
    if \<open>(N', y) \<in> \<langle>Id\<rangle>list_rel_mset_rel\<close>
    for L ba N N' y
    using that
    by (auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_def nat_shiftr_div2 list.rel_eq
      atms_of_def image_image image_Un split: if_splits)
  show ?thesis
    supply list.rel_eq[simp]
    apply (intro frefI nres_relI)
    unfolding initialise_VMTF_def uncurry_def conc_Id id_def isa_vmtf_init_def
      distinct_atms_int_empty_def nres_monad1
    apply (subst Let_def)
    apply (refine_vcg)
    subgoal by (auto dest: list_rel_mset_rel_imp_same_length)
      apply (rule W_ref[THEN order_trans]; assumption?)
    subgoal for N' N'n' n' Nn
      apply (auto dest: list_rel_mset_rel_imp_same_length simp: vmtf_def)
      apply (rule exI[of _ \<open>(rev (fst N'))\<close>])
      apply (rule_tac exI[of _ \<open>[]\<close>])
      apply (auto dest: list_rel_mset_rel_imp_same_length simp: vmtf_def hd_rev last_conv_nth rev_nth
        atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n)
      apply (auto dest: list_rel_mset_rel_imp_same_length simp: vmtf_def hd_rev last_conv_nth rev_nth
        atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n list_rel_mset_rel_def list_mset_rel_def br_def)
      done
    done
qed


lemma initialise_ACIDS:
  shows  \<open>(uncurry initialise_ACIDS, uncurry (\<lambda>N n. RES (acids N ([]::(nat,nat)ann_lits)))) \<in>
      [\<lambda>(N,n). (\<forall>L\<in># N. L < n) \<and> (distinct_mset N) \<and> size N < unat32_max \<and> set_mset N = set_mset \<A>]\<^sub>f
      (\<langle>nat_rel\<rangle>list_rel_mset_rel) \<times>\<^sub>f nat_rel \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
    (is \<open>(?init, ?R) \<in> _\<close>)
proof -
  define I' where \<open>I' x \<equiv> (\<lambda>(a,b::(nat,nat)acids). b \<in> acids \<A> (map (\<lambda>a. (Decided (Pos a)) :: (nat,nat)ann_lit) (drop a (fst x))) \<and> a \<le> length (fst x) \<and>
    snd b = a \<and> fst (snd (fst b)) = mset (take a (fst x)))\<close> for x :: \<open>nat list \<times> nat\<close>
 have I0: \<open>(\<forall>L\<in>#fst y. L < snd y) \<and>
    distinct_mset (fst y) \<and>
    size (fst y) < unat32_max \<and> set_mset (fst y) = set_mset \<A> \<Longrightarrow>
    (x, y) \<in> \<langle>nat_rel\<rangle>list_rel_mset_rel \<times>\<^sub>f nat_rel \<Longrightarrow>
   length (fst x) \<le> unat32_max \<Longrightarrow> I' x (0, (mset (fst x), {#}, \<lambda>_. 0), 0)\<close> for x y
   by (cases x, cases y)
    (auto simp: I'_def acids_def list_rel_mset_rel_def list_mset_rel_def br_def defined_lit_map
     dest!: multi_member_split)

 have I'_Suc: \<open>I' x (fst s + 1,
      (fst (fst (snd s)), add_mset (fst x ! fst s) (fst (snd (fst (snd s)))),
    (snd (snd (fst (snd s))))(fst x ! fst s := snd (snd s))),
   snd (snd s) + 1)\<close> and
   pre: \<open>fst x ! fst s \<notin># fst (snd (fst (snd s)))\<close>
   if
     \<open>(\<forall>L\<in>#fst y. L < snd y) \<and>
     distinct_mset (fst y) \<and>
     size (fst y) < unat32_max \<and> set_mset (fst y) = set_mset \<A>\<close> and
     \<open>(x, y) \<in> \<langle>nat_rel\<rangle>list_rel_mset_rel \<times>\<^sub>f nat_rel\<close> and
     \<open>x = (a, b)\<close> and
     \<open>y = (aa, ba)\<close> and
     \<open>length (fst x) \<le> unat32_max\<close> and
     \<open>I' x s\<close> and
     \<open>fst s < length_uint32_nat (fst x)\<close> and
     \<open>fst s < length_uint32_nat (fst x)\<close> and
     \<open>snd (snd s) = fst s\<close> and
     \<open>fst s + 1 \<le> unat32_max\<close>
   for a b aa ba s x y
 proof -
   have \<open>mset (take (Suc (fst s)) a) \<subseteq># \<A>\<close>
     apply (rule subset_mset.trans[of _ \<open>mset a\<close>])
     using that
     apply (clarsimp_all simp: acids_def defined_lit_map list_rel_mset_rel_def br_def list_mset_rel_def
       image_image acids_heur_import_variable_def I'_def mset_take_subseteq)
     by (metis distinct_subseteq_iff fst_eqD le_refl set_take_subset take_all_iff that(1))

   then show  \<open>I' x (fst s + 1,
      (fst (fst (snd s)), add_mset (fst x ! fst s) (fst (snd (fst (snd s)))),
    (snd (snd (fst (snd s))))(fst x ! fst s := snd (snd s))),
   snd (snd s) + 1)\<close> \<open>fst x ! fst s \<notin># fst (snd (fst (snd s)))\<close>
     using that
     by (force simp: acids_def take_Suc_conv_app_nth defined_lit_map list_rel_mset_rel_def br_def list_mset_rel_def
       image_image acids_heur_import_variable_def I'_def Cons_nth_drop_Suc[symmetric] distinct_in_set_take_iff
       dest: multi_member_split)+
 qed

  show ?thesis
    unfolding uncurry_def case_prod_beta initialise_ACIDS_def
      acids_heur_import_variable_def ACIDS.mop_prio_insert_def nres_monad3
      init_ACIDS_def nres_monad3 init_ACIDS0_def
      bind_to_let_conv Let_def
    apply (intro frefI nres_relI)
    subgoal for x y
      apply (cases x, cases y)
      apply (refine_vcg specify_left[OF WHILEIT_rule_stronger_inv[where \<Phi> = \<open>\<lambda>(a::nat,b::(nat,nat)acids). b \<in> acids \<A> ([]::(nat,nat)ann_lits)\<close> and
        I' = \<open>I' x\<close> and
        R = \<open>measure (\<lambda>(a,b). length (fst x) - a)\<close>]])
      subgoal  apply (auto simp: list_rel_mset_rel_def list_mset_rel_def br_def acids_def)
        using gt_or_eq_0 by blast
      subgoal by (auto simp: list_rel_mset_rel_def list_mset_rel_def br_def)
      subgoal by auto
      subgoal by auto
      subgoal by (rule I0)
      subgoal by (auto simp: I'_def)
      subgoal by (auto simp:)
      subgoal by auto
      subgoal by (rule pre)
      subgoal by (auto simp: I'_def list_rel_mset_rel_def list_mset_rel_def br_def
        acids_def)
      subgoal by (rule I'_Suc)
      subgoal by (auto simp: I'_def)
      subgoal 
        by (auto simp add: I'_def)
      subgoal apply (auto simp: list_rel_mset_rel_def list_mset_rel_def br_def acids_def)
        by (metis distinct_subseteq_iff set_mset_mset)
      done
    done
qed

definition initialize_Bump_Init :: \<open>nat list \<Rightarrow> nat \<Rightarrow> bump_heuristics_init nres\<close> where
  \<open>initialize_Bump_Init A n = do {
  focused \<leftarrow> initialise_VMTF A n;
  hstable \<leftarrow> initialise_ACIDS A n;
  to_remove \<leftarrow> distinct_atms_int_empty n;
  RETURN (Tuple4 hstable focused True to_remove)
  }\<close>

lemma specify_left_RES:
  assumes "m \<le> RES \<Phi>"
  assumes "\<And>x. x \<in> \<Phi> \<Longrightarrow> f x \<le> M"  
  shows "do { x \<leftarrow> m; f x } \<le> M"
  using assms by (auto simp: pw_le_iff refine_pw_simps)

lemma initialize_Bump_Init:
  shows  \<open>(uncurry initialize_Bump_Init, uncurry (\<lambda>N n. RES (bump_heur_init N []))) \<in>
      [\<lambda>(N,n). (\<forall>L\<in># N. L < n) \<and> (distinct_mset N) \<and> size N < unat32_max \<and> set_mset N = set_mset \<A>]\<^sub>f
      (\<langle>nat_rel\<rangle>list_rel_mset_rel) \<times>\<^sub>f nat_rel \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
    (is \<open>(?init, ?R) \<in> _\<close>)
  unfolding initialize_Bump_Init_def uncurry_def distinct_atms_int_empty_def nres_monad1
  apply (intro frefI nres_relI)
  apply (refine_rcg)
  apply hypsubst
  apply (rule specify_left_RES[OF initialise_VMTF[where \<A>=\<A>, THEN fref_to_Down_curry, unfolded conc_fun_RES]])
  apply assumption+
  apply (rule specify_left_RES[OF initialise_ACIDS[where \<A>=\<A>, THEN fref_to_Down_curry, unfolded conc_fun_RES]])
  apply assumption+
  apply (auto simp: bump_heur_init_def distinct_atoms_rel_def distinct_hash_atoms_rel_def
    atoms_hash_rel_def intro!: relcompI)
  done


type_synonym bump_heuristics_option_fst_As = \<open>vmtf_remove_int_option_fst_As\<close>

lemma isa_vmtf_init_consD:
  \<open>((ns, m, fst_As, lst_As, next_search)) \<in> isa_vmtf_init \<A> M \<Longrightarrow>
     ((ns, m, fst_As, lst_As, next_search)) \<in> isa_vmtf_init \<A> (L # M)\<close>
  by (auto simp: isa_vmtf_init_def dest: vmtf_consD)

lemma isa_vmtf_init_consD':
  \<open>vm \<in> isa_vmtf_init \<A> M \<Longrightarrow> vm \<in> isa_vmtf_init \<A> (L # M)\<close>
  by (auto simp: isa_vmtf_init_def dest: vmtf_consD)

(*TODO share*)

lemma vmtf_cong:
  \<open>set_mset \<A> = set_mset \<B> \<Longrightarrow> L \<in> vmtf \<A> M \<Longrightarrow> L \<in> vmtf \<B> M\<close>
  using \<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>] atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>]
  unfolding vmtf_def vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def
  by auto
lemma isa_vmtf_init_cong:
  \<open>set_mset \<A> = set_mset \<B> \<Longrightarrow> isa_vmtf_init \<A> M  =isa_vmtf_init \<B> M\<close>
  using \<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>] atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>] vmtf_cong[of \<A> \<B>] vmtf_cong[of \<B> \<A>]
  unfolding isa_vmtf_init_def vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def
  by auto
lemma isa_acids_cong:
  \<open>set_mset \<A> = set_mset \<B> \<Longrightarrow> acids \<A>  = acids \<B>\<close>
  using \<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>] atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>]
  unfolding acids_def
  by (auto intro!: ext intro!: distinct_subseteq_iff[THEN iffD1])

lemma distinct_atoms_rel_cong:
  \<open>set_mset \<A> = set_mset \<B> \<Longrightarrow> distinct_atoms_rel \<A> = distinct_atoms_rel \<B>\<close>
  using \<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>] atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>]
  unfolding vmtf_def vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def distinct_atoms_rel_def atoms_hash_rel_def distinct_hash_atoms_rel_def
  by auto

lemma bump_heur_init_cong:
  \<open>set_mset \<A> = set_mset \<B> \<Longrightarrow>  bump_heur_init \<A> M = bump_heur_init \<B> M\<close>
  using isa_vmtf_init_cong[of \<A> \<B> M] 
    \<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>] atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>] distinct_atoms_rel_cong[of \<A> \<B>] isa_acids_cong[of \<A> \<B>]
  unfolding bump_heur_init_def isa_acids_cong[of \<A> \<B>]
  by auto


lemma bump_heur_init_consD':
  \<open>vm \<in> bump_heur_init \<A> M \<Longrightarrow> vm \<in> bump_heur_init \<A> (Propagated L n # M)\<close>
  by (auto simp: bump_heur_init_def dest: isa_vmtf_init_consD' acids_prepend)

end
