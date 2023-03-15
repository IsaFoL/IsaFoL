theory IsaSAT_Bump_Heuristics_Init_State
imports Watched_Literals_VMTF 
(*
  IsaSAT_VSIDS
  *)
  Tuple4
begin

type_synonym vmtf_remove_int_option_fst_As = \<open>nat_vmtf_node list \<times> nat \<times> nat option \<times> nat option \<times> nat option\<close>


definition isa_vmtf_init
   :: \<open>nat multiset \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> vmtf_remove_int_option_fst_As set\<close>
where
  \<open>isa_vmtf_init \<A>\<^sub>i\<^sub>n M = {(ns, m, fst_As, lst_As, next_search).
   \<A>\<^sub>i\<^sub>n \<noteq> {#} \<longrightarrow> (fst_As \<noteq> None \<and> lst_As \<noteq> None \<and> (ns, m, the fst_As, the lst_As, next_search) \<in> vmtf \<A>\<^sub>i\<^sub>n M)}\<close>

(*TODO: share the to_remove part of Bump_Heuristics_Init*)
type_synonym bump_heuristics_init = \<open>(vmtf_remove_int_option_fst_As, vmtf_remove_int_option_fst_As, bool, nat list \<times> bool list) tuple4\<close>

abbreviation Bump_Heuristics_Init :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bump_heuristics_init\<close> where
  \<open>Bump_Heuristics_Init a b c d \<equiv> Tuple4 a b c d\<close>

lemmas bump_heuristics_init_splits = Tuple4.tuple4.splits
hide_fact tuple4.splits

abbreviation get_stable_heuristics :: \<open>bump_heuristics_init \<Rightarrow> vmtf_remove_int_option_fst_As\<close> where
  \<open>get_stable_heuristics \<equiv> Tuple4_a\<close>

abbreviation get_focused_heuristics :: \<open>bump_heuristics_init \<Rightarrow> vmtf_remove_int_option_fst_As\<close> where
  \<open>get_focused_heuristics \<equiv> Tuple4_b\<close>

abbreviation is_focused_heuristics :: \<open>bump_heuristics_init \<Rightarrow> bool\<close> where
  \<open>is_focused_heuristics \<equiv> Tuple4_c\<close>

abbreviation is_stable_heuristics:: \<open>bump_heuristics_init \<Rightarrow> bool\<close> where
  \<open>is_stable_heuristics x \<equiv> \<not>is_focused_heuristics x\<close>

abbreviation get_bumped_variables :: \<open>bump_heuristics_init \<Rightarrow> nat list \<times> bool list\<close> where
  \<open>get_bumped_variables \<equiv> Tuple4_d\<close>

abbreviation set_stable_heuristics :: \<open>vmtf_remove_int_option_fst_As \<Rightarrow>bump_heuristics_init \<Rightarrow> _\<close> where
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
      get_stable_heuristics x \<in> isa_vmtf_init \<A> M \<and>
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

definition bump_heur_import_variable where
  \<open>bump_heur_import_variable L x = (case x of Bump_Heuristics_Init hstable focused foc n \<Rightarrow>
    Bump_Heuristics_Init (vmtf_heur_import_variable L hstable) (vmtf_heur_import_variable L focused) foc n)\<close>

definition initialise_VMTF :: \<open>nat list \<Rightarrow> nat \<Rightarrow> vmtf_remove_int_option_fst_As nres\<close> where
\<open>initialise_VMTF N n = do {
   let A = replicate n (VMTF_Node 0 None None);
   ASSERT(length N \<le> uint32_max);
   (n, A, cnext) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(i, A, cnext). i < length_uint32_nat N)
      (\<lambda>(i, A, cnext). do {
        ASSERT(i < length_uint32_nat N);
        let L = (N ! i);
        ASSERT(L < length A);
        ASSERT(cnext \<noteq> None \<longrightarrow> the cnext < length A);
        ASSERT(i + 1 \<le> uint32_max);
        RETURN (i + 1, vmtf_cons A L cnext (i), Some L)
      })
      (0, A, None);
   RETURN ((A, n, cnext, (if N = [] then None else Some ((N!0))), cnext))
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
      [\<lambda>(N,n). (\<forall>L\<in># N. L < n) \<and> (distinct_mset N) \<and> size N < uint32_max \<and> set_mset N = set_mset \<A>]\<^sub>f
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
              _ \<leftarrow> ASSERT (i + 1 \<le> uint32_max);
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
    if H: \<open>case y of (N, n) \<Rightarrow>(\<forall>L\<in># N. L < n) \<and> distinct_mset N \<and> size N < uint32_max \<and>
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

definition initialize_Bump_Init :: \<open>nat list \<Rightarrow> nat \<Rightarrow> bump_heuristics_init nres\<close> where
  \<open>initialize_Bump_Init A n = do {
  focused \<leftarrow> initialise_VMTF A n;
  hstable \<leftarrow> initialise_VMTF A n;
  to_remove \<leftarrow> distinct_atms_int_empty n;
  RETURN (Tuple4 hstable focused False to_remove)
  }\<close>

lemma specify_left_RES:
  assumes "m \<le> RES \<Phi>"
  assumes "\<And>x. x \<in> \<Phi> \<Longrightarrow> f x \<le> M"  
  shows "do { x \<leftarrow> m; f x } \<le> M"
  using assms by (auto simp: pw_le_iff refine_pw_simps)

lemma initialize_Bump_Init:
  shows  \<open>(uncurry initialize_Bump_Init, uncurry (\<lambda>N n. RES (bump_heur_init N []))) \<in>
      [\<lambda>(N,n). (\<forall>L\<in># N. L < n) \<and> (distinct_mset N) \<and> size N < uint32_max \<and> set_mset N = set_mset \<A>]\<^sub>f
      (\<langle>nat_rel\<rangle>list_rel_mset_rel) \<times>\<^sub>f nat_rel \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
    (is \<open>(?init, ?R) \<in> _\<close>)
  unfolding initialize_Bump_Init_def uncurry_def distinct_atms_int_empty_def nres_monad1
  apply (intro frefI nres_relI)
  apply (refine_rcg)
  apply hypsubst
  apply (rule specify_left_RES[OF initialise_VMTF[where \<A>=\<A>, THEN fref_to_Down_curry, unfolded conc_fun_RES]])
  apply assumption+
  apply (rule specify_left_RES[OF initialise_VMTF[where \<A>=\<A>, THEN fref_to_Down_curry, unfolded conc_fun_RES]])
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
  \<open>set_mset \<A> = set_mset \<B> \<Longrightarrow> L \<in> isa_vmtf_init \<A> M \<Longrightarrow> L \<in> isa_vmtf_init \<B> M\<close>
  using \<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>] atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>] vmtf_cong[of \<A> \<B>]
  unfolding isa_vmtf_init_def vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def
  by auto


lemma bump_heur_init_consD':
  \<open>vm \<in> bump_heur_init \<A> M \<Longrightarrow> vm \<in> bump_heur_init \<A> (Propagated L n # M)\<close>
  by (auto simp: bump_heur_init_def dest: isa_vmtf_init_consD')

end