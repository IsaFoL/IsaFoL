theory IsaSAT_Simplify_Pure_Literals
  imports IsaSAT_Simplify_Pure_Literals_Defs
    Watched_Literals.Watched_Literals_Watch_List_Inprocessing
    More_Refinement_Libs.WB_More_Refinement_Loops
    IsaSAT_Restart
begin

lemma isa_pure_literal_count_occs_clause_wl_pure_literal_count_occs_clause_wl:
  assumes \<open>(S, S') \<in> twl_st_heur_restart_ana' r u\<close>
    \<open>(occs, occs') \<in> \<langle>bool_rel\<rangle>map_fun_rel (D\<^sub>0 (all_init_atms_st S'))\<close>
    \<open>(C,C')\<in>nat_rel\<close>
  shows \<open>isa_pure_literal_count_occs_clause_wl C S occs remaining \<le>\<Down>{((occs, remaining), occs').
    (occs, occs') \<in> \<langle>bool_rel\<rangle>map_fun_rel (D\<^sub>0 (all_init_atms_st S'))}
    (pure_literal_count_occs_clause_wl C' S' occs')\<close>
proof -
  have pure_literal_count_occs_clause_wl_alt_def:
    \<open>pure_literal_count_occs_clause_wl C S occs = do {
    ASSERT (pure_literal_count_occs_clause_wl_pre C S occs);
    let m = length (get_clauses_wl S \<propto> C);
    (i, occs) \<leftarrow> WHILE\<^sub>T\<^bsup>pure_literal_count_occs_clause_wl_invs C S occs\<^esup> (\<lambda>(i, occs). i < m)
      (\<lambda>(i, occs). do {
        let L = get_clauses_wl S \<propto> C ! i;
        let occs = occs (L := True);
        RETURN (i+1, occs)
      })
      (0, occs);
   RETURN occs
  }\<close> for C S occs
     by (auto simp: pure_literal_count_occs_clause_wl_def)
  have [refine0]: \<open> ((0, occs, remaining), 0, occs') \<in> {((n, occs, remaining), n', occs').
             (n,n')\<in> nat_rel \<and> (occs, occs') \<in> \<langle>bool_rel\<rangle>map_fun_rel (D\<^sub>0 (all_init_atms_st S'))}\<close>
    using assms by auto
  show ?thesis
    supply RETURN_as_SPEC_refine[refine2 del]
    unfolding isa_pure_literal_count_occs_clause_wl_def pure_literal_count_occs_clause_wl_alt_def
      mop_arena_length_st_def mop_access_lit_in_clauses_heur_def
    apply (refine_vcg mop_arena_length[THEN fref_to_Down_curry, unfolded comp_def,
      of \<open>get_clauses_wl S'\<close> C' \<open>get_clauses_wl_heur S\<close> C \<open>set (get_vdom S)\<close>]
      mop_arena_lit(2)[THEN RETURN_as_SPEC_refine, of _ _ \<open>set (get_vdom S)\<close>])
    subgoal using assms unfolding isa_pure_literal_count_occs_clause_wl_pre_def by fast
    subgoal
      unfolding pure_literal_count_occs_clause_wl_pre_def
        pure_literal_count_occs_l_clause_pre_def
      by normalize_goal+ auto
    subgoal using assms by (auto simp: twl_st_heur_restart_def twl_st_heur_restart_ana_def)
    subgoal using assms unfolding isa_pure_literal_count_occs_clause_wl_invs_def by fast
    subgoal by auto
    subgoal by auto
    subgoal using assms by (auto simp: twl_st_heur_restart_def twl_st_heur_restart_ana_def)
    subgoal
      unfolding pure_literal_count_occs_clause_wl_pre_def
        pure_literal_count_occs_l_clause_pre_def
      by normalize_goal+ auto
    subgoal using assms by auto
    subgoal by auto
    subgoal by auto
    subgoal
      unfolding pure_literal_count_occs_clause_wl_pre_def
        pure_literal_count_occs_l_clause_pre_def
      by normalize_goal+
       (auto simp add: map_fun_rel_def ran_m_def all_init_atms_alt_def
        \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms(2) all_init_lits_of_wl_def all_lits_of_mm_add_mset
        dest!: multi_member_split
        dest: nth_mem_mset[THEN in_clause_in_all_lits_of_m])
    subgoal
      unfolding pure_literal_count_occs_clause_wl_pre_def
        pure_literal_count_occs_l_clause_pre_def
      apply normalize_goal+
      apply (auto 4 3 simp add: map_fun_rel_def ran_m_def all_init_atms_alt_def
        \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms(2) all_init_lits_of_wl_def all_lits_of_mm_add_mset
        dest!: multi_member_split
        dest: nth_mem_mset[THEN in_clause_in_all_lits_of_m] in_all_lits_of_mm_uminusD)
      by (metis Un_iff all_lits_of_mm_add_mset in_all_lits_of_mm_uminusD in_clause_in_all_lits_of_m
        nth_mem_mset set_mset_union)
    subgoal by (auto simp add: map_fun_rel_def)
    subgoal by auto
    done
qed


(*TODO Move*)
lemma distinct_mset_add_subset_iff: \<open>distinct_mset (A+B) \<Longrightarrow> A + B \<subseteq># C \<longleftrightarrow> A \<subseteq># C \<and> B \<subseteq># C\<close>
  by (induction A)
   (auto simp add: insert_subset_eq_iff subset_remove1_mset_notin)

lemma isa_pure_literal_count_occs_wl_pure_literal_count_occs_wl:
  assumes \<open>(S, S') \<in> twl_st_heur_restart_ana' r u\<close>
  shows \<open>isa_pure_literal_count_occs_wl S \<le>
    \<Down> (bool_rel \<times>\<^sub>f \<langle>bool_rel\<rangle>map_fun_rel (D\<^sub>0 (all_init_atms_st S')))
    (pure_literal_count_occs_wl S')\<close>
proof -
  have pure_literal_count_occs_wl_alt_def:
  \<open>pure_literal_count_occs_wl S = do {
  ASSERT (pure_literal_count_occs_wl_pre S);
  xs \<leftarrow> SPEC (\<lambda>xs. distinct_mset xs \<and> (\<forall>C\<in>#dom_m (get_clauses_wl S). irred (get_clauses_wl S) C \<longrightarrow> C \<in># xs));
  abort \<leftarrow> RES (UNIV :: bool set);
  let occs = (\<lambda>_. False);
  (_, occs, abort) \<leftarrow> WHILE\<^sub>T(\<lambda>(A, occs, abort). A \<noteq> {#} \<and> \<not>abort)
      (\<lambda>(A, occs, abort). do {
        ASSERT (A \<noteq> {#});
        C \<leftarrow> SPEC (\<lambda>C. C \<in># A);
        b \<leftarrow> RETURN (C \<in># dom_m (get_clauses_wl S));
        if (b \<and> irred (get_clauses_wl S) C) then do {
          occs \<leftarrow> pure_literal_count_occs_clause_wl C S occs;
          abort \<leftarrow> RES (UNIV :: bool set);
          RETURN (remove1_mset C A, occs, abort)
        } else RETURN  (remove1_mset C A, occs, abort)
      })
      (xs, occs, abort);
   RETURN (abort, occs)
  }\<close> for S
  by (auto simp: pure_literal_count_occs_wl_def)

  have dist: \<open>distinct_mset A \<Longrightarrow> distinct_mset B \<Longrightarrow> set_mset A \<inter> set_mset B = {} \<Longrightarrow> distinct_mset (A + B)\<close> for A B
    by (metis distinct_mset_add set_mset_eq_empty_iff set_mset_inter)

  have [refine0]: \<open>pure_literal_count_occs_wl_pre S' \<Longrightarrow>
    RETURN (get_avdom S @ get_ivdom S)
    \<le> \<Down> (list_mset_rel)
    (SPEC
      (\<lambda>xs. distinct_mset xs \<and>
      (\<forall>C\<in>#dom_m (get_clauses_wl S').
    irred (get_clauses_wl S') C \<longrightarrow> C \<in># xs)))\<close>
    apply (rule RETURN_SPEC_refine)
    apply (rule exI[of _ \<open>mset (get_avdom S @ get_ivdom S)\<close>])
    using assms unfolding twl_st_heur_restart_def twl_st_heur_restart_ana_def in_pair_collect_simp
    apply -
    apply normalize_goal+
    by (auto simp: list_mset_rel_def br_def aivdom_inv_dec_alt_def
      dest: distinct_mset_mono
      intro!: dist)
  have conj_eqI: \<open>a=a' \<Longrightarrow> b=b' \<Longrightarrow> (a&b) = (a'&b')\<close> for a a' b b'
    by auto
  have [refine0]: \<open>(get_avdom S @ get_ivdom S, xs) \<in> list_mset_rel \<Longrightarrow>
    (c \<le> 0, abort) \<in> bool_rel \<Longrightarrow>
    ((0, replicate (length (get_watched_wl_heur S)) False, c),
  xs, \<lambda>_. False, abort)
  \<in> {(i,xs). xs = mset (drop i  (get_avdom S @ get_ivdom S))} \<times>\<^sub>r \<langle>bool_rel\<rangle>map_fun_rel (D\<^sub>0 (all_init_atms_st S')) \<times>\<^sub>r {(a,b). b = (a \<le> 0)}\<close> for xs abort c
    using assms unfolding twl_st_heur_restart_def twl_st_heur_restart_ana_def in_pair_collect_simp
    apply -
    apply normalize_goal+
    by (auto simp: list_mset_rel_def br_def map_fun_rel_def all_init_atms_alt_def)
  have [refine0]: \<open>RETURN (0 \<ge> a) \<le> \<Down> bool_rel (RES UNIV)\<close> for a
    by auto
  have K: \<open>(a',b)\<in> nat_rel \<Longrightarrow> (a, a'\<in># dom_m (get_clauses_wl S')) \<in> A\<Longrightarrow> (a,b\<in># dom_m (get_clauses_wl S'))\<in>A\<close> for a b f A a'
    by auto
  have aivdom: \<open>aivdom_inv_dec (get_aivdom S) (dom_m (get_clauses_wl S'))\<close> and
    valid: \<open>valid_arena (get_clauses_wl_heur S) (get_clauses_wl S') (set (get_vdom S))\<close>
    using assms
    by (auto simp: twl_st_heur_restart_def twl_st_heur_restart_ana_def
      aivdom_inv_dec_alt_def dest!: )
  have dist_vdom: \<open>distinct (get_vdom S)\<close> and
      valid: \<open>valid_arena (get_clauses_wl_heur S) (get_clauses_wl S') (set (get_vdom S))\<close>
    using assms by (auto simp: twl_st_heur_restart_def twl_st_heur_restart_ana_def aivdom_inv_dec_alt_def)


  have vdom_incl: \<open>set (get_vdom S) \<subseteq> {MIN_HEADER_SIZE..< length (get_clauses_wl_heur S)}\<close>
    using valid_arena_in_vdom_le_arena[OF valid] arena_dom_status_iff[OF valid] by auto

  have dist: \<open>distinct_mset A \<Longrightarrow> distinct_mset B \<Longrightarrow> set_mset A \<inter> set_mset B = {} \<Longrightarrow> distinct_mset (A + B)\<close> for A B
    by (metis distinct_mset_add set_mset_eq_empty_iff set_mset_inter)
  then have dist2: \<open>distinct_mset (mset (get_avdom S @ get_ivdom S))\<close>
    using aivdom unfolding aivdom_inv_dec_alt_def
    by (auto intro!: dist dest: distinct_mset_mono)

  have \<open>mset (get_avdom S @ get_ivdom S) \<subseteq># mset (get_vdom S)\<close>
    using dist2 aivdom unfolding aivdom_inv_dec_alt_def
    by (auto simp: distinct_mset_add_subset_iff dist2)
  then have \<open>length (get_avdom S @ get_ivdom S) \<le> length (get_vdom S)\<close>
    using size_mset_mono by fastforce
  also have le_vdom_arena: \<open>length (get_vdom S) \<le> length (get_clauses_wl_heur S) - 2\<close>
    by (subst distinct_card[OF dist_vdom, symmetric])
      (use card_mono[OF _ vdom_incl] in auto)
  finally have le: \<open>length (get_avdom S @ get_ivdom S) \<le> length (get_clauses_wl_heur S) - 2\<close> .
  show ?thesis
    unfolding isa_pure_literal_count_occs_wl_def
      pure_literal_count_occs_wl_alt_def
    apply (rewrite at \<open>let _ = length _ in _\<close> Let_def)
    apply (rewrite at \<open>let _ = _ - _ in _\<close> Let_def)
    apply (refine_vcg mop_arena_status2[where vdom=\<open>set(get_vdom S)\<close> and N=\<open>get_clauses_wl S'\<close>]
      isa_pure_literal_count_occs_clause_wl_pure_literal_count_occs_clause_wl)
    subgoal by (rule le)
    subgoal by (auto simp: word_greater_zero_iff)
    subgoal by (auto simp: access_avdom_at_pre_def)
    subgoal by (auto simp: access_avdom_at_pre_def)
    subgoal by (auto simp: access_ivdom_at_pre_def length_avdom_def)
    subgoal by (auto 6 4 intro: in_set_dropI simp: nth_append)
    apply (assumption)
    subgoal
      using aivdom
      apply (simp add: aivdom_inv_dec_alt_def)
      by (metis (no_types, lifting) Un_iff length_append mset_subset_eqD nth_mem_mset
        set_mset_mset set_union_code)
    subgoal by (rule valid)
    apply (rule K;assumption)
    subgoal by auto
    apply (rule assms)
    subgoal by simp
    subgoal by (auto simp: drop_Suc_nth simp del: drop_append)
    subgoal by (auto simp: drop_Suc_nth simp del: drop_append)
    subgoal by auto
    done
qed


(*TODO dedup*)
lemma lookup_clause_rel_cong:
  \<open>set_mset \<A> = set_mset \<B> \<Longrightarrow> L \<in> lookup_clause_rel \<A> \<Longrightarrow> L \<in> lookup_clause_rel \<B>\<close>
  using  \<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>] atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>]
  unfolding lookup_clause_rel_def
  by (cases L) (auto)

lemma isa_propagate_pure_bt_wl_propagate_pure_bt_wl:
  assumes S\<^sub>0T: \<open>(S\<^sub>0, T) \<in> twl_st_heur_restart_ana' r u\<close> and
    \<open>(L,L')\<in>Id\<close>
  shows \<open>isa_propagate_pure_bt_wl L S\<^sub>0 \<le>\<Down>{(U, V). (U,V)\<in>twl_st_heur_restart_ana' r u \<and> get_vmtf_heur U = get_vmtf_heur S\<^sub>0} (propagate_pure_bt_wl L' T)\<close>
proof -
  have propagate_pure_bt_wl_alt_def:
    \<open>propagate_pure_bt_wl = (\<lambda>L (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, WS). do {
      ASSERT(propagate_pure_wl_pre L (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, WS));
      M \<leftarrow> cons_trail_propagate_l L 0 M;
      RETURN (M, N, D, NE, UE, add_mset {#L#} NEk, UEk, NS, US, N0, U0, add_mset (-L) Q, WS)})\<close>
    unfolding propagate_pure_bt_wl_def by auto
  have [refine]: \<open>S=S\<^sub>0 \<Longrightarrow> M = get_trail_wl T \<Longrightarrow>
    mop_isa_length_trail (get_trail_wl_heur S) \<le> SPEC (\<lambda>ca. (ca, length M) \<in> Id)\<close> for S M
     apply (subst twl_st_heur_restart_isa_length_trail_get_trail_wl[of _ T r])
     using S\<^sub>0T apply simp
     using S\<^sub>0T apply (simp_all add: twl_st_heur_restart_ana_def twl_st_heur_restart_def
       all_init_atms_st_alt_def all_init_atms_alt_def)
     done
   have trail: \<open>(get_trail_wl_heur S\<^sub>0, get_trail_wl T) \<in> trail_pol (all_init_atms_st T)\<close> for x2a x2
     using assms by (auto simp: twl_st_heur_restart_def twl_st_heur_restart_ana_def
       all_init_atms_alt_def)
    have H: \<open>A = B \<Longrightarrow> x \<in> A \<Longrightarrow> x \<in> B\<close> for A B x
      by auto
    have H': \<open>A = B \<Longrightarrow> A x \<Longrightarrow> B x\<close> for A B x
      by auto

    obtain M N D NE UE NEk UEk NS US N0 U0 Q WS where
      T: \<open>T = (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, WS)\<close>
      by (cases T)
    {
      assume pre: \<open>propagate_pure_wl_pre L T\<close>
     note cong =  trail_pol_cong heuristic_rel_cong
       option_lookup_clause_rel_cong
        vdom_m_cong[symmetric, THEN H] isasat_input_nempty_cong[THEN iffD1]
       isasat_input_bounded_cong[THEN iffD1]
        cach_refinement_empty_cong[THEN H']
        phase_saving_cong[THEN H']
        \<L>\<^sub>a\<^sub>l\<^sub>l_cong[THEN H]
       D\<^sub>0_cong[THEN H]
       lookup_clause_rel_cong
       map_fun_rel_D\<^sub>0_cong
       isa_vmtf_cong[THEN isa_vmtf_consD]
       isasat_input_nempty_cong[THEN iffD1]
       isasat_input_bounded_cong[THEN iffD1]
    note subst = empty_occs_list_cong
  
      let ?T = \<open>(Propagated L 0 # M, N, D, NE, UE, add_mset {#L'#} NEk, UEk, NS, US, N0, U0,
        add_mset (- L') Q, WS)\<close>
      have \<open>L' \<in># all_lits_of_mm ({#mset (fst x). x \<in># init_clss_l N#} + (NE + NEk) + NS + N0)\<close> and
        D: \<open>D = None\<close> and
        undef: \<open>undefined_lit M L'\<close>
        using pre assms(2) unfolding propagate_pure_wl_pre_def propagate_pure_l_pre_def apply -
        by (solves \<open>normalize_goal+; auto simp: T twl_st_l_def all_init_lits_of_wl_def\<close>)+
      then have H: \<open>set_mset (all_init_lits_of_wl ?T) = set_mset (all_init_lits_of_wl T)\<close>
        unfolding T by (auto simp: all_init_lits_of_wl_def
          all_lits_of_mm_add_mset all_lits_of_m_add_mset in_all_lits_of_mm_uminus_iff)
      then have H: \<open>set_mset (all_init_atms_st ?T) = set_mset (all_init_atms_st T)\<close>
        unfolding all_init_atms_st_alt_def by auto
      note _ = D undef subst[OF H] cong[OF H[symmetric]]
  } note cong = this(4-) and subst = this(3) and D = this(1) and undef = this(2)

    show ?thesis
    supply [simp del] = isasat_input_nempty_def isasat_input_bounded_def
    unfolding propagate_pure_bt_wl_alt_def isa_propagate_pure_bt_wl_def T
    apply (rewrite at \<open>let _ = get_trail_wl_heur _ in _\<close> Let_def)
    apply (rewrite at \<open>let _ = get_stats_heur _ in _\<close> Let_def)
    apply (cases S\<^sub>0)
    apply (hypsubst, unfold prod.simps)
    apply (refine_vcg
      cons_trail_Propagated_tr2[of _ _ _ _ _ _ \<open>all_init_atms_st T\<close>])
    subgoal by (auto simp: DECISION_REASON_def)
    subgoal by (rule cons_trail_Propagated_tr_pre[of _ \<open>get_trail_wl T\<close> \<open>all_init_atms_st T\<close>])
      (use \<open>(L,L')\<in>Id\<close> trail in \<open>auto simp: propagate_pure_wl_pre_def propagate_pure_l_pre_def
        state_wl_l_def twl_st_l_def \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms all_init_lits_of_wl_def all_init_lits_of_l_def
        get_init_clss_l_def T\<close>)
    subgoal by (use trail assms in \<open>auto simp: T\<close>)
    subgoal by (use \<open>(L,L')\<in>Id\<close> trail in \<open>auto simp: propagate_pure_wl_pre_def propagate_pure_l_pre_def
        state_wl_l_def twl_st_l_def \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms all_init_lits_of_wl_def all_init_lits_of_l_def
        get_init_clss_l_def T\<close>)
    subgoal using assms D undef unfolding twl_st_heur_restart_ana_def twl_st_heur_restart_def
      \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms all_init_atms_st_alt_def all_init_atms_alt_def T subst
      unfolding all_init_atms_st_alt_def[symmetric] apply -
      apply (simp only: in_pair_collect_simp)
      apply (intro conjI)
      subgoal
        apply simp
        using cong T apply fast
        done
      subgoal by simp
      subgoal
        apply simp
        using cong T apply fast
        done
      subgoal
        apply auto
        done
      subgoal
        apply simp
        done
      subgoal
        apply simp
        using cong(10-) T apply fast
        done
      subgoal apply simp using cong(10-) T by fast
      subgoal by simp
      subgoal by simp
      subgoal apply simp using cong T by fast
      subgoal by simp
      subgoal by simp
      subgoal apply simp using cong(4) T by fast
      subgoal by simp
      subgoal apply simp using cong T by fast
      subgoal by simp (use cong T in fast)
      subgoal by simp
      subgoal by simp (use cong T in fast)
      subgoal using subst by (simp add: T all_init_atms_st_def)
      subgoal by (simp add: learned_clss_count_def)
      subgoal by (simp add: learned_clss_count_def)
      subgoal by (simp add: subst)
      done
    done
qed


lemma isa_pure_literal_deletion_wl_pure_literal_deletion_wl:
  assumes S\<^sub>0T: \<open>(S\<^sub>0, T) \<in> twl_st_heur_restart_ana' r u\<close> and
    occs: \<open>(occs, occs') \<in> \<langle>bool_rel\<rangle>map_fun_rel (D\<^sub>0 (all_init_atms_st T))\<close>
  shows \<open>isa_pure_literal_deletion_wl occs S\<^sub>0 \<le>\<Down>{((_, U), V). (U,V)\<in>twl_st_heur_restart_ana' r u} (pure_literal_deletion_wl occs' T)\<close>
proof -
  have B: \<open>\<Down>Id(pure_literal_deletion_wl occs' T) \<ge>
  (do {
    ASSERT (pure_literal_deletion_wl_pre T);
    iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>l
      (\<lambda>A (T). do {
         ASSERT (A \<in># all_init_atms_st T);
         let L = (if occs' (Pos A) \<and> \<not> occs' (Neg A)
                  then Pos A else Neg A);
         let val = polarity (get_trail_wl T) L;
         if \<not>occs' (-L) \<and> val = None
         then do {S \<leftarrow> propagate_pure_bt_wl L T;
          RETURN (S)}
        else RETURN (T)
           })
           (atm_of `# all_init_lits_of_wl T)
     (\<lambda>xs S. pure_literal_deletion_wl_inv T (atm_of `# all_init_lits_of_wl T) (S, xs))
     (T)})\<close> (is \<open>_ \<ge> ?B\<close> is \<open>_ \<ge> do { ASSERT _; iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>l ?f _ _ _}\<close>)
  proof -
    have [refine0]: \<open>(x, xs) \<in> Id \<Longrightarrow> set_mset x = set_mset (atm_of `# all_init_lits_of_wl T) \<Longrightarrow>
      ((x, T), T, xs) \<in> {((a,b), (c,d)). (a,d) \<in>Id \<and> (b,c)\<in>Id}\<close> for x xs
      by (auto simp: all_init_atms_st_alt_def)
    have K: \<open>a=b \<Longrightarrow> a \<le>\<Down>Id b\<close> for a b
      by auto
    have Lin: \<open>pure_literal_deletion_wl_inv T (atm_of `# all_init_lits_of_wl T) (x1, x2) \<Longrightarrow>
       L \<in># x2 \<Longrightarrow> L \<in># all_init_atms_st x1\<close> for L x1 x2
     unfolding pure_literal_deletion_wl_inv_def prod.simps pure_literal_deletion_l_inv_def
     apply normalize_goal+
     apply (simp add: all_init_atms_st_alt_def)
     by (metis (no_types, lifting) all_init_lits_of_l_all_init_lits_of_wl mset_subset_eqD
       multiset.set_map rtranclp_cdcl_twl_pure_remove_l_same(7))

    show ?thesis
      unfolding iterate_over_VMTF_def pure_literal_deletion_wl_def
        pure_literal_deletion_candidates_wl_def iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>l_def
        iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>lC_def nres_monad3 nres_bind_let_law If_bind_distrib
      apply (rewrite at \<open>let _ =  \<Union> _ in _\<close> Let_def)
      apply refine_vcg
      subgoal by (auto simp: all_init_atms_st_alt_def)
      subgoal by fast
      subgoal for \<A> xs x x' x1 x2
        unfolding all_init_atms_st_alt_def pure_literal_deletion_l_inv_def
        pure_literal_deletion_wl_inv_def case_prod_beta
        apply normalize_goal+
        apply (rename_tac ya yb yc, rule_tac x=ya in exI[of])
        apply (rule_tac x=yb in exI[of])
        apply (intro conjI)
        apply simp
        apply simp
        apply (rule_tac x=yc in exI[of])
        apply simp_all
        by (metis distinct_subseteq_iff set_image_mset subset_mset.dual_order.trans subset_mset.order_refl)
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by (simp add: Lin)
      subgoal by (auto simp: polarity_def)
      apply (rule K)
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      done
   qed

   have vmtf: \<open>get_vmtf_heur S\<^sub>0 \<in> bump_heur (all_init_atms_st T) (get_trail_wl T)\<close> and
     nempty: \<open>isasat_input_nempty (all_init_atms_st T)\<close> and
     bounded: \<open>isasat_input_bounded (all_init_atms_st T)\<close>
     using assms unfolding twl_st_heur_restart_ana_def twl_st_heur_restart_def
     by (simp_all add: all_init_atms_alt_def del: isasat_input_nempty_def)
  let ?vm = \<open>get_vmtf_heur S\<^sub>0\<close>
  obtain M where vmtf': \<open>(get_vmtf_heur_array S\<^sub>0, fst (snd (bump_get_heuristics ?vm)),
    get_vmtf_heur_fst S\<^sub>0, fst (snd (snd (snd (bump_get_heuristics ?vm)))), snd (snd (snd (snd (bump_get_heuristics ?vm))))) \<in> vmtf (all_init_atms_st T) M\<close> and
    M: \<open>M = (get_trail_wl T)  \<or> M = (get_unit_trail (get_trail_wl T))\<close>
    using vmtf unfolding bump_heur_def get_vmtf_heur_array_def bump_get_heuristics_def get_vmtf_heur_fst_def
    by (cases \<open>bump_get_heuristics ns\<close>) (auto simp: bump_get_heuristics_def bumped_vmtf_array_fst_def
      split: if_splits)
   have C: \<open>\<Down>Id ?B \<ge> (do {
     ASSERT (pure_literal_deletion_wl_pre T);
     (S) \<leftarrow> iterate_over_VMTF ?f
     (\<lambda>S. \<exists>xs. pure_literal_deletion_wl_inv T (atm_of `# all_init_lits_of_wl T) (S, xs))
     (get_vmtf_heur_array S\<^sub>0, Some (get_vmtf_heur_fst S\<^sub>0)) (T);
     RETURN (S)
     })\<close> (is \<open>_ \<ge> ?C\<close>)
     apply (refine_vcg iterate_over_VMTF_iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>l)
     unfolding nres_monad2 all_init_atms_st_alt_def[symmetric]
     apply (rule iterate_over_VMTF_iterate_over_\<L>\<^sub>a\<^sub>l\<^sub>l[OF vmtf'])
     subgoal using nempty by auto
     subgoal using bounded by auto
     subgoal by blast
     done

   have D: \<open>\<Down>(twl_st_heur_restart_ana' r u) ?C \<ge>
  (do {
    ASSERT (pure_literal_deletion_wl_pre T);
    S \<leftarrow> iterate_over_VMTF
      (\<lambda>A (T). do {
         ASSERT (nat_of_lit (Pos A) < length occs);
         ASSERT (nat_of_lit (Neg A) < length occs);
         ASSERT (occs ! (nat_of_lit(Pos A)) = occs' (Pos A));
         ASSERT (occs ! (nat_of_lit(Neg A)) = occs' (Neg A));
         let L = (if occs ! (nat_of_lit(Pos A)) \<and> \<not> occs ! (nat_of_lit (Neg A))
                  then Pos A else Neg A);
         val \<leftarrow> mop_polarity_pol (get_trail_wl_heur T) L;
         ASSERT (nat_of_lit (-L) < length occs);
         if \<not>occs ! nat_of_lit (-L) \<and> val = None
         then do {S \<leftarrow> isa_propagate_pure_bt_wl L T;
           ASSERT (get_vmtf_heur_array S\<^sub>0 = get_vmtf_heur_array S);
          RETURN (S)}
        else RETURN (T)
           })
      (\<lambda>S. get_vmtf_heur_array S\<^sub>0 = get_vmtf_heur_array S)
     (get_vmtf_heur_array S\<^sub>0, Some (get_vmtf_heur_fst S\<^sub>0))
     (S\<^sub>0);
    RETURN S})\<close> (is \<open>_ \<ge> ?D\<close>)
   proof -
     have [refine]: \<open> ((Some (get_vmtf_heur_fst S\<^sub>0), S\<^sub>0), Some (get_vmtf_heur_fst S\<^sub>0), T)
       \<in> Id \<times>\<^sub>r {(U,V). (U,V)\<in>twl_st_heur_restart_ana' r u \<and> get_vmtf_heur_array S\<^sub>0 = get_vmtf_heur_array U}\<close>
       using assms by auto
     have H: \<open>P \<in>#\<L>\<^sub>a\<^sub>l\<^sub>l (atm_of `# all_init_lits_of_wl A) \<longleftrightarrow> atm_of P \<in># all_init_atms_st A\<close> for P A
       using \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms(2) in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n by (metis all_init_atms_st_alt_def)
     have K: \<open>a=b \<Longrightarrow>(a,b)\<in>Id\<close> for a b
       by auto
     have [simp, intro!]: \<open>(x2a, x2) \<in> twl_st_heur_restart_ana r \<Longrightarrow>
    (get_trail_wl_heur x2a, get_trail_wl x2) \<in> trail_pol (atm_of `# all_init_lits_of_wl x2)\<close> for x2a x2
       by (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def
         all_init_atms_alt_def all_init_atms_st_alt_def)
     have occs_st: \<open>occs ! (nat_of_lit (Pos (x1))) = occs' (Pos (x1))\<close>
       \<open>occs ! (nat_of_lit (Neg (x1))) = occs' (Neg (x1))\<close>
       \<open>nat_of_lit (Pos x1) < length occs\<close>
       \<open>nat_of_lit (Neg x1) < length occs\<close>
       if inv: \<open>\<exists>xs. pure_literal_deletion_wl_inv T (atm_of `# all_init_lits_of_wl T) (x2, xs)\<close>
         \<open>x1 \<in># all_init_atms_st x2\<close> for x1 x2
     proof -
       obtain xs where inv: \<open>pure_literal_deletion_wl_inv T (atm_of `# all_init_lits_of_wl T) (x2, xs)\<close>
         using inv by auto
       have  \<open>x1 \<in># all_init_atms_st T\<close>
         using inv unfolding pure_literal_deletion_wl_inv_def prod.simps
           pure_literal_deletion_l_inv_def apply -
         by normalize_goal+
           (metis (no_types, opaque_lifting) all_init_atms_st_alt_def
           all_init_lits_of_l_all_init_lits_of_wl rtranclp_cdcl_twl_pure_remove_l_same(7) set_image_mset that(2))
       then show \<open>occs ! (nat_of_lit (Pos (x1))) = occs' (Pos (x1))\<close>
         \<open>occs ! (nat_of_lit (Neg (x1))) = occs' (Neg (x1))\<close>
       \<open>nat_of_lit (Pos x1) < length occs\<close>
       \<open>nat_of_lit (Neg x1) < length occs\<close>
         using occs by (auto simp: map_fun_rel_def \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset dest!: multi_member_split)
     qed
     show ?thesis
       unfolding iterate_over_VMTF_def nres_monad3 nres_bind_let_law prod.simps If_bind_distrib
         mop_polarity_pol_def nres_monad2 nres_monad1[of _ \<open>\<lambda>x. RETURN (_,x)\<close>]
       apply (refine_vcg isa_propagate_pure_bt_wl_propagate_pure_bt_wl[where r=r and u=u])
       subgoal by auto
       subgoal by auto
       subgoal by auto
       subgoal by auto
       subgoal by auto
       subgoal for x x' x1 x2 x1a x2a
         unfolding case_prod_beta
         by (rule occs_st) (assumption, simp)
       subgoal for x x' x1 x2 x1a x2a
         unfolding case_prod_beta
         by (rule occs_st) (assumption, simp)
       subgoal for x x' x1 x2 x1a x2a
         unfolding case_prod_beta
         by (rule occs_st) (assumption, simp)
       subgoal for x x' x1 x2 x1a x2a
         unfolding case_prod_beta
         by (rule occs_st) (assumption, simp)
       subgoal for x x' x1 x2 x1a x2a
         by (rule polarity_pol_pre[of _ _ \<open>(all_init_atms_st x2)\<close>])
          (auto simp add: H \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms all_init_atms_st_alt_def all_init_atms_alt_def)
      apply (rule K)
      subgoal for x x' x1 x2 x1a x2a
        using assms
        by (auto intro!: polarity_pol_polarity[of \<open>(all_init_atms_st x2)\<close>, unfolded option_rel_id_simp, THEN fref_to_Down_unRET_uncurry_Id]
          simp: H all_init_atms_st_alt_def)
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by (auto simp: get_vmtf_heur_array_def)
      subgoal by auto
      subgoal by auto
      subgoal by auto
      done
  qed

  have E: \<open>\<Down>{((_, U), V). (U,V)\<in>Id}?D \<ge> isa_pure_literal_deletion_wl_raw occs S\<^sub>0\<close> (is \<open>_ \<ge> ?E\<close>)
  proof -
     have K: \<open>a=b \<Longrightarrow> a\<le>\<Down>Id b\<close> for a b
       by auto
     have H1: \<open>(S, x'a) \<in> Id \<Longrightarrow> ((x1b + 1, S), x'a)  \<in> {((a,b),c). (b,c)\<in>Id}\<close> for S x'a x1b
       by auto
         have H2: \<open>\<And>x x' x1 x2 x1a x2a.
    pure_literal_deletion_wl_pre T \<Longrightarrow>
    isa_pure_literal_deletion_wl_pre S\<^sub>0 \<Longrightarrow>
           (x, x') \<in> {((a, b, c), x, y). (a, x) \<in> Id \<and> (c, y) \<in> Id} \<Longrightarrow> x' = (x1, x2) \<Longrightarrow> x = (x1a, x2a) \<Longrightarrow> (x2a, x2) \<in> {((a,b),c). (b,c)\<in>Id}\<close>
           by auto
    have [refine]: \<open>((Some (get_vmtf_heur_fst S\<^sub>0), 0, S\<^sub>0), Some (get_vmtf_heur_fst S\<^sub>0), S\<^sub>0) \<in>
      {((a,b,c), (x,y)). (a,x)\<in> Id \<and> (c,y)\<in>Id}\<close> by auto
    show ?thesis
      unfolding isa_pure_literal_deletion_wl_raw_def iterate_over_VMTF_def prod.simps Let_def
      apply refine_vcg
      subgoal using assms unfolding isa_pure_literal_deletion_wl_pre_def by  fast
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      apply (rule K)
      subgoal by auto
      subgoal by auto
      apply (rule K)
      subgoal by auto
      subgoal by auto
      apply (rule H1)
      subgoal by auto
      subgoal by auto
      subgoal by auto
      apply (rule H2; assumption)
      subgoal by auto
      done
   qed
   have F: \<open>\<Down>Id ?E \<ge> isa_pure_literal_deletion_wl occs S\<^sub>0\<close>
   proof -
     have [refine]: \<open>((Some (get_vmtf_heur_fst S\<^sub>0), 0, S\<^sub>0), snd (get_vmtf_heur_array S\<^sub>0, Some (get_vmtf_heur_fst S\<^sub>0)), 0, S\<^sub>0) \<in> Id \<times>\<^sub>r Id \<times>\<^sub>r Id\<close>
       by auto
     have K: \<open>a=b \<Longrightarrow> a\<le>\<Down>Id b\<close> for a b
       by auto
     show ?thesis
       unfolding isa_pure_literal_deletion_wl_def isa_pure_literal_deletion_wl_raw_def
         iterate_over_VMTF_def nres_monad3 nres_monad2 If_bind_distrib case_prod_beta
         nres_bind_let_law
       apply refine_vcg
       subgoal by auto
       subgoal by auto
       subgoal by auto
       subgoal by auto
       subgoal by auto
       subgoal by auto
       subgoal by auto
       apply (rule K)
       subgoal by auto
       subgoal by auto
       apply (rule K)
       subgoal by auto
       subgoal by auto
       subgoal by auto
       subgoal by auto
       subgoal by auto
       done
   qed
   show ?thesis
     apply (rule order_trans[OF F])
     apply (rule order_trans)
     apply (rule ref_two_step'[OF E])
     apply (subst conc_fun_chain)
     apply (rule order_trans)
     apply (rule ref_two_step'[OF D])
     apply (subst conc_fun_chain)
     apply (rule order_trans)
     apply (rule ref_two_step'[OF C])
     apply (subst conc_fun_chain)
     apply (rule order_trans)
     apply (rule ref_two_step'[OF B])
     apply (rule ref_two_step'')
     by auto
qed

end