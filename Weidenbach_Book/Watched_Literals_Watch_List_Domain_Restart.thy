theory Watched_Literals_Watch_List_Domain_Restart
  imports Watched_Literals_Watch_List_Domain Watched_Literals_Watch_List_Restart
begin

locale isasat_restart_ops =
  twl_restart + isasat_input_ops

locale isasat_restart_bounded =
  twl_restart + isasat_input_bounded

lemma cdcl_twl_restart_get_all_init_clss:
  assumes \<open>cdcl_twl_restart S T\<close>
  shows \<open>get_all_init_clss T = get_all_init_clss S\<close>
  using assms by (induction rule: cdcl_twl_restart.induct) auto

lemma rtranclp_cdcl_twl_restart_get_all_init_clss:
  assumes \<open>cdcl_twl_restart\<^sup>*\<^sup>* S T\<close>
  shows \<open>get_all_init_clss T = get_all_init_clss S\<close>
  using assms by (induction rule: rtranclp_induct) (auto simp: cdcl_twl_restart_get_all_init_clss)


context isasat_input_ops
begin

lemma cdcl_twl_restart_is_\<L>\<^sub>a\<^sub>l\<^sub>l:
  assumes
    ST: \<open>cdcl_twl_restart\<^sup>*\<^sup>* S T\<close> and
    struct_invs_S: \<open>twl_struct_invs S\<close> and
    L: \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l (all_lits_of_mm (clauses (get_clauses S) + unit_clss S))\<close>
  shows  \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l (all_lits_of_mm (clauses (get_clauses T) + unit_clss T))\<close>
proof -
  have \<open>twl_struct_invs T\<close>
    using rtranclp_cdcl_twl_restart_twl_struct_invs[OF ST struct_invs_S] .
  then have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of T)\<close>
    unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  then have \<open>?thesis \<longleftrightarrow> is_\<L>\<^sub>a\<^sub>l\<^sub>l (all_lits_of_mm (get_all_init_clss T))\<close>
    unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def is_\<L>\<^sub>a\<^sub>l\<^sub>l_alt_def
    by (cases T)
      (auto simp: cdcl\<^sub>W_restart_mset_state)
  moreover have \<open>get_all_init_clss T = get_all_init_clss S\<close>
    using rtranclp_cdcl_twl_restart_get_all_init_clss[OF ST] .
  moreover {
    have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of S)\<close>
      using struct_invs_S
      unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast+
    then have \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l (all_lits_of_mm (get_all_init_clss S))\<close>
      using L
      unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def is_\<L>\<^sub>a\<^sub>l\<^sub>l_alt_def
      by (cases S)
        (auto simp: cdcl\<^sub>W_restart_mset_state)
  }
  ultimately show ?thesis
    by argo
qed

end

context isasat_restart_bounded
begin

sublocale isasat_restart_ops
  by standard

definition remove_all_annot_true_clause_imp_wl_D_inv
  :: \<open>nat twl_st_wl \<Rightarrow> _ \<Rightarrow> nat \<times> nat twl_st_wl \<Rightarrow> bool\<close>
where
  \<open>remove_all_annot_true_clause_imp_wl_D_inv S xs = (\<lambda>(i, T).
     remove_all_annot_true_clause_imp_wl_inv S xs (i, T) \<and>
     literals_are_\<L>\<^sub>i\<^sub>n T)\<close>

lemma remove_all_annot_true_clause_imp_wl_inv_literals_are_\<L>\<^sub>i\<^sub>n:
  assumes
    inv: \<open>remove_all_annot_true_clause_imp_wl_inv S xs (i, T)\<close> and
    L: \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close>
  shows \<open>literals_are_\<L>\<^sub>i\<^sub>n T\<close>
proof -
  obtain S2 T2 S3 where
    part_S: \<open>partial_correct_watching S\<close> and
    part_T: \<open>partial_correct_watching T\<close> and
    S_S2: \<open>(S, S2) \<in> state_wl_l None\<close> and
    T_T2: \<open>(T, T2) \<in> state_wl_l None\<close> and
    S2_T2:\<open>remove_one_annot_true_clause\<^sup>*\<^sup>* S2 T2\<close> and
    list_invs_S2: \<open>twl_list_invs S2\<close> and
    \<open>i \<le> length xs\<close> and
    \<open>twl_list_invs S2\<close> and
    confl_S2: \<open>get_conflict_l S2 = None\<close> and
    upd_S2: \<open>clauses_to_update_l S2 = {#}\<close> and
    S2_S3: \<open>(S2, S3) \<in> twl_st_l None\<close> and
    struct_invs_S3: \<open>twl_struct_invs S3\<close>
    using inv unfolding remove_all_annot_true_clause_imp_wl_inv_def
      remove_all_annot_true_clause_imp_inv_def prod.case
    by blast

  obtain T3 where
    T2_T2: \<open>(T2, T3) \<in> twl_st_l None\<close> and
    struct_invs_T3: \<open>twl_struct_invs T3\<close> and
    S3_T3: \<open>cdcl_twl_restart\<^sup>*\<^sup>* S3 T3\<close> and
    \<open>cdcl_twl_restart_l\<^sup>*\<^sup>* S2 T2\<close>
    using rtranclp_remove_one_annot_true_clause_cdcl_twl_restart_l2[OF S2_T2 list_invs_S2
      confl_S2 upd_S2 S2_S3 struct_invs_S3] by blast

  show ?thesis
    using cdcl_twl_restart_is_\<L>\<^sub>a\<^sub>l\<^sub>l[OF S3_T3  struct_invs_S3] L
    S_S2 T_T2 S2_S3 T2_T2
    by (auto simp: mset_take_mset_drop_mset')
qed

definition remove_all_annot_true_clause_imp_wl_D_pre
  :: \<open>nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> bool\<close>
where
  \<open>remove_all_annot_true_clause_imp_wl_D_pre L S \<longleftrightarrow> (L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> literals_are_\<L>\<^sub>i\<^sub>n S)\<close>

definition remove_all_annot_true_clause_imp_wl_D
  :: \<open>nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> (nat twl_st_wl) nres\<close>
where
\<open>remove_all_annot_true_clause_imp_wl_D = (\<lambda>L (M, N0, D, NE0, UE, Q, W). do {
    ASSERT(remove_all_annot_true_clause_imp_wl_D_pre L (M, N0, D, NE0, UE, Q, W));
    let xs = W L;
    (_, N, NE) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i, N, NE).
        remove_all_annot_true_clause_imp_wl_D_inv (M, N0, D, NE0, UE, Q, W) xs
          (i, M, N, D, NE, UE, Q, W)\<^esup>
      (\<lambda>(i, N, NE). i < length xs)
      (\<lambda>(i, N, NE). do {
        ASSERT(i < length xs);
        if xs!i \<in># dom_m N
        then do {
          (N, NE) \<leftarrow> remove_all_annot_true_clause_one_imp (xs!i, N, NE);
          ASSERT(remove_all_annot_true_clause_imp_wl_D_inv (M, N0, D, NE0, UE, Q, W) xs
            (i, M, N, D, NE, UE, Q, W));
          RETURN (i+1, N, NE)
        }
        else
          RETURN (i+1, N, NE)
      })
      (0, N0, NE0);
    RETURN (M, N, D, NE, UE, Q, W)
  })\<close>

text \<open>
  We are actually slighty ``cheating'' in this refinement step: thanks to the assertion
  after the call to \<^term>\<open>remove_all_annot_true_clause_one_imp\<close>, we do not need to refine it.
\<close>
lemma remove_all_annot_true_clause_imp_wl_remove_all_annot_true_clause_imp:
  \<open>(uncurry remove_all_annot_true_clause_imp_wl_D, uncurry remove_all_annot_true_clause_imp_wl) \<in>
   {(L, L'). L = L' \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l} \<times>\<^sub>f {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S} \<rightarrow>\<^sub>f
     \<langle>{(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S}\<rangle>nres_rel\<close>
proof -
  have remove_all_annot_true_clause_imp_wl_D_inv:
    \<open>remove_all_annot_true_clause_imp_wl_D_inv S xs(i, T)\<close>
    if
      \<open>remove_all_annot_true_clause_imp_wl_inv S xs (i, T)\<close> and
      \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close>
    for S xs i T
    using that remove_all_annot_true_clause_imp_wl_inv_literals_are_\<L>\<^sub>i\<^sub>n[of S xs i T]
    unfolding remove_all_annot_true_clause_imp_wl_D_inv_def
    by blast
  have [refine0]:
    \<open>remove_all_annot_true_clause_one_imp S \<le> \<Down> Id (remove_all_annot_true_clause_one_imp S')\<close>
    if \<open>(S, S') \<in> Id\<close>
    for S S'
    using that by auto
  show ?thesis
    supply [[goals_limit=1]]
    unfolding uncurry_def remove_all_annot_true_clause_imp_wl_D_def
      remove_all_annot_true_clause_imp_wl_def
    apply (intro frefI nres_relI)
    apply clarify
    subgoal for L M N0 D NE0 UE Q W L' M' N0' D' NE0' UE' Q' W'
      apply (refine_vcg
          WHILEIT_refine[where R = \<open>{((i, N, NE), (i', N', NE')). i = i' \<and> N=N' \<and>NE=NE' \<and>
            literals_are_\<L>\<^sub>i\<^sub>n (M, N, D, NE, UE, Q, W)}\<close>])
      subgoal unfolding remove_all_annot_true_clause_imp_wl_D_pre_def by force
      subgoal by auto
      subgoal by (rule remove_all_annot_true_clause_imp_wl_D_inv) auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by (rule remove_all_annot_true_clause_imp_wl_D_inv) auto
      subgoal unfolding remove_all_annot_true_clause_imp_wl_D_inv_def by auto
      subgoal by auto
      subgoal unfolding remove_all_annot_true_clause_imp_wl_D_pre_def by auto
      done
    done
qed

definition remove_one_annot_true_clause_one_imp_wl_D_pre where
  \<open>remove_one_annot_true_clause_one_imp_wl_D_pre i T \<longleftrightarrow>
     remove_one_annot_true_clause_one_imp_wl_pre i T \<and>
     literals_are_\<L>\<^sub>i\<^sub>n T\<close>

definition remove_one_annot_true_clause_one_imp_wl_D
  :: \<open>nat \<Rightarrow> nat twl_st_wl \<Rightarrow> (nat \<times> nat twl_st_wl) nres\<close>
where
\<open>remove_one_annot_true_clause_one_imp_wl_D = (\<lambda>i (M, N, D, NE, UE, Q, W). do {
      ASSERT(remove_one_annot_true_clause_one_imp_wl_D_pre i (M, N, D, NE, UE, Q, W));
      (L, C) \<leftarrow> SPEC(\<lambda>(L, C). (rev M)!i = Propagated L C);
      if C = 0 then RETURN (i+1, M, N, D, NE, UE, Q, W)
      else do {
        ASSERT(C \<in># dom_m N);
        M \<leftarrow> replace_annot_in_trail_spec M L;
        (N', C, b) \<leftarrow> extract_and_remove N C;
        let S = (if b then (M, N', D, add_mset (mset C) NE, UE, Q, W)
                      else (M, N', D, NE, add_mset (mset C) UE, Q, W));
        S \<leftarrow> remove_all_annot_true_clause_imp_wl_D L S;
        RETURN (i+1, S)
      }
  })\<close>


lemma remove_one_annot_true_clause_one_imp_wl_D_remove_one_annot_true_clause_one_imp_wl:
  \<open>(uncurry remove_one_annot_true_clause_one_imp_wl_D,
    uncurry remove_one_annot_true_clause_one_imp_wl) \<in>
   nat_rel \<times>\<^sub>f {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S} \<rightarrow>\<^sub>f
     \<langle>nat_rel \<times>\<^sub>f {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S}\<rangle>nres_rel\<close>
proof -

  have [refine0]: \<open>replace_annot_in_trail_spec L M \<le> \<Down> Id (replace_annot_in_trail_spec L' M')\<close>
    if \<open>(L, L') \<in> Id\<close> and \<open>(M ,M') \<in> Id\<close> for L L' M M'
    using that by auto
  have [refine0]: \<open>extract_and_remove N j \<le> \<Down> {((N1, C1, b1), (N1', C1', b1')).
         N1' = fmdrop j N \<and> C1' = N\<propto>j \<and>
         b1 = irred N j \<and> N1 = N1' \<and> C1 = C1' \<and> b1 = b1'} (extract_and_remove N' j')\<close>
       (is \<open>_ \<le> \<Down> ?extract_and_remove _\<close>)
    if \<open>(j, j') \<in> Id\<close> and \<open>(N ,N') \<in> Id\<close> and \<open>j' \<in># dom_m N'\<close>
    for j j' :: nat and M M' N N' and C C'
    using that
    by (auto simp: extract_and_remove_def intro_spec_refine_iff
        intro!: ASSERT_refine_left RES_refine)
  have x1_Lall: \<open>x1 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    if
      pre: \<open>remove_one_annot_true_clause_one_imp_wl_pre L'
      (M', N0', D', NE0', UE', Q', W')\<close> and
      x1: \<open>rev M' ! L' = Propagated x1 x2\<close> and
      L: \<open>literals_are_\<L>\<^sub>i\<^sub>n (M', N0', D', NE0', UE', Q', W')\<close>
    for x1 L' N0' D' NE0' UE' Q' W' M' x2
  proof -
    obtain x xa where
      x: \<open>((M', N0', D', NE0', UE', Q', W'), x) \<in> state_wl_l None\<close> and
      \<open>partial_correct_watching
      (M', N0', D', NE0', UE', Q', W')\<close> and
      \<open>twl_list_invs x\<close> and
      le: \<open>L' < length (get_trail_l x)\<close> and
      \<open>twl_list_invs x\<close> and
      \<open>get_conflict_l x = None\<close> and
      \<open>clauses_to_update_l x = {#}\<close> and
      x_xa: \<open>(x, xa) \<in> twl_st_l None\<close> and
      struct_invs_xa: \<open>twl_struct_invs xa\<close>
      using pre unfolding remove_one_annot_true_clause_one_imp_wl_pre_def
       remove_one_annot_true_clause_one_imp_pre_def by blast
    have le': \<open>L' < length M'\<close>
      using le x by auto
    have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail (get_trail_wl (M', N0', D', NE0', UE', Q', W'))\<close>
      apply (rule literals_are_\<L>\<^sub>i\<^sub>n_literals_are_\<L>\<^sub>i\<^sub>n_trail)
         apply (rule x)
        apply (rule struct_invs_xa)
       apply (rule x_xa)
      apply (rule L)
      done
    from literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l_atms[OF this, of \<open>lit_of (rev M' ! L')\<close>]
    have \<open>atm_of (lit_of (rev M' ! L')) \<in># \<A>\<^sub>i\<^sub>n\<close>
      using le' by (auto simp: rev_nth lits_of_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n)
    then show ?thesis
      using x1 by (auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n)
  qed
  have res: \<open>((x1a,
        if x2e
        then (Ma, x1d, D, add_mset (mset x1e) NE0,
              UE, Q, W)
        else (Ma, x1d, D, NE0,
              add_mset (mset x1e) UE, Q, W)),
       x1,
       if x2c
       then (Maa, x1b, D',
             add_mset (mset x1c) NE0', UE', Q', W')
       else (Maa, x1b, D', NE0',
             add_mset (mset x1c) UE', Q', W'))
      \<in> {(L, L'). L = L' \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l} \<times>\<^sub>f
         {(S, T).
          (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S}\<close>
    if
      eq': \<open>((L, M, N0, D, NE0, UE, Q, W), L', M', N0', D', NE0', UE', Q', W') \<in> nat_rel \<times>\<^sub>f
        {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S}\<close>
      \<open>(Ma, Maa) \<in> Id\<close>
      \<open>(x, x') \<in> Id\<close> and
      \<open>remove_one_annot_true_clause_one_imp_wl_pre L' (M', N0', D', NE0', UE', Q', W')\<close> and
      pre: \<open>remove_one_annot_true_clause_one_imp_wl_D_pre
      L (M, N0, D, NE0, UE, Q, W)\<close> and
      lit:
        \<open>x \<in> {(La, C). rev M ! L = Propagated La C}\<close>
        \<open>x' \<in> {(L, C). rev M' ! L' = Propagated L C}\<close> and
      \<open>x2a \<noteq> 0\<close> and
      \<open>x2 \<noteq> 0\<close> and
      \<open>x2 \<in># dom_m N0'\<close> and
      \<open>x2a \<in># dom_m N0\<close> and
      eq: \<open>(xa, x'a) \<in> {((N1, C1, b1), N1', C1', b1').
         N1' = fmdrop x2a N0 \<and>
         C1' = N0 \<propto> x2a \<and>
         b1 = irred N0 x2a \<and>
         N1 = N1' \<and> C1 = C1' \<and> b1 = b1'}\<close> and
      st:
        \<open>x2b = (x1c, x2c)\<close>
        \<open>x'a = (x1b, x2b)\<close>
        \<open>x2d = (x1e, x2e)\<close>
        \<open>xa = (x1d, x2d)\<close>
        \<open>x' = (x1, x2)\<close> and
        \<open>x = (x1a, x2a)\<close>
    for x x' x1 x2 x1a x2a Ma Maa xa x'a x1b x2b x1c
      x2c x1d x2d x1e x2e L M N0 D NE0 UE Q W L' M' N0' D' NE0' UE' Q' W'
  proof -
    have st':
      \<open>x2b = (N0' \<propto> x2a, irred N0' x2a)\<close>
      \<open>x'a = (fmdrop x2a N0', N0' \<propto> x2a, irred N0' x2a)\<close>
      \<open>x2d = the (fmlookup N0' x2a)\<close>
      \<open>xa = (fmdrop x2a N0', the (fmlookup N0' x2a))\<close>
      \<open>x' = (x1, x2)\<close>
      \<open>Ma = Maa\<close>
      \<open>x = (x1, x2)\<close>
      \<open>x1b = fmdrop x2a N0'\<close>
      \<open>L = L'\<close>
      \<open>x1c = N0' \<propto> x2a\<close>
      \<open>M = M'\<close>
      \<open>N0 = N0'\<close>
      \<open>x1d = fmdrop x2a N0'\<close>
      \<open>D = D'\<close>
      \<open>x1e = N0' \<propto> x2a\<close>
      \<open>NE0 = NE0'\<close>
      \<open>UE = UE'\<close>
      \<open>Q = Q'\<close>
      \<open>W = W'\<close>
      \<open>x2e = irred N0' x2a\<close>
      \<open>x2c = x2e\<close>
      using st eq eq'
      by (cases \<open>the (fmlookup N0' x2a)\<close>; auto)+
    have [simp]: \<open>x1a = x1\<close>
      using \<open>x = (x1a, x2a)\<close> unfolding \<open>x = (x1, x2)\<close>
      by auto
    obtain x xa where
      L: \<open>literals_are_\<L>\<^sub>i\<^sub>n (M, N0, D, NE0, UE, Q, W)\<close> and
      x: \<open>((M, N0, D, NE0, UE, Q, W), x) \<in> state_wl_l None\<close> and
      \<open>partial_correct_watching (M, N0, D, NE0, UE, Q, W)\<close> and
      \<open>twl_list_invs x\<close> and
      le: \<open>L < length (get_trail_l x)\<close> and
      \<open>twl_list_invs x\<close> and
      \<open>get_conflict_l x = None\<close> and
      \<open>clauses_to_update_l x = {#}\<close> and
      x_xa: \<open>(x, xa) \<in> twl_st_l None\<close> and
      struct_invs_xa: \<open>twl_struct_invs xa\<close>
      using pre unfolding remove_one_annot_true_clause_one_imp_wl_pre_def
       remove_one_annot_true_clause_one_imp_pre_def remove_one_annot_true_clause_one_imp_wl_D_pre_def
      by blast
    have le': \<open>L < length M\<close>
      using le x by auto
    have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail (get_trail_wl (M, N0, D, NE0, UE, Q, W))\<close>
      apply (rule literals_are_\<L>\<^sub>i\<^sub>n_literals_are_\<L>\<^sub>i\<^sub>n_trail)
         apply (rule x)
        apply (rule struct_invs_xa)
       apply (rule x_xa)
      apply (rule L)
      done
    from literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l_atms[OF this, of \<open>lit_of (rev M ! L)\<close>]
    have \<open>atm_of (lit_of (rev M ! L)) \<in># \<A>\<^sub>i\<^sub>n\<close>
      using le' by (auto simp: rev_nth lits_of_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n)
    then have \<open>x1a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
      using lit x unfolding st' by (auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n st state_wl_l_def st
          split: if_splits)
    then show ?thesis
      using x \<open>x2a \<in># dom_m N0\<close> L unfolding st by (auto simp: st' ran_m_fmdrop
          image_mset_remove1_mset_if)
  qed
  show ?thesis
    supply [[goals_limit=1]]
    unfolding uncurry_def remove_one_annot_true_clause_one_imp_wl_D_def
      remove_one_annot_true_clause_one_imp_wl_def
    apply (intro frefI nres_relI)
    apply clarify
    subgoal for L M N0 D NE0 UE Q W L' M' N0' D' NE0' UE' Q' W'
      apply (refine_vcg
        remove_all_annot_true_clause_imp_wl_remove_all_annot_true_clause_imp[THEN fref_to_Down_curry])
      subgoal unfolding remove_one_annot_true_clause_one_imp_wl_D_pre_def by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal for x x' x1 x2 x1a x2a Ma Maa xa x'a x1b x2b x1c
       x2c x1d x2d x1e x2e
        by (rule res)
      subgoal by auto
      done
    done
qed
definition remove_one_annot_true_clause_imp_wl_D_inv where
  \<open>remove_one_annot_true_clause_imp_wl_D_inv S = (\<lambda>(i, T).
     remove_one_annot_true_clause_imp_wl_inv S (i, T) \<and> literals_are_\<L>\<^sub>i\<^sub>n T)\<close>

definition remove_one_annot_true_clause_imp_wl_D :: \<open>nat twl_st_wl \<Rightarrow> (nat twl_st_wl) nres\<close>
where
\<open>remove_one_annot_true_clause_imp_wl_D = (\<lambda>S. do {
    (_, S) \<leftarrow> WHILE\<^sub>T\<^bsup>remove_one_annot_true_clause_imp_wl_D_inv S\<^esup>
      (\<lambda>(i, S). i < length (get_trail_wl S) \<and> \<not>is_decided (get_trail_wl S!i))
      (\<lambda>(i, S). remove_one_annot_true_clause_one_imp_wl_D i S)
      (0, S);
    RETURN S
  })\<close>


lemma remove_one_annot_true_clause_imp_wl_D_remove_one_annot_true_clause_imp_wl:
  \<open>(remove_one_annot_true_clause_imp_wl_D, remove_one_annot_true_clause_imp_wl) \<in>
   {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S} \<rightarrow>\<^sub>f
     \<langle>{(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S}\<rangle>nres_rel\<close>
proof -
  show ?thesis
    unfolding uncurry_def remove_one_annot_true_clause_imp_wl_D_def
      remove_one_annot_true_clause_imp_wl_def
    apply (intro frefI nres_relI)
    apply (refine_vcg
      WHILEIT_refine[where R=\<open>nat_rel \<times>\<^sub>r {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S}\<close>]
      remove_one_annot_true_clause_one_imp_wl_D_remove_one_annot_true_clause_one_imp_wl[THEN fref_to_Down_curry])
    subgoal by auto
    subgoal for S S' T T'
      by (cases T') (auto simp: remove_one_annot_true_clause_imp_wl_D_inv_def)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

definition mark_to_delete_clauses_wl_D_pre where
  \<open>mark_to_delete_clauses_wl_D_pre S \<longleftrightarrow> mark_to_delete_clauses_wl_pre S \<and> literals_are_\<L>\<^sub>i\<^sub>n S\<close>

definition mark_to_delete_clauses_wl_D_inv where
  \<open>mark_to_delete_clauses_wl_D_inv = (\<lambda>(M, N0, D, NE, UE, Q, W) xs0 (b, i, N, xs).
       mark_to_delete_clauses_wl_inv (M, N0, D, NE, UE, Q, W) xs0 (b, i, N, xs) \<and>
        literals_are_\<L>\<^sub>i\<^sub>n (M, N, D, NE, UE, Q, W))\<close>

definition mark_to_delete_clauses_wl_D :: \<open>nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close> where
\<open>mark_to_delete_clauses_wl_D  = (\<lambda>(M, N, D, NE, UE, Q, W). do {
    ASSERT(mark_to_delete_clauses_wl_D_pre (M, N, D, NE, UE, Q, W));
    xs0 \<leftarrow> collect_valid_indices_wl (M, N, D, NE, UE, Q, W);
    (_, _, N, _) \<leftarrow> WHILE\<^sub>T\<^bsup>mark_to_delete_clauses_wl_D_inv (M, N, D, NE, UE, Q, W) xs0\<^esup>
      (\<lambda>(brk, i, N, xs). \<not>brk \<and> i < length xs)
      (\<lambda>(brk, i, N, xs). do {
        if(xs!i \<notin># dom_m N) then RETURN (brk, i, N, delete_index_and_swap xs i)
        else do {
          ASSERT(0 < length (N\<propto>(xs!i)));
          ASSERT(N\<propto>(xs!i)!0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l);
          can_del \<leftarrow> SPEC(\<lambda>b. b \<longrightarrow> (Propagated (N\<propto>(xs!i)!0) (xs!i) \<notin> set M) \<and> \<not>irred N (xs!i));
          brk \<leftarrow> SPEC(\<lambda>_. True);
          ASSERT(i < length xs);
          if can_del
          then
            RETURN (brk, i+1, fmdrop (xs!i) N, xs)
          else
            RETURN (brk, i+1, N, xs)
        }
      })
      (False, 0, N, xs0);
    RETURN (M, N, D, NE, UE, Q, W)
  })\<close>

lemma (in -) Union_bool_expand: \<open>(\<Union>can_del\<in>{b::bool. P b}. f can_del) =
   ((if P True then f True else {}) \<union> (if P False then f False else {})) \<close>
  apply auto
  apply (case_tac can_del; solves \<open>auto\<close>)
  apply (case_tac can_del; solves \<open>auto\<close>)
  apply (case_tac can_del; solves \<open>auto\<close>)
  apply (case_tac x; solves \<open>auto\<close>)
  done

lemma mark_to_delete_clauses_wl_D_mark_to_delete_clauses_wl:
  \<open>(mark_to_delete_clauses_wl_D, mark_to_delete_clauses_wl) \<in>
   {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S} \<rightarrow>\<^sub>f
     \<langle>{(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S}\<rangle>nres_rel\<close>
proof -
  have [refine0]: \<open>collect_valid_indices_wl S \<le> \<Down> Id (collect_valid_indices_wl T)\<close>
    if \<open>(S, T) \<in> Id\<close> for S T
    using that by auto
  have [iff]: \<open>(\<forall>(x::bool) xa. P x xa) \<longleftrightarrow> (\<forall>xa.( P True xa \<and> P False xa))\<close> for P
    by metis

  have R_notin: \<open>((brk, i, N, delete_index_and_swap xs i), brk', i', N',
       delete_index_and_swap xs' i')
      \<in> {((brk, i, N, xs), brk', i', N', xs').
          brk = brk' \<and>
          i = i' \<and>
          N = N' \<and>
          xs = xs' \<and> mark_to_delete_clauses_wl_D_inv S xs0 (brk, i, N, xs)}\<close>
    if
      T: \<open>T = (SM, SN, SD, SNE, SUE, SQ, SW)\<close> and
      S: \<open>S = (SM, SN, SD, SNE, SUE, SQ, SW)\<close> and
      \<open>literals_are_\<L>\<^sub>i\<^sub>n (SM, SN, SD, SNE, SUE, SQ, SW)\<close> and
      \<open>mark_to_delete_clauses_wl_D_pre (SM, SN, SD, SNE, SUE, SQ, SW)\<close> and
      xs: \<open>(xs0, xs0') \<in> {(N, N'). N = N' \<and> distinct N}\<close> and
      \<open>xs0 \<in> {N. distinct N}\<close> and
      \<open>xs0' \<in> {N. distinct N}\<close> and
      ss': \<open>(s, s') \<in> {((brk, i, N, xs), brk', i', N', xs'). brk = brk' \<and> i = i' \<and> N = N' \<and>
         xs = xs' \<and> mark_to_delete_clauses_wl_D_inv S xs0 (brk, i, N, xs)}\<close> and
      \<open>case s of (brk, i, N, xs) \<Rightarrow> \<not> brk \<and> i < length xs\<close> and
      \<open>case s' of (brk, i, N, xs) \<Rightarrow> \<not> brk \<and> i < length xs\<close> and
      inv: \<open>mark_to_delete_clauses_wl_D_inv (SM, SN, SD, SNE, SUE, SQ, SW) xs0 s\<close> and
      \<open>mark_to_delete_clauses_wl_inv (SM, SN, SD, SNE, SUE, SQ, SW) xs0' s'\<close> and
      post_inv: \<open>(case s' of (brk, i, N, xs) \<Rightarrow>
        if xs ! i \<notin># dom_m N
        then RETURN (brk, i, N, delete_index_and_swap xs i)
        else ASSERT (0 < length (N \<propto> (xs ! i))) \<bind>
            (\<lambda>_. SPEC (\<lambda>b. b \<longrightarrow> Propagated (N \<propto> (xs ! i) ! 0) (xs ! i) \<notin> set SM \<and>
                   \<not> irred N (xs ! i)) \<bind>
             (\<lambda>can_del. SPEC (\<lambda>_. True) \<bind>
                 (\<lambda>brk. ASSERT (i < length xs) \<bind>
                        (\<lambda>_. if can_del
                             then RETURN (brk, i + 1, fmdrop (xs ! i) N, xs)
                             else RETURN (brk, i + 1, N, xs))))))
     \<le> SPEC (mark_to_delete_clauses_wl_inv (SM, SN, SD, SNE, SUE, SQ, SW)
               xs0')\<close> and
      st:
        \<open>si' = (N', xs')\<close>
        \<open>sbrk' = (i', si')\<close>
        \<open>s' = (brk', sbrk')\<close>
        \<open>si = (N, xs)\<close>
        \<open>sbrk = (i, si)\<close>
        \<open>s = (brk, sbrk)\<close> and
      [simp]: \<open>xs ! i \<notin># dom_m N\<close> \<open>xs' ! i' \<notin># dom_m N'\<close>
    for s s' brk' sbrk' i' si' N' xs' brk sbrk i si N xs
      TM TN TD TNE TUE TQ TW SM SN SD SNE SUE SQ SW xs0 xs0' S T
  proof -
    have st:
      \<open>si' = (N', xs')\<close>
      \<open>sbrk' = (i', N', xs')\<close>
      \<open>s' = (brk', i', N', xs')\<close>
      \<open>si = (N', xs')\<close>
      \<open>sbrk = (i', N', xs')\<close>
      \<open>s = (brk, i', N', xs')\<close>
      \<open>i = i'\<close>
      \<open>N = N'\<close>
      \<open>xs = xs'\<close>
      \<open>brk =brk'\<close> and
      \<open>mark_to_delete_clauses_wl_D_inv S xs0 (brk, i', N', xs')\<close>
      using st ss' by auto
    have post: \<open>mark_to_delete_clauses_wl_inv (SM, SN, SD, SNE, SUE, SQ, SW) xs0'
     (brk', i', N', butlast (xs'[i' := last xs']))\<close>
      using post_inv unfolding st
      by auto
    then have \<open>mark_to_delete_clauses_wl_D_inv S xs0 (brk', i', N', butlast (xs'[i' := last xs']))\<close>
      using inv xs unfolding mark_to_delete_clauses_wl_D_inv_def prod.case S st
      by auto
    then show ?thesis
      by (auto simp: st)
  qed
  have Lit_inL: \<open>N \<propto> (xs ! i) ! 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    if
      T: \<open>T = (SM, SN, SD, SNE, SUE, SQ, SW)\<close> and
      S: \<open>S = (SM, SN, SD, SNE, SUE, SQ, SW)\<close> and
      ss': \<open>(s, s') \<in> {((brk, i, N, xs), brk', i', N', xs'). brk = brk' \<and> i = i' \<and>
         N = N' \<and> xs = xs' \<and> mark_to_delete_clauses_wl_D_inv S xs0 (brk, i, N, xs)}\<close> and
      st:
        \<open>si' = (N', xs')\<close>
        \<open>sbrk' = (i', si')\<close>
        \<open>s' = (brk', sbrk')\<close>
        \<open>si = (N, xs)\<close>
        \<open>sbrk = (i, si)\<close>
        \<open>s = (brk, sbrk)\<close> and
      dom: \<open>\<not> xs ! i \<notin># dom_m N\<close> and
      \<open>\<not> xs' ! i' \<notin># dom_m N'\<close> and
    le: \<open>0 < length (N \<propto> (xs ! i))\<close>
    for s s' brk' sbrk' i' si' N' xs' brk sbrk i si N xs
      TM TN TD TNE TUE TQ TW SM SN SD SNE SUE SQ SW xs0 xs0' S T
  proof -
    have st:
      \<open>si' = (N', xs')\<close>
      \<open>sbrk' = (i', N', xs')\<close>
      \<open>s' = (brk', i', N', xs')\<close>
      \<open>si = (N', xs')\<close>
      \<open>sbrk = (i', N', xs')\<close>
      \<open>s = (brk, i', N', xs')\<close>
      \<open>i = i'\<close>
      \<open>N = N'\<close>
      \<open>xs = xs'\<close>
      \<open>brk =brk'\<close> and
      inv_x: \<open>mark_to_delete_clauses_wl_D_inv S xs0 (brk, i', N', xs')\<close>
      using st ss' by auto
    have \<open>literals_are_\<L>\<^sub>i\<^sub>n  (SM, N', SD, SNE, SUE, SQ, SW)\<close>
      using inv_x unfolding mark_to_delete_clauses_wl_D_inv_def prod.case S
      by fast
    then have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N \<propto> (xs ! i)))\<close>
      using literals_are_in_\<L>\<^sub>i\<^sub>n_nth[of \<open>xs!i\<close> \<open>(SM, N', SD, SNE, SUE, SQ, SW)\<close>] dom
      by (auto simp: st)
    then show ?thesis
      by (rule literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l) (use le in auto)
  qed
  have H: \<open>SPEC (\<lambda>N. distinct N)
       \<le> \<Down> {(N, N'). N=N' \<and> distinct N}
           (SPEC (\<lambda>N. distinct N))\<close>
    by (auto intro!: RES_refine)
  have removed: \<open>((break1, i + 1, fmdrop (xs ! i) N, xs), break1', i' + 1,
       fmdrop (xs' ! i') N', xs')
      \<in> {((brk, i, N, xs), brk', i', N', xs').
          brk = brk' \<and>
          i = i' \<and>
          N = N' \<and>
          xs = xs' \<and> mark_to_delete_clauses_wl_D_inv S xs0 (brk, i, N, xs)}\<close>
    if
      \<open>T = (SM, SN, SD, SNE, SUE, SQ, SW)\<close> and
      S: \<open>S = (SM, SN, SD, SNE, SUE, SQ, SW)\<close> and
      \<open>literals_are_\<L>\<^sub>i\<^sub>n (SM, SN, SD, SNE, SUE, SQ, SW)\<close> and
      pre: \<open>mark_to_delete_clauses_wl_D_pre (SM, SN, SD, SNE, SUE, SQ, SW)\<close> and
      xs0_xs0': \<open>(xs0, xs0') \<in> {(N, N'). N = N' \<and> distinct N}\<close> and
      \<open>xs0 \<in> {N. distinct N}\<close> and
      \<open>xs0' \<in> {N. distinct N}\<close> and
      ss': \<open>(s, s') \<in> {((brk, i, N, xs), brk', i', N', xs'). brk = brk' \<and> i = i' \<and> N = N' \<and>
         xs = xs' \<and> mark_to_delete_clauses_wl_D_inv S xs0 (brk, i, N, xs)}\<close> and
      \<open>case s of (brk, i, N, xs) \<Rightarrow> \<not> brk \<and> i < length xs\<close> and
      \<open>case s' of (brk, i, N, xs) \<Rightarrow> \<not> brk \<and> i < length xs\<close> and
      inv: \<open>mark_to_delete_clauses_wl_D_inv (SM, SN, SD, SNE, SUE, SQ, SW) xs0 s\<close> and
      \<open>mark_to_delete_clauses_wl_inv (SM, SN, SD, SNE, SUE, SQ, SW) xs0' s'\<close> and
      post: \<open>(case s' of
      (brk, i, N, xs) \<Rightarrow>
        if xs ! i \<notin># dom_m N
        then RETURN (brk, i, N, delete_index_and_swap xs i)
        else ASSERT (0 < length (N \<propto> (xs ! i))) \<bind>
             (\<lambda>_. SPEC
                   (\<lambda>b. b \<longrightarrow>
                        Propagated (N \<propto> (xs ! i) ! 0) (xs ! i) \<notin> set SM \<and>
                        \<not> irred N (xs ! i)) \<bind>
                  (\<lambda>can_del.
                      SPEC (\<lambda>_. True) \<bind>
                      (\<lambda>brk. ASSERT (i < length xs) \<bind>
                             (\<lambda>_. if can_del
                                  then RETURN
 (brk, i + 1, fmdrop (xs ! i) N, xs)
                                  else RETURN (brk, i + 1, N, xs))))))
     \<le> SPEC (mark_to_delete_clauses_wl_inv (SM, SN, SD, SNE, SUE, SQ, SW)
               xs0')\<close> and
      s:
        \<open>si' = (N', xs')\<close>
        \<open>sbrk' = (i', si')\<close>
        \<open>s' = (brk', sbrk')\<close>
        \<open>si = (N, xs)\<close>
        \<open>sbrk = (i, si)\<close>
        \<open>s = (brk, sbrk)\<close> and
      dom: \<open>\<not> xs ! i \<notin># dom_m N\<close> and
      \<open>\<not> xs' ! i' \<notin># dom_m N'\<close> and
      length: \<open>0 < length (N' \<propto> (xs' ! i'))\<close> and
      \<open>0 < length (N \<propto> (xs ! i))\<close> and
      \<open>N \<propto> (xs ! i) ! 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and
      can_del: \<open>can_del \<in> {b. b \<longrightarrow>
            Propagated (N \<propto> (xs ! i) ! 0) (xs ! i) \<notin> set SM \<and>
            \<not> irred N (xs ! i)}\<close> and
      can_del': \<open>can_del' \<in> {b. b \<longrightarrow>
            Propagated (N' \<propto> (xs' ! i') ! 0) (xs' ! i') \<notin> set SM \<and>
            \<not> irred N' (xs' ! i')}\<close> and
      s':
        \<open>(break1, break1') \<in> bool_rel\<close>
        \<open>(can_del, can_del') \<in> bool_rel\<close> and
      \<open>break1 \<in> {_. True}\<close> and
      \<open>break1' \<in> {_. True}\<close> and
      i'_le: \<open>i' < length xs'\<close> and
      \<open>i < length xs\<close> and
      [simp]: \<open>can_del\<close> and
      \<open>can_del'\<close>
    for s s' brk' sbrk' i' si' N' xs' brk sbrk i si N xs can_del can_del' break1 break1'
      TM TN TD TNE TUE TQ TW SM SN SD SNE SUE SQ SW xs0 xs0' S T
  proof -
    have st:
      \<open>si' = (N', xs')\<close>
      \<open>sbrk' = (i', N', xs')\<close>
      \<open>s' = (brk', i', N', xs')\<close>
      \<open>si = (N, xs)\<close>
      \<open>sbrk = (i, N, xs)\<close>
      \<open>s = (brk, i, N, xs)\<close>
      \<open>xs0 = xs0'\<close>
      \<open>break1 = break1'\<close>
      \<open>can_del = can_del'\<close>
      \<open>i = i'\<close>
      \<open>N = N'\<close>
      \<open>xs = xs'\<close> and
      [simp]: \<open>can_del'\<close>
      using s s' xs0_xs0' ss'
      by auto
    have 1: \<open>(if can_del then RETURN (brk, i' + 1, fmdrop (xs' ! i') N', xs')
               else RETURN (brk, i' + 1, N', xs')) =
       RETURN (if can_del then (brk, i' + 1, fmdrop (xs' ! i') N', xs')
               else (brk, i' + 1, N', xs'))\<close> for can_del brk
      by auto
    have \<open>\<not>irred N' (xs' ! i') \<Longrightarrow> \<not>Propagated (N' \<propto> (xs' ! i') ! 0) (xs' ! i') \<in> set SM \<Longrightarrow>
        \<forall>x\<in>range (\<lambda>brk. (brk, Suc i', fmdrop (xs' ! i') N', xs')) \<union>
        range (\<lambda>brk. (brk, Suc i', N', xs')).
       mark_to_delete_clauses_wl_inv (SM, SN, SD, SNE, SUE, SQ, SW) xs0' x\<close> and
      \<open>mark_to_delete_clauses_wl_inv (SM, SN, SD, SNE, SUE, SQ, SW) xs0'
            (break1, Suc i', N', xs')\<close>
      using post dom length i'_le can_del
      by (auto simp: st 1 RES_RETURN_RES RES_RES_RETURN_RES Union_bool_expand subset_Collect_conv
          split: if_splits)
    then have st': \<open>mark_to_delete_clauses_wl_inv (SM, SN, SD, SNE, SUE, SQ, SW) xs0'
       (break1', Suc i', fmdrop (xs' ! i') N', xs')\<close>
      using dom length i'_le can_del'
      by (auto simp: st 1 RES_RETURN_RES RES_RES_RETURN_RES Union_bool_expand subset_Collect_conv
          split: if_splits)
    then obtain a aa ab ac ad ae b af ba c d e f g U' where
      SU: \<open>((SM, SN, SD, SNE, SUE, SQ, SW), af, ba, c, d, e, f, g) \<in> state_wl_l None\<close> and
        \<open>partial_correct_watching (SM, SN, SD, SNE, SUE, SQ, SW)\<close> and
      rem: \<open>remove_one_annot_true_clause\<^sup>*\<^sup>* (af, ba, c, d, e, f, g)
          (af, fmdrop (xs' ! i') N', c, d, e, f, g)\<close> and
       \<open>filter_mset (\<lambda>i. i \<in># dom_m (fmdrop (xs' ! i') N')) (mset xs') =
             filter_mset (\<lambda>i. i \<in># dom_m (fmdrop (xs' ! i') N')) (mset xs0')\<close> and
        \<open>distinct xs'\<close> and
      list_invs_U: \<open>twl_list_invs (af, ba, c, d, e, f, g)\<close> and
      confl: \<open>get_conflict_l (af, ba, c, d, e, f, g) = None\<close> and
      upd: \<open>clauses_to_update_l (af, ba, c, d, e, f, g) = {#}\<close> and
      UU': \<open>((af, ba, c, d, e, f, g), U') \<in> twl_st_l None\<close> and
      struct_U': \<open>twl_struct_invs U'\<close>
      unfolding mark_to_delete_clauses_wl_inv_def prod.case mark_to_delete_clauses_l_inv_def
      apply -
      apply normalize_goal+
      apply (case_tac x)
      apply clarify
      by blast
    obtain V where
     \<open>cdcl_twl_restart_l\<^sup>*\<^sup>* (af, ba, c, d, e, f, g)
        (af, fmdrop (xs' ! i') N', c, d, e, f, g)\<close> and
     UV: \<open>((af, fmdrop (xs' ! i') N', c, d, e, f, g), V)
       \<in> twl_st_l None\<close> and
     U'V: \<open>cdcl_twl_restart\<^sup>*\<^sup>* U' V\<close> and
     \<open>twl_struct_invs V\<close>
      using rtranclp_remove_one_annot_true_clause_cdcl_twl_restart_l2[OF rem list_invs_U confl upd
          UU' struct_U']
      by blast
    have lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n (SM, SN, SD, SNE, SUE, SQ, SW)\<close>
      using inv pre unfolding mark_to_delete_clauses_wl_D_pre_def prod.case s by fast+
    have SV: \<open>((SM, fmdrop (xs' ! i') N', SD, SNE, SUE, SQ, SW), af, fmdrop (xs' ! i') N', c, d, e, f, g) \<in> state_wl_l None\<close>
      using SU by (auto simp: state_wl_l_def)
    have \<open>literals_are_\<L>\<^sub>i\<^sub>n (SM, fmdrop (xs' ! i') N', SD, SNE, SUE, SQ, SW)\<close>
      using cdcl_twl_restart_is_\<L>\<^sub>a\<^sub>l\<^sub>l[OF U'V struct_U' ] lits SU UU' UV SV
      by (auto simp del: get_clauses.simps get_clauses_wl.simps get_clauses_l.simps
          unit_clss.simps get_unit_clauses_l.simps get_unit_clauses_wl.simps
          simp: mset_take_mset_drop_mset')
    then have \<open>mark_to_delete_clauses_wl_D_inv S xs0' (break1', Suc i', fmdrop (xs' ! i') N', xs')\<close>
      using st' unfolding mark_to_delete_clauses_wl_D_inv_def S prod.case
      by auto
    then show ?thesis
      by (auto simp: st)
  qed
  have kept: \<open>((break1, i + 1, N, xs), break1', i' + 1, N', xs')
      \<in> {((brk, i, N, xs), brk', i', N', xs').
          brk = brk' \<and>
          i = i' \<and>
          N = N' \<and>
          xs = xs' \<and>
          mark_to_delete_clauses_wl_D_inv S xs0
           (brk, i, N, xs)}\<close>
    if
      T: \<open>T = (SM, SN, SD, SNE, SUE, SQ, SW)\<close> and
      S: \<open>S = (SM, SN, SD, SNE, SUE, SQ, SW)\<close> and
      \<open>literals_are_\<L>\<^sub>i\<^sub>n (SM, SN, SD, SNE, SUE, SQ, SW)\<close> and
      \<open>mark_to_delete_clauses_wl_pre (SM, SN, SD, SNE, SUE, SQ, SW)\<close> and
      pre: \<open>mark_to_delete_clauses_wl_D_pre (SM, SN, SD, SNE, SUE, SQ, SW)\<close> and
      xs0_xs0': \<open>(xs0, xs0') \<in> {(N, N'). N = N' \<and> distinct N}\<close> and
      \<open>xs0 \<in> {N. distinct N}\<close> and
      \<open>xs0' \<in> {N. distinct N}\<close> and
      ss': \<open>(s, s') \<in> {((brk, i, N, xs), brk', i', N', xs'). brk = brk' \<and> i = i' \<and>
         N = N' \<and> xs = xs' \<and> mark_to_delete_clauses_wl_D_inv S xs0 (brk, i, N, xs)}\<close> and
      \<open>case s of (brk, i, N, xs) \<Rightarrow> \<not> brk \<and> i < length xs\<close> and
      \<open>case s' of (brk, i, N, xs) \<Rightarrow> \<not> brk \<and> i < length xs\<close> and
      \<open>mark_to_delete_clauses_wl_D_inv (SM, SN, SD, SNE, SUE, SQ, SW) xs0 s\<close> and
      \<open>mark_to_delete_clauses_wl_inv (SM, SN, SD, SNE, SUE, SQ, SW) xs0' s'\<close> and
      post: \<open>(case s' of (brk, i, N, xs) \<Rightarrow> if xs ! i \<notin># dom_m N
        then RETURN (brk, i, N, delete_index_and_swap xs i)
        else ASSERT (0 < length (N \<propto> (xs ! i))) \<bind>
             (\<lambda>_. SPEC
                   (\<lambda>b. b \<longrightarrow>
                        Propagated (N \<propto> (xs ! i) ! 0)
                         (xs ! i)
                        \<notin> set SM \<and>
                        \<not> irred N (xs ! i)) \<bind>
                  (\<lambda>can_del.
                      SPEC (\<lambda>_. True) \<bind>
                      (\<lambda>brk. ASSERT (i < length xs) \<bind>
                             (\<lambda>_.
  if can_del then RETURN (brk, i + 1, fmdrop (xs ! i) N, xs)
  else RETURN (brk, i + 1, N, xs))))))
     \<le> SPEC
         (mark_to_delete_clauses_wl_inv
           (SM, SN, SD, SNE, SUE, SQ, SW) xs0')\<close> and
      s:
        \<open>si' = (N', xs')\<close>
        \<open>sbrk' = (i', si')\<close>
        \<open>s' = (brk', sbrk')\<close>
        \<open>si = (N, xs)\<close>
        \<open>sbrk = (i, si)\<close>
        \<open>s = (brk, sbrk)\<close> and
      dom: \<open>\<not> xs ! i \<notin># dom_m N\<close> and
      \<open>\<not> xs' ! i' \<notin># dom_m N'\<close> and
      length: \<open>0 < length (N' \<propto> (xs' ! i'))\<close> and
      \<open>0 < length (N \<propto> (xs ! i))\<close> and
      \<open>N \<propto> (xs ! i) ! 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and
      \<open>can_del
     \<in> {b. b \<longrightarrow>
            Propagated (N \<propto> (xs ! i) ! 0) (xs ! i) \<notin> set SM \<and>
            \<not> irred N (xs ! i)}\<close> and
      \<open>can_del' \<in> {b. b \<longrightarrow>
            Propagated (N' \<propto> (xs' ! i') ! 0) (xs' ! i')
            \<notin> set SM \<and>
            \<not> irred N' (xs' ! i')}\<close> and
      s':
        \<open>(break1, break1') \<in> bool_rel\<close>
        \<open>(can_del, can_del') \<in> bool_rel\<close> and
      \<open>break1 \<in> {_. True}\<close> and
      \<open>break1' \<in> {_. True}\<close> and
      i'_le: \<open>i' < length xs'\<close> and
      \<open>i < length xs\<close> and
      can_del: \<open>\<not> can_del\<close> and
      \<open>\<not> can_del'\<close>
    for s s' brk' sbrk' i' si' N' xs' brk sbrk i si N xs can_del can_del' break1 break1'
      TM TN TD TNE TUE TQ TW SM SN SD SNE SUE SQ SW xs0 xs0' S T
  proof -
    have st:
      \<open>si' = (N', xs')\<close>
      \<open>sbrk' = (i', N', xs')\<close>
      \<open>s' = (brk', i', N', xs')\<close>
      \<open>si = (N, xs)\<close>
      \<open>sbrk = (i, N, xs)\<close>
      \<open>s = (brk, i, N, xs)\<close>
      \<open>xs0 = xs0'\<close>
      \<open>break1 = break1'\<close>
      \<open>can_del = can_del'\<close>
      \<open>i = i'\<close>
      \<open>N = N'\<close>
      \<open>xs = xs'\<close> and
      [simp]: \<open>can_del' = False\<close>
      using s s' xs0_xs0' ss' can_del
      by auto
    have 1: \<open>(if can_del then RETURN (brk, i' + 1, fmdrop (xs' ! i') N', xs')
               else RETURN (brk, i' + 1, N', xs')) =
       RETURN (if can_del then (brk, i' + 1, fmdrop (xs' ! i') N', xs')
               else (brk, i' + 1, N', xs'))\<close> for can_del brk
      by auto
    have \<open>\<not>irred N' (xs' ! i') \<Longrightarrow> \<not>Propagated (N' \<propto> (xs' ! i') ! 0) (xs' ! i') \<in> set SM \<Longrightarrow>
        \<forall>x\<in>range (\<lambda>brk. (brk, Suc i', fmdrop (xs' ! i') N', xs')) \<union>
        range (\<lambda>brk. (brk, Suc i', N', xs')).
       mark_to_delete_clauses_wl_inv (SM, SN, SD, SNE, SUE, SQ, SW) xs0' x\<close> and
      \<open>mark_to_delete_clauses_wl_inv (SM, SN, SD, SNE, SUE, SQ, SW) xs0'
            (break1, Suc i', N', xs')\<close>
      using post dom length i'_le can_del
      by (auto simp: st 1 RES_RETURN_RES RES_RES_RETURN_RES Union_bool_expand subset_Collect_conv
          split: if_splits)
    then have st': \<open>mark_to_delete_clauses_wl_inv (SM, SN, SD, SNE, SUE, SQ, SW) xs0'
       (break1', Suc i', N', xs')\<close>
      using dom length i'_le
      by (auto simp: st 1 RES_RETURN_RES RES_RES_RETURN_RES Union_bool_expand subset_Collect_conv
          split: if_splits)
    then obtain a aa ab ac ad ae b af ba c d e f g U' where
    \<open>distinct xs'\<close> and
      SU: \<open>((SM, SN, SD, SNE, SUE, SQ, SW), af, ba, c, d, e, f, g) \<in> state_wl_l None\<close> and
      \<open>partial_correct_watching (SM, SN, SD, SNE, SUE, SQ, SW)\<close> and
      rem: \<open>remove_one_annot_true_clause\<^sup>*\<^sup>* (af, ba, c, d, e, f, g)
          (af, N', c, d, e, f, g)\<close> and
      \<open>filter_mset (\<lambda>i. i \<in># dom_m N') (mset xs') =
             filter_mset (\<lambda>i. i \<in># dom_m N') (mset xs0')\<close> and
      \<open>distinct xs'\<close> and
      list_invs_U: \<open>twl_list_invs (af, ba, c, d, e, f, g)\<close> and
      confl: \<open>get_conflict_l (af, ba, c, d, e, f, g) = None\<close> and
      upd: \<open>clauses_to_update_l (af, ba, c, d, e, f, g) = {#}\<close> and
      UU': \<open>((af, ba, c, d, e, f, g), U') \<in> twl_st_l None\<close> and
      struct_U': \<open>twl_struct_invs U'\<close>
      unfolding mark_to_delete_clauses_wl_inv_def prod.case mark_to_delete_clauses_l_inv_def
      apply -
      apply normalize_goal+
      apply (case_tac x)
      apply clarify
      by blast
    obtain V where
      \<open>cdcl_twl_restart_l\<^sup>*\<^sup>* (af, ba, c, d, e, f, g) (af, N', c, d, e, f, g)\<close> and
      UV: \<open>((af, N', c, d, e, f, g), V) \<in> twl_st_l None\<close> and
      U'V: \<open>cdcl_twl_restart\<^sup>*\<^sup>* U' V\<close> and
      \<open>twl_struct_invs V\<close>
      using rtranclp_remove_one_annot_true_clause_cdcl_twl_restart_l2[OF rem list_invs_U confl upd
          UU' struct_U']
      by blast
    have lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n (SM, SN, SD, SNE, SUE, SQ, SW)\<close>
      using pre unfolding mark_to_delete_clauses_wl_D_pre_def prod.case s by fast+
    have SV: \<open>((SM, N', SD, SNE, SUE, SQ, SW), af, N', c, d, e, f, g) \<in> state_wl_l None\<close>
      using SU by (auto simp: state_wl_l_def)
    have \<open>literals_are_\<L>\<^sub>i\<^sub>n (SM, N', SD, SNE, SUE, SQ, SW)\<close>
      using cdcl_twl_restart_is_\<L>\<^sub>a\<^sub>l\<^sub>l[OF U'V struct_U' ] lits SU UU' UV SV
      by (auto simp del: get_clauses.simps get_clauses_wl.simps get_clauses_l.simps
          unit_clss.simps get_unit_clauses_l.simps get_unit_clauses_wl.simps
          simp: mset_take_mset_drop_mset')
    then have \<open>mark_to_delete_clauses_wl_D_inv S xs0' (break1', Suc i', N', xs')\<close>
      using st' unfolding mark_to_delete_clauses_wl_D_inv_def S prod.case
      by auto
    then show ?thesis
      by (auto simp: st)
  qed
  have refine_ASSERT:
    \<open>(\<Phi> \<Longrightarrow> \<Psi>) \<Longrightarrow> (\<Phi> \<Longrightarrow> \<Psi> \<Longrightarrow> P \<le> \<Down> R Q) \<Longrightarrow>
         do {ASSERT \<Psi>; P} \<le> \<Down> R (do {ASSERT \<Phi>; Q})\<close> for P Q \<Phi> \<Psi> R
    by refine_vcg auto
  show ?thesis
    unfolding uncurry_def mark_to_delete_clauses_wl_D_def mark_to_delete_clauses_wl_def
      collect_valid_indices_wl_def
    apply (intro frefI nres_relI)
    subgoal for S T
      apply (cases S; cases T)
      apply (clarify)
      apply (rule refine_ASSERT)
      subgoal unfolding mark_to_delete_clauses_wl_D_pre_def by auto
      apply (rule bind_refine_RES(3)[OF H])
      subgoal for TM TN TD TNE TUE TQ TW SM SN SD SNE SUE SQ SW xs0 xs0'
        apply (refine_vcg
            remove_one_annot_true_clause_imp_wl_D_remove_one_annot_true_clause_imp_wl[THEN fref_to_Down]
            remove_one_annot_true_clause_one_imp_wl_D_remove_one_annot_true_clause_one_imp_wl[THEN fref_to_Down_curry]
            WHILEIT_refine_with_post[where R = \<open>{((brk, i, N, xs), (brk', i', N', xs')). brk = brk' \<and>
              i=i' \<and> N=N' \<and> xs = xs' \<and>
              mark_to_delete_clauses_wl_D_inv S xs0 (brk, i, N, xs)}\<close>])
        subgoal unfolding mark_to_delete_clauses_wl_D_inv_def by auto
        subgoal unfolding mark_to_delete_clauses_wl_D_inv_def by auto
        subgoal by auto
        subgoal by auto
        subgoal by (rule R_notin)
        subgoal by auto
        subgoal by (rule Lit_inL)
        subgoal by auto
        subgoal by auto
        subgoal by auto
        subgoal by auto
        subgoal by (rule removed)
        subgoal by (rule kept)
        subgoal unfolding mark_to_delete_clauses_wl_D_inv_def by auto
        done
      done
    done
qed


definition rewatch_clause_D
  :: \<open>nat clauses_l \<Rightarrow> nat \<Rightarrow> (nat literal \<Rightarrow> watched) \<Rightarrow> (nat literal \<Rightarrow> watched) nres\<close>
where
  \<open>rewatch_clause_D N C W = do {
    ASSERT(length (N \<propto> C) > 1);
    let L = N \<propto> C ! 0;
    let L' = N \<propto> C ! 1;
    ASSERT(L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l);
    ASSERT(L' \<in># \<L>\<^sub>a\<^sub>l\<^sub>l);
    RETURN (W(L := W L @ [C], L' := W L' @ [C]))
  }\<close>

lemma rewatch_clause_D_rewatch_clause:
  \<open>(uncurry2 rewatch_clause_D, uncurry2 rewatch_clause) \<in>
     [\<lambda>((N, C), W). literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N \<propto> C))]\<^sub>f Id \<times>\<^sub>f Id  \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  unfolding uncurry_def rewatch_clause_D_def rewatch_clause_def
  apply (intro frefI nres_relI)
  apply (refine_rcg)
  subgoal by auto
  subgoal by (auto intro: literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l)
  subgoal by (auto intro: literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l)
  subgoal by auto
  done

definition rewatch_clauses_prog_D_pre :: \<open>nat twl_st_wl \<Rightarrow> bool\<close>  where
  \<open>rewatch_clauses_prog_D_pre S \<longleftrightarrow>
     (rewatch_clauses_prog_pre S \<and> literals_are_\<L>\<^sub>i\<^sub>n S)\<close>

definition rewatch_clauses_prog_D :: \<open>nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close> where
\<open>rewatch_clauses_prog_D = (\<lambda>(M, N, D, NE, UE, Q, W0). do {
  ASSERT(rewatch_clauses_prog_D_pre (M, N, D, NE, UE, Q, W0));
  let W0 = empty_WL W0;
  xs \<leftarrow> SPEC(\<lambda>xs. dom_m N \<subseteq># mset xs \<and> distinct xs);
  (_, W) \<leftarrow> WHILE\<^sub>T\<^bsup>rewatch_clauses_prog_inv (M, N, D, NE, UE, Q, W0) xs\<^esup>
    (\<lambda>(i, W). i < length xs)
    (\<lambda>(i, W). do {
      ASSERT(i < length xs);
      if xs!i \<in># dom_m N then do {
        W \<leftarrow> rewatch_clause_D N (xs!i) W;
        RETURN(i+1, W)
      } else  RETURN(i+1, W)
    })
    (0, W0);
  RETURN (M, N, D, NE, UE, Q, W)
})\<close>


lemma rewatch_clauses_prog_D_rewatch_clauses_prog:
  \<open>(rewatch_clauses_prog_D, rewatch_clauses_prog) \<in>
   {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S} \<rightarrow>\<^sub>f
     \<langle>{(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S}\<rangle>nres_rel\<close>
proof -
  show ?thesis
    unfolding rewatch_clauses_prog_D_def rewatch_clauses_prog_def
    apply (intro frefI nres_relI)
    apply (refine_rcg
     rewatch_clause_D_rewatch_clause[THEN fref_to_Down_curry2]
      WHILEIT_refine[where R = \<open>nat_rel \<times>\<^sub>f (Id :: ((nat literal \<Rightarrow> watched) \<times> _) set) \<close>])
    subgoal unfolding rewatch_clauses_prog_D_pre_def by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal unfolding rewatch_clauses_prog_D_pre_def
      by (auto dest!: literals_are_in_\<L>\<^sub>i\<^sub>n_nth[of _ \<open>(M, N, D, NE, UE, Q, W0)\<close> for M N D NE UE Q W0,
            simplified])
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed


definition mark_to_delete_clauses_wl_D_post where
  \<open>mark_to_delete_clauses_wl_D_post S T \<longleftrightarrow>
     (mark_to_delete_clauses_wl_post S T \<and> literals_are_\<L>\<^sub>i\<^sub>n S)\<close>

definition cdcl_twl_restart_wl_prog_D :: \<open>nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close> where
\<open>cdcl_twl_restart_wl_prog_D S = do {
    S \<leftarrow> remove_one_annot_true_clause_imp_wl_D S;
    ASSERT(mark_to_delete_clauses_wl_D_pre S);
    T \<leftarrow> mark_to_delete_clauses_wl_D S;
    rewatch_clauses_prog_D T
  }\<close>

lemma cdcl_twl_restart_wl_prog_D_cdcl_twl_restart_wl_prog:
  \<open>(cdcl_twl_restart_wl_prog_D, cdcl_twl_restart_wl_prog) \<in>
   {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S} \<rightarrow>\<^sub>f
     \<langle>{(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S}\<rangle>nres_rel\<close>
proof -
  have [refine0]: \<open>rewatch_clauses_prog_D U \<le> \<Down> {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S}
          (rewatch_clauses U')\<close>
    if
      UU': \<open>(U, U') \<in> {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S}\<close> and
      post: \<open>mark_to_delete_clauses_wl_post T' U'\<close>
    for S S' T T' U U'
  proof -
    have le: \<open>rewatch_clauses_prog_D U \<le> \<Down> {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S}
            (rewatch_clauses_prog U')\<close>
      using rewatch_clauses_prog_D_rewatch_clauses_prog[THEN fref_to_Down, of U U']
        UU' by auto
    obtain x xa xb where
      \<open>(T', x) \<in> state_wl_l None\<close> and
      U'_xa: \<open>(U', xa) \<in> state_wl_l None\<close> and
      xxb: \<open>(x, xb) \<in> twl_st_l None\<close> and
      rem: \<open>remove_one_annot_true_clause\<^sup>*\<^sup>* x xa\<close> and
      list_invs: \<open>twl_list_invs x\<close> and
      struct_xb: \<open>twl_struct_invs xb\<close> and
      part_T': \<open>partial_correct_watching T'\<close> and
      confl: \<open>get_conflict_l x = None\<close> and
      upd: \<open>clauses_to_update_l x = {#}\<close> and
      \<open>partial_correct_watching T'\<close> and
      part_U': \<open>partial_correct_watching U'\<close>
      using post unfolding mark_to_delete_clauses_wl_post_def mark_to_delete_clauses_l_post_def
      by blast
    obtain xc where
      xa_xc: \<open>(xa, xc) \<in> twl_st_l None\<close> and
      struct_xc: \<open>twl_struct_invs xc\<close> and
      x_xa: \<open>cdcl_twl_restart_l\<^sup>*\<^sup>* x xa\<close> and
      \<open>cdcl_twl_restart\<^sup>*\<^sup>* xb xc\<close>
      using rtranclp_remove_one_annot_true_clause_cdcl_twl_restart_l2[OF rem list_invs confl upd
          xxb struct_xb]
      by blast
    have list_xa: \<open>twl_list_invs xa\<close>
      using rtranclp_cdcl_twl_restart_l_list_invs[OF x_xa list_invs] .
    have \<open>rewatch_clauses_prog U' \<le> rewatch_clauses U'\<close>
      using rewatch_clauses_prog_rewatch_clauses[of U', OF U'_xa xa_xc struct_xc list_xa part_U'] .
    then show ?thesis
      using ref_two_step[OF le] by blast
  qed
  show ?thesis
    unfolding uncurry_def cdcl_twl_restart_wl_prog_D_def cdcl_twl_restart_wl_prog_def
    apply (intro frefI nres_relI)
    apply (refine_vcg
      remove_one_annot_true_clause_imp_wl_D_remove_one_annot_true_clause_imp_wl[THEN fref_to_Down]
      remove_one_annot_true_clause_one_imp_wl_D_remove_one_annot_true_clause_one_imp_wl[THEN fref_to_Down_curry]
      mark_to_delete_clauses_wl_D_mark_to_delete_clauses_wl[THEN fref_to_Down])
    subgoal for S T U V
      unfolding mark_to_delete_clauses_wl_D_pre_def by blast
    apply assumption
    done
qed


definition restart_abs_wl_D_pre :: \<open>nat twl_st_wl \<Rightarrow> bool \<Rightarrow> bool\<close> where
  \<open>restart_abs_wl_D_pre S brk \<longleftrightarrow>
    (restart_abs_wl_pre S brk \<and> literals_are_\<L>\<^sub>i\<^sub>n S)\<close>

definition restart_prog_wl_D :: "nat twl_st_wl \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> (nat twl_st_wl \<times> nat) nres" where
  \<open>restart_prog_wl_D S n brk = do {
     ASSERT(restart_abs_wl_D_pre S brk);
     b \<leftarrow> restart_required_wl S n;
     if b \<and> \<not>brk then do {
       T \<leftarrow> cdcl_twl_restart_wl_prog_D S;
       RETURN (T, n + 1)
     }
     else
       RETURN (S, n)
   }\<close>

lemma restart_prog_wl_D_restart_prog_wl:
  \<open>(uncurry2 restart_prog_wl_D, uncurry2 restart_prog_wl) \<in>
     {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S} \<times>\<^sub>f nat_rel  \<times>\<^sub>f bool_rel \<rightarrow>\<^sub>f
     \<langle>{(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S} \<times>\<^sub>r nat_rel\<rangle>nres_rel\<close>
proof -
  have [refine0]: \<open>restart_required_wl x1c x2b \<le> \<Down> Id (restart_required_wl x1a x2)\<close>
    if \<open>(x1c, x1a) \<in> Id\<close> \<open>(x2b, x2) \<in> Id\<close>
    for x1c x1a x2b x2
    using that by auto

  show ?thesis
    unfolding uncurry_def restart_prog_wl_D_def restart_prog_wl_def
    apply (intro frefI nres_relI)
    apply (refine_vcg
      cdcl_twl_restart_wl_prog_cdcl_twl_restart_l_prog[THEN fref_to_Down_curry2]
      rewatch_clauses_prog_D_rewatch_clauses_prog[THEN fref_to_Down]
      remove_one_annot_true_clause_imp_wl_D_remove_one_annot_true_clause_imp_wl[THEN fref_to_Down]
      cdcl_twl_restart_wl_prog_D_cdcl_twl_restart_wl_prog[THEN fref_to_Down])
    subgoal unfolding restart_abs_wl_D_pre_def by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

definition cdcl_twl_stgy_restart_prog_wl_D :: "nat twl_st_wl \<Rightarrow> nat twl_st_wl nres" where
  \<open>cdcl_twl_stgy_restart_prog_wl_D S\<^sub>0 =
  do {
    (brk, T, _) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(brk, T, n). cdcl_twl_stgy_restart_abs_wl_inv S\<^sub>0 brk T n\<^esup>
      (\<lambda>(brk, _). \<not>brk)
      (\<lambda>(brk, S, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop_wl_D S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog_wl_D T;
        (T, n) \<leftarrow> restart_prog_wl_D T n brk;
        RETURN (brk, T, n)
      })
      (False, S\<^sub>0::nat twl_st_wl, 0);
    RETURN T
  }\<close>

lemma cdcl_twl_stgy_restart_prog_wl_D_cdcl_twl_stgy_restart_prog_wl:
  \<open>(cdcl_twl_stgy_restart_prog_wl_D, cdcl_twl_stgy_restart_prog_wl) \<in>
     {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S} \<rightarrow>\<^sub>f
     \<langle>{(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S}\<rangle>nres_rel\<close>
  unfolding uncurry_def cdcl_twl_stgy_restart_prog_wl_D_def
    cdcl_twl_stgy_restart_prog_wl_def
  apply (intro frefI nres_relI)
  apply (refine_vcg
      restart_prog_wl_D_restart_prog_wl[THEN fref_to_Down_curry2]
      cdcl_twl_o_prog_wl_D_spec'[THEN fref_to_Down]
      unit_propagation_outer_loop_wl_D_spec'[THEN fref_to_Down]
      WHILEIT_refine[where R=\<open>bool_rel \<times>\<^sub>r {(S, T). (S, T) \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S} \<times>\<^sub>r nat_rel\<close>])
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  done

end

text \<open>
  This is a list of comments (how does it work for glucose and cadical) to prepare the future
  refinement:
  \<^enum> Reduction
     \<^item> every 2000+300*n (rougly since inprocessing changes the real number, cadical)
           (split over initialisation file); don't restart if level < 2 or if the level is less
       than the fast average
     \<^item> curRestart * nbclausesbeforereduce;
          curRestart = (conflicts / nbclausesbeforereduce) + 1 (glucose)
  \<^enum> Killed
     \<^item> half of the clauses that \<^bold>\<open>can\<close> be deleted (i.e., not used since last restart), not strictly
       LBD, but a probability of being useful.
     \<^item> half of the clauses
  \<^enum> Restarts:
     \<^item> EMA-14, aka restart if enough clauses and slow_glue_avg * opts.restartmargin > f (file ema.cpp)
     \<^item> (lbdQueue.getavg() * K) > (sumLBD / conflictsRestarts),
       \<^text>\<open>conflictsRestarts > LOWER_BOUND_FOR_BLOCKING_RESTART && lbdQueue.isvalid() && trail.size() > R * trailQueue.getavg()\<close>
\<close>
end